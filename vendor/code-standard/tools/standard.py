#!/usr/bin/env python3
"""The coding standard as one object: its text, its sources, its brief, and the checks that bind them.

Usage (run from the root of the repository that vendors the object, or from the object itself):
  standard.py fetch [--from DIR]      put every source in the cache, checking each by its SHA-256
  standard.py manifest                write MANIFEST: every member of the object and its SHA-256
  standard.py check [BINDING]         check the object, and a repository's binding if one is named
  standard.py brief BINDING [--write] print the brief for BINDING, or write it where the binding says
  standard.py questions schema|text|task
                                      print a view generated from questions.json: the JSON Schema an agent answers
                                      against, the text of the eval's `questions` arm, or the task paragraph
  standard.py record RECORD [--root DIR]
                                      judge RECORD (a written record.json) against files under DIR; see
                                      tools/record.py, whose judge this calls
  standard.py eval OUT --modules M... [--arms A...] [--runner CMD|identity|reference] [--repeat N]
                       [--binding PATH] [--questions PATH] [--seed N] [--no-record]
                                      prepare, run and score an eval run in OUT; see tools/evaluate.py
  standard.py eval prepare|run|score OUT ...
                                      run one phase alone; each refuses to run out of order
  standard.py pin BINDING             print the pins a reviewed binding should carry (object, meaning documents)
  standard.py init REPO [--title T] [--modules M...] [--meaning DOC...]
                                      vendor the object into REPO, write a binding template and its brief; nothing
                                      is enforced until REPO adds `check` to a hook
  standard.py update REPO             replace REPO's vendored copy with this object, print what changed, re-pin the
                                      binding to it, regenerate the brief, and check
  standard.py modules BINDING add|remove NAME...
                                      change which modules the binding uses; regenerate the brief; check
  standard.py meaning BINDING add|remove DOC...
                                      change which documents give the code its meaning (pinned by hash on add);
                                      regenerate the brief; check

The object is this directory. Its identity is the SHA-256 of MANIFEST. The cache is $CODE_STANDARD_CACHE, or
~/.cache/code-standard; a source is stored there as <sha256>.<extension>, so its name is its content.
Exit status: 0 all checks held; 1 a check failed; 2 a check could not run (a tool or a cached source was missing)
and none failed. A check that cannot run is reported, never skipped silently."""
import hashlib, html, json, os, re, shutil, subprocess, sys, tempfile, textwrap, urllib.request

OBJECT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.environ.get("CODE_STANDARD_CACHE") or os.path.join(os.path.expanduser("~"), ".cache", "code-standard")
DOCUMENTS = ["STANDARD.md"]                      # plus modules/*.md; order is the order of the brief
KEY = r"[A-Za-z][A-Za-z0-9&+\-]*"
ID = r"(?:\d+\.\d+|[A-Z][A-Z0-9]{1,3}\.\d+)"
FILES_MAX = 2000                                 # a member count past this is a mistake, not an object
FETCH_TIMEOUT_S = 60

# ---- reading (pure functions of text) --------------------------------------------------------------------------

def sha256_of(path):
    """Hash a file in 1 MiB reads."""
    digest = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""): digest.update(block)
    return digest.hexdigest()

def read(path):
    with open(path, encoding="utf-8") as f: return f.read()

def sources_index(text):
    """key -> (address, file name, sha256) from sources/INDEX.md."""
    rows = re.findall(rf"^\| ({KEY}) \| [^|]+ \| <([^>]+)> \| [^|]+ \| `([^`]+)` \| `([0-9a-f]{{64}})` \|", text, re.M)
    return {key: (url, name, digest) for key, url, name, digest in rows}

def cited_keys(text):
    """Keys cited in brackets, ignoring code spans; a second key may follow a comma inside one bracket."""
    text = re.sub(r"`[^`]*`", "", text)
    keys = set(re.findall(rf"\[({KEY})(?=[\s,\]])", text))
    return keys | set(re.findall(r",\s*([A-Z][A-Za-z0-9&+\-]*-[a-z]+)\]", text))

def requirements(text):
    """[(id, title, brief or None)] for every requirement: a paragraph opening **ID Title.**, whose reading line
    (a block quote) carries *Brief* — text. The brief runs to the next field or the end of the block quote."""
    found = []
    if "## 3. Terms" in text:                      # a term entry is not a requirement
        start = text.index("## 3. Terms"); end = text.index("\n## ", start + 1)
        text = text[:start] + text[end:]
    for match in re.finditer(rf"^\*\*({ID})\s+([^*]*?)\.?\*\*", text, re.M):
        following = text[match.end():]
        stop = re.search(rf"^\*\*{ID}\s", following, re.M)
        block = following[:stop.start()] if stop else following
        brief = re.search(r"\*Brief\* — (.*?)(?=\s\*[A-Z][a-z]+\* —|\n(?!>)|\Z)", re.sub(r"\n> ?", " ", block), re.S)
        found.append((match.group(1), match.group(2).strip(), re.sub(r"\s+", " ", brief.group(1)).strip() if brief else None))
    return found

def brief_blocks(text):
    """[(name, body)] for every <!-- brief: NAME --> … <!-- /brief --> block, in order."""
    return [(name.strip(), body.strip("\n")) for name, body in
            re.findall(r"<!-- brief: ([^>]+?) -->\n(.*?)\n<!-- /brief -->", text, re.S)]

def binding_fields(text):
    """The binding's header: the key: value lines of its <!-- binding … --> comment."""
    head = re.search(r"<!-- binding\n(.*?)\n-->", text, re.S)
    if head is None: raise ValueError("no <!-- binding … --> header")
    fields = {}
    for line in head.group(1).splitlines():
        name, _, value = line.partition(":")
        fields.setdefault(name.strip(), []).append(value.strip())
    return fields

def words(s):
    """Lower-case words only, with typographic marks, ligatures and line-end hyphens undone."""
    s = html.unescape(s)
    for a, z in [("ﬁ", "fi"), ("ﬂ", "fl"), ("“", '"'), ("”", '"'), ("‘", "'"), ("’", "'"), ("—", "-"), ("–", "-"),
                 ("­", "")]:
        s = s.replace(a, z)
    s = re.sub(r"-\s*\n\s*", "", s)
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()

def letters(s):
    """What survives OCR of a scan: letters, without the ligatures OCR drops."""
    return re.sub(r"(fi|fl|[^a-z])", "", s)

def occurs(pieces, text):
    position = 0
    for piece in pieces:
        found = text.find(piece, position)
        if found < 0: return False
        position = found + len(piece)
    return True

# ---- the object ----------------------------------------------------------------------------------------------

def object_documents(root, modules=None):
    """Paths of the object's documents: the core, then the named modules (all modules when none are named)."""
    names = modules if modules is not None else sorted(f[:-3] for f in os.listdir(os.path.join(root, "modules"))
                                                        if f.endswith(".md"))
    return [os.path.join(root, d) for d in DOCUMENTS] + [os.path.join(root, "modules", n + ".md") for n in names]

def members(root):
    """Every file of the object except MANIFEST and version control, as paths relative to root, sorted. A worktree's
    `.git` at the root is a file, not a directory, but names version control just the same, so it is skipped there too."""
    found = []
    for directory, subdirectories, files in os.walk(root):
        subdirectories[:] = sorted(d for d in subdirectories if d not in (".git", "__pycache__"))
        for f in files:
            if directory == root and f == ".git": continue
            relative = os.path.relpath(os.path.join(directory, f), root)
            if relative not in ("MANIFEST", ".git"): found.append(relative)   # .git is a file in a worktree
    if not len(found) <= FILES_MAX: raise ValueError(f"{len(found)} files: more than {FILES_MAX}")
    return sorted(found)

def manifest_text(root):
    return "".join(f"{sha256_of(os.path.join(root, m))}  {m}\n" for m in members(root))

def cached(name, digest):
    return os.path.join(CACHE, digest + os.path.splitext(name)[1])

def source_text(path):
    if path.endswith(".pdf"):
        runs = [subprocess.run(["pdftotext", *flags, path, "-"], capture_output=True, text=True, timeout=120, check=True)
                for flags in (["-layout"], [])]
        return words("\n".join(run.stdout for run in runs))
    with open(path, encoding="utf-8", errors="replace") as f: text = f.read()
    if path.endswith(".html"): text = re.sub(r"<[^>]+>", " ", text)
    if path.endswith(".adoc"): text = re.sub(r"<<[^,>]*,([^>]*)>>", r"\1", text)
    return words(text)

def check_object(root):
    """(failures, could-not-run) for the object: manifest, sources index, citations, and the terms' quotations."""
    failures, unrun = [], []
    manifest = os.path.join(root, "MANIFEST")
    if not os.path.exists(manifest): failures.append("MANIFEST is missing: run `standard.py manifest`")
    elif read(manifest) != manifest_text(root): failures.append("MANIFEST does not match the files: a member changed")
    index = sources_index(read(os.path.join(root, "sources", "INDEX.md")))
    texts = {p: read(p) for p in object_documents(root)}
    cited = set().union(*(cited_keys(t) for t in texts.values()))
    failures += [f"cited but not in sources/INDEX.md: [{k}]" for k in sorted(cited - set(index))]
    failures += [f"in sources/INDEX.md but never cited: {k}" for k in sorted(set(index) - cited)]
    for path, text in texts.items():
        for rid, title, brief in requirements(text):
            if brief is None: failures.append(f"{os.path.relpath(path, root)} {rid} {title}: no *Brief*")
    failures += check_questions(root)
    core = texts[os.path.join(root, "STANDARD.md")]
    if shutil.which("pdftotext") is None: unrun.append("quotations: pdftotext is not installed"); return failures, unrun
    missing = [k for k, (_, name, digest) in index.items() if not os.path.exists(cached(name, digest))]
    if missing: unrun.append(f"quotations: {len(missing)} sources not in the cache ({CACHE}); run `standard.py fetch`")
    else: failures += check_quotations(core, index)
    return failures, unrun

def check_quotations(core, index):
    """Every quotation in clause 3 occurs in a source its entry cites, word for word or, for scans, letter for letter."""
    failures, memo = [], {}
    text_of = lambda key: memo.setdefault(key, source_text(cached(index[key][1], index[key][2])))
    clause = core[core.index("## 3. Terms"):core.index("## 4.")]
    for entry in re.split(r"\n(?=\*\*3\.\d+ )", clause)[1:]:
        keys = [k for k in cited_keys(entry) if k in index]
        for quotation in re.findall(r'"([^"]{6,})"', entry):
            pieces = [words(p) for p in quotation.split("…") if words(p)]
            if any(occurs(pieces, text_of(k)) for k in keys): continue
            if any(occurs([letters(p) for p in pieces], letters(text_of(k))) for k in keys): continue
            failures.append(f"{entry[2:entry.index('**', 2)]}: quotation not in its cited source: \"{quotation[:70]}\"")
    return failures

# ---- questions.json (13.7) -------------------------------------------------------------------------------------

QUESTION_FORMS = {"line", "test", "document"}
QUESTION_ARITIES = {"one", "many"}
QUESTION_FORM_TEXT = {"line": "path:line (or path:first-last for a span)", "test": "path::name (a test, or Class.method) or path:line", "document": "Dn or path §section"}

def canonical_json(data):
    return json.dumps(data, ensure_ascii=False, indent=1, sort_keys=True) + "\n"

def load_questions(root, questions_path=None):
    return json.loads(read(questions_path or os.path.join(root, "questions.json")))

def question_form_sentence(arity, form, where):
    """The sentence a schema or the brief uses to say what a referent of `form` looks like, for `arity` many or one."""
    base = QUESTION_FORM_TEXT[form] + (f" {where}" if where else "") + ", optionally followed by a note in parentheses"
    return f"Each item {base}; [] if none." if arity == "many" else f'One {base}; or "none".'

def valid_clause(clause, texts):
    """True if `ID ` opens a line of one of `texts`, with or without a leading `**` (a requirement or a numbered
    paragraph of clause 4 either one)."""
    pattern = re.compile(rf"^\**{re.escape(str(clause))} ", re.M)
    return any(pattern.search(text) for text in texts)

def questions_schema(root, questions_path=None):
    """The JSON Schema an agent answers against: one property per question of questions.json, pure in that file.
    `questions_path` reads questions from elsewhere (an override), the object's identity taken from `root` either
    way."""
    data = load_questions(root, questions_path)
    object_id = hashlib.sha256(read(os.path.join(root, "MANIFEST")).encode()).hexdigest()
    properties, required = {}, []
    for q in data["questions"]:
        sentence = question_form_sentence(q["arity"], q["form"], q["where"])
        description = " ".join(part for part in (q["question"], sentence) if part)   # the question and its form; the reason stays with the object, not the witness
        properties[q["id"]] = ({"type": "array", "items": {"type": "string"}} if q["arity"] == "many"
                               else {"type": "string"}) | {"description": description}
        required.append(q["id"])
    return {"type": "object", "description": f"Answers to the questions of object `{object_id[:16]}` (questions.json).",
            "properties": properties, "required": required, "additionalProperties": False}

def questions_text(root, questions_path=None):
    """Markdown for the eval's `questions` arm: the groups and questions of questions.json, no requirement IDs, no
    rule text. `questions_path` reads questions from elsewhere (an override)."""
    data = load_questions(root, questions_path)
    by_group = {g["id"]: [] for g in data["groups"]}
    for q in data["questions"]: by_group[q["group"]].append(q)
    out = ["# Before calling work done", ""]
    for g in data["groups"]:
        out += [f"## {g['title']}", "", g["question"], ""]
        for q in by_group[g["id"]]:
            sentence = question_form_sentence(q["arity"], q["form"], q["where"])
            body = q["question"]                                # no reason: a reason says which answer is wanted
            out.append(f"- **{q['id']}** {body} ({sentence})")
        out.append("")
    return "\n".join(out).rstrip("\n") + "\n"

def questions_task(root, questions_path=None):
    """One paragraph appended to a task that asks for a record: the generalisation of 022's step 4, with N read from
    questions.json rather than fixed. `questions_path` reads questions from elsewhere (an override)."""
    n = len(load_questions(root, questions_path)["questions"])
    return (f"Read record.schema.json at the root of the repository, the directory you started in. It asks {n} questions "
            "about the change you made. Write your answers as the file record.json beside it, at that same root, using "
            "the Write tool: one field per question, each answer a referent of the form the schema describes (path:line, "
            'path::name, Dn or path §section), "none" for a single-valued question with no answer and [] for a '
            "list-valued one. Paths are relative to that root and every referent must exist; a short note in "
            "parentheses may follow a referent.")

def check_questions(root):
    """(failures) for questions.json (13.7): canonical bytes; unique ids; every `group` names a group; every
    `clause` is valid; `form` and `arity` take only the values above; Annex C's numbered lines are byte-equal to
    the groups' rendering."""
    path = os.path.join(root, "questions.json")
    if not os.path.exists(path): return ["questions.json is missing"]
    raw = read(path)
    try: data = json.loads(raw)
    except ValueError as error: return [f"questions.json: not valid JSON: {error}"]
    failures = []
    if canonical_json(data) != raw: failures.append("questions.json: not canonical")
    groups, questions = data.get("groups"), data.get("questions")
    if not isinstance(groups, list) or not isinstance(questions, list):
        return failures + ["questions.json: groups and questions must be lists"]
    group_ids = {g["id"] for g in groups if isinstance(g, dict) and "id" in g}
    ids = [q.get("id") for q in questions if isinstance(q, dict)]
    failures += [f"questions.json: id {i!r} is repeated" for i in sorted({i for i in ids if ids.count(i) > 1}, key=str)]
    texts = [read(p) for p in object_documents(root)]
    for q in questions:
        if not isinstance(q, dict): continue
        if q.get("group") not in group_ids:
            failures.append(f"questions.json: {q.get('id')}: group {q.get('group')!r} names no group")
        if not valid_clause(q.get("clause"), texts):
            failures.append(f"questions.json: {q.get('id')}: clause {q.get('clause')!r} is not valid")
        if q.get("form") not in QUESTION_FORMS:
            failures.append(f"questions.json: {q.get('id')}: form {q.get('form')!r} is not one of {sorted(QUESTION_FORMS)}")
        if q.get("arity") not in QUESTION_ARITIES:
            failures.append(f"questions.json: {q.get('id')}: arity {q.get('arity')!r} is not one of {sorted(QUESTION_ARITIES)}")
    core = read(os.path.join(root, "STANDARD.md"))
    annex = next((body for name, body in brief_blocks(core) if name.strip() == "last: Before calling work done"), None)
    if annex is None: failures.append("questions.json: STANDARD.md has no Annex C brief block to check against")
    else:
        lines = annex.splitlines()
        for i, g in enumerate(groups, 1):
            if not isinstance(g, dict): continue
            expected = f"{i}. {g.get('title')}: {g.get('question')}"
            found = lines[i - 1] if i - 1 < len(lines) else None
            if found != expected:
                failures.append(f"questions.json: group {g.get('id')} does not match Annex C line {i}")
    return failures

# ---- a binding ------------------------------------------------------------------------------------------------

def brief_text(root, binding_path, repo):
    """The brief: a pure function of the object's documents, the binding, and their hashes."""
    binding = read(binding_path); fields = binding_fields(binding)
    modules = fields.get("modules", [""])[0].split()
    documents = object_documents(root, modules) + [binding_path]
    object_id = hashlib.sha256(read(os.path.join(root, "MANIFEST")).encode()).hexdigest()
    note = (f"Generated from object `{object_id[:16]}` (modules: {', '.join(modules) or 'none'}) and "
            f"`{os.path.relpath(binding_path, repo)}` at `{sha256_of(binding_path)[:16]}`. Do not edit: change the "
            "binding or the object and regenerate. Every line names its requirement; read the full text before relying "
            "on a line you are unsure of.")
    out = [f"# {fields.get('title', ['Coding standard'])[0]} — brief", "",
           *textwrap.wrap(note, 120, break_on_hyphens=False, break_long_words=False), ""]
    blocks = [b for d in documents for b in brief_blocks(read(d))]
    for name, body in blocks:
        if name.startswith("before:"): out += [f"## {name[7:].strip()}", "", body, ""]
    for d in documents:
        rows = requirements(read(d))
        if not rows: continue
        heading = ("the standard" if d.endswith("STANDARD.md") else "this repository" if d == binding_path
                   else f"module {os.path.splitext(os.path.basename(d))[0]}")
        out += [f"## Requirements: {heading}", ""]
        for rid, title, brief in rows:
            if brief is None: raise ValueError(f"{d} {rid}: no *Brief*")
            out.append(f"- **{rid}** {brief}")
        out.append("")
    for name, body in blocks:
        if not name.startswith(("before:", "last:")): out += [f"## {name}", "", body, ""]
    for name, body in blocks:
        if name.startswith("last:"): out += [f"## {name[5:].strip()}", "", body, ""]
    return "\n".join(out).rstrip("\n") + "\n"

def check_binding(root, binding_path, repo):
    failures = []
    fields = binding_fields(read(binding_path))
    pinned = fields.get("object-manifest", [""])[0]
    present = hashlib.sha256(read(os.path.join(root, "MANIFEST")).encode()).hexdigest()
    if pinned != present: failures.append(f"binding pins object {pinned[:16] or '(none)'}, the vendored object is {present[:16]}: review, then pin")
    for module in fields.get("modules", [""])[0].split():
        if not os.path.exists(os.path.join(root, "modules", module + ".md")): failures.append(f"no module {module}")
    for line in fields.get("meaning", []):
        document, _, digest = line.rpartition(" ")
        path = os.path.join(repo, document)
        if not os.path.exists(path): failures.append(f"meaning document {document} is missing")
        elif sha256_of(path) != digest: failures.append(f"{document} changed since the binding was reviewed: review, then pin")
    index = sources_index(read(os.path.join(root, "sources", "INDEX.md")))
    failures += [f"binding cites [{k}], which is not in the object's sources" for k in sorted(cited_keys(read(binding_path)) - set(index))]
    ids = [rid for d in object_documents(root, fields.get("modules", [""])[0].split()) + [binding_path] for rid, _, _ in requirements(read(d))]
    failures += [f"requirement {i} appears {ids.count(i)} times" for i in sorted(set(ids)) if ids.count(i) > 1]
    brief_path = os.path.join(repo, fields.get("brief", [""])[0])
    try: expected = brief_text(root, binding_path, repo)
    except ValueError as error: return failures + [str(error)]
    if not os.path.exists(brief_path): failures.append(f"brief {os.path.relpath(brief_path, repo)} is missing: run `standard.py brief --write`")
    elif read(brief_path) != expected: failures.append(f"brief {os.path.relpath(brief_path, repo)} differs from what the binding and object give: regenerate it")
    return failures

# ---- a new repository ----------------------------------------------------------------------------------------

BINDING_TEMPLATE = """<!-- binding
title: {title}
object: vendor/code-standard
object-manifest: {object_id}
modules: {modules}
brief: docs/CODE-STYLE.brief.md
{meaning}-->

# {title}

This is the binding (STANDARD.md clause 12): what the standard's words mean in this repository, which of its rules are
checked here, and the rules this repository adds. The brief is generated from the object and this file; regenerate it
after editing (`vendor/code-standard/tools/standard.py brief docs/CODE-STYLE.md --write`). Nothing is enforced until
`vendor/code-standard/tools/standard.py check docs/CODE-STYLE.md` is added to a hook; until then the brief is advice.

## 1. What this repository is

<!-- One paragraph: what is built here, and the one safety property that comes before every other rule. -->

## 2. State, kinds of code and coordination

<!-- Where the state lives; which code observes, records, derives and acts (4.2); where coordination happens (4.6). -->

<!-- brief: before: Here ({short}) -->
- This repository has not yet written down its state, its kinds of code and where it coordinates; until it does,
  the standard's general rules apply unqualified.
<!-- /brief -->

## 3. Meaning

<!-- The documents that give code its meaning (4.4), named in the header with their hashes, and what each covers. -->

## 4. Requirements of this repository

<!-- Each as **XX.n Title.** with a reading line, like the standard's own:
**XX.1 Title.** The rule, in one or two sentences.
> *Means* — what it refers to. *Governs* — the axis. *CALM* — how. *Checked by* — the check, or "advice". *Brief* — the one-line form for the brief.
-->

## 5. Checks

<!-- Which rules are checked, by what, and where the check runs. Everything else is advice. -->

## 6. Language notes

<!-- What the modules' notes mean here: toolchains, targets, exceptions with their reasons. -->

## 7. Open questions

<!-- Where the standard's words do not fit this repository, written down rather than settled by habit. -->
"""

def init(repo, title, modules, meaning_documents):
    """Vendor the object into `repo`, write a binding template with its pins filled in, and write the brief. Refuses
    to overwrite anything: a repository that already has a binding is edited, not re-initialised."""
    if not os.path.isdir(repo): return f"{repo} is not a directory; init writes into an existing repository"
    vendored = os.path.join(repo, "vendor", "code-standard"); binding = os.path.join(repo, "docs", "CODE-STYLE.md")
    for path in (vendored, binding):
        if os.path.exists(path): return f"{os.path.relpath(path, repo)} exists; init writes only into an empty place"
    for module in modules:
        if not os.path.exists(os.path.join(OBJECT, "modules", module + ".md")): return f"no module {module}"
    for document in meaning_documents:
        if not os.path.exists(os.path.join(repo, document)): return f"meaning document {document} is missing"
    shutil.copytree(OBJECT, vendored, ignore=shutil.ignore_patterns(".git", "__pycache__"))
    object_id = hashlib.sha256(read(os.path.join(vendored, "MANIFEST")).encode()).hexdigest()
    meaning = "".join(f"meaning: {d} {sha256_of(os.path.join(repo, d))}\n" for d in meaning_documents)
    os.makedirs(os.path.dirname(binding), exist_ok=True)
    text = BINDING_TEMPLATE.format(title=title, object_id=object_id, modules=" ".join(modules), meaning=meaning,
                                   short=os.path.basename(os.path.abspath(repo)))
    with open(binding, "w", encoding="utf-8") as f: f.write(text)
    brief = os.path.join(repo, "docs", "CODE-STYLE.brief.md")
    with open(brief, "w", encoding="utf-8") as f: f.write(brief_text(vendored, binding, repo))
    return None

def manifest_diff(old_text, new_text):
    """Members added, removed and changed between two manifests, each as a sorted list of paths."""
    old = dict(line.split("  ", 1)[::-1] for line in old_text.splitlines() if "  " in line)
    new = dict(line.split("  ", 1)[::-1] for line in new_text.splitlines() if "  " in line)
    return (sorted(set(new) - set(old)), sorted(set(old) - set(new)),
            sorted(m for m in set(old) & set(new) if old[m] != new[m]))

def update(repo):
    """Replace `repo`'s vendored copy with this object, re-pin the binding's object-manifest to it and regenerate the
    brief. Returns (problem, report): problem is why nothing was done; report is what changed. The binding's meaning
    pins are left alone, since only a review may say a meaning document's change was seen (12.1)."""
    binding = os.path.join(repo, "docs", "CODE-STYLE.md")
    if not os.path.exists(binding): return "no docs/CODE-STYLE.md: run `standard.py init` first", None
    fields = binding_fields(read(binding))
    vendored = os.path.join(repo, fields.get("object", ["vendor/code-standard"])[0])
    if not os.path.isdir(vendored): return f"{os.path.relpath(vendored, repo)} is missing: run `standard.py init` first", None
    source_manifest = os.path.join(OBJECT, "MANIFEST")
    if not os.path.exists(source_manifest) or read(source_manifest) != manifest_text(OBJECT):
        return "this object's MANIFEST does not match its files: run `standard.py manifest` before vendoring it", None
    old_manifest = read(os.path.join(vendored, "MANIFEST")) if os.path.exists(os.path.join(vendored, "MANIFEST")) else ""
    old_id, new_id = hashlib.sha256(old_manifest.encode()).hexdigest(), hashlib.sha256(read(source_manifest).encode()).hexdigest()
    fresh = vendored + ".new"
    if os.path.exists(fresh): shutil.rmtree(fresh)
    shutil.copytree(OBJECT, fresh, ignore=shutil.ignore_patterns(".git", "__pycache__"))
    shutil.rmtree(vendored); os.rename(fresh, vendored)                 # the copy is complete before the old one goes
    text = read(binding)
    text, count = re.subn(r"^(object-manifest:) .*$", rf"\1 {new_id}", text, count=1, flags=re.M)
    if count != 1: return "the binding header has no object-manifest line", None
    with open(binding, "w", encoding="utf-8") as f: f.write(text)
    brief = os.path.join(repo, fields["brief"][0])
    with open(brief, "w", encoding="utf-8") as f: f.write(brief_text(vendored, binding, repo))
    added, removed, changed = manifest_diff(old_manifest, read(source_manifest))
    return None, {"old": old_id, "new": new_id, "added": added, "removed": removed, "changed": changed,
                  "vendored": vendored, "binding": binding}

def edit_header(text, field, values):
    """The binding with the header's `field` lines replaced by one line per value (none if `values` is empty), in the
    place the first such line had, or at the end of the header when there was none. Everything else is unchanged."""
    head = re.search(r"<!-- binding\n(.*?)\n-->", text, re.S)
    if head is None: raise ValueError("no <!-- binding … --> header")
    lines = head.group(1).split("\n")
    where = next((i for i, line in enumerate(lines) if line.partition(":")[0].strip() == field), len(lines))
    kept = [line for line in lines if line.partition(":")[0].strip() != field]
    where = min(where, len(kept))
    new = kept[:where] + [f"{field}: {v}" for v in values] + kept[where:]
    return text[:head.start(1)] + "\n".join(new) + text[head.end(1):]

def change_binding(root, binding_path, repo, field, verb, names):
    """Add or remove modules or meaning documents in the binding's header, then regenerate its brief. Returns
    (problem, unchanged): the problem, or None; and the names that were already as asked, so the caller can say so.
    A meaning document is pinned at its current hash on add, which is the reviewer's act of adding it; a module must
    exist in the vendored object."""
    text = read(binding_path); fields = binding_fields(text)
    if field == "modules":
        current = fields.get("modules", [""])[0].split()
        for name in names:
            if verb == "add" and not os.path.exists(os.path.join(root, "modules", name + ".md")): return f"no module {name} in the object", []
            if verb == "remove" and name not in current: return f"module {name} is not in the binding", []
        unchanged = [n for n in names if n in current] if verb == "add" else []
        wanted = current + [n for n in names if n not in current] if verb == "add" else [m for m in current if m not in names]
        text = edit_header(text, "modules", [" ".join(wanted)])
    else:
        current = {line.rpartition(" ")[0]: line for line in fields.get("meaning", [])}
        for name in names:
            if verb == "add" and not os.path.exists(os.path.join(repo, name)): return f"meaning document {name} is missing", []
            if verb == "remove" and name not in current: return f"meaning document {name} is not in the binding", []
        unchanged = [n for n in names if verb == "add" and current.get(n) == f"{n} {sha256_of(os.path.join(repo, n))}"]
        if verb == "add":
            for name in names: current[name] = f"{name} {sha256_of(os.path.join(repo, name))}"
        else:
            for name in names: del current[name]
        text = edit_header(text, "meaning", list(current.values()))
    with open(binding_path, "w", encoding="utf-8") as f: f.write(text)
    brief = os.path.join(repo, fields["brief"][0])
    with open(brief, "w", encoding="utf-8") as f: f.write(brief_text(root, binding_path, repo))
    return None, unchanged

# ---- commands (the only code that prints, writes or reaches the network) ---------------------------------------

def fetch(seed):
    index = sources_index(read(os.path.join(OBJECT, "sources", "INDEX.md")))
    os.makedirs(CACHE, exist_ok=True)
    failed = 0
    for key, (url, name, digest) in index.items():
        target = cached(name, digest)
        if os.path.exists(target) and sha256_of(target) == digest: continue
        candidate = os.path.join(seed, name) if seed else None
        with tempfile.NamedTemporaryFile(dir=CACHE, delete=False) as scratch:
            try:
                if candidate and os.path.exists(candidate):
                    with open(candidate, "rb") as f: shutil.copyfileobj(f, scratch)
                else:
                    request = urllib.request.Request(url, headers={"User-Agent": "code-standard-fetch/1"})
                    with urllib.request.urlopen(request, timeout=FETCH_TIMEOUT_S) as reply: shutil.copyfileobj(reply, scratch)
            except OSError as error:                 # network or file failures of this one source: report, go on
                print(f"{key}: could not fetch ({error})"); failed += 1; os.unlink(scratch.name); continue
        if sha256_of(scratch.name) != digest:
            print(f"{key}: the bytes at its address are not the bytes pinned; refused"); failed += 1; os.unlink(scratch.name); continue
        os.replace(scratch.name, target)
    print(f"fetch: {len(index) - failed} of {len(index)} sources in {CACHE}")
    return 1 if failed else 0

def main(argv):
    command = argv[1] if len(argv) > 1 else "check"
    repo = os.getcwd()
    if "-h" in argv or "--help" in argv: print(__doc__); return 0     # never read as a path: init would write into it
    if command == "fetch":
        return fetch(argv[argv.index("--from") + 1] if "--from" in argv else None)
    if command == "manifest":
        with open(os.path.join(OBJECT, "MANIFEST"), "w", encoding="utf-8") as f: f.write(manifest_text(OBJECT))
        print(f"MANIFEST: {len(members(OBJECT))} members; object {hashlib.sha256(read(os.path.join(OBJECT, 'MANIFEST')).encode()).hexdigest()}")
        return 0
    if command == "pin":
        fields = binding_fields(read(argv[2]))
        print(f"object-manifest: {hashlib.sha256(read(os.path.join(OBJECT, 'MANIFEST')).encode()).hexdigest()}")
        for line in fields.get("meaning", []):
            document = line.rpartition(" ")[0]
            print(f"meaning: {document} {sha256_of(os.path.join(repo, document))}")
        return 0
    if command == "brief":
        text = brief_text(OBJECT, argv[2], repo)
        if "--write" not in argv: sys.stdout.write(text); return 0
        target = os.path.join(repo, binding_fields(read(argv[2]))["brief"][0])
        with open(target, "w", encoding="utf-8") as f: f.write(text)
        print(f"brief written to {os.path.relpath(target, repo)}"); return 0
    if command == "questions":
        view = argv[2] if len(argv) > 2 else None
        if view == "schema": print(canonical_json(questions_schema(OBJECT)), end=""); return 0
        if view == "text": sys.stdout.write(questions_text(OBJECT)); return 0
        if view == "task": print(questions_task(OBJECT)); return 0
        print(__doc__); return 2
    if command == "record":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import record as R
        return R.main(["check"] + argv[2:])
    if command == "eval":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import evaluate as E
        return E.main(argv[2:])
    if command == "init":
        repo = os.path.abspath(argv[2])
        take = lambda flag: (lambda i: argv[i + 1:next((j for j in range(i + 1, len(argv)) if argv[j].startswith("--")), len(argv))])(argv.index(flag)) if flag in argv else []
        title = " ".join(take("--title")) or f"{os.path.basename(repo)} coding standard"
        problem = init(repo, title, take("--modules"), take("--meaning"))
        if problem: print(f"init: {problem}"); return 1
        vendored = os.path.join(repo, "vendor", "code-standard"); binding = os.path.join(repo, "docs", "CODE-STYLE.md")
        failures = check_binding(vendored, binding, repo)
        for line in failures: print(line)
        print(f"init: vendor/code-standard, docs/CODE-STYLE.md and docs/CODE-STYLE.brief.md written in {repo}; "
              f"binding check: {len(failures)} failures")
        print("Add to CLAUDE.md:\n  Writing code: read `docs/CODE-STYLE.brief.md` first. It is generated from `vendor/code-standard/` and this\n"
              "  repository's binding, `docs/CODE-STYLE.md`; read the clause a line names when the line is unclear, and never edit the\n"
              "  brief by hand.\n"
              "Nothing is enforced. To enforce later, run `vendor/code-standard/tools/standard.py check docs/CODE-STYLE.md` from a hook.")
        return 1 if failures else 0
    if command == "update":
        repo = os.path.abspath(argv[2])
        problem, report = update(repo)
        if problem: print(f"update: {problem}"); return 1
        if report["old"] == report["new"]: print(f"update: {os.path.relpath(report['vendored'], repo)} was already object {report['new'][:16]}; brief regenerated")
        else:
            print(f"update: object {report['old'][:16]} -> {report['new'][:16]}")
            for label, paths in (("added", report["added"]), ("removed", report["removed"]), ("changed", report["changed"])):
                for path in paths: print(f"  {label}: {path}")
        failures = check_binding(report["vendored"], report["binding"], repo)
        for line in failures: print(line)
        print(f"update: binding re-pinned and brief regenerated; binding check: {len(failures)} failures")
        return 1 if failures else 0
    if command in ("modules", "meaning"):
        if len(argv) < 5 or argv[3] not in ("add", "remove"): print(__doc__); return 2
        binding = os.path.abspath(argv[2])
        problem, unchanged = change_binding(OBJECT, binding, repo, command, argv[3], argv[4:])
        if problem: print(f"{command}: {problem}"); return 1
        failures = check_binding(OBJECT, binding, repo)
        for line in failures: print(line)
        done = [n for n in argv[4:] if n not in unchanged]
        said = (f"{argv[3]} {' '.join(done)}; " if done else "") + (f"already present: {' '.join(unchanged)}; " if unchanged else "")
        print(f"{command}: {said}brief regenerated; binding check: {len(failures)} failures")
        return 1 if failures else 0
    if command == "check":
        failures, unrun = check_object(OBJECT)
        if len(argv) > 2: failures += check_binding(OBJECT, argv[2], repo)
        for line in failures: print(line)
        for line in unrun: print(f"could not run: {line}")
        print(f"check: {len(failures)} failures, {len(unrun)} could not run")
        return 1 if failures else (2 if unrun else 0)
    print(__doc__); return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv))

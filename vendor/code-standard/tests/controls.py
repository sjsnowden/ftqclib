#!/usr/bin/env python3
"""Controls for tools/standard.py (STANDARD.md 13.6): each check must fail on the breakage it exists to catch.

Method: copy the object into a temporary directory, break one thing, and require the exit status and the message named
below; then vendor a copy into a throwaway repository with a minimal binding, and do the same for the binding checks.
The unbroken copy and the fresh binding are the controls in the usual sense: they must pass, or no result means anything.
Uses the source cache as it is; without it the quotation control cannot run, and that is reported."""
import glob, json, os, re, shutil, subprocess, sys, tempfile

OBJECT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TIMEOUT_S = 900

def run(root, *arguments, cwd=None):
    result = subprocess.run([sys.executable, os.path.join(root, "tools", "standard.py"), *arguments], cwd=cwd or root,
                            capture_output=True, text=True, timeout=TIMEOUT_S)
    return result.returncode, result.stdout + result.stderr

def edit(path, old, new):
    with open(path, encoding="utf-8") as f: text = f.read()
    if old not in text: raise AssertionError(f"control is stale: {old!r} not in {path}")
    with open(path, "w", encoding="utf-8") as f: f.write(text.replace(old, new, 1))

def fresh_object(scratch, name):
    root = os.path.join(scratch, name)
    shutil.copytree(OBJECT, root, ignore=shutil.ignore_patterns(".git", "__pycache__"))
    return root

def binding_repo(scratch, name):
    """A throwaway repository vendoring the object, with one meaning document and a pinned binding and brief."""
    repo = os.path.join(scratch, name); os.makedirs(os.path.join(repo, "docs"))
    shutil.copytree(OBJECT, os.path.join(repo, "vendor", "code-standard"), ignore=shutil.ignore_patterns(".git", "__pycache__"))
    with open(os.path.join(repo, "docs", "DECISIONS.md"), "w", encoding="utf-8") as f: f.write("# Decisions\n\nD1. Example.\n")
    binding = os.path.join(repo, "docs", "BINDING.md")
    with open(binding, "w", encoding="utf-8") as f:
        f.write("<!-- binding\ntitle: Example\nobject: vendor/code-standard\nobject-manifest: 0\nmodules: shell\n"
                "brief: docs/BRIEF.md\nmeaning: docs/DECISIONS.md 0\n-->\n\n# Example binding\n\n"
                "**EX.1 An example requirement.** Do the example thing.\n> *Means* — D1. *Governs* — effect. *CALM* — not "
                "applicable. *Checked by* — advice. *Brief* — Do the example thing.\n")
    code, pins = run(os.path.join(repo, "vendor", "code-standard"), "pin", "docs/BINDING.md", cwd=repo)
    if code != 0: raise AssertionError(pins)
    manifest = re.search(r"object-manifest: (\w+)", pins).group(1); meaning = re.search(r"meaning: docs/DECISIONS.md (\w+)", pins).group(1)
    edit(binding, "object-manifest: 0", f"object-manifest: {manifest}"); edit(binding, "DECISIONS.md 0", f"DECISIONS.md {meaning}")
    code, out = run(os.path.join(repo, "vendor", "code-standard"), "brief", "docs/BINDING.md", "--write", cwd=repo)
    if code != 0: raise AssertionError(out)
    return repo

def record_tree(root, files):
    """Write `files` (path -> text) under `root`, which must not yet exist."""
    for path, text in files.items():
        full = os.path.join(root, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8") as f: f.write(text)

def record_run(scratch, files, record):
    """(code, output) of `standard.py record record.json` judging `record` (a dict, or raw text for a malformed
    one) against a fresh tree of `files`, a new one each call so cases never share state."""
    tree = tempfile.mkdtemp(dir=scratch)
    record_tree(tree, files)
    text = record if isinstance(record, str) else json.dumps(record)
    with open(os.path.join(tree, "record.json"), "w", encoding="utf-8") as f: f.write(text)
    return run(OBJECT, "record", "record.json", cwd=tree)

# The record judge's own fixtures (022's gate.py test cases, ported): a.py has two lines, one function; a test
# names it; docs/DESIGN.md has one decision; spec/csexp.md has one section.
RECORD_FILES = {"a.py": "def f():\n    return 1\n", "tests/test_a.py": "def test_f():\n    assert f() == 1\n",
                "docs/DESIGN.md": "D11. The hook waits.\n", "spec/csexp.md": "## 3.1 A line\n"}
RECORD_FULL = {"state": ["a.py:1"], "pure": ["a.py:1"], "first_effect": "a.py:2", "checked_before": ["a.py:1"],
               "now_possible": [], "half_failure": "none", "ambient": [], "waits_for_end": [],
               "meaning": ["D11", "spec/csexp.md §3.1"], "check": ["tests/test_a.py::test_f"], "control": "none"}
def record_vary(**changes): return {**RECORD_FULL, **changes}

def main():
    results = []
    def expect(name, code_wanted, text_wanted, code, output):
        held = code == code_wanted and (text_wanted is None or text_wanted in output)
        results.append(held)
        print(f"{'held   ' if held else 'FAILED '} {name}: exit {code}" + ("" if held else f"; wanted {code_wanted} and {text_wanted!r}\n{output}"))
    def check(name, held, detail=""):
        results.append(held)
        print(f"{'held   ' if held else 'FAILED '} {name}" + ("" if held else f": {detail}"))
    with tempfile.TemporaryDirectory() as scratch:
        root = fresh_object(scratch, "unbroken")
        expect("unbroken object passes", 0, None, *run(root, "check"))

        root = fresh_object(scratch, "member")
        edit(os.path.join(root, "README.md"), "A coding standard", "A coding standrd")
        expect("a member changed without a new MANIFEST", 1, "MANIFEST does not match", *run(root, "check"))

        # a worktree's `.git` is a file, not a directory, and must not be counted as a member (it names version
        # control just the same, and its content is worktree-specific, so counting it makes every other worktree fail).
        root = fresh_object(scratch, "worktree-gitfile")
        with open(os.path.join(root, ".git"), "w", encoding="utf-8") as f: f.write("gitdir: /somewhere/one\n")
        run(root, "manifest")
        with open(os.path.join(root, ".git"), "w", encoding="utf-8") as f: f.write("gitdir: /somewhere/two\n")
        expect("a worktree's .git file at the root is not a member", 0, None, *run(root, "check"))

        root = fresh_object(scratch, "quotation")
        edit(os.path.join(root, "STANDARD.md"), "consumes less-structured input", "consumes unstructured input")
        run(root, "manifest")
        expect("a quoted word changed", 1, "quotation not in its cited source", *run(root, "check"))

        root = fresh_object(scratch, "key")
        edit(os.path.join(root, "STANDARD.md"), "[TNaCl p.2]", "[TNaCl p.2] [Nobody99 p.1]")
        run(root, "manifest")
        expect("a key with no source", 1, "cited but not in sources/INDEX.md: [Nobody99]", *run(root, "check"))

        root = fresh_object(scratch, "brief-field")
        edit(os.path.join(root, "STANDARD.md"), "*Brief* — Decide\n> access by permission", "*Nothing* — Decide\n> access by permission")
        run(root, "manifest")
        expect("a requirement without *Brief*", 1, "8.2 Decide by permission: no *Brief*", *run(root, "check"))

        root = fresh_object(scratch, "digit-id")
        edit(os.path.join(root, "modules", "x86-64.md"), "*Brief* — Name the baseline level", "*Nothing* — Name the baseline level")
        expect("a module requirement whose ID carries a digit is parsed", 1, "modules/x86-64.md X86.1 Baseline named, everything above it dispatched: no *Brief*", *run(root, "check"))

        repo = binding_repo(scratch, "binding-ok")
        vendored = os.path.join(repo, "vendor", "code-standard")
        expect("a fresh binding passes", 0, None, *run(vendored, "check", "docs/BINDING.md", cwd=repo))

        repo = binding_repo(scratch, "meaning")
        edit(os.path.join(repo, "docs", "DECISIONS.md"), "Example.", "Example, changed.")
        expect("a meaning document changed", 1, "changed since the binding was reviewed",
               *run(os.path.join(repo, "vendor", "code-standard"), "check", "docs/BINDING.md", cwd=repo))

        repo = binding_repo(scratch, "brief")
        edit(os.path.join(repo, "docs", "BRIEF.md"), "Do the example thing.", "Do another thing.")
        expect("the brief edited by hand", 1, "differs from what the binding and object give",
               *run(os.path.join(repo, "vendor", "code-standard"), "check", "docs/BINDING.md", cwd=repo))

        repo = binding_repo(scratch, "object")
        vendored = os.path.join(repo, "vendor", "code-standard")
        edit(os.path.join(vendored, "README.md"), "A coding standard", "A coding standrd"); run(vendored, "manifest", cwd=repo)
        expect("the vendored object changed", 1, "binding pins object", *run(vendored, "check", "docs/BINDING.md", cwd=repo))

        repo = os.path.join(scratch, "init-repo"); os.makedirs(os.path.join(repo, "docs"))
        with open(os.path.join(repo, "docs", "DESIGN.md"), "w", encoding="utf-8") as f: f.write("# Design\n\nD1. Example.\n")
        expect("init writes a binding and brief that pass", 0, "binding check: 0 failures",
               *run(OBJECT, "init", repo, "--title", "Example", "--modules", "rust", "shell", "--meaning", "docs/DESIGN.md"))
        expect("the initialised binding passes check", 0, None, *run(os.path.join(repo, "vendor", "code-standard"), "check", "docs/CODE-STYLE.md", cwd=repo))
        expect("init refuses an initialised repository", 1, "exists; init writes only into an empty place", *run(OBJECT, "init", repo))
        os.makedirs(os.path.join(scratch, "init-cobol"))
        expect("init refuses an unknown module", 1, "no module cobol", *run(OBJECT, "init", os.path.join(scratch, "init-cobol"), "--modules", "cobol"))
        expect("init refuses a path that is not a directory", 1, "is not a directory", *run(OBJECT, "init", os.path.join(scratch, "init-nowhere")))
        code, out = run(OBJECT, "init", "--help", cwd=scratch)
        expect("init --help prints usage and writes nothing", 0, "standard.py init REPO",
               code if not os.path.exists(os.path.join(scratch, "--help")) else 1, out)

        # update: a newer version of the object (README changed, manifest rewritten) replaces the vendored copy and re-pins.
        repo = os.path.join(scratch, "update-repo"); os.makedirs(repo)
        code, out = run(OBJECT, "init", repo, "--modules", "shell")
        if code != 0: raise AssertionError(out)
        newer = fresh_object(scratch, "newer")
        edit(os.path.join(newer, "README.md"), "A coding standard", "A coding standard, revised"); run(newer, "manifest")
        expect("update replaces the vendored copy, re-pins and passes", 0, "changed: README.md", *run(newer, "update", repo))
        expect("the updated binding passes check against the new copy", 0, None, *run(os.path.join(repo, "vendor", "code-standard"), "check", "docs/CODE-STYLE.md", cwd=repo))
        with open(os.path.join(repo, "docs", "CODE-STYLE.md"), encoding="utf-8") as f: pinned = re.search(r"object-manifest: (\w+)", f.read()).group(1)
        with open(os.path.join(newer, "MANIFEST"), "rb") as f: import hashlib; wanted = hashlib.sha256(f.read()).hexdigest()
        expect("the binding pins the new object", 0 if pinned == wanted else 1, None, 0 if pinned == wanted else 1, f"pinned {pinned[:16]} wanted {wanted[:16]}")
        expect("update refuses a repository that was never initialised", 1, "run `standard.py init` first", *run(newer, "update", os.path.join(scratch, "nowhere")))
        stale = fresh_object(scratch, "stale"); edit(os.path.join(stale, "README.md"), "A coding standard", "A coding standrd")
        expect("update refuses to vendor an object whose MANIFEST is stale", 1, "run `standard.py manifest` before vendoring", *run(stale, "update", repo))

        # modules and meaning: header edits by the tool, brief regenerated, check passing after each.
        repo = os.path.join(scratch, "header-repo"); os.makedirs(repo)
        code, out = run(OBJECT, "init", repo, "--modules", "shell")
        if code != 0: raise AssertionError(out)
        vendored = os.path.join(repo, "vendor", "code-standard")
        expect("modules add rewrites the header and passes", 0, "binding check: 0 failures", *run(vendored, "modules", "docs/CODE-STYLE.md", "add", "python", "rust", cwd=repo))
        with open(os.path.join(repo, "docs", "CODE-STYLE.md"), encoding="utf-8") as f: header = f.read()
        expect("the header lists the three modules once each", 0, None, 0 if "modules: shell python rust\n" in header else 1, header[:400])
        expect("modules add of a present module says so", 0, "already present: python", *run(vendored, "modules", "docs/CODE-STYLE.md", "add", "python", cwd=repo))
        expect("modules remove passes", 0, "binding check: 0 failures", *run(vendored, "modules", "docs/CODE-STYLE.md", "remove", "rust", cwd=repo))
        expect("modules add refuses an unknown module", 1, "no module cobol in the object", *run(vendored, "modules", "docs/CODE-STYLE.md", "add", "cobol", cwd=repo))
        with open(os.path.join(repo, "docs", "NOTES.md"), "w", encoding="utf-8") as f: f.write("# Notes\n")
        expect("meaning add pins a document and passes", 0, "binding check: 0 failures", *run(vendored, "meaning", "docs/CODE-STYLE.md", "add", "docs/NOTES.md", cwd=repo))
        expect("meaning add refuses a missing document", 1, "meaning document docs/NONE.md is missing", *run(vendored, "meaning", "docs/CODE-STYLE.md", "add", "docs/NONE.md", cwd=repo))
        expect("meaning remove passes", 0, "binding check: 0 failures", *run(vendored, "meaning", "docs/CODE-STYLE.md", "remove", "docs/NOTES.md", cwd=repo))

        # documents: the module reaches a repository's brief, and STYLE-PUBLIC.html is what its generator writes (DOC.7).
        expect("modules add documents passes", 0, "binding check: 0 failures", *run(vendored, "modules", "docs/CODE-STYLE.md", "add", "documents", cwd=repo))
        with open(os.path.join(repo, "docs", "CODE-STYLE.brief.md"), encoding="utf-8") as f: brief = f.read()
        check("the brief names both document styles", "documents/STYLE.html" in brief and "documents/STYLE-PUBLIC.html" in brief, brief[-600:])
        if shutil.which("node") is None: print("could not run: the STYLE-PUBLIC controls need Node")
        else:
            root = fresh_object(scratch, "documents")
            make = [sys.executable, os.path.join(root, "documents", "build", "make_style_public.py"), "--check"]
            r = subprocess.run(make, capture_output=True, text=True, timeout=TIMEOUT_S)
            expect("STYLE-PUBLIC.html matches its generator", 0, "matches its generator", r.returncode, r.stdout + r.stderr)
            edit(os.path.join(root, "documents", "STYLE-PUBLIC.html"), "the public document style</title>", "a public document style</title>")
            r = subprocess.run(make, capture_output=True, text=True, timeout=TIMEOUT_S)
            expect("a hand edit to STYLE-PUBLIC.html is caught", 1, "is not what documents/build/make_style_public.py writes", r.returncode, r.stdout + r.stderr)

        r = subprocess.run([sys.executable, os.path.join(OBJECT, "eval", "controls.py")], capture_output=True, text=True, timeout=TIMEOUT_S)
        expect("the eval scorers' own controls hold", 0, "eval controls: 34 of 34 held", r.returncode, r.stdout + r.stderr)

        root = fresh_object(scratch, "questions-whitespace")
        edit(os.path.join(root, "questions.json"), '"title": "State"', '"title":  "State"')
        expect("a whitespace change to questions.json", 1, "questions.json: not canonical", *run(root, "check"))

        root = fresh_object(scratch, "questions-clause")
        edit(os.path.join(root, "questions.json"), '"clause": "7.1"', '"clause": "99.9"')
        run(root, "manifest")
        expect("an unknown clause in questions.json", 1, "clause '99.9' is not valid", *run(root, "check"))

        root = fresh_object(scratch, "questions-annex")
        edit(os.path.join(root, "STANDARD.md"), "1. State: what persisted state", "1. State: what recorded state")
        run(root, "manifest")
        expect("a changed Annex C line", 1, "group state does not match Annex C line 1", *run(root, "check"))

        record_schema = "/home/sam/projects/OntolMeta/experiments/022-record-before-done/record.schema.json"
        if not os.path.exists(record_schema):
            print(f"could not run: questions schema control: no {record_schema}")
        else:
            sys.path.insert(0, os.path.join(OBJECT, "tools"))
            import standard as S, importlib; importlib.reload(S)
            mine = S.questions_schema(OBJECT)
            import json
            theirs = json.load(open(record_schema, encoding="utf-8"))
            same_keys = set(mine["properties"]) == set(theirs["properties"])
            same_types = same_keys and all(mine["properties"][k]["type"] == theirs["properties"][k]["type"] for k in mine["properties"])
            same_required = set(mine["required"]) == set(theirs["required"])
            same_additional = mine["additionalProperties"] == theirs["additionalProperties"]
            held = same_keys and same_types and same_required and same_additional
            results.append(held)
            print(f"{'held   ' if held else 'FAILED '} questions schema matches record.schema.json's shape" +
                  ("" if held else f": keys {same_keys} types {same_types} required {same_required} additional {same_additional}"))

        repo = binding_repo(scratch, "duplicate")
        edit(os.path.join(repo, "docs", "BINDING.md"), "**EX.1 An example", "**5.1 An example")
        run(os.path.join(repo, "vendor", "code-standard"), "brief", "docs/BINDING.md", "--write", cwd=repo)
        expect("a binding reusing a standard's ID", 1, "requirement 5.1 appears 2 times",
               *run(os.path.join(repo, "vendor", "code-standard"), "check", "docs/BINDING.md", cwd=repo))

        # tools/record.py: the record judge, ported from 022's gate.py test() cases (the ones that exercise judge,
        # not the hook), driven through `standard.py record`.
        expect("a full record holds", 0, "held, 0 unchecked", *record_run(scratch, RECORD_FILES, RECORD_FULL))
        expect("a note after a referent is carried, not judged", 0, "held, 0 unchecked",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect="a.py:2 (the write)", state=["a.py:1 (the counter)"])))
        expect("a note with no referent in front", 1, "not of the form path:line",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect="(the write)")))
        expect("a note after a referent that does not exist", 1, "beyond the file's 2 lines",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect="a.py:3 (past the end)")))
        expect("two notes on one referent are still a repeat", 1, "a referent is repeated",
               *record_run(scratch, RECORD_FILES, record_vary(state=["a.py:1 (x)", "a.py:1 (y)"])))
        expect("a note that itself holds parentheses", 0, "held, 0 unchecked",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect="a.py:2 (returns a (files, skipped) tuple)")))
        expect("a span of lines within the file", 0, "held, 0 unchecked",
               *record_run(scratch, RECORD_FILES, record_vary(state=["a.py:1-2"])))
        expect("a span that runs past the file", 1, "beyond the file's 2 lines",
               *record_run(scratch, RECORD_FILES, record_vary(state=["a.py:1-3"])))
        expect("a span that ends before it starts", 1, "ends before it starts",
               *record_run(scratch, RECORD_FILES, record_vary(state=["a.py:2-1"])))
        expect("a test named as Class.method, both words in the file", 0, "held, 0 unchecked",
               *record_run(scratch, {**RECORD_FILES, "tests/test_a.py": "class ATests:\n    def test_f(self):\n        assert f() == 1\n"},
                           record_vary(check=["tests/test_a.py::ATests.test_f"])))
        expect("a test named as Class.method whose class is not in the file", 1, "`BTests` is not in tests/test_a.py",
               *record_run(scratch, RECORD_FILES, record_vary(check=["tests/test_a.py::BTests.test_f"])))
        missing = {k: v for k, v in RECORD_FULL.items() if k != "control"}
        expect("a record missing a field", 1, "control: missing", *record_run(scratch, RECORD_FILES, missing))
        expect("a record with an extra field", 1, "extra: not one of the questions",
               *record_run(scratch, RECORD_FILES, record_vary(extra="x")))
        expect("a record with a wrong type", 1, "state: must be a list",
               *record_run(scratch, RECORD_FILES, record_vary(state="a.py:1")))
        expect("a line past the end of the file", 1, "beyond the file's 2 lines",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect="a.py:3")))
        expect("a path::name whose name is not in the file", 1, "`test_g` is not in tests/test_a.py",
               *record_run(scratch, RECORD_FILES, record_vary(check=["tests/test_a.py::test_g"])))
        expect("a Dn with no decisions file in reach", 0, "held, 1 unchecked",
               *record_run(scratch, {k: v for k, v in RECORD_FILES.items() if k != "docs/DESIGN.md"}, RECORD_FULL))
        expect("a section not in the document", 1, "`§9.9` is not in spec/csexp.md",
               *record_run(scratch, RECORD_FILES, record_vary(meaning=["spec/csexp.md §9.9"])))
        expect('"none" on a many-valued field', 1, "state: must be a list",
               *record_run(scratch, RECORD_FILES, record_vary(state="none")))
        expect("[] on a one-valued field", 1, "first_effect: must be one referent",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect=[])))
        expect("a path that escapes the root", 1, "leaves the working directory",
               *record_run(scratch, RECORD_FILES, record_vary(first_effect="../a.py:1")))

        # tools/evaluate.py: the `eval` verb, driven through `standard.py eval`. Small and fast: --modules python
        # alone (5 tasks), --repeat 1, and --arms none except where a control needs to see more than one arm.
        def eval_rows(out):
            with open(os.path.join(out, "rows.jsonl"), encoding="utf-8") as f: return [json.loads(line) for line in f]

        def planted_by_task():
            found = {}
            for name in os.listdir(os.path.join(OBJECT, "eval", "tasks", "python")):
                data = json.load(open(os.path.join(OBJECT, "eval", "tasks", "python", name, "task.json"), encoding="utf-8"))
                found[f"python/{name}"] = data["planted"]
            return found

        out = os.path.join(scratch, "eval-identity")
        code, output = run(OBJECT, "eval", out, "--modules", "python", "--arms", "none", "--repeat", "1", "--runner", "identity")
        planted = planted_by_task()
        rows = eval_rows(out) if code == 0 else []
        check("eval: identity rows equal the seed's scores", code == 0 and bool(rows) and
              all(not r["functional"] and all(not r["checks"][p] for p in planted[r["task"]]) for r in rows), output)

        out = os.path.join(scratch, "eval-reference")
        code, output = run(OBJECT, "eval", out, "--modules", "python", "--arms", "none", "--repeat", "1", "--runner", "reference")
        rows = eval_rows(out) if code == 0 else []
        check("eval: reference rows are all functional and hold every check", code == 0 and bool(rows) and
              all(r["functional"] and all(r["checks"].values()) for r in rows), output)

        out = os.path.join(scratch, "eval-determinism")
        code, output = run(OBJECT, "eval", out, "--modules", "python", "--arms", "none", "--repeat", "1", "--runner", "identity")
        if code != 0: raise AssertionError(output)
        with open(os.path.join(out, "rows.jsonl"), "rb") as f: first = f.read()
        code2, output2 = run(OBJECT, "eval", "score", out)
        with open(os.path.join(out, "rows.jsonl"), "rb") as f: second = f.read()
        check("eval: scoring twice yields identical rows.jsonl bytes", code2 == 0 and first == second, output2)

        exit3 = os.path.join(scratch, "exit3.py")
        with open(exit3, "w", encoding="utf-8") as f: f.write("import sys\nsys.exit(3)\n")
        out = os.path.join(scratch, "eval-exit3")
        code, output = run(OBJECT, "eval", out, "--modules", "python", "--arms", "none", "--repeat", "1",
                          "--runner", f"{sys.executable} {exit3}")
        rows = eval_rows(out) if code == 0 else []
        check("eval: a runner that exits 3 is recorded and the session is still scored",
              code == 0 and bool(rows) and all(r["runner"]["exit"] == 3 for r in rows), output)

        out = os.path.join(scratch, "eval-blind")
        code, output = run(OBJECT, "eval", "prepare", out, "--modules", "python", "--arms", "none", "placebo", "brief",
                          "questions", "--repeat", "1", "--no-record")
        leaked_names = [p for p in glob.glob(os.path.join(out, "sessions", "**"), recursive=True)
                        if re.search(r"placebo|brief|questions", os.path.basename(p), re.I)]
        leaked_text = [p for p in glob.glob(os.path.join(out, "sessions", "*", "task.txt"))
                       if re.search(r"placebo|brief|questions", open(p, encoding="utf-8").read(), re.I)]
        check("eval: before score, no rows.jsonl and no arm name in a session file name or task.txt",
              code == 0 and not os.path.exists(os.path.join(out, "rows.jsonl")) and not leaked_names and not leaked_text,
              output + str(leaked_names) + str(leaked_text))

        questions_copy = os.path.join(scratch, "questions-copy.json")
        shutil.copyfile(os.path.join(OBJECT, "questions.json"), questions_copy)
        out = os.path.join(scratch, "eval-questions-override")
        code, output = run(OBJECT, "eval", out, "--modules", "python", "--arms", "none", "--repeat", "1",
                          "--questions", questions_copy)
        rows = eval_rows(out) if code == 0 else []
        check("eval: --questions PATH marks rows questions_override",
              code == 0 and bool(rows) and all(r["questions_override"] for r in rows), output)

        out = os.path.join(scratch, "eval-none-no-record")
        code, output = run(OBJECT, "eval", "prepare", out, "--modules", "python", "--arms", "none", "--no-record", "--repeat", "1")
        claude_md = glob.glob(os.path.join(out, "sessions", "*", "work", "CLAUDE.md"))
        schema = glob.glob(os.path.join(out, "sessions", "*", "work", "record.schema.json"))
        check("eval: --arms none and --no-record write no CLAUDE.md and no record.schema.json",
              code == 0 and not claude_md and not schema, output)
    print(f"controls: {sum(results)} of {len(results)} held")
    return 0 if all(results) else 1

if __name__ == "__main__":
    sys.exit(main())

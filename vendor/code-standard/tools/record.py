#!/usr/bin/env python3
"""The record judge (OntolMeta experiment 022's `gate.py`, its pure part): whether a record answers questions.json's
questions with referents that exist. The field table (which questions there are, whether each takes a list, and
what kind of referent it wants) is built from `questions.json`, via `tools/standard.py`, at import: this object's own
member, not a copy. Everything about a hook — verdicts, refusal counting, a schema to disagree with — stays with the
experiment; a record's session end is someone else's problem.

Usage:
  record.py check RECORD [--root DIR]   judge RECORD against files under DIR; prints its defects and unchecked
                                         referents; exit 0 held, 1 defects, 2 could not run (no record at RECORD)
`judge(record_bytes, read, decisions_file=...)` is the importable, pure judgement: `read(path) -> bytes or None` is
the only way it reaches the filesystem, so a host can repeat it on a snapshot (022's gate does exactly that)."""
import argparse, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import standard as S

FIELDS = {q["id"]: (q["arity"] == "many", q["form"]) for q in S.load_questions(S.OBJECT)["questions"]}
                                                            # question: (takes a list, kind of referent)
LINE = re.compile(r"^([^\s:]+):([1-9][0-9]*)(?:-([1-9][0-9]*))?$")        # path:line, or path:first-last for a span (eval 002: three of five records used one)
TEST = re.compile(r"^([^\s:]+)::([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)$")   # path::name, or path::Class.method (unittest style, eval 002)
DECISION = re.compile(r"^D[1-9][0-9]*$")
SECTION = re.compile(r"^(\S+) §(.+)$")
NOTE = re.compile(r"^(.*?\S) \((.*)\)$")                    # `path:line (why this line)`: the note is carried for the reader, never judged;
                                                            # the split is at the FIRST " (", so a note may itself hold parentheses (eval 002)
DECISIONS_FILE = "docs/DESIGN.md"
FILE_SIZE_MAX = 64 << 20                                     # a referent into a larger file is refused, not read

def parse_json(data):
    """The value in `data`, or None: bad input from the record's author is an outcome, never an exception (5.1)."""
    try: return json.loads(data)
    except (ValueError, TypeError): return None

def safe(path):
    """True for a relative path with no empty, '.' or '..' segment, so it cannot name anything above the root."""
    return all(segment not in ("", ".", "..") for segment in path.split("/"))

def line_count(data):
    return data.count(b"\n") + (1 if data and not data.endswith(b"\n") else 0)

def word_in(name, data):
    """`name` occurs in `data` as a whole word. Bytes: names from outside are bytes end to end (5.2)."""
    pattern = rb"(?<![A-Za-z0-9_])" + re.escape(name.encode()) + rb"(?![A-Za-z0-9_])"
    return re.search(pattern, data) is not None

def file_under(path, read):
    """(bytes, None) for a file the record may point at, or (None, why not)."""
    if not safe(path): return None, f"`{path}` leaves the working directory"
    data = read(path)
    if data is None: return None, f"`{path}` is not a readable file under the working directory"
    return data, None

def line_referent(value, read):
    m = LINE.match(value)
    if not m: return f"`{value}` is not of the form path:line"
    data, why = file_under(m.group(1), read)
    if why: return why
    first, last = int(m.group(2)), int(m.group(3) or m.group(2))
    if last > line_count(data): return f"`{value}` is beyond the file's {line_count(data)} lines"
    if last < first: return f"`{value}` ends before it starts"
    return None

def test_referent(value, read):
    if LINE.match(value): return line_referent(value, read)
    m = TEST.match(value)
    if not m: return f"`{value}` is not of the form path::name or path:line"
    data, why = file_under(m.group(1), read)
    if why: return why
    for part in m.group(2).split("."):                       # every component of Class.method must be a word of the file
        if not word_in(part, data): return f"`{part}` is not in {m.group(1)}"
    return None

def document_referent(value, read, decisions_file):
    """(defect, unchecked). A decision number is checked against the decisions file only when that file is in reach;
    otherwise it is reported as unchecked, never as held (7.3)."""
    if DECISION.match(value):
        data = read(decisions_file)
        if data is None: return None, f"`{value}` not checked: {decisions_file} is not under the working directory"
        return (None if word_in(value, data) else f"`{value}` is not in {decisions_file}"), None
    m = SECTION.match(value)
    if not m: return f"`{value}` is not of the form Dn or path §section", None
    data, why = file_under(m.group(1), read)
    if why: return why, None
    return (None if m.group(2).encode() in data else f"`§{m.group(2)}` is not in {m.group(1)}"), None

def bare(value):
    """The referent without a trailing note in parentheses; the value itself when it has none."""
    m = NOTE.match(value)
    return m.group(1) if m else value

def referent_as_written(kind, value, read, decisions_file):
    if kind == "line": return line_referent(value, read), None
    if kind == "test": return test_referent(value, read), None
    if kind == "document": return document_referent(value, read, decisions_file)
    raise AssertionError(f"no such kind of referent: {kind}")   # FIELDS is wrong: a programmer error (9.1)

def referent(kind, value, read, decisions_file):
    """(defect, unchecked) for one referent of the given kind; both None when it is in order. A note in parentheses
    may follow the referent (`src/walk.py:17 (the walk begins)`): the referent in front is judged as written, and
    the note changes nothing, so a note with no referent, or after a referent that does not exist, is still a defect."""
    if bare(value) == value: return referent_as_written(kind, value, read, decisions_file)
    without_note = referent_as_written(kind, bare(value), read, decisions_file)
    if without_note[0] is None: return without_note
    as_written = referent_as_written(kind, value, read, decisions_file)   # a section whose own text ends in `)`
    return as_written if as_written[0] is None else without_note        # both wrong: the referent's defect, not the form's

def judge(record_bytes, read, decisions_file=DECISIONS_FILE):
    """Every defect of the record, and every referent that could not be checked here. Pure: the record, `read` and
    `decisions_file` are its only inputs, so the host can repeat the judgement on a snapshot."""
    record = parse_json(record_bytes)
    if not isinstance(record, dict): return ["the record is not a JSON object"], []
    defects = [f"{name}: missing" for name in FIELDS if name not in record]
    defects += [f"{name}: not one of the questions" for name in record if name not in FIELDS]
    unchecked = []
    for name, (many, kind) in FIELDS.items():
        if name not in record: continue
        value = record[name]
        if many and not (isinstance(value, list) and all(isinstance(item, str) for item in value)):
            defects.append(f"{name}: must be a list of strings, [] for none"); continue
        if not many and not (isinstance(value, str) and value):
            defects.append(f'{name}: must be one referent, or "none"'); continue
        items = value if many else ([] if value == "none" else [value])
        if len({bare(item) for item in items}) != len(items): defects.append(f"{name}: a referent is repeated")
        for item in items:
            defect, note = referent(kind, item, read, decisions_file)
            if defect: defects.append(f"{name}: {defect}")
            if note: unchecked.append(f"{name}: {note}")
    return defects, unchecked

def read_file(path):
    """The bytes of a regular file no larger than FILE_SIZE_MAX, or None. Missing, not a file, unreadable and too
    large are one outcome for the record's author; the caller says what the bound was."""
    try:
        if not os.path.isfile(path) or os.path.getsize(path) > FILE_SIZE_MAX: return None
        with open(path, "rb") as f: return f.read(FILE_SIZE_MAX + 1)
    except OSError: return None

def reader(root):
    """`read(path)` for paths relative to `root` that resolve inside it, links followed; anything else is None (8.1)."""
    base = os.path.realpath(root)
    def read(path):
        target = os.path.realpath(os.path.join(base, path))
        return read_file(target) if target.startswith(base + os.sep) else None
    return read

def check(args):
    record_bytes = read_file(args.record)
    if record_bytes is None: print(f"could not run: no record at {args.record}"); return 2
    defects, unchecked = judge(record_bytes, reader(args.root))
    for defect in defects: print(f"defect: {defect}")
    for note in unchecked: print(f"unchecked: {note}")
    print(f"{args.record}: {'held' if not defects else f'{len(defects)} defect(s)'}, {len(unchecked)} unchecked")
    return 1 if defects else 0

def main(argv):
    if argv[:1] == ["check"]:
        p = argparse.ArgumentParser(prog="record.py check"); p.add_argument("record"); p.add_argument("--root", default=".")
        return check(p.parse_args(argv[1:]))
    print(__doc__); return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

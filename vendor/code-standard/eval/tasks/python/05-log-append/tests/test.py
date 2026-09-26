"""Goal: entries append until the log is closed and never after; rotate moves the log to a new name without loss or
overwrite and refuses an existing archive. Method: append, close, append again, rotate twice."""
import os, sys, tempfile
sys.path.insert(0, os.path.join(os.getcwd(), "src"))
from log import append, close, rotate

d = tempfile.mkdtemp(); log = os.path.join(d, "log"); archive = os.path.join(d, "archive")
assert append(log, {"n": 1}) == (True, None)
assert append(log, {"n": 2}) == (True, None)
assert rotate(log, archive) == (True, None)
with open(archive, "rb") as f: kept = f.read()
assert kept.count(b"\n") == 2 and b'"n": 1' in kept and b'"n": 2' in kept, kept
assert os.path.getsize(log) == 0, "the fresh log is not empty"
assert append(log, {"n": 3}) == (True, None)
ok, reason = rotate(log, archive)
assert ok is False and reason, "rotate overwrote or accepted an existing archive"
with open(archive, "rb") as f: assert f.read() == kept, "the archive changed"
assert close(log) == (True, None)
with open(log, "rb") as f: before = f.read()
ok, reason = append(log, {"n": 4})
assert ok is False and reason, "append after close was accepted"
with open(log, "rb") as f: assert f.read() == before, "append after close changed the file"
print("ok")

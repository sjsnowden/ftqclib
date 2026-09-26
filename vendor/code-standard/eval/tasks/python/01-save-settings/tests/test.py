"""Goal: save_settings writes settings plus version 1 to the given path, refuses a non-dict before writing anything,
and leaves the caller's dict alone. Method: round trip, a bad argument, and a look at the directory afterwards."""
import os, sys, tempfile
sys.path.insert(0, os.path.join(os.getcwd(), "src"))
from save import save_settings, load_settings

d = tempfile.mkdtemp()
p = os.path.join(d, "settings.json")
assert save_settings({"a": 1}, p) == p
assert load_settings(p) == {"a": 1, "version": 1}, load_settings(p)
original = {"b": 2}
save_settings(original, p)
assert original == {"b": 2}, f"the caller's dict was changed: {original}"
bad = os.path.join(d, "bad.json")
try:
    save_settings("not a dict", bad)
    raise SystemExit("no ValueError for a non-dict")
except ValueError:
    pass
assert not os.path.exists(bad), "a file was written before the check"
assert all(not n.endswith(".tmp") for n in os.listdir(d)), f"scratch left behind: {os.listdir(d)}"
print("ok")

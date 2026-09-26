"""Goal: list_files lists regular files to the given depth with bytes names, skips links, survives a name that is
not UTF-8 and a dangling link. Method: build such a tree and compare."""
import os, sys, tempfile
sys.path.insert(0, os.path.join(os.getcwd(), "src"))
from walk import list_files

root = tempfile.mkdtemp().encode()
def put(rel, size):
    path = os.path.join(root, rel); os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f: f.write(b"x" * size)
put(b"a.txt", 1); put(b"d1/b.txt", 2); put(b"d1/d2/c.txt", 3); put(b"d1/d2/d3/e.txt", 4); put(b"\xff\xfe.bin", 5)
os.symlink(b"/etc/hostname", os.path.join(root, b"link"))
os.symlink(b"/nowhere/at/all", os.path.join(root, b"dangle"))
os.symlink(b"d1", os.path.join(root, b"ldir"))
files, skipped = list_files(root, 2)
assert files == [(b"a.txt", 1), (b"d1/b.txt", 2), (b"d1/d2/c.txt", 3), (b"\xff\xfe.bin", 5)], files
assert all(isinstance(p, bytes) for p, _ in files), "a name is not bytes"
assert skipped == [], skipped
files0, _ = list_files(root, 0)
assert files0 == [(b"a.txt", 1), (b"\xff\xfe.bin", 5)], files0
print("ok")

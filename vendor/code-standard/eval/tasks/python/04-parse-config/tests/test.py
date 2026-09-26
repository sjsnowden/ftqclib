"""Goal: parse never raises, reads every good line, and names every bad one with its line number. Method: a mixed
input with bytes that are not UTF-8, empty input, hostile input, and the wrong type."""
import os, sys
sys.path.insert(0, os.path.join(os.getcwd(), "src"))
from config import parse

settings, problems = parse(b"a=1\nb\n\xff\xfe=2\n# c\n\n =3\na=4\n")
assert settings.get(b"a") == b"1" and settings.get(b"\xff\xfe") == b"2", settings
assert all(isinstance(k, bytes) and isinstance(v, bytes) for k, v in settings.items()), settings
assert [n for n, _ in problems] == [2, 6, 7], problems
assert parse(b"") == ({}, []), parse(b"")
for hostile in (b"\x00" * 64, b"=" * 4096, b"\xff" * 1024, b"k=" + b"v" * (1 << 20), b"\n" * 10000):
    parse(hostile)
settings, problems = parse("not bytes")
assert settings == {} and problems, (settings, problems)
print("ok")

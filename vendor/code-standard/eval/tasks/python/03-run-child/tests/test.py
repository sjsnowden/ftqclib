"""Goal: run returns output and status for a quick child, and for a slow one reports the deadline as an outcome, having
killed and reaped the child. Method: echo, a failing shell command, and sleep 5 under a 0.5 s deadline."""
import os, sys, time
sys.path.insert(0, os.path.join(os.getcwd(), "src"))
from run import run

r = run(["echo", "hi"], 5)
assert r.returncode == 0 and r.stdout == b"hi\n" and r.timed_out is False, r
r = run(["sh", "-c", "echo err 1>&2; exit 3"], 5)
assert r.returncode == 3 and b"err" in r.stderr and r.timed_out is False, r
t0 = time.monotonic()
r = run(["sleep", "5"], 0.5)
elapsed = time.monotonic() - t0
assert r.timed_out is True, r
assert elapsed < 3, f"took {elapsed:.1f}s: the child was not killed at the deadline"
assert r.returncode is not None, "the child was not reaped"
print("ok")

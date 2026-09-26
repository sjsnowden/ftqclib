import subprocess
from dataclasses import dataclass


@dataclass(frozen=True)
class Result:
    returncode: int | None
    stdout: bytes
    stderr: bytes
    timed_out: bool


def run(command, timeout_s):
    """Run `command` with a deadline. When the deadline passes the child is killed and reaped and `timed_out` says so:
    a deadline reached is an outcome, never an exception. The child has one owner, this function, for its whole life."""
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as child:
        try:
            out, err = child.communicate(timeout=timeout_s)
            return Result(child.returncode, out, err, False)
        except subprocess.TimeoutExpired:
            child.kill()
            out, err = child.communicate(timeout=timeout_s)
            return Result(child.returncode, out, err, True)

import os
import signal
import subprocess
from dataclasses import dataclass


@dataclass
class RunResult:
    returncode: int
    stdout: bytes
    stderr: bytes
    timed_out: bool


def run(command, timeout_s):
    """Run `command`, killing it if it is still running after `timeout_s` seconds.

    Returns a RunResult. On timeout, the child and any processes it started
    are killed and reaped before this returns, and timed_out is True.
    """
    child = subprocess.Popen(
        command,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        out, err = child.communicate(timeout=timeout_s)
        return RunResult(child.returncode, out, err, False)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        out, err = child.communicate(timeout=timeout_s)
        return RunResult(child.returncode, out, err, True)

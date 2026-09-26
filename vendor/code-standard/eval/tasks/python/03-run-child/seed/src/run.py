import subprocess


def run(command):
    """Run `command` and return (returncode, stdout, stderr)."""
    child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = child.communicate()
    return child.returncode, out, err

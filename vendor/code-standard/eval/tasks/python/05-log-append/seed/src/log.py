import json
import shutil


def append(path, entry):
    """Append one entry as a line of JSON."""
    with open(path, "a") as f:
        f.write(json.dumps(entry) + "\n")


def close(path):
    """Mark the log closed."""
    with open(path, "a") as f:
        f.write("closed\n")


def rotate(path, archive):
    """Copy the log to the archive and start again."""
    shutil.copy(path, archive)
    open(path, "w").close()

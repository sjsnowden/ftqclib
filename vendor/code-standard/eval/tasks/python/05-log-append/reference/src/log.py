import json
import os

CLOSED = b"closed\n"


def _fsync_directory(path):
    fd = os.open(os.path.dirname(os.path.abspath(path)), os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _is_closed(path):
    try:
        with open(path, "rb") as f:
            f.seek(0, os.SEEK_END)
            f.seek(max(0, f.tell() - len(CLOSED)))
            return f.read() == CLOSED
    except FileNotFoundError:
        return False


def append(path, entry):
    """Append one JSON entry as a line; (True, None), or (False, reason) once the log is closed."""
    if _is_closed(path):
        return False, "the log is closed"
    with open(path, "ab") as f:
        f.write(json.dumps(entry, sort_keys=True).encode("utf-8") + b"\n")
        f.flush()
        os.fsync(f.fileno())
    return True, None


def close(path):
    """Write the closed mark, after which nothing follows; (False, reason) if already closed."""
    if _is_closed(path):
        return False, "already closed"
    with open(path, "ab") as f:
        f.write(CLOSED)
        f.flush()
        os.fsync(f.fileno())
    return True, None


def rotate(path, archive):
    """Give the log the name `archive`, exclusively, and start a fresh empty log. A link then an unlink is a move that
    can neither overwrite nor lose: the entries have a second name before they lose the first."""
    try:
        os.link(path, archive)
    except FileExistsError:
        return False, "archive exists"
    except FileNotFoundError:
        return False, "no log to rotate"
    os.unlink(path)
    with open(path, "xb"):
        pass
    _fsync_directory(path)
    return True, None

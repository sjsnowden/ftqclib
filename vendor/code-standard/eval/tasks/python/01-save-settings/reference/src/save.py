import json
import os


def save_settings(settings, path):
    """Write `settings` plus a version key to `path`, atomically, and return `path`. The type check comes first, so a
    bad argument leaves no file behind, and the argument itself is not changed."""
    if not isinstance(settings, dict):
        raise ValueError("settings must be a dict")
    data = json.dumps({**settings, "version": 1}, sort_keys=True)
    scratch = path + ".tmp"
    with open(scratch, "w", encoding="utf-8") as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(scratch, path)
    return path


def load_settings(path):
    with open(path) as f:
        return json.loads(f.read())

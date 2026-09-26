import os

DEPTH_MAX_LIMIT = 64


def list_files(root, depth_max):
    """(files, skipped): files are (relative path as bytes, size) for every regular file at most `depth_max`
    directories below `root`, sorted; skipped are the directories that could not be read. Names stay bytes, since they
    are not text; symbolic links are neither followed nor listed; the walk is bounded by an explicit stack and depth."""
    if not isinstance(root, bytes):
        raise TypeError("root must be bytes")
    if not 0 <= depth_max <= DEPTH_MAX_LIMIT:
        raise ValueError(f"depth_max must be between 0 and {DEPTH_MAX_LIMIT}")
    found, skipped = [], []
    stack = [(root, 0)]
    while stack:
        directory, depth = stack.pop()
        try:
            entries = list(os.scandir(directory))
        except OSError:
            skipped.append(os.path.relpath(directory, root))
            continue
        for entry in entries:
            if entry.is_symlink():
                continue
            if entry.is_dir(follow_symlinks=False):
                if depth < depth_max:
                    stack.append((entry.path, depth + 1))
            elif entry.is_file(follow_symlinks=False):
                found.append((os.path.relpath(entry.path, root), entry.stat(follow_symlinks=False).st_size))
    return sorted(found), sorted(skipped)

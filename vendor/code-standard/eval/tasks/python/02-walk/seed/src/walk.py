import os


def list_files(root):
    """Every file under root with its size, as (relative path, size), sorted."""
    found = []
    for directory, _, names in os.walk(root):
        for name in names:
            path = os.path.join(directory, name)
            found.append((os.path.relpath(path, root), os.path.getsize(path)))
    return sorted(found)

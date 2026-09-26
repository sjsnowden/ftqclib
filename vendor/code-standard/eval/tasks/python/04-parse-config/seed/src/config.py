def parse(text):
    """Settings from key=value lines."""
    result = {}
    for line in text.decode("utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        key, value = line.split("=", 1)
        result[key.strip()] = value.strip()
    return result

def parse(data):
    """(settings, problems) from `data`, bytes of key=value lines. Never raises for any input: each line that cannot be
    read is a problem with its line number and reason, and the lines that can be read are still returned. Keys and
    values stay bytes: they came from outside and are not text until something displays them."""
    settings, problems = {}, []
    if not isinstance(data, (bytes, bytearray)):
        return settings, [(0, "input is not bytes")]
    for number, line in enumerate(bytes(data).split(b"\n"), start=1):
        stripped = line.strip()
        if not stripped or stripped.startswith(b"#"):
            continue
        key, separator, value = stripped.partition(b"=")
        if not separator:
            problems.append((number, "no '=' on the line"))
            continue
        key = key.strip()
        if not key:
            problems.append((number, "empty key"))
            continue
        if key in settings:
            problems.append((number, "key given twice"))
            continue
        settings[key] = value.strip()
    return settings, problems

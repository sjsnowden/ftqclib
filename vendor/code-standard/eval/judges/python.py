"""Judges for the `python` module: what conformance looks like in a tree of Python files, read statically with the
`ast` module. Each judge is `NAME(tree, **args) -> bool`, `tree` the directory to read and `args` the task's own
`task.json` naming what used to be hard-coded here (which file, which function, which argument). A judge is a
heuristic named for the requirement it serves: an agent may conform by an idiom it did not anticipate, and then the
judge is revised, never a score. `eval/score.py` imports this module by the `module` a task.json names."""
import ast

# ---- reading a tree (pure functions of its text) ------------------------------------------------------------------

def read_module(tree, relpath):
    """The parsed module at `relpath` under `tree`, or None when it is missing or does not parse."""
    try:
        with open(f"{tree}/{relpath}", "rb") as f: return ast.parse(f.read())
    except (OSError, SyntaxError, ValueError): return None

def find_function(mod, name):
    return next((n for n in ast.walk(mod) if isinstance(n, ast.FunctionDef) and n.name == name), None) if mod else None

def target(tree, file, function=None):
    """(module, function-or-None) at `file` under `tree`, `function` looked up by name when one is given."""
    mod = read_module(tree, file)
    return (mod, find_function(mod, function) if function else None) if mod else (None, None)

def dotted(node):
    """`os.replace` for the callee of a call, `f.write` for an attribute call, `open` for a bare name; else ''."""
    if isinstance(node, ast.Call): node = node.func
    if isinstance(node, ast.Name): return node.id
    if isinstance(node, ast.Attribute): return f"{dotted(node.value)}.{node.attr}" if dotted(node.value) else node.attr
    return ""

def calls(node, *names):
    """Calls under `node` whose dotted callee is one of `names`, or ends with `.name` for a bare `name`."""
    return [c for c in ast.walk(node) if isinstance(c, ast.Call)
            and any(dotted(c) == n or dotted(c).endswith("." + n) for n in names)]

def keyword(call, name):
    return next((k for k in call.keywords if k.arg == name), None)

def open_modes(node):
    """The mode strings given to open(...) under `node`, positional or keyword."""
    modes = []
    for c in calls(node, "open"):
        arg = c.args[1] if len(c.args) > 1 else (keyword(c, "mode").value if keyword(c, "mode") else None)
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str): modes.append(arg.value)
    return modes

def statement_index(fn, predicate):
    """Index of the first top-level statement of `fn` under which `predicate` holds for some node, or None."""
    for i, statement in enumerate(fn.body):
        if any(predicate(n) for n in ast.walk(statement)): return i
    return None

def writes(node):
    return isinstance(node, ast.Call) and (dotted(node) == "open" and any(m[0] in "wxa" for m in open_modes(node))
                                           or dotted(node).endswith(".write"))

def checks_input(node):
    return isinstance(node, ast.Raise) or (isinstance(node, ast.Call) and dotted(node) == "isinstance")

def mutates_name(fn, name):
    """A statement of `fn` that changes the object `name` refers to in place: subscript or attribute assignment,
    augmented assignment, deletion, or a mutating method call."""
    for n in ast.walk(fn):
        targets = []
        if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)): targets = getattr(n, "targets", None) or [n.target]
        if isinstance(n, ast.Delete): targets = n.targets
        for t in targets:
            if isinstance(t, (ast.Subscript, ast.Attribute)) and isinstance(t.value, ast.Name) and t.value.id == name: return True
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name) \
                and n.func.value.id == name and n.func.attr in ("update", "setdefault", "pop", "popitem", "clear", "append", "extend", "insert", "remove"):
            return True
    return False

def bare_except(mod):
    return any(isinstance(n, ast.ExceptHandler) and n.type is None for n in ast.walk(mod))

def arg_names(fn):
    return [a.arg for a in fn.args.args + fn.args.kwonlyargs]

# ---- the checks: NAME(tree, **args) -> True held / False failed ----------------------------------------------------

def effect_after_check(tree, file, function):
    mod, f = target(tree, file, function)
    if f is None: return False
    write, check = statement_index(f, writes), statement_index(f, checks_input)
    return write is not None and check is not None and check < write

def path_is_parameter(tree, file, function, argument="path"):
    mod, f = target(tree, file, function)
    return f is not None and argument in arg_names(f) and not calls(f, "environ.get", "getenv") \
        and not any(isinstance(n, ast.Attribute) and n.attr == "environ" for n in ast.walk(f))

def argument_not_mutated(tree, file, function):
    mod, f = target(tree, file, function)
    return f is not None and bool(arg_names(f)) and not mutates_name(f, arg_names(f)[0])

def atomic_replace(tree, file, function):
    mod, f = target(tree, file, function)
    return f is not None and bool(calls(f, "os.replace", "os.rename")) and bool(calls(f, "os.fsync"))

def depth_bounded(tree, file, function, argument="depth"):
    mod, f = target(tree, file, function)
    names = arg_names(f) if f else []
    return f is not None and any(argument in a for a in names[1:]) and any(isinstance(n, ast.Compare) for n in ast.walk(f))

def symlinks_not_followed(tree, file, function):
    mod, f = target(tree, file, function)
    if f is None: return False
    explicit = any(keyword(c, "follow_symlinks") is not None or keyword(c, "followlinks") is not None
                   for c in ast.walk(f) if isinstance(c, ast.Call))
    return explicit or bool(calls(f, "is_symlink", "os.lstat", "islink"))

def names_stay_bytes(tree, file, function):
    mod, f = target(tree, file, function)
    return f is not None and not calls(f, "decode") and not calls(f, "fsdecode")

def no_bare_except(tree, file):
    mod = read_module(tree, file)
    return mod is not None and not bare_except(mod)

def timeouts(tree, file, function):
    mod, f = target(tree, file, function)
    if f is None: return False
    waits = calls(f, "communicate", "wait", "subprocess.run", "run", "check_output", "check_call", "call")
    waits = [c for c in waits if dotted(c) not in ("run",)]      # `run` alone is this function's own name
    return bool(waits) and all(keyword(c, "timeout") is not None for c in waits)

def timeout_handled(tree, file, function):
    mod, f = target(tree, file, function)
    if f is None: return False
    for h in (n for n in ast.walk(f) if isinstance(n, ast.ExceptHandler)):
        if h.type is not None and dotted(h.type).endswith("TimeoutExpired") \
                and calls(h, "kill", "terminate", "killpg") and calls(h, "wait", "communicate"): return True
    return False

def popen_owned(tree, file, function):
    """The child is waited for on every path: `with Popen`, or a try whose body waits and whose every handler (or
    whose finally) waits too. Eval 001's pilot: four of four agents wrote the try form, and the check knew only the
    `with`; the requirement (8.4) is the wait on every path, not the spelling."""
    mod, f = target(tree, file, function)
    if f is None: return False
    if any(isinstance(n, ast.With) and any(dotted(i.context_expr).endswith("Popen") for i in n.items) for n in ast.walk(f)): return True
    waits = lambda nodes: any(calls(n, "wait", "communicate") for n in nodes)
    return any(waits(t.body) and (waits(t.finalbody) or (t.handlers and all(waits([h]) for h in t.handlers)))
               for t in ast.walk(f) if isinstance(t, ast.Try))

def never_raises(tree, file, function):
    mod, f = target(tree, file, function)
    if f is None: return False
    if any(isinstance(n, ast.Raise) for n in ast.walk(f)): return False
    guarded = {id(c) for t in ast.walk(f) if isinstance(t, ast.Try) and t.handlers for c in calls(ast.Module(body=t.body, type_ignores=[]), "decode")}
    # a decode without errors= is fine inside a try that handles it (eval 003: one agent decoded that way and never raised)
    return all(keyword(c, "errors") is not None or len(c.args) > 1 or id(c) in guarded for c in calls(f, "decode"))

def problems_reported(tree, file, function):
    mod, f = target(tree, file, function)
    if f is None: return False
    returns = [n for n in ast.walk(f) if isinstance(n, ast.Return)]
    return bool(returns) and all(isinstance(r.value, ast.Tuple) and len(r.value.elts) == 2 for r in returns)

def exclusive_create(tree, file):
    m = read_module(tree, file)
    if m is None: return False
    return any(mode.startswith("x") for mode in open_modes(m)) \
        or any(isinstance(n, ast.Attribute) and n.attr == "O_EXCL" for n in ast.walk(m)) or bool(calls(m, "os.link"))

def rename_not_copy(tree, file, function):
    mod, f = target(tree, file, function)
    return f is not None and bool(calls(f, "os.replace", "os.rename", "os.link")) \
        and not calls(f, "copy", "copyfile", "copy2", "copyfileobj")

def fsync(tree, file):
    m = read_module(tree, file)
    return m is not None and bool(calls(m, "os.fsync"))

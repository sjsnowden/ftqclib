# Module — Python

What the standard's requirements mean in Python. Each item names the requirement it serves.

- 5.2: list directories with a `bytes` path and keep names as `bytes`; decode only for display, with
  `errors="surrogateescape"` [PEP383 L66–77] or `"replace"`, never for sorting or equality.
- 6.2: write to a temporary file in the same directory, `flush()`, `os.fsync()`, `os.replace()`, then open the directory
  and `os.fsync()` it.
- RK.3: files holding facts are opened with mode `"x"` or `"xb"`.
- 6.3: `now` and a random source are parameters, with defaults only at the program's edge; callers pass them.
- 7.1: a derivation module does not import `time`, `random` or `subprocess`, and does not call `print` or open for
  writing.
- 8.4: `asyncio.TaskGroup` for tasks; `with subprocess.Popen(...)` and `wait(timeout=...)`, then `kill()` and `wait()` at
  the deadline; a `daemon=True` thread only with a timed `join()` and the outcome recorded.
- 8.6: every `subprocess.run`, `.wait` and `.communicate` has `timeout=`.
- 9.1: `assert` is removed under `python -O`; anything that must hold in production is `if not condition: raise
  SomeError("what was expected")`, and `assert` is for tests. No bare `except:`. `except Exception` only where every
  possible failure has the same correct response, with a comment saying so. A named exception is caught where the
  operation was started.
- 9.4: never return a fabricated value in place of a reading that failed; return `None` and render it as `unknown` at the
  edge.
- 10.1: every tree walk takes a depth argument and refuses beyond a named limit, or uses an explicit stack.
- 10.9: the standard library only unless the binding records a reason; a new import is a decision to record.
- Resource lifetime: `with` for anything that must be closed or removed.
- Naming: `snake_case`; acronyms lowercase in identifiers; no single letters outside comprehensions and loop indices.
  Rounding: `//`, `divmod` or an explicit `round()`. `def` rather than an assigned `lambda`.
- Line length: 100 columns in files brought to it; the binding keeps the list.

<!-- brief: Python -->
Names as `bytes`; facts opened with `"x"`; atomic replace by `os.replace` and `os.fsync`; `timeout=` on every subprocess
call; `if not condition: raise`, not `assert`, where it must hold in production; no bare `except:`; `asyncio.TaskGroup`;
`with` for resources; the standard library unless the binding records a reason.
<!-- /brief -->

#!/usr/bin/env python3
"""Scorers for the eval tasks: what conformance looks like in a tree of files, and how a breach is seen (4.5).

Task-agnostic: `tasks()` walks `eval/tasks/*/*/task.json`; `score(task, tree)` loads that file, runs the task's
`test` command in a temporary copy of `tree` (under a deadline), imports `eval/judges/<module>.py` and calls
`judge(tree, **args)` for each check the task names. Nothing here needs a model: a rig applies this to the recorded
final state of a run. `score` refuses a task whose `task.json` is not canonical, names a judge its module lacks, or
names a clause that is not valid (STANDARD.md's requirements, or a model clause of 4.1-4.8): the message says which,
and the CLI exits 2. `score.py tasks` lists the tasks and their checks."""
import glob, importlib.util, json, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
OBJECT = os.path.dirname(HERE)
TASKS = os.path.join(HERE, "tasks")
JUDGES = os.path.join(HERE, "judges")
TEST_TIMEOUT_S = 60

sys.path.insert(0, os.path.join(OBJECT, "tools"))
import standard as S

# ---- tasks: task.json is the only source of what a task checks ---------------------------------------------------

def tasks():
    """Task ids (`module/name`) for every `eval/tasks/*/*/task.json`, sorted."""
    paths = sorted(glob.glob(os.path.join(TASKS, "*", "*", "task.json")))
    return [os.path.relpath(os.path.dirname(p), TASKS).replace(os.sep, "/") for p in paths]

def load_task(task):
    """(data, raw bytes) for a task's task.json, parsed but not yet validated."""
    path = os.path.join(TASKS, task, "task.json")
    raw = S.read(path)
    return json.loads(raw), raw

def load_judges(module_name):
    """The judges module named `module_name` under `eval/judges/`, imported by path."""
    path = os.path.join(JUDGES, f"{module_name}.py")
    if not os.path.exists(path): raise ValueError(f"no judges module {module_name!r}")
    spec = importlib.util.spec_from_file_location(f"code_standard_judges_{module_name}", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def validate_task(task, data, raw):
    """Raise ValueError, with a message naming the task, when task.json is not canonical or names an unknown judge
    or an invalid clause."""
    if S.canonical_json(data) != raw: raise ValueError(f"{task}: task.json is not canonical")
    judges = load_judges(data["module"])
    texts = [S.read(p) for p in S.object_documents(OBJECT)]
    for c in data["checks"]:
        if not hasattr(judges, c["judge"]): raise ValueError(f"{task}: judge {c['judge']!r} is not in module {data['module']!r}")
        if not S.valid_clause(c["clause"], texts): raise ValueError(f"{task}: clause {c['clause']!r} is not valid")

# ---- the functional test, and the score ---------------------------------------------------------------------------

def functional(task, tree, test_command):
    """(passed, output): the task's hidden test run in a temporary copy of `tree`, under a deadline. A crash or a
    deadline is a failure with its output, never an exception here."""
    with tempfile.TemporaryDirectory() as scratch:
        copy = os.path.join(scratch, "tree"); shutil.copytree(tree, copy, symlinks=True)
        tests_dir = os.path.join(TASKS, task, "tests")
        if os.path.isdir(tests_dir): shutil.copytree(tests_dir, os.path.join(copy, "tests"), dirs_exist_ok=True)
        try:
            r = subprocess.run(test_command, cwd=copy, capture_output=True, text=True,
                               timeout=TEST_TIMEOUT_S, errors="replace")
        except subprocess.TimeoutExpired as e:
            return False, f"deadline of {TEST_TIMEOUT_S}s reached; output so far: {(e.stdout or b'')[-500:]}"
        return r.returncode == 0, (r.stdout + r.stderr)[-2000:]

def score(task, tree):
    """The task's score against `tree`: functional pass and each named check held or not, as a dict. Raises
    ValueError (see `validate_task`) instead of scoring a task.json that is not trustworthy."""
    data, raw = load_task(task)
    validate_task(task, data, raw)
    judges = load_judges(data["module"])
    passed, output = functional(task, tree, data["test"])
    held = {c["name"]: bool(getattr(judges, c["judge"])(tree, **c["args"])) for c in data["checks"]}
    return {"task": task, "tree": os.path.abspath(tree), "module": data["module"], "functional": passed,
            "functional_output": output.strip(), "checks": held, "held": sum(held.values()), "of": len(held),
            "requirements": {c["name"]: c["clause"] for c in data["checks"]}}

def main(argv):
    if argv[:1] == ["tasks"]:
        for task in tasks():
            data, _ = load_task(task)
            print(task, " ".join(f"{c['name']}({c['clause']})" for c in data["checks"]))
        return 0
    if argv[:1] == ["score"] and len(argv) == 3:
        task, tree = argv[1], argv[2]
        if task not in tasks(): print(f"no task {task}"); return 2
        try:
            result = score(task, tree)
        except ValueError as error:
            print(f"refused: {error}"); return 2
        print(json.dumps(result, indent=1)); return 0 if result["functional"] else 1
    print(__doc__); return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

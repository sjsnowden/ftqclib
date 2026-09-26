#!/usr/bin/env python3
"""Controls for the eval scorers (STANDARD.md 13.6): every check must be seen to fail on something and to hold on the
reference; the reference must pass its functional test and the seed must fail it. No task-specific data lives here:
each task names its own `planted` checks and `mutants` in its `task.json`.

Method: score each task's seed and reference as they are; for a check the seed does not violate, apply the task's
aimed mutant (a string replacement, each changing one thing) and require that check alone to fail. A check covered
neither by the seed nor by a mutant is reported: it has never been seen to fail, so its holding means nothing.
One further control has no task: a task.json naming a judge that does not exist is refused by `score`."""
import json, os, shutil, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import score as S
standard = S.S

def main():
    results = []
    def expect(name, held, detail=""):
        results.append(held); print(f"{'held   ' if held else 'FAILED '} {name}" + ("" if held else f": {detail}"))

    covered = {}
    for task in S.tasks():
        data, _ = S.load_task(task)
        planted = set(data["planted"])
        covered[task] = set(planted)
        base = os.path.join(S.TASKS, task)

        reference = S.score(task, os.path.join(base, "reference"))
        expect(f"{task}: the reference passes its functional test", reference["functional"], reference["functional_output"][-300:])
        expect(f"{task}: the reference holds every check", all(reference["checks"].values()), str(reference["checks"]))

        seed = S.score(task, os.path.join(base, "seed"))
        expect(f"{task}: the seed fails its functional test", not seed["functional"])
        failed = {name for name, held in seed["checks"].items() if not held}
        expect(f"{task}: the seed fails every planted check", planted <= failed, f"planted {sorted(planted)}, failed {sorted(failed)}")

        idioms = os.path.join(base, "idioms")
        for name in (sorted(os.listdir(idioms)) if os.path.isdir(idioms) else []):
            # A second conforming solution, written by someone else (the first came from eval 001's pilot): the checks must
            # hold on it as on the reference, or they measure the reference's spelling and not the requirement.
            other = S.score(task, os.path.join(idioms, name))
            expect(f"{task}: idiom {name} passes its functional test", other["functional"], other["functional_output"][-300:])
            expect(f"{task}: idiom {name} holds every check", all(other["checks"].values()), str(other["checks"]))

        judges = S.load_judges(data["module"])
        for m in data["mutants"]:
            with tempfile.TemporaryDirectory() as scratch:
                tree = os.path.join(scratch, "tree"); shutil.copytree(os.path.join(base, "reference"), tree)
                source_path = os.path.join(tree, m["file"])
                source = open(source_path, encoding="utf-8").read()
                if source.count(m["old"]) != 1:
                    expect(f"{task}: mutant for {m['check']} applies", False, f"anchor found {source.count(m['old'])} times"); continue
                open(source_path, "w", encoding="utf-8").write(source.replace(m["old"], m["new"]))
                held = {c["name"]: bool(getattr(judges, c["judge"])(tree, **c["args"])) for c in data["checks"]}
                expect(f"{task}: mutant makes {m['check']} fail and nothing else",
                       held[m["check"]] is False and all(v for n, v in held.items() if n != m["check"]), str(held))
                covered[task].add(m["check"])

    for task in S.tasks():
        data, _ = S.load_task(task)
        never = {c["name"] for c in data["checks"]} - covered[task]
        expect(f"{task}: every check has been seen to fail", not never, f"never seen failing: {sorted(never)}")

    with tempfile.TemporaryDirectory() as scratch:
        root = os.path.join(scratch, "broken")
        shutil.copytree(S.OBJECT, root, ignore=shutil.ignore_patterns(".git", "__pycache__"))
        task = S.tasks()[0]
        task_json = os.path.join(root, "eval", "tasks", task, "task.json")
        with open(task_json, encoding="utf-8") as f: data = json.load(f)
        data["checks"][0]["judge"] = "no_such_judge"
        with open(task_json, "w", encoding="utf-8") as f: f.write(standard.canonical_json(data))
        result = subprocess.run([sys.executable, os.path.join(root, "eval", "score.py"), "score", task,
                                  os.path.join(root, "eval", "tasks", task, "reference")],
                                 capture_output=True, text=True, timeout=120)
        expect("a task naming a missing judge is refused by score", result.returncode == 2, result.stdout + result.stderr)

    print(f"eval controls: {sum(results)} of {len(results)} held")
    return 0 if all(results) else 1

if __name__ == "__main__":
    sys.exit(main())

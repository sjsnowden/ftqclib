"""A sequential ftqclib development comparison. Records own state; worker output never chooses checks.

Preparation, model-free controls, model execution and reporting are separate commands. This concrete domain
driver reuses OntolKernel's store, invocation adapter and protected checker. It is not a second workflow ISA.
"""
import argparse
import base64
import contextlib
import datetime
import fcntl
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import uuid

import fixtures
import runtime as runtime_tools


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def kernel_imports(path):
    for child in ("kernel", "run"):
        sys.path.insert(0, str(Path(path) / child))
    import eval_check
    import eval_session
    from store import Store
    return Store, eval_check, eval_session


def git(root, *arguments):
    command = ["git", "-c", "user.name=Ontologic study", "-c", "user.email=study@localhost",
               "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "-C", str(root), *arguments]
    outcome = subprocess.run(command, capture_output=True, timeout=180)
    if outcome.returncode:
        raise ValueError(outcome.stderr.decode(errors="replace")[-3000:])
    return outcome.stdout


def write_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())


def event(store, study, kind, **fields):
    stamp = datetime.datetime.now(datetime.timezone.utc).isoformat()
    return store.append(kind, stamp, study=study, **fields)


@contextlib.contextmanager
def admission_lock(root):
    """One live owner holds the entire worker/capture/check cycle; OS releases the lock after a crash."""
    with (root / "owner.lock").open("a") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("another study owner is active; trials are sequential") from error
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def slots(tasks, repetitions):
    """Rotate arm order across case/repetition blocks; opaque storage identities disclose no condition."""
    result = []
    for repetition in range(1, repetitions + 1):
        for index, task in enumerate(tasks):
            offset = (index + repetition - 1) % 3
            order = "ABC"[offset:] + "ABC"[:offset]
            for condition in order:
                result.append({"id": uuid.uuid4().hex, "task": task, "condition": condition,
                               "repetition": repetition})
    return result


def selected_slots(repetitions, selection=None):
    """Pin an explicitly requested task/arm/repetition, or the complete comparison order."""
    declared = slots(["F01", "F02"], repetitions)
    if selection is None:
        return declared
    if not re.fullmatch(r"F0[12]:[ABC]:[1-3]", selection):
        raise ValueError("slot selection must be TASK:CONDITION:REPETITION, e.g. F01:B:1")
    task, condition, repetition = selection.split(":")
    chosen = [slot for slot in declared if (slot["task"], slot["condition"], slot["repetition"])
              == (task, condition, int(repetition))]
    if len(chosen) != 1:
        raise ValueError("selected repetition exceeds the declared repetitions")
    return chosen


def render(contract, condition):
    """Same public contract in all arms; B surfaces its structure, C removes presentation padding."""
    public = {key: contract[key] for key in ("purpose", "obligation", "evidence", "acceptance",
                                           "completion", "writes", "standards")}
    common = ("\nThe full public contract is .task/contract.json. Run python3 .task/check.py for identical "
              "public self-checks. Build products belong only under .scratch. If blocked, report the exact "
              "missing prerequisite; do not invent success. Stop after your one submitted candidate.\n")
    if condition == "A":
        return (contract["obligation"] + "\nFollow the requirements and evidence in .task/contract.json. "
                "Make the required source repair and check it." + common).encode()
    if condition == "B":
        body = "\n\n".join(key.upper() + "\n" + ("\n".join(value) if isinstance(value, list) else value)
                             for key, value in public.items())
    elif condition == "C":
        body = "\n".join("\n".join(value) if isinstance(value, list) else value for value in public.values())
    else:
        raise ValueError("unknown prompt condition")
    return (body + common).encode()


def owner_projection(source, destination, task, control="seed"):
    value = fixtures.prepare(task, source, destination, control=control)
    if value["status"] != "prepared":
        raise ValueError("fixture preparation failed: " + json.dumps(value))
    return value


def seed_commit(repo, task, base, projection, destination):
    git(repo, "worktree", "add", "--detach", str(destination), base)
    # This is a fresh owner worktree inside the study. Remove only its explicitly tracked names.
    for raw in git(destination, "ls-files", "-z").split(b"\0"):
        if raw:
            relative = Path(raw.decode())
            target = destination / relative
            if relative.is_absolute() or ".." in relative.parts or destination not in target.resolve().parents:
                raise ValueError("tracked path escapes seed worktree")
            target.unlink()
    shutil.copytree(projection, destination, dirs_exist_ok=True)
    git(destination, "add", "-A")
    git(destination, "commit", "-q", "-m", "Freeze " + task + " evaluation seed")
    return git(destination, "rev-parse", "HEAD").decode().strip()


def source_objects(store, kernel):
    paths = [*Path(__file__).parent.glob("*.py"), *Path(__file__).parent.glob("tasks/*/*")]
    paths += list((kernel / "kernel").glob("*.py")) + list((kernel / "run").glob("*.py"))
    return {str(path.resolve()): store.put(path.read_bytes()) for path in sorted(paths) if path.is_file()}


def prepare(args):
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,100}", args.id):
        raise ValueError("study id must be a bounded safe identifier")
    if not 0 < args.deadline_seconds <= 3600 or not 0 < args.token_limit <= 10000000:
        raise ValueError("positive bounded deadline and aggregate token admission limit required")
    if args.provider == "codex" and args.budget_usd is not None:
        raise ValueError("Codex has no per-invocation dollar limit; omit budget-usd")
    if args.provider == "claude" and (args.budget_usd is None or not 0 < args.budget_usd <= 100):
        raise ValueError("Claude requires an explicit positive invocation dollar ceiling <=100")
    if any(not value or value.startswith("-") or len(value) > 200 for value in (args.model, args.effort)):
        raise ValueError("explicit bounded model and effort identifiers required")
    declared = selected_slots(args.repetitions, getattr(args, "slot", None))
    root, source, kernel = args.study.resolve(), args.source.resolve(), args.kernel.resolve()
    root.mkdir(parents=True, exist_ok=False)
    (root / "owner").mkdir()
    Store, _, _ = kernel_imports(kernel)
    store = Store(str(root / "records"))
    repo, reference = root / "owner/repo.git", root / "owner/reference"
    git(source, "clone", "--quiet", "--bare", "--no-local", str(source), str(repo))
    git(repo, "worktree", "add", "--detach", str(reference), fixtures.REVISION)
    task_rows, runtime_cache = {}, {}
    for task in sorted({slot["task"] for slot in declared}):
        seed = root / "owner/seeds" / task
        original = root / "owner/references" / task
        spec = owner_projection(reference, seed, task)
        owner_projection(reference, original, task, "reference")
        runtime = runtime_tools.prepare(task, args.runtime.resolve() / "reference", args.runtime.resolve(), spec,
                                        cache=runtime_cache)
        for name, data in runtime_tools.public_files(task, spec["contract"], runtime).items():
            write_new(seed / name, data)
            write_new(original / name, data)
        commit = seed_commit(repo, task, fixtures.REVISION, seed, root / "owner/seed-worktrees" / task)
        task_rows[task] = {"contract": spec["contract"], "seed": str(seed), "reference": str(original),
                           "seed_commit": commit, "seed_sha256": fixtures.tree_digest(fixtures.tree_files(seed)),
                           "runtime": runtime}
    manifest = {"schema": 1, "id": args.id, "source_commit": fixtures.REVISION, "kernel": str(kernel),
                "runtime": str(args.runtime.resolve()), "tasks": task_rows,
                "slots": declared, "sources": source_objects(store, kernel),
                "execution": {"provider": args.provider, "executable": args.executable, "model": args.model,
                              "effort": args.effort, "deadline_seconds": args.deadline_seconds,
                              "budget_usd": args.budget_usd, "observed_token_limit": args.token_limit},
                "policy": {"concurrency": 1, "outer_quality_retries": 0, "unknown_usage_stops_admission": True,
                           "token_limit": "soft admission threshold; one in-flight invocation can overshoot",
                           "split": "development", "condition_A": "constructed incumbent-style baseline"}}
    write_new(root / "manifest.json", canonical(manifest))
    identity = store.put(canonical(manifest))
    write_new(root / "manifest.ref", identity.encode())
    event(store, args.id, "study_pin", manifest=identity)
    event(store, args.id, "stage", name="prepared", detail="Awaiting reference and fixture controls; no workers launched")
    print(json.dumps({"study": str(root), "manifest": identity, "slots": len(manifest["slots"])}))


def load(root):
    manifest = json.loads((root / "manifest.json").read_bytes())
    Store, checker, adapter = kernel_imports(manifest["kernel"])
    store = Store(str(root / "records"))
    if store.get((root / "manifest.ref").read_text()) != canonical(manifest):
        raise ValueError("study manifest changed after preparation")
    return manifest, store, checker, adapter


def verify_sources(manifest):
    for filename, expected in manifest["sources"].items():
        if digest(Path(filename).read_bytes()) != expected:
            raise ValueError("implementation changed after study preparation: " + filename)


def report(manifest, entries):
    rows, known_tokens, unknown_tokens = [], 0, 0
    for slot in manifest["slots"]:
        history = [entry for entry in entries if entry.get("slot") == slot["id"]]
        endings = [entry for entry in history if entry["kind"] == "trial_end"]
        if len(endings) > 1:
            raise ValueError("conflicting trial closures")
        outcome = endings[0]["result"] if endings else {"execution": "unfinished" if history else "not_run",
                                                        "assessment": "unresolved", "tokens": None, "cost_usd": None}
        if history:
            if outcome["tokens"] is None:
                unknown_tokens += 1
            else:
                known_tokens += outcome["tokens"]
        rows.append({**slot, **outcome})
    return {"study": manifest["id"], "slots": rows, "known_tokens": known_tokens,
            "unknown_token_invocations": unknown_tokens, "complete": all(row["execution"] not in
            ("not_run", "unfinished") for row in rows), "scope": "development canaries; no population-wide comparison claim"}


def retain_tree(store, directory):
    """The owner archives source bytes before any disposable tree can be discarded."""
    files = fixtures.tree_files(directory)
    return store.put(canonical({name: store.put(data) for name, data in sorted(files.items())}))


def check_candidate(root, manifest, store, checker, task, candidate, identity, runtime_cache):
    row = manifest["tasks"][task]
    result = fixtures.assess(task, row["reference"], candidate)
    retained = retain_tree(store, candidate)
    if not result.get("admitted"):
        return {**result, "source_object": retained}
    selected = row["runtime"]
    runtime_tools.verify(selected, cache=runtime_cache)
    candidate.joinpath(".scratch").mkdir(exist_ok=True)
    build = root / "checks" / identity
    build.mkdir(parents=True, exist_ok=False)
    # Lean resolves a package from one search root; its private output root must
    # also contain the audited, unaffected ancestors of rebuilt local modules.
    runtime_tools.seed_build(selected, build / "build")
    reads = [(selected["toolchain"], "/toolchain")]
    reads += [(path, "/deps/" + str(i)) for i, path in enumerate(selected["lean_path"])]
    examiner = fixtures.ROOT / row["contract"]["examiner"]
    reads.append((str(examiner.parent), "/verifier"))
    environment = {"LEAN_PATH": "/work/.scratch/build:" + ":".join("/deps/" + str(i)
                   for i in range(len(selected["lean_path"]))), "LEAN_NUM_THREADS": "2"}
    receipts = {}
    commands = selected["checks"] + [check for check in fixtures.check_commands(task) if check["id"] == "examiner"]
    for check in commands:
        actual = ["/toolchain/bin/lean", "-j2", "-M4096", *check["command"][1:]]
        if check["id"] == "examiner":
            actual[-1] = "/verifier/" + examiner.name
        if "-o" in actual:
            (build / actual[actual.index("-o") + 1].removeprefix(".scratch/")).parent.mkdir(parents=True, exist_ok=True)
        observation = checker.run(str(candidate), actual, store, identity + "-" + check["id"],
                                  readonly=reads, writable=[(str(build), "/work/.scratch")],
                                  environment=environment, deadline_seconds=180, memory_bytes=8589934592,
                                  processes_max=512)
        receipt = {"source_sha256": result["source_sha256"], "command": check["command"],
                   "actual_command": actual, "status": "finished" if observation["status"] in
                   ("completed", "failed") else observation["status"], "returncode": observation["exit"],
                   "observation": observation["receipt"]}
        receipts[check["id"]] = receipt
        if observation["status"] != "completed":
            break
    return {**fixtures.assess(task, row["reference"], candidate, compiler_results=receipts),
            "source_object": retained, "checks": receipts}


def controls(root, manifest, store, checker):
    if any(e["kind"] == "controls_end" for e in store.entries()):
        raise ValueError("controls already attempted; retain their outcome and prepare a new study to change them")
    reference = root / "owner/reference"
    outcomes, runtime_cache = [], {}
    definitions = {"F01": ["reference", "alternate", "unfinished", "added-axiom", "weakened-statement", "changed-definition", "unstable-simp"],
                   "F02": ["reference", "alternate", "seed", "module-deletion", "omitted-import"]}
    definitions = {task: names for task, names in definitions.items() if task in manifest["tasks"]}
    for task, names in definitions.items():
        selected = manifest["tasks"][task]
        for control in names:
            identity = task + "-" + control
            event(store, manifest["id"], "stage", name="controls", detail=identity)
            destination = root / "owner/controls" / identity
            owner_projection(reference, destination, task, control)
            for name, data in runtime_tools.public_files(task, selected["contract"], selected["runtime"]).items():
                write_new(destination / name, data)
            assessment = check_candidate(root, manifest, store, checker, task, destination, identity, runtime_cache)
            positive = control in ("reference", "alternate")
            correct = control_outcome(task, control, assessment, store)
            outcome = {"task": task, "control": control, "expected": "accepted" if positive else "rejected",
                       "correct": correct, "assessment": store.put(canonical(assessment)),
                       "status": assessment["status"], "reason": assessment.get("reason", assessment.get("reasons"))}
            outcomes.append(outcome)
            event(store, manifest["id"], "control_end", result=outcome)
            print(json.dumps(outcome), flush=True)
            if positive and not correct:
                break
    passed = all(row["correct"] for row in outcomes) and len(outcomes) == sum(map(len, definitions.values()))
    event(store, manifest["id"], "controls_end", passed=passed, outcomes=store.put(canonical(outcomes)))
    event(store, manifest["id"], "stage", name="ready" if passed else "blocked",
          detail="Model-free controls passed" if passed else "Fixture controls require repair; no model admissions")
    return passed


def control_outcome(task, control, assessment, store):
    """A negative control must fail for its intended reason, not merely produce a nonzero process exit."""
    if control in ("reference", "alternate"):
        return assessment.get("accepted", False)
    if control == "unstable-simp":
        return assessment["status"] == "refused" and any(
            "simp stability:" in reason for reason in assessment.get("reasons", []))
    if control not in ("unfinished", "seed"):
        return assessment["status"] == "refused" and bool(assessment.get("reasons"))
    if task == "F02" and control == "seed" and assessment["status"] == "refused":
        reasons = assessment.get("reasons", [])
        return all(any(reason.startswith(f"F02 declaration home: {name} must have exactly one declaration site in ")
                       for reason in reasons) for name in ("signOf_zero", "signOf_one"))
    if assessment["status"] != "failed":
        return False
    observations = []
    for check in assessment.get("checks", {}).values():
        receipt = json.loads(store.get(check["observation"]))
        for raw in store.get(receipt["capture"]).splitlines():
            row = json.loads(raw)
            if row["kind"] == "bytes":
                observations.append(base64.b64decode(row["data_base64"]))
    output = b"".join(observations).decode("utf-8", "replace")
    if task == "F01":
        return "sorryAx" in output
    checks = assessment.get("checks", {})
    individual = [value for name, value in checks.items() if name != "examiner"]
    return (assessment.get("reason") == "owner check failed: examiner" and all(row["returncode"] == 0
            for row in individual) and "F02 declaration home:" in output)


def execution_refusal(manifest, entries):
    controls = [entry for entry in entries if entry["kind"] == "controls_end"]
    if len(controls) != 1 or not controls[0]["passed"]:
        return "controls have not passed"
    starts = {e["slot"] for e in entries if e["kind"] == "trial_start"}
    ends = {e["slot"] for e in entries if e["kind"] == "trial_end"}
    if starts - ends:
        return "an earlier invocation is unclosed; investigate before admitting more work"
    if any(e["kind"] == "trial_end" and e["result"]["assessment"] == "unresolved" for e in entries):
        return "an unresolved invocation or check requires a new reviewed study before further admissions"
    projection = report(manifest, entries)
    if projection["unknown_token_invocations"]:
        return "a launched invocation has unknown token usage"
    if projection["known_tokens"] >= manifest["execution"]["observed_token_limit"]:
        return "observed token admission limit reached"
    return None


def run_trial(root, manifest, store, checker, adapter, slot, runtime_cache):
    identity, task = slot["id"], slot["task"]
    selected = manifest["tasks"][task]
    runtime_tools.verify(selected["runtime"], cache=runtime_cache)
    trial = root / "trials" / identity
    trial.mkdir(parents=True, exist_ok=False)
    worktree = trial / "worktree"
    git(root / "owner/repo.git", "worktree", "add", "--detach", str(worktree), selected["seed_commit"])
    projection = trial / "input"
    shutil.copytree(worktree, projection, ignore=shutil.ignore_patterns(".git"))
    if fixtures.tree_digest(fixtures.tree_files(projection)) != selected["seed_sha256"]:
        raise ValueError("trial worktree does not reproduce its frozen source seed")
    write_new(trial / "prompt.txt", render(selected["contract"], slot["condition"]))
    writes = [fixtures.Z_SHEAR] if task == "F01" else [fixtures.PAIRING, fixtures.RESIDUAL, fixtures.AMPLITUDE]
    session = {"schema": 1, "id": identity, "prompt": "prompt.txt", "seed": "input",
               "store": str(root / "worker-records"), "writes": writes, "frozen": [".task/**"],
               **{key: value for key, value in manifest["execution"].items() if key != "observed_token_limit"},
               "readable": selected["runtime"]["readable"],
               "readable_provenance": selected["runtime"]["readable_provenance"]}
    write_new(trial / "session.json", canonical(session))
    event(store, manifest["id"], "trial_start", slot=identity, session=store.put(canonical(session)))
    outcome = adapter.run_session(str(trial / "session.json"))
    event(store, manifest["id"], "trial_worker", slot=identity, invocation=outcome.get("invocation"),
          result=store.put(canonical(outcome)))
    assessment = {"status": "needs-checks", "accepted": False, "reason": "worker did not finish with an admitted candidate"}
    if outcome.get("finished") and outcome["status"] == "refused":
        assessment = {"status": "refused", "accepted": False, "reason": outcome.get("reason")}
    if outcome["status"] == "candidate":
        candidate = trial / "candidate"
        adapter.materialise_candidate(str(root / "worker-records"), outcome, str(candidate))
        event(store, manifest["id"], "trial_check", slot=identity, phase="started")
        assessment = check_candidate(root, manifest, store, checker, task, candidate, identity, runtime_cache)
    accepted = assessment.get("accepted", False)
    judgment = "accepted" if accepted else "rejected" if assessment["status"] in ("refused", "failed") else "unresolved"
    result = {"execution": outcome["status"], "assessment": judgment, "tokens": outcome.get("tokens"),
              "cost_usd": outcome.get("cost_usd"), "usage": outcome.get("usage"),
              "invocation": outcome.get("invocation"), "assessment_object": store.put(canonical(assessment))}
    if outcome["status"] == "candidate":
        for name in writes:
            if (candidate / name).is_file():
                shutil.copyfile(candidate / name, worktree / name)
            else:
                (worktree / name).unlink(missing_ok=True)
        git(worktree, "add", "--", *writes)
        git(worktree, "commit", "--allow-empty", "-q", "-m", "Captured candidate: " + judgment)
        result["checkpoint"] = git(worktree, "rev-parse", "HEAD").decode().strip()
    event(store, manifest["id"], "trial_end", slot=identity, result=result)
    return result


def run(root, manifest, store, checker, adapter):
    runtime_cache = {}
    for slot in manifest["slots"]:
        entries = store.entries()
        if any(e["kind"] == "trial_end" and e["slot"] == slot["id"] for e in entries):
            continue
        refusal = execution_refusal(manifest, entries)
        if refusal:
            event(store, manifest["id"], "stage", name="stopped", detail=refusal)
            print(json.dumps({"status": "stopped", "reason": refusal}), flush=True)
            return 2
        verify_sources(manifest)
        result = run_trial(root, manifest, store, checker, adapter, slot, runtime_cache)
        print(json.dumps({"slot": slot["id"], **result}), flush=True)
        if result["assessment"] == "unresolved":
            event(store, manifest["id"], "stage", name="stopped", detail="Unresolved invocation/check; investigate before continuation")
            return 2
    projection = report(manifest, store.entries())
    event(store, manifest["id"], "study_end", report=store.put(canonical(projection)))
    print(json.dumps(projection, indent=2))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    create = sub.add_parser("prepare")
    for name in ("source", "study", "kernel", "runtime"):
        create.add_argument("--" + name, required=True, type=Path)
    create.add_argument("--id", required=True)
    create.add_argument("--provider", choices=("codex", "claude"), default="codex")
    create.add_argument("--executable", required=True)
    create.add_argument("--model", default="gpt-5.6-luna")
    create.add_argument("--effort", default="medium")
    create.add_argument("--repetitions", type=int, choices=range(1, 4), default=2)
    create.add_argument("--slot", help="Prepare only TASK:CONDITION:REPETITION, e.g. F01:B:1")
    create.add_argument("--deadline-seconds", type=int, default=300)
    create.add_argument("--token-limit", type=int, default=150000)
    create.add_argument("--budget-usd", type=float)
    for name in ("report", "controls", "run"):
        item = sub.add_parser(name)
        item.add_argument("study", type=Path)
    args = parser.parse_args()
    if args.command == "prepare":
        return prepare(args)
    root = args.study.resolve()
    manifest, store, checker, adapter = load(root)
    if args.command == "report":
        print(json.dumps(report(manifest, store.entries()), indent=2))
        return
    with admission_lock(root):
        verify_sources(manifest)
        try:
            if args.command == "controls":
                if not controls(root, manifest, store, checker):
                    return 2
            else:
                return run(root, manifest, store, checker, adapter)
        except Exception as error:
            event(store, manifest["id"], "stage", name="blocked", detail=type(error).__name__ + ": " + str(error)[:1200])
            raise


if __name__ == "__main__":
    raise SystemExit(main())

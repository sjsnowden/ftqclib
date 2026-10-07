#!/usr/bin/env python3
"""Prepare, control, run and verify a real dependent ftqclib proof contribution.

The study is immutable after preparation. A fresh study is required for changed
obligations or implementation. The native kernel retains acceptance and Git
checkpoints. This command owns all effect admission and serial Lean execution.
"""
import argparse
import contextlib
import json
from pathlib import Path
import re
import sys
from types import SimpleNamespace

import chain_check
import chain_continue
import chain_kernel
import chain_runner
import control_cache
import fixtures
import local_retrieval
import runtime_pin
import study
import proof_program
import work_program

PROFILE = '''"""Frozen proof-chain host: checks are executed by the isolated owner adapter."""
GATED_KINDS = ("proof", "run")
CODE_KINDS = ()
CONTRACT_KIND = None
SHARED_WRITES = ()
def brief_lines(step):
    return ["Produce the frozen Lean proof; owner-only checks determine acceptance."]
def blind_brief(step, allowed, common):
    return None
def brief_inputs(root, step):
    return None, None
def code_files(step):
    return [path for path in step["writes"] if path.endswith(".lean")], [], False
def gate_rows(root, plan, step, deadline, expected):
    return [{"name": "proof-chain protected checker", "ok": False, "source": "dependency",
             "detail": "Run chain_study.py verify for isolated compiler replay."}], None
'''


def write(path, value):
    study.write_new(path, study.canonical(value))


def validate_spec(spec):
    nodes = spec.get("nodes")
    if spec.get("schema") != 1 or spec.get("source_commit") != fixtures.REVISION or not 1 <= len(nodes) <= 32:
        raise ValueError("unsupported bounded proof specification")
    known, paths, names = set(), set(), set()
    for node in nodes:
        if not re.fullmatch(r"T[0-9]{2}\.[0-9]+", node["id"]) or node["id"] in known:
            raise ValueError("node identity must be unique and native-step shaped")
        if not re.fullmatch(r"FTQCLib\.CSS\.Decoder\.[A-Za-z][A-Za-z0-9]*", node["module"]):
            raise ValueError("module outside the declared contribution namespace")
        if node["path"] != node["module"].replace(".", "/") + ".lean" or node["path"] in paths:
            raise ValueError("source destination differs from unique module")
        if not set(node["deps"]) <= known or node["name"] in names:
            raise ValueError("non-topological dependencies or duplicate theorem name")
        if node["statement"].split(":", 1)[1].strip() != node["expected_type"].strip():
            raise ValueError("statement and independently frozen expected type differ")
        if not node["statement"].startswith("theorem " + node["name"] + " :"):
            raise ValueError("statement declaration differs from expected theorem name")
        known.add(node["id"])
        paths.add(node["path"])
        names.add(node["name"])


def plan_files(worktree, spec, execution, *, replace=False, program=None, prepared_plan=None):
    plan = prepared_plan if prepared_plan is not None else work_program.legacy_plan(spec, execution, program)
    import plan_check
    import brief
    if plan_check.refusals(plan, ()):
        raise ValueError("native kernel refuses the proof plan")
    for step in plan["steps"]:
        brief.common(step, step["writes"])
    files = {".ontologic/plan.json": study.canonical(plan), ".ontologic/profile.py": PROFILE.encode(),
             ".ontologic/TARGETS.md": ("# T01 — Minimum-weight quantum decoder bridge\n\n" +
                                       "\n".join(spec["semantic_notes"]) + "\n").encode(),
             ".ontologic/.gitignore": b"state/\n"}
    for name, data in files.items():
        path = worktree / name
        if replace:
            path.write_bytes(data)
        else:
            study.write_new(path, data)
    study.git(worktree, "add", "--", *files)
    if study.git(worktree, "status", "--porcelain", "--", *files):
        study.git(worktree, "commit", "-q", "-m", "Freeze decoder bridge obligations and owner profile", "--", *files)
    return study.git(worktree, "rev-parse", "HEAD").decode().strip()


def preparation(args):
    if not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9._-]{0,80}", args.id):
        raise ValueError("safe bounded study ID required")
    spec = json.loads(args.spec.read_bytes())
    validate_spec(spec)
    root, kernel = args.study.resolve(), args.kernel.resolve()
    root.mkdir(parents=True, exist_ok=False)
    with contextlib.ExitStack() as locks:
        locks.enter_context(study.admission_lock(root))
        if args.continue_from:
            locks.enter_context(study.admission_lock(args.continue_from.resolve()))
        prepare_locked(args, spec, root, kernel)


def prepare_locked(args, spec, root, kernel):
    Store, _, _ = study.kernel_imports(kernel)
    store = Store(str(root / "records"))
    repo, worktree = root / "owner/repo.git", root / "worktree"
    repo.parent.mkdir()
    source = args.continue_from.resolve() / "worktree" if args.continue_from else args.source.resolve()
    revision = study.git(source, "rev-parse", "HEAD").decode().strip() if args.continue_from else spec["source_commit"]
    study.git(source, "clone", "--quiet", "--bare", "--no-local", str(source), str(repo))
    study.git(repo, "worktree", "add", "--detach", str(worktree), revision)
    if not args.continue_from and any((worktree / node["path"]).exists() for node in spec["nodes"]):
        raise ValueError("contribution would overwrite an existing baseline module")
    execution = {"provider": "codex", "executable": args.executable, "model": args.model,
                 "effort": args.effort, "deadline_seconds": args.deadline_seconds, "model_catalog": str(args.model_catalog.resolve()),
                 "model_catalog_sha256": study.digest(args.model_catalog.read_bytes()),
                 "observed_token_limit": args.token_limit}
    program = (proof_program.validate(json.loads(args.program.read_bytes()), spec["nodes"])
               if getattr(args, "program", None) else None)
    initial = work_program.lower(work_program.from_proof(spec, {**execution, "proof_policy": proof_policy(args)}, program))
    if not initial["ok"]:
        raise ValueError("initial Work IR refused: " + json.dumps(initial["errors"]))
    seed = plan_files(worktree, spec, execution, replace=bool(args.continue_from), program=program,
                      prepared_plan=initial["plan"])
    build = json.loads(args.build.read_bytes())
    manifest = make_manifest(args, spec, execution, seed, build, store)
    retained = store.put(study.canonical(initial["artifact"]))
    if retained != initial["identity"]:
        raise ValueError("initial Work IR storage identity differs")
    manifest["initial_work_ir"] = {"schema": 1, "label": "initial program; later native plan versions are authoritative",
                                   "artifact": retained, "identity": initial["identity"], "seed_commit": seed}
    if program:
        manifest["proof_program"] = program
        manifest["sources"][str(args.program.resolve())] = store.put(args.program.read_bytes())
        manifest["kernel_config"].update(proof_program.config(program))
        if getattr(args, "typed_interaction", False):
            manifest["kernel_config"].update(proof_program.interaction_config(program, spec["nodes"], args.id))
    elif getattr(args, "typed_interaction", False):
        raise ValueError("typed interaction requires a declared proof program")
    if args.runtime_pin:
        manifest["runtime_pin"] = runtime_pin.admit(args.runtime_pin, manifest, store)
    if args.controls_from:
        reference = control_cache.admit(args.controls_from, manifest, store)
        if reference:
            manifest["controls_certificate"] = reference
    if args.continue_from:
        # Receipt re-admission needs the frozen snapshot identity, without executing
        # backend retrieval, the compiler, or the model while preparing a version.
        checker = chain_check.Checker(root, manifest, store, None, SimpleNamespace(snapshot=manifest["snapshot_id"]))
        manifest["continuation"] = chain_continue.adopt(args.continue_from, worktree, manifest, store,
                                                       checker.validate_result)
    write(root / "manifest.json", manifest)
    write(root / "driver-config.json", manifest["kernel_config"])
    identity = store.put(study.canonical(manifest))
    study.write_new(root / "manifest.ref", identity.encode())
    study.event(store, args.id, "study_pin", manifest=identity)
    study.event(store, args.id, "stage", name="prepared", detail="Frozen obligations; mechanical controls pending")
    print(json.dumps({"study": str(root), "worktree": str(worktree), "manifest": identity, "nodes": len(spec["nodes"])}))


def make_manifest(args, spec, execution, seed, build, store):
    snapshot = args.snapshot.resolve()
    snapshot_id = (snapshot / "snapshot.ref").read_text().strip()
    if study.digest((snapshot / "snapshot.json").read_bytes()) != snapshot_id:
        raise ValueError("snapshot reference differs from its bytes")
    sources = study.source_objects(store, args.kernel.resolve())
    controls = Path(__file__).with_name("chain_controls.lean")
    consumers = Path(__file__).with_name("chain_consumers.lean")
    for path in (controls, consumers):
        sources[str(path.resolve())] = store.put(path.read_bytes())
    sources[str(args.spec.resolve())] = store.put(args.spec.read_bytes())
    config = {"provider": "codex", "harness": str(args.kernel.resolve()),
              "plan": ".ontologic/plan.json", "targets": ".ontologic/TARGETS.md",
              "binding": ".ontologic/TARGETS.md", "state": ".ontologic/state",
              "profile": ".ontologic/profile.py", "pins": [".ontologic/plan.json", ".ontologic/TARGETS.md"],
              "unjudged_retries": 0, "default_prior_usd": 0.0}
    return {"schema": 1, "kind": "proof-chain", "id": args.id, "source_commit": spec["source_commit"],
            "kernel": str(args.kernel.resolve()), "kernel_config": config, "seed_commit": seed,
            "specification": store.put(args.spec.read_bytes()), "nodes": spec["nodes"], "sources": sources,
            "execution": execution, "compiler": chain_check.compiler_record(build),
            "build_receipt": store.put(args.build.read_bytes()), "snapshot": str(snapshot), "snapshot_id": snapshot_id,
            "formalism": build["plan"], "controls_source": str(controls.resolve()),
            "consumers_source": str(consumers.resolve()),
            "policy": proof_policy(args)}


def proof_policy(args):
    return {"concurrency": 1, "protocol": 3 if getattr(args, "evidence_needs", False) else 2, "max_calls": args.max_calls,
            "max_requests": args.max_requests, "node_token_limit": args.node_token_limit,
            "max_retrieval_rounds": args.max_retrieval_rounds,
            "max_ineffective_rounds": args.max_ineffective_rounds,
            "input_bytes_max": 32768, "unknown_usage_stops_admission": True,
            "token_limit": "soft admission threshold; one in-flight call can exceed it", "automatic_escalations": 0}


def verify_initial_program(root, manifest, store):
    """Verify the immutable initial binding, never substitute it for an active plan."""
    reference = manifest.get("initial_work_ir")
    if reference is None:
        return
    if set(reference) != {"schema", "label", "artifact", "identity", "seed_commit"} or reference["schema"] != 1:
        raise ValueError("initial Work IR reference shape differs")
    data = store.get(reference["artifact"])
    if study.digest(data) != reference["identity"] or reference["artifact"] != reference["identity"]:
        raise ValueError("initial Work IR identity differs")
    artifact = json.loads(data)
    lowered = work_program.lower(artifact.get("program"))
    if not lowered["ok"] or study.canonical(lowered["artifact"]) != data:
        raise ValueError("initial Work IR compilation differs")
    spec = json.loads(store.get(manifest["specification"]))
    execution = {**manifest["execution"], "proof_policy": manifest["policy"]}
    expected = work_program.build_initial(spec, execution, manifest.get("proof_program"),
                                           artifact["program"]["metadata"]["function_order"])
    if study.canonical(expected) != study.canonical(artifact["program"]) or spec["nodes"] != manifest["nodes"]:
        raise ValueError("initial Work IR differs from frozen proof manifest")
    if reference["seed_commit"] != manifest["seed_commit"]:
        raise ValueError("initial Work IR seed binding differs")
    initial_plan = study.git(root / "worktree", "show", reference["seed_commit"] + ":.ontologic/plan.json")
    if initial_plan != study.canonical(lowered["plan"]):
        raise ValueError("initial Work IR differs from native seed plan")
    for key, value in lowered["config"].items():
        if manifest["kernel_config"].get(key) != value:
            raise ValueError("initial Work IR differs from native message configuration")


def load(root):
    manifest = json.loads((root / "manifest.json").read_bytes())
    Store, executor, _ = study.kernel_imports(manifest["kernel"])
    store = Store(str(root / "records"))
    if (root / "manifest.ref").read_text().strip() != store.put(study.canonical(manifest)):
        raise ValueError("manifest changed after preparation")
    verify_initial_program(root, manifest, store)
    study.verify_sources(manifest)
    catalog = Path(manifest["execution"]["model_catalog"])
    if study.digest(catalog.read_bytes()) != manifest["execution"]["model_catalog_sha256"]:
        raise ValueError("model capability catalog changed after preparation")
    pinned = manifest.get("runtime_pin") is not None
    study.event(store, manifest["id"], "stage", name="runtime-bind" if pinned else "runtime-audit",
                detail="Binding owner-pinned runtime receipt" if pinned else "Auditing runtime and retrieval bytes")
    lease = runtime_pin.from_store(manifest, store)
    backend = local_retrieval.Backend(manifest["snapshot"], manifest["snapshot_id"], store, executor, lease=lease)
    checker = chain_check.Checker(root, manifest, store, executor, backend)
    checker.verify()
    return manifest, store, checker, backend


def toy_node():
    return {"id": "control", "module": "Control", "path": "Control.lean", "name": "chainControl",
            "header": "import ECCLib.Decoding\nimport FTQCLib.CSS.SurfaceCode", "deps": [],
            "statement": "theorem chainControl : True", "expected_type": "True"}


def boundary_controls(checker, progress=lambda _: None):
    issue = {"hash": "0" * 64, "operands": []}
    node, found = toy_node(), []
    for name, proof, accepted in (("valid-proof", "by\n  trivial", True),
                                  ("sorry-refused", "by\n  sorry", False),
                                  ("unstable-simp-refused", "by\n  simp", False),
                                  ("declaration-escape-refused", "by\n  trivial\ntheorem evil : True := by trivial", False),
                                  ("ill-typed-proof-refused", "by\n  exact (0 : Nat)", False)):
        progress(name)
        result = checker.check(node, proof, issue)
        found.append({"id": name, "passed": result["accepted"] == accepted,
                      "result": checker.store.put(study.canonical(result))})
    wrong = {**node, "expected_type": "False"}
    progress("exact-type-refused")
    result = checker.check(wrong, "by\n  trivial", issue)
    found.append({"id": "exact-type-refused", "passed": not result["accepted"] and result["status"] == "failed",
                  "result": checker.store.put(study.canonical(result))})
    return found


def statement_controls(manifest, checker, progress=lambda _: None):
    """Compile only owner-labelled stubs to check binder/API compatibility; never accept them as proofs."""
    dependencies, found = {}, []
    issue = {"hash": "0" * 64, "operands": []}
    for node in manifest["nodes"]:
        progress("statement-" + node["id"])
        result = checker.check(node, "by\n  sorry", issue, admit=False, examine=False, dependencies=dependencies)
        found.append({"id": "statement-" + node["id"], "passed": result["accepted"],
                      "stub_only": True, "result": checker.store.put(study.canonical(result))})
        if not result["accepted"]:
            print(json.dumps({"control": found[-1], "diagnostic": result["diagnostic"]}), flush=True)
            break
        for item in result["artifacts"]:
            dependencies[item["path"]] = chain_check.object_bytes(checker.store, item["hash"])
    return found


def controls(root, manifest, store, checker):
    if any(entry["kind"] == "proposal_start" for entry in store.entries()):
        raise ValueError("controls must precede model admissions")
    cached = control_cache.reuse(manifest, store)
    if cached is not None:
        return finish_controls(manifest, store, cached, reused=True)
    progress = lambda name: study.event(store, manifest["id"], "stage", name="controls", detail="Checking " + name)
    rows = boundary_controls(checker, progress)
    rows += statement_controls(manifest, checker, progress)
    progress("finite-discriminating-controls")
    node = {"id": "mathematical-controls", "path": "Controls.lean"}
    candidate, build, deps = checker.layout("finite-controls", node, Path(manifest["controls_source"]).read_bytes(), {})
    result = checker.execute(candidate, build, deps, "Controls.lean", "finite-controls")
    rows.append({"id": "finite-discriminating-controls", "passed": result["execution"]["status"] == "completed",
                 "result": store.put(study.canonical(result))})
    return finish_controls(manifest, store, rows)


def finish_controls(manifest, store, rows, *, reused=False):
    expected = 7 + len(manifest["nodes"])
    passed = len(rows) == expected and all(row["passed"] for row in rows)
    ref = store.put(study.canonical(rows))
    certificate = control_cache.retain(manifest, store, rows) if passed else None
    study.event(store, manifest["id"], "controls_end", passed=passed, rows=ref, certificate=certificate,
                reused=reused, detail=f"{sum(row['passed'] for row in rows)}/{expected} controls " +
                ("reused from exact checking contract" if reused else "passed"))
    study.event(store, manifest["id"], "stage", name="ready" if passed else "blocked",
                detail="Mechanical controls passed; proof workers not started" if passed else "Mechanical controls failed")
    print(json.dumps({"passed": passed, "rows": rows}), flush=True)
    return 0 if passed else 2


def host(root, manifest, store, checker, backend):
    runner = chain_runner.Runner(root, manifest, store, checker, backend)
    kernel = chain_kernel.make_kernel(root / "worktree", manifest, store, runner, checker.validate_result)
    runner.kernel = kernel
    return kernel


def report(root, manifest, store, kernel):
    import replay
    entries = kernel.entries()
    retired = kernel.native.state_module.retired(entries)
    usage = chain_runner.known_usage(store, manifest["id"])
    replay_result = replay.replay_decisions(str(root / "worktree"), manifest["id"],
                                          config=kernel.config, store=kernel.store)
    result = {"study": manifest["id"], "retired": list(retired), "expected": len(manifest["nodes"]),
              "complete": len(retired) == len(manifest["nodes"]), "usage": usage,
              "tokens": sum(usage.values()) if usage is not None else None,
              "replay": replay_result, "view": kernel.view(),
              "checkpoint": study.git(root / "worktree", "rev-parse", "HEAD").decode().strip(),
              "kernel_head": kernel.store.head_hash(), "study_head": store.head_hash()}
    result["usage_observation"] = chain_continue.usage_exposure(store.entries(), manifest["id"])
    result["prior_usage"] = (json.loads(store.get(manifest["continuation"]))["prior_usage"]
                             if manifest.get("continuation") else None)
    ref = store.put(study.canonical(result))
    study.event(store, manifest["id"], "report", result=ref)
    print(json.dumps(result), flush=True)
    return result


def run(root, manifest, store, checker, backend):
    endings = [entry for entry in store.entries() if entry["kind"] == "controls_end"]
    if not endings or endings[-1]["passed"] is not True:
        raise ValueError("mechanical controls must pass before model admission")
    kernel = host(root, manifest, store, checker, backend)
    study.event(store, manifest["id"], "stage", name="running", detail="Sequential proof DAG; model tools disabled")
    end = kernel.run([node["id"] for node in manifest["nodes"]], 1000.0, 0.0)
    result = report(root, manifest, store, kernel)
    if result["complete"]:
        study.event(store, manifest["id"], "study_end", detail="All proof nodes retired; compiler replay pending")
        return 0
    study.event(store, manifest["id"], "stage", name="blocked", detail=str(end.get("refusal") or "Proof chain incomplete"))
    return 2


def verify(root, manifest, store, checker, backend):
    """Replay actual accepted Lean sources in fresh build directories without model invocations."""
    kernel = host(root, manifest, store, checker, backend)
    retired = kernel.native.state_module.retired(kernel.entries())
    dependencies, rows = {}, []
    for node in manifest["nodes"]:
        retirement = retired.get(node["id"])
        if retirement is None:
            raise ValueError("cannot verify incomplete chain: " + node["id"])
        issue = next(entry for entry in kernel.entries() if entry["hash"] == retirement["issue"])
        output = next(entry for entry in retirement["outputs"] if entry["path"] == node["path"])
        source = chain_check.object_bytes(store, output["hash"]).decode()
        prefix = node["header"].rstrip() + "\n\n" + node["statement"].rstrip() + " := "
        if not source.startswith(prefix):
            raise ValueError("retired source differs from frozen statement")
        checked = checker.check(node, source[len(prefix):], issue, dependencies=dependencies)
        rows.append({"node": node["id"], "passed": checked["accepted"],
                     "certificate": checked.get("certificate")})
        if not checked["accepted"]:
            break
        for artifact in checked["artifacts"]:
            dependencies[artifact["path"]] = chain_check.object_bytes(store, artifact["hash"])
    passed = len(rows) == len(manifest["nodes"]) and all(row["passed"] for row in rows)
    if passed:
        node = {"id": "integrated-consumers", "path": "Consumers.lean"}
        source = Path(manifest["consumers_source"]).read_bytes()
        candidate, build, deps = checker.layout("integrated-consumers", node, source, dependencies)
        consumer = checker.execute(candidate, build, deps, "Consumers.lean", "integrated-consumers")
        passed = consumer["execution"]["status"] == "completed"
        rows.append({"node": "integrated-consumers", "passed": passed,
                     "result": store.put(study.canonical(consumer))})
    study.event(store, manifest["id"], "compiler_replay", passed=passed, rows=store.put(study.canonical(rows)))
    print(json.dumps({"compiler_replay": passed, "rows": rows}), flush=True)
    return 0 if passed else 2


def bounded_integer(low, high):
    def parse(value):
        number = int(value)
        if not low <= number <= high:
            raise argparse.ArgumentTypeError(f"expected an integer in [{low}, {high}]")
        return number
    return parse


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("prepare")
    for field in ("study", "source", "kernel", "spec", "build", "snapshot", "model-catalog"):
        create.add_argument("--" + field, type=Path, required=True)
    create.add_argument("--id", required=True)
    create.add_argument("--executable", required=True)
    create.add_argument("--model", default="gpt-5.6-luna")
    create.add_argument("--effort", default="medium")
    create.add_argument("--continue-from", type=Path)
    create.add_argument("--program", type=Path, help="Named model functions and bounded blocked-question routes")
    create.add_argument("--typed-interaction", action="store_true", help="Pin typed local-owner submission contracts")
    create.add_argument("--evidence-needs", action="store_true", help="Opt into proof outcome/evidence-need protocol 3")
    create.add_argument("--runtime-pin", type=Path, help="Explicit owner-maintained runtime pin; full audit is separate")
    create.add_argument("--controls-from", type=Path, help="Reuse matching closed control receipts; otherwise run controls")
    for field, default, low, high in (("deadline-seconds", 180, 1, 3600),
                                    ("token-limit", 120000, 1, 10000000),
                                    ("node-token-limit", 24000, 1, 1000000),
                                    ("max-calls", 6, 1, 32), ("max-requests", 4, 0, 8),
                                    ("max-retrieval-rounds", 2, 0, 8),
                                    ("max-ineffective-rounds", 2, 1, 8)):
        create.add_argument("--" + field, type=bounded_integer(low, high), default=default)
    for command in ("controls", "run", "verify", "start"):
        commands.add_parser(command).add_argument("study", type=Path)
    args = parser.parse_args()
    if args.command == "prepare":
        preparation(args)
        return 0
    root = args.study.resolve()
    with study.admission_lock(root):
        manifest, store, checker, backend = load(root)
        try:
            if args.command == "controls":
                return controls(root, manifest, store, checker)
            if args.command == "start":
                if controls(root, manifest, store, checker):
                    return 2
                if run(root, manifest, store, checker, backend):
                    return 2
                return verify(root, manifest, store, checker, backend)
            return (run if args.command == "run" else verify)(root, manifest, store, checker, backend)
        except Exception as error:
            study.event(store, manifest["id"], "stage", name="blocked", detail=str(error)[:1000])
            raise


if __name__ == "__main__":
    raise SystemExit(main())

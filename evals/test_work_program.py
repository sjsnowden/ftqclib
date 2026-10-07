"""Goal: Work IR preserves native proof definitions and refuses alternate meanings.

Method: concrete round trips, planted redundant-field disagreements, real native
question/reply replay, and immutable seed verification after a future plan edit.
Finite injected answers/checks establish no paid-model or Lean correctness claim.
"""
import copy
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace

os.environ.setdefault("ONTOLKERNEL", str(Path(__file__).resolve().parents[2] / "ontolkernel-proof"))
import test_proof_program as native
import chain_kernel
import chain_study
import fixtures
import study
import work_program

SPEC = {"schema": 1, "id": "bridge-test", "source_commit": fixtures.REVISION,
        "semantic_notes": ["Preserve the actual frozen mathematical obligation."], "nodes": [{
            "id": "T01.1", "deps": [], "module": "FTQCLib.CSS.Decoder.Answer",
            "path": "FTQCLib/CSS/Decoder/Answer.lean", "header": "import Library.Base",
            "name": "Library.answer", "statement": "theorem Library.answer : True",
            "expected_type": "True", "purpose": "Establish the consumer obligation",
            "evidence": [["Library", "fact"]], "evidence_notes": ["Exact supplied declaration"],
            "imports": ["Library.Base"], "checks": ["Check the expected declaration type"],
            "consumer": {"intent": "Use the accepted interface", "expected_name": "Library.answer"}}]}
EXECUTION = {"provider": "codex", "executable": "codex", "model": "scripted", "effort": "medium",
             "deadline_seconds": 180, "model_catalog": "/catalog.json", "model_catalog_sha256": "a" * 64,
             "observed_token_limit": 10000, "proof_policy": chain_study.proof_policy(SimpleNamespace(
                 max_calls=3, max_requests=2, node_token_limit=1000, max_retrieval_rounds=2,
                 max_ineffective_rounds=2))}


def check(name, condition):
    assert condition, name
    print("ok: " + name, flush=True)


def roundtrip():
    for program in (None, native.PROGRAM):
        raw = work_program.from_proof(SPEC, EXECUTION, program)
        lowered = work_program.lower(raw)
        check("host accepts valid proof IR", lowered["ok"])
        check("all mathematical, execution and program fields round trip", lowered["spec"] == SPEC
              and lowered["execution"] == EXECUTION and lowered["program"] == program)
        expected = {"steps": [{"id": "T01.1", "target": "T01", "kind": "proof", "scheduled": True,
                    "title": "Establish the consumer obligation", "artifact": "FTQCLib/CSS/Decoder/Answer.lean",
                    "gate": "Protected Lean type and axiom checks", "depends_on": [],
                    "writes": ["FTQCLib/CSS/Decoder/Answer.lean", ".ontologic/certificates/T01.1.json"],
                    "agent": {"model": "scripted", "effort": "medium"}}], "reviewed_steps": []}
        if program:
            expected["steps"].append({"id": "T02.M", "target": "T02", "kind": "proof", "scheduled": False,
                "title": "assess_prerequisite: Assess the missing prerequisite using supplied declarations",
                "artifact": "typed advice", "gate": "Answer schema; sender retains proof checking",
                "depends_on": [], "writes": [], "agent": {"model": "scripted", "effort": "medium"},
                "model_function": "assess_prerequisite"})
        check("legacy native plan is byte-equivalent", study.canonical(lowered["plan"]) == study.canonical(expected))
        check("identity binds execution budgets", work_program.lower(work_program.from_proof(
            SPEC, {**EXECUTION, "observed_token_limit": 10001}, program))["identity"] != lowered["identity"])
        changed = copy.deepcopy(raw)
        changed["metadata"] = dict(reversed(list(changed["metadata"].items())))
        check("mapping order does not change identity", work_program.lower(changed)["identity"] == lowered["identity"])
        raw["metadata"]["spec"]["nodes"][0]["purpose"] = "Mutation after construction"
        check("builders detach owner inputs", SPEC["nodes"][0]["purpose"] == "Establish the consumer obligation")
    spec = copy.deepcopy(SPEC)
    second = copy.deepcopy(spec["nodes"][0])
    second.update(id="T01.2", deps=["T01.1"], module="FTQCLib.CSS.Decoder.Second",
                  path="FTQCLib/CSS/Decoder/Second.lean", name="Library.second",
                  statement="theorem Library.second : True",
                  consumer={"intent": "Use second", "expected_name": "Library.second"})
    spec["nodes"].append(second)
    lowered = work_program.lower(work_program.from_proof(spec, EXECUTION))
    check("checked predecessor refs preserve native dependencies", lowered["ok"]
          and lowered["artifact"]["dependencies"]["T01.2"] == ["T01.1"]
          and lowered["plan"]["steps"][1]["depends_on"] == ["T01.1"])


def disagreements():
    raw = work_program.from_proof(SPEC, EXECUTION, native.PROGRAM)
    cases = [("unknown node param", lambda value: value["nodes"][0]["params"].update(command="hidden")),
             ("different theorem param", lambda value: value["nodes"][0]["params"]["node"].update(expected_type="False")),
             ("endpoint scheduled", lambda value: value["nodes"][-1].update(mode="step")),
             ("different output", lambda value: value["nodes"][0].update(writes=["Other.lean"])),
             ("different route", lambda value: value["metadata"]["config"]["message_routes"].update({"T01.1": []})),
             ("unknown execution field", lambda value: value["metadata"]["execution"].update(shell="hidden")),
             ("unknown mathematical field", lambda value: value["metadata"]["spec"]["nodes"][0].update(command="hidden")),
             ("protected policy changed", lambda value: value["metadata"]["execution"]["proof_policy"].update(concurrency=2)),
             ("unknown adapter metadata", lambda value: value["metadata"].update(authority="hidden")),
             ("exports omitted", lambda value: value.update(exports={}))]
    for name, mutate in cases:
        changed = copy.deepcopy(raw)
        mutate(changed)
        result = work_program.lower(changed)
        check(name + " is a structured refusal", not result["ok"] and bool(result["errors"])
              and result["artifact"] is None and result["plan"] is None)


def endpoint_order():
    program = copy.deepcopy(native.PROGRAM)
    definition = program["functions"].pop("assess_prerequisite")
    program["functions"] = {"zeta": {**definition, "step": "T02.M"},
                            "alpha": {**definition, "step": "T03.M"}}
    program["on_blocked"] = {"T01.1": "zeta"}
    raw = work_program.from_proof(SPEC, EXECUTION, program)
    before = work_program.lower(raw)
    stored = json.loads(study.canonical(before["artifact"]))
    after = work_program.lower(stored["program"])
    check("unsorted function names survive canonical artifact storage", after["ok"]
          and after["identity"] == before["identity"] and after["plan"] == before["plan"]
          and [step["id"] for step in after["plan"]["steps"]] == ["T01.1", "T02.M", "T03.M"])


def native_host(directory, *, legacy=False):
    root, manifest, store = native.native_test.fixture(directory)
    lowered = work_program.lower(work_program.from_proof(SPEC, EXECUTION, native.PROGRAM))
    plan = work_program.legacy_plan(SPEC, EXECUTION, native.PROGRAM) if legacy else lowered["plan"]
    (root / "plan.json").write_bytes(study.canonical(plan))
    chain_kernel.git(root, "add", "plan.json")
    chain_kernel.git(root, "commit", "-qm", "initial IR native plan")
    manifest.update(nodes=copy.deepcopy(SPEC["nodes"]), proof_program=copy.deepcopy(native.PROGRAM),
                    formalism=native.runner_test.FORMALISM,
                    execution={key: value for key, value in EXECUTION.items() if key != "proof_policy"},
                    policy=EXECUTION["proof_policy"])
    runner = native.Scripted(directory, manifest, store)
    kernel = chain_kernel.make_kernel(root, manifest, store, runner, lambda issue, result: None)
    runner.kernel = kernel
    return kernel, runner


def native_flow(directory):
    kernel, runner = native_host(directory)
    kernel.run(["T01.1"], 100, 0)
    kinds = [entry["kind"] for entry in kernel.entries()]
    check("lowered native plan completes question/reply and checked retirement", kinds.count("issue") == 2
          and kinds.count("message_delivery") == 1 and kinds.count("message_reply") == 1
          and kinds.count("retire") == 1 and len(runner.calls) == 3)
    replay = native.native_test.replay.replay_decisions(str(kernel.root), kernel.run_id, config=kernel.config, store=kernel.store)
    check("lowered native plan replays without differences", replay["replayable"] and not replay["differing"])
    with tempfile.TemporaryDirectory(prefix="work-legacy-") as original:
        previous, previous_runner = native_host(Path(original), legacy=True)
        previous.run(["T01.1"], 100, 0)
        semantic = lambda host: [(entry["kind"], entry.get("step"), entry.get("outcome"), entry.get("to"))
                                  for entry in host.entries()]
        check("legacy and lowered plans make identical native instruction decisions", semantic(previous) == semantic(kernel)
              and [role for role, _ in previous_runner.calls] == [role for role, _ in runner.calls]
              and native.chain_runner.known_usage(previous_runner.store, previous_runner.manifest["id"])
                  == native.chain_runner.known_usage(runner.store, runner.manifest["id"]))


def native_activation(directory):
    import control_cli
    import control_run
    kernel, runner = native_host(directory)
    check("lowered native plan begins", kernel.begin(100, 0) is None)
    config = directory / "driver.json"
    config.write_bytes(study.canonical(kernel.config))
    future = copy.deepcopy(kernel.plan)
    future["steps"][0]["proof_evidence"] = [["Library", "newFact"]]
    path = directory / "future.json"
    path.write_bytes(study.canonical(future))
    submitted, code = control_cli.execute(str(kernel.root), kernel.run_id, ["plan", "submit", str(path)], str(config))
    check("future native plan submitted", code == 0)
    control_run.poll(kernel)
    status, _ = control_cli.execute(str(kernel.root), kernel.run_id, ["status"], str(config))
    activated, code = control_cli.execute(str(kernel.root), kernel.run_id,
        ["plan", "activate", submitted["version"], "--from", status["active_plan"]], str(config))
    check("future native plan activation requested", code == 0)
    control_run.poll(kernel)
    issue, job = kernel.issue("T01.1", 100, 0)
    check("native activated evidence is authoritative for the new invocation", kernel.plan == future
          and native.proof_effects.node_for(runner, job)["evidence"] == [["Library", "newFact"]])


def initial_binding(directory):
    root, manifest, store = native.native_test.fixture(directory)
    program = copy.deepcopy(native.PROGRAM)
    definition = program["functions"].pop("assess_prerequisite")
    program["functions"] = {"zeta": {**definition, "step": "T02.M"}, "alpha": {**definition, "step": "T03.M"}}
    program["on_blocked"] = {"T01.1": "zeta"}
    lowered = work_program.lower(work_program.from_proof(SPEC, EXECUTION, program))
    (root / ".ontologic").mkdir()
    (root / ".ontologic/plan.json").write_bytes(study.canonical(lowered["plan"]))
    chain_kernel.git(root, "add", ".ontologic/plan.json")
    chain_kernel.git(root, "commit", "-qm", "retain initial seed")
    seed = chain_kernel.git(root, "rev-parse", "HEAD").decode().strip()
    identity = store.put(study.canonical(lowered["artifact"]))
    manifest.update(nodes=SPEC["nodes"], specification=store.put(study.canonical(SPEC)),
                    seed_commit=seed, proof_program=program, policy=EXECUTION["proof_policy"],
                    execution={key: value for key, value in EXECUTION.items() if key != "proof_policy"},
                    initial_work_ir={"schema": 1, "artifact": identity, "identity": identity, "seed_commit": seed,
                                     "label": "initial program; later native plan versions are authoritative"})
    manifest["kernel_config"].update(lowered["config"])
    manifest = json.loads(study.canonical(manifest))
    future = copy.deepcopy(lowered["plan"])
    future["steps"][0]["proof_evidence"] = [["Library", "newFact"]]
    (root / ".ontologic/plan.json").write_bytes(study.canonical(future))
    chain_study.verify_initial_program(directory, manifest, store)
    check("initial verification permits a distinct later native plan", True)
    changed = copy.deepcopy(manifest)
    changed["policy"]["node_token_limit"] += 1
    try:
        chain_study.verify_initial_program(directory, changed, store)
    except ValueError:
        check("manifest budget disagreement is refused", True)
    else:
        raise AssertionError("manifest budget disagreement accepted")
    legacy = {key: value for key, value in manifest.items() if key != "initial_work_ir"}
    chain_study.verify_initial_program(directory, legacy, store)
    check("legacy manifest requires no IR artifact", True)


if __name__ == "__main__":
    roundtrip()
    disagreements()
    endpoint_order()
    for test in (native_flow, native_activation, initial_binding):
        with tempfile.TemporaryDirectory(prefix="work-program-") as directory:
            test(Path(directory))

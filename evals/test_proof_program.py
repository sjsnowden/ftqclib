"""Real native DAG effects with finite injected model/checker results; no paid calls or Lean claims."""
import copy
import json
import os
from pathlib import Path
import tempfile

os.environ.setdefault("ONTOLKERNEL", str(Path(__file__).resolve().parents[2] / "ontolkernel-proof"))
import test_chain_kernel as native_test
import test_chain_runner as runner_test
import chain_kernel
import chain_runner
import proof_program
import proof_effects
import study

PROGRAM = {"schema": 1, "functions": {"assess_prerequisite": {
    "step": "T02.M", "purpose": "Assess the missing prerequisite using supplied declarations",
    "model": "scripted", "effort": "medium", "evidence": ["Library.fact"]}},
    "on_blocked": {"T01.1": "assess_prerequisite"}, "message_limit": 2, "max_model_calls": 8}


class Checker(runner_test.Checker):
    def __init__(self, store):
        super().__init__()
        self.store = store

    def check(self, node, proof, issue):
        self.calls.append((proof, issue["hash"]))
        return {"accepted": True, "status": "passed", "source": self.store.put(b"test proof"),
                "certificate": self.store.put(b"test certificate")}


class Scripted(chain_runner.Runner):
    def __init__(self, root, manifest, store):
        super().__init__(root, manifest, store, Checker(store), runner_test.Backend())
        self.calls = []

    def invoke(self, job, number, packet, schema, instructions, role, slot):
        refusal = self.admission_refusal()
        assert refusal is None, refusal
        self.calls.append((role, packet))
        invocation = "call-" + str(len(self.calls))
        self.event("proposal_start", slot=slot, issue=job["issue"]["hash"], round=number, invocation=invocation)
        if role.startswith("function:"):
            value = {"status": "evidence", "body": "Use True.intro; the required fact is supplied.", "declarations": []}
            result = {"finished": True, "text": json.dumps(value), "usage": runner_test.USAGE, "admitted": True}
        else:
            result = runner_test.proposal("blocked" if "recorded_inputs" not in packet else "check_candidate", proof="by trivial")
        self.event("proposal_end", slot=slot, issue=job["issue"]["hash"], round=number,
                   invocation=invocation, usage=result["usage"])
        return result


def fixture(directory, cap=8):
    root, manifest, store = native_test.fixture(directory)
    node = {**runner_test.NODE, "id": "T01.1", "deps": []}
    program = copy.deepcopy(PROGRAM)
    program["max_model_calls"] = cap
    proof_program.validate(program, [node])
    step = native_test.step(node["id"], [])
    step["writes"] = [node["path"], ".ontologic/certificates/T01.1.json"]
    plan = {"steps": [step, *proof_program.compile_steps(program)], "reviewed_steps": []}
    (root / "plan.json").write_bytes(study.canonical(plan))
    chain_kernel.git(root, "add", "plan.json")
    chain_kernel.git(root, "commit", "-qm", "declare effect program")
    manifest.update(nodes=[node], proof_program=program, formalism=runner_test.FORMALISM,
                    execution={"observed_token_limit": 10000},
                    policy={"max_calls": 3, "max_requests": 2, "node_token_limit": 1000})
    runner = Scripted(directory, manifest, store)
    kernel = chain_kernel.make_kernel(root, manifest, store, runner, lambda issue, result: None)
    runner.kernel = kernel
    return kernel, runner


def exchange(directory):
    kernel, runner = fixture(directory)
    kernel.run(["T01.1"], 100, 0)
    entries = kernel.entries()
    kinds = [e["kind"] for e in entries]
    assert kinds.count("issue") == 2 and kinds.count("message_delivery") == 1
    assert kinds.count("message_reply") == 1 and kinds.count("retire") == 1
    assert [e["step"] for e in entries if e["kind"] == "retire"] == ["T01.1"]
    assert len(runner.checker.calls) == 1 and len(runner.calls) == 3
    assert runner.calls[-1][1]["recorded_inputs"][".step/inbox.json"]["status"] == "answered"
    assert chain_runner.known_usage(runner.store, runner.manifest["id"]) == {
        key: value * 3 for key, value in runner_test.USAGE.items()}
    assert not any(e["kind"] == "node_blocked" for e in runner.store.entries())
    import chain_view
    view = chain_view.view_of(runner.manifest, runner.store.entries())
    assert view["usage"]["tokens_known"] == sum(runner_test.USAGE.values()) * 3
    waiting = next(i for i, e in enumerate(runner.store.entries()) if e["kind"] == "node_waiting")
    assert chain_view.view_of(runner.manifest, runner.store.entries()[:waiting + 1])["nodes"][0]["phase"] == "waiting for reply"
    replay = native_test.replay.replay_decisions(str(kernel.root), kernel.run_id,
                                                config=kernel.config, store=kernel.store)
    assert replay["replayable"] and not replay["differing"], replay
    print("ok: blocked -> native question -> named answer -> new issue -> checked retirement")


def budget(directory):
    kernel, runner = fixture(directory, cap=1)
    kernel.run(["T01.1"], 100, 0)
    assert len(runner.calls) == 1 and not runner.checker.calls
    assert not any(e["kind"] == "message_delivery" for e in kernel.entries())
    assert "model-call limit" in kernel.deferred["T01.1"]
    print("ok: answer calls cannot bypass the shared model admission budget")


def plan_guard(directory):
    kernel, runner = fixture(directory)
    assert proof_effects.control_refusal(kernel, {"request": ["invalid"]}) is None
    plan = copy.deepcopy(kernel.plan)
    plan["steps"][0]["proof_evidence"] = [["Library", "fact"]]
    observed = {"request": {"op": "plan_submit", "payload": {"plan": plan}}}
    assert proof_effects.control_refusal(kernel, observed) is None
    plan["steps"][0]["writes"].append("checker.py")
    assert proof_effects.control_refusal(kernel, observed)
    plan["steps"][0]["writes"].pop()
    plan["steps"][-1]["scheduled"] = True
    assert proof_effects.control_refusal(kernel, observed)
    print("ok: versioned evidence admitted; checker writes and scheduled answer endpoints refused")


def recovery(directory):
    import message_decide
    kernel, runner = fixture(directory)
    assert kernel.begin(100, 0) is None
    issue, job = kernel.issue("T01.1", 100, 0)
    kernel.close(issue, runner(job))
    question = next(e for e in kernel.entries() if e["kind"] == "message")
    made = message_decide.on_delivery(kernel.entries(), kernel.setting, question,
                                      {"ceiling_usd": 100, "floor_usd": 0, "reserved_usd": 0},
                                      kernel.now(), kernel.store.get)
    kernel.commit("message_delivery", made)
    delivery = made["issued"]["issue"]
    job = {"issue": delivery, "step": kernel.steps[delivery["step"]], "files": made["issued"]["files"]}
    runner.answer(job)  # Crash after durable answer, before native reply commit.
    resumed = Scripted(directory, runner.manifest, runner.store)
    host = chain_kernel.make_kernel(kernel.root, runner.manifest, runner.store, resumed, lambda i, r: None)
    resumed.kernel = host
    host.run(["T01.1"], 100, 0)
    assert len(resumed.calls) == 1 and resumed.calls[0][0] == "proof-proposal"
    assert sum(e["kind"] == "message_delivery" for e in host.entries()) == 1
    assert sum(e["kind"] == "retire" for e in host.entries()) == 1
    print("ok: durable answer recovered without repeating the model call")


def commands(directory):
    import control_cli
    import control_run
    kernel, runner = fixture(directory)
    assert kernel.begin(100, 0) is None
    config = directory / "driver.json"
    config.write_bytes(study.canonical(kernel.config))
    future = copy.deepcopy(kernel.plan)
    future["steps"][0]["proof_evidence"] = [["Library", "fact"]]
    path = directory / "future.json"
    path.write_bytes(study.canonical(future))
    submitted, code = control_cli.execute(str(kernel.root), kernel.run_id, ["plan", "submit", str(path)], str(config))
    assert code == 0, submitted
    control_run.poll(kernel)
    status, _ = control_cli.execute(str(kernel.root), kernel.run_id, ["status"], str(config))
    activated, code = control_cli.execute(str(kernel.root), kernel.run_id,
        ["plan", "activate", submitted["version"], "--from", status["active_plan"]], str(config))
    assert code == 0, activated
    control_run.poll(kernel)
    assert kernel.plan == future
    result, code = control_cli.execute(str(kernel.root), kernel.run_id,
                                       ["message", "T01.1", "Use the original obligation; examine Library.fact"], str(config))
    assert code == 0, result
    control_run.poll(kernel)
    issue, job = kernel.issue("T01.1", 100, 0)
    assert proof_effects.node_for(runner, job)["evidence"] == [["Library", "fact"]]
    packet = {}
    proof_effects.add_inputs(runner, job, packet)
    assert packet["recorded_inputs"][".step/control.json"]["messages"][0]["body"].startswith("Use the original")
    plan = copy.deepcopy(kernel.plan)
    plan["steps"][0]["agent"]["effort"] = "high"
    path = directory / "replacement.json"
    path.write_bytes(study.canonical(plan))
    submitted, code = control_cli.execute(str(kernel.root), kernel.run_id, ["plan", "submit", str(path)], str(config))
    assert code == 0, submitted
    control_run.poll(kernel)
    status, _ = control_cli.execute(str(kernel.root), kernel.run_id, ["status"], str(config))
    activated, code = control_cli.execute(str(kernel.root), kernel.run_id,
        ["plan", "activate", submitted["version"], "--from", status["active_plan"]], str(config))
    assert code == 0, activated
    control_run.poll(kernel)
    controls = [e for e in kernel.entries() if e["kind"] == "control"]
    assert controls[-1]["status"] == "refused", controls[-1]
    print("ok: operator inbox reaches proof packet; mutation of issued work is refused")


def ambiguous_answer(directory):
    import message_decide
    kernel, runner = fixture(directory)
    assert kernel.begin(100, 0) is None
    issue, job = kernel.issue("T01.1", 100, 0)
    kernel.close(issue, runner(job))
    question = next(e for e in kernel.entries() if e["kind"] == "message")
    made = message_decide.on_delivery(kernel.entries(), kernel.setting, question,
        {"ceiling_usd": 100, "floor_usd": 0, "reserved_usd": 0}, kernel.now(), kernel.store.get)
    kernel.commit("message_delivery", made)
    assert "ambiguous interrupted answer" in kernel.recover()
    assert len(runner.calls) == 1
    runner.event("proposal_start", issue=made["issued"]["issue"]["hash"], round=1, invocation="unfinished")
    assert "unknown usage" in runner.admission_refusal()
    print("ok: ambiguous answer and unfinished usage prevent further model admission")


if __name__ == "__main__":
    import proposal_agent
    assert proposal_agent.schema_refusal(proof_program.RESULT_SCHEMA) is None
    for test in (exchange, budget, plan_guard, recovery, commands, ambiguous_answer):
        with tempfile.TemporaryDirectory(prefix="proof-program-") as directory:
            test(Path(directory))

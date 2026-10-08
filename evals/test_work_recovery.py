"""Goal: typed recovery retains facts and authority through fresh invocations.

Finite providers drive real owner dispatch/state persistence in a temporary store;
no model, Lean, network or subprocess effects. A non-Lean instance exercises the
same core, and corruption, changed contracts and unauthorised effects fail closed.
"""
import copy
import json
from pathlib import Path
import tempfile

import evidence_protocol
import proof_resolver
import proof_work_state
import study
import test_chain_runner as fixtures


def request(name="Library.fact"):
    return {"outcome": "need", "need": "declaration_names", "names": [name],
            "fragment": None, "proof": None, "reason": None}


def check(root):
    Store, _, _ = study.kernel_imports(Path(__file__).resolve().parents[2] / "ontolkernel-proof")
    import work_state
    runner = fixtures.Scripted([])
    runner.store = Store(str(root / "records"))
    runner.manifest.update(recovery_state=True)
    runner.manifest["policy"]["protocol"] = 3
    runner.event = lambda kind, **fields: study.event(runner.store, runner.manifest["id"], kind, **fields)
    node = fixtures.NODE
    issue = {"hash": "d" * 64, "step": node["id"], "operands": []}
    session = evidence_protocol.Session(runner.backend, 2, fixtures.SNAPSHOT)
    proof_work_state.restore(runner, node, issue, session)
    action = session.dispatch(json.dumps(request()))
    first = proof_work_state.record(runner, node, issue, session, action)
    fresh = evidence_protocol.Session(runner.backend, 2, fixtures.SNAPSHOT)
    proof_work_state.restore(runner, node, {**issue, "hash": "e" * 64}, fresh)
    assert fresh.requests_used == 1 and fresh.requests_left == 1
    assert "Library.fact" in json.dumps(fresh.retrieved)
    assert fresh.dispatch(json.dumps(request()))["status"] == "refused"
    assert len(runner.backend.calls) == 1
    assert proof_work_state.evidence(runner, node, issue)["state"] == first
    changed = {**node, "expected_type": "False"}
    other = evidence_protocol.Session(runner.backend, 2, fixtures.SNAPSHOT)
    proof_work_state.restore(runner, changed, issue, other)
    assert other.work_state is None and other.requests_used == 0
    generic(root, work_state)
    resolver(runner, node, issue)
    print("Recovery: continuity, dedup, budgets, contract separation, resolver effects, admission and non-Lean instance passed")


def generic(root, core):
    refs = [str(n) * 64 for n in range(1, 7)]
    original = core.create(*refs[:4], inputs=[refs[4]])
    next_state = core.advance(original, inputs=[refs[5], refs[4]])
    assert next_state["inputs"] == sorted(refs[4:]) and original["inputs"] == [refs[4]]
    assert next_state["parents"] == [study.digest(study.canonical(original))]
    malformed = {**next_state, "inputs": [refs[4], refs[4]]}
    assert core.validate(malformed)
    registry = {("Produce", "text.Normalized/v1"): {"handler": "text.check", "capability": "check"},
                ("Propose", "text.Task/v1"): {"handler": "owner.admit", "capability": "propose"}}
    outcome = {"kind": "Produce", "type": "text.Normalized/v1", "payload": refs[0]}
    assert core.route(outcome, registry, {"check"})["handler"] == "text.check"
    assert core.route(outcome, registry, set())["status"] == "refused"
    assert core.route({**outcome, "type": "shell"}, registry, {"check"})["status"] == "refused"
    assert core.route({**outcome, "kind": "Propose", "type": "text.Task/v1"}, registry,
                      {"propose"})["status"] == "awaiting_admission"


def resolver(runner, node, issue):
    need = {**request("Library.second"), "statement": None}
    candidate = {"outcome": "candidate", "proof": "by\n  exact True.intro", "need": None,
                 "names": None, "fragment": None, "reason": None, "statement": None}
    replies, packets = [need, candidate], []
    runner.checker = fixtures.Checker({candidate["proof"]: "passed"})
    def invoke(job, number, packet, schema, instructions, role, slot):
        packets.append(copy.deepcopy(packet))
        return {"admitted": True, "finished": True, "usage": fixtures.USAGE,
                "text": json.dumps(replies.pop(0))}
    runner.invoke = invoke
    result, reply = proof_resolver.run(runner, {}, node, issue, {}, [])
    assert reply["status"] == "adaptation" and runner.checker.calls == [candidate["proof"]]
    assert "Library.fact" in json.dumps(packets[0]["retained_work"])
    assert "Library.second" in json.dumps(packets[1]["retrieved"])
    assert result["usage"]["input_tokens"] == 2 * fixtures.USAGE["input_tokens"]
    proposed = {**candidate, "outcome": "propose", "proof": None, "statement": "True", "reason": "support"}
    value, refusal = proof_resolver.parse(json.dumps(proposed))
    assert refusal is None
    session = evidence_protocol.Session(runner.backend, 2, fixtures.SNAPSHOT)
    proof_work_state.restore(runner, node, issue, session)
    outcome = proof_resolver.dispatch(runner, node, issue, session, value)
    assert outcome["status"] == "prerequisite" and len(runner.checker.calls) == 1
    assert runner.store.entries()[-1]["kind"] == "extension_proposed"
    raw = runner.store.get(session.work_contract)
    Path(runner.store.object_path(session.work_contract)).write_bytes(raw + b" ")
    try:
        proof_work_state.read(runner.store, session.work_contract)
    except ValueError:
        pass
    else:
        raise AssertionError("corrupt reference admitted")


def native_exchange(root):
    import test_proof_program as native
    kernel, runner = native.fixture(root)
    runner.manifest.update(recovery_state=True, source_commit="a" * 40)
    runner.manifest["policy"]["protocol"] = 3
    candidate = {"outcome": "candidate", "proof": "by trivial", "need": None,
                 "names": None, "fragment": None, "reason": None}
    blocked = {**candidate, "outcome": "blocked", "proof": None, "reason": "support needed"}
    replies = [request("Library.new"), blocked, {**request("Library.other"), "statement": None},
               {**candidate, "statement": None}, candidate]
    packets = []
    def invoke(job, number, packet, schema, instructions, role, slot):
        assert runner.admission_refusal() is None
        packets.append(copy.deepcopy(packet))
        invocation = "recovery-" + str(len(packets))
        runner.event("proposal_start", issue=job["issue"]["hash"], round=number, invocation=invocation)
        result = {"admitted": True, "finished": True, "usage": fixtures.USAGE,
                  "text": json.dumps(replies.pop(0))}
        runner.event("proposal_end", issue=job["issue"]["hash"], round=number,
                     invocation=invocation, usage=fixtures.USAGE)
        return result
    runner.invoke = invoke
    kernel.run(["T01.1"], 100, 0)
    assert len(packets) == 5 and not replies
    assert "Library.new" in json.dumps(packets[2]["retained_work"])
    assert all(name in json.dumps(packets[-1]["retrieved"]) for name in ("Library.new", "Library.other"))
    assert packets[-1]["requests_left"] == 0
    assert any(e["kind"] == "retire" for e in kernel.entries())
    assert len(runner.checker.calls) == 2
    print("Native mailbox: retrieve -> block -> resolver retrieve/check -> resume with facts/budget -> checked retirement passed")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as temporary:
        check(Path(temporary))
    with tempfile.TemporaryDirectory() as temporary:
        native_exchange(Path(temporary))

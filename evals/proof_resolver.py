"""Act: bounded Lean recovery through registered owner handlers, never model tools."""
import copy
import json

import evidence_protocol
import proof_loop
import proof_work_state
import study

SCHEMA = copy.deepcopy(evidence_protocol.SCHEMA)
SCHEMA["properties"]["outcome"]["enum"] = ["candidate", "need", "blocked", "propose"]
SCHEMA["properties"]["statement"] = {"type": ["string", "null"], "maxLength": 4096}
SCHEMA["required"].append("statement")
INSTRUCTIONS = evidence_protocol.INSTRUCTIONS + (
    " Resolve the obstruction using retained evidence and checker diagnostics. "
    "You may supply a proof of the original obligation, request evidence, or set outcome=propose "
    "with statement containing an exact Lean proposition for a supporting obligation and reason explaining "
    "its use. For propose, proof/need/names/fragment are null. Otherwise statement is null. "
    "A proposed obligation awaits owner admission; never treat it as a proved assumption.")


def parse(raw):
    limits = evidence_protocol.legacy.limits
    try:
        value = json.loads(raw, object_pairs_hook=limits.unique, parse_constant=limits.invalid_constant)
        if not isinstance(value, dict) or set(value) != set(SCHEMA["required"]):
            return None, "resolver response fields differ"
        statement = value.pop("statement")
        if value["outcome"] == "propose":
            if (not limits.valid_text(statement, 4096) or not limits.valid_text(value["reason"], 2048)
                    or any(value[key] is not None for key in ("proof", "need", "names", "fragment"))):
                return None, "proposal requires exact statement and reason only"
            return {**value, "statement": statement}, None
        if statement is not None:
            return None, "statement is inactive outside propose"
        return evidence_protocol.action(json.dumps(value))
    except (ValueError, TypeError, UnicodeError, RecursionError):
        return None, "invalid resolver JSON"


def typed(value, store):
    kind, nominal = {"candidate": ("Produce", "lean.ProofBody/v1"),
                     "need": ("Need", "lean.Evidence/v1"),
                     "propose": ("Propose", "lean.Obligation/v1"),
                     "blocked": ("Suspend", "work.Obstruction/v1")}[value["outcome"]]
    return {"kind": kind, "type": nominal, "payload": proof_work_state.put(store, value)}


def dispatch(runner, node, source, session, value):
    import work_state
    routed = work_state.route(typed(value, runner.store), proof_work_state.REGISTRY,
                             {"check", "retrieve", "propose", "suspend"})
    if routed["status"] == "awaiting_admission":
        runner.event("extension_proposed", slot=node["id"], proposal=routed["outcome"]["payload"],
                     work_state=study.digest(study.canonical(session.work_state)),
                     detail="Supporting obligation awaits trusted owner admission")
        return {"status": "prerequisite", "body": value["statement"] + "\n" + value["reason"], "declarations": []}
    if routed["status"] != "ready":
        return {"status": "needs_operator", "body": routed["reason"], "declarations": []}
    action = session.dispatch(json.dumps(value))
    proof_work_state.record(runner, node, source, session, action)
    if action["status"] == "candidate":
        assessment = runner.checker.check(node, action["proof"], source)
        proof_work_state.record(runner, node, source, session,
                                {"kind": "check", "candidate": study.digest(action["proof"].encode()),
                                 "assessment": assessment})
        if assessment["accepted"]:
            return {"status": "adaptation", "body": "Checked candidate for original obligation:\n" + action["proof"],
                    "declarations": []}
        return {"feedback": assessment.get("diagnostic") or assessment["status"]}
    if action["status"] == "retrieval_result":
        return {"feedback": None}
    if action["status"] == "refused":
        return {"feedback": action["reason"]}
    return {"status": "needs_operator", "body": action.get("reason") or action["status"], "declarations": []}


def run(runner, job, node, source, packet, initial):
    session = evidence_protocol.Session(runner.backend, runner.manifest["policy"]["max_requests"],
                                        runner.backend.snapshot, initial)
    proof_work_state.restore(runner, node, source, session)
    if session.work_state is None:
        proof_work_state.record(runner, node, source, session, {"status": "ready"})
    records, feedback = [], None
    reply = {"status": "needs_operator", "body": "Bounded resolver exhausted without an accepted result.", "declarations": []}
    for number in range(1, 3):
        current = {**packet, "retained_work": proof_work_state.evidence(runner, node, source),
                   "retrieved": session.retrieved, "requests_left": session.requests_left, "latest": feedback}
        result = runner.invoke(job, number, current, SCHEMA, INSTRUCTIONS, "function:resolve", node["id"])
        if result.get("admitted"):
            records.append(result)
        if not result.get("finished") or proof_loop.usage_sum([result.get("usage")]) is None:
            return result, None
        value, refusal = parse(result["text"])
        if refusal:
            feedback = refusal
            continue
        resolved = dispatch(runner, node, source, session, value)
        if "status" in resolved:
            reply = resolved
            break
        feedback = resolved["feedback"]
    usage = proof_loop.usage_sum([row.get("usage") for row in records])
    return {"finished": True, "text": json.dumps(reply), "usage": usage, "reason": None,
            "tokens": sum(usage.values()) if usage is not None else None, "turns": len(records)}, reply

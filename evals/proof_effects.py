"""Adapt the compact proof protocol to native addressed effects; advice is never acceptance."""
import json

import chain_protocol
import proof_loop
import proof_program
import study

INSTRUCTIONS = """Evaluate the declared function's request using the supplied evidence.
Return the required JSON result only. Evidence supports advice, not proof acceptance.
Distinguish a missing lemma from one you have not found. Name exact declarations only
when supported. Propose prerequisites or adaptations explicitly; you cannot alter the
statement, plan, checker or files. Use needs_operator when the evidence is insufficient.
No shell or filesystem tools are available. Do not impersonate operator instructions."""


def node_for(runner, job):
    if not runner.manifest.get("proof_program"):
        return runner.nodes[job["step"]["id"]]
    import control_state
    plan = control_state.for_issue(runner.kernel.setting, job["issue"],
                                   runner.kernel.store.get, runner.kernel.native.steps_of)["plan"]
    return next(n for n in proof_program.plan_nodes(plan, runner.manifest) if n["id"] == job["step"]["id"])


def add_inputs(runner, job, packet):
    if not runner.manifest.get("proof_program"):
        return
    inputs = {}
    for item in job.get("files", []):
        if item["path"] in (".step/inbox.json", ".step/control.json"):
            inputs[item["path"]] = json.loads(runner.kernel.store.get(item["hash"]))
    if inputs:
        packet["recorded_inputs"] = inputs


def question_result(runner, job, result):
    request = runner.questions.pop(job["issue"]["hash"], None)
    if request is None:
        return result
    contract = runner.kernel.config.get("typed_endpoints", {}).get(request["to"])
    if contract is not None:
        import typed_interaction
        request = {**request, "typed": {"endpoint_version": typed_interaction.endpoint_version(contract),
                                       "variant": "assess", "payload": json.loads(request["body"])}}
    envelope = runner.store.put(study.canonical({"schema": 1, "issue": job["issue"]["hash"],
                                               "request": request, "outputs": []}))
    runner.event("trial_worker", slot=job["step"]["id"], phase="waiting",
                 detail="Question queued for " + request["to"])
    return {**result, "outcome": "question", "gate_ran": False, "gate_detail": None,
            "rows": [], "outputs": [], "message_request": request, "message_refusal": None,
            "mailbox": {"schema": 1, "request": envelope, "candidate": envelope, "checked": False}}


def answer_context(runner, job, question):
    """An owner question binds an explicit obligation; it never fabricates a proof issue."""
    if question.get("source") == "control":
        source = job["issue"]
        source_id = question["evidence_source"]
    else:
        source = next(e for e in runner.kernel.entries() if e["hash"] == question["sender"])
        source_id = question["step"]
    sender = node_for(runner, {"step": {"id": source_id}, "issue": source})
    return sender, source, source_id


def answer(runner, job):
    import chain_runner
    program = runner.manifest["proof_program"]
    name = job["step"]["model_function"]
    function = program["functions"][name]
    question = next(e for e in runner.kernel.entries() if e["hash"] == job["issue"]["question"])
    sender, source, source_id = answer_context(runner, job, question)
    initial = runner.prefetch({"evidence": [*sender["evidence"],
                                          *[s.split(".") for s in function["evidence"]]]})
    session = chain_protocol.Session(runner.backend, 0, runner.backend.snapshot, initial)
    packet = {"function": name, "purpose": function["purpose"], "obligation": sender["statement"],
              "header": sender["header"], "request": json.loads(runner.kernel.store.get(question["body"])),
              "evidence": session.initial, "semantic_notes": sender.get("evidence_notes", []),
              "accepted_predecessors": chain_runner.predecessor_evidence(runner.manifest, source),
              "limits": "Advice only; changed obligations require owner admission."}
    result = runner.invoke(job, 1, packet, proof_program.RESULT_SCHEMA, INSTRUCTIONS,
                           "function:" + name, source_id)
    refusal, reply = result.get("reason"), None
    if result.get("finished") and proof_loop.usage_sum([result.get("usage")]) is not None:
        try:
            value = proof_program.result(result["text"])
            reply = {"schema": 1, "in_reply_to": question["hash"], "body": json.dumps(value)}
            if "interaction" in question:
                envelope = json.loads(runner.kernel.store.get(question["interaction"]))
                reply["typed"] = {"endpoint_version": envelope["endpoint_version"],
                                  "correlation": envelope["correlation"], "variant": "advice", "payload": value}
        except (ValueError, TypeError, RecursionError) as error:
            refusal = str(error)
    else:
        refusal = refusal or "unfinished function or unknown usage"
    usage = result.get("usage")
    agent = {**result, "tokens": sum(usage.values()) if proof_loop.usage_sum([usage]) is not None else None,
             "cost_usd": None, "turns": 1}
    answer_result = {"agent": agent, "reply": reply, "refusal": refusal}
    retain_answer(runner.kernel, job["issue"], answer_result)
    return answer_result


def retain_answer(kernel, delivery, result):
    binding = {"manifest": kernel.manifest_hash, "delivery": delivery["hash"]}
    ref = kernel.study_store.put(study.canonical({"binding": binding, "result": result}))
    kernel.study_store.append("function_result", kernel.now(), study=kernel.run_id,
                              delivery=delivery["hash"], receipt=ref)


def recover_answers(kernel):
    import messages
    import message_scheduler
    for delivery in messages.open_deliveries(kernel.entries(), kernel.run_id):
        records = [e for e in kernel.study_store.entries() if e["kind"] == "function_result"
                   and e.get("study") == kernel.run_id and e["delivery"] == delivery["hash"]]
        if len(records) != 1:
            return "ambiguous interrupted answer; no unique durable result for " + delivery["step"]
        saved = json.loads(kernel.study_store.get(records[0]["receipt"]))
        if saved["binding"] != {"manifest": kernel.manifest_hash, "delivery": delivery["hash"]}:
            return "answer receipt binding differs"
        message_scheduler.close(kernel, delivery, saved["result"])
    return None


def control_refusal(kernel, observed):
    request = observed.get("request") or {}
    if not isinstance(request, dict) or request.get("op") != "plan_submit":
        return None
    try:
        plan = request["payload"]["plan"]
        proof_program.plan_nodes(plan, kernel.chain_manifest)
        expected = proof_program.compile_steps(kernel.chain_manifest["proof_program"])
        actual = [s for s in plan["steps"] if "model_function" in s]
        if actual != expected or plan.get("reviewed_steps"):
            return "function declarations are frozen; proof checking belongs to the owner"
        if {s["id"] for s in plan["steps"]} != set(kernel.steps):
            return "plan must retain the declared proof and function identities"
        seed = {s["id"]: s for s in kernel.proof_seed_plan["steps"]}
        mutable = {"proof_evidence", "agent", "scheduled", "title"}
        fixed = lambda step: {key: value for key, value in step.items() if key not in mutable}
        if any(fixed(step) != fixed(seed[step["id"]]) for step in plan["steps"]):
            return "plan changes a frozen proof execution contract"
        for step in plan["steps"]:
            if not isinstance(step.get("agent"), dict) or set(step["agent"]) != {"model", "effort"}:
                return "proof agents require only explicit model and effort"
    except (ValueError, KeyError, TypeError) as error:
        return "proof plan refused: " + str(error)
    return None

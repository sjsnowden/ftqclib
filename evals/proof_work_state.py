"""Record/project the Lean instance of domain-neutral work state.

The owner writes states. Hash-checked, same-contract evidence crosses invocation
and mailbox boundaries. Candidate bytes remain unaccepted until the Lean gate.
"""
import json

import chain_protocol
import study

REGISTRY = {
    ("Produce", "lean.ProofBody/v1"): {"handler": "lean.check", "capability": "check"},
    ("Need", "lean.Evidence/v1"): {"handler": "lean.retrieve", "capability": "retrieve"},
    ("Propose", "lean.Obligation/v1"): {"handler": "owner.admit_extension", "capability": "propose"},
    ("Suspend", "work.Obstruction/v1"): {"handler": "owner.suspend", "capability": "suspend"},
}


def read(store, identity):
    raw = store.get(identity)
    if study.digest(raw) != identity:
        raise ValueError("work-state object identity differs")
    return json.loads(raw)


def put(store, value):
    return store.put(study.canonical(value))


def contract(runner, node, issue):
    return put(runner.store, {"type": "lean.ProofContract/v1", "obligation": node,
        "snapshot": runner.backend.snapshot, "source_commit": runner.manifest["source_commit"],
        "operands": issue["operands"], "policy": runner.manifest["policy"],
        "implementation": runner.manifest.get("sources", {}),
        "acceptance": {"handler": "lean.check", "exact_type": node["expected_type"],
                       "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"]}})


def latest(runner, binding):
    import work_state
    rows = [e for e in runner.store.entries() if e["kind"] == "work_state"
            and e.get("study") == runner.manifest["id"] and e.get("contract") == binding]
    if not rows:
        return None
    state = read(runner.store, rows[-1]["state"])
    refusal = work_state.validate(state)
    if refusal or state["contract"] != binding:
        raise ValueError(refusal or "work-state contract differs")
    return state


def restore(runner, node, issue, session):
    binding = contract(runner, node, issue)
    state = latest(runner, binding)
    session.work_state = state
    session.work_contract = binding
    if state is None:
        return session
    saved = read(runner.store, state["continuation"])
    budget = read(runner.store, state["budget"])
    if not 0 <= budget["retrievals_used"] <= session.max_requests:
        raise ValueError("continued retrieval budget exceeds contract")
    for mapping in (saved["names"], saved["queries"]):
        for response in mapping.values():
            if response is not None:
                session.validate(response)
    session.names.update(saved["names"])
    session.queries.update(saved["queries"])
    session.seen.update(saved["seen"])
    session.retrieved = saved["retrieved"]
    session.requests_used = budget["retrievals_used"]
    session.ineffective_requests = budget["ineffective_requests"]
    return session


def record(runner, node, issue, session, observation):
    import work_state
    store = runner.store
    continuation = put(store, {"issue": issue["hash"], "names": session.names, "queries": session.queries,
                              "seen": sorted(session.seen), "retrieved": session.retrieved})
    budget = put(store, {"retrievals_used": session.requests_used,
                         "ineffective_requests": session.ineffective_requests})
    previous = session.work_state
    if previous is None:
        authority = put(store, {"registry": [[*key, value] for key, value in REGISTRY.items()],
                                "grants": ["check", "retrieve", "propose", "suspend"]})
        previous = work_state.create(session.work_contract, continuation, authority, budget)
        put(store, previous)
    ref = put(store, observation)
    inputs = [put(store, value) for value in [*session.names.values(), *session.queries.values()] if value is not None]
    candidates = [put(store, {"type": "lean.ProofBody/v1", "proof": observation["proof"]})] if "proof" in observation else []
    obstruction = ref if observation.get("status") in ("blocked", "refused", "retrieval_failed") else None
    state = work_state.advance(previous, inputs=inputs, observations=[ref], candidates=candidates,
                               obstruction=obstruction, continuation=continuation, budget=budget)
    identity = put(store, state)
    runner.event("work_state", slot=node["id"], issue=issue["hash"], contract=session.work_contract, state=identity)
    session.work_state = state
    return identity


def evidence(runner, node, issue):
    state = latest(runner, contract(runner, node, issue))
    if state is None:
        return None
    saved = read(runner.store, state["continuation"])
    observations = [read(runner.store, ref) for ref in state["observations"]]
    checks = [{"candidate": row["candidate"], "status": row["assessment"]["status"],
               "accepted": row["assessment"]["accepted"],
               "diagnostic": chain_protocol.limits.bounded_text(row["assessment"].get("diagnostic") or "", 2048)}
              for row in observations if row.get("kind") == "check"]
    candidates = [{"reference": ref, "proof": chain_protocol.limits.bounded_text(
        read(runner.store, ref)["proof"], 2048)} for ref in state["candidates"]]
    return {"state": study.digest(study.canonical(state)), "retrieved": saved["retrieved"],
            "candidates": candidates, "checks": checks,
            "obstruction": read(runner.store, state["obstruction"]) if state["obstruction"] else None}

"""Bounded, shell-free proof attempts inside OntolKernel's ordinary dependency DAG.

Fresh model calls carry the obligation, admitted evidence and latest diagnostic.
The owner retains all observations, refuses unknown usage, caches repeated proof
checks, and stops as soon as protected checks accept. No transcript is replayed.
"""
import json
from pathlib import Path
import time
import uuid

import chain_check
import chain_protocol as protocol
import proof_loop
import study
import proof_program
import proof_effects


def known_usage(store, identity):
    events = [entry for entry in store.entries() if entry.get("study") == identity]
    starts = [entry for entry in events if entry["kind"] == "proposal_start"]
    ends = [entry for entry in events if entry["kind"] == "proposal_end"]
    keys = lambda rows: [(entry.get("issue"), entry.get("round"), entry.get("invocation")) for entry in rows]
    opened, closed = keys(starts), keys(ends)
    if (any(not isinstance(i, str) or not i or type(n) is not int or n < 1
            or not isinstance(v, str) or not v for i, n, v in opened + closed)
            or len(opened) != len({row[:2] for row in opened})
            or len(closed) != len({row[:2] for row in closed}) or set(opened) != set(closed)):
        return None
    return proof_loop.usage_sum([entry.get("usage") for entry in ends])


def admission(store, manifest):
    usage = known_usage(store, manifest["id"])
    if usage is None:
        return "an invocation is unfinished or has unknown usage; no further model admission"
    if sum(usage.values()) >= manifest["execution"]["observed_token_limit"]:
        return "study token admission threshold reached"
    cap = manifest.get("proof_program", {}).get("max_model_calls")
    calls = sum(e["kind"] == "proposal_start" and e.get("study") == manifest["id"] for e in store.entries())
    if cap is not None and calls >= cap:
        return "program model-call limit reached (proof and answer calls combined)"
    return None


def predecessor_evidence(manifest, issue):
    """Give exact admitted interfaces, not predecessor transcripts or opaque unversioned claims."""
    nodes = {node["id"]: node for node in manifest["nodes"]}
    found = []
    for operand in issue["operands"]:
        node = nodes[operand["step"]]
        if operand["path"] == node["path"]:
            found.append({"node": node["id"], "module": node["module"],
                          "declaration": node["statement"]})
    return found


def context(manifest, node, issue, ledger):
    return {"purpose": node["purpose"], "node": node["id"],
            "header": node["header"], "obligation": node["statement"],
            "accepted_predecessors": predecessor_evidence(manifest, issue),
            "acceptance": ["Return only the complete tactic body beginning with by; introduce all forall binders.",
                           "The owner fixes the statement, compiles it, checks its exact type and transitive axioms.",
                           "Use simp only, simpa only, dsimp only and simp_all only with explicit lemma lists.",
                           "No sorry/admit, new declarations, commands, native_decide or side effects.",
                           "Read supplied declarations before requesting more retrieval; no filesystem tools exist."],
            "completion": "Owner acceptance ends the node; use blocked with a precise missing prerequisite.",
            "failed_candidates": ledger[-6:], "semantic_notes": node.get("evidence_notes", [])}


def build_packet(manifest, node, issue, ledger, session, latest, requests_left):
    """Project current evidence only; immutable identity bindings stay in owner receipts."""
    formalism = {"schema": 1, "modules": [], "anchors": [],
                 "semantic_notes": manifest["formalism"]["semantic_notes"]}
    return protocol.packet(context(manifest, node, issue, ledger), formalism, session.snapshot_id,
                           requests_left=requests_left, latest=latest,
                           retrieved={"initial": session.initial, "retained": session.retrieved})


class Runner:
    def __init__(self, root, manifest, store, checker, backend):
        self.root, self.manifest, self.store = Path(root), manifest, store
        self.checker, self.backend, self.kernel = checker, backend, None
        self.nodes = {node["id"]: node for node in manifest["nodes"]}
        self.questions = {}

    def event(self, kind, **fields):
        return study.event(self.store, self.manifest["id"], kind, **fields)

    def admission_refusal(self):
        return admission(self.store, self.manifest)

    def prefetch(self, node):
        evidence, seen = [], set()
        for name in node["evidence"]:
            if tuple(name) in seen:
                continue
            seen.add(tuple(name))
            response = self.backend.call("read_declaration", name)
            evidence.append(response)
            if response["status"] not in ("ok", "missing"):
                raise ValueError("required initial declaration retrieval unavailable: " + ".".join(name))
        # All full lookup receipts remain in the store. Packet bounding happens before a model call.
        return evidence

    def launch(self, job, number, packet):
        return self.invoke(job, number, packet, protocol.SCHEMA, protocol.INSTRUCTIONS,
                           "proof-proposal", job["step"]["id"])

    def invoke(self, job, number, packet, schema, instructions, role, slot):
        import proposal_agent
        reason = admission(self.store, self.manifest)
        if reason:
            return {"finished": False, "reason": reason, "usage": None, "admitted": False}
        study.verify_sources(self.manifest)
        self.checker.verify()
        prompt = json.dumps(packet, ensure_ascii=False, separators=(",", ":"))
        if len(prompt.encode()) > self.manifest["policy"]["input_bytes_max"]:
            raise ValueError("assembled proof packet exceeds admitted byte limit")
        identity = {"session": job["issue"]["hash"], "invocation": uuid.uuid4().hex,
                    "role": role, "binding": job["issue"]["hash"]}
        directory = self.root / "workers" / identity["invocation"]
        directory.mkdir(parents=True)
        directory.chmod(0o500)
        config = {key: self.manifest["execution"][key] for key in
                  ("executable", "model", "effort", "deadline_seconds", "model_catalog")}
        config.update({key: job["issue"]["agent"][key] for key in ("model", "effort")})
        self.event("proposal_start", slot=slot, issue=job["issue"]["hash"], round=number,
                   invocation=identity["invocation"],
                   prompt=self.store.put(prompt.encode()), prompt_bytes=len(prompt.encode()),
                   detail=f"{role}: {config['model']} / {config['effort']}")
        result = proposal_agent.run(self.store, identity, str(directory), schema, instructions, prompt, config)
        self.event("proposal_end", slot=slot, issue=job["issue"]["hash"], round=number,
                   invocation=identity["invocation"],
                   result_object=self.store.put(study.canonical(result)), usage=result.get("usage"),
                   detail="proposal returned" if result.get("finished") else result.get("reason"))
        return {**result, "admitted": True}

    def answer(self, job):
        return proof_effects.answer(self, job)

    def retrieve(self, session, text, node, number, rounds):
        limit = self.manifest["policy"].get("max_retrieval_rounds", 2)
        selected, _ = protocol.action(text)
        retrieval = selected and selected["action"] in ("search_name", "read_declarations")
        if retrieval and rounds >= limit:
            action = session.outcome("refused", reason="retrieval round limit reached; propose a proof or report the missing premise")
        else:
            action = session.dispatch(text)
        if action["status"] not in ("candidate", "blocked"):
            self.event("tool_result", slot=node["id"], round=number, status=action["status"],
                       detail=action.get("reason") or action.get("operation"),
                       receipts=action["receipts"], observation=self.store.put(study.canonical(action)))
        return action, rounds + int(bool(retrieval))

    def assess(self, job, node, proof, number, checked):
        identity = study.digest(proof.encode())
        repeated = identity in checked
        if not repeated:
            self.event("trial_check", slot=node["id"], phase="started", round=number, candidate=identity)
            checked[identity] = self.checker.check(node, proof, job["issue"])
            self.event("trial_check", slot=node["id"], phase="completed", round=number,
                       assessment=self.store.put(study.canonical(checked[identity])))
        return identity, checked[identity], repeated

    def rounds(self, job, node, initial):
        policy = self.manifest["policy"]
        session = protocol.Session(self.backend, policy["max_requests"], self.backend.snapshot, initial)
        records, ledger, checked, latest, retrieval_rounds, repeats = [], [], {}, None, 0, 0
        assessment, reason = None, "per-node model-call limit reached"
        for number in range(1, policy["max_calls"] + 1):
            usage = proof_loop.usage_sum([record.get("usage") for record in records])
            if usage is None or sum(usage.values()) >= policy["node_token_limit"]:
                reason = "unknown usage or per-node token admission threshold reached"
                break
            left = session.requests_left if retrieval_rounds < policy.get("max_retrieval_rounds", 2) else 0
            packet = build_packet(self.manifest, node, job["issue"], ledger, session, latest, left)
            proof_effects.add_inputs(self, job, packet)
            result = self.launch(job, number, packet)
            if result["admitted"]:
                records.append(result)
            if not result.get("finished") or proof_loop.usage_sum([result.get("usage")]) is None:
                reason = result.get("reason") or "worker usage is unknown"
                break
            action, retrieval_rounds = self.retrieve(session, result["text"], node, number, retrieval_rounds)
            reason = "per-node model-call limit reached"
            if action["status"] == "retrieval_failed":
                reason = "owner retrieval unavailable: " + str(action["reason"])
                break
            if action["status"] == "retrieval_result":
                continue
            if action["ineffective"]:
                reason = action["reason"]
                if session.ineffective_requests + repeats >= policy.get("max_ineffective_rounds", 2):
                    reason = "no new evidence: " + reason
                    break
                latest = {**(latest or {}), "retrieval_refusal": reason}
                continue
            if action["status"] != "candidate":
                reason = action.get("reason", "retrieval failed")
                if action["status"] == "blocked" and self.manifest.get("proof_program"):
                    request = proof_program.question(self.manifest["proof_program"], node["id"], reason,
                                                     "Resume the original obligation using the recorded reply.")
                    if request:
                        self.questions[job["issue"]["hash"]] = request
                break
            proof = action["proof"]
            identity, assessment, repeated = self.assess(job, node, proof, number, checked)
            repeats += int(repeated)
            if assessment["accepted"]:
                return records, assessment, None, session.requests_used, len(checked)
            if assessment["status"] not in ("failed", "refused"):
                reason = "protected compiler/examiner unavailable; no speculative retry"
                break
            diagnostic = assessment.get("diagnostic") or "protected acceptance failed"
            ledger.append({"candidate": list(checked).index(identity) + 1, "round": number, "reason": diagnostic[:240]})
            latest = {"proof": protocol.limits.bounded_text(proof, 4096),
                      "diagnostic": protocol.limits.bounded_text(diagnostic)}
            if repeats + session.ineffective_requests >= policy.get("max_ineffective_rounds", 2):
                reason = "no new evidence: repeated rejected candidate"
                break
        return records, assessment, reason, session.requests_used, len(checked)

    def result(self, job, records, assessment, reason, searches, checks, elapsed):
        import verdict
        usage = proof_loop.usage_sum([row.get("usage") for row in records])
        accepted = assessment is not None and assessment["accepted"] and usage is not None
        summary = {"assessment": "accepted" if accepted else "unresolved", "reason": reason,
                   "tokens": sum(usage.values()) if usage is not None else None, "usage": usage,
                   "cost_usd": None, "model_calls": len(records), "elapsed_seconds": elapsed,
                   "worker_tool_calls": 0 if all(row.get("worker_tool_calls") == 0 for row in records) else None,
                   "retrieval_requests": searches, "distinct_candidates_checked": checks,
                   "proposals": self.store.put(study.canonical(records))}
        row = {"name": "protected Lean acceptance", "ok": accepted,
               "source": "work" if assessment and assessment["status"] in ("passed", "failed", "refused")
                         else "dependency", "detail": reason or "exact type and transitive axioms checked"}
        node, outputs = self.nodes[job["step"]["id"]], []
        if accepted:
            outputs = [{"path": node["path"], "hash": assessment["source"], "mode": ""},
                       {"path": ".ontologic/certificates/" + node["id"] + ".json",
                        "hash": assessment["certificate"], "mode": ""}]
        agent = {"finished": True, "reason": reason, "tokens": summary["tokens"], "usage": usage,
                 "cost_usd": None, "text": "owner accepted proof" if accepted else reason, "stderr": "",
                 "duration_ms": round(elapsed * 1000), "turns": len(records)}
        return {"agent": agent, "outputs": outputs, "rows": [row], "contract": None,
                "gate_ran": True, "gate_detail": row["detail"], "outcome": verdict.outcome([row]),
                "outside": [], "fault": None, "fault_refusal": None, "reads": None,
                "rows_before": None, "review": None, "chain": summary}

    def __call__(self, job):
        node, started = proof_effects.node_for(self, job), time.monotonic()
        self.event("trial_start", slot=node["id"], issue=job["issue"]["hash"], detail=node["purpose"])
        reason = admission(self.store, self.manifest)
        if reason:
            outcome = ([], None, reason, 0, 0)
        else:
            initial = self.prefetch(node)
            outcome = self.rounds(job, node, initial)
        result = self.result(job, *outcome, time.monotonic() - started)
        result = proof_effects.question_result(self, job, result)
        self.event("trial_end", slot=node["id"], result=result["chain"])
        if result["outcome"] == "question":
            self.event("node_waiting", slot=node["id"], detail="Waiting for " + result["message_request"]["to"])
        self.kernel.retain_result(job["issue"], result)
        if result["outcome"] not in ("green", "question"):
            self.event("node_blocked", slot=node["id"], reason=result["chain"]["reason"], result=result["chain"])
        return result

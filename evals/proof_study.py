"""Act: sequential F01 comparison with a tool-free proposer and owner-executed effects.

Arms A (compact local evidence) and B (same plus bounded Loogle) use the same model,
effort, proof boundary and owner checks. Existing full-agent run 2 is historical,
not a concurrent randomized control. Source/check requests and results are immutable.
"""
import argparse
import base64
import json
from pathlib import Path
import shutil
import sys
import time
import uuid

import fixtures
import loogle
import proof_loop
import runtime
import study


def write(path, value):
    study.write_new(path, study.canonical(value))


def prepare(args):
    """Prepare one source baseline and six independent worktrees, with no model calls."""
    root, source, kernel = args.study.resolve(), args.source.resolve(), args.kernel.resolve()
    catalog = args.model_catalog.resolve()
    catalog_sha256 = study.digest(catalog.read_bytes())
    root.mkdir(parents=True, exist_ok=False)
    Store, _, _ = study.kernel_imports(kernel)
    store = Store(str(root / "records"))
    (root / "owner").mkdir()
    repo, reference = root / "owner/repo.git", root / "owner/reference"
    study.git(source, "clone", "--quiet", "--bare", "--no-local", str(source), str(repo))
    study.git(repo, "worktree", "add", "--detach", str(reference), fixtures.REVISION)
    seed, original = root / "owner/seeds/F01", root / "owner/references/F01"
    specification = study.owner_projection(reference, seed, "F01")
    study.owner_projection(reference, original, "F01", "reference")
    tools = runtime.prepare("F01", args.runtime.resolve() / "reference", args.runtime.resolve(), specification)
    for name, data in runtime.public_files("F01", specification["contract"], tools).items():
        study.write_new(seed / name, data)
        study.write_new(original / name, data)
    commit = study.seed_commit(repo, "F01", fixtures.REVISION, seed, root / "owner/seed-worktrees/F01")
    context = proof_loop.evidence(fixtures.tree_files(seed), specification["contract"])
    selected = []
    for repetition in range(1, args.repetitions + 1):
        for condition in ("AB" if repetition % 2 else "BA"):
            selected.append({"id": uuid.uuid4().hex, "task": "F01", "condition": condition, "repetition": repetition})
    manifest = {"schema": 1, "id": args.id, "source_commit": fixtures.REVISION,
                "kernel": str(kernel), "runtime": str(args.runtime.resolve()), "slots": selected,
                "tasks": {"F01": {"contract": specification["contract"], "seed": str(seed),
                                  "reference": str(original), "seed_commit": commit, "runtime": tools}},
                "execution": {"provider": "codex", "executable": args.executable,
                              "model": args.model, "effort": args.effort, "deadline_seconds": 120,
                              "model_catalog": str(catalog), "model_catalog_sha256": catalog_sha256,
                              "budget_usd": None, "observed_token_limit": 350000},
                "protocol": "proof-proposals-v2", "evidence": store.put(study.canonical(context)),
                "policy": {"condition_A": "compact local evidence; no worker tools",
                           "condition_B": "same plus owner Loogle prefetch and bounded follow-up search",
                           "prefetch_query": "ZMod, _ + _ = 0", "max_calls": 6, "max_searches": 2,
                           "concurrency": 1, "context": "fresh evidence + latest candidate/diagnostics only",
                           "input_bytes_max": 24576, "search_hits_max": 5,
                           "baseline": "historical run 2; no isolated causal estimate"},
                "sources": study.source_objects(store, kernel)}
    write(root / "manifest.json", manifest)
    identity = store.put(study.canonical(manifest))
    study.write_new(root / "manifest.ref", identity.encode())
    study.event(store, manifest["id"], "study_pin", manifest=identity)
    study.event(store, manifest["id"], "stage", name="prepared", detail="Compact A / Loogle B; awaiting controls")
    print(json.dumps({"study": str(root), "manifest": identity, "slots": len(selected)}), flush=True)


def search(store, manifest, query, *, slot=None, round_number=0):
    request = store.put(study.canonical({"operation": "loogle", "query": query,
                                       "client": manifest["sources"][str(Path(loogle.__file__).resolve())]}))
    study.event(store, manifest["id"], "tool_request", slot=slot, round=round_number,
                detail="Loogle search", request=request)
    started = time.monotonic()
    result = loogle.search(query, max_hits=manifest["policy"]["search_hits_max"])
    result["elapsed_seconds"] = time.monotonic() - started
    identity = store.put(study.canonical(result))
    study.event(store, manifest["id"], "tool_result", slot=slot, round=round_number,
                detail="Loogle " + result["status"], request=request, result_object=identity)
    return {"query": query, "status": result["status"], "hits": result.get("hits", []),
            "receipt": identity, "advisory": True,
            "note": "Public current Mathlib search; every used declaration must compile with the pinned toolchain."}


def diagnostic(store, assessment):
    """Only public target/consumer output enters repair context; private examiner output never does."""
    reasons = assessment.get("reasons", [])
    if reasons:
        return proof_loop.bounded_text("\n".join(reasons))
    for name in ("target", "consumers"):
        check = assessment.get("checks", {}).get(name)
        if check and check.get("returncode") != 0:
            receipt = json.loads(store.get(check["observation"]))
            records = store.get(receipt["capture"]).splitlines()
            output = b"".join(base64.b64decode(row["data_base64"]) for line in records
                              if (row := json.loads(line)).get("kind") == "bytes")
            return {"stage": name, **proof_loop.bounded_text(output.decode("utf-8", errors="replace"))}
    return None


def check_proof(root, manifest, store, checker, trial, round_number, proof, runtime_cache):
    identity = trial.name + "-" + str(round_number)
    seed = Path(manifest["tasks"]["F01"]["seed"])
    proposed, reason = proof_loop.candidate_source((seed / fixtures.Z_SHEAR).read_bytes(), proof)
    if reason:
        return {"accepted": False, "status": "refused", "reasons": [reason]}, None
    candidate = trial / "candidates" / str(round_number)
    shutil.copytree(seed, candidate)
    (candidate / fixtures.Z_SHEAR).write_bytes(proposed)
    request = store.put(study.canonical({"operation": "check_candidate", "source": store.put(proposed),
                                       "baseline": manifest["evidence"], "round": round_number}))
    study.event(store, manifest["id"], "trial_check", slot=trial.name, phase="started", request=request)
    assessment = study.check_candidate(root, manifest, store, checker, "F01", candidate, identity, runtime_cache)
    ref = store.put(study.canonical(assessment))
    study.event(store, manifest["id"], "trial_check", slot=trial.name, phase="completed", assessment=ref)
    return assessment, candidate


def launch(store, manifest, trial, round_number, packet):
    """One compact observed proposal; no previous provider thread is resumed."""
    import proposal_agent
    prompt = json.dumps(packet, ensure_ascii=False, separators=(",", ":"))
    if len(prompt.encode("utf-8")) > manifest["policy"]["input_bytes_max"]:
        return {"finished": False, "reason": "assembled input byte limit", "usage": None}
    binding = store.put(study.canonical({"study": manifest["id"], "slot": trial.name,
                                        "round": round_number, "protocol": manifest["protocol"],
                                        "evidence": manifest["evidence"]}))
    identity = {"session": trial.name, "invocation": uuid.uuid4().hex, "role": "proof-proposal", "binding": binding}
    directory = trial / "model" / str(round_number)
    directory.mkdir(parents=True)
    directory.chmod(0o500)
    study.event(store, manifest["id"], "proposal_start", slot=trial.name, round=round_number,
                prompt=store.put(prompt.encode()), prompt_bytes=len(prompt.encode()), binding=binding,
                detail=manifest["execution"]["model"] + " " + manifest["execution"]["effort"] +
                       ": compact proof proposal " + str(round_number))
    config = {key: manifest["execution"][key] for key in
              ("executable", "model", "effort", "deadline_seconds", "model_catalog")}
    result = proposal_agent.run(store, identity, str(directory), proof_loop.SCHEMA,
                                proof_loop.INSTRUCTIONS, prompt, config)
    ref = store.put(study.canonical(result))
    study.event(store, manifest["id"], "proposal_end", slot=trial.name, round=round_number,
                result_object=ref, detail="proposal returned" if result.get("finished") else result.get("reason"))
    return result


def next_effect(raw, searches_left):
    return proof_loop.action(raw, searches_left=searches_left)


def rounds(root, manifest, store, checker, trial, context, retrieval, runtime_cache, known_before):
    """The parent owns bounded continuation; successful owner checks end work without another model call."""
    records, previous, searches, checks, checked = [], None, 0, 0, {}
    enabled = retrieval is not None
    assessment, accepted_path = {"accepted": False, "status": "unresolved"}, None
    reason, termination = "model call limit", "rejected"
    for number in range(1, manifest["policy"]["max_calls"] + 1):
        total = proof_loop.usage_sum([row["usage"] for row in records])
        if total is None or known_before + sum(total.values()) >= manifest["execution"]["observed_token_limit"]:
            reason, termination = "unknown usage or token admission limit", "unresolved"
            break
        packet = proof_loop.packet(context, search_enabled=enabled and searches < manifest["policy"]["max_searches"],
                                   latest=previous, retrieved=retrieval)
        result = launch(store, manifest, trial, number, packet)
        records.append(result)
        if not result.get("finished"):
            reason = result.get("reason", "proposal invocation failed")
            termination = "unresolved"
            break
        action, reason = next_effect(result["text"],
                                     manifest["policy"]["max_searches"] - searches if enabled else 0)
        if reason:
            termination = "unresolved"
            break
        if action["action"] == "blocked":
            reason = action["reason"]
            termination = "blocked"
            break
        if action["action"] == "search":
            retrieval = search(store, manifest, action["query"], slot=trial.name, round_number=number)
            searches += 1
            continue
        checks += 1
        identity = study.digest(action["proof"].encode())
        if identity in checked:
            assessment, candidate = checked[identity]
            study.event(store, manifest["id"], "tool_result", slot=trial.name, round=number,
                        detail="identical candidate: reused recorded check", candidate=identity,
                        assessment=store.put(study.canonical(assessment)))
        else:
            assessment, candidate = check_proof(root, manifest, store, checker, trial, number, action["proof"], runtime_cache)
            checked[identity] = assessment, candidate
        if assessment.get("accepted"):
            accepted_path, reason = candidate, None
            termination = "accepted"
            break
        if assessment.get("status") not in ("failed", "refused"):
            reason, termination = "owner check incomplete or unavailable", "unresolved"
            break
        feedback = diagnostic(store, assessment)
        if feedback is None:
            reason = "owner acceptance failed; private examiner details withheld"
            termination = "rejected" if assessment.get("status") in ("failed", "refused") else "unresolved"
            break
        previous = {"proof": action["proof"], "diagnostic": feedback}
    else:
        reason = "model call limit"
    return records, assessment, accepted_path, reason, searches, checks, len(checked), termination


def run_trial(root, manifest, store, checker, slot, prefetch, runtime_cache, known_before):
    trial = root / "trials" / slot["id"]
    trial.mkdir(parents=True)
    worktree = trial / "worktree"
    study.git(root / "owner/repo.git", "worktree", "add", "--detach", str(worktree),
              manifest["tasks"]["F01"]["seed_commit"])
    context = json.loads(store.get(manifest["evidence"]))
    study.event(store, manifest["id"], "trial_start", slot=slot["id"],
                detail="compact local" if slot["condition"] == "A" else "compact + Loogle")
    started = time.monotonic()
    records, assessment, candidate, reason, searches, checks, distinct_checks, termination = rounds(
        root, manifest, store, checker, trial, context, prefetch if slot["condition"] == "B" else None,
        runtime_cache, known_before)
    usage = proof_loop.usage_sum([row.get("usage") for row in records])
    worker_actions = [row.get("worker_tool_calls") for row in records]
    result = {"assessment": termination if termination in ("accepted", "rejected") else "unresolved",
              "execution": "completed" if termination in ("accepted", "rejected") else termination, "reason": reason,
              "usage": usage, "tokens": sum(usage.values()) if usage is not None else None,
              "cost_usd": None, "model_calls": len(records),
              "worker_tool_calls": sum(worker_actions) if all(type(value) is int for value in worker_actions) else None,
              "followup_searches": searches, "check_requests": checks, "distinct_candidates_checked": distinct_checks,
              "reused_checks": checks - distinct_checks, "elapsed_seconds": time.monotonic() - started,
              "assessment_object": store.put(study.canonical(assessment)),
              "proposals": store.put(study.canonical(records))}
    study.event(store, manifest["id"], "trial_worker", slot=slot["id"], detail="proposal sequence closed")
    if candidate is not None:
        source = (candidate / fixtures.Z_SHEAR).read_bytes()
        (worktree / fixtures.Z_SHEAR).write_bytes(source)
        study.git(worktree, "add", "--", fixtures.Z_SHEAR)
        study.git(worktree, "commit", "-q", "-m", "Accepted compact proof " + slot["id"])
        result["checkpoint"] = study.git(worktree, "rev-parse", "HEAD").decode().strip()
        result["source"] = store.put(source)
    study.event(store, manifest["id"], "trial_end", slot=slot["id"], result=result)
    print(json.dumps({"slot": slot, "result": result}), flush=True)
    return result


def run(root, manifest, store, checker):
    import proposal_agent
    endings = [row for row in store.entries() if row["kind"] == "controls_end"]
    if not endings or endings[-1]["passed"] is not True:
        raise ValueError("controls must pass before model admission")
    if any(row["kind"] == "trial_start" for row in store.entries()):
        raise ValueError("retain prior work; prepare a fresh study rather than replaying admissions")
    # proposal_agent.run performs its actual-CLI no-tools transport audit before every live call.
    catalog = Path(manifest["execution"]["model_catalog"])
    if study.digest(catalog.read_bytes()) != manifest["execution"]["model_catalog_sha256"]:
        raise ValueError("model capability catalog changed after pinning")
    prefetch = search(store, manifest, manifest["policy"]["prefetch_query"])
    if prefetch["status"] != "ok":
        raise ValueError("Loogle prefetch unavailable; do not silently change the search arm")
    runtime_cache, results, known, stopped = {}, [], 0, None
    for slot in manifest["slots"]:
        study.verify_sources(manifest)
        runtime.verify(manifest["tasks"]["F01"]["runtime"], cache=runtime_cache)
        result = run_trial(root, manifest, store, checker, slot, prefetch, runtime_cache, known)
        results.append({**slot, **result})
        if result["tokens"] is not None:
            known += result["tokens"]
        if result["tokens"] is None or result["assessment"] == "unresolved":
            stopped = result["reason"] or ("unknown token usage" if result["tokens"] is None else "unresolved trial")
            break
        if known >= manifest["execution"]["observed_token_limit"]:
            stopped = "token admission limit"
            break
    write(root / "report.json", {"study": manifest["id"], "trials": results, "tokens": known,
                                 "complete": stopped is None and len(results) == len(manifest["slots"]),
                                 "unknown_token_invocations": sum(row["tokens"] is None for row in results),
                                 "stopped": stopped})
    if stopped:
        study.event(store, manifest["id"], "stage", name="stopped", detail=stopped)
        return 2
    study.event(store, manifest["id"], "study_end", detail="Compact comparison complete", tokens=known)
    return 0


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("prepare")
    for name in ("study", "source", "kernel", "runtime"):
        create.add_argument("--" + name, type=Path, required=True)
    create.add_argument("--id", required=True)
    create.add_argument("--executable", required=True)
    create.add_argument("--model-catalog", type=Path, required=True)
    create.add_argument("--model", default="gpt-5.6-luna")
    create.add_argument("--effort", default="medium")
    create.add_argument("--repetitions", type=int, choices=(1, 2, 3), default=3)
    for command in ("controls", "run"):
        commands.add_parser(command).add_argument("study", type=Path)
    args = parser.parse_args()
    if args.command == "prepare":
        return prepare(args)
    root = args.study.resolve()
    manifest, store, checker, _ = study.load(root)
    with study.admission_lock(root):
        study.verify_sources(manifest)
        try:
            if args.command == "controls":
                return 0 if study.controls(root, manifest, store, checker) else 2
            return run(root, manifest, store, checker)
        except Exception as error:
            study.event(store, manifest["id"], "stage", name="blocked", detail=str(error)[:1000])
            raise


if __name__ == "__main__":
    raise SystemExit(main())

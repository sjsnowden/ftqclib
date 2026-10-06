"""Adopt verified completed proof nodes into a new, separately budgeted study.

Old logs and objects retain their exact identities. An adoption certificate binds
the closed source scope and every inherited retirement. It does not turn unknown
old token usage into zero, admit a model call, or change a frozen theorem. The
caller owns both study admission locks while adopting, and supplies the protected
result validator; no compiler or model is invoked here.
"""
import json
from pathlib import Path
import re

import chain_kernel
import proof_loop
import study

NODE_FIELDS = ("id", "module", "path", "imports", "name", "header", "statement", "expected_type", "deps")
BASE_FIELDS = ("source_commit", "snapshot_id", "compiler", "formalism")
OBJECTS_MAX = 100000
OBJECT_BYTES_MAX = 2 * 1024 ** 3
LOG_BYTES_MAX = 32 * 1024 ** 2


def decode_log(data, head, native):
    """Validate one complete historical log without consulting mutable filesystem state."""
    if len(data) > LOG_BYTES_MAX or not data.endswith(b"\n"):
        raise ValueError("historical log is empty, truncated or over its byte bound")
    entries, previous = [], None
    for line in data.splitlines():
        entry = json.loads(line)
        digest = native.sha256(native.canonical({key: value for key, value in entry.items() if key != "hash"}))
        if entry["hash"] != digest or entry["parents"] != ([previous] if previous else []):
            raise ValueError("historical log hash or parent differs")
        entries.append(entry)
        previous = digest
    if previous != head:
        raise ValueError("historical log differs from its closed head")
    return entries


def source_state(root, native):
    manifest_data = (root / "manifest.json").read_bytes()
    manifest = json.loads(manifest_data)
    reference = (root / "manifest.ref").read_text().strip()
    records = native.Store(str(root / "records"))
    if native.sha256(manifest_data) != reference or records.get(reference) != manifest_data:
        raise ValueError("source manifest identity differs")
    config = manifest["kernel_config"]
    kernel = native.Store(str(root / "worktree" / config["state"] / "log"), records.objects)
    logs = {"study": records, "kernel": kernel}
    retained, entries = {}, {}
    for name, store in logs.items():
        data = Path(store.log).read_bytes()
        entries[name] = decode_log(data, store.head_hash(), native)
        retained[name] = {"head": store.head_hash(), "bytes": data}
    for identity in {row["run"] for row in entries["kernel"] if "run" in row}:
        if native.state_module.open_issues(entries["kernel"], identity):
            raise ValueError("source contains an open native invocation")
        if native.messages.open_deliveries(entries["kernel"], identity):
            raise ValueError("source contains an open message delivery")
    if entries["kernel"][-1]["kind"] != "end":
        raise ValueError("source native run has no closed end")
    pin = native.state_module.latest_pin(entries["kernel"], manifest["id"])
    if pin is None or pin["config"].get("chain_manifest") != reference:
        raise ValueError("source kernel pin does not bind its manifest")
    return {"manifest": manifest, "manifest_hash": reference, "records": records, "kernel": kernel,
            "logs": retained, "entries": entries, "worktree": root / "worktree"}


def copy_objects(source, destination):
    """Copy immutable objects by verified identity; never rewrite source facts."""
    count, total = 0, 0
    for store in (source["records"], source["kernel"]):
        for path in Path(store.objects).glob("*/*"):
            digest = path.parent.name + path.name
            if not re.fullmatch(r"[0-9a-f]{64}", digest) or path.is_symlink() or not path.is_file():
                raise ValueError("source object directory contains an unknown entry")
            count += 1
            total += path.stat().st_size
            if count > OBJECTS_MAX or total > OBJECT_BYTES_MAX:
                raise ValueError("source object import exceeds its bound")
            if destination.put(store.get(digest)) != digest:
                raise ValueError("immutable object changed while copying")


def usage_exposure(events, identity):
    """Retain known totals and exact unresolved invocations as separate quantities."""
    starts = [row for row in events if row.get("study") == identity and row["kind"] == "proposal_start"]
    ends = [row for row in events if row.get("study") == identity and row["kind"] == "proposal_end"]
    key = lambda row: (row.get("issue"), row.get("round"), row.get("invocation"))
    if len({key(row) for row in starts}) != len(starts) or len({key(row) for row in ends}) != len(ends):
        raise ValueError("duplicate source invocation records")
    by_key = {key(row): row for row in ends}
    if not set(by_key) <= {key(row) for row in starts}:
        raise ValueError("source usage closes an unknown invocation")
    known, unknown = [], []
    for row in starts:
        end = by_key.get(key(row))
        usage = proof_loop.usage_sum([end.get("usage")]) if end else None
        if usage is None:
            unknown.append({"source_study": identity, "issue": row.get("issue"), "round": row.get("round"),
                            "invocation": row.get("invocation"), "slot": row.get("slot"),
                            "reason": "usage unknown" if end else "invocation has no recorded end"})
        else:
            known.append(usage)
    totals = proof_loop.usage_sum(known)
    return {"source_study": identity, "model_calls": len(starts), "known_usage": totals,
            "known_tokens": sum(totals.values()), "usage_complete": not unknown,
            "unknown_invocations": unknown, "tokens": None if unknown else sum(totals.values()),
            "new_admission_budget": False}


def compatible(source, manifest, worktree, native):
    """Freeze mathematical meaning while allowing a separately versioned implementation and policy."""
    old = source["manifest"]
    if old["id"] == manifest["id"] or any(old.get(key) != manifest.get(key) for key in BASE_FIELDS):
        raise ValueError("continuation changes its identity or mathematical baseline")
    old_nodes = {node["id"]: node for node in old["nodes"]}
    new_nodes = {node["id"]: node for node in manifest["nodes"]}
    retired = native.state_module.retired(source["entries"]["kernel"])
    if not retired or not set(retired) <= set(new_nodes):
        raise ValueError("continuation lacks accepted nodes")
    for identity in retired:
        if any(old_nodes[identity].get(key) != new_nodes[identity].get(key) for key in NODE_FIELDS):
            raise ValueError("accepted theorem, imports or dependencies changed: " + identity)
    config = manifest["kernel_config"]
    new_plan, new_steps = native.load_steps(str(worktree), config["plan"])
    ignored = tuple(config.get("definition_ignored", native.decide.DEFINITION_IGNORED))
    definitions = native.decide.step_definitions(new_steps, ignored)
    pins = {row["run"]: row for row in source["entries"]["kernel"] if row["kind"] == "pin"}
    for identity, retirement in retired.items():
        pin = pins[retirement["run"]]
        plan = json.loads(source["kernel"].get(pin["plan_version"]))
        prior = native.decide.step_definitions(native.steps_of(plan), ignored)
        if prior[identity] != definitions[identity]:
            raise ValueError("accepted native step definition changed: " + identity)
    return retired, definitions


def origin_history(source, retirement, store, native):
    """Follow at most eight admitted source generations to the original result journal."""
    current = source
    for _ in range(8):
        if current["manifest"]["id"] == retirement["run"]:
            return current["entries"]
        reference = current["manifest"].get("continuation")
        if reference is None:
            raise ValueError("inherited retirement has no admitted origin")
        certificate = json.loads(store.get(reference))
        manifest = json.loads(store.get(certificate["source_manifest"]))
        history = {name: decode_log(store.get(value["object"]), value["head"], native)
                   for name, value in certificate["logs"].items()}
        if (certificate["target_study"] != current["manifest"]["id"]
                or history["kernel"] != current["entries"]["kernel"][:len(history["kernel"])]):
            raise ValueError("inherited origin is not an admitted native prefix")
        current = {"manifest": manifest, "entries": history}
    raise ValueError("continuation ancestry exceeds eight generations")


def prior_exposure(source, store):
    current = usage_exposure(source["entries"]["study"], source["manifest"]["id"])
    reference = source["manifest"].get("continuation")
    if reference is None:
        return current
    prior = json.loads(store.get(reference))["prior_usage"]
    known = proof_loop.usage_sum([current["known_usage"], prior["known_usage"]])
    unknown = [*prior["unknown_invocations"], *current["unknown_invocations"]]
    return {**current, "model_calls": prior["model_calls"] + current["model_calls"],
            "known_usage": known, "known_tokens": sum(known.values()), "usage_complete": not unknown,
            "tokens": None if unknown else sum(known.values()), "unknown_invocations": unknown,
            "ancestry": prior.get("ancestry", [prior["source_study"]]) + [current["source_study"]]}


def accepted_row(source, retirement, manifest, worktree, store, validator, native):
    """Re-admit source and protected check receipts, including the exact Git projection."""
    entries = source["entries"]["kernel"]
    issue = next(row for row in entries if row["hash"] == retirement["issue"])
    if native.state_module.stale_operands(entries, issue):
        raise ValueError("inherited result has stale operands")
    origin = origin_history(source, retirement, store, native)
    records = [row for row in origin["study"] if row["kind"] == "node_result"
               and row.get("study") == retirement["run"] and row.get("issue") == issue["hash"]]
    if len(records) != 1:
        raise ValueError("inherited result lacks one durable receipt")
    record = records[0]
    receipt = json.loads(store.get(record["receipt"]))
    pin = native.state_module.latest_pin(entries, retirement["run"])
    if receipt != {"binding": chain_kernel.issue_binding(issue, pin["config"]["chain_manifest"]),
                   "result": record["result"]}:
        raise ValueError("inherited durable receipt differs from its issue")
    result = json.loads(store.get(record["result"]))
    if result["outcome"] != "green" or result["outputs"] != retirement["outputs"]:
        raise ValueError("inherited result differs from its accepted outputs")
    plan, steps = native.load_steps(str(worktree), manifest["kernel_config"]["plan"])
    refusal = chain_kernel.output_refusal(steps[issue["step"]], result) or validator(issue, result)
    if refusal is not None:
        raise ValueError("inherited protected result refused: " + str(refusal))
    observations = [row for row in origin["study"] if row["kind"] == "node_retired"
                    and row.get("retirement") == retirement["hash"]]
    checkpoint = chain_kernel.existing_checkpoint(worktree, retirement)
    if len(observations) != 1 or observations[0]["checkpoint"] != checkpoint:
        raise ValueError("inherited retirement lacks its recorded Git checkpoint")
    chain_kernel.verify_checkpoint(worktree, checkpoint, retirement, native.sha256)
    for output in retirement["outputs"]:
        data = store.get(output["hash"])
        if (worktree / output["path"]).read_bytes() != data:
            raise ValueError("inherited worktree output differs from accepted bytes")
    return {"step": retirement["step"], "source_study": retirement["run"],
            "retirement": retirement["hash"], "issue": issue["hash"],
            "outputs": retirement["outputs"], "checkpoint": checkpoint, "result": record["result"],
            "receipt": record["receipt"], "source_usage": result.get("chain", {})}


def target_commit(source, worktree, manifest):
    """Only owner control files may change between the old contribution and new preparation."""
    origin = chain_kernel.git(source["worktree"], "rev-parse", "HEAD").decode().strip()
    current = chain_kernel.git(worktree, "rev-parse", "HEAD").decode().strip()
    chain_kernel.git(worktree, "merge-base", "--is-ancestor", origin, current)
    config = manifest["kernel_config"]
    allowed = {config[key] for key in ("plan", "profile", "targets", "binding")}
    allowed.add(".ontologic/.gitignore")
    changed = chain_kernel.git(worktree, "diff", "--name-only", "-z", origin, current)
    if not {item.decode() for item in changed.split(b"\0") if item} <= allowed:
        raise ValueError("new preparation changed files outside owner controls")
    if chain_kernel.git(worktree, "status", "--porcelain", "--untracked-files=no"):
        raise ValueError("target contribution worktree has modified tracked files")
    return origin, current


def adopt(source_root, worktree, manifest, store, validate_result):
    """Import a closed study; return manifest['continuation'] before final manifest pinning.

    Target Git HEAD descends from the source contribution with only owner control
    changes. Target logs are fresh, and plan files already exist. This function only
    prepares evidence; neither an old unknown call nor a new call is resumed.
    """
    native = chain_kernel.native_modules(manifest["kernel"])
    source = source_state(Path(source_root), native)
    worktree = Path(worktree)
    commit, prepared = target_commit(source, worktree, manifest)
    target = native.Store(str(worktree / manifest["kernel_config"]["state"] / "log"), store.objects)
    if Path(target.log).exists() or Path(target.head).exists() or store.entries():
        raise ValueError("continuation requires fresh target logs")
    retired, definitions = compatible(source, manifest, worktree, native)
    copy_objects(source, store)
    rows = [accepted_row(source, row, manifest, worktree, store, validate_result, native)
            for row in retired.values()]
    logs = {name: {"head": value["head"], "object": store.put(value["bytes"])}
            for name, value in source["logs"].items()}
    certificate = {"schema": 1, "source_study": source["manifest"]["id"], "target_study": manifest["id"],
                   "source_manifest": source["manifest_hash"], "source_commit": commit,
                   "prepared_commit": prepared, "logs": logs,
                   "baseline": {key: manifest.get(key) for key in BASE_FIELDS},
                   "definitions": {key: definitions[key] for key in retired}, "accepted": rows,
                   "prior_usage": prior_exposure(source, store),
                   "prompt_metadata_changed": [row["id"] for row in manifest["nodes"] if row["id"] in retired
                       and row != next(old for old in source["manifest"]["nodes"] if old["id"] == row["id"])]}
    reference = store.put(native.canonical(certificate))
    study.write_new(Path(target.log), source["logs"]["kernel"]["bytes"])
    study.write_new(Path(target.head), (source["logs"]["kernel"]["head"] + "\n").encode())
    study.event(store, manifest["id"], "continuation_adopted", certificate=reference,
                source_study=certificate["source_study"], prior_usage=certificate["prior_usage"])
    for row in rows:
        inherited_event(store, manifest["id"], certificate, reference, row)
    return reference


def inherited_event(store, identity, certificate, reference, row):
    summary = {"assessment": "accepted", "inherited": True, "model_calls": 0, "tokens": 0,
               "worker_tool_calls": 0, "elapsed_seconds": 0, "reason": "verified prior acceptance"}
    study.event(store, identity, "node_retired", slot=row["step"], issue=row["issue"],
                retirement=row["retirement"], checkpoint=row["checkpoint"], result=summary,
                result_object=row["result"], inherited=True, adoption=reference,
                source_study=row["source_study"], via_study=certificate["source_study"], source_usage=row["source_usage"],
                model_calls=0, tokens=0)


def validate_inherited(kernel):
    """Recheck the admission certificate before inherited nodes can suppress new work."""
    entries, native = kernel.entries(), kernel.native
    foreign = {key: row for key, row in native.state_module.retired(entries).items() if row["run"] != kernel.run_id}
    reference = kernel.continuation
    if not foreign and reference is None:
        return
    if reference is None:
        raise ValueError("foreign retirements require an explicit continuation certificate")
    certificate = json.loads(kernel.study_store.get(reference))
    if certificate["schema"] != 1 or certificate["target_study"] != kernel.run_id:
        raise ValueError("continuation certificate belongs to another study")
    old = json.loads(kernel.study_store.get(certificate["source_manifest"]))
    logs, history = certificate["logs"], {}
    for name in ("kernel", "study"):
        history[name] = decode_log(kernel.study_store.get(logs[name]["object"]), logs[name]["head"], native)
    if entries[:len(history["kernel"])] != history["kernel"]:
        raise ValueError("native history differs from its admitted source prefix")
    source = {"manifest": old, "kernel": kernel.store, "entries": history}
    if certificate["prior_usage"] != prior_exposure(source, kernel.study_store):
        raise ValueError("inherited usage exposure differs from the closed source history")
    rows = {row["step"]: row for row in certificate["accepted"]}
    if len(rows) != len(certificate["accepted"]) or set(rows) != set(foreign):
        raise ValueError("inherited standing nodes differ from the adoption certificate")
    retired, definitions = compatible(source, kernel.chain_manifest, Path(kernel.root), native)
    if certificate["baseline"] != {key: kernel.chain_manifest.get(key) for key in BASE_FIELDS}:
        raise ValueError("adopted mathematical baseline changed")
    for identity, retirement in foreign.items():
        expected = accepted_row(source, retirement, kernel.chain_manifest, Path(kernel.root),
                                kernel.study_store, kernel.validate_result, native)
        if rows[identity] != expected or certificate["definitions"][identity] != definitions[identity]:
            raise ValueError("adoption certificate differs from protected source acceptance")

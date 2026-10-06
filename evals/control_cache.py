"""Reuse closed owner-control receipts only under the same complete checking contract.

Worker prompts, model settings and study IDs do not affect the control key. Compiler,
runtime assumption, statements, control sources and checker implementation do.
This cache admits no proof: candidate compilation and examination still run.
"""
import json
from pathlib import Path
import re

import study

CODE = ("chain_study.py", "chain_check.py", "fixtures.py", "runtime.py", "runtime_pin.py",
        "control_cache.py", "study.py", "eval_check.py", "processes.py", "store.py")
NODE_FIELDS = ("id", "module", "path", "header", "statement", "expected_type", "deps")


def binding(manifest):
    sources = {}
    for name in CODE:
        matches = [identity for path, identity in manifest["sources"].items() if Path(path).name == name]
        if len(matches) != 1:
            raise ValueError("control contract requires one implementation identity: " + name)
        sources[name] = matches[0]
    return {"schema": 1, "compiler": manifest["compiler"], "snapshot_id": manifest["snapshot_id"],
            "source_commit": manifest["source_commit"], "runtime_pin": manifest.get("runtime_pin"),
            "code": sources, "controls": manifest["sources"][manifest["controls_source"]],
            "nodes": [{key: node[key] for key in NODE_FIELDS} for node in manifest["nodes"]]}


def expected_rows(manifest):
    return ["valid-proof", "sorry-refused", "unstable-simp-refused", "declaration-escape-refused",
            "ill-typed-proof-refused", "exact-type-refused", *["statement-" + node["id"] for node in manifest["nodes"]],
            "finite-discriminating-controls"]


def validate_rows(manifest, rows):
    if [row["id"] for row in rows] != expected_rows(manifest) or any(row["passed"] is not True for row in rows):
        raise ValueError("control certificate lacks the complete passing scope")


def validate_receipts(store, rows):
    for row in rows:
        result = json.loads(store.get(row["result"]))
        checks = result.get("checks", [result] if "execution" in result else [])
        for check in checks:
            execution = check["execution"]
            if json.loads(store.get(execution["receipt"])) != {key: value for key, value in execution.items() if key != "receipt"}:
                raise ValueError("cached execution differs from its receipt")
        for artifact in result.get("artifacts", []):
            store.get(artifact["hash"])


def retain(manifest, store, rows):
    validate_rows(manifest, rows)
    validate_receipts(store, rows)
    return store.put(study.canonical({"schema": 1, "kind": "passed-owner-controls",
                                     "binding": binding(manifest), "rows": rows}))


def transfer(source, target, initial):
    """Copy the bounded immutable object closure, including diagnostics and execution receipts."""
    pending, seen, total = list(initial), set(), 0
    while pending:
        identity = pending.pop()
        if identity in seen:
            continue
        seen.add(identity)
        if len(seen) > 10000:
            raise ValueError("control receipt closure exceeds object bound")
        data = source.get(identity)
        total += len(data)
        if total > 128 * 1024 ** 2 or study.digest(data) != identity:
            raise ValueError("control receipt closure exceeds byte bound or hash differs")
        target.put(data)
        # Only actual objects in the explicitly supplied source store are followed.
        # Other hash-shaped strings are identities of external admitted inputs.
        for raw in re.findall(rb'"([a-f0-9]{64})"', data):
            reference = raw.decode("ascii")
            if reference not in seen and Path(source.object_path(reference)).is_file():
                pending.append(reference)


def admit(source_root, manifest, target):
    source_root = Path(source_root)
    raw = (source_root / "manifest.json").read_bytes()
    source_manifest = json.loads(raw)
    identity = (source_root / "manifest.ref").read_text().strip()
    Store, _, _ = study.kernel_imports(manifest["kernel"])
    source = Store(str(source_root / "records"))
    if study.digest(raw) != identity or source.get(identity) != raw:
        raise ValueError("control source manifest differs from its pin")
    entries = [row for row in source.entries() if row.get("study") == source_manifest["id"]
               and row["kind"] == "controls_end" and row.get("passed") is True]
    if not entries or not entries[-1].get("certificate"):
        return None
    reference = entries[-1]["certificate"]
    certificate = json.loads(source.get(reference))
    if (certificate.get("schema") != 1 or certificate.get("kind") != "passed-owner-controls"
            or certificate.get("binding") != binding(source_manifest)):
        raise ValueError("control certificate differs from its producing contract")
    if certificate.get("binding") != binding(manifest):
        return None
    validate_rows(manifest, certificate["rows"])
    validate_receipts(source, certificate["rows"])
    transfer(source, target, [reference])
    return reference


def reuse(manifest, store):
    reference = manifest.get("controls_certificate")
    if reference is None:
        return None
    certificate = json.loads(store.get(reference))
    if (certificate.get("schema") != 1 or certificate.get("kind") != "passed-owner-controls"
            or certificate.get("binding") != binding(manifest)):
        raise ValueError("cached controls do not bind this checking contract")
    validate_rows(manifest, certificate["rows"])
    validate_receipts(store, certificate["rows"])
    return certificate["rows"]

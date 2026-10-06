"""Goal: closed controls are reusable across prompts but never across checking contracts.

Method: real temporary stores, complete synthetic control-scope records, changed
contracts, missing rows and corrupted objects. No compiler or model invocation.
"""
import copy
import json
from pathlib import Path
import tempfile

import control_cache
import study
from test_runtime_pin import refuses

KERNEL = Path(__file__).resolve().parents[3] / "ontolkernel"
Store, _, _ = study.kernel_imports(KERNEL)


def fixture(root):
    source = root / "source"
    records = Store(str(source / "records"))
    sources = {"/code/" + name: study.digest(name.encode()) for name in control_cache.CODE}
    sources["/code/controls.lean"] = "c" * 64
    manifest = {"id": "source", "kernel": str(KERNEL), "sources": sources,
                "controls_source": "/code/controls.lean", "source_commit": "a" * 40,
                "snapshot_id": "b" * 64, "compiler": {"version": "one"}, "runtime_pin": "d" * 64,
                "nodes": [{key: [] if key == "deps" else "N1" for key in control_cache.NODE_FIELDS}]}
    data = study.canonical(manifest)
    study.write_new(source / "manifest.json", data)
    study.write_new(source / "manifest.ref", records.put(data).encode())
    result = records.put(study.canonical({"fixture": "control result, not a real compiler receipt"}))
    rows = [{"id": name, "passed": True, "result": result} for name in control_cache.expected_rows(manifest)]
    certificate = control_cache.retain(manifest, records, rows)
    study.event(records, "source", "controls_end", passed=True, certificate=certificate)
    return source, records, manifest, rows, certificate


def check(root):
    source, records, manifest, rows, certificate = fixture(root)
    target = Store(str(root / "target"))
    assert control_cache.admit(source, manifest, target) == certificate
    assert control_cache.reuse({**manifest, "controls_certificate": certificate}, target) == rows
    assert target.get(rows[0]["result"]) == records.get(rows[0]["result"])
    cosmetic = {**manifest, "id": "different-study", "execution": {"model": "other", "effort": "other"}}
    cosmetic["nodes"] = [{**manifest["nodes"][0], "purpose": "new wording", "evidence": ["new fact"]}]
    assert control_cache.admit(source, cosmetic, target) == certificate
    for field in ("source_commit", "snapshot_id", "compiler", "runtime_pin"):
        changed = {**manifest, field: "changed"}
        assert control_cache.admit(source, changed, target) is None
        refuses(lambda: control_cache.reuse({**changed, "controls_certificate": certificate}, target))
    changed = copy.deepcopy(manifest)
    changed["nodes"][0]["expected_type"] = "False"
    assert control_cache.admit(source, changed, target) is None
    changed = copy.deepcopy(manifest)
    changed["sources"]["/code/chain_check.py"] = "e" * 64
    assert control_cache.admit(source, changed, target) is None
    refuses(lambda: control_cache.retain(manifest, target, rows[:-1]))
    refuses(lambda: control_cache.retain(manifest, target, [{**rows[0], "passed": False}, *rows[1:]]))
    result_path = Path(target.object_path(rows[0]["result"]))
    result_bytes = result_path.read_bytes()
    result_path.write_bytes(b"corrupt result")
    refuses(lambda: control_cache.reuse({**manifest, "controls_certificate": certificate}, target))
    result_path.write_bytes(result_bytes)
    Path(records.object_path(certificate)).write_bytes(b"corrupt")
    refuses(lambda: control_cache.admit(source, manifest, target))
    print("Control reuse binds exact runtime/checker/statements, preserves receipts and rejects incomplete scopes")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="ontol-controls-") as directory:
        check(Path(directory))

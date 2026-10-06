"""Goal: cheap pinned admission has an explicit trust boundary and full audit detects violations.

Method: real temporary trees and content-addressed stores; plant byte, identity and
root replacements. Python audit events detect forbidden directory enumeration in
the fast path. No model calls, Lean builds, mocks or timing-dependent assertions.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile

import chain_check
import local_retrieval
import runtime
import runtime_pin
import study

KERNEL = Path(__file__).resolve().parents[3] / "ontolkernel"
Store, _, _ = study.kernel_imports(KERNEL)


def refuses(operation):
    try:
        operation()
    except (ValueError, OSError):
        return
    raise AssertionError("expected refusal")


def fixture(root):
    tools, snapshot = root / "tools", root / "snapshot"
    study.write_new(tools / "bin/lean", b"compiler fixture")
    grant = root / "grant.json"
    study.write_new(grant, study.canonical(runtime.tree_manifest(tools)))
    content = snapshot / "content"
    study.write_new(content / "lib/FTQCLib/Base.olean", b"baseline fixture")
    binding = {"artifacts": runtime.tree_manifest(content)}
    closure = study.digest(study.canonical(binding))
    study.write_new(content / "lib/OntologicSearchScope.trace",
                    study.canonical({"depHash": "ontologic-sha256:" + closure}))
    study.write_new(content / "index/loogle.index", b"index fixture")
    spec = {"schema": 1, "scope": "OntologicSearchScope", "binding": binding,
            "closure": closure, "files": runtime.tree_manifest(content),
            "plan": {"max_hits": 5, "lookup_bytes": 8192}}
    data = study.canonical(spec)
    study.write_new(snapshot / "snapshot.json", data)
    manifest = {"source_commit": "b" * 40, "snapshot": str(snapshot), "snapshot_id": study.digest(data),
                "compiler": {"schema": 1, "readable": [str(tools)], "manifest_files": {str(tools): str(grant)},
                             "readable_provenance": {str(tools): study.digest(grant.read_bytes())}}, "nodes": []}
    return manifest, content, tools


def check(root):
    manifest, content, tools = fixture(root)
    pin = runtime_pin.publish(manifest)
    identity = study.digest(study.canonical(pin))
    assert runtime_pin.audit(pin)["passed"]
    scans = []
    sys.addaudithook(lambda event, args: scans.append(args) if event == "os.scandir" else None)
    lease = runtime_pin.Lease(pin, identity, manifest)
    store = Store(str(root / "records"))
    backend = local_retrieval.Backend(manifest["snapshot"], manifest["snapshot_id"], store, None, lease=lease)
    checker = chain_check.Checker(root, manifest, store, None, backend)
    for _ in range(5):
        checker.verify()
        assert backend.unchanged()
    assert not scans, "pinned admission/checks must not traverse either runtime tree"
    target = root / "linked.olean"
    source = content / "lib/FTQCLib/Base.olean"
    chain_check.link_or_copy(source, target)
    assert target.stat().st_ino == source.stat().st_ino and target.read_bytes() == source.read_bytes()
    source.write_bytes(b"owner violated the pin")
    assert lease.unchanged(), "root check must not claim detection of owner interior writes"
    refuses(lambda: runtime_pin.audit(pin))
    refuses(lambda: local_retrieval.Backend(manifest["snapshot"], manifest["snapshot_id"], store, None))
    changed = {**manifest, "source_commit": "c" * 40}
    refuses(lambda: runtime_pin.Lease(pin, identity, changed))
    altered = copy.deepcopy(pin)
    altered["assumption"] = "silently trust everything"
    refuses(lambda: runtime_pin.Lease(altered, study.digest(study.canonical(altered)), manifest))
    tools.rename(root / "old-tools")
    tools.mkdir()
    assert not lease.unchanged()
    refuses(lambda: checker.verify())
    refuses(lambda: runtime_pin.Lease(pin, identity, manifest))
    print("Pinned bind has zero tree scans; strict audit, replacement refusals and explicit owner boundary pass")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="ontol-pin-") as directory:
        check(Path(directory))

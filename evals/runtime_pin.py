"""Owner-maintained runtime pins; full byte auditing is a separate operation.

The owner promises not to mutate the named runtime trees during their lifetime.
Workers receive read-only mounts. This assumption is explicit, not a claim of
filesystem-enforced immutability. Binding reads small identity records and root
identities; it never traverses or hashes runtime contents. audit() checks bytes.
"""
import argparse
import json
from pathlib import Path
import stat

import runtime
import study

ASSUMPTION = "owner preserves pinned runtime contents; workers have read-only mounts"
PIN_BYTES_MAX = 65536


def read_identity(path, expected, limit=32 * 1024 ** 2):
    path = Path(path)
    if path.stat().st_size > limit:
        raise ValueError("identity record exceeds byte bound")
    data = path.read_bytes()
    if study.digest(data) != expected:
        raise ValueError("runtime identity record changed: " + str(path))
    return json.loads(data)


def root_identity(path):
    path = Path(path)
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode):
        raise ValueError("pinned root must be a directory, not a symlink")
    return {"path": str(path), "device": info.st_dev, "inode": info.st_ino}


def binding(manifest):
    return {"source_commit": manifest["source_commit"], "snapshot": manifest["snapshot"],
            "snapshot_id": manifest["snapshot_id"], "compiler": manifest["compiler"]}


def publish(manifest):
    """Record the owner's explicit assumption against existing version manifests, without a byte audit."""
    inputs = binding(manifest)
    snapshot = Path(inputs["snapshot"])
    read_identity(snapshot / "snapshot.json", inputs["snapshot_id"])
    compiler = inputs["compiler"]
    if set(compiler["readable"]) != set(compiler["manifest_files"]) or not compiler["readable"]:
        raise ValueError("compiler manifest grants differ")
    for path in compiler["readable"]:
        read_identity(compiler["manifest_files"][path], compiler["readable_provenance"][path])
    roots = [root_identity(snapshot / "content"), *[root_identity(path) for path in compiler["readable"]]]
    return {"schema": 1, "kind": "owner-runtime-pin", "assumption": ASSUMPTION,
            "binding": inputs, "roots": roots, "publisher": study.digest(Path(__file__).read_bytes())}


class Lease:
    def __init__(self, pin, identity, manifest):
        if study.digest(study.canonical(pin)) != identity:
            raise ValueError("runtime pin bytes differ from their identity")
        if (pin.get("schema") != 1 or pin.get("kind") != "owner-runtime-pin"
                or pin.get("assumption") != ASSUMPTION or pin.get("binding") != binding(manifest)):
            raise ValueError("runtime pin does not bind this study")
        self.pin, self.identity = pin, identity
        snapshot = Path(manifest["snapshot"])
        self.snapshot = manifest["snapshot_id"]
        self.content = snapshot / "content"
        self.spec = read_identity(snapshot / "snapshot.json", self.snapshot)
        for path in manifest["compiler"]["readable"]:
            read_identity(manifest["compiler"]["manifest_files"][path],
                          manifest["compiler"]["readable_provenance"][path])
        expected = [str(self.content), *manifest["compiler"]["readable"]]
        if [row["path"] for row in pin["roots"]] != expected or not self.unchanged():
            raise ValueError("pinned runtime root replaced or missing")

    def unchanged(self):
        """O(number of roots); interior bytes are covered by the declared owner assumption."""
        try:
            return all(root_identity(row["path"]) == row for row in self.pin["roots"])
        except OSError:
            return False


def from_store(manifest, store):
    identity = manifest.get("runtime_pin")
    if identity is None:
        return None
    pin = json.loads(store.get(identity))
    return Lease(pin, identity, manifest)


def admit(path, manifest, store):
    path = Path(path)
    if path.stat().st_size > PIN_BYTES_MAX:
        raise ValueError("runtime pin exceeds byte bound")
    data = path.read_bytes()
    pin = json.loads(data)
    identity = study.digest(study.canonical(pin))
    Lease(pin, identity, manifest)
    return store.put(study.canonical(pin))


def audit(pin):
    """Explicit expensive effect; return a new audit fact without mutating the pin."""
    manifest = pin["binding"]
    identity = study.digest(study.canonical(pin))
    lease = Lease(pin, identity, manifest)
    before = runtime.tree_metadata(lease.content)
    if runtime.tree_manifest(lease.content) != lease.spec["files"]:
        raise ValueError("snapshot artifact bytes differ")
    if before != runtime.tree_metadata(lease.content):
        raise ValueError("snapshot changed during audit")
    runtime.verify(manifest["compiler"])
    if not lease.unchanged():
        raise ValueError("pinned root changed during audit")
    return {"schema": 1, "kind": "runtime-byte-audit", "pin": identity,
            "passed": True, "auditor": study.digest(Path(__file__).read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("publish")
    create.add_argument("--manifest", type=Path, required=True)
    create.add_argument("--assume-owner-pinned", action="store_true", required=True)
    create.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("audit")
    check.add_argument("pin", type=Path)
    check.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = (publish(json.loads(args.manifest.read_bytes())) if args.command == "publish"
              else audit(json.loads(args.pin.read_bytes())))
    study.write_new(args.output, study.canonical(result))
    print(json.dumps({"path": str(args.output), "identity": study.digest(study.canonical(result)),
                      "kind": result["kind"]}))


if __name__ == "__main__":
    main()

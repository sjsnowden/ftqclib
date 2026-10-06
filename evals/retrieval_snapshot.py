"""Prepare an immutable search environment from owner-admitted compiled imports.

This command consumes the baseline build receipt, never a worker worktree. The
generated trace is an Ontologic digest bridge for Loogle's depHash API, not a Lake
build receipt. Its digest binds every copied artifact, source plan and tool. A
changed accepted dependency requires a new destination and snapshot identity.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import time
import uuid

import local_retrieval
import runtime
import study

SCOPE = "OntologicSearchScope"


def write(path, value):
    study.write_new(path, study.canonical(value))


def checked(checker, store, source, command, reads, environment, writes=(), seconds=180, memory_bytes=8 * 1024**3):
    started = time.monotonic()
    result = checker.run(str(source), command, store, "prepare-" + uuid.uuid4().hex,
                         readonly=reads, writable=writes, environment=environment,
                         deadline_seconds=seconds, log_bytes_max=2 * 1024**2,
                         file_bytes=512 * 1024**2, memory_bytes=memory_bytes)
    output = local_retrieval.streams(store, result)
    if result["status"] != "completed":
        raise ValueError("snapshot preparation failed: " + json.dumps(result) + "\n" +
                         output["stderr"].decode(errors="replace")[-3000:] +
                         output["stdout"].decode(errors="replace")[-1000:])
    return {"execution": result, "elapsed_seconds": time.monotonic() - started}, output


def compile_scope(root, build, checker, store):
    source, library = root / "assembly", root / "content/lib"
    (source / ".scratch/build").mkdir(parents=True)
    library.mkdir(parents=True)
    modules = build["plan"]["modules"]
    if not modules or len(modules) > 64 or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", m) for m in modules):
        raise ValueError("invalid declared import scope")
    data = "".join("import " + name + "\n" for name in modules).encode()
    study.write_new(source / (SCOPE + ".lean"), data)
    paths = [build["lib"], *build["packages"]]
    reads = [(build["toolchain"], "/toolchain")] + [(path, "/deps/p" + str(i)) for i, path in enumerate(paths)]
    environment = {"LEAN_PATH": ":".join("/deps/p" + str(i) for i in range(len(paths))), "LEAN_NUM_THREADS": "2"}
    command = ["/toolchain/bin/lean", "-j2", "-M4096", "-o", ".scratch/build/" + SCOPE + ".olean", SCOPE + ".lean"]
    receipt, _ = checked(checker, store, source, command, reads, environment,
                         [(str(library), "/work/.scratch/build")])
    return source, reads, environment, receipt


def inventory(root, source, reads, environment, checker, store):
    study.write_new(source / "request.json", study.canonical({"operation": "inventory", "payload": None, "max_hits": 5}))
    environment = {**environment, "LEAN_PATH": "/deps/snapshot/lib:" + environment["LEAN_PATH"] + ":/toolchain/lib/lean"}
    receipt, output = checked(checker, store, source,
                              ["/usr/bin/python3", "-B", "/deps/snapshot/driver.py"],
                              [*reads, (str(root / "content"), "/deps/snapshot")], environment)
    value = json.loads(output["stdout"])
    if value.get("status") != "ok" or value["count"] != len(value["modules"]):
        raise ValueError("scope inventory failed: " + str(value)[:2000])
    return value, receipt


def project(root, build, modules):
    library = root / "content/lib"
    paths = [library, Path(build["lib"]), *map(Path, build["packages"]), Path(build["toolchain"]) / "lib/lean"]
    origins = {}
    for parts in modules:
        if not local_retrieval.valid_name(parts) or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", p) for p in parts):
            raise ValueError("unsafe imported module component")
        relative = "/".join(parts)
        choices = [path for path in paths if (path / (relative + ".olean")).is_file()]
        if len(choices) != 1:
            raise ValueError("ambiguous or missing compiled module: " + relative)
        origin = choices[0]
        origins[".".join(parts)] = str(origin)
        if origin == library:
            continue
        for suffix in runtime.ARTIFACTS:
            path = origin / (relative + suffix)
            if path.exists():
                if path.is_symlink():
                    raise ValueError("compiled artifact is linked")
                target = library / (relative + suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, target)
    return origins


def seal_index(root, build, checker, store, tools):
    content = root / "content"
    before = runtime.tree_manifest(content)
    binding = {"plan": build["plan"], "source_hashes": build["source_hashes"],
               "artifacts": before, "tools": tools, "format": "ontologic-dependency-digest-v1"}
    digest = study.digest(study.canonical(binding))
    write(content / ("lib/" + SCOPE + ".trace"), {"depHash": "ontologic-sha256:" + digest})
    source, output = root / "index-request", root / "index-output"
    (source / ".scratch/index").mkdir(parents=True)
    output.mkdir()
    command = ["/usr/bin/time", "-v", "/usr/bin/timeout", "--signal=TERM", "--kill-after=5s", "600s",
               "/deps/snapshot/bin/loogle", "--path", "/deps/snapshot/lib", "--module", SCOPE,
               "--index-mode", "write", "--index-file", "/work/.scratch/index/loogle.index", "--json"]
    receipt, _ = checked(checker, store, source, command, [(str(content), "/deps/snapshot")],
                         {"LEAN_PATH": "/deps/snapshot/lib", "LEAN_NUM_THREADS": "2"},
                         [(str(output), "/work/.scratch/index")], seconds=630, memory_bytes=12 * 1024**3)
    (content / "index").mkdir()
    shutil.copyfile(output / "loogle.index", content / "index/loogle.index")
    return digest, binding, receipt


def prepare(args):
    build_raw = args.build.read_bytes()
    build = json.loads(build_raw)
    if build.get("schema") != 2:
        raise ValueError("snapshot requires artifact-bound build receipt schema 2")
    if any(row["status"] != "completed" or row["exit"] != 0 for row in build["receipts"]):
        raise ValueError("baseline build is not completely successful")
    # Verify the prepared baseline source against its build receipt before using artifacts.
    for relative, digest in build["source_hashes"].items():
        if study.digest((Path(build["source"]) / relative).read_bytes()) != digest:
            raise ValueError("baseline source differs from its build receipt")
    root = args.destination.resolve()
    root.mkdir(parents=True, exist_ok=False)
    (root / "content/bin").mkdir(parents=True)
    Store, checker, _ = study.kernel_imports(args.kernel)
    store = Store(str(root / "records"))
    build_object, runtime_cache = admit_build(args.build, build_raw, build, store, Store)
    for name, path in (("loogle", args.loogle), ("declaration-lookup", args.lookup)):
        shutil.copyfile(path, root / "content/bin" / name)
        (root / "content/bin" / name).chmod(0o555)
    shutil.copyfile(Path(__file__).with_name("retrieval_driver.py"), root / "content/driver.py")
    tools = {"loogle_setup": json.loads(args.loogle_receipt.read_bytes()),
             "lookup_setup": json.loads(args.lookup_receipt.read_bytes()),
             "lookup_source": study.digest(Path(__file__).with_name("DeclarationLookup.lean").read_bytes()),
             "lean_binary": runtime.file_hash(Path(build["toolchain"]) / "bin/lean"),
             "builder": study.digest(Path(__file__).read_bytes())}
    if runtime.file_hash(root / "content/bin/loogle")["sha256"] != tools["loogle_setup"]["executable_sha256"]:
        raise ValueError("Loogle executable differs from setup receipt")
    if (runtime.file_hash(root / "content/bin/declaration-lookup")["sha256"] != tools["lookup_setup"]["binary"]["sha256"]
            or tools["lookup_source"] != tools["lookup_setup"]["source"]["sha256"]):
        raise ValueError("lookup executable or source differs from setup receipt")
    source, reads, environment, compiled = compile_scope(root, build, checker, store)
    observed, inventory_receipt = inventory(root, source, reads, environment, checker, store)
    origins = project(root, build, observed["modules"])
    runtime.verify(build["runtime_inputs"], runtime_cache)
    if runtime.tree_manifest(Path(build["lib"])) != build["artifacts"]:
        raise ValueError("baseline artifacts changed during projection")
    print(json.dumps({"stage": "projected", "modules": len(origins)}), flush=True)
    closure, binding, index_receipt = seal_index(root, build, checker, store, tools)
    for path in (root / "content").rglob("*"):
        if path.is_file():
            path.chmod(0o555 if path.parent.name == "bin" else 0o444)
    spec = {"schema": 1, "plan": build["plan"], "scope": SCOPE, "closure": closure,
            "binding": binding, "build_receipt_sha256": build_object,
            "module_origins": origins, "files": runtime.tree_manifest(root / "content"),
            "receipts": {"scope": compiled, "inventory": inventory_receipt, "index": index_receipt}}
    raw = study.canonical(spec)
    study.write_new(root / "snapshot.json", raw)
    identity = store.put(raw)
    backend = local_retrieval.Backend(root, identity, store, checker)
    anchors = [backend.call("read_declaration", name.split(".")) for name in build["plan"]["anchors"]]
    if any(result["status"] != "ok" for result in anchors):
        write(root / "anchor-failure.json", anchors)
        raise ValueError("declared semantic anchor failed lookup")
    write(root / "ready.json", {"snapshot": identity, "anchors": anchors, "modules": len(origins),
                               "index_seconds": index_receipt["elapsed_seconds"],
                               "index_bytes": (root / "content/index/loogle.index").stat().st_size})
    study.write_new(root / "snapshot.ref", identity.encode())
    print(json.dumps({"snapshot": str(root), "id": identity, "modules": len(origins),
                      "index_seconds": index_receipt["elapsed_seconds"]}), flush=True)


def admit_build(path, raw, build, store, Store):
    """Retain original build objects and verify their still-present artifacts and grants."""
    original = Store(str(path.parent / "records"))
    for object_path in Path(original.objects).glob("*/*"):
        identity = object_path.parent.name + object_path.name
        if re.fullmatch(r"[0-9a-f]{64}", identity):
            store.put(original.get(identity))
    identity = store.put(raw)
    if runtime.tree_manifest(Path(build["lib"])) != build["artifacts"]:
        raise ValueError("compiled artifacts differ from successful build receipt")
    if store.get(build["artifacts_object"]) != study.canonical(build["artifacts"]):
        raise ValueError("compiled artifact manifest object differs")
    for relative, digest in build["source_hashes"].items():
        if store.put((Path(build["source"]) / relative).read_bytes()) != digest:
            raise ValueError("baseline source changed")
    cache = {}
    runtime.verify(build["runtime_inputs"], cache)
    return identity, cache


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("build", "destination", "kernel", "loogle", "lookup", "loogle-receipt", "lookup-receipt"):
        parser.add_argument("--" + name, type=Path, required=True)
    prepare(parser.parse_args())


if __name__ == "__main__":
    main()

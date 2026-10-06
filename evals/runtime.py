"""Prepare audited read-only runtime grants without compiling or exposing withheld artifacts.

Only local ancestors of public checks are copied; every edited module and local
descendant is excluded. Third-party caches and the pinned toolchain are read-only.
Worker and checker build products remain private. Manifests are owner-only files
outside grant roots; verify re-observes exact file sets, bytes, modes and links.
Optional verification caches live only in one owner process. Unchanged complete
metadata reuses its earlier byte audit; it does not claim a fresh byte read.
Runtime directories must deny worker writes. Hostile local OS users are outside
this cache's trust model; no cache state is persisted or reused across processes.
"""
import hashlib
import inspect
import json
import os
import pathlib
from pathlib import Path
import re
import shutil
import stat

import fixtures

ENTRIES_MAX = 262144
FILE_BYTES_MAX = 2 * 1024 ** 3
TREE_BYTES_MAX = 32 * 1024 ** 3
ARTIFACTS = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir")
PUBLIC_FIELDS = ("id", "purpose", "obligation", "evidence", "acceptance", "completion", "writes", "standards")


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_hash(path):
    with path.open("rb") as handle:
        before = os.fstat(handle.fileno())
        if not stat.S_ISREG(before.st_mode) or before.st_size > FILE_BYTES_MAX:
            raise ValueError("runtime input is not a bounded regular file: " + str(path))
        identity = hashlib.file_digest(handle, "sha256").hexdigest()
        after = os.fstat(handle.fileno())
    if (before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (after.st_size, after.st_mtime_ns, after.st_ctime_ns):
        raise ValueError("runtime input changed during hashing: " + str(path))
    return {"sha256": identity, "bytes": before.st_size, "mode": stat.S_IMODE(before.st_mode)}


def tree_manifest(root):
    """Stream file hashing under fixed tree/byte bounds; linked targets must stay inside the grant."""
    root = root.resolve()
    if not root.is_dir():
        raise ValueError("runtime grant is missing: " + str(root))
    found, count, total = {}, 0, 0
    for directory, children, files in os.walk(root, followlinks=False):
        relative = Path(directory).relative_to(root)
        if len(relative.parts) > 64:
            raise ValueError("runtime directory depth bound")
        for name in sorted(children + files):
            count += 1
            if count > ENTRIES_MAX or name == ".git":
                raise ValueError("runtime entry bound or Git administration in grant")
            path = Path(directory) / name
            if path.is_symlink():
                target = path.resolve(strict=True)
                if root != target and root not in target.parents:
                    raise ValueError("runtime link escapes its grant: " + str(path))
                found[path.relative_to(root).as_posix()] = {"link": os.readlink(path)}
            elif path.is_file():
                value = file_hash(path)
                total += value["bytes"]
                if total > TREE_BYTES_MAX:
                    raise ValueError("runtime tree byte bound")
                found[path.relative_to(root).as_posix()] = value
            elif not path.is_dir():
                raise ValueError("runtime input is not a directory or regular file: " + str(path))
    return found


def walk_error(error):
    raise error


def metadata_fields(value):
    return (value.st_size, value.st_mode, value.st_ino, value.st_dev,
            value.st_mtime_ns, value.st_ctime_ns, value.st_uid, value.st_gid, value.st_nlink)


def tree_metadata(root):
    """Fingerprint every bounded path, including directories and literal linked targets."""
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("runtime grant is not a directory: " + str(root))
    found = {".": metadata_fields(root.lstat())}
    count, total = 0, 0
    for directory, children, files in os.walk(root, followlinks=False, onerror=walk_error):
        relative = Path(directory).relative_to(root)
        if len(relative.parts) > 64:
            raise ValueError("runtime directory depth bound")
        for name in sorted(children + files):
            count += 1
            if count > ENTRIES_MAX or name == ".git":
                raise ValueError("runtime entry bound or Git administration in grant")
            path = Path(directory) / name
            value = path.lstat()
            link = None
            if stat.S_ISLNK(value.st_mode):
                target = path.resolve(strict=True)
                if root != target and root not in target.parents:
                    raise ValueError("runtime link escapes its grant: " + str(path))
                link = os.readlink(path)
            elif stat.S_ISREG(value.st_mode):
                total += value.st_size
                if value.st_size > FILE_BYTES_MAX or total > TREE_BYTES_MAX:
                    raise ValueError("runtime file/tree byte bound")
            elif not stat.S_ISDIR(value.st_mode):
                raise ValueError("runtime input is not a directory or regular file: " + str(path))
            found[path.relative_to(root).as_posix()] = (metadata_fields(value), link)
    return digest(canonical({"root": str(root), "entries": found}))


def public_checks(spec, files):
    """Private examiner paths never enter worker controls, including an unrecognized check label."""
    found = []
    for check in spec["checks"]:
        command = check["command"]
        if check["id"] == "examiner":
            continue
        if not command or command[0] != "lean" or command[-1] not in files:
            continue
        if not command[-1].endswith(".lean") or Path(command[-1]).is_absolute():
            continue
        outputs = [command[index + 1] for index, value in enumerate(command[:-1]) if value == "-o"]
        if any(not name.startswith(".scratch/build/") or ".." in Path(name).parts for name in outputs):
            raise ValueError("public check output escapes private build tree")
        found.append({"id": check["id"], "command": list(command)})
    if not found:
        raise ValueError("task has no public source checks")
    return found


def affected_checks(task, files, required):
    """Rebuild every affected intermediate import; Lean imports do not compile missing source modules."""
    known = {check["command"][-1][:-5].replace("/", "."): check for check in required}
    found = []
    for module in fixtures.dependent_modules(task, files):
        if module in known:
            found.append(known.pop(module))
        else:
            path = module.replace(".", "/")
            found.append({"id": "dependency-" + module,
                          "command": ["lean", "-o", ".scratch/build/" + path + ".olean", path + ".lean"]})
    found += list(known.values())
    return found


def import_graph(files):
    found = {}
    for path, data in files.items():
        if not path.endswith(".lean"):
            continue
        code = fixtures.code_without_comments(data.decode("utf-8"))
        imports = []
        for line in re.findall(r"(?m)^(?:public\s+)?import\s+([^\n]+)", code):
            imports += re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", line)
        found[path[:-5].replace("/", ".")] = imports
    return found


def ancestors(graph, roots):
    found, pending = set(), list(dict.fromkeys(roots))
    queued = set(pending)
    for _ in range(len(graph) + len(pending) + 1):
        if not pending:
            return found
        current = pending.pop()
        if current in found or current not in graph:
            continue
        found.add(current)
        for name in graph[current]:
            if name in graph and name not in queued:
                queued.add(name)
                pending.append(name)
    raise ValueError("local import graph traversal bound")


def descendants(graph, modules):
    reverse = {name: set() for name in graph}
    for name, imports in graph.items():
        for dependency in imports:
            if dependency in reverse:
                reverse[dependency].add(name)
    return ancestors(reverse, modules)


def local_artifacts(reference, destination, modules):
    source = reference / ".lake/build/lib/lean"
    copied = []
    for module in sorted(modules):
        name = module.replace(".", "/")
        if not (source / (name + ".olean")).is_file():
            raise ValueError("required local ancestor artifact is missing: " + module)
        for suffix in ARTIFACTS:
            path = source / (name + suffix)
            if not path.exists():
                continue
            if path.is_symlink() or not stat.S_ISREG(path.stat().st_mode):
                raise ValueError("local artifact must be an unlinked regular file")
            target = destination / (name + suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            target.chmod(0o444)
            copied.append(target.relative_to(destination).as_posix())
    return copied


def package_grants(reference):
    manifest = json.loads((reference / "lake-manifest.json").read_bytes())
    found, omitted = [], []
    for package in manifest["packages"]:
        name = package["name"]
        if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
            raise ValueError("invalid package name")
        path = reference / ".lake/packages" / name / ".lake/build/lib/lean"
        if not path.is_dir():
            omitted.append({"package": name, "path": str(path), "reason": "artifact_directory_missing"})
            continue
        found.append(path.resolve())
    return found, omitted


def record_grants(grants, destination):
    provenance, manifests = {}, {}
    for index, path in enumerate(grants):
        contents = tree_manifest(path)
        identity = digest(canonical(contents))
        manifest = destination / ("grant-" + str(index) + ".json")
        with manifest.open("xb") as handle:
            handle.write(canonical(contents))
            handle.flush()
            os.fsync(handle.fileno())
        provenance[str(path)] = identity
        manifests[str(path)] = str(manifest)
    return provenance, manifests


def prepare(task, reference_build_root, runtime_root, spec, cache=None):
    """No build runs here. Owner controls must establish the sufficiency of retained caches."""
    reference, runtime = Path(reference_build_root).resolve(), Path(runtime_root).resolve()
    if task not in ("F01", "F02") or spec["task"] != task:
        raise ValueError("runtime task does not match fixture specification")
    files = fixtures.tree_files(reference)
    checks = affected_checks(task, files, public_checks(spec, files))
    graph = import_graph(files)
    roots = [check["command"][-1][:-5].replace("/", ".") for check in checks]
    excluded = set(spec["excluded_modules"])
    editable = {fixtures.Z_SHEAR[:-5].replace("/", ".")} if task == "F01" else {
        name[:-5].replace("/", ".") for name in (fixtures.PAIRING, fixtures.RESIDUAL, fixtures.AMPLITUDE)}
    if not editable <= excluded:
        raise ValueError("excluded artifacts do not cover the edited module set")
    if not descendants(graph, editable) <= excluded:
        raise ValueError("excluded artifacts do not cover every local target descendant")
    allowed = ancestors(graph, roots) - excluded
    packages, omitted = package_grants(reference)
    destination = runtime / "tasks" / task
    previous = destination / "runtime.json"
    if previous.is_file():
        record = json.loads(previous.read_bytes())
        verify(record, cache)
        if (record["excluded_modules"] != sorted(excluded) or record["local_modules"] != sorted(allowed)
                or record["checks"] != checks or record.get("reference_sha256") != fixtures.tree_digest(files)
                or record.get("omitted_packages", []) != omitted
                or record["lean_path"][1:] != [str(path) for path in packages]):
            raise ValueError("existing runtime inputs differ; retain them and prepare a new runtime version")
        return record
    destination.mkdir(parents=True, exist_ok=False)
    local = destination / "lib"
    local.mkdir()
    copied = local_artifacts(reference, local, allowed)
    tools = runtime / "lean-4.29.1-linux"
    if not (tools / "bin/lean").is_file():
        raise ValueError("pinned Lean executable is missing")
    dependencies = [local, *packages]
    grants = [*dependencies, tools]
    provenance, manifests = record_grants(grants, destination)
    record = {"schema": 1, "task": task, "toolchain": str(tools), "readable": [str(path) for path in grants],
              "readable_provenance": provenance, "manifest_files": manifests,
              "lean_path": [str(path) for path in dependencies], "checks": checks,
              "excluded_modules": sorted(excluded), "local_modules": sorted(allowed), "copied": copied,
              "omitted_packages": omitted,
              "reference_sha256": fixtures.tree_digest(files),
              "limits": {"threads": 2, "memory_mb": 4096, "check_deadline_seconds": 120}}
    with (destination / "runtime.json").open("xb") as handle:
        handle.write(canonical(record))
        handle.flush()
        os.fsync(handle.fileno())
    return record


def verify(record, cache=None):
    """Audit bytes once per owner process; an optional cache rechecks complete metadata."""
    if record["schema"] != 1 or set(record["readable"]) != set(record["manifest_files"]):
        raise ValueError("runtime manifest grant set changed")
    for path in record["readable"]:
        retained = Path(record["manifest_files"][path]).read_bytes()
        expected = record["readable_provenance"][path]
        if digest(retained) != expected:
            raise ValueError("runtime dependency manifest changed: " + path)
        before = tree_metadata(Path(path))
        key = (path, expected)
        prior = cache.get(key) if cache is not None else None
        if prior == (os.getpid(), before):
            continue
        observed = canonical(tree_manifest(Path(path)))
        if before != tree_metadata(Path(path)):
            raise ValueError("runtime dependency changed during byte audit: " + path)
        if observed != retained:
            raise ValueError("runtime dependency bytes changed: " + path)
        if prior is not None and prior[0] == os.getpid() and prior[1] != before:
            raise ValueError("runtime dependency metadata changed since owner audit: " + path)
        if cache is not None:
            cache[key] = (os.getpid(), before)
    return True


def build_artifacts(record):
    """Select only the retained local ancestor files; never infer grants from directory contents."""
    local = record["lean_path"][0]
    retained = Path(record["manifest_files"][local]).read_bytes()
    if digest(retained) != record["readable_provenance"][local]:
        raise ValueError("local artifact manifest changed")
    manifest = json.loads(retained)
    found, total = [], 0
    names = record["copied"]
    if len(names) > ENTRIES_MAX or len(set(names)) != len(names):
        raise ValueError("local artifact entry bound or duplicate")
    for name in sorted(names):
        path = Path(name)
        suffix = next((suffix for suffix in sorted(ARTIFACTS, key=len, reverse=True) if name.endswith(suffix)), None)
        if (path.is_absolute() or not path.parts or any(part in (".", "..") for part in path.parts)
                or path.as_posix() != name or not suffix):
            raise ValueError("invalid local artifact path")
        module = name[:-len(suffix)].replace("/", ".")
        if module not in record["local_modules"] or module in record["excluded_modules"]:
            raise ValueError("local artifact is outside the admitted ancestor set")
        value = manifest.get(name, {})
        size = value.get("bytes")
        if type(size) is not int or not 0 <= size <= FILE_BYTES_MAX or "sha256" not in value:
            raise ValueError("local artifact lacks a bounded retained file identity")
        total += size
        if total > TREE_BYTES_MAX:
            raise ValueError("local artifact byte bound")
        found.append({"path": name, "sha256": value["sha256"], "bytes": size})
    return found


def copy_build_artifacts(source, destination, artifacts):
    """Copy admitted files, without shared inodes, into a private package root; repeat checks are safe."""
    source, destination = pathlib.Path(source), pathlib.Path(destination)
    original_root, private_root = source.resolve(strict=True), destination.resolve()
    if (destination.is_symlink() or original_root == private_root or original_root in private_root.parents
            or private_root in original_root.parents):
        raise ValueError("private build destination must be separate and unlinked")
    destination.mkdir(parents=True, exist_ok=True)
    for artifact in artifacts:
        name = pathlib.Path(artifact["path"])
        if name.is_absolute() or not name.parts or any(part in (".", "..") for part in name.parts):
            raise ValueError("invalid private artifact path")
        original, target = source / name, destination / name
        for base in (source, destination):
            for parent in (base, *(base / pathlib.Path(*name.parts[:index]) for index in range(1, len(name.parts)))):
                if parent.is_symlink():
                    raise ValueError("linked artifact parent")
        value = original.lstat()
        if not stat.S_ISREG(value.st_mode) or value.st_nlink != 1 or value.st_size != artifact["bytes"]:
            raise ValueError("local artifact is not its retained regular file")
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists() and (target.is_symlink() or not target.is_file() or target.stat().st_nlink != 1):
            raise ValueError("private artifact destination is linked or nonregular")
        if target.is_symlink():
            raise ValueError("private artifact destination is linked")
        shutil.copyfile(original, target)
        with target.open("rb") as handle:
            identity = hashlib.file_digest(handle, "sha256").hexdigest()
        if identity != artifact["sha256"] or target.stat().st_size != artifact["bytes"]:
            raise ValueError("copied local artifact differs from its retained identity")


def seed_build(record, destination):
    """Caller verifies runtime first; seed only its admitted local files, without rehashing third-party grants."""
    copy_build_artifacts(record["lean_path"][0], destination, build_artifacts(record))


def public_files(task, contract, runtime_record):
    """Identical public files for every condition; no owner examiner command or original source path."""
    if task != runtime_record["task"] or task != contract["id"]:
        raise ValueError("public task/runtime identity mismatch")
    public = {key: contract[key] for key in PUBLIC_FIELDS}
    execution = {"lean": str(Path(runtime_record["toolchain"]) / "bin/lean"),
                 "lean_path": runtime_record["lean_path"], "checks": runtime_record["checks"],
                 "limits": runtime_record["limits"], "local_artifacts": build_artifacts(runtime_record)}
    script = ("#!/usr/bin/env python3\n"
              "\"\"\"Public advisory source checks; worker success does not establish owner acceptance.\"\"\"\n"
              "import hashlib,json,os,pathlib,shutil,stat,subprocess,sys\n"
              + inspect.getsource(copy_build_artifacts) + "\n"
              +
              "SPEC=json.loads(" + repr(canonical(execution).decode("ascii")) + ")\n"
              "root=pathlib.Path.cwd()\nbuild=root/'.scratch/build'\nbuild.mkdir(parents=True,exist_ok=True)\n"
              "copy_build_artifacts(SPEC['lean_path'][0],build,SPEC['local_artifacts'])\n"
              "environment=dict(os.environ)\n"
              "environment['LEAN_PATH']=os.pathsep.join([str(build),*SPEC['lean_path']])\n"
              "environment['LEAN_NUM_THREADS']='2'\nrows=[]\n"
              "for check in SPEC['checks']:\n"
              " command=[SPEC['lean'],'-j2','-M4096',*check['command'][1:]]\n"
              " for index,value in enumerate(command[:-1]):\n"
              "  if value=='-o': (root/command[index+1]).parent.mkdir(parents=True,exist_ok=True)\n"
              " output=build/('public-'+str(len(rows)))\n"
              " try:\n"
              "  with output.with_suffix('.stdout').open('wb') as stdout,output.with_suffix('.stderr').open('wb') as stderr:\n"
              "   child=subprocess.run(command,env=environment,timeout=120,stdout=stdout,stderr=stderr)\n"
              "  row={'id':check['id'],'exit':child.returncode,'timed_out':False}\n"
              " except subprocess.TimeoutExpired:\n"
              "  row={'id':check['id'],'exit':None,'timed_out':True}\n"
              " for suffix,stream in [('.stdout',sys.stdout.buffer),('.stderr',sys.stderr.buffer)]:\n"
              "  with output.with_suffix(suffix).open('rb') as recorded: stream.write(recorded.read(65536))\n"
              " rows.append(row)\n"
              " if row['exit']!=0: break\n"
              "print(json.dumps({'public_checks':rows,'acceptance':'not assessed'}))\n"
              "sys.exit(0 if len(rows)==len(SPEC['checks']) and all(row['exit']==0 for row in rows) else 1)\n")
    return {".task/contract.json": canonical(public), ".task/check.py": script.encode("utf-8")}

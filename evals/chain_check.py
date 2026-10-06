"""Owner-only Lean proof admission, isolated compilation and immutable certificates.

The worker supplies one tactic body. The owner supplies imports, statement, exact
type examiner, transitive axiom policy and dependency artifacts. No worker paths,
commands or writable source tree are accepted. Compilation is serial per owner.
"""
import json
import errno
import os
from pathlib import Path
import shutil
import uuid

import fixtures
import local_retrieval
import runtime
import study

ARTIFACT_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ilean", ".ir")


def object_bytes(store, identity):
    data = store.get(identity)
    if study.digest(data) != identity:
        raise ValueError("immutable object bytes differ: " + identity)
    return data


def link_or_copy(source, destination):
    """Project owner-pinned baseline bytes without copying them; checker mounts remain read-only."""
    try:
        return os.link(source, destination)
    except OSError as error:
        if error.errno != errno.EXDEV:
            raise
        return shutil.copy2(source, destination)


def assembled(node, proof, *, admit=True):
    if not isinstance(proof, str) or len(proof.encode("utf-8")) > 16384:
        raise ValueError("proof body exceeds 16384 bytes")
    reason = fixtures.admitted_window("F01", proof.encode("utf-8")) if admit else None
    if reason:
        raise ValueError(reason.replace("F01", "proof node"))
    return (node["header"].rstrip() + "\n\n" + node["statement"].rstrip() + " := " +
            proof.rstrip() + "\n").encode("utf-8")


def examiner(node):
    """Generate a protected, independently typed consumer and a transitive axiom sweep."""
    prefix = f"import {node['module']}\nimport Lean\n\n"
    opens = "\n".join(line for line in node["header"].splitlines() if line.startswith("open "))
    prefix += opens + "\nopen Lean\n\n"
    name, expected = node["name"], node["expected_type"]
    return (prefix + f"""run_cmd do
  match (← Lean.getEnv).find? `{name} with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Required theorem declaration missing"

example : {expected} := @{name}

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← getConstInfo `{name}
  let expected ← Lean.Elab.Term.elabType (← `({expected}))
  unless ← Lean.Meta.isDefEq info.type expected do
    throwError "Declaration type differs from protected expected type"

run_cmd do
  let info ← Lean.getConstInfo `{name}
  let names := match info.value? with
    | some value => value.getUsedConstants.toList.map Lean.Name.toString
    | none => []
  Lean.Elab.Command.liftIO <| IO.FS.writeFile "/build/used-constants.json" (Lean.toJson names).compress

run_cmd do
  let environment ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let mut pending := [`{name}]
  let mut seen : Lean.NameSet := {{}}
  let mut queued : Lean.NameSet := pending.foldl (fun names name => names.insert name) {{}}
  for _ in [0:200000] do
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if !seen.contains name then
        seen := seen.insert name
        match environment.find? name with
        | none => throwError "Missing dependency {{name}}"
        | some info =>
          match info with
          | .axiomInfo _ =>
            if !permitted.contains name then
              throwError "Unapproved transitive axiom {{name}}"
          | _ => pure ()
          let dependencies := info.type.getUsedConstants.toList ++
            (match info.value? with | some value => value.getUsedConstants.toList | none => [])
          for dependency in dependencies do
            if !queued.contains dependency then
              queued := queued.insert dependency
              pending := dependency :: pending
  if !pending.isEmpty then
    throwError "Transitive axiom examination exceeded bound"
""").encode("utf-8")


def compiler_record(build):
    """Grant only the audited compiler; baseline libraries come from the retrieval snapshot."""
    record, path = build["runtime_inputs"], build["toolchain"]
    return {"schema": 1, "readable": [path],
            "manifest_files": {path: record["manifest_files"][path]},
            "readable_provenance": {path: record["readable_provenance"][path]}}


def diagnostics(store, checks):
    for checked in checks:
        if checked["execution"]["status"] != "completed":
            streams = local_retrieval.streams(store, checked["execution"])
            raw = streams["stdout"] + b"\n" + streams["stderr"]
            return raw[:3072].decode("utf-8", "replace")
    return "Owner check refused the candidate."


class Checker:
    def __init__(self, root, manifest, store, executor, backend):
        self.root, self.manifest, self.store = Path(root), manifest, store
        self.executor, self.backend, self.runtime_cache = executor, backend, {}
        self.compiler = manifest["compiler"]
        self.toolchain = self.compiler["readable"][0]
        self.nodes = {node["id"]: node for node in manifest["nodes"]}

    def verify(self):
        lease = getattr(self.backend, "lease", None)
        if lease is None:
            runtime.verify(self.compiler, cache=self.runtime_cache)
        elif lease.pin["binding"]["compiler"] != self.compiler:
            raise ValueError("runtime lease does not bind this compiler")
        if not self.backend.unchanged():
            raise ValueError("baseline retrieval artifacts changed")

    def dependency_files(self, issue):
        """Only certificates and sources explicitly bound by this native kernel issue may enter."""
        operands = {entry["path"]: entry for entry in issue["operands"]}
        files = {}
        for entry in issue["operands"]:
            if not entry["path"].startswith(".ontologic/certificates/"):
                continue
            certificate = json.loads(object_bytes(self.store, entry["hash"]))
            node = self.nodes[entry["step"]]
            source = operands.get(node["path"])
            if (certificate["node"] != node["id"] or certificate["snapshot"] != self.backend.snapshot
                    or source is None or source["hash"] != certificate["source"]):
                raise ValueError("predecessor certificate differs from admitted source operand")
            for artifact in certificate["artifacts"]:
                path = artifact["path"]
                if path not in {node["module"].replace(".", "/") + suffix for suffix in ARTIFACT_SUFFIXES}:
                    raise ValueError("certificate names an undeclared module artifact")
                data = object_bytes(self.store, artifact["hash"])
                if path in files and files[path] != data:
                    raise ValueError("conflicting predecessor artifacts")
                files[path] = data
        return files

    def execute(self, candidate, build, deps, source, label):
        """Run a fixed compiler command in the protected projection and retain every pipe byte."""
        self.verify()
        output = source[:-5] + ".olean"
        (build / output).parent.mkdir(parents=True, exist_ok=True)
        command = ["/toolchain/bin/lean", "-j2", "-M4096", "-o", "/build/" + output, source]
        result = self.executor.run(str(candidate), command, self.store, "chain-" + uuid.uuid4().hex,
            readonly=[(self.toolchain, "/toolchain"), (str(self.backend.content / "lib"), "/deps/base"),
                      (str(deps), "/deps/accepted")], writable=[(str(build), "/build")],
            deadline_seconds=120, log_bytes_max=262144, memory_bytes=8 * 1024 ** 3,
            environment={"LEAN_PATH": "/deps/accepted:/deps/base", "LEAN_NUM_THREADS": "2"})
        self.verify()
        return {"id": label, "source": source, "execution": result}

    def layout(self, label, node, source, dependencies):
        directory = self.root / "checks" / (label + "-" + uuid.uuid4().hex)
        candidate, build, deps = (directory / name for name in ("source", "build", "dependencies"))
        for path in (candidate, build, deps):
            path.mkdir(parents=True)
        study.write_new(candidate / node["path"], source)
        roots = {path.split("/", 1)[0] for path in dependencies if "/" in path}
        if "." in node.get("module", ""):
            roots.add(node["module"].split(".", 1)[0])
        # Lean selects a namespace root, not each leaf independently. Present one
        # complete read-only namespace containing the baseline and admitted additions.
        for name in roots:
            baseline = self.backend.content / "lib" / name
            if baseline.is_dir():
                copy = link_or_copy if getattr(self.backend, "lease", None) else shutil.copy2
                shutil.copytree(baseline, deps / name, copy_function=copy)
        for path, data in dependencies.items():
            study.write_new(deps / path, data)
        return candidate, build, deps

    def check(self, node, proof, issue, *, admit=True, examine=True, dependencies=None):
        """An accepted certificate binds a concrete source and two completed protected checks."""
        try:
            source = assembled(node, proof, admit=admit)
        except ValueError as error:
            return {"accepted": False, "status": "refused", "diagnostic": str(error), "checks": []}
        bound = self.dependency_files(issue) if dependencies is None else dependencies
        candidate, build, deps = self.layout(node["id"], node, source, bound)
        checks = [self.execute(candidate, build, deps, node["path"], "target")]
        if examine and checks[0]["execution"]["status"] == "completed":
            for suffix in ARTIFACT_SUFFIXES:
                path = node["module"].replace(".", "/") + suffix
                if (build / path).is_file():
                    study.write_new(deps / path, (build / path).read_bytes())
            study.write_new(candidate / "Examiner.lean", examiner(node))
            checks.append(self.execute(candidate, build, deps, "Examiner.lean", "examiner"))
        accepted = all(row["execution"]["status"] == "completed" for row in checks)
        status = "passed" if accepted else "failed" if any(row["execution"]["status"] == "failed"
                 for row in checks) else "unavailable"
        artifact_paths = [node["module"].replace(".", "/") + suffix for suffix in ARTIFACT_SUFFIXES]
        artifacts = [{"path": path, "hash": self.store.put((build / path).read_bytes())}
                     for path in artifact_paths if (build / path).is_file()] if accepted else []
        if accepted and node["module"].replace(".", "/") + ".olean" not in [a["path"] for a in artifacts]:
            raise ValueError("compiler completed without its required module artifact")
        result = {"schema": 1, "accepted": accepted, "status": status, "node": node["id"],
                  "issue": issue["hash"], "operands": issue["operands"], "snapshot": self.backend.snapshot,
                  "source": self.store.put(source), "checks": checks, "artifacts": artifacts,
                  "examined": examine, "used_constants": json.loads((build / "used-constants.json").read_bytes())
                  if accepted and examine else None,
                  "diagnostic": None if accepted else diagnostics(self.store, checks)}
        return {**result, "certificate": self.store.put(study.canonical(result))}

    def validate_result(self, issue, result):
        """Re-admit durable results before retirement/recovery, without trusting a stored green flag alone."""
        if result["outcome"] != "green":
            return None
        node = self.nodes[issue["step"]]
        outputs = {row["path"]: row["hash"] for row in result["outputs"]}
        expected = {node["path"], ".ontologic/certificates/" + node["id"] + ".json"}
        if set(outputs) != expected:
            return "accepted outputs differ from this node's destinations"
        certificate = json.loads(object_bytes(self.store, outputs[".ontologic/certificates/" + node["id"] + ".json"]))
        if (certificate["issue"] != issue["hash"] or certificate["operands"] != issue["operands"]
                or certificate["node"] != node["id"] or certificate["snapshot"] != self.backend.snapshot
                or certificate["source"] != outputs[node["path"]] or not certificate["examined"]):
            return "certificate binding differs from the native issue"
        source = object_bytes(self.store, certificate["source"])
        prefix = (node["header"].rstrip() + "\n\n" + node["statement"].rstrip() + " := ").encode()
        if not source.startswith(prefix) or assembled(node, source[len(prefix):].decode()) != source:
            return "accepted source differs from frozen statement/proof grammar"
        if [row["id"] for row in certificate["checks"]] != ["target", "examiner"]:
            return "acceptance requires target and protected examiner"
        for row in certificate["checks"]:
            execution = row["execution"]
            if execution["status"] != "completed" or execution["exit"] != 0 or execution.get("survived"):
                return "acceptance contains an incomplete protected check"
            retained = json.loads(object_bytes(self.store, execution["receipt"]))
            if retained != {key: value for key, value in execution.items() if key != "receipt"}:
                return "checker execution differs from retained receipt"
        artifacts = certificate["artifacts"]
        paths = [artifact["path"] for artifact in artifacts]
        base = node["module"].replace(".", "/")
        if (len(paths) != len(set(paths)) or base + ".olean" not in paths
                or not set(paths) <= {base + suffix for suffix in ARTIFACT_SUFFIXES}):
            return "certificate artifacts differ from the declared module"
        for artifact in artifacts:
            object_bytes(self.store, artifact["hash"])
        return None

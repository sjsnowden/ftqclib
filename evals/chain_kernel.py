"""Act: a proof-chain host for the existing OntolKernel ISA and scheduler.

The native log owns readiness and retirement. The study journal owns durable child
results and Git checkpoint observations. An interrupted issue is resumed only from
a verified result; unknown execution is refused before native abandonment. Git is
a projection of immutable accepted bytes, never evidence that a proof was accepted.
The caller owns the study admission lock and supplies an independently checked
result validator. This host runs one child at a time and disables operator control.
"""
import importlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys


def native_modules(path):
    """Observe the explicitly named kernel, refusing an already imported other copy."""
    root = Path(path).resolve()
    for name in ("run", "kernel"):
        sys.path.insert(0, str(root / name))
    module = importlib.import_module("kernel")
    if Path(module.__file__).resolve() != root / "kernel" / "kernel.py":
        raise ValueError("another OntolKernel copy is already imported")
    return module


def issue_binding(issue, manifest_hash):
    """The durable return names the exact instruction and every versioned operand."""
    return {"schema": 1, "manifest": manifest_hash, "issue": issue["hash"],
            "plan_version": issue.get("plan_version"), "operands": issue["operands"]}


def output_refusal(step, result):
    """Admit only explicit file destinations; a green result supplies all of them."""
    paths = [item["path"] for item in result["outputs"]]
    declared = step["writes"]
    for path in [*declared, *paths]:
        value = PurePosixPath(path)
        if not path or value.is_absolute() or ".." in value.parts or "\\" in path or ":" in path:
            return "unsafe output path"
        if set(path) & set("*?[") or value.as_posix() != path:
            return "chain outputs must be exact normalized paths"
    if len(paths) != len(set(paths)) or not set(paths) <= set(declared):
        return "result writes outside its declared destinations"
    if result["outcome"] == "green" and set(paths) != set(declared):
        return "accepted result omits a declared destination"
    return None


def git(root, *arguments):
    """Run one bounded Git effect in the owned contribution worktree."""
    command = ["git", "-c", "user.name=OntolKernel", "-c", "user.email=kernel@localhost",
               "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgSign=false", *arguments]
    result = subprocess.run(command, cwd=root, capture_output=True, timeout=60)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", "replace"))
    return result.stdout


def existing_checkpoint(root, retirement):
    """Read at most ten matching commits; duplicates are a refusal, never a choice."""
    trailer = "Ontol-Retirement: " + retirement["hash"]
    raw = git(root, "log", "-10", "--format=%H%x00%B%x00", "--fixed-strings", "--grep=" + trailer)
    fields, matches = raw.decode("utf-8").split("\0"), []
    for index in range(0, len(fields) - 1, 2):
        if trailer in fields[index + 1].splitlines():
            matches.append(fields[index].strip())
    if len(matches) > 1:
        raise ValueError("duplicate Git checkpoints for one retirement")
    return matches[0] if matches else None


def verify_checkpoint(root, commit, retirement, digest):
    """Check both the bytes projected and the exact extent of the Git write."""
    paths = {item["path"] for item in retirement["outputs"]}
    changed = git(root, "diff-tree", "--no-commit-id", "--name-only", "-r", "-z", commit)
    if not {item.decode("utf-8") for item in changed.split(b"\0") if item} <= paths:
        raise ValueError("checkpoint contains undeclared paths")
    for item in retirement["outputs"]:
        if item["hash"] is None:
            if git(root, "ls-tree", commit, "--", item["path"]):
                raise ValueError("checkpoint retained a deleted output")
        elif digest(git(root, "show", commit + ":" + item["path"])) != item["hash"]:
            raise ValueError("checkpoint differs from immutable accepted bytes")


def create_checkpoint(root, head, retirement):
    """Commit only declared paths, preserving unrelated staged work."""
    paths = [item["path"] for item in retirement["outputs"]]
    if paths:
        git(root, "add", "-A", "--", *paths)
    message = (retirement["step"] + ": accepted proof\n\nOntol-Head: " + head
               + "\nOntol-Retirement: " + retirement["hash"] + "\n")
    git(root, "commit", "-q", "--only", "--allow-empty", "-m", message, "--", *paths)
    return git(root, "rev-parse", "HEAD").decode("ascii").strip()


def make_kernel(root, manifest, study_store, runner, validate_result):
    """Build the native kernel with a durable return and checkpoint boundary.

    ``runner(job)`` receives the native job unchanged. It calls
    ``kernel.retain_result(job['issue'], result)`` before returning; close also
    enforces retention. ``validate_result(issue, result)`` returns None or a
    refusal, including independent verification of every accepted check receipt.
    The manifest names id, kernel and kernel_config; plan/profile files exist
    under root. Configuration and manifest identity cannot change on resume.
    """
    module = native_modules(manifest["kernel"])
    manifest = json.loads(module.canonical(manifest))
    manifest_hash = module.sha256(module.canonical(manifest))
    config = {**module.DEFAULTS, **manifest["kernel_config"], "concurrency": 1,
              "input_scope": "dependencies", "control_enabled": False, "control_idle_s": 0,
              "attempt_mailboxes": False, "message_routes": {}, "record": None}
    config["chain_manifest"] = manifest_hash
    host_type = type("ChainKernel", (ChainEffects, module.Kernel), {})
    host = host_type(str(root), manifest["id"], config, attempt_runner=runner)
    host.native = module
    host.store = module.Store(host.store.root, study_store.objects)
    host.study_store, host.manifest_hash = study_store, manifest_hash
    host.chain_manifest, host.continuation = manifest, manifest.get("continuation")
    host.validate_result = validate_result
    return host


class ChainEffects:
    """The result and checkpoint effects around native decisions."""
    def issue(self, step_id, ceiling_usd, floor_usd):
        admission = getattr(self.attempt_runner, "admission_refusal", None)
        reason = admission() if admission else None
        if reason is not None:
            if not isinstance(reason, str) or not reason:
                raise ValueError("runner admission must return None or a refusal reason")
            self.deferred[step_id] = reason
            return None
        return super().issue(step_id, ceiling_usd, floor_usd)

    def result_record(self, issue):
        records = [entry for entry in self.study_store.entries()
                   if entry["kind"] == "node_result" and entry.get("study") == self.run_id
                   and entry.get("issue") == issue["hash"]]
        if len(records) > 1:
            raise ValueError("multiple durable results for one issue")
        if not records:
            return None
        receipt = json.loads(self.study_store.get(records[0]["receipt"]))
        expected = issue_binding(issue, self.manifest_hash)
        if receipt.get("binding") != expected or receipt.get("result") != records[0]["result"]:
            raise ValueError("durable result does not bind this instruction")
        result = json.loads(self.study_store.get(receipt["result"]))
        self.check_result(issue, result)
        return records[0], result

    def check_result(self, issue, result):
        known = {entry["hash"]: entry for entry in self.entries() if entry["kind"] == "issue"}
        if known.get(issue["hash"]) != issue or issue["run"] != self.run_id:
            raise ValueError("return names an unknown or altered native issue")
        refusal = output_refusal(self.steps[issue["step"]], result)
        if refusal:
            raise ValueError(refusal)
        for item in result["outputs"]:
            if item["hash"] is not None:
                self.store.get(item["hash"])
        refusal = self.validate_result(issue, result)
        if refusal is not None:
            raise ValueError("durable result refused: " + str(refusal))

    def retain_result(self, issue, result):
        self.check_result(issue, result)
        existing = self.result_record(issue)
        digest = self.native.sha256(self.native.canonical(result))
        if existing:
            if existing[0]["result"] != digest:
                raise ValueError("a durable result cannot be replaced")
            return existing[0]
        self.study_store.put(self.native.canonical(result))
        receipt = self.study_store.put(self.native.canonical({
            "binding": issue_binding(issue, self.manifest_hash), "result": digest}))
        return self.study_store.append("node_result", self.now(), study=self.run_id,
                                       slot=issue["step"], issue=issue["hash"], receipt=receipt, result=digest)

    def close(self, issue, result):
        self.retain_result(issue, result)
        return super().close(issue, result)

    def commit(self, event, made):
        group = super().commit(event, made)
        for entry in group:
            if entry["kind"] == "retire":
                self.checkpoint(entry)
        return group

    def checkpoint(self, retirement):
        recorded = [entry for entry in self.study_store.entries() if entry["kind"] == "node_retired"
                    and entry.get("study") == self.run_id and entry.get("retirement") == retirement["hash"]]
        if len(recorded) > 1:
            raise ValueError("duplicate retirement observations")
        commit = existing_checkpoint(self.root, retirement)
        if recorded and commit != recorded[0]["checkpoint"]:
            raise ValueError("recorded checkpoint is missing or replaced")
        if commit is None:
            self.native.sandbox.apply(self.root, retirement["outputs"], self.store)
            commit = create_checkpoint(self.root, self.store.head_hash(), retirement)
        verify_checkpoint(self.root, commit, retirement, self.native.sha256)
        if not recorded:
            issue = next(entry for entry in self.entries() if entry["hash"] == retirement["issue"])
            record, result = self.result_record(issue)
            summary = result.get("chain", {})
            fields = {key: summary[key] for key in
                      ("model_calls", "tokens", "elapsed_seconds", "worker_tool_calls") if key in summary}
            self.study_store.append("node_retired", self.now(), study=self.run_id, slot=retirement["step"],
                                    issue=issue["hash"], retirement=retirement["hash"], checkpoint=commit,
                                    result_object=record["result"], result=summary, chain=summary, **fields)

    def recover(self):
        import chain_continue
        entries = self.entries()
        pin = self.native.state_module.latest_pin(entries, self.run_id)
        if pin and pin["config"].get("chain_manifest") != self.manifest_hash:
            return "chain manifest changed since pinning"
        refusal = self.native.decide.pin_refusal(entries, self.setting, self.observed_pins())
        if refusal:
            return refusal
        chain_continue.validate_inherited(self)
        pending = []
        for issue in self.native.state_module.open_issues(entries, self.run_id):
            saved = self.result_record(issue)
            if saved is None:
                return "ambiguous interrupted invocation; no durable result for " + issue["step"]
            pending.append((issue, saved[1]))
        for issue, result in pending:
            self.close(issue, result)
        for retirement in self.native.state_module.retired(self.entries()).values():
            if retirement["run"] == self.run_id:
                self.checkpoint(retirement)
        return None

    def begin(self, ceiling_usd, floor_usd):
        tail = self.store.set_aside_tail()
        if tail:
            self.commit("tail", self.native.decide.on_tail(self.entries(), self.setting, tail, self.now()))
        refusal = self.recover()
        return refusal if refusal else super().begin(ceiling_usd, floor_usd)

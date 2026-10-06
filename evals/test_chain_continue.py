"""Goal: reuse accepted work across implementation versions without inventing acceptance or usage.

Method: real Git and native kernel logs, finite local workers, a closed unknown
invocation, and planted source/plan/history faults. No models or Lean compilers.
"""
import copy
import json
from pathlib import Path
import tempfile

import chain_continue
import chain_kernel
import study
import test_chain_kernel as controls

NATIVE = controls.NATIVE


def check(name, condition):
    if not condition:
        raise AssertionError(name)
    print("ok: " + name, flush=True)


def fixture(directory):
    root = directory / "source"
    root.mkdir()
    worktree, manifest, _ = controls.fixture(root)
    records = NATIVE.Store(str(root / "records"))
    manifest["nodes"] = [{"id": name, "module": name, "path": name + ".lean", "name": name,
                          "header": "import Base", "statement": "True", "expected_type": "True",
                          "deps": [] if index == 0 else ["T01.1"], "evidence": [["Base", "lemma"]]}
                         for index, name in enumerate(("T01.1", "T01.2"))]
    manifest.update(source_commit="baseline", snapshot_id="a" * 64, compiler={"id": "compiler"}, formalism={})
    data = NATIVE.canonical(manifest)
    study.write_new(root / "manifest.json", data)
    study.write_new(root / "manifest.ref", records.put(data).encode())
    def worker(job):
        issue = job["issue"]
        answer = controls.result(kernel, issue)
        usage = dict(input_tokens=5, cache_read_input_tokens=0, cache_creation_input_tokens=0, output_tokens=2)
        if issue["step"] == "T01.2":
            answer.update(outcome="red", outputs=[], rows=[{"name": "unresolved", "ok": False}])
            answer["agent"].update(tokens=None, usage=None)
            answer["chain"].update(tokens=None, usage=None)
            usage = None
        fields = {"issue": issue["hash"], "slot": issue["step"], "round": 1, "invocation": issue["hash"]}
        study.event(records, manifest["id"], "proposal_start", **fields)
        study.event(records, manifest["id"], "proposal_end", usage=usage, **fields)
        kernel.retain_result(issue, answer)
        return answer
    kernel = chain_kernel.make_kernel(worktree, manifest, records, worker, controls.validator)
    kernel.run(["T01.1", "T01.2"], 100, 0)
    return root, manifest, kernel


def target(directory, source, prior, *, title=False, identity="new-chain"):
    root = directory / "target"
    root.mkdir()
    worktree = root / "worktree"
    chain_kernel.git(directory, "clone", "--quiet", "--no-local", str(source / "worktree"), str(worktree))
    manifest = copy.deepcopy(prior)
    manifest["id"] = identity
    manifest["policy"] = {"max_calls": 2, "requires_authorization": True}
    manifest["nodes"][0]["evidence"] = [["Base", "betterPromptEvidence"]]
    if title:
        (worktree / "TARGETS.md").write_text("Revised owner efficiency policy; same theorems.\n")
        chain_kernel.git(worktree, "add", "TARGETS.md")
        chain_kernel.git(worktree, "commit", "-qm", "Version owner policy")
    return root, worktree, manifest, NATIVE.Store(str(root / "records"))


def adopted(directory):
    source, prior, original = fixture(directory)
    root, worktree, manifest, records = target(directory, source, prior, title=True)
    old_log, old_head = Path(original.store.log).read_bytes(), original.store.head_hash()
    reference = chain_continue.adopt(source, worktree, manifest, records, controls.validator)
    manifest["continuation"] = reference
    study.write_new(root / "manifest.json", NATIVE.canonical(manifest))
    study.write_new(root / "manifest.ref", records.put(NATIVE.canonical(manifest)).encode())
    certificate = json.loads(records.get(reference))
    check("unknown prior usage is carried explicitly", certificate["prior_usage"]["tokens"] is None
          and certificate["prior_usage"]["known_tokens"] == 7
          and len(certificate["prior_usage"]["unknown_invocations"]) == 1)
    check("prompt metadata may change without revising accepted mathematics",
          certificate["prompt_metadata_changed"] == ["T01.1"])
    calls = []
    def worker(job):
        calls.append(job["issue"])
        fields = {"issue": job["issue"]["hash"], "slot": job["step"]["id"], "round": 1,
                  "invocation": job["issue"]["hash"]}
        usage = dict(input_tokens=5, cache_read_input_tokens=0, cache_creation_input_tokens=0, output_tokens=2)
        study.event(records, manifest["id"], "proposal_start", **fields)
        study.event(records, manifest["id"], "proposal_end", usage=usage, **fields)
        return controls.result(kernel, job["issue"])
    kernel = chain_kernel.make_kernel(worktree, manifest, records, worker, controls.validator)
    check("source native prefix copied byte for byte", Path(kernel.store.log).read_bytes() == old_log
          and kernel.store.head_hash() == old_head)
    kernel.run(["T01.1", "T01.2"], 100, 0)
    check("only unfinished node is issued in new study", [row["step"] for row in calls] == ["T01.2"])
    check("new issue consumes inherited accepted hash", calls[0]["operands"][0]["hash"]
          == certificate["accepted"][0]["outputs"][0]["hash"])
    inherited = [row for row in records.entries() if row["kind"] == "node_retired" and row.get("inherited")]
    check("inherited viewer observation separates old and new usage", len(inherited) == 1
          and inherited[0]["result"]["tokens"] == 0 and inherited[0]["source_usage"]["tokens"] == 7)
    check("source records remain immutable", Path(original.store.log).read_bytes() == old_log
          and original.store.head_hash() == old_head)
    check("both nodes stand after new native completion", set(NATIVE.state_module.retired(kernel.entries()))
          == {"T01.1", "T01.2"})
    another_generation(directory, root, manifest)


def another_generation(directory, source, prior):
    (directory / "third").mkdir()
    root, worktree, manifest, records = target(directory / "third", source, prior, identity="third-chain")
    reference = chain_continue.adopt(source, worktree, manifest, records, controls.validator)
    manifest["continuation"] = reference
    certificate = json.loads(records.get(reference))
    check("unknown exposure survives another implementation version", certificate["prior_usage"]["tokens"] is None
          and certificate["prior_usage"]["known_tokens"] == 14
          and len(certificate["prior_usage"]["unknown_invocations"]) == 1)
    kernel = chain_kernel.make_kernel(worktree, manifest, records, controls.unused, controls.validator)
    kernel.run(["T01.1", "T01.2"], 100, 0)
    check("multi-generation accepted work needs no worker calls", not any(
        row["kind"] == "issue" and row["run"] == manifest["id"] for row in kernel.entries()))


def refuses(directory, fault):
    source, prior, original = fixture(directory)
    root, worktree, manifest, records = target(directory, source, prior)
    if fault == "statement":
        manifest["nodes"][0]["statement"] = "False"
    elif fault == "native plan":
        plan = json.loads((worktree / "plan.json").read_bytes())
        plan["steps"][0]["agent"]["model"] = "changed"
        (worktree / "plan.json").write_text(json.dumps(plan))
        chain_kernel.git(worktree, "add", "plan.json")
        chain_kernel.git(worktree, "commit", "-qm", "Changed accepted instruction")
    elif fault == "output":
        (worktree / "T01.1.lean").write_text("unaccepted replacement")
        chain_kernel.git(worktree, "add", "T01.1.lean")
        chain_kernel.git(worktree, "commit", "-qm", "Changed inherited proof")
    elif fault == "open issue":
        original.issue("T01.1", 100, 0)
    elif fault == "unknown object":
        digest = original.study_store.put(b"corrupt me")
        Path(original.study_store.object_path(digest)).write_bytes(b"corrupted bytes")
    try:
        chain_continue.adopt(source, worktree, manifest, records, controls.validator)
    except (ValueError, RuntimeError):
        check("adoption refuses " + fault, not Path(worktree / ".state/log/HEAD").exists())
    else:
        check("adoption refuses " + fault, False)


def without_certificate(directory):
    source, prior, original = fixture(directory)
    root, worktree, manifest, records = target(directory, source, prior)
    chain_continue.adopt(source, worktree, manifest, records, controls.validator)
    kernel = chain_kernel.make_kernel(worktree, manifest, records, controls.unused, controls.validator)
    try:
        kernel.begin(100, 0)
    except ValueError as error:
        check("foreign retirement cannot bypass explicit adoption", "explicit continuation certificate" in str(error))
    else:
        check("foreign retirement cannot bypass explicit adoption", False)


def main():
    for case in (adopted, without_certificate):
        with tempfile.TemporaryDirectory(prefix="ontol-continue-") as directory:
            case(Path(directory))
    for fault in ("statement", "native plan", "output", "open issue", "unknown object"):
        with tempfile.TemporaryDirectory(prefix="ontol-continue-") as directory:
            refuses(Path(directory), fault)
    print("All continuation controls passed.")


if __name__ == "__main__":
    main()

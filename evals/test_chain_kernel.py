"""Goal: native DAG retirement survives interruption without repeating paid work.

Method: real temporary Git repositories, real native ISA decisions, finite injected
workers and planted interruption points. No model, compiler, network or test mocks.
"""
import copy
import json
from pathlib import Path
import tempfile
import os

import chain_kernel

KERNEL = Path(os.environ.get("ONTOLKERNEL", Path(__file__).resolve().parents[3] / "ontolkernel"))
NATIVE = chain_kernel.native_modules(KERNEL)
import replay
PROFILE = '''GATED_KINDS = ("proof", "run")
CODE_KINDS = ()
CONTRACT_KIND = None
SHARED_WRITES = ()
def brief_lines(step): return []
def blind_brief(step, allowed, common): return ["Return the specified proof."]
def brief_inputs(root, step): return None, None
def gate_rows(root, plan, step, deadline, expected): return [], None
def code_files(step): return [], [], []
'''


def check(name, condition):
    if not condition:
        raise AssertionError(name)
    print("ok: " + name, flush=True)


def step(identifier, dependencies):
    return {"id": identifier, "target": "T01", "phase": 1, "kind": "proof",
            "title": identifier, "artifact": "proof", "gate": "owner", "writes": [identifier + ".lean"],
            "frozen": [], "depends_on": dependencies, "commands": [], "agent_type": None,
            "scheduled": True, "agent": {"model": "scripted", "effort": "medium"}}


def fixture(directory):
    root = directory / "worktree"
    root.mkdir()
    plan = {"steps": [step("T01.1", []), step("T01.2", ["T01.1"])], "reviewed_steps": []}
    for name, data in {"plan.json": json.dumps(plan), "profile.py": PROFILE,
                       "TARGETS.md": "### T01 Proof chain\nDeterministic control.\n",
                       ".gitignore": ".state/\n"}.items():
        (root / name).write_text(data)
    chain_kernel.git(root, "init", "-q")
    chain_kernel.git(root, "add", ".")
    chain_kernel.git(root, "commit", "-qm", "protected seed")
    manifest = {"id": "chain-controls", "kernel": str(KERNEL), "kernel_config": {
        "plan": "plan.json", "profile": "profile.py", "targets": "TARGETS.md", "binding": "TARGETS.md",
        "pins": ["plan.json", "profile.py", "TARGETS.md"], "state": ".state", "harness": str(KERNEL)}}
    journal = NATIVE.Store(str(directory / "study"))
    journal.put((root / "plan.json").read_bytes())
    journal.put(NATIVE.canonical(plan))
    return root, manifest, journal


def validator(issue, result):
    return None if result.get("owner_checked") == issue["hash"] else "missing owner check binding"


def unused(job):
    raise AssertionError("interrupted work must not be launched again")


def host(fixture_, runner=unused, validate=validator):
    return chain_kernel.make_kernel(*fixture_, runner, validate)


def result(kernel, issue):
    data = ("accepted " + issue["step"] + "\n").encode()
    digest = kernel.study_store.put(data)
    return {"agent": {"finished": True, "cost_usd": 0, "tokens": 7, "turns": 1},
            "outputs": [{"path": issue["step"] + ".lean", "hash": digest, "mode": ""}],
            "outside": [], "fault": None, "fault_refusal": None, "gate_ran": True,
            "gate_detail": None, "rows": [{"name": "owner acceptance", "ok": True}],
            "contract": None, "review": None, "outcome": "green", "owner_checked": issue["hash"],
            "chain": {"model_calls": 1, "tokens": 7, "worker_tool_calls": 0}}


def native_dispatch(directory):
    found, captured = fixture(directory), []
    def worker(job):
        captured.append(job)
        answer = result(kernel, job["issue"])
        kernel.retain_result(job["issue"], answer)
        return answer
    kernel = host(found, worker)
    check("forced dependency projection and serial execution", kernel.config["concurrency"] == 1
          and kernel.config["input_scope"] == "dependencies")
    kernel.run(["T01.2", "T01.1"], 100, 0)
    check("native scheduler waits for dependency", [job["step"]["id"] for job in captured] == ["T01.1", "T01.2"])
    first, second = captured
    expected = {"step": "T01.1", "path": "T01.1.lean", "hash": NATIVE.sha256(b"accepted T01.1\n")}
    check("native issue binds exact accepted operand", second["issue"]["operands"] == [expected])
    check("injected runner receives native job and store", first["store"] is kernel.store
          and first["issue"] in kernel.entries() and "files" in first and "brief" in first)
    checks = [entry for entry in found[2].entries() if entry["kind"] == "node_retired"]
    check("retirement yields two verified Git checkpoints", len(checks) == 2
          and all(entry["tokens"] == 7 for entry in checks))
    check("viewer summary remains separate from immutable result identity", all(
        entry["result"]["model_calls"] == 1 and len(entry["result_object"]) == 64 for entry in checks))
    replayed = replay.replay_decisions(str(found[0]), kernel.run_id, config=kernel.config, store=kernel.store)
    check("native decision replay reads explicit configuration and shared plan objects",
          replayed["replayable"] and replayed["decisions"] == replayed["reproduced"] == 2
          and not replayed["differing"])
    before = len(captured)
    host(found).run(["T01.1", "T01.2"], 100, 0)
    check("finished chain resume never repeats workers", len(captured) == before)
    check("default native attempt runner preserved", NATIVE.Kernel(str(found[0]), "plain", kernel.config)
          .attempt_runner is NATIVE.attempt_module.run_attempt)


def durable_before_close(directory):
    found = fixture(directory)
    kernel = host(found)
    check("fresh native begin accepted", kernel.begin(100, 0) is None)
    issue, _ = kernel.issue("T01.1", 100, 0)
    saved = result(kernel, issue)
    receipt = kernel.retain_result(issue, saved)
    binding = json.loads(found[2].get(receipt["receipt"]))["binding"]
    check("durable receipt binds plan, issue and operands", binding["issue"] == issue["hash"]
          and binding["plan_version"] == issue["plan_version"] and binding["operands"] == issue["operands"])
    resumed = host(found)
    check("durable result closes after process interruption", resumed.begin(100, 0) is None)
    check("recovery retires exactly once without abandon", list(NATIVE.state_module.retired(resumed.entries())) == ["T01.1"]
          and not any(entry["kind"] == "abandon" for entry in resumed.entries()))
    changed = {**saved, "chain": {"tokens": 8}}
    try:
        resumed.retain_result(issue, changed)
    except ValueError as error:
        check("durable result replacement refused", "cannot be replaced" in str(error))
    else:
        check("durable result replacement refused", False)


def retirement_before_checkpoint(directory, existing=False):
    found = fixture(directory)
    kernel = host(found)
    kernel.begin(100, 0)
    issue, _ = kernel.issue("T01.1", 100, 0)
    saved = result(kernel, issue)
    kernel.retain_result(issue, saved)
    decision = NATIVE.decide.on_return(kernel.entries(), kernel.setting, issue, saved, kernel.now())
    NATIVE.Kernel.commit(kernel, "return", decision)
    retirement = NATIVE.state_module.retired(kernel.entries())["T01.1"]
    commit = None
    if existing:
        commit = chain_kernel.create_checkpoint(found[0], kernel.store.head_hash(), retirement)
    else:
        (found[0] / "T01.1.lean").unlink()
    (found[0] / "unrelated.txt").write_text("keep staged")
    chain_kernel.git(found[0], "add", "unrelated.txt")
    resumed = host(found)
    check("retirement checkpoint recovery accepted", resumed.begin(100, 0) is None)
    entries = [entry for entry in found[2].entries() if entry["kind"] == "node_retired"]
    check("checkpoint repaired or reused exactly once", len(entries) == 1
          and (commit is None or entries[0]["checkpoint"] == commit))
    check("unrelated staged work stays outside checkpoint",
          chain_kernel.git(found[0], "diff", "--cached", "--name-only").strip() == b"unrelated.txt")
    check("accepted immutable source restored", (found[0] / "T01.1.lean").read_bytes() == b"accepted T01.1\n")


def ambiguous(directory):
    found = fixture(directory)
    kernel = host(found)
    kernel.begin(100, 0)
    issue, _ = kernel.issue("T01.1", 100, 0)
    resumed = host(found)
    refusal = resumed.begin(100, 0)
    check("ambiguous interrupted call fails closed", "ambiguous interrupted invocation" in refusal)
    check("refusal leaves unresolved issue untouched", NATIVE.state_module.open_issues(resumed.entries(), kernel.run_id) == [issue]
          and not any(entry["kind"] == "abandon" for entry in resumed.entries()))


def stale(directory):
    found = fixture(directory)
    kernel = host(found)
    kernel.begin(100, 0)
    first, _ = kernel.issue("T01.1", 100, 0)
    kernel.close(first, result(kernel, first))
    second, _ = kernel.issue("T01.2", 100, 0)
    kernel.reopen_by_person("T01.1", "control", "seeded predecessor withdrawal")
    route = kernel.close(second, result(kernel, second))
    check("native ISA requeues a stale accepted candidate", route["decision"] == "requeue"
          and "T01.2" not in NATIVE.state_module.retired(kernel.entries()))
    check("stale candidate never reaches Git or output tree", not (found[0] / "T01.2.lean").exists())


def wrong_receipt(directory):
    found = fixture(directory)
    kernel = host(found)
    kernel.begin(100, 0)
    issue, _ = kernel.issue("T01.1", 100, 0)
    saved = result(kernel, issue)
    kernel.retain_result(issue, saved)
    refused = host(found, validate=lambda issue, answer: "seeded checker refusal")
    try:
        refused.begin(100, 0)
    except ValueError as error:
        check("resume independently revalidates result evidence", "seeded checker refusal" in str(error))
    else:
        check("resume independently revalidates result evidence", False)
    changed = copy.deepcopy(found[1])
    changed["new_plan"] = "different"
    kernel = host((found[0], changed, found[2]))
    check("resume refuses changed manifest", kernel.begin(100, 0) == "chain manifest changed since pinning")
    check("output authority remains exact", chain_kernel.output_refusal(step("T01.1", []),
          {**saved, "outputs": [{"path": "../escape", "hash": "a" * 64}]}) == "unsafe output path")


def preissue_admission(directory):
    found = fixture(directory)
    class RefusedRunner:
        def admission_refusal(self):
            return "unknown prior invocation usage"
        def __call__(self, job):
            raise AssertionError("refused admission must not start a worker")
    kernel = host(found, RefusedRunner())
    end = kernel.run(["T01.1", "T01.2"], 100, 0)
    check("runner admission refuses before any native issue", not any(
        row["kind"] == "issue" for row in kernel.entries())
        and end["deferred"] == {"T01.1": "unknown prior invocation usage"})


def main():
    cases = [native_dispatch, durable_before_close, retirement_before_checkpoint, ambiguous, stale,
             wrong_receipt, preissue_admission]
    for case in cases:
        with tempfile.TemporaryDirectory(prefix="ontol-chain-") as directory:
            case(Path(directory))
    with tempfile.TemporaryDirectory(prefix="ontol-chain-") as directory:
        retirement_before_checkpoint(Path(directory), existing=True)
    print("All chain kernel controls passed.")


if __name__ == "__main__":
    main()

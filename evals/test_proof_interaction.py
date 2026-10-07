"""Goal: typed proof submissions reuse native admission, checking and durable answers.

Method: disposable Git fixtures and finite scripted providers; actual shared CLI,
terminal subprocess and stdin/file submission. No model, Lean or network effects.
"""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile

os.environ.setdefault("ONTOLKERNEL", str(Path(__file__).resolve().parents[2] / "ontolkernel-proof"))
import chain_kernel
import proof_program
import proof_control
import study
import test_proof_program as native

import control_cli
import control_run
import control_transport
import messages
import replay
import trace_panes
import work_submit


def check(name, condition):
    if not condition:
        raise AssertionError(name)
    print("ok: " + name, flush=True)


def fixture(directory):
    original, _ = native.fixture(directory)
    manifest = copy.deepcopy(original.chain_manifest)
    manifest["kernel_config"].update(proof_program.interaction_config(
        manifest["proof_program"], manifest["nodes"], manifest["id"]))
    runner = native.Scripted(directory, manifest, original.study_store)
    kernel = chain_kernel.make_kernel(Path(original.root), manifest, original.study_store, runner,
                                      lambda issue, result: None)
    runner.kernel = kernel
    config = Path(kernel.root) / "driver-config.json"
    config.write_bytes(study.canonical(manifest["kernel_config"]))
    (directory / "driver-config.json").write_bytes(study.canonical(manifest["kernel_config"]))
    (directory / "manifest.json").write_bytes(study.canonical(manifest))
    (directory / "manifest.ref").write_text(study.digest(study.canonical(manifest)))
    return kernel, runner, str(config)


def worker_exchange(directory):
    kernel, runner, _ = fixture(directory)
    kernel.run(["T01.1"], 100, 0)
    question = next(entry for entry in kernel.entries() if entry["kind"] == "message")
    future = messages.future(kernel.entries(), kernel.run_id, question["hash"], kernel.store.get)
    check("opt-in worker question mechanically binds typed endpoint", future["closed"]
          and future["status"] == "answered" and future["envelope"]["caller"] == "T01.1")
    check("typed advice still requires independent proof checking", len(runner.checker.calls) == 1)
    check("new invocation consumes reply rather than live model session", len(runner.calls) == 3
          and len([entry for entry in kernel.entries() if entry["kind"] == "issue"]) == 2)
    report = replay.replay_decisions(kernel.root, kernel.run_id, config=kernel.config, store=kernel.store)
    check("typed proof continuation replays exactly", not report["differing"])


def owner_exchange(directory, retained=None):
    kernel, runner, config = fixture(directory)
    check("owner fixture begins", kernel.begin(100, 0) is None)
    before = Path(kernel.store.log).read_bytes(), Path(kernel.store.head).read_bytes()
    words = ["invoke", "assess_prerequisite", "assess", '{"request":"inspect missing prerequisite"}',
             "--source", "T01.1", "--key", "owner-future"]
    result, code = control_cli.execute(kernel.root, kernel.run_id, words, config)
    identity = result["request"]
    request = next(item["request"] for item in control_transport.pending(kernel.store.root)
                   if item["id"] == identity)
    check("owner submission does not write native facts", code == 0 and result["status"] == "submitted"
          and before == (Path(kernel.store.log).read_bytes(), Path(kernel.store.head).read_bytes()))
    payload_file = Path(kernel.root) / "invoke.json"
    payload_file.write_bytes(study.canonical(request))
    file_result, _ = control_cli.execute(kernel.root, kernel.run_id, ["invoke", "invoke.json"], config)
    stdin_result, _ = control_cli.request_json(kernel.root, kernel.run_id, config, study.canonical(request))
    bridge_result, _ = proof_control.execute(directory, data=study.canonical(request))
    job = trace_panes.CommandJob(kernel.root, kernel.run_id, "invoke invoke.json", 0, config)
    job.process.wait(timeout=15)
    terminal_result = job.poll(0)
    check("Python flags file stdin and terminal have identical canonical request",
          {file_result["request"], stdin_result["request"], terminal_result["request"], bridge_result["request"]} == {identity})
    recorded = (directory / "driver-config.json").read_bytes()
    (directory / "driver-config.json").write_bytes(study.canonical({"state": "different"}))
    try:
        proof_control.execute(directory, data=study.canonical(request))
    except ValueError as error:
        check("proof command bridge refuses altered pinned configuration", "configuration differs" in str(error))
    else:
        check("proof command bridge refuses altered pinned configuration", False)
    (directory / "driver-config.json").write_bytes(recorded)
    control_run.poll(kernel)
    question = next(entry for entry in kernel.entries() if entry["kind"] == "message")
    check("owner invocation cannot resume proof or restore draft", question["source"] == "control"
          and question["draft"] == [] and messages.latest(kernel.entries(), kernel.run_id, "T01.1") == (None, None))
    admitted, _ = control_cli.execute(kernel.root, kernel.run_id, ["inspect", identity], config)
    check("admission remains distinct from completion", admitted["status"] == "admitted"
          and admitted["future"]["status"] == "pending" and not admitted["future"]["closed"])
    kernel.run(["T01.1"], 100, 0)
    completed, _ = control_cli.execute(kernel.root, kernel.run_id, ["receipt", identity], config)
    check("real native endpoint answer closes owner future", completed["status"] == "completed"
          and completed["outcome"] == "answered" and completed["future"]["closed"])
    report = replay.replay_decisions(kernel.root, kernel.run_id, config=kernel.config, store=kernel.store)
    check("owner invocation and answer decision replay agree", not report["differing"])
    count = len(runner.calls)
    kernel.run(["T01.1"], 100, 0)
    check("closed owner endpoint invocation is never repeated", len(runner.calls) == count)
    if retained:
        retained.parent.mkdir(parents=True, exist_ok=True)
        retained.write_bytes(study.canonical({"schema": 1, "label": "Finite scripted proof interaction fixture; no paid model or Lean claim",
                                             "entries": kernel.entries()}))


def scheduled_inputs(directory):
    kernel, _, config = fixture(directory)
    kernel.begin(100, 0)
    words = ["run", "T01.1", "input", '{"instruction":"keep original obligation"}', "--key", "ready-input"]
    result, _ = control_cli.execute(kernel.root, kernel.run_id, words, config)
    control_run.poll(kernel)
    receipt, _ = control_cli.execute(kernel.root, kernel.run_id, ["receipt", result["request"]], config)
    check("run admits only existing ready scheduled work", receipt["status"] == "admitted")
    issue, _ = kernel.issue("T01.1", 100, 0)
    request = work_submit.construct("run", kernel.run_id, "already-running", kernel.config, kernel.entries(),
                                    kernel.store.get, "T01.1", "input", {})
    work_submit.submit(kernel.store, kernel.store, kernel.run_id, request)
    control_run.poll(kernel)
    identity = study.digest(study.canonical(request))
    refused, _ = control_cli.execute(kernel.root, kernel.run_id, ["inspect", identity], config)
    check("run cannot create another open invocation", refused["status"] == "refused")
    inbox = json.loads(kernel.store.get(issue["control_inbox"]))
    check("typed input reaches exact existing invocation", inbox["messages"][0]["interaction"]["request"]["variant"] == "input")


def main():
    retained = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    with tempfile.TemporaryDirectory(prefix="proof-interaction-") as name:
        for case, function in (("worker", worker_exchange), ("owner", owner_exchange), ("scheduled", scheduled_inputs)):
            directory = Path(name) / case
            directory.mkdir()
            if function is owner_exchange:
                function(directory, retained)
            else:
                function(directory)


if __name__ == "__main__":
    main()

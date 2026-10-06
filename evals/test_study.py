"""Goal: the development study preserves prompt obligations and accounts for every declared slot.

Method: existing public task contracts, pure render/slot/report derivations and
synthetic recorded trial events. No provider, Lean, Lake or build calls.
"""
import json
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import study
import fixtures
import runtime

FIELDS = ("purpose", "obligation", "evidence", "acceptance", "completion", "writes", "standards")


def check(name, condition):
    assert condition, name
    print("ok: " + name, flush=True)


def prompt_information():
    for task in ("F01", "F02"):
        contract = fixtures.task_spec(task)
        rendered = {condition: study.render(contract, condition) for condition in "ABC"}
        check(task + " renderer repeats identical bytes", all(
            study.render(contract, condition) == rendered[condition] for condition in "ABC"))
        facts = [fact for key in FIELDS for fact in (
            contract[key] if isinstance(contract[key], list) else [contract[key]])]
        check(task + " compact condition retains every public fact", all(
            fact in rendered["C"].decode() for fact in facts))
        check(task + " compact prompt is shorter by measured bytes", len(rendered["C"]) < len(rendered["B"]))
        check(task + " expanded condition exposes the same public facts", all(
            fact in rendered["B"].decode() for fact in facts))
        check(task + " baseline has access to the same public contract", contract["obligation"]
              in rendered["A"].decode() and ".task/contract.json" in rendered["A"].decode())
        check(task + " renderers never include private examiner fields", all(
            contract["examiner"].encode() not in value and b"{examiner}" not in value
            for value in rendered.values()))
        print(json.dumps({"task": task, "prompt_bytes": {condition: len(value)
                                                         for condition, value in rendered.items()}}))


def declared_slots():
    slots = study.slots(["F01", "F02"], 2)
    check("two-case comparison declares twelve distinct slots", len(slots) == 12
          and len({slot["id"] for slot in slots}) == 12)
    for task in ("F01", "F02"):
        for repetition in (1, 2):
            block = [slot for slot in slots if slot["task"] == task and slot["repetition"] == repetition]
            check(task + " repetition " + str(repetition) + " declares all three conditions",
                  sorted(slot["condition"] for slot in block) == list("ABC"))
    check("slot storage names disclose no condition labels", all(len(slot["id"]) == 32
          and set(slot["id"]) <= set("0123456789abcdef") for slot in slots))
    return {"id": "scripted-study", "slots": slots}


def recorded_accounting(manifest):
    empty = study.report(manifest, [])
    check("unrun slots prevent a complete report", not empty["complete"] and len(empty["slots"]) == 12
          and all(row["execution"] == "not_run" for row in empty["slots"]))
    slot = manifest["slots"][0]["id"]
    started = {"kind": "trial_start", "slot": slot}
    partial = study.report(manifest, [started])
    check("interrupted invocation remains explicit", not partial["complete"]
          and partial["slots"][0]["execution"] == "unfinished" and partial["unknown_token_invocations"] == 1)
    ended = {"kind": "trial_end", "slot": slot, "result": {
        "execution": "candidate", "assessment": "accepted", "tokens": 123, "cost_usd": None}}
    closed = study.report(manifest, [started, ended])
    check("known usage is counted once while other slots remain visible", closed["known_tokens"] == 123
          and closed["unknown_token_invocations"] == 0 and not closed["complete"])
    unknown = {**ended, "result": {**ended["result"], "tokens": None}}
    report = study.report(manifest, [started, unknown])
    check("missing provider usage is unknown rather than zero", report["unknown_token_invocations"] == 1
          and report["slots"][0]["tokens"] is None)
    try:
        study.report(manifest, [started, ended, unknown])
    except ValueError as error:
        conflict = "conflicting" in str(error)
    else:
        conflict = False
    check("contradictory closures cannot select a convenient result", conflict)


def put(root, name, data):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return path


def runtime_fixture(root):
    reference, prepared = root / "reference", root / "runtime"
    sources = {fixtures.Z_SHEAR: b"import FTQCLib.Shared\n",
               "FTQCLib/Stabilizer/ZShearCheck.lean": b"import FTQCLib.Stabilizer.ZShear\n",
               "FTQCLib/Shared.lean": b"import Mathlib.Dummy\n"}
    for name, data in sources.items():
        put(reference, name, data)
    for module in ("FTQCLib/Shared", "FTQCLib/Stabilizer/ZShear", "FTQCLib/Stabilizer/ZShearCheck"):
        for suffix in (".olean", ".ilean", ".olean.private", ".olean.server", ".ir"):
            put(reference, ".lake/build/lib/lean/" + module + suffix, (module + " reference-proof").encode())
    put(reference, "lake-manifest.json", b'{"packages":[{"name":"mathlib","rev":"scripted"},{"name":"Cli"}]}')
    put(reference, ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Dummy.olean", b"third-party fixture")
    code = (f"#!{sys.executable}\nimport sys,pathlib,re,os\n"
            "if '-j2' not in sys.argv or '-M4096' not in sys.argv: sys.exit(2)\n"
            "for module in re.findall(r'^import ([A-Za-z0-9_.]+)',pathlib.Path(sys.argv[-1]).read_text(),re.M):\n"
            " roots=[pathlib.Path(p) for p in os.environ['LEAN_PATH'].split(os.pathsep)]\n"
            " package=module.split('.')[0]\n"
            " selected=next((root for root in roots if (root/package).is_dir()),None)\n"
            " if selected is None or not (selected/(module.replace('.','/')+'.olean')).is_file(): sys.exit(3)\n"
            "if '-o' in sys.argv: pathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'scripted output')\n"
            "print('scripted compiler protocol; not Lean evidence')\n")
    executable = put(prepared, "lean-4.29.1-linux/bin/lean", code.encode())
    executable.chmod(0o755)
    spec = {"task": "F01", "checks": fixtures.check_commands("F01"),
            "excluded_modules": ["FTQCLib.Stabilizer.ZShear", "FTQCLib.Stabilizer.ZShearCheck"]}
    return reference, prepared, spec


def runtime_grants():
    with tempfile.TemporaryDirectory(prefix="ftqc-runtime-") as temporary:
        root = Path(temporary)
        reference, prepared, spec = runtime_fixture(root)
        record = runtime.prepare("F01", reference, prepared, spec)
        check("runtime copies only required local ancestors", record["local_modules"] == ["FTQCLib.Shared"]
              and all("Stabilizer" not in name for name in record["copied"]))
        check("prepared grant byte manifests verify", runtime.verify(record))
        check("unbuilt manifest package is recorded rather than granted", len(record["omitted_packages"]) == 1
              and record["omitted_packages"][0]["package"] == "Cli"
              and record["omitted_packages"][0]["reason"] == "artifact_directory_missing"
              and all("/Cli/" not in path for path in record["readable"]))
        check("a compatible prepared runtime can be reused by another study",
              runtime.prepare("F01", reference, prepared, spec) == record)
        contract = fixtures.task_spec("F01")
        public = runtime.public_files("F01", contract, record)
        check("public files retain identical bytes after canonical JSON reload", public == runtime.public_files(
            "F01", json.loads(runtime.canonical(contract)), json.loads(runtime.canonical(record))))
        check("public contract and commands contain no private examiner paths", "examiner" not in json.loads(
            public[".task/contract.json"]) and b"Examiner.lean" not in public[".task/check.py"])
        worker = root / "worker"
        for name, data in public.items():
            put(worker, name, data)
        for name in (fixtures.Z_SHEAR, "FTQCLib/Stabilizer/ZShearCheck.lean"):
            put(worker, name, (reference / name).read_bytes())
        process = subprocess.run([sys.executable, ".task/check.py"], cwd=worker, capture_output=True, timeout=10)
        check("public helper uses fixed compiler flags and private outputs", process.returncode == 0
              and (worker / ".scratch/build/FTQCLib/Stabilizer/ZShear.olean").read_bytes() == b"scripted output")
        check("public helper supplies the complete local package root before rebuilding affected sources",
              (worker / ".scratch/build/FTQCLib/Shared.olean").read_bytes() == b"FTQCLib/Shared reference-proof"
              and (worker / ".scratch/build/FTQCLib/Stabilizer/ZShearCheck.olean").read_bytes() == b"scripted output")
        repeated = subprocess.run([sys.executable, ".task/check.py"], cwd=worker, capture_output=True, timeout=10)
        check("repeated public checks preserve package-root coverage", repeated.returncode == 0)
        artifact = Path(record["lean_path"][0]) / "FTQCLib/Shared.olean"
        artifact.chmod(0o644)
        artifact.write_bytes(b"mutated")
        try:
            runtime.verify(record)
        except ValueError:
            detected = True
        else:
            detected = False
        check("changed dependency bytes stop admission", detected)
    graph = {"A": ["B", "C", "B"], "B": ["D", "D"], "C": ["D"], "D": []}
    check("diamond and repeated imports remain bounded and complete", runtime.ancestors(graph, ["A", "A"])
          == set(graph))


def cached_verification():
    with tempfile.TemporaryDirectory(prefix="ftqc-cache-") as temporary:
        reference, prepared, spec = runtime_fixture(Path(temporary))
        record = runtime.prepare("F01", reference, prepared, spec)
        cache, calls = {}, []
        original = runtime.file_hash

        def counted(path):
            calls.append(str(path))
            return original(path)

        runtime.file_hash = counted
        try:
            runtime.verify(record, cache)
            cold = len(calls)
            runtime.verify(record, cache)
            check("warm owner cache scans metadata without reading artifact bytes", cold > 0 and len(calls) == cold)
            runtime.prepare("F01", reference, prepared, spec, cache)
            check("reused preparation shares the owner verification cache", len(calls) == cold)
            runtime.verify(record)
            check("default verification still reads every grant byte", len(calls) == 2 * cold)
            key = next(iter(cache))
            cache[key] = (-1, cache[key][1])
            runtime.verify(record, cache)
            check("cache metadata from another process cannot skip a byte audit", len(calls) > 2 * cold)
            artifact = Path(record["lean_path"][0]) / "FTQCLib/Shared.olean"
            before = artifact.stat()
            artifact.chmod(0o644)
            artifact.write_bytes(b"x" * before.st_size)
            artifact.chmod(before.st_mode)
            os.utime(artifact, ns=(before.st_atime_ns, before.st_mtime_ns))
            check("restoring mtime cannot hide a same-size mutation", refused_verification(record, cache)
                  and artifact.stat().st_mtime_ns == before.st_mtime_ns)
        finally:
            runtime.file_hash = original


def private_build_seeding():
    with tempfile.TemporaryDirectory(prefix="ftqc-private-build-") as temporary:
        reference, prepared, spec = runtime_fixture(Path(temporary))
        record = runtime.prepare("F01", reference, prepared, spec)
        build = Path(temporary) / "private/build"
        runtime.verify(record)
        runtime.seed_build(record, build)
        files = {path.relative_to(build).as_posix() for path in build.rglob("*") if path.is_file()}
        check("owner build contains exactly admitted local artifacts", files == set(record["copied"])
              and all("Stabilizer" not in name for name in files))
        original = Path(record["lean_path"][0]) / "FTQCLib/Shared.olean"
        private = build / "FTQCLib/Shared.olean"
        check("private artifacts share bytes without sharing mutable inodes", original.read_bytes() == private.read_bytes()
              and (original.stat().st_dev, original.stat().st_ino) != (private.stat().st_dev, private.stat().st_ino))
        rebuilt = put(build, "FTQCLib/Stabilizer/ZShear.olean", b"private rebuilt source")
        runtime.seed_build(record, build)
        check("repeat seeding cannot introduce target originals", rebuilt.read_bytes() == b"private rebuilt source")
        forged = {**record, "copied": ["FTQCLib/Stabilizer/ZShear.olean"]}
        try:
            runtime.seed_build(forged, Path(temporary) / "forged")
        except ValueError:
            refused = True
        else:
            refused = False
        check("excluded modules cannot enter the seeding grant", refused)
        private.unlink()
        private.symlink_to(original)
        try:
            runtime.seed_build(record, build)
        except ValueError:
            refused = True
        else:
            refused = False
        check("linked private artifact destinations refuse copying", refused)


def refused_verification(record, cache):
    try:
        runtime.verify(record, cache)
    except ValueError:
        return True
    return False


def cache_tree_changes():
    for change in ("addition", "link", "replacement", "mode"):
        with tempfile.TemporaryDirectory(prefix="ftqc-cache-change-") as temporary:
            reference, prepared, spec = runtime_fixture(Path(temporary))
            package = reference / ".lake/packages/mathlib/.lake/build/lib/lean"
            alias = package / "alias"
            alias.symlink_to("Mathlib/Dummy.olean")
            record = runtime.prepare("F01", reference, prepared, spec)
            cache = {}
            runtime.verify(record, cache)
            artifact = package / "Mathlib/Dummy.olean"
            if change == "addition":
                (package / "new-empty-directory").mkdir()
            elif change == "link":
                alias.unlink()
                alias.symlink_to("Mathlib")
            elif change == "replacement":
                data = artifact.read_bytes()
                artifact.unlink()
                artifact.write_bytes(data)
            else:
                artifact.chmod(0o400)
            check("cached verification refuses grant " + change, refused_verification(record, cache))


def cache_audit_race():
    with tempfile.TemporaryDirectory(prefix="ftqc-cache-race-") as temporary:
        reference, prepared, spec = runtime_fixture(Path(temporary))
        record = runtime.prepare("F01", reference, prepared, spec)
        local = Path(record["lean_path"][0])
        original = runtime.tree_manifest

        def changed_after_read(root):
            observed = original(root)
            if root == local:
                (local / "FTQCLib/Shared.olean").chmod(0o400)
            return observed

        runtime.tree_manifest = changed_after_read
        cache = {}
        try:
            check("a metadata change during the deep audit cannot seed the cache",
                  refused_verification(record, cache) and not cache)
        finally:
            runtime.tree_manifest = original


def control_failure_reason():
    check("unstable simp control requires its own style diagnostic",
          study.control_outcome("F01", "unstable-simp", {"status": "refused", "reasons": [
              fixtures.Z_SHEAR + ": simp stability: use explicit only"]}, None)
          and not study.control_outcome("F01", "unstable-simp", {"status": "refused", "reasons": [
              "protected source changed"]}, None))
    reasons = [f"F02 declaration home: {name} must have exactly one declaration site in "
               "FTQCLib/Carrier/CharSumPairing.lean; observed consumer"
               for name in ("signOf_zero", "signOf_one")]
    check("seed control recognizes both declaration ownership failures",
          study.control_outcome("F02", "seed", {"status": "refused", "reasons": reasons}, None))
    check("seed control does not mistake unrelated refusal for its intended defect",
          not study.control_outcome("F02", "seed", {"status": "refused", "reasons": ["protected source changed"]}, None))
    check("seed control requires both declared ownership defects",
          not study.control_outcome("F02", "seed", {"status": "refused", "reasons": reasons[:1]}, None))


def control_exit_status():
    """A shell supervisor must distinguish passed controls from a blocked study."""
    for command, outcome, expected in (("controls", False, 2), ("controls", True, 0),
                                       ("run", 2, 2), ("run", 0, 0)):
        script = "\n".join([
            "import contextlib, pathlib, sys",
            "import study",
            "study.load=lambda root: ({},None,None,None)",
            "study.admission_lock=lambda root: contextlib.nullcontext()",
            "study.verify_sources=lambda manifest: None",
            "study." + ("controls" if command == "controls" else "run") + "=lambda *args: " + repr(outcome),
            "sys.argv=['study.py'," + repr(command) + ",'.']",
            "raise SystemExit(study.main())",
        ])
        result = subprocess.run([sys.executable, "-B", "-c", script], cwd=Path(__file__).parent,
                                capture_output=True, timeout=10)
        check(command + " CLI exit status for outcome=" + str(outcome), result.returncode == expected)


def expected_budget_stop():
    """A configured admission stop produces a reason and no exception-shaped failure."""
    manifest = {"id": "budget-test", "slots": [{"id": "first"}, {"id": "next"}],
                "execution": {"observed_token_limit": 150000}}
    with tempfile.TemporaryDirectory(prefix="ftqc-admission-") as temporary:
        Store, _, _ = study.kernel_imports(Path(__file__).resolve().parents[3] / "ontolkernel")
        store = Store(str(Path(temporary) / "records"))
        study.event(store, manifest["id"], "controls_end", passed=True)
        study.event(store, manifest["id"], "trial_start", slot="first")
        study.event(store, manifest["id"], "trial_end", slot="first", result={
            "execution": "candidate", "assessment": "accepted", "tokens": 352438, "cost_usd": None})
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = study.run(Path(temporary), manifest, store, None, None)
        events = store.entries()
        check("token admission stop does not launch another worker or raise a traceback", code == 2
              and json.loads(output.getvalue())["reason"] == "observed token admission limit reached"
              and events[-1]["kind"] == "stage" and events[-1]["name"] == "stopped"
              and sum(row["kind"] == "trial_start" for row in events) == 1)


def main():
    prompt_information()
    recorded_accounting(declared_slots())
    chosen = study.selected_slots(2, "F01:B:1")
    check("explicit run two selection admits only the requested slot", len(chosen) == 1 and
          (chosen[0]["task"], chosen[0]["condition"], chosen[0]["repetition"]) == ("F01", "B", 1))
    check("default still declares the full suite", len(study.selected_slots(2)) == 12)
    for invalid in ("F03:A:1", "F01:D:1", "F01:B:0", "F01:B:3", "F01:B:1:extra"):
        try:
            study.selected_slots(2, invalid)
        except ValueError:
            check("invalid or undeclared selection refused: " + invalid, True)
        else:
            raise AssertionError("invalid selection admitted: " + invalid)
    runtime_grants()
    private_build_seeding()
    cached_verification()
    cache_tree_changes()
    cache_audit_race()
    control_failure_reason()
    control_exit_status()
    expected_budget_stop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

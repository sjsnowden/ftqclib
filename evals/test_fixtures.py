"""Goal: task seeds isolate reviewed edits and source admission rejects altered obligations and escapes.

Method: exact pinned Git source, real disposable projections, positive/defective source controls, closure and
receipt-bound checks. No Lean/Lake execution or synthetic compiler-success claim occurs in this test.
"""
import json
from pathlib import Path
import tempfile

import fixtures
import runtime


def source_cases(files):
    for task in ("F01", "F02"):
        positives = ("reference", "alternate", "seed") if task == "F01" else ("reference", "alternate")
        for label in positives:
            candidate = fixtures.overlay(task, files, label)
            assert fixtures.admission(task, files, candidate) == [], (task, label)
        negative = (("weakened-statement", "changed-definition", "added-axiom") if task == "F01" else
                    ("module-deletion", "omitted-import"))
        for label in negative:
            assert fixtures.admission(task, files, fixtures.overlay(task, files, label)), (task, label)
        changed = dict(files)
        changed["README.md"] += b"\nprotected input change\n"
        assert fixtures.admission(task, files, changed)
        assert fixtures.admitted_window(task, b"by\n  sorry\nnamespace Injected")
        assert fixtures.admitted_window(task, b"by\n  native_decide")
        assert fixtures.admitted_window(task, b"by\n  sorry\n#eval IO.println 1")
        for command in (b"open Lean", b"variable (extra : False)", b"local notation X => True",
                        b"scoped notation X => True", b"universe injected", b"builtin_initialize IO.Process.exit 0",
                        b"elab_rules : tactic | early => return ()", b"run_elab IO.Process.exit 0"):
            assert fixtures.admitted_window(task, b"by\n  sorry\n" + command)
            assert fixtures.admitted_window(task, b"by\n  sorry\n  " + command)
        assert fixtures.admitted_window(task, b"by\n  /- theorem ignored /- nested -/ -/\n  sorry") is None
    f01 = fixtures.overlay("F01", files, "seed")[fixtures.Z_SHEAR]
    prefix, proof, suffix = fixtures.f01_window(f01)
    original_prefix, _, original_suffix = fixtures.f01_window(files[fixtures.Z_SHEAR])
    assert prefix == original_prefix and suffix == original_suffix
    assert proof == fixtures.with_eol(b"by\n  sorry", f01)
    f02 = fixtures.overlay("F02", files, "seed")
    assert fixtures.with_eol(fixtures.SIGNS, f02[fixtures.PAIRING]) not in f02[fixtures.PAIRING]
    assert fixtures.with_eol(fixtures.SIGNS, f02[fixtures.RESIDUAL]) in f02[fixtures.RESIDUAL]
    assert fixtures.with_eol(fixtures.SIGN_ALTERNATE, f02[fixtures.AMPLITUDE]) in f02[fixtures.AMPLITUDE]


def ownership_cases(files):
    seed = fixtures.overlay("F02", files, "seed")
    assert all(reason.startswith("F02 declaration home:") for reason in fixtures.admission("F02", files, seed))
    windows = fixtures.f02_windows(files)
    duplicate = dict(files)
    prefix, _, suffix = windows[fixtures.AMPLITUDE]
    duplicate[fixtures.AMPLITUDE] = prefix + fixtures.with_eol(fixtures.SIGN_ALTERNATE, prefix) + suffix
    assert fixtures.admission("F02", files, duplicate)
    missing = dict(files)
    prefix, _, suffix = windows[fixtures.PAIRING]
    zero_only = fixtures.SIGNS.split("/-- `signOf 1".encode())[0]
    missing[fixtures.PAIRING] = prefix + fixtures.with_eol(zero_only, prefix) + suffix
    assert any("signOf_one" in reason for reason in fixtures.admission("F02", files, missing))
    comment = b'/- theorem signOf_one : signOf 1 = -1 := by sorry -/\n'
    missing[fixtures.PAIRING] = prefix + fixtures.with_eol(zero_only + comment, prefix) + suffix
    assert any("signOf_one" in reason for reason in fixtures.admission("F02", files, missing))
    positive = dict(files)
    # Keep the amplitude suffix: the comment is neither a declaration nor an ownership site.
    amplitude_prefix, _, amplitude_suffix = windows[fixtures.AMPLITUDE]
    positive[fixtures.AMPLITUDE] = amplitude_prefix + fixtures.with_eol(comment, amplitude_prefix) + amplitude_suffix
    assert fixtures.admission("F02", files, positive) == []
    assert "signOf_one" not in fixtures.code_without_comments('"theorem signOf_one"')


def simp_cases(files):
    # The previously accepted F01 repair ended in this unstable tactic, with its actual local helper.
    unstable = fixtures.overlay("F01", files, "unstable-simp")
    _, proof, _ = fixtures.f01_window(unstable[fixtures.Z_SHEAR])
    prior = ("by\n  ext i\n  · rfl\n  · simp only [zShearBy_Z, zShearBy_X, Pi.add_apply]\n"
             "    have h2 : (2 : ZMod 2) = 0 := by decide\n    ring_nf\n    simp [h2]").encode()
    assert proof == fixtures.with_eol(prior, unstable[fixtures.Z_SHEAR])
    reasons = fixtures.admission("F01", files, unstable)
    assert reasons and all("simp stability:" in reason for reason in reasons), reasons
    for task in ("F01", "F02"):
        for tactic in ("simp", "simpa", "simp_all", "dsimp"):
            for modifier in ("", "?", "!", "?!"):
                head = tactic + modifier
                for tail in ("", " [h2]", " at h", " (config := { zeta := false }) only [h2]",
                             " (discharger := assumption) only [h2]"):
                    why = fixtures.admitted_window(task, ("by\n  " + head + tail).encode())
                    assert why and why.startswith("simp stability:"), (task, head, tail, why)
                for tail in (" only", " only [h2]", " only [h2] at *", " only [h2] using h2",
                             "/- gap /- nested simp -/ -/only [h2]", " -- simp\n    only [h2]"):
                    why = fixtures.admitted_window(task, ("by\n  " + head + tail).encode())
                    assert why is None, (task, head, tail, why)
            assert fixtures.admitted_window(task, ("by\n  " + tactic + "/- gap -/at h").encode())
        for body in ("exact simpLemma", "exact simp_result", "exact simp'", "exact simp'x'", "exact αsimp",
                     "exact simpα", "exact simp℀", "exact simpₐ", "exact simp?Lemma", "exact simpa!Lemma",
                     "exact simp_all?Lemma",
                     "exact Module.simp", "exact Module.simpa", "exact «simp»", "exact «Name».simp",
                     'exact "simp [h2] \\\" simp_all \\\""', "/- simp /- simpa -/ simp_all -/\n  rfl"):
            why = fixtures.admitted_window(task, ("by\n  " + body).encode())
            assert why is None, (body, why)
    text = 'simp/- nested /- inner -/\ncomment -/only "simp"'
    masked = fixtures.code_without_comments(text)
    assert len(masked) == len(text) and masked.count("\n") == text.count("\n")
    assert fixtures.simp_stability(masked) is None
    # A comment can separate tokens but cannot split an identifier into the keyword `only`.
    assert fixtures.admitted_window("F01", b"by\n  simp on/- gap -/ly [h2]")
    assert fixtures.admitted_window("F01", b"by\n  simp (config := { singlePass := true }) only [h2]")
    assert fixtures.admitted_window("F01", b"by\n  simp (discharger := simp) only [h2]")
    assert fixtures.admitted_window("F01", b"by\n  simp (discharger := simp only [h2]) [h2]")
    characters = b'''by
  let a : Char := '"'
  have h : (0 : Nat) = 0 := by simp
  let b : Char := '"'
  exact h'''
    assert fixtures.admitted_window("F01", characters).startswith("simp stability:")
    assert fixtures.admitted_window("F01", characters.replace(b"by simp", b"by simp only")) is None
    assert fixtures.admitted_window("F01", b"by\n  let a : Char := '\\\"'\n  simp [h2]").startswith("simp stability:")
    for prefix in (b"s!", b"m!", b"f!", b"println! ", b"Macro.trace[foo] "):
        interpolation = b'by\n  have _ := ' + prefix + b'"{(show Nat from by simp)}"\n  rfl'
        assert fixtures.admitted_window("F01", interpolation).startswith("simp stability:")
    assert fixtures.admitted_window("F01", b'by\n  have _ := s!/- gap -/"hi"\n  rfl')
    escaped = 'by\n  let «a"» := 0\n  have h : (0 : Nat) = 0 := by simp\n  let «b"» := 0\n  exact h'.encode()
    assert fixtures.admitted_window("F01", escaped).startswith("simp stability:")
    assert fixtures.admitted_window("F01", escaped.replace(b"by simp", b"by simp only")) is None
    for identifier in ('«a/-"»', '«a--"»', '«a"»'):
        assert fixtures.code_without_comments(identifier) == identifier
    for literal in ('s!"{value}"', 'm!"{value}"', '"arbitrary {brace} text"'):
        assert fixtures.code_without_comments(literal)
        assert fixtures.admitted_window("F01", ("by\n  have _ := " + literal + "\n  rfl").encode())
    module = ('import Init\n\ndef text (value : Nat) : String := s!"{value}"\n'
              'def braces : String := "arbitrary {brace} text"\n').encode()
    assert runtime.import_graph({"Fixture.lean": module}) == {"Fixture": ["Init"]}


def closure_cases(files):
    graph = runtime.import_graph(files)
    assert fixtures.PAIRING[:-5].replace("/", ".") in graph
    for task in ("F01", "F02"):
        modules = fixtures.dependent_modules(task, files)
        declared = [check["command"][-1][:-5].replace("/", ".")
                    for check in fixtures.task_spec(task)["checks"] if check["id"] != "examiner"]
        assert modules == declared
        assert set(modules).issubset(set(fixtures.excluded_modules(task, files)))
        contract = fixtures.task_spec(task)
        assert {"purpose", "obligation", "evidence", "acceptance", "completion", "writes", "checks"} <= contract.keys()
        for check in fixtures.check_commands(task):
            assert "{examiner}" not in check["command"]
    assert "FTQCLib.Carrier.HadamardElimination" in fixtures.dependent_modules("F02", files)
    assert "FTQCLib.Stabilizer.ZShear" in fixtures.excluded_modules("F01", files)


def projection_cases():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        for task in ("F01", "F02"):
            baseline, candidate = root / (task + "-reference"), root / (task + "-seed")
            reference = fixtures.prepare(task, fixtures.ROOT, baseline, control="reference")
            prepared = fixtures.prepare(task, fixtures.ROOT, candidate,
                                        control="seed" if task == "F01" else "alternate")
            assert reference["status"] == "prepared", reference
            assert prepared["status"] == "prepared", prepared
            assert prepared["formal"] == "unverified"
            assert not (candidate / ".git").exists()
            assert not (candidate / ".lake").exists()
            assert not (candidate / "evals").exists()
            assert not list(candidate.rglob("CLAUDE.md"))
            assert not list(candidate.rglob("AGENTS.md"))
            result = fixtures.assess(task, baseline, candidate)
            assert result["status"] == "needs-checks" and not result["accepted"]
            assert result["source_sha256"] == prepared["source_sha256"]
            check = fixtures.check_commands(task)[0]
            receipt = {check["id"]: {"source_sha256": result["source_sha256"], "command": check["command"],
                                     "status": "finished", "returncode": 1}}
            assert fixtures.assess(task, baseline, candidate, compiler_results=receipt)["status"] == "failed"
            receipt[check["id"]]["source_sha256"] = "stale"
            assert fixtures.assess(task, baseline, candidate, compiler_results=receipt)["status"] == "needs-checks"
            assert fixtures.prepare(task, fixtures.ROOT, candidate)["status"] == "refused"


def check():
    files = fixtures.tracked_files(fixtures.ROOT)
    source_cases(files)
    ownership_cases(files)
    simp_cases(files)
    closure_cases(files)
    projection_cases()
    print("F01/F02 source controls, canonical projections, affected closures and receipt gates passed; Lean unverified")


if __name__ == "__main__":
    check()

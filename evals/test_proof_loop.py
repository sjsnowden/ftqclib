"""Goal: malformed proposals cannot acquire effects, and evidence excludes the solution.

Method: adversarial protocol values and exact source-boundary properties; no models,
network, compiler or shell chosen by a worker.
"""
import json
from pathlib import Path

import fixtures
import proof_loop


def check(name, condition):
    assert condition, name
    print("ok: " + name, flush=True)


def request(**changes):
    value = {"action": "check_candidate", "proof": "by\n  rfl",
             "query": None, "reason": None}
    return json.dumps({**value, **changes})


def parse(raw, searches=1):
    return proof_loop.action(raw, searches_left=searches)


def protocol():
    check("declared proof operation admitted", parse(request())[1] is None)
    bad = [request(action="bash"), request(action=[]), request(action={}), request(action=None),
           request(baseline="b" * 64), request(command="git diff"), request(proof=123),
           request(proof="\ud800"), request(proof="x" * (proof_loop.PROOF_BYTES_MAX + 1)),
           request(proof="by\n  rfl\x00"), request(query="git diff"), "[]", "null", "{", "[" * 2000,
           request().replace('"action":', '"action":"search","action":')]
    check("unknown operations, worker-selected baseline and malformed JSON all refuse",
          all(parse(raw)[0] is None for raw in bad))
    search = request(action="search", proof=None, query="ZMod, _ + _ = 0")
    check("search grant and budget enforced before dispatch", parse(search, 0)[0] is None and parse(search)[1] is None)
    blocked = request(action="blocked", proof=None, reason="missing declaration")
    check("blocked is a distinct outcome", parse(blocked)[0]["action"] == "blocked")


def boundaries():
    root = fixtures.ROOT
    source = (root / fixtures.Z_SHEAR).read_bytes()
    prefix, _, suffix = fixtures.f01_window(source)
    secret = b"by\n  exact NEVER_EXPOSE_THIS_REFERENCE_PROOF"
    seed = prefix + secret + suffix
    files = {fixtures.Z_SHEAR: seed,
             "FTQCLib/Pauli/Basic.lean": (root / "FTQCLib/Pauli/Basic.lean").read_bytes()}
    context = proof_loop.evidence(files, fixtures.task_spec("F01"))
    encoded = json.dumps(context)
    check("evidence excludes target proof and later consumers", "NEVER_EXPOSE" not in encoded
          and "zShearByEquiv" not in encoded and "Examiner.lean" not in encoded)
    check("evidence contains exact target context", "zShearBy_zShearBy" in encoded and "@[ext]" in encoded
          and context["source_sha256"] == fixtures.sha256(seed))
    for proof in ("by\n  rfl", "by\n  simp only [zShearBy_X]"):
        proposed, error = proof_loop.candidate_source(seed, proof)
        check("proof splice preserves every protected byte: " + proof, error is None and
              proposed == prefix + fixtures.with_eol(proof.encode(), seed) + suffix)
    for proof in ("by\ntheorem stolen : True := by trivial", "by\n  simp", "by\n  run_tac pure ()"):
        check("declarations, unstable simp and execution escape refuse", proof_loop.candidate_source(seed, proof)[0] is None)
    original = proof_loop.packet(context, search_enabled=False, latest={"proof": "LATEST"})
    check("packet has only supplied latest context", original["latest"] == {"proof": "LATEST"}
          and original["capabilities"] == ["check_candidate", "blocked"])


def accounting():
    fields = {"input_tokens": 10, "cache_read_input_tokens": 20, "cache_creation_input_tokens": 0, "output_tokens": 3}
    check("usage is disjoint across all rounds", sum(proof_loop.usage_sum([fields, fields]).values()) == 66)
    check("missing usage remains unknown", proof_loop.usage_sum([fields, None]) is None)
    check("bad usage remains unknown", proof_loop.usage_sum([{**fields, "input_tokens": True}]) is None)
    bounded = proof_loop.bounded_text("Ω" * 4000)
    check("diagnostics have UTF-8 byte bounds and explicit truncation",
          bounded["truncated"] and len(bounded["text"].encode()) <= proof_loop.DIAGNOSTIC_BYTES_MAX)


if __name__ == "__main__":
    protocol()
    boundaries()
    accounting()

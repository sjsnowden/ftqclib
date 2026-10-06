# Pinned runtime admission

The proof-chain driver supports two explicit modes. Existing manifests retain
strict byte auditing and full metadata rescans. New studies can name an
**owner-maintained runtime pin**. In that mode the owner promises to preserve the
named compiler and retrieval trees; workers and checkers receive read-only mounts.
This is a prototype trust assumption, not filesystem-enforced immutability.

Publication records the repository revision, retrieval snapshot identity, compiler
manifest identities and runtime root identities. Study startup verifies those
identity records. Per-invocation checks inspect only the named roots, without
enumerating their contents. Replacing a root is refused. Interior owner writes
violate the assumption and are not detected by the cheap check. Publish a new
runtime version when its contents change. Root identities may need republishing
after moving installations or changing filesystems.

## Commands

Run these in WSL from this worktree. Paths are explicit; commands do not select the
terminal's current study or alter a running owner.

```sh
python3 -B evals/runtime_pin.py publish \
  --manifest /path/to/prior-study/manifest.json \
  --assume-owner-pinned --output /path/to/runtime-pin.json

# A separate, expensive byte audit; produces a new fact and never rewrites the pin.
python3 -B evals/runtime_pin.py audit /path/to/runtime-pin.json \
  --output /path/to/runtime-audit.json

# Add to the usual chain_study.py prepare arguments:
--runtime-pin /path/to/runtime-pin.json

# Optional: reuse complete controls from the same checking contract.
--controls-from /path/to/prior-study
```

The admitted pin is copied into the study's immutable store and bound by its
manifest. Changing the external publication file cannot replace that admitted
object. Omitting `--runtime-pin` preserves strict mode. There is no automatic
downgrade from a rejected pin to an unchecked runtime.

## Control certificates

Passing controls produce a content-addressed certificate. Its contract binds the
compiler, snapshot, owner-pin identity, repository revision, complete statement
scope, control source and checking implementation. Model settings, prompt wording
and retrieval hints do not affect it. Preparation can import a matching completed
certificate and its retained result/diagnostic objects with `--controls-from`.
Changed contracts or older studies without certificates cause the controls to run;
corrupt certificates and incomplete evidence are refused.

The first run of a changed checker still executes its controls. Each control emits
its name to the existing terminal stage line. Reusing controls records an explicit
reuse event. This cache never accepts a worker proof: candidate compilation,
exact-type checking and transitive-axiom examination remain mandatory.

In pinned mode the private dependency projection hard-links the baseline files
instead of copying their bytes. The checker sees this projection read-only; new
artifacts go into a separate writable build directory. Cross-filesystem links fall
back to ordinary copies. Strict mode keeps its previous copying behavior.

## Measurements and validation

On 2026-10-06, admission on the actual decoder runtime took **0.263, 0.317 and
0.312 seconds**, with **zero directory scans**. One thousand repeated checks took
0.0146 seconds, also without scans. Publication took 0.218 seconds. The checks read
identity records rather than the 8 GB runtime payload. Measurements used the
existing OS cache; the earlier 64.993-second full-audit observation had different
cache conditions and is not a controlled speedup benchmark.

A real disposable continuation also exercised the `prepare` command, complete
`load` path (including source-pin validation), and native recovery of four accepted
proofs. Its load took **0.381 seconds**. It executed no controls, models or compiler
calls and did not modify the live study. The parent workspace retains the receipt
in `outputs/evals/ftqclib/runtime-pin-integration-01.json`.

The parent workspace retains `work/benchmark_pinned_runtime.py` and
`outputs/evals/ftqclib/runtime-pin-benchmark-01.json`. Tests are
`test_runtime_pin.py` and `test_control_cache.py`, plus the existing proof-protocol,
runner, kernel and continuation controls. They check root replacement, altered
pins, explicit interior-mutation assumptions, full-audit detection, zero scans,
cache invalidation and complete receipt scope without model or Lean invocations.

The running decoder-chain-04 stays on its original pinned source. These changes
belong to the separate `codex/pinned-runtime` worktree; activating them requires a
new study manifest, not editing the running study.

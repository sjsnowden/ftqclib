# F01/F02 development fixtures

Owner code and protected examiners for source revision
`75589c95949b6d290c53405e0cdc31334120e19a`. These are retained-proof reconstruction and
historical integration development fixtures, not held-out mathematical-performance evidence.

`fixtures.prepare(task, source, destination, control="seed")` exports exact tracked Git blob bytes
into a fresh neutral directory, then applies the reviewed overlay. Windows checkout CRLF is not
used as the canonical source encoding. Preparation requires the pinned revision and a clean tracked
checkout; a Windows worktree pointer is translated explicitly when called from WSL. `.git`, `.lake`,
`.scratch`, `evals`, every `CLAUDE.md` and every `AGENTS.md` are excluded. The public JSON contracts
flatten the applicable Lean requirements once for all prompt conditions. No private examiner,
reference proof, Git history or original target artifact is a worker input.

Preparation returns `status`, `task`, `control`, `source_revision`, `source_sha256`, `destination`,
`contract`, `checks`, `examiner_sha256`, `excluded_modules`, and `formal: "unverified"`. A failure
reports its read/write phase and never reports a ready workspace. A write failure may leave a
partial directory for the owner to inspect; it cannot be reused by another preparation.

F01 controls are `seed`, `reference`, `alternate`, `unfinished`, `weakened-statement`,
`changed-definition`, `added-axiom`, and `unstable-simp`. Only the proof term of `zShearBy_zShearBy` is granted.
Both its statement and the next top-level declaration are protected by exact source boundaries.
The alternate uses the same finite arithmetic fact through a different final tactic sequence.
The unauthorized-axiom control makes the target depend on an injected axiom; it also violates the
source boundary. The unfinished seed is admitted as a source proposal, but is never accepted
without an axiom-clean protected compiler examination.
The unstable-simp control reproduces the first model's formally valid proof ending in `simp [h2]`;
source admission must reject it for its missing explicit `only`, independently of compiler success.

F02 controls are `seed`, `reference`, `alternate`, `module-deletion`, and `omitted-import`.
The seed reverses only the sign lemma consolidation from `6710bd1` in the real relocated
`Carrier/CharSumPairing`, `Carrier/ResidualBit`, and `Carrier/HadamardAmplitudeCheck` modules.
It removes the shared sign lemmas and restores their historical local copies. Pinned Lean 4.29.1 can
merge agreeing theorem declarations from different modules; a successful combined import therefore
does not prove single ownership. Source admission and the protected raw imported-module audit enforce
one shared declaration site for both sign lemmas. Reference
restores the pinned arrangement; alternate changes the shared `signOf_one` proof to its historical
explicit conditional proof. Existing imports, the `signOf` definition and every consumer remain
protected. Only the three sign insertion/removal windows are granted.

`fixtures.assess(task, baseline, candidate, compiler_results=None)` requires an **original reference
projection** as baseline, not the failing F02 seed. It compares the closed captured source tree and
the reviewed edit windows. A conservative nested-comment/string-aware token scan rejects declaration
escapes and trust shortcuts; it is an admission restriction, not a substitute for Lean parsing.
Absent compiler receipts return `needs-checks`, `accepted: false`, `formal: "unverified"`.

`fixtures.check_commands(task)` gives exact commands for owner receipts. The parent creates output
directories and supplies the recorded Lean executable/options/environment. `.scratch/build` must
come first in `LEAN_PATH`; verified unaffected ancestor artifacts may follow. `excluded_modules`
contains all local descendants that could carry original declarations and must be excluded from
worker caches, not only the acceptance scope. All affected intermediates on the acceptance path
must rebuild: F02 has twelve source modules before the composed examiner. Never reuse cached
intermediates importing the original shared sign definitions. Worker-produced `.olean` files are
not acceptance evidence. The owner checker starts with clean private writable output.

Compiler receipts map each check ID to `{source_sha256, command, status, returncode}`. `command`
must equal `check_commands(task)` including the owner absolute examiner path; `status` must be
`finished` and the exit code zero. The caller owns execution, source capture and receipt attribution.
Missing, stale, timed-out or failed checks never pass. The protected examiners check declaration kind,
expected type, transitive conventional axioms and named consumers. F01 additionally compiles the
existing `ZShearCheck` rows. F02 imports both real consumers into one environment and checks their
preserved names. Their own source is excluded from the proposal and supplied only after capture.

Model-free source tests: `python3 evals/test_fixtures.py`. They do not run Lean/Lake and do not
fabricate compiler-success evidence. The owner centrally runs compiler controls sequentially before
any paid trial. No fixture is called formally validated from these Python tests alone.

## Compact proof workflow (2026-10-06)

`proof_study.py` compares two F01 workflow arms: A supplies compact local declarations;
B adds one shared, retained Loogle prefetch and at most two worker-requested follow-up
searches. These A/B labels are scoped to `proof-proposals-v2`, not the earlier prompt
presentation experiment. Version 2 moves baseline identity binding entirely into
the owner request; the model does not copy or select an identity. Three repetitions
run sequentially in alternating arm order.
The existing full-agent run 2 is a historical baseline with one observation.

`proof_loop.py` derives the protocol and packet. The model returns one JSON proposal
whose owner request is bound to immutable study/slot/round/evidence; it has no tools or writable source workspace.
Only the owner can dispatch the declared search/check effects. It splices a bounded
proof into the protected statement, executes the existing compiler/consumer/examiner
checks, records receipts, and commits accepted source in the trial's private worktree.
The next model call gets the same small evidence packet and latest candidate/public
diagnostic, without the accumulated operational transcript. Private examiner output
never enters repair context. Repeated identical candidates reuse the recorded check
within the same frozen trial. Model calls, searches and byte sizes are bounded;
unknown usage, failed execution or unfinished owner checks stop further admissions.

OntolKernel's `proposal_agent.py` uses the same signed-in Codex executable and exact
model/effort, with replacement instructions and a frozen tool-capability catalog.
Before every live call it runs that CLI against a local synthetic Responses service:
the actual request must have no tools and exactly the explicitly supplied text.
Synthetic transport observations are marked and excluded from inference usage.
Unrecognized settings, remaining tools, context additions or changed bindings refuse
the live call. This is a measured restricted CLI adapter, not a direct bare-model API.

`loogle.py` performs fixed-origin bounded HTTP in the owner. The public service's
current corpus has no pinned-version guarantee; its names/types are advisory until
our pinned Lean checks succeed. Full raw responses, hashes and service metadata are
kept outside model context. The initial query and shared response are recorded once.
No complete MathBones bank is required for this pilot.

Model-free tests: `test_proof_loop.py`, `test_loogle.py`, and OntolKernel's
`tests/proposal_agent.py`. Existing seven F01 compiler controls must also pass.
`proof_comparison.py` reports all trials and usage, acceptance, per-accepted-result
tokens and percentage changes. These observations compare bundled workflows on one
development fixture; they do not establish broad quality equivalence or isolate
Loogle's causal contribution from sampling variation.

The completed six-trial development-10 comparison used gpt-5.6-luna medium. Compact
local evidence accepted 2/3 trials at 9,770 mean tokens (14,655 tokens per accepted
result including the failed attempt). Compact + Loogle accepted 3/3 at 2,678.33 mean
tokens, versus 372,816 for the single historical full-agent run. All 18 proposals
made zero tool calls; all accepted proofs passed the same source and Lean checks.
The Loogle mean was 99.28% lower, with 93.79% less uncached input. These are F01
development observations, not a broad quality claim. The entire study used 37,345
reported tokens. A preserved v1 pilot used another 23,327, including an identity-copy
failure that motivated owner-only identity binding. The exported comparison and
complete provenance live in `outputs/evals/ftqclib/compact-comparison/` in the parent workspace.

# Running the ftqclib development comparison

The implementation lives in the `evals/prompt-comparison` development worktree. The original ftqclib
checkout supplies the pinned commit and is not a worker workspace. This pack has two development tasks,
three prompt conditions and two repetitions: twelve outer worker invocations, with no automatic quality
retry. It is separate from the proposed general 72-invocation suite.

Linux/WSL is required for the process, filesystem and network boundaries. The Python tools use the standard
library. `bubblewrap`, `prlimit`, Git and the pinned Linux Lean 4.29.1 runtime must be available. The setup
tool uses Python 3.14's zstd support to extract the official release after checking its published SHA-256.

## Preparation and execution

Set `SOURCE`, `KERNEL`, `RUNTIME` and `STUDY` to explicit Linux paths. `SOURCE` is the pinned ftqclib checkout;
`KERNEL` is the modified OntolKernel checkout. New study and runtime destinations must be owned by the caller.
Run from the ftqclib development worktree:

```bash
python3 evals/setup_runtime.py "$RUNTIME" --source "$SOURCE"
python3 evals/build_reference.py "$RUNTIME" "$KERNEL" cache-complete
python3 evals/build_reference.py "$RUNTIME" "$KERNEL" reference
python3 -B evals/test_fixtures.py
python3 -B evals/test_study.py
python3 -B evals/study.py prepare --source "$SOURCE" --study "$STUDY" \
  --kernel "$KERNEL" --runtime "$RUNTIME" --id ftqclib-development \
  --provider codex --executable /absolute/path/to/codex \
  --model gpt-5.6-luna --effort medium --deadline-seconds 300 --token-limit 150000
python3 -B evals/study.py controls "$STUDY"
python3 -B evals/study.py run "$STUDY"
python3 -B evals/study.py report "$STUDY"
```

To run one explicitly requested trial, add `--slot F01:B:1` to `prepare` (task, prompt condition,
repetition). The resulting immutable study contains exactly that slot and prepares controls for its task;
it does not silently retry or carry over another study's accepted result. Keep the previous study as evidence.
Use a fresh native Linux study directory for WSL runs, for example under
`/home/sam/ftqclib-eval-runtime/studies/`, and export reports to Windows afterward. This avoids repeated
cross-filesystem metadata operations in worker capture and protected checking.

Preparation and controls make no model calls. `run` is the inference command. It refuses admission before
controls pass, when recorded implementation bytes change, after unclosed or unresolved work, or once the
observed-token admission threshold is reached. The threshold is soft: one in-flight worker can overshoot it.
Missing usage is unknown and stops further admissions. Codex dollar cost remains unknown. To use Anthropic,
select `--provider claude`, its executable, an explicit supported model/effort, and `--budget-usd` for each
worker. Unsupported provider settings fail; no alternate model is silently selected.

The token threshold counts cached input as well as uncached input and output. It is checked between whole
CLI worker invocations; it cannot interrupt a worker at an exact token count. A configured admission stop
returns a structured reason and nonzero status, without an exception traceback. An explicitly selected
single trial ends normally once that trial is closed; its complete measured usage is still reported.

Lake prepares the reference and dependencies. Each trial then runs the declared Lean source graph directly,
with two threads and a 4096 MiB Lean allocation limit, using audited read-only dependencies and fresh private
outputs. Both prompt conditions and final checks use the same toolchain/options. The checker adds its own
protected declaration, type, axiom and consumer examinations. These are not worker inputs.

## What is retained and what is displayed

Each slot gets its own worktree from an owner-held seed commit and a Git-free worker projection. Candidate
bytes, supplied prompt, provider streams, usage, checker receipts and assessments are retained outside the
worker's authority. The parent checkpoints finished admitted candidates, marking their assessment outcome.
Unknown or rejected work is never called accepted merely because a Git commit exists.

```bash
python3 "$KERNEL/kernel/trace_tree.py" --study "$STUDY" --watch
```

For overnight viewing, add `--deadline-minutes 0` to remain open until quit. Positive values retain a finite
observation deadline and print an explicit expiry message. The task's interactive launcher
`work/launch_ftqclib_viewer.sh` uses indefinite viewing, retains stderr and exit diagnostics, and keeps an
unexpected exit visible. The observer's lifetime does not control the study runner.

The Ontologic terminal displays the controls gate branching to the twelve declared trials, with recorded
worker/check/checkpoint stages and an event pane. Failed controls prominently block admission; they are not
reported as failed model trials. Model, effort and known/unknown usage remain visible. `G` selects the graph;
`E` selects recorded events. Its `ONTOLOGIC>` prompt accepts `status`, `trials`, `show SLOT`, `usage`, `help`, and
`quit`. It is an observer; these commands do not start work or change the study. A stopped viewer does not stop
the runner. This concrete study graph does not fabricate native Kernel ISA entries or inter-trial dependencies.

The preparation window can follow an owner-controlled `current-study` symlink. Switching that pointer changes
the observed run without modifying either run's evidence.

## Limits of the first pack

Prompt A is a constructed baseline with the same accessible public contract. B places the contract explicitly
in the prompt; C preserves its operative text while removing headings and blank lines. C is only modestly
shorter; this comparison must measure outcomes and total usage, not assume shorter instructions win.

Compiler success and source admission are separate. The lexical edit restrictions are conservative admission
rules, not a complete Lean parser or a proof of safety against arbitrary hostile elaboration code. The checker
is confined, has independent code and rebuilds captured source; no worker-produced `.olean` is used as final
evidence. Controls validate the intended defects before model trials.

Source admission now enforces explicit `only` on direct `simp`, `simpa`, `simp_all` and `dsimp` uses in the
editable windows. Comments and strings preserve token separation and cannot supply a fake `only` token.
The supported subset permits whitespace/comments and `?`/`!` modifiers before `only`, then ordinary
lemma lists, locations and `using` terms. Config/discharger prefixes before `only` are conservatively refused;
interpolated/brace-bearing strings are refused so embedded proof code cannot be mistaken for string data.
Characters and escaped identifiers preserve their lexical boundaries. This is a bounded source-admission
subset, not a full Lean parser. The `unstable-simp` F01 negative control
reproduces the prior submitted proof and must fail for the `simp stability:` reason before model admission.

Address-space limits are per process, file-size limits per file, and NPROC per real UID. They are not aggregate
trial memory/disk quotas. Trials and compiler checks run sequentially. Only the named local scope is built;
`FTQCLibHeavy`, the whole-repository combined import, paper fidelity and held-out validation are later stages.

Runtime verification may reuse a byte audit only within the same owner process after rescanning complete file
metadata. Changes trigger a fresh audit and refusal. This assumes the owner controls the runtime directories;
it is not a defense against a hostile local operating system. No verification cache persists between commands.

Lean resolves each package from one search root. Before rebuilding local modules, the public helper and owner
checker copy exactly the audited unaffected local ancestors into their respective private build roots; excluded
target artifacts remain absent. These copies do not share mutable inodes with the read-only cache.

F02 checks declaration ownership independently of successful imports. The pinned Lean version can merge equal
theorems declared in different modules, so compilation alone cannot establish the single shared declaration
site required by this task. Source admission and the protected imported-module audit both enforce that site.

Failed controls and unresolved execution return a nonzero CLI status. A shell supervisor can stop or notify on
that status. The terminal observes durable events; automatic delivery back into the assistant chat is not yet
implemented and should not be inferred from a displayed queue or a running viewer.

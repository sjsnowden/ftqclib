# Scripted proof effects

The proof driver now uses OntolKernel's existing message, wait_reply,
message_delivery, message_reply, issue, control and plan_activate instructions.
There is no second scheduler. A blocked worker with a declared handler suspends
without a mathematical verdict. Its handler receives a fresh compact packet;
the reply becomes an explicit input to a new proof invocation. Only the protected
Lean checker can establish acceptance. All causal references point backward to
existing immutable records: the apparent loop remains a DAG.

## Functions and the ISA

`proof-program.json` is an example declaration for the nine-node decoder study.
Pass it to `chain_study.py prepare --program PATH` alongside the existing prepare
arguments. Preparation freezes the program, named routes, model/effort, evidence,
and budgets in the manifest. Use a new study version when changing the program.

Declare up to eight functions. Names such as `assess_prerequisite`,
`evaluate_request` or `propose_adaptation` are script-level bindings to the same
compact invocation operation; they are not new ISA opcodes. Each has an explicit
purpose, model, effort and list of exact Lean declaration names. `on_blocked`
binds each proof to one function in advance. Workers cannot invent destinations,
executables or capabilities. There is no nested messaging from an answer worker.

The interface resembles typed Rust functions over a small instruction set, but
this prototype is Python plus validated JSON, not a Rust compiler or RISC-V VM.
Its answer value is:

```json
{"status":"evidence","body":"bounded explanation","declarations":["Exact.name"]}
```

The other tags are `prerequisite`, `adaptation`, and `needs_operator`. These are
advice, not automatic authority to create a theorem or change a plan. The next
proof invocation receives the tagged value and may use its bounded retrieval
operations. The caller's exact obligation, accepted predecessor interfaces and declaration evidence
are supplied to the answer function. Populate evidence for the actual problem;
an empty evidence list does not establish that a lemma is absent.

## Budgets, records and recovery

Proofs and answers use one shell-free model adapter. Every actual invocation has
a proposal_start/proposal_end pair, retained prompt/result and validated usage.
The program's max_model_calls counts both roles, including calls inside a proof
attempt. The study token threshold applies to both. Unknown or unfinished usage
stops new admission. A per-proof message limit bounds repeated questions.

The answer is retained with its manifest and delivery identity before closing
the native delivery. Recovery can finish that closure without another model
call. An open delivery with no unique durable result is refused as ambiguous.
Answering never retires the answer endpoint or accepts a proof.

## Operator messages and versioned future plans

Use the same native control transport from another POSIX shell:

```bash
python3 evals/proof_control.py "$STUDY" status
python3 evals/proof_control.py "$STUDY" message T01.7 'Examine the distinction between these distance definitions.'
python3 evals/proof_control.py "$STUDY" plan submit /absolute/path/next-plan.json
python3 evals/proof_control.py "$STUDY" plan activate VERSION --from CURRENT_VERSION
python3 evals/proof_control.py "$STUDY" receipt REQUEST_ID
```

Submission is not admission. Only the running owner admits requests and records
receipts. A message arriving during an invocation follows the native correction
rule: the candidate is not carried forward; a new invocation receives the
operator inbox. The command process does not acquire the long-running study
execution lock or write the kernel log. Finished runs reject new submissions.

Future plan versions may change evidence (`proof_evidence`, arrays of name
components), model/effort, title and scheduling. The native ISA refuses changes
to already bound work. The proof host additionally preserves all declared
identities, output destinations, dependencies, checker contract and function
definitions. New mathematical obligations or dependencies require a new study
manifest and controls; unrestricted graph synthesis is not implemented.

The study graph records waiting-for-reply instead of a spurious dependency
failure. The existing study observer remains read-only; use the command above
or the native kernel control terminal for submissions. Prior studies and their
pinned implementations are not upgraded in place.

## Validation

`test_proof_program.py` exercises actual native decisions with finite injected
model/checker responses: exchange, replay, shared budget, recovery, operator
inboxes and plan protection. Those tests make no Lean or paid-model claims.
Existing kernel messaging/control and proof-driver tests cover the unchanged
paths. A live proof study remains a separate execution with explicit budgets.

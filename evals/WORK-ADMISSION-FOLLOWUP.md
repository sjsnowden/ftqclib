# Admit and execute proposed prerequisites before resuming proof work

The proof driver records a supporting-obligation proposal but does not admit or execute it as a new task. It returns the proposal as a prerequisite reply, allowing the original worker to resume without the supporting proof. This spends calls without resolving the dependency.

This is an implementation gap in the proof adapter, not a fundamental restriction of the immutable DAG design. The current plan validator deliberately permits only predeclared theorem definitions and dependencies; new definitions require a new versioned study manifest and controls.

## Evidence and implementation baseline

- ftqclib commit `63edabd`: retained proof work state and bounded recovery.
- OntolKernel commit `fab0484`: domain-neutral immutable work state and recovery routing.
- `evals/proof_resolver.py`, `dispatch`: records `extension_proposed`, then returns a `prerequisite` reply. No admission or child execution follows.
- `evals/proof_program.py`, `plan_nodes`: rejects new theorem definitions and mathematical dependencies in a mid-run plan.
- Local study `decoder-chain-07`, T01.7: the resolver proposed a distance lemma; two further parent calls ran without its proof. Seven calls consumed 34,512 reported tokens overall, with no candidate checks and no new proof. Eight previously accepted nodes were inherited.
- Proposal object: `d372f20f4c17ac08a04d8ddce5b1e690aaf7efc68bffbda45b4d88650cb3aa28`.

Recording a proposal is not admission, execution, or evidence that its proposition holds. The existing recovery work implements proposal handling and continuity, not the complete dynamic-prerequisite mechanism.

## Required behavior

1. Record a proposed prerequisite and suspend the dependent continuation. Do not treat the proposal as ordinary advice that immediately resumes the parent.
2. Require a trusted admission decision bound to the exact proposal, contract, authority, allowed effects, and budget. The proposing worker cannot grant itself authority. Support explicit rejection and operator intervention.
3. Compile an admitted extension into a new immutable program version, with a child contract, acceptance gate, and dependency on its accepted output. Preserve the original theorem obligation and completed work. A new versioned study manifest is a valid initial implementation; do not bypass the existing plan guard by mutating a manifest.
4. Execute the child through the normal bounded worker and checker machinery. For Lean, check the actual supporting proof, type, and permitted axioms before making it available to the parent.
5. Resume a new parent invocation only when its required accepted artifact exists. Preserve the prior evidence and history; bind the new invocation and checks to the new inputs.
6. Record child failure, rejection, timeout, and budget exhaustion explicitly. Do not turn an unproved proposal into an assumption or an automatic retry loop.

Keep proposal, admission, dependency, and continuation semantics generic. Lean propositions, proof artifacts, and checking rules belong in the domain adapter. Models return typed requests; the deterministic controller performs effects. An explicitly trusted model may evaluate admission under a configured policy, with its decision recorded.

The history remains a DAG: proposal -> admission -> program version -> child invocation -> accepted artifact -> parent continuation. There is no backward edge or mutation of historical records.

## Acceptance tests

- Scripted integration: blocked parent -> proposal -> suspension -> trusted admission -> child proof check -> parent continuation and proof check.
- No parent invocation while admission or a required accepted child artifact is absent.
- Unauthorized admission, rejection, invalid child proof, timeout, and exhausted budgets cannot unblock the parent.
- Admission binds the exact proposal and program version; stale or duplicate decisions cannot create duplicate tasks.
- Original obligations and previously accepted nodes remain unchanged; immutable records replay to the same state.
- Generic admission/dependency tests use a non-Lean instance as well as the Lean adapter.
- After mechanical tests pass, run one bounded live comparison. Report newly checked work and incremental usage; do not claim token savings from proposal recording alone.

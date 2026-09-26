# Module LN — Lean 4

For repositories written in Lean 4 against Mathlib: proofs meant to be read and reused, certificates meant to be
trusted, and Lean code that runs as a program. What the standard's requirements mean in Lean, and Lean's own rules,
with the reasons. A binding that names this module pins the Mathlib revision it follows, says which of these rules it
checks, and keeps its own repository-specific rules (targets, staging of inherited code) in its own clauses.

## Why these rules

Mathlib is about a million theorems that change every month and are increasingly written by machines and read by
people. Names are the index by which anything is found; general statements are what can be reused; consistent normal
forms are what let automation work; robust proofs are the ones that survive next month's release. A convention
followed locally is a search that fails globally. The kernel checks that a proof is a proof; it does not check that
the statement says what was meant, that the axioms are the expected three, or that the proof will still elaborate
after an upgrade. Those are the reader's, and these rules are for them.

The defaults to resist, because they are what an agent writes unprompted: a long tactic script where a lemma was due;
a statement fitted to today's caller; a private definition that duplicates Mathlib's; a limit raised to make it pass;
a linter switched off. Each is cheap now and paid for at every release.

## Requirements

**LN.1 Mathlib is the standard.** Naming, docstring structure, hypotheses, `simp` discipline and the linter set are
Mathlib's, without local variation. Where this module is silent, read the relevant Mathlib source at the pinned
revision before inventing a convention; memory of Mathlib is not Mathlib.
> *Means* — Mathlib's conventions as found in its source at the revision the binding pins. *Governs* — semantics.
> *CALM* — not applicable. *Checked by* — `weak.linter.mathlibStandardSet = true` in the lakefile; the rest is advice.
> *Brief* — Lean follows Mathlib in naming, docstrings, hypotheses and simp discipline; when unsure, read Mathlib's
> source at the pinned revision, not memory.

**LN.2 The statement before the proof.** A theorem's statement and a lemma's hypotheses are reviewed like code,
before and apart from the proof. State every result at the weakest hypotheses its statement needs (`Finite` where
`Nat.card` is used, not `Fintype`) and supply the stronger instance inside the proof. A wrong statement costs more than
a wrong proof, because the kernel will accept a proof of it.
> *Means* — 4.4, 4.5: meaning is in the statement, and the statement is what a reader checks. *Governs* — semantics,
> verification. *CALM* — not applicable. *Checked by* — `linter.unusedFintypeInType`, `linter.unusedSectionVars`;
> review. *Brief* — Review the statement apart from its proof; state it at the weakest hypotheses it needs and supply
> the stronger instance inside the proof.

**LN.3 What is trusted is named.** Every headline result carries `#guard_msgs in #print axioms` with its axiom list
written out; only `propext`, `Classical.choice` and `Quot.sound` appear, and `sorryAx` never. `implemented_by`,
`extern`, `native_decide` and `partial` are trusted code, not proof: each use on a certificate's path is named with its
reason, and `partial` does not appear on one at all.
> *Means* — 3.34, the trusted computing base: Lean's axioms and its escapes from the kernel. *Governs* —
> verification. *CALM* — not applicable. *Checked by* — the axiom sweep fails the build. *Brief* — Every headline
> result has a build-failing axiom sweep listing only `propext`, `Classical.choice`, `Quot.sound`; anything opaque to
> the kernel is named with its reason and kept off a certificate's path.

**LN.4 Proofs that survive the next release.** `simp only [...]` where a proof must stay stable; bare `simp`,
`decide` and `omega` only where they have been seen to run at the scale used; `maxHeartbeats` and `maxRecDepth`
raised only with an adjacent comment saying why, and only after the slow step has been extracted into its own lemma.
> *Means* — 10.7, a limit is a choice that names its measurement; robustness against Mathlib's monthly change.
> *Governs* — verification. *CALM* — not applicable. *Checked by* — review; a raised limit without a comment is a
> finding. *Brief* — `simp only` where stability matters, `decide` only where seen to run, no raised limit without a
> written reason and an extracted lemma.

**LN.5 Homes and names.** A definition lives in the lowest layer that can state it, never in the layer that first
needed it; everything about one object lives in one module; a module's docstring has Mathlib's sections (`Main
definitions`, `Main results`, and `Implementation notes` where a non-obvious choice was made); a theorem's name reads
the statement's head symbols in order.
> *Means* — 11.2, one word one meaning, applied to declarations; 11.3. *Governs* — semantics. *CALM* — not
> applicable. *Checked by* — advice; a new module without the docstring sections is a review finding. *Brief* — A
> definition's home is the lowest layer that can state it; one module per object; Mathlib's docstring sections; names
> that read the statement.

**LN.6 Instances by parameter.** Where the carrier is a standard construction (units, subtypes, quotients,
products), take the instance as a hypothesis with a compatibility equation rather than declaring one that may collide
with Mathlib's. An instance that must be declared is `scoped`, with the collision it avoids written in
`Implementation notes`.
> *Means* — 6.1, one writer per piece of state, read for instances: two instances of one class on one type are two
> writers of one fact. *Governs* — semantics. *CALM* — not applicable. *Checked by* — review. *Brief* — Prefer a
> parameter with a compatibility equation to a new instance; declare one only `scoped`, with the collision written
> down.

**LN.7 Linters are not disabled.** No `set_option linter.* false` at file scope. A linter firing means the code is
wrong in the way it names, and the fix is the code: `omit [Inst] in`, wrapping at 100 characters, `Finite` for
`Fintype`. A per-declaration `set_option … in` carries an adjacent reason.
> *Means* — 13.0: a check switched off is a check that does not exist. *Governs* — verification. *CALM* — not
> applicable. *Checked by* — the linters under `lake build`; a search for file-scope disables. *Brief* — Never disable
> a linter at file scope; fix the code it names; a per-declaration exception carries its reason.

**LN.8 A check module per module.** Each `Foo.lean` has a `FooCheck.lean` holding: the axiom sweep (LN.3); at least
one agreement row, the same fact reached by an independent route; discriminating rows, instances a weaker statement
could not accept; kernel rows where the fact is decidable at the scale used, and a note where it is not. Mutation is
aimed, not sprayed: at vacuous statements and decorative hypotheses, never at a proof the kernel accepted, and always
beside an unmutated control.
> *Means* — 4.5 and 13.6: every claim names how a breach would be seen, and every check is shown able to fail.
> *Governs* — verification. *CALM* — a missing check module is a finding only over the closed set of topic modules the
> binding lists. *Checked by* — the check modules fail the build. *Brief* — Every topic module has a check module:
> axiom sweep, an agreement row, discriminating rows, kernel rows or a note; mutation aimed and controlled.

**LN.9 Lean as a program.** Code that runs, not only elaborates, keeps the standard's program rules: effects in `IO`
at the edge and a pure core (`BaseIO` cannot throw; `EIO ε` says what can); outcomes in `Except`, never `panic!`,
which returns a default and carries on unless `LEAN_ABORT_ON_PANIC` is set; names taken from the kernel's `Name`
components as they are, never re-parsed from pretty-printed text; `partial` nowhere a result is relied on.
> *Means* — 5.1, 5.2, 9.1 and 9.4 read in Lean. *Governs* — effect, semantics. *CALM* — not applicable. *Checked by* —
> review; a `panic!` in code that runs is a finding. *Brief* — In Lean that runs: effects at the edge in `IO`, outcomes
> in `Except` never `panic!`, names as `Name` components never re-parsed text, no `partial` where a result is relied on.

<!-- brief: Lean -->
Mathlib's conventions at the pinned revision; the statement reviewed apart from its proof, at the weakest hypotheses;
a build-failing axiom sweep; `simp only`, no unexplained raised limits; no linter disabled at file scope; a check
module beside every module; in running code, `Except` not `panic!`.
<!-- /brief -->

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.LetterSoundness
import FTQCLib.Hilbert.ConditionSoundness

/-!
# Soundness of every branch: the frame's referee is the Hilbert semantics

T20 (`docs/TARGETS.md`): by induction on T14's terms, T18 for the word letters and T19 for the
conditioning letters, the Hilbert image of `interpretAmp p ψ` is `⟦p⟧` applied to the image of `ψ`;
so the branch at an outcome string `o`, the interpretation evaluated at `o`, is `K_o` applied to
the image of the input. As corrected on 2026-10-02 (`docs/STEPS.md`, entry 2026-10-02l), this is a
theorem against T17's `⟦p⟧` for **every** protocol, not a run along an outcome string.

**The frame-to-Hilbert identification.** The frame's referee `Protocol.interpretAmp p`
(`Carrier/Protocol.lean`) acts on amplitude functions `(Fin n → ZMod 2) → ℂ`. T17's semantics
`hilbertSem p`, written `⟦p⟧` (`Hilbert/ProtocolSemantics.lean`), is a linear map
`QubitSpace n →ₗ[ℂ] QubitSpace (n + k)`, and `QubitSpace n` is the abbreviation
`(Fin n → ZMod 2) → ℂ` (`Hilbert/QubitSpace.lean`). So the identification is the identity on
functions: the Hilbert image of an amplitude function `ψ` is `ψ` itself, and of a carrier state `S`
it is `amp S`, as in T18 and T19 (`Hilbert/LetterSoundness.lean`,
`Hilbert/ConditionSoundness.lean`). No `toQState` is needed, since the statements here are
equalities of functions and not of norms.

**Every protocol.** `interpretAmp_eq_hilbertSem` is stated with no hypothesis on the protocol: the
induction goes through T18's `runAmp_eq_wordGate` and T19's `pauliProjection_eq_bornProjection`,
neither of which has a hypothesis (`docs/fidelity/T20.md`, the first point). In particular a word
appended after `k` conditioning letters is a `GateWord (n + k) m`, whose letters may name any bit of
`Fin (n + k)`, outcome bits included: an H on an outcome bit, a CNOT targeting one, a diagonal
exponent reading one. Such words are cases of the statement, not exceptions to it. T17's row `H1`
is one: conditioning on `Z₀`, then H on its outcome bit, gives `K_o = Z^o/√2`, which is no product
of a projector and a unitary (`docs/fidelity/T20.md`, Claim 10; the row is T20.2's).

**The branch is the evaluation at `o`.** T14's `Protocol.branch p S o` is
`w ↦ amp (interpret p S) (Fin.append w o)`, the interpretation of a carrier state evaluated at the
outcome string. T17's `kraus p o` is the matrix of `(I ⊗ ⟨o|) ⟦p⟧`, and `kraus_mulVec` says that
`K_o ψ` is `⟦p⟧ ψ` evaluated at `o`. So `branch_eq_kraus` is `interpretAmp_eq_hilbertSem` evaluated
at `o`, after T14's `amp_interpret` has replaced `amp (interpret p S)` by `interpretAmp p (amp S)`;
its hypotheses `IsCarrier S` and `S.m = m` are `amp_interpret`'s own (`docs/fidelity/T20.md`, the
second point), and the image of the input is `amp S`.

**The product form.** Where every outcome bit is used only as a control, T17's predicate
`OutcomeControlsOnly p` (which also forbids an X or a Z of a conditioning Pauli on an outcome bit),
T17's `kraus_eq_prod_of_controlsOnly` turns `K_o` into `krausProduct p o`, and the branch is that
product applied to the image of the input (`branch_eq_krausProduct`). This is a corollary of
`branch_eq_kraus`, proved here by composition.

## Main results

* `interpretAmp_eq_hilbertSem` — for every protocol `p`, `interpretAmp p` is `⟦p⟧` as functions on
  `QubitSpace n` (proved at T20.3).
* `branch_eq_kraus` — on a carrier state at the protocol's precision, the branch at `o` is
  `kraus p o` applied to the input's amplitude (proved at T20.3).
* `branch_eq_krausProduct` — under `OutcomeControlsOnly p`, the branch at `o` is T17's product
  form applied to the input's amplitude.

## Implementation notes

* The conditioning case of the induction is an index computation (`docs/fidelity/T20.md`, the
  fourth point): `interpretAmp` reads the new outcome at `Fin.last (n + k)` and the rest by
  `Fin.init`, `conditionIsometry` at `Fin.natAdd (n + k)` against the one-bit string and by
  `Fin.castAdd 1`; the sum over `b` keeps one term.
* No `-- source:` citation: T20's section names no corpus papers. The Kraus operator read off an
  isometry and applied to the input is Knill and Laflamme's `A_a = ⟨μ_a| U |e⟩`
  (`docs/fidelity/T20.md`, Claim 6).

## References

* E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, arXiv:quant-ph/9604034:
  operators of an evolution read off an isometry, applied to the system's state.
* V. Danos, E. Kashefi and P. Panangaden, *The measurement calculus*, arXiv:quant-ph/0412135: the
  branches of a pattern; here an outcome is a free bit (decision D2), so a word may act on it.
-/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Frame.Walkthrough
open scoped Matrix

variable {m n : ℕ}

/-- The conditioning isometry at a word `v` of `N + 1` bits is the Born projector at the outcome
`v (Fin.last N)`, evaluated at `Fin.init v`: of the sum over `b`, only the term `b = v (Fin.last N)`
is nonzero. Restated from T17's private `conditionIsometry_append`, in the indexing of
`interpretAmp`. -/
private theorem conditionIsometry_apply_last {N : ℕ} (P : SignedPauli N) (φ : QubitSpace N)
    (v : Fin (N + 1) → ZMod 2) :
    conditionIsometry P φ v = bornProjection P (v (Fin.last N)) φ (Fin.init v) := by
  have hnat : Fin.natAdd N (0 : Fin 1) = Fin.last N := Fin.ext rfl
  rw [conditionIsometry, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply,
    Finset.sum_eq_single (v (Fin.last N))]
  · rw [LinearMap.comp_apply, appendOutcome, LinearMap.coe_mk, AddHom.coe_mk, if_pos]
    · rfl
    · funext i
      rw [Subsingleton.elim i 0, Function.comp_apply, hnat]
  · intro b _ hb
    rw [LinearMap.comp_apply, appendOutcome, LinearMap.coe_mk, AddHom.coe_mk, if_neg]
    intro h
    apply hb
    rw [← hnat]
    exact (congrFun h 0).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The frame's referee is the Hilbert semantics.** For every protocol `p`, words on outcome bits
included, the frame's referee `interpretAmp p` is T17's `⟦p⟧ = hilbertSem p`, as functions
`QubitSpace n → QubitSpace (n + k)`: the Hilbert image of `interpretAmp p ψ` is `⟦p⟧` applied to
the image of `ψ`, the identification being the identity on amplitude functions. -/
theorem interpretAmp_eq_hilbertSem {k : ℕ} (p : Protocol m n k) :
    p.interpretAmp = ⇑(hilbertSem p) := by
  induction p with
  | nil => rfl
  | word p w ih =>
    funext f
    rw [Protocol.interpretAmp_word, hilbertSem_word, LinearMap.comp_apply, ih,
      runAmp_eq_wordGate]
  | condition p P hP ih =>
    funext f
    rw [Protocol.interpretAmp_condition, hilbertSem_condition, LinearMap.comp_apply, ih]
    funext v
    rw [pauliProjection_eq_bornProjection, conditionIsometry_apply_last]

/-- **The branch at `o` is `K_o` applied to the input.** On a carrier state `S` at the protocol's
precision, the branch at the outcome string `o`, the interpretation evaluated at `o`, is T17's
Kraus operator `kraus p o = (I ⊗ ⟨o|) ⟦p⟧` applied to the image `amp S` of the input. -/
theorem branch_eq_kraus {k : ℕ} (p : Protocol m n k) {S : KernelSumState n} (hS : IsCarrier S)
    (hm : S.m = m) (o : Fin k → ZMod 2) :
    p.branch S o = kraus p o *ᵥ amp S := by
  rw [kraus_mulVec, ← interpretAmp_eq_hilbertSem, ← (amp_interpret p hS hm).2]
  rfl

/-- **The product form of a branch.** Where every outcome bit is used only as a control
(`OutcomeControlsOnly p`), the branch at `o` of a carrier state at the protocol's precision is
T17's product form `krausProduct p o` applied to the input's amplitude: the Born projectors of the
conditioning letters' data parts at their outcomes and the unitaries the words give at `o`, in term
order. -/
theorem branch_eq_krausProduct {k : ℕ} (p : Protocol m n k) (hp : OutcomeControlsOnly p)
    {S : KernelSumState n} (hS : IsCarrier S) (hm : S.m = m) (o : Fin k → ZMod 2) :
    p.branch S o = krausProduct p o *ᵥ amp S := by
  rw [branch_eq_kraus p hS hm o, kraus_eq_prod_of_controlsOnly p hp o]

end FTQCLib.Hilbert

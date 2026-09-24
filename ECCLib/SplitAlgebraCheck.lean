/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.SplitAlgebra
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Checks for the splitting theorem

Axiom sweeps, and the discriminating row that `IsAlgClosed` is not removable.

The row is `K = ℝ`, `A = ℂ`. Here `A` is a reduced, finite-dimensional, commutative `K`-algebra —
every hypothesis of `card_maximalSpectrum_eq_finrank` except algebraic closure of the base — and
the conclusion **fails**: `ℂ` is a field, so it has exactly one maximal ideal, while its dimension
over `ℝ` is two. That is why the theory is phrased over an algebraically closed base, and why an
`ℝ` base cannot work.

Note what this row does *not* say. It does not say `ℂ` is forced — any algebraically closed base
works, and `AlgebraicClosure ℚ` is one with no analysis in its import closure. `ℂ` is chosen here
because the consumer is a complex matrix algebra.
-/

namespace ECCLib

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.splitAlgEquivOfBijectiveResidue' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitAlgEquivOfBijectiveResidue

/-- info: 'ECCLib.splitAlgEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitAlgEquiv

/-- info: 'ECCLib.card_maximalSpectrum_eq_finrank' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_maximalSpectrum_eq_finrank

/-- info: 'ECCLib.completeOrthogonalIdempotents_primitiveIdempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.completeOrthogonalIdempotents_primitiveIdempotent

/-- info: 'ECCLib.primitiveIdempotent_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.primitiveIdempotent_ne_zero

/-- info: 'ECCLib.isReduced_of_splitEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.isReduced_of_splitEquiv

/-- info: 'ECCLib.moduleFinite_of_splitEquiv' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.moduleFinite_of_splitEquiv

/-! ## Discriminating row — `IsAlgClosed` is not removable

`ℂ` as an `ℝ`-algebra satisfies every other hypothesis and breaks the conclusion. -/

/-- `ℂ` is a field, so it has exactly one maximal ideal. -/
theorem card_maximalSpectrum_complex : Nat.card (MaximalSpectrum ℂ) = 1 := by
  have : Subsingleton (MaximalSpectrum ℂ) :=
    ⟨fun I J => MaximalSpectrum.ext (by
      rw [(Ideal.eq_bot_of_prime I.asIdeal), (Ideal.eq_bot_of_prime J.asIdeal)])⟩
  have : Nonempty (MaximalSpectrum ℂ) := ⟨⟨⊥, Ideal.bot_isMaximal⟩⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩

/-- ...but its dimension over `ℝ` is two. -/
theorem finrank_real_complex_eq_two : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

/-- **Therefore the conclusion of `card_maximalSpectrum_eq_finrank` is false over a base that is
not algebraically closed.** Every other hypothesis holds for `ℝ ≤ ℂ`: `ℂ` is a commutative,
reduced, finite-dimensional `ℝ`-algebra. -/
theorem isAlgClosed_not_removable :
    Nat.card (MaximalSpectrum ℂ) ≠ Module.finrank ℝ ℂ := by
  rw [card_maximalSpectrum_complex, finrank_real_complex_eq_two]
  norm_num

/-- The other hypotheses really do hold in that counterexample, so it is the algebraic closure
of the base that fails and nothing else. -/
example : IsReduced ℂ := inferInstance

example : Module.Finite ℝ ℂ := inferInstance

/-! ## The character layer -/

/-- info: 'ECCLib.algHom_ext_of_ker_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.algHom_ext_of_ker_eq

/-- info: 'ECCLib.splitChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitChar

/-- info: 'ECCLib.splitChar_apply' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitChar_apply

/-- info: 'ECCLib.splitChar_primitiveIdempotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitChar_primitiveIdempotent

/-- info: 'ECCLib.mul_primitiveIdempotent' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.mul_primitiveIdempotent

/-- info: 'ECCLib.sum_splitChar_smul_primitiveIdempotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_splitChar_smul_primitiveIdempotent

/-- info: 'ECCLib.splitChar_injective' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitChar_injective

/-- info: 'ECCLib.splitChar_surjective' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.splitChar_surjective

/-- info: 'ECCLib.equivAlgHom' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.equivAlgHom

/-- info: 'ECCLib.equivAlgHom_apply' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.equivAlgHom_apply

/-- info: 'ECCLib.exists_equiv_primitiveIdempotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.exists_equiv_primitiveIdempotent

/-- info: 'ECCLib.isIdempotentElem_primitiveIdempotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.isIdempotentElem_primitiveIdempotent

/-- info: 'ECCLib.exists_equiv_splitChar_of_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.exists_equiv_splitChar_of_injective

/-! ## Non-vacuity of the uniqueness theorem

The primitive family itself satisfies every hypothesis, so the theorem's instance space is
inhabited. This is the trivial instantiation; the substantive consumer is the identification of
`Scheme/TranslationSpectrum.lean`. -/

example {K A : Type*} [Field K] [CommRing A] [IsReduced A] [Algebra K A] [Module.Finite K A]
    [IsAlgClosed K] [Fintype (MaximalSpectrum A)] [DecidableEq (MaximalSpectrum A)] :
    ∃ σ : MaximalSpectrum A ≃ MaximalSpectrum A,
      ∀ I, primitiveIdempotent K A I = primitiveIdempotent K A (σ I) :=
  exists_equiv_primitiveIdempotent completeOrthogonalIdempotents_primitiveIdempotent
    primitiveIdempotent_ne_zero rfl

end ECCLib

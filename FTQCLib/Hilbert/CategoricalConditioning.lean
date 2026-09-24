/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CategoricalEquivalence
import FTQCLib.Hilbert.MeasurementCollapse

/-! # The scaled carrier and its generator-stability (conditioning)

Extending the maximal-subgroupoid equivalence (`CategoricalEquivalence.lean`) to conditioning
(selective Lüders) requires a **sub-normalized** carrier: `ludersChannel` maps a normalized
density to a `weight • (density)` with `weight ∈ {0, ½, 1}`. This file establishes the carrier
and the crux it rests on — that the two generator families (`qConj`, `ludersChannel`) preserve
it — reusing the Lüders ↔ conditioning correspondence
(`ludersChannel_stabProjector_self/_zero/_notMem`). The generated-monoid action category is
built here; the full equivalence is in `CategoricalConditioningEquiv.lean`. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Stabilizer

variable {n : ℕ}

/-- A **sub-normalized pure stabilizer density**: a complex multiple `c • Π_S` of a full-rank
stabilizer projector. The weight `c` records the cumulative measurement probability (`c = 0` is the
impossible outcome); the operational morphisms (`qConj`, `ludersChannel`) act within this cone. -/
def IsScaledStabDensity (A : QState n →ₗ[ℂ] QState n) : Prop :=
  ∃ (c : ℂ) (S : SignedStab n),
    IsStabilizer S.L ∧ Module.finrank (ZMod 2) S.L = n ∧ A = c • stabProjector S

/-- Every pure stabilizer density is sub-normalized (weight `1`). -/
theorem IsPureStabDensity.isScaled {A : QState n →ₗ[ℂ] QState n} (h : IsPureStabDensity A) :
    IsScaledStabDensity A := by
  obtain ⟨S, hS, hfull, rfl⟩ := h
  exact ⟨1, S, hS, hfull, (one_smul ℂ _).symm⟩

/-- **Clifford conjugation preserves the scaled cone** (weight unchanged). -/
theorem qConj_isScaledStabDensity {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    {A : QState n →ₗ[ℂ] QState n} (h : IsScaledStabDensity A) :
    IsScaledStabDensity (qConj U A) := by
  obtain ⟨c, S, hS, hfull, rfl⟩ := h
  refine ⟨c, cliffordAction hU S, cliffordAction_isStabilizer hU hS, ?_, ?_⟩
  · rw [cliffordAction_finrank]; exact hfull
  · rw [qConj_smul, qConj_stabProjector]

/-- **Selective Lüders preserves the scaled cone** (weight scaled by `0`, `½`, or `1`). The three
cases are the proven correspondence: `Q ∈ L` correct outcome (weight `1`), wrong outcome (weight
`0`), and `Q ∉ L` collapse (weight `½`, `L ↦ pauliCondition L Q`). -/
theorem ludersChannel_isScaledStabDensity {Q : Pauli n} {ε : ℂ} (hε : ε * ε = 1)
    {A : QState n →ₗ[ℂ] QState n} (h : IsScaledStabDensity A) :
    IsScaledStabDensity (ludersChannel Q ε A) := by
  obtain ⟨c, S, hS, hfull, rfl⟩ := h
  have hsmul : ludersChannel Q ε (c • stabProjector S)
      = c • ludersChannel Q ε (stabProjector S) := by
    rw [← ludersChannelₗ_apply, map_smul, ludersChannelₗ_apply]
  rw [hsmul]
  by_cases hQ : Q ∈ S.L
  · by_cases hεχ : ε = S.sign Q
    · refine ⟨c, S, hS, hfull, ?_⟩
      rw [hεχ, ludersChannel_stabProjector_self S hQ]
    · have hχ : S.sign Q * S.sign Q = 1 := sign_mul_self S hQ
      have hneg : ε = -S.sign Q := by
        have h0 : (ε - S.sign Q) * (ε + S.sign Q) = 0 := by linear_combination hε - hχ
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd (sub_eq_zero.mp h) hεχ
        · exact eq_neg_of_add_eq_zero_left h
      refine ⟨0, S, hS, hfull, ?_⟩
      rw [hneg, ludersChannel_stabProjector_zero S hQ, smul_zero, zero_smul]
  · obtain ⟨S', hS'L, hluders⟩ := ludersChannel_stabProjector_notMem S hS hfull hQ hε
    refine ⟨c * 2⁻¹, S', ?_, ?_, ?_⟩
    · rw [hS'L]; exact pauliCondition_isStabilizer hS Q
    · rw [hS'L]; exact pauliCondition_finrank hS hfull Q
    · rw [hluders, smul_smul]

/-! ## The generated operational monoid and its action on the scaled cone

`M := Submonoid.closure {qConjₗ U, ludersChannelₗ Q ε}` in the superoperator monoid; it acts on the
scaled cone by application (stability lifts through `closure_induction`). This is the `Monoid` +
`MulAction` substrate `𝒪` needs as an `ActionCategory` for the full (conditioning) equivalence. -/

/-- The operational generators as superoperators: Clifford conjugations and selective Lüders
(`ε² = 1`). -/
noncomputable def operationGens (n : ℕ) : Set (Module.End ℂ (QState n →ₗ[ℂ] QState n)) :=
  {T | (∃ U : cliffordSubgroup n, T = qConjₗ U.1)
    ∨ (∃ (Q : Pauli n) (ε : ℂ), ε * ε = 1 ∧ T = ludersChannelₗ Q ε)}

/-- The generated operational monoid (smallest submonoid of superoperators containing the
generators). -/
noncomputable def operationMonoid (n : ℕ) : Submonoid (Module.End ℂ (QState n →ₗ[ℂ] QState n)) :=
  Submonoid.closure (operationGens n)

/-- Each generator preserves the scaled cone (the two foundation lemmas). -/
theorem operationGens_isScaledStabDensity {T : Module.End ℂ (QState n →ₗ[ℂ] QState n)}
    (hT : T ∈ operationGens n) {A : QState n →ₗ[ℂ] QState n} (hA : IsScaledStabDensity A) :
    IsScaledStabDensity (T A) := by
  rcases hT with ⟨U, rfl⟩ | ⟨Q, ε, hε, rfl⟩
  · rw [qConjₗ_apply]; exact qConj_isScaledStabDensity U.2 hA
  · rw [ludersChannelₗ_apply]; exact ludersChannel_isScaledStabDensity hε hA

/-- **Every operation preserves the scaled cone.** Lifts generator-stability through the closure. -/
theorem operationMonoid_isScaledStabDensity {T : Module.End ℂ (QState n →ₗ[ℂ] QState n)}
    (hT : T ∈ operationMonoid n) :
    ∀ A : QState n →ₗ[ℂ] QState n, IsScaledStabDensity A → IsScaledStabDensity (T A) := by
  induction hT using Submonoid.closure_induction with
  | mem T hT => intro A hA; exact operationGens_isScaledStabDensity hT hA
  | one => intro A hA; exact hA
  | mul T T' _ _ ihT ihT' => intro A hA; exact ihT _ (ihT' _ hA)

/-- **The operational monoid acts on the scaled cone** — the `MulAction` substrate for the `𝒪`-side
`ActionCategory` of the full (conditioning) equivalence. -/
noncomputable instance :
    MulAction (operationMonoid n) {A : QState n →ₗ[ℂ] QState n // IsScaledStabDensity A} where
  smul T A := ⟨T.1 A.1, operationMonoid_isScaledStabDensity T.2 A.1 A.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

end FTQCLib.Hilbert

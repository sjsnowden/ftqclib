/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basis
import FTQCLib.Stabilizer.AmplitudeStabilizer

/-!
# Checks for the Hermitian Pauli action

The checks are targeted, one hypothesis or one convention each, all on one qubit with the amplitude
`δ₀` (`1` at the word `0`, `0` at the word `1`).

**The argument order of the composition law is load-bearing.** `betaFrame X Z = 1` and
`betaFrame Z X = 3` (kernel rows). Applying `X` and then `Z` to `δ₀` gives `−1` at the word `1`,
and so does `i^{betaFrame X Z}` times the action of `X + Z` — the law's order — while
`i^{betaFrame Z X}` times the same action gives `+1`: the swapped law is false on this witness.
The agreement pair reaches `−1` two ways, by composing the two actions and by the law's scalar.

**The stabilizer predicate is not vacuous.** The span of `Z` stabilizes `δ₀` (with sign `+1`); the
span of `X` does not, because `X` moves the support.

**The hypotheses of the rigidity theorem are load-bearing.** Without `f ≠ 0`: the spans of `X` and
of `Z` both have dimension `1 = n`, both stabilize the zero function, and differ. Without the
dimension hypotheses: the zero subspace and the span of `Z` both stabilize `δ₀` and differ.

**Agreement on the involution at odd `yWeight`.** `Y = X + Z` applied twice to `δ₀` returns `δ₀`,
computed directly at both words (the theorem `pauliAct_pauliAct` gives it for every `g`).

What no row here tests: the scalar group `±1` of `StabilizedBy` against a larger one; anything at
`n ≥ 2` (witnesses for CNOT and `restrict` are not included here). The action is `ℂ`-valued and noncomputable (`Complex.I`), so no amplitude row is
a kernel row — the absence is forced, not skipped; the kernel rows are the `ZMod 4` cocycle values
and the `Pauli 1` facts. -/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli Module

/-- The one-qubit amplitude `δ₀`: `1` at the word `0`, `0` at the word `1`. -/
noncomputable def delta0 : (Fin 1 → ZMod 2) → ℂ := fun w => if w 0 = 0 then 1 else 0

/-- `δ₀` at the word `0`. -/
theorem delta0_zero : delta0 ![0] = 1 := by
  simp [delta0]

/-- `δ₀` at the word `1`. -/
theorem delta0_one : delta0 ![1] = 0 := by
  simp [delta0]

/-- `δ₀` is not the zero function. -/
theorem delta0_ne_zero : delta0 ≠ 0 := by
  intro h
  have h0 := congrFun h ![0]
  rw [delta0_zero] at h0
  exact one_ne_zero h0

/-! ## Kernel rows: the cocycle values and the `Pauli 1` facts -/

/-- The cocycle value in the law's order: `betaFrame X Z = 1`. -/
theorem betaFrame_x_z : betaFrame (paulix 0 : Pauli 1) (pauliz 0) = 1 := by decide

/-- The cocycle value in the swapped order: `betaFrame Z X = 3`. -/
theorem betaFrame_z_x : betaFrame (pauliz 0 : Pauli 1) (paulix 0) = 3 := by decide

/-- `X` and `Z` are distinct nonzero Paulis on one qubit. -/
theorem paulix_ne_pauliz : (paulix 0 : Pauli 1) ≠ pauliz 0 := by decide

/-! ## The order of the composition law -/

/-- The action of `X + Z` on `δ₀` at the word `1` is `i`. -/
theorem pauliAct_y_delta0_one :
    pauliAct (paulix 0 + pauliz 0 : Pauli 1) delta0 ![1] = Complex.I := by
  have hyw : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have hsum : ![1] + (paulix 0 + pauliz 0 : Pauli 1).X = ![0] := by decide
  have hz : zDot (paulix 0 + pauliz 0 : Pauli 1) ![0] = 0 := by decide
  simp only [pauliAct, hyw, hsum, hz, delta0_zero, pow_one, pow_zero, mul_one]

/-- **Agreement, first way.** Applying `X` and then `Z` to `δ₀` gives `−1` at the word `1`. -/
theorem compose_x_then_z :
    pauliAct (pauliz 0 : Pauli 1) (pauliAct (paulix 0) delta0) ![1] = -1 := by
  have hywZ : yWeight (pauliz 0 : Pauli 1) = 0 := by decide
  have hywX : yWeight (paulix 0 : Pauli 1) = 0 := by decide
  have hzZ : zDot (pauliz 0 : Pauli 1) (![1] + (pauliz 0 : Pauli 1).X) = 1 := by decide
  have hsum : ![1] + (pauliz 0 : Pauli 1).X + (paulix 0 : Pauli 1).X = ![0] := by decide
  have hzX : zDot (paulix 0 : Pauli 1) ![0] = 0 := by decide
  simp only [pauliAct, hywZ, hywX, hzZ, hsum, hzX, delta0_zero, pow_zero, pow_one, one_mul,
    mul_one]

/-- **Agreement, second way.** The law's scalar `i^{betaFrame X Z}` times the action of `X + Z`
gives the same `−1`. -/
theorem law_order_agrees :
    Complex.I ^ (betaFrame (paulix 0 : Pauli 1) (pauliz 0)).val
      * pauliAct (paulix 0 + pauliz 0 : Pauli 1) delta0 ![1] = -1 := by
  have h1 : ((1 : ZMod 4)).val = 1 := by decide
  rw [betaFrame_x_z, pauliAct_y_delta0_one, h1, pow_one, Complex.I_mul_I]

/-- **Discriminating row.** With the swapped order `betaFrame Z X` the law gives `+1`, not `−1`:
the swapped law is false on this witness. -/
theorem swapped_order_fails :
    Complex.I ^ (betaFrame (pauliz 0 : Pauli 1) (paulix 0)).val
      * pauliAct (paulix 0 + pauliz 0 : Pauli 1) delta0 ![1] = 1 := by
  have h3 : ((3 : ZMod 4)).val = 3 := by decide
  rw [betaFrame_z_x, pauliAct_y_delta0_one, h3, ← pow_succ]
  exact Complex.I_pow_four

/-- The two orders disagree: the composition law cannot hold in both. -/
theorem orders_disagree :
    Complex.I ^ (betaFrame (paulix 0 : Pauli 1) (pauliz 0)).val
        * pauliAct (paulix 0 + pauliz 0 : Pauli 1) delta0 ![1]
      ≠ Complex.I ^ (betaFrame (pauliz 0 : Pauli 1) (paulix 0)).val
        * pauliAct (paulix 0 + pauliz 0 : Pauli 1) delta0 ![1] := by
  rw [law_order_agrees, swapped_order_fails]
  norm_num

/-! ## The stabilizer predicate is not vacuous -/

/-- `zDot` against `Z` on one qubit reads the word. -/
theorem zDot_pauliz (w : Fin 1 → ZMod 2) : zDot (pauliz 0 : Pauli 1) w = (w 0).val := by
  have h1 : ((1 : ZMod 2)).val = 1 := by decide
  simp [zDot, pauliz, h1]

/-- The span of `Z` stabilizes `δ₀`, with sign `+1`. -/
theorem stabilizedBy_span_z :
    StabilizedBy (Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)}) delta0 := by
  intro g hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · exact ⟨0, by simp⟩
  · refine ⟨0, ?_⟩
    funext w
    have hyw : yWeight (pauliz 0 : Pauli 1) = 0 := by decide
    have hX : (pauliz 0 : Pauli 1).X = 0 := rfl
    simp only [one_smul, pauliAct, hyw, hX, add_zero, zDot_pauliz, pow_zero, one_mul,
      ZMod.val_zero]
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h1
    · simp [h0]
    · simp [delta0, h1]

/-- The span of `X` does not stabilize `δ₀`: `X` moves the support. -/
theorem not_stabilizedBy_span_x :
    ¬ StabilizedBy (Submodule.span (ZMod 2) {(paulix 0 : Pauli 1)}) delta0 := by
  intro h
  obtain ⟨s, hs⟩ := h (paulix 0) (Submodule.mem_span_singleton_self _)
  have h0 := congrFun hs ![0]
  have hyw : yWeight (paulix 0 : Pauli 1) = 0 := by decide
  have hsum : ![0] + (paulix 0 : Pauli 1).X = ![1] := by decide
  have hz : zDot (paulix 0 : Pauli 1) ![1] = 0 := by decide
  simp only [pauliAct, hyw, hsum, hz, delta0_one, delta0_zero, pow_zero, one_mul, mul_one] at h0
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h0.symm

/-! ## The hypotheses of the rigidity theorem are load-bearing -/

/-- The spans of `X` and of `Z` differ. -/
theorem span_x_ne_span_z :
    Submodule.span (ZMod 2) {(paulix 0 : Pauli 1)}
      ≠ Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)} := by
  intro h
  have hmem : (paulix 0 : Pauli 1) ∈ Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)} :=
    h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · exact absurd ha (by decide)
  · exact absurd ha (by decide)

/-- **`f ≠ 0` is load-bearing.** Both spans have dimension `1 = n`, both stabilize the zero
function, and they differ: dropping `f ≠ 0` from `eq_of_stabilizedBy_of_stabilizedBy` would make
it false. -/
theorem hf_load_bearing :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {(paulix 0 : Pauli 1)}) = 1
      ∧ finrank (ZMod 2) (Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)}) = 1
      ∧ StabilizedBy (Submodule.span (ZMod 2) {(paulix 0 : Pauli 1)})
          (0 : (Fin 1 → ZMod 2) → ℂ)
      ∧ StabilizedBy (Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)})
          (0 : (Fin 1 → ZMod 2) → ℂ)
      ∧ Submodule.span (ZMod 2) {(paulix 0 : Pauli 1)}
          ≠ Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)} :=
  ⟨finrank_span_singleton (by decide), finrank_span_singleton (by decide),
    stabilizedBy_zero _, stabilizedBy_zero _, span_x_ne_span_z⟩

/-- The zero subspace differs from the span of `Z`. -/
theorem bot_ne_span_z :
    (⊥ : Submodule (ZMod 2) (Pauli 1)) ≠ Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)} := by
  intro h
  have hmem : (pauliz 0 : Pauli 1) ∈ (⊥ : Submodule (ZMod 2) (Pauli 1)) :=
    h ▸ Submodule.mem_span_singleton_self _
  rw [Submodule.mem_bot] at hmem
  exact absurd hmem (by decide)

/-- **The dimension hypotheses are load-bearing.** The zero subspace and the span of `Z` both
stabilize the nonzero `δ₀` and differ. -/
theorem finrank_load_bearing :
    StabilizedBy (⊥ : Submodule (ZMod 2) (Pauli 1)) delta0
      ∧ StabilizedBy (Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)}) delta0
      ∧ delta0 ≠ 0
      ∧ (⊥ : Submodule (ZMod 2) (Pauli 1)) ≠ Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)} :=
  ⟨stabilizedBy_bot _, stabilizedBy_span_z, delta0_ne_zero, bot_ne_span_z⟩

/-- **The theorem on the witness.** With `δ₀ ≠ 0` and dimension `1`, the span of `Z` is the only
stabilizer of dimension one: any other is equal to it. -/
theorem rigidity_on_witness (L : Submodule (ZMod 2) (Pauli 1)) (hr : finrank (ZMod 2) L = 1)
    (hs : StabilizedBy L delta0) : L = Submodule.span (ZMod 2) {(pauliz 0 : Pauli 1)} :=
  eq_of_stabilizedBy_of_stabilizedBy hr (finrank_span_singleton (by decide)) delta0_ne_zero hs
    stabilizedBy_span_z

/-! ## Agreement on the involution at odd `yWeight` -/

/-- `Y = X + Z` applied twice to `δ₀` returns `δ₀`, computed directly at both words. -/
theorem involution_y_direct :
    pauliAct (paulix 0 + pauliz 0 : Pauli 1) (pauliAct (paulix 0 + pauliz 0) delta0) = delta0 := by
  funext w
  have hw : w = ![w 0] := by
    funext i
    fin_cases i
    rfl
  have hyw : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have hs0 : ![0] + (paulix 0 + pauliz 0 : Pauli 1).X = ![1] := by decide
  have hs1 : ![1] + (paulix 0 + pauliz 0 : Pauli 1).X = ![0] := by decide
  have hz0 : zDot (paulix 0 + pauliz 0 : Pauli 1) ![0] = 0 := by decide
  have hz1 : zDot (paulix 0 + pauliz 0 : Pauli 1) ![1] = 1 := by decide
  rw [hw]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h1
  · rw [h0]
    simp only [pauliAct, hyw, hs0, hs1, hz0, hz1, delta0_zero, pow_one, pow_zero, mul_one]
    simp
  · rw [h1]
    simp only [pauliAct, hyw, hs0, hs1, hz0, hz1, delta0_one, pow_one, pow_zero, mul_one,
      mul_zero]

/-- The direct computation agrees with the theorem. -/
theorem involution_y_agrees :
    pauliAct (paulix 0 + pauliz 0 : Pauli 1) (pauliAct (paulix 0 + pauliz 0) delta0) = delta0 :=
  pauliAct_pauliAct _ _

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Stabilizer.neg_one_pow_eq_I_pow' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms neg_one_pow_eq_I_pow

/-- info: 'FTQCLib.Stabilizer.I_pow_eq_of_natCast_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms I_pow_eq_of_natCast_eq

/-- info: 'FTQCLib.Stabilizer.I_pow_val_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms I_pow_val_add

/-- info: 'FTQCLib.Stabilizer.pauliAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pauliAct

/-- info: 'FTQCLib.Stabilizer.pauliAct_apply' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_apply

/-- info: 'FTQCLib.Stabilizer.pauliAct_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_zero

/-- info: 'FTQCLib.Stabilizer.pauliAct_zero_fun' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_zero_fun

/-- info: 'FTQCLib.Stabilizer.pauliAct_mul_left' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_mul_left

/-- info: 'FTQCLib.Stabilizer.pauliAct_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_add

/-- info: 'FTQCLib.Stabilizer.pauliAct_pauliAct' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_pauliAct

/-- info: 'FTQCLib.Stabilizer.pauliAct_eq_zero_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_eq_zero_iff

/-- info: 'FTQCLib.Stabilizer.StabilizedBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms StabilizedBy

/-- info: 'FTQCLib.Stabilizer.stabilizedBy_bot' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms stabilizedBy_bot

/-- info: 'FTQCLib.Stabilizer.stabilizedBy_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms stabilizedBy_zero

/-- info: 'FTQCLib.Stabilizer.StabilizedBy.mono' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms StabilizedBy.mono

/-- info: 'FTQCLib.Stabilizer.omega_eq_zero_of_stabilizes' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms omega_eq_zero_of_stabilizes

/-- info: 'FTQCLib.Stabilizer.isStabilizer_of_stabilizedBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_of_stabilizedBy

/-- info: 'FTQCLib.Stabilizer.isStabilizer_sup_of_stabilizedBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_sup_of_stabilizedBy

/-- info: 'FTQCLib.Stabilizer.eq_of_stabilizedBy_of_stabilizedBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_of_stabilizedBy_of_stabilizedBy

end FTQCLib.Stabilizer

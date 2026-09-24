/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierState

/-!
# Acceptance rows for well-formedness and the floor stratum

Three one-qubit records at precision one with the flat exponent:

* `KX` — `L = ⟨X⟩`, scale `1`: the uniform amplitude with its true stabilizer. A carrier, on the
  floor, satisfying the exponent law — each computed **directly** (`isCarrier_KX`, `isFloor_KX`,
  `shiftLaw_KX`), and each direction of `isFloor_iff_shiftLaw` reaching the other side
  (`floor_KX_agrees`, `shiftLaw_KX_agrees`): the agreement rows.
* `KY` — `L = ⟨Y⟩`, scale `1`: the same amplitude with a stale Lagrangian. A carrier, **not** on
  the floor (`Y` sends the uniform amplitude at the word `0` to `−i`), and **not** satisfying the
  exponent law (the defect of `Y` is `0` at the word `0` and `1` at the word `1`): both sides of
  the equivalence are false, so the equivalence is discriminating in both directions.
* `K0` — `L = ⟨X⟩`, scale `0`: not a carrier, so not on the floor, yet the exponent law holds
  (it never reads the scale). So the carrier hypothesis of `isFloor_iff_shiftLaw` is load-bearing
  (`hc_load_bearing`).

`finrank_eq_of_isCarrier` is reached two ways on `KX`: through the theorem and through Mathlib's
`finrank_span_singleton`. For `gauge_of_stateEq`, the nonzero-scale hypotheses are load-bearing:
with both scales `0` the two records `⟨X⟩` and `⊥` have the same (zero) denotation and different
shadows (`gauge_needs_hc`).

The denotations are `ℂ`-valued and noncomputable, so the amplitude rows are not kernel rows; the
`ZMod 2` arithmetic of the exponent law on `KY` is decided by the kernel. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Module

/-! ## Singleton spans are isotropic -/

/-- The span of one Pauli is isotropic. -/
theorem isStabilizer_span_singleton {n : ℕ} (x : Pauli n) :
    IsStabilizer (Submodule.span (ZMod 2) {x}) := by
  intro p hp q hq
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
  rw [omega_smul_left, omega_smul_right, omega_self]
  simp

/-! ## The witnesses -/

/-- `⟨X⟩` on one qubit. -/
noncomputable def lagX : Submodule (ZMod 2) (Pauli 1) := Submodule.span (ZMod 2) {paulix 0}

/-- `⟨Y⟩` on one qubit. -/
noncomputable def lagY : Submodule (ZMod 2) (Pauli 1) :=
  Submodule.span (ZMod 2) {paulix 0 + pauliz 0}

/-- The uniform amplitude with its true stabilizer `⟨X⟩`. -/
noncomputable def KX : KernelState 1 := ⟨1, 0, 1, lagX, 0⟩

/-- The uniform amplitude with the stale Lagrangian `⟨Y⟩`. -/
noncomputable def KY : KernelState 1 := ⟨1, 0, 1, lagY, 0⟩

/-- The `⟨X⟩` record with scale `0`. -/
noncomputable def K0 : KernelState 1 := ⟨1, 0, 0, lagX, 0⟩

/-- Every word is on the support of `⟨X⟩` at the origin. -/
theorem lagX_support (w : Fin 1 → ZMod 2) :
    ∃ p ∈ lagX, w = (0 : Fin 1 → ZMod 2) + p.X := by
  refine ⟨(w 0) • paulix 0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
  funext i
  fin_cases i
  simp [paulix]

/-- Every word is on the support of `⟨Y⟩` at the origin. -/
theorem lagY_support (w : Fin 1 → ZMod 2) :
    ∃ p ∈ lagY, w = (0 : Fin 1 → ZMod 2) + p.X := by
  refine ⟨(w 0) • (paulix 0 + pauliz 0),
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
  funext i
  fin_cases i
  simp [paulix, pauliz]

/-- The flat exponent evaluates to `0`. -/
theorem eval_zero_poly (v : Fin 1 → ZMod 2) : DiagPhase.eval (0 : DiagPhase 1 1) v = 0 := by
  unfold DiagPhase.eval
  simp

/-- `KX` denotes the constant `1`. -/
theorem amp_KX (w : Fin 1 → ZMod 2) : amp (ofKernelState KX) w = 1 := by
  rw [amp_ofKernelState_pos KX (lagX_support w)]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 1 1) w) = 1
  rw [eval_zero_poly, charOf_zero, one_mul]

/-- `KY` denotes the constant `1`. -/
theorem amp_KY (w : Fin 1 → ZMod 2) : amp (ofKernelState KY) w = 1 := by
  rw [amp_ofKernelState_pos KY (lagY_support w)]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 1 1) w) = 1
  rw [eval_zero_poly, charOf_zero, one_mul]

/-! ## `KX`: carrier, floor, exponent law — directly, and through the theorem -/

/-- `KX` is a carrier. -/
theorem isCarrier_KX : IsCarrier (ofKernelState KX) := by
  refine ⟨le_rfl, isStabilizer_span_singleton (paulix 0), ?_, ?_⟩
  · exact orthogonal_le_of_lagrangian (isStabilizer_span_singleton (paulix 0))
      (finrank_span_singleton (by decide))
  · intro h
    have h0 := congrFun h 0
    rw [amp_KX] at h0
    exact one_ne_zero h0

/-- `zDot` against a multiple of `X` vanishes. -/
theorem zDot_smul_paulix (a : ZMod 2) (v : Fin 1 → ZMod 2) : zDot (a • paulix 0) v = 0 := by
  simp [zDot, paulix]

/-- `KX` is on the floor, computed directly: `X` shifts the constant function to itself. -/
theorem isFloor_KX : IsFloor (ofKernelState KX) := by
  refine ⟨isCarrier_KX, ?_⟩
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {paulix 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨0, ?_⟩
  funext w
  have hy : yWeight (a • paulix 0) = 0 := zDot_smul_paulix a _
  simp only [pauliAct, hy, zDot_smul_paulix, pow_zero, one_mul, amp_KX, ZMod.val_zero]

/-- `KX` satisfies the exponent law, computed directly: every defect is `0`. -/
theorem shiftLaw_KX : ShiftLaw KX := by
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {paulix 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨0, ?_⟩
  intro w _
  simp only [KX]
  rw [eval_zero_poly, eval_zero_poly, zDot_smul_paulix]
  decide

/-- **Agreement.** The theorem's `←` direction reaches the floor from the exponent law. -/
theorem floor_KX_agrees : IsFloor (ofKernelState KX) :=
  (isFloor_iff_shiftLaw KX isCarrier_KX).mpr shiftLaw_KX

/-- **Agreement.** The theorem's `→` direction reaches the exponent law from the floor. -/
theorem shiftLaw_KX_agrees : ShiftLaw KX :=
  (isFloor_iff_shiftLaw KX isCarrier_KX).mp isFloor_KX

/-- `finrank_eq_of_isCarrier` on `KX`. -/
theorem finrank_KX : finrank (ZMod 2) (ofKernelState KX).L = 1 :=
  finrank_eq_of_isCarrier isCarrier_KX

/-- The same dimension through Mathlib. -/
theorem finrank_KX_direct : finrank (ZMod 2) lagX = 1 :=
  finrank_span_singleton (by decide)

/-! ## `KY`: a carrier that is not on the floor, and fails the exponent law -/

/-- `KY` is a carrier. -/
theorem isCarrier_KY : IsCarrier (ofKernelState KY) := by
  refine ⟨le_rfl, isStabilizer_span_singleton (paulix 0 + pauliz 0), ?_, ?_⟩
  · exact orthogonal_le_of_lagrangian (isStabilizer_span_singleton (paulix 0 + pauliz 0))
      (finrank_span_singleton (by decide))
  · intro h
    have h0 := congrFun h 0
    rw [amp_KY] at h0
    exact one_ne_zero h0

/-- `Y` is in `⟨Y⟩`. -/
theorem pauliy_mem_lagY : paulix 0 + pauliz 0 ∈ (ofKernelState KY).L := by
  change _ ∈ Submodule.span (ZMod 2) {paulix 0 + pauliz 0}
  exact Submodule.mem_span_singleton_self _

/-- **Discriminating.** `KY` is not on the floor: `Y` sends the uniform amplitude at `0` to `−i`,
which is neither `+1` nor `−1`. -/
theorem not_isFloor_KY : ¬ IsFloor (ofKernelState KY) := by
  rintro ⟨-, hs⟩
  obtain ⟨s, hsg⟩ := hs (paulix 0 + pauliz 0) pauliy_mem_lagY
  have h := congrFun hsg 0
  have hy : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have hz : zDot (paulix 0 + pauliz 0 : Pauli 1)
      ((0 : Fin 1 → ZMod 2) + (paulix 0 + pauliz 0 : Pauli 1).X) = 1 := by decide
  simp only [pauliAct, hy, hz, amp_KY, pow_one, mul_one] at h
  rcases zmod_two_eq_zero_or_one s with rfl | rfl
  · rw [ZMod.val_zero, pow_zero] at h
    have := congrArg Complex.im h
    simp at this
  · have hv : ((1 : ZMod 2)).val = 1 := by decide
    rw [hv, pow_one] at h
    have := congrArg Complex.im h
    simp at this

/-- **Discriminating.** `KY` fails the exponent law: the defect of `Y` is `0` at the word `0` and
`1` at the word `1` (kernel row on the `ZMod 2` arithmetic). -/
theorem not_shiftLaw_KY : ¬ ShiftLaw KY := by
  intro h
  simp only [ShiftLaw, KY] at h
  obtain ⟨k, hk⟩ := h (paulix 0 + pauliz 0)
    (by unfold lagY; exact Submodule.mem_span_singleton_self _)
  have h0 := hk 0 (lagY_support 0)
  have h1 := hk ![1] (lagY_support ![1])
  rw [eval_zero_poly, eval_zero_poly] at h0 h1
  have hz0 : zDot (paulix 0 + pauliz 0 : Pauli 1) 0 = 0 := zDot_zero_right _
  have hz1 : zDot (paulix 0 + pauliz 0 : Pauli 1) ![1] = 1 := by decide
  rw [hz0] at h0
  rw [hz1, ← h0] at h1
  revert h1
  decide

/-! ## The carrier hypothesis of the equivalence is load-bearing -/

/-- `K0` is not on the floor: its denotation is the zero function. -/
theorem not_isFloor_K0 : ¬ IsFloor (ofKernelState K0) :=
  fun h => h.1.2.2.2 (amp_c_zero _ rfl)

/-- `K0` satisfies the exponent law: the law never reads the scale. -/
theorem shiftLaw_K0 : ShiftLaw K0 := by
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {paulix 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨0, ?_⟩
  intro w _
  simp only [K0]
  rw [eval_zero_poly, eval_zero_poly, zDot_smul_paulix]
  decide

/-- **`IsCarrier` is load-bearing in `isFloor_iff_shiftLaw`.** Without it the equivalence would
be false on `K0`. -/
theorem hc_load_bearing : ¬ IsFloor (ofKernelState K0) ∧ ShiftLaw K0 :=
  ⟨not_isFloor_K0, shiftLaw_K0⟩

/-! ## The nonzero-scale hypotheses of completeness are load-bearing -/

/-- With both scales `0`, `⟨X⟩` and `⊥` have the same denotation and different shadows. -/
theorem gauge_needs_hc :
    amp (ofKernelState (⟨1, 0, 0, lagX, 0⟩ : KernelState 1))
        = amp (ofKernelState (⟨1, 0, 0, ⊥, 0⟩ : KernelState 1))
      ∧ Submodule.map xProj lagX ≠ Submodule.map xProj (⊥ : Submodule (ZMod 2) (Pauli 1)) := by
  refine ⟨(amp_c_zero _ rfl).trans (amp_c_zero _ rfl).symm, ?_⟩
  intro h
  have hmem : (paulix 0 : Pauli 1).X ∈ Submodule.map xProj lagX :=
    Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  rw [h, Submodule.map_bot, Submodule.mem_bot] at hmem
  exact absurd hmem (by decide)

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.IsCarrier' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsCarrier

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_c_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ampCore_c_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_c_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_c_zero

/-- info: 'FTQCLib.Frame.Walkthrough.c_ne_zero_of_isCarrier' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms c_ne_zero_of_isCarrier

/-- info: 'FTQCLib.Frame.Walkthrough.finrank_eq_of_isCarrier' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finrank_eq_of_isCarrier

/-- info: 'FTQCLib.Frame.Walkthrough.IsFloor' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsFloor

/-- info: 'FTQCLib.Frame.Walkthrough.L_eq_of_stateEq_of_isFloor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms L_eq_of_stateEq_of_isFloor

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_pos' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_ofKernelState_pos

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_neg' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_ofKernelState_neg

/-- info: 'FTQCLib.Frame.Walkthrough.vec_add_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms vec_add_self

/-- info: 'FTQCLib.Frame.Walkthrough.support_add_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms support_add_X

/-- info: 'FTQCLib.Frame.Walkthrough.support_add_X_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms support_add_X_iff

/-- info: 'FTQCLib.Frame.Walkthrough.x₀_mem_support' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms x₀_mem_support

/-- info: 'FTQCLib.Frame.Walkthrough.ShiftLaw' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ShiftLaw

/-- info: 'FTQCLib.Frame.Walkthrough.two_pow_pred_mul_zDot_add_X' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_pow_pred_mul_zDot_add_X

/-- info: 'FTQCLib.Frame.Walkthrough.neg_one_pow_zDot_add_X' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms neg_one_pow_zDot_add_X

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_amp_ofKernelState_of_defect' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_amp_ofKernelState_of_defect

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_iff_shiftLaw' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFloor_iff_shiftLaw

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_ne_zero_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_ofKernelState_ne_zero_iff

/-- info: 'FTQCLib.Frame.Walkthrough.gauge_of_stateEq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gauge_of_stateEq

end FTQCLib.Frame.Walkthrough

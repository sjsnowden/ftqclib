/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardGateCertificate
import FTQCLib.Examples.CarrierStateCheck
import FTQCLib.Examples.CarrierStateHadamardCheck

/-!
# Check: the one-H certificate

* **The certificate on the point state.** `KZ` (`L = ⟨Z⟩`, `δ₀`, offset `0`) has bit `0` pinned
  and a flat exponent, so `cert_pinned` applies (`cert_pinned_KZ`): the chart of `H|0⟩` is the
  chart action on the chart of `|0⟩`. The χ-component is reached two ways at the generator `X` of
  the output's Lagrangian: the decoded character of the pinned output is `0` (`chi_out_X`,
  computed), and the transported character `chiAt KZ (τ X) + tvSignZ 0 (τ X)` is `0`
  (`chi_transported_X`, computed), which is what `cert_chi` asserts (`cert_chi_KZ`).
* **The cochain values** on one qubit (kernel rows): `tvSignZ 0 Y = 2`, `tvSignZ 0 X = 0`,
  `tvSignZ 0 Z = 0`.
* **The swap is the transvection** on the three nontrivial one-qubit Paulis (kernel rows).

Not tested here: `hpin` and `hqfree` as load-bearing hypotheses — `HadamardReductionCheck`
carries the `hqfree` control for the pinned executable's denotation; the decode-level controls
belong to the free executable's floor closure, which is not proved here. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame FTQCLib.Gates FTQCLib.Stabilizer Module

/-! ## Kernel rows -/

/-- The cochain at `Y`. -/
theorem tvSignZ_y : tvSignZ (0 : Fin 1) (paulix 0 + pauliz 0) = 2 := by decide

/-- The cochain at `X`. -/
theorem tvSignZ_x : tvSignZ (0 : Fin 1) (paulix 0) = 0 := by decide

/-- The cochain at `Z`. -/
theorem tvSignZ_z : tvSignZ (0 : Fin 1) (pauliz 0) = 0 := by decide

/-- The transvection swaps `X` and `Z` and fixes `Y`, on one qubit. -/
theorem tv_one_qubit :
    transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0) = pauliz 0
      ∧ transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (pauliz 0) = paulix 0
      ∧ transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0 + pauliz 0)
          = paulix 0 + pauliz 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [← pauliSwapOn_singleton_eq_transvection] <;> decide

/-! ## The certificate on the point state -/

/-- Bit `0` is pinned in `⟨Z⟩`. -/
theorem KZ_pinned : ∀ p ∈ lagZ, p.X (0 : Fin 1) = 0 := by
  intro p hp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  simp [pauliz]

/-- The flat exponent is free of every bit. -/
theorem zero_poly_free (i : Fin 1) : ∀ (w : Fin 1 → ZMod 2) (b : ZMod 2),
    DiagPhase.eval (0 : DiagPhase 1 1) (Function.update w i b)
      = DiagPhase.eval (0 : DiagPhase 1 1) w := by
  intro w b
  unfold DiagPhase.eval
  simp

/-- **The certificate on `|0⟩`.** -/
theorem cert_pinned_KZ :
    chartOf (applyHPinned (0 : Fin 1) ⟨1, 0, 1, lagZ, 0⟩)
        (isFloor_applyHPinned (0 : Fin 1) isFloor_KZ KZ_pinned (zero_poly_free 0)) one_le_two
      = frameTransvectionYAction (0 : Fin 1)
          (chartOf ⟨1, 0, 1, lagZ, 0⟩ isFloor_KZ one_le_two) :=
  cert_pinned (0 : Fin 1) 0 1 lagZ 0 KZ_pinned (zero_poly_free 0) isFloor_KZ

/-- `X` is in the output's Lagrangian `τ⟨Z⟩`. -/
theorem paulix_mem_out :
    paulix (0 : Fin 1)
      ∈ Submodule.map (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0)).toLinearMap lagZ :=
  Submodule.mem_map.mpr ⟨pauliz 0, Submodule.mem_span_singleton_self _, tv_one_qubit.2.1⟩

/-- **Computed:** the decoded character of the pinned output at `X` is `0`. -/
theorem chi_out_X :
    chiAt (applyHPinned (0 : Fin 1) (⟨1, 0, 1, lagZ, 0⟩ : KernelState 1)) (paulix 0) = 0 := by
  unfold chiAt chiOfE eAt
  simp only [applyHPinned]
  have he : ∀ v : Fin 1 → ZMod 2,
      DiagPhase.eval ((0 : DiagPhase 1 1) + hSignPoly 0 ((0 : Fin 1 → ZMod 2) 0) 1) v = 0 := by
    intro v
    rw [DiagPhase.eval_add, eval_hSignPoly_one]
    unfold DiagPhase.eval
    simp
  simp only [he]
  decide

/-- **Computed:** the transported character at `X` is `0`. -/
theorem chi_transported_X :
    chiAt (⟨1, 0, 1, lagZ, 0⟩ : KernelState 1)
          (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0))
        + tvSignZ (0 : Fin 1) (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0))
      = 0 := by
  rw [tv_one_qubit.1, tvSignZ_z, add_zero]
  unfold chiAt chiOfE eAt
  simp only [eval_zero_poly]
  decide

/-- **Agreement:** `cert_chi` on `|0⟩` at `X`, with both sides computed above. -/
theorem cert_chi_KZ :
    chiAt (applyHPinned (0 : Fin 1) (⟨1, 0, 1, lagZ, 0⟩ : KernelState 1)) (paulix 0)
      = chiAt (⟨1, 0, 1, lagZ, 0⟩ : KernelState 1)
          (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0))
        + tvSignZ (0 : Fin 1) (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0)) :=
  cert_chi (0 : Fin 1) 0 1 lagZ 0 KZ_pinned (zero_poly_free 0) paulix_mem_out

/-- The two computed sides agree with each other. -/
theorem cert_chi_KZ_values :
    chiAt (applyHPinned (0 : Fin 1) (⟨1, 0, 1, lagZ, 0⟩ : KernelState 1)) (paulix 0)
      = chiAt (⟨1, 0, 1, lagZ, 0⟩ : KernelState 1)
          (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0))
        + tvSignZ (0 : Fin 1) (transvectionEquiv (paulix (0 : Fin 1) + pauliz 0) (paulix 0)) := by
  rw [chi_out_X, chi_transported_X]

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_singleton_eq_transvection' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_singleton_eq_transvection

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_singleton_eq_transvection'' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_singleton_eq_transvection'

/-- info: 'FTQCLib.Frame.Walkthrough.mem_map_pauliSwapOn' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_map_pauliSwapOn

/-- info: 'FTQCLib.Frame.Walkthrough.decodeFloor' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms decodeFloor

/-- info: 'FTQCLib.Frame.Walkthrough.chartOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chartOf

/-- info: 'FTQCLib.Frame.Walkthrough.chartOf_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chartOf_L

/-- info: 'FTQCLib.Frame.Walkthrough.chartOf_chi' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chartOf_chi

/-- info: 'FTQCLib.Frame.Walkthrough.chartOf_congr' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chartOf_congr

/-- info: 'FTQCLib.Frame.Walkthrough.eval_hSignPoly_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_hSignPoly_one

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_one_mul_val' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toFour_one_mul_val

/-- info: 'FTQCLib.Frame.Walkthrough.update_add_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms update_add_left

/-- info: 'FTQCLib.Frame.Walkthrough.add_update_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms add_update_right

/-- info: 'FTQCLib.Frame.Walkthrough.eAt_update_free' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms eAt_update_free

/-- info: 'FTQCLib.Frame.Walkthrough.eAt_applyHPinned' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eAt_applyHPinned

/-- info: 'FTQCLib.Frame.Walkthrough.cert_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cert_L

/-- info: 'FTQCLib.Frame.Walkthrough.tv_coords' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms tv_coords

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_tv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms yWeight_tv

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_update_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zDot_update_zero

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_split_tv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zDot_split_tv

/-- info: 'FTQCLib.Frame.Walkthrough.cert_chi' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cert_chi

/-- info: 'FTQCLib.Frame.Walkthrough.cert_pinned' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cert_pinned

/-- info: 'FTQCLib.Frame.Walkthrough.tvSignZ_add_tv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms tvSignZ_add_tv

/-- info: 'FTQCLib.Frame.Walkthrough.frameTransvectionYAction_invol' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frameTransvectionYAction_invol

/-- info: 'FTQCLib.Frame.Walkthrough.cert_free' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms cert_free

end FTQCLib.Frame.Walkthrough

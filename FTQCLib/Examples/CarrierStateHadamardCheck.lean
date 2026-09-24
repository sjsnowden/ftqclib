/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierStateHadamard

/-!
# Check: closure under the Hadamard rules

* **The sign of the intertwining lemma is load-bearing.** On one qubit with `g = Y` (so
  `(g.X 0)(g.Z 0) = 1`) and the point amplitude `δ₀`: the swap-lifted action of `Y` on the Walsh
  transform of `δ₀` at the word `0` is `−i/√2`, while the Walsh transform of the action of `Y` on
  `δ₀` at the word `0` is `+i/√2` — the two sides of the unsigned law differ
  (`sign_load_bearing`), and the signed law is the theorem.
* **`isFloor_hRaise` on the point state.** `KZ` (`L = ⟨Z⟩`, the amplitude `δ₀`) is on the floor
  (`isFloor_KZ`, direct). Its raise at bit `0` with the representer `0` has Lagrangian `⟨X⟩` and
  denotes the constant `1/√2`; that it is on the floor is computed directly
  (`stabilizedBy_raised_KZ`) and reached through the theorem (`isFloor_hRaise_KZ`) — the agreement
  pair.
* **`walshTransform_ne_zero` is discriminating**: the Walsh transform of `δ₀` is the constant
  `1/√2`, not zero (`walsh_delta0`).

What no row here tests: the shadow hypothesis of `isCarrier_applyHFiner` (off the shadow the free
rule's output can be the zero function), and `hqfree` for the pinned rule
(`HadamardReductionCheck` carries the classical row); both are hypotheses inherited from certified
theorems, not introduced here. The denotations are `ℂ`-valued; the `Pauli 1` and `ZMod 2` facts are
kernel rows. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Module

/-! ## Examples -/

/-- The one-qubit point amplitude `δ₀`. -/
noncomputable def d0 : (Fin 1 → ZMod 2) → ℂ := fun w => if w 0 = 0 then 1 else 0

/-- `δ₀` at the word `0`. -/
theorem d0_zero : d0 ![0] = 1 := by
  simp [d0]

/-- `δ₀` at the word `1`. -/
theorem d0_one : d0 ![1] = 0 := by
  simp [d0]

/-- Every word on one qubit is `![0]` or `![1]`. -/
theorem word_cases (w : Fin 1 → ZMod 2) : w = ![0] ∨ w = ![1] := by
  rcases zmod_two_eq_zero_or_one (w 0) with h | h
  · left
    funext i
    fin_cases i
    exact h
  · right
    funext i
    fin_cases i
    exact h

/-- `⟨Z⟩` on one qubit. -/
noncomputable def lagZ : Submodule (ZMod 2) (Pauli 1) := Submodule.span (ZMod 2) {pauliz 0}

/-- The point state `|0⟩`: `L = ⟨Z⟩`, flat exponent, scale `1`, offset `0`. -/
noncomputable def KZ : KernelState 1 := ⟨1, 0, 1, lagZ, 0⟩

/-- The span of one Pauli is isotropic. -/
theorem isStabilizer_span_singleton' {n : ℕ} (x : Pauli n) :
    IsStabilizer (Submodule.span (ZMod 2) {x}) := by
  intro p hp q hq
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
  rw [omega_smul_left, omega_smul_right, omega_self]
  simp

/-- The support of `KZ` is the word `0`. -/
theorem KZ_support_iff (w : Fin 1 → ZMod 2) :
    (∃ p ∈ lagZ, w = (0 : Fin 1 → ZMod 2) + p.X) ↔ w = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
    funext i
    fin_cases i
    simp [pauliz]
  · rintro rfl
    exact ⟨0, Submodule.zero_mem _, by simp⟩

/-- `KZ` denotes `δ₀`. -/
theorem amp_KZ : amp (ofKernelState KZ) = d0 := by
  funext w
  rcases word_cases w with rfl | rfl
  · rw [amp_ofKernelState_pos KZ ((KZ_support_iff _).mpr (by decide)), d0_zero]
    change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 1 1) ![0]) = 1
    have h0 : DiagPhase.eval (0 : DiagPhase 1 1) ![0] = 0 := by
      unfold DiagPhase.eval
      simp
    rw [h0, charOf_zero, one_mul]
  · rw [amp_ofKernelState_neg KZ (fun h => by
      have := (KZ_support_iff _).mp h
      exact absurd this (by decide)), d0_one]

/-- `KZ` is a carrier. -/
theorem isCarrier_KZ : IsCarrier (ofKernelState KZ) := by
  refine ⟨le_rfl, isStabilizer_span_singleton' (pauliz (0 : Fin 1)), ?_, ?_⟩
  · exact orthogonal_le_of_lagrangian (isStabilizer_span_singleton' (pauliz (0 : Fin 1)))
      (finrank_span_singleton (by decide))
  · rw [amp_KZ]
    intro h
    have h0 := congrFun h ![0]
    rw [d0_zero] at h0
    exact one_ne_zero h0

/-- `zDot` against a multiple of `Z` reads the word. -/
theorem zDot_smul_pauliz (a : ZMod 2) (v : Fin 1 → ZMod 2) :
    zDot (a • pauliz 0) v = a.val * (v 0).val := by
  simp [zDot, pauliz]

/-- `KZ` is on the floor, directly: `Z` fixes `δ₀`. -/
theorem isFloor_KZ : IsFloor (ofKernelState KZ) := by
  refine ⟨isCarrier_KZ, ?_⟩
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {pauliz 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨0, ?_⟩
  funext w
  have hX : (a • pauliz 0 : Pauli 1).X = 0 := by
    funext i
    simp [pauliz]
  have hy : yWeight (a • pauliz (0 : Fin 1)) = 0 := by
    unfold yWeight
    rw [hX, zDot_zero_right]
  rw [amp_KZ]
  simp only [pauliAct, hy, hX, add_zero, pow_zero, one_mul, ZMod.val_zero]
  rcases word_cases w with rfl | rfl
  · rw [d0_zero, zDot_smul_pauliz]
    simp
  · rw [d0_one]
    simp

/-! ## The raised point state -/

/-- The Walsh transform of `δ₀` is the constant `1/√2`. -/
theorem walsh_delta0 : walshTransform 0 d0 = fun _ => 1 / (Real.sqrt 2 : ℂ) := by
  funext w
  have h0 : Function.update w 0 0 = ![0] := by
    funext i
    fin_cases i
    simp
  have h1 : Function.update w 0 1 = ![1] := by
    funext i
    fin_cases i
    simp
  simp only [walshTransform, h0, h1, d0_zero, d0_one, mul_zero, add_zero, mul_one]

/-- The Walsh transform of `δ₀` is not zero. -/
theorem walsh_delta0_ne_zero : walshTransform 0 d0 ≠ 0 := by
  rw [walsh_delta0]
  intro h
  have h0 := congrFun h ![0]
  simp at h0

/-- The representer `0` at bit `0` of `KZ`: the shadow of `⟨Z⟩` is trivial. -/
theorem KZ_representer : ∀ v ∈ Submodule.map xProj lagZ, dotF2 (0 : Fin 1 → ZMod 2) v = v 0 := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  simp [dotF2, pauliz]

/-- **Through the theorem.** The raise of `KZ` at bit `0` is on the floor. -/
theorem isFloor_hRaise_KZ : IsFloor (hRaise (0 : Fin 1) 0 (ofKernelState KZ)) :=
  isFloor_hRaise (0 : Fin 1) 0 isFloor_KZ rfl KZ_representer

/-- **Directly.** The raised Lagrangian `⟨X⟩` stabilizes the constant `1/√2`. -/
theorem stabilizedBy_raised_KZ :
    StabilizedBy (Submodule.map (pauliSwapOn {0}) lagZ) (walshTransform 0 d0) := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  refine ⟨0, ?_⟩
  funext w
  have hZ : (pauliSwapOn {0} (a • pauliz 0) : Pauli 1).Z = 0 := by
    funext i
    fin_cases i
    simp [pauliz]
  have hz : ∀ v : Fin 1 → ZMod 2, zDot (pauliSwapOn {0} (a • pauliz (0 : Fin 1))) v = 0 := by
    intro v
    unfold zDot
    rw [hZ]
    simp
  have hy : yWeight (pauliSwapOn {0} (a • pauliz 0)) = 0 := hz _
  rw [walsh_delta0]
  simp only [pauliAct, hy, hz, pow_zero, one_mul, ZMod.val_zero]

/-- The two routes reach the same Lagrangian: the raise's `L` is the swapped `⟨Z⟩`. -/
theorem hRaise_KZ_L :
    (hRaise (0 : Fin 1) 0 (ofKernelState KZ)).L = Submodule.map (pauliSwapOn {0}) lagZ :=
  rfl

/-! ## The sign of the intertwining lemma -/

/-- The swap fixes `Y` on one qubit. -/
theorem swap_y : pauliSwapOn {0} (paulix 0 + pauliz 0 : Pauli 1) = paulix 0 + pauliz 0 := by
  decide

/-- The swap-lifted action of `Y` on the Walsh transform of `δ₀`, at the word `0`: `−i/√2`. -/
theorem lhs_value :
    pauliAct (pauliSwapOn {0} (paulix 0 + pauliz 0)) (walshTransform 0 d0) ![0]
      = -Complex.I * (1 / (Real.sqrt 2 : ℂ)) := by
  rw [swap_y, walsh_delta0]
  have hy : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have hz : zDot (paulix 0 + pauliz 0 : Pauli 1)
      (![0] + (paulix 0 + pauliz 0 : Pauli 1).X) = 1 := by decide
  simp only [pauliAct, hy, hz, pow_one]
  ring

/-- The Walsh transform of the action of `Y` on `δ₀`, at the word `0`: `+i/√2`. -/
theorem rhs_value :
    walshTransform 0 (pauliAct (paulix 0 + pauliz 0) d0) ![0]
      = Complex.I * (1 / (Real.sqrt 2 : ℂ)) := by
  have hy : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have hu0 : Function.update (![0] : Fin 1 → ZMod 2) 0 0 = ![0] := by decide
  have hu1 : Function.update (![0] : Fin 1 → ZMod 2) 0 1 = ![1] := by decide
  have hs0 : ![0] + (paulix 0 + pauliz 0 : Pauli 1).X = ![1] := by decide
  have hs1 : ![1] + (paulix 0 + pauliz 0 : Pauli 1).X = ![0] := by decide
  have hz1 : zDot (paulix 0 + pauliz 0 : Pauli 1) ![1] = 1 := by decide
  have hz0 : zDot (paulix 0 + pauliz 0 : Pauli 1) ![0] = 0 := by decide
  have hsign : signOf ((![0] : Fin 1 → ZMod 2) 0) = 1 := by
    simp [signOf]
  simp only [walshTransform, pauliAct, hu0, hu1, hs0, hs1, hz1, hz0, hy, d0_zero, d0_one, hsign,
    pow_one, pow_zero, mul_one, mul_zero, zero_add, one_mul]
  ring

/-- **The sign is load-bearing.** The unsigned law fails on `Y` and `δ₀` at the word `0`. -/
theorem sign_load_bearing :
    pauliAct (pauliSwapOn {0} (paulix 0 + pauliz 0)) (walshTransform 0 d0) ![0]
      ≠ walshTransform 0 (pauliAct (paulix 0 + pauliz 0) d0) ![0] := by
  rw [lhs_value, rhs_value]
  intro h
  have hsq : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  field_simp at h
  norm_num at h

/-- **The signed law holds** on the same witness: the theorem's instance. -/
theorem signed_law_on_witness :
    pauliAct (pauliSwapOn {0} (paulix 0 + pauliz 0)) (walshTransform 0 d0)
      = fun w => (-1) ^ (((paulix 0 + pauliz 0 : Pauli 1).X 0).val
          * ((paulix 0 + pauliz 0 : Pauli 1).Z 0).val)
        * walshTransform 0 (pauliAct (paulix 0 + pauliz 0) d0) w :=
  pauliAct_pauliSwapOn_walshTransform 0 _ d0

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.omega_pauliSwapOn_singleton' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms omega_pauliSwapOn_singleton

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_map_pauliSwapOn' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_map_pauliSwapOn

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms pauliSwapEquiv

/-- info: 'FTQCLib.Frame.Walkthrough.finrank_map_pauliSwapOn' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finrank_map_pauliSwapOn

/-- info: 'FTQCLib.Frame.Walkthrough.coisotropic_map_pauliSwapOn' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coisotropic_map_pauliSwapOn

/-- info: 'FTQCLib.Frame.Walkthrough.walshTransform_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walshTransform_zero

/-- info: 'FTQCLib.Frame.Walkthrough.walshTransform_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walshTransform_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.signOf_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms signOf_eq

/-- info: 'FTQCLib.Frame.Walkthrough.update_add_swapX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms update_add_swapX

/-- info: 'FTQCLib.Frame.Walkthrough.update_add_X' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms update_add_X

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_split' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zDot_split

/-- info: 'FTQCLib.Frame.Walkthrough.sum_erase_update' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sum_erase_update

/-- info: 'FTQCLib.Frame.Walkthrough.sum_erase_swap' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sum_erase_swap

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_pauliSwapOn' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms yWeight_pauliSwapOn

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_pauliSwapOn_walshTransform' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pauliAct_pauliSwapOn_walshTransform

/-- info: 'FTQCLib.Frame.Walkthrough.stabilizedBy_map_pauliSwapOn_walshTransform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stabilizedBy_map_pauliSwapOn_walshTransform

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_hRaise' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isCarrier_hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hRaise' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isFloor_hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyHFiner' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isCarrier_applyHFiner

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_cover_of_isCarrier' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hadamard_cover_of_isCarrier

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyHPinned' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isCarrier_applyHPinned

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyHPinned' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFloor_applyHPinned

end FTQCLib.Frame.Walkthrough

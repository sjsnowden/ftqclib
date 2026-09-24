/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.ResidualBit
import FTQCLib.Examples.HadamardEliminationCheck

/-!
# Check: the residual class has no height-zero presentation

Axiom rows for every declaration of `ResidualBit`, and two examples:

* **The T-state** at `m = 3` (`KT`: exponent `X₀`, `⟨X₀⟩`): at the pair `0, e₀` the difference
  is `1`, with `2 ≠ 0` and `2 ≠ 4`; so neither the Walsh transform of its amplitude nor the free
  rule's output `applyHFiner 0` is the amplitude of any height-zero record — the modulus
  obstruction, beside `hFiner_not_kernelState`. The control: on the uniform record `KX` the pair
  difference is `0` and the eliminated record `hKX` (`HadamardEliminationCheck`) is a height-zero
  presentation.
* **`CCZ` then H** — the residual with non-affine support: `CCZ` on the uniform record on three
  registers at `m = 1` (`Kccz`, exponent `X₀X₁X₂`), H at bit `2`. The output is `√2` at `000`,
  `100`, `010` and `0` at their sum `110`: the support `{w₂ = w₀ w₁}` is not a coset, so no
  height-zero record presents it — the support obstruction; every pair there is collapse-shaped, so
  the modulus obstruction is silent (the two obstructions are independent).
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## The T-state at `m = 3` -/

/-- The T-state at `m = 3`: exponent `X₀` on `⟨X₀⟩`. -/
noncomputable def KT : KernelState 1 := ⟨3, MvPolynomial.X 0, 1, lagX, 0⟩

/-- The exponent's difference along `e₀` at `0` is `1`. -/
theorem KT_diff :
    DiagPhase.eval KT.q ((0 : Fin 1 → ZMod 2) + Pi.single 0 1) - DiagPhase.eval KT.q 0 = 1 := by
  change DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 3) ((0 : Fin 1 → ZMod 2) + Pi.single 0 1) -
    DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 3) 0 = 1
  rw [eval_X, eval_X]
  decide

/-- The residual value: `2·1 ≠ 0`. -/
theorem KT_not_collapse :
    2 * (DiagPhase.eval KT.q ((0 : Fin 1 → ZMod 2) + Pi.single 0 1) - DiagPhase.eval KT.q 0) ≠
      0 := by
  rw [KT_diff]
  decide

/-- The residual value: `2·1 ≠ 4`. -/
theorem KT_not_rotate :
    2 * (DiagPhase.eval KT.q ((0 : Fin 1 → ZMod 2) + Pi.single 0 1) - DiagPhase.eval KT.q 0) ≠
      (2 : ZMod (2 ^ KT.m)) ^ (KT.m - 1) := by
  rw [KT_diff]
  decide

/-- **The T-state.** The Walsh transform of the T-state's amplitude is no height-zero record. -/
theorem residual_KT :
    ¬ ∃ T : KernelState 1, amp (ofKernelState T) = walshTransform 0 (amp (ofKernelState KT)) :=
  not_exists_kernelState_walsh_of_residual KT (by decide) one_ne_zero 0 rfl (lagX_support 0)
    (lagX_support _) KT_not_collapse KT_not_rotate

/-- Bit `0` of `⟨X₀⟩` is X-supported. -/
theorem xSupported_lagX : (Pi.single 0 1 : Fin 1 → ZMod 2) ∈ Submodule.map xProj lagX :=
  Submodule.mem_map.mpr ⟨paulix 0, Submodule.mem_span_singleton_self _, rfl⟩

/-- **The T-state, the free rule.** `applyHFiner 0` on the T-state has no height-zero presentation.
-/
theorem residual_KT_applyHFiner :
    ¬ ∃ T : KernelState 1, amp (ofKernelState T) = amp (applyHFiner 0 (ofKernelState KT)) :=
  not_exists_kernelState_applyHFiner_of_residual KT (by decide) one_ne_zero 0 xSupported_lagX rfl
    (lagX_support 0) (lagX_support _) KT_not_collapse KT_not_rotate

/-- **The control.** On the uniform record `KX` the pair difference is `0` (collapse), and the
eliminated record `hKX` is a height-zero presentation of the Walsh transform. -/
theorem KX_diff_zero :
    2 * (DiagPhase.eval KX.q ((0 : Fin 1 → ZMod 2) + Pi.single 0 1) - DiagPhase.eval KX.q 0) =
      0 := by
  change 2 * (DiagPhase.eval (0 : DiagPhase 1 1) ((0 : Fin 1 → ZMod 2) + Pi.single 0 1) -
    DiagPhase.eval (0 : DiagPhase 1 1) 0) = 0
  rw [eval_zero_diag, eval_zero_diag]
  decide

theorem exists_kernelState_walsh_KX :
    ∃ T : KernelState 1, amp (ofKernelState T) = walshTransform 0 (amp (ofKernelState KX)) := by
  obtain ⟨K, hK⟩ := exists_kernelState_of_h_eq_zero hKX rfl
  exact ⟨K, by rw [← hK]; exact amp_hKX⟩

/-! ## `CCZ` then H: the residual with non-affine support -/

/-- `CCZ` on the uniform record on three registers at `m = 1`: exponent `X₀X₁X₂` on the all-`X`
Lagrangian. -/
noncomputable def Kccz : KernelState 3 :=
  ⟨1, MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2, 1, lagXXX, 0⟩

theorem eval_ccz (v : Fin 3 → ZMod 2) :
    DiagPhase.eval Kccz.q v =
      ((v 0).val : ZMod (2 ^ Kccz.m)) * ((v 1).val : ZMod (2 ^ Kccz.m)) *
        ((v 2).val : ZMod (2 ^ Kccz.m)) := by
  change DiagPhase.eval (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 : DiagPhase 3 1) v =
    ((v 0).val : ZMod (2 ^ 1)) * ((v 1).val : ZMod (2 ^ 1)) * ((v 2).val : ZMod (2 ^ 1))
  rw [eval_mul, eval_mul, eval_X, eval_X, eval_X]

theorem amp_Kccz (v : Fin 3 → ZMod 2) :
    amp (ofKernelState Kccz) v =
      charOf 1 (((v 0).val : ZMod (2 ^ 1)) * ((v 1).val : ZMod (2 ^ 1)) *
        ((v 2).val : ZMod (2 ^ 1))) := by
  rw [amp_ofKernelState_pos Kccz (lagXXX_support v), eval_ccz]
  change (1 : ℂ) * charOf 1 (((v 0).val : ZMod (2 ^ 1)) * ((v 1).val : ZMod (2 ^ 1)) *
    ((v 2).val : ZMod (2 ^ 1))) = _
  rw [one_mul]

/-- The output at `000`: `√2`. -/
theorem w14_000 : walshTransform 2 (amp (ofKernelState Kccz)) ![0, 0, 0] = Real.sqrt 2 := by
  unfold walshTransform
  rw [amp_Kccz, amp_Kccz]
  have e0 : Function.update (![0, 0, 0] : Fin 3 → ZMod 2) 2 0 = ![0, 0, 0] := by decide
  have e1 : Function.update (![0, 0, 0] : Fin 3 → ZMod 2) 2 1 = ![0, 0, 1] := by decide
  rw [e0, e1]
  have v0 : (![0, 0, 0] : Fin 3 → ZMod 2) 0 = 0 := by decide
  have v1 : (![0, 0, 0] : Fin 3 → ZMod 2) 1 = 0 := by decide
  have v2 : (![0, 0, 0] : Fin 3 → ZMod 2) 2 = 0 := by decide
  have u0 : (![0, 0, 1] : Fin 3 → ZMod 2) 0 = 0 := by decide
  have u1 : (![0, 0, 1] : Fin 3 → ZMod 2) 1 = 0 := by decide
  have u2 : (![0, 0, 1] : Fin 3 → ZMod 2) 2 = 1 := by decide
  rw [v0, v1, v2, u0, u1, u2, signOf_zero]
  simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, mul_zero, charOf_zero, one_mul,
    one_add_one_eq_two]
  exact one_div_sqrt_two_mul_two

/-- The output at `100`: `√2`. -/
theorem w14_100 : walshTransform 2 (amp (ofKernelState Kccz)) ![1, 0, 0] = Real.sqrt 2 := by
  unfold walshTransform
  rw [amp_Kccz, amp_Kccz]
  have e0 : Function.update (![1, 0, 0] : Fin 3 → ZMod 2) 2 0 = ![1, 0, 0] := by decide
  have e1 : Function.update (![1, 0, 0] : Fin 3 → ZMod 2) 2 1 = ![1, 0, 1] := by decide
  rw [e0, e1]
  have v1 : (![1, 0, 0] : Fin 3 → ZMod 2) 1 = 0 := by decide
  have v2 : (![1, 0, 0] : Fin 3 → ZMod 2) 2 = 0 := by decide
  have u1 : (![1, 0, 1] : Fin 3 → ZMod 2) 1 = 0 := by decide
  rw [v1, v2, u1, signOf_zero]
  simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, mul_zero, charOf_zero, one_mul,
    one_add_one_eq_two]
  exact one_div_sqrt_two_mul_two

/-- The output at `010`: `√2`. -/
theorem w14_010 : walshTransform 2 (amp (ofKernelState Kccz)) ![0, 1, 0] = Real.sqrt 2 := by
  unfold walshTransform
  rw [amp_Kccz, amp_Kccz]
  have e0 : Function.update (![0, 1, 0] : Fin 3 → ZMod 2) 2 0 = ![0, 1, 0] := by decide
  have e1 : Function.update (![0, 1, 0] : Fin 3 → ZMod 2) 2 1 = ![0, 1, 1] := by decide
  rw [e0, e1]
  have v0 : (![0, 1, 0] : Fin 3 → ZMod 2) 0 = 0 := by decide
  have v2 : (![0, 1, 0] : Fin 3 → ZMod 2) 2 = 0 := by decide
  have u0 : (![0, 1, 1] : Fin 3 → ZMod 2) 0 = 0 := by decide
  rw [v0, v2, u0, signOf_zero]
  simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, mul_zero, charOf_zero, one_mul,
    one_add_one_eq_two]
  exact one_div_sqrt_two_mul_two

/-- The output at `110`, the sum of the three: `0`. -/
theorem w14_110 : walshTransform 2 (amp (ofKernelState Kccz)) ![1, 1, 0] = 0 := by
  unfold walshTransform
  rw [amp_Kccz, amp_Kccz]
  have e0 : Function.update (![1, 1, 0] : Fin 3 → ZMod 2) 2 0 = ![1, 1, 0] := by decide
  have e1 : Function.update (![1, 1, 0] : Fin 3 → ZMod 2) 2 1 = ![1, 1, 1] := by decide
  rw [e0, e1]
  have v0 : (![1, 1, 0] : Fin 3 → ZMod 2) 0 = 1 := by decide
  have v1 : (![1, 1, 0] : Fin 3 → ZMod 2) 1 = 1 := by decide
  have v2 : (![1, 1, 0] : Fin 3 → ZMod 2) 2 = 0 := by decide
  have u0 : (![1, 1, 1] : Fin 3 → ZMod 2) 0 = 1 := by decide
  have u1 : (![1, 1, 1] : Fin 3 → ZMod 2) 1 = 1 := by decide
  have u2 : (![1, 1, 1] : Fin 3 → ZMod 2) 2 = 1 := by decide
  rw [v0, v1, v2, u0, u1, u2, signOf_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    ZMod.val_zero]
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, charOf_zero, charOf_one_one, one_mul]
  ring

/-- The three words sum to the fourth. -/
theorem w14_sum : (![0, 0, 0] : Fin 3 → ZMod 2) + ![1, 0, 0] + ![0, 1, 0] = ![1, 1, 0] := by
  decide

theorem sqrt_two_ne_zero_C : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)

/-- **`CCZ` then H.** The output of H at bit `2` on `Kccz` is no height-zero record: its support is
not a coset. -/
theorem residual_ccz :
    ¬ ∃ T : KernelState 3, amp (ofKernelState T) = walshTransform 2 (amp (ofKernelState Kccz)) :=
  not_exists_kernelState_of_not_affine (w := ![0, 0, 0]) (w' := ![1, 0, 0]) (w'' := ![0, 1, 0])
    (by rw [w14_000]; exact sqrt_two_ne_zero_C) (by rw [w14_100]; exact sqrt_two_ne_zero_C)
    (by rw [w14_010]; exact sqrt_two_ne_zero_C) (by rw [w14_sum, w14_110])

/-- The modulus obstruction is silent on `Kccz`: the pair at `0` along `e₂` has difference `0`. -/
theorem ccz_pair_collapse :
    2 * (DiagPhase.eval Kccz.q ((0 : Fin 3 → ZMod 2) + Pi.single 2 1) - DiagPhase.eval Kccz.q 0) =
      0 := by
  rw [eval_ccz, eval_ccz]
  decide

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_charOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_charOf

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_amp_ofKernelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_amp_ofKernelState

/-- info: 'FTQCLib.Frame.Walkthrough.support_of_amp_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_of_amp_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_kernelState_of_two_moduli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_kernelState_of_two_moduli

/-- info: 'FTQCLib.Frame.Walkthrough.support_ofKernelState_add_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_ofKernelState_add_add

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_kernelState_of_not_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_kernelState_of_not_affine

/-- info: 'FTQCLib.Frame.Walkthrough.update_zero_of_apply_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms update_zero_of_apply_zero

/-- info: 'FTQCLib.Frame.Walkthrough.update_one_of_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms update_one_of_apply_zero

/-- info: 'FTQCLib.Frame.Walkthrough.add_single_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_single_apply_self

/-- info: 'FTQCLib.Frame.Walkthrough.update_add_single_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms update_add_single_zero

/-- info: 'FTQCLib.Frame.Walkthrough.update_add_single_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms update_add_single_one

/-- info: 'FTQCLib.Frame.Walkthrough.signOf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signOf_zero

/-- info: 'FTQCLib.Frame.Walkthrough.signOf_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signOf_one

/-- info: 'FTQCLib.Frame.Walkthrough.walsh_ofKernelState_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walsh_ofKernelState_pair

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_one_add_of_normSq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_one_add_of_normSq_one

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_one_sub_of_normSq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_one_sub_of_normSq_one

/-- info: 'FTQCLib.Frame.Walkthrough.mul_self_eq_neg_one_of_re_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_self_eq_neg_one_of_re_zero

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charOf_residual

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_pair_ne_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_pair_ne_of_residual

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_kernelState_walsh_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_kernelState_walsh_of_residual

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_kernelState_applyHFiner_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_kernelState_applyHFiner_of_residual

/-- info: 'FTQCLib.Frame.Walkthrough.KT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KT

/-- info: 'FTQCLib.Frame.Walkthrough.KT_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KT_diff

/-- info: 'FTQCLib.Frame.Walkthrough.KT_not_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KT_not_collapse

/-- info: 'FTQCLib.Frame.Walkthrough.KT_not_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KT_not_rotate

/-- info: 'FTQCLib.Frame.Walkthrough.residual_KT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_KT

/-- info: 'FTQCLib.Frame.Walkthrough.xSupported_lagX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xSupported_lagX

/-- info: 'FTQCLib.Frame.Walkthrough.residual_KT_applyHFiner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_KT_applyHFiner

/-- info: 'FTQCLib.Frame.Walkthrough.KX_diff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KX_diff_zero

/-- info: 'FTQCLib.Frame.Walkthrough.exists_kernelState_walsh_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_kernelState_walsh_KX

/-- info: 'FTQCLib.Frame.Walkthrough.Kccz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kccz

/-- info: 'FTQCLib.Frame.Walkthrough.eval_ccz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_ccz

/-- info: 'FTQCLib.Frame.Walkthrough.amp_Kccz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_Kccz

/-- info: 'FTQCLib.Frame.Walkthrough.w14_000' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms w14_000

/-- info: 'FTQCLib.Frame.Walkthrough.w14_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms w14_100

/-- info: 'FTQCLib.Frame.Walkthrough.w14_010' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms w14_010

/-- info: 'FTQCLib.Frame.Walkthrough.w14_110' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms w14_110

/-- info: 'FTQCLib.Frame.Walkthrough.w14_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms w14_sum

/-- info: 'FTQCLib.Frame.Walkthrough.sqrt_two_ne_zero_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sqrt_two_ne_zero_C

/-- info: 'FTQCLib.Frame.Walkthrough.residual_ccz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms residual_ccz

/-- info: 'FTQCLib.Frame.Walkthrough.ccz_pair_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ccz_pair_collapse

end FTQCLib.Frame.Walkthrough

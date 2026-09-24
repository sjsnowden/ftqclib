/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardElimination
import FTQCLib.Examples.CarrierStateCheck
import FTQCLib.Examples.CarrierStateHadamardCheck
import FTQCLib.Examples.DyadicCharacterCheck

/-!
# Check: the eliminating H

Axiom rows for every declaration of `HadamardElimination`, and worked examples of the main theorem.

## Examples

* **`KX`**, the uniform record on one register at `m = 1` (support `{0, 1}`, exponent `0`; the
  `X` reader, `g.Z 0 = 0`): collapse with `ε = 0`; the image is a floor at height `0` with
  Lagrangian `⟨Z₀⟩`, support `{0}`, amplitude `√2` at `0` and `0` at `1`.
* **`KM`**, the signed record at `m = 1` (support `{0, 1}`, exponent `X₀`, the sign `(−1)^{x₀}`):
  the exponent law reads `κ = 1`, so `ε = 1`; the offset moves to `e₀`, the support is `{1}`, the
  amplitude `√2` at `1` and `0` at `0`.
* **`KS`**, the uniform record then `S` at `m = 2` (exponent `X₀`, Lagrangian `⟨Y₀⟩`): the `Y`
  reader has `g.Z 0 = 1`, so rotate with `a = 1`; the output exponent is `3·X₀`, the scale
  `(1 + i)/√2`, the amplitudes `(1 + i)/√2` and `(1 − i)/√2`; the `Y` sign flips.
* **`KZ`**, the record on `{0}` (Lagrangian `⟨Z₀⟩`): bit `0` is not X-supported, no reader,
  neither alignment; the raise branch.
* The T-then-H record at `m = 3`, a value at height one: the adjoined difference takes the
  values `1, 5`, in neither shape (`not_signAffine_T`, `not_rotateData_T`; the rows are `rw`
  evaluations at the word `0`, so they are not vacuous).
* The non-affine rotate at `n = 3, m = 2`: exponent `X₀ + 2·X₀X₁X₂` on the all-`X`
  Lagrangian, aligned by the shear `zShear 0 e₀`, eliminated by rotate with `Λ = X₀ ⊕ X₁X₂`; the
  output exponent takes the value `3`.
* **`KY`**, the stale Lagrangian `⟨Y₀⟩` under the uniform amplitude: the collapse alignment at
  the `X` datum does not hold, and the collapse eliminator's amplitude disagrees with the Walsh
  transform at the word `1` — the alignment hypothesis is load-bearing.
* The support presentations `x₀'' + π_X L''` on `KX` and `KM`.

`decide` cannot run through `DiagPhase.eval`; every evaluation row is an `rw` row over the cases
of the bits.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer Module

/-! ## Evaluation helpers -/

/-- `castAdd 0` is the identity. -/
theorem castAdd_zero_eq {N : ℕ} (k : Fin N) : Fin.castAdd 0 k = k := Fin.ext rfl

/-- The zero exponent evaluates to `0`. -/
theorem eval_zero_diag {N m : ℕ} (v : Fin N → ZMod 2) :
    DiagPhase.eval (0 : DiagPhase N m) v = 0 := by
  unfold DiagPhase.eval
  rw [map_zero]

/-- A variable evaluates to its bit. -/
theorem eval_X_diag {N m : ℕ} (i : Fin N) (v : Fin N → ZMod 2) :
    DiagPhase.eval (MvPolynomial.X i : DiagPhase N m) v = ((v i).val : ZMod (2 ^ m)) := by
  unfold DiagPhase.eval DiagPhase.liftBinary
  rw [MvPolynomial.eval_X]

theorem signOf_zero' : signOf 0 = 1 := if_pos rfl

theorem signOf_one' : signOf 1 = -1 := if_neg one_ne_zero

/-- The adjoined difference of `X₀` at precision `m`: `1 + 2^{m−1}·w₀`. -/
theorem lastDiff_hSumExp_X {m : ℕ} (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) :
    (lastDiff (hSumExp (h := 0) (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) m))).eval
        (Fin.append w y) =
      1 + (2 : ZMod (2 ^ m)) ^ (m - 1) * ((w 0).val : ZMod (2 ^ m)) := by
  rw [lastDiff_hSumExp, append_fin0, castAdd_zero_eq]
  unfold funcDerivEval funcDeriv
  rw [eval_X_diag, eval_X_diag, Pi.add_apply, Function.update_self, Pi.single_eq_same, zero_add,
    show ((1 : ZMod 2).val : ℕ) = 1 by decide, ZMod.val_zero, Nat.cast_one, Nat.cast_zero,
    sub_zero]

/-- The adjoined difference of the flat exponent at `m = 1`: the bit itself. -/
theorem lastDiff_hSumExp_flat (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) :
    (lastDiff (hSumExp (h := 0) (0 : Fin 1) (0 : DiagPhase (1 + 0) 1))).eval (Fin.append w y) =
      ((w 0).val : ZMod (2 ^ 1)) := by
  rw [lastDiff_hSumExp, append_fin0, castAdd_zero_eq]
  unfold funcDerivEval funcDeriv
  rw [eval_zero_diag, eval_zero_diag, sub_zero, zero_add, Nat.sub_self, pow_zero, one_mul]

/-! ## The datum on the reader shapes -/

/-- The `X` reader's datum is `e₀`. -/
theorem floorSigma_X : floorSigma (0 : Fin 1) (paulix 0) = Pi.single 0 1 := by decide

/-- The `Y` reader's datum is `e₀` as well: `1 + g.Z 0 = 0` kills the correction. -/
theorem floorSigma_Y : floorSigma (0 : Fin 1) (paulix 0 + pauliz 0) = Pi.single 0 1 := by decide

/-- A two-bit datum: the reader `X₀Z₁` at bit `0` has datum `e₀ + e₁`. -/
theorem floorSigma_XZ :
    floorSigma (0 : Fin 2) (paulix 0 + pauliz 1) = Pi.single 0 1 + Pi.single 1 1 := by decide

/-! ## The bit and the reader numerals (the trichotomy at `m = 1, 2`) -/

/-- Collapse residues at `m = 2`. -/
theorem two_mul_eq_zero_iff_m2 : ∀ κ : ZMod (2 ^ 2), 2 * κ = 0 ↔ κ = 0 ∨ κ = 2 := by decide

/-- Rotate residues at `m = 2`. -/
theorem two_mul_eq_two_iff_m2 : ∀ κ : ZMod (2 ^ 2), 2 * κ = 2 ↔ κ = 1 ∨ κ = 3 := by decide

/-- The bit is forced by the residue. -/
theorem bit_forced_m2 :
    ∀ ε : ZMod 2, (2 : ZMod (2 ^ 2)) ^ (2 - 1) * ((ε.val : ℕ) : ZMod (2 ^ 2)) = 2 ↔ ε = 1 := by
  decide

/-- No rotate residue at `m = 1`. -/
theorem no_rotate_kappa_m1 : ¬ ∃ κ : ZMod (2 ^ 1), 2 * κ = (2 : ZMod (2 ^ 1)) ^ (1 - 1) := by
  decide

/-- `exists_bit_of_two_mul_eq_zero` at `m = 2`, `κ = 2`: the bit is `1`. -/
theorem bit_of_two_m2 :
    ∃ ε : ZMod 2,
      (2 : ZMod (2 ^ 2)) = (2 : ZMod (2 ^ 2)) ^ (2 - 1) * ((ε.val : ℕ) : ZMod (2 ^ 2)) :=
  exists_bit_of_two_mul_eq_zero (by decide) (by decide)

/-! ## `KX`: the uniform record on one register at `m = 1` -/

/-- The `X` reader on `⟨X⟩`. -/
theorem isReader_X : IsReader lagX 0 (paulix 0) :=
  ⟨Submodule.mem_span_singleton_self _, rfl⟩

/-- Collapse alignment on `⟨X⟩` at the `X` datum. -/
theorem alignedCollapse_lagX : AlignedCollapse lagX 0 (floorSigma 0 (paulix 0)) :=
  alignedCollapse_floorSigma isReader_X rfl

/-- The collapse shape on the uniform record `KX` with `ε = 0`, computed directly. -/
theorem signAffine_KX :
    SignAffine (h := 0) (hSumExp (h := 0) (0 : Fin 1) (0 : DiagPhase (1 + 0) 1)) lagX 0
      (floorSigma 0 (paulix 0)) 0 := by
  intro w _ y
  rw [lastDiff_hSumExp_flat, floorSigma_X, zero_add, dotF2_single_left, Nat.sub_self, pow_zero,
    one_mul]

/-- The eliminating H on the uniform record `KX`. -/
noncomputable def hKX : KernelSumState 1 :=
  hElimCollapse 0 (floorSigma 0 (paulix 0)) 0 (ofKernelState KX)

/-- `hKX` is a floor (through `isFloor_hElimCollapse`). -/
theorem isFloor_hKX : IsFloor hKX :=
  isFloor_hElimCollapse 0 (ofKernelState KX) isFloor_KX (floorSigma_apply_self 0 _)
    alignedCollapse_lagX signAffine_KX

/-- `h` back to `0`. -/
theorem hKX_h : hKX.h = 0 := rfl

/-- On `KX`, the output amplitude is the Walsh transform of the input amplitude. -/
theorem amp_hKX : amp hKX = walshTransform 0 (amp (ofKernelState KX)) :=
  amp_hElimCollapse 0 (ofKernelState KX) le_rfl (floorSigma_apply_self 0 _) alignedCollapse_lagX
    isCarrier_KX.2.1 signAffine_KX

/-- The Walsh transform of the uniform amplitude at `0`. -/
theorem walsh_KX_zero : walshTransform 0 (amp (ofKernelState KX)) 0 = Real.sqrt 2 := by
  unfold walshTransform
  rw [amp_KX, amp_KX, Pi.zero_apply, signOf_zero', one_mul, one_add_one_eq_two]
  exact one_div_sqrt_two_mul_two

/-- The Walsh transform of the uniform amplitude at `1`. -/
theorem walsh_KX_one : walshTransform 0 (amp (ofKernelState KX)) (Pi.single 0 1) = 0 := by
  unfold walshTransform
  rw [amp_KX, amp_KX, Pi.single_eq_same, signOf_one']
  ring

/-- `hKX`: the amplitude at `0` is `√2`. -/
theorem amp_hKX_zero : amp hKX 0 = Real.sqrt 2 := by
  rw [amp_hKX, walsh_KX_zero]

/-- `hKX`: the amplitude at `1` is `0`. -/
theorem amp_hKX_one : amp hKX (Pi.single 0 1) = 0 := by
  rw [amp_hKX, walsh_KX_one]

/-- The swap at bit `0` sends `X` to `Z`. -/
theorem pauliSwapOn_paulix : pauliSwapOn {(0 : Fin 1)} (paulix 0) = pauliz 0 := by
  ext i <;> fin_cases i <;> decide

/-- `hKX`: the Lagrangian is `⟨Z₀⟩`. -/
theorem hKX_L : hKX.L = Submodule.span (ZMod 2) {pauliz 0} := by
  change Submodule.map (pauliSwapOn {0}) lagX = _
  rw [lagX, Submodule.map_span, Set.image_singleton, pauliSwapOn_paulix]

/-- `hKX`: the presented support is `{0}`. -/
theorem support_hKX (w : Fin 1 → ZMod 2) : (∃ p ∈ hKX.L, w = hKX.x₀ + p.X) ↔ w = 0 := by
  change (∃ p ∈ (hElimCollapse 0 (floorSigma 0 (paulix 0)) 0 (ofKernelState KX)).L,
      w = (hElimCollapse 0 (floorSigma 0 (paulix 0)) 0 (ofKernelState KX)).x₀ + p.X) ↔ _
  rw [support_hElimCollapse 0 0 (ofKernelState KX) (floorSigma_apply_self 0 _) alignedCollapse_lagX
    isCarrier_KX.2.1, floorSigma_X, dotF2_single_left, zero_add]
  constructor
  · rintro ⟨-, h0⟩
    funext i
    fin_cases i
    exact h0
  · rintro rfl
    exact ⟨lagX_support 0, rfl⟩

/-! ## `KM`: the signed record at `m = 1` -/

/-- The signed record: exponent `X₀` at `m = 1` on `⟨X⟩` (the sign `(−1)^{x₀}` on `{0, 1}`). -/
noncomputable def KM : KernelState 1 := ⟨1, MvPolynomial.X 0, 1, lagX, 0⟩

/-- `KM` denotes `(−1)^{w₀}`. -/
theorem amp_KM (w : Fin 1 → ZMod 2) : amp (ofKernelState KM) w = charOf 1 ((w 0).val) := by
  rw [amp_ofKernelState_pos KM (lagX_support w)]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 1) w) = _
  rw [eval_X_diag, one_mul]

/-- `KM` is a carrier. -/
theorem isCarrier_KM : IsCarrier (ofKernelState KM) := by
  refine ⟨le_rfl, isStabilizer_span_singleton (paulix 0),
    orthogonal_le_of_lagrangian (isStabilizer_span_singleton (paulix 0))
      (finrank_span_singleton (by decide)), ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [amp_KM] at h0
  exact charOf_ne_zero _ _ h0

/-- The exponent law on `KM`: the defect along `a·X` is `a`. -/
theorem shiftLaw_KM : ShiftLaw KM := by
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {paulix 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨((a.val : ℕ) : ZMod (2 ^ 1)), ?_⟩
  intro w _
  simp only [KM]
  rw [eval_X_diag, eval_X_diag, zDot_smul_paulix]
  simp only [X_smul, paulix, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0] <;> decide

/-- `KM` is a floor. -/
theorem isFloor_KM : IsFloor (ofKernelState KM) :=
  (isFloor_iff_shiftLaw KM isCarrier_KM).mpr shiftLaw_KM

/-- The collapse shape on `KM` with `ε = 1`, computed directly. -/
theorem signAffine_KM :
    SignAffine (h := 0) (hSumExp (h := 0) (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) 1))
      lagX 0 (floorSigma 0 (paulix 0)) 1 := by
  intro w _ y
  rw [lastDiff_hSumExp_X, floorSigma_X, dotF2_single_left]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0] <;> decide

/-- The eliminating H on `KM`. -/
noncomputable def hKM : KernelSumState 1 :=
  hElimCollapse 0 (floorSigma 0 (paulix 0)) 1 (ofKernelState KM)

/-- `hKM` is a floor. -/
theorem isFloor_hKM : IsFloor hKM :=
  isFloor_hElimCollapse 0 (ofKernelState KM) isFloor_KM (floorSigma_apply_self 0 _)
    alignedCollapse_lagX signAffine_KM

/-- `hKM`: the offset moves to `e₀`. -/
theorem hKM_x₀ : hKM.x₀ = Pi.single 0 1 := by
  change (0 : Fin 1 → ZMod 2) + (1 + dotF2 (floorSigma 0 (paulix 0)) 0) •
    (Pi.single 0 1 : Fin 1 → ZMod 2) = _
  rw [floorSigma_X, dotF2_single_left, Pi.zero_apply, add_zero, one_smul, zero_add]

/-- On `KM`, the output amplitude is the Walsh transform of the input amplitude. -/
theorem amp_hKM : amp hKM = walshTransform 0 (amp (ofKernelState KM)) :=
  amp_hElimCollapse 0 (ofKernelState KM) le_rfl (floorSigma_apply_self 0 _) alignedCollapse_lagX
    isCarrier_KM.2.1 signAffine_KM

/-- The Walsh transform of `(−1)^{w₀}` at `0`. -/
theorem walsh_KM_zero : walshTransform 0 (amp (ofKernelState KM)) 0 = 0 := by
  unfold walshTransform
  rw [amp_KM, amp_KM, Pi.zero_apply, signOf_zero', Function.update_self, Function.update_self,
    ZMod.val_zero, Nat.cast_zero, charOf_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    Nat.cast_one, charOf_one_one]
  ring

/-- The Walsh transform of `(−1)^{w₀}` at `1`. -/
theorem walsh_KM_one :
    walshTransform 0 (amp (ofKernelState KM)) (Pi.single 0 1) = Real.sqrt 2 := by
  unfold walshTransform
  rw [amp_KM, amp_KM, Pi.single_eq_same, signOf_one', Function.update_self, Function.update_self,
    ZMod.val_zero, Nat.cast_zero, charOf_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    Nat.cast_one, charOf_one_one, neg_one_mul, neg_neg, one_add_one_eq_two]
  exact one_div_sqrt_two_mul_two

/-- `hKM`: the amplitude at `0` is `0`. -/
theorem amp_hKM_zero : amp hKM 0 = 0 := by
  rw [amp_hKM, walsh_KM_zero]

/-- `hKM`: the amplitude at `1` is `√2`. -/
theorem amp_hKM_one : amp hKM (Pi.single 0 1) = Real.sqrt 2 := by
  rw [amp_hKM, walsh_KM_one]

/-- `hKM`: the presented support is `{1}`. -/
theorem support_hKM (w : Fin 1 → ZMod 2) :
    (∃ p ∈ hKM.L, w = hKM.x₀ + p.X) ↔ w = Pi.single 0 1 := by
  change (∃ p ∈ (hElimCollapse 0 (floorSigma 0 (paulix 0)) 1 (ofKernelState KM)).L,
      w = (hElimCollapse 0 (floorSigma 0 (paulix 0)) 1 (ofKernelState KM)).x₀ + p.X) ↔ _
  rw [support_hElimCollapse 0 1 (ofKernelState KM) (floorSigma_apply_self 0 _) alignedCollapse_lagX
    isCarrier_KM.2.1, floorSigma_X, dotF2_single_left]
  have key : ∀ a : ZMod 2, 1 + a = 0 ↔ a = 1 := by decide
  rw [key]
  constructor
  · rintro ⟨-, h1⟩
    funext i
    fin_cases i
    exact h1
  · rintro rfl
    exact ⟨lagX_support _, by rw [Pi.single_eq_same]⟩

/-! ## `KS`: the uniform record then `S` at `m = 2` -/

/-- The uniform record after `S`: exponent `X₀` at `m = 2` on `⟨Y₀⟩`. -/
noncomputable def KS : KernelState 1 := ⟨2, MvPolynomial.X 0, 1, lagY, 0⟩

/-- `KS` denotes `i^{w₀}`. -/
theorem amp_KS (w : Fin 1 → ZMod 2) : amp (ofKernelState KS) w = charOf 2 ((w 0).val) := by
  rw [amp_ofKernelState_pos KS (lagY_support w)]
  change (1 : ℂ) * charOf 2 (DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 2) w) = _
  rw [eval_X_diag, one_mul]

/-- `KS` is a carrier. -/
theorem isCarrier_KS : IsCarrier (ofKernelState KS) := by
  refine ⟨by decide, isStabilizer_span_singleton (paulix 0 + pauliz 0),
    orthogonal_le_of_lagrangian (isStabilizer_span_singleton (paulix 0 + pauliz 0))
      (finrank_span_singleton (by decide)), ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [amp_KS] at h0
  exact charOf_ne_zero _ _ h0

/-- `zDot` against a multiple of `Y` reads the bit. -/
theorem zDot_smul_pauliy (a : ZMod 2) (v : Fin 1 → ZMod 2) :
    zDot (a • (paulix 0 + pauliz 0)) v = a.val * (v 0).val := by
  simp [zDot, paulix, pauliz]

/-- The exponent law on `KS`: the defect along `a·Y` is `a`. -/
theorem shiftLaw_KS : ShiftLaw KS := by
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {paulix 0 + pauliz 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨((a.val : ℕ) : ZMod (2 ^ 2)), ?_⟩
  intro w _
  simp only [KS]
  rw [eval_X_diag, eval_X_diag, zDot_smul_pauliy]
  simp only [X_add, X_smul, paulix, pauliz, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one, add_zero]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0] <;> decide

/-- `KS` is a floor. -/
theorem isFloor_KS : IsFloor (ofKernelState KS) :=
  (isFloor_iff_shiftLaw KS isCarrier_KS).mpr shiftLaw_KS

/-- The `Y` reader on `⟨Y⟩`. -/
theorem isReader_Y : IsReader lagY 0 (paulix 0 + pauliz 0) :=
  ⟨Submodule.mem_span_singleton_self _, by decide⟩

/-- Rotate alignment on `⟨Y⟩`: the reader has `g.Z 0 = 1`. -/
theorem alignedRotate_lagY : AlignedRotate lagY 0 := ⟨_, isReader_Y, by decide⟩

/-- The rotate shape on `KS` with `a = 1` and `Λ = X₀`, computed directly. -/
theorem rotateData_KS :
    RotateData (h := 0) (hSumExp (h := 0) (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) 2))
      lagY 0 1 (xorForm (h := 0) (m := 2) (Pi.single 0 1) 0) := by
  refine ⟨by decide, fun w _ y => ⟨w 0, ?_, ?_⟩⟩
  · rw [xorForm_eval, zero_add]
    have hfun : (fun j => Fin.append w y (Fin.castAdd 0 j)) = w :=
      funext fun j => Fin.append_left w y j
    rw [hfun, dotF2_single_left]
  · rw [lastDiff_hSumExp_X]

/-- The eliminating H on `KS`. -/
noncomputable def hKS : KernelSumState 1 :=
  hElimRotate 0 (ofKernelState KS) 1 (xorForm (h := 0) (m := 2) (Pi.single 0 1) 0)

/-- `hKS` is a floor. -/
theorem isFloor_hKS : IsFloor hKS :=
  isFloor_hElimRotate 0 (ofKernelState KS) isFloor_KS alignedRotate_lagY rotateData_KS

/-- `h` back to `0`. -/
theorem hKS_h : hKS.h = 0 := rfl

/-- On `KS`, the output amplitude is the Walsh transform of the input amplitude. -/
theorem amp_hKS : amp hKS = walshTransform 0 (amp (ofKernelState KS)) :=
  amp_hElimRotate 0 (ofKernelState KS) (by decide) alignedRotate_lagY rotateData_KS

/-- `hKS`: the scale is `(1 + i)/√2`. -/
theorem hKS_c : hKS.c = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  change (1 : ℂ) * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ) = _
  rw [charOf_two_one, one_mul]

/-- `hKS`: the output exponent, as the explicit polynomial, is `3·X₀`. -/
theorem eval_hKS_exponent (w : Fin (1 + 0) → ZMod 2) :
    (snocFreeze 0 (hSumExp (h := 0) 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 2)) +
        MvPolynomial.C (-1) * xorForm (h := 0) (m := 2) (Pi.single 0 1) 0).eval w =
      3 * ((w 0).val : ZMod (2 ^ 2)) := by
  rw [eval_add, eval_mul, eval_C, snocFreeze_eval, hSumExp_eval, xorForm_eval, zero_add]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [eval_X, castAdd_zero_eq, Function.update_self, ZMod.val_zero, Nat.cast_zero, mul_zero,
    add_zero]
  have hfun : (fun j => w (Fin.castAdd 0 j)) = w := funext fun j => rfl
  rw [hfun, dotF2_single_left]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0] <;> decide

/-- `hKS`: the record's exponent is that polynomial. -/
theorem eval_hKS_Q (w : Fin (1 + 0) → ZMod 2) :
    DiagPhase.eval (n := 1 + 0) (m := 2) hKS.Q w = 3 * ((w 0).val : ZMod (2 ^ 2)) :=
  eval_hKS_exponent w

/-- `hKS`: the amplitude at `0` is `(1 + i)/√2`. -/
theorem amp_hKS_zero : amp hKS 0 = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [amp_hKS]
  unfold walshTransform
  rw [amp_KS, amp_KS, Pi.zero_apply, signOf_zero', Function.update_self, Function.update_self,
    ZMod.val_zero, Nat.cast_zero, charOf_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    Nat.cast_one, charOf_two_one]
  ring

/-- `hKS`: the amplitude at `1` is `(1 − i)/√2`. -/
theorem amp_hKS_one : amp hKS (Pi.single 0 1) = (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [amp_hKS]
  unfold walshTransform
  rw [amp_KS, amp_KS, Pi.single_eq_same, signOf_one', Function.update_self, Function.update_self,
    ZMod.val_zero, Nat.cast_zero, charOf_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    Nat.cast_one, charOf_two_one]
  ring

/-- The swap at bit `0` fixes `Y`. -/
theorem pauliSwapOn_pauliy :
    pauliSwapOn {(0 : Fin 1)} (paulix 0 + pauliz 0) = paulix 0 + pauliz 0 := by
  ext i <;> fin_cases i <;> decide

/-- `Y` is in `⟨Y⟩`. -/
theorem pauliy_mem_lagY' : (paulix 0 + pauliz 0 : Pauli 1) ∈ lagY :=
  Submodule.mem_span_singleton_self _

/-- The defect of `KS` along `Y` is `1`. -/
theorem defect_KS (w : Fin 1 → ZMod 2) (_ : ∃ p ∈ KS.L, w = KS.x₀ + p.X) :
    DiagPhase.eval KS.q (w + (paulix 0 + pauliz 0 : Pauli 1).X) - DiagPhase.eval KS.q w -
      (2 : ZMod (2 ^ KS.m)) ^ (KS.m - 1) *
        ((zDot (paulix 0 + pauliz 0 : Pauli 1) w : ℕ) : ZMod (2 ^ KS.m)) = 1 := by
  have h := shiftLaw_KS
  simp only [KS]
  have h1 := zDot_smul_pauliy 1 w
  rw [one_smul] at h1
  rw [eval_X_diag, eval_X_diag, h1]
  simp only [X_add, paulix, pauliz, Pi.add_apply, Pi.single_eq_same, add_zero]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0] <;> decide

/-- `Y` fixes `amp KS`: the scalar `i·(−1)·i = 1`. -/
theorem pauliAct_Y_KS :
    pauliAct (paulix 0 + pauliz 0 : Pauli 1) (amp (ofKernelState KS)) = amp (ofKernelState KS) := by
  rw [pauliAct_amp_ofKernelState_of_defect KS (by decide) pauliy_mem_lagY' defect_KS]
  have hy : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have h2 : charOf KS.m 1 = Complex.I := charOf_two_one
  funext w
  rw [hy, h2, pow_one, pow_one]
  linear_combination (-(amp (ofKernelState KS) w)) * Complex.I_sq

/-- **The `Y` sign under H.** Under H the `Y` sign flips: `Y` acts on `amp hKS` by `−1`. -/
theorem pauliAct_Y_hKS :
    pauliAct (paulix 0 + pauliz 0 : Pauli 1) (amp hKS) = fun w => -1 * amp hKS w := by
  rw [amp_hKS]
  conv_lhs => rw [← pauliSwapOn_pauliy]
  rw [pauliAct_pauliSwapOn_walshTransform, pauliAct_Y_KS]
  funext w
  have hx : ((paulix 0 + pauliz 0 : Pauli 1).X 0).val *
      ((paulix 0 + pauliz 0 : Pauli 1).Z 0).val = 1 := by
    decide
  rw [hx, pow_one]

/-! ## `KZ`: the record on `{0}`, the raise branch -/

/-- Bit `0` of `⟨Z₀⟩` is not X-supported. -/
theorem not_xSupported_lagZ : (Pi.single 0 1 : Fin 1 → ZMod 2) ∉ Submodule.map xProj lagZ := by
  rintro ⟨p, hp, hpX⟩
  change p ∈ Submodule.span (ZMod 2) {pauliz 0} at hp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  have h0 := congrFun hpX 0
  simp [pauliz] at h0

/-- No reader at bit `0` on `⟨Z₀⟩`. -/
theorem no_reader_lagZ : ¬ ∃ g, IsReader lagZ 0 g :=
  fun h => not_xSupported_lagZ ((exists_reader_iff lagZ 0).mp h)

/-- Neither alignment on `⟨Z₀⟩`. -/
theorem not_aligned_lagZ :
    ¬ AlignedRotate lagZ 0 ∧ ∀ σ : Fin 1 → ZMod 2, ¬ AlignedCollapse lagZ 0 σ :=
  ⟨fun h => not_xSupported_lagZ (single_mem_of_alignedRotate h),
    fun _ h => not_xSupported_lagZ (single_mem_of_alignedCollapse h)⟩

/-- `hadamard_floor_total` on `KZ` reaches its floor image through the raise branch. -/
theorem hadamard_floor_total_KZ :
    ∃ T : KernelSumState 1, IsFloor T ∧ T.h = 0 ∧ T.L = Submodule.map (pauliSwapOn {0}) lagZ ∧
      amp T = walshTransform 0 (amp (ofKernelState KZ)) :=
  hadamard_floor_total_kernelState KZ isFloor_KZ 0

/-! ## The T-then-H record at `m = 3`, a value at height one -/

/-- The T-state exponent `X₀` at `m = 3` is in the collapse shape for no datum. -/
theorem not_signAffine_T (σ : Fin 1 → ZMod 2) (ε : ZMod 2) :
    ¬ SignAffine (h := 0) (hSumExp (h := 0) (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
      lagX 0 σ ε := by
  intro h
  have h0 := h 0 (lagX_support 0) Fin.elim0
  rw [lastDiff_hSumExp_X, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at h0
  have key : ∀ b : ZMod 2,
      (1 : ZMod (2 ^ 3)) ≠ (2 : ZMod (2 ^ 3)) ^ (3 - 1) * ((b.val : ℕ) : ZMod (2 ^ 3)) := by
    decide
  exact key _ h0

/-- The T-state exponent `X₀` at `m = 3` is in the rotate shape for no residue and no `Λ`. -/
theorem not_rotateData_T (a : ZMod (2 ^ 3)) (Λ : DiagPhase (1 + 0) 3) :
    ¬ RotateData (h := 0) (hSumExp (h := 0) (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
      lagX 0 a Λ := by
  rintro ⟨ha, h⟩
  obtain ⟨b, -, hb⟩ := h 0 (lagX_support 0) Fin.elim0
  rw [lastDiff_hSumExp_X, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at hb
  have key : ∀ a : ZMod (2 ^ 3), ∀ b : ZMod 2, 2 * a = (2 : ZMod (2 ^ 3)) ^ (3 - 1) →
      (1 : ZMod (2 ^ 3)) = a + (2 : ZMod (2 ^ 3)) ^ (3 - 1) * ((b.val : ℕ) : ZMod (2 ^ 3)) →
      False := by
    decide
  exact key a b ha hb

/-! ## The non-affine rotate at `n = 3, m = 2` -/

/-- The all-`X` Lagrangian on three bits, constraint-presented. -/
def lagXXX : Submodule (ZMod 2) (Pauli 3) where
  carrier := {p | p.Z = 0}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [Z_add, hp, hq, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Z_smul, hp, smul_zero]

/-- Every word is on its support at the origin. -/
theorem lagXXX_support (w : Fin 3 → ZMod 2) : ∃ p ∈ lagXXX, w = (0 : Fin 3 → ZMod 2) + p.X :=
  ⟨⟨w, 0⟩, rfl, by rw [zero_add]⟩

/-- The all-`X` Lagrangian is isotropic. -/
theorem isStabilizer_lagXXX : IsStabilizer lagXXX := by
  intro p hp q hq
  change p.Z = 0 at hp
  change q.Z = 0 at hq
  rw [omega_eq_dotF2, hp, hq]
  unfold dotF2
  simp

/-- The `X₀` reader on the all-`X` Lagrangian. -/
theorem isReader_XXX : IsReader lagXXX 0 (paulix 0) := ⟨rfl, rfl⟩

/-- The sheared Lagrangian, aligned for rotate at bit `0`. -/
def lagXXX' : Submodule (ZMod 2) (Pauli 3) :=
  Submodule.map (zShear 0 (Pi.single 0 1)) lagXXX

/-- The sheared Lagrangian is rotate-aligned at bit `0`. -/
theorem alignedRotate_lagXXX' : AlignedRotate lagXXX' 0 := by
  have h := alignedRotate_map_zShear_of_reader isReader_XXX
  rwa [show (1 + (paulix 0).Z 0) • (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single 0 1 by decide] at h

/-- Its support is still every word. -/
theorem lagXXX'_support (w : Fin 3 → ZMod 2) :
    ∃ p ∈ lagXXX', w = (0 : Fin 3 → ZMod 2) + p.X := by
  rw [mem_support_iff (⟨2, 0, 0, 1, lagXXX', 0⟩ : KernelSumState 3) w]
  change w - 0 ∈ Submodule.map xProj (Submodule.map (zShear 0 (Pi.single 0 1)) lagXXX)
  rw [map_xProj_map_zShear, ← mem_support_iff (⟨2, 0, 0, 1, lagXXX, 0⟩ : KernelSumState 3) w]
  exact lagXXX_support w

/-- The exponent `X₀ + 2·X₀X₁X₂` at `m = 2`. -/
noncomputable def q8 : DiagPhase 3 2 :=
  MvPolynomial.X 0 + MvPolynomial.C 2 * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)

theorem eval_q8 (v : Fin 3 → ZMod 2) :
    DiagPhase.eval q8 v = ((v 0).val : ZMod (2 ^ 2)) +
      2 * (((v 0).val : ZMod (2 ^ 2)) * ((v 1).val : ZMod (2 ^ 2)) *
        ((v 2).val : ZMod (2 ^ 2))) := by
  unfold q8 DiagPhase.eval DiagPhase.liftBinary
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The Boolean form `X₀ ⊕ X₁X₂`. -/
noncomputable def Λ8 : DiagPhase 3 2 :=
  MvPolynomial.X 0 + MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.C 2 * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)

theorem eval_Λ8 (v : Fin 3 → ZMod 2) :
    DiagPhase.eval Λ8 v = ((v 0).val : ZMod (2 ^ 2)) +
      ((v 1).val : ZMod (2 ^ 2)) * ((v 2).val : ZMod (2 ^ 2)) -
      2 * (((v 0).val : ZMod (2 ^ 2)) * ((v 1).val : ZMod (2 ^ 2)) *
        ((v 2).val : ZMod (2 ^ 2))) := by
  unfold Λ8 DiagPhase.eval DiagPhase.liftBinary
  simp only [map_add, map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The rotate shape on the non-affine exponent, with `a = 1` and `Λ = X₀ ⊕ X₁X₂`. -/
theorem rotateData_q8 :
    RotateData (h := 0) (hSumExp (h := 0) (0 : Fin 3) (q8 : DiagPhase (3 + 0) 2)) lagXXX' 0 1
      (Λ8 : DiagPhase (3 + 0) 2) := by
  refine ⟨by decide, fun w _ y => ⟨w 0 + w 1 * w 2, ?_, ?_⟩⟩
  · change DiagPhase.eval Λ8 (Fin.append w y) = _
    rw [append_fin0, eval_Λ8]
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_one (w 1) with h1 | h1 <;>
      rcases zmod_two_eq_zero_or_one (w 2) with h2 | h2 <;> rw [h0, h1, h2] <;> decide
  · rw [lastDiff_hSumExp, append_fin0, castAdd_zero_eq]
    unfold funcDerivEval funcDeriv
    rw [eval_q8, eval_q8]
    simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same,
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0),
      Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0),
      Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), add_zero, zero_add]
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_one (w 1) with h1 | h1 <;>
      rcases zmod_two_eq_zero_or_one (w 2) with h2 | h2 <;> rw [h0, h1, h2] <;> decide

/-- The sheared record. -/
noncomputable def K8 : KernelSumState 3 := ⟨2, 0, q8, 1, lagXXX', 0⟩

/-- The eliminating H on the sheared record. -/
noncomputable def hK8 : KernelSumState 3 := hElimRotate 0 K8 1 (Λ8 : DiagPhase (3 + 0) 2)

/-- The amplitude equation on the sheared record: the constructor fires on
the non-affine exponent. -/
theorem amp_hK8 : amp hK8 = walshTransform 0 (amp K8) :=
  amp_hElimRotate 0 K8 (by decide) alignedRotate_lagXXX' rotateData_q8

/-- The shear did not change the input's amplitude. -/
theorem amp_K8_eq : amp K8 = amp (⟨2, 0, q8, 1, lagXXX, 0⟩ : KernelSumState 3) :=
  amp_map_zShear (m := 2) (h := 0) q8 1 0 (Pi.single 0 1) lagXXX 0

/-- `h` stays `0`. -/
theorem hK8_h : hK8.h = 0 := rfl

/-- The sheared record's output exponent, as the explicit polynomial, at `(1, 0, 0)` is `3`. -/
theorem eval_hK8_exponent_100 :
    (snocFreeze 0 (hSumExp (h := 0) 0 (q8 : DiagPhase (3 + 0) 2)) +
        MvPolynomial.C (-1) * (Λ8 : DiagPhase (3 + 0) 2)).eval ![1, 0, 0] = 3 := by
  rw [eval_add, eval_mul, eval_C, snocFreeze_eval, hSumExp_eval]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [castAdd_zero_eq, eval_q8, eval_Λ8]
  decide

/-- The eliminated record's exponent at `(1, 0, 0)` is `3` — the constructor at a level-three
value. -/
theorem eval_hK8_Q_100 : DiagPhase.eval (n := 3 + 0) (m := 2) hK8.Q ![1, 0, 0] = 3 :=
  eval_hK8_exponent_100

/-! ## `KY`: the stale Lagrangian -/

/-- The collapse alignment does not hold on `⟨Y⟩` at the `X` datum (the reader is `Y`-type). -/
theorem not_alignedCollapse_lagY : ¬ AlignedCollapse lagY 0 (floorSigma 0 (paulix 0)) := by
  rw [floorSigma_X]
  intro h
  change (⟨Pi.single 0 1, Pi.single 0 1 + Pi.single 0 1⟩ : Pauli 1) ∈
    Submodule.span (ZMod 2) {paulix 0 + pauliz 0} at h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hx := congrArg (fun p : Pauli 1 => p.X 0) ha
  have hz := congrArg (fun p : Pauli 1 => p.Z 0) ha
  simp only [X_smul, Z_smul, X_add, Z_add, paulix, pauliz, Pi.smul_apply, Pi.add_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one, add_zero, zero_add] at hx hz
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · exact absurd hx (by decide)
  · exact absurd hz (by decide)

/-- The stale collapse record: the eliminator applied with the true stabilizer's datum on `⟨Y⟩`. -/
noncomputable def hKY : KernelSumState 1 :=
  hElimCollapse 0 (floorSigma 0 (paulix 0)) 0 (ofKernelState KY)

/-- Its support presents the word `1`. -/
theorem hKY_support_one : ∃ p ∈ hKY.L, (Pi.single 0 1 : Fin 1 → ZMod 2) = hKY.x₀ + p.X := by
  refine ⟨pauliSwapOn {0} (paulix 0 + pauliz 0), Submodule.mem_map_of_mem pauliy_mem_lagY', ?_⟩
  rw [pauliSwapOn_pauliy]
  change (Pi.single 0 1 : Fin 1 → ZMod 2) =
    (0 : Fin 1 → ZMod 2) + (0 + dotF2 (floorSigma 0 (paulix 0)) 0) •
      (Pi.single 0 1 : Fin 1 → ZMod 2) + (Pi.single 0 1 + 0)
  rw [floorSigma_X, dotF2_single_left, Pi.zero_apply, add_zero, zero_smul, zero_add, add_zero,
    zero_add]

/-- **Discriminating.** Without alignment the eliminator's amplitude at `1` is nonzero while the
Walsh transform of the uniform amplitude vanishes there: the alignment hypothesis of
`amp_hElimCollapse` is load-bearing. -/
theorem amp_hKY_ne :
    amp hKY (Pi.single 0 1) ≠ walshTransform 0 (amp (ofKernelState KY)) (Pi.single 0 1) := by
  have hw : walshTransform 0 (amp (ofKernelState KY)) (Pi.single 0 1) = 0 := by
    unfold walshTransform
    rw [amp_KY, amp_KY, Pi.single_eq_same, signOf_one']
    ring
  rw [hw, amp_pos hKY_support_one]
  change ampCore 1 0 _ ((Real.sqrt 2 : ℂ) * 1) _ ≠ 0
  rw [ampCore_zero]
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos))
    one_ne_zero) (Complex.exp_ne_zero _)

/-! ## The floor data read by the constructor -/

/-- `zDot` against `X` vanishes. -/
theorem zDot_paulix_zero (v : Fin 1 → ZMod 2) : zDot (paulix 0) v = 0 := by
  simp [zDot, paulix]

/-- The residue on `KX` along `X` is `0`. -/
theorem floorKappa_KX : floorKappa KX (paulix 0) = 0 := by
  unfold floorKappa
  simp only [KX]
  rw [eval_zero_poly, eval_zero_poly, zDot_paulix_zero]
  decide

/-- The collapse bit on `KX` is `0`. -/
theorem floorEps_KX : floorEps KX (paulix 0) = 0 := by
  unfold floorEps
  rw [if_pos floorKappa_KX]

/-- On `KX`, the constructor reproduces the hand-built record. -/
theorem hElimFloor_KX : hElimFloor 0 KX (paulix 0) = hKX := by
  unfold hElimFloor
  rw [if_pos (by decide : (paulix 0).Z 0 = 0), floorEps_KX]
  rfl

/-- The residue on `KM` along `X` is `1`. -/
theorem floorKappa_KM : floorKappa KM (paulix 0) = 1 := by
  unfold floorKappa
  simp only [KM]
  rw [eval_X_diag, eval_X_diag, zDot_paulix_zero]
  simp only [paulix, Pi.add_apply, Pi.single_eq_same, Pi.zero_apply, zero_add]
  decide

/-- The collapse bit on `KM` is `1`. -/
theorem floorEps_KM : floorEps KM (paulix 0) = 1 := by
  unfold floorEps
  rw [if_neg (by rw [floorKappa_KM]; decide)]

/-- On `KM`, the constructor reproduces the hand-built record. -/
theorem hElimFloor_KM : hElimFloor 0 KM (paulix 0) = hKM := by
  unfold hElimFloor
  rw [if_pos (by decide : (paulix 0).Z 0 = 0), floorEps_KM]
  rfl

/-- The residue on `KS` along `Y` is `1`. -/
theorem floorKappa_KS : floorKappa KS (paulix 0 + pauliz 0) = 1 :=
  defect_KS 0 (x₀_mem_support KS)

/-- On `KS`, the constructor reproduces the hand-built record. -/
theorem hElimFloor_KS : hElimFloor 0 KS (paulix 0 + pauliz 0) = hKS := by
  unfold hElimFloor
  rw [if_neg (by decide), floorKappa_KS, floorSigma_Y]
  rfl

/-- `KX` through `hFloor`: the output amplitude is the Walsh transform. -/
theorem amp_hFloor_KX : amp (hFloor 0 KX) = walshTransform 0 (amp (ofKernelState KX)) :=
  amp_hFloor isFloor_KX 0

/-- `KX` through `hFloor`: a floor at height `0`. -/
theorem isFloor_hFloor_KX : IsFloor (hFloor 0 KX) ∧ (hFloor 0 KX).h = 0 :=
  ⟨isFloor_hFloor isFloor_KX 0, hFloor_h 0 KX⟩

/-- `KZ` through `hFloor`, the raise branch: the output amplitude is the Walsh transform. -/
theorem amp_hFloor_KZ : amp (hFloor 0 KZ) = walshTransform 0 (amp (ofKernelState KZ)) :=
  amp_hFloor isFloor_KZ 0

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Frame.Walkthrough.update_zero_add_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms update_zero_add_single

/-- info: 'FTQCLib.Frame.Walkthrough.update_zero_eq_add_smul_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms update_zero_eq_add_smul_single

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_smul_left

/-- info: 'FTQCLib.Frame.Walkthrough.hSumExp_eval_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hSumExp_eval_snoc

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_hSumExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_hSumExp

/-- info: 'FTQCLib.Frame.Walkthrough.hElimCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.hElimRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.hElimCollapse_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimCollapse_m

/-- info: 'FTQCLib.Frame.Walkthrough.hElimCollapse_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimCollapse_h

/-- info: 'FTQCLib.Frame.Walkthrough.hElimCollapse_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimCollapse_L

/-- info: 'FTQCLib.Frame.Walkthrough.hElimCollapse_x₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimCollapse_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.hElimRotate_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimRotate_m

/-- info: 'FTQCLib.Frame.Walkthrough.hElimRotate_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimRotate_h

/-- info: 'FTQCLib.Frame.Walkthrough.hElimRotate_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimRotate_L

/-- info: 'FTQCLib.Frame.Walkthrough.hElimRotate_x₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimRotate_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.support_hElimCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_hElimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.support_hElimRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_hElimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hElimCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hElimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hElimRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hElimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_hElimCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_hElimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_hElimRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_hElimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hElimCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hElimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hElimRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hElimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_apply_self

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_add_single_of_Z_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_add_single_of_Z_zero

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_floorSigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_floorSigma

/-- info: 'FTQCLib.Frame.Walkthrough.alignedCollapse_floorSigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedCollapse_floorSigma

/-- info: 'FTQCLib.Hierarchy.exists_bit_of_two_mul_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_bit_of_two_mul_eq_zero

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_hSumExp_of_shiftLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_hSumExp_of_shiftLaw

/-- info: 'FTQCLib.Frame.Walkthrough.signAffine_of_shiftLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signAffine_of_shiftLaw

/-- info: 'FTQCLib.Frame.Walkthrough.rotateData_of_shiftLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotateData_of_shiftLaw

/-- info: 'FTQCLib.Frame.Walkthrough.exists_floor_hElim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_floor_hElim

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_floor_total_kernelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hadamard_floor_total_kernelState

/-- info: 'FTQCLib.Frame.Walkthrough.exists_kernelState_of_h_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_kernelState_of_h_eq_zero

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_floor_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hadamard_floor_total

/-- info: 'FTQCLib.Frame.Walkthrough.castAdd_zero_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms castAdd_zero_eq

/-- info: 'FTQCLib.Frame.Walkthrough.eval_zero_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_zero_diag

/-- info: 'FTQCLib.Frame.Walkthrough.eval_X_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_X_diag

/-- info: 'FTQCLib.Frame.Walkthrough.signOf_zero'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signOf_zero'

/-- info: 'FTQCLib.Frame.Walkthrough.signOf_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signOf_one'

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_hSumExp_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_hSumExp_X

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_hSumExp_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_hSumExp_flat

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_X

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_Y

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_XZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_XZ

/-- info: 'FTQCLib.Frame.Walkthrough.two_mul_eq_zero_iff_m2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_eq_zero_iff_m2

/-- info: 'FTQCLib.Frame.Walkthrough.two_mul_eq_two_iff_m2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_eq_two_iff_m2

/-- info: 'FTQCLib.Frame.Walkthrough.bit_forced_m2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bit_forced_m2

/-- info: 'FTQCLib.Frame.Walkthrough.no_rotate_kappa_m1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_rotate_kappa_m1

/-- info: 'FTQCLib.Frame.Walkthrough.bit_of_two_m2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bit_of_two_m2

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_X

/-- info: 'FTQCLib.Frame.Walkthrough.alignedCollapse_lagX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedCollapse_lagX

/-- info: 'FTQCLib.Frame.Walkthrough.signAffine_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signAffine_KX

/-- info: 'FTQCLib.Frame.Walkthrough.hKX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKX

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hKX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hKX

/-- info: 'FTQCLib.Frame.Walkthrough.hKX_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKX_h

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKX

/-- info: 'FTQCLib.Frame.Walkthrough.walsh_KX_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walsh_KX_zero

/-- info: 'FTQCLib.Frame.Walkthrough.walsh_KX_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walsh_KX_one

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKX_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKX_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKX_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKX_one

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_paulix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_paulix

/-- info: 'FTQCLib.Frame.Walkthrough.hKX_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKX_L

/-- info: 'FTQCLib.Frame.Walkthrough.support_hKX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_hKX

/-- info: 'FTQCLib.Frame.Walkthrough.KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KM

/-- info: 'FTQCLib.Frame.Walkthrough.amp_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_KM

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_KM

/-- info: 'FTQCLib.Frame.Walkthrough.shiftLaw_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftLaw_KM

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_KM

/-- info: 'FTQCLib.Frame.Walkthrough.signAffine_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signAffine_KM

/-- info: 'FTQCLib.Frame.Walkthrough.hKM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKM

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hKM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hKM

/-- info: 'FTQCLib.Frame.Walkthrough.hKM_x₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKM_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKM

/-- info: 'FTQCLib.Frame.Walkthrough.walsh_KM_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walsh_KM_zero

/-- info: 'FTQCLib.Frame.Walkthrough.walsh_KM_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walsh_KM_one

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKM_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKM_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKM_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKM_one

/-- info: 'FTQCLib.Frame.Walkthrough.support_hKM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_hKM

/-- info: 'FTQCLib.Frame.Walkthrough.KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KS

/-- info: 'FTQCLib.Frame.Walkthrough.amp_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_KS

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_KS

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_smul_pauliy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot_smul_pauliy

/-- info: 'FTQCLib.Frame.Walkthrough.shiftLaw_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftLaw_KS

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_KS

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_Y

/-- info: 'FTQCLib.Frame.Walkthrough.alignedRotate_lagY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedRotate_lagY

/-- info: 'FTQCLib.Frame.Walkthrough.rotateData_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotateData_KS

/-- info: 'FTQCLib.Frame.Walkthrough.hKS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKS

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hKS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hKS

/-- info: 'FTQCLib.Frame.Walkthrough.hKS_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKS_h

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKS

/-- info: 'FTQCLib.Frame.Walkthrough.hKS_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKS_c

/-- info: 'FTQCLib.Frame.Walkthrough.eval_hKS_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_hKS_exponent

/-- info: 'FTQCLib.Frame.Walkthrough.eval_hKS_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_hKS_Q

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKS_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKS_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKS_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKS_one

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_pauliy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_pauliy

/-- info: 'FTQCLib.Frame.Walkthrough.pauliy_mem_lagY'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliy_mem_lagY'

/-- info: 'FTQCLib.Frame.Walkthrough.defect_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms defect_KS

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_Y_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_Y_KS

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_Y_hKS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_Y_hKS

/-- info: 'FTQCLib.Frame.Walkthrough.not_xSupported_lagZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_xSupported_lagZ

/-- info: 'FTQCLib.Frame.Walkthrough.no_reader_lagZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_reader_lagZ

/-- info: 'FTQCLib.Frame.Walkthrough.not_aligned_lagZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_aligned_lagZ

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_floor_total_KZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hadamard_floor_total_KZ

/-- info: 'FTQCLib.Frame.Walkthrough.not_signAffine_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_signAffine_T

/-- info: 'FTQCLib.Frame.Walkthrough.not_rotateData_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_rotateData_T

/-- info: 'FTQCLib.Frame.Walkthrough.lagXXX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagXXX

/-- info: 'FTQCLib.Frame.Walkthrough.lagXXX_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagXXX_support

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_lagXXX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isStabilizer_lagXXX

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_XXX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_XXX

/-- info: 'FTQCLib.Frame.Walkthrough.lagXXX'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagXXX'

/-- info: 'FTQCLib.Frame.Walkthrough.alignedRotate_lagXXX'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedRotate_lagXXX'

/-- info: 'FTQCLib.Frame.Walkthrough.lagXXX'_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagXXX'_support

/-- info: 'FTQCLib.Frame.Walkthrough.q8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms q8

/-- info: 'FTQCLib.Frame.Walkthrough.eval_q8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_q8

/-- info: 'FTQCLib.Frame.Walkthrough.Λ8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Λ8

/-- info: 'FTQCLib.Frame.Walkthrough.eval_Λ8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_Λ8

/-- info: 'FTQCLib.Frame.Walkthrough.rotateData_q8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotateData_q8

/-- info: 'FTQCLib.Frame.Walkthrough.K8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K8

/-- info: 'FTQCLib.Frame.Walkthrough.hK8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hK8

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hK8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hK8

/-- info: 'FTQCLib.Frame.Walkthrough.amp_K8_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_K8_eq

/-- info: 'FTQCLib.Frame.Walkthrough.hK8_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hK8_h

/-- info: 'FTQCLib.Frame.Walkthrough.eval_hK8_exponent_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_hK8_exponent_100

/-- info: 'FTQCLib.Frame.Walkthrough.eval_hK8_Q_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_hK8_Q_100

/-- info: 'FTQCLib.Frame.Walkthrough.not_alignedCollapse_lagY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_alignedCollapse_lagY

/-- info: 'FTQCLib.Frame.Walkthrough.hKY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKY

/-- info: 'FTQCLib.Frame.Walkthrough.hKY_support_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hKY_support_one

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hKY_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hKY_ne

/-- info: 'FTQCLib.Hierarchy.two_pow_pred_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_pred_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.floorKappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorKappa

/-- info: 'FTQCLib.Frame.Walkthrough.shiftLaw_defect_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftLaw_defect_eq

/-- info: 'FTQCLib.Frame.Walkthrough.floorEps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorEps

/-- info: 'FTQCLib.Frame.Walkthrough.floorKappa_eq_of_two_mul_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorKappa_eq_of_two_mul_eq_zero

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor_h

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor_L

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hElimFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hElimFloor

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hElimFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hElimFloor

/-- info: 'FTQCLib.Frame.Walkthrough.hFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hFloor

/-- info: 'FTQCLib.Frame.Walkthrough.hFloor_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hFloor_h

/-- info: 'FTQCLib.Frame.Walkthrough.hFloor_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hFloor_L

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hFloor

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hFloor

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_paulix_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot_paulix_zero

/-- info: 'FTQCLib.Frame.Walkthrough.floorKappa_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorKappa_KX

/-- info: 'FTQCLib.Frame.Walkthrough.floorEps_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorEps_KX

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor_KX

/-- info: 'FTQCLib.Frame.Walkthrough.floorKappa_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorKappa_KM

/-- info: 'FTQCLib.Frame.Walkthrough.floorEps_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorEps_KM

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor_KM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor_KM

/-- info: 'FTQCLib.Frame.Walkthrough.floorKappa_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorKappa_KS

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor_KS

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hFloor_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hFloor_KX

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hFloor_KX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hFloor_KX

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hFloor_KZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hFloor_KZ

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.AffineDifference

/-!
# Acceptance rows for the dyadic-affine difference

* **The degree bound is load-bearing**: the cubic `X₀X₁X₂` at `m = 1` satisfies the coefficient
  conditions vacuously and its difference is not dyadic-affine (`not_isF2Affine_cubic`, by the
  second-difference falsifier). The level hypothesis carries the degree bound the coefficient
  conditions alone lack.
* **The linear-coefficient bound is load-bearing**: `X₀` at `m = 3` has effective level `3`, and its
  difference is not dyadic-affine (`not_isF2Affine_lin_m3`).
* **Agreement**: the difference of the `CZ` exponent `X₀X₁` at `m = 1` is dyadic-affine through the
  theorem (`effLevel_CZ`, `isMultilinear_CZ`) and directly, with the data `a = 0`, `e = e₁`.
* **The level of the frame's named exponents**: `X₀` has level `m` at every positive precision, so
  the `S` exponent at `m = 2` is level two and the `T` exponent at `m = 3` is level three.

`DiagPhase.eval` is noncomputable, so the evaluation rows are `rw` rows on named exponents and the
falsifier's final arithmetic is decided by the kernel. -/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial

/-! ## The level of the named exponents -/

/-- `1 ≠ 0` in `ZMod (2^m)` at positive precision. -/
theorem one_ne_zero_of_one_le {m : ℕ} (hm : 1 ≤ m) : (1 : ZMod (2 ^ m)) ≠ 0 := by
  have h1 : (1 : ZMod (2 ^ m)).val = 1 := by
    haveI : Fact (1 < 2 ^ m) := ⟨by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm⟩
    exact ZMod.val_one _
  intro h
  rw [h, ZMod.val_zero] at h1
  exact absurd h1 (by norm_num)

/-- `twoAdicVal 1 = 0` at positive precision. -/
theorem twoAdicVal_one {m : ℕ} (hm : 1 ≤ m) : twoAdicVal (1 : ZMod (2 ^ m)) = 0 := by
  rw [twoAdicVal_of_ne_zero (one_ne_zero_of_one_le hm)]
  have h1 : (1 : ZMod (2 ^ m)).val = 1 := by
    haveI : Fact (1 < 2 ^ m) := ⟨by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm⟩
    exact ZMod.val_one _
  rw [h1]
  simp

/-- `X₀` at precision `m` has effective level `m`. -/
theorem effectiveLevel_X {m : ℕ} (hm : 1 ≤ m) :
    effectiveLevel (MvPolynomial.X 0 : DiagPhase 1 m) = (m - 1) + 1 := by
  rw [show (MvPolynomial.X 0 : DiagPhase 1 m) = monomial (Finsupp.single 0 1) 1 from rfl,
    effectiveLevel_monomial_eq (one_ne_zero_of_one_le hm)]
  unfold effLevelMonom
  rw [twoAdicVal_one hm, Finsupp.sum_single_index rfl, Nat.sub_zero]

/-- `X₀` is multilinear. -/
theorem isMultilinear_X {m : ℕ} : IsMultilinear (MvPolynomial.X 0 : DiagPhase 1 m) := by
  intro d hd k
  rw [show (MvPolynomial.X 0 : DiagPhase 1 m) = monomial (Finsupp.single 0 1) 1 from rfl,
    MvPolynomial.support_monomial] at hd
  by_cases h1 : (1 : ZMod (2 ^ m)) = 0
  · rw [if_pos h1] at hd; exact absurd hd (Finset.notMem_empty _)
  · rw [if_neg h1, Finset.mem_singleton] at hd
    subst hd
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num

/-- The `S` exponent at `m = 2` is in the level-two family. -/
theorem effLevel_S_m2 : effectiveLevel (MvPolynomial.X 0 : DiagPhase 1 2) = 2 :=
  effectiveLevel_X (by norm_num)

/-- The `T` exponent at `m = 3` is not. -/
theorem effLevel_X_m3 : effectiveLevel (MvPolynomial.X 0 : DiagPhase 1 3) = 3 :=
  effectiveLevel_X (by norm_num)

/-- The `CZ` exponent `X₀X₁` at `m = 1` is one multilinear monomial. -/
theorem XX_monomial : (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)
    = monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [show (MvPolynomial.X 0 : DiagPhase 2 1) = monomial (Finsupp.single 0 1) 1 from rfl,
    show (MvPolynomial.X 1 : DiagPhase 2 1) = monomial (Finsupp.single 1 1) 1 from rfl,
    monomial_mul, mul_one]

/-- The `CZ` exponent is in the level-two family. -/
theorem effLevel_CZ :
    effectiveLevel (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1) = 2 := by
  rw [XX_monomial, effectiveLevel_monomial_eq (one_ne_zero_of_one_le (m := 1) (by norm_num))]
  unfold effLevelMonom
  rw [twoAdicVal_one (m := 1) (by norm_num),
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  norm_num

/-- The `CZ` exponent is multilinear. -/
theorem isMultilinear_CZ :
    IsMultilinear (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1) := by
  intro d hd k
  rw [XX_monomial, MvPolynomial.support_monomial,
    if_neg (one_ne_zero_of_one_le (m := 1) (by norm_num)), Finset.mem_singleton] at hd
  subst hd
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  fin_cases k <;> norm_num

/-! ## Agreement on the `CZ` exponent -/

/-- The difference of `X₀X₁` along `X₀` at `m = 1` reads the other bit, at every word. -/
theorem funcDerivEval_XX (v : Fin 2 → ZMod 2) :
    funcDerivEval 0 (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1) v
      = ((v 1).val : ZMod (2 ^ 1)) := by
  unfold funcDerivEval funcDeriv DiagPhase.eval DiagPhase.liftBinary
  rw [map_mul, map_mul]
  simp only [MvPolynomial.eval_X]
  have e0 : (v + (Pi.single 0 1 : Fin 2 → ZMod 2)) 0 = v 0 + 1 := by simp
  have e1 : (v + (Pi.single 0 1 : Fin 2 → ZMod 2)) 1 = v 1 := by simp
  rw [e0, e1]
  rcases (show v 0 = 0 ∨ v 0 = 1 by revert v; decide) with h0 | h0 <;>
    rcases (show v 1 = 0 ∨ v 1 = 1 by revert v; decide) with h1 | h1 <;>
    rw [h0, h1] <;> decide

/-- **Directly**: the difference is dyadic-affine with `a = 0` and `e = e₁`. -/
theorem isF2Affine_XX_direct :
    IsF2Affine (funcDerivEval 0 (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)) := by
  refine ⟨0, Pi.single 1 1, fun v => ?_⟩
  rw [funcDerivEval_XX]
  have hs : (∑ l, (Pi.single 1 1 : Fin 2 → ZMod 2) l * v l) = v 1 := by
    rw [Finset.sum_eq_single 1 (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_mul])
      (fun h => absurd (Finset.mem_univ 1) h), Pi.single_eq_same, one_mul]
  rw [hs, zero_add]
  simp

/-- **Through the theorem**: the same conclusion from the level and multilinearity. -/
theorem isF2Affine_XX_theorem :
    IsF2Affine (funcDerivEval 0 (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)) :=
  funcDerivEval_isF2Affine (by rw [effLevel_CZ]) 0

/-- **Through the multilinear route**: the polynomial-side theorem gives the same conclusion. -/
theorem isF2Affine_XX_theorem_of_isMultilinear :
    IsF2Affine (funcDerivEval 0 (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)) :=
  funcDerivEval_isF2Affine_of_isMultilinear isMultilinear_CZ (by rw [effLevel_CZ]) 0

/-! ## The square: outside multilinearity, inside the class -/

/-- `2·X₀²` at precision two: the exponent vector `2e₀` is in the support, so the exponent is
not multilinear. -/
theorem not_isMultilinear_sq :
    ¬ IsMultilinear (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)
      (2 : ZMod (2 ^ 2)) : DiagPhase 1 2) := by
  intro h
  have hmem : Finsupp.single (0 : Fin 1) 2 ∈ (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)
      (2 : ZMod (2 ^ 2)) : DiagPhase 1 2).support := by
    rw [MvPolynomial.support_monomial, if_neg (by decide), Finset.mem_singleton]
  have := h _ hmem 0
  rw [Finsupp.single_eq_same] at this
  omega

/-- Its effective level is `(2 − 1 − v₂(2)) + 2 = 2`. -/
theorem effLevel_sq_le_two :
    effectiveLevel (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)
      (2 : ZMod (2 ^ 2)) : DiagPhase 1 2) ≤ 2 := by
  have hc : (2 : ZMod (2 ^ 2)) ≠ 0 := by decide
  rw [effectiveLevel_monomial_eq hc]
  unfold effLevelMonom
  rw [twoAdicVal_of_ne_zero hc, show (2 : ZMod (2 ^ 2)).val = 2 by decide,
    Nat.Prime.factorization_self Nat.prime_two, Finsupp.sum_single_index (by rfl)]

/-- The difference of the square is dyadic-affine by the theorem — the row the multilinear form
does not state. -/
theorem isF2Affine_sq :
    IsF2Affine (funcDerivEval 0 (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 2)
      (2 : ZMod (2 ^ 2)) : DiagPhase 1 2)) :=
  funcDerivEval_isF2Affine effLevel_sq_le_two 0

/-! ## The hypotheses are load-bearing -/

/-- The difference of the cubic along its last variable is the product of the other two bits. -/
theorem dcube_eval (v : Fin 3 → ZMod 2) (h2 : v 2 = 0) :
    funcDerivEval (2 : Fin 3)
        (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 : DiagPhase 3 1) v
      = ((v 0).val : ZMod (2 ^ 1)) * ((v 1).val : ZMod (2 ^ 1)) := by
  unfold funcDerivEval funcDeriv DiagPhase.eval DiagPhase.liftBinary
  rw [map_mul, map_mul, map_mul, map_mul]
  simp only [MvPolynomial.eval_X]
  have e0 : (v + (Pi.single 2 1 : Fin 3 → ZMod 2)) 0 = v 0 := by simp
  have e1 : (v + (Pi.single 2 1 : Fin 3 → ZMod 2)) 1 = v 1 := by simp
  have e2 : (v + (Pi.single 2 1 : Fin 3 → ZMod 2)) 2 = 1 := by simp [h2]
  rw [e0, e1, e2, h2, show ((1 : ZMod 2).val) = 1 from by decide,
    show ((0 : ZMod 2).val) = 0 from by decide]
  push_cast
  ring

/-- **The degree bound is load-bearing.** The cubic meets the coefficient conditions vacuously and
its difference is not dyadic-affine. -/
theorem not_isF2Affine_cubic :
    ¬ IsF2Affine (funcDerivEval (2 : Fin 3)
        (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 : DiagPhase 3 1)) := by
  intro h
  have key := h.second_diff ![1, 0, 0] ![0, 1, 0]
  have hsum : (![1, 0, 0] : Fin 3 → ZMod 2) + ![0, 1, 0] = ![1, 1, 0] := by
    funext j; fin_cases j <;> decide
  have hzero : (0 : Fin 3 → ZMod 2) = ![0, 0, 0] := by funext j; fin_cases j <;> decide
  rw [hsum, hzero, dcube_eval _ (by decide), dcube_eval _ (by decide),
    dcube_eval _ (by decide), dcube_eval _ (by decide)] at key
  revert key
  decide +kernel

/-- The difference of `X₀` at `m = 3` is `±1`. -/
theorem dlin_eval (a : ZMod 2) :
    funcDerivEval (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase 1 3) ![a]
      = (((a + 1).val : ℕ) : ZMod (2 ^ 3)) - ((a.val : ℕ) : ZMod (2 ^ 3)) := by
  unfold funcDerivEval funcDeriv DiagPhase.eval DiagPhase.liftBinary
  have hpt : ((![a] : Fin 1 → ZMod 2) + (Pi.single 0 1 : Fin 1 → ZMod 2)) 0 = a + 1 := by simp
  rw [MvPolynomial.eval_X, MvPolynomial.eval_X, hpt]
  rfl

/-- **The linear-coefficient bound is load-bearing.** `X₀` at `m = 3` (level three) has a
difference that is not dyadic-affine. -/
theorem not_isF2Affine_lin_m3 :
    ¬ IsF2Affine (funcDerivEval (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase 1 3)) := by
  intro h
  have key := h.second_diff ![1] ![1]
  have hsum : (![1] : Fin 1 → ZMod 2) + ![1] = ![0] := by funext j; fin_cases j; decide
  have hzero : (0 : Fin 1 → ZMod 2) = ![0] := by funext j; fin_cases j; decide
  rw [hsum, hzero, dlin_eval, dlin_eval] at key
  revert key
  decide +kernel

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.two_pow_pred_mul_val_add' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_pow_pred_mul_val_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsF2Affine' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsF2Affine

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_const' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isF2Affine_const

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsF2Affine.add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsF2Affine.add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_lin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isF2Affine_lin

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isF2Affine_sum

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsF2Affine.second_diff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsF2Affine.second_diff

/-- info: 'FTQCLib.Hierarchy.DiagPhase.exponent_cases' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms exponent_cases

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eq_two_pow_pred_of_twoAdicVal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_two_pow_pred_of_twoAdicVal

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_eval_of_effectiveLevel_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isF2Affine_eval_of_effectiveLevel_le_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.shiftDeriv_effectiveLevel_le_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftDeriv_effectiveLevel_le_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.funcDerivEval_isF2Affine' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms funcDerivEval_isF2Affine

/-- info: 'FTQCLib.Hierarchy.DiagPhase.funcDerivEval_isF2Affine_of_isMultilinear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms funcDerivEval_isF2Affine_of_isMultilinear

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_sq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isF2Affine_sq

/-- info: 'FTQCLib.Hierarchy.DiagPhase.one_ne_zero_of_one_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_ne_zero_of_one_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms twoAdicVal_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.XX_monomial' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms XX_monomial

/-- info: 'FTQCLib.Hierarchy.DiagPhase.dcube_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms dcube_eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.dlin_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms dlin_eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_X' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms effectiveLevel_X

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isMultilinear_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isMultilinear_X

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effLevel_S_m2' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms effLevel_S_m2

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effLevel_X_m3' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms effLevel_X_m3

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effLevel_CZ' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms effLevel_CZ

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isMultilinear_CZ' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isMultilinear_CZ

/-- info: 'FTQCLib.Hierarchy.DiagPhase.funcDerivEval_XX' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms funcDerivEval_XX

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_XX_direct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isF2Affine_XX_direct

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isF2Affine_XX_theorem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isF2Affine_XX_theorem

/-- info: 'FTQCLib.Hierarchy.DiagPhase.not_isF2Affine_cubic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_isF2Affine_cubic

/-- info: 'FTQCLib.Hierarchy.DiagPhase.not_isF2Affine_lin_m3' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_isF2Affine_lin_m3

end FTQCLib.Hierarchy.DiagPhase

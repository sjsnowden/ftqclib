/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.DyadicValuation

/-!
# Check: the top bit and the dyadic valuation

Witness rows for `FTQCLib.Hierarchy.DyadicValuation`, then the axiom rows. The witness rows are
kernel rows on concrete precisions: the `4c = 0` dichotomy takes each of its two branches, the
valuation of a power of two reads `min m a` on both sides of `m`, and the top bit is nonzero at
precision one while `2^{m−1} · 2` vanishes there.
-/

namespace FTQCLib.Hierarchy

open DiagPhase

/-! ## Witness rows -/

/-- At precision `2`, `c = 1` has `4c = 0` and `2c = 2 = 2^{m−1}`: the second branch. -/
theorem four_mul_one_zmod4 : (4 : ZMod (2 ^ 2)) * 1 = 0 := by decide

theorem two_mul_one_zmod4_eq_top : (2 : ZMod (2 ^ 2)) * 1 = (2 : ZMod (2 ^ 2)) ^ (2 - 1) := by
  decide

/-- At precision `2`, `c = 2` has `4c = 0` and `2c = 0`: the first branch. -/
theorem two_mul_two_zmod4 : (2 : ZMod (2 ^ 2)) * 2 = 0 := by decide

/-- The dichotomy on both witnesses, through the theorem. -/
theorem dichotomy_one : (2 : ZMod (2 ^ 2)) * 1 = 0 ∨ (2 : ZMod (2 ^ 2)) * 1 = 2 ^ (2 - 1) :=
  two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero four_mul_one_zmod4

theorem dichotomy_two : (2 : ZMod (2 ^ 2)) * 2 = 0 ∨ (2 : ZMod (2 ^ 2)) * 2 = 2 ^ (2 - 1) :=
  two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero (by decide)

/-- The top bit at precision one is `1 ≠ 0`, and `2^{m−1} · 2 = 0` there. -/
theorem top_bit_one : (2 : ZMod (2 ^ 1)) ^ (1 - 1) ≠ 0 := two_pow_pred_ne_zero le_rfl

theorem top_bit_one_mul_two : (2 : ZMod (2 ^ 1)) ^ (1 - 1) * 2 = 0 := two_pow_pred_mul_two

/-- The valuation of `2` at precision `3` is `1`; of `2^5` it is `3` (saturated). -/
theorem twoAdicVal_two_zmod8 : twoAdicVal ((2 : ZMod (2 ^ 3)) ^ 1) = 1 := by
  rw [twoAdicVal_pow_two]
  decide

theorem twoAdicVal_two_pow_five_zmod8 : twoAdicVal ((2 : ZMod (2 ^ 3)) ^ 5) = 3 := by
  rw [twoAdicVal_pow_two]
  decide

/-- A residue killed by `2` at precision `3`: `κ = 4` is the top bit times the bit `1`. -/
theorem exists_bit_four_zmod8 :
    ∃ ε : ZMod 2,
      (4 : ZMod (2 ^ 3)) = (2 : ZMod (2 ^ 3)) ^ (3 - 1) * ((ε.val : ℕ) : ZMod (2 ^ 3)) :=
  exists_bit_of_two_mul_eq_zero (by norm_num) (by decide)

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Hierarchy.two_pow_pred_mul_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_pred_mul_two

/-- info: 'FTQCLib.Hierarchy.two_pow_pred_ne_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_pred_ne_zero

/-- info: 'FTQCLib.Hierarchy.exists_bit_of_two_mul_eq_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_bit_of_two_mul_eq_zero

/-- info: 'FTQCLib.Hierarchy.two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.pow_two_eq_zero_of_ge' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagPhase.pow_two_eq_zero_of_ge

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_pow_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagPhase.twoAdicVal_pow_two

end FTQCLib.Hierarchy

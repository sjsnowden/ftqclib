/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.SqrtTwo

/-!
# Check: `√2` as a complex number

The axiom sweep of `SqrtTwo.lean`, one row of each kind, and one mutant.

* **Agreement.** The two forms of `1/√2` agree with the inverse: `(√2)⁻¹ = √2/2`.
* **Discriminating.** `√2 · √2` is `2`, not `√2 + √2 = 2√2`: the two differ, since `√2 ≠ 1`.
* **Inhabitation.** `inv_sqrt_two_sq` read on `1/√2`: `(1/√2)² = 1/2`.
-/

namespace FTQCLib.Frame.Walkthrough

-- row: agreement
/-- `(√2)⁻¹ = √2/2`, from `one_div_sqrt_two`. -/
theorem inv_sqrt_two_eq_half_sqrt_two : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  rw [← one_div, one_div_sqrt_two]

-- row: discriminating
/-- `√2 · √2 ≠ √2 + √2`: multiplying is not adding. -/
theorem sqrt_two_mul_self_ne_add :
    (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) ≠ Real.sqrt 2 + Real.sqrt 2 := by
  rw [sqrt_two_mul_self, ← two_mul]
  intro h
  have h1 : (Real.sqrt 2 : ℂ) = 1 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    exact (mul_left_cancel₀ h2 (h.symm.trans (mul_one 2).symm))
  have : Real.sqrt 2 = 1 := by exact_mod_cast h1
  have h3 : (2 : ℝ) = 1 := by
    rw [← Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), this]
    norm_num
  norm_num at h3

-- row: inhabitation
/-- `(1/√2)² = 1/2`. -/
theorem one_div_sqrt_two_sq : (1 / (Real.sqrt 2 : ℂ)) ^ 2 = 1 / 2 := by
  rw [one_div, inv_sqrt_two_sq]

/-! ## Axiom sweep -/

/-- info: 'FTQCLib.Frame.Walkthrough.ofReal_sqrt_two_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ofReal_sqrt_two_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.one_div_sqrt_two_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.one_div_sqrt_two_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.sqrt_two_mul_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sqrt_two_mul_self

/-- info: 'FTQCLib.Frame.Walkthrough.sqrt_two_sq_complex' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sqrt_two_sq_complex

/-- info: 'FTQCLib.Frame.Walkthrough.inv_sqrt_two_sq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.inv_sqrt_two_sq

/-- info: 'FTQCLib.Frame.Walkthrough.one_div_sqrt_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.one_div_sqrt_two

/-- info: 'FTQCLib.Frame.Walkthrough.one_div_sqrt_two_mul_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.one_div_sqrt_two_mul_two

/-- info: 'FTQCLib.Frame.Walkthrough.inv_sqrt_two_eq_half_sqrt_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.inv_sqrt_two_eq_half_sqrt_two

/-- info: 'FTQCLib.Frame.Walkthrough.sqrt_two_mul_self_ne_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sqrt_two_mul_self_ne_add

/-- info: 'FTQCLib.Frame.Walkthrough.one_div_sqrt_two_sq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.one_div_sqrt_two_sq

/-- info: 'FTQCLib.Frame.Walkthrough.sqrt_two_pow_four' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sqrt_two_pow_four

/-- info: 'FTQCLib.Frame.Walkthrough.sq_pow_sqrt_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sq_pow_sqrt_two

/-- info: 'FTQCLib.Frame.Walkthrough.sq_zpow_sqrt_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sq_zpow_sqrt_two

/-! ## Declared mutants -/

-- mutant: sqrt_two_mul_self_value | FTQCLib/Carrier/SqrtTwo.lean | (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by | (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 4 := by

end FTQCLib.Frame.Walkthrough

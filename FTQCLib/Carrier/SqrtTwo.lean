/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# `√2` as a complex number

A carrier state's scale carries `√2` to a power (H's free rule divides by it), so the same few facts
about `(Real.sqrt 2 : ℂ)` are needed across the carrier modules. They live here, once, below
`HadamardGate.lean`, the lowest carrier module that uses them (docs/STEPS.md, entry 2026-10-01b).
Before, they were stated in ten places (three of them check modules) and re-proved inline in
twenty-two.

## Main results

* `ofReal_sqrt_two_ne_zero`, `one_div_sqrt_two_ne_zero` — `√2 ≠ 0` and `1/√2 ≠ 0`.
* `sqrt_two_mul_self`, `sqrt_two_sq_complex` — `√2 · √2 = 2` and `√2 ^ 2 = 2`.
* `inv_sqrt_two_sq` — `(√2)⁻¹ ^ 2 = 1/2`.
* `one_div_sqrt_two`, `one_div_sqrt_two_mul_two` — `1/√2 = √2/2` and `(1/√2) · 2 = √2`.
* `sqrt_two_pow_four` — `√2 ^ 4 = 4`, the normalisation at height four (entry 2026-10-01n).
-/

namespace FTQCLib.Frame.Walkthrough

/-- `√2 ≠ 0` in `ℂ`. -/
theorem ofReal_sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- `1/√2 ≠ 0` in `ℂ`. -/
theorem one_div_sqrt_two_ne_zero : 1 / (Real.sqrt 2 : ℂ) ≠ 0 :=
  one_div_ne_zero ofReal_sqrt_two_ne_zero

/-- `√2 · √2 = 2` in `ℂ`. -/
theorem sqrt_two_mul_self : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `√2 ^ 2 = 2` in `ℂ`. -/
theorem sqrt_two_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [sq, sqrt_two_mul_self]

/-- `(1/√2)² = 1/2` in `ℂ`. -/
theorem inv_sqrt_two_sq : (Real.sqrt 2 : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, sqrt_two_sq_complex, one_div]

/-- `1/√2 = √2/2` in `ℂ`. -/
theorem one_div_sqrt_two : 1 / (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) / 2 := by
  rw [div_eq_div_iff ofReal_sqrt_two_ne_zero two_ne_zero, one_mul, sqrt_two_mul_self]

/-- `(1/√2)·2 = √2` in `ℂ`. -/
theorem one_div_sqrt_two_mul_two : (1 / (Real.sqrt 2 : ℂ)) * 2 = Real.sqrt 2 := by
  rw [one_div_sqrt_two, div_mul_cancel₀ _ two_ne_zero]

/-- `√2 ^ 4 = 4` in `ℂ`. -/
theorem sqrt_two_pow_four : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrt_two_sq_complex]
  norm_num

/-- `(√2^t)^2 = 2^t` for a natural `t`. -/
theorem sq_pow_sqrt_two (t : ℕ) : ((Real.sqrt 2 : ℝ) ^ t) ^ 2 = (2 : ℝ) ^ t := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `(√2^e)^2 = 2^e` for an integer `e`. -/
theorem sq_zpow_sqrt_two (e : ℤ) : ((Real.sqrt 2 : ℝ) ^ e) ^ 2 = (2 : ℝ) ^ e := by
  rcases Int.eq_nat_or_neg e with ⟨t, ht | ht⟩
  · rw [ht, zpow_natCast, zpow_natCast, sq_pow_sqrt_two]
  · rw [ht, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_pow, sq_pow_sqrt_two]

end FTQCLib.Frame.Walkthrough

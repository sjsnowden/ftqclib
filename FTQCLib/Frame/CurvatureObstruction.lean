/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Frame.PrecisionValuation

set_option linter.style.longLine false

/-!
# The curvature obstruction and the factorization `D(D+2) = 0`

The frame's difference operator `D = funcDerivG i` is **not a differential**: `D² = −2D`
(`funcDerivG_funcDerivG`), not `D² = 0`. This file records the algebraic content of that fact —
the *obstruction* side of the question whether `D` carries a curved / A∞ DGA structure.

* `funcDerivG_factorization` — `D² + 2D = 0`, i.e. `D` satisfies its minimal polynomial `t·(t+2)`.
  This is the matrix-factorization-shaped object (a factorization of `t² + 2t` over
  `ZMod (2^m)`): `D` and `D+2` are complementary factors of the zero operator.
* `two_not_isUnit` — `2` is a **non-unit** in `ZMod (2^m)` (`m ≥ 1`), with `two_zero_divisor` the explicit
  zero-divisor witness `2 · 2^{m-1} = 0`, `2^{m-1} ≠ 0`.

Together with `funcDerivG_sq_ne_zero` (`D² ≠ 0` over `ZMod 4`) these are the obstruction: the defect `−2` in
`D² = −2D` is a **non-unit** multiple of `D`, so it cannot be rescaled/gauged away to make `D` a strict
differential over `ZMod (2^m)` for `m ≥ 2`. This file does not construct a curved/A∞ structure
that would *absorb* the `−2` as curvature: the classical Maurer–Cartan absorption needs to divide
by `k!` (a char-0 unit) or a *unit* curvature, both unavailable here, and Mathlib has no
`MatrixFactorization`/`CurvedAlgebra`/`Ainfinity` structure to instantiate. Contrast the frame's
*strict* cochain complex (`delta2_comp_delta1 : δ² = 0`, `FTQCLib/Cohomology/Cochains.lean`), a
genuine DGA precisely because its differential is not `funcDerivG`.
-/

open FTQCLib.Hierarchy.BooleanMobius FTQCLib.Hierarchy.DiagPhase

namespace FTQCLib.Frame.Curvature

variable {n : ℕ}

/-- **The factorization `D(D+2) = 0`.** `funcDerivG i` satisfies its minimal polynomial `t·(t+2) = t² + 2t`:
`D² + 2D = 0`. Immediate from `D² = −2D` (`funcDerivG_funcDerivG`). So `D` and `D + 2` are complementary factors
of the zero operator — a matrix-factorization-shaped object, not a differential. -/
theorem funcDerivG_factorization {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG i f) + (2 : ℤ) • funcDerivG i f = 0 := by
  rw [funcDerivG_funcDerivG, ← add_smul]
  norm_num

/-- **`2` is a non-unit in `ZMod (2^m)`** for `m ≥ 1` (`2 ∣ 2^m`, so `2` is not coprime to the modulus). This is
why the `−2` defect cannot be gauged away: the classical curvature-absorption theorems require the curvature to be
a *unit*. -/
theorem two_not_isUnit {m : ℕ} (hm : 1 ≤ m) : ¬ IsUnit (2 : ZMod (2 ^ m)) := by
  rw [show (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) by norm_cast,
    ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_two, not_not]
  exact dvd_pow_self 2 (by omega)

/-- **The explicit zero-divisor witness.** `2 · 2^{m-1} = 2^m = 0` in `ZMod (2^m)`, with `2^{m-1} ≠ 0` for
`m ≥ 1`. So `2` is a genuine zero divisor — the concrete reason it is a non-unit. -/
theorem two_zero_divisor {m : ℕ} (hm : 1 ≤ m) :
    (2 : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) = 0
      ∧ (2 : ZMod (2 ^ m)) ^ (m - 1) ≠ 0 := by
  have hpow : ∀ k : ℕ, (2 : ZMod (2 ^ m)) ^ k = ((2 ^ k : ℕ) : ZMod (2 ^ m)) := by
    intro k; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [← pow_succ', Nat.sub_add_cancel hm, hpow, ZMod.natCast_self]
  · rw [hpow, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd) (by omega)

end FTQCLib.Frame.Curvature

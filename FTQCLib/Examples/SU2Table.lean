/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.SU2CoverageLinfty

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # Worked examples for frame-native SU(2) coverage (measure A)

The two-grade companion to `su2_coverage` (`FTQCLib/Examples/SU2CoverageLinfty.lean`), mirroring `RzTable`:

* **Symbolic / arbitrary grade** — `su2_coverage` itself: for *any* Euler angles `α, β, γ` and precision `m`,
  the frame's Euler word is within `6·π/2^m` of the target in the max-row-sum measure. Re-exposed here as
  `coverage_arbitrary`.
* **Concrete grade** — the `θ = 2π/3` instance at `m = 2, 3, 4` (bounds `3π/2, 3π/4, 3π/8`, the `Θ(log 1/ε)`
  shrink), plus the **exact `= 0`** sanity for a target already on the frame's dyadic grid.

Unlike the diagonal `RzTable` ladder (`π/6, π/12, π/24` exact equalities), the SU(2) composite distance is a
`2×2` matrix-product quantity, so the non-Clifford concrete gives the *bound*, not a closed-form equality; the
clean numeral is the dyadic `= 0` case. Frame-pure (imports no `FTQCLib.Hilbert`). -/

namespace FTQCLib.Frame.SU2

open Matrix Real

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormSMulClass

/-! ## Symbolic grade -/

/-- **Coverage, arbitrary target.** For every Euler angles `α, β, γ` and precision `m`, the frame's dyadic
Euler word is within `6·π/2^m` of `R_z(α)·H·R_z(β)·H·R_z(γ)` in the measure. (This is `su2_coverage`, named
as the example's symbolic grade.) -/
theorem coverage_arbitrary (α β γ : ℝ) (m : ℕ) :
    ∃ a b c : ZMod (2 ^ m),
      ‖Rz α * (Had * (Rz β * (Had * Rz γ)))
        - Rz (2 * Real.pi * (a.val : ℝ) / 2 ^ m)
            * (Had * (Rz (2 * Real.pi * (b.val : ℝ) / 2 ^ m)
                * (Had * Rz (2 * Real.pi * (c.val : ℝ) / 2 ^ m))))‖
        ≤ 6 * Real.pi / 2 ^ m :=
  su2_coverage α β γ m

/-! ## Concrete grade — the `θ = 2π/3` word at growing precision -/

/-- The concrete Euler word target `R_z(2π/3)·H·R_z(2π/3)·H·R_z(2π/3)` (a tilted-axis, non-Clifford,
non-diagonal single-qubit unitary). -/
noncomputable def target2pi3 : Matrix (Fin 2) (Fin 2) ℂ :=
  Rz (2 * Real.pi / 3) * (Had * (Rz (2 * Real.pi / 3) * (Had * Rz (2 * Real.pi / 3))))

/-- The frame's approximant for `target2pi3` at precision `m`, given the three tower coefficients. -/
noncomputable def approx2pi3 (m : ℕ) (a b c : ZMod (2 ^ m)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Rz (2 * Real.pi * (a.val : ℝ) / 2 ^ m)
    * (Had * (Rz (2 * Real.pi * (b.val : ℝ) / 2 ^ m)
        * (Had * Rz (2 * Real.pi * (c.val : ℝ) / 2 ^ m))))

/-- **m = 2: within `3π/2`.** -/
theorem example_2pi3_m2 : ∃ a b c : ZMod (2 ^ 2),
    ‖target2pi3 - approx2pi3 2 a b c‖ ≤ 3 * Real.pi / 2 := by
  obtain ⟨a, b, c, h⟩ := su2_coverage (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) 2
  exact ⟨a, b, c, by rw [target2pi3, approx2pi3]; refine h.trans (le_of_eq ?_); ring⟩

/-- **m = 3: within `3π/4`.** -/
theorem example_2pi3_m3 : ∃ a b c : ZMod (2 ^ 3),
    ‖target2pi3 - approx2pi3 3 a b c‖ ≤ 3 * Real.pi / 4 := by
  obtain ⟨a, b, c, h⟩ := su2_coverage (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) 3
  exact ⟨a, b, c, by rw [target2pi3, approx2pi3]; refine h.trans (le_of_eq ?_); ring⟩

/-- **m = 4: within `3π/8`.** The `Θ(log 1/ε)` shrink: `3π/2 → 3π/4 → 3π/8`. -/
theorem example_2pi3_m4 : ∃ a b c : ZMod (2 ^ 4),
    ‖target2pi3 - approx2pi3 4 a b c‖ ≤ 3 * Real.pi / 8 := by
  obtain ⟨a, b, c, h⟩ := su2_coverage (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) 4
  exact ⟨a, b, c, by rw [target2pi3, approx2pi3]; refine h.trans (le_of_eq ?_); ring⟩

/-! ## Exact grade — a target already on the frame's dyadic grid is built with distance `0` -/

/-- **Exact on the grid (distance `0`, by construction).** A target whose Euler angles already lie on the
frame's dyadic grid `{2π·k/2^m}` — i.e. a word `approx2pi3 m a b c` — is built by the frame with distance
exactly `0`: it is its own approximant, no rounding. Trivial, but it is the exact Clifford/sanity endpoint
of the `≤ 6π/2^m` bound (off-grid): at `m = 2` the grid holds the `S = R_z(π/2)` word, at `m = 3` the `T`
word, and the frame hits every one of them exactly. -/
theorem coverage_exact_on_grid (m : ℕ) (a b c : ZMod (2 ^ m)) :
    ‖approx2pi3 m a b c - approx2pi3 m a b c‖ = 0 := by rw [sub_self, norm_zero]

end FTQCLib.Frame.SU2

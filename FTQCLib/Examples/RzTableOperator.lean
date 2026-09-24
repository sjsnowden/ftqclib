/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.RzTable
import FTQCLib.Hilbert.RzApproxOperator

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # Operator-norm distances for the Rz table: the exact ladder

The separable Hilbert-side certificate for `FTQCLib/Examples/RzTable.lean`: the θ = 2π/3 ladder's finished
tables sit at EXACT operator-norm distance from the anchored `R_z(2π/3)` phase gate — the chords of the
arc numerals: `2·sin(π/12)`, `2·sin(π/24)`, `2·sin(π/48)` at m = 2, 3, 4. These are equalities, not
bounds: the two engines of the certificate meet in `qDiag_sub_opNorm_eq_anchored`, so the operator
distance is pinned, and it halves (asymptotically) per rung alongside the arc ladder `π/6, π/12, π/24`.

Follows the project's separable-certificate discipline: `RzTable.lean` is frame-pure; this file adds the
Hilbert-side receipt and nothing flows back. -/

namespace FTQCLib.Hilbert

open FTQCLib.Hierarchy.DiagPhase FTQCLib.Frame.Walkthrough MvPolynomial Real

/-- **m = 2, exact operator distance.** The one-row table's gate is exactly `2·sin(π/12)` from the
anchored `R_z(2π/3)` phase gate in operator norm — the chord of the arc distance `π/6`. -/
theorem ladder_two_opNorm :
    ‖qDiagCLM (fun v : Fin 1 → ZMod 2 => ((v 0).val : ℝ) * (2 * π / 3))
      - qDiagCLM (realPhase (runRows 2 [C (1 : ZMod (2 ^ 2)) * X 0]).q)‖
      = 2 * Real.sin (π / 12) := by
  rw [ladder_two_q]
  have hfun : realPhase (C (1 : ZMod (2 ^ 2)) * X (0 : Fin 1))
      = fun v => ((v 0).val : ℝ) * (2 * π * 1 / 2 ^ 2) := by
    funext v
    rw [realPhase_linear, show (((1 : ZMod (2 ^ 2)).val : ℝ)) = 1 from by
      rw [show (1 : ZMod (2 ^ 2)).val = 1 from by decide, Nat.cast_one]]
  rw [hfun, qDiag_sub_opNorm_eq_anchored,
    show ((2 * π / 3 - 2 * π * 1 / 2 ^ 2) / 2 : ℝ) = π / 12 from by ring,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]))]

/-- **m = 3, exact operator distance.** The two-row table's gate is exactly `2·sin(π/24)` from the
anchored `R_z(2π/3)` phase gate — the chord of the arc distance `π/12`. -/
theorem ladder_three_opNorm :
    ‖qDiagCLM (fun v : Fin 1 → ZMod 2 => ((v 0).val : ℝ) * (2 * π / 3))
      - qDiagCLM (realPhase (runRows 3 [C (1 : ZMod (2 ^ 3)) * X 0, C (2 : ZMod (2 ^ 3)) * X 0]).q)‖
      = 2 * Real.sin (π / 24) := by
  rw [ladder_three_q]
  have hfun : realPhase (C (3 : ZMod (2 ^ 3)) * X (0 : Fin 1))
      = fun v => ((v 0).val : ℝ) * (2 * π * 3 / 2 ^ 3) := by
    funext v
    rw [realPhase_linear, show (((3 : ZMod (2 ^ 3)).val : ℝ)) = 3 from by
      rw [show (3 : ZMod (2 ^ 3)).val = 3 from by decide]; norm_num]
  rw [hfun, qDiag_sub_opNorm_eq_anchored,
    show ((2 * π / 3 - 2 * π * 3 / 2 ^ 3) / 2 : ℝ) = -(π / 24) from by ring,
    Real.sin_neg, abs_neg,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]))]

/-- **m = 4, exact operator distance.** The two-row table's gate is exactly `2·sin(π/48)` from the
anchored `R_z(2π/3)` phase gate — the chord of the arc distance `π/24`. -/
theorem ladder_four_opNorm :
    ‖qDiagCLM (fun v : Fin 1 → ZMod 2 => ((v 0).val : ℝ) * (2 * π / 3))
      - qDiagCLM (realPhase (runRows 4 [C (1 : ZMod (2 ^ 4)) * X 0, C (4 : ZMod (2 ^ 4)) * X 0]).q)‖
      = 2 * Real.sin (π / 48) := by
  rw [ladder_four_q]
  have hfun : realPhase (C (5 : ZMod (2 ^ 4)) * X (0 : Fin 1))
      = fun v => ((v 0).val : ℝ) * (2 * π * 5 / 2 ^ 4) := by
    funext v
    rw [realPhase_linear, show (((5 : ZMod (2 ^ 4)).val : ℝ)) = 5 from by
      rw [show (5 : ZMod (2 ^ 4)).val = 5 from by decide]; norm_num]
  rw [hfun, qDiag_sub_opNorm_eq_anchored,
    show ((2 * π / 3 - 2 * π * 5 / 2 ^ 4) / 2 : ℝ) = π / 48 from by ring,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos]))]

end FTQCLib.Hilbert

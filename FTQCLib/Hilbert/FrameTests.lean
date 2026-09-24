/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKGateTests
import FTQCLib.Hilbert.FrameDescent
import FTQCLib.Hierarchy.FrameExponent

/-! # Kernel frame — non-vacuity on the T gate

These witnesses show the frame's level and descent are non-trivial on the canonical
non-Clifford gate `T` (the `π/4` phase, precision `3`):

* `level_tGate` — the frame level of `T` is exactly `3`.
* `tGate_descent_four` — the fourth difference of `T` vanishes (descent forward,
  since `level T = 3 < 4`).
* `tGate_descent_three_ne` — the **third** difference of `T` does *not* vanish:
  its value at `0` is `4 ≠ 0` in `ZMod 8`, computed through the `−2Δ` tower
  `Δ³ = 4·Δ`. Together with `tGate_descent_four` this pins the level: the descent
  is sharp at `3`.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

/-- The `T`-gate exponent is multilinear (a single degree-one monomial). -/
lemma isMultilinear_tGate (i : Fin n) : DiagPhase.IsMultilinear (DiagPhase.tGatePoly i) := by
  have hmon : (DiagPhase.tGatePoly i : DiagPhase n 3)
      = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 3)) := X_eq_monomial i
  rw [hmon]
  intro d hd k
  rw [MvPolynomial.support_monomial, if_neg (by decide : ¬ (1 : ZMod (2 ^ 3)) = 0),
    Finset.mem_singleton] at hd
  subst hd
  rw [Finsupp.single_apply]
  split_ifs <;> omega

/-- **Frame level of `T` is 3.** Computes `effectiveLevel` of the single monomial
`X i` at precision `3`: `(3 − 1 − v₂(1)) + 1 = 3`. -/
theorem level_tGate (i : Fin n) : level (DiagPhase.tGatePoly i) = 3 := by
  have hmon : (DiagPhase.tGatePoly i : DiagPhase n 3)
      = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 3)) := X_eq_monomial i
  show DiagPhase.effectiveLevel (DiagPhase.tGatePoly i) = 3
  rw [hmon, DiagPhase.effectiveLevel_monomial_eq (by decide : ¬ (1 : ZMod (2 ^ 3)) = 0)]
  unfold DiagPhase.effLevelMonom
  rw [twoAdicVal_one_eq_zero (by decide) (by decide), Finsupp.sum_single_index rfl]

/-- **Fourth difference of `T` vanishes.** Since `level T = 3 < 4`, the descent
forward direction kills every 4-fold difference. -/
theorem tGate_descent_four (i : Fin n) :
    iterDiff (List.replicate 4 (Pi.single i (1 : ZMod 2))) (DiagPhase.tGatePoly i) = 0 :=
  descent_forward (isMultilinear_tGate i) (by
    rw [List.length_replicate, show DiagPhase.effectiveLevel (DiagPhase.tGatePoly i) = 3 from level_tGate i]
    omega)

/-- **Third difference of `T` does not vanish.** Its value at `0` is `4 ≠ 0` in
`ZMod 8`, computed through the depth-for-degree `−2Δ` tower: with `g` the value
function of `T`, `Δ³g = (−2)·((−2)·Δg)`, and `Δg(0) = g(e) − g(0) = 1`, so
`Δ³g(0) = (−2)·((−2)·1) = 4`. With `tGate_descent_four` this pins `level T = 3`:
the descent is sharp. -/
theorem tGate_descent_three_ne (i : Fin n) :
    iterDiff [Pi.single i 1, Pi.single i 1, Pi.single i 1] (DiagPhase.tGatePoly i) ≠ 0 := by
  have hg0 : (DiagPhase.tGatePoly i).eval 0 = 0 := by
    show MvPolynomial.eval (DiagPhase.liftBinary 0) (MvPolynomial.X i) = 0
    rw [MvPolynomial.eval_X]
    show ((((0 : Fin n → ZMod 2) i).val : ℕ) : ZMod (2 ^ 3)) = 0
    simp
  have hge : (DiagPhase.tGatePoly i).eval (Pi.single i 1) = 1 := by
    show MvPolynomial.eval (DiagPhase.liftBinary (Pi.single i 1)) (MvPolynomial.X i) = 1
    rw [MvPolynomial.eval_X]
    show ((((Pi.single i 1 : Fin n → ZMod 2) i).val : ℕ) : ZMod (2 ^ 3)) = 1
    rw [Pi.single_eq_same]
    decide
  have hval : (iterDiff [Pi.single i 1, Pi.single i 1, Pi.single i 1]
      (DiagPhase.tGatePoly i)).eval 0 = (4 : ZMod (2 ^ 3)) := by
    have e1 : (iterDiff [Pi.single i 1, Pi.single i 1, Pi.single i 1]
        (DiagPhase.tGatePoly i)).eval
        = frameDiff (Pi.single i 1) (frameDiff (Pi.single i 1)
            (frameDiff (Pi.single i 1) (DiagPhase.tGatePoly i).eval)) := by
      rw [iterDiff_cons, iterDiff_cons, iterDiff_cons, iterDiff_nil,
        shiftBy_eval_frameDiff, shiftBy_eval_frameDiff, shiftBy_eval_frameDiff]
    rw [e1, frameDiff_self_eq_neg_two_zsmul]
    show (-2 : ℤ) • frameDiff (Pi.single i 1) (frameDiff (Pi.single i 1)
        (DiagPhase.tGatePoly i).eval) 0 = 4
    rw [frameDiff_self_eq_neg_two_zsmul]
    show (-2 : ℤ) • ((-2 : ℤ) • frameDiff (Pi.single i 1)
        (DiagPhase.tGatePoly i).eval 0) = 4
    rw [frameDiff_apply, zero_add, hge, hg0]
    decide
  intro hzero
  rw [hzero, show (0 : DiagPhase n 3).eval 0 = 0 by simp [DiagPhase.eval]] at hval
  exact absurd hval (by decide)

end FTQCLib.Frame

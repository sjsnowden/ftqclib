/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Bridge.HOFBridge

set_option linter.style.longLine false

/-!
# End-to-end verification — the general degree theorem reproduces the `T`-gate degree

`eval_isPolyDegLE_effectiveLevel` says every multilinear diagonal phase `P` has nonclassical
degree `≤ effectiveLevel P`. This file instantiates it on the concrete `T`-gate polynomial
`PT = X₀` over `ZMod 8` and checks it lands the *same* number as the independent direct proof
`tFn_isPolyDegLE_three`: the `T`-phase's `effectiveLevel` is exactly `3`, and the general theorem
hence gives `IsPolyDegLE 3 tFn`. A consistency check on the `effectiveLevel` bookkeeping through
the general theorem.
-/

namespace FTQCLib.Bridge

open FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Explore.CubicPolarization ECCLib MvPolynomial

/-- The `T`-gate as a diagonal phase polynomial: the single monomial `X₀` over `ZMod 8` (`n=1`, `m=3`). -/
noncomputable def PT : DiagPhase 1 3 := monomial (Finsupp.single (0 : Fin 1) 1) (1 : ZMod (2 ^ 3))

/-- `PT` evaluates to the frame's `T`-phase `tFn = |v₀|`. -/
lemma PT_eval : PT.eval = tFn := by
  funext v
  simp only [PT, DiagPhase.eval, MvPolynomial.eval_monomial, tFn, liftBinary, one_mul]
  rw [Finsupp.prod_single_index (by simp), pow_one]

/-- `PT` is multilinear (its one monomial `X₀` has all exponents `≤ 1`). -/
lemma PT_multilinear : DiagPhase.IsMultilinear PT := by
  intro d hd k
  rw [PT, MvPolynomial.support_monomial, if_neg (by decide : (1 : ZMod (2 ^ 3)) ≠ 0),
    Finset.mem_singleton] at hd
  subst hd
  have hk0 : k = 0 := Subsingleton.elim k 0
  subst hk0
  simp

/-- The `T`-gate's effective level is exactly `3` = interaction `1` + precision `m−1 = 2`
(coefficient `1` is a 2-adic unit, so `twoAdicVal = 0`). -/
lemma PT_effectiveLevel : DiagPhase.effectiveLevel PT = 3 := by
  have h1 : (1 : ZMod (2 ^ 3)) ≠ 0 := by decide
  rw [PT, effectiveLevel_monomial_eq h1]
  have hval : twoAdicVal (1 : ZMod (2 ^ 3)) = 0 := by
    rw [twoAdicVal_of_ne_zero h1, show (1 : ZMod (2 ^ 3)).val = 1 from by decide]
    simp [Nat.factorization_one]
  unfold effLevelMonom
  rw [hval, Finsupp.sum_single_index (by rfl)]

/-- **End-to-end verification:** instantiating the general theorem on `PT` reproduces
`IsPolyDegLE 3 tFn`, agreeing with the independent direct proof `tFn_isPolyDegLE_three`. -/
theorem tFn_isPolyDegLE_three_via_effectiveLevel : IsPolyDegLE 3 tFn := by
  have h := eval_isPolyDegLE_effectiveLevel PT PT_multilinear
  rw [PT_effectiveLevel, PT_eval] at h
  exact h

end FTQCLib.Bridge

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BoolReduceLevel

/-!
# Check: the Boolean normal form's multilinearity and level

Witness rows for `FTQCLib.Hierarchy.BoolReduceLevel`, then the axiom rows. The witness is the
square `X₀²` at precision one: its normal form is `X₀`, one level lower, so the level bound is an
inequality and the normal form is neither the identity nor the zero map. A multilinear exponent
is fixed by the normal form (the row the `levelExt` docstring rested on). `decide` does not run
through `effectiveLevel` (`Nat.factorization` does not reduce), so the level rows go through
`effectiveLevel_monomial_eq` and the `ℕ` arithmetic of `effLevelMonom`.
-/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial

/-! ## Witness rows -/

/-- The square `X₀²` at precision one, as a monomial. -/
noncomputable abbrev sq0 : DiagPhase 1 1 :=
  monomial (Finsupp.single (0 : Fin 1) 2) (1 : ZMod (2 ^ 1))

theorem boolShadow_single_two :
    boolShadow (Finsupp.single (0 : Fin 1) 2) = Finsupp.single (0 : Fin 1) 1 := by
  classical
  refine Finsupp.ext fun k => ?_
  fin_cases k
  simp

/-- The normal form of the square is the variable. -/
theorem boolReduce_sq0 :
    boolReduce sq0 = monomial (Finsupp.single (0 : Fin 1) 1) (1 : ZMod (2 ^ 1)) := by
  rw [boolReduce_monomial (by decide), boolShadow_single_two]

/-- The level drops from `2` to `1`: the bound is an inequality. -/
theorem effectiveLevel_boolReduce_sq0_lt :
    effectiveLevel (boolReduce sq0) < effectiveLevel sq0 := by
  have hc : (1 : ZMod (2 ^ 1)) ≠ 0 := by decide
  rw [boolReduce_sq0, effectiveLevel_monomial_eq hc, effectiveLevel_monomial_eq hc]
  unfold effLevelMonom
  rw [Finsupp.sum_single_index (by rfl), Finsupp.sum_single_index (by rfl)]
  omega

/-- The normal form is not the identity. -/
theorem boolReduce_sq0_ne_self : boolReduce sq0 ≠ sq0 := by
  intro h
  have hlt := effectiveLevel_boolReduce_sq0_lt
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- The normal form is not the zero map. -/
theorem boolReduce_sq0_ne_zero : boolReduce sq0 ≠ 0 := by
  rw [boolReduce_sq0]
  intro h
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 1)) h
  rw [MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
  exact absurd hcoeff (by decide)

/-- `X₀ X₁` at precision two is one multilinear monomial. -/
theorem xx_monomial :
    (X 0 * X 1 : DiagPhase 2 2) = monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [show (X 0 : DiagPhase 2 2) = monomial (Finsupp.single 0 1) 1 from rfl,
    show (X 1 : DiagPhase 2 2) = monomial (Finsupp.single 1 1) 1 from rfl, monomial_mul, mul_one]

theorem isMultilinear_xx : IsMultilinear (X 0 * X 1 : DiagPhase 2 2) := by
  intro d hd k
  rw [xx_monomial, MvPolynomial.support_monomial, if_neg (by decide), Finset.mem_singleton] at hd
  subst hd
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- A multilinear exponent is fixed: `X₀ X₁` at precision two. -/
theorem boolReduce_xx : boolReduce (X 0 * X 1 : DiagPhase 2 2) = X 0 * X 1 :=
  boolReduce_eq_self_of_isMultilinear isMultilinear_xx

/-- `X₀ X₁` has no constant term. -/
theorem coeff_zero_xx : (X 0 * X 1 : DiagPhase 2 2).coeff 0 = 0 := by
  rw [xx_monomial, MvPolynomial.coeff_monomial, if_neg]
  intro h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  simp at this

/-- The extended level of a constant-free multilinear exponent is its level. -/
theorem levelExt_xx :
    FTQCLib.Frame.levelExt (X 0 * X 1 : DiagPhase 2 2) = effectiveLevel (X 0 * X 1 : DiagPhase 2 2) :=
  FTQCLib.Frame.levelExt_eq_effectiveLevel isMultilinear_xx coeff_zero_xx

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_apply_le_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_apply_le_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_isMultilinear' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_isMultilinear

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_boolReduce_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_boolReduce_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.coeff_boolReduce' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_boolReduce

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_monomial' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_monomial

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_eq_self_of_le_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_eq_self_of_le_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_eq_self_of_isMultilinear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_eq_self_of_isMultilinear

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_idem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_idem

/-- info: 'FTQCLib.Frame.levelExt_le_effectiveLevel_sub_C' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.levelExt_le_effectiveLevel_sub_C

/-- info: 'FTQCLib.Frame.levelExt_eq_effectiveLevel' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.levelExt_eq_effectiveLevel

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_boolReduce_sq0_lt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_boolReduce_sq0_lt

/-- info: 'FTQCLib.Frame.levelExt_add_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.levelExt_add_le

/-- info: 'FTQCLib.Frame.levelExt_add_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.levelExt_add_C

end FTQCLib.Hierarchy.DiagPhase

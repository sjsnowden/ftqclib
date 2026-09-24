/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.EffectiveLevel

/-!
# Check: the effective level

Axiom rows for every declaration of `FTQCLib.Hierarchy.EffectiveLevel`, each under a build-failing
`#guard_msgs`. The level's witness rows live beside their consumers (`BoolReduceLevelCheck` for
the normal form's drop, `PolarFormCheck` for the gate polynomials' bounds, `AffineDifferenceCheck`
for the square at precision two); this module is the sweep.
-/

namespace FTQCLib.Hierarchy.DiagPhase

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_of_ne_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_of_ne_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_lt_of_ne_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_lt_of_ne_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.pow_twoAdicVal_dvd_val' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pow_twoAdicVal_dvd_val

/-- info: 'FTQCLib.Hierarchy.DiagPhase.pow_dvd_val_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pow_dvd_val_iff

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_two_mul_ge' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_two_mul_ge

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_neg' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_neg

/-- info: 'FTQCLib.Hierarchy.DiagPhase.twoAdicVal_add_ge_min' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoAdicVal_add_ge_min

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effLevelMonom' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effLevelMonom

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effLevelMonom_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effLevelMonom_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_le_level' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_le_level

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_finsetSum_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_finsetSum_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_add_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_add_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_monomial_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_monomial_eq

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_monomial_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_monomial_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsMultilinear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsMultilinear

/-- info: 'FTQCLib.Hierarchy.DiagPhase.totalDegree_le_effectiveLevel' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalDegree_le_effectiveLevel

/-- info: 'FTQCLib.Hierarchy.DiagPhase.one_le_effectiveLevel_of_pos_totalDegree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_le_effectiveLevel_of_pos_totalDegree

/-- info: 'FTQCLib.Hierarchy.DiagPhase.shiftDeriv_monomial_of_di_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftDeriv_monomial_of_di_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.bind₁_flipShift_monomial_multilinear_di_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind₁_flipShift_monomial_multilinear_di_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.shiftDeriv_monomial_multilinear_di_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftDeriv_monomial_multilinear_di_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.two_mul_monomial' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_monomial

/-- info: 'FTQCLib.Hierarchy.DiagPhase.shiftDeriv_monomial_effectiveLevel_lt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftDeriv_monomial_effectiveLevel_lt

/-- info: 'FTQCLib.Hierarchy.DiagPhase.shiftDeriv_effectiveLevel_lt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftDeriv_effectiveLevel_lt

end FTQCLib.Hierarchy.DiagPhase

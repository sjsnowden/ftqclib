/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BoolReduce

/-!
# Check: the Boolean normal form

Axiom rows for every declaration of `FTQCLib.Hierarchy.BoolReduce`, each under a build-failing
`#guard_msgs`. The normal form's witness rows live in `BoolReduceLevelCheck` (the square at
precision one, where the level drops) and `PolarFormCheck` (the gate polynomials are their own
normal forms); this module is the sweep.
-/

namespace FTQCLib.Hierarchy.DiagPhase

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_apply' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_apply

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_support' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_support

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_apply_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_apply_mem

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_apply_notMem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_apply_notMem

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_sum

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_sum_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_sum_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_sum_superset' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_sum_superset

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_totalDegree_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_totalDegree_le

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_eval_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_eval_eq

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolShadow_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolShadow_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_C

end FTQCLib.Hierarchy.DiagPhase

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs

/-!
# Check: the diagonal phase substrate

Axiom rows for every declaration of `FTQCLib.Hierarchy.Defs`, each under a build-failing `#guard_msgs`.
The substrate every later Hierarchy module is stated over: `DiagPhase`, `liftBinary`, `eval`
with its four algebraic laws, `level` and `discreteDeriv`.

The witness rows for these objects live beside their consumers; this module is the sweep.
-/

namespace FTQCLib.Hierarchy.DiagPhase

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagPhase

/-- info: 'FTQCLib.Hierarchy.DiagPhase.liftBinary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftBinary

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.level' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms level

/-- info: 'FTQCLib.Hierarchy.DiagPhase.discreteDeriv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteDeriv

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_mul

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_X

end FTQCLib.Hierarchy.DiagPhase

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.GatePolynomials

/-!
# Check: the gate phase polynomials

Axiom rows for every declaration of `FTQCLib.Hierarchy.GatePolynomials`, each under a build-failing `#guard_msgs`.
The named exponents — `tGatePoly`, `cczPoly`, `rzGatePoly`, `sGate`, `czGate`, `csPoly` —
with their degrees, levels and the two evaluation lemmas.

The witness rows for these objects live beside their consumers; this module is the sweep.
-/

namespace FTQCLib.Hierarchy.DiagPhase

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.tGatePoly' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tGatePoly

/-- info: 'FTQCLib.Hierarchy.DiagPhase.tGatePoly_totalDegree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tGatePoly_totalDegree

/-- info: 'FTQCLib.Hierarchy.DiagPhase.tGatePoly_level' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tGatePoly_level

/-- info: 'FTQCLib.Hierarchy.DiagPhase.cczPoly' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cczPoly

/-- info: 'FTQCLib.Hierarchy.DiagPhase.rzGatePoly' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rzGatePoly

/-- info: 'FTQCLib.Hierarchy.DiagPhase.rzGatePoly_totalDegree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rzGatePoly_totalDegree

/-- info: 'FTQCLib.Hierarchy.DiagPhase.rzGatePoly_level' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rzGatePoly_level

/-- info: 'FTQCLib.Hierarchy.DiagPhase.cczPoly_totalDegree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cczPoly_totalDegree

/-- info: 'FTQCLib.Hierarchy.DiagPhase.cczPoly_level' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cczPoly_level

/-- info: 'FTQCLib.Hierarchy.DiagPhase.sGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.czGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.csPoly' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms csPoly

/-- info: 'FTQCLib.Hierarchy.DiagPhase.sGate_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sGate_eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.czGate_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czGate_eval

end FTQCLib.Hierarchy.DiagPhase

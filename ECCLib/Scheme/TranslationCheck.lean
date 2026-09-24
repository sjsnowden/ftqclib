/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Translation
import Mathlib.Data.ZMod.Basic

/-!
# Checks for the orbit layer and the commutant theorem

Kernel rows live on the PRIMAL orbit index `orbits H V : Finset (Finset V)` — the one
scheme object a kernel can execute — at the cyclotomic toys
`(ZMod n)ˣ` acting on `ZMod n` by multiplication (Mathlib's `Units` action, computable
`Fintype`): the orbits are `{0}` and the nonzero elements. Nothing indexed by characters
is decided. The algebraic content is covered by the build-failing axiom sweep.
-/

namespace ECCLib.Scheme

/-- `(ZMod 3)ˣ` on `ZMod 3`: two orbits, `{0}` and `{1,2}`. -/
example : (orbits (ZMod 3)ˣ (ZMod 3)).card = 2 := by decide
/-- `(ZMod 5)ˣ` on `ZMod 5`: two orbits, `{0}` and `{1,2,3,4}`. -/
example : (orbits (ZMod 5)ˣ (ZMod 5)).card = 2 := by decide
/-- The orbit of `1` is all four nonzero residues. -/
example : (orb (ZMod 5)ˣ (1 : ZMod 5)).card = 4 := by decide
/-- `0` is fixed: its orbit is a singleton. -/
example : (orb (ZMod 5)ˣ (0 : ZMod 5)).card = 1 := by decide
/-- A discriminating row: the wrong count is refuted. -/
example : ¬ ((orbits (ZMod 5)ˣ (ZMod 5)).card = 3) := by decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.isCompat_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCompat_iff

/-- info: 'ECCLib.Scheme.isCompat_iff_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCompat_iff_commute

/-- info: 'ECCLib.Scheme.mem_schemeAlgebra_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_schemeAlgebra_iff

/-- info: 'ECCLib.Scheme.schemeAlgebra_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.schemeAlgebra_mul_comm

/-- info: 'ECCLib.Scheme.linearIndependent_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.linearIndependent_adj

/-- info: 'ECCLib.Scheme.finrank_schemeAlgebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.finrank_schemeAlgebra

/-- info: 'ECCLib.Scheme.sum_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_orbits

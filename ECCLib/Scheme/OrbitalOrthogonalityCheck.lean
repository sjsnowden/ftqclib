/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitalOrthogonality
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance rows for the orbital orthogonality

The transpose count is kernel-checked at the **non-symmetric** cyclotomic carrier
`(ZMod 4)ˣ` on `ZMod 4`, where the orbital of `(0, 1)` is genuinely distinct from its
transpose — the rows that show the transpose diagonal is load-bearing, not decoration. The
spectral results are noncomputable; their live instantiations are the Johnson and Hamming
orthogonality check modules, and their algebraic content is accepted by the build-failing
axiom sweep.
-/

namespace ECCLib.Scheme

open Matrix

/-- The transpose count fires on the transpose diagonal: the orbital of `(0,1)` under
`(ZMod 4)ˣ` is `{(0,1),(0,3)}`, its transpose is the orbital of `(1,0)`, and the paired
trace counts both pairs. -/
example : (orbitalAdj ℤ (orb (ZMod 4)ˣ ((0, 1) : ZMod 4 × ZMod 4))
    * orbitalAdj ℤ (orb (ZMod 4)ˣ ((1, 0) : ZMod 4 × ZMod 4))).trace = 2 := by decide

/-- Off the transpose diagonal the trace vanishes — here at a **non-symmetric** orbital
paired with itself. -/
example : (orbitalAdj ℤ (orb (ZMod 4)ˣ ((0, 1) : ZMod 4 × ZMod 4))
    * orbitalAdj ℤ (orb (ZMod 4)ˣ ((0, 1) : ZMod 4 × ZMod 4))).trace = 0 := by decide

/-- A discriminating row: the wrong pairing value is refuted. -/
example : ¬((orbitalAdj ℤ (orb (ZMod 4)ˣ ((0, 1) : ZMod 4 × ZMod 4))
    * orbitalAdj ℤ (orb (ZMod 4)ˣ ((1, 0) : ZMod 4 × ZMod 4))).trace = 0) := by decide

/-- The transpose orbital, concretely: transposing the orbital of `(0,1)` gives the orbital
of `(1,0)`. -/
example : transposePairs (orb (ZMod 4)ˣ ((0, 1) : ZMod 4 × ZMod 4))
    = orb (ZMod 4)ˣ ((1, 0) : ZMod 4 × ZMod 4) := by decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.splitChar_orbitalBasis' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.splitChar_orbitalBasis

/-- info: 'ECCLib.Scheme.sum_spectralMult_mul_eigenmatrixP_mul_eigenmatrixP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_spectralMult_mul_eigenmatrixP_mul_eigenmatrixP

/-- info: 'ECCLib.Scheme.card_mul_eigenmatrixQ_transposePairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_mul_eigenmatrixQ_transposePairs

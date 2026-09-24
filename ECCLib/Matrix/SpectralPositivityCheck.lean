/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.SpectralPositivity
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Acceptance rows for the positivity bridge

The theorems here are hypothesis-carrying and consumed live downstream
(`Scheme/OrbitalPositivity.lean` discharges the `⋆`-closure at every orbital algebra, so
non-vacuity is witnessed by the library itself). The row this module owns is the
**control aimed at the `⋆`-closure hypothesis**: `!![1,1;0,0]` is idempotent and not
Hermitian, so idempotency alone never yields the conclusion — the hypothesis is
load-bearing, not decoration. (The mutant it rules out: a "proof" that never used
`hstar` would have to derive Hermitian from idempotency, which this matrix refutes.)
-/

namespace ECCLib.Scheme

open Matrix

/-- The control matrix: idempotent. -/
example : IsIdempotentElem !![(1 : ℂ), 1; 0, 0] := by
  unfold IsIdempotentElem
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Control — the `⋆`-closure hypothesis is load-bearing**: the same matrix is not
Hermitian, so no argument from idempotency alone can reach
`conjTranspose_coe_primitiveIdempotent`'s conclusion. -/
example : ¬(!![(1 : ℂ), 1; 0, 0]ᴴ = !![(1 : ℂ), 1; 0, 0]) := by
  intro h
  have h2 := congrFun (congrFun h 0) 1
  simp [Matrix.conjTranspose_apply] at h2

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.coe_primitiveIdempotent_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coe_primitiveIdempotent_ne_zero

/-- info: 'ECCLib.Scheme.spectralMult_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.spectralMult_ne_zero

/-- info: 'ECCLib.Scheme.conjTranspose_coe_primitiveIdempotent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.conjTranspose_coe_primitiveIdempotent

/-- info: 'ECCLib.Scheme.isHermitian_coe_primitiveIdempotent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isHermitian_coe_primitiveIdempotent

/-- info: 'ECCLib.Scheme.posSemidef_coe_primitiveIdempotent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.posSemidef_coe_primitiveIdempotent

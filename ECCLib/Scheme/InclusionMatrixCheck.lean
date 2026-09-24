/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.InclusionMatrix

/-!
# Acceptance rows for the inclusion matrix

Kernel rows over `ℤ` at `n = 3, t = 1, k = 2`: the Gram entries are the binomial double
counts they claim to be, with a discriminating off-value, and the two Gram products land in
their orbital algebras at a live carrier. The algebraic content is accepted by the
build-failing axiom sweep.
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix

/-- `(NᵀN)[K,K'] = C(#(K∩K'), t)`: two `2`-sets meeting in one point admit one common
`1`-subset. -/
example : ((inclMatrix ℤ 3 1 2)ᵀ * inclMatrix ℤ 3 1 2)
    ⟨{0, 1}, by decide⟩ ⟨{0, 2}, by decide⟩ = 1 := by decide

/-- The diagonal Gram entry counts all `1`-subsets of a `2`-set. -/
example : ((inclMatrix ℤ 3 1 2)ᵀ * inclMatrix ℤ 3 1 2)
    ⟨{0, 1}, by decide⟩ ⟨{0, 1}, by decide⟩ = 2 := by decide

/-- A discriminating row: the wrong entry is refuted. -/
example : ¬(((inclMatrix ℤ 3 1 2)ᵀ * inclMatrix ℤ 3 1 2)
    ⟨{0, 1}, by decide⟩ ⟨{0, 2}, by decide⟩ = 2) := by decide

/-- `(NNᵀ)[A,B] = C(n − #(A∪B), k − #(A∪B))`: two distinct points lie in one common
`2`-set of `[3]`. -/
example : (inclMatrix ℤ 3 1 2 * (inclMatrix ℤ 3 1 2)ᵀ)
    ⟨{0}, by decide⟩ ⟨{1}, by decide⟩ = 1 := by decide

/-- One point lies in two `2`-sets of `[3]`. -/
example : (inclMatrix ℤ 3 1 2 * (inclMatrix ℤ 3 1 2)ᵀ)
    ⟨{0}, by decide⟩ ⟨{0}, by decide⟩ = 2 := by decide

end ECCLib.Scheme.Johnson

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.Johnson.inclMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.inclMatrix

/-- info: 'ECCLib.Scheme.Johnson.inclMatrix_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.inclMatrix_apply

/-- info: 'ECCLib.Scheme.Johnson.transpose_mul_inclMatrix_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.transpose_mul_inclMatrix_apply

/-- info: 'ECCLib.Scheme.Johnson.inclMatrix_mul_transpose_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.inclMatrix_mul_transpose_apply

/-- info: 'ECCLib.Scheme.Johnson.smul_subset_smul_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.smul_subset_smul_iff

/-- info: 'ECCLib.Scheme.Johnson.transpose_mul_inclMatrix_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.transpose_mul_inclMatrix_mem

/-- info: 'ECCLib.Scheme.Johnson.inclMatrix_mul_transpose_mem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.inclMatrix_mul_transpose_mem

/-- info: 'ECCLib.Scheme.Johnson.conjTranspose_inclMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.conjTranspose_inclMatrix

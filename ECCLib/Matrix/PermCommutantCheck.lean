/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.PermCommutant
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance rows for permutation commutants

Axiom sweeps, and the rows showing that the two closure lemmas are stated at genuinely different
strengths for a reason.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.commute_permMatrix_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.commute_permMatrix_iff

/-- info: 'ECCLib.Scheme.mem_permCommutant_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_permCommutant_iff

/-- info: 'ECCLib.Scheme.mem_permCommutant_closure_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_permCommutant_closure_iff

/-- info: 'ECCLib.Scheme.transpose_mem_permCommutant' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transpose_mem_permCommutant

/-! ## Discriminating rows: the base ring really is generic, and the two closures differ

`commute_permMatrix_iff` is stated at `[Semiring R]` — not a commutative ring, not a field, and
certainly not `ℂ`. These rows exercise it where the original `ℂ`-only statement could not go. -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Over `ZMod 2`, where the qLDPC-facing consumer lives. Named rather than anonymous so the
module owns a declaration: the ontology extractor requires every module to emit at least one
node, and an all-`example` check module emits none. -/
theorem commute_permMatrix_iff_zmod2 (σ : Equiv.Perm n) (M : Matrix n n (ZMod 2)) :
    M * σ.permMatrix (ZMod 2) = σ.permMatrix (ZMod 2) * M ↔ ∀ x y, M (σ x) (σ y) = M x y :=
  commute_permMatrix_iff σ M

/-- Over `ℕ`, a semiring with no negation at all — which pins that `Semiring` is the real
hypothesis and not shorthand for something stronger. -/
example (σ : Equiv.Perm n) (M : Matrix n n ℕ) :
    M * σ.permMatrix ℕ = σ.permMatrix ℕ * M ↔ ∀ x y, M (σ x) (σ y) = M x y :=
  commute_permMatrix_iff σ M

/-- Transpose-closure needs only a commutative base, so it is available over `ZMod 2`. -/
example {S : Set (Equiv.Perm n)} {M : Matrix n n (ZMod 2)}
    (hM : M ∈ permCommutant (ZMod 2) S) : Mᵀ ∈ permCommutant (ZMod 2) S :=
  transpose_mem_permCommutant hM

/-- Conjugate-transpose closure needs a `StarRing`, which `ZMod n` does not have — so the two
lemmas are stated separately rather than merged. Here it is over `ℂ`, where the star exists. -/
example {S : Set (Equiv.Perm n)} {M : Matrix n n ℂ}
    (hM : M ∈ permCommutant ℂ S) : Mᴴ ∈ permCommutant ℂ S :=
  conjTranspose_mem_permCommutant hM

/-- Neither closure lemma places any hypothesis on `S`: the empty set of permutations works, and
so does the set of *all* of them. -/
example {M : Matrix n n ℂ} (hM : M ∈ permCommutant ℂ (∅ : Set (Equiv.Perm n))) :
    Mᴴ ∈ permCommutant ℂ (∅ : Set (Equiv.Perm n)) :=
  conjTranspose_mem_permCommutant hM

example {M : Matrix n n ℂ} (hM : M ∈ permCommutant ℂ (Set.univ : Set (Equiv.Perm n))) :
    Mᴴ ∈ permCommutant ℂ (Set.univ : Set (Equiv.Perm n)) :=
  conjTranspose_mem_permCommutant hM

end Generic

end ECCLib.Scheme

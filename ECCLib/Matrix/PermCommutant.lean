/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Star.Subalgebra

/-!
# Matrices that commute with permutation matrices

A matrix commutes with the permutation matrix of `σ` exactly when its entries are invariant
under `σ` acting on both indices at once. Everything in this file is that observation and its
immediate consequences for the commutant of a **set** of permutations.

## Main definitions

* `permMats` — the permutation matrices of a set of permutations.
* `permCommutant` — the subalgebra of matrices commuting with all of them.

## Main results

* `commute_permMatrix_iff` — commuting is entrywise invariance.
* `mem_permCommutant_iff` — membership is entrywise invariance under every member of the set.
* `conjTranspose_mem_permCommutant` — the commutant is closed under the conjugate transpose,
  with **no hypothesis on the set at all**.

## Why a set and not a group

The set is the primary form deliberately. A commutant is determined by the subgroup its
generators generate, so nothing is lost; and the layers that consume this centralize two
families at once — translations together with a symmetry action — which only the set form
expresses without first constructing the group they generate.

## Why this lives here

Nothing here mentions an orbit, a scheme or a particular ring, so it belongs
at the lowest layer that can state it. Two consumers want it and neither wants the other's
context: the orbital layer above, and — over `ZMod 2` — the regular representation of a group
on itself, where `commute_permMatrix_iff` is the matrix form of left/right commutation.

## Implementation notes

Stated over an arbitrary `Semiring R` (a `CommSemiring` for the subalgebra, which needs a
commutative base to be an algebra at all). The proofs are the ones written for `ℂ` in the
translation layer and they transfer unchanged: the argument is a re-indexing through
`PEquiv.toMatrix_toPEquiv_mul` and `PEquiv.mul_toMatrix_toPEquiv`, and nothing in it is
scalar-specific.

The declarations use the namespace `ECCLib.Scheme`, where they were first stated, so that
their consumers are unaffected by the file's location. The namespace does not match the
directory.
-/

namespace ECCLib.Scheme

open Matrix

section PermMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Semiring R]

/-- A matrix commutes with the permutation matrix of `σ` exactly when its entries are
invariant under `σ` on both indices. -/
theorem commute_permMatrix_iff (σ : Equiv.Perm n) (M : Matrix n n R) :
    M * σ.permMatrix R = σ.permMatrix R * M ↔ ∀ x y, M (σ x) (σ y) = M x y := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  constructor
  · intro h x y
    have := congrFun (congrFun h x) (σ y)
    simpa [Matrix.submatrix_apply] using this.symm
  · intro h
    ext x y
    simp only [Matrix.submatrix_apply, id]
    have := h x (σ.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

end PermMatrix

section Commutant

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (R : Type*) [CommSemiring R]

/-- The permutation matrices of a set of permutations. -/
def permMats (S : Set (Equiv.Perm X)) : Set (Matrix X X R) :=
  (fun σ : Equiv.Perm X => σ.permMatrix R) '' S

/-- The matrices commuting with every permutation matrix of `S`. A centralizer is a
subalgebra for free, which is the reason this construction is taken as primitive rather
than an association scheme's axioms. -/
def permCommutant (S : Set (Equiv.Perm X)) : Subalgebra R (Matrix X X R) :=
  Subalgebra.centralizer R (permMats R S)

variable {R}

/-- Membership in the commutant is entrywise invariance under every member of the set. -/
theorem mem_permCommutant_iff {S : Set (Equiv.Perm X)} (M : Matrix X X R) :
    M ∈ permCommutant R S ↔ ∀ σ ∈ S, ∀ x y, M (σ x) (σ y) = M x y := by
  rw [permCommutant, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h σ hσ x y
    exact (commute_permMatrix_iff _ M).mp (h _ ⟨σ, hσ, rfl⟩).symm x y
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact ((commute_permMatrix_iff _ M).mpr (fun x y => h σ hσ x y)).symm

/-- **The commutant is `⋆`-closed, with no hypothesis on `S` whatsoever.** If `M` is constant
on the pairs `S` identifies, so is `Mᴴ`, because conjugation acts entrywise and swapping the
two indices preserves the invariance condition. This is what makes reducedness available over
`ℂ` without assuming the scheme is symmetric. -/
theorem conjTranspose_mem_permCommutant [StarRing R] {S : Set (Equiv.Perm X)}
    {M : Matrix X X R} (hM : M ∈ permCommutant R S) : Mᴴ ∈ permCommutant R S := by
  rw [mem_permCommutant_iff] at hM ⊢
  intro σ hσ x y
  simp only [Matrix.conjTranspose_apply]
  exact congrArg star (hM σ hσ y x)

/-- The transpose analogue, over a commutative ring and with no hypothesis on `S`. -/
theorem transpose_mem_permCommutant {S : Set (Equiv.Perm X)} {M : Matrix X X R}
    (hM : M ∈ permCommutant R S) : Mᵀ ∈ permCommutant R S := by
  rw [mem_permCommutant_iff] at hM ⊢
  intro σ hσ x y
  simp only [Matrix.transpose_apply]
  exact hM σ hσ y x

/-- **The commutant of a set is the commutant of the group it generates.** This is what makes
the set form lossless: nothing is given up by not passing to the generated subgroup first, and
a layer centralizing two families at once never has to construct the group they generate. -/
theorem mem_permCommutant_closure_iff {S : Set (Equiv.Perm X)} (M : Matrix X X R) :
    M ∈ permCommutant R S ↔ M ∈ permCommutant R (Subgroup.closure S : Set (Equiv.Perm X)) := by
  rw [mem_permCommutant_iff, mem_permCommutant_iff]
  refine ⟨fun h σ hσ => ?_, fun h σ hσ => h σ (Subgroup.subset_closure hσ)⟩
  induction hσ using Subgroup.closure_induction with
  | mem σ hs => exact h σ hs
  | one => intro x y; rfl
  | mul a b _ _ ha hb =>
      intro x y
      have := ha (b x) (b y)
      rw [hb x y] at this
      exact this
  | inv a _ ha =>
      intro x y
      have := ha (a⁻¹ x) (a⁻¹ y)
      simpa using this.symm

end Commutant

end ECCLib.Scheme

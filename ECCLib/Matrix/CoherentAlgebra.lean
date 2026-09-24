/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.PermCommutant
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# Coherent algebras, and the commutant as one

A **coherent algebra** is a matrix algebra containing the identity `1` and the all-ones matrix
`J`, closed under the Schur (Hadamard) product and under transpose. The commutant of any set of
permutation matrices is one. That statement is Godsil §1.3.2, and the object it names is the
centralizer ring of a coherent configuration in the sense of Higman (1970).

`ECCLib/Matrix/PermCommutant.lean` already supplies two of the four axioms for free —
`permCommutant` is a `Subalgebra`, so it contains `1`, and `transpose_mem_permCommutant` gives
transpose-closure with no hypothesis on the generating set. This file supplies the other two.

## Main definitions

* `IsCoherentAlgebra` — the four axioms, as a `Prop` on a subalgebra of matrices.

## Main results

* `hadamard_mem_permCommutant` — the commutant is closed under the Schur product.
* `of_one_mem_permCommutant` — the all-ones matrix lies in every permutation commutant.
* `isCoherentAlgebra_permCommutant` — **the commutant of any set of permutation matrices is a
  coherent algebra**, with no hypothesis whatsoever on the set.

## Why this is cheaper here than in the source

Godsil argues at matrix level: `P (M ⊙ N) = (PM) ⊙ (PN) = (MP) ⊙ (NP) = (M ⊙ N) P`. Our
`mem_permCommutant_iff` states membership *entrywise* — a choice made in `PermCommutant.lean`
for unrelated reasons — so the Schur product's own defining equation is the entire proof, and no
matrix identity is needed. The all-ones matrix is invariant under relabelling by inspection, so
its membership is `rfl` four binders deep.

## On the axiom set, which is a choice

Godsil gives the definition twice and the two do not agree. §1.3 asks for closure under complex
conjugation as well, and so is available only over a `⋆`-ring; §16.10 asks only for `1`, `J`,
Schur and transpose. **This file takes §16.10**, because it is ring-generic and the whole point
of the layer is that it does not need `ℂ`. Higman's own 1970 statement of the centralizer ring is
over an arbitrary commutative coefficient ring, so the general form is the historically canonical
one rather than a modern weakening.

Nothing is lost: `⋆`-closure is already available as `conjTranspose_mem_permCommutant` under
`[StarRing R]`, and `isCoherentAlgebra_permCommutant` composes with it wherever both hold.

Note also that the hypothesis here is `[CommSemiring R]`, weaker than the `[CommRing R]` the
orbital basis needs. Schur closure consumes no subtraction.

## Implementation notes

`IsCoherentAlgebra` is a `Prop` structure rather than a class. It has exactly one consumer in
this library. A structure states the theorem without asking the
instance machinery to carry a concept that nothing yet dispatches on.

The `Schur` field is stated on the carrier (`M ∈ S → N ∈ S → M ⊙ N ∈ S`) rather than as a
second algebra structure on `S`. The Schur product is not the subalgebra's multiplication and
giving it one would collide with the `Subalgebra` instance already there.

This module declares `namespace ECCLib.Scheme`, following `PermCommutant.lean`, whose
objects it is about. Note that `ECCLib/Matrix/CommStarMatrix.lean` in the same directory
declares `namespace ECCLib` instead.

## References

Godsil, *Association Schemes* (2010 lecture notes), §1.3 and §16.10; Higman, *Coherent
configurations I*, Rend. Sem. Mat. Univ. Padova **44** (1970), §§3–4.
-/

namespace ECCLib.Scheme

open Matrix

section Coherent

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {R : Type*} [CommSemiring R]

/-- **A coherent algebra**: a matrix subalgebra containing the all-ones matrix and closed under
both the Schur product and transpose. Containment of `1` is already part of being a subalgebra
and so is not repeated as a field. -/
structure IsCoherentAlgebra (S : Subalgebra R (Matrix X X R)) : Prop where
  /-- The all-ones matrix — the unit of the Schur product — is a member. -/
  of_one_mem : (Matrix.of 1 : Matrix X X R) ∈ S
  /-- Closure under the Schur (Hadamard) product. -/
  hadamard_mem : ∀ {M N : Matrix X X R}, M ∈ S → N ∈ S → M ⊙ N ∈ S
  /-- Closure under transpose. -/
  transpose_mem : ∀ {M : Matrix X X R}, M ∈ S → Mᵀ ∈ S

/-- The identity matrix is a member, recovered from the subalgebra structure. -/
theorem IsCoherentAlgebra.one_mem {S : Subalgebra R (Matrix X X R)}
    (_ : IsCoherentAlgebra S) : (1 : Matrix X X R) ∈ S :=
  S.one_mem

/-! ## The commutant satisfies the two missing axioms -/

/-- **The commutant is closed under the Schur product**, with no hypothesis on `S`. Membership is
entrywise invariance, and the Schur product is defined entrywise, so the two compose directly. -/
theorem hadamard_mem_permCommutant {S : Set (Equiv.Perm X)} {M N : Matrix X X R}
    (hM : M ∈ permCommutant R S) (hN : N ∈ permCommutant R S) :
    M ⊙ N ∈ permCommutant R S := by
  rw [mem_permCommutant_iff] at hM hN ⊢
  intro σ hσ x y
  simp only [Matrix.hadamard_apply]
  rw [hM σ hσ x y, hN σ hσ x y]

/-- **The all-ones matrix lies in every permutation commutant.** A constant matrix is invariant
under relabelling both indices, so this holds for any `S` at all. -/
theorem of_one_mem_permCommutant (S : Set (Equiv.Perm X)) :
    (Matrix.of 1 : Matrix X X R) ∈ permCommutant R S :=
  (mem_permCommutant_iff _).mpr fun _ _ _ _ => rfl

/-- **The commutant of any set of permutation matrices is a coherent algebra** (Godsil §1.3.2).
No hypothesis on the set: it need not be a group, need not be transitive, and the ring need only
be a commutative semiring. -/
theorem isCoherentAlgebra_permCommutant (S : Set (Equiv.Perm X)) :
    IsCoherentAlgebra (permCommutant R S) where
  of_one_mem := of_one_mem_permCommutant S
  hadamard_mem := hadamard_mem_permCommutant
  transpose_mem := transpose_mem_permCommutant

/-! ## The all-ones matrix, as the object the axioms are about

Two facts kept here rather than left implicit, because `1` and `of 1` are different matrices and
confusing them silently produces statements that are true for the wrong reason. -/

omit [Fintype X] [DecidableEq X] in
/-- Every entry of the all-ones matrix is `1`. -/
@[simp] theorem of_one_apply (x y : X) : (Matrix.of 1 : Matrix X X R) x y = 1 := rfl

omit [Fintype X] [DecidableEq X] in
/-- The all-ones matrix is the unit of the Schur product, which is why it is the axiom rather
than an arbitrary choice of distinguished element. -/
theorem hadamard_of_one_self (M : Matrix X X R) : M ⊙ (Matrix.of 1 : Matrix X X R) = M :=
  Matrix.hadamard_of_one M

end Coherent

end ECCLib.Scheme

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.Ring

/-!
# Structure constants of a based algebra

Fix a basis of an algebra. Every product of basis elements expands in that basis, and the
coefficients are the **structure constants**. This file defines them and proves the two
coordinate identities they satisfy: multiplication in coordinates is the bilinear form of the
structure constants, and multiplication by a fixed element is a matrix.

## Main definitions

* `strConst` — the structure constants: the coordinates of a product of basis elements.
* `constMulMat` — the matrix of multiplication by a fixed algebra element.

## Main results

* `repr_mul` — **the coordinate theorem**: `⟪x * y⟫ₖ = Σᵢⱼ cᵢⱼₖ ⟪x⟫ᵢ ⟪y⟫ⱼ`.
* `repr_const_mul` — the single-sum analogue for a fixed left factor.
* `mul_basis_eq_repr_smul` — for an **orthogonally idempotent** basis the structure constants
  are diagonal: `x * bᵢ = ⟪x⟫ᵢ • bᵢ`. This is the eigenvalue equation of every split algebra's
  primitive-idempotent basis, before any vector appears.

## Generality

`[CommRing R] [CommRing A] [Algebra R A]` with a basis indexed by `Fin m`. **No field, no
irreducibility, no finiteness of `A` beyond the basis, no characteristic assumption.** The
coordinate theorem is hypothesis-free because the structure constants are *defined* as the
thing it expands into, rather than characterised by some other property and then related.

## Implementation notes

This file is kept separate from `ECCLib/GateAlgebra.lean`, which imports `ECCLib.Circuit`:
nothing here needs a circuit, a netlist, or `ZMod 2`; the mathematics is about a basis of an
algebra and nothing else, so consumers that want only the coordinate theory import only the
coordinate theory.

The basis is indexed by `Fin m` rather than an arbitrary `Fintype`; a caller with a
differently-indexed basis reindexes through `Basis.reindex`.

`open Module` is required: in this Mathlib `Basis` lives in the `Module` namespace, and the bare
name does not resolve without it.
-/

namespace ECCLib

open Module

section CoordinateTheorem

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {m : ℕ}

/-- The **structure constants** of a based algebra: the coordinates of products of basis
elements. Defined as exactly the coefficients the coordinate identity below expands into, which
is why that identity carries no hypotheses. -/
noncomputable def strConst (B : Basis (Fin m) R A) (i j k : Fin m) : R := B.repr (B i * B j) k

/-- **The coordinate theorem**: multiplication in any based algebra, in coordinates, is the
bilinear form of the structure constants. No field, no irreducibility, no finiteness of `A`,
no characteristic. -/
theorem repr_mul (B : Basis (Fin m) R A) (x y : A) (k : Fin m) :
    B.repr (x * y) k = ∑ i, ∑ j, strConst B i j k * (B.repr x i * B.repr y j) := by
  calc B.repr (x * y) k
      = B.repr ((∑ i, B.repr x i • B i) * (∑ j, B.repr y j • B j)) k := by
        rw [B.sum_repr x, B.sum_repr y]
    _ = ∑ i, ∑ j, (B.repr x i * B.repr y j) • B.repr (B i * B j) k := by
        rw [Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finsupp.finset_sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply]
    _ = ∑ i, ∑ j, strConst B i j k * (B.repr x i * B.repr y j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_mul, strConst]
        ring

/-- The single-sum analogue for multiplication by a fixed constant: `a · x` in coordinates is
the matrix `constMulMat B a` applied to the coordinates of `x`. -/
noncomputable def constMulMat (B : Basis (Fin m) R A) (a : A) : Matrix (Fin m) (Fin m) R :=
  fun k i => B.repr (a * B i) k

theorem repr_const_mul (B : Basis (Fin m) R A) (a x : A) (k : Fin m) :
    B.repr (a * x) k = ∑ i, constMulMat B a k i * B.repr x i := by
  calc B.repr (a * x) k
      = B.repr (a * ∑ i, B.repr x i • B i) k := by rw [B.sum_repr x]
    _ = B.repr (∑ i, B.repr x i • (a * B i)) k := by
        have h : a * (∑ i, B.repr x i • B i) = ∑ i, B.repr x i • (a * B i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
        rw [h]
    _ = ∑ i, B.repr x i • B.repr (a * B i) k := by
        rw [map_sum, Finsupp.finset_sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Finsupp.smul_apply]
    _ = ∑ i, constMulMat B a k i * B.repr x i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_eq_mul, constMulMat]
        ring

end CoordinateTheorem

/-! ## Orthogonal idempotent bases

A separate section because the hypotheses are strictly weaker than the coordinate theorem's:
no commutativity of the algebra, a semiring of scalars, and an arbitrary finite index. -/

section OrthogonalIdempotentBasis

variable {K A ι : Type*} [CommSemiring K] [Semiring A] [Algebra K A] [Finite ι]

/-- When the basis is a family of **orthogonal idempotents**, multiplication against a basis
element reads off a single coordinate: `x * bᵢ = ⟪x⟫ᵢ • bᵢ`. Equivalently, the structure
constants are diagonal. No commutativity, no field, no `DecidableEq` — expanding `x` in the
basis kills every cross term by orthogonality and fixes the diagonal one by idempotence.

For the primitive-idempotent basis of a split commutative algebra this is the eigenvalue
equation inside the algebra, which is why the spectral layers consume it. -/
theorem mul_basis_eq_repr_smul (b : Basis ι K A) (hb : OrthogonalIdempotents ⇑b) (x : A)
    (i : ι) : x * b i = b.repr x i • b i := by
  haveI := Fintype.ofFinite ι
  conv_lhs => rw [← b.sum_repr x]
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, (hb.idem i).eq]
  · intro j _ hj
    rw [smul_mul_assoc, hb.ortho hj, smul_zero]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

end OrthogonalIdempotentBasis

end ECCLib

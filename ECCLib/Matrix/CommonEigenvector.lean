/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Common eigenvectors of a matrix subalgebra

A vector that every member of a matrix subalgebra scales, together with the scaling
functional. Over a ring with no zero divisors the functional is an algebra character
(`IsCommonEigenvector.algHom`) and is determined by the vector (`eigenvalue_unique`). The
constructor `isCommonEigenvector_basis` builds the functional from eigen-equations on a basis
of the subalgebra — the form both carriers actually supply.

Mentions no group, no orbit, no scheme, no `ℂ`: this is the lowest layer that can state any of
it, and the module every carrier enters the spectral theory through.

## Main definitions

* `IsCommonEigenvector S v χ` — `v ≠ 0` and every `M ∈ S` scales `v` by `χ M`.
* `IsCommonEigenvector.algHom` — the functional, as an algebra character `↥S →ₐ[K] K`.

## Main results

* `IsCommonEigenvector.eigenvalue_unique` — the functional is determined by the vector.
* `isCommonEigenvector_basis` — eigen-equations on a basis extend to the whole subalgebra,
  with the functional given by an explicit linear formula, no choice.

## Generality

The definition needs `[CommSemiring K]`. The character needs `[CommRing K]
[NoZeroDivisors K]` — **not** a field: the scalar is never divided by, only cancelled at a
nonzero coordinate. (It is tempting to assume `Field` is needed; the check module builds the
character over `ℤ` to show it is not.)

## Implementation notes

The functional `χ` is **data**, not an existential: both carriers know their eigenvalues in
closed form, and carrying the formula in the statement is what lets downstream identifications
(`eberlein`, `kraw`) be stated as equations rather than through a choice function.

The namespace is `ECCLib.Scheme`, following `Matrix/PermCommutant.lean`.
-/

namespace ECCLib.Scheme

open Matrix Module

section Def

variable {K X : Type*} [CommSemiring K] [Fintype X] [DecidableEq X]

/-- A **common eigenvector** of a matrix subalgebra, with its scaling functional as data:
`v` is nonzero and every member of `S` scales it by the functional's value. -/
structure IsCommonEigenvector (S : Subalgebra K (Matrix X X K)) (v : X → K)
    (χ : ↥S → K) : Prop where
  ne_zero : v ≠ 0
  mulVec_eq : ∀ M : ↥S, (M : Matrix X X K) *ᵥ v = χ M • v

/-- Eigen-equations on a **basis** of the subalgebra extend to the whole subalgebra, with the
functional given by the explicit linear formula. This is the constructor the carriers use:
each knows its eigenvalues only on the distinguished basis. -/
theorem isCommonEigenvector_basis {S : Subalgebra K (Matrix X X K)} {ι : Type*} [Fintype ι]
    (B : Basis ι K ↥S) (μ : ι → K) {v : X → K} (hv : v ≠ 0)
    (h : ∀ i, ((B i : ↥S) : Matrix X X K) *ᵥ v = μ i • v) :
    IsCommonEigenvector S v (fun M => ∑ i, B.repr M i * μ i) where
  ne_zero := hv
  mulVec_eq M := by
    conv_lhs => rw [← B.sum_repr M]
    simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, Matrix.sum_mulVec,
      Matrix.smul_mulVec, h, smul_smul, ← Finset.sum_smul]

end Def

/-- Cancellation at a nonzero vector: equal scalings have equal scalars. This is the whole
reason `NoZeroDivisors` suffices where a field looks needed. Stated with no instances on `X`
at all — it is a fact about functions. -/
theorem eq_of_smul_eq_smul_of_ne_zero {K X : Type*} [Ring K] [NoZeroDivisors K]
    {v : X → K} (hv : v ≠ 0) {c d : K} (h : c • v = d • v) : c = d := by
  obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    exact hv (funext hno)
  have hcd := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at hcd
  have hsub : (c - d) * v x = 0 := by rw [sub_mul, hcd, sub_self]
  rcases mul_eq_zero.mp hsub with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hx

section Character

variable {K X : Type*} [CommRing K] [NoZeroDivisors K] [Fintype X] [DecidableEq X]

namespace IsCommonEigenvector

variable {S : Subalgebra K (Matrix X X K)} {v : X → K} {χ χ' : ↥S → K}

/-- The functional is determined by the vector. -/
theorem eigenvalue_unique (h : IsCommonEigenvector S v χ)
    (h' : IsCommonEigenvector S v χ') : χ = χ' :=
  funext fun M =>
    eq_of_smul_eq_smul_of_ne_zero h.ne_zero ((h.mulVec_eq M).symm.trans (h'.mulVec_eq M))

/-- The functional of a common eigenvector is an **algebra character**. Multiplicativity is
`(MN)v = M(Nv) = χ(N)·(Mv) = χ(M)χ(N)·v`; every law is the same cancellation at the nonzero
vector. -/
def algHom (h : IsCommonEigenvector S v χ) : ↥S →ₐ[K] K where
  toFun := χ
  map_one' := eq_of_smul_eq_smul_of_ne_zero h.ne_zero (by
    have h1 := h.mulVec_eq 1
    rw [OneMemClass.coe_one, Matrix.one_mulVec] at h1
    rw [one_smul]
    exact h1.symm)
  map_mul' M N := eq_of_smul_eq_smul_of_ne_zero h.ne_zero (by
    have hchain : ((M * N : ↥S) : Matrix X X K) *ᵥ v = (χ M * χ N) • v := by
      rw [MulMemClass.coe_mul, ← Matrix.mulVec_mulVec, h.mulVec_eq N, Matrix.mulVec_smul,
        h.mulVec_eq M, smul_smul, mul_comm (χ N) (χ M)]
    rw [← h.mulVec_eq (M * N), hchain])
  map_zero' := eq_of_smul_eq_smul_of_ne_zero h.ne_zero (by
    have h0 := h.mulVec_eq 0
    rw [ZeroMemClass.coe_zero, Matrix.zero_mulVec] at h0
    rw [zero_smul]
    exact h0.symm)
  map_add' M N := eq_of_smul_eq_smul_of_ne_zero h.ne_zero (by
    have hMN := h.mulVec_eq (M + N)
    rw [AddMemClass.coe_add, Matrix.add_mulVec, h.mulVec_eq M, h.mulVec_eq N,
      ← add_smul] at hMN
    exact hMN.symm)
  commutes' c := by
    refine eq_of_smul_eq_smul_of_ne_zero h.ne_zero ?_
    have hc := h.mulVec_eq (algebraMap K ↥S c)
    rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec] at hc
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    exact hc.symm

theorem coe_algHom (h : IsCommonEigenvector S v χ) : ⇑h.algHom = χ := rfl

end IsCommonEigenvector

end Character

end ECCLib.Scheme

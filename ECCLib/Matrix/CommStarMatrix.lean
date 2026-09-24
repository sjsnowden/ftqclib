/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# Normal complex matrices and nilpotency

A **normal** complex matrix that is nilpotent is zero. That single fact is what makes a
commutative `⋆`-closed algebra of complex matrices reduced, which is the hypothesis the
splitting theorem needs.

## Main results

* `eq_zero_of_isHermitian_of_isNilpotent` — a Hermitian nilpotent complex matrix is zero.
* `eq_zero_of_commute_conjTranspose_of_isNilpotent` — a **normal** nilpotent one is zero.
* `isReduced_of_commute_of_conjTranspose_mem` — hence a commutative `⋆`-closed subalgebra of
  `Matrix X X ℂ` is reduced.

## The two hypotheses are both load-bearing, and neither can be traded for the other

**Symmetry is not enough over `ℂ`.** `!![1, I; I, -1]` satisfies `IsSymm`, squares to zero and
is nonzero, so no version of these lemmas may take `IsSymm` as its input. Over `ℂ` the plain
transpose carries no positivity; only the conjugate transpose does. This is an easy trap to
fall into, and the check module keeps the counterexample so a future weakening fails to
compile.

**Normality is not enough either — commutativity of the ambient algebra is doing real work.**
A `⋆`-closed subalgebra of `Matrix X X ℂ` need not be reduced: `M₂(ℂ)` is `⋆`-closed and
contains `!![0, 1; 0, 0]`. What `⋆`-closure alone buys, with no commutativity, is
*semisimplicity*, which is strictly weaker than reducedness. Reducedness is available only once
commutativity supplies normality for every element.

## Implementation notes

`Matrix.trace_conjTranspose_mul_self_eq_zero_iff` is Mathlib's, and using it at `ℂ` requires
`open scoped ComplexOrder`, whose instances live in `Analysis/Complex/Order.lean` and
`Analysis/RCLike/Basic.lean`. Those imports are the cost of not re-proving a library lemma, and
they are confined to this module. A hand-rolled `Complex.normSq` argument would avoid them at
the price of restating something Mathlib already has; the library lemma is preferred.

The nilpotency argument halves the exponent rather than inducting downwards: from `M ^ (2 * m)
= 0` and Hermitian-ness, `trace ((M ^ m)ᴴ * M ^ m) = 0`, so `M ^ m = 0`. Iterating from a power
of two reaches `M` itself.
-/

namespace ECCLib

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
open scoped ComplexOrder in
/-- A complex matrix whose Gram trace vanishes is zero. -/
theorem eq_zero_of_trace_conjTranspose_mul_self (M : Matrix X X ℂ)
    (h : (Mᴴ * M).trace = 0) : M = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h

open scoped ComplexOrder in
/-- A Hermitian nilpotent complex matrix is zero. -/
theorem eq_zero_of_isHermitian_of_isNilpotent {M : Matrix X X ℂ}
    (hh : M.IsHermitian) (hn : IsNilpotent M) : M = 0 := by
  have halve : ∀ m : ℕ, M ^ (2 * m) = 0 → M ^ m = 0 := by
    intro m hm
    refine eq_zero_of_trace_conjTranspose_mul_self _ ?_
    have hH : (M ^ m)ᴴ = M ^ m := by rw [Matrix.conjTranspose_pow, hh]
    rw [hH, ← pow_add, ← two_mul, hm, Matrix.trace_zero]
  have key : ∀ j : ℕ, M ^ (2 ^ j) = 0 → M = 0 := by
    intro j
    induction j with
    | zero => intro h; simpa using h
    | succ j ih =>
      intro h
      refine ih (halve _ ?_)
      rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring]
      exact h
  obtain ⟨k, hk⟩ := hn
  exact key k (pow_eq_zero_of_le (Nat.le_of_lt Nat.lt_two_pow_self) hk)

open scoped ComplexOrder in
/-- **A normal nilpotent complex matrix is zero.** Stated at the weakest hypothesis the
statement needs — normality of the single matrix, not commutativity of anything around it. -/
theorem eq_zero_of_commute_conjTranspose_of_isNilpotent {M : Matrix X X ℂ}
    (hc : Commute M Mᴴ) (hn : IsNilpotent M) : M = 0 := by
  obtain ⟨k, hk⟩ := hn
  have hN : (Mᴴ * M) ^ k = 0 := by rw [(hc.symm).mul_pow, hk, mul_zero]
  have hHerm : (Mᴴ * M).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h0 := eq_zero_of_isHermitian_of_isNilpotent hHerm ⟨k, hN⟩
  exact eq_zero_of_trace_conjTranspose_mul_self _ (by rw [h0, Matrix.trace_zero])

/-- **A commutative `⋆`-closed subalgebra of complex matrices is reduced.** Commutativity is
what supplies normality for every element; without it the statement is false, since `M₂(ℂ)` is
`⋆`-closed and has nonzero nilpotents. -/
theorem isReduced_of_commute_of_conjTranspose_mem (A : Subalgebra ℂ (Matrix X X ℂ))
    (hcomm : ∀ M ∈ A, ∀ N ∈ A, M * N = N * M)
    (hstar : ∀ M ∈ A, Mᴴ ∈ A) : IsReduced A := by
  constructor
  intro M hM
  have hMA : (M : Matrix X X ℂ) ∈ A := M.2
  have hc : Commute (M : Matrix X X ℂ) (M : Matrix X X ℂ)ᴴ :=
    hcomm _ hMA _ (hstar _ hMA)
  obtain ⟨k, hk⟩ := hM
  have hz : (M : Matrix X X ℂ) ^ k = 0 := by
    have := congrArg (Subalgebra.val A) hk
    simpa using this
  exact Subtype.ext (eq_zero_of_commute_conjTranspose_of_isNilpotent hc ⟨k, hz⟩)

end ECCLib

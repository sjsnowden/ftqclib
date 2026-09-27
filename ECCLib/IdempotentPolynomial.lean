/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# Squares of linear forms in idempotent variables, and two's complement

A variable `x` with `x * x = x` takes only the values of a bit, so a polynomial in such variables
is multilinear: squaring a linear form `∑ cᵢ xᵢ` gives the diagonal `∑ cᵢ² xᵢ` (each `xᵢ²` collapses
to `xᵢ`) and the off-diagonal products `cⱼ cₖ xⱼ xₖ`, and nothing of higher degree. This module
states that identity over any commutative semiring, reads the two's-complement value of a bit
vector as such a linear form, and combines the two: the square of a two's-complement integer is a
polynomial of degree exactly two in its bits, with the coefficients `cₖ²` on single bits and
`cⱼ cₖ` on ordered pairs.

This is the fact behind the kinetic step of a split-operator propagation on `n` qubits: the phase
`α m²`, with `m` the two's-complement momentum index of the register, is `n` single-qubit phases
`α cₖ²` and `n(n−1)/2` two-qubit phases `2α cⱼ cₖ` (each unordered pair is two ordered ones).

## Main definitions

* `ECCLib.twosCoeff` — the weight of bit `k` in width `w`: `2^k`, and `−2^(w−1)` for the
  sign bit.

## Main results

* `ECCLib.sq_sum_mul_of_idem` — the square of a linear form in idempotent variables.
* `ECCLib.ofBits_eq_sum` — Batteries' `Nat.ofBits` as the sum `∑ 2^i · bitᵢ`.
* `ECCLib.toNat_eq_sum_getLsbD` — a bit vector's value as the same sum.
* `ECCLib.toInt_eq_sum_twosCoeff` — its two's-complement value as `∑ twosCoeff w k · bitₖ`.
* `ECCLib.twosComplement_sq_expand` — the square of that value, expanded.

## Implementation notes

The value readings go through the core lemmas `BitVec.toInt_eq_msb_cond`,
`BitVec.msb_eq_getLsbD_last` and `BitVec.testBit_toNat` and through Batteries'
`Nat.ofBits_testBit`; nothing about `BitVec.toInt` is re-proved. The square is stated with
`Finset.offDiag` and needs neither `DecidableEq` nor finiteness on the index type (the proof
takes `classical`).
-/

namespace ECCLib

open Finset

/-! ## The square of a linear form in idempotent variables -/

/-- **The square of a linear form in idempotent variables** is its diagonal plus its
off-diagonal products: with `x i * x i = x i` for `i ∈ s`,
`(∑ cᵢ xᵢ)² = ∑ cᵢ² xᵢ + ∑_{(j,k) ∈ s.offDiag} cⱼ cₖ (xⱼ xₖ)`. -/
theorem sq_sum_mul_of_idem {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (c x : ι → R) (hx : ∀ i ∈ s, x i * x i = x i) :
    (∑ i ∈ s, c i * x i) ^ 2
      = ∑ i ∈ s, c i ^ 2 * x i + ∑ p ∈ s.offDiag, c p.1 * c p.2 * (x p.1 * x p.2) := by
  classical
  rw [sq, sum_mul_sum, ← sum_product' (f := fun i j => c i * x i * (c j * x j)),
    ← diag_union_offDiag, sum_union (disjoint_diag_offDiag s), sum_diag]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    calc c i * x i * (c i * x i) = c i ^ 2 * (x i * x i) := by ring
      _ = c i ^ 2 * x i := by rw [hx i hi]
  · exact sum_congr rfl fun p _ => by ring

/-! ## Bits as a linear form -/

/-- Batteries' `Nat.ofBits` (little endian) is the sum `∑ᵢ 2^i · bitᵢ`. -/
theorem ofBits_eq_sum {n : ℕ} (f : Fin n → Bool) :
    Nat.ofBits f = ∑ i : Fin n, 2 ^ (i : ℕ) * (f i).toNat := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.ofBits_succ, ih, Fin.sum_univ_succ, mul_sum, add_comm]
    congr 1
    · simp
    · exact sum_congr rfl fun i _ => by simp [Fin.val_succ, pow_succ]; ring

/-- A bit vector's value is the sum of its bits weighted by powers of two. -/
theorem toNat_eq_sum_getLsbD {w : ℕ} (x : BitVec w) :
    x.toNat = ∑ i : Fin w, 2 ^ (i : ℕ) * (x.getLsbD i).toNat := by
  have h := Nat.ofBits_testBit x.toNat w
  rw [Nat.mod_eq_of_lt x.isLt] at h
  rw [← h, ofBits_eq_sum]
  rfl

/-- The **two's-complement weight** of bit `k` in width `w`: `2^k`, except `−2^(w−1)` for the
sign bit `k = w − 1`. -/
def twosCoeff (w : ℕ) (k : Fin w) : ℤ :=
  if (k : ℕ) + 1 = w then -2 ^ (k : ℕ) else 2 ^ (k : ℕ)

/-- A bit vector's **two's-complement value** is the linear form `∑ₖ twosCoeff w k · bitₖ`. -/
theorem toInt_eq_sum_twosCoeff {w : ℕ} (x : BitVec w) :
    x.toInt = ∑ k : Fin w, twosCoeff w k * ((x.getLsbD k).toNat : ℤ) := by
  cases w with
  | zero => simp [BitVec.toInt, BitVec.toNat_of_zero_length]
  | succ n =>
    have hlast : twosCoeff (n + 1) (Fin.last n) = -2 ^ n := by simp [twosCoeff]
    have hcast (k : Fin n) : twosCoeff (n + 1) k.castSucc = 2 ^ (k : ℕ) := by
      have hk : (k : ℕ) + 1 ≠ n + 1 := by omega
      simp only [twosCoeff, Fin.val_castSucc, hk, if_false]
    rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_getLsbD_last, toNat_eq_sum_getLsbD,
      Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hlast]
    simp only [hcast, Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel]
    push_cast
    cases x.getLsbD n
    · simp
    · simp only [Bool.toNat_true, Nat.cast_one, mul_one, if_true, pow_succ]
      ring

/-! ## The square of a two's-complement value -/

/-- **The square of a two's-complement value, expanded in its bits:**
`toInt² = ∑ₖ cₖ² bₖ + ∑_{j ≠ k} cⱼ cₖ bⱼ bₖ` with `cₖ = twosCoeff w k` and `bₖ` the bits. -/
theorem twosComplement_sq_expand {w : ℕ} (x : BitVec w) :
    x.toInt ^ 2
      = ∑ k : Fin w, twosCoeff w k ^ 2 * ((x.getLsbD k).toNat : ℤ)
        + ∑ p ∈ (univ : Finset (Fin w)).offDiag,
            twosCoeff w p.1 * twosCoeff w p.2
              * (((x.getLsbD p.1).toNat : ℤ) * ((x.getLsbD p.2).toNat : ℤ)) := by
  rw [toInt_eq_sum_twosCoeff]
  exact sq_sum_mul_of_idem univ _ _ fun k _ => by cases x.getLsbD k <;> simp

end ECCLib

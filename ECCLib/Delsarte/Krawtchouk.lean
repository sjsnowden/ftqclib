/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

set_option linter.unusedSectionVars false

/-!
# Krawtchouk numbers (the Delsarte LP layer)

`kraw q n k i` is the **Krawtchouk number** `K_k^{n,q}(i)` — the value at the shell
index `i` of the degree-`k` Krawtchouk polynomial — defined by the closed alternating
sum, which is computable and kernel-cheap. The generating polynomial
`(1 − X)^i (1 + (q−1)X)^{n−i}` recovers it as a coefficient (`kraw_eq_coeff`), which
is the hinge every character-side statement uses.

Vocabulary note: the existing `ECCLib.Coding.krawtchouk_sum` / `krawtchouk_pi`
are the *character sums* — the generating identity's closed form over a field, never
indexed by the degree `k`. `kraw` is the *number* `K_k(i)`; the two vocabularies meet
exactly at `kraw_eq_coeff`.

Convention hazards, pinned by machine computation:
* `n − i` and `k − j` inside `kraw` are ℕ-truncated, so values at `i > n` are junk;
  every consumer bounds its quantifiers by `Finset.range (n+1)` and pins `n`.
* The degree-one closed form is FALSE without `i ≤ n`; the check
  file keeps a permanent counterexample row so the hypothesis cannot be "simplified"
  away.
* The generating polynomial is written `(1 − X)^i * (1 + (q−1)X)^(n−i)` in THAT order
  so the antidiagonal reindexing in `kraw_eq_coeff` lands on the standard summand.
-/

namespace ECCLib.Delsarte

open Polynomial

/-- The Krawtchouk number `K_k^{n,q}(i)`, as the closed alternating sum.
Computable; values at `i > n` are ℕ-truncation junk (bound quantifiers by `n`). -/
def kraw (q n k i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ j * ((q : ℤ) - 1) ^ (k - j) * (i.choose j : ℤ) * ((n - i).choose (k - j) : ℤ)

/-! ## Fingerprints (the normalization tripwires; box rows in `KrawtchoukCheck.lean`) -/

@[simp] theorem kraw_zero_left (q n i : ℕ) : kraw q n 0 i = 1 := by
  simp [kraw]

/-- `K_k(0) = C(n,k)(q−1)^k` — unconditional. -/
theorem kraw_at_zero (q n k : ℕ) : kraw q n k 0 = (n.choose k : ℤ) * ((q : ℤ) - 1) ^ k := by
  unfold kraw
  rw [Finset.sum_eq_single 0]
  · simp [mul_comm]
  · intro j _ hj0
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h

/-- `K₁(i) = (q−1)n − q·i` — REQUIRES `i ≤ n` (false off-domain,
see the guard row in the check file). -/
theorem kraw_one (q n i : ℕ) (h : i ≤ n) :
    kraw q n 1 i = ((q : ℤ) - 1) * n - q * i := by
  have h' : ((n - i : ℕ) : ℤ) = (n : ℤ) - i := by
    push_cast [Nat.cast_sub h]; ring
  unfold kraw
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.choose_one_right, h']
  ring

/-- `K₂(i)` in choose-mixed closed form — REQUIRES `i ≤ n`. Needed because the `rm1`
sharp family's certificates are degree-≤2. -/
theorem kraw_two (q n i : ℕ) (h : i ≤ n) :
    kraw q n 2 i
      = ((q : ℤ) - 1) ^ 2 * ((n - i).choose 2 : ℤ)
        - ((q : ℤ) - 1) * i * ((n : ℤ) - i) + (i.choose 2 : ℤ) := by
  have h' : ((n - i : ℕ) : ℤ) = (n : ℤ) - i := by
    push_cast [Nat.cast_sub h]; ring
  unfold kraw
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.choose_one_right, h']
  ring

/-! ## The generating polynomial and the coefficient hinge -/

/-- The Krawtchouk generating polynomial `(1 − X)^i (1 + (q−1)X)^{n−i}` over `ℤ`.
Same ℕ-truncation in `n − i` as `kraw`, so `kraw_eq_coeff` is unconditional. -/
noncomputable def krawPoly (q n i : ℕ) : Polynomial ℤ :=
  (1 - Polynomial.X) ^ i * (1 + Polynomial.C ((q : ℤ) - 1) * Polynomial.X) ^ (n - i)

/-- Coefficients of `(1 + cX)^m` — the binomial helper Mathlib lacks (verified absent
at the gate: only the `c = 1` case exists). -/
theorem coeff_one_add_C_mul_X_pow {R : Type*} [CommRing R] (c : R) (m r : ℕ) :
    ((1 + Polynomial.C c * Polynomial.X) ^ m).coeff r = (m.choose r : R) * c ^ r := by
  have h1 : (1 + Polynomial.C c * Polynomial.X) = (Polynomial.C c * Polynomial.X + 1) := by
    ring
  rw [h1, add_pow, Polynomial.finset_sum_coeff]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      ((Polynomial.C c * Polynomial.X) ^ j * 1 ^ (m - j) * (m.choose j : Polynomial R)).coeff r
        = if r = j then c ^ j * (m.choose j : R) else 0 := by
    intro j _
    rw [one_pow, mul_one, mul_pow, ← Polynomial.C_pow, ← Polynomial.C_eq_natCast,
      mul_assoc, mul_comm (Polynomial.X ^ j), ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  by_cases hr : r ∈ Finset.range (m + 1)
  · simp [hr, mul_comm]
  · have h0 : m.choose r = 0 :=
      Nat.choose_eq_zero_of_lt (by simpa [Nat.lt_succ_iff, not_le] using
        (Finset.mem_range.not.mp hr))
    simp [hr, h0]

/-- **The hinge**: the Krawtchouk number is the `X^k` coefficient of the generating
polynomial. Unconditional — both sides carry the same ℕ-truncation. -/
theorem kraw_eq_coeff (q n k i : ℕ) : kraw q n k i = (krawPoly q n i).coeff k := by
  have hsub : (1 - Polynomial.X : Polynomial ℤ) = 1 + Polynomial.C (-1 : ℤ) * Polynomial.X := by
    simp [neg_mul, sub_eq_add_neg]
  unfold krawPoly
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold kraw
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsub, coeff_one_add_C_mul_X_pow, coeff_one_add_C_mul_X_pow]
  ring

end ECCLib.Delsarte

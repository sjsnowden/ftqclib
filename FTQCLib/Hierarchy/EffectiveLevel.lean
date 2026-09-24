/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.FuncDeriv
import FTQCLib.Hierarchy.BoolReduce
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic


/-!
# Effective Clifford-hierarchy level of a phase polynomial

The CGK 2017 formula `level(P) := (m - 1) + totalDegree(P)` is the
crude polynomial-side Clifford-hierarchy bound. Conjugation by a Pauli
`X_i` is encoded polynomially by `shiftDeriv i P`, which descends the
level by exactly one in the operator picture. Polynomially, this
descent has **two** sources:

1. **Total-degree drop.** For the substitution `X_i ↦ X_i + 1` over
   `ZMod (2^m)`, total degree always strictly drops on positive-degree
   inputs (`discreteDeriv_totalDegree_lt`, in `Descent.lean`).
2. **2-adic precision drop.** For the substitution `X_i ↦ 1 − X_i` —
   the Boolean shift, encoded by `shiftDeriv` — on multilinear
   polynomials, total degree may *not* strictly drop. Instead, the
   leading-degree term acquires a factor of `2` in its coefficient,
   which corresponds (operationally) to a precision drop `m → m − 1`.

The **effective level** of `P` blends these two:

  `effLevelMonom m c d := (m − 1 − twoAdicVal c) + d.sum`,
  `effectiveLevel P    := sup_{d ∈ P.support} effLevelMonom m (P.coeff d) d`,

where `twoAdicVal c` is the largest `k` with `2^k ∣ c.val` (with the
convention `twoAdicVal 0 = m`, making the constant-zero contribution
vanish).

This file proves:

1. `twoAdicVal : ZMod (2^m) → ℕ` and the basic properties
   `twoAdicVal_zero`, `twoAdicVal_le`, `twoAdicVal_lt_of_ne_zero`,
   `pow_twoAdicVal_dvd_val`, `pow_dvd_val_iff`.
2. `twoAdicVal_two_mul_ge` — the precision-drop step: `v(2c) ≥ v(c) + 1`
   when `2c ≠ 0`. Used by the strict-drop lemma below.
3. `twoAdicVal_neg` — negation preserves the 2-adic valuation.
4. `twoAdicVal_add_ge_min` — `v(a + b) ≥ min v(a) v(b)`. Used to bound
   the effective level of a sum of polynomials.
5. `effLevelMonom`, `effectiveLevel`, `effectiveLevel_le_level`,
   `effectiveLevel_finsetSum_le`, and `totalDegree_le_effectiveLevel`.
6. The **strict-drop lemma** `shiftDeriv_effectiveLevel_lt`: for
   multilinear `P : DiagPhase n m` with positive total degree,
   `effectiveLevel (shiftDeriv i P) < effectiveLevel P`. The proof
   decomposes `P` as a sum of monomials, bounds each summand of
   `shiftDeriv i P` per-monomial, and transfers via
   `effectiveLevel_finsetSum_le`.
-/

namespace FTQCLib.Hierarchy

open MvPolynomial

namespace DiagPhase

variable {n m : ℕ}

/-! ### Two-adic valuation on `ZMod (2^m)`

`twoAdicVal c` is the 2-adic valuation of `c.val`, with `c = 0` mapped
to `m` (the convention that makes zero coefficients ignored downstream).
For nonzero `c`, since `c.val ∈ [1, 2^m − 1]`, the valuation is at most
`m − 1`. -/

/-- The 2-adic valuation of `c : ZMod (2^m)`, with the convention
`twoAdicVal 0 = m`. For `c ≠ 0`, returns `Nat.factorization c.val 2`,
the exponent of `2` in `c.val`'s prime factorization. -/
noncomputable def twoAdicVal {m : ℕ} (c : ZMod (2 ^ m)) : ℕ :=
  if c = 0 then m else Nat.factorization c.val 2

@[simp] lemma twoAdicVal_zero : twoAdicVal (0 : ZMod (2 ^ m)) = m := by
  unfold twoAdicVal; rw [if_pos rfl]

/-- For nonzero `c`, the 2-adic valuation is `Nat.factorization c.val 2`. -/
lemma twoAdicVal_of_ne_zero {c : ZMod (2 ^ m)} (hc : c ≠ 0) :
    twoAdicVal c = Nat.factorization c.val 2 := by
  unfold twoAdicVal; rw [if_neg hc]

private lemma val_eq_zero_iff {c : ZMod (2 ^ m)} : c.val = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hcast : c = (c.val : ZMod (2 ^ m)) := (ZMod.natCast_zmod_val c).symm
    rw [hcast, h]; simp
  · intro h
    rw [h]; simp

/-- For `c ≠ 0` in `ZMod (2^m)`, the 2-adic valuation is at most
`m − 1`. Proved by noting that `2^(twoAdicVal c) ∣ c.val` while
`c.val < 2^m` (so the valuation is strictly less than `m`). -/
lemma twoAdicVal_lt_of_ne_zero {c : ZMod (2 ^ m)} (hc : c ≠ 0) :
    twoAdicVal c < m := by
  rw [twoAdicVal_of_ne_zero hc]
  have hval_ne : c.val ≠ 0 := fun h => hc (val_eq_zero_iff.mp h)
  have hdvd : 2 ^ (Nat.factorization c.val 2) ∣ c.val := Nat.ordProj_dvd c.val 2
  have hpow_le : 2 ^ (Nat.factorization c.val 2) ≤ c.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hval_ne) hdvd
  have hlt : c.val < 2 ^ m := ZMod.val_lt c
  have hpow_lt : 2 ^ (Nat.factorization c.val 2) < 2 ^ m :=
    lt_of_le_of_lt hpow_le hlt
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt

/-- The 2-adic valuation is at most `m` (always, regardless of `c`). -/
lemma twoAdicVal_le (c : ZMod (2 ^ m)) : twoAdicVal c ≤ m := by
  by_cases hc : c = 0
  · rw [hc, twoAdicVal_zero]
  · exact (twoAdicVal_lt_of_ne_zero hc).le

/-- For `c ≠ 0`, `2^(twoAdicVal c) ∣ c.val`. The basic divisibility
characterisation of the 2-adic valuation. -/
lemma pow_twoAdicVal_dvd_val {c : ZMod (2 ^ m)} (hc : c ≠ 0) :
    2 ^ (twoAdicVal c) ∣ c.val := by
  rw [twoAdicVal_of_ne_zero hc]
  exact Nat.ordProj_dvd c.val 2

/-- Characterisation: `2^k ∣ c.val` iff `k ≤ twoAdicVal c`, for `c ≠ 0`. -/
lemma pow_dvd_val_iff {c : ZMod (2 ^ m)} (hc : c ≠ 0) (k : ℕ) :
    2 ^ k ∣ c.val ↔ k ≤ twoAdicVal c := by
  rw [twoAdicVal_of_ne_zero hc]
  have hval_ne : c.val ≠ 0 := fun h => hc (val_eq_zero_iff.mp h)
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hval_ne]

/-! ### 2-adic valuation under multiplication by 2

The crucial fact: `twoAdicVal (2*c) ≥ twoAdicVal c + 1` whenever
`2*c ≠ 0`. This is the precision-drop step in the CGK descent.

We prove the *weaker* inequality form (≥ rather than =) because it's
all we need downstream and avoids a delicate boundary-case analysis at
the wrap-around `c.val ≥ 2^(m-1)`. -/

/-- The `val` of `2 * c` in `ZMod (2^m)` equals `(2 * c.val) mod 2^m`. -/
private lemma val_two_mul (c : ZMod (2 ^ m)) :
    ((2 : ZMod (2 ^ m)) * c).val = (2 * c.val) % 2 ^ m := by
  have hc_cast : c = (c.val : ZMod (2 ^ m)) := (ZMod.natCast_zmod_val c).symm
  conv_lhs => rw [hc_cast]
  have h2 : (2 : ZMod (2 ^ m)) = ((2 : ℕ) : ZMod (2 ^ m)) := by norm_num
  rw [h2, ← Nat.cast_mul, ZMod.val_natCast]

/-- **Weak version of `twoAdicVal_two_mul`**: whenever `2*c ≠ 0`,
the 2-adic valuation of `2*c` is at least `twoAdicVal c + 1`.

Proof: `2^(v(c)) ∣ c.val` (definition), so `2^(v(c) + 1) ∣ 2 * c.val`.
Also `v(c) + 1 ≤ m` (since `c ≠ 0` implies `v(c) ≤ m - 1`), so
`2^(v(c) + 1) ∣ 2^m`. The val of `2*c` is `(2*c.val) mod 2^m`, and
divisibility transfers through the modular reduction. -/
lemma twoAdicVal_two_mul_ge {c : ZMod (2 ^ m)}
    (h2c : (2 : ZMod (2 ^ m)) * c ≠ 0) :
    twoAdicVal c + 1 ≤ twoAdicVal ((2 : ZMod (2 ^ m)) * c) := by
  -- `c ≠ 0` (otherwise `2 * c = 0`).
  have hc : c ≠ 0 := fun h => h2c (by rw [h, mul_zero])
  -- `v(c) + 1 ≤ m` because `v(c) < m`.
  have hvc_lt : twoAdicVal c < m := twoAdicVal_lt_of_ne_zero hc
  have hvc_succ_le : twoAdicVal c + 1 ≤ m := hvc_lt
  -- `2^(v(c)) ∣ c.val`, so `2^(v(c) + 1) = 2 * 2^(v(c)) ∣ 2 * c.val`.
  have hdvd_c : 2 ^ (twoAdicVal c) ∣ c.val := pow_twoAdicVal_dvd_val hc
  have hdvd_2c : 2 ^ (twoAdicVal c + 1) ∣ 2 * c.val := by
    rw [pow_succ]
    -- Goal: 2^twoAdicVal c * 2 ∣ 2 * c.val.
    -- Rewrite as 2 * 2^twoAdicVal c ∣ 2 * c.val and use mul_dvd_mul_left.
    rw [mul_comm (2 ^ twoAdicVal c) 2]
    exact mul_dvd_mul_left 2 hdvd_c
  -- `2^(v(c) + 1) ∣ 2^m`.
  have hdvd_pow_m : 2 ^ (twoAdicVal c + 1) ∣ 2 ^ m :=
    pow_dvd_pow 2 hvc_succ_le
  -- So `2^(v(c) + 1) ∣ (2 * c.val) mod 2^m = (2*c).val`.
  have hdvd_2c_val : 2 ^ (twoAdicVal c + 1) ∣ ((2 : ZMod (2 ^ m)) * c).val := by
    rw [val_two_mul]
    rcases Nat.lt_or_ge (2 * c.val) (2 ^ m) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; exact hdvd_2c
    · have h_lt_2pm : 2 * c.val < 2 * 2 ^ m :=
        Nat.mul_lt_mul_of_pos_left (ZMod.val_lt c) (by norm_num)
      have hmod_eq : (2 * c.val) % 2 ^ m = 2 * c.val - 2 ^ m := by
        rw [Nat.mod_eq_sub_mod hge]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod_eq]
      exact Nat.dvd_sub hdvd_2c hdvd_pow_m
  -- Convert divisibility to a valuation bound.
  exact (pow_dvd_val_iff h2c (twoAdicVal c + 1)).mp hdvd_2c_val

/-! ### 2-adic valuation of a sum

In `ZMod (2^m)`, `twoAdicVal (a + b) ≥ min (twoAdicVal a) (twoAdicVal b)`.
Used to handle coefficient collection when summing monomials. -/

private lemma val_add (a b : ZMod (2 ^ m)) :
    (a + b).val = (a.val + b.val) % 2 ^ m := by
  rw [ZMod.val_add a b]

/-- Negation preserves the 2-adic valuation: `twoAdicVal (-c) = twoAdicVal c`.

Proof: `(-c).val = 2^m - c.val` for `c ≠ 0`. For each `k ≤ m`,
`2^k ∣ 2^m` (since `k ≤ m`), so `2^k ∣ (-c).val ↔ 2^k ∣ c.val`. The
valuation, as the max such `k`, is therefore unchanged. -/
lemma twoAdicVal_neg (c : ZMod (2 ^ m)) :
    twoAdicVal (-c) = twoAdicVal c := by
  by_cases hc : c = 0
  · rw [hc, neg_zero]
  -- c ≠ 0. Show `2^k ∣ (-c).val ↔ k ≤ twoAdicVal c`, and the same for `-c`.
  have h_neg_ne : (-c) ≠ 0 := neg_ne_zero.mpr hc
  -- Need NeZero (2^m) instance for val_neg_of_ne_zero.
  have hm_pos : 0 < 2 ^ m := Nat.two_pow_pos m
  haveI : NeZero (2 ^ m) := ⟨hm_pos.ne'⟩
  haveI : NeZero c := ⟨hc⟩
  have h_val_neg : (-c).val = 2 ^ m - c.val := ZMod.val_neg_of_ne_zero c
  -- We characterise both valuations by the same divisibility condition.
  apply le_antisymm
  · -- twoAdicVal (-c) ≤ twoAdicVal c: show k = twoAdicVal (-c) divides c.val.
    by_contra h
    -- h : ¬(twoAdicVal (-c) ≤ twoAdicVal c), i.e., twoAdicVal c < twoAdicVal (-c).
    have hsucc_le : twoAdicVal c + 1 ≤ twoAdicVal (-c) := Nat.lt_iff_add_one_le.mp (not_le.mp h)
    have h_dvd_neg : 2 ^ (twoAdicVal c + 1) ∣ (-c).val :=
      (pow_dvd_val_iff h_neg_ne (twoAdicVal c + 1)).mpr hsucc_le
    -- Also 2^(twoAdicVal c + 1) ∣ 2^m (since twoAdicVal (-c) ≤ m).
    have h_le_m : twoAdicVal c + 1 ≤ m :=
      hsucc_le.trans (twoAdicVal_le _)
    have h_dvd_2m : 2 ^ (twoAdicVal c + 1) ∣ 2 ^ m := pow_dvd_pow 2 h_le_m
    -- So 2^(twoAdicVal c + 1) ∣ 2^m - (-c).val = 2^m - (2^m - c.val) = c.val.
    have h_val_le : c.val ≤ 2 ^ m := (ZMod.val_lt c).le
    have h_eq : c.val = 2 ^ m - (-c).val := by
      rw [h_val_neg]; omega
    have h_dvd_c : 2 ^ (twoAdicVal c + 1) ∣ c.val := by
      rw [h_eq]
      exact Nat.dvd_sub h_dvd_2m h_dvd_neg
    -- Then twoAdicVal c + 1 ≤ twoAdicVal c, contradiction.
    have := (pow_dvd_val_iff hc (twoAdicVal c + 1)).mp h_dvd_c
    omega
  · -- twoAdicVal c ≤ twoAdicVal (-c): symmetric argument.
    have h_dvd : 2 ^ (twoAdicVal c) ∣ c.val := pow_twoAdicVal_dvd_val hc
    have h_le_m : twoAdicVal c ≤ m := twoAdicVal_le _
    have h_dvd_2m : 2 ^ (twoAdicVal c) ∣ 2 ^ m := pow_dvd_pow 2 h_le_m
    have h_dvd_neg : 2 ^ (twoAdicVal c) ∣ (-c).val := by
      rw [h_val_neg]
      exact Nat.dvd_sub h_dvd_2m h_dvd
    exact (pow_dvd_val_iff h_neg_ne (twoAdicVal c)).mp h_dvd_neg

/-- `twoAdicVal (a + b) ≥ min (twoAdicVal a) (twoAdicVal b)`. -/
lemma twoAdicVal_add_ge_min (a b : ZMod (2 ^ m)) :
    min (twoAdicVal a) (twoAdicVal b) ≤ twoAdicVal (a + b) := by
  -- Case-split on whether `a = 0`, `b = 0`, or both nonzero.
  by_cases ha : a = 0
  · subst ha
    rw [zero_add, twoAdicVal_zero]
    exact min_le_right _ _
  by_cases hb : b = 0
  · subst hb
    rw [add_zero, twoAdicVal_zero]
    exact min_le_left _ _
  by_cases hab : a + b = 0
  · rw [hab, twoAdicVal_zero]
    -- Both `twoAdicVal a < m` and `twoAdicVal b < m` (since a, b ≠ 0).
    -- min ≤ twoAdicVal a < m, so min < m, hence min ≤ m.
    exact le_trans (min_le_left _ _) (twoAdicVal_le a)
  -- Both `a, b ≠ 0` and `a + b ≠ 0`. Use the divisibility characterisation.
  set k := min (twoAdicVal a) (twoAdicVal b) with hk_def
  have hdvd_a : 2 ^ (twoAdicVal a) ∣ a.val := pow_twoAdicVal_dvd_val ha
  have hdvd_b : 2 ^ (twoAdicVal b) ∣ b.val := pow_twoAdicVal_dvd_val hb
  have hka : 2 ^ k ∣ a.val := dvd_trans (pow_dvd_pow 2 (min_le_left _ _)) hdvd_a
  have hkb : 2 ^ k ∣ b.val := dvd_trans (pow_dvd_pow 2 (min_le_right _ _)) hdvd_b
  have hk_le : k ≤ m := le_trans (min_le_left _ _) (twoAdicVal_le a)
  have hkm : 2 ^ k ∣ 2 ^ m := pow_dvd_pow 2 hk_le
  have hk_sum : 2 ^ k ∣ a.val + b.val := Nat.dvd_add hka hkb
  -- `(a+b).val = (a.val + b.val) % 2^m`. Mod-by-multiple preserves divisibility.
  have hdvd_val : 2 ^ k ∣ (a + b).val := by
    rw [val_add]
    rcases Nat.lt_or_ge (a.val + b.val) (2 ^ m) with hlt' | hge'
    · rw [Nat.mod_eq_of_lt hlt']; exact hk_sum
    · have h_sum_lt : a.val + b.val < 2 ^ m + 2 ^ m := by
        have := ZMod.val_lt a; have := ZMod.val_lt b
        omega
      have hmod_eq : (a.val + b.val) % 2 ^ m = a.val + b.val - 2 ^ m := by
        rw [Nat.mod_eq_sub_mod hge']
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod_eq]
      exact Nat.dvd_sub hk_sum hkm
  exact (pow_dvd_val_iff hab k).mp hdvd_val

/-! ### Effective level of a monomial

For a coefficient `c` and exponent vector `d`, the **effective level**
contribution is `(m - 1 - twoAdicVal c) + d.sum`, in ℕ (Nat
subtraction is well-defined for `c ≠ 0` since `twoAdicVal c ≤ m - 1`).
For `c = 0` we get `0 + d.sum = d.sum`, but `c = 0` monomials are
never in the polynomial's support, so this branch is unused. -/

/-- The effective level contribution of a monomial `c · X^d`. For
`c = 0`, returns `d.sum` (which is harmless since such terms don't
appear in the support). For `c ≠ 0`, returns
`(m − 1 − twoAdicVal c) + d.sum`. -/
noncomputable def effLevelMonom (m : ℕ) (c : ZMod (2 ^ m))
    (d : Fin n →₀ ℕ) : ℕ :=
  (m - 1 - twoAdicVal c) + d.sum (fun _ e => e)

/-- For `c = 0`, the effective level contribution is just `d.sum`,
because `m - 1 - m = 0` (Nat subtraction). -/
lemma effLevelMonom_zero (d : Fin n →₀ ℕ) :
    effLevelMonom m (0 : ZMod (2 ^ m)) d = d.sum (fun _ e => e) := by
  unfold effLevelMonom
  rw [twoAdicVal_zero]
  have h : m - 1 - m = 0 := by omega
  rw [h, Nat.zero_add]

/-! ### Effective level of a polynomial

`effectiveLevel P` is the maximum over `P.support` of the per-monomial
effective level. For the zero polynomial (empty support), it is `0`. -/

/-- The effective Clifford-hierarchy level of a polynomial. The supremum
over `P.support` of the per-monomial effective level. -/
noncomputable def effectiveLevel (P : DiagPhase n m) : ℕ :=
  P.support.sup (fun d => effLevelMonom m (P.coeff d) d)

/-- The zero polynomial has effective level zero. -/
@[simp] lemma effectiveLevel_zero : effectiveLevel (0 : DiagPhase n m) = 0 := by
  unfold effectiveLevel
  simp

/-! ### Effective level is bounded by level

For each monomial, `(m - 1 - twoAdicVal c) + d.sum ≤ (m - 1) + d.sum`
(since `twoAdicVal c ≥ 0`), and `d.sum ≤ P.totalDegree`. Taking the max
gives `effectiveLevel P ≤ (m - 1) + P.totalDegree = level P`. -/

theorem effectiveLevel_le_level (P : DiagPhase n m) :
    effectiveLevel P ≤ P.level := by
  unfold effectiveLevel level
  refine Finset.sup_le ?_
  intro d hd
  unfold effLevelMonom
  have h1 : m - 1 - twoAdicVal (P.coeff d) ≤ m - 1 := Nat.sub_le _ _
  have h2 : d.sum (fun _ e => e) ≤ P.totalDegree := le_totalDegree hd
  omega

/-! ### Helper: effective-level bound via sum-of-monomials

If `Q` is expressed as a finite sum of (not-necessarily-disjoint)
polynomials `Q = ∑ α, q α`, then `effectiveLevel Q ≤ max_α effectiveLevel (q α)`.

The proof handles coefficient collection via `twoAdicVal_add_ge_min`. -/

/-- The effective level of a finite sum of polynomials is bounded by the
max of the effective levels of the summands. -/
lemma effectiveLevel_finsetSum_le {ι : Type*} (s : Finset ι)
    (f : ι → DiagPhase n m) :
    effectiveLevel (∑ i ∈ s, f i)
      ≤ s.sup (fun i => effectiveLevel (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has hind =>
    rw [Finset.sum_insert has, Finset.sup_insert]
    -- effectiveLevel (f a + sum) ≤ max (effectiveLevel (f a)) (effectiveLevel sum).
    have h_add : effectiveLevel ((f a) + ∑ i ∈ s, f i)
        ≤ max (effectiveLevel (f a)) (effectiveLevel (∑ i ∈ s, f i)) := by
      unfold effectiveLevel
      refine Finset.sup_le ?_
      intro e he
      have h_coeff :
          MvPolynomial.coeff e ((f a) + ∑ i ∈ s, f i) =
            MvPolynomial.coeff e (f a) + MvPolynomial.coeff e (∑ i ∈ s, f i) :=
        MvPolynomial.coeff_add _ _ _
      unfold effLevelMonom
      rw [h_coeff]
      set c_a := MvPolynomial.coeff e (f a) with hca_def
      set c_s := MvPolynomial.coeff e (∑ i ∈ s, f i) with hcs_def
      have hmin :
          min (twoAdicVal c_a) (twoAdicVal c_s) ≤ twoAdicVal (c_a + c_s) :=
        twoAdicVal_add_ge_min c_a c_s
      have h_sub_le :
          m - 1 - twoAdicVal (c_a + c_s)
            ≤ max (m - 1 - twoAdicVal c_a) (m - 1 - twoAdicVal c_s) := by
        omega
      -- Case on whether `c_a = 0` or `c_s = 0`.
      by_cases hca : c_a = 0
      · by_cases hcs : c_s = 0
        · -- Both zero: sum is zero, so e ∉ support. Contradiction.
          have : MvPolynomial.coeff e ((f a) + ∑ i ∈ s, f i) = 0 := by
            rw [h_coeff, hca, hcs, zero_add]
          exact absurd he (by rw [MvPolynomial.notMem_support_iff]; exact this)
        · -- c_a = 0: e ∈ (∑ f i).support.
          have he_s : e ∈ (∑ i ∈ s, f i).support := by
            rw [MvPolynomial.mem_support_iff, ← hcs_def]; exact hcs
          rw [hca, zero_add]
          calc (m - 1 - twoAdicVal c_s) + e.sum (fun _ e => e)
              ≤ effectiveLevel (∑ i ∈ s, f i) := by
                unfold effectiveLevel
                exact Finset.le_sup
                  (f := fun d => effLevelMonom m
                                   (MvPolynomial.coeff d (∑ i ∈ s, f i)) d)
                  he_s
            _ ≤ max (effectiveLevel (f a)) (effectiveLevel (∑ i ∈ s, f i)) :=
                le_max_right _ _
      · by_cases hcs : c_s = 0
        · -- c_s = 0: e ∈ (f a).support.
          have he_a : e ∈ (f a).support := by
            rw [MvPolynomial.mem_support_iff, ← hca_def]; exact hca
          rw [hcs, add_zero]
          calc (m - 1 - twoAdicVal c_a) + e.sum (fun _ e => e)
              ≤ effectiveLevel (f a) := by
                unfold effectiveLevel
                exact Finset.le_sup
                  (f := fun d => effLevelMonom m (MvPolynomial.coeff d (f a)) d)
                  he_a
            _ ≤ max (effectiveLevel (f a)) (effectiveLevel (∑ i ∈ s, f i)) :=
                le_max_left _ _
        · -- Both nonzero.
          have he_a : e ∈ (f a).support := by
            rw [MvPolynomial.mem_support_iff, ← hca_def]; exact hca
          have he_s : e ∈ (∑ i ∈ s, f i).support := by
            rw [MvPolynomial.mem_support_iff, ← hcs_def]; exact hcs
          have h_le_a : (m - 1 - twoAdicVal c_a) + e.sum (fun _ x => x)
              ≤ effectiveLevel (f a) := by
            unfold effectiveLevel
            exact Finset.le_sup
              (f := fun d => effLevelMonom m (MvPolynomial.coeff d (f a)) d)
              he_a
          have h_le_s : (m - 1 - twoAdicVal c_s) + e.sum (fun _ x => x)
              ≤ effectiveLevel (∑ i ∈ s, f i) := by
            unfold effectiveLevel
            exact Finset.le_sup
              (f := fun d => effLevelMonom m
                               (MvPolynomial.coeff d (∑ i ∈ s, f i)) d)
              he_s
          rcases max_cases (m - 1 - twoAdicVal c_a) (m - 1 - twoAdicVal c_s)
            with ⟨heq, _⟩ | ⟨heq, _⟩
          · rw [heq] at h_sub_le
            calc (m - 1 - twoAdicVal (c_a + c_s)) + e.sum (fun _ e => e)
                ≤ (m - 1 - twoAdicVal c_a) + e.sum (fun _ e => e) := by omega
              _ ≤ effectiveLevel (f a) := h_le_a
              _ ≤ max (effectiveLevel (f a)) (effectiveLevel (∑ i ∈ s, f i)) :=
                  le_max_left _ _
          · rw [heq] at h_sub_le
            calc (m - 1 - twoAdicVal (c_a + c_s)) + e.sum (fun _ e => e)
                ≤ (m - 1 - twoAdicVal c_s) + e.sum (fun _ e => e) := by omega
              _ ≤ effectiveLevel (∑ i ∈ s, f i) := h_le_s
              _ ≤ max (effectiveLevel (f a)) (effectiveLevel (∑ i ∈ s, f i)) :=
                  le_max_right _ _
    calc effectiveLevel ((f a) + ∑ i ∈ s, f i)
        ≤ max (effectiveLevel (f a)) (effectiveLevel (∑ i ∈ s, f i)) := h_add
      _ ≤ max (effectiveLevel (f a)) (s.sup (fun i => effectiveLevel (f i))) :=
          max_le_max le_rfl hind

/-! ### Per-monomial effective level

For a single monomial `monomial d c` (with `c ≠ 0`), the effective
level equals `effLevelMonom m c d` exactly. -/

/-- The effective level of a single nonzero monomial. -/
lemma effectiveLevel_monomial_eq {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)}
    (hc : c ≠ 0) :
    effectiveLevel (monomial d c : DiagPhase n m) = effLevelMonom m c d := by
  unfold effectiveLevel
  classical
  rw [MvPolynomial.support_monomial, if_neg hc, Finset.sup_singleton]
  congr 1
  rw [MvPolynomial.coeff_monomial, if_pos rfl]

/-- The effective level of any monomial (including zero coefficient)
is bounded by `effLevelMonom m c d`. -/
lemma effectiveLevel_monomial_le (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) :
    effectiveLevel (monomial d c : DiagPhase n m) ≤ effLevelMonom m c d := by
  by_cases hc : c = 0
  · rw [hc]; simp
  · rw [effectiveLevel_monomial_eq hc]

/-! ### Multilinear polynomials

A polynomial `P : DiagPhase n m` is **multilinear** if every exponent
vector `d ∈ P.support` has all entries at most `1`. Equivalently, every
monomial of `P` is a product of distinct variables. -/

/-- A polynomial `P` is multilinear if all its monomials have exponent
vectors with each entry at most `1`. -/
def IsMultilinear (P : DiagPhase n m) : Prop :=
  ∀ d ∈ P.support, ∀ k, d k ≤ 1

/-! ### The strict-drop lemma

For multilinear `P` with positive total degree, `shiftDeriv i P` has
strictly smaller effective level than `P`. The proof decomposes
`P = ∑_{d ∈ P.support} monomial d (P.coeff d)` and bounds each summand
of `shiftDeriv i P`, then transfers via `effectiveLevel_finsetSum_le`. -/

/-- **Easy direction**: every monomial in `P.support` contributes
`d.sum ≤ effLevelMonom m (coeff d) d` to the effective level, so
`P.totalDegree ≤ effectiveLevel P`. -/
theorem totalDegree_le_effectiveLevel (P : DiagPhase n m) :
    P.totalDegree ≤ effectiveLevel P := by
  unfold effectiveLevel MvPolynomial.totalDegree
  refine Finset.sup_le ?_
  intro d hd
  have h_le : d.sum (fun _ e => e)
      ≤ effLevelMonom m (P.coeff d) d := by
    unfold effLevelMonom
    exact Nat.le_add_left _ _
  exact h_le.trans
    (Finset.le_sup (f := fun d => effLevelMonom m (P.coeff d) d) hd)

/-- For multilinear `P` with positive total degree, `effectiveLevel P ≥ 1`. -/
theorem one_le_effectiveLevel_of_pos_totalDegree
    {P : DiagPhase n m} (hP : 0 < P.totalDegree) :
    1 ≤ effectiveLevel P :=
  hP.trans_le (totalDegree_le_effectiveLevel P)

/-! ### `shiftDeriv` of a single multilinear monomial

For multilinear `d` (each entry `≤ 1`) with `d i = 0`,
`shiftDeriv i (monomial d c) = 0`. With `d i = 1`,
`shiftDeriv i (monomial d c) = monomial (d.erase i) c − 2 · monomial d c`. -/

open Finsupp in
/-- `shiftDeriv i (monomial d c) = 0` when `d i = 0` (the substitution
fixes monomials not involving `X_i`). -/
lemma shiftDeriv_monomial_of_di_zero (i : Fin n) (d : Fin n →₀ ℕ)
    (c : ZMod (2 ^ m)) (hdi : d i = 0) :
    shiftDeriv i (monomial d c : DiagPhase n m) = 0 := by
  classical
  unfold shiftDeriv
  rw [bind₁_monomial]
  -- For every `k ∈ d.support`, `k ≠ i`, so `flipShift i k = X k`.
  have h_supp : ∀ k ∈ d.support, flipShift (m := m) i k = X k := by
    intro k hk
    have hki : k ≠ i := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hk) hdi
    unfold flipShift; rw [if_neg hki]
  rw [Finset.prod_congr rfl (fun k hk => by rw [h_supp k hk])]
  -- Now: bind₁_eval = C c * ∏ k ∈ d.support, X k ^ d k = monomial d c.
  rw [prod_X_pow_eq_monomial, C_mul_monomial, mul_one]
  exact sub_self _

/-- Helper: for multilinear `d` with `d i = 1`, the polynomial
`bind₁ (flipShift i) (monomial d c) = monomial (d.erase i) c - monomial d c`.
The substitution `X_i ↦ 1 - X_i` produces, on the `i`-th factor, a
`(1 - X_i)` term that splits into two monomials. -/
lemma bind₁_flipShift_monomial_multilinear_di_one (i : Fin n)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m))
    (hdi : d i = 1) :
    (MvPolynomial.bind₁ (flipShift (m := m) i) (monomial d c) : DiagPhase n m)
      = monomial (d.erase i) c - monomial d c := by
  classical
  rw [bind₁_monomial]
  -- i ∈ d.support since d i = 1 ≠ 0.
  have hi_mem : i ∈ d.support := by
    rw [Finsupp.mem_support_iff, hdi]; norm_num
  -- Split the product on the `i` entry.
  rw [← Finset.mul_prod_erase _ _ hi_mem]
  have h_flipi : flipShift (m := m) i i = (1 - X i) := by
    unfold flipShift; rw [if_pos rfl]
  rw [h_flipi, hdi, pow_one]
  have h_off : ∀ k ∈ d.support.erase i, flipShift (m := m) i k = X k := by
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    unfold flipShift; rw [if_neg hki]
  rw [Finset.prod_congr rfl (fun k hk => by rw [h_off k hk])]
  -- Now: C c * ((1 - X i) * ∏ k ∈ d.support.erase i, X k ^ d k).
  -- The product ∏ k ∈ d.support.erase i, X k ^ d k = monomial (d.erase i) 1.
  have h_prod_eq : (∏ k ∈ d.support.erase i, X k ^ d k :
                    MvPolynomial (Fin n) (ZMod (2 ^ m)))
      = ∏ k ∈ (d.erase i).support, X k ^ (d.erase i) k := by
    rw [Finsupp.support_erase]
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rw [Finsupp.erase_apply, if_neg hki]
  rw [h_prod_eq, prod_X_pow_eq_monomial]
  -- Goal: C c * ((1 - X i) * monomial (d.erase i) 1) = monomial (d.erase i) c - monomial d c.
  -- Expand (1 - X i) * M.
  rw [sub_mul, one_mul]
  rw [mul_sub]
  -- First term: C c * monomial (d.erase i) 1 = monomial (d.erase i) c.
  rw [C_mul_monomial, mul_one]
  -- Second term: C c * (X i * monomial (d.erase i) 1) = monomial d c.
  have h_xi_monomial :
      (C c * (X i * monomial (d.erase i) 1) : DiagPhase n m) = monomial d c := by
    rw [X, monomial_mul, mul_one]
    rw [C_mul_monomial, mul_one]
    -- Goal: monomial (Finsupp.single i 1 + d.erase i) c = monomial d c.
    have h_finsupp_eq : Finsupp.single i 1 + d.erase i = d := by
      ext k
      by_cases hki : k = i
      · subst hki
        rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl, Finsupp.erase_same, add_zero, hdi]
      · rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (fun h => hki h.symm),
          Finsupp.erase_apply, if_neg hki, zero_add]
    rw [h_finsupp_eq]
  rw [h_xi_monomial]

/-- For multilinear `d` with `d i = 1`,
`shiftDeriv i (monomial d c) = monomial (d.erase i) c - 2 * monomial d c`. -/
lemma shiftDeriv_monomial_multilinear_di_one (i : Fin n)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m))
    (hdi : d i = 1) :
    shiftDeriv i (monomial d c : DiagPhase n m)
      = monomial (d.erase i) c - 2 * monomial d c := by
  unfold shiftDeriv
  rw [bind₁_flipShift_monomial_multilinear_di_one i d c hdi]
  ring

/-! ### Per-monomial effective level bounds for `shiftDeriv`

For a multilinear `d` with `d i = 1` and any `c ≠ 0`:

* `monomial (d.erase i) c` has effective level
  `(m - 1 - twoAdicVal c) + (d.sum - 1) ≤ effLevelMonom m c d - 1`.
* `2 * monomial d c = monomial d (2c)` has effective level
  `(m - 1 - twoAdicVal (2c)) + d.sum ≤ effLevelMonom m c d - 1`
  (when `2c ≠ 0`; otherwise the term is zero and contributes 0). -/

/-- `(d.erase i).sum = d.sum - 1` when `d i ≥ 1`. -/
private lemma sum_erase_eq (i : Fin n) (d : Fin n →₀ ℕ) (hdi : 1 ≤ d i) :
    (d.erase i).sum (fun _ e => e) = d.sum (fun _ e => e) - d i := by
  classical
  rw [Finsupp.sum, Finsupp.support_erase, Finsupp.sum]
  -- Show ∑ k ∈ d.support.erase i, (d.erase i) k = ∑ k ∈ d.support, d k - d i.
  have hi_mem : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; intro h; rw [h] at hdi; exact absurd hdi (by norm_num)
  have h1 : ∑ k ∈ d.support.erase i, (d.erase i) k
      = ∑ k ∈ d.support.erase i, d k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rw [Finsupp.erase_apply, if_neg hki]
  rw [h1]
  rw [← Finset.sum_erase_add _ _ hi_mem, Nat.add_sub_cancel]

/-- For multilinear `d` with `d i = 1`, `(d.erase i).sum = d.sum - 1`. -/
private lemma sum_erase_multilinear (i : Fin n) {d : Fin n →₀ ℕ} (hdi : d i = 1) :
    (d.erase i).sum (fun _ e => e) = d.sum (fun _ e => e) - 1 := by
  rw [sum_erase_eq i d (by rw [hdi])]
  rw [hdi]

/-- The two-element multiplication `2 * monomial d c = monomial d (2c)`
in any `DiagPhase n m`. (Un-privated for the descent-reverse `−2Δ` tower.) -/
lemma two_mul_monomial (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) :
    (2 : DiagPhase n m) * monomial d c = monomial d ((2 : ZMod (2 ^ m)) * c) := by
  rw [show (2 : DiagPhase n m) = C (2 : ZMod (2 ^ m)) from by rfl]
  rw [C_mul_monomial]

/-- **The level of a sum** is at most the larger of the two levels: the coefficients add, and the
valuation of a sum is at least the smaller valuation (`twoAdicVal_add_ge_min`). Un-privated for
the frame's extended level (`levelExt_add_le`), which reads it through the Boolean normal form. -/
lemma effectiveLevel_add_le (A B : DiagPhase n m) :
    effectiveLevel (A + B) ≤ max (effectiveLevel A) (effectiveLevel B) := by
  classical
  -- Express A + B as `∑ i ∈ {true, false}, (if i then A else B)`.
  have h_sum : (A + B : DiagPhase n m)
      = ∑ i ∈ ({true, false} : Finset Bool), (if i then A else B) := by
    rw [show ({true, false} : Finset Bool) = ({true} ∪ {false}) from rfl]
    rw [Finset.sum_union (by decide : Disjoint ({true} : Finset Bool) {false})]
    simp
  rw [h_sum]
  refine (effectiveLevel_finsetSum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro j hj
  rw [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · change effectiveLevel A ≤ _; exact le_max_left _ _
  · change effectiveLevel B ≤ _; exact le_max_right _ _

/-- **Per-monomial effective-level drop**: for a multilinear `d` with
`d i = 1` and `c ≠ 0`, the polynomial
`monomial (d.erase i) c − 2 · monomial d c` has effective level
strictly less than `effLevelMonom m c d` (the per-monomial level of
the source). -/
lemma shiftDeriv_monomial_effectiveLevel_lt
    (i : Fin n) {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)}
    (hc : c ≠ 0) (hdi : d i = 1) :
    effectiveLevel ((monomial (d.erase i) c - 2 * monomial d c) : DiagPhase n m)
      + 1 ≤ effLevelMonom m c d := by
  classical
  -- Setup: m ≥ 1 (since c ≠ 0 in ZMod (2^m)), d.sum ≥ 1, v(c) < m.
  have hm_pos : 1 ≤ m := by
    by_contra hm
    -- hm : ¬(1 ≤ m), i.e., m < 1, i.e., m = 0.
    have hm0 : m = 0 := Nat.lt_one_iff.mp (not_le.mp hm)
    subst hm0
    have : c.val < 1 := ZMod.val_lt c
    exact hc (val_eq_zero_iff.mp (Nat.lt_one_iff.mp this))
  have h_sum_pos : 1 ≤ d.sum (fun _ e => e) := by
    rw [Finsupp.sum]
    have hi_mem : i ∈ d.support := by
      rw [Finsupp.mem_support_iff, hdi]; norm_num
    calc (1 : ℕ) = d i := hdi.symm
      _ ≤ ∑ k ∈ d.support, d k :=
          Finset.single_le_sum (f := fun (j : Fin n) => d j)
            (fun _ _ => Nat.zero_le _) hi_mem
  have h_v_c_lt : twoAdicVal c < m := twoAdicVal_lt_of_ne_zero hc
  -- Rewrite the subtraction.
  rw [two_mul_monomial]
  rw [show (monomial (d.erase i) c - monomial d ((2 : ZMod (2 ^ m)) * c) : DiagPhase n m)
        = monomial (d.erase i) c + monomial d (-((2 : ZMod (2 ^ m)) * c)) from by
        rw [sub_eq_add_neg, ← map_neg]]
  refine Nat.add_one_le_iff.mpr ?_
  refine lt_of_le_of_lt (effectiveLevel_add_le _ _) ?_
  refine max_lt ?_ ?_
  · -- First summand: monomial (d.erase i) c.
    refine lt_of_le_of_lt (effectiveLevel_monomial_le _ _) ?_
    unfold effLevelMonom
    rw [sum_erase_multilinear i hdi]
    omega
  · -- Second summand: monomial d (-2c).
    -- Case-split: 2c = 0 (then -2c = 0 and the monomial is the zero polynomial) vs 2c ≠ 0.
    by_cases h2c : (2 : ZMod (2 ^ m)) * c = 0
    · -- -2c = 0, so the monomial is zero.
      have h_neg_zero : -((2 : ZMod (2 ^ m)) * c) = 0 := by rw [h2c, neg_zero]
      rw [h_neg_zero]
      rw [show ((monomial d (0 : ZMod (2 ^ m))) : DiagPhase n m) = 0 from
        (LinearMap.map_zero _)]
      rw [effectiveLevel_zero]
      unfold effLevelMonom
      omega
    · -- 2c ≠ 0. v(-2c) = v(2c) ≥ v(c) + 1.
      have h_neg_ne : -((2 : ZMod (2 ^ m)) * c) ≠ 0 := neg_ne_zero.mpr h2c
      rw [effectiveLevel_monomial_eq h_neg_ne]
      unfold effLevelMonom
      rw [twoAdicVal_neg]
      have h_v_two_mul : twoAdicVal c + 1 ≤ twoAdicVal ((2 : ZMod (2 ^ m)) * c) :=
        twoAdicVal_two_mul_ge h2c
      have h_v_2c_lt : twoAdicVal ((2 : ZMod (2 ^ m)) * c) < m :=
        twoAdicVal_lt_of_ne_zero h2c
      omega

/-- **Strict-drop lemma**: for multilinear `P : DiagPhase n m` with
positive total degree, `effectiveLevel (shiftDeriv i P)` is strictly
less than `effectiveLevel P`.

The proof bounds every monomial in the support-indexed decomposition
of `shiftDeriv i P` and transfers via `effectiveLevel_finsetSum_le`. -/
theorem shiftDeriv_effectiveLevel_lt {P : DiagPhase n m} (i : Fin n)
    (h_mul : IsMultilinear P) (h_deg : 0 < P.totalDegree) :
    effectiveLevel (shiftDeriv i P) < effectiveLevel P := by
  classical
  -- Decompose shiftDeriv as a sum over P.support.
  have h_decomp : shiftDeriv i P
      = ∑ d ∈ P.support, shiftDeriv i (monomial d (P.coeff d)) := by
    simp only [shiftDeriv]
    conv_lhs =>
      rw [show P = ∑ d ∈ P.support, monomial d (P.coeff d) from P.as_sum]
    rw [map_sum, Finset.sum_sub_distrib]
  rw [h_decomp]
  -- Bound by effLevelMonom for each summand.
  refine lt_of_le_of_lt (effectiveLevel_finsetSum_le _ _) ?_
  -- Sup over P.support of summand effective levels is bounded.
  -- Use `Finset.sup_lt_iff`.
  have h_pos_eff : 1 ≤ effectiveLevel P :=
    one_le_effectiveLevel_of_pos_totalDegree h_deg
  refine Finset.sup_lt_iff (by exact_mod_cast h_pos_eff) |>.mpr ?_
  intro d hd
  have h_c_ne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have h_d_mul : ∀ k, d k ≤ 1 := h_mul d hd
  by_cases hdi : d i = 0
  · -- shiftDeriv = 0, effectiveLevel = 0 < effectiveLevel P.
    rw [shiftDeriv_monomial_of_di_zero i d (P.coeff d) hdi]
    simpa using h_pos_eff
  · -- d i ≠ 0. Since d k ≤ 1, d i = 1.
    have h_di_one : d i = 1 := by
      have hle := h_d_mul i
      omega
    rw [shiftDeriv_monomial_multilinear_di_one i d (P.coeff d) h_di_one]
    -- Use shiftDeriv_monomial_effectiveLevel_lt.
    have h_drop : effectiveLevel
        ((monomial (d.erase i) (P.coeff d) - 2 * monomial d (P.coeff d)) : DiagPhase n m)
            + 1 ≤ effLevelMonom m (P.coeff d) d :=
      shiftDeriv_monomial_effectiveLevel_lt i h_c_ne h_di_one
    have h_effLev_le : effLevelMonom m (P.coeff d) d ≤ effectiveLevel P := by
      unfold effectiveLevel
      exact Finset.le_sup
        (f := fun e => effLevelMonom m (P.coeff e) e) hd
    omega

end DiagPhase

end FTQCLib.Hierarchy

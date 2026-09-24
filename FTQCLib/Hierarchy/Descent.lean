/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs

set_option linter.unusedSectionVars false

/-! # Strict descent for the discrete partial derivative

The discrete partial derivative
  `Δ_i P := bind₁ (fun k => if k = i then X k + 1 else X k) P − P`
on `DiagPhase n m = MvPolynomial (Fin n) (ZMod (2^m))` is the
polynomial-framework analogue of conjugation of the diagonal unitary
`U_P` by the Pauli `X_i`: it drops the Clifford-hierarchy level by one.

The engine of the hierarchy proof is the *strict descent lemma*

  `(Δ_i P).totalDegree < P.totalDegree   when   P.totalDegree > 0`.

This file proves the four core lemmas:

* `discreteDeriv_zero`, `discreteDeriv_C`, `discreteDeriv_add` — basic
  algebraic identities that follow from `bind₁` being an algebra
  homomorphism.
* `discreteDeriv_totalDegree_le` — the easy bound: `Δ_i` never raises
  total degree.
* `discreteDeriv_totalDegree_lt` — the strict version, used as the
  decreasing measure in the recursive level-drop argument.

The strict descent is proved via the monomial decomposition
`P = ∑ d ∈ P.support, monomial d (coeff d P)`. For each monomial:

* If `d i = 0`, the substitution `X_i ↦ X_i + 1` leaves the monomial
  fixed, so its `Δ_i` is zero.
* If `d i > 0`, the binomial theorem gives
    `(X_i + 1)^{d_i} = X_i^{d_i} + (terms of degree < d_i in X_i)`,
  so the difference has total degree `≤ d.sum − 1`.

Either way each monomial contribution has total degree `< d.sum ≤
P.totalDegree`, and summing preserves the strict bound.
-/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial

variable {n m : ℕ}

/-- Helper: the substitution that the discrete partial derivative uses.
For brevity in proofs we name `substShift i k := if k = i then X k + 1
else X k`. -/
private noncomputable def substShift (i : Fin n) (k : Fin n) :
    MvPolynomial (Fin n) (ZMod (2 ^ m)) :=
  if k = i then X k + 1 else X k

/-- Unfold `discreteDeriv` to its `bind₁` form. -/
private lemma discreteDeriv_eq (i : Fin n) (P : DiagPhase n m) :
    discreteDeriv i P = bind₁ (substShift (m := m) i) P - P := by
  rfl

/-- `Δ_i` annihilates the zero polynomial. Immediate from `bind₁` being
an algebra hom (in particular, sending `0` to `0`). -/
theorem discreteDeriv_zero (i : Fin n) :
    discreteDeriv (m := m) i 0 = 0 := by
  rw [discreteDeriv_eq]
  simp

/-- `Δ_i` annihilates constant polynomials. Immediate from
`bind₁_C_right`: the substitution `X_i ↦ X_i + 1` leaves `C c` fixed,
so the difference is zero. -/
theorem discreteDeriv_C (i : Fin n) (c : ZMod (2 ^ m)) :
    discreteDeriv (n := n) i (C c) = 0 := by
  rw [discreteDeriv_eq]
  rw [show (bind₁ (substShift (m := m) i) (C c) : DiagPhase n m) = C c from
    bind₁_C_right _ c]
  simp

/-- `Δ_i` is additive: `Δ_i (P + Q) = Δ_i P + Δ_i Q`. Follows from
`bind₁` being an algebra hom (hence additive). -/
theorem discreteDeriv_add (i : Fin n) (P Q : DiagPhase n m) :
    discreteDeriv i (P + Q) = discreteDeriv i P + discreteDeriv i Q := by
  rw [discreteDeriv_eq, discreteDeriv_eq, discreteDeriv_eq, map_add]
  abel

/-- `X k` has total degree at most 1 in any base ring. (When the base
ring is nontrivial this is the equality `totalDegree_X`; in the trivial
ring `X k = 0`, total degree 0.) -/
private lemma totalDegree_X_le_one (k : Fin n) :
    (X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree ≤ 1 := by
  have h : (X k : MvPolynomial (Fin n) (ZMod (2 ^ m))) =
      monomial (Finsupp.single k 1) (1 : ZMod (2 ^ m)) := by
    rw [X, monomial]
  rw [h]
  refine (totalDegree_monomial_le _ _).trans ?_
  simp [Finsupp.sum_single_index]

/-- The substitution `substShift i k = X k` (if `k ≠ i`) or `X i + 1`
(if `k = i`) has total degree at most 1 at every index. -/
private lemma substShift_totalDegree_le (i k : Fin n) :
    (substShift (m := m) i k).totalDegree ≤ 1 := by
  unfold substShift
  split_ifs with hk
  · -- `X k + 1`: total degree at most 1.
    calc (X k + 1 : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
        ≤ max (X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
            (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree :=
          totalDegree_add _ _
      _ ≤ max 1 0 := by
          gcongr
          · exact totalDegree_X_le_one k
          · rw [totalDegree_one]
      _ = 1 := by simp
  · -- `X k`: total degree at most 1.
    exact totalDegree_X_le_one k

/-- Monomial bound for `bind₁ (substShift i)`: applied to a single
monomial `monomial d c`, the substitution yields a polynomial of total
degree at most `d.sum`. -/
private lemma bind₁_substShift_monomial_totalDegree_le (i : Fin n)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) :
    (bind₁ (substShift (m := m) i) (monomial d c)).totalDegree
      ≤ d.sum (fun _ e => e) := by
  rw [bind₁_monomial]
  calc (C c * ∏ k ∈ d.support, substShift (m := m) i k ^ d k).totalDegree
      ≤ (C c).totalDegree
        + (∏ k ∈ d.support, substShift (m := m) i k ^ d k).totalDegree :=
        totalDegree_mul _ _
    _ = (∏ k ∈ d.support, substShift (m := m) i k ^ d k).totalDegree := by
        rw [totalDegree_C, zero_add]
    _ ≤ ∑ k ∈ d.support, (substShift (m := m) i k ^ d k).totalDegree :=
        totalDegree_finset_prod _ _
    _ ≤ ∑ k ∈ d.support, d k * (substShift (m := m) i k).totalDegree := by
        gcongr with k _
        exact totalDegree_pow _ _
    _ ≤ ∑ k ∈ d.support, d k * 1 := by
        gcongr with k _
        exact substShift_totalDegree_le i k
    _ = ∑ k ∈ d.support, d k := by simp
    _ = d.sum (fun _ e => e) := rfl

/-- The substitution `bind₁ (substShift i)` does not raise total
degree. Proved by writing `P` as the support-indexed sum of monomials
and bounding each summand. -/
private lemma bind₁_substShift_totalDegree_le (i : Fin n) (P : DiagPhase n m) :
    (bind₁ (substShift (m := m) i) P).totalDegree ≤ P.totalDegree := by
  -- Rewrite `P` as the sum of its monomials, then push `bind₁` over the
  -- sum and bound each summand individually.
  conv_lhs => rw [P.as_sum, map_sum]
  refine totalDegree_finsetSum_le ?_
  intro d hd
  refine (bind₁_substShift_monomial_totalDegree_le i d (P.coeff d)).trans ?_
  -- `d.sum (fun _ e => e) ≤ P.totalDegree` because `d ∈ P.support`.
  exact le_totalDegree hd

/-- **Easy descent bound**: `Δ_i P` has total degree at most `P`. -/
theorem discreteDeriv_totalDegree_le (i : Fin n) (P : DiagPhase n m) :
    (discreteDeriv i P).totalDegree ≤ P.totalDegree := by
  rw [discreteDeriv_eq]
  calc (bind₁ (substShift (m := m) i) P - P).totalDegree
      ≤ max (bind₁ (substShift (m := m) i) P).totalDegree P.totalDegree :=
        totalDegree_sub _ _
    _ ≤ max P.totalDegree P.totalDegree :=
        max_le_max (bind₁_substShift_totalDegree_le i P) le_rfl
    _ = P.totalDegree := max_self _

/-! ### Strict descent

The remaining work is the strict bound `(Δ_i P).totalDegree <
P.totalDegree` under `0 < P.totalDegree`. The proof proceeds by

1. expanding `(X i + 1)^k - X i^k` via the binomial theorem and bounding
   its total degree by `k - 1` (Lemma `Xi_addOne_pow_sub_totalDegree`),
2. lifting to the monomial bound `(Δ_i (monomial d c)).totalDegree <
   d.sum` (Lemma `discreteDeriv_monomial_totalDegree_lt`),
3. summing over the monomial support of `P` (`discreteDeriv_totalDegree_lt`).
-/

/-- **Binomial cancellation**: `(X i + 1)^k - X i^k` has total degree
strictly less than `k` (when `k ≥ 1`). The top-degree term `X i^k`
cancels, leaving a sum of monomials in `X i` of degree at most `k - 1`.
Proved by expanding `(X i + 1)^k` via `add_pow` and isolating the top
term. -/
private lemma Xi_addOne_pow_sub_totalDegree (i : Fin n) {k : ℕ} (hk : 1 ≤ k) :
    ((X i + 1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ k - X i ^ k).totalDegree
      < k := by
  -- Step 1: expand `(X i + 1)^k` via the binomial theorem.
  have h_expand :
      ((X i + 1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ k)
        = ∑ j ∈ Finset.range (k + 1),
            X i ^ j * (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)
              * (k.choose j : MvPolynomial (Fin n) (ZMod (2 ^ m))) :=
    add_pow (X i) 1 k
  -- Step 2: separate the top (`j = k`) summand from the rest.
  rw [h_expand, Finset.sum_range_succ]
  -- The `j = k` term is `X i ^ k * 1 * 1 = X i ^ k`, which will cancel.
  have h_kk : (X i ^ k * (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - k)
                * (k.choose k : MvPolynomial (Fin n) (ZMod (2 ^ m))))
              = X i ^ k := by
    rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
  rw [h_kk, add_sub_cancel_right]
  -- Bound the sum: each summand `X i ^ j * 1 ^ (k - j) * (k.choose j)` has
  -- total degree at most `j`, which is `< k` for `j ∈ range k`.
  refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ?_
  refine Finset.sup_lt_iff (by exact_mod_cast hk) |>.mpr ?_
  intro j hj
  have hj_lt : j < k := Finset.mem_range.mp hj
  -- Each summand has totalDegree ≤ j.
  -- We bound by writing the summand as a constant (cast of `k.choose j`)
  -- times `X i ^ j * 1 ^ (k - j)`, then `totalDegree_mul` etc.
  have h_choose_const :
      ((k.choose j : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree) ≤ 0 := by
    have : (k.choose j : MvPolynomial (Fin n) (ZMod (2 ^ m)))
            = C ((k.choose j : ℕ) : ZMod (2 ^ m)) := by
      rw [← C_eq_coe_nat]
    rw [this, totalDegree_C]
  calc (X i ^ j * (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)
            * (k.choose j : MvPolynomial (Fin n) (ZMod (2 ^ m)))).totalDegree
      ≤ (X i ^ j * (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)).totalDegree
          + (k.choose j : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree :=
        totalDegree_mul _ _
    _ ≤ (X i ^ j * (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)).totalDegree
          + 0 := by gcongr
    _ = (X i ^ j * (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)).totalDegree :=
          by rw [add_zero]
    _ ≤ (X i ^ j : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
          + ((1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)).totalDegree :=
        totalDegree_mul _ _
    _ ≤ j * (X i : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
          + ((1 : MvPolynomial (Fin n) (ZMod (2 ^ m))) ^ (k - j)).totalDegree := by
        gcongr
        exact totalDegree_pow _ _
    _ ≤ j * 1 + 0 := by
        gcongr
        · exact totalDegree_X_le_one i
        · rw [one_pow]
          exact le_of_eq totalDegree_one
    _ = j := by ring
    _ < k := hj_lt

/-- When `d i = 0`, the substitution `substShift i` is the identity on
the variables appearing in `monomial d c`, so `bind₁ (substShift i)`
fixes `monomial d c`. -/
private lemma bind₁_substShift_monomial_of_di_zero (i : Fin n)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) (hdi : d i = 0) :
    bind₁ (substShift (m := m) i) (monomial d c) = monomial d c := by
  rw [bind₁_monomial]
  -- `f k = X k` for every `k ∈ d.support`, since `i ∉ d.support`.
  have h_supp : ∀ k ∈ d.support, substShift (m := m) i k = X k := by
    intro k hk
    have hki : k ≠ i := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hk) hdi
    unfold substShift
    rw [if_neg hki]
  rw [Finset.prod_congr rfl (fun k hk => by rw [h_supp k hk])]
  -- Now goal: `C c * ∏ k ∈ d.support, X k ^ d k = monomial d c`.
  rw [prod_X_pow_eq_monomial, C_mul_monomial, mul_one]

/-- **Strict descent at a monomial**: if the monomial `monomial d c` has
positive total degree (`d.sum ≥ 1`), then `Δ_i (monomial d c)` has
strictly smaller total degree. -/
private lemma discreteDeriv_monomial_totalDegree_lt (i : Fin n)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) (hd : 1 ≤ d.sum (fun _ e => e)) :
    (discreteDeriv i (monomial d c : DiagPhase n m)).totalDegree
      < d.sum (fun _ e => e) := by
  rw [discreteDeriv_eq]
  by_cases hdi : d i = 0
  · -- `bind₁ f` fixes `monomial d c`, so the difference is zero.
    rw [bind₁_substShift_monomial_of_di_zero i d c hdi, sub_self,
      totalDegree_zero]
    exact hd
  · -- `d i ≥ 1`. Factor `bind₁ f (monomial d c) - monomial d c` and use
    -- the binomial cancellation lemma.
    have hdi_pos : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr hdi
    -- Rewrite both sides of the subtraction as products.
    rw [bind₁_monomial, monomial_eq]
    -- Split `d.support` at `k = i`.
    have hi_mem : i ∈ d.support := by
      rw [Finsupp.mem_support_iff]; exact hdi
    -- Express each side as `C c * (f i)^{d i} * ∏_{k ≠ i} (f k or X k)^{d k}`.
    set rest_prod : MvPolynomial (Fin n) (ZMod (2 ^ m)) :=
      ∏ k ∈ d.support.erase i, X k ^ d k with hrest_def
    -- bind₁ side: ∏ k ∈ d.support, substShift i k ^ d k
    --           = (X i + 1)^{d i} * ∏ k ∈ d.support.erase i, X k ^ d k
    have h_bind_split :
        (∏ k ∈ d.support, substShift (m := m) i k ^ d k)
          = (X i + 1)^(d i) * rest_prod := by
      rw [← Finset.mul_prod_erase _ _ hi_mem]
      -- LHS now: substShift i i ^ d i * ∏ k ∈ d.support.erase i, substShift i k ^ d k
      have h_i : substShift (m := m) i i = (X i + 1) := by
        unfold substShift; rw [if_pos rfl]
      rw [h_i]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      have h_ne : substShift (m := m) i k = X k := by
        unfold substShift; rw [if_neg hki]
      rw [h_ne]
    -- monomial side: d.prod (X · ^ ·) = X i ^ d i * ∏_{k ∈ d.support.erase i} X k ^ d k
    have h_mono_split :
        (d.prod fun n e => X n ^ e : MvPolynomial (Fin n) (ZMod (2 ^ m)))
          = X i ^ d i * rest_prod := by
      rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hi_mem]
    rw [h_bind_split, h_mono_split]
    -- Now the goal is:
    -- (C c * ((X i + 1) ^ d i * rest_prod) - C c * (X i ^ d i * rest_prod)).totalDegree
    --   < d.sum
    -- Factor: C c * ((X i + 1)^{d i} - X i^{d i}) * rest_prod.
    have h_factor :
        (C c * ((X i + 1) ^ d i * rest_prod) - C c * (X i ^ d i * rest_prod))
          = C c * (((X i + 1) ^ d i - X i ^ d i) * rest_prod) := by ring
    rw [h_factor]
    -- Bound via `totalDegree_mul`:
    -- ≤ (C c).totalDegree + ((X i + 1)^{d i} - X i^{d i}).totalDegree + rest_prod.totalDegree
    -- ≤ 0 + (d i - 1) + ∑_{k ∈ d.support.erase i} d k
    -- = d.sum - 1 < d.sum.
    have h_inner_lt : (((X i + 1) ^ d i - X i ^ d i :
                        MvPolynomial (Fin n) (ZMod (2 ^ m)))).totalDegree < d i :=
      Xi_addOne_pow_sub_totalDegree i hdi_pos
    have h_rest_le : rest_prod.totalDegree ≤
        ∑ k ∈ d.support.erase i, d k := by
      rw [hrest_def]
      refine (totalDegree_finset_prod _ _).trans ?_
      refine Finset.sum_le_sum ?_
      intro k _
      refine (totalDegree_pow _ _).trans ?_
      have hk_le : (X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree ≤ 1 :=
        totalDegree_X_le_one k
      calc d k * (X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
          ≤ d k * 1 := Nat.mul_le_mul_left _ hk_le
        _ = d k := by ring
    -- Combine the bounds.
    have h_sum_split :
        ∑ k ∈ d.support.erase i, d k + d i = d.sum (fun _ e => e) := by
      rw [Finsupp.sum, ← Finset.sum_erase_add _ _ hi_mem]
    calc (C c * (((X i + 1) ^ d i - X i ^ d i) * rest_prod)).totalDegree
        ≤ (C c).totalDegree
            + (((X i + 1) ^ d i - X i ^ d i) * rest_prod).totalDegree :=
          totalDegree_mul _ _
      _ = (((X i + 1) ^ d i - X i ^ d i) * rest_prod).totalDegree := by
          rw [totalDegree_C, zero_add]
      _ ≤ ((X i + 1) ^ d i - X i ^ d i :
            MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
          + rest_prod.totalDegree :=
          totalDegree_mul _ _
      _ < d i + rest_prod.totalDegree := by
          exact Nat.add_lt_add_right h_inner_lt _
      _ ≤ d i + ∑ k ∈ d.support.erase i, d k := by
          exact Nat.add_le_add_left h_rest_le _
      _ = d.sum (fun _ e => e) := by
          rw [Nat.add_comm]; exact h_sum_split

/-- **Strict descent lemma**: when `P` has positive total degree, the
discrete partial derivative `Δ_i P` has strictly smaller total degree.
This is the engine of the level-drop induction in the
Cui–Gottesman–Krishna hierarchy classification: each iteration of
conjugation by Pauli `X` drops the polynomial-level by at least one.
Proved by writing `P` as the sum of its monomials, applying
`discreteDeriv_monomial_totalDegree_lt` to each summand, and bounding
the resulting sum. -/
theorem discreteDeriv_totalDegree_lt {P : DiagPhase n m} (i : Fin n)
    (h : 0 < P.totalDegree) :
    (discreteDeriv i P).totalDegree < P.totalDegree := by
  -- Rewrite `discreteDeriv i P` as a sum over the support of `P`.
  have h_eq : discreteDeriv i P
      = ∑ d ∈ P.support, discreteDeriv i (monomial d (P.coeff d)) := by
    have hPsum : P = ∑ d ∈ P.support, (monomial d (P.coeff d) : DiagPhase n m) :=
      P.as_sum
    rw [discreteDeriv_eq]
    conv_lhs => rw [hPsum]
    simp_rw [discreteDeriv_eq]
    rw [map_sum, Finset.sum_sub_distrib]
  rw [h_eq]
  -- Each summand has totalDegree < P.totalDegree.
  refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ?_
  refine Finset.sup_lt_iff (by exact_mod_cast h) |>.mpr ?_
  intro d hd
  -- `d.sum ≤ P.totalDegree` from membership; but we need strict.
  -- Use `discreteDeriv_monomial_totalDegree_lt` for the d.sum ≥ 1 case,
  -- and a direct check for d.sum = 0 (where Δ_i = 0).
  by_cases hdsum : 1 ≤ d.sum (fun _ e => e)
  · -- Strict bound on the monomial degree.
    have h_lt := discreteDeriv_monomial_totalDegree_lt i d (P.coeff d) hdsum
    -- And d.sum ≤ P.totalDegree.
    have h_le : d.sum (fun _ e => e) ≤ P.totalDegree := le_totalDegree hd
    exact lt_of_lt_of_le h_lt h_le
  · -- d.sum = 0: monomial is a constant, Δ_i is zero.
    have hd0 : d.sum (fun _ e => e) = 0 := by
      have h_lt : d.sum (fun _ e => e) < 1 := not_le.mp hdsum
      omega
    -- A `Finsupp.sum` of natural numbers being zero forces `d = 0`.
    have hd_eq : d = 0 := by
      ext k
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      by_cases hk : k ∈ d.support
      · -- `d k ≤ d.sum` and `d.sum = 0`, so `d k = 0`.
        have h_in_sum : d k ≤ d.sum (fun _ e => e) := by
          rw [Finsupp.sum]
          exact Finset.single_le_sum (f := fun (j : Fin n) => d j)
            (fun _ _ => Nat.zero_le _) hk
        omega
      · exact Finsupp.notMem_support_iff.mp hk
    -- With `d = 0`, the monomial is a constant.
    have h_mono : (monomial d (P.coeff d) : DiagPhase n m)
        = C (P.coeff d) := by
      rw [hd_eq, ← C_apply]
    rw [h_mono, discreteDeriv_C, totalDegree_zero]
    exact h

end FTQCLib.Hierarchy.DiagPhase

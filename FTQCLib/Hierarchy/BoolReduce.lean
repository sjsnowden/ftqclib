/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.FuncDeriv
import Mathlib.Data.Finsupp.Indicator


/-!
# Boolean reduction of phase polynomials

For evaluation on binary inputs `v : Fin n → ZMod 2`, the only fact
needed about `x ^ a` in `ZMod (2^m)` is the two-element identity
`0 ^ a = 0` and `1 ^ a = 1` (for `a ≥ 1`). Consequently every
polynomial `P : DiagPhase n m` agrees on `liftBinary v` with its
**Boolean reduction** `boolReduce P`, a multilinear (degree ≤ 1 in
each variable) polynomial built by collapsing every monomial
`monomial d c` to `monomial (boolShadow d) c`, where `boolShadow d`
is the indicator of `d.support`.

This file proves three concrete polynomial-algebra results:

* `boolShadow` — the multilinear shadow of an exponent multiset;
  technical machinery (`boolShadow_apply`, `boolShadow_support`,
  `boolShadow_sum_le`).
* `boolReduce` — the linear extension of `monomial d c ↦
  monomial (boolShadow d) c` over the monomial support of `P`.
* `boolReduce_eval` — agreement of `(boolReduce P).eval` and
  `P.eval` on every binary input. The proof reduces to the
  two-element check above.
* `boolReduce_totalDegree_le` — `boolReduce` does not raise total
  degree. (In fact it never raises the degree of *any* monomial; the
  bound `|d.support| ≤ d.sum` is tight for multilinear `d`.)

## The level drop

The Cui–Gottesman–Krishna forward direction needs a level drop under the discrete derivative. On
the Boolean normal form the *total degree* does not drop in general once `m ≥ 2`: `shiftDeriv` of
the multilinear `X i * A` (with `A` free of `X i`) is `(1 - X i) * A - X i * A = A - 2 * X i * A`,
whose top term survives because `2 ≠ 0` in `ZMod (2^m)`. The drop that holds is in the **effective
level**, which charges that factor `2` to the valuation: `shiftDeriv_effectiveLevel_lt`
(`FTQCLib/Hierarchy/EffectiveLevel.lean`) is the formal statement. The normal form's own level
bound is
`effectiveLevel_boolReduce_le`, with the multilinearity `boolReduce_isMultilinear` and the merge
formula `coeff_boolReduce` (`FTQCLib/Hierarchy/BoolReduceLevel.lean`).

A drop in the precision `m` itself — dividing the `2`-divisible top coefficients through and
landing in `ZMod (2^(m-1))` — is a different statement about a rescaling operator, and is not
built.
-/

namespace FTQCLib.Hierarchy

open MvPolynomial

namespace DiagPhase

variable {n m : ℕ}

/-! ### The Boolean shadow of an exponent multiset

`boolShadow d` replaces every nonzero entry of `d` by `1`, producing
the indicator of `d.support`. Concretely:
* `(boolShadow d) k = 1` if `d k ≥ 1`,
* `(boolShadow d) k = 0` if `d k = 0`.

Its support equals `d.support` (since `1 ≠ 0` in `ℕ`), and its
`Finsupp.sum` equals `d.support.card ≤ d.sum`. -/
noncomputable def boolShadow (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.indicator d.support (fun _ _ => 1)

@[simp] lemma boolShadow_apply (d : Fin n →₀ ℕ) (k : Fin n) :
    boolShadow d k = if k ∈ d.support then 1 else 0 := by
  classical
  unfold boolShadow
  rw [Finsupp.indicator_apply]
  split_ifs <;> rfl

/-- The support of `boolShadow d` equals the support of `d`. -/
lemma boolShadow_support (d : Fin n →₀ ℕ) :
    (boolShadow d).support = d.support := by
  classical
  ext k
  rw [Finsupp.mem_support_iff, boolShadow_apply]
  by_cases hk : k ∈ d.support
  · rw [if_pos hk]
    refine ⟨fun _ => hk, fun _ => ?_⟩
    exact one_ne_zero
  · rw [if_neg hk]
    refine ⟨fun h => (h rfl).elim, fun h => (hk h).elim⟩

/-- For `k ∈ d.support`, `boolShadow d k = 1`. -/
lemma boolShadow_apply_mem {d : Fin n →₀ ℕ} {k : Fin n}
    (hk : k ∈ d.support) : boolShadow d k = 1 := by
  rw [boolShadow_apply, if_pos hk]

/-- For `k ∉ d.support`, `boolShadow d k = 0`. -/
lemma boolShadow_apply_notMem {d : Fin n →₀ ℕ} {k : Fin n}
    (hk : k ∉ d.support) : boolShadow d k = 0 := by
  rw [boolShadow_apply, if_neg hk]

/-- The total degree of `boolShadow d` (its `Finsupp.sum`) equals the
cardinality of `d.support`. -/
lemma boolShadow_sum (d : Fin n →₀ ℕ) :
    (boolShadow d).sum (fun _ e => e) = d.support.card := by
  classical
  rw [Finsupp.sum, boolShadow_support]
  -- Every entry of `boolShadow d` on `d.support` is `1`, so the sum is
  -- `∑ k ∈ d.support, 1 = d.support.card`.
  rw [Finset.sum_congr rfl
      (g := fun _ => (1 : ℕ))
      (fun k hk => boolShadow_apply_mem hk)]
  rw [Finset.sum_const, Nat.smul_one_eq_cast]
  simp

/-- The total degree of `boolShadow d` is at most that of `d`. Each
nonzero entry of `d` contributes at least `1` to `d.sum`, so
`d.support.card ≤ d.sum`. -/
lemma boolShadow_sum_le (d : Fin n →₀ ℕ) :
    (boolShadow d).sum (fun _ e => e) ≤ d.sum (fun _ e => e) := by
  classical
  rw [boolShadow_sum, Finsupp.sum]
  -- `d.support.card ≤ ∑ k ∈ d.support, d k` because each `d k ≥ 1` on
  -- the support.
  have hcard : d.support.card = ∑ _k ∈ d.support, (1 : ℕ) := by
    rw [Finset.sum_const, Nat.smul_one_eq_cast]; simp
  rw [hcard]
  refine Finset.sum_le_sum ?_
  intro k hk
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)

/-! ### The Boolean reduction of a polynomial

Replace every monomial `monomial d c` in `P` by `monomial (boolShadow d) c`,
where `boolShadow d` is the indicator of `d.support`. Different `d`s in
`P.support` may share the same Boolean shadow; the corresponding
coefficients are added (this is just the `Finset.sum` of the
`monomial`s). -/
noncomputable def boolReduce (P : DiagPhase n m) : DiagPhase n m :=
  ∑ d ∈ P.support, monomial (boolShadow d) (P.coeff d)

/-- `boolReduce` sends `0` to `0`. -/
@[simp] lemma boolReduce_zero : boolReduce (0 : DiagPhase n m) = 0 := by
  unfold boolReduce
  simp

/-- The reduction may be summed over any superset of the support: the extra monomials have
coefficient `0`. -/
theorem boolReduce_sum_superset {P : DiagPhase n m} {s : Finset (Fin n →₀ ℕ)}
    (hs : P.support ⊆ s) : boolReduce P = ∑ d ∈ s, monomial (boolShadow d) (P.coeff d) := by
  unfold boolReduce
  refine Finset.sum_subset hs (fun d _ hd => ?_)
  rw [MvPolynomial.notMem_support_iff.mp hd, map_zero]

/-- **The normal form is additive.** Both sides are read on the union of the three supports, where
the coefficients add monomial by monomial. -/
theorem boolReduce_add (P Q : DiagPhase n m) :
    boolReduce (P + Q) = boolReduce P + boolReduce Q := by
  classical
  have hP : P.support ⊆ P.support ∪ Q.support ∪ (P + Q).support :=
    (Finset.subset_union_left).trans Finset.subset_union_left
  have hQ : Q.support ⊆ P.support ∪ Q.support ∪ (P + Q).support :=
    (Finset.subset_union_right).trans Finset.subset_union_left
  have hPQ : (P + Q).support ⊆ P.support ∪ Q.support ∪ (P + Q).support := Finset.subset_union_right
  rw [boolReduce_sum_superset hP, boolReduce_sum_superset hQ, boolReduce_sum_superset hPQ,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun d _ => by rw [MvPolynomial.coeff_add, map_add])

/-! ### Total-degree bound

Each summand `monomial (boolShadow d) (coeff d P)` has total degree at
most `(boolShadow d).sum ≤ d.sum ≤ P.totalDegree`. Summing preserves
the bound via `totalDegree_finsetSum_le`. -/

theorem boolReduce_totalDegree_le (P : DiagPhase n m) :
    (boolReduce P).totalDegree ≤ P.totalDegree := by
  unfold boolReduce
  refine totalDegree_finsetSum_le ?_
  intro d hd
  refine (totalDegree_monomial_le _ _).trans ?_
  -- `(boolShadow d).sum ≤ d.sum ≤ P.totalDegree`.
  refine (boolShadow_sum_le d).trans ?_
  exact le_totalDegree hd

/-! ### Evaluation agreement on binary inputs

The proof reduces to a per-monomial check: for each `d ∈ P.support`,
the `(monomial d c)` and `(monomial (boolShadow d) c)` evaluations
agree on every binary input. Concretely, both equal
`c * ∏ k ∈ d.support, (liftBinary v k)`, because:

* The left side is `c * ∏ k ∈ d.support, (liftBinary v k)^(d k)`,
  and `(liftBinary v k)^(d k) = liftBinary v k` for `k ∈ d.support`
  (where `d k ≥ 1`) because `liftBinary v k ∈ {0, 1}` and both `0` and
  `1` are fixed by positive powers.
* The right side is `c * ∏ k ∈ d.support, (liftBinary v k)^1` because
  `boolShadow d` takes value `1` on `d.support` and has support equal
  to `d.support`. -/

/-- A `ZMod (2^m)` element of the form `liftBinary v k` is either `0`
or `1`. -/
private lemma liftBinary_cases (v : Fin n → ZMod 2) (k : Fin n) :
    liftBinary (m := m) v k = 0 ∨ liftBinary (m := m) v k = 1 := by
  unfold liftBinary
  have hlt : (v k).val < 2 := ZMod.val_lt _
  interval_cases (v k).val
  · left; simp
  · right; simp

/-- The two-element identity: `x^a = x` for `x ∈ {0, 1}` and `a ≥ 1`. -/
private lemma pow_eq_of_binary {x : ZMod (2 ^ m)} (hx : x = 0 ∨ x = 1)
    {a : ℕ} (ha : 1 ≤ a) : x ^ a = x := by
  rcases hx with hx0 | hx1
  · rw [hx0]; rw [zero_pow (Nat.one_le_iff_ne_zero.mp ha)]
  · rw [hx1]; rw [one_pow]

/-- Per-monomial evaluation agreement. For every `d` and `c`,
`MvPolynomial.eval (liftBinary v) (monomial d c) =
  MvPolynomial.eval (liftBinary v) (monomial (boolShadow d) c)`. -/
private lemma eval_monomial_boolShadow (v : Fin n → ZMod 2)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) :
    MvPolynomial.eval (liftBinary v) (monomial d c)
      = MvPolynomial.eval (liftBinary v) (monomial (boolShadow d) c) := by
  classical
  rw [eval_monomial, eval_monomial]
  congr 1
  -- Goal: `d.prod (fun k e => (liftBinary v k)^e) =
  --        (boolShadow d).prod (fun k e => (liftBinary v k)^e)`.
  rw [Finsupp.prod, Finsupp.prod, boolShadow_support]
  -- Both products are over `d.support`. Show termwise agreement.
  refine Finset.prod_congr rfl ?_
  intro k hk
  -- LHS exponent: `d k`. RHS exponent: `(boolShadow d) k = 1`.
  rw [boolShadow_apply_mem hk, pow_one]
  -- `(liftBinary v k)^(d k) = liftBinary v k`.
  have hd_pos : 1 ≤ d k :=
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)
  exact pow_eq_of_binary (liftBinary_cases v k) hd_pos

/-- **Evaluation agreement on binary inputs**: `boolReduce P` agrees
with `P` on every `liftBinary v`. -/
theorem boolReduce_eval (P : DiagPhase n m) (v : Fin n → ZMod 2) :
    MvPolynomial.eval (liftBinary v) (boolReduce P)
      = MvPolynomial.eval (liftBinary v) P := by
  -- Write `P` as the sum of its monomials and apply `eval_monomial_boolShadow`
  -- term-by-term.
  unfold boolReduce
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro d _
  exact (eval_monomial_boolShadow v d (P.coeff d)).symm

/-- **Evaluation agreement, `DiagPhase.eval` form**. The wrapped form
`DiagPhase.eval` is the one used downstream in `CGKForward.lean`. -/
theorem boolReduce_eval_eq (P : DiagPhase n m) (v : Fin n → ZMod 2) :
    (boolReduce P).eval v = P.eval v := by
  unfold DiagPhase.eval
  exact boolReduce_eval P v

/-! ### Idempotence and trivial cases

`boolReduce` is the identity on multilinear polynomials (each `d`
already has `d k ≤ 1`), and in particular on constants. We record the
constant case since it is the only one used in the base of the
induction. -/

/-- `boolShadow 0 = 0`: the indicator of the empty support is zero. -/
@[simp] lemma boolShadow_zero : boolShadow (0 : Fin n →₀ ℕ) = 0 := by
  ext k
  rw [boolShadow_apply, Finsupp.support_zero]
  simp

@[simp] theorem boolReduce_C (c : ZMod (2 ^ m)) :
    boolReduce (n := n) (C c) = C c := by
  classical
  unfold boolReduce
  by_cases hc : c = 0
  · simp [hc]
  · rw [support_C, if_neg hc, Finset.sum_singleton, coeff_C, if_pos rfl,
      boolShadow_zero]
    rw [← C_apply]

/-! ### The level drop, for navigation

The strict drop under `shiftDeriv` is in the effective level, not the total degree:
`shiftDeriv_effectiveLevel_lt` (`EffectiveLevel.lean`), with `boolReduce_eval` identifying the
normal form's values and `effectiveLevel_boolReduce_le` (`BoolReduceLevel.lean`) bounding its
level. The module docstring says which statement is which. -/

end DiagPhase

end FTQCLib.Hierarchy

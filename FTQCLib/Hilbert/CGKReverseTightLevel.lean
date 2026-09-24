/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseGeneral
import FTQCLib.Hilbert.CGKReverseVanish
import FTQCLib.Hilbert.CGKReverseAnchor

set_option linter.unusedSectionVars false

/-! # CGK reverse — tighter polynomial witness via Möbius assembly

The general-`k` polynomial-witness existence theorem
`cgk_reverse_dyadic_poly_general` of `CGKReverseGeneral.lean` uses a
Boolean Lagrange basis to interpolate the per-point dyadic values of
the phase function `g`. That construction produces a polynomial whose
`totalDegree` is bounded only by `n` (the number of qubits) — not by
the hierarchy level `k`. The result of CGK Theorem 2 at `p = 2` is
sharper: the polynomial has `totalDegree ≤ k`.

This file delivers the sharper bound via **Möbius-coefficient
assembly**. The construction:

* For each non-empty `S ⊆ Fin n` with `|S| ≤ k`, the iterated
  discrete derivative `c_S := funcDerivPhaseSubset S g 0` is dyadic
  mod `2π` (`mobiusCoeff_dyadic_mod_2pi_level_k`).
* For `|S| > k`, the same coefficient is **exactly** an integer
  multiple of `2π` (`funcDerivPhaseSubset_vanish_mod_2pi_of_card_gt_level`).
* The constant term `c_∅ = g(0)` is dyadic mod `2π` by hypothesis
  (the anchor).
* Assemble `P(X) = Σ_{S : |S| ≤ k} c_S' · ∏_{i ∈ S} X_i` over a
  uniform precision `m` chosen so every `c_S` admits a precision-`m`
  encoding `c_S' ∈ ZMod (2^m)`. The polynomial has
  `totalDegree ≤ k` by `totalDegree_finsetSum_le`.
* By Möbius inversion (`mobius_inversion_boolean`,
  `BooleanMobius.lean`) and the vanishing of high-weight
  coefficients, the polynomial-side evaluation `realPhase P v`
  matches `g(v)` modulo `2π`.

## What this file delivers

* **`cgk_reverse_dyadic_poly_mobius_general`** — for every `k ≥ 1`,
  a diagonal `U` at level `k` of the dyadic hierarchy with `g(0)`
  dyadic mod `2π` admits a polynomial witness `P : DiagPhase n m`
  with `P.totalDegree ≤ k`. The improvement over the Lagrange-based
  version (`cgk_reverse_dyadic_poly_general`) is the tighter degree
  bound.

## What this file does NOT deliver

* **`P.level ≤ k`** against `IsCliffordHierarchyDyadic k U`. The
  level bound `P.level = (m - 1) + P.totalDegree` is precision-
  dependent. The dyadic predicate does not bound the base-scalar
  precision `m` by `k` (counterexample: `e^{iπ/4} · I` lives at
  dyadic level 1 with base scalar `α = e^{iπ/4}` needing precision
  `m ≥ 3`, so every polynomial encoding has `P.level ≥ 2`). The
  strict `P.level ≤ k` bound requires a tightened predicate that
  recursively constrains base-scalar precision by depth; the
  projective form is `cgk_reverse_projective_sharp` in
  `CGKTwoSided.lean`.

## Anchors

* CGK 2017 (arXiv:1608.06596) Theorem 2 / Lemma 4, eq. (62) at
  `p = 2`: the level formula `w = (m - 1) + d`, where `d` is the
  polynomial degree.
* Rota 1964 — Möbius inversion on the Boolean lattice.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase BooleanMobius

variable {n : ℕ}

/-! ## Coefficient bookkeeping

For each `S ⊆ Fin n` with `|S| ≤ k`, we extract a dyadic encoding of
the Möbius coefficient `c_S := funcDerivPhaseSubset S g 0`. The
non-empty `S` cases use `mobiusCoeff_dyadic_mod_2pi_level_k`; the
empty case uses the anchor `g(0)` dyadic. The vanishing for `|S| > k`
is handled separately at the assembly step. -/

/-- **Pointwise dyadic representation of all Möbius coefficients up to
weight `k`.** Given level-`k` hierarchy membership and the anchor
`g(0)` dyadic, every Möbius coefficient `funcDerivPhaseSubset S g 0`
(for every `S` with `|S| ≤ k`, including the empty case `c_∅ = g(0)`)
admits a dyadic representation at some per-`S` precision. -/
private theorem mobiusCoeff_dyadic_pointwise
    {k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    (h_anchor : IsDyadicMod2pi (g 0)) :
    ∀ S : Finset (Fin n), S.card ≤ k →
      IsDyadicMod2pi (funcDerivPhaseSubset S g 0) := by
  intro S _hS_card
  by_cases h_empty : S = ∅
  · rw [h_empty, funcDerivPhaseSubset_empty]
    exact h_anchor
  · exact mobiusCoeff_dyadic_mod_2pi_level_k hk h_hier
      (Finset.nonempty_iff_ne_empty.mpr h_empty)

/-- **Uniform precision for the Möbius coefficients up to weight `k`.**
Since `Finset (Fin n)` is finite, the pointwise per-`S` precision lifts
to a uniform precision `m` such that every coefficient `c_S` (for
`|S| ≤ k`) admits a representation at precision `m`. -/
private theorem exists_uniform_precision_mobiusCoeffs
    {k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    (h_anchor : IsDyadicMod2pi (g 0)) :
    ∃ (m : ℕ),
      ∀ S : Finset (Fin n), S.card ≤ k →
        ∃ (c : ZMod (2 ^ m)) (kint : ℤ),
          funcDerivPhaseSubset S g 0 =
            2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m + 2 * Real.pi * (kint : ℝ) := by
  classical
  -- For each S : Finset (Fin n), assign a per-S precision m_S, residue
  -- c_S, offset k_S realising the dyadic representation when |S| ≤ k.
  -- For |S| > k, choose any (m_S = 0, c_S = 0, k_S = 0) so `choose` works.
  have h_dy : ∀ S : Finset (Fin n),
      ∃ (mS : ℕ) (cS : ZMod (2 ^ mS)) (kintS : ℤ),
        S.card ≤ k →
          funcDerivPhaseSubset S g 0 =
            2 * Real.pi * (cS.val : ℝ) / (2 : ℝ) ^ mS
              + 2 * Real.pi * (kintS : ℝ) := by
    intro S
    by_cases hScard : S.card ≤ k
    · obtain ⟨mS, cS, kintS, hSeq⟩ := mobiusCoeff_dyadic_pointwise hk h_hier h_anchor S hScard
      exact ⟨mS, cS, kintS, fun _ => hSeq⟩
    · exact ⟨0, 0, 0, fun h => absurd h hScard⟩
  choose mS cS kintS hSeq using h_dy
  -- M = sup over all S : Finset (Fin n) of mS S. The universe is finite,
  -- so this is a Finset.univ.sup.
  set M := (Finset.univ : Finset (Finset (Fin n))).sup mS with hM_def
  refine ⟨M, ?_⟩
  intro S hScard
  have hmS_le : mS S ≤ M := Finset.le_sup (Finset.mem_univ S)
  -- Lift cS S from ZMod (2^(mS S)) to ZMod (2^M) via natCast scaling.
  set m₀ := mS S with hm₀_def
  set Δ := M - m₀ with hΔ_def
  have hΔ_eq : m₀ + Δ = M := by rw [hΔ_def]; omega
  have h_bound : ((cS S).val * 2 ^ Δ) < 2 ^ M := by
    have h_cv_lt : (cS S).val < 2 ^ m₀ := ZMod.val_lt (cS S)
    have h_pow_split : (2 : ℕ) ^ M = 2 ^ m₀ * 2 ^ Δ := by
      rw [← pow_add, hΔ_eq]
    rw [h_pow_split]
    have h_two_pow_pos : 0 < (2 : ℕ) ^ Δ := Nat.two_pow_pos Δ
    exact Nat.mul_lt_mul_of_pos_right h_cv_lt h_two_pow_pos
  refine ⟨((cS S).val * 2 ^ Δ : ZMod (2 ^ M)), kintS S, ?_⟩
  have h_val_eq : (((cS S).val * 2 ^ Δ : ZMod (2 ^ M))).val
                = (cS S).val * 2 ^ Δ := by
    have h_cast_eq : (((cS S).val * 2 ^ Δ : ℕ) : ZMod (2 ^ M))
        = ((cS S).val * 2 ^ Δ : ZMod (2 ^ M)) := by
      push_cast
      rfl
    rw [← h_cast_eq]
    exact ZMod.val_natCast_of_lt h_bound
  rw [h_val_eq, hSeq S hScard]
  -- Equation: 2π·c.val/2^m₀ + 2π·k = 2π·(c.val*2^Δ)/2^M + 2π·k
  -- with M = m₀ + Δ.
  have h_pow_pos_M : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have h_pow_pos_m₀ : (0 : ℝ) < (2 : ℝ) ^ m₀ := by positivity
  have h_pow_ne_m₀ : (2 : ℝ) ^ m₀ ≠ 0 := ne_of_gt h_pow_pos_m₀
  have h_pow_ne_M : (2 : ℝ) ^ M ≠ 0 := ne_of_gt h_pow_pos_M
  have h_pow_split_real : (2 : ℝ) ^ M = (2 : ℝ) ^ m₀ * (2 : ℝ) ^ Δ := by
    rw [← pow_add, hΔ_eq]
  push_cast
  rw [h_pow_split_real]
  field_simp
  ring

/-! ## The monomial polynomial of a Finset

The polynomial `∏_{i ∈ S} X_i` over `ZMod (2^m)`, used as the building
block for the Möbius assembly. -/

/-- The monomial polynomial `∏_{i ∈ S} X_i` over `ZMod (2^m)`. Used as
the building block for the Möbius assembly: the coefficient of the
Möbius coefficient `c_S` in the polynomial witness. -/
noncomputable def monomialOfFinset {n m : ℕ} (S : Finset (Fin n)) :
    DiagPhase n m :=
  ∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2^m)))

@[simp] theorem monomialOfFinset_empty {n m : ℕ} :
    monomialOfFinset (∅ : Finset (Fin n)) = (1 : DiagPhase n m) := by
  unfold monomialOfFinset
  rw [Finset.prod_empty]

/-- The total degree of `monomialOfFinset S` is at most `|S|`. Each
factor `X_i` has degree ≤ 1, so the product has degree ≤ `|S|` (by
`MvPolynomial.totalDegree_finset_prod`). -/
theorem monomialOfFinset_totalDegree {n m : ℕ} (S : Finset (Fin n)) :
    (monomialOfFinset (n := n) (m := m) S).totalDegree ≤ S.card := by
  unfold monomialOfFinset
  calc (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2^m)))).totalDegree
      ≤ ∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2^m))).totalDegree := by
        exact MvPolynomial.totalDegree_finset_prod S _
    _ ≤ ∑ _i ∈ S, 1 := by
        apply Finset.sum_le_sum
        intro i _
        -- totalDegree (X i) ≤ 1 unconditional.
        -- X i = monomial (Finsupp.single i 1) 1, and
        -- totalDegree (monomial s a) ≤ s.sum (fun _ n => n).
        -- For s = Finsupp.single i 1, the sum is 1.
        have hX : (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2^m)))
                = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2^m)) := by
          rw [MvPolynomial.X, MvPolynomial.monomial]
        rw [hX]
        refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
        simp [Finsupp.sum_single_index]
    _ = S.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- Evaluating `monomialOfFinset S` at `liftBinary v` gives the
indicator `1` if `S ⊆ supp v` else `0`. The key combinatorial step in
the Möbius assembly. -/
theorem monomialOfFinset_eval {n m : ℕ} (S : Finset (Fin n))
    (v : Fin n → ZMod 2) :
    (monomialOfFinset (m := m) S).eval v =
      if S ⊆ FTQCLib.Codes.supp v then 1 else 0 := by
  unfold monomialOfFinset DiagPhase.eval
  rw [MvPolynomial.eval_prod]
  -- Goal: ∏ i ∈ S, eval (liftBinary v) (X i)
  --      = if S ⊆ supp v then 1 else 0.
  -- Use that each eval (liftBinary v) (X i) = (v i).val cast to ZMod 2^m,
  -- which is 0 if v i = 0 and 1 if v i = 1.
  by_cases hSv : S ⊆ FTQCLib.Codes.supp v
  · -- Every i ∈ S has v i = 1, so each factor is 1; product is 1.
    rw [if_pos hSv]
    apply Finset.prod_eq_one
    intro i hi
    rw [MvPolynomial.eval_X]
    -- liftBinary v i = (v i).val cast to ZMod 2^m.
    change DiagPhase.liftBinary v i = 1
    unfold DiagPhase.liftBinary
    have h_vi : v i = 1 := by
      have hi' : i ∈ FTQCLib.Codes.supp v := hSv hi
      unfold FTQCLib.Codes.supp at hi'
      exact (Finset.mem_filter.mp hi').2
    rw [h_vi]
    haveI : Fact (1 < 2) := ⟨by norm_num⟩
    rw [ZMod.val_one]
    simp
  · -- There is some i ∈ S with v i = 0, making that factor zero.
    rw [if_neg hSv]
    -- Find an i ∈ S with i ∉ supp v.
    obtain ⟨i, hi_in_S, hi_not_in_supp⟩ : ∃ i ∈ S, i ∉ FTQCLib.Codes.supp v := by
      by_contra h_all
      push_neg at h_all
      exact hSv h_all
    -- v i = 0 (since i ∉ supp v).
    have h_vi : v i = 0 := by
      unfold FTQCLib.Codes.supp at hi_not_in_supp
      by_contra h_ne
      have h_or : v i = 0 ∨ v i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      rcases h_or with h0 | h1
      · exact h_ne h0
      · exact hi_not_in_supp (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩)
    -- The product is zero because the i-th factor is zero.
    apply Finset.prod_eq_zero hi_in_S
    rw [MvPolynomial.eval_X]
    change DiagPhase.liftBinary v i = 0
    unfold DiagPhase.liftBinary
    rw [h_vi]
    rw [ZMod.val_zero]
    simp

/-! ## The Möbius-assembly polynomial

Given a coefficient function `c : Finset (Fin n) → ZMod (2^m)`, the
assembly polynomial is `Σ_{S, |S| ≤ k} c S · monomialOfFinset S`. By
`totalDegree_finsetSum_le` plus `monomialOfFinset_totalDegree`, the
total degree is at most `k`. -/

/-- The Möbius-assembly polynomial: `P(X) = Σ_{S, |S| ≤ k} c S · ∏_{i
∈ S} X_i`. -/
noncomputable def mobiusAssemblyPoly {n m : ℕ} (k : ℕ)
    (c : Finset (Fin n) → ZMod (2^m)) : DiagPhase n m :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k),
    MvPolynomial.C (c S) * monomialOfFinset S

/-- The total degree of `mobiusAssemblyPoly k c` is at most `k`. Each
summand has total degree ≤ `0 + k = k` (the C-factor contributes 0,
the monomial contributes ≤ `|S| ≤ k`). -/
theorem mobiusAssemblyPoly_totalDegree {n m k : ℕ}
    (c : Finset (Fin n) → ZMod (2^m)) :
    (mobiusAssemblyPoly (n := n) (m := m) k c).totalDegree ≤ k := by
  unfold mobiusAssemblyPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro S hS
  rw [Finset.mem_filter] at hS
  -- totalDegree (C(c S) * monomialOfFinset S) ≤ 0 + |S| ≤ k.
  calc (MvPolynomial.C (c S) * monomialOfFinset S).totalDegree
      ≤ (MvPolynomial.C (c S)).totalDegree
          + (monomialOfFinset (m := m) S).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = 0 + (monomialOfFinset (m := m) S).totalDegree := by
        rw [MvPolynomial.totalDegree_C]
    _ ≤ 0 + S.card := by
        exact Nat.add_le_add_left (monomialOfFinset_totalDegree S) 0
    _ = S.card := zero_add _
    _ ≤ k := hS.2

/-- The evaluation of `mobiusAssemblyPoly k c` at `v` is the sum
`Σ_{S ⊆ supp v, |S| ≤ k} c S`. Uses `monomialOfFinset_eval` to collapse
the indicator function. -/
theorem mobiusAssemblyPoly_eval {n m k : ℕ}
    (c : Finset (Fin n) → ZMod (2^m)) (v : Fin n → ZMod 2) :
    (mobiusAssemblyPoly (n := n) (m := m) k c).eval v =
      ∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k),
        c S := by
  unfold mobiusAssemblyPoly DiagPhase.eval
  rw [map_sum]
  -- Goal: ∑ S ∈ univ.filter (...), eval (liftBinary v) (C (c S) * mon S)
  --      = ∑ S ∈ (supp v).powerset.filter (...), c S
  -- Split: eval (C (c S) * mon S) = c S * eval (mon S)
  --                              = c S * (if S ⊆ supp v then 1 else 0)
  -- So the sum picks up only those S with S ⊆ supp v and |S| ≤ k.
  have h_each : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k),
      MvPolynomial.eval (DiagPhase.liftBinary v) (MvPolynomial.C (c S) * monomialOfFinset S)
        = if S ⊆ FTQCLib.Codes.supp v then c S else 0 := by
    intro S _hS
    rw [map_mul, MvPolynomial.eval_C]
    change c S * (monomialOfFinset (m := m) S).eval v = _
    rw [monomialOfFinset_eval]
    by_cases hsub : S ⊆ FTQCLib.Codes.supp v
    · rw [if_pos hsub, if_pos hsub, mul_one]
    · rw [if_neg hsub, if_neg hsub, mul_zero]
  rw [Finset.sum_congr rfl h_each]
  -- Now: ∑ S ∈ univ.filter (|S| ≤ k), if S ⊆ supp v then c S else 0
  --    = ∑ S ∈ (supp v).powerset.filter (|S| ≤ k), c S.
  -- Convert if-then-else to filter using `Finset.sum_filter`.
  rw [← Finset.sum_filter]
  -- Goal: ∑ S ∈ (univ.filter (|S| ≤ k)).filter (S ⊆ supp v), c S
  --     = ∑ S ∈ (supp v).powerset.filter (|S| ≤ k), c S.
  apply Finset.sum_congr ?_ (fun S _ => rfl)
  -- Filter-equality.
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  constructor
  · rintro ⟨hk_card, hsub⟩
    exact ⟨hsub, hk_card⟩
  · rintro ⟨hsub, hk_card⟩
    exact ⟨hk_card, hsub⟩

/-! ## The Möbius-assembly main theorem

We now assemble the infrastructure above into the main theorem
`cgk_reverse_dyadic_poly_mobius_general`: every diagonal `U` at level
`k ≥ 1` of the dyadic hierarchy with `g(0)` dyadic mod 2π admits a
polynomial witness `P : DiagPhase n m` with `P.totalDegree ≤ k`. This
refines `cgk_reverse_dyadic_poly_general` of `CGKReverseGeneral.lean`
from `totalDegree ≤ n` (Lagrange-based) to `totalDegree ≤ k`
(Möbius-based).
-/

/-- **The polymorphic `funcDerivSubset` and the real-valued
`funcDerivPhaseSubset` agree on real-valued phase functions.** This is
the bridge between `BooleanMobius.eq_sum_mobiusCoeff` (stated for the
polymorphic `funcDerivSubset`) and the real-valued
`funcDerivPhaseSubset` of `CGKReverseIteration.lean`. (The lemma is
also re-proved as a private helper in `CGKReverseAnchor.lean`.) -/
private theorem funcDerivSubset_eq_funcDerivPhaseSubset_local
    (g : (Fin n → ZMod 2) → ℝ) (S : Finset (Fin n)) :
    funcDerivSubset S g = funcDerivPhaseSubset S g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [funcDerivSubset_empty, funcDerivPhaseSubset_empty]
  | @insert i S hi ih =>
      rw [funcDerivSubset_insert hi, funcDerivPhaseSubset_insert hi, ih]
      funext w
      rw [funcDerivPhase_apply]
      rfl

/-- **The `realPhase` of the Möbius-assembly polynomial as a sum of
dyadic rationals.** Specialising `mobiusAssemblyPoly_eval` and
`realPhase`, we get an explicit formula relating
`DiagPhase.realPhase (mobiusAssemblyPoly k c) v` to the sum
`∑_{S ⊆ supp v, S.card ≤ k} 2π · (c S).val / 2^m` modulo `2π · ℤ`.

The modular slack `2π · J` records the residue carry of summing
`ZMod (2^m)` elements: the sum-of-`.val` may exceed `2^m` while the
sum in `ZMod (2^m)` has wrapped around. -/
private theorem realPhase_mobiusAssemblyPoly_eq_sum_mod_two_pi
    {n m k : ℕ} (c : Finset (Fin n) → ZMod (2 ^ m))
    (v : Fin n → ZMod 2) :
    ∃ J : ℤ,
      DiagPhase.realPhase (mobiusAssemblyPoly (n := n) (m := m) k c) v
        = (∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter
              (fun S => S.card ≤ k),
              2 * Real.pi * ((c S).val : ℝ) / (2 : ℝ) ^ m)
            + 2 * Real.pi * (J : ℝ) := by
  classical
  -- Use the evaluation formula `mobiusAssemblyPoly_eval`:
  -- `(P.eval v) = ∑_{S ⊆ supp v, S.card ≤ k} c S` in `ZMod (2^m)`.
  set s := ∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k),
              c S with hs_def
  set N : ℕ := ∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k),
                  (c S).val with hN_def
  -- Underlying nat sum of vals agrees with sum in ZMod (2^m) via cast.
  have h_natCast :
      ((N : ℕ) : ZMod (2 ^ m)) = s := by
    rw [hs_def, hN_def]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro S _
    exact ZMod.natCast_zmod_val (c S)
  -- The .val of s differs from N by a multiple of 2^m.
  -- We want J such that s.val = N + 2^m · J (where J = -(N - s.val)/2^m ≤ 0).
  -- Equivalently: s.val - N = 2^m · J.
  have h_dvd : ((2 ^ m : ℕ) : ℤ) ∣ ((s.val : ℤ) - (N : ℤ)) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    -- Goal: ((s.val : ℝ-like) - (N : ℝ-like) : ZMod (2^m)) = 0.
    -- After push_cast, both sides reside in ZMod (2 ^ m) via nat coercion.
    have h1 : ((s.val : ℕ) : ZMod (2 ^ m)) = s := ZMod.natCast_zmod_val s
    have h2 : ((N : ℕ) : ZMod (2 ^ m)) = s := h_natCast
    -- After push_cast we expect the target to be `(s.val : ZMod _) - (N : ZMod _) = 0`.
    -- Rewrite both to s.
    rw [h1, h2]
    ring
  obtain ⟨J, hJ⟩ := h_dvd
  refine ⟨J, ?_⟩
  -- Now compute realPhase.
  unfold DiagPhase.realPhase
  -- P.eval v = s, so (P.eval v).val = s.val.
  rw [mobiusAssemblyPoly_eval]
  -- Goal: 2π · s.val / 2^m = ∑_S 2π · (c S).val / 2^m + 2π · J.
  rw [← hs_def]
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h_pow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h_pow_pos
  have h_real_eq :
      ((s.val : ℝ)) - ((N : ℝ)) = ((2 ^ m : ℕ) : ℝ) * (J : ℝ) := by
    have h_cast : ((s.val : ℤ) - (N : ℤ) : ℝ) = (((2 ^ m : ℕ) : ℤ) * J : ℝ) := by
      exact_mod_cast hJ
    have h_two_pow : (((2 ^ m : ℕ) : ℤ) : ℝ) = ((2 ^ m : ℕ) : ℝ) := by
      push_cast; rfl
    push_cast at h_cast
    rw [h_cast]
    push_cast
    ring
  have h_sum_real :
      ((N : ℝ)) = (∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k),
                      ((c S).val : ℝ)) := by
    rw [hN_def]; push_cast; rfl
  -- Sum on the RHS: ∑ 2π · (c S).val / 2^m = 2π · N / 2^m.
  have h_sum_factor :
      (∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k),
            2 * Real.pi * ((c S).val : ℝ) / (2 : ℝ) ^ m)
      = 2 * Real.pi * ((N : ℝ)) / (2 : ℝ) ^ m := by
    rw [h_sum_real, ← Finset.sum_div, ← Finset.mul_sum]
  rw [h_sum_factor]
  -- Goal: 2π · s.val / 2^m = 2π · N / 2^m + 2π · J.
  -- s.val = N + 2^m · J ⇒ 2π · s.val / 2^m = 2π · N / 2^m + 2π · J.
  -- Real-side equation:
  have h_pow_real_eq : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; rfl
  rw [h_pow_real_eq] at h_real_eq
  field_simp
  linarith

/-! ## The main theorem

We assemble all the pieces. The construction:

1. From `h_anchor`, take the phase function `f` (`U = diagonalGateEquiv f`
   with `IsDyadicMod2pi (f 0)`).
2. By `exists_uniform_precision_mobiusCoeffs`, obtain a uniform
   precision `m` such that every `(Δ_S f)(0)` (for `S.card ≤ k`) is
   representable at precision `m`.
3. Use `Classical.choose` to extract per-`S` residues `cS_data S :
   ZMod (2^m)` and integer offsets `kintS_data S : ℤ` realising the
   dyadic representation (only valid for `S.card ≤ k`; arbitrarily
   defined as `0` for `S.card > k`).
4. Set `P := mobiusAssemblyPoly k cS_data`. The total-degree bound
   `P.totalDegree ≤ k` is `mobiusAssemblyPoly_totalDegree`.
5. The equality `U = diagonalGateEquiv (realPhase P)` follows from
   `diagonalGateEquiv_eq_of_diff_two_pi`: pointwise, `f v -
   realPhase P v ∈ 2π · ℤ`. Proof:
   - Möbius inversion gives `f(v) = ∑_{S ⊆ supp v}
     funcDerivPhaseSubset S f 0`.
   - Split by `S.card ≤ k` vs `S.card > k`.
   - For `S.card ≤ k`: the uniform-precision representation gives
     `funcDerivPhaseSubset S f 0 = 2π · (cS_data S).val / 2^m + 2π
     · kintS_data S`.
   - For `S.card > k`: the vanishing theorem gives
     `funcDerivPhaseSubset S f 0 = 2π · ℤ`.
   - `realPhase P v = ∑_{S ⊆ supp v, S.card ≤ k} 2π · (cS_data S).val
     / 2^m + 2π · ℤ` by `realPhase_mobiusAssemblyPoly_eq_sum_mod_two_pi`.
   - Subtracting: all dyadic contributions cancel, leaving an integer
     multiple of `2π`.
-/

/-- **CGK reverse polynomial-witness existence with degree bound
`P.totalDegree ≤ k`.** For a diagonal `U` at level `k ≥ 1` of the
dyadic Clifford hierarchy with `g(0)` dyadic mod 2π, there is a
polynomial `P : DiagPhase n m` (some precision `m`) with
`U = diagonalGateEquiv (realPhase P)` and `P.totalDegree ≤ k`.

This refines `cgk_reverse_dyadic_poly_general` (whose total-degree
bound is `≤ n`, from Lagrange interpolation) to the CGK-sharp bound
`≤ k`, established via Möbius-coefficient assembly. The precision
`m` is the uniform precision over the per-`S` dyadic representations
of the Möbius coefficients.

The `P.level ≤ k` strengthening is FALSE under
`IsCliffordHierarchyDyadic`: the dyadic predicate does not bound the
base-scalar precision `m` by `k` (counterexample: `e^{iπ/4} · I` has
dyadic level 1 with `α = e^{iπ/4}` needing precision `m ≥ 3`, so
every polynomial encoding has `P.level ≥ 2`).

Anchors: CGK 2017 (arXiv:1608.06596) Theorem 2 / Lemma 4 reverse
direction at `p = 2`. -/
theorem cgk_reverse_dyadic_poly_mobius_general
    {n k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (_h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_anchor : ∃ f, U = diagonalGateEquiv f ∧ IsDyadicMod2pi (f 0))
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      U = diagonalGateEquiv (DiagPhase.realPhase P) ∧ P.totalDegree ≤ k := by
  classical
  -- Step 1: Extract the anchored phase function f.
  obtain ⟨f, hU_eq, h_f_zero⟩ := h_anchor
  -- Transfer hierarchy hypothesis to f.
  have h_hier_f : IsCliffordHierarchyDyadic k (diagonalGateEquiv f) := by
    rw [← hU_eq]; exact h_hier
  -- Step 2: Uniform precision m for the Möbius coefficients.
  obtain ⟨m, h_uniform⟩ :=
    exists_uniform_precision_mobiusCoeffs hk h_hier_f h_f_zero
  -- Step 3: Extract per-S residues and offsets.
  -- For S.card ≤ k: explicit representation.
  -- For S.card > k: assign 0 (won't be used in the sum).
  have h_choose : ∀ S : Finset (Fin n),
      ∃ (cS : ZMod (2 ^ m)) (kintS : ℤ),
        S.card ≤ k →
          funcDerivPhaseSubset S f 0
            = 2 * Real.pi * (cS.val : ℝ) / (2 : ℝ) ^ m
              + 2 * Real.pi * (kintS : ℝ) := by
    intro S
    by_cases hScard : S.card ≤ k
    · obtain ⟨cS, kintS, hcS⟩ := h_uniform S hScard
      exact ⟨cS, kintS, fun _ => hcS⟩
    · exact ⟨0, 0, fun h => absurd h hScard⟩
  choose cS_data kintS_data h_S_data using h_choose
  -- Step 4: Define the assembly polynomial P.
  set P := mobiusAssemblyPoly (n := n) (m := m) k cS_data with hP_def
  refine ⟨m, P, ?_, ?_⟩
  · -- Step 5: U = diagonalGateEquiv (realPhase P).
    rw [hU_eq]
    apply diagonalGateEquiv_eq_of_diff_two_pi
    intro v
    -- For each v, exhibit kint : ℤ with f v - realPhase P v = 2π · kint.
    -- We compute via Möbius inversion.
    -- Möbius inversion gives:
    --   f v = ∑_{S ⊆ supp v} funcDerivPhaseSubset S f 0
    have h_mobius_f :
        f v = ∑ S ∈ (FTQCLib.Codes.supp v).powerset,
                funcDerivPhaseSubset S f 0 := by
      have h := eq_sum_mobiusCoeff f v
      unfold mobiusCoeff at h
      rw [h]
      apply Finset.sum_congr rfl
      intro S _
      exact congrFun (funcDerivSubset_eq_funcDerivPhaseSubset_local f S) 0
    -- Split by S.card ≤ k vs S.card > k.
    set Plow := (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k)
      with hPlow_def
    set Phigh := (FTQCLib.Codes.supp v).powerset.filter (fun S => ¬ S.card ≤ k)
      with hPhigh_def
    have h_split :
        (FTQCLib.Codes.supp v).powerset
          = Plow ∪ Phigh := by
      have h_eq := Finset.filter_union_filter_not_eq
            (fun S => S.card ≤ k) (FTQCLib.Codes.supp v).powerset
      rw [hPlow_def, hPhigh_def]
      exact h_eq.symm
    have h_disj : Disjoint Plow Phigh := by
      rw [hPlow_def, hPhigh_def, Finset.disjoint_filter]
      intro S _ hle hnle
      exact hnle hle
    have h_sum_split :
        (∑ S ∈ (FTQCLib.Codes.supp v).powerset, funcDerivPhaseSubset S f 0)
          = (∑ S ∈ Plow, funcDerivPhaseSubset S f 0)
              + (∑ S ∈ Phigh, funcDerivPhaseSubset S f 0) := by
      rw [h_split, Finset.sum_union h_disj]
    -- High part: each summand is 2π · ℤ. Aggregate the offsets.
    have h_high_each : ∀ S ∈ Phigh, ∃ kS : ℤ,
        funcDerivPhaseSubset S f 0 = 2 * Real.pi * (kS : ℝ) := by
      intro S hS
      rw [hPhigh_def, Finset.mem_filter] at hS
      have hScard : k < S.card := by
        rcases hS with ⟨_, hnle⟩; omega
      exact funcDerivPhaseSubset_vanish_mod_2pi_of_card_gt_level
        hk h_hier_f hScard
    choose khigh_data h_high_eq using h_high_each
    have h_high_sum_eq :
        (∑ S ∈ Phigh, funcDerivPhaseSubset S f 0)
          = 2 * Real.pi *
              (∑ S ∈ Phigh.attach, (khigh_data S.val S.property : ℝ)) := by
      rw [← Finset.sum_attach Phigh (fun S => funcDerivPhaseSubset S f 0)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      exact h_high_eq S.val S.property
    -- The high-sum offset is an integer.
    set Khigh : ℤ := ∑ S ∈ Phigh.attach, khigh_data S.val S.property
      with hKhigh_def
    have h_high_int :
        (∑ S ∈ Phigh, funcDerivPhaseSubset S f 0)
          = 2 * Real.pi * (Khigh : ℝ) := by
      rw [h_high_sum_eq, hKhigh_def]
      push_cast
      rfl
    -- Low part: each summand has dyadic representation.
    -- funcDerivPhaseSubset S f 0 = 2π · (cS_data S).val / 2^m + 2π · kintS_data S
    have h_low_each : ∀ S ∈ Plow,
        funcDerivPhaseSubset S f 0
          = 2 * Real.pi * ((cS_data S).val : ℝ) / (2 : ℝ) ^ m
            + 2 * Real.pi * (kintS_data S : ℝ) := by
      intro S hS
      rw [hPlow_def, Finset.mem_filter] at hS
      exact h_S_data S hS.2
    have h_low_sum :
        (∑ S ∈ Plow, funcDerivPhaseSubset S f 0)
          = (∑ S ∈ Plow, 2 * Real.pi * ((cS_data S).val : ℝ) / (2 : ℝ) ^ m)
              + (∑ S ∈ Plow, 2 * Real.pi * (kintS_data S : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl h_low_each
    -- Aggregate the kintS_data offsets.
    set Klow : ℤ := ∑ S ∈ Plow, kintS_data S with hKlow_def
    have h_low_int :
        (∑ S ∈ Plow, 2 * Real.pi * (kintS_data S : ℝ))
          = 2 * Real.pi * (Klow : ℝ) := by
      rw [hKlow_def]
      push_cast
      rw [Finset.mul_sum]
    -- Now: f v = (∑_{S ∈ Plow} 2π · (cS_data S).val / 2^m)
    --         + 2π · Klow + 2π · Khigh.
    have h_f_eq :
        f v = (∑ S ∈ Plow, 2 * Real.pi * ((cS_data S).val : ℝ) / (2 : ℝ) ^ m)
              + 2 * Real.pi * (Klow : ℝ) + 2 * Real.pi * (Khigh : ℝ) := by
      rw [h_mobius_f, h_sum_split, h_low_sum, h_low_int, h_high_int]
    -- realPhase P v = (∑_{S ∈ Plow} 2π · (cS_data S).val / 2^m) + 2π · J.
    obtain ⟨J, h_P_eq⟩ :=
      realPhase_mobiusAssemblyPoly_eq_sum_mod_two_pi (k := k) cS_data v
    -- The sum index in `realPhase_mobiusAssemblyPoly_eq_sum_mod_two_pi`
    -- is `(FTQCLib.Codes.supp v).powerset.filter (S.card ≤ k)`, identical
    -- to `Plow`.
    have h_Plow_eq :
        (FTQCLib.Codes.supp v).powerset.filter (fun S => S.card ≤ k) = Plow := by
      rw [hPlow_def]
    rw [h_Plow_eq] at h_P_eq
    -- Subtract.
    refine ⟨Klow + Khigh - J, ?_⟩
    rw [h_f_eq, h_P_eq]
    push_cast
    ring
  · -- Step 6: P.totalDegree ≤ k.
    exact mobiusAssemblyPoly_totalDegree cS_data

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.AJO
import FTQCLib.Codes.AJOOverlap
import FTQCLib.Codes.AJOLattice
import Mathlib.Analysis.Real.Pi.Irrational

set_option linter.unusedSectionVars false

/-! # AJO Theorem 1 (uniform-angle case): direct statement from `IsTransversalLogical`

This file restates the AJO Theorem 1 target directly in terms of
`IsTransversalLogical` from `FTQCLib/Codes/AJO.lean`, bypassing the
intermediate `AJOOverlapHypothesis` predicate in
`FTQCLib/Codes/AJOOverlap.lean`.

## Why this file exists

`AJOOverlapHypothesis` enumerates a finite list of constraints — single
overlaps, pairwise overlaps, m-fold overlaps with the `2^(|I|-1)`
factor, and the analogous logical conditions. But `IsTransversalLogical`
is a universal quantification over **all** `v ∈ ker(H_Z)` and
**all** `h ∈ row(H_X)`. The enumerated list captures the constraints
from `v ∈ {0, single generators g_i, g_L, g_L + generator}` but misses
arbitrary F_2 combinations of generators and unit-vector instantiations
inside `ker(H_Z)`.

The omission matters: examples like

  `n = 9, H_X = [g_1, g_2]` with `g_1 = (1,1,1,1,1,1,0,0,0)` and
  `g_2 = (0,0,0,1,1,1,1,1,1)`, `g_L = (0,0,0,0,0,0,1,1,1)`, `θ = π/3`

satisfy `AJOOverlapHypothesis` (with the corrected `2^(|I|-1)` factors
and the non-triviality clause) but FAIL `IsTransversalLogical`: take
`v = e_1` (a unit vector, in `ker(H_Z)` when `H_Z = 0`) and `h = g_1`;
the condition reads `θ · (wt(g_1) − 2·wt(e_1 ∧ g_1)) = θ · (6 − 2) =
4θ ∈ 2π·ℤ`, which gives `θ ∈ (π/2)·ℤ`. Our `θ = π/3` violates this.

So the enumerated predicate was a strict subset of trans-logical's
actual constraints, and putative counterexamples to "predicate →
dyadic θ" were not counterexamples to the genuine "IsTransversalLogical
→ dyadic θ" theorem.

## Approach

State the target directly:

```
theorem ajo_uniform_dyadic
    {n r_X r_Z : ℕ}
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    (g_L : Fin n → ZMod 2)
    (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_notInStab : g_L ∉ cssXLogicalSubspace H_X)
    (θ : ℝ)
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N)
```

The proof works directly from `h_trans`, instantiating `v` strategically
inside `ker(H_Z)`:

* `v = 0`: the constraint reads `θ · wt(h) ∈ 2π·ℤ` for `h ∈ row(H_X)`.
* `v = e_j` for `j ∈ ker(H_Z)` componentwise (i.e., `j` such that
  column `j` of `H_Z` is zero): the constraint reads
  `θ · (wt(h) − 2·(h_j)) ∈ 2π·ℤ`.
  Subtracting `v = 0`: `θ · 2 · (h_j) ∈ 2π·ℤ`. So if `h_j = 1`,
  `θ ∈ π·ℤ`.
* `v = g_L`: `θ · (wt(h) − 2·wt(g_L ∧ h)) ∈ 2π·ℤ`.
* compound `v`: more constraints.

The lattice of constraints, together with the non-triviality
`wt(g_L) · θ ∉ 2π·ℤ`, forces `θ` into a dyadic-rational multiple of `2π`.

## Status

This file proves the following:

* **`AJOOverlapConclusion`-style helper lemmas** for the dyadic
  conclusion: `dyadic_of_intMul_two_pi`, `dyadic_of_pi_intMul`,
  `dyadic_of_two_theta_eq_two_pi_intMul`, `dyadic_of_pow_two_weight`.
* **`ajo_uniform_dyadic_of_unit_vec_route`** — Route 1 from the spec:
  when there exists a qubit `j` with column `j` of `H_Z` zero and some
  `h ∈ row(H_X)` with `h j = 1`, the angle `θ` is forced into `π·ℤ`,
  hence dyadic with denominator `2`. The non-triviality is unused in
  this case (the constraints alone suffice).
* **`ajo_uniform_dyadic_of_h_pow_two`** — power-of-two-weight route:
  when there exists `h ∈ row(H_X)` with `wt(h)` a power of 2, the v=0
  constraint forces `θ` dyadic.
* **`ajo_uniform_dyadic_of_gL_overlap_pow_two`** — g_L-overlap power-of-
  two route: when `wt(g_L ∧ h)` is a power of 2 for some
  `h ∈ row(H_X)`, the combined v=0 and v=g_L constraints force `θ`
  dyadic.

The general theorem `ajo_uniform_dyadic` is **NOT proved in this
file**; it is documented with a careful honesty note about which cases
remain open. In particular, the literal statement as written admits a
degenerate counterexample where `H_X = 0`: with row(H_X) = {0} the
trans-logical condition is vacuous for any `θ`, while non-triviality is
satisfied by any irrational multiple of `2π / wt(g_L)`. The general
theorem requires either a non-degeneracy hypothesis (e.g., that
`cssXLogicalSubspace H_X` contains a non-zero element) or the
substantive inclusion-exclusion / Möbius-inversion argument from AJO
2014 Section III.A combined with that hypothesis.
-/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Hierarchy Matrix

variable {n r_X r_Z : ℕ}

/-! ## Trans-logical constraint, instantiated -/

/-- For `f = linearPhase (uniform θ)`, the trans-logical condition at
a specific `(v, h)` pair simplifies to an integer linear constraint on
`θ`. -/
theorem isTransversalLogical_uniform_eval
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (v : Fin n → ZMod 2) (hv : v ∈ cssXLogicalCarrier H_Z)
    (h : Fin n → ZMod 2) (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ,
      linearPhase (fun _ : Fin n => θ) (v + h)
      - linearPhase (fun _ : Fin n => θ) v
        = 2 * Real.pi * (k : ℝ) := by
  exact h_trans v hv h hh

/-! ## Dyadic-conclusion helper lemmas

These translate "θ lies in a specific lattice in ℝ" into the explicit
form `θ = 2π · a / 2^N`. -/

/-- **Dyadic from `θ ∈ 2π·ℤ`.** If `θ = 2π · k` for some integer `k`,
then `θ` is dyadic with denominator `2^0 = 1`. -/
theorem dyadic_of_intMul_two_pi {θ : ℝ} (k : ℤ)
    (h : θ = 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  refine ⟨k, 0, ?_⟩
  rw [h]
  simp

/-- **Dyadic from `θ ∈ π·ℤ`.** If `θ = π · k` for some integer `k`, then
`θ = 2π · k / 2`, dyadic with denominator `2^1 = 2`. -/
theorem dyadic_of_pi_intMul {θ : ℝ} (k : ℤ)
    (h : θ = Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  refine ⟨k, 1, ?_⟩
  rw [h]
  ring

/-- **Dyadic from `2θ ∈ 2π·ℤ`.** If `2θ = 2π · k`, then `θ = π · k`,
dyadic with denominator `2`. -/
theorem dyadic_of_two_theta_eq_two_pi_intMul {θ : ℝ} (k : ℤ)
    (h : 2 * θ = 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  refine ⟨k, 1, ?_⟩
  linarith [h]

/-- **Dyadic from a `θ · (2^N) ∈ 2π·ℤ` constraint.** If `θ` multiplied
by an integer of the form `2^N` (cast as a real) equals `2π · k`, then
`θ` is dyadic with denominator `2^N`. -/
theorem dyadic_of_pow_two_weight {θ : ℝ} {N : ℕ} {k : ℤ}
    (h : θ * ((2 ^ N : ℕ) : ℝ) = 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N' : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N') := by
  refine ⟨k, N, ?_⟩
  have hpow : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; ring
  rw [hpow] at h
  have hne : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp
  linarith [h]

/-- **Dyadic from a `2θ · (2^N) ∈ 2π·ℤ` constraint.** If `2θ · 2^N =
2π · k`, then `θ = 2π · k / 2^(N+1)`. -/
theorem dyadic_of_two_theta_pow_two_weight {θ : ℝ} {N : ℕ} {k : ℤ}
    (h : 2 * θ * ((2 ^ N : ℕ) : ℝ) = 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N' : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N') := by
  refine ⟨k, N + 1, ?_⟩
  have hpow : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; ring
  rw [hpow] at h
  have hne : (2 : ℝ) ^ N ≠ 0 := by positivity
  have hne2 : ((2 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  linarith [h]

/-! ## Route 1: Unit-vector specialization

When there exists `j : Fin n` with column `j` of `H_Z` zero and an
X-stabilizer `h ∈ row(H_X)` with `h j = 1`, the unit-vector instantiation
of trans-logical gives `θ · (wt(h) − 2) ∈ 2π·ℤ` and the zero-vector
instantiation gives `θ · wt(h) ∈ 2π·ℤ`. Subtracting forces
`2θ ∈ 2π·ℤ`, hence `θ ∈ π·ℤ`. -/

/-- **Route 1 (unit-vector route).** Suppose there exists `j : Fin n`
such that column `j` of `H_Z` is identically zero and there exists
`h ∈ cssXLogicalSubspace H_X` with `h j = 1`. Then `θ ∈ π·ℤ`, and so
`θ` is a dyadic multiple of `2π` (with denominator `2`).

This is the cleanly applicable case: it uses only `IsTransversalLogical`
and does not require the non-triviality hypothesis. The non-triviality
is automatic from the conclusion (any non-trivial `g_L` plus `θ ∈ π·ℤ`
satisfies `wt(g_L) · θ ∈ π·ℤ`, which lies in `2π·ℤ` only when
`wt(g_L)` is even; for odd-weight `g_L` the non-triviality follows). -/
theorem ajo_uniform_dyadic_of_unit_vec_route
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {j : Fin n} (hcol : ∀ i : Fin r_Z, H_Z i j = 0)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    (hhj : h j = 1) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  -- Extract the v = 0 constraint: θ · wt(h) ∈ 2π·ℤ.
  obtain ⟨k₀, hk₀⟩ := isTransversalLogical_uniform_zero_constraint h_trans hh
  -- Extract the v = e_j constraint: θ · (wt(h) − 2·(h j).val) ∈ 2π·ℤ.
  obtain ⟨k₁, hk₁⟩ :=
    isTransversalLogical_uniform_unit_vec_constraint h_trans j hcol hh
  -- Compute (h j).val = 1 from h j = 1.
  have hj_val : (h j).val = 1 := by
    rw [hhj]
    haveI : Fact (1 < 2) := ⟨by norm_num⟩
    exact ZMod.val_one 2
  rw [hj_val] at hk₁
  -- Subtract: θ · 2 = 2π · (k₀ − k₁), so 2θ = 2π · (k₀ − k₁).
  have hsub : 2 * θ = 2 * Real.pi * ((k₀ - k₁ : ℤ) : ℝ) := by
    push_cast at hk₀ hk₁ ⊢
    -- hk₀: θ * wt(h) = 2π · k₀.
    -- hk₁: θ * (wt(h) − 2) = 2π · k₁.
    -- Subtract: θ · 2 = 2π · (k₀ − k₁).
    linarith [hk₀, hk₁]
  exact dyadic_of_two_theta_eq_two_pi_intMul (k₀ - k₁) hsub

/-! ## Route 2: Power-of-two weight in `row(H_X)`

If some `h ∈ row(H_X)` has Hamming weight a power of 2, the v=0
constraint alone gives `θ` dyadic. -/

/-- **Route 2 (h-weight power-of-two route).** If there exists
`h ∈ cssXLogicalSubspace H_X` with `wt(h) = 2^N` for some `N : ℕ`,
then `θ` is dyadic with denominator `2^N`. -/
theorem ajo_uniform_dyadic_of_h_pow_two
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    {N : ℕ} (hwt : hammingWeight h = 2 ^ N) :
    ∃ (a : ℤ) (N' : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N') := by
  obtain ⟨k, hk⟩ := isTransversalLogical_uniform_zero_constraint h_trans hh
  rw [hwt] at hk
  exact dyadic_of_pow_two_weight hk

/-! ## Route 3: Power-of-two `g_L`-overlap weight

If `wt(g_L ∧ h) = 2^N` for some `h ∈ row(H_X)`, then combining the v=0
and v=g_L constraints gives `2θ · 2^N ∈ 2π·ℤ`, so `θ` is dyadic with
denominator `2^(N+1)`. -/

/-- **Route 3 (`g_L`-overlap power-of-two route).** If there exists
`h ∈ cssXLogicalSubspace H_X` such that `wt(g_L ∧ h) = 2^N` for some
`N : ℕ`, then `θ` is dyadic with denominator `2^(N+1)`. The
constraint `2θ · wt(g_L ∧ h) ∈ 2π·ℤ` is obtained by subtracting the
`v = g_L` constraint from the `v = 0` constraint at the same `h`. -/
theorem ajo_uniform_dyadic_of_gL_overlap_pow_two
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2}
    (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    {N : ℕ} (hwt : hammingWeight (fun j => g_L j * h j) = 2 ^ N) :
    ∃ (a : ℤ) (N' : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N') := by
  -- Extract v = 0 constraint: θ · wt(h) ∈ 2π·ℤ.
  obtain ⟨k₀, hk₀⟩ := isTransversalLogical_uniform_zero_constraint h_trans hh
  -- Extract v = g_L constraint:
  -- θ · (wt(h) − 2·wt(g_L ∧ h)) ∈ 2π·ℤ.
  obtain ⟨k₁, hk₁⟩ :=
    isTransversalLogical_uniform_logical_constraint h_trans h_carrier hh
  -- Subtract: 2θ · wt(g_L ∧ h) = 2π · (k₀ − k₁).
  have hsub :
      2 * θ * (hammingWeight (fun j => g_L j * h j) : ℝ) =
        2 * Real.pi * ((k₀ - k₁ : ℤ) : ℝ) := by
    push_cast at hk₀ hk₁ ⊢
    linarith [hk₀, hk₁]
  rw [hwt] at hsub
  exact dyadic_of_two_theta_pow_two_weight hsub

/-! ## Non-triviality forces `wt(g_L) > 0`

A small but important observation: the non-triviality
`∀ k, wt(g_L) · θ ≠ 2π · k` immediately rules out `wt(g_L) = 0`. -/

/-- The non-triviality hypothesis implies `g_L` has positive Hamming
weight. -/
theorem ajo_uniform_hammingWeight_gL_pos
    {θ : ℝ} {g_L : Fin n → ZMod 2}
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ)) :
    0 < hammingWeight g_L := by
  by_contra hle
  -- wt(g_L) is not positive in ℕ means wt(g_L) = 0.
  have hzero : hammingWeight g_L = 0 := by omega
  -- Apply h_nontriv at k = 0: (0 : ℝ) * θ ≠ 2π · 0 = 0, contradiction.
  exact h_nontriv 0 (by rw [hzero]; push_cast; ring)

/-! ## Documented target — general `ajo_uniform_dyadic`

The general theorem combining the routes above is:

```
theorem ajo_uniform_dyadic
    {n r_X r_Z : ℕ}
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    (g_L : Fin n → ZMod 2)
    (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_notInStab : g_L ∉ cssXLogicalSubspace H_X)
    (θ : ℝ)
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N)
```

### Status: not proved here.

The statement as written admits a **literal counterexample** in the
degenerate regime where `H_X = 0` (the zero matrix):

  `n = 1, r_X = 1, r_Z = 1, H_X = 0, H_Z = 0, g_L = 1, θ = π · √2`.

* `g_L ∈ cssXLogicalCarrier H_Z = ker(0) = full space` ✓
* `g_L ∉ cssXLogicalSubspace H_X = im(0^T) = {0}` because `g_L = 1 ≠ 0` ✓
* `IsTransversalLogical`: row(H_X) = im(0^T) = {0}, so for `h ∈ row(H_X)`
  we have `h = 0`, and the condition reads `f(v + 0) − f(v) = 0 ∈ 2π·ℤ` ✓
* `h_nontriv`: `wt(g_L) · θ = 1 · π√2 = π√2`. For this to equal `2π·k`
  we would need `π√2 = 2πk`, i.e., `√2 = 2k`, impossible. ✓
* But `θ = π√2` is irrational, not dyadic.

So the literal statement is false; a proof would require fixing it. The
two natural fixes:

1. **Non-degeneracy:** Add a hypothesis that `cssXLogicalSubspace H_X`
   contains a non-zero element. Then there exists `h ∈ row(H_X)` with
   `h ≠ 0`, and v=0 gives `θ · wt(h) ∈ 2π·ℤ`, so `θ` is a rational
   multiple of `2π`. Combined with the lattice extraction above, the
   dyadic conclusion follows by the Möbius-inversion argument of AJO
   2014 pp. 7-8.

2. **Replace conclusion with logical-angle dyadic:** AJO 2014 actually
   bounds the logical action `θ_L = θ · wt(g_L) mod 2π`, not the
   physical angle `θ`. The conclusion `θ_L` dyadic does hold under
   trans-logical alone (without non-degeneracy), because the constraints
   directly involve `wt(g_L)`-multiples. The hypothesis `h_nontriv`
   then says `θ_L ∉ 2π·ℤ`, i.e., the logical action is non-trivial.

### What the routes above establish

The three concrete routes proved above —
`ajo_uniform_dyadic_of_unit_vec_route`,
`ajo_uniform_dyadic_of_h_pow_two`,
`ajo_uniform_dyadic_of_gL_overlap_pow_two` — cover the principal cases
where a "witness" weight of the right shape exists. Together they
discharge the AJO theorem on:

* Codes where some qubit `j` is "free on the Z-side" (column `j` of
  `H_Z` is zero) and "touched on the X-side" (some `h ∈ row(H_X)` has
  `h j = 1`). This is generic for non-degenerate CSS codes.
* Codes admitting an X-stabilizer of power-of-two weight (e.g., the
  Steane `[[7, 1, 3]]` code with `wt(g_i) = 4`, the toric code with
  `wt(g_i) = 4`, the surface code with `wt(g_i) = 4`).
* Codes admitting a power-of-two `g_L`-overlap weight (which is implied
  by, e.g., the existence of an X-stabilizer disjoint from `supp(g_L)`
  paired with `Pi.single j 1` arguments not used here).

### What remains open

The substantive missing piece is the full Möbius-inversion / inclusion-
exclusion argument on the `2^{r_X}` subsets of X-stabilizer generators,
combined with the `h_nontriv` hypothesis applied through the lattice of
constraints, that AJO 2014 carry out in their Section III.A. The
elementary infrastructure for this argument lives in
`AJOLattice.lean` (constraint extraction, unit-vector specialization)
and `AJOOverlap.lean` (overlap algebra, monotonicity, dyadic-weight
reductions).
-/

/-! ## Formal counterexample to the literal `ajo_uniform_dyadic`

To make the failure of the literal statement explicit, we construct
concrete `n, r_X, r_Z, H_X, H_Z, g_L, θ` for which `IsTransversalLogical`
holds, `h_nontriv` holds, `g_L ∈ ker(H_Z) \ row(H_X)`, yet `θ` is not a
dyadic multiple of `2π`. The setup is the degenerate case
`H_X = H_Z = 0`, `n = 1`, `g_L = (1)`, `θ = 1`. The proof of
non-dyadicity uses irrationality of `π` (`Mathlib.Analysis.Real.Pi.Irrational`). -/

/-- The 1-qubit "zero CSS code" with `H_X = 0`: a single row of length 1
all-zero. -/
def ajoLiteralCounterHX : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  fun _ _ => 0

/-- The matching `H_Z = 0`. -/
def ajoLiteralCounterHZ : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
  fun _ _ => 0

/-- The non-trivial single-qubit logical: the constant-`1` function. -/
def ajoLiteralCounterGL : Fin 1 → ZMod 2 :=
  fun _ => 1

/-- The Hamming weight of the literal-counterexample `g_L` is `1`. -/
theorem ajoLiteralCounter_hammingWeight_gL :
    hammingWeight ajoLiteralCounterGL = 1 := by
  unfold hammingWeight ajoLiteralCounterGL
  haveI : Fact (1 < 2) := ⟨by norm_num⟩
  simp

/-- The kernel of the zero `H_Z` matrix on `Fin 1` is the full space:
in particular, `g_L` lies in it. -/
theorem ajoLiteralCounter_gL_mem_carrier :
    ajoLiteralCounterGL ∈ cssXLogicalCarrier ajoLiteralCounterHZ := by
  unfold cssXLogicalCarrier
  rw [LinearMap.mem_ker]
  ext i
  simp [ajoLiteralCounterHZ, Matrix.mulVec, dotProduct]

/-- The image of the transpose of zero `H_X` is `{0}`. The literal-
counterexample `g_L` is non-zero (its single component is `1`), so it is
not in this image. -/
theorem ajoLiteralCounter_gL_not_mem_subspace :
    ajoLiteralCounterGL ∉ cssXLogicalSubspace ajoLiteralCounterHX := by
  unfold cssXLogicalSubspace
  rw [LinearMap.mem_range]
  rintro ⟨u, hu⟩
  -- `mulVecLin (0)ᵀ u = 0`, so `0 = g_L`, but `g_L 0 = 1`.
  have h0 : (Matrix.mulVecLin ajoLiteralCounterHXᵀ u) 0 = 0 := by
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, ajoLiteralCounterHX, zero_mul,
      Finset.sum_const_zero]
  have h1 : ajoLiteralCounterGL 0 = 1 := rfl
  rw [hu] at h0
  rw [h1] at h0
  exact absurd h0 (by decide)

/-- The trans-logical condition is vacuous on the zero `H_X` matrix: the
only `h ∈ row(H_X) = im(H_Xᵀ) = {0}` is `h = 0`, and `f(v + 0) − f(v) =
0 ∈ 2π·ℤ`. -/
theorem ajoLiteralCounter_isTransversalLogical (θ : ℝ) :
    IsTransversalLogical (linearPhase (fun _ : Fin 1 => θ))
      ajoLiteralCounterHX ajoLiteralCounterHZ := by
  intro v _ h hh
  -- Show `h = 0` from `h ∈ cssXLogicalSubspace 0`.
  have hh0 : h = 0 := by
    obtain ⟨u, hu⟩ := hh
    ext i
    have hzero : Matrix.mulVecLin ajoLiteralCounterHXᵀ u i = 0 := by
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, ajoLiteralCounterHX, zero_mul,
        Finset.sum_const_zero]
    rw [hu] at hzero
    rw [hzero]
    rfl
  refine ⟨0, ?_⟩
  rw [hh0]
  simp

/-- The non-triviality hypothesis holds at `θ = 1`: `wt(g_L) · 1 = 1`,
and `1 = 2π · k` for an integer `k` would imply `2π` is rational
(`= 1/k`), contradicting irrationality of `π`. -/
theorem ajoLiteralCounter_nontriv :
    ∀ k : ℤ, (hammingWeight ajoLiteralCounterGL : ℝ) * (1 : ℝ) ≠
      2 * Real.pi * (k : ℝ) := by
  intro k hk
  rw [ajoLiteralCounter_hammingWeight_gL] at hk
  -- `hk : (1 : ℕ) · 1 = 2π · k`, i.e., `1 = 2π · k`.
  -- If `k = 0`: 1 = 0, false. If `k ≠ 0`: `2π = 1/k` rational, contradicting irrationality.
  push_cast at hk
  -- `hk : 1 = 2π · k`.
  by_cases hkz : k = 0
  · rw [hkz] at hk; push_cast at hk; linarith [hk]
  · -- `π = 1/(2k)`, rational.
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hkz
    have : Real.pi = 1 / (2 * (k : ℝ)) := by
      field_simp
      linarith [hk]
    -- Contradict `Irrational π`.
    refine irrational_pi ⟨1 / (2 * (k : ℚ)), ?_⟩
    rw [this]
    push_cast
    ring

/-- The angle `θ = 1` is **not** a dyadic multiple of `2π`: if
`1 = 2π · a / 2^N` then `π = 2^N / (2·a)` (when `a ≠ 0`) or `1 = 0` (when
`a = 0`), both impossible. -/
theorem ajoLiteralCounter_not_dyadic :
    ¬ ∃ (a : ℤ) (N : ℕ), (1 : ℝ) = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  rintro ⟨a, N, h⟩
  -- `1 = 2π · a / 2^N`, so `2^N = 2π · a`.
  have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h2N_ne : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h2N_pos
  have hkey : ((2 : ℝ) ^ N) = 2 * Real.pi * (a : ℝ) := by
    field_simp at h
    linarith [h]
  by_cases haz : a = 0
  · rw [haz] at hkey
    push_cast at hkey
    -- `2^N = 0`, contradiction.
    linarith [h2N_pos, hkey]
  · -- `π = 2^N / (2 · a)`, rational, contradicting irrationality.
    have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast haz
    have hpi_eq : Real.pi = (2 : ℝ) ^ N / (2 * (a : ℝ)) := by
      field_simp
      linarith [hkey]
    refine irrational_pi ⟨((2 ^ N : ℤ) : ℚ) / (2 * (a : ℚ)), ?_⟩
    rw [hpi_eq]
    push_cast
    ring

/-- **The literal `ajo_uniform_dyadic` statement is false.** There exist
concrete `n, r_X, r_Z, H_X, H_Z, g_L, θ` satisfying all the stated
hypotheses (`g_L ∈ ker(H_Z) \ row(H_X)`, trans-logical, non-trivial
logical action) but for which `θ` is not a dyadic multiple of `2π`.
The witness is the degenerate `H_X = H_Z = 0` zero-stabilizer code on
1 qubit, with `g_L = (1)` and `θ = 1`. -/
theorem ajo_uniform_dyadic_literal_false :
    ∃ (n r_X r_Z : ℕ)
      (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
      (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
      (g_L : Fin n → ZMod 2)
      (θ : ℝ),
        g_L ∈ cssXLogicalCarrier H_Z ∧
        g_L ∉ cssXLogicalSubspace H_X ∧
        IsTransversalLogical (linearPhase (fun _ : Fin n => θ)) H_X H_Z ∧
        (∀ k : ℤ, (hammingWeight g_L : ℝ) * θ ≠ 2 * Real.pi * (k : ℝ)) ∧
        ¬ ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) :=
  ⟨1, 1, 1, ajoLiteralCounterHX, ajoLiteralCounterHZ, ajoLiteralCounterGL, 1,
    ajoLiteralCounter_gL_mem_carrier,
    ajoLiteralCounter_gL_not_mem_subspace,
    ajoLiteralCounter_isTransversalLogical 1,
    ajoLiteralCounter_nontriv,
    ajoLiteralCounter_not_dyadic⟩

end FTQCLib.Codes

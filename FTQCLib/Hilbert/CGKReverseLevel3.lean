/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseAnchor

set_option linter.unusedSectionVars false

/-! # CGK reverse — level-3 conditional closure

This file extends `CGKReverseAnchor.lean` to **level 3** of the dyadic
hierarchy, proving that the conditional

  `IsCliffordHierarchyDyadic 3 (D_g) → IsDyadicMod2pi (g 0) →
   ∀ v, IsDyadicMod2pi (g v)`

is **true** at level 3.

## The key identity

At level 3 with `g(0)` dyadic, the descent gives `D_{Δ_i g}` at level 2
for each `i`. To apply the level-2 conditional closure
(`isDyadicMod2pi_of_level_two_diagonal_anchored`), we need
`(Δ_i g)(0)` dyadic. Naively this seems circular because
`(Δ_i g)(0) = g(e_i) - g(0)` and we don't yet know `g(e_i)` dyadic.

The escape is a **mod-2 algebraic identity**. In `ZMod 2`,
`e_i + e_i = 0`, so

  `Δ_i Δ_i g (v) = [g(v + 2e_i) - g(v + e_i)] - [g(v + e_i) - g(v)]
                = [g(v) - g(v + e_i)] - [g(v + e_i) - g(v)]
                = -2 (g(v + e_i) - g(v))
                = -2 (Δ_i g)(v)`

as a function identity. So `Δ_i Δ_i g = (-2) • Δ_i g` (pointwise).

Now apply the level-2 Möbius coefficient closure
(`mobiusCoeff_dyadic_mod_2pi_level_two`) to `D_{Δ_i g}` at level 2,
with the **single-element subset** `{i}`. This gives
`(Δ_i (Δ_i g))(0)` dyadic mod 2π, i.e., `-2 (Δ_i g)(0)` dyadic mod 2π.

The final ingredient is the **halving lemma**: if `2 x` is dyadic mod
2π, then `x` is dyadic mod 2π (at one bit more precision). With this,
`(Δ_i g)(0)` dyadic mod 2π, level-2 anchored closure applies on
`D_{Δ_i g}`, and Möbius inversion delivers `g(v)` dyadic for every `v`.

## Files used

* `FTQCLib/Hilbert/CGKReverseAnchor.lean` — level-1, level-2 closures and
  `IsDyadicMod2pi` algebraic closures.
* `FTQCLib/Hilbert/CGKReverseDyadic.lean` — the descent theorem
  `diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`.

## Anchors

* CGK 2017 (arXiv:1608.06596) §III, Lemma 2 eq (50)–(51).
* Rota 1964 — Möbius inversion on the Boolean lattice.
* `isDyadicMod2pi_of_level_one_diagonal`, the descent theorem
  `diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`,
  `mobiusCoeff_dyadic_mod_2pi_level_two` and
  `isDyadicMod2pi_of_level_two_diagonal_anchored`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase BooleanMobius

variable {n : ℕ}

/-! ## Halving lemma for `IsDyadicMod2pi`

If `2 * x` is dyadic mod 2π at precision `m`, then `x` is dyadic mod 2π
at precision `m + 1`.

Sketch: from `2x = 2π · c.val / 2^m + 2π · k` (with `c : ZMod 2^m`,
`k : ℤ`), halving gives `x = 2π · c.val / 2^{m+1} + π · k`. Then
`π · k = 2π · (k mod 2) / 2 + 2π · (k / 2)`. Combine the `(k mod 2)`
half-shift with the `2^m` numerator at precision `m + 1`:

* If `k` is even (`k = 2j`): `x = 2π · c.val / 2^{m+1} + 2π · j`,
  witness `(m+1, c.val, j)`.
* If `k` is odd (`k = 2j + 1`): `x = 2π · (c.val + 2^m) / 2^{m+1} + 2π · j`,
  witness `(m+1, c.val + 2^m, j)`.
-/

/-- **Halving lemma.** If `2 * x` is dyadic mod 2π, then `x` is dyadic
mod 2π. -/
theorem IsDyadicMod2pi.half {x : ℝ} (h : IsDyadicMod2pi (2 * x)) :
    IsDyadicMod2pi x := by
  obtain ⟨m, c, k, hx_eq⟩ := h
  -- hx_eq : 2 * x = 2π · c.val/2^m + 2π · k.
  -- So x = π · c.val/2^m + π · k.
  -- Use π = 2π · 1/2. We have c.val/2^m = (c.val * 2)/2^{m+1}.
  -- Split on parity of k.
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- k = j + j = 2j (Int.even gives k = j + j).
    refine ⟨m + 1, (c.val : ZMod (2 ^ (m + 1))), j, ?_⟩
    have h_val : ((c.val : ZMod (2 ^ (m + 1)))).val = c.val := by
      have hc_lt : c.val < 2 ^ m := ZMod.val_lt c
      have h_lt : c.val < 2 ^ (m + 1) := by
        have : 2 ^ m < 2 ^ (m + 1) := by
          rw [pow_succ]; omega
        omega
      exact ZMod.val_natCast_of_lt h_lt
    rw [h_val]
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have h_pow_pos2 : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
    have h_pow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h_pow_pos
    have h_pow_succ : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
      rw [pow_succ]; ring
    -- Solve from hx_eq.
    have h_x : x = (2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m + 2 * Real.pi * (k : ℝ)) / 2 := by
      have := hx_eq
      linarith
    rw [h_x]
    rw [h_pow_succ]
    have hk : (k : ℝ) = 2 * (j : ℝ) := by
      have h_k : k = j + j := hj
      have h_cast : (k : ℝ) = (j : ℝ) + (j : ℝ) := by exact_mod_cast h_k
      linarith
    rw [hk]
    field_simp
  · -- k = 2j + 1 (Int.odd gives k = 2j + 1).
    refine ⟨m + 1, (c.val + 2 ^ m : ZMod (2 ^ (m + 1))), j, ?_⟩
    have hc_lt : c.val < 2 ^ m := ZMod.val_lt c
    have h_bound : c.val + 2 ^ m < 2 ^ (m + 1) := by
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
      omega
    have h_val : ((c.val + 2 ^ m : ZMod (2 ^ (m + 1)))).val = c.val + 2 ^ m := by
      have : ((c.val + 2 ^ m : ℕ) : ZMod (2 ^ (m + 1))) =
              (c.val : ZMod (2 ^ (m + 1))) + (2 ^ m : ZMod (2 ^ (m + 1))) := by
        push_cast
        rfl
      rw [show ((c.val + 2 ^ m : ZMod (2 ^ (m + 1)))).val
            = ((c.val + 2 ^ m : ℕ) : ZMod (2 ^ (m + 1))).val from by
        congr 1
        push_cast
        rfl]
      exact ZMod.val_natCast_of_lt h_bound
    rw [h_val]
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have h_pow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h_pow_pos
    have h_pow_succ : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
      rw [pow_succ]; ring
    -- Solve from hx_eq.
    have h_x : x = (2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m + 2 * Real.pi * (k : ℝ)) / 2 := by
      have := hx_eq
      linarith
    rw [h_x]
    rw [h_pow_succ]
    have hk : (k : ℝ) = 2 * (j : ℝ) + 1 := by
      have h_k : k = 2 * j + 1 := hj
      have h_cast : (k : ℝ) = 2 * (j : ℝ) + 1 := by exact_mod_cast h_k
      exact h_cast
    rw [hk]
    push_cast
    field_simp
    ring

/-! ## The discrete-derivative-squared identity

For any phase function `g : (Fin n → ZMod 2) → ℝ` and any index
`i : Fin n`, applying `funcDerivPhase i` twice produces `(-2) ·
funcDerivPhase i g` as a function:

  `funcDerivPhase i (funcDerivPhase i g) v = -2 · (funcDerivPhase i g) v`

This is the mod-2 algebraic identity at the heart of the level-3
closure. -/

/-- **Δ_i ∘ Δ_i = -2 · Δ_i** (as functions on phase functions). At
each input `v`, applying the discrete derivative `funcDerivPhase i`
twice produces `-2` times the single derivative. This is because in
`ZMod 2`, `e_i + e_i = 0`, so the second derivative cancels back to
`v` and the alternating sum collapses to `-2 (Δ_i g)(v)`. -/
theorem funcDerivPhase_self_eq_neg_two_smul (i : Fin n)
    (g : (Fin n → ZMod 2) → ℝ) :
    funcDerivPhase i (funcDerivPhase i g) = fun v => -2 * funcDerivPhase i g v := by
  funext v
  simp only [funcDerivPhase_apply]
  -- LHS = [g(v + e_i + e_i) - g(v + e_i)] - [g(v + e_i) - g(v)]
  -- Since 2 · Pi.single i 1 = 0 in (Fin n → ZMod 2), v + e_i + e_i = v.
  have h_two : (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) +
               (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) = 0 := by
    -- Each component is x + x = 0 in ZMod 2.
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    by_cases hj : j = i
    · subst hj; rw [Pi.single_eq_same]; decide
    · simp [Pi.single, Function.update, hj]
  have h_v : v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)
                + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) = v := by
    rw [add_assoc, h_two, add_zero]
  rw [h_v]
  ring

/-- Specialised to `v = 0`: `funcDerivPhase i (funcDerivPhase i g) 0
= -2 · (funcDerivPhase i g) 0`. -/
theorem funcDerivPhase_self_zero (i : Fin n)
    (g : (Fin n → ZMod 2) → ℝ) :
    funcDerivPhase i (funcDerivPhase i g) 0 = -2 * funcDerivPhase i g 0 := by
  have h := funcDerivPhase_self_eq_neg_two_smul i g
  exact congrFun h 0

/-! ## The level-3 conditional closure

Combining the halving lemma, the `Δ_i ∘ Δ_i = -2 · Δ_i` identity, and
the level-2 closure, we obtain the level-3 conditional closure.

Strategy:

1. From `D_g` at level 3, the descent theorem
   `diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`
   at `S = {i}` gives `D_{Δ_i g}` at level 2.

2. `mobiusCoeff_dyadic_mod_2pi_level_two` applied to
   `D_{Δ_i g}` at level 2, with `S' = {i}` (non-empty), gives
   `(funcDerivPhaseSubset {i} (Δ_i g))(0) = (Δ_i Δ_i g)(0)` dyadic
   mod 2π.

3. By `funcDerivPhase_self_zero`, this equals `-2 (Δ_i g)(0)`.

4. By the halving lemma and negation closure, `(Δ_i g)(0)` is
   dyadic mod 2π.

5. By `isDyadicMod2pi_of_level_two_diagonal_anchored` applied to
   `D_{Δ_i g}` at level 2 (with `(Δ_i g)(0)` dyadic), every
   `(Δ_i g)(v)` is dyadic.

6. The required Möbius coefficients `(Δ_S g)(0)` are dyadic for
   every `S` non-empty:
   * `|S| = 1`, `S = {i}`: from step 4.
   * `|S| ≥ 2`: pick `i ∈ S`. `(Δ_S g)(0) = (Δ_{S \ {i}} (Δ_i g))(0)`
     (by commutativity), which is dyadic via
     `mobiusCoeff_dyadic_mod_2pi_level_two` on `D_{Δ_i g}` at `S \ {i}`.

7. By Möbius-via-anchor, `g(v)` is dyadic for every `v`.
-/

/-- **Extraction of `(Δ_i g)(0)` dyadic from level 3.** At level 3 of
the dyadic hierarchy, `(Δ_i g)(0) = g(e_i) - g(0)` is dyadic mod 2π
for every `i`. -/
theorem funcDerivPhase_zero_dyadic_of_level_three
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 3 (diagonalGateEquiv g))
    (i : Fin n) :
    IsDyadicMod2pi (funcDerivPhase i g 0) := by
  -- Step 1: descent at {i} gives D_{Δ_i g} at level 2.
  have h_card_lt : ({i} : Finset (Fin n)).card < 3 := by
    rw [Finset.card_singleton]; omega
  have h_descent :=
    diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
      g h_hier h_card_lt
  have h_level : (3 : ℕ) - ({i} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_singleton]
  rw [h_level, funcDerivPhaseSubset_singleton] at h_descent
  -- h_descent : IsCliffordHierarchyDyadic 2 (diagonalGateEquiv (funcDerivPhase i g))
  -- Step 2: apply mobiusCoeff_dyadic_mod_2pi_level_two at S' = {i}.
  have h_mobius :=
    mobiusCoeff_dyadic_mod_2pi_level_two h_descent
      (S := ({i} : Finset (Fin n)))
      (Finset.singleton_nonempty i)
  -- h_mobius : IsDyadicMod2pi (funcDerivPhaseSubset {i} (funcDerivPhase i g) 0)
  rw [funcDerivPhaseSubset_singleton] at h_mobius
  -- h_mobius : IsDyadicMod2pi (funcDerivPhase i (funcDerivPhase i g) 0)
  -- Step 3: rewrite via funcDerivPhase_self_zero.
  rw [funcDerivPhase_self_zero] at h_mobius
  -- h_mobius : IsDyadicMod2pi (-2 * funcDerivPhase i g 0)
  -- Step 4: halve and negate.
  have h_two_dy : IsDyadicMod2pi (2 * funcDerivPhase i g 0) := by
    have := h_mobius.neg
    have h_neg : -(-2 * funcDerivPhase i g 0) = 2 * funcDerivPhase i g 0 := by ring
    rw [h_neg] at this
    exact this
  exact h_two_dy.half

/-- **Level-3 Möbius coefficient dyadicity.** For `D_g` at level 3
of the dyadic hierarchy with `g(0)` dyadic, every non-empty Möbius
coefficient `(Δ_S g)(0)` is dyadic mod 2π.

Cases on `|S|`:
* `|S| = 1`: from `funcDerivPhase_zero_dyadic_of_level_three`.
* `|S| ≥ 2`: pick `i ∈ S`, write `S = insert i T` (with `T = S.erase i`,
  `|T| ≥ 1` non-empty). Descent at `{i}` gives `D_{Δ_i g}` at level 2.
  Apply `mobiusCoeff_dyadic_mod_2pi_level_two` on `D_{Δ_i g}` at
  `T` (non-empty). Use commutativity of `funcDerivPhase` to identify
  `(Δ_S g)(0) = (Δ_T (Δ_i g))(0)`.
-/
theorem mobiusCoeff_dyadic_mod_2pi_level_three
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 3 (diagonalGateEquiv g))
    {S : Finset (Fin n)} (h_nonempty : S.Nonempty) :
    IsDyadicMod2pi (funcDerivPhaseSubset S g 0) := by
  classical
  -- Pick i ∈ S.
  obtain ⟨i, hi⟩ := h_nonempty
  set T := S.erase i with hT_def
  have hi_notin_T : i ∉ T := Finset.notMem_erase i S
  have h_S_eq : S = insert i T := by
    rw [hT_def, Finset.insert_erase hi]
  -- Case on whether T is empty.
  by_cases h_T_empty : T = ∅
  · -- S = {i}, T empty. Apply step-4 extraction.
    have h_S_singleton : S = {i} := by
      rw [h_S_eq, h_T_empty]
      rfl
    rw [h_S_singleton, funcDerivPhaseSubset_singleton]
    exact funcDerivPhase_zero_dyadic_of_level_three h_hier i
  · -- |S| ≥ 2: T non-empty. Reduce to mobiusCoeff_dyadic_mod_2pi_level_two
    -- on D_{Δ_i g} at level 2.
    rw [h_S_eq, funcDerivPhaseSubset_insert hi_notin_T]
    -- Goal: IsDyadicMod2pi (funcDerivPhase i (funcDerivPhaseSubset T g) 0).
    -- Swap to funcDerivPhaseSubset T (funcDerivPhase i g) via commutativity.
    have h_swap : funcDerivPhase i (funcDerivPhaseSubset T g)
                = funcDerivPhaseSubset T (funcDerivPhase i g) := by
      classical
      induction T using Finset.induction_on with
      | empty =>
          rw [funcDerivPhaseSubset_empty, funcDerivPhaseSubset_empty]
      | @insert j U hj ih =>
          rw [funcDerivPhaseSubset_insert hj, funcDerivPhaseSubset_insert hj]
          rw [← ih]
          exact funcDerivPhase_comm i j _
    rw [h_swap]
    -- Goal: IsDyadicMod2pi (funcDerivPhaseSubset T (funcDerivPhase i g) 0).
    -- Apply mobiusCoeff_dyadic_mod_2pi_level_two on D_{Δ_i g} at level 2.
    have h_descent_i :
        IsCliffordHierarchyDyadic 2
          (diagonalGateEquiv (funcDerivPhase i g)) := by
      have h_card_lt : ({i} : Finset (Fin n)).card < 3 := by
        rw [Finset.card_singleton]; omega
      have h_descent :=
        diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
          g h_hier h_card_lt
      have h_level : (3 : ℕ) - ({i} : Finset (Fin n)).card = 2 := by
        rw [Finset.card_singleton]
      rw [h_level, funcDerivPhaseSubset_singleton] at h_descent
      exact h_descent
    have h_T_nonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_T_empty
    exact mobiusCoeff_dyadic_mod_2pi_level_two h_descent_i h_T_nonempty

/-- **Level-3 conditional closure.** At level 3 of the dyadic hierarchy
with `g(0)` dyadic mod 2π, `g(v)` is dyadic mod 2π for every `v`.

In particular the conditional `g(0) dyadic → ∀ v, g(v) dyadic` holds
at level 3. -/
theorem isDyadicMod2pi_of_level_three_diagonal_anchored
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 3 (diagonalGateEquiv g))
    (h_zero : IsDyadicMod2pi (g 0))
    (v : Fin n → ZMod 2) :
    IsDyadicMod2pi (g v) := by
  apply isDyadicMod2pi_of_mobius_dyadic
  intro S _hS
  by_cases h_empty : S = ∅
  · rw [h_empty, funcDerivPhaseSubset_empty]
    exact h_zero
  · exact mobiusCoeff_dyadic_mod_2pi_level_three h_hier
      (Finset.nonempty_iff_ne_empty.mpr h_empty)

/-- **`AnchoredLevelDyadic` is TRUE at `k = 3`.** -/
theorem anchoredLevelDyadic_three :
    AnchoredLevelDyadic (n := n) 3 := by
  intro g h_hier h_zero v
  exact isDyadicMod2pi_of_level_three_diagonal_anchored h_hier h_zero v

/-! ## Summary

This file proves the level-3 conditional dyadicity for CGK reverse.
Combined with `CGKReverseAnchor.lean`:

| Level | Statement | Source |
|---|---|---|
| `k = 1` | `∀ v, IsDyadicMod2pi (g v)` unconditional | `CGKReverseAnchor.lean` |
| `k = 2` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | `CGKReverseAnchor.lean` |
| `k = 3` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | this file |
| `k ≥ 4` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | `CGKReverseGeneral.lean` |

The level-3 closure makes essential use of the `ZMod 2` algebraic
identity `Δ_i Δ_i = -2 · Δ_i` (the mod-2 squaring of the discrete
derivative), combined with the halving lemma for `IsDyadicMod2pi` (a
factor of 2 costs one bit of precision). The bottleneck at level 3 is
the `|S| = 1` Möbius coefficient; the same mechanism (descent +
halving + induction) delivers the `|S| ≥ 1` coefficients at every
level, which is the content of `CGKReverseGeneral.lean`.
-/

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseLevel3
import FTQCLib.Hilbert.CGKReverseAssembly

set_option linter.unusedSectionVars false

/-! # CGK reverse — general-level closure (all `k ≥ 1`)

This file generalises the level-3 conditional closure of
`CGKReverseLevel3.lean` to **all levels** `k ≥ 1` of the dyadic
operational Clifford hierarchy. The core observation is the algebraic identity

  `Δ_i Δ_i g (v) = -2 · (Δ_i g)(v)`

(from `e_i + e_i = 0` in `(F₂)ⁿ`), combined with the halving lemma
`IsDyadicMod2pi.half`, breaks the apparent circularity between
"`(Δ_i g)(0)` dyadic" and "`g(e_i)` dyadic". The level-3 file
`CGKReverseLevel3.lean` deploys this for `k = 3`. Here we lift the
mechanism to arbitrary `k` by simultaneous induction over two
statements:

* **Möbius coefficient closure** (unconditional on `g(0)`): every
  non-empty `(Δ_S g)(0)` is dyadic mod 2π.

* **Conditional closure** (anchor `g(0)` dyadic): every `g(v)` is
  dyadic mod 2π.

The induction step at `k + 1` reduces both statements to the
level-`k` versions via the descent theorem
`diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`
plus the mod-2 derivative-squared identity. The structural pattern
is identical to the level-3 proof; only the precision (number of
halvings) grows with `k`.

## What this file delivers

* **`mobiusCoeff_dyadic_mod_2pi_level_k`** — for every `k ≥ 1` and
  every non-empty `S`, `(Δ_S g)(0)` is dyadic mod 2π at level `k`.

* **`isDyadicMod2pi_of_level_k_diagonal_anchored`** — for every
  `k ≥ 1`, level-`k` plus `g(0)` dyadic implies `g(v)` dyadic for
  every `v`.

* **`anchoredLevelDyadic_of_one_le`** — the anchored dyadicity
  statement `AnchoredLevelDyadic k` holds at every `k ≥ 1`.

* **`cgk_reverse_dyadic_phase_dyadic_general`** — the phase-function
  pointwise closure: at level `k ≥ 1` of the dyadic hierarchy with
  `g(0)` dyadic, every `g(v)` is dyadic mod 2π. This is the
  structural anchor for downstream polynomial assembly.

## Anchors

* CGK 2017 (arXiv:1608.06596) Theorem 2 / Lemma 4 — `n`-qudit reverse
  direction at `p = 2`.
* Gottesman–Chuang 1999 (arXiv:quant-ph/9908010) — operational
  Clifford hierarchy.
* Rota 1964 — Möbius inversion on the Boolean lattice.
* The mod-2 derivative-squared identity
  `Δ_i Δ_i g = -2 · Δ_i g`, rooted in `(F₂)ⁿ` algebra; see
  `funcDerivPhase_self_eq_neg_two_smul` in `CGKReverseLevel3.lean`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase BooleanMobius

variable {n : ℕ}

/-! ## The bundled mutual-induction proposition

We prove the two conclusions simultaneously, bundled into one
`Prop`-level statement. The form chosen is

  `LevelClosurePair k`

for `k ≥ 1`, asserting

* Möbius coefficient closure at level `k` (unconditional on `g(0)`),
  and
* Conditional closure at level `k` (anchored on `g(0)` dyadic).

The induction step `k → k + 1` uses the Möbius half of `LevelClosurePair
k` to establish both halves of `LevelClosurePair (k + 1)`. -/

/-- **Bundled mutual-induction proposition.** At a given level `k`,
both Möbius-coefficient closure (unconditional) and conditional
closure (anchored on `g(0)`) hold for every diagonal `D_g` at that
level. -/
def LevelClosurePair (k : ℕ) : Prop :=
  ∀ {g : (Fin n → ZMod 2) → ℝ},
    IsCliffordHierarchyDyadic k (diagonalGateEquiv g) →
    (∀ {S : Finset (Fin n)}, S.Nonempty →
       IsDyadicMod2pi (funcDerivPhaseSubset S g 0)) ∧
    (IsDyadicMod2pi (g 0) →
       ∀ v, IsDyadicMod2pi (g v))

/-- **Base case: `k = 1`.** At level 1 of the dyadic hierarchy:
* every Möbius coefficient `(Δ_S g)(0)` is dyadic mod 2π
  (by `funcDerivPhaseSubset_dyadic_of_level_one`);
* every `g(v)` is dyadic mod 2π unconditionally
  (by `isDyadicMod2pi_of_level_one_diagonal_all_v`); the anchor
  hypothesis is not used. -/
theorem levelClosurePair_one : LevelClosurePair (n := n) 1 := by
  intro g h_hier
  refine ⟨?_, ?_⟩
  · intro S _hS
    exact funcDerivPhaseSubset_dyadic_of_level_one h_hier S 0
  · intro _h_zero v
    exact isDyadicMod2pi_of_level_one_diagonal_all_v h_hier v

/-! ## The inductive step

The core inductive argument: given `LevelClosurePair k`, derive
`LevelClosurePair (k + 1)`.

For the Möbius half at `k + 1`: take non-empty `S`, want
`(Δ_S g)(0)` dyadic.

* **Case `|S| = 1`** (`S = {i}`). Descent at `{i}` gives
  `D_{Δ_i g}` at level `k`. By the Möbius half of IH applied to
  `D_{Δ_i g}` at `S' = {i}`,
  `(Δ_i Δ_i g)(0) = -2 · (Δ_i g)(0)` is dyadic mod 2π. By the
  halving lemma `IsDyadicMod2pi.half` plus negation closure,
  `(Δ_i g)(0)` is dyadic mod 2π.

* **Case `|S| ≥ 2`**. Pick `i ∈ S`, set `T = S.erase i`
  (non-empty since `|S| ≥ 2`). By descent at `{i}`,
  `D_{Δ_i g}` is at level `k`. By the Möbius half of IH applied
  to `D_{Δ_i g}` at `S' = T` (non-empty),
  `(Δ_T (Δ_i g))(0)` is dyadic mod 2π. By commutativity of
  `funcDerivPhase`, this equals `(Δ_S g)(0)`.

For the conditional half at `k + 1`: with `g(0)` dyadic, want
`g(v)` dyadic for every `v`. By the Möbius-via-anchor lemma
`isDyadicMod2pi_of_mobius_dyadic`, it suffices that every
`(Δ_S g)(0)` with `S ⊆ supp v` is dyadic. For `S = ∅` this is
the hypothesis. For `S ≠ ∅` this is the just-proved Möbius half
at level `k + 1`. -/

/-- **Inductive step.** `LevelClosurePair k → LevelClosurePair (k + 1)`
for `k ≥ 1`. -/
theorem levelClosurePair_succ {k : ℕ} (_hk : 1 ≤ k)
    (ih : LevelClosurePair (n := n) k) :
    LevelClosurePair (n := n) (k + 1) := by
  intro g h_hier
  -- First prove the Möbius half at level k + 1, then derive the
  -- conditional half from it.
  have h_mobius :
      ∀ {S : Finset (Fin n)}, S.Nonempty →
        IsDyadicMod2pi (funcDerivPhaseSubset S g 0) := by
    classical
    intro S h_nonempty
    -- Pick i ∈ S; write S = insert i T with T = S.erase i.
    obtain ⟨i, hi⟩ := h_nonempty
    set T := S.erase i with hT_def
    have hi_notin_T : i ∉ T := Finset.notMem_erase i S
    have h_S_eq : S = insert i T := by
      rw [hT_def, Finset.insert_erase hi]
    -- Descent at {i}: |{i}| = 1 < k + 1, level (k + 1) - 1 = k.
    have h_card_lt : ({i} : Finset (Fin n)).card < k + 1 := by
      rw [Finset.card_singleton]; omega
    have h_descent :=
      diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
        g h_hier h_card_lt
    have h_level : (k + 1 : ℕ) - ({i} : Finset (Fin n)).card = k := by
      rw [Finset.card_singleton]; omega
    rw [h_level, funcDerivPhaseSubset_singleton] at h_descent
    -- h_descent : IsCliffordHierarchyDyadic k (D_{Δ_i g}).
    -- The Möbius half of IH on D_{Δ_i g}, applied at appropriate S'.
    obtain ⟨ih_mobius_i, _⟩ := ih h_descent
    by_cases h_T_empty : T = ∅
    · -- S = {i}, T empty. Apply IH-Möbius at S' = {i} on D_{Δ_i g}.
      have h_S_singleton : S = {i} := by
        rw [h_S_eq, h_T_empty]
        rfl
      rw [h_S_singleton, funcDerivPhaseSubset_singleton]
      have h_ih_singleton :=
        ih_mobius_i (Finset.singleton_nonempty i)
      rw [funcDerivPhaseSubset_singleton] at h_ih_singleton
      -- h_ih_singleton : IsDyadicMod2pi (Δ_i (Δ_i g) 0)
      rw [funcDerivPhase_self_zero] at h_ih_singleton
      -- h_ih_singleton : IsDyadicMod2pi (-2 * Δ_i g 0)
      have h_two_dy : IsDyadicMod2pi (2 * funcDerivPhase i g 0) := by
        have h_neg := h_ih_singleton.neg
        have h_eq : -(-2 * funcDerivPhase i g 0)
                  = 2 * funcDerivPhase i g 0 := by ring
        rw [h_eq] at h_neg
        exact h_neg
      exact h_two_dy.half
    · -- |S| ≥ 2: T non-empty. Reduce to IH-Möbius at S' = T on D_{Δ_i g}.
      rw [h_S_eq, funcDerivPhaseSubset_insert hi_notin_T]
      -- Goal: IsDyadicMod2pi (Δ_i (Δ_T g) 0).
      -- Swap to Δ_T (Δ_i g) via commutativity.
      have h_swap : funcDerivPhase i (funcDerivPhaseSubset T g)
                  = funcDerivPhaseSubset T (funcDerivPhase i g) := by
        classical
        induction T using Finset.induction_on with
        | empty =>
            rw [funcDerivPhaseSubset_empty, funcDerivPhaseSubset_empty]
        | @insert j U hj ih =>
            rw [funcDerivPhaseSubset_insert hj,
                funcDerivPhaseSubset_insert hj]
            rw [← ih]
            exact funcDerivPhase_comm i j _
      rw [h_swap]
      have h_T_nonempty : T.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr h_T_empty
      exact ih_mobius_i h_T_nonempty
  refine ⟨h_mobius, ?_⟩
  -- Conditional half: with g(0) dyadic, every g(v) is dyadic.
  intro h_zero v
  apply isDyadicMod2pi_of_mobius_dyadic
  intro S _hS
  by_cases h_empty : S = ∅
  · rw [h_empty, funcDerivPhaseSubset_empty]
    exact h_zero
  · exact h_mobius (Finset.nonempty_iff_ne_empty.mpr h_empty)

/-! ## The general-`k` closure

By induction on `k` starting from `k = 1`, we obtain
`LevelClosurePair k` for every `k ≥ 1`. -/

/-- **The bundled mutual-induction closure at level `k`.** For every
`k ≥ 1`, the pair (Möbius coefficient closure, conditional closure)
holds at level `k`. -/
theorem levelClosurePair_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    LevelClosurePair (n := n) k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases h_k'_zero : k' = 0
    · subst h_k'_zero
      exact levelClosurePair_one
    · have h_k'_pos : 1 ≤ k' := Nat.one_le_iff_ne_zero.mpr h_k'_zero
      exact levelClosurePair_succ h_k'_pos (ih h_k'_pos)

/-! ## Corollaries: the two stand-alone statements

We unfold `LevelClosurePair` into its two halves as separate
theorems. -/

/-- **The level-`k` Möbius coefficient closure (unconditional).** At
every level `k ≥ 1`, every non-empty Möbius coefficient
`(Δ_S g)(0)` is dyadic mod 2π.

Proof: induction on `k` via `levelClosurePair_of_one_le`.

Anchor: CGK 2017 (arXiv:1608.06596) §III Lemma 2 eq (50)–(51) at
`p = 2`; Rota 1964 Möbius inversion. -/
theorem mobiusCoeff_dyadic_mod_2pi_level_k
    {n k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    IsDyadicMod2pi (funcDerivPhaseSubset S g 0) :=
  ((levelClosurePair_of_one_le (n := n) hk) h_hier).1 hS

/-- **The level-`k` conditional closure (anchored).** At every level
`k ≥ 1` with `g(0)` dyadic mod 2π, every `g(v)` is dyadic mod 2π.

Proof: induction on `k` via `levelClosurePair_of_one_le`.

The hypothesis `g(0)` dyadic is non-trivial for `k ≥ 2`: the loose
dyadic hierarchy at level `k ≥ 2` does not force `g(0)` dyadic on
its own (a non-dyadic global phase makes `g(0)` arbitrary). For
`k = 1` the hypothesis is redundant (the level-1 base case forces
`g(0)` dyadic structurally).

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 2 reverse direction at
`p = 2`. -/
theorem isDyadicMod2pi_of_level_k_diagonal_anchored
    {n k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    (h_anchor : IsDyadicMod2pi (g 0)) :
    ∀ v, IsDyadicMod2pi (g v) :=
  ((levelClosurePair_of_one_le (n := n) hk) h_hier).2 h_anchor

/-- **`AnchoredLevelDyadic` is TRUE at every `k ≥ 1`.**
This extends the `k = 1, 2` cases of `CGKReverseAnchor.lean` and the
`k = 3` case of `CGKReverseLevel3.lean` to all levels. -/
theorem anchoredLevelDyadic_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    AnchoredLevelDyadic (n := n) k := by
  intro g h_hier h_zero v
  exact isDyadicMod2pi_of_level_k_diagonal_anchored hk h_hier h_zero v

/-! ## The phase-function pointwise closure (anchored)

Repackaging of `isDyadicMod2pi_of_level_k_diagonal_anchored` in the
naming convention of `cgk_reverse_dyadic_phase_dyadic_level_one` and
`cgk_reverse_dyadic_phase_dyadic_level_two`. -/

/-- **General-`k` structural closure (anchored).** For a diagonal
`U = diagonalGateEquiv g` at level `k ≥ 1` of the dyadic hierarchy
with `g(0)` dyadic mod 2π, every `g(v)` is dyadic mod 2π.

This is the general analogue of
`cgk_reverse_dyadic_phase_dyadic_level_one` (`k = 1`, unconditional)
and `cgk_reverse_dyadic_phase_dyadic_level_two` (`k = 2`, anchored).

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 2 reverse direction at
`p = 2`; Rota 1964 Möbius inversion. -/
theorem cgk_reverse_dyadic_phase_dyadic_general
    {k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    (h_zero : IsDyadicMod2pi (g 0)) :
    ∀ v, IsDyadicMod2pi (g v) :=
  isDyadicMod2pi_of_level_k_diagonal_anchored hk h_hier h_zero

/-! ## Reverse direction — existence for diagonals (anchored)

The general-`k` reverse direction in its strongest unconditional
form (existence of a polynomial witness) requires not just the
**values** `g(v)` to be dyadic mod 2π, but a finite uniform
precision bound `m` such that **every** `g(v)` is representable at
precision `m`. The pointwise dyadicity (
`cgk_reverse_dyadic_phase_dyadic_general`) gives precision per
point, but the precisions can in principle vary with `v`.

For the **finite-domain** `(F₂)ⁿ` setting, the supremum of the
per-point precisions is finite (there are only `2^n` inputs), so a
finite uniform `m` exists. The polynomial witness is then constructed
below by Boolean Lagrange interpolation
(`cgk_reverse_dyadic_poly_general`). -/

/-- **Existence of a uniform precision for the per-point dyadic
representations.** Since `(Fin n → ZMod 2)` is finite, the pointwise
dyadicity `∀ v, IsDyadicMod2pi (g v)` lifts to a uniform precision
`m` such that for every `v` there is a representation at precision
`m`. This is a routine `Finset.max'` argument over the (finite) per-
point precisions. The substantive content is
`cgk_reverse_dyadic_phase_dyadic_general`; the uniform-precision
upgrade is bookkeeping. -/
theorem exists_uniform_precision_of_pointwise_dyadic
    {g : (Fin n → ZMod 2) → ℝ}
    (h : ∀ v, IsDyadicMod2pi (g v)) :
    ∃ (m : ℕ),
      ∀ v, ∃ (c : ZMod (2 ^ m)) (kint : ℤ),
        g v = 2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m + 2 * Real.pi * (kint : ℝ) := by
  classical
  -- For each v, pick a per-point witness (m_v, c_v, k_v).
  choose m c kint h_eq using h
  -- The set of per-point precisions is finite; take the max.
  -- For an empty type Fin n → ZMod 2 (n large), the set is finite (= 2^n).
  -- For n = 0, the function type has one element (the empty function),
  -- so the set is still finite with one element.
  refine ⟨Finset.univ.sup m, ?_⟩
  intro v
  -- Lift c_v from ZMod (2 ^ m v) to ZMod (2 ^ (Finset.univ.sup m)).
  -- The natural map: cast via natCast through ℕ.
  -- Specifically: (c_v).val < 2 ^ (m v) ≤ 2 ^ (Finset.univ.sup m).
  have h_mv_le : m v ≤ Finset.univ.sup m :=
    Finset.le_sup (Finset.mem_univ v)
  have h_pow_le : (2 : ℕ) ^ m v ≤ (2 : ℕ) ^ (Finset.univ.sup m) :=
    Nat.pow_le_pow_right (by omega) h_mv_le
  -- Define cv' : ZMod (2 ^ (Finset.univ.sup m)) by reducing (c v).val * (2 ^ Δ).
  -- We need the equation
  --   g v = 2π · cv'.val / 2^M + 2π · k'
  -- where M = Finset.univ.sup m. We have
  --   g v = 2π · (c v).val / 2^(m v) + 2π · k v
  -- Multiply numerator and denominator by 2^Δ where Δ = M - m v.
  set M := Finset.univ.sup m with hM_def
  set Δ := M - m v with hΔ_def
  have hΔ_eq : m v + Δ = M := by
    rw [hΔ_def]; omega
  -- The new c is (c v).val * 2 ^ Δ, viewed in ZMod (2 ^ M).
  have h_bound : ((c v).val * 2 ^ Δ) < 2 ^ M := by
    have h_cv_lt : (c v).val < 2 ^ (m v) := ZMod.val_lt (c v)
    have h_pow_split : (2 : ℕ) ^ M = 2 ^ (m v) * 2 ^ Δ := by
      rw [← pow_add, hΔ_eq]
    rw [h_pow_split]
    have h_two_pow_pos : 0 < (2 : ℕ) ^ Δ := Nat.two_pow_pos Δ
    exact Nat.mul_lt_mul_of_pos_right h_cv_lt h_two_pow_pos
  refine ⟨((c v).val * 2 ^ Δ : ZMod (2 ^ M)), kint v, ?_⟩
  have h_val_eq : ((((c v).val * 2 ^ Δ : ℕ) : ZMod (2 ^ M)) : ZMod (2 ^ M)).val
                = (c v).val * 2 ^ Δ := by
    exact ZMod.val_natCast_of_lt h_bound
  -- The Lean expression `((c v).val * 2 ^ Δ : ZMod (2 ^ M)) : ZMod (2 ^ M))` is
  -- the same as `(((c v).val * 2 ^ Δ : ℕ) : ZMod (2 ^ M))`.
  have h_val_eq' : (((c v).val * 2 ^ Δ : ZMod (2 ^ M))).val
                = (c v).val * 2 ^ Δ := by
    have : (((c v).val * 2 ^ Δ : ℕ) : ZMod (2 ^ M))
        = ((c v).val * 2 ^ Δ : ZMod (2 ^ M)) := by
      push_cast
      rfl
    rw [← this]
    exact ZMod.val_natCast_of_lt h_bound
  rw [h_val_eq']
  -- Now massage the equation g v = 2π · ((c v).val * 2^Δ) / 2^M + 2π · k.
  rw [h_eq v]
  have h_pow_pos_M : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have h_pow_pos_mv : (0 : ℝ) < (2 : ℝ) ^ (m v) := by positivity
  have h_pow_ne_mv : (2 : ℝ) ^ (m v) ≠ 0 := ne_of_gt h_pow_pos_mv
  have h_pow_ne_M : (2 : ℝ) ^ M ≠ 0 := ne_of_gt h_pow_pos_M
  -- (2 ^ M : ℝ) = (2 ^ (m v) : ℝ) * (2 ^ Δ : ℝ).
  have h_pow_split_real : (2 : ℝ) ^ M = (2 : ℝ) ^ (m v) * (2 : ℝ) ^ Δ := by
    rw [← pow_add, hΔ_eq]
  push_cast
  rw [h_pow_split_real]
  field_simp

/-! ## Reverse direction with existence statement (anchored)

A high-level wrapper packaging the dyadic-pointwise closure into the
"there exists a uniform precision" form. -/

/-- **CGK reverse, general `k`, anchored, existence.** For a diagonal
`U` at level `k ≥ 1` of the dyadic hierarchy with `g(0)` dyadic mod
2π, there exists a uniform precision `m` such that every `g(v)`
admits a representation `g v = 2π · c_v.val / 2^m + 2π · k_v`.

This is the structural existence statement underlying the polynomial
witness: with a uniform precision in hand, one can construct
`P : DiagPhase n m` whose evaluations recover `g` up to integer
multiples of `2π`; this is `cgk_reverse_dyadic_poly_general` below.

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 2 reverse direction at
`p = 2`. -/
theorem cgk_reverse_dyadic_general
    {k : ℕ} (hk : 1 ≤ k)
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    (h_anchor : IsDyadicMod2pi (g 0)) :
    ∃ (m : ℕ),
      ∀ v, ∃ (c : ZMod (2 ^ m)) (kint : ℤ),
        g v = 2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m + 2 * Real.pi * (kint : ℝ) :=
  exists_uniform_precision_of_pointwise_dyadic
    (cgk_reverse_dyadic_phase_dyadic_general hk h_hier h_anchor)

/-! ## Polynomial-witness assembly

We now upgrade the uniform-precision existence statement to a full
**polynomial witness** `P : DiagPhase n m` such that `U =
diagonalGateEquiv (DiagPhase.realPhase P)`. The construction uses
the Boolean Lagrange basis on `(Fin n → ZMod 2)`: for each `v`, the
Lagrange polynomial

  `L_v(X) = ∏_i (X_i if v_i = 1, else (1 - X_i))`

evaluates to `1` at `v` and `0` at every other Boolean input. The
polynomial

  `P = Σ_v c_v · L_v(X)`

then evaluates to `c_v` at `v` (with the per-point witnesses
extracted from the uniform-precision dyadic representations). -/

/-- The Boolean Lagrange basis polynomial at `v`. Evaluates to `1` at
`v` and `0` at every other Boolean input. -/
noncomputable def lagrangeBoolean {n m : ℕ} (v : Fin n → ZMod 2) :
    DiagPhase n m :=
  ∏ i, (if v i = 1 then MvPolynomial.X i
        else (1 - MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2^m))))

/-- The lifted Boolean value: `(v i).val` is 0 or 1 in `ZMod (2^m)`. -/
private theorem liftBinary_val_eq_zero_or_one {n m : ℕ}
    (v : Fin n → ZMod 2) (i : Fin n) :
    DiagPhase.liftBinary (m := m) v i =
      if v i = 1 then (1 : ZMod (2^m)) else (0 : ZMod (2^m)) := by
  unfold DiagPhase.liftBinary
  by_cases hv : v i = 1
  · rw [hv]; simp
  · have hv0 : v i = 0 := by
      have h2 : v i = 0 ∨ v i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      tauto
    rw [hv0]; simp

/-- The Lagrange basis polynomial evaluated at the same input is `1`. -/
theorem lagrangeBoolean_eval_self {n m : ℕ} (v : Fin n → ZMod 2) :
    (lagrangeBoolean (m := m) v).eval v = 1 := by
  unfold lagrangeBoolean DiagPhase.eval
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i _
  by_cases hv : v i = 1
  · simp only [hv, if_true]
    rw [MvPolynomial.eval_X]
    rw [liftBinary_val_eq_zero_or_one v i, hv]
    simp
  · have hv0 : v i = 0 := by
      have h2 : v i = 0 ∨ v i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      tauto
    simp only [hv, if_false]
    rw [map_sub, map_one, MvPolynomial.eval_X]
    rw [liftBinary_val_eq_zero_or_one v i, hv0]
    simp

/-- The Lagrange basis polynomial evaluated at a different input is `0`. -/
theorem lagrangeBoolean_eval_other {n m : ℕ} {v w : Fin n → ZMod 2}
    (hvw : v ≠ w) :
    (lagrangeBoolean (m := m) v).eval w = 0 := by
  unfold lagrangeBoolean DiagPhase.eval
  rw [map_prod]
  -- There exists i such that v i ≠ w i. At this i, the factor is 0.
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ w i := by
    by_contra h
    push_neg at h
    apply hvw
    funext i
    exact h i
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  -- Determine the factor at i. The branch depends on (v i).
  by_cases hv : v i = 1
  · -- v i = 1, w i = 0. Factor is X_i evaluated at 0 = liftBinary w i = 0.
    have hw : w i = 0 := by
      have h2 : w i = 0 ∨ w i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      cases h2 with
      | inl h => exact h
      | inr h => exfalso; apply hi; rw [hv, h]
    simp only [hv, if_true]
    rw [MvPolynomial.eval_X]
    rw [liftBinary_val_eq_zero_or_one w i, hw]
    simp
  · -- v i = 0, w i = 1. Factor is (1 - X_i) evaluated at 1 = 0.
    have hv0 : v i = 0 := by
      have h2 : v i = 0 ∨ v i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      tauto
    have hw1 : w i = 1 := by
      have h2 : w i = 0 ∨ w i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      cases h2 with
      | inl h => exfalso; apply hi; rw [hv0, h]
      | inr h => exact h
    simp only [hv, if_false]
    rw [map_sub, map_one, MvPolynomial.eval_X]
    rw [liftBinary_val_eq_zero_or_one w i, hw1]
    simp

/-- The interpolating polynomial for a function `c : (Fin n → ZMod 2)
→ ZMod (2^m)`. Defined as the Boolean Lagrange expansion
`Σ_v c v • L_v(X)`. -/
noncomputable def interpolatingPoly {n m : ℕ}
    (c : (Fin n → ZMod 2) → ZMod (2^m)) : DiagPhase n m :=
  ∑ v, MvPolynomial.C (c v) * lagrangeBoolean v

/-- **Interpolation theorem.** `(interpolatingPoly c).eval v = c v`
for every `v`. -/
theorem interpolatingPoly_eval {n m : ℕ}
    (c : (Fin n → ZMod 2) → ZMod (2^m)) (v : Fin n → ZMod 2) :
    (interpolatingPoly c).eval v = c v := by
  change (MvPolynomial.eval (DiagPhase.liftBinary v))
        (∑ w, MvPolynomial.C (c w) * lagrangeBoolean w) = c v
  rw [map_sum]
  -- The sum picks up only the v-term; other terms vanish by
  -- lagrangeBoolean_eval_other.
  rw [Finset.sum_eq_single v]
  · -- v-term: eval (C (c v) * lagrangeBoolean v) v = c v · 1 = c v.
    rw [map_mul, MvPolynomial.eval_C]
    change c v * (lagrangeBoolean (m := m) v).eval v = c v
    rw [lagrangeBoolean_eval_self]
    ring
  · -- Other terms vanish.
    intro w _ hw
    rw [map_mul, MvPolynomial.eval_C]
    change c w * (lagrangeBoolean (m := m) w).eval v = 0
    rw [lagrangeBoolean_eval_other (v := w) (w := v) hw]
    ring
  · intro h
    exfalso
    exact h (Finset.mem_univ v)

/-! ## The polynomial-witness existence theorem

Combining `cgk_reverse_dyadic_general` (uniform-precision pointwise
dyadicity) with `interpolatingPoly` (Boolean Lagrange interpolation),
we obtain a polynomial `P : DiagPhase n m` such that
`U = diagonalGateEquiv (realPhase P)`. The level bound `P.level ≤ k`
is precision-dependent and not directly established here. -/

/-- **CGK reverse polynomial-witness existence, general `k`,
anchored.** For a diagonal `U` at level `k ≥ 1` of the dyadic
Clifford hierarchy with `g(0)` dyadic mod 2π, there is a polynomial
`P : DiagPhase n m` (some precision `m`) such that
`U = diagonalGateEquiv (DiagPhase.realPhase P)`.

The level bound `P.level ≤ k` is precision-dependent and is not
established here: it requires tracking the precision through the
Möbius assembly. The degree bound `totalDegree ≤ k` is
`cgk_reverse_dyadic_poly_mobius_general` in `CGKReverseTightLevel.lean`.

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 2 / Lemma 4 reverse
direction at `p = 2`. -/
theorem cgk_reverse_dyadic_poly_general
    {k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (_h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_anchor : ∃ f, U = diagonalGateEquiv f ∧ IsDyadicMod2pi (f 0))
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      U = diagonalGateEquiv (DiagPhase.realPhase P) := by
  -- Extract g from the diagonal-with-anchor hypothesis.
  obtain ⟨g, hU_eq, h_anchor_g⟩ := h_anchor
  -- The hierarchy hypothesis on U transfers to D_g.
  have h_hier_g : IsCliffordHierarchyDyadic k (diagonalGateEquiv g) := by
    rw [← hU_eq]
    exact h_hier
  -- Apply the uniform-precision existence.
  obtain ⟨m, h_uniform⟩ :=
    cgk_reverse_dyadic_general hk h_hier_g h_anchor_g
  -- Choose per-v witnesses (c v, k v) so that
  --   g v = 2π · (c v).val / 2^m + 2π · k v.
  classical
  choose c kint hc using h_uniform
  -- Define P = interpolatingPoly c.
  refine ⟨m, interpolatingPoly c, ?_⟩
  -- Show: U = diagonalGateEquiv (realPhase (interpolatingPoly c)).
  rw [hU_eq]
  apply diagonalGateEquiv_eq_of_diff_two_pi
  intro v
  refine ⟨kint v, ?_⟩
  -- Show: g v - realPhase (interpolatingPoly c) v = 2π · (kint v).
  unfold DiagPhase.realPhase
  rw [interpolatingPoly_eval c v]
  -- Goal: g v - 2π · (c v).val / 2^m = 2π · (kint v).
  rw [hc v]
  ring

/-! ## Tight hierarchy version

The tight hierarchy `IsCliffordHierarchyTight` is the loose dyadic
hierarchy with the additional constraint that base-case scalars are
`±1`. The conditional closure carries over via the canonical map
`IsCliffordHierarchyTight.toCliffordHierarchyDyadic`.

**Note on automaticity of the anchor.** At tight level **1**, the
anchor `g(0)` dyadic is automatic (the tight base scalar `±1` gives
`g(0) ∈ {0, π} (mod 2π)`, both dyadic) — this is
`cgk_reverse_tight_level_one`'s implicit ingredient. At tight level
`k ≥ 2`, the anchor is **not** automatic: the recursive `.step` rule
constrains conjugates by Paulis but not the operator's own global
phase. So the general tight version still requires the anchor as a
hypothesis, identical in form to the loose dyadic version. -/

/-- **Tight hierarchy general-`k` closure (anchored).** For a
diagonal `U = diagonalGateEquiv g` at level `k ≥ 1` of the tight
Clifford hierarchy with `g(0)` dyadic mod 2π, every `g(v)` is dyadic
mod 2π.

Proof: tight implies loose dyadic; then apply
`cgk_reverse_dyadic_phase_dyadic_general`. -/
theorem cgk_reverse_tight_phase_dyadic_general
    {k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyTight k (diagonalGateEquiv g))
    (h_zero : IsDyadicMod2pi (g 0)) :
    ∀ v, IsDyadicMod2pi (g v) :=
  cgk_reverse_dyadic_phase_dyadic_general hk
    h_hier.toCliffordHierarchyDyadic h_zero

/-- **Tight hierarchy general-`k` existence (anchored).** For a
diagonal `U = diagonalGateEquiv g` at level `k ≥ 1` of the tight
Clifford hierarchy with `g(0)` dyadic mod 2π, there exists a uniform
precision `m` for the dyadic representations of every `g(v)`. -/
theorem cgk_reverse_tight_general
    {k : ℕ} (hk : 1 ≤ k)
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyTight k (diagonalGateEquiv g))
    (h_anchor : IsDyadicMod2pi (g 0)) :
    ∃ (m : ℕ),
      ∀ v, ∃ (c : ZMod (2 ^ m)) (kint : ℤ),
        g v = 2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m + 2 * Real.pi * (kint : ℝ) :=
  cgk_reverse_dyadic_general hk h_hier.toCliffordHierarchyDyadic h_anchor

/-- **Tight hierarchy polynomial-witness existence (anchored).** For a
diagonal `U` at level `k ≥ 1` of the tight Clifford hierarchy with
`g(0)` dyadic mod 2π, there is a polynomial `P : DiagPhase n m`
(some precision `m`) such that `U = diagonalGateEquiv (realPhase P)`.

The level bound `P.level ≤ k` is precision-dependent and is not
established here.

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 2 / Lemma 4 reverse
direction at `p = 2`. -/
theorem cgk_reverse_tight_poly_general
    {k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (_h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_anchor : ∃ f, U = diagonalGateEquiv f ∧ IsDyadicMod2pi (f 0))
    (h_hier : IsCliffordHierarchyTight k U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      U = diagonalGateEquiv (DiagPhase.realPhase P) :=
  cgk_reverse_dyadic_poly_general hk U _h_diag h_anchor
    h_hier.toCliffordHierarchyDyadic

/-! ## Tight level 1: the anchor is automatic

At tight level 1, `g(0)` is forced dyadic by the base-scalar `±1`
constraint, so the conditional closure becomes unconditional. -/

/-- **Tight level-1 closure (unconditional).** For a diagonal
`U = diagonalGateEquiv g` at level 1 of the tight Clifford
hierarchy, every `g(v)` is dyadic mod 2π. Unconditional: the tight
base-scalar `±1` forces `g(0) ∈ {0, π}`, automatically dyadic. -/
theorem cgk_reverse_tight_level_one_phase_dyadic
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyTight 1 (diagonalGateEquiv g)) :
    ∀ v, IsDyadicMod2pi (g v) :=
  isDyadicMod2pi_of_level_one_diagonal_all_v
    h_hier.toCliffordHierarchyDyadic

/-- **Tight level-1 polynomial-witness existence (unconditional).**
At tight level 1, the anchor is automatic (base-scalar `±1` gives
`g(0) ∈ {0, π}`, both dyadic). So the polynomial-witness existence
theorem holds unconditionally at tight level 1.

Note: `cgk_reverse_tight_level_one` is sharper, giving
`P.level ≤ 1`. This corollary gives only existence (no level bound)
but is the natural specialisation of the general-`k` machinery. -/
theorem cgk_reverse_tight_level_one_poly
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_hier : IsCliffordHierarchyTight 1 U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      U = diagonalGateEquiv (DiagPhase.realPhase P) := by
  obtain ⟨g, hU_eq⟩ := h_diag
  have h_hier_g : IsCliffordHierarchyTight 1 (diagonalGateEquiv g) := by
    rw [← hU_eq]; exact h_hier
  -- Anchor is automatic at tight level 1.
  have h_anchor_g : IsDyadicMod2pi (g 0) :=
    isDyadicMod2pi_of_level_one_diagonal h_hier_g.toCliffordHierarchyDyadic
  refine cgk_reverse_tight_poly_general (k := 1) (by omega) U
    ⟨g, hU_eq⟩ ⟨g, hU_eq, h_anchor_g⟩ h_hier

/-! ## Summary

| Level | Statement | Source |
|---|---|---|
| `k = 1` | `∀ v, IsDyadicMod2pi (g v)` unconditional | `CGKReverseAnchor.lean` |
| `k = 2` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | `CGKReverseAnchor.lean` |
| `k = 3` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | `CGKReverseLevel3.lean` |
| `k ≥ 4` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | this file |
| `k ≥ 1` | Uniform-precision existence (anchored) | this file |
| `k ≥ 1` | Polynomial-witness existence (anchored) | this file |
| `k ≥ 1` | Tight conditional + existence | this file |
| `k = 1` (tight) | Unconditional `∀ v, dyadic` | this file |

The general-`k` closure follows from the level-3 mechanism (the
`Δ_i Δ_i = -2 · Δ_i` identity plus halving) by simultaneous induction
on `k`. The structural pattern at level `k + 1` reproduces the level-3
argument, applying the level-`k` induction hypothesis where the
level-3 proof applies the level-2 Möbius coefficient closure.

## Scope

* **Level bound `P.level ≤ k`.** The polynomial witness here carries no
  level bound. The degree bound `totalDegree ≤ k` is
  `CGKReverseTightLevel.lean`; the sharp projective form
  (`effectiveLevel ≤ k` up to a global phase) is
  `cgk_reverse_projective_sharp` in `CGKTwoSided.lean`.

* **Tight hierarchy unconditional version at `k ≥ 2`.** Not proved.
  At tight level `k ≥ 2` the `g(0)` anchor is not forced by the
  hierarchy structure alone (the .step rule only constrains
  Pauli conjugates, not the operator's global phase).

* **Vanishing for `|S| > k`.** Proved in `CGKReverseVanish.lean`.
-/

end FTQCLib.Hilbert

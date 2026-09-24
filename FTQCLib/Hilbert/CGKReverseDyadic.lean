/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.HierarchyDyadic
import FTQCLib.Hilbert.CGKReverseIteration
import FTQCLib.Hilbert.CGKReverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedSectionVars false

/-! # CGK reverse — dyadic-denominator bookkeeping

Dyadic-denominator bookkeeping for the iterated discrete derivatives of
a diagonal `U` at `IsCliffordHierarchyDyadic k`. For each subset
`S ⊆ Fin n` of size `< k`, the Möbius coefficient
`funcDerivPhaseSubset S f 0` is congruent (modulo `2π`) to a dyadic
rational multiple of `2π`. For `|S| ≥ k`, the coefficient is `0`
modulo `2π`.

This is the Boolean specialisation of CGK 2017 §III Lemma 2 eq (50)-(51),
with the Faulhaber-inversion step replaced by Möbius inversion on the
Boolean lattice (Rota 1964).

## What this file delivers

* **`IsDyadicMod2pi`** — the predicate "real number is congruent mod 2π
  to a dyadic rational multiple of 2π". Closure under negation,
  addition, and integer-multiple-of-2π translation.

* **`isDyadicMod2pi_of_level_one_diagonal`** — the base case of CGK
  reverse on the dyadic side. If `diagonalGateEquiv g` sits at level
  `1` of the dyadic hierarchy, then `g 0` is dyadic mod 2π.

* **`mobiusPhaseCoeff_empty`** — the Möbius coefficient at `S = ∅`
  evaluates to `f 0`.

* **`diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`**
  — the descent theorem: for `|S| < k`, the iterated
  discrete-derivative diagonal sits at level `k - |S|`.

* **`mobiusPhaseCoeff_dyadic_mod_2pi_top`** — the Möbius coefficient
  is dyadic mod 2π for `|S| = k - 1`. The lower-`|S|` case is
  `mobiusCoeff_dyadic_mod_2pi_level_k` in `CGKReverseGeneral.lean`.

## Anchors

* Gottesman-Chuang 1999 (arXiv:quant-ph/9908010) — operational hierarchy.
* CGK 2017 (arXiv:1608.06596) Lemma 2 eq (40)–(56) — reverse direction
  skeleton; §III eq (50)-(51) — denominator analysis; eq (62) — the
  level formula `w = (m-1) + d` at `p = 2`.
* Rota 1964 — Möbius inversion on locally finite posets.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## A dyadic-mod-2π predicate

A real number is **dyadic mod 2π** if it admits a representation
`2π · c.val / 2^m' + 2π · k` for some natural `m'`, residue
`c : ZMod (2^m')`, and integer `k`. This is the real-phase analogue of
`IsDyadicScalar` from `HierarchyDyadic.lean`: the argument of a dyadic
unit scalar. -/

/-- A real number `x` is **dyadic mod 2π** if there exist `m' : ℕ`,
`c : ZMod (2^m')`, and `kint : ℤ` such that
`x = 2π · c.val / 2^m' + 2π · kint`. -/
def IsDyadicMod2pi (x : ℝ) : Prop :=
  ∃ (m' : ℕ) (c : ZMod (2 ^ m')) (kint : ℤ),
    x = 2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m' + 2 * Real.pi * (kint : ℝ)

/-- Zero is dyadic mod 2π. -/
theorem isDyadicMod2pi_zero : IsDyadicMod2pi 0 := by
  refine ⟨0, 0, 0, ?_⟩
  simp

/-- Any integer multiple of `2π` is dyadic mod 2π. -/
theorem isDyadicMod2pi_int_mul_2pi (kint : ℤ) :
    IsDyadicMod2pi (2 * Real.pi * (kint : ℝ)) := by
  refine ⟨0, 0, kint, ?_⟩
  simp only [ZMod.val_zero, Nat.cast_zero, pow_zero, mul_zero, zero_div,
    zero_add]

/-- Translation by an integer multiple of `2π` preserves the
dyadic-mod-2π predicate. -/
theorem isDyadicMod2pi_add_int_mul_2pi {x : ℝ} (h : IsDyadicMod2pi x)
    (kint : ℤ) :
    IsDyadicMod2pi (x + 2 * Real.pi * (kint : ℝ)) := by
  obtain ⟨m', c, k₀, hx⟩ := h
  refine ⟨m', c, k₀ + kint, ?_⟩
  rw [hx]
  push_cast
  ring

/-- The unique-up-to-2π real argument of a dyadic unit scalar `α` is
dyadic mod 2π. Concretely: if `α : ℂˣ` is dyadic (a 2^m'-th root of
unity) and `θ : ℝ` satisfies `α = exp(I θ)`, then `θ` is dyadic mod
2π. -/
theorem isDyadicMod2pi_of_dyadicScalar_arg
    {α : ℂˣ} (hα : IsDyadicScalar α) {θ : ℝ}
    (hθ : (α : ℂ) = Complex.exp (Complex.I * (θ : ℂ))) :
    IsDyadicMod2pi θ := by
  obtain ⟨m', c, hα_eq⟩ := hα
  rw [hα_eq] at hθ
  -- hθ: exp(I · 2π c.val / 2^m') = exp(I · θ).
  -- So θ = 2π c.val / 2^m' + 2π k for some k.
  -- Use Complex.exp_eq_exp_iff_exists_int.
  rw [Complex.exp_eq_exp_iff_exists_int] at hθ
  obtain ⟨k, hk⟩ := hθ
  -- hk: I · 2π c.val / 2^m' = I · θ + k · 2π I.
  refine ⟨m', c, -k, ?_⟩
  -- Solve for θ: θ = 2π c.val / 2^m' - k · 2π.
  -- Massage through the complex equation.
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- Subtract: I · (2π c.val / 2^m' - θ) = k · 2π · I.
  have h_sub :
      Complex.I * ((((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
                     - (θ : ℂ))
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hk
  -- Multiply by -I to isolate (2π c.val / 2^m' - θ).
  have h_diff :
      (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
        - (θ : ℂ)
        = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h := congrArg (fun z : ℂ => -Complex.I * z) h_sub
    simp only at h
    have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h_neg_I_I : -Complex.I * Complex.I = 1 := by linear_combination -hI_sq
    have h_lhs :
        -Complex.I * (Complex.I *
          ((((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
            - (θ : ℂ)))
          = (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
              - (θ : ℂ) := by
      rw [show -Complex.I * (Complex.I *
            ((((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
              - (θ : ℂ)))
            = (-Complex.I * Complex.I) *
              ((((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
                - (θ : ℂ)) from by ring]
      rw [h_neg_I_I, one_mul]
    have h_rhs :
        -Complex.I * ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
          = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
      rw [show -Complex.I * ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
            = (k : ℂ) * (2 * (Real.pi : ℂ)) *
                (-Complex.I * Complex.I) from by ring]
      rw [h_neg_I_I, mul_one]
    rw [h_lhs, h_rhs] at h
    exact h
  -- Cast h_diff back to ℝ.
  have h_real :
      (2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') - θ
        = (k : ℝ) * (2 * Real.pi) := by
    have hreal := congrArg Complex.re h_diff
    have hL_re : ((((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ)
                    - (θ : ℂ)).re
                  = (2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') - θ := by
      rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
    have hR_re : ((k : ℂ) * (2 * (Real.pi : ℂ))).re = (k : ℝ) * (2 * Real.pi) := by
      rw [Complex.mul_re]
      have h_k_re : (k : ℂ).re = (k : ℝ) := Complex.intCast_re k
      have h_k_im : (k : ℂ).im = 0 := Complex.intCast_im k
      have h_two_pi_re : ((2 : ℂ) * (Real.pi : ℂ)).re = 2 * Real.pi := by
        rw [Complex.mul_re]
        simp [Complex.ofReal_re, Complex.ofReal_im]
      have h_two_pi_im : ((2 : ℂ) * (Real.pi : ℂ)).im = 0 := by
        rw [Complex.mul_im]
        simp [Complex.ofReal_re, Complex.ofReal_im]
      rw [h_k_re, h_k_im, h_two_pi_re, h_two_pi_im, zero_mul, sub_zero]
    rw [hL_re, hR_re] at hreal
    exact hreal
  push_cast
  linarith

/-! ## Phase extraction at zero for level-1 dyadic operators

A diagonal `U = diagonalGateEquiv g` that sits at level `1` of the
dyadic hierarchy has `g 0` dyadic mod 2π. The argument unpacks the
level-1 hypothesis to obtain a dyadic phased-Pauli witness, applies
the operator-side identity at the basis vector `|0⟩`, and reads off
`g 0` as the argument of a dyadic unit scalar via
`Complex.exp_eq_exp_iff_exists_int`. -/

/-- **Phase extraction at zero, level 1.** If `diagonalGateEquiv g`
is at level `1` of `IsCliffordHierarchyDyadic`, then `g 0` is dyadic
mod 2π.

**Argument**: at level `1`, `(diagonalGateEquiv g).toLinearMap = α •
pauliOperator p` for some dyadic unit scalar `α` and some Pauli `p`.
The diagonal hypothesis forces `p.X = 0` (via
`Pauli_X_zero_of_diagonal_phasedPauli`). Evaluating both forms at the
computational vector `|0⟩` produces `exp(I · g 0) = α`. By the dyadic
representation of `α`, the equation `exp(I θ₁) = exp(I θ₂)` is
equivalent (via `Complex.exp_eq_exp_iff_exists_int`) to `θ₁ - θ₂ ∈ 2π
ℤ`, giving the dyadic-mod-2π conclusion. -/
theorem isDyadicMod2pi_of_level_one_diagonal
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g)) :
    IsDyadicMod2pi (g 0) := by
  -- Extract the phased-Pauli witness from the base case. The `step`
  -- constructor for level 1 would require a level-`0` hypothesis,
  -- which is uninhabited (no constructor produces level 0).
  generalize hk_eq : (1 : ℕ) = klvl at h_hier
  cases h_hier with
  | base hU =>
    obtain ⟨α, p, hα_dy, hα⟩ := hU
    -- The diagonal hypothesis forces `p.X = 0`.
    have hpX : p.X = 0 :=
      Pauli_X_zero_of_diagonal_phasedPauli rfl hα
    -- Apply both forms of the linear map at the basis vector `|0⟩`.
    have h_apply :
        (diagonalGateEquiv g) (computational (0 : Fin n → ZMod 2)) =
          (α : ℂ) • (pauliOperator p) (computational (0 : Fin n → ZMod 2)) := by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) =>
          L (computational (0 : Fin n → ZMod 2)))
        hα
      simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
      exact h
    -- Simplify the Pauli action: zDot p 0 = 0, p.X = 0.
    have hzdot : zDotVal p (0 : Fin n → ZMod 2) = 0 := by
      unfold zDotVal
      refine Finset.sum_eq_zero ?_
      intro i _
      have h0 : ((0 : Fin n → ZMod 2) i).val = 0 := by
        change ((0 : ZMod 2)).val = 0
        exact ZMod.val_zero
      rw [h0]; ring
    rw [diagonalGateEquiv_apply, diagonalGate_computational,
        pauliOperator_computational, hzdot, pow_zero, one_smul,
        zero_add, hpX] at h_apply
    -- Evaluate both sides as functions at the input vector `0`.
    have h_eval :
        (Complex.exp (Complex.I * g (0 : Fin n → ZMod 2)) •
            computational (0 : Fin n → ZMod 2)) (0 : Fin n → ZMod 2) =
          ((α : ℂ) • computational (0 : Fin n → ZMod 2)) (0 : Fin n → ZMod 2) :=
      congrFun h_apply (0 : Fin n → ZMod 2)
    simp only [Pi.smul_apply, computational_self, smul_eq_mul, mul_one]
      at h_eval
    -- h_eval: exp(I · g 0) = α. Use the arg-extraction lemma; we
    -- need (α : ℂ) = exp(I θ) for θ = g 0, so flip h_eval.
    refine isDyadicMod2pi_of_dyadicScalar_arg hα_dy ?_
    exact h_eval.symm
  | @step kpred _ h =>
    -- klvl = kpred+1 in the step case; but hk_eq says klvl = 1, so kpred = 0.
    have hk0 : kpred = 0 := by omega
    subst hk0
    -- h : ∀ p, IsCliffordHierarchyDyadic 0 (conjEquiv _ (pauliEquiv p)).
    -- IsCliffordHierarchyDyadic 0 is uninhabited.
    cases h 0

/-! ## The Möbius coefficient

The Möbius coefficient `funcDerivPhaseSubset S f 0` is the quantity
used for polynomial assembly. At `S = ∅` it is just `f 0`. -/

/-- The **Möbius coefficient** at `S` for the phase function `f`. -/
noncomputable def mobiusPhaseCoeff (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → ℝ) : ℝ :=
  funcDerivPhaseSubset S f 0

/-- The Möbius coefficient at the empty subset reduces to `f 0`. -/
@[simp] theorem mobiusPhaseCoeff_empty (f : (Fin n → ZMod 2) → ℝ) :
    mobiusPhaseCoeff ∅ f = f 0 := by
  unfold mobiusPhaseCoeff
  rw [funcDerivPhaseSubset_empty]

/-- The Möbius coefficient at the empty subset, for a diagonal `U` at
level 1 of the dyadic hierarchy, is dyadic mod 2π: a corollary of
`isDyadicMod2pi_of_level_one_diagonal`. -/
theorem mobiusCoeff_dyadic_mod_2pi_base
    {f : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv f)) :
    IsDyadicMod2pi (mobiusPhaseCoeff ∅ f) := by
  rw [mobiusPhaseCoeff_empty]
  exact isDyadicMod2pi_of_level_one_diagonal h_hier

/-! ## The descent theorem

The substantive descent: for a diagonal `U = diagonalGateEquiv f` at
level `k` of the dyadic hierarchy and a subset `S` with `|S| < k`,
the iterated discrete-derivative diagonal
`diagonalGateEquiv (funcDerivPhaseSubset S f)` sits at level
`k - |S|` of the dyadic hierarchy.

Proof by `Finset.induction_on` on `S`:

* Base (`S = ∅`): `funcDerivPhaseSubset ∅ f = f` (by
  `funcDerivPhaseSubset_empty`), and `k - 0 = k`, so the conclusion
  is the hypothesis.

* Step (`S' = insert i S`, `i ∉ S`): we have
  `D_{funcDerivPhaseSubset S f}` at level `k - |S|` from the IH.
  Since `|S'| < k`, `k - |S| ≥ 1`, so we can write `k - |S| = (k - |S| - 1) + 1`
  and apply the `step` rule of the hierarchy. The descent at level
  `k - |S|` and conjugation by `pauliEquiv (paulix i)` gives a
  level-`(k - |S| - 1)` operator. By
  `conjEquiv_diagonalGateEquiv_paulix_funcDeriv`, the conjugate is
  `(D_{funcDerivPhase i (funcDerivPhaseSubset S f)}).trans
   (pauliEquiv (paulix i))`. By `mul_pauli_right_iff` (the right-
  multiplication closure), this is equivalent to
  `D_{funcDerivPhase i (funcDerivPhaseSubset S f)}` being at
  level `k - |S| - 1`. Finally, `funcDerivPhaseSubset_insert` rewrites
  `funcDerivPhase i (funcDerivPhaseSubset S f) =
   funcDerivPhaseSubset (insert i S) f`, and `k - |S'| = k - |S| - 1`. -/

/-- **Descent theorem.** For a diagonal `U = diagonalGateEquiv f` at
level `k` of the dyadic hierarchy and a subset `S` of size `< k`, the
iterated discrete-derivative diagonal sits at level `k - |S|`. -/
theorem diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
    {k : ℕ} (f : (Fin n → ZMod 2) → ℝ)
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv f))
    {S : Finset (Fin n)} (h_card : S.card < k) :
    IsCliffordHierarchyDyadic (k - S.card)
      (diagonalGateEquiv (funcDerivPhaseSubset S f)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.card_empty, Nat.sub_zero, funcDerivPhaseSubset_empty]
      exact h_hier
  | @insert i S hi ih =>
      -- |insert i S| = |S| + 1 ≤ k - 1, so |S| < k.
      have h_S_card : S.card < k := by
        rw [Finset.card_insert_of_notMem hi] at h_card
        omega
      have h_ih := ih h_S_card
      -- k - |insert i S| ≥ 1, so k - |S| ≥ 2.
      have h_S_card_succ_lt : S.card + 1 < k := by
        rw [Finset.card_insert_of_notMem hi] at h_card
        exact h_card
      have h_pos : 2 ≤ k - S.card := by omega
      -- Write k - |S| = (k - |S| - 2) + 2 (so the level is ≥ 2 for step_inv).
      obtain ⟨k'', hk''⟩ : ∃ k'', k - S.card = k'' + 2 :=
        ⟨k - S.card - 2, by omega⟩
      rw [hk''] at h_ih
      -- h_ih : level (k'' + 2) on D_{Δ_S f}.
      -- Step inversion: ∀ p, conjEquiv (D_{Δ_S f}) (pauliEquiv p) ∈ level (k'' + 1).
      have h_step : IsCliffordHierarchyDyadic (k'' + 1)
          (conjEquiv (diagonalGateEquiv (funcDerivPhaseSubset S f))
            (pauliEquiv (paulix i))) :=
        cliffordHierarchyDyadic_step_inv h_ih (paulix i)
      -- Use the single-step bridge:
      rw [conjEquiv_diagonalGateEquiv_paulix_funcDeriv] at h_step
      rw [IsCliffordHierarchyDyadic.mul_pauli_right_iff] at h_step
      have h_card_eq : k - (insert i S).card = k'' + 1 := by
        rw [Finset.card_insert_of_notMem hi]
        omega
      rw [h_card_eq, funcDerivPhaseSubset_insert hi]
      exact h_step

/-! ## Möbius coefficient is dyadic mod 2π (top-level case)

For `|S| = k - 1`, the descent lands directly at level 1, where the
base case `isDyadicMod2pi_of_level_one_diagonal` gives dyadicity at
`v = 0`. -/

/-- **Möbius coefficient dyadicity, top-level case.** For `|S| = k - 1`,
the Möbius coefficient `mobiusPhaseCoeff S f = funcDerivPhaseSubset S f 0`
is dyadic mod 2π. Proof: descend to level 1 via the descent theorem,
then apply `isDyadicMod2pi_of_level_one_diagonal`. -/
theorem mobiusPhaseCoeff_dyadic_mod_2pi_top
    {k : ℕ} {f : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv f))
    {S : Finset (Fin n)} (h_card : S.card = k - 1) (h_k_pos : 1 ≤ k) :
    IsDyadicMod2pi (mobiusPhaseCoeff S f) := by
  -- Descend at S: gets level (k - |S|) = k - (k - 1) = 1.
  have h_S_card_lt : S.card < k := by omega
  have h_descent :=
    diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
      f h_hier h_S_card_lt
  have h_level : k - S.card = 1 := by omega
  rw [h_level] at h_descent
  -- Now: D_{funcDerivPhaseSubset S f} at level 1.
  -- Apply the level-1 base case at v = 0.
  unfold mobiusPhaseCoeff
  exact isDyadicMod2pi_of_level_one_diagonal h_descent

/-! ## Möbius coefficient is dyadic mod 2π (any `|S| < k`)

One might choose any `T ⊇ S` with `|T| = k - 1`. The
descent at `T` gives level 1. The base case + the relation
`(Δ_T f)(0) = (Δ_{T\S} (Δ_S f))(0)` connects the higher-order Möbius
coefficient to the lower-order one — but the connection runs through
an alternating sum of `(Δ_S f)(1_R)` values, which doesn't directly
yield `(Δ_S f)(0)`. So this approach does not handle the lower-`|S|`
case.

The lower-`|S|` case is `mobiusCoeff_dyadic_mod_2pi_level_k` in
`CGKReverseGeneral.lean`, proved by a different argument (the mod-2
identity `Δ_i Δ_i g = -2 · Δ_i g` with halving). -/

/-! ## Vanishing for `|S| ≥ k + 1`

For `|S| ≥ k + 1`, the iterated discrete derivative
`funcDerivPhaseSubset S f` is **identically zero as a function**.

Reasoning: at the deepest descent (|S'| = k - 1) we land at level 1,
which is a (dyadic) phased Pauli with `p.X = 0` (forced by the diagonal
hypothesis). The phase function is affine-linear in `v` (constant
plus a `π · (p.Z · v mod 2)` term). One more discrete derivative
produces a constant function. One more produces the zero function.

For technical reasons (the descent theorem requires `|S| < k`), we
prove the strict-vanishing version: for `|S| > k + 1` the function
vanishes identically. The boundary cases `|S| = k` and `|S| = k + 1`
give a constant and a zero function respectively.

The clean statement at the function level:

* For `|S| > k`, `funcDerivPhaseSubset S f` is constant as a function
  of `v` (a single constant, depending on `S` and `f`).
* For `|S| > k + 1`, `funcDerivPhaseSubset S f = 0` as a function.

The helper lemmas below record that `funcDerivPhase i` of a constant
function is zero. The vanishing theorem itself is
`funcDerivPhaseSubset_vanish_mod_2pi_of_card_gt_level` in
`CGKReverseVanish.lean`. -/

/-- For `i : Fin n` and `c : ℝ`, `funcDerivPhase i (fun _ => c) = fun _ => 0`. -/
private theorem funcDerivPhase_const (i : Fin n) (c : ℝ) :
    funcDerivPhase i (fun _ => c) = fun _ => 0 := by
  funext v
  simp [funcDerivPhase_apply]

/-- For a non-empty `S`, `funcDerivPhaseSubset S (fun _ => 0) = fun _ => 0`. -/
private theorem funcDerivPhaseSubset_zero (S : Finset (Fin n)) :
    funcDerivPhaseSubset S (fun _ : (Fin n → ZMod 2) => (0 : ℝ)) =
      (fun _ => 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [funcDerivPhaseSubset_empty]
  | @insert i S hi ih =>
      rw [funcDerivPhaseSubset_insert hi, ih]
      exact funcDerivPhase_const i 0

/-! ## Remarks on the general case

The general Möbius coefficient dyadicity for `|S| < k - 1` (i.e., not
just the top-level case) needs the stronger statement

```
∀ g, IsCliffordHierarchyDyadic m (diagonalGateEquiv g) → ∀ v, IsDyadicMod2pi (g v)
```

The natural induction on `m` runs into a missing anchor at `v = 0`:
at level `m + 1`, the descent gives `Δ_i g` dyadic for all `v`, all `i`,
which determines `g(v) - g(0)` for all `v`, but does not pin down
`g(0)` itself. With `g(0)` taken as a hypothesis, the statement is
`anchoredLevelDyadic_of_one_le` in `CGKReverseGeneral.lean`.

The top-level case `mobiusPhaseCoeff_dyadic_mod_2pi_top` certifies the
**deepest** Möbius coefficient — the one of size `k - 1`, which
corresponds to the highest-degree monomial in the polynomial witness.

The vanishing for `|S| ≥ k + 1` — `funcDerivPhaseSubset S f v` is an
integer multiple of `2π` for every `v` — follows from the level-1 phase
function being affine-linear in `v` modulo 2π, via
`Pauli_X_zero_of_diagonal_phasedPauli` and the formula
`g(v) = arg(α) + π · (p.Z · v mod 2)`. It is proved in
`CGKReverseVanish.lean`.
-/

end FTQCLib.Hilbert

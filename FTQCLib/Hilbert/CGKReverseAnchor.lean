/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseDyadic
import FTQCLib.Hierarchy.BooleanMobius

set_option linter.unusedSectionVars false

/-! # CGK reverse — the "anchor" structural lemmas

This file extends `CGKReverseDyadic.lean` with the structural results
needed to bridge from "Möbius coefficients dyadic" to "phase function
dyadic at every input".

## Background

The descent theorem
`diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`
plus the level-1 base case
`isDyadicMod2pi_of_level_one_diagonal` deliver dyadicity of the
**top-level** Möbius coefficient `(Δ_S g)(0)` for `|S| = k − 1` at
level `k` of `IsCliffordHierarchyDyadic`.

For the polynomial-witness assembly, we need
the **point-wise** dyadicity of `g(v)` itself, not just of its
top-level Möbius coefficient. Möbius inversion
(`BooleanMobius.eq_sum_mobiusCoeff`) gives the bridge:

```
g(v) = Σ_{S ⊆ supp v} (Δ_S g)(0)
```

so dyadicity of every `(Δ_S g)(0)` (with `S ⊆ supp v`) plus closure
of `IsDyadicMod2pi` under addition implies dyadicity of `g(v)`.

This file delivers the closure machinery and uses it for the cases
where descent does close the dyadicity of all Möbius coefficients
involved.

## What this file delivers

* **Closure of `IsDyadicMod2pi` under addition, negation, and finite
  sums.** The key technical lemma is `IsDyadicMod2pi.add`, lifting
  both witnesses to a common precision and adding the residues.

* **Level-1 strengthening (`isDyadicMod2pi_of_level_one_diagonal_all_v`).**
  At level 1 of the dyadic hierarchy, the diagonal `D_g` has `g(v)`
  dyadic mod 2π for **every** `v` (not just `v = 0`). The argument
  reads `g(v) ≡ arg(α) + π · (p.Z · v mod 2) (mod 2π)` from the
  phased-Pauli decomposition; both summands are dyadic mod 2π.

* **Level-1 iterated dyadicity
  (`funcDerivPhaseSubset_dyadic_of_level_one`).** At level 1, every
  iterated derivative `(Δ_T g)(v)` is dyadic mod 2π. Proof: induction
  on `|T|` using closure of `IsDyadicMod2pi` under subtraction.

* **Möbius-via-anchor (`isDyadicMod2pi_of_mobius_dyadic`).** Given all
  `(Δ_S g)(0)` dyadic mod 2π for `S ⊆ supp v`, conclude `g(v)` dyadic
  mod 2π. This is the structural bridge used by all higher-level
  reconstructions.

* **Level-2 Möbius coefficient dyadicity
  (`mobiusCoeff_dyadic_mod_2pi_level_two`).** At level 2 of the
  dyadic hierarchy, every non-empty Möbius coefficient `(Δ_S g)(0)`
  is dyadic mod 2π. (`|S| = 1` is direct by descent; `|S| ≥ 2` reduces
  to level-1 iterated dyadicity applied to a single descent step.)

* **Level-2 conditional closure (`isDyadicMod2pi_of_level_two_diagonal_anchored`).**
  At level 2 of the dyadic hierarchy with `g(0)` dyadic, `g(v)` is
  dyadic for every `v`. Combines the Möbius coefficient dyadicity
  with `isDyadicMod2pi_of_mobius_dyadic`.

## Higher levels

The level-`k ≥ 3` case requires Möbius-coefficient dyadicity at
non-top-level `|S| < k − 1`. Descent at `|T| ≤ k − 1` lands the
iterated derivative at level `≥ 2`, where the closure proved here does
not apply without recursing on the conclusion itself. The statement is
recorded as `AnchoredLevelDyadic`; it is proved for every
`k ≥ 1` as `anchoredLevelDyadic_of_one_le` in
`CGKReverseLevel3.lean` / `CGKReverseGeneral.lean`, using the mod-2
identity `Δ_i Δ_i g = -2 · Δ_i g` together with halving.

The level-2 closure presented here covers the first non-trivial step
beyond `mobiusPhaseCoeff_dyadic_mod_2pi_top`.

## Anchors

* CGK 2017 (arXiv:1608.06596) §III, Lemma 2 eq (50)–(51) for
  Möbius-coefficient dyadicity.
* Rota 1964 *On the foundations of combinatorial theory I, theory
  of Möbius functions* for the Möbius-inversion identity.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase BooleanMobius

variable {n : ℕ}

/-! ## Closure of `IsDyadicMod2pi` under addition

The predicate `IsDyadicMod2pi` is closed under negation, addition,
and finite sums. The proofs follow the pattern of
`IsDyadicScalar.mul` in `HierarchyDyadic.lean`: lift both witnesses
to a common precision, then sum the residues, absorbing the
wraparound via `2π`-periodicity. -/

/-- **Closure of `IsDyadicMod2pi` under addition.** Strategy: convert
to dyadic-scalar form via `Complex.exp(I · x)` and use
`IsDyadicScalar.mul`, then read off via `isDyadicMod2pi_of_dyadicScalar_arg`. -/
theorem IsDyadicMod2pi.add {x y : ℝ}
    (hx : IsDyadicMod2pi x) (hy : IsDyadicMod2pi y) :
    IsDyadicMod2pi (x + y) := by
  -- Construct dyadic units exp(I · x) and exp(I · y).
  obtain ⟨m₁, c₁, k₁, hx_eq⟩ := hx
  obtain ⟨m₂, c₂, k₂, hy_eq⟩ := hy
  -- exp(I · x) has dyadic unit form.
  have hex_ne : Complex.exp (Complex.I * (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hey_ne : Complex.exp (Complex.I * (y : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hex_dy : IsDyadicScalar (Units.mk0 _ hex_ne) := by
    refine ⟨m₁, c₁, ?_⟩
    rw [Units.val_mk0]
    -- Need: exp(I · x) = exp(I · 2π · c₁.val / 2^m₁).
    -- From hx_eq: x = 2π · c₁.val / 2^m₁ + 2π · k₁.
    -- So exp(I · x) = exp(I · 2π · c₁.val / 2^m₁) · exp(I · 2π · k₁)
    --             = exp(I · 2π · c₁.val / 2^m₁) · 1.
    have h_diff : Complex.I * (x : ℂ)
        = Complex.I * (((2 * Real.pi * (c₁.val : ℝ) / (2 : ℝ) ^ m₁) : ℝ) : ℂ) +
            (k₁ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have h : (x : ℂ) =
          (((2 * Real.pi * (c₁.val : ℝ) / (2 : ℝ) ^ m₁) : ℝ) : ℂ) +
            (((2 * Real.pi * (k₁ : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hx_eq
      have h2 : (((2 * Real.pi * (k₁ : ℝ)) : ℝ) : ℂ)
              = (k₁ : ℂ) * (2 * (Real.pi : ℂ)) := by push_cast; ring
      rw [h, h2]
      ring
    rw [h_diff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hey_dy : IsDyadicScalar (Units.mk0 _ hey_ne) := by
    refine ⟨m₂, c₂, ?_⟩
    rw [Units.val_mk0]
    have h_diff : Complex.I * (y : ℂ)
        = Complex.I * (((2 * Real.pi * (c₂.val : ℝ) / (2 : ℝ) ^ m₂) : ℝ) : ℂ) +
            (k₂ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have h : (y : ℂ) =
          (((2 * Real.pi * (c₂.val : ℝ) / (2 : ℝ) ^ m₂) : ℝ) : ℂ) +
            (((2 * Real.pi * (k₂ : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hy_eq
      have h2 : (((2 * Real.pi * (k₂ : ℝ)) : ℝ) : ℂ)
              = (k₂ : ℂ) * (2 * (Real.pi : ℂ)) := by push_cast; ring
      rw [h, h2]
      ring
    rw [h_diff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- Product is dyadic.
  have h_prod_dy := IsDyadicScalar.mul hex_dy hey_dy
  -- The product's complex value is exp(I · (x + y)).
  have h_prod_val :
      ((Units.mk0 _ hex_ne * Units.mk0 _ hey_ne : ℂˣ) : ℂ)
        = Complex.exp (Complex.I * ((x + y : ℝ) : ℂ)) := by
    simp only [Units.val_mul, Units.val_mk0]
    rw [show Complex.I * ((x + y : ℝ) : ℂ) =
            Complex.I * (x : ℂ) + Complex.I * (y : ℂ) from by push_cast; ring]
    rw [Complex.exp_add]
  exact isDyadicMod2pi_of_dyadicScalar_arg h_prod_dy h_prod_val

/-- Zero is dyadic mod 2π. (Restatement for use in finite-sum
induction.) -/
theorem IsDyadicMod2pi.zero : IsDyadicMod2pi 0 := isDyadicMod2pi_zero

/-- **Closure of `IsDyadicMod2pi` under negation.** -/
theorem IsDyadicMod2pi.neg {x : ℝ} (hx : IsDyadicMod2pi x) :
    IsDyadicMod2pi (-x) := by
  obtain ⟨m, c, k, hx_eq⟩ := hx
  -- Two cases: c = 0 (trivial, -x is integer multiple of 2π) or c ≠ 0.
  by_cases hc : c = 0
  · refine ⟨m, 0, -k, ?_⟩
    subst hc
    rw [hx_eq]
    have h_val_zero : ZMod.val (0 : ZMod (2 ^ m)) = 0 := ZMod.val_zero
    rw [h_val_zero]
    push_cast
    ring
  · -- -c.val in ZMod (2^m): (-c).val = 2^m - c.val (when c ≠ 0).
    refine ⟨m, -c, -k - 1, ?_⟩
    rw [hx_eq]
    have h_neg_val : (-c).val = 2 ^ m - c.val := by
      rw [ZMod.neg_val]
      simp [hc]
    rw [h_neg_val]
    have hc_lt : c.val < 2 ^ m := ZMod.val_lt c
    have hc_le : c.val ≤ 2 ^ m := le_of_lt hc_lt
    have h_cast_sub : ((2 ^ m - c.val : ℕ) : ℝ) = (2 ^ m : ℝ) - (c.val : ℝ) := by
      have h := Nat.cast_sub (R := ℝ) hc_le
      push_cast at h
      exact h
    rw [h_cast_sub]
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have h_pow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h_pow_pos
    push_cast
    field_simp
    ring

/-- **Closure of `IsDyadicMod2pi` under subtraction.** -/
theorem IsDyadicMod2pi.sub {x y : ℝ}
    (hx : IsDyadicMod2pi x) (hy : IsDyadicMod2pi y) :
    IsDyadicMod2pi (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- **Closure of `IsDyadicMod2pi` under finite sums.** -/
theorem IsDyadicMod2pi.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (h : ∀ i ∈ s, IsDyadicMod2pi (f i)) :
    IsDyadicMod2pi (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact IsDyadicMod2pi.zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply IsDyadicMod2pi.add
      · exact h i (Finset.mem_insert_self _ _)
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ## Level-1 strengthening: dyadicity at every input

`isDyadicMod2pi_of_level_one_diagonal` shows `g(0)` dyadic
for a level-1 dyadic diagonal. We extend to all `v`.

The argument: at level 1, the diagonal phased-Pauli witness gives
`exp(I · g(v)) = α · (-1)^{p.Z · v}` with `p.X = 0`. Both `α` and
`(-1)^{p.Z · v}` are dyadic units; their product is dyadic by
`IsDyadicScalar.mul`. Reading off via
`isDyadicMod2pi_of_dyadicScalar_arg` gives `g(v)` dyadic mod 2π. -/

/-- **Level-1 strengthening.** At level 1 of the dyadic hierarchy
with diagonal `D_g`, the phase function `g` is dyadic mod 2π at
every input. -/
theorem isDyadicMod2pi_of_level_one_diagonal_all_v
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g))
    (v : Fin n → ZMod 2) :
    IsDyadicMod2pi (g v) := by
  generalize hk_eq : (1 : ℕ) = klvl at h_hier
  cases h_hier with
  | base hU =>
      obtain ⟨α, p, hα_dy, hα⟩ := hU
      have hpX : p.X = 0 :=
        Pauli_X_zero_of_diagonal_phasedPauli rfl hα
      -- Apply both forms at the basis vector |v⟩.
      have h_apply :
          (diagonalGateEquiv g) (computational v) =
            (α : ℂ) • (pauliOperator p) (computational v) := by
        have h := congrArg
          (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L (computational v))
          hα
        simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
        exact h
      rw [diagonalGateEquiv_apply, diagonalGate_computational,
          pauliOperator_computational, hpX, add_zero] at h_apply
      have h_eval :
          (Complex.exp (Complex.I * (g v : ℂ)) • computational v) v =
            ((α : ℂ) • (-1 : ℂ) ^ (zDotVal p v) • computational v) v :=
        congrFun h_apply v
      simp only [Pi.smul_apply, computational_self, smul_eq_mul, mul_one]
        at h_eval
      -- h_eval : exp(I · g v) = α · (-1)^{p.Z · v}.
      -- Identify the product α · (-1)^{p.Z · v} as a dyadic unit scalar.
      have hα_unit : IsDyadicScalar α := hα_dy
      have h_neg_one_ne : ((-1 : ℂ)) ^ (zDotVal p v) ≠ 0 :=
        pow_ne_zero _ (by norm_num)
      have h_neg_one_dy :
          IsDyadicScalar (Units.mk0 ((-1 : ℂ)) (by norm_num) ^ (zDotVal p v)) := by
        have hne1 : ((-1 : ℂ)) ^ zDotVal p v ≠ 0 :=
          pow_ne_zero _ (by norm_num)
        have h_dy := isDyadicScalar_neg_one_pow (zDotVal p v) hne1
        have h_unit_eq :
            (Units.mk0 ((-1 : ℂ)) (by norm_num : ((-1 : ℂ) : ℂ) ≠ 0))
                ^ (zDotVal p v) =
              Units.mk0 ((-1 : ℂ) ^ zDotVal p v) hne1 := by
          apply Units.ext
          simp
        rw [h_unit_eq]
        exact h_dy
      have h_prod_dy := IsDyadicScalar.mul hα_unit h_neg_one_dy
      have h_prod_val :
          ((α * Units.mk0 ((-1 : ℂ)) (by norm_num : ((-1 : ℂ) : ℂ) ≠ 0)
              ^ (zDotVal p v) : ℂˣ) : ℂ)
            = Complex.exp (Complex.I * (g v : ℂ)) := by
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
        rw [← h_eval]
      -- Apply isDyadicMod2pi_of_dyadicScalar_arg.
      exact isDyadicMod2pi_of_dyadicScalar_arg h_prod_dy h_prod_val
  | @step kpred _ h =>
      have hk0 : kpred = 0 := by omega
      subst hk0
      cases h 0

/-! ## Level-1 iterated dyadicity

For any `T`, the iterated discrete derivative `(Δ_T g)(v)` at level 1
is dyadic mod 2π for every `v`. Proof by induction on `|T|` using
closure of `IsDyadicMod2pi` under subtraction. -/

/-- **Level-1 iterated dyadicity.** At level 1 of the dyadic
hierarchy, every iterated discrete derivative `(Δ_T g)(v)` is dyadic
mod 2π. -/
theorem funcDerivPhaseSubset_dyadic_of_level_one
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g))
    (T : Finset (Fin n)) (v : Fin n → ZMod 2) :
    IsDyadicMod2pi (funcDerivPhaseSubset T g v) := by
  classical
  induction T using Finset.induction_on generalizing v with
  | empty =>
      rw [funcDerivPhaseSubset_empty]
      exact isDyadicMod2pi_of_level_one_diagonal_all_v h_hier v
  | @insert i T hi ih =>
      rw [funcDerivPhaseSubset_insert hi, funcDerivPhase_apply]
      exact IsDyadicMod2pi.sub (ih _) (ih _)

/-! ## Möbius-via-anchor: dyadicity from Möbius coefficients

The structural bridge: if every Möbius coefficient
`(Δ_S g)(0)` for `S ⊆ supp v` is dyadic mod 2π, then `g(v)` itself
is dyadic mod 2π. -/

/-- The polymorphic `funcDerivSubset` and the real-valued
`funcDerivPhaseSubset` agree on real-valued phase functions. -/
private theorem funcDerivSubset_eq_funcDerivPhaseSubset
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

/-- **Möbius-via-anchor.** If every Möbius coefficient
`(Δ_S g)(0)` for `S ⊆ supp v` is dyadic mod 2π, then `g(v)` is dyadic
mod 2π. -/
theorem isDyadicMod2pi_of_mobius_dyadic
    {g : (Fin n → ZMod 2) → ℝ} (v : Fin n → ZMod 2)
    (h : ∀ S ∈ (FTQCLib.Codes.supp v).powerset,
        IsDyadicMod2pi (funcDerivPhaseSubset S g 0)) :
    IsDyadicMod2pi (g v) := by
  have h_sum :
      g v = ∑ S ∈ (FTQCLib.Codes.supp v).powerset, funcDerivSubset S g 0 := by
    have h := eq_sum_mobiusCoeff g v
    unfold mobiusCoeff at h
    exact h
  rw [h_sum]
  apply IsDyadicMod2pi.sum
  intro S hS
  rw [funcDerivSubset_eq_funcDerivPhaseSubset]
  exact h S hS

/-! ## Iterated descent dyadicity at all `v` (top-level case)

For `|S| = k − 1` at `IsCliffordHierarchyDyadic k (D_g)`, every value
`(Δ_S g)(v)` is dyadic mod 2π. (Descent gives level 1, then the level-1
strengthening applies pointwise.) -/

/-- **Iterated descent dyadicity at all `v`.** For `|S| = k − 1` at
`IsCliffordHierarchyDyadic k (D_g)`, every value `(Δ_S g)(v)` is
dyadic mod 2π. -/
theorem funcDerivPhaseSubset_dyadic_all_v_top_level
    {k : ℕ} {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    {S : Finset (Fin n)} (h_card : S.card = k - 1) (h_k_pos : 1 ≤ k) :
    ∀ v, IsDyadicMod2pi (funcDerivPhaseSubset S g v) := by
  intro v
  have h_S_card_lt : S.card < k := by omega
  have h_descent :=
    diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
      g h_hier h_S_card_lt
  have h_level : k - S.card = 1 := by omega
  rw [h_level] at h_descent
  exact isDyadicMod2pi_of_level_one_diagonal_all_v h_descent v

/-! ## Level-2 Möbius coefficient dyadicity

For `D_g` at level 2 of the dyadic hierarchy, every non-empty Möbius
coefficient `(Δ_S g)(0)` is dyadic mod 2π.

Argument by `|S|` case analysis:
* `|S| = 1`: descent gives `D_{Δ_S g}` at level 1; apply
  `isDyadicMod2pi_of_level_one_diagonal_all_v` at `v = 0`.
* `|S| ≥ 2`: pick `i ∈ S`, write `S = insert i T` with `|T| ≥ 1`.
  Then `(Δ_S g) = Δ_T (Δ_i g) = funcDerivPhaseSubset T (funcDerivPhase i g)`.
  Descent at `{i}` gives `D_{Δ_i g}` at level 1. By level-1 iterated
  dyadicity, `(Δ_T (Δ_i g))(v)` is dyadic mod 2π for every `v` (in
  particular `v = 0`). -/

/-- **Level-2 Möbius coefficient dyadicity.** Every non-empty
Möbius coefficient `(Δ_S g)(0)` at level 2 of the dyadic hierarchy is
dyadic mod 2π. -/
theorem mobiusCoeff_dyadic_mod_2pi_level_two
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 2 (diagonalGateEquiv g))
    {S : Finset (Fin n)} (h_nonempty : S.Nonempty) :
    IsDyadicMod2pi (funcDerivPhaseSubset S g 0) := by
  classical
  -- Pick i ∈ S; write S = insert i T with T = S.erase i.
  obtain ⟨i, hi⟩ := h_nonempty
  set T := S.erase i with hT_def
  have hi_notin_T : i ∉ T := Finset.notMem_erase i S
  have h_S_eq : S = insert i T := by
    rw [hT_def, Finset.insert_erase hi]
  -- By `funcDerivPhaseSubset_insert`,
  --   funcDerivPhaseSubset (insert i S) f = funcDerivPhase i (funcDerivPhaseSubset S f),
  -- so Δ_{insert i T} g = Δ_i (Δ_T g) ("outer i, inner T").
  -- Equivalently by commutativity, we can also write this as Δ_T (Δ_i g),
  -- using funcDerivPhase_comm to swap.
  --
  -- For our proof, we want: Δ_T (Δ_i g) which is "outer T, inner i".
  -- The descent applies to Δ_i g (taking g and applying Δ_i).
  -- Then iterated dyadicity of Δ_T applied to the level-1 function Δ_i g.
  rw [h_S_eq]
  rw [funcDerivPhaseSubset_insert hi_notin_T]
  -- Goal: IsDyadicMod2pi (funcDerivPhase i (funcDerivPhaseSubset T g) 0).
  -- We want to swap to funcDerivPhaseSubset T (funcDerivPhase i g) 0.
  -- These are equal by commutativity (induction on T).
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
  -- Apply iterated dyadicity at level 1 (for Δ_i g).
  -- We need D_{Δ_i g} at level 1.
  have h_descent_i :
      IsCliffordHierarchyDyadic 1
        (diagonalGateEquiv (funcDerivPhase i g)) := by
    -- Use descent at {i}: S.card = 1 < 2, level 2 - 1 = 1.
    have h_card_lt : ({i} : Finset (Fin n)).card < 2 := by
      rw [Finset.card_singleton]; omega
    have h := diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
      g h_hier h_card_lt
    have h_level : (2 : ℕ) - ({i} : Finset (Fin n)).card = 1 := by
      rw [Finset.card_singleton]
    rw [h_level] at h
    rw [funcDerivPhaseSubset_singleton] at h
    exact h
  exact funcDerivPhaseSubset_dyadic_of_level_one h_descent_i T 0

/-! ## Level-2 conditional closure

At level 2 of the dyadic hierarchy with `g(0)` dyadic, `g(v)` is
dyadic for every `v`. Combine Möbius-via-anchor with level-2
coefficient dyadicity. -/

/-- **Level-2 conditional closure.** At level 2 of the dyadic
hierarchy with `g(0)` dyadic mod 2π, `g(v)` is dyadic mod 2π for
every `v`. -/
theorem isDyadicMod2pi_of_level_two_diagonal_anchored
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 2 (diagonalGateEquiv g))
    (h_zero : IsDyadicMod2pi (g 0))
    (v : Fin n → ZMod 2) :
    IsDyadicMod2pi (g v) := by
  apply isDyadicMod2pi_of_mobius_dyadic
  intro S hS
  -- Case on whether S is empty.
  by_cases h_empty : S = ∅
  · rw [h_empty, funcDerivPhaseSubset_empty]
    exact h_zero
  · exact mobiusCoeff_dyadic_mod_2pi_level_two h_hier
      (Finset.nonempty_iff_ne_empty.mpr h_empty)

/-! ## Tight-hierarchy unconditional level-2 closure

For the **tight** hierarchy `IsCliffordHierarchyTight`, `g(0)` is
automatically dyadic at level 1 (in fact ∈ {0, π}). At level 2 of the
tight hierarchy, the constraint forces the conjugates to be tight
level 1, but the operator's eigenvalue at `|0⟩` is not thereby
constrained dyadic.

For the LOOSE dyadic hierarchy, the same obstruction applies: `g(0)`
at level 2 is not automatic.

So the **unconditional** level-2 statement does not follow from this
argument in either version (and is false for the loose hierarchy). The
conditional version above is the level-2 result. -/

/-! ## The statement at level ≥ 3

For `D_g` at level `k ≥ 3` of the dyadic hierarchy, the analogous
result requires Möbius coefficient dyadicity at `|S| ≤ k − 2` (not
just `|S| = k − 1` for the top-level case). The descent gives
`D_{Δ_S g}` at level `k − |S| ≥ 2`, where the analogous closure
would have to be applied recursively — but the recursion's hypothesis
`(Δ_S g)(0)` dyadic at level `k − |S| ≥ 2` is itself what is to be
proved.

Two direct approaches do not close this:

* **Structural unpacking** of the level-`m` predicate to extract
  `g(0)` as an explicit operator eigenvalue. At level 1 this is direct
  (the phased-Pauli witness gives `g(0) = arg α`, with `α` dyadic). At
  level `m ≥ 2`, the recursive hierarchy gives derivative info
  (`Δ_i g` at level `m − 1`), not point-value info at `v = 0`.

* **A single-step bridge for arbitrary Pauli** (not just `paulix i`).
  `conjEquiv_diagonalGateEquiv_general` in `CGKForward.lean` shows
  that the general-Pauli conjugate has a trailing X-Pauli, so the
  operator-side descent yields derivative information, not point-value
  information at non-zero `v`.

The proof for all levels (`CGKReverseLevel3.lean`,
`CGKReverseGeneral.lean`) instead uses the mod-2 identity
`Δ_i Δ_i g = -2 · Δ_i g` together with halving. -/

/-- **The level-`k` anchored dyadicity statement.** For every `g`,
`IsCliffordHierarchyDyadic k (D_g)` plus `IsDyadicMod2pi (g 0)`
implies `∀ v, IsDyadicMod2pi (g v)`. Proved here for `k = 1, 2`; the
general case is `anchoredLevelDyadic_of_one_le` in
`CGKReverseGeneral.lean`. -/
def AnchoredLevelDyadic (k : ℕ) : Prop :=
  ∀ (g : (Fin n → ZMod 2) → ℝ),
    IsCliffordHierarchyDyadic k (diagonalGateEquiv g) →
    IsDyadicMod2pi (g 0) →
    ∀ v, IsDyadicMod2pi (g v)

/-- For `k = 1`, the anchored dyadicity statement is trivially TRUE (and
in fact the `IsDyadicMod2pi (g 0)` hypothesis is redundant, since the
level-1 base case forces it). -/
theorem anchoredLevelDyadic_one :
    AnchoredLevelDyadic (n := n) 1 := by
  intro g h_hier _h_zero v
  exact isDyadicMod2pi_of_level_one_diagonal_all_v h_hier v

/-- For `k = 2`, the anchored dyadicity statement is TRUE (proven above). -/
theorem anchoredLevelDyadic_two :
    AnchoredLevelDyadic (n := n) 2 := by
  intro g h_hier h_zero v
  exact isDyadicMod2pi_of_level_two_diagonal_anchored h_hier h_zero v

/-! ## Summary

This file proves the level-1 and level-2 cases of CGK reverse on the
dyadic side.

| Level | Statement | Status |
|---|---|---|
| `k = 1` | `∀ v, IsDyadicMod2pi (g v)` unconditional | proved here |
| `k = 2` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | proved here |
| `k = 2` | `∀ v, IsDyadicMod2pi (g v)` unconditional | false (loose), open (tight) |
| `k ≥ 3` | `IsDyadicMod2pi (g 0) → ∀ v, IsDyadicMod2pi (g v)` | `CGKReverseGeneral.lean` |

The level-2 conditional closure is the first non-trivial step beyond
`mobiusPhaseCoeff_dyadic_mod_2pi_top` (which handles only the
top-level `|S| = k − 1` case at any level `k`). The additional
ingredient at level `k ≥ 3` is the `|S| < k − 1` Möbius coefficient
dyadicity, proved in `CGKReverseGeneral.lean`.
-/

end FTQCLib.Hilbert

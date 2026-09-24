/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Hierarchy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedSectionVars false

/-! # The operational Clifford hierarchy with dyadic-phase restriction

The operational Clifford hierarchy with dyadic-phase restriction. The
base case `α ∈ ℂˣ` is constrained to be a `2^m'`-th root of unity for
some `m'`, matching the physical Clifford hierarchy of gates expressible
in a finite-precision polynomial framework. Gottesman-Chuang 1999
(arXiv:quant-ph/9908010) originally defined the hierarchy without this
restriction; CGK 2017 (arXiv:1608.06596) §III makes the restriction
implicit by working in the polynomial framework. We package the
restriction explicitly here.

## Motivation

`FTQCLib/Hilbert/Hierarchy.lean` defines `IsPhasedPauli U` as the existence
of *any* unit scalar `α : ℂˣ` and Pauli `p` with
`U.toLinearMap = α • pauliOperator p`. The polynomial-phase framework
of `FTQCLib.Hierarchy.DiagPhase`, however, produces phases of the form
`exp(I · 2π · c.val / 2^m)` with `c : ZMod (2^m)` — i.e., the only
phases representable are `2^m'`-th roots of unity. Consequently, the
operational predicate `IsCliffordHierarchy` is *strictly broader* than
the polynomial-framework predicate: an operator
`exp(I · π · √2) • pauliOperator p` is in `IsCliffordHierarchy 1` but
admits no finite-precision polynomial encoding.

To state the CGK reverse equivalence rigorously, we tighten the base
case to dyadic phases and propagate the restriction through the
recursive hierarchy. The tightened predicate is
`IsCliffordHierarchyDyadic k U`.

## What this file provides

* **`IsDyadicScalar α`** — `α` is a `2^m'`-th root of unity for some
  `m'`. Existential closure (over `m'`) of `IsDyadicPhase α m'` from
  `CGKReverse.lean`.
* **`IsPhasedPauliDyadic U`** — like `IsPhasedPauli` but with `α`
  constrained dyadic.
* **`IsCliffordHierarchyDyadic k U`** — recursive hierarchy with
  `IsPhasedPauliDyadic` at the base.
* **`IsCliffordHierarchyDyadic.toCliffordHierarchy`** — the tightened
  predicate implies the loose one.
* **Monotonicity** lemmas paralleling `Hierarchy.lean`:
  `two_of_one`, `succ`, `mono`.
* **Pauli inclusion**: every `pauliEquiv p` is in
  `IsCliffordHierarchyDyadic 1` with witness `α = 1` (dyadic with
  `m' = 0` or `m' = 1`, `c = 0`).

## Anchor

Gottesman-Chuang 1999 (arXiv:quant-ph/9908010); CGK 2017
(arXiv:1608.06596) §III.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-! ## Dyadic unit scalars -/

/-- A unit complex scalar `α : ℂˣ` is **dyadic** if it is a `2^m'`-th
root of unity for some `m'`. Concretely, there exist `m' : ℕ` and
`c : ZMod (2^m')` with `(α : ℂ) = exp(I · 2π · c.val / 2^m')`.

This is the existential closure (over the precision `m'`) of the
predicate `IsDyadicPhase` defined in `FTQCLib.Hilbert.CGKReverse`. -/
def IsDyadicScalar (α : ℂˣ) : Prop :=
  ∃ (m' : ℕ) (c : ZMod (2 ^ m')),
    (α : ℂ) = Complex.exp (Complex.I *
      (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m') : ℝ) : ℂ))

/-- The unit `1 : ℂˣ` is dyadic, witnessed by `m' = 0`, `c = 0`.

For `m' = 0`, `2^0 = 1`, so `ZMod 1 ≃ Unit` (singleton). The unique
element has `.val = 0`, and the RHS exponent is `I · (0 / 1) = 0`, so
`exp = 1`. -/
theorem isDyadicScalar_one : IsDyadicScalar (1 : ℂˣ) := by
  refine ⟨0, 0, ?_⟩
  simp only [Units.val_one, ZMod.val_zero, Nat.cast_zero, pow_zero,
    mul_zero, zero_div, ofReal_zero,
    Complex.exp_zero]

/-- The unit `-1 : ℂˣ` is dyadic, witnessed by `m' = 1`, `c = 1`. -/
theorem isDyadicScalar_neg_one : IsDyadicScalar (-1 : ℂˣ) := by
  refine ⟨1, 1, ?_⟩
  have hval : (1 : ZMod (2 ^ 1)).val = 1 := by decide
  rw [hval]
  -- Goal: ((-1 : ℂˣ) : ℂ) = exp(I · (((2π · ↑1 / 2^1) : ℝ) : ℂ)).
  have hsimp : (((2 * Real.pi * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 1) : ℝ) : ℂ)
                = (Real.pi : ℂ) := by
    push_cast
    ring
  rw [hsimp]
  rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I from by ring,
      Complex.exp_pi_mul_I]
  simp

/-- The signed unit `(-1)^k` (for `k : ℕ`) is dyadic, witnessed by
`m' = 1`, `c = k mod 2`. -/
theorem isDyadicScalar_neg_one_pow (k : ℕ)
    (h : ((-1 : ℂ) ^ k) ≠ 0) :
    IsDyadicScalar (Units.mk0 ((-1 : ℂ) ^ k) h) := by
  refine ⟨1, (k : ZMod (2 ^ 1)), ?_⟩
  simp only [Units.val_mk0]
  have h_val : ((k : ZMod (2 ^ 1))).val = k % 2 := by
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    rw [h2]
    exact ZMod.val_natCast 2 k
  rw [h_val]
  -- Goal: (-1)^k = exp(I · (2π · (k % 2) / 2^1 : ℝ)).
  -- And (-1)^k = (-1)^(k % 2), then we identify (-1)^(k % 2) = exp(I · π · (k % 2)).
  have h_pow_mod : ((-1 : ℂ))^k = ((-1 : ℂ))^(k % 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul]
    have hsq : ((-1 : ℂ))^2 = 1 := by norm_num
    rw [hsq, one_pow, one_mul]
  rw [h_pow_mod]
  have h_simp_real :
      (((2 * Real.pi * ((k % 2 : ℕ) : ℝ) / (2 : ℝ) ^ 1) : ℝ) : ℂ)
        = (Real.pi : ℂ) * ((k % 2 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [h_simp_real]
  rw [show Complex.I * ((Real.pi : ℂ) * ((k % 2 : ℕ) : ℂ))
        = ((k % 2 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-! ## Dyadic-phased Paulis (the tightened base level) -/

/-- `IsPhasedPauliDyadic U` says that the underlying linear map of `U`
coincides with `α · pauliOperator p` for some Pauli `p : Pauli n` and
some **dyadic** unit scalar `α : ℂˣ` (i.e., a `2^m'`-th root of unity
for some `m'`).

This is the tightened version of `IsPhasedPauli` — it carves out the
subset of phased Paulis whose global phase is representable in the
finite-precision polynomial framework. -/
def IsPhasedPauliDyadic (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : Prop :=
  ∃ (α : ℂˣ) (p : Pauli n),
    IsDyadicScalar α ∧
    U.toLinearMap = (α : ℂ) • (pauliOperator p)

/-- A dyadic phased Pauli is in particular a phased Pauli. -/
theorem IsPhasedPauliDyadic.toIsPhasedPauli
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (h : IsPhasedPauliDyadic U) :
    IsPhasedPauli U := by
  obtain ⟨α, p, _, hα⟩ := h
  exact ⟨α, p, hα⟩

/-- The unsigned Pauli equivalence `pauliEquiv p` is a dyadic phased
Pauli (with phase `1`, which is dyadic with witness `m' = 0`). -/
theorem isPhasedPauliDyadic_pauliEquiv (p : Pauli n) :
    IsPhasedPauliDyadic (pauliEquiv p) := by
  refine ⟨1, p, isDyadicScalar_one, ?_⟩
  apply LinearMap.ext
  intro ψ
  simp only [Units.val_one, one_smul]
  rfl

/-! ## The dyadic operational Clifford hierarchy -/

/-- The operational Clifford hierarchy on `QubitSpace n` with the
dyadic-phase restriction at the base.

* `base`: at level `1`, every dyadic phased Pauli `U` (i.e.,
  `U.toLinearMap = α • pauliOperator p` with `α` a `2^m'`-th root of
  unity) sits in the hierarchy.
* `step`: at level `k+1`, `U` sits in the hierarchy iff for every
  Pauli `p`, the conjugate `U · pauliEquiv p · U⁻¹` sits at level
  `k`.

This is the dyadic version of `IsCliffordHierarchy`. The recursive
step is the same; only the base differs. -/
inductive IsCliffordHierarchyDyadic :
    ℕ → (QubitSpace n ≃ₗ[ℂ] QubitSpace n) → Prop where
  | base {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (h : IsPhasedPauliDyadic U) :
      IsCliffordHierarchyDyadic 1 U
  | step {k : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
      (h : ∀ p : Pauli n, IsCliffordHierarchyDyadic k (conjEquiv U (pauliEquiv p))) :
      IsCliffordHierarchyDyadic (k + 1) U

/-- The tightened (dyadic) hierarchy implies the loose hierarchy. The
recursive structure is the same; we drop the dyadic-ness witness at the
base. -/
theorem IsCliffordHierarchyDyadic.toCliffordHierarchy {k : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic k U) :
    IsCliffordHierarchy k U := by
  induction h with
  | base hU => exact .base hU.toIsPhasedPauli
  | step _ ih => exact .step (fun q => ih q)

/-- Convenience constructor: every Pauli equivalence sits at level 1
of the dyadic hierarchy. -/
theorem IsCliffordHierarchyDyadic.pauli (p : Pauli n) :
    IsCliffordHierarchyDyadic 1 (pauliEquiv p) :=
  .base (isPhasedPauliDyadic_pauliEquiv p)

/-! ## Monotonicity of the dyadic operational Clifford hierarchy

These lemmas parallel `IsCliffordHierarchy.two_of_one`, `.succ`, `.mono`
in `Hierarchy.lean`. The only twist is that the base-step lemma
`two_of_one` must produce a *dyadic* phased Pauli at level 2, not just
any phased Pauli. Inspecting the computation in `Hierarchy.lean`, the
phase produced is `(-1)^e` for some `e : ℕ` — which is `±1`, hence
dyadic with `m' = 1`, `c = e % 2`. So dyadicness is preserved.
-/

/-- Closed form for the inverse of a phased Pauli, duplicated here as a
local lemma because the corresponding lemma in `Hierarchy.lean` is
`private`. If `U.toLinearMap = α • pauliOperator p_U`, then
`U.symm ψ = ((-1)^{p_U.Z · p_U.X} · α⁻¹) • pauliOperator p_U ψ`. -/
private lemma phasedPauli_symm_apply_form
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} {α : ℂˣ} {p_U : Pauli n}
    (hU : U.toLinearMap = (α : ℂ) • (pauliOperator p_U))
    (ψ : QubitSpace n) :
    U.symm ψ =
      (((-1 : ℂ)^(zDotVal p_U p_U.X)) * ((α⁻¹ : ℂˣ) : ℂ)) •
        pauliOperator p_U ψ := by
  have hU_apply : ∀ φ : QubitSpace n,
      U φ = (α : ℂ) • pauliOperator p_U φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hU
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  have step1 : U (U.symm ψ) = ψ := LinearEquiv.apply_symm_apply U ψ
  rw [hU_apply] at step1
  have hα_inv_left : ((α⁻¹ : ℂˣ) : ℂ) * (α : ℂ) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero α)]
  have step2 : pauliOperator p_U (U.symm ψ) = ((α⁻¹ : ℂˣ) : ℂ) • ψ := by
    have h := congrArg (fun (φ : QubitSpace n) => ((α⁻¹ : ℂˣ) : ℂ) • φ) step1
    simp only at h
    rw [smul_smul, hα_inv_left, one_smul] at h
    exact h
  have step3 :
      ((-1 : ℂ)^(zDotVal p_U p_U.X)) • U.symm ψ =
        ((α⁻¹ : ℂˣ) : ℂ) • pauliOperator p_U ψ := by
    have hsq := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L (U.symm ψ))
      (pauliOperator_squared p_U)
    simp only [LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hsq
    have h := congrArg (fun (φ : QubitSpace n) => pauliOperator p_U φ) step2
    simp only at h
    rw [LinearMap.map_smul] at h
    rw [hsq] at h
    exact h
  have h_sq_one :
      ((-1 : ℂ)^(zDotVal p_U p_U.X)) * ((-1 : ℂ)^(zDotVal p_U p_U.X)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have h6 :
      ((-1 : ℂ)^(zDotVal p_U p_U.X)) •
          ((-1 : ℂ)^(zDotVal p_U p_U.X)) • U.symm ψ =
        ((-1 : ℂ)^(zDotVal p_U p_U.X)) •
          ((α⁻¹ : ℂˣ) : ℂ) • pauliOperator p_U ψ :=
    congrArg (fun φ => ((-1 : ℂ)^(zDotVal p_U p_U.X)) • φ) step3
  rw [smul_smul] at h6
  rw [h_sq_one, one_smul, smul_smul] at h6
  exact h6

/-- **Base step (1 → 2)** for the dyadic hierarchy: every dyadic phased
Pauli sits at level 2.

The computation is identical to `IsCliffordHierarchy.two_of_one`; the
phase produced is `(-1)^e` for some `e : ℕ`, which is dyadic (m' = 1).
-/
theorem IsCliffordHierarchyDyadic.two_of_one
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsPhasedPauliDyadic U) :
    IsCliffordHierarchyDyadic 2 U := by
  refine .step (fun q => .base ?_)
  obtain ⟨α, p_U, _hα_dy, hα⟩ := hU
  -- The phase is (-1)^e, dyadic with m' = 1.
  set e : ℕ := zDotVal p_U p_U.X + zDotVal q p_U.X + zDotVal p_U (p_U + q).X
    with he_def
  have hpow_ne_zero : ((-1 : ℂ)^e) ≠ 0 := by
    refine pow_ne_zero _ ?_
    norm_num
  refine ⟨Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero, q,
          isDyadicScalar_neg_one_pow e hpow_ne_zero, ?_⟩
  -- Now establish the linear-map equality. This is exactly the
  -- computation in IsCliffordHierarchy.two_of_one in Hierarchy.lean.
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe,
    Units.val_mk0]
  change conjEquiv U (pauliEquiv q) ψ = ((-1 : ℂ)^e) • pauliOperator q ψ
  rw [conjEquiv_apply, pauliEquiv_apply]
  rw [phasedPauli_symm_apply_form hα ψ]
  rw [LinearMap.map_smul (pauliOperator q)]
  rw [show pauliOperator q (pauliOperator p_U ψ)
        = ((-1 : ℂ)^(zDotVal q p_U.X)) • pauliOperator (p_U + q) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul p_U q)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  rw [smul_smul]
  have hU_apply : ∀ φ : QubitSpace n,
      U φ = (α : ℂ) • pauliOperator p_U φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  rw [hU_apply]
  rw [LinearMap.map_smul (pauliOperator p_U)]
  rw [smul_smul]
  rw [show pauliOperator p_U (pauliOperator (p_U + q) ψ)
        = ((-1 : ℂ)^(zDotVal p_U (p_U + q).X)) •
            pauliOperator ((p_U + q) + p_U) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul (p_U + q) p_U)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  have hpq : (p_U + q) + p_U = q := by
    have h2pU : p_U + p_U = (0 : Pauli n) := by
      ext i
      · change p_U.X i + p_U.X i = (0 : Pauli n).X i
        simp [CharTwo.add_self_eq_zero]
      · change p_U.Z i + p_U.Z i = (0 : Pauli n).Z i
        simp [CharTwo.add_self_eq_zero]
    have : (p_U + q) + p_U = q + (p_U + p_U) := by abel
    rw [this, h2pU, add_zero]
  rw [hpq, smul_smul]
  congr 1
  have hα_α_inv : (α : ℂ) * ((α⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero α)]
  rw [he_def]
  rw [pow_add, pow_add]
  ring_nf
  rw [hα_α_inv]
  ring

/-- **Successor step**: `IsCliffordHierarchyDyadic k U → IsCliffordHierarchyDyadic (k+1) U`.

Proof by induction on the level-`k` hierarchy proof of `U`, mirroring
`IsCliffordHierarchy.succ`. -/
theorem IsCliffordHierarchyDyadic.succ {k : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic k U) :
    IsCliffordHierarchyDyadic (k + 1) U := by
  induction h with
  | base hU =>
      exact two_of_one hU
  | step _ ih =>
      exact .step (fun q => ih q)

/-- **Monotonicity**: `IsCliffordHierarchyDyadic k U → IsCliffordHierarchyDyadic k' U`
for `k ≤ k'`. Proof: chain `succ` along the difference `k' - k`. -/
theorem IsCliffordHierarchyDyadic.mono {k k' : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hkk' : k ≤ k') (h : IsCliffordHierarchyDyadic k U) :
    IsCliffordHierarchyDyadic k' U := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hkk'
  clear hkk'
  induction d with
  | zero =>
      rw [Nat.add_zero]
      exact h
  | succ d ih =>
      rw [← Nat.add_assoc]
      exact ih.succ

/-- **Step inversion.** For `U` at level `k + 2` of the dyadic hierarchy
and any Pauli `p`, the conjugate `conjEquiv U (pauliEquiv p)` sits at
level `k + 1`. We use `k + 2` (i.e., level ≥ 2) so the .step constructor
unambiguously produces the level-(k+1) witness.

For level 1 (base case), the inverse statement would give a level-0
operator, which is uninhabited; we exclude that case by requiring
level ≥ 2. -/
theorem cliffordHierarchyDyadic_step_inv {k : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic (k + 2) U) (p : Pauli n) :
    IsCliffordHierarchyDyadic (k + 1) (conjEquiv U (pauliEquiv p)) := by
  generalize hkeq : k + 2 = klvl at h
  cases h with
  | base hU =>
      -- klvl = 1 case: k + 2 = 1, impossible.
      omega
  | @step k_old _ h_step =>
      have : k_old = k + 1 := by omega
      subst this
      exact h_step p

/-! ## Closure properties for dyadic scalars and phased Paulis

The dyadic-mod-2π descent in `CGKReverseDyadic.lean` requires several
algebraic closures that the original `Hierarchy.lean` did not need.
These are:

* **`IsDyadicScalar.mul`** — the dyadic-scalar set is closed under
  multiplication: lift both witnesses to a common precision
  `M = max m₁ m₂`, then represent the product as a `2^M`-th root of
  unity.

* **`IsPhasedPauliDyadic.mul_pauli_right`** — composing a dyadic
  phased Pauli with an unsigned Pauli on the right yields another
  dyadic phased Pauli; the combined phase is the original phase
  times a `(-1)^…` from `pauliOperator_mul`.

* **`IsPhasedPauliDyadic.pauli_conj`** — conjugating a dyadic phased
  Pauli by an unsigned Pauli yields another dyadic phased Pauli.

* **`IsPhasedPauliDyadic.scale`** — scaling a dyadic phased Pauli by
  a dyadic scalar yields another dyadic phased Pauli.

* **`IsCliffordHierarchyDyadic.dyadic_scale`** — the dyadic hierarchy
  is closed under scaling by a dyadic scalar.

* **`IsCliffordHierarchyDyadic.pauli_conj`** — the dyadic hierarchy is
  closed under conjugation by an unsigned Pauli.

* **`IsCliffordHierarchyDyadic.mul_pauli_right`** — the dyadic
  hierarchy is closed under right-composition by an unsigned Pauli.

These closures together let the iterated discrete-derivative descent
in `CGKReverseDyadic.lean` stay inside the dyadic hierarchy at every
step.
-/

/-- Lift two dyadic-scalar witnesses to a common precision `M`.
If `α` is represented at precision `m₁` with residue `c₁`, then `α`
is also represented at precision `m₁ + d` with residue
`c₁ * 2^d`, since `c₁ * 2^d / 2^(m₁+d) = c₁ / 2^m₁`. -/
private theorem isDyadicScalar_lift_precision
    {α : ℂ} {m₁ : ℕ} {c₁ : ZMod (2 ^ m₁)} (d : ℕ)
    (hα : α = Complex.exp (Complex.I *
            (((2 * Real.pi * (c₁.val : ℝ) / (2 : ℝ) ^ m₁) : ℝ) : ℂ))) :
    ∃ c' : ZMod (2 ^ (m₁ + d)),
      α = Complex.exp (Complex.I *
            (((2 * Real.pi * (c'.val : ℝ) / (2 : ℝ) ^ (m₁ + d)) : ℝ) : ℂ)) := by
  refine ⟨(c₁.val * 2 ^ d : ℕ), ?_⟩
  rw [hα]
  -- Bound: c₁.val * 2^d < 2^(m₁+d).
  have h_bound : c₁.val * 2 ^ d < 2 ^ (m₁ + d) := by
    have hv := ZMod.val_lt c₁
    rw [pow_add]
    have h2dpos : 0 < (2 : ℕ) ^ d := Nat.pow_pos (by norm_num : (0 : ℕ) < 2)
    exact (Nat.mul_lt_mul_right h2dpos).mpr hv
  -- ZMod val of (c₁.val * 2^d : ZMod (2^(m₁+d))) = c₁.val * 2^d.
  have h_val :
      ((c₁.val * 2 ^ d : ℕ) : ZMod (2 ^ (m₁ + d))).val = c₁.val * 2 ^ d :=
    ZMod.val_natCast_of_lt h_bound
  -- Reduce to equality of the real exponents.
  have h_exp_eq :
      ((2 * Real.pi * (c₁.val : ℝ) / (2 : ℝ) ^ m₁) : ℝ) =
        ((2 * Real.pi *
          (((c₁.val * 2 ^ d : ℕ) : ZMod (2 ^ (m₁ + d))).val : ℝ) /
            (2 : ℝ) ^ (m₁ + d)) : ℝ) := by
    rw [h_val]
    have h_pow_add : (2 : ℝ) ^ (m₁ + d) = (2 : ℝ) ^ m₁ * (2 : ℝ) ^ d := by
      rw [pow_add]
    rw [h_pow_add]
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ m₁ := by positivity
    have h2dpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    push_cast
    field_simp
  rw [h_exp_eq]

/-- A helper: at any precision M, the product
`α · β` where `α = exp(I · 2π c_α / 2^M)` and `β = exp(I · 2π c_β / 2^M)`
(both at precision M) equals `exp(I · 2π (c_α + c_β) / 2^M)` (the ZMod
sum). The `2π`-wraparound is absorbed by the `2π`-periodicity of
`exp(I · ·)`. -/
private theorem exp_add_zmod_val (M : ℕ) (c₁' c₂' : ZMod (2 ^ M)) :
    Complex.exp (Complex.I *
      (((2 * Real.pi * (c₁'.val : ℝ) / (2 : ℝ) ^ M) : ℝ) : ℂ)) *
    Complex.exp (Complex.I *
      (((2 * Real.pi * (c₂'.val : ℝ) / (2 : ℝ) ^ M) : ℝ) : ℂ))
    = Complex.exp (Complex.I *
      (((2 * Real.pi * ((c₁' + c₂').val : ℝ) / (2 : ℝ) ^ M) : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  -- Define q as the quotient of c₁'.val + c₂'.val by 2^M.
  set q : ℕ := (c₁'.val + c₂'.val) / 2 ^ M with hq_def
  -- The key Nat-level identity from div_add_mod and ZMod.val_add.
  have hdam : q * 2 ^ M + (c₁'.val + c₂'.val) % 2 ^ M = c₁'.val + c₂'.val := by
    rw [hq_def, Nat.mul_comm]
    exact Nat.div_add_mod (c₁'.val + c₂'.val) (2 ^ M)
  have h_val_mod : (c₁' + c₂' : ZMod (2 ^ M)).val =
      (c₁'.val + c₂'.val) - q * 2 ^ M := by
    rw [ZMod.val_add c₁' c₂']
    omega
  have h_q_bound : q * 2 ^ M ≤ c₁'.val + c₂'.val := by
    omega
  -- Real-valued version, isolating c₁'.val + c₂'.val.
  have h_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  have h_pos_ne : (2 : ℝ) ^ M ≠ 0 := ne_of_gt h_pos
  have h_val_real :
      (c₁'.val : ℝ) + (c₂'.val : ℝ) =
        ((c₁' + c₂' : ZMod (2 ^ M)).val : ℝ) + (q : ℝ) * ((2 : ℝ) ^ M) := by
    have h_sub_cast : (((c₁'.val + c₂'.val) - q * 2 ^ M : ℕ) : ℝ) =
        (c₁'.val + c₂'.val : ℝ) - (q * 2 ^ M : ℝ) := by
      have h := Nat.cast_sub (R := ℝ) h_q_bound
      push_cast at h
      exact_mod_cast h
    have h1 : ((c₁' + c₂' : ZMod (2 ^ M)).val : ℝ) =
              (c₁'.val + c₂'.val : ℝ) - (q * 2 ^ M : ℝ) := by
      rw [h_val_mod]
      exact h_sub_cast
    push_cast at h1
    linarith
  -- The real-valued exponent identity follows by direct calculation.
  have h_inner :
      2 * Real.pi * (c₁'.val : ℝ) / (2 : ℝ) ^ M +
          2 * Real.pi * (c₂'.val : ℝ) / (2 : ℝ) ^ M
      = 2 * Real.pi * ((c₁' + c₂' : ZMod (2 ^ M)).val : ℝ) / (2 : ℝ) ^ M +
          (q : ℝ) * (2 * Real.pi) := by
    have h := h_val_real
    field_simp
    linarith
  -- Lift to ℂ: I·LHS = I·RHS.
  have h_diff_complex :
      Complex.I * (((2 * Real.pi * (c₁'.val : ℝ) / (2 : ℝ) ^ M) : ℝ) : ℂ) +
        Complex.I *
          (((2 * Real.pi * (c₂'.val : ℝ) / (2 : ℝ) ^ M) : ℝ) : ℂ)
      = Complex.I *
          (((2 * Real.pi * ((c₁' + c₂' : ZMod (2 ^ M)).val : ℝ) / (2 : ℝ) ^ M) : ℝ) : ℂ) +
        ((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h_inner_C :
        ((2 * Real.pi * (c₁'.val : ℝ) / (2 : ℝ) ^ M +
            2 * Real.pi * (c₂'.val : ℝ) / (2 : ℝ) ^ M : ℝ) : ℂ) =
          ((2 * Real.pi * ((c₁' + c₂' : ZMod (2 ^ M)).val : ℝ) / (2 : ℝ) ^ M +
              (q : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      exact_mod_cast h_inner
    push_cast at h_inner_C
    push_cast
    linear_combination Complex.I * h_inner_C
  rw [h_diff_complex]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- An auxiliary lemma: `α • β` factored through `Units.mk0` matches the
`Units` multiplication. -/
private theorem isDyadicScalar_mk0_mul {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    (Units.mk0 (α * β) (mul_ne_zero hα hβ) : ℂˣ) =
      Units.mk0 α hα * Units.mk0 β hβ := by
  apply Units.ext
  simp

/-- **The dyadic-scalar set is closed under multiplication.** Given
`α` and `β` dyadic, their product `α · β` is dyadic. Proof: lift
both representations to a common precision `M = m₁ + m₂`, then sum
the residues. -/
theorem IsDyadicScalar.mul {α β : ℂˣ}
    (hα : IsDyadicScalar α) (hβ : IsDyadicScalar β) :
    IsDyadicScalar (α * β) := by
  obtain ⟨m₁, c₁, hα_eq⟩ := hα
  obtain ⟨m₂, c₂, hβ_eq⟩ := hβ
  -- Lift α to precision m₁ + m₂.
  obtain ⟨c₁_lift, hα_lift⟩ :=
    isDyadicScalar_lift_precision (m₁ := m₁) (c₁ := c₁) m₂ hα_eq
  -- Lift β to precision m₂ + m₁; reuse hα-style call structure.
  obtain ⟨c₂_swap, hβ_swap⟩ :=
    isDyadicScalar_lift_precision (m₁ := m₂) (c₁ := c₂) m₁ hβ_eq
  -- Use `m₂ + m₁ = m₁ + m₂` to make both into the same ZMod.
  have h_comm : m₂ + m₁ = m₁ + m₂ := Nat.add_comm _ _
  -- Apply h_comm to c₂_swap and hβ_swap by elimination.
  clear hα_eq hβ_eq
  revert c₂_swap hβ_swap
  rw [h_comm]
  intro c₂_lift hβ_lift
  -- Now both lifts at the same precision M = m₁ + m₂.
  refine ⟨m₁ + m₂, c₁_lift + c₂_lift, ?_⟩
  rw [Units.val_mul, hα_lift, hβ_lift]
  exact exp_add_zmod_val _ c₁_lift c₂_lift

/-- **Dyadic phased Pauli is closed under right-composition by an
unsigned Pauli.** If `U.toLinearMap = α • pauliOperator p_U` with `α`
dyadic, then `(U.trans (pauliEquiv p)).toLinearMap =
((-1)^(p.Z · p_U.X) · α) • pauliOperator (p_U + p)`. The combined
scalar `(-1)^... · α` is dyadic by `IsDyadicScalar.mul`. -/
theorem IsPhasedPauliDyadic.mul_pauli_right
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsPhasedPauliDyadic U) (p : Pauli n) :
    IsPhasedPauliDyadic (U.trans (pauliEquiv p)) := by
  obtain ⟨α, p_U, hα_dy, hα⟩ := h
  -- The combined phase is α · (-1)^{p.Z · p_U.X}.
  set e : ℕ := zDotVal p p_U.X with he_def
  have hpow_ne_zero : ((-1 : ℂ)^e) ≠ 0 := by
    refine pow_ne_zero _ ?_
    norm_num
  set β : ℂˣ := α * Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero with hβ_def
  have hβ_dy : IsDyadicScalar β := by
    rw [hβ_def]
    exact IsDyadicScalar.mul hα_dy
      (isDyadicScalar_neg_one_pow e hpow_ne_zero)
  refine ⟨β, p_U + p, hβ_dy, ?_⟩
  apply LinearMap.ext
  intro ψ
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, pauliEquiv_apply,
    LinearMap.smul_apply]
  -- LHS: ((U.trans (pauliEquiv p)) ψ) = pauliOperator p (U ψ).
  -- Substitute U ψ = α • pauliOperator p_U ψ.
  have hU_apply : ∀ φ : QubitSpace n,
      U φ = (α : ℂ) • pauliOperator p_U φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  rw [hU_apply]
  -- Apply pauliOperator p to the scaled state.
  rw [LinearMap.map_smul (pauliOperator p)]
  -- Use pauliOperator_mul p_U p.
  rw [show pauliOperator p (pauliOperator p_U ψ)
        = ((-1 : ℂ)^(zDotVal p p_U.X)) • pauliOperator (p_U + p) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul p_U p)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  rw [smul_smul]
  -- Now goal: (α * (-1)^e) • pauliOperator (p_U + p) ψ = β • pauliOperator (p_U + p) ψ.
  -- The scalar matches by definition of β.
  congr 1

/-! ## Scaling closure for the dyadic hierarchy

Conjugation by a Pauli annihilates a dyadic scaling factor (the sign in
`(pauliEquiv p).symm` cancels the scaling). Therefore the dyadic
hierarchy is closed under `scaleEquiv` by a dyadic scalar.
-/

/-- Conjugation by a Pauli is invariant under outer scaling by any unit.
Proof: the scaling on the outer copy and its inverse on `.symm` cancel
in the conjugation product. -/
private lemma conjEquiv_scaleEquiv_pauliEquiv (β : ℂˣ)
    (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (p : Pauli n) :
    conjEquiv (scaleEquiv β V) (pauliEquiv p) = conjEquiv V (pauliEquiv p) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  simp only [conjEquiv_apply, scaleEquiv_apply, scaleEquiv_symm_apply,
    pauliEquiv_apply, LinearEquiv.coe_coe]
  rw [LinearMap.map_smul, LinearEquiv.map_smul]
  rw [smul_smul]
  rw [show (β : ℂ) * ((β⁻¹ : ℂˣ) : ℂ) = 1 from by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero β)]]
  rw [one_smul]

/-- Scaling a dyadic phased Pauli by a dyadic unit yields another
dyadic phased Pauli. -/
theorem IsPhasedPauliDyadic.scale {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsPhasedPauliDyadic U) {β : ℂˣ} (hβ : IsDyadicScalar β) :
    IsPhasedPauliDyadic (scaleEquiv β U) := by
  obtain ⟨α, p, hα_dy, hα⟩ := h
  refine ⟨β * α, p, IsDyadicScalar.mul hβ hα_dy, ?_⟩
  apply LinearMap.ext
  intro ψ
  rw [scaleEquiv_toLinearMap, hα]
  simp only [LinearMap.smul_apply, Units.val_mul]
  rw [mul_smul]

/-- The dyadic operational Clifford hierarchy is closed under
multiplication by a dyadic unit scalar. -/
theorem IsCliffordHierarchyDyadic.dyadic_scale {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} {β : ℂˣ}
    (hβ : IsDyadicScalar β)
    (hV : IsCliffordHierarchyDyadic k V) :
    IsCliffordHierarchyDyadic k (scaleEquiv β V) := by
  induction hV with
  | base h => exact .base (h.scale hβ)
  | @step k V hstep ih =>
      refine .step (fun p => ?_)
      rw [conjEquiv_scaleEquiv_pauliEquiv]
      exact hstep p

/-! ## Pauli-conjugation closure for the dyadic hierarchy -/

/-- Conjugation by `pauliEquiv p` of a dyadic phased Pauli yields a
dyadic phased Pauli. Combines `pauliOperator_mul` (twice) with
`IsDyadicScalar.mul` and `isDyadicScalar_neg_one_pow`. -/
theorem IsPhasedPauliDyadic.pauli_conj
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsPhasedPauliDyadic V) (p : Pauli n) :
    IsPhasedPauliDyadic (conjEquiv (pauliEquiv p) V) := by
  -- The result is essentially the `two_of_one` computation specialised
  -- to the case where the level-1 operator we conjugate is itself a
  -- dyadic phased Pauli; the conjugating operator is the pure
  -- `pauliEquiv p` (no extra scalar). Reuse the structure of the
  -- existing `two_of_one`-style computation.
  obtain ⟨α, p_V, hα_dy, hα⟩ := h
  -- The combined sign exponent.
  set e : ℕ := zDotVal p p.X + zDotVal p_V p.X + zDotVal p (p + p_V).X with he_def
  have hpow_ne_zero : ((-1 : ℂ)^e) ≠ 0 := by
    refine pow_ne_zero _ ?_
    norm_num
  -- The combined scalar is α · (-1)^e, dyadic.
  set γ : ℂˣ := α * Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero with hγ_def
  have hγ_dy : IsDyadicScalar γ := by
    rw [hγ_def]
    exact IsDyadicScalar.mul hα_dy (isDyadicScalar_neg_one_pow e hpow_ne_zero)
  refine ⟨γ, p_V, hγ_dy, ?_⟩
  apply LinearMap.ext
  intro ψ
  -- Compute conjEquiv (pauliEquiv p) V at ψ.
  -- conjEquiv (pauliEquiv p) V ψ = (pauliEquiv p) (V ((pauliEquiv p).symm ψ))
  --   = pauliOp p (V ((-1)^{p.Z·p.X} • pauliOp p ψ))
  --   = pauliOp p ((-1)^{p.Z·p.X} • V (pauliOp p ψ))   [V linear]
  --   = (-1)^{p.Z·p.X} • pauliOp p (α • pauliOp p_V (pauliOp p ψ))  [V applied]
  --   = (-1)^{p.Z·p.X} α • pauliOp p (pauliOp p_V (pauliOp p ψ)).
  -- Now apply pauliOperator_mul twice.
  simp only [LinearEquiv.coe_coe, LinearMap.smul_apply]
  change conjEquiv (pauliEquiv p) V ψ = (γ : ℂ) • pauliOperator p_V ψ
  rw [conjEquiv_apply, pauliEquiv_symm_apply, pauliEquiv_apply]
  -- Inner: V ((-1)^{p.Z·p.X} • pauliOperator p ψ).
  rw [LinearEquiv.map_smul]
  -- V acts as α • pauliOperator p_V.
  have hV_apply : ∀ φ : QubitSpace n,
      V φ = (α : ℂ) • pauliOperator p_V φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  rw [hV_apply]
  -- Use pauliOperator_mul p p_V.
  rw [show pauliOperator p_V (pauliOperator p ψ)
        = ((-1 : ℂ)^(zDotVal p_V p.X)) • pauliOperator (p + p_V) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul p p_V)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  -- Pull the scalar through.
  rw [smul_smul, smul_smul]
  rw [LinearMap.map_smul (pauliOperator p)]
  -- Apply pauliOperator_mul (p + p_V) p.
  rw [show pauliOperator p (pauliOperator (p + p_V) ψ)
        = ((-1 : ℂ)^(zDotVal p (p + p_V).X)) •
            pauliOperator ((p + p_V) + p) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul (p + p_V) p)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  -- (p + p_V) + p = p_V in characteristic 2.
  have hpq : (p + p_V) + p = p_V := by
    have h2p : p + p = (0 : Pauli n) := by
      ext i
      · change p.X i + p.X i = (0 : Pauli n).X i
        simp [CharTwo.add_self_eq_zero]
      · change p.Z i + p.Z i = (0 : Pauli n).Z i
        simp [CharTwo.add_self_eq_zero]
    have : (p + p_V) + p = p_V + (p + p) := by abel
    rw [this, h2p, add_zero]
  rw [hpq]
  rw [smul_smul]
  congr 1
  -- The scalar: (-1)^{p.Z·p.X} · α · (-1)^{p_V.Z·p.X} · (-1)^{p.Z·(p+p_V).X}
  --           = α · (-1)^{p.Z·p.X + p_V.Z·p.X + p.Z·(p+p_V).X}
  --           = α · (-1)^e = γ.
  rw [hγ_def]
  simp only [Units.val_mul, Units.val_mk0]
  rw [he_def, pow_add, pow_add]
  ring

/-- The dyadic operational Clifford hierarchy is closed under
conjugation by an unsigned Pauli. Proof by induction on the hierarchy
proof: base case uses `IsPhasedPauliDyadic.pauli_conj`; step case uses
the conjugation identity
`conjEquiv (conjEquiv X V) Q = conjEquiv X (conjEquiv V (conjEquiv X Q))`
(valid for `X = pauliEquiv p` after absorbing the `.symm` scalar via
`conjEquiv_scaleEquiv_pauliEquiv`) plus `two_of_one` to extract the
dyadic phased Pauli structure of `conjEquiv (pauliEquiv p) (pauliEquiv q)`. -/
theorem IsCliffordHierarchyDyadic.pauli_conj {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic k V) (p : Pauli n) :
    IsCliffordHierarchyDyadic k (conjEquiv (pauliEquiv p) V) := by
  induction h generalizing p with
  | base hV => exact .base (hV.pauli_conj p)
  | @step k V hstep ih =>
      refine .step (fun q => ?_)
      -- Goal: IsCliffordHierarchyDyadic k
      --         (conjEquiv (conjEquiv (pauliEquiv p) V) (pauliEquiv q)).
      -- Use conjEquiv_conjEquiv_pauliEquiv: this equals
      --   conjEquiv (pauliEquiv p) (conjEquiv V (conjEquiv (pauliEquiv p) (pauliEquiv q))).
      -- By two_of_one, conjEquiv (pauliEquiv p) (pauliEquiv q)
      --   = scaleEquiv ((-1)^e) (pauliEquiv q).
      -- By conjEquiv pulling through scaleEquiv inside (linearity):
      --   conjEquiv V (scaleEquiv c X) = scaleEquiv c (conjEquiv V X).
      -- So conjEquiv V (conjEquiv (pauliEquiv p) (pauliEquiv q))
      --   = scaleEquiv ((-1)^e) (conjEquiv V (pauliEquiv q)).
      -- By IH applied to hstep q: conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q)) ∈ level k.
      -- conjEquiv pulls scaleEquiv from inside:
      --   conjEquiv (pauliEquiv p) (scaleEquiv c X) = scaleEquiv c (conjEquiv (pauliEquiv p) X).
      -- Combining: the result is scaleEquiv ((-1)^e) of a level-k object, which is level-k
      -- (by `dyadic_scale`).
      -- Let me phrase this cleanly.
      -- Step 1: identify `conjEquiv (pauliEquiv p) (pauliEquiv q)` as a phased Pauli.
      set e : ℕ := zDotVal p p.X + zDotVal q p.X + zDotVal p (p + q).X with he_def
      have hpow_ne_zero : ((-1 : ℂ)^e) ≠ 0 := by
        refine pow_ne_zero _ ?_
        norm_num
      have h_phased :
          conjEquiv (pauliEquiv p) (pauliEquiv q) =
            scaleEquiv (Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero) (pauliEquiv q) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        change conjEquiv (pauliEquiv p) (pauliEquiv q) ψ =
              scaleEquiv (Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero) (pauliEquiv q) ψ
        rw [conjEquiv_apply, pauliEquiv_symm_apply, pauliEquiv_apply,
            pauliEquiv_apply]
        simp only [scaleEquiv_apply, pauliEquiv_apply, Units.val_mk0]
        -- conjEquiv (pauliEquiv p) (pauliEquiv q) ψ
        --   = (pauliEquiv p) ((pauliEquiv q) ((pauliEquiv p).symm ψ))
        --   = pauliOp p (pauliOp q ((-1)^{p.Z·p.X} • pauliOp p ψ))
        --   = pauliOp p ((-1)^{p.Z·p.X} • pauliOp q (pauliOp p ψ))
        --   = (-1)^{p.Z·p.X} • pauliOp p (pauliOp q (pauliOp p ψ)).
        -- Now apply pauliOperator_mul p q twice.
        rw [LinearMap.map_smul (pauliOperator q)]
        rw [show pauliOperator q (pauliOperator p ψ)
              = ((-1 : ℂ)^(zDotVal q p.X)) • pauliOperator (p + q) ψ from by
            have h := congrArg
              (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
              (pauliOperator_mul p q)
            simp only [LinearMap.coe_comp, Function.comp_apply,
              LinearMap.smul_apply] at h
            exact h]
        rw [LinearMap.map_smul (pauliOperator p)]
        rw [LinearMap.map_smul (pauliOperator p)]
        rw [show pauliOperator p (pauliOperator (p + q) ψ)
              = ((-1 : ℂ)^(zDotVal p (p + q).X)) •
                  pauliOperator ((p + q) + p) ψ from by
            have h := congrArg
              (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
              (pauliOperator_mul (p + q) p)
            simp only [LinearMap.coe_comp, Function.comp_apply,
              LinearMap.smul_apply] at h
            exact h]
        -- (p + q) + p = q.
        have hpq : (p + q) + p = q := by
          have h2p : p + p = (0 : Pauli n) := by
            ext i
            · change p.X i + p.X i = (0 : Pauli n).X i
              simp [CharTwo.add_self_eq_zero]
            · change p.Z i + p.Z i = (0 : Pauli n).Z i
              simp [CharTwo.add_self_eq_zero]
          have : (p + q) + p = q + (p + p) := by abel
          rw [this, h2p, add_zero]
        rw [hpq]
        -- Combine the scalars.
        rw [smul_smul, smul_smul]
        congr 1
        -- Target: (-1)^{p.Z·p.X} * (-1)^{q.Z·p.X} * (-1)^{p.Z·(p+q).X} = (-1)^e.
        rw [show ((-1 : ℂ)^(zDotVal p p.X)) *
                  ((-1 : ℂ)^(zDotVal q p.X)) *
                  ((-1 : ℂ)^(zDotVal p (p + q).X))
              = (-1 : ℂ)^(zDotVal p p.X + zDotVal q p.X + zDotVal p (p + q).X)
              from by rw [pow_add, pow_add]]
      -- Step 2: conjEquiv V (h_phased thing) = scaleEquiv c (conjEquiv V (pauliEquiv q)).
      have h_pull_inside :
          conjEquiv V (conjEquiv (pauliEquiv p) (pauliEquiv q)) =
            scaleEquiv (Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero)
              (conjEquiv V (pauliEquiv q)) := by
        rw [h_phased]
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, scaleEquiv_apply, pauliEquiv_apply,
          LinearEquiv.coe_coe]
        -- Goal: V (c • Q (V.symm ψ)) = c • V (Q (V.symm ψ)). V is linear.
        rw [LinearEquiv.map_smul]
      -- Step 3: the conjugation identity. The universal identity is
      -- `conjEquiv (conjEquiv X V) Q = conjEquiv X (conjEquiv V (conjEquiv X.symm Q))`.
      -- For `X = pauliEquiv p`, `X.symm` differs from `X` by a scaleEquiv, so
      -- `conjEquiv X.symm Q = conjEquiv X Q` by `conjEquiv_scaleEquiv_pauliEquiv`.
      have h_X_symm :
          (pauliEquiv p).symm =
            scaleEquiv (Units.mk0 ((-1 : ℂ)^(zDotVal p p.X))
                        (by refine pow_ne_zero _ ?_; norm_num)) (pauliEquiv p) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [scaleEquiv_apply, pauliEquiv_apply, pauliEquiv_symm_apply,
          Units.val_mk0, LinearEquiv.coe_coe]
      have h_conj_inner_eq :
          conjEquiv (pauliEquiv p).symm (pauliEquiv q) =
            conjEquiv (pauliEquiv p) (pauliEquiv q) := by
        rw [h_X_symm]
        exact conjEquiv_scaleEquiv_pauliEquiv _ _ _
      have h_conj_id :
          conjEquiv (conjEquiv (pauliEquiv p) V) (pauliEquiv q) =
            conjEquiv (pauliEquiv p)
              (conjEquiv V (conjEquiv (pauliEquiv p) (pauliEquiv q))) := by
        rw [← h_conj_inner_eq]
        -- Now goal: conjEquiv (conjEquiv X V) Q = conjEquiv X (conjEquiv V (conjEquiv X.symm Q))
        -- where X = pauliEquiv p and Q = pauliEquiv q. This is the universal
        -- algebraic identity, proven pointwise.
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, conjEquiv_symm_apply,
          LinearEquiv.coe_coe, LinearEquiv.symm_symm]
      rw [h_conj_id, h_pull_inside]
      -- Step 4: conjEquiv (pauliEquiv p) (scaleEquiv c X)
      --   = scaleEquiv c (conjEquiv (pauliEquiv p) X).
      have h_pull_outside :
          conjEquiv (pauliEquiv p)
            (scaleEquiv (Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero)
              (conjEquiv V (pauliEquiv q))) =
          scaleEquiv (Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero)
            (conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q))) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, scaleEquiv_apply, LinearEquiv.coe_coe]
        exact LinearEquiv.map_smul _ _ _
      rw [h_pull_outside]
      -- Step 5: IH gives directly: conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q)) ∈ level k.
      -- IH has signature `ih : ∀ (q_inner p_outer : Pauli n), ...`.
      exact (ih q p).dyadic_scale
        (isDyadicScalar_neg_one_pow e hpow_ne_zero)

/-! ## Right-multiplication closure for the dyadic hierarchy -/

/-- The dyadic operational Clifford hierarchy is closed under
right-multiplication by an unsigned Pauli `pauliEquiv p`. Proof:
induction on the hierarchy proof, using
`IsPhasedPauliDyadic.mul_pauli_right` at the base and the identity
`conjEquiv (V.trans (pauliEquiv p)) Q = conjEquiv (pauliEquiv p) (conjEquiv V Q)`
plus `IsCliffordHierarchyDyadic.pauli_conj` at the step. -/
theorem IsCliffordHierarchyDyadic.mul_pauli_right {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic k V) (p : Pauli n) :
    IsCliffordHierarchyDyadic k (V.trans (pauliEquiv p)) := by
  induction h generalizing p with
  | base hV => exact .base (hV.mul_pauli_right p)
  | @step k V hstep ih =>
      refine .step (fun q => ?_)
      -- Goal: IsCliffordHierarchyDyadic k
      --         (conjEquiv (V.trans (pauliEquiv p)) (pauliEquiv q)).
      -- conjEquiv (V.trans (pauliEquiv p)) Q
      --   = (V.trans (pauliEquiv p)) ∘ Q ∘ (V.trans (pauliEquiv p)).symm
      --   = pauliEquiv p ∘ V ∘ Q ∘ V.symm ∘ (pauliEquiv p).symm
      --   = pauliEquiv p ∘ (conjEquiv V Q) ∘ (pauliEquiv p).symm
      --   = conjEquiv (pauliEquiv p) (conjEquiv V Q).
      have h_id :
          conjEquiv (V.trans (pauliEquiv p)) (pauliEquiv q) =
            conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q)) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply,
          LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
          LinearEquiv.coe_coe]
      rw [h_id]
      exact (hstep q).pauli_conj p

/-- The dyadic operational Clifford hierarchy is closed under
right-multiplication by an unsigned Pauli, in both directions. The
reverse direction multiplies by the same Pauli (since `pauliEquiv p`
composed with itself is `scaleEquiv ((-1)^{p.Z·p.X}) id`, a dyadic
scaling). -/
theorem IsCliffordHierarchyDyadic.mul_pauli_right_iff {k : ℕ}
    (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (p : Pauli n) :
    IsCliffordHierarchyDyadic k (V.trans (pauliEquiv p)) ↔
      IsCliffordHierarchyDyadic k V := by
  refine ⟨fun h => ?_, fun h => h.mul_pauli_right p⟩
  -- Apply `mul_pauli_right` to (V.trans (pauliEquiv p)) again with the same p.
  -- (V.trans (pauliEquiv p)).trans (pauliEquiv p) is
  --   scaleEquiv ((-1)^{p.Z·p.X}) V.
  have h_back :
      (V.trans (pauliEquiv p)).trans (pauliEquiv p) =
        scaleEquiv (Units.mk0 ((-1 : ℂ)^(zDotVal p p.X))
                    (by refine pow_ne_zero _ ?_; norm_num)) V := by
    refine LinearEquiv.toLinearMap_injective ?_
    apply LinearMap.ext
    intro ψ
    simp only [LinearEquiv.trans_apply, scaleEquiv_apply,
      pauliEquiv_apply, LinearEquiv.coe_coe,
      Units.val_mk0]
    -- LHS: pauliOp p (pauliOp p (V ψ)) = (pauliOp p)^2 (V ψ)
    --   = (-1)^{p.Z·p.X} • V ψ.
    have hsq := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L (V ψ))
      (pauliOperator_squared p)
    simp only [LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hsq
    exact hsq
  -- Now apply mul_pauli_right to h (a level-k for V.trans (pauliEquiv p)).
  have hgot := h.mul_pauli_right p
  -- hgot : IsCliffordHierarchyDyadic k ((V.trans (pauliEquiv p)).trans (pauliEquiv p)).
  rw [h_back] at hgot
  -- Now hgot is scaleEquiv c V at level k. Reverse the scaling.
  -- Use that scaleEquiv c (scaleEquiv c⁻¹ X) = X (for c² = 1, c⁻¹ = c).
  -- The simplest: c = (-1)^k, and (-1)^k · (-1)^k = 1, so c = c⁻¹.
  -- Apply dyadic_scale with c⁻¹ to recover V.
  have h_scale_inv :
      scaleEquiv (Units.mk0 ((-1 : ℂ)^(zDotVal p p.X))
                  (by refine pow_ne_zero _ ?_; norm_num))
        (scaleEquiv (Units.mk0 ((-1 : ℂ)^(zDotVal p p.X))
                    (by refine pow_ne_zero _ ?_; norm_num)) V) = V := by
    refine LinearEquiv.toLinearMap_injective ?_
    apply LinearMap.ext
    intro ψ
    simp only [scaleEquiv_apply, LinearEquiv.coe_coe, Units.val_mk0]
    rw [smul_smul]
    rw [show ((-1 : ℂ)^(zDotVal p p.X) * (-1 : ℂ)^(zDotVal p p.X)) = 1 from by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num]
    rw [one_smul]
  rw [← h_scale_inv]
  exact hgot.dyadic_scale (isDyadicScalar_neg_one_pow _ _)

end FTQCLib.Hilbert

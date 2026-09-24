/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.PauliProduct

set_option linter.unusedSectionVars false

/-! # The operational Clifford hierarchy on the qubit Hilbert space

This file builds the operational side of the Clifford hierarchy as a
predicate on `QubitSpace n ≃ₗ[ℂ] QubitSpace n`. The hierarchy is the
recursive definition originally due to Gottesman-Chuang and used in
the CGK (Cui-Gottesman-Krishna 2017) framework:

  C⁽¹⁾ = {α · P : α ∈ ℂ×, P a Pauli operator},
  C⁽ᵏ⁺¹⁾ = {U : ∀ q Pauli, U q U⁻¹ ∈ C⁽ᵏ⁾},

with conjugation in the convention `U q U⁻¹` (the standard
left-action convention). The chapter-2 polynomial-side predicate
`IsDiagonalHierarchyLevel` lives in `FTQCLib/Hierarchy/HierarchyLevel.lean`;
the operator-side analogue here lets us state CGK as an equivalence
between the two predicates on `diagonalGateEquiv (realPhase P)`.

The file defines:

* **`scaleEquiv α e`** — multiplying a linear equivalence by a unit
  scalar `α : ℂˣ`. The unit shape makes the inverse structural.
* **`conjEquiv U V`** — conjugation `U V U⁻¹` realised as
  `U.symm.trans (V.trans U)`. With `LinearEquiv.trans` composing
  left-to-right, evaluation gives `U (V (U⁻¹ x))`, matching the
  Heisenberg-picture conjugation convention.
* **`IsPhasedPauli U`** — the base-level predicate: `U` agrees as a
  linear map with `α · pauliOperator p` for some `α ∈ ℂ×` and some
  Pauli `p`.
* **`IsCliffordHierarchy k U`** — the recursive hierarchy predicate
  on `U : QubitSpace n ≃ₗ[ℂ] QubitSpace n`. Level 1 is phased Paulis;
  level `k+1` requires every conjugate of a Pauli to sit at level `k`.

The file also proves monotonicity: `IsCliffordHierarchy k U →
IsCliffordHierarchy k' U` for `k ≤ k'`. The base step `1 → 2` is the
statement that conjugating any Pauli by a phased Pauli is again a
phased Pauli; that follows from the Pauli-product identity
`pauliOperator p · pauliOperator q = (phase) · pauliOperator (p + q)`
in `FTQCLib/Hilbert/PauliProduct.lean` together with the squared identity
`pauliOperator p · pauliOperator p = (phase) · id`. Higher steps
follow by induction on the difference `k' - k`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-! ## Scaling a linear equivalence by a nonzero complex scalar -/

/-- Multiply a linear equivalence `e` on `QubitSpace n` by a unit
complex scalar `α : ℂˣ`. The result is the linear equivalence whose
forward map is `α • e` and whose inverse is `α⁻¹ • e.symm`. We
package `α` as a unit (`ℂˣ`) so the inverse is structural rather
than relying on a nonzero-of-condition hypothesis. -/
noncomputable def scaleEquiv (α : ℂˣ) (e : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n where
  toFun ψ := (α : ℂ) • e ψ
  invFun ψ := ((α⁻¹ : ℂˣ) : ℂ) • e.symm ψ
  map_add' ψ φ := by simp [smul_add]
  map_smul' c ψ := by
    simp only [LinearEquiv.map_smul, RingHom.id_apply]
    rw [smul_comm]
  left_inv ψ := by
    simp only
    rw [LinearEquiv.map_smul, ← smul_assoc, smul_eq_mul]
    rw [show ((α⁻¹ : ℂˣ) : ℂ) * (α : ℂ) = 1 from by
      rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero α)]]
    rw [one_smul, LinearEquiv.symm_apply_apply]
  right_inv ψ := by
    simp only
    rw [LinearEquiv.map_smul, ← smul_assoc, smul_eq_mul]
    rw [show (α : ℂ) * ((α⁻¹ : ℂˣ) : ℂ) = 1 from by
      rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero α)]]
    rw [one_smul, LinearEquiv.apply_symm_apply]

@[simp] theorem scaleEquiv_apply (α : ℂˣ) (e : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (ψ : QubitSpace n) :
    scaleEquiv α e ψ = (α : ℂ) • e ψ := rfl

@[simp] theorem scaleEquiv_symm_apply (α : ℂˣ) (e : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (ψ : QubitSpace n) :
    (scaleEquiv α e).symm ψ = ((α⁻¹ : ℂˣ) : ℂ) • e.symm ψ := rfl

@[simp] theorem scaleEquiv_toLinearMap (α : ℂˣ)
    (e : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    (scaleEquiv α e).toLinearMap = (α : ℂ) • e.toLinearMap := by
  apply LinearMap.ext
  intro ψ
  simp [scaleEquiv_apply]

/-! ## Conjugation as a linear equivalence -/

/-- Conjugation of `V` by `U`, realised as the linear equivalence
`U V U⁻¹` on `QubitSpace n`. With `LinearEquiv.trans` composing
left-to-right, `(U.symm.trans (V.trans U)) ψ = U (V (U.symm ψ))`,
which is the standard Heisenberg-picture conjugation
`U V U⁻¹`. -/
noncomputable def conjEquiv (U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  U.symm.trans (V.trans U)

@[simp] theorem conjEquiv_apply (U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (ψ : QubitSpace n) :
    conjEquiv U V ψ = U (V (U.symm ψ)) := rfl

@[simp] theorem conjEquiv_symm_apply (U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (ψ : QubitSpace n) :
    (conjEquiv U V).symm ψ = U (V.symm (U.symm ψ)) := rfl

/-! ## The base level: phased Pauli operators -/

/-- `IsPhasedPauli U` says that the underlying linear map of `U`
coincides with `α · pauliOperator p` for some unit scalar `α : ℂˣ`
and some Pauli `p : Pauli n`. This captures the level-1 set
`C⁽¹⁾ = {α · P : α ≠ 0, P ∈ Pauli group}` of the Clifford
hierarchy, including the global phase. -/
def IsPhasedPauli (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : Prop :=
  ∃ (α : ℂˣ) (p : Pauli n), U.toLinearMap = (α : ℂ) • (pauliOperator p)

/-- The unsigned Pauli equivalence `pauliEquiv p` is itself a phased
Pauli (with phase `1`). -/
theorem isPhasedPauli_pauliEquiv (p : Pauli n) :
    IsPhasedPauli (pauliEquiv p) := by
  refine ⟨1, p, ?_⟩
  apply LinearMap.ext
  intro ψ
  simp only [Units.val_one, one_smul]
  rfl

/-- The scaling `scaleEquiv α (pauliEquiv p)` is a phased Pauli for
any unit `α`. -/
theorem isPhasedPauli_scale_pauliEquiv (α : ℂˣ) (p : Pauli n) :
    IsPhasedPauli (scaleEquiv α (pauliEquiv p)) := by
  refine ⟨α, p, ?_⟩
  apply LinearMap.ext
  intro ψ
  rw [scaleEquiv_toLinearMap]
  simp only [LinearMap.smul_apply]
  congr 1

/-! ## The operational Clifford hierarchy -/

/-- The operational Clifford hierarchy on `QubitSpace n`.

* `base`: at level `1`, every phased Pauli `U` (i.e. `U = α · P` for
  some scalar `α` and Pauli `P`) sits in the hierarchy.
* `step`: at level `k+1`, `U` sits in the hierarchy iff for every
  Pauli `p`, the conjugate `U · pauliEquiv p · U⁻¹` sits at level
  `k`.

This is the standard recursive definition of CGK and matches the
Gottesman-Chuang gate-teleportation hierarchy. Level `0` is not
inhabited: the recursion bottoms out at level `1`. -/
inductive IsCliffordHierarchy : ℕ → (QubitSpace n ≃ₗ[ℂ] QubitSpace n) → Prop where
  | base {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (h : IsPhasedPauli U) :
      IsCliffordHierarchy 1 U
  | step {k : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
      (h : ∀ p : Pauli n, IsCliffordHierarchy k (conjEquiv U (pauliEquiv p))) :
      IsCliffordHierarchy (k + 1) U

/-- Convenience constructor: every Pauli equivalence sits at level 1. -/
theorem IsCliffordHierarchy.pauli (p : Pauli n) :
    IsCliffordHierarchy 1 (pauliEquiv p) :=
  .base (isPhasedPauli_pauliEquiv p)

/-- Convenience constructor: every scaled Pauli sits at level 1. -/
theorem IsCliffordHierarchy.scaled_pauli (α : ℂˣ) (p : Pauli n) :
    IsCliffordHierarchy 1 (scaleEquiv α (pauliEquiv p)) :=
  .base (isPhasedPauli_scale_pauliEquiv α p)

/-! ## Monotonicity of the operational Clifford hierarchy

`IsCliffordHierarchy k U → IsCliffordHierarchy k' U` for `k ≤ k'`.

The proof has three layers:

1. **`IsPhasedPauli.symm_apply_form`**: given `U.toLinearMap = α •
   pauliOperator p_U`, derive a closed form for `U.symm`:
   `U.symm ψ = (-1)^{p_U.Z · p_U.X} · α⁻¹ • pauliOperator p_U ψ`.
   This is forced because `pauliOperator p_U` is its own inverse up
   to the sign `(-1)^{p_U.Z · p_U.X}` (`pauliOperator_squared`).

2. **`IsCliffordHierarchy.two_of_one`** (base step `1 → 2`): for any
   phased Pauli `U` and any Pauli `q`, the conjugate `conjEquiv U
   (pauliEquiv q)` is again a phased Pauli, hence sits at level `1`.
   The computation chains `pauliOperator_mul` twice to combine three
   Pauli operators and uses `p_U + q + p_U = q` in `(ZMod 2)^n`.

3. **`IsCliffordHierarchy.succ`** (step `k → k+1`): induct on the
   level-`k` proof of `IsCliffordHierarchy k U`. The `base` case
   reduces to step 2; the `step` case uses the induction hypothesis
   on each conjugate. Then **`IsCliffordHierarchy.mono`** chains
   `succ` along the difference `k' - k`.
-/

/-- Closed form for the inverse of a phased Pauli. If
`U.toLinearMap = α • pauliOperator p_U`, then
`U.symm ψ = ((-1)^{p_U.Z · p_U.X} · α⁻¹) • pauliOperator p_U ψ`.

This is forced: `pauliOperator p_U` is its own inverse up to the sign
`(-1)^{p_U.Z · p_U.X}` from `pauliOperator_squared`, so the inverse
of `α • pauliOperator p_U` is the scaled version that absorbs both
factors. -/
private lemma IsPhasedPauli.symm_apply_form
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} {α : ℂˣ} {p_U : Pauli n}
    (hU : U.toLinearMap = (α : ℂ) • (pauliOperator p_U))
    (ψ : QubitSpace n) :
    U.symm ψ =
      (((-1 : ℂ)^(zDotVal p_U p_U.X)) * ((α⁻¹ : ℂˣ) : ℂ)) •
        pauliOperator p_U ψ := by
  -- Strategy: from U φ = α • pauliOperator p_U φ, deduce
  --   pauliOperator p_U (U.symm ψ) = α⁻¹ • ψ.
  -- Then apply pauliOperator p_U again and use pauliOperator_squared.
  have hU_apply : ∀ φ : QubitSpace n,
      U φ = (α : ℂ) • pauliOperator p_U φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hU
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    -- `LinearEquiv.coe_coe` rewrites `U.toLinearMap φ` to `U φ`.
    exact h
  -- (1) U (U.symm ψ) = ψ.
  have step1 : U (U.symm ψ) = ψ := LinearEquiv.apply_symm_apply U ψ
  -- (2) Substitute hU_apply into step1: α • pauliOperator p_U (U.symm ψ) = ψ.
  rw [hU_apply] at step1
  -- (3) Multiply both sides by α⁻¹: pauliOperator p_U (U.symm ψ) = α⁻¹ • ψ.
  have hα_inv_left : ((α⁻¹ : ℂˣ) : ℂ) * (α : ℂ) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero α)]
  have step2 : pauliOperator p_U (U.symm ψ) = ((α⁻¹ : ℂˣ) : ℂ) • ψ := by
    have h := congrArg (fun (φ : QubitSpace n) => ((α⁻¹ : ℂˣ) : ℂ) • φ) step1
    simp only at h
    -- h : α⁻¹ • (α • pauliOperator p_U (U.symm ψ)) = α⁻¹ • ψ.
    rw [smul_smul, hα_inv_left, one_smul] at h
    exact h
  -- (4) Apply pauliOperator p_U to both sides of step2:
  --   pauliOperator p_U (pauliOperator p_U (U.symm ψ)) = pauliOperator p_U (α⁻¹ • ψ).
  -- LHS via pauliOperator_squared = (-1)^{p_U.Z·p_U.X} • U.symm ψ.
  -- RHS via map_smul = α⁻¹ • pauliOperator p_U ψ.
  have step3 :
      ((-1 : ℂ)^(zDotVal p_U p_U.X)) • U.symm ψ =
        ((α⁻¹ : ℂˣ) : ℂ) • pauliOperator p_U ψ := by
    have hsq := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L (U.symm ψ))
      (pauliOperator_squared p_U)
    -- hsq : pauliOperator p_U (pauliOperator p_U (U.symm ψ)) =
    --         (-1)^{p_U.Z·p_U.X} • (LinearMap.id) (U.symm ψ)
    --     = (-1)^{p_U.Z·p_U.X} • U.symm ψ.
    simp only [LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply] at hsq
    -- Now apply pauliOperator p_U to both sides of step2:
    have h := congrArg (fun (φ : QubitSpace n) => pauliOperator p_U φ) step2
    simp only at h
    -- h : pauliOperator p_U (pauliOperator p_U (U.symm ψ))
    --     = pauliOperator p_U (α⁻¹ • ψ).
    rw [LinearMap.map_smul] at h
    -- h : ... = α⁻¹ • pauliOperator p_U ψ.
    rw [hsq] at h
    exact h
  -- (5) From step3, isolate U.symm ψ by multiplying by (-1)^{p_U.Z·p_U.X}.
  -- We use the squared-to-1 fact: (-1)^k · (-1)^k = 1.
  have h_sq_one :
      ((-1 : ℂ)^(zDotVal p_U p_U.X)) * ((-1 : ℂ)^(zDotVal p_U p_U.X)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  -- From step3: x • A = y • B  →  x • (x • A) = x • (y • B) → A = x • y • B
  -- (using smul_smul and h_sq_one).
  have h6 :
      ((-1 : ℂ)^(zDotVal p_U p_U.X)) •
          ((-1 : ℂ)^(zDotVal p_U p_U.X)) • U.symm ψ =
        ((-1 : ℂ)^(zDotVal p_U p_U.X)) •
          ((α⁻¹ : ℂˣ) : ℂ) • pauliOperator p_U ψ :=
    congrArg (fun φ => ((-1 : ℂ)^(zDotVal p_U p_U.X)) • φ) step3
  rw [smul_smul] at h6
  rw [h_sq_one, one_smul, smul_smul] at h6
  exact h6

/-- **Base step (1 → 2)**: every phased Pauli sits at level 2 of the
operational Clifford hierarchy.

Given `U` with `U.toLinearMap = α • pauliOperator p_U`, we need to
show that for every Pauli `q`, `conjEquiv U (pauliEquiv q)` is a
phased Pauli. The computation:

  `conjEquiv U (pauliEquiv q) ψ = U (pauliOperator q (U.symm ψ))`.

Plug in the closed form for `U.symm` from `IsPhasedPauli.symm_apply_form`,
then chain `pauliOperator_mul` twice. Using `p_U + q + p_U = q` (a
`Pauli n`-level identity in characteristic 2), the result is
`(some unit sign) • pauliOperator q ψ`, hence a phased Pauli with
Pauli `q`. -/
theorem IsCliffordHierarchy.two_of_one
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsPhasedPauli U) :
    IsCliffordHierarchy 2 U := by
  refine .step (fun q => .base ?_)
  -- Goal: IsPhasedPauli (conjEquiv U (pauliEquiv q)).
  obtain ⟨α, p_U, hα⟩ := hU
  -- The phase is (-1)^{p_U.Z·p_U.X + q.Z·p_U.X + p_U.Z·(p_U+q).X}.
  -- It's ±1, hence a unit in ℂˣ.
  set e : ℕ := zDotVal p_U p_U.X + zDotVal q p_U.X + zDotVal p_U (p_U + q).X
    with he_def
  have hpow_ne_zero : ((-1 : ℂ)^e) ≠ 0 := by
    refine pow_ne_zero _ ?_
    norm_num
  refine ⟨Units.mk0 ((-1 : ℂ)^e) hpow_ne_zero, q, ?_⟩
  -- Show: (conjEquiv U (pauliEquiv q)).toLinearMap
  --        = (-1)^e • pauliOperator q.
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe,
    Units.val_mk0]
  -- LHS: conjEquiv U (pauliEquiv q) ψ = U (pauliEquiv q (U.symm ψ))
  --                                 = U (pauliOperator q (U.symm ψ)).
  change conjEquiv U (pauliEquiv q) ψ = ((-1 : ℂ)^e) • pauliOperator q ψ
  rw [conjEquiv_apply, pauliEquiv_apply]
  -- Plug in the closed form for U.symm ψ.
  rw [IsPhasedPauli.symm_apply_form hα ψ]
  -- Goal:
  --   U (pauliOperator q (((-1)^{p_U.Z·p_U.X} * α⁻¹) • pauliOperator p_U ψ))
  --     = (-1)^e • pauliOperator q ψ.
  -- Pull the scalar out of `pauliOperator q`.
  rw [LinearMap.map_smul (pauliOperator q)]
  -- Goal:
  --   U (((-1)^{p_U.Z·p_U.X} * α⁻¹) • pauliOperator q (pauliOperator p_U ψ))
  --     = (-1)^e • pauliOperator q ψ.
  -- Use pauliOperator_mul p_U q:
  --   pauliOperator q (pauliOperator p_U ψ) = (-1)^{q.Z·p_U.X} • pauliOperator (p_U+q) ψ.
  rw [show pauliOperator q (pauliOperator p_U ψ)
        = ((-1 : ℂ)^(zDotVal q p_U.X)) • pauliOperator (p_U + q) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul p_U q)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  -- Goal:
  --   U (((-1)^{p_U.Z·p_U.X} * α⁻¹) • ((-1)^{q.Z·p_U.X} • pauliOperator (p_U+q) ψ))
  --     = (-1)^e • pauliOperator q ψ.
  rw [smul_smul]
  -- Apply U:  U φ = α • pauliOperator p_U φ.
  have hU_apply : ∀ φ : QubitSpace n,
      U φ = (α : ℂ) • pauliOperator p_U φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  rw [hU_apply]
  -- Goal:
  --   α • pauliOperator p_U
  --     ((((-1)^{p_U.Z·p_U.X} * α⁻¹) * (-1)^{q.Z·p_U.X}) • pauliOperator (p_U+q) ψ)
  --     = (-1)^e • pauliOperator q ψ.
  rw [LinearMap.map_smul (pauliOperator p_U)]
  rw [smul_smul]
  -- Use pauliOperator_mul (p_U + q) p_U:
  --   pauliOperator p_U (pauliOperator (p_U+q) ψ) =
  --     (-1)^{p_U.Z·(p_U+q).X} • pauliOperator ((p_U+q) + p_U) ψ.
  rw [show pauliOperator p_U (pauliOperator (p_U + q) ψ)
        = ((-1 : ℂ)^(zDotVal p_U (p_U + q).X)) •
            pauliOperator ((p_U + q) + p_U) ψ from by
      have h := congrArg
        (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul (p_U + q) p_U)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at h
      exact h]
  -- (p_U + q) + p_U = q in Pauli n (Z/2 coefficients).
  have hpq : (p_U + q) + p_U = q := by
    have h2pU : p_U + p_U = (0 : Pauli n) := by
      ext i
      · -- X-component: 2·p_U.X i = 0 in ZMod 2.
        change p_U.X i + p_U.X i = (0 : Pauli n).X i
        simp [CharTwo.add_self_eq_zero]
      · -- Z-component: 2·p_U.Z i = 0 in ZMod 2.
        change p_U.Z i + p_U.Z i = (0 : Pauli n).Z i
        simp [CharTwo.add_self_eq_zero]
    -- (p_U + q) + p_U = q + (p_U + p_U) = q + 0 = q.
    have : (p_U + q) + p_U = q + (p_U + p_U) := by abel
    rw [this, h2pU, add_zero]
  rw [hpq, smul_smul]
  -- Goal: scalar1 • pauliOperator q ψ = (-1)^e • pauliOperator q ψ.
  -- We just need the scalars to match.
  congr 1
  -- Compute the scalar.
  -- scalar1 = α * (((-1)^{p_U.Z·p_U.X} * α⁻¹) * (-1)^{q.Z·p_U.X} * (-1)^{p_U.Z·(p_U+q).X})
  --        = α * α⁻¹ * (-1)^{p_U.Z·p_U.X + q.Z·p_U.X + p_U.Z·(p_U+q).X}
  --        = (-1)^e.
  have hα_α_inv : (α : ℂ) * ((α⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero α)]
  rw [he_def]
  rw [pow_add, pow_add]
  ring_nf
  rw [hα_α_inv]
  ring

/-- **Successor step**: `IsCliffordHierarchy k U → IsCliffordHierarchy (k+1) U`.

Proof by induction on the level-`k` hierarchy proof of `U`.

* `base` case (k=1): `U` is a phased Pauli; apply `two_of_one`.
* `step` case (k = k'+1, with hypothesis `∀ p, IsCliffordHierarchy k'
  (conjEquiv U (pauliEquiv p))` and IH `∀ p, IsCliffordHierarchy (k'+1)
  (conjEquiv U (pauliEquiv p))`): apply `step` constructor with the
  IH. -/
theorem IsCliffordHierarchy.succ {k : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchy k U) :
    IsCliffordHierarchy (k + 1) U := by
  induction h with
  | base hU =>
      -- Level 1: U is a phased Pauli. Climb to level 2.
      exact two_of_one hU
  | step _ ih =>
      -- Level k'+1: the IH gives that each conjugate climbs from k'
      -- to k'+1. So U climbs from k'+1 to k'+2.
      exact .step (fun q => ih q)

/-- **Monotonicity**: `IsCliffordHierarchy k U → IsCliffordHierarchy k' U`
for `k ≤ k'`. Proof: chain `succ` along the difference `k' - k`. -/
theorem IsCliffordHierarchy.mono {k k' : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hkk' : k ≤ k') (h : IsCliffordHierarchy k U) :
    IsCliffordHierarchy k' U := by
  -- Induct on the difference `k' - k`.
  obtain ⟨d, rfl⟩ := Nat.le.dest hkk'
  clear hkk'
  -- Now goal: IsCliffordHierarchy (k + d) U.
  induction d with
  | zero =>
      -- k + 0 = k, so we're done.
      rw [Nat.add_zero]
      exact h
  | succ d ih =>
      -- IsCliffordHierarchy (k + d) U  →  IsCliffordHierarchy (k + (d + 1)) U.
      -- Use the induction hypothesis to climb to (k + d), then `succ` once more.
      rw [← Nat.add_assoc]
      exact ih.succ

end FTQCLib.Hilbert

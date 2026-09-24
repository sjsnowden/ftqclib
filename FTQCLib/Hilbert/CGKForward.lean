/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGK
import FTQCLib.Hilbert.Hierarchy
import FTQCLib.Hilbert.DiagonalEquiv
import FTQCLib.Hierarchy.Descent
import FTQCLib.Hierarchy.HierarchyLevel
import FTQCLib.Hierarchy.RzHardness
import FTQCLib.Hierarchy.FuncDeriv
import FTQCLib.Hierarchy.BoolReduce
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.BoolReduceLevel

set_option linter.unusedSectionVars false

/-! # Cui-Gottesman-Krishna, forward direction

This file proves the forward direction of the Cui-Gottesman-Krishna
(CGK) equivalence.

CGK 2017 (arXiv 1608.06596) Theorem 2 states: a diagonal unitary
`U_P = ∑_v exp(2πi · P(v) / 2^m) |v⟩⟨v|` sits at level
`(m-1) + totalDegree(P)` of the Clifford hierarchy. The polynomial-
side predicate `IsDiagonalHierarchyLevel k P` from
`FTQCLib/Hierarchy/HierarchyLevel.lean` already records the level
inequality on the polynomial side. The operational-side predicate
`IsCliffordHierarchy k U` from `FTQCLib/Hilbert/Hierarchy.lean` records
the recursive definition on the operator side. The forward direction
of CGK says the polynomial-side bound *implies* the operator-side
predicate via `diagonalGateEquiv (realPhase P)`.

## Proof structure

By induction on the level `k`:

1. **Base case** (`totalDegree(P) = 0`): `P` is a constant `c`. The
   gate is the scalar `exp(I · 2π · c / 2^m)` times the identity.
   The identity is `pauliOperator 0`, so the gate is a phased Pauli,
   in `C^(1)`. Lifted by monotonicity to `C^(k)` for any `k ≥ 1`.
2. **Inductive step** (`totalDegree(P) ≥ 1`): to show
   `diagonalGateEquiv (realPhase P) ∈ C^(k+1)`, use the `.step`
   constructor — for every Pauli `q`, the conjugate
   `conjEquiv (diagonalGateEquiv (realPhase P)) (pauliEquiv q)` must
   sit at level `k`. The general descent identity
   `conjEquiv_diagonalGateEquiv_general` writes this conjugate as the
   diagonal gate of the shifted phase `f(· + q.X) - f(·)` followed by
   `pauliEquiv q`. Replacing `P` by its multilinear Boolean reduction
   `boolReduce P`, the shifted phase is the real phase of
   `shiftBy q.X (boolReduce P)` modulo `2π`, whose effective level is
   strictly smaller (`shiftByStrictDrop_general`). The inductive
   hypothesis and right-multiplication closure
   (`IsCliffordHierarchy.trans_pauliEquiv`) finish the step.

The polynomial discrete derivative `discreteDeriv` does not realise the
operator-side phase difference for `m ≥ 2`, which is why the proof uses
the binary-correct shift `shiftBy` instead. The hypothesis of
`cgk_forward` is `(boolReduce P).effectiveLevel + 1 ≤ k`; the sharp bound
is `cgk_forward_sharp` and
`IsCliffordHierarchyPolyEncodable.toCliffordHierarchy_sharp` in
`FTQCLib/Hilbert/CGKSharpForward.lean`, and the two-sided classification
is in `FTQCLib/Hilbert/CGKTwoSided.lean`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n m : ℕ}

/-! ## Base case: constant phase polynomial → phased identity

A `P : DiagPhase n m` with `totalDegree(P) = 0` is constant
(`P = MvPolynomial.C c` for `c = P.coeff 0`). The diagonal gate then
applies the same phase `exp(I · 2π · c.val / 2^m)` to every basis
vector, i.e. it is a global phase multiple of the identity
`pauliOperator 0`. Hence it is a phased Pauli, in `IsCliffordHierarchy 1`.
By monotonicity it lifts to `IsCliffordHierarchy k` for any `k ≥ 1`.
-/

/-- For constant `P` (`P = MvPolynomial.C c`), the real phase
`realPhase P v` does not depend on `v`: it equals the constant
`2π · c.val / 2^m` at every input. -/
private theorem realPhase_const {P : DiagPhase n m}
    (hP : P = MvPolynomial.C (P.coeff 0)) (v : Fin n → ZMod 2) :
    realPhase P v = 2 * Real.pi * (P.coeff 0).val / (2 : ℝ)^m := by
  unfold realPhase
  unfold DiagPhase.eval
  conv_lhs => rw [hP]
  rw [MvPolynomial.eval_C]

/-- For constant `P`, the diagonal gate `diagonalGateEquiv (realPhase P)`
agrees as a linear map with the scalar `exp(I · θ_P)` times
`pauliOperator 0`, where `θ_P = 2π · (P.coeff 0).val / 2^m`. -/
private lemma diagonalGateEquiv_const_toLinearMap {P : DiagPhase n m}
    (hP : P = MvPolynomial.C (P.coeff 0)) :
    (diagonalGateEquiv (DiagPhase.realPhase P)).toLinearMap =
      (Complex.exp (Complex.I *
          (((2 * Real.pi * (P.coeff 0).val / (2 : ℝ)^m : ℝ) : ℂ)))) •
        (pauliOperator (0 : Pauli n)) := by
  apply LinearMap.ext
  intro ψ
  funext v
  rw [pauliOperator_zero]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply,
    smul_eq_mul]
  change diagonalGate (DiagPhase.realPhase P) ψ v =
    Complex.exp (Complex.I *
        (((2 * Real.pi * (P.coeff 0).val / (2 : ℝ)^m : ℝ) : ℂ))) * ψ v
  rw [diagonalGate_apply]
  rw [realPhase_const hP]

/-- A constant phase polynomial gives a phased Pauli (with Pauli `0`). -/
theorem isPhasedPauli_diagonalGateEquiv_of_const {P : DiagPhase n m}
    (hP : P = MvPolynomial.C (P.coeff 0)) :
    IsPhasedPauli (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  refine ⟨Units.mk0
            (Complex.exp (Complex.I *
              (((2 * Real.pi * (P.coeff 0).val / (2 : ℝ)^m : ℝ) : ℂ))))
            (Complex.exp_ne_zero _),
          0, ?_⟩
  rw [diagonalGateEquiv_const_toLinearMap hP]
  rfl

/-- A constant phase polynomial gives a level-1 hierarchy element. -/
theorem isCliffordHierarchy_one_of_totalDegree_zero
    {P : DiagPhase n m} (hP : P.totalDegree = 0) :
    IsCliffordHierarchy 1 (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  have hP_C : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hP
  exact .base (isPhasedPauli_diagonalGateEquiv_of_const hP_C)

/-- A constant phase polynomial gives a level-`k` hierarchy element for
any `k ≥ 1` (lifted via monotonicity from level 1). -/
theorem isCliffordHierarchy_of_totalDegree_zero
    {P : DiagPhase n m} (hP : P.totalDegree = 0) {k : ℕ} (hk : 1 ≤ k) :
    IsCliffordHierarchy k (diagonalGateEquiv (DiagPhase.realPhase P)) :=
  (isCliffordHierarchy_one_of_totalDegree_zero hP).mono hk

/-! ## Pauli left-multiplication closure: the level-1 (base) case

The lemma below is the level-1 case of Pauli left-multiplication
closure (`IsCliffordHierarchy.pauliEquiv_trans` below). It is
structural (purely about products of Paulis) and does not require any
phase-polynomial content.

If `V` is a phased Pauli, so is
`(pauliEquiv p).trans V`. Proof: write `V.toLinearMap = α · pauliOperator q`,
then `(pauliEquiv p).trans V` applies `pauliOperator q ∘ pauliOperator p`
on the right, which by `pauliOperator_mul` is `(-1)^... • pauliOperator (p+q)`.
The scalar `(-1)^... · α` is a unit; the Pauli is `p + q`. -/
theorem IsPhasedPauli.pauliEquiv_trans {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (p : Pauli n) (hV : IsPhasedPauli V) :
    IsPhasedPauli ((pauliEquiv p).trans V) := by
  obtain ⟨α, q, hα⟩ := hV
  -- The combined phase is α · (-1)^{q.Z · p.X}, and the combined
  -- Pauli is p + q.
  set β : ℂ := (α : ℂ) * (-1 : ℂ) ^ (zDotVal q p.X) with hβ_def
  have hβ_ne_zero : β ≠ 0 := by
    rw [hβ_def]
    refine mul_ne_zero (Units.ne_zero α) ?_
    refine pow_ne_zero _ ?_
    norm_num
  refine ⟨Units.mk0 β hβ_ne_zero, p + q, ?_⟩
  apply LinearMap.ext
  intro ψ
  -- LHS: ((pauliEquiv p).trans V) ψ = V (pauliEquiv p ψ)
  --                                = V (pauliOperator p ψ).
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, pauliEquiv_apply,
    LinearMap.smul_apply, Units.val_mk0]
  -- Express V via hα.
  have hV_apply : ∀ φ : QubitSpace n, V φ = (α : ℂ) • pauliOperator q φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  rw [hV_apply]
  -- Goal: α • pauliOperator q (pauliOperator p ψ) = β • pauliOperator (p+q) ψ.
  -- Apply pauliOperator_mul p q.
  rw [show pauliOperator q (pauliOperator p ψ) =
        ((-1 : ℂ)^(zDotVal q p.X)) • pauliOperator (p + q) ψ from by
    have h := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
      (pauliOperator_mul p q)
    simp only [LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply] at h
    exact h]
  rw [smul_smul, hβ_def]

/-- Inverting `IsCliffordHierarchy 1 V` always produces a phased
Pauli witness. The `step` case of the inductive definition at level
`k+1 = 1` would require `k = 0` and an `IsCliffordHierarchy 0`
witness for every conjugate, but `IsCliffordHierarchy 0` is
uninhabited (no constructor produces a `0`). So inversion reduces
to `base`. -/
private theorem isPhasedPauli_of_isCliffordHierarchy_one
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hV : IsCliffordHierarchy 1 V) : IsPhasedPauli V := by
  generalize hk : (1 : ℕ) = k at hV
  cases hV with
  | base h => exact h
  | @step k' V hstep =>
      -- `k' + 1 = 1`, so `k' = 0`. Use `hstep` at `q = 0` to derive
      -- a contradiction: `IsCliffordHierarchy 0 _` is uninhabited.
      have hk' : k' = 0 := by omega
      subst hk'
      -- `hstep 0` is now `IsCliffordHierarchy 0 _`. Inverting this
      -- shows it cannot be `base` (since `base` gives level 1) and
      -- cannot be `step` (since `step` gives level k+1 ≥ 1). The
      -- generalize trick gives us a `(0 = 1)` contradiction.
      exact (level_zero_uninhabited (hstep 0)).elim
where
  level_zero_uninhabited :
      ∀ {V' : QubitSpace n ≃ₗ[ℂ] QubitSpace n},
        ¬ IsCliffordHierarchy 0 V' := by
    intro V' h
    generalize hl : (0 : ℕ) = l at h
    cases h with
    | base _ => omega
    | @step k' V'' _ => omega

/-- Level-1 Pauli left-multiplication closure: if `V` is at level 1, so is
`(pauliEquiv p).trans V`. Proof: extract the phased Pauli witness, use
`IsPhasedPauli.pauliEquiv_trans` to combine, then re-package as level 1. -/
theorem IsCliffordHierarchy.one_pauliEquiv_trans
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (p : Pauli n)
    (hV : IsCliffordHierarchy 1 V) :
    IsCliffordHierarchy 1 ((pauliEquiv p).trans V) :=
  .base ((isPhasedPauli_of_isCliffordHierarchy_one hV).pauliEquiv_trans p)

/-! ## Scalar-closure of the operational Clifford hierarchy

The operational hierarchy is closed under scalar multiplication: if
`V ∈ C^(k)` and `β : ℂˣ`, then `scaleEquiv β V ∈ C^(k)`. The proof
is by induction on `k`:

* Base (k=1): `V` is a phased Pauli `α · pauliOperator q`, so
  `scaleEquiv β V` is `(β · α) · pauliOperator q`, again a phased
  Pauli.
* Inductive step (k = k'+1): conjugating by a Pauli `p` cancels the
  scalar (the β on the left and β⁻¹ on the right combine to 1), so
  `conjEquiv (scaleEquiv β V) (pauliEquiv p) = conjEquiv V (pauliEquiv p)`,
  which is in `C^(k')` by the level-(k'+1) hypothesis on `V`.

It is used for Pauli left-multiplication closure at arbitrary level.
-/

/-- Scaling a phased Pauli by a unit yields another phased Pauli. -/
theorem IsPhasedPauli.scaleEquiv (β : ℂˣ)
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hV : IsPhasedPauli V) :
    IsPhasedPauli (scaleEquiv β V) := by
  obtain ⟨α, q, hα⟩ := hV
  refine ⟨β * α, q, ?_⟩
  apply LinearMap.ext
  intro ψ
  rw [scaleEquiv_toLinearMap, hα]
  simp only [LinearMap.smul_apply, Units.val_mul]
  rw [mul_smul]

/-- Conjugation by a Pauli annihilates the scaling factor: for any
unit `β` and any `V`, conjugating `scaleEquiv β V` by `pauliEquiv p`
gives the same map as conjugating `V` by `pauliEquiv p`. The β on
the left and β⁻¹ on the right cancel. -/
private lemma conjEquiv_scaleEquiv (β : ℂˣ)
    (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (p : Pauli n) :
    conjEquiv (scaleEquiv β V) (pauliEquiv p) = conjEquiv V (pauliEquiv p) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  -- Both sides unfold to U.symm.trans (pauliEquiv p).trans U applied to ψ.
  simp only [conjEquiv_apply, scaleEquiv_apply, scaleEquiv_symm_apply,
    pauliEquiv_apply, LinearEquiv.coe_coe]
  -- LHS: β • V (pauliOperator p (β⁻¹ • V.symm ψ)).
  -- pauliOperator p is linear, so pulls β⁻¹: β • V (β⁻¹ • pauliOperator p (V.symm ψ)).
  -- V is linear, so pulls β⁻¹: β • β⁻¹ • V (pauliOperator p (V.symm ψ)) = ...
  rw [LinearMap.map_smul, LinearEquiv.map_smul]
  rw [smul_smul]
  rw [show (β : ℂ) * ((β⁻¹ : ℂˣ) : ℂ) = 1 from by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero β)]]
  rw [one_smul]

/-- The operational Clifford hierarchy is closed under scalar
multiplication by a unit. -/
theorem IsCliffordHierarchy.scaleEquiv (β : ℂˣ) {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hV : IsCliffordHierarchy k V) :
    IsCliffordHierarchy k (FTQCLib.Hilbert.scaleEquiv β V) := by
  -- Induct on hV; the IH is unused because `conjEquiv_scaleEquiv`
  -- directly identifies the conjugate of `scaleEquiv β V` with the
  -- conjugate of `V`.
  induction hV with
  | base h => exact .base (h.scaleEquiv β)
  | @step k V hstep _ =>
      refine .step (fun p => ?_)
      rw [conjEquiv_scaleEquiv]
      exact hstep p

/-! ## Pauli left-multiplication closure at arbitrary level

We now extend the level-1 result `IsCliffordHierarchy.one_pauliEquiv_trans`
to arbitrary level `k`. The proof has two ingredients:

1. **Conjugate-of-composition identity** (`conjEquiv_pauliEquiv_trans`):
   `conjEquiv ((pauliEquiv p).trans V) (pauliEquiv q)`
   = `scaleEquiv α' (conjEquiv V (pauliEquiv q'))`,
   where `α'` and `q'` are the phase and Pauli of the phased-Pauli
   conjugate `conjEquiv (pauliEquiv p) (pauliEquiv q)`. (This is just
   `two_of_one` applied to `pauliEquiv p`, plus pushing `V` through
   the resulting scalar via linearity.)
2. **`IsCliffordHierarchy.scaleEquiv`** (proved above): the hierarchy
   is closed under scalar multiplication.

Combining: at the step level `k+1`, `V`'s hypothesis says
`conjEquiv V (pauliEquiv q') ∈ C^k`. Scalar-scale it by `α'` to land
in `C^k` again. That's exactly the conjugate of
`(pauliEquiv p).trans V` by `pauliEquiv q`. Iterating across all `q`
yields `(pauliEquiv p).trans V ∈ C^(k+1)`. -/

/-- The conjugate-of-composition identity. -/
private lemma conjEquiv_pauliEquiv_trans_eq
    (p q : Pauli n) (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    ∃ (α' : ℂˣ) (q' : Pauli n),
      conjEquiv ((pauliEquiv p).trans V) (pauliEquiv q) =
        FTQCLib.Hilbert.scaleEquiv α' (conjEquiv V (pauliEquiv q')) := by
  -- The conjugate of pauliEquiv q by pauliEquiv p is a phased Pauli.
  have hConj : IsPhasedPauli (conjEquiv (pauliEquiv p) (pauliEquiv q)) := by
    have h := IsCliffordHierarchy.two_of_one
      (isPhasedPauli_pauliEquiv p)
    -- h : IsCliffordHierarchy 2 (pauliEquiv p).
    -- Inspect: h = .step (fun q' => .base ?_).
    cases h with
    | @step _ _ hstep =>
        -- hstep : ∀ q', IsCliffordHierarchy 1 (conjEquiv (pauliEquiv p) (pauliEquiv q'))
        -- Apply hstep at our q, then unfold the level-1 hypothesis.
        exact isPhasedPauli_of_isCliffordHierarchy_one (hstep q)
  obtain ⟨α', q', hα'⟩ := hConj
  refine ⟨α', q', ?_⟩
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  -- LHS: conjEquiv ((pauliEquiv p).trans V) (pauliEquiv q) ψ
  --   = (pauliEquiv p).trans V (pauliEquiv q (((pauliEquiv p).trans V).symm ψ))
  --   = V (pauliEquiv p (pauliEquiv q ((pauliEquiv p).symm (V.symm ψ))))
  --   = V (conjEquiv (pauliEquiv p) (pauliEquiv q) (V.symm ψ))
  --   = V (α' • pauliOperator q' (V.symm ψ))   [via hα']
  --   = α' • V (pauliOperator q' (V.symm ψ))   [linearity of V]
  --   = α' • V (pauliEquiv q' (V.symm ψ))      [pauliEquiv_apply]
  --   = α' • conjEquiv V (pauliEquiv q') ψ.
  -- RHS: scaleEquiv α' (conjEquiv V (pauliEquiv q')) ψ
  --   = α' • conjEquiv V (pauliEquiv q') ψ
  --   = α' • V (pauliEquiv q' (V.symm ψ)).
  simp only [conjEquiv_apply, LinearEquiv.coe_coe, scaleEquiv_apply,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, pauliEquiv_apply]
  -- We want: V (pauliOperator p (pauliOperator q ((pauliEquiv p).symm (V.symm ψ))))
  --        = α' • V (pauliOperator q' (V.symm ψ)).
  -- Rewrite the inner triple as conjEquiv (pauliEquiv p) (pauliEquiv q) (V.symm ψ).
  -- Use hα': (conjEquiv (pauliEquiv p) (pauliEquiv q)).toLinearMap = α' • pauliOperator q'.
  have hConj_apply :
      conjEquiv (pauliEquiv p) (pauliEquiv q) (V.symm ψ) =
        (α' : ℂ) • pauliOperator q' (V.symm ψ) := by
    have h := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L (V.symm ψ)) hα'
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  -- The LHS-side conjugate matches.
  have hLHS_form :
      pauliOperator p (pauliOperator q ((pauliEquiv p).symm (V.symm ψ)))
        = conjEquiv (pauliEquiv p) (pauliEquiv q) (V.symm ψ) := by
    rfl
  rw [hLHS_form, hConj_apply]
  -- Goal: V ((α' : ℂ) • pauliOperator q' (V.symm ψ))
  --     = (α' : ℂ) • V (pauliOperator q' (V.symm ψ)).
  rw [LinearEquiv.map_smul]

/-- **Pauli left-multiplication closure.** If
`V ∈ C^(k)`, then `(pauliEquiv p).trans V ∈ C^(k)`. -/
theorem IsCliffordHierarchy.pauliEquiv_trans {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (p : Pauli n) (hV : IsCliffordHierarchy k V) :
    IsCliffordHierarchy k ((pauliEquiv p).trans V) := by
  induction hV with
  | base h =>
      -- Level 1: V is a phased Pauli.
      exact .base (h.pauliEquiv_trans p)
  | @step k V hstep _ =>
      -- Level k+1: V satisfies `∀ q, conjEquiv V (pauliEquiv q) ∈ C^k`.
      -- We must show: ∀ q, conjEquiv ((pauliEquiv p).trans V) (pauliEquiv q) ∈ C^k.
      refine .step (fun q => ?_)
      -- Use the identity from `conjEquiv_pauliEquiv_trans_eq`.
      obtain ⟨α', q', hEq⟩ := conjEquiv_pauliEquiv_trans_eq p q V
      rw [hEq]
      -- Goal: IsCliffordHierarchy k (scaleEquiv α' (conjEquiv V (pauliEquiv q'))).
      -- Apply scalar-closure to the conjugate (which is in C^k by V's hypothesis).
      exact (hstep q').scaleEquiv α'

/-! ## Conjugating the diagonal gate by a single `paulix`

The operator-side descent rule `diagonalGate_paulix_shift` from
`CGK.lean` says

  `U ∘ pauliOperator (paulix i)
     = pauliOperator (paulix i) ∘ diagonalGate (realPhase-shift)`.

Below we lift this to a `LinearEquiv` identity for `conjEquiv U
(pauliEquiv (paulix i))`. The result is `(pauliEquiv (paulix i)).trans
(diagonal-difference-equiv)`, where the difference equiv has phase
pattern `realPhase P (· + e_i) - realPhase P ·`. This is the **shape**
of the descent on the operator side. The matching polynomial-side level
drop is supplied by `shiftBy` below.
-/

/-- The conjugate of `pauliEquiv (paulix i)` by `diagonalGateEquiv
(realPhase P)` equals the composition `diagonalGate(shift-difference)
followed by pauliEquiv (paulix i)`, where `shift-difference v =
realPhase P (v + e_i) - realPhase P v`. This is the operator-side
descent in `LinearEquiv` form. -/
theorem conjEquiv_diagonalGateEquiv_paulix
    (P : DiagPhase n m) (i : Fin n) :
    conjEquiv (diagonalGateEquiv (DiagPhase.realPhase P))
        (pauliEquiv (paulix i)) =
      (diagonalGateEquiv (fun v : Fin n → ZMod 2 =>
          DiagPhase.realPhase P (v + Pi.single i 1) -
            DiagPhase.realPhase P v)).trans
        (pauliEquiv (paulix i)) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  funext w
  -- Strategy: write the conjugate at ψ as U · X · U⁻¹ ψ where U =
  -- diagonalGate (realPhase P), U.symm = diagonalGate (- realPhase P).
  -- The RHS computes as X · D' ψ where D' has the shift-difference
  -- pattern. Reduce both sides at w to the same scalar times
  -- ψ (w - e_i).
  simp only [conjEquiv_apply, LinearEquiv.coe_coe,
    diagonalGateEquiv_symm_apply, pauliEquiv_apply,
    LinearEquiv.trans_apply, diagonalGateEquiv_apply]
  unfold diagonalGate pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- (paulix i).Z = 0 so zDotVal = 0 on every input.
  have hX : (paulix i).X = Pi.single i 1 := rfl
  have hzdot : ∀ u : Fin n → ZMod 2, zDotVal (paulix i) u = 0 := by
    intro u
    unfold zDotVal
    refine Finset.sum_eq_zero ?_
    intro j _
    have h0 : ((paulix i).Z j).val = 0 := by
      have hZj : (paulix i).Z j = (0 : ZMod 2) := rfl
      rw [hZj]
      exact ZMod.val_zero
    rw [h0]; ring
  rw [hX]
  rw [hzdot]
  simp only [pow_zero, one_mul]
  -- LHS at w:
  --   exp(I · realPhase P w) · (exp(I · (- realPhase P (w - e_i))) · ψ (w - e_i)).
  -- RHS at w:
  --   1 · (exp(I · (realPhase P (w - e_i + e_i) - realPhase P (w - e_i))) · ψ (w - e_i))
  --   = exp(I · (realPhase P w - realPhase P (w - e_i))) · ψ (w - e_i).
  have hw : w - Pi.single i 1 + Pi.single i 1 = w := by ring
  rw [hw]
  -- The exponents combine via exp_add.
  rw [show (Complex.exp (Complex.I * ((realPhase P w) : ℂ)) *
            (Complex.exp (Complex.I * ((- realPhase P (w - Pi.single i 1) : ℝ) : ℂ)) *
              ψ (w - Pi.single i 1)))
        = (Complex.exp (Complex.I * ((realPhase P w) : ℂ)) *
            Complex.exp (Complex.I * ((- realPhase P (w - Pi.single i 1) : ℝ) : ℂ))) *
          ψ (w - Pi.single i 1) from by ring]
  rw [← Complex.exp_add]
  -- Goal: exp(I·realPhase P w + I·(-realPhase P (w-e_i))) · ψ(w-e_i)
  --     = exp(I·(realPhase P w - realPhase P (w-e_i))) · ψ(w-e_i).
  congr 2
  push_cast
  ring

/-! ## Conjugating the diagonal gate by a single `pauliz`

`Z`-Paulis commute with diagonal gates: the operator `pauliOperator
(pauliz i)` is itself diagonal (multiplication by `(-1)^{v i}`), and
two diagonal operators commute. Hence `conjEquiv U (pauliEquiv
(pauliz i)) = pauliEquiv (pauliz i)` as a `LinearEquiv`.
-/

/-- Diagonal-Z commutation: the conjugate of `pauliEquiv (pauliz i)`
by any diagonal gate is `pauliEquiv (pauliz i)` itself. -/
theorem conjEquiv_diagonalGateEquiv_pauliz
    (f : (Fin n → ZMod 2) → ℝ) (i : Fin n) :
    conjEquiv (diagonalGateEquiv f) (pauliEquiv (pauliz i)) =
      pauliEquiv (pauliz i) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [conjEquiv_apply, LinearEquiv.coe_coe,
    diagonalGateEquiv_symm_apply, pauliEquiv_apply,
    diagonalGateEquiv_apply]
  -- LHS at w:
  --   diagonalGate f (pauliOperator (pauliz i) (diagonalGate (-f) ψ)) w
  --     = exp(I·f(w)) · pauliOperator (pauliz i) (diagonalGate (-f) ψ) w
  --     = exp(I·f(w)) · (-1)^{(w i).val} · (diagonalGate (-f) ψ) w
  --     = exp(I·f(w)) · (-1)^{(w i).val} · exp(I·(-f(w))) · ψ w
  --     = exp(I·f(w)) · exp(I·(-f(w))) · (-1)^{(w i).val} · ψ w
  --     = 1 · (-1)^{(w i).val} · ψ w.
  -- RHS at w:
  --   pauliOperator (pauliz i) ψ w = (-1)^{(w i).val} · ψ w.
  unfold diagonalGate pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- (pauliz i).X = 0 so the bit shift is identity.
  have hX : (pauliz i).X = 0 := rfl
  rw [hX]
  simp only [sub_zero]
  -- The exp(I·f) · exp(-I·f) factor cancels to 1.
  rw [show (Complex.exp (Complex.I * (f w : ℂ)) *
            ((-1 : ℂ)^(zDotVal (pauliz i) w) *
              (Complex.exp (Complex.I * ((- f w : ℝ) : ℂ)) * ψ w)))
        = (Complex.exp (Complex.I * (f w : ℂ)) *
            Complex.exp (Complex.I * ((- f w : ℝ) : ℂ))) *
            ((-1 : ℂ)^(zDotVal (pauliz i) w) * ψ w) from by ring]
  rw [← Complex.exp_add]
  rw [show (Complex.I * (f w : ℂ) + Complex.I * ((- f w : ℝ) : ℂ)) = 0 from by
    push_cast; ring]
  rw [Complex.exp_zero, one_mul]

/-! ## Z-Pauli conjugate is in `C^(k)`

Combining `conjEquiv_diagonalGateEquiv_pauliz` with the level-1
membership of `pauliEquiv (pauliz i)` and monotonicity. -/

/-- For any phase pattern `f` and any qubit `i`, the conjugate of
`pauliEquiv (pauliz i)` by `diagonalGateEquiv f` sits at every
hierarchy level `k ≥ 1`. -/
theorem isCliffordHierarchy_conjEquiv_diagonalGateEquiv_pauliz
    (f : (Fin n → ZMod 2) → ℝ) (i : Fin n) {k : ℕ} (hk : 1 ≤ k) :
    IsCliffordHierarchy k
      (conjEquiv (diagonalGateEquiv f) (pauliEquiv (pauliz i))) := by
  rw [conjEquiv_diagonalGateEquiv_pauliz]
  exact (IsCliffordHierarchy.pauli (pauliz i)).mono hk

/-! ## Forward direction via `boolReduce` + `effectiveLevel`

The remaining body of this file proves the forward direction. The
strategy uses the multilinear `boolReduce` of `P` (which agrees with
`P` pointwise on binary inputs and is hence operator-equivalent) and
the strict effective-level drop of `shiftDeriv` on multilinear inputs
(`shiftDeriv_effectiveLevel_lt` from `EffectiveLevel.lean`).
-/

/-! ## Auxiliary identities between `P` and `boolReduce P`

The Boolean reduction `boolReduce P` agrees with `P` pointwise on
binary inputs (`boolReduce_eval_eq`), so the real-valued phase function
`realPhase` is the same for both. This lets us replace `P` by
`boolReduce P` throughout the operator-side argument.
-/

/-- `realPhase P` and `realPhase (boolReduce P)` are equal as functions
on `Fin n → ZMod 2`. They agree pointwise because `boolReduce_eval_eq`
shows the underlying `.eval` agrees, and `realPhase` factors through
`.eval`. -/
theorem realPhase_boolReduce_eq (P : DiagPhase n m) :
    DiagPhase.realPhase (DiagPhase.boolReduce P) = DiagPhase.realPhase P := by
  funext v
  unfold DiagPhase.realPhase
  rw [DiagPhase.boolReduce_eval_eq P v]

/-- The diagonal-gate equiv built from `realPhase P` equals the one
built from `realPhase (boolReduce P)`. -/
theorem diagonalGateEquiv_realPhase_boolReduce (P : DiagPhase n m) :
    diagonalGateEquiv (DiagPhase.realPhase P)
      = diagonalGateEquiv (DiagPhase.realPhase (DiagPhase.boolReduce P)) := by
  rw [realPhase_boolReduce_eq]

/-! ## Conjugate of `pauliEquiv q` by a diagonal gate, for arbitrary `q`

We generalise `conjEquiv_diagonalGateEquiv_paulix` and
`conjEquiv_diagonalGateEquiv_pauliz` to any `q : Pauli n`. The shape
of the conjugate is identical: the diagonal gate is replaced by one
with the shifted phase `f(· + q.X) - f(·)`, and the Pauli factor
remains `pauliEquiv q` on the right.

The proof works just like the `paulix i` case, but with `q.X` in
place of `Pi.single i 1` and the `pauliz` sign carried through. -/

/-- **General descent identity.** For any phase pattern `f` and any
Pauli `q`,
`conjEquiv (diagonalGateEquiv f) (pauliEquiv q) =
 (diagonalGateEquiv (f(· + q.X) - f(·))).trans (pauliEquiv q)`.

Specialisations:
* `q = paulix i`: matches `conjEquiv_diagonalGateEquiv_paulix`.
* `q = pauliz i` (`q.X = 0`): the shift is identity, the inner
  diagonal becomes phase `0`, and the result is just `pauliEquiv q`. -/
theorem conjEquiv_diagonalGateEquiv_general
    (f : (Fin n → ZMod 2) → ℝ) (q : Pauli n) :
    conjEquiv (diagonalGateEquiv f) (pauliEquiv q) =
      (diagonalGateEquiv (fun v : Fin n → ZMod 2 =>
          f (v + q.X) - f v)).trans (pauliEquiv q) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [conjEquiv_apply, LinearEquiv.coe_coe,
    diagonalGateEquiv_symm_apply, pauliEquiv_apply,
    LinearEquiv.trans_apply, diagonalGateEquiv_apply]
  unfold diagonalGate pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS at w:
  --   exp(I·f(w)) · (-1)^{q.Z · (w - q.X)} · exp(I·(-f(w - q.X))) · ψ(w - q.X).
  -- RHS at w:
  --   (-1)^{q.Z · (w - q.X)} · exp(I·(f(w - q.X + q.X) - f(w - q.X))) · ψ(w - q.X).
  -- Use w - q.X + q.X = w to align the inner argument.
  have hw : w - q.X + q.X = w := by ring
  rw [hw]
  -- Combine the exponentials on the LHS and bring the (-1)^... to the front.
  rw [show (Complex.exp (Complex.I * ((f w) : ℂ)) *
            ((-1 : ℂ)^(zDotVal q (w - q.X)) *
              (Complex.exp (Complex.I * ((- f (w - q.X) : ℝ) : ℂ)) *
                ψ (w - q.X))))
        = ((-1 : ℂ)^(zDotVal q (w - q.X))) *
            ((Complex.exp (Complex.I * ((f w) : ℂ)) *
              Complex.exp (Complex.I * ((- f (w - q.X) : ℝ) : ℂ))) *
              ψ (w - q.X)) from by ring]
  rw [← Complex.exp_add]
  -- The RHS:
  rw [show ((-1 : ℂ)^(zDotVal q (w - q.X)) *
            (Complex.exp (Complex.I * ((f w - f (w - q.X) : ℝ) : ℂ)) *
              ψ (w - q.X)))
        = ((-1 : ℂ)^(zDotVal q (w - q.X))) *
            (Complex.exp (Complex.I * ((f w - f (w - q.X) : ℝ) : ℂ)) *
              ψ (w - q.X)) from by ring]
  -- The two exp arguments must match.
  congr 2
  push_cast
  ring

/-! ## Right-multiplication closure of the operational Clifford hierarchy

`IsCliffordHierarchy.pauliEquiv_trans` (already in this file) is the
**left**-multiplication form: if `V ∈ C^k`, then `(pauliEquiv p).trans V
= V ∘ pauliEquiv p ∈ C^k`. We need the **right**-multiplication
analogue for the inductive step of `cgk_forward`.

The strategy: first prove that `conjEquiv (pauliEquiv p)` preserves
the hierarchy (call this `conjEquiv_pauliEquiv` closure). Then observe
`conjEquiv (V.trans (pauliEquiv p)) (pauliEquiv q) =
 conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q))`, and use the
recursive structure of `IsCliffordHierarchy`. -/

/-- Composition-identity for `conjEquiv` of `V.trans A`: pushing the
`A` through the conjugation. -/
private lemma conjEquiv_trans_eq
    (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (A : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (q : Pauli n) :
    conjEquiv (V.trans A) (pauliEquiv q) =
      conjEquiv A (conjEquiv V (pauliEquiv q)) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  simp only [conjEquiv_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, pauliEquiv_apply]

/-- Helper: a phased Pauli conjugated by `pauliEquiv p` is again a
phased Pauli. -/
private lemma IsPhasedPauli.conjEquiv_pauliEquiv
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (p : Pauli n) (hV : IsPhasedPauli V) :
    IsPhasedPauli (conjEquiv (pauliEquiv p) V) := by
  obtain ⟨α, r, hα⟩ := hV
  -- conjEquiv (pauliEquiv p) (scaleEquiv α (pauliEquiv r))
  --   = scaleEquiv α (conjEquiv (pauliEquiv p) (pauliEquiv r)).
  -- And conjEquiv (pauliEquiv p) (pauliEquiv r) is a phased Pauli (level-2 base
  -- step `two_of_one`).
  have hConjPaulis : IsPhasedPauli (conjEquiv (pauliEquiv p) (pauliEquiv r)) := by
    have htwo := IsCliffordHierarchy.two_of_one (isPhasedPauli_pauliEquiv p)
    cases htwo with
    | @step _ _ hstep =>
        exact isPhasedPauli_of_isCliffordHierarchy_one (hstep r)
  -- Identify conjEquiv (pauliEquiv p) V with
  --   scaleEquiv α (conjEquiv (pauliEquiv p) (pauliEquiv r)).
  have h_eq : conjEquiv (pauliEquiv p) V =
      FTQCLib.Hilbert.scaleEquiv α (conjEquiv (pauliEquiv p) (pauliEquiv r)) := by
    refine LinearEquiv.toLinearMap_injective ?_
    apply LinearMap.ext
    intro ψ
    simp only [conjEquiv_apply, LinearEquiv.coe_coe, scaleEquiv_apply,
      pauliEquiv_apply]
    have hV_apply : ∀ φ : QubitSpace n, V φ = (α : ℂ) • pauliOperator r φ := by
      intro φ
      have hh := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
      simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at hh
      exact hh
    rw [hV_apply]
    rw [LinearMap.map_smul]
  rw [h_eq]
  exact hConjPaulis.scaleEquiv α

/-- **Conjugation by a Pauli equiv preserves the operational Clifford
hierarchy.** If `V ∈ C^k`, then `conjEquiv (pauliEquiv p) V ∈ C^k`.

This is a key structural property: the C^k strata are closed under
conjugation by Paulis. Proof by induction on the level proof of V. -/
theorem IsCliffordHierarchy.conjEquiv_of_pauliEquiv {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (p : Pauli n) (hV : IsCliffordHierarchy k V) :
    IsCliffordHierarchy k (conjEquiv (pauliEquiv p) V) := by
  induction hV with
  | base h => exact .base (h.conjEquiv_pauliEquiv p)
  | @step k V hstep ih =>
      -- V is at level k+1: ∀ q, conjEquiv V (pauliEquiv q) ∈ C^k.
      -- IH `ih q : IsCliffordHierarchy k (conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q)))`.
      -- Want: conjEquiv (pauliEquiv p) V ∈ C^(k+1), i.e., for all q,
      --   conjEquiv (conjEquiv (pauliEquiv p) V) (pauliEquiv q) ∈ C^k.
      refine .step (fun q => ?_)
      -- Compute conjEquiv (conjEquiv (pauliEquiv p) V) (pauliEquiv q):
      -- = pauliEquiv p ∘ V ∘ (pauliEquiv p).symm ∘ pauliEquiv q ∘ pauliEquiv p ∘ V.symm
      --   ∘ (pauliEquiv p).symm
      -- The inner sandwich `(pauliEquiv p).symm ∘ pauliEquiv q ∘ pauliEquiv p` =
      --   conjEquiv (pauliEquiv p).symm (pauliEquiv q) — equal to
      --   conjEquiv (pauliEquiv p) (pauliEquiv q) up to a sign factor
      --   (by `conjEquiv_scaleEquiv` since (pauliEquiv p).symm = scaleEquiv c (pauliEquiv p)).
      -- That conjugate is a phased Pauli scaleEquiv α' (pauliEquiv q') (from two_of_one).
      -- So conjEquiv (conjEquiv (pauliEquiv p) V) (pauliEquiv q) =
      --   scaleEquiv α' (pauliEquiv p) ∘ V ∘ pauliOp q' ∘ V.symm ∘ (pauliEquiv p).symm
      --   which is handled via the following general identity.
      --
      -- We use the identity:
      -- conjEquiv (conjEquiv A V) Y = conjEquiv A (conjEquiv V (conjEquiv A.symm Y)).
      -- This follows from the algebraic identity (ABA⁻¹)Y(ABA⁻¹)⁻¹ = A(B(A⁻¹YA)B⁻¹)A⁻¹.
      have h_cong : conjEquiv (conjEquiv (pauliEquiv p) V) (pauliEquiv q) =
          conjEquiv (pauliEquiv p)
            (conjEquiv V (conjEquiv (pauliEquiv p).symm (pauliEquiv q))) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, conjEquiv_symm_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_symm]
      rw [h_cong]
      -- Now (pauliEquiv p).symm = scaleEquiv ((-1)^k) (pauliEquiv p) (by the symm_apply formula),
      -- and conjEquiv (scaleEquiv c U) Y = conjEquiv U Y by `conjEquiv_scaleEquiv`.
      have h_symm_conj : conjEquiv (pauliEquiv p).symm (pauliEquiv q) =
          conjEquiv (pauliEquiv p) (pauliEquiv q) := by
        -- (pauliEquiv p).symm and pauliEquiv p differ by a scalar; conjugation is invariant.
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, LinearEquiv.coe_coe, pauliEquiv_symm_apply,
          pauliEquiv_apply, LinearEquiv.symm_symm]
        -- Goal: c • pauliOp p (pauliOp q (pauliOp p ψ))
        --     = pauliOp p (pauliOp q (c • pauliOp p ψ))
        -- where c = (-1)^{p.Z·p.X}. Push c through both pauliOps via linearity.
        rw [LinearMap.map_smul (pauliOperator q), LinearMap.map_smul (pauliOperator p)]
      rw [h_symm_conj]
      -- Now: conjEquiv (pauliEquiv p) (pauliEquiv q) is a phased Pauli by two_of_one.
      have hConjPaulis : IsPhasedPauli (conjEquiv (pauliEquiv p) (pauliEquiv q)) := by
        have htwo := IsCliffordHierarchy.two_of_one (isPhasedPauli_pauliEquiv p)
        cases htwo with
        | @step _ _ hstep' =>
            exact isPhasedPauli_of_isCliffordHierarchy_one (hstep' q)
      obtain ⟨α', q', hα'⟩ := hConjPaulis
      -- Identify conjEquiv (pauliEquiv p) (pauliEquiv q) = scaleEquiv α' (pauliEquiv q').
      have h_pauli_form : conjEquiv (pauliEquiv p) (pauliEquiv q) =
          FTQCLib.Hilbert.scaleEquiv α' (pauliEquiv q') := by
        refine LinearEquiv.toLinearMap_injective ?_
        rw [hα']
        apply LinearMap.ext
        intro ψ
        simp [scaleEquiv_toLinearMap]
      rw [h_pauli_form]
      -- conjEquiv V (scaleEquiv α' (pauliEquiv q')) = scaleEquiv α' (conjEquiv V (pauliEquiv q')).
      have h_pull_scale : conjEquiv V (FTQCLib.Hilbert.scaleEquiv α' (pauliEquiv q')) =
          FTQCLib.Hilbert.scaleEquiv α' (conjEquiv V (pauliEquiv q')) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, LinearEquiv.coe_coe, scaleEquiv_apply]
        rw [LinearEquiv.map_smul]
      rw [h_pull_scale]
      -- Now: conjEquiv (pauliEquiv p) (scaleEquiv α' (conjEquiv V (pauliEquiv q'))).
      -- Pull the scale outside: conjEquiv (pauliEquiv p) (scaleEquiv β X)
      --   = scaleEquiv β (conjEquiv (pauliEquiv p) X).
      have h_pull_scale2 : conjEquiv (pauliEquiv p)
            (FTQCLib.Hilbert.scaleEquiv α' (conjEquiv V (pauliEquiv q')))
          = FTQCLib.Hilbert.scaleEquiv α' (conjEquiv (pauliEquiv p)
              (conjEquiv V (pauliEquiv q'))) := by
        refine LinearEquiv.toLinearMap_injective ?_
        apply LinearMap.ext
        intro ψ
        simp only [conjEquiv_apply, LinearEquiv.coe_coe, scaleEquiv_apply]
        -- Goal: pauliEquiv p (α' • (conjEquiv V (pauliEquiv q') ((pauliEquiv p).symm ψ)))
        --     = α' • pauliEquiv p (conjEquiv V (pauliEquiv q') ((pauliEquiv p).symm ψ)).
        -- Pull α' through pauliEquiv p (linearity).
        rw [LinearEquiv.map_smul]
      rw [h_pull_scale2]
      -- By IH on q': conjEquiv (pauliEquiv p) (conjEquiv V (pauliEquiv q')) ∈ C^k.
      -- Then scaleEquiv α' (...) ∈ C^k by scaleEquiv closure.
      exact (ih q').scaleEquiv α'

/-- Helper: a phased Pauli composed with `pauliEquiv p` on the right is
again a phased Pauli. -/
private lemma IsPhasedPauli.trans_pauliEquiv {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hV : IsPhasedPauli V) (p : Pauli n) :
    IsPhasedPauli (V.trans (pauliEquiv p)) := by
  obtain ⟨α, r, hα⟩ := hV
  set β : ℂ := (α : ℂ) * (-1 : ℂ) ^ (zDotVal p r.X)
  have hβ_ne : β ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero α) ?_
    exact pow_ne_zero _ (by norm_num)
  refine ⟨Units.mk0 β hβ_ne, r + p, ?_⟩
  apply LinearMap.ext
  intro ψ
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, pauliEquiv_apply,
    LinearMap.smul_apply, Units.val_mk0]
  -- LHS: pauliOp p (V ψ) where V φ = α • pauliOp r φ (via hα).
  have hV_apply : ∀ φ : QubitSpace n, V φ = (α : ℂ) • pauliOperator r φ := by
    intro φ
    have hh := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at hh
    exact hh
  rw [hV_apply, LinearMap.map_smul]
  rw [show pauliOperator p (pauliOperator r ψ)
        = ((-1 : ℂ)^(zDotVal p r.X)) • pauliOperator (r + p) ψ from by
      have hh := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
        (pauliOperator_mul r p)
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply] at hh
      exact hh]
  rw [smul_smul]

/-- **Right-multiplication closure**: if `V ∈ C^k`, then
`V.trans (pauliEquiv p) ∈ C^k`. Combines `conjEquiv_trans_eq` with
`conjEquiv_of_pauliEquiv` closure and the existing left-multiplication
closure. -/
theorem IsCliffordHierarchy.trans_pauliEquiv {k : ℕ}
    {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (p : Pauli n) (hV : IsCliffordHierarchy k V) :
    IsCliffordHierarchy k (V.trans (pauliEquiv p)) := by
  induction hV with
  | base h => exact .base (h.trans_pauliEquiv p)
  | @step k V hstep ih =>
      refine .step (fun q => ?_)
      rw [conjEquiv_trans_eq]
      exact (hstep q).conjEquiv_of_pauliEquiv p

/-! ## Polynomial-side shift along a binary vector

For `s : Fin n → ZMod 2`, the substitution `X_k ↦ if s k = 1 then 1 - X_k else X_k`
realises the bit-flip pattern of `s` on binary inputs: at `x ∈ {0, 1}`, the value
becomes `1 - x` if `s k = 1` (flip) or `x` otherwise (fix). We define `shiftBy s P`
as this substitution minus `P`, mirroring `shiftDeriv` but for the general
multi-bit shift. -/

namespace DiagPhase

open FTQCLib.Hierarchy

/-- The polynomial substitution that realises the boolean shift `v ↦ v + s`
on `(F₂)ⁿ` (lifted to `ZMod (2^m)`): sends `X_k` to `1 − X_k` if `s k = 1`
(bit-flip on `k`) and to `X_k` otherwise. -/
noncomputable def vecShift (s : Fin n → ZMod 2) (k : Fin n) :
    MvPolynomial (Fin n) (ZMod (2 ^ m)) :=
  if s k = 1 then (1 - MvPolynomial.X k) else MvPolynomial.X k

/-- The polynomial-side shift by `s`: `bind₁ (vecShift s) P - P`. Its
evaluation at `liftBinary v` matches `P.eval (liftBinary (v + s)) -
P.eval (liftBinary v)` (analogue of `shiftDeriv_eval`). -/
noncomputable def shiftBy (s : Fin n → ZMod 2) (P : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hierarchy.DiagPhase n m :=
  MvPolynomial.bind₁ (vecShift (m := m) s) P - P

private lemma shiftBy_eq (s : Fin n → ZMod 2) (P : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hilbert.DiagPhase.shiftBy s P
      = MvPolynomial.bind₁ (vecShift (m := m) s) P - P :=
  rfl

/-- Bridge identity: evaluating `vecShift s k` at `liftBinary v` yields
the `k`-th coordinate of the lifted shifted vector `liftBinary (v + s)`. -/
private lemma eval_vecShift_apply (s : Fin n → ZMod 2) (k : Fin n)
    (v : Fin n → ZMod 2) :
    MvPolynomial.eval (FTQCLib.Hierarchy.DiagPhase.liftBinary (m := m) v)
        (vecShift (m := m) s k)
      = (FTQCLib.Hierarchy.DiagPhase.liftBinary (m := m) (v + s)) k := by
  classical
  unfold vecShift
  split_ifs with hsk
  · -- s k = 1: target `1 - (v k).val = ((v + s) k).val` in ZMod (2^m).
    rw [map_sub, map_one, MvPolynomial.eval_X]
    unfold FTQCLib.Hierarchy.DiagPhase.liftBinary
    have hvk_add : (v + s) k = v k + s k := by simp
    rw [hvk_add, hsk]
    -- Case on `v k ∈ {0, 1}`.
    have hlt : (v k).val < 2 := ZMod.val_lt _
    have hval : v k = ((v k).val : ZMod 2) := (ZMod.natCast_zmod_val _).symm
    haveI : Fact (1 < 2) := ⟨Nat.one_lt_two⟩
    interval_cases (v k).val
    · -- v k = 0: target `1 - ((v k).val : ZMod (2^m)) = ((v k + 1).val : ZMod (2^m))`.
      have hvk0 : v k = 0 := by rw [hval]; norm_cast
      rw [hvk0]
      -- After rewrite: 1 - ↑((0 : ZMod 2).val) = ↑((0 + 1 : ZMod 2).val).
      simp only [zero_add, ZMod.val_one 2]
      push_cast; ring
    · -- v k = 1: target `1 - ((v k).val : ZMod (2^m)) = ((v k + 1).val : ZMod (2^m))`.
      have hvk1 : v k = 1 := by rw [hval]; norm_cast
      rw [hvk1]
      have h1plus1 : (1 + 1 : ZMod 2) = 0 := by decide
      rw [h1plus1]
      simp only [ZMod.val_zero]
      push_cast; ring
  · -- s k ≠ 1, so s k = 0: target `(v k).val = ((v + s) k).val`.
    rw [MvPolynomial.eval_X]
    unfold FTQCLib.Hierarchy.DiagPhase.liftBinary
    have hsk_zero : s k = 0 := by
      have hlt : (s k).val < 2 := ZMod.val_lt _
      have hval_eq : s k = ((s k).val : ZMod 2) := (ZMod.natCast_zmod_val _).symm
      interval_cases (s k).val
      · rw [hval_eq]; norm_cast
      · exfalso
        apply hsk
        rw [hval_eq]; norm_cast
    have hvk_add : (v + s) k = v k := by simp [hsk_zero]
    rw [hvk_add]

/-- **Eval bridge for `shiftBy`**: evaluating `shiftBy s P` at
`liftBinary v` gives `P.eval (liftBinary (v + s)) - P.eval (liftBinary v)`. -/
theorem shiftBy_eval (s : Fin n → ZMod 2) (P : FTQCLib.Hierarchy.DiagPhase n m)
    (v : Fin n → ZMod 2) :
    MvPolynomial.eval (FTQCLib.Hierarchy.DiagPhase.liftBinary v)
        (FTQCLib.Hilbert.DiagPhase.shiftBy s P)
      = MvPolynomial.eval (FTQCLib.Hierarchy.DiagPhase.liftBinary (v + s)) P
        - MvPolynomial.eval (FTQCLib.Hierarchy.DiagPhase.liftBinary v) P := by
  rw [shiftBy_eq, map_sub]
  congr 1
  -- Use aeval_bind₁ to reduce.
  have h := MvPolynomial.aeval_bind₁
      (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
      (FTQCLib.Hierarchy.DiagPhase.liftBinary (m := m) v)
      (vecShift (m := m) s) P
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  -- Show the function arguments to eval agree pointwise.
  have hfun : (fun k : Fin n =>
      MvPolynomial.eval (FTQCLib.Hierarchy.DiagPhase.liftBinary (m := m) v)
        (vecShift (m := m) s k))
      = FTQCLib.Hierarchy.DiagPhase.liftBinary (m := m) (v + s) := by
    funext k
    exact eval_vecShift_apply s k v
  rw [hfun]

/-- `shiftBy s P` evaluated via `DiagPhase.eval` realises the binary
shift difference of `P.eval`. -/
theorem shiftBy_eval_eq (s : Fin n → ZMod 2) (P : FTQCLib.Hierarchy.DiagPhase n m)
    (v : Fin n → ZMod 2) :
    (FTQCLib.Hilbert.DiagPhase.shiftBy s P).eval v = P.eval (v + s) - P.eval v := by
  unfold FTQCLib.Hierarchy.DiagPhase.eval
  exact shiftBy_eval s P v

/-- `shiftBy 0 P = 0` because `vecShift 0` is the identity substitution. -/
@[simp] lemma shiftBy_zero (P : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hilbert.DiagPhase.shiftBy (0 : Fin n → ZMod 2) P = 0 := by
  -- vecShift 0 k = X k for all k (since 0 k = 0 ≠ 1).
  rw [shiftBy_eq]
  have h_id : ∀ k : Fin n,
      vecShift (m := m) (0 : Fin n → ZMod 2) k
        = (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))) := by
    intro k
    unfold vecShift
    have h : (0 : Fin n → ZMod 2) k = 0 := rfl
    rw [h]
    split_ifs with h2
    · exact absurd h2 (by decide)
    · rfl
  have h_funext : (vecShift (m := m) (0 : Fin n → ZMod 2))
                = (MvPolynomial.X : Fin n → MvPolynomial (Fin n) (ZMod (2 ^ m))) := by
    funext k; exact h_id k
  rw [h_funext]
  have hbind :
      MvPolynomial.bind₁ (MvPolynomial.X : Fin n → MvPolynomial (Fin n) (ZMod (2 ^ m))) P = P := by
    rw [MvPolynomial.bind₁_X_left]
    rfl
  rw [hbind]
  simp

/-! ## `shiftBy` reduces to `shiftDeriv` for single-bit shifts

When `s = Pi.single i 1` (a single bit), `vecShift s = flipShift i` and
hence `shiftBy s = shiftDeriv i`. -/

private lemma vecShift_single (i : Fin n) (k : Fin n) :
    vecShift (m := m) (Pi.single i 1) k
      = FTQCLib.Hierarchy.DiagPhase.flipShift (m := m) i k := by
  unfold vecShift FTQCLib.Hierarchy.DiagPhase.flipShift
  by_cases hki : k = i
  · subst hki
    have hs : (Pi.single k (1 : ZMod 2) : Fin n → ZMod 2) k = 1 := by simp
    rw [hs, if_pos rfl, if_pos rfl]
  · have hs : (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = 0 :=
      Pi.single_eq_of_ne hki 1
    rw [hs, if_neg (by decide : (0 : ZMod 2) ≠ 1), if_neg hki]

theorem shiftBy_single_eq_shiftDeriv (i : Fin n)
    (P : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hilbert.DiagPhase.shiftBy (Pi.single i 1) P
      = FTQCLib.Hierarchy.DiagPhase.shiftDeriv i P := by
  rw [shiftBy_eq]
  change MvPolynomial.bind₁ (vecShift (m := m) (Pi.single i 1)) P - P
       = MvPolynomial.bind₁ (FTQCLib.Hierarchy.DiagPhase.flipShift (m := m) i) P - P
  congr 1
  have h_eq : vecShift (m := m) (Pi.single i 1)
              = FTQCLib.Hierarchy.DiagPhase.flipShift (m := m) i := by
    funext k
    exact vecShift_single i k
  rw [h_eq]

/-! ### `shiftBy` is additive

We use this when bounding the effective level of `shiftBy s P` via the
monomial decomposition of `P`. -/

theorem shiftBy_add (s : Fin n → ZMod 2) (P Q : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hilbert.DiagPhase.shiftBy s (P + Q)
      = FTQCLib.Hilbert.DiagPhase.shiftBy s P + FTQCLib.Hilbert.DiagPhase.shiftBy s Q := by
  rw [shiftBy_eq, shiftBy_eq, shiftBy_eq, map_add]
  abel

theorem shiftBy_finsetSum {α : Type*} (s : Fin n → ZMod 2)
    (t : Finset α) (f : α → FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hilbert.DiagPhase.shiftBy s (∑ i ∈ t, f i)
      = ∑ i ∈ t, FTQCLib.Hilbert.DiagPhase.shiftBy s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rw [shiftBy_eq]; simp
  | insert a s_set has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has, shiftBy_add, ih]

/-! ### Polynomial identity for decomposing `shiftBy` into single-bit shifts

For `s : Fin n → ZMod 2` with `s i = 1` and `s' = s - Pi.single i 1`
(so `s' i = 0` and `s = s' + Pi.single i 1`), we have

  `shiftBy s P = shiftBy (Pi.single i 1) (shiftBy s' P)
                 + shiftBy (Pi.single i 1) P
                 + shiftBy s' P`.

This identity allows recursive analysis of `shiftBy s P` on `|supp s|`.
-/

/-- Bridge: substituting `vecShift (Pi.single i 1)` into `vecShift s' k`
gives `vecShift (Pi.single i 1 + s') k`, provided `s' i = 0`. -/
private lemma bind₁_vecShift_single_vecShift (i : Fin n) (s' : Fin n → ZMod 2)
    (hs' : s' i = 0) (k : Fin n) :
    (MvPolynomial.bind₁ (vecShift (m := m) (Pi.single i 1))
        (vecShift (m := m) s' k) : MvPolynomial (Fin n) (ZMod (2 ^ m)))
      = vecShift (m := m)
          ((Pi.single i 1 : Fin n → ZMod 2) + s') k := by
  -- Unfold the outer vecShift at k.
  change MvPolynomial.bind₁ (vecShift (m := m) (Pi.single i 1))
        (if s' k = 1 then 1 - MvPolynomial.X k else MvPolynomial.X k)
      = if ((Pi.single i 1 : Fin n → ZMod 2) + s') k = 1
          then 1 - MvPolynomial.X k else MvPolynomial.X k
  by_cases hki : k = i
  · -- k = i: s' k = 0 (hypothesis).
    subst hki
    have hsk' : s' k = 0 := hs'
    have h_sum : ((Pi.single k (1 : ZMod 2) : Fin n → ZMod 2) + s') k = 1 := by
      change (Pi.single k (1 : ZMod 2) : Fin n → ZMod 2) k + s' k = 1
      rw [Pi.single_eq_same, hsk', add_zero]
    rw [h_sum, hsk', if_neg (by decide : (0 : ZMod 2) ≠ 1), if_pos rfl]
    -- LHS: bind₁ (vecShift (Pi.single k 1)) (X k) = vecShift (Pi.single k 1) k = 1 - X k.
    rw [MvPolynomial.bind₁_X_right]
    -- vecShift (Pi.single k 1) k: Pi.single k 1 k = 1, so result = 1 - X k.
    change (if (Pi.single k (1 : ZMod 2) : Fin n → ZMod 2) k = 1 then
            (1 - MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m)))
          else MvPolynomial.X k) = 1 - MvPolynomial.X k
    rw [Pi.single_eq_same, if_pos rfl]
  · -- k ≠ i.
    have hek : (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = 0 :=
      Pi.single_eq_of_ne hki 1
    have h_sum : ((Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) + s') k = s' k := by
      change (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k + s' k = s' k
      rw [hek, zero_add]
    rw [h_sum]
    by_cases hsk' : s' k = 1
    · rw [if_pos hsk']
      rw [map_sub, map_one, MvPolynomial.bind₁_X_right]
      -- vecShift (Pi.single i 1) k: (Pi.single i 1) k = 0 ≠ 1, so result = X k.
      change 1 - (if (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = 1 then
                  (1 - MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m)))
                else MvPolynomial.X k) = 1 - MvPolynomial.X k
      rw [hek, if_neg (by decide : (0 : ZMod 2) ≠ 1)]
    · rw [if_neg hsk']
      rw [MvPolynomial.bind₁_X_right]
      change (if (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = 1 then
              (1 - MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m)))
            else MvPolynomial.X k) = MvPolynomial.X k
      rw [hek, if_neg (by decide : (0 : ZMod 2) ≠ 1)]

/-- Composition identity: `bind₁ (vecShift (Pi.single i 1)) ∘ bind₁ (vecShift s')
= bind₁ (vecShift (Pi.single i 1 + s'))`. -/
private lemma bind₁_vecShift_compose (i : Fin n) (s' : Fin n → ZMod 2)
    (hs' : s' i = 0) (P : FTQCLib.Hierarchy.DiagPhase n m) :
    MvPolynomial.bind₁ (vecShift (m := m) (Pi.single i 1))
        (MvPolynomial.bind₁ (vecShift (m := m) s') P)
      = MvPolynomial.bind₁
          (vecShift (m := m) ((Pi.single i 1 : Fin n → ZMod 2) + s')) P := by
  rw [MvPolynomial.bind₁_bind₁]
  -- Goal: bind₁ (fun k => bind₁ ... (vecShift s' k)) P = bind₁ (vecShift (Pi.single i 1 + s')) P.
  -- Show the bind₁ functions are equal pointwise.
  have h_fun_eq : (fun k : Fin n =>
        (MvPolynomial.bind₁ (vecShift (m := m) (Pi.single i 1))
          (vecShift (m := m) s' k) : MvPolynomial (Fin n) (ZMod (2 ^ m))))
      = vecShift (m := m) ((Pi.single i 1 : Fin n → ZMod 2) + s') := by
    funext k
    exact bind₁_vecShift_single_vecShift i s' hs' k
  rw [h_fun_eq]

/-- **Polynomial identity for decomposing `shiftBy`**: for `s = Pi.single i 1 + s'`
with `s' i = 0`,
`shiftBy s P = shiftBy (Pi.single i 1) (shiftBy s' P) + shiftBy (Pi.single i 1) P
+ shiftBy s' P`. -/
theorem shiftBy_decompose (i : Fin n) (s' : Fin n → ZMod 2) (hs' : s' i = 0)
    (P : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hilbert.DiagPhase.shiftBy ((Pi.single i 1 : Fin n → ZMod 2) + s') P
      = FTQCLib.Hilbert.DiagPhase.shiftBy (Pi.single i 1)
          (FTQCLib.Hilbert.DiagPhase.shiftBy s' P)
        + FTQCLib.Hilbert.DiagPhase.shiftBy (Pi.single i 1) P
        + FTQCLib.Hilbert.DiagPhase.shiftBy s' P := by
  simp only [shiftBy_eq]
  -- After simp: LHS = bind₁ (vecShift (Pi.single i 1 + s')) P - P
  -- RHS = bind₁ (vecShift (Pi.single i 1)) (bind₁ (vecShift s') P - P)
  --       - (bind₁ (vecShift s') P - P)
  --       + (bind₁ (vecShift (Pi.single i 1)) P - P) + (bind₁ (vecShift s') P - P)
  -- Expand the first term via map_sub.
  rw [map_sub]
  -- Now LHS has bind₁ (vecShift (Pi.single i 1)) (bind₁ (vecShift s') P) which
  -- equals bind₁ (vecShift (Pi.single i 1 + s')) P by composition.
  have h_comp := bind₁_vecShift_compose i s' hs' P
  rw [h_comp]
  ring

/-! ### Total-degree bound for `shiftBy`

`shiftBy s P` does not raise total degree. Used as a non-strict bound
in combination with the strict effective-level drop below. -/

/-- Each `vecShift s k` has total degree at most 1. -/
private lemma vecShift_totalDegree_le (s : Fin n → ZMod 2) (k : Fin n) :
    (vecShift (m := m) s k).totalDegree ≤ 1 := by
  unfold vecShift
  split_ifs with hsk
  · -- 1 - X k: total degree at most 1.
    calc (1 - MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
        ≤ max (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
            (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ max 0 1 := by
          gcongr
          · rw [MvPolynomial.totalDegree_one]
          · -- X k has total degree at most 1.
            have h : (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))) =
                MvPolynomial.monomial (Finsupp.single k 1) (1 : ZMod (2 ^ m)) := by
              rw [MvPolynomial.X, MvPolynomial.monomial]
            rw [h]
            refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
            simp [Finsupp.sum_single_index]
      _ = 1 := by simp
  · -- X k has total degree at most 1.
    have h : (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))) =
        MvPolynomial.monomial (Finsupp.single k 1) (1 : ZMod (2 ^ m)) := by
      rw [MvPolynomial.X, MvPolynomial.monomial]
    rw [h]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    simp [Finsupp.sum_single_index]

/-- `shiftBy s P` does not raise the total degree. (Used in combination
with the per-monomial effective-level bound.) -/
theorem shiftBy_totalDegree_le (s : Fin n → ZMod 2)
    (P : FTQCLib.Hierarchy.DiagPhase n m) :
    (FTQCLib.Hilbert.DiagPhase.shiftBy s P).totalDegree ≤ P.totalDegree := by
  rw [shiftBy_eq]
  calc (MvPolynomial.bind₁ (vecShift (m := m) s) P - P).totalDegree
      ≤ max (MvPolynomial.bind₁ (vecShift (m := m) s) P).totalDegree
          P.totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max P.totalDegree P.totalDegree := by
        gcongr
        -- bind₁ of substitution of total-degree ≤ 1 polys doesn't raise total degree.
        -- This follows from the standard MvPolynomial.totalDegree_bind₁_le style argument.
        classical
        conv_lhs => rw [P.as_sum, map_sum]
        refine MvPolynomial.totalDegree_finsetSum_le ?_
        intro d hd
        rw [MvPolynomial.bind₁_monomial]
        calc (MvPolynomial.C (P.coeff d) *
              ∏ k ∈ d.support, vecShift (m := m) s k ^ d k).totalDegree
            ≤ (MvPolynomial.C (P.coeff d)).totalDegree
              + (∏ k ∈ d.support, vecShift (m := m) s k ^ d k).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ = (∏ k ∈ d.support, vecShift (m := m) s k ^ d k).totalDegree := by
              rw [MvPolynomial.totalDegree_C, zero_add]
          _ ≤ ∑ k ∈ d.support, (vecShift (m := m) s k ^ d k).totalDegree :=
              MvPolynomial.totalDegree_finset_prod _ _
          _ ≤ ∑ k ∈ d.support, d k * (vecShift (m := m) s k).totalDegree := by
              gcongr with k _
              exact MvPolynomial.totalDegree_pow _ _
          _ ≤ ∑ k ∈ d.support, d k * 1 := by
              gcongr with k _
              exact vecShift_totalDegree_le s k
          _ = ∑ k ∈ d.support, d k := by simp
          _ = d.sum (fun _ e => e) := rfl
          _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd
    _ = P.totalDegree := max_self _

end DiagPhase

/-! ## Forward direction of CGK (conditional formulation)

We state the forward direction conditionally on a single
polynomial-side ingredient: the strict effective-level drop of
`shiftBy s` on multilinear polynomials, for arbitrary nonzero
`s : Fin n → ZMod 2`. This is the **strict-drop predicate**
`ShiftByStrictDrop`. For single-bit `s`, the predicate is
provable from `shiftDeriv_effectiveLevel_lt` + `shiftBy_single_eq_shiftDeriv`
(see `shiftByStrictDrop_single` below). For multi-bit `s`, the
polynomial identity `shiftBy_decompose` reduces the problem
recursively, using multilinearity preservation
`IsMultilinear P → IsMultilinear (shiftBy s P)` (`shiftBy_isMultilinear`);
the general case is `shiftByStrictDrop_general`. -/

/-- The strict-drop predicate for `shiftBy` on multilinear inputs. -/
def ShiftByStrictDrop (n m : ℕ) : Prop :=
  ∀ (P : FTQCLib.Hierarchy.DiagPhase n m),
    FTQCLib.Hierarchy.DiagPhase.IsMultilinear P →
    0 < FTQCLib.Hierarchy.DiagPhase.effectiveLevel P →
    ∀ s : Fin n → ZMod 2, s ≠ 0 →
      FTQCLib.Hierarchy.DiagPhase.effectiveLevel
          (FTQCLib.Hilbert.DiagPhase.shiftBy s P)
        < FTQCLib.Hierarchy.DiagPhase.effectiveLevel P

/-- The strict-drop predicate at single-bit shifts holds: this is
`shiftDeriv_effectiveLevel_lt` combined with `shiftBy_single_eq_shiftDeriv`. -/
theorem shiftByStrictDrop_single (n m : ℕ) (i : Fin n)
    (P : FTQCLib.Hierarchy.DiagPhase n m)
    (h_mul : FTQCLib.Hierarchy.DiagPhase.IsMultilinear P)
    (h_eff : 0 < FTQCLib.Hierarchy.DiagPhase.effectiveLevel P) :
    FTQCLib.Hierarchy.DiagPhase.effectiveLevel
        (FTQCLib.Hilbert.DiagPhase.shiftBy (Pi.single i 1) P)
      < FTQCLib.Hierarchy.DiagPhase.effectiveLevel P := by
  rw [FTQCLib.Hilbert.DiagPhase.shiftBy_single_eq_shiftDeriv]
  by_cases h_deg : 0 < P.totalDegree
  · exact FTQCLib.Hierarchy.DiagPhase.shiftDeriv_effectiveLevel_lt i h_mul h_deg
  · push_neg at h_deg
    rw [Nat.le_zero] at h_deg
    rw [FTQCLib.Hierarchy.DiagPhase.shiftDeriv_totalDegree_zero i h_deg]
    rw [FTQCLib.Hierarchy.DiagPhase.effectiveLevel_zero]
    exact h_eff

/-! ### Hamming weight of a binary vector

For `s : Fin n → ZMod 2`, the `hammingWeight s` is the number of
coordinates where `s` is nonzero, i.e. where `s k = 1`. Used as the
induction parameter for the multi-bit `shiftBy` strict-drop lemma. -/

/-- The Hamming weight of `s : Fin n → ZMod 2`: the cardinality of the
set of indices where `s` is nonzero. -/
noncomputable def hammingWeight (s : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => s i ≠ 0)).card

lemma hammingWeight_eq_zero_iff (s : Fin n → ZMod 2) :
    hammingWeight s = 0 ↔ s = 0 := by
  classical
  unfold hammingWeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    have hi : ¬ (s i ≠ 0) := h (Finset.mem_univ i)
    push_neg at hi
    rw [hi]; rfl
  · intro h i _
    push_neg
    rw [h]; rfl

/-- If `s ≠ 0`, there exists an index `i` with `s i = 1`. -/
lemma exists_one_of_ne_zero {s : Fin n → ZMod 2} (hs : s ≠ 0) :
    ∃ i : Fin n, s i = 1 := by
  by_contra h
  push_neg at h
  apply hs
  funext i
  have hi : s i ≠ 1 := h i
  -- s i ∈ {0, 1}, so s i ≠ 1 ↔ s i = 0.
  have hlt : (s i).val < 2 := ZMod.val_lt _
  have hval : s i = ((s i).val : ZMod 2) := (ZMod.natCast_zmod_val _).symm
  interval_cases (s i).val
  · rw [hval]; norm_cast
  · exfalso
    apply hi
    rw [hval]; norm_cast

/-- For `s i = 1`, removing the `i`-th bit drops the Hamming weight by 1. -/
lemma hammingWeight_sub_single (s : Fin n → ZMod 2) (i : Fin n) (hsi : s i = 1) :
    hammingWeight (s - Pi.single i 1) + 1 = hammingWeight s := by
  classical
  unfold hammingWeight
  -- Both filters are equal except at i: at i, s i = 1 ≠ 0, while
  -- (s - Pi.single i 1) i = s i - 1 = 0.
  have hsi' : (s - Pi.single i 1 : Fin n → ZMod 2) i = 0 := by
    change s i - (Pi.single i 1 : Fin n → ZMod 2) i = 0
    rw [Pi.single_eq_same, hsi, sub_self]
  have h_off : ∀ k : Fin n, k ≠ i →
      (s - Pi.single i 1 : Fin n → ZMod 2) k = s k := by
    intro k hki
    change s k - (Pi.single i 1 : Fin n → ZMod 2) k = s k
    rw [Pi.single_eq_of_ne hki, sub_zero]
  -- The filter at s is the filter at (s - e_i) ∪ {i}.
  have h_eq : Finset.univ.filter (fun k : Fin n => s k ≠ 0)
      = insert i (Finset.univ.filter (fun k : Fin n =>
            (s - Pi.single i 1 : Fin n → ZMod 2) k ≠ 0)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hk
      by_cases hki : k = i
      · left; exact hki
      · right
        rw [h_off k hki]
        exact hk
    · intro hk
      rcases hk with hk | hk
      · subst hk
        rw [hsi]
        exact one_ne_zero
      · by_cases hki : k = i
        · subst hki
          rw [hsi]
          exact one_ne_zero
        · rwa [h_off k hki] at hk
  rw [h_eq]
  have h_not_mem : i ∉ Finset.univ.filter (fun k : Fin n =>
      (s - Pi.single i 1 : Fin n → ZMod 2) k ≠ 0) := by
    rw [Finset.mem_filter]
    push_neg
    intro _
    exact hsi'
  rw [Finset.card_insert_of_notMem h_not_mem]

/-- Decomposing `s` as `Pi.single i 1 + (s - Pi.single i 1)` when `s i = 1`. -/
lemma sub_single_decompose (s : Fin n → ZMod 2) (i : Fin n) (hsi : s i = 1) :
    s = (Pi.single i 1 : Fin n → ZMod 2) + (s - Pi.single i 1) := by
  ring

/-- The "remainder" `s - Pi.single i 1` has zero at `i` when `s i = 1`. -/
lemma sub_single_at_i_eq_zero (s : Fin n → ZMod 2) (i : Fin n) (hsi : s i = 1) :
    (s - Pi.single i 1 : Fin n → ZMod 2) i = 0 := by
  change s i - (Pi.single i 1 : Fin n → ZMod 2) i = 0
  rw [Pi.single_eq_same, hsi, sub_self]

/-! ### Multilinearity preservation under `shiftBy`

For multilinear `P`, `shiftBy s P` is multilinear. The proof:
1. `bind₁ (vecShift s) (monomial d c)` is multilinear when `d` itself is
   multilinear (each `d k ≤ 1`): the product
   `∏_{k ∈ d.support} (vecShift s k)^(d k)` is a product over distinct
   variables of polynomials each of degree ≤ 1 in their own variable, so
   the result is multilinear.
2. Multilinearity is preserved under `MvPolynomial` addition and
   negation (support inclusion).
3. `shiftBy s P = bind₁ (vecShift s) P - P` is multilinear when `P` is.
-/

namespace DiagPhase

open FTQCLib.Hierarchy

/-- Support of `X k` (without `Nontrivial` assumption): support is
contained in `{Finsupp.single k 1}`. Avoids the `Nontrivial`-requiring
`MvPolynomial.support_X`. -/
private lemma X_support_subset (k : Fin n) :
    (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).support ⊆
      {Finsupp.single k 1} := by
  intro e he
  rw [MvPolynomial.X, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at he
  by_cases h_eq : Finsupp.single k 1 = e
  · rw [Finset.mem_singleton, ← h_eq]
  · rw [if_neg h_eq] at he
    exact absurd rfl he

/-- Support of `1` is contained in `{0}` (without `Nontrivial`). -/
private lemma one_support_subset :
    (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))).support ⊆ {0} := by
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at he
  by_cases he0 : e = 0
  · rw [he0]; exact Finset.mem_singleton_self _
  · rw [if_neg (fun heq => he0 heq.symm)] at he
    exact absurd rfl he

/-- `vecShift s k` is a polynomial whose support lies in
`{0, Finsupp.single k 1}` — every monomial has exponent vector with
entries `≤ 1`, all concentrated at index `k`. -/
private lemma vecShift_support_subset (s : Fin n → ZMod 2) (k : Fin n) :
    (vecShift (m := m) s k).support ⊆
      {(0 : Fin n →₀ ℕ), Finsupp.single k 1} := by
  classical
  unfold vecShift
  split_ifs with hsk
  · -- `1 - X k`. Support ⊆ support(1) ∪ support(X k) ⊆ {0} ∪ {single k 1}.
    intro d hd
    have h_sub : (1 - MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).support
        ⊆ ((1 : MvPolynomial (Fin n) (ZMod (2 ^ m))).support ∪
           (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).support) := by
      have h := MvPolynomial.support_sub
        (p := (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))))
        (q := MvPolynomial.X k)
      exact h
    have hd' := h_sub hd
    rw [Finset.mem_union] at hd'
    rcases hd' with hd1 | hdx
    · have hd0 : d = 0 := Finset.mem_singleton.mp (one_support_subset hd1)
      rw [hd0]
      exact Finset.mem_insert_self _ _
    · have hdx' : d = Finsupp.single k 1 := Finset.mem_singleton.mp (X_support_subset k hdx)
      rw [hdx']
      refine Finset.mem_insert_of_mem ?_
      exact Finset.mem_singleton_self _
  · -- `X k`. Support ⊆ {single k 1}.
    intro d hd
    have hdx' : d = Finsupp.single k 1 := Finset.mem_singleton.mp (X_support_subset k hd)
    rw [hdx']
    refine Finset.mem_insert_of_mem ?_
    exact Finset.mem_singleton_self _

/-- `vecShift s k` itself is "multilinear at k": every monomial in its
support has exponent vector with all entries `≤ 1`. -/
private lemma vecShift_isMultilinear_at (s : Fin n → ZMod 2) (k : Fin n)
    (d : Fin n →₀ ℕ) (hd : d ∈ (vecShift (m := m) s k).support) (j : Fin n) :
    d j ≤ 1 := by
  classical
  have h_in := vecShift_support_subset s k hd
  rw [Finset.mem_insert, Finset.mem_singleton] at h_in
  rcases h_in with hd0 | hdsing
  · rw [hd0]; simp
  · rw [hdsing]
    by_cases hjk : j = k
    · subst hjk
      rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply, if_neg (fun heq => hjk heq.symm)]
      exact Nat.zero_le _

/-- Multilinearity is closed under negation: `(-P).support = P.support`. -/
private lemma IsMultilinear.neg {P : DiagPhase n m} (hP : IsMultilinear P) :
    IsMultilinear (-P) := by
  intro d hd k
  rw [MvPolynomial.support_neg] at hd
  exact hP d hd k

/-- Multilinearity is closed under addition: `(P+Q).support ⊆ P.support ∪ Q.support`. -/
private lemma IsMultilinear.add {P Q : DiagPhase n m}
    (hP : IsMultilinear P) (hQ : IsMultilinear Q) :
    IsMultilinear (P + Q) := by
  classical
  intro d hd k
  have h_sub := MvPolynomial.support_add (p := P) (q := Q) hd
  rw [Finset.mem_union] at h_sub
  rcases h_sub with hP' | hQ'
  · exact hP d hP' k
  · exact hQ d hQ' k

/-- Multilinearity is closed under subtraction. -/
private lemma isMultilinear_sub {P Q : DiagPhase n m}
    (hP : IsMultilinear P) (hQ : IsMultilinear Q) :
    IsMultilinear (P - Q) := by
  rw [sub_eq_add_neg]
  exact IsMultilinear.add hP (IsMultilinear.neg hQ)

/-- Multilinearity is closed under finite sums. -/
private lemma isMultilinear_finsetSum {α : Type*} (t : Finset α)
    (f : α → DiagPhase n m) (hf : ∀ a ∈ t, IsMultilinear (f a)) :
    IsMultilinear (∑ a ∈ t, f a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      intro d hd k
      rw [MvPolynomial.support_zero] at hd
      exact absurd hd (Finset.notMem_empty _)
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      refine IsMultilinear.add (hf a (Finset.mem_insert_self a s)) ?_
      exact ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))

/-- The zero polynomial is multilinear. -/
private lemma IsMultilinear.zero : IsMultilinear (0 : DiagPhase n m) := by
  intro d hd k
  rw [MvPolynomial.support_zero] at hd
  exact absurd hd (Finset.notMem_empty _)

/-- The polynomial `monomial d c` is multilinear iff `d` itself is
multilinear (each entry ≤ 1). For `c = 0` the monomial is zero, so
multilinear vacuously. (Public because
`FrameDescentReverse.iterDiff_monomial_eq_zero_of_effLevelMonom_lt` uses it.) -/
lemma IsMultilinear.monomial (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m))
    (hd : ∀ k, d k ≤ 1) : IsMultilinear (MvPolynomial.monomial d c : DiagPhase n m) := by
  classical
  intro e he k
  by_cases hc : c = 0
  · rw [hc] at he
    rw [show (MvPolynomial.monomial d (0 : ZMod (2 ^ m)) : DiagPhase n m) = 0 from
      LinearMap.map_zero _] at he
    rw [MvPolynomial.support_zero] at he
    exact absurd he (Finset.notMem_empty _)
  · rw [MvPolynomial.support_monomial, if_neg hc, Finset.mem_singleton] at he
    rw [he]
    exact hd k

/-- The product `∏_{k ∈ s.support} f k` is multilinear when each `f k`
has support concentrated at `k` with multilinear exponents. Specifically:
if `f k` has support ⊆ `{0, Finsupp.single k 1}`, then the product
`∏_{k ∈ s} f k` over a Finset `s` has support consisting of
multilinear exponent vectors with entries `≤ 1`. -/
private lemma prod_vecShift_isMultilinear (s : Fin n → ZMod 2)
    (t : Finset (Fin n)) :
    IsMultilinear
      ((∏ k ∈ t, vecShift (m := m) s k) : DiagPhase n m) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      -- The empty product is 1: support is {0} (multilinear).
      rw [Finset.prod_empty]
      intro d hd k
      rw [MvPolynomial.mem_support_iff] at hd
      rw [MvPolynomial.coeff_one] at hd
      by_cases hd0 : d = 0
      · rw [hd0]; simp
      · rw [if_neg (fun heq => hd0 heq.symm)] at hd
        exact absurd rfl hd
  | insert a t' hat ih =>
      rw [Finset.prod_insert hat]
      -- Goal: IsMultilinear (vecShift s a * ∏ k ∈ t', vecShift s k).
      -- First: show that every monomial in `∏ j ∈ t', vecShift s j`.support has
      -- support ⊆ t' (each exponent vector is zero outside t').
      have h_prod_supp : ∀ (u : Finset (Fin n)),
          ∀ e ∈ ((∏ j ∈ u, vecShift (m := m) s j)
            : DiagPhase n m).support, ∀ j, j ∉ u → e j = 0 := by
        intro u
        induction u using Finset.induction_on with
        | empty =>
            intro e he j _
            rw [Finset.prod_empty] at he
            rw [MvPolynomial.mem_support_iff] at he
            rw [MvPolynomial.coeff_one] at he
            by_cases he0 : e = 0
            · rw [he0]; simp
            · rw [if_neg (fun heq => he0 heq.symm)] at he
              exact absurd rfl he
        | insert b u hbu ih_inner =>
            intro e he j hj
            rw [Finset.mem_insert] at hj
            push_neg at hj
            rw [Finset.prod_insert hbu] at he
            have h_mul_supp := MvPolynomial.support_mul _ _ he
            rw [Finset.mem_add] at h_mul_supp
            obtain ⟨f1, hf1, f2, hf2, h_sum'⟩ := h_mul_supp
            rw [← h_sum']
            simp only [Finsupp.add_apply]
            have hf1_j : f1 j = 0 := by
              have h1 := vecShift_support_subset s b hf1
              rw [Finset.mem_insert, Finset.mem_singleton] at h1
              rcases h1 with hf1_0 | hf1_sing
              · rw [hf1_0]; simp
              · rw [hf1_sing]
                rw [Finsupp.single_apply, if_neg (fun heq => hj.1 heq.symm)]
            have hf2_j : f2 j = 0 := ih_inner f2 hf2 j hj.2
            rw [hf1_j, hf2_j, add_zero]
      intro d hd k
      have h_mul_sub := MvPolynomial.support_mul
        (vecShift (m := m) s a) (∏ k ∈ t', vecShift (m := m) s k) hd
      rw [Finset.mem_add] at h_mul_sub
      obtain ⟨e1, he1, e2, he2, h_sum⟩ := h_mul_sub
      rw [← h_sum]
      simp only [Finsupp.add_apply]
      have h_e1 := vecShift_isMultilinear_at s a e1 he1 k
      have h_e2 := ih e2 he2 k
      by_cases hka : k = a
      · subst hka
        have h_e2_zero : e2 k = 0 := h_prod_supp t' e2 he2 k hat
        rw [h_e2_zero, add_zero]
        exact h_e1
      · -- k ≠ a. e1 k = 0 because e1 ∈ vecShift s a.support has support ⊆ {0, single a 1}.
        have h_e1_zero : e1 k = 0 := by
          have h_in := vecShift_support_subset s a he1
          rw [Finset.mem_insert, Finset.mem_singleton] at h_in
          rcases h_in with he1_0 | he1_sing
          · rw [he1_0]; simp
          · rw [he1_sing]
            rw [Finsupp.single_apply, if_neg (fun heq => hka heq.symm)]
        rw [h_e1_zero, zero_add]
        exact h_e2

/-- `bind₁ (vecShift s)` applied to a multilinear monomial yields a
multilinear polynomial. -/
private lemma bind₁_vecShift_monomial_isMultilinear
    (s : Fin n → ZMod 2) (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m))
    (hd : ∀ k, d k ≤ 1) :
    IsMultilinear ((MvPolynomial.bind₁ (vecShift (m := m) s)
        (MvPolynomial.monomial d c : DiagPhase n m)) : DiagPhase n m) := by
  classical
  rw [MvPolynomial.bind₁_monomial]
  -- For each k in d.support, d k ≥ 1 and d k ≤ 1, so d k = 1, so
  -- (vecShift s k)^(d k) = vecShift s k. The product is thus
  -- ∏ k ∈ d.support, vecShift s k, which is multilinear.
  have h_pow_eq : ∀ k ∈ d.support, (vecShift (m := m) s k) ^ (d k)
                = vecShift (m := m) s k := by
    intro k hk
    have h_ge : 1 ≤ d k := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)
    have h_le : d k ≤ 1 := hd k
    have h_eq : d k = 1 := le_antisymm h_le h_ge
    rw [h_eq, pow_one]
  rw [Finset.prod_congr rfl h_pow_eq]
  -- Now: C c * ∏ k ∈ d.support, vecShift s k.
  -- Multilinearity of a product times a constant.
  intro e he k
  have h_mul_sub := MvPolynomial.support_mul
    (MvPolynomial.C c) (∏ k ∈ d.support, vecShift (m := m) s k) he
  rw [Finset.mem_add] at h_mul_sub
  obtain ⟨e1, he1, e2, he2, h_sum⟩ := h_mul_sub
  rw [← h_sum]
  simp only [Finsupp.add_apply]
  -- e1 ∈ (C c).support, so e1 = 0.
  have h_e1_zero : e1 = 0 := by
    have h_sub : (MvPolynomial.C c : MvPolynomial (Fin n) (ZMod (2 ^ m))).support ⊆ {0} := by
      intro f hf
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hf
      by_cases hf0 : f = 0
      · rw [hf0]; exact Finset.mem_singleton_self _
      · rw [if_neg (fun heq => hf0 heq.symm)] at hf
        exact absurd rfl hf
    exact Finset.mem_singleton.mp (h_sub he1)
  rw [h_e1_zero]
  simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add]
  -- Now: e2 k ≤ 1 since e2 ∈ (∏ k ∈ d.support, vecShift s k).support.
  exact (prod_vecShift_isMultilinear s d.support : IsMultilinear _) e2 he2 k

/-- `bind₁ (vecShift s) P` is multilinear when `P` is. -/
private lemma bind₁_vecShift_isMultilinear {P : DiagPhase n m}
    (s : Fin n → ZMod 2) (h_mul : IsMultilinear P) :
    IsMultilinear (MvPolynomial.bind₁ (vecShift (m := m) s) P : DiagPhase n m) := by
  classical
  -- Rewrite bind₁ ... P = ∑ d ∈ P.support, bind₁ ... (monomial d (coeff d)).
  have h_rewrite :
      (MvPolynomial.bind₁ (vecShift (m := m) s) P : DiagPhase n m)
        = ∑ d ∈ P.support,
            MvPolynomial.bind₁ (vecShift (m := m) s)
              (MvPolynomial.monomial d (P.coeff d) : DiagPhase n m) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [h_rewrite]
  refine isMultilinear_finsetSum P.support _ ?_
  intro d hd
  exact bind₁_vecShift_monomial_isMultilinear s d (P.coeff d) (h_mul d hd)

/-- **Multilinearity preservation under `shiftBy`**: if `P` is multilinear,
so is `shiftBy s P` for any `s`. -/
theorem shiftBy_isMultilinear {P : DiagPhase n m} (s : Fin n → ZMod 2)
    (h_mul : IsMultilinear P) :
    IsMultilinear (FTQCLib.Hilbert.DiagPhase.shiftBy s P) := by
  rw [FTQCLib.Hilbert.DiagPhase.shiftBy_eq]
  exact isMultilinear_sub (bind₁_vecShift_isMultilinear s h_mul) h_mul

end DiagPhase

/-! ### Effective-level bounds for sums

The non-strict bound `effectiveLevel (shiftBy s P) ≤ effectiveLevel P`
is not needed separately: it follows from the strict-drop predicate plus
`0 < effectiveLevel P`. Below we prove the strict-drop predicate directly
by induction on the Hamming weight of `s`, using the 3-term
decomposition `shiftBy_decompose`; the two lemmas here bound the
effective level of a negation and of a 3-term sum. -/

/-- The `effectiveLevel` of `-P` equals that of `P`. -/
private lemma effectiveLevel_neg (P : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hierarchy.DiagPhase.effectiveLevel (-P)
      = FTQCLib.Hierarchy.DiagPhase.effectiveLevel P := by
  unfold FTQCLib.Hierarchy.DiagPhase.effectiveLevel
  rw [MvPolynomial.support_neg]
  apply Finset.sup_congr rfl
  intro d _
  unfold FTQCLib.Hierarchy.DiagPhase.effLevelMonom
  -- Goal: (m - 1 - twoAdicVal ((-P).coeff d)) + d.sum
  --     = (m - 1 - twoAdicVal (P.coeff d)) + d.sum
  -- After unfolding effLevelMonom, the goal is to show equality of the two sums.
  -- We use `congr 1` to reduce to showing the (m - 1 - twoAdicVal _) parts agree.
  congr 1
  -- Goal: (m - 1 - twoAdicVal ((-P).coeff d)) = (m - 1 - twoAdicVal (P.coeff d))
  congr 1
  -- Goal: twoAdicVal ((-P).coeff d) = twoAdicVal (P.coeff d).
  have h_coeff : ((-P) : FTQCLib.Hierarchy.DiagPhase n m).coeff d = - P.coeff d :=
    MvPolynomial.coeff_neg (Fin n) d P
  rw [h_coeff]
  exact FTQCLib.Hierarchy.DiagPhase.twoAdicVal_neg _

/-- `effectiveLevel` is sub-additive in the sense that
`effectiveLevel (A + B + C) ≤ max (effectiveLevel A) (max (effectiveLevel B) (effectiveLevel C))`.
A 3-term version of `effectiveLevel_add_le`, derived from
`effectiveLevel_finsetSum_le`. -/
private lemma effectiveLevel_add3_le
    (A B C : FTQCLib.Hierarchy.DiagPhase n m) :
    FTQCLib.Hierarchy.DiagPhase.effectiveLevel (A + B + C)
      ≤ max (FTQCLib.Hierarchy.DiagPhase.effectiveLevel A)
          (max (FTQCLib.Hierarchy.DiagPhase.effectiveLevel B)
            (FTQCLib.Hierarchy.DiagPhase.effectiveLevel C)) := by
  classical
  -- A + B + C = ∑ i ∈ {0, 1, 2}, [if i = 0 then A, if i = 1 then B, else C].
  set f : Fin 3 → FTQCLib.Hierarchy.DiagPhase n m := fun i =>
    if i = 0 then A else if i = 1 then B else C
  have h_sum : (A + B + C : FTQCLib.Hierarchy.DiagPhase n m)
      = ∑ i : Fin 3, f i := by
    simp [Fin.sum_univ_three, f]
  rw [h_sum]
  refine (FTQCLib.Hierarchy.DiagPhase.effectiveLevel_finsetSum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro i _
  fin_cases i
  · change FTQCLib.Hierarchy.DiagPhase.effectiveLevel (f 0) ≤ _
    simp only [f]
    exact le_max_of_le_left le_rfl
  · change FTQCLib.Hierarchy.DiagPhase.effectiveLevel (f 1) ≤ _
    simp only [f]
    refine le_max_of_le_right ?_
    exact le_max_of_le_left le_rfl
  · change FTQCLib.Hierarchy.DiagPhase.effectiveLevel (f 2) ≤ _
    simp only [f]
    refine le_max_of_le_right ?_
    exact le_max_of_le_right le_rfl

/-! ### The strict-drop predicate at arbitrary nonzero shifts

By strong induction on the Hamming weight of `s`. -/

/-- **The strict-drop predicate `ShiftByStrictDrop` holds for all `n, m`.**

Proof: strong induction on the Hamming weight of `s`. The base case
(`weight = 1`) is `shiftByStrictDrop_single`. The inductive step uses
`shiftBy_decompose` to write `shiftBy s P` as a sum of three terms, each
of which strictly drops effective level below `effectiveLevel P`. The
key auxiliary lemma is multilinearity preservation
(`shiftBy_isMultilinear`), used to invoke the single-bit strict drop on
`shiftBy s' P`. -/
theorem shiftByStrictDrop_general (n m : ℕ) : ShiftByStrictDrop n m := by
  intro P h_mul h_eff s
  -- Strong induction on hammingWeight s.
  generalize hN : hammingWeight s = N
  induction N using Nat.strong_induction_on generalizing s P with
  | _ N ih =>
      intro hs
      -- s ≠ 0 ⇒ N = hammingWeight s ≥ 1.
      have hN_pos : 1 ≤ N := by
        rw [← hN]
        rcases Nat.eq_zero_or_pos (hammingWeight s) with h0 | hpos
        · exact absurd ((hammingWeight_eq_zero_iff s).mp h0) hs
        · exact hpos
      -- Get a nonzero index i with s i = 1.
      obtain ⟨i, hsi⟩ := exists_one_of_ne_zero hs
      -- Case split on whether N = 1 (single-bit case) or N ≥ 2.
      by_cases hN1 : N = 1
      · -- N = 1: s = Pi.single i 1.
        have h_s_eq : s = Pi.single i 1 := by
          funext j
          by_cases hji : j = i
          · subst hji
            rw [Pi.single_eq_same, hsi]
          · -- For j ≠ i, s j must be 0, otherwise weight ≥ 2.
            rw [Pi.single_eq_of_ne hji]
            -- Suppose s j = 1, then both i, j are in the filter, so weight ≥ 2.
            by_contra h_ne
            -- s j ∈ {0, 1}, so s j ≠ 0 → s j = 1.
            have h_sj_one : s j = 1 := by
              have hlt : (s j).val < 2 := ZMod.val_lt _
              have hval : s j = ((s j).val : ZMod 2) := (ZMod.natCast_zmod_val _).symm
              interval_cases (s j).val
              · exfalso; apply h_ne; rw [hval]; norm_cast
              · rw [hval]; norm_cast
            -- Both i and j are in the filter, with j ≠ i. So weight ≥ 2.
            have h_two_le : 2 ≤ hammingWeight s := by
              unfold hammingWeight
              have hi_mem : i ∈ Finset.univ.filter (fun k : Fin n => s k ≠ 0) := by
                rw [Finset.mem_filter]
                exact ⟨Finset.mem_univ i, by rw [hsi]; exact one_ne_zero⟩
              have hj_mem : j ∈ Finset.univ.filter (fun k : Fin n => s k ≠ 0) := by
                rw [Finset.mem_filter]
                exact ⟨Finset.mem_univ j, by rw [h_sj_one]; exact one_ne_zero⟩
              have h_pair : ({i, j} : Finset (Fin n)) ⊆
                  Finset.univ.filter (fun k : Fin n => s k ≠ 0) := by
                intro x hx
                rw [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl
                · exact hi_mem
                · exact hj_mem
              calc 2 = ({i, j} : Finset (Fin n)).card := by
                    rw [Finset.card_insert_of_notMem (by
                      rw [Finset.mem_singleton]; exact fun heq => hji heq.symm),
                      Finset.card_singleton]
                _ ≤ _ := Finset.card_le_card h_pair
            omega
        rw [h_s_eq]
        exact shiftByStrictDrop_single n m i P h_mul h_eff
      · -- N ≥ 2.
        have hN_ge_two : 2 ≤ N := by omega
        -- s' = s - Pi.single i 1.
        set s' : Fin n → ZMod 2 := s - Pi.single i 1 with hs'_def
        have hs'_i : s' i = 0 := sub_single_at_i_eq_zero s i hsi
        have h_weight_s' : hammingWeight s' + 1 = N := by
          rw [← hN]
          exact hammingWeight_sub_single s i hsi
        have h_weight_s'_lt : hammingWeight s' < N := by omega
        -- Decompose s = Pi.single i 1 + s' (since s i = 1).
        have h_s_decomp : s = (Pi.single i 1 : Fin n → ZMod 2) + s' := by
          rw [hs'_def]; ring
        rw [h_s_decomp]
        -- Apply shiftBy_decompose.
        rw [FTQCLib.Hilbert.DiagPhase.shiftBy_decompose i s' hs'_i P]
        -- Goal: effLev (T1 + T2 + T3) < effLev P, where
        --   T1 = shiftBy (Pi.single i 1) (shiftBy s' P),
        --   T2 = shiftBy (Pi.single i 1) P,
        --   T3 = shiftBy s' P.
        refine lt_of_le_of_lt (effectiveLevel_add3_le _ _ _) ?_
        refine max_lt ?_ (max_lt ?_ ?_)
        · -- T1 = shiftBy e_i (shiftBy s' P).
          -- shiftBy s' P is multilinear by shiftBy_isMultilinear.
          have h_s'_mul := DiagPhase.shiftBy_isMultilinear s' h_mul
          -- Two cases: effLev (shiftBy s' P) > 0 or = 0.
          by_cases h_s'_eff : 0 < FTQCLib.Hierarchy.DiagPhase.effectiveLevel
              (FTQCLib.Hilbert.DiagPhase.shiftBy s' P)
          · -- Apply shiftByStrictDrop_single on (shiftBy s' P) at i:
            -- effLev (T1) < effLev (shiftBy s' P).
            have h_drop_inner := shiftByStrictDrop_single n m i
              (FTQCLib.Hilbert.DiagPhase.shiftBy s' P) h_s'_mul h_s'_eff
            -- Combined with effLev (shiftBy s' P) ≤ effLev P (which we get
            -- from the IH applied to s' if s' ≠ 0, or directly if s' = 0).
            -- Either way: effLev (shiftBy s' P) < effLev P.
            have h_t3_lt : FTQCLib.Hierarchy.DiagPhase.effectiveLevel
                (FTQCLib.Hilbert.DiagPhase.shiftBy s' P)
                < FTQCLib.Hierarchy.DiagPhase.effectiveLevel P := by
              by_cases hs'_zero : s' = 0
              · rw [hs'_zero, FTQCLib.Hilbert.DiagPhase.shiftBy_zero,
                  FTQCLib.Hierarchy.DiagPhase.effectiveLevel_zero]
                exact h_eff
              · exact ih (hammingWeight s') h_weight_s'_lt P h_mul h_eff
                  s' rfl hs'_zero
            exact h_drop_inner.trans h_t3_lt
          · -- effLev (shiftBy s' P) = 0. Then effLev T1 = effLev (shiftBy e_i (shiftBy s' P)).
            -- Reduce via shiftDeriv on a polynomial of totalDegree ≤ effLev = 0 (so constant).
            have h_s'_eff_le : FTQCLib.Hierarchy.DiagPhase.effectiveLevel
                (FTQCLib.Hilbert.DiagPhase.shiftBy s' P) ≤ 0 := Nat.not_lt.mp h_s'_eff
            have h_s'_eff_zero : FTQCLib.Hierarchy.DiagPhase.effectiveLevel
                (FTQCLib.Hilbert.DiagPhase.shiftBy s' P) = 0 := Nat.le_zero.mp h_s'_eff_le
            rw [FTQCLib.Hilbert.DiagPhase.shiftBy_single_eq_shiftDeriv]
            -- Q := shiftBy s' P. totalDegree Q ≤ effLev Q = 0.
            have h_Q_td : (FTQCLib.Hilbert.DiagPhase.shiftBy s' P).totalDegree ≤ 0 :=
              le_of_le_of_eq
                (FTQCLib.Hierarchy.DiagPhase.totalDegree_le_effectiveLevel _) h_s'_eff_zero
            rw [Nat.le_zero] at h_Q_td
            rw [FTQCLib.Hierarchy.DiagPhase.shiftDeriv_totalDegree_zero i h_Q_td]
            rw [FTQCLib.Hierarchy.DiagPhase.effectiveLevel_zero]
            exact h_eff
        · -- T2 = shiftBy (Pi.single i 1) P: by shiftByStrictDrop_single.
          exact shiftByStrictDrop_single n m i P h_mul h_eff
        · -- T3 = shiftBy s' P.
          by_cases hs'_zero : s' = 0
          · rw [hs'_zero, FTQCLib.Hilbert.DiagPhase.shiftBy_zero,
              FTQCLib.Hierarchy.DiagPhase.effectiveLevel_zero]
            exact h_eff
          · exact ih (hammingWeight s') h_weight_s'_lt P h_mul h_eff
              s' rfl hs'_zero

/-! ### Diagonal gate of a shifted phase function

Two real phase functions `f, g : (Fin n → ZMod 2) → ℝ` that differ
pointwise by an integer multiple of `2π` give equal diagonal gates
(because `exp(2πi · k) = 1` for integer `k`). This is the operator-
side "equivalence modulo `2π`" identity that lets us swap polynomial
witnesses for the shifted phase. -/

/-- Two diagonal gates agree if their phase patterns differ pointwise by
integer multiples of `2π`. -/
theorem diagonalGateEquiv_eq_of_diff_two_pi
    {f g : (Fin n → ZMod 2) → ℝ}
    (h : ∀ v, ∃ k : ℤ, f v - g v = 2 * Real.pi * (k : ℝ)) :
    diagonalGateEquiv f = diagonalGateEquiv g := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  funext w
  change diagonalGate f ψ w = diagonalGate g ψ w
  rw [diagonalGate_apply, diagonalGate_apply]
  congr 1
  obtain ⟨k, hk⟩ := h w
  -- f w = g w + 2π · k. Hence exp(I · f w) = exp(I · g w) · exp(I · 2π · k) = exp(I · g w).
  have hR : (f w : ℝ) = (g w : ℝ) + 2 * Real.pi * (k : ℝ) := by linarith
  have hC : (f w : ℂ) = (g w : ℂ) + 2 * Real.pi * (k : ℂ) := by exact_mod_cast hR
  rw [hC]
  rw [show Complex.I * ((g w : ℂ) + 2 * Real.pi * (k : ℂ))
        = Complex.I * (g w : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) from by ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The shift-difference of `realPhase (boolReduce P)` matches the
`realPhase` of `shiftBy q.X (boolReduce P)` modulo `2π·ℤ`. -/
private lemma realPhase_shiftBy_diff_two_pi
    (P : FTQCLib.Hierarchy.DiagPhase n m) (q : Pauli n) :
    ∀ v : Fin n → ZMod 2, ∃ k : ℤ,
      (DiagPhase.realPhase (DiagPhase.boolReduce P) (v + q.X) -
        DiagPhase.realPhase (DiagPhase.boolReduce P) v)
        - DiagPhase.realPhase
            (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)) v
        = 2 * Real.pi * (k : ℝ) := by
  intro v
  -- Use the eval bridge: shiftBy q.X (boolReduce P).eval v
  --   = boolReduce P.eval(v + q.X) - boolReduce P.eval v (in ZMod 2^m).
  -- Then convert to integer values and extract the modular k.
  have h_eval :
      (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)).eval v
        = (DiagPhase.boolReduce P).eval (v + q.X) - (DiagPhase.boolReduce P).eval v :=
    FTQCLib.Hilbert.DiagPhase.shiftBy_eval_eq q.X (DiagPhase.boolReduce P) v
  set A : ℕ := ((DiagPhase.boolReduce P).eval (v + q.X)).val
  set B : ℕ := ((DiagPhase.boolReduce P).eval v).val
  set C : ℕ := ((FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)).eval v).val
  -- The .val of a difference: (a - b).val ≡ a.val - b.val (mod 2^m). So C ≡ A - B (mod 2^m).
  have h_zmod : (((A : ℤ) - (B : ℤ) - (C : ℤ)) : ZMod (2^m)) = 0 := by
    push_cast
    have hA : ((A : ℕ) : ZMod (2^m)) = (DiagPhase.boolReduce P).eval (v + q.X) := by
      exact ZMod.natCast_zmod_val _
    have hB : ((B : ℕ) : ZMod (2^m)) = (DiagPhase.boolReduce P).eval v := by
      exact ZMod.natCast_zmod_val _
    have hC : ((C : ℕ) : ZMod (2^m))
        = (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)).eval v := by
      exact ZMod.natCast_zmod_val _
    rw [hA, hB, hC, h_eval]
    ring
  have h_dvd : ((2 ^ m : ℕ) : ℤ) ∣ ((A : ℤ) - (B : ℤ) - (C : ℤ)) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at h_zmod ⊢
    convert h_zmod using 1
  obtain ⟨k, hk⟩ := h_dvd
  refine ⟨k, ?_⟩
  -- realPhase difference = 2π · (A/2^m - B/2^m - C/2^m) = 2π · (A - B - C)/2^m = 2π · k.
  unfold DiagPhase.realPhase
  have hpow_ne : ((2 : ℝ)^m : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk_real : (A : ℝ) - (B : ℝ) - (C : ℝ) = (k : ℝ) * (2 : ℝ)^m := by
    have h_int_eq : ((A : ℤ) - (B : ℤ) - (C : ℤ)) = ((2 ^ m : ℕ) : ℤ) * k := hk
    have h_real_eq : (A : ℝ) - (B : ℝ) - (C : ℝ) = ((2 : ℝ)^m) * (k : ℝ) := by
      exact_mod_cast h_int_eq
    linarith
  field_simp
  linarith

/-! ### The forward direction (conditional)

We now prove the forward direction conditionally on the
`ShiftByStrictDrop` predicate. Strong induction on `k`. -/

/-- **The forward direction of Cui-Gottesman-Krishna**, conditional on
the `ShiftByStrictDrop` predicate.

For `(boolReduce P).effectiveLevel + 1 ≤ k`, the diagonal gate
`diagonalGateEquiv (realPhase P)` sits at level `k` of the operational
Clifford hierarchy.

The hypothesis `ShiftByStrictDrop n m` packages the polynomial-side
multi-bit `shiftBy` effective-level drop. For single-bit shifts the
predicate is `shiftByStrictDrop_single`; the general case is
`shiftByStrictDrop_general`. -/
theorem cgk_forward_of_strictDrop {n m : ℕ}
    (h_drop : ShiftByStrictDrop n m)
    (P : FTQCLib.Hierarchy.DiagPhase n m) {k : ℕ}
    (hk : (DiagPhase.boolReduce P).effectiveLevel + 1 ≤ k) :
    IsCliffordHierarchy k (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  rw [diagonalGateEquiv_realPhase_boolReduce]
  -- Generalise on P (to apply IH to a smaller polynomial later).
  induction k generalizing P with
  | zero => omega
  | succ k' ih =>
      have h_le : (DiagPhase.boolReduce P).effectiveLevel ≤ k' := by omega
      by_cases h_deg : 0 < (DiagPhase.boolReduce P).totalDegree
      · refine .step (fun q => ?_)
        rw [conjEquiv_diagonalGateEquiv_general]
        refine IsCliffordHierarchy.trans_pauliEquiv q ?_
        -- The shift-difference diagonal equals the gate of realPhase(shiftBy q.X (boolReduce P))
        -- (modulo 2π·ℤ pointwise).
        rw [diagonalGateEquiv_eq_of_diff_two_pi
              (realPhase_shiftBy_diff_two_pi P q)]
        -- Apply IH on shiftBy q.X (boolReduce P).
        by_cases hqX : q.X = 0
        · -- q.X = 0: shiftBy 0 = 0, realPhase 0 = 0, gate = identity, in C^1 ⊆ C^k'.
          rw [hqX, FTQCLib.Hilbert.DiagPhase.shiftBy_zero]
          have h_realPhase_zero :
              DiagPhase.realPhase (0 : FTQCLib.Hierarchy.DiagPhase n m)
                = (0 : (Fin n → ZMod 2) → ℝ) := by
            funext v
            unfold DiagPhase.realPhase DiagPhase.eval
            simp
          rw [h_realPhase_zero, diagonalGateEquiv_zero]
          -- The identity equiv is a phased Pauli (1 · pauliOperator 0).
          have h_k'_pos : 1 ≤ k' := by
            have := DiagPhase.totalDegree_le_effectiveLevel (DiagPhase.boolReduce P)
            omega
          refine IsCliffordHierarchy.mono h_k'_pos ?_
          refine .base ⟨1, 0, ?_⟩
          apply LinearMap.ext
          intro ψ
          simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_apply,
            Units.val_one, one_smul]
          rw [pauliOperator_zero]
          rfl
        · -- q.X ≠ 0: use strict drop.
          have h_eff_pos : 0 < (DiagPhase.boolReduce P).effectiveLevel := by
            calc 0 < (DiagPhase.boolReduce P).totalDegree := h_deg
              _ ≤ (DiagPhase.boolReduce P).effectiveLevel :=
                DiagPhase.totalDegree_le_effectiveLevel _
          have h_strict := h_drop (DiagPhase.boolReduce P)
            (boolReduce_isMultilinear P) h_eff_pos q.X hqX
          have h_chain :
              (DiagPhase.boolReduce
                  (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P))).effectiveLevel
                  + 1 ≤ k' := by
            have h1 : (DiagPhase.boolReduce
                  (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P))).effectiveLevel
                ≤ (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)).effectiveLevel :=
              effectiveLevel_boolReduce_le _
            have h2 :
                (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)).effectiveLevel
                < (DiagPhase.boolReduce P).effectiveLevel := h_strict
            omega
          have h_ih := ih (FTQCLib.Hilbert.DiagPhase.shiftBy q.X (DiagPhase.boolReduce P)) h_chain
          rwa [realPhase_boolReduce_eq] at h_ih
      · push_neg at h_deg
        rw [Nat.le_zero] at h_deg
        have hb : DiagPhase.boolReduce P
            = MvPolynomial.C ((DiagPhase.boolReduce P).coeff 0) :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h_deg
        exact (isCliffordHierarchy_one_of_totalDegree_zero h_deg).mono (by omega : 1 ≤ k' + 1)

/-- **The forward direction of Cui-Gottesman-Krishna** (top-level form),
unconditional: `shiftByStrictDrop_general` discharges the
`ShiftByStrictDrop` hypothesis of `cgk_forward_of_strictDrop`. -/
theorem cgk_forward {n m : ℕ}
    (P : FTQCLib.Hierarchy.DiagPhase n m) {k : ℕ}
    (hk : (DiagPhase.boolReduce P).effectiveLevel + 1 ≤ k) :
    IsCliffordHierarchy k (diagonalGateEquiv (DiagPhase.realPhase P)) :=
  cgk_forward_of_strictDrop (shiftByStrictDrop_general n m) P hk

end FTQCLib.Hilbert

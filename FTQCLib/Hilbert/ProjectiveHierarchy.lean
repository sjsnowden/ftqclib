/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseTightLevel

set_option linter.unusedSectionVars false

/-! # Projective Clifford hierarchy and CGK reverse modulo a global phase

The operator-side `IsCliffordHierarchy k U` predicate from
`FTQCLib/Hilbert/Hierarchy.lean` is invariant under global complex-unit
scaling through its `.step` constructor: `conjEquiv (α • V) Q
= conjEquiv V Q` for any unit `α : ℂˣ`, because conjugation cancels
the scalar. Consequently the operator-side hierarchy is naturally a
*projective* object — it lives on the quotient
`(QubitSpace n ≃ₗ[ℂ] QubitSpace n) / (ℂˣ acting by scaling)`.

The CGK reverse polynomial-witness theorem (`cgk_reverse_dyadic_poly_mobius_general`,
`CGKReverseTightLevel.lean`) achieves `P.totalDegree ≤ k`
but cannot achieve `P.level ≤ k` because the dyadic predicate does
not bound the base-scalar precision `m`. Concretely:
`U = e^{iπ/4} · I` lives at `IsCliffordHierarchyDyadic 1` with base
scalar `α = e^{iπ/4}` at precision `m ≥ 3`, so every polynomial
encoding has `P.level ≥ 2`. The strict `P.level ≤ k` bound is FALSE
in the non-projective framework.

In the projective framework two diagonal gates that differ by a global
complex-unit scalar are physically equivalent (they implement the
same projective unitary on rays). The troublesome global phase factors
into the equivalence relation: we can anchor the polynomial witness
so that the constant coefficient vanishes, removing one source of
precision overhead.

## What this file delivers

* **`ScalarEquiv U V`** — `U` and `V` differ by a global unit scalar.
  Equivalence relation with `refl`, `symm`, `trans`. Bundled as a
  `Setoid` for downstream applications that quotient out by the global
  phase.
* **`conjEquiv_toLinearMap_eq_of_scalarEquiv`** — conjugation
  `Q ↦ U Q U⁻¹` depends only on the projective equivalence class of `U`.
  This is the structural reason the operator-side hierarchy is
  projective.
* **`diagonalGateEquiv_scalarEquiv_anchored`** — every diagonal
  `diagonalGateEquiv g` is `ScalarEquiv` to the anchored representative
  `diagonalGateEquiv (fun v => g v - g 0)` via the global phase
  `exp(I · g 0)`.
* **`mobiusAssemblyPoly_projected`** — the constant-term-zeroed
  Möbius-assembly polynomial. Subtracting `MvPolynomial.C (P.coeff 0)`
  from any `P : DiagPhase n m` produces a polynomial with
  `coeff 0 = 0`, the same `totalDegree`, and `realPhase` shifted by a
  constant `2π · (P.coeff 0).val / 2^m`.
* **`cgk_reverse_dyadic_poly_projective`** — the projective restatement
  of `cgk_reverse_dyadic_poly_mobius_general`. For every `k ≥ 1` and every
  `U` at `IsCliffordHierarchyDyadic k` with a dyadic-anchored diagonal
  witness (`∃ f, U = diagonalGateEquiv f ∧ IsDyadicMod2pi (f 0)`, the
  same anchor that theorem needs), exists `P` with:
  * `U` `ScalarEquiv` `diagonalGateEquiv (realPhase P)`,
  * `P.totalDegree ≤ k`,
  * `MvPolynomial.coeff 0 P = 0` (the projective normalisation).

## Scope

* **`P.level ≤ k` strict bound** — not proved here. It requires bounding
  the per-`S` precision `m_S` of every non-empty Möbius coefficient
  `funcDerivPhaseSubset S g 0` by `k - |S| + 1`, the CGK
  precision-by-level bound. This file bounds `totalDegree ≤ k` (via the
  vanishing theorem) but lifts all coefficients to a uniform precision
  `m` chosen as the pointwise sup of per-`S` precisions, which can
  exceed `k`. The ScalarEquiv anchoring zeros out the `g(0)`
  contribution to precision (the constant term of the polynomial
  witness becomes `0`), but does not bound the per-`S` precisions of
  non-constant coefficients. The precision-by-level bound and the
  resulting strict `effectiveLevel ≤ k` statement are in
  `ProjectiveStrictLevel.lean`.

* **The `IsDyadicMod2pi (f 0)` hypothesis** — needed by the argument
  here. The `ScalarEquiv` shift `f → f - f 0` produces a witness with
  `f' 0 = 0` (trivially dyadic), but does **not** transport
  `IsCliffordHierarchyDyadic k U` to the shifted operator unless the
  shift's scalar `α = exp(I · f 0)` is itself dyadic: the hierarchy is
  dyadic-step-invariant but not general-scalar-step-invariant.
  `cgk_reverse_dyadic_poly_projective_effectiveLevel`
  (`ProjectiveStrictLevel.lean`) drops the hypothesis by a different
  argument.

## Anchors

* CGK 2017 (arXiv:1608.06596) §III: the polynomial framework is
  inherently projective — the level formula `w = (m - 1) + d` counts
  the projective-class hierarchy level, not the operator-level depth.
* `cgk_reverse_dyadic_poly_mobius_general` (`CGKReverseTightLevel.lean`)
  with `totalDegree ≤ k`.
* `IsCliffordHierarchyPolyEncodable` (`CGKReverseStrict.lean`) as the
  "fully tight" predicate that admits unconditional pointwise
  dyadicity.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## The projective equivalence relation -/

/-- **Projective equivalence of unitary equivalences.** Two linear
equivalences `U, V : QubitSpace n ≃ₗ[ℂ] QubitSpace n` are
*projectively equivalent* iff they differ by a global complex-unit
scalar — i.e., there is `α : ℂˣ` with
`U.toLinearMap = α • V.toLinearMap`.

In the projective Hilbert-space picture, two operators that agree up
to a global phase implement the same unitary on rays. The Clifford
hierarchy is naturally a projective object: the `.step` constructor of
`IsCliffordHierarchy` cancels global phases via conjugation. -/
def ScalarEquiv (U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : Prop :=
  ∃ α : ℂˣ, U.toLinearMap = (α : ℂ) • V.toLinearMap

@[refl] theorem ScalarEquiv.refl
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : ScalarEquiv U U := by
  refine ⟨1, ?_⟩
  simp

@[symm] theorem ScalarEquiv.symm
    {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (h : ScalarEquiv U V) :
    ScalarEquiv V U := by
  obtain ⟨α, hα⟩ := h
  refine ⟨α⁻¹, ?_⟩
  have hα_ne : ((α : ℂ)) ≠ 0 := Units.ne_zero α
  rw [hα, ← smul_assoc, smul_eq_mul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ hα_ne, one_smul]

@[trans] theorem ScalarEquiv.trans
    {U V W : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h₁ : ScalarEquiv U V) (h₂ : ScalarEquiv V W) : ScalarEquiv U W := by
  obtain ⟨α, hα⟩ := h₁
  obtain ⟨β, hβ⟩ := h₂
  refine ⟨α * β, ?_⟩
  rw [hα, hβ, ← smul_assoc, smul_eq_mul, Units.val_mul]

/-- ScalarEquiv as a setoid on `QubitSpace n ≃ₗ[ℂ] QubitSpace n`.
Bundled for downstream uses that need to quotient by global phase. -/
def scalarEquivSetoid : Setoid (QubitSpace n ≃ₗ[ℂ] QubitSpace n) where
  r := ScalarEquiv
  iseqv :=
    ⟨ScalarEquiv.refl, ScalarEquiv.symm, ScalarEquiv.trans⟩

/-! ## Conjugation is ScalarEquiv-invariant

The key structural fact justifying the projective framework: for any
`Q`, conjugation `U Q U⁻¹` depends only on the projective equivalence
class of `U`. Concretely, `(α V) Q (α V)⁻¹ = α V Q α⁻¹ V⁻¹ = V Q V⁻¹`,
the `α` and `α⁻¹` cancelling. -/

/-- **Conjugation depends only on the projective class of the conjugating
operator.** If `U` and `V` are `ScalarEquiv`, then for every `Q`,
`conjEquiv U Q` and `conjEquiv V Q` have the same underlying linear
map.

Proof: write `U = α • V` (as linear maps) and compute pointwise.
`(conjEquiv U Q) ψ = U (Q (U⁻¹ ψ))`. The forward `U` factors out an
`α`; the inverse `U⁻¹` factors out an `α⁻¹`. The `α` and `α⁻¹` combine
to `1`, leaving `V (Q (V⁻¹ ψ)) = (conjEquiv V Q) ψ`. -/
theorem conjEquiv_toLinearMap_eq_of_scalarEquiv
    {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (Q : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h : ScalarEquiv U V) :
    (conjEquiv U Q).toLinearMap = (conjEquiv V Q).toLinearMap := by
  obtain ⟨α, hα⟩ := h
  -- Forward map: U φ = α • V φ.
  have hU_apply : ∀ φ, U φ = (α : ℂ) • V φ := by
    intro φ
    have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L φ) hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  -- Inverse map. By uniqueness of inverses: U(α⁻¹ • V.symm ψ) = ψ, so
  -- U.symm ψ = α⁻¹ • V.symm ψ.
  have hα_ne : ((α : ℂ)) ≠ 0 := Units.ne_zero α
  have hα_α_inv : (α : ℂ) * ((α⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ hα_ne]
  have hUsymm_apply : ∀ ψ, U.symm ψ = ((α⁻¹ : ℂˣ) : ℂ) • V.symm ψ := by
    intro ψ
    have h_check : U (((α⁻¹ : ℂˣ) : ℂ) • V.symm ψ) = ψ := by
      rw [hU_apply, LinearEquiv.map_smul, ← smul_assoc, smul_eq_mul,
          hα_α_inv, one_smul, LinearEquiv.apply_symm_apply]
    have h_sym :
        U.symm (U (((α⁻¹ : ℂˣ) : ℂ) • V.symm ψ)) = U.symm ψ :=
      congrArg U.symm h_check
    rw [LinearEquiv.symm_apply_apply] at h_sym
    exact h_sym.symm
  -- Pointwise computation.
  apply LinearMap.ext
  intro ψ
  change (conjEquiv U Q) ψ = (conjEquiv V Q) ψ
  rw [conjEquiv_apply, conjEquiv_apply]
  rw [hUsymm_apply]
  -- Goal: U (Q (α⁻¹ • V.symm ψ)) = V (Q (V.symm ψ)).
  rw [LinearEquiv.map_smul Q]
  -- Goal: U (α⁻¹ • Q (V.symm ψ)) = V (Q (V.symm ψ)).
  rw [hU_apply]
  -- Goal: α • V (α⁻¹ • Q (V.symm ψ)) = V (Q (V.symm ψ)).
  rw [LinearEquiv.map_smul V]
  -- Goal: α • (α⁻¹ • V (Q (V.symm ψ))) = V (Q (V.symm ψ)).
  rw [← smul_assoc, smul_eq_mul, hα_α_inv, one_smul]

/-! ## Diagonal anchoring lemma

Every diagonal gate is `ScalarEquiv` to an *anchored* representative
whose phase function vanishes at `0`. The anchoring witness is the
unit scalar `α = exp(I · g 0)`, and the structural identity is
`exp(I · g v) = exp(I · g 0) · exp(I · (g v - g 0))`. -/

/-- **The complex number `exp(z)` is a unit for every `z : ℂ`.** A
direct consequence of `Complex.exp_ne_zero`. We package this as a
`ℂˣ` to plug into `ScalarEquiv`. -/
noncomputable def expUnit (z : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

@[simp] theorem expUnit_val (z : ℂ) :
    ((expUnit z : ℂˣ) : ℂ) = Complex.exp z := by
  rfl

/-- **The anchoring lemma.** Every `diagonalGateEquiv g` is
`ScalarEquiv` to the anchored representative
`diagonalGateEquiv (fun v => g v - g 0)` via the global phase
`α = exp(I · g 0) ∈ ℂˣ`.

Proof: pointwise,
`exp(I · g v) = exp(I · g 0) · exp(I · (g v - g 0))`,
so `diagonalGate g ψ v = exp(I · g 0) · diagonalGate (g - g 0) ψ v`.
The constant `exp(I · g 0)` factors out to a global scaling. -/
theorem diagonalGateEquiv_scalarEquiv_anchored
    (g : (Fin n → ZMod 2) → ℝ) :
    ScalarEquiv (diagonalGateEquiv g)
                (diagonalGateEquiv (fun v => g v - g 0)) := by
  refine ⟨expUnit (Complex.I * (g 0 : ℂ)), ?_⟩
  rw [diagonalGateEquiv_toLinearMap, diagonalGateEquiv_toLinearMap]
  apply LinearMap.ext
  intro ψ
  funext v
  -- LHS: diagonalGate g ψ v = exp(I · g v) · ψ v.
  -- RHS: (α • diagonalGate (g - g 0)) ψ v.
  --    = α • (diagonalGate (g - g 0) ψ) v
  --    = α · (diagonalGate (g - g 0) ψ v)
  --    = α · (exp(I · (g v - g 0)) · ψ v).
  rw [diagonalGate_apply]
  change Complex.exp (Complex.I * (g v : ℂ)) * ψ v
        = ((expUnit (Complex.I * (g 0 : ℂ)) : ℂˣ) : ℂ)
            * (Complex.exp (Complex.I * ((g v - g 0 : ℝ) : ℂ)) * ψ v)
  rw [expUnit_val]
  -- Identity: exp(I · g v) = exp(I · g 0) · exp(I · (g v - g 0)).
  have h_split :
      Complex.exp (Complex.I * (g v : ℂ))
        = Complex.exp (Complex.I * (g 0 : ℂ))
            * Complex.exp (Complex.I * ((g v - g 0 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h_split]
  ring

/-! ## Constant-term projection of a phase polynomial

We need to project away the constant term of a polynomial witness so
that the remaining polynomial has `coeff 0 = 0`. The constant-term
contribution to `realPhase` is a global shift; absorbing it into a
`ScalarEquiv` produces a normalised projective witness. -/

/-- The constant-coefficient projection of `P : DiagPhase n m`. We
subtract `MvPolynomial.C (P.coeff 0)` from `P`. -/
noncomputable def constProject {n m : ℕ} (P : DiagPhase n m) : DiagPhase n m :=
  P - MvPolynomial.C (P.coeff 0)

/-- The projected polynomial has the same total degree as the
original. Subtracting a constant cannot increase the total degree, and
the inequality `totalDegree (P - C c) ≤ max (totalDegree P) (totalDegree (C c))
= totalDegree P` (since `totalDegree (C c) = 0`). -/
theorem constProject_totalDegree_le {n m : ℕ} (P : DiagPhase n m) :
    (constProject P).totalDegree ≤ P.totalDegree := by
  unfold constProject
  calc (P - MvPolynomial.C (P.coeff 0)).totalDegree
      ≤ max P.totalDegree (MvPolynomial.C (P.coeff 0)).totalDegree := by
        exact MvPolynomial.totalDegree_sub _ _
    _ = max P.totalDegree 0 := by
        rw [MvPolynomial.totalDegree_C]
    _ = P.totalDegree := max_eq_left (Nat.zero_le _)

/-- The constant coefficient of the projected polynomial is zero. -/
theorem constProject_coeff_zero {n m : ℕ} (P : DiagPhase n m) :
    (constProject P).coeff 0 = 0 := by
  unfold constProject
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C]
  simp

/-- The evaluation of `constProject P` at `v` differs from that of `P`
by the constant `-P.coeff 0`. -/
theorem constProject_eval {n m : ℕ} (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    (constProject P).eval v = P.eval v - P.coeff 0 := by
  unfold constProject DiagPhase.eval
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_C]

/-- The `realPhase` of `constProject P` differs from `realPhase P` by
the constant `2π · (P.coeff 0).val / 2^m` (modulo `2π`-wraparound).

Concretely, there is an integer `J` such that
`realPhase (constProject P) v - realPhase P v
  = -2π · (P.coeff 0).val / 2^m + 2π · J`. -/
theorem realPhase_constProject_diff {n m : ℕ} (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    ∃ J : ℤ,
      DiagPhase.realPhase (constProject P) v
        = DiagPhase.realPhase P v
            - 2 * Real.pi * ((P.coeff 0).val : ℝ) / (2 : ℝ) ^ m
            + 2 * Real.pi * (J : ℝ) := by
  -- Underlying nat-cast trick: (P.eval v - P.coeff 0).val differs from
  -- P.eval v).val - (P.coeff 0).val by a multiple of 2^m.
  classical
  unfold DiagPhase.realPhase
  rw [constProject_eval]
  -- Goal:
  --   2π · (P.eval v - P.coeff 0).val / 2^m
  --     = 2π · (P.eval v).val / 2^m - 2π · (P.coeff 0).val / 2^m + 2π · J.
  set a : ZMod (2 ^ m) := P.eval v with ha_def
  set b : ZMod (2 ^ m) := P.coeff 0 with hb_def
  -- We want a J such that (a - b).val = a.val - b.val + 2^m · J in ℤ.
  -- Equivalently, ((a - b).val - a.val + b.val) is a multiple of 2^m.
  have h_dvd : ((2 ^ m : ℕ) : ℤ) ∣
      (((a - b).val : ℤ) - ((a.val : ℤ) - (b.val : ℤ))) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    -- Need: ((a - b).val - a.val + b.val : ZMod (2^m)) = 0.
    have h1 : (((a - b).val : ℕ) : ZMod (2 ^ m)) = a - b :=
      ZMod.natCast_zmod_val _
    have h2 : ((a.val : ℕ) : ZMod (2 ^ m)) = a := ZMod.natCast_zmod_val _
    have h3 : ((b.val : ℕ) : ZMod (2 ^ m)) = b := ZMod.natCast_zmod_val _
    -- After push_cast we have an equation in ZMod (2^m); simplify.
    rw [h1, h2, h3]
    ring
  obtain ⟨J, hJ⟩ := h_dvd
  refine ⟨J, ?_⟩
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h_pow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h_pow_pos
  -- Real-valued version of hJ.
  have h_real :
      ((a - b).val : ℝ) - ((a.val : ℝ) - (b.val : ℝ))
        = ((2 ^ m : ℕ) : ℝ) * (J : ℝ) := by
    have h_cast :
        (((a - b).val : ℤ) - ((a.val : ℤ) - (b.val : ℤ)) : ℝ)
          = (((2 ^ m : ℕ) : ℤ) * J : ℝ) := by
      exact_mod_cast hJ
    push_cast at h_cast
    push_cast
    linarith
  have h_pow_real_eq : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; rfl
  rw [h_pow_real_eq] at h_real
  field_simp
  linarith

/-! ## The projective reverse theorem

We now assemble the infrastructure into the projective restatement of
`cgk_reverse_dyadic_poly_mobius_general`. Given a `U` at
`IsCliffordHierarchyDyadic k` with the same anchored dyadic witness
that theorem needs, we produce a polynomial `P` with:
* `totalDegree ≤ k` (from the Möbius-assembly degree bound),
* `coeff 0 P = 0` (the projective normalisation, via `constProject`),
* `U` `ScalarEquiv` `diagonalGateEquiv (realPhase P)` (the constant
  term absorbed into the global phase).

The anchor hypothesis `IsDyadicMod2pi (f 0)` is unchanged; it is
dropped in `ProjectiveStrictLevel.lean`. -/

/-- **The projective CGK reverse with constant-term-zeroed polynomial.**
For every `k ≥ 1` and every `U : QubitSpace n ≃ₗ[ℂ] QubitSpace n` at
`IsCliffordHierarchyDyadic k` with an anchored dyadic diagonal witness,
there exist a precision `m` and a polynomial `P : DiagPhase n m` with:

* `U` is **`ScalarEquiv`** to `diagonalGateEquiv (realPhase P)`,
* `P.totalDegree ≤ k`,
* `MvPolynomial.coeff 0 P = 0` (the projective normalisation: the
  constant term has been absorbed into the global phase).

**Approach**: apply `cgk_reverse_dyadic_poly_mobius_general`
to obtain a full polynomial `P_full` with
`U = diagonalGateEquiv (realPhase P_full)` and
`P_full.totalDegree ≤ k`. Project out the constant term via
`constProject P_full`; the resulting polynomial has `coeff 0 = 0` and
the same `totalDegree`. The difference in `realPhase` is a global
phase, absorbed by `ScalarEquiv`.

Note: this does NOT give `P.level ≤ k`. The precision `m` of `P_full`
is unchanged by the projection; it is bounded only by the uniform
precision required for the Möbius coefficients of all non-empty
subsets `S` with `|S| ≤ k`, which the loose dyadic predicate does not
constrain to `m ≤ k + 1 - d`. The strict bound is
`cgk_reverse_dyadic_poly_projective_effectiveLevel`
(`ProjectiveStrictLevel.lean`).

Anchors: CGK 2017 (arXiv:1608.06596) Theorem 2 / Lemma 4 reverse
direction at `p = 2`; `cgk_reverse_dyadic_poly_mobius_general`. -/
theorem cgk_reverse_dyadic_poly_projective
    {n k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_anchor : ∃ f, U = diagonalGateEquiv f ∧ IsDyadicMod2pi (f 0))
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      ScalarEquiv U (diagonalGateEquiv (DiagPhase.realPhase P)) ∧
      P.totalDegree ≤ k ∧
      MvPolynomial.coeff 0 P = 0 := by
  -- Step 1: apply `cgk_reverse_dyadic_poly_mobius_general` to obtain the full polynomial witness.
  obtain ⟨m, P_full, hU_eq_full, h_deg_full⟩ :=
    cgk_reverse_dyadic_poly_mobius_general hk U h_diag h_anchor h_hier
  -- Step 2: project out the constant term.
  set P : DiagPhase n m := constProject P_full with hP_def
  refine ⟨m, P, ?_, ?_, ?_⟩
  · -- ScalarEquiv U (diagonalGateEquiv (realPhase P)).
    -- We have U = diagonalGateEquiv (realPhase P_full).
    -- By the realPhase-difference identity, realPhase P_full v
    --   = realPhase P v + 2π · (P_full.coeff 0).val / 2^m + 2π · J(v)
    -- for some integer J(v). So
    --   diagonalGateEquiv (realPhase P_full)
    --     = exp(I · 2π · (P_full.coeff 0).val / 2^m) • diagonalGateEquiv (realPhase P)
    -- (the J(v) integer multiples factor out via 2π-periodicity of exp).
    --
    -- This gives ScalarEquiv U (diagonalGateEquiv (realPhase P)) via the
    -- unit `α = exp(I · 2π · (P_full.coeff 0).val / 2^m)`.
    refine ⟨expUnit
      (Complex.I *
        ((2 * Real.pi * ((P_full.coeff 0).val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)), ?_⟩
    rw [hU_eq_full, diagonalGateEquiv_toLinearMap,
        diagonalGateEquiv_toLinearMap]
    apply LinearMap.ext
    intro ψ
    funext v
    rw [diagonalGate_apply]
    change Complex.exp (Complex.I * (DiagPhase.realPhase P_full v : ℂ)) * ψ v
          = ((expUnit (Complex.I *
              ((2 * Real.pi * ((P_full.coeff 0).val : ℝ) / (2 : ℝ) ^ m
                : ℝ) : ℂ)) : ℂˣ) : ℂ)
              * (Complex.exp (Complex.I * (DiagPhase.realPhase P v : ℂ)) * ψ v)
    -- We have an extra `J(v)` for each v; the 2π-periodicity absorbs it.
    obtain ⟨J, hJ⟩ := realPhase_constProject_diff (m := m) (P := P_full) v
    -- hJ : realPhase (constProject P_full) v = realPhase P_full v
    --        - 2π · (P_full.coeff 0).val / 2^m + 2π · J
    -- i.e., realPhase P v = realPhase P_full v
    --        - 2π · (P_full.coeff 0).val / 2^m + 2π · J
    -- Rearranged: realPhase P_full v
    --   = realPhase P v + 2π · (P_full.coeff 0).val / 2^m - 2π · J.
    rw [expUnit_val]
    -- Identity: exp(I · realPhase P_full v)
    --   = exp(I · 2π · (P_full.coeff 0).val / 2^m) · exp(I · realPhase P v)
    -- (modulo 2π · J factor which is exp(I · 2π · J) = 1).
    have h_eq_real :
        (DiagPhase.realPhase P_full v : ℂ)
          = ((2 * Real.pi * ((P_full.coeff 0).val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)
              + (DiagPhase.realPhase P v : ℂ)
              + ((-(2 * Real.pi * (J : ℝ))) : ℝ) := by
      have h_real :
          DiagPhase.realPhase P_full v
            = (2 * Real.pi * ((P_full.coeff 0).val : ℝ) / (2 : ℝ) ^ m)
              + DiagPhase.realPhase P v
              + (-(2 * Real.pi * (J : ℝ))) := by
        rw [← hP_def] at hJ
        linarith
      exact_mod_cast h_real
    rw [h_eq_real]
    -- exp(I · (a + b + c)) = exp(I · a) · exp(I · b) · exp(I · c).
    -- exp(I · c) = exp(I · (-2π J)) = (exp(2π I))^(-J) = 1.
    rw [show Complex.I *
            (((2 * Real.pi * ((P_full.coeff 0).val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)
              + (DiagPhase.realPhase P v : ℂ)
              + (((-(2 * Real.pi * (J : ℝ))) : ℝ) : ℂ))
          = Complex.I *
              ((2 * Real.pi * ((P_full.coeff 0).val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)
            + Complex.I * (DiagPhase.realPhase P v : ℂ)
            + Complex.I *
              (((-(2 * Real.pi * (J : ℝ))) : ℝ) : ℂ) from by ring]
    rw [Complex.exp_add, Complex.exp_add]
    -- Cancel exp(I · (-2π J)) = 1 via exp_int_mul_two_pi_mul_I.
    have h_int : Complex.I * (((-(2 * Real.pi * (J : ℝ))) : ℝ) : ℂ)
        = ((-J : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h_int]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    ring
  · -- P.totalDegree ≤ k.
    exact le_trans (constProject_totalDegree_le P_full) h_deg_full
  · -- MvPolynomial.coeff 0 P = 0.
    exact constProject_coeff_zero P_full

/-! ## Convenience corollary: projective restatement without the constant-term clause

We also state the looser projective form that doesn't carry the
`coeff 0 = 0` clause — the direct ScalarEquiv-relaxation of the
existence statement of `cgk_reverse_dyadic_poly_mobius_general`. -/

/-- **The projective CGK reverse without the constant-term clause.**
A weaker form of `cgk_reverse_dyadic_poly_projective` that drops the
`coeff 0 = 0` clause. The constant-term-zeroed version is strictly
stronger; this version is included for cases where only the
`ScalarEquiv` relation matters and the polynomial's constant
coefficient is irrelevant. -/
theorem cgk_reverse_dyadic_poly_projective_loose
    {n k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_anchor : ∃ f, U = diagonalGateEquiv f ∧ IsDyadicMod2pi (f 0))
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      ScalarEquiv U (diagonalGateEquiv (DiagPhase.realPhase P)) ∧
      P.totalDegree ≤ k := by
  obtain ⟨m, P, h_se, h_deg, _h_coeff⟩ :=
    cgk_reverse_dyadic_poly_projective hk U h_diag h_anchor h_hier
  exact ⟨m, P, h_se, h_deg⟩

/-! ## Toward the strict level bound

The infrastructure above absorbs the `g(0)` contribution into a global
phase (the `ScalarEquiv` relation) and produces a polynomial witness
with `coeff 0 = 0`. The remaining obstacle to a strict level bound is
the precision `m` of the polynomial witness.

Here `m` is chosen as the pointwise supremum (over `S ⊆ Fin n` with
`|S| ≤ k`) of per-`S` precisions `m_S` realising the dyadic
representation of `funcDerivPhaseSubset S g 0`. The CGK precision-
by-level bound states:

  for non-empty S with |S| ≤ k, m_S ≤ k - |S| + 1.

Equivalently, the higher-order Möbius coefficients live at LOWER
precision: each step `Δ_i` cuts the precision by `1`. This is the
content of CGK's Lemma 4 reverse direction.

With a uniform precision alone, the bound gives only
`P.level = (m - 1) + P.totalDegree = (k - 1) + k = 2k - 1`. The
sharper statement encodes the mixed precisions inside a
uniform-precision polynomial via divisibility,
`c_S = c'_S * 2^(m - m_S)` for `c'_S : ZMod (2^m_S)`, and measures the
result by `effectiveLevel`. Both the precision-by-level bound
(`mobiusCoeff_precision_bound`) and the resulting strict statement
(`cgk_reverse_dyadic_poly_projective_effectiveLevel`) are in
`ProjectiveStrictLevel.lean`. -/

end FTQCLib.Hilbert

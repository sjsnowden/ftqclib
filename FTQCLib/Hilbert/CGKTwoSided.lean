/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKSharpForward
import FTQCLib.Hilbert.ProjectiveStrictLevel

set_option linter.unusedSectionVars false

/-! # The two-sided CGK classification of diagonal hierarchy gates

The sharp classification of diagonal gates in the Clifford hierarchy,
assembled from the sharp forward direction
(`cgk_forward_sharp`, `FTQCLib/Hilbert/CGKSharpForward.lean`) and the sharp
projective reverse
(`cgk_reverse_dyadic_poly_projective_effectiveLevel`,
`FTQCLib/Hilbert/ProjectiveStrictLevel.lean`):

> a diagonal gate sits at hierarchy level `k` exactly when it is a
> global phase times the diagonal gate of a constant-free multilinear
> phase polynomial of effective level at most `k`.

Matching CGK's own group structure `C_d^(k) ≅ U(1) × ∏ ℤ` (full global
phase at every level — they add all global phases "for later
convenience" below their Eq. 3), the global phase `α`:

* ranges over ARBITRARY units at `k ≥ 2` (`cgk_diagonal_dyadic_iff`) —
  a dyadic-α iff would be FALSE there, since the step rule never sees
  the global scalar (`e^{iπ/3}·I` is at dyadic level 2);
* is dyadic at `k = 1` (`cgk_diagonal_dyadic_iff_one`), where the base
  constructor constrains it.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## Conjugation cancels arbitrary global scalings -/

/-- Conjugating by a scaled operator equals conjugating by the operator:
the scalar cancels. Equational form of
`conjEquiv_toLinearMap_eq_of_scalarEquiv`. -/
theorem conjEquiv_scaleEquiv_eq (β : ℂˣ)
    (V Q : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    conjEquiv (scaleEquiv β V) Q = conjEquiv V Q :=
  LinearEquiv.toLinearMap_injective
    (conjEquiv_toLinearMap_eq_of_scalarEquiv Q ⟨β, scaleEquiv_toLinearMap β V⟩)

/-- At every level `k ≥ 2` the dyadic hierarchy is closed under scaling
by an ARBITRARY unit: the step rule only constrains conjugates, and
conjugation cancels the scalar. (At `k = 1` this is false — the base
constructor constrains the scalar to be dyadic.) -/
theorem IsCliffordHierarchyDyadic.scale_of_two_le {k : ℕ} (hk : 2 ≤ k)
    (β : ℂˣ) {V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic k V) :
    IsCliffordHierarchyDyadic k (scaleEquiv β V) := by
  cases h with
  | base hb => omega
  | step hstep =>
      refine .step (fun p => ?_)
      rw [conjEquiv_scaleEquiv_eq]
      exact hstep p

/-! ## The sharp reverse, packaged

`cgk_reverse_dyadic_poly_projective_effectiveLevel` delivers the
witness at precision `k` with `effectiveLevel ≤ k` and zero constant
coefficient, up to `ScalarEquiv`. Here it is upgraded to a MULTILINEAR
witness (via `boolReduce`, which preserves all three clauses and the
gate) and the `ScalarEquiv` is unfolded into a `scaleEquiv` equation. -/

/-- **The sharp CGK reverse, classification form.** Every diagonal `U`
at dyadic hierarchy level `k ≥ 1` is a global phase times the diagonal
gate of a constant-free multilinear polynomial at precision `k` with
`effectiveLevel ≤ k`. No anchor hypothesis. -/
theorem cgk_reverse_projective_sharp {n k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (α : ℂˣ) (P : DiagPhase n k),
      DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
      DiagPhase.effectiveLevel P ≤ k ∧
      U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  obtain ⟨P, h_se, h_eff, h_c0⟩ :=
    cgk_reverse_dyadic_poly_projective_effectiveLevel hk U h_diag h_hier
  rw [diagonalGateEquiv_realPhase_boolReduce] at h_se
  obtain ⟨α, hα⟩ := scalarEquiv_iff_eq_scaleEquiv.mp h_se
  exact ⟨α, DiagPhase.boolReduce P, boolReduce_isMultilinear P,
    boolReduce_coeff_zero h_c0,
    le_trans (effectiveLevel_boolReduce_le P) h_eff, hα⟩

/-! ## The level-1 endpoint

At `k = 1` the global phase IS constrained (the base constructor forces
a dyadic scalar), and the classification inverts the base constructor
directly: a diagonal level-1 gate is a dyadic phase times a pure-Z
Pauli, whose polynomial witness is `phasedZPoly`. -/

/-- Inverting the level-1 constructor: level 0 is uninhabited, so a
level-1 member comes from the base. -/
private lemma isPhasedPauliDyadic_of_level_one
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyDyadic 1 U) : IsPhasedPauliDyadic U := by
  cases h with
  | base hb => exact hb
  | step hstep => cases hstep 0

private lemma phasedZPoly_support_form (p : Pauli n) :
    ∀ d ∈ (phasedZPoly p).support, ∃ i : Fin n, d = Finsupp.single i 1 := by
  intro d hd
  by_contra hno
  apply MvPolynomial.mem_support_iff.mp hd
  unfold phasedZPoly
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
    if_neg (fun h => hno ⟨i, h.symm⟩), mul_zero]

private lemma phasedZPoly_isMultilinear (p : Pauli n) :
    DiagPhase.IsMultilinear (phasedZPoly p) := by
  intro d hd j
  obtain ⟨i, rfl⟩ := phasedZPoly_support_form p d hd
  rw [Finsupp.single_apply]
  split_ifs <;> omega

private lemma phasedZPoly_coeff_zero (p : Pauli n) :
    (phasedZPoly p).coeff 0 = 0 := by
  unfold phasedZPoly
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
    if_neg (fun h => Finsupp.single_ne_zero.mpr one_ne_zero h), mul_zero]

private lemma phasedZPoly_effectiveLevel_le_one (p : Pauli n) :
    DiagPhase.effectiveLevel (phasedZPoly p) ≤ 1 := by
  have h_sup : (phasedZPoly p).support.sup
      (fun d => DiagPhase.effLevelMonom 1 ((phasedZPoly p).coeff d) d) ≤ 1 := by
    apply Finset.sup_le
    intro d hd
    obtain ⟨i, rfl⟩ := phasedZPoly_support_form p d hd
    unfold DiagPhase.effLevelMonom
    have h_sum : (Finsupp.single i (1 : ℕ)).sum (fun _ e => e) = 1 :=
      Finsupp.sum_single_index rfl
    rw [h_sum]
    omega
  exact h_sup

/-- A pure-Z Pauli equivalence is the diagonal gate of its
`phasedZPoly` witness. -/
private lemma pauliEquiv_eq_diagonal_of_pure_Z (p : Pauli n) (hpX : p.X = 0) :
    pauliEquiv p = diagonalGateEquiv (DiagPhase.realPhase (phasedZPoly p)) := by
  apply LinearEquiv.toLinearMap_injective
  rw [pauliEquiv_toLinearMap_eq,
    show DiagPhase.realPhase (phasedZPoly p) = phasedZPattern p
      from realPhase_phasedZPoly_eq p]
  exact (diagonalGateEquiv_phasedZPattern_eq_pauliOperator p hpX).symm

/-- **The two-sided CGK classification at level 1** (dyadic global
phase): a diagonal `U` is at dyadic hierarchy level 1 iff it is a
DYADIC phase times the diagonal gate of a constant-free multilinear
precision-1 polynomial of effective level ≤ 1 (i.e. a pure-Z Pauli
pattern). -/
theorem cgk_diagonal_dyadic_iff_one {n : ℕ}
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f) :
    IsCliffordHierarchyDyadic 1 U ↔
      ∃ (α : ℂˣ) (P : DiagPhase n 1), IsDyadicScalar α ∧
        DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
        DiagPhase.effectiveLevel P ≤ 1 ∧
        U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  constructor
  · intro h
    obtain ⟨α, p, hα_dy, hα⟩ := isPhasedPauliDyadic_of_level_one h
    obtain ⟨f, hf⟩ := h_diag
    have hpX : p.X = 0 := Pauli_X_zero_of_diagonal_phasedPauli hf hα
    refine ⟨α, phasedZPoly p, hα_dy, phasedZPoly_isMultilinear p,
      phasedZPoly_coeff_zero p, phasedZPoly_effectiveLevel_le_one p, ?_⟩
    rw [← pauliEquiv_eq_diagonal_of_pure_Z p hpX]
    apply LinearEquiv.toLinearMap_injective
    rw [scaleEquiv_toLinearMap, pauliEquiv_toLinearMap_eq]
    exact hα
  · rintro ⟨α, P, hα_dy, _h_mul, h_c0, h_eff, rfl⟩
    exact (cgk_forward_sharp_base h_c0 h_eff).dyadic_scale hα_dy

/-! ## The two-sided main theorem (k ≥ 2, free global phase) -/

/-- Classification direction of the main theorem (alias of the packaged
sharp reverse, named for the two-sided narrative): valid at every
`k ≥ 1`, with the global phase unconstrained. -/
theorem cgk_diagonal_classify {n k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (α : ℂˣ) (P : DiagPhase n k),
      DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
      DiagPhase.effectiveLevel P ≤ k ∧
      U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) :=
  cgk_reverse_projective_sharp hk U h_diag h_hier

/-- Construction direction with a DYADIC global phase: valid at every
`k ≥ 1`. -/
theorem cgk_diagonal_construct {n m k : ℕ} (hk : 1 ≤ k) {α : ℂˣ}
    (hα : IsDyadicScalar α) {P : DiagPhase n m}
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ k) :
    IsCliffordHierarchyDyadic k
      (scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P))) :=
  (cgk_forward_sharp P hk h_mul h_const h_eff).dyadic_scale hα

/-- Construction direction with an ARBITRARY global phase: valid at
`k ≥ 2` (where the hierarchy absorbs any unit scalar). -/
theorem cgk_diagonal_construct_of_two_le {n m k : ℕ} (hk : 2 ≤ k) (α : ℂˣ)
    {P : DiagPhase n m}
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ k) :
    IsCliffordHierarchyDyadic k
      (scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P))) :=
  IsCliffordHierarchyDyadic.scale_of_two_le hk α
    (cgk_forward_sharp P (by omega) h_mul h_const h_eff)

/-- **The two-sided CGK classification** (qubits, diagonal gates,
`k ≥ 2`): a diagonal `U` is at dyadic hierarchy level `k` iff it is a
global phase (ARBITRARY unit, matching CGK's `U(1) × ∏ ℤ` group
structure) times the diagonal gate of a constant-free multilinear
polynomial at precision `k` with `effectiveLevel ≤ k`.

The effective level — per monomial, `(m − 1 − v₂(c)) + deg` — is CGK's
Theorem 3 level at `p = 2`; the `k = 1` companion (where the phase is
constrained dyadic) is `cgk_diagonal_dyadic_iff_one`. -/
theorem cgk_diagonal_dyadic_iff {n k : ℕ} (hk : 2 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f) :
    IsCliffordHierarchyDyadic k U ↔
      ∃ (α : ℂˣ) (P : DiagPhase n k),
        DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
        DiagPhase.effectiveLevel P ≤ k ∧
        U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  constructor
  · exact cgk_reverse_projective_sharp (by omega) U h_diag
  · rintro ⟨α, P, h_mul, h_c0, h_eff, rfl⟩
    exact cgk_diagonal_construct_of_two_le hk α h_mul h_c0 h_eff

/-- The main theorem with existential precision: any precision `m` may
carry the witness. -/
theorem cgk_diagonal_dyadic_iff_exists_m {n k : ℕ} (hk : 2 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f) :
    IsCliffordHierarchyDyadic k U ↔
      ∃ (m : ℕ) (α : ℂˣ) (P : DiagPhase n m),
        DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
        DiagPhase.effectiveLevel P ≤ k ∧
        U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  constructor
  · intro h
    obtain ⟨α, P, h_mul, h_c0, h_eff, hU⟩ :=
      cgk_reverse_projective_sharp (by omega) U h_diag h
    exact ⟨k, α, P, h_mul, h_c0, h_eff, hU⟩
  · rintro ⟨m, α, P, h_mul, h_c0, h_eff, rfl⟩
    exact cgk_diagonal_construct_of_two_le hk α h_mul h_c0 h_eff

/-! ## The per-monomial corollary

Recovers the familiar single-gate form of CGK Theorem 2 at `p = 2`: a
monomial gate with coefficient `c` of 2-adic valuation `v` and
(multilinear) degree `deg` sits at every level
`k ≥ (m − 1 − v) + deg`. -/

/-- A single-monomial diagonal gate at its sharp CGK level. -/
theorem cgk_forward_monomial {n m : ℕ} (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m))
    {k : ℕ} (hk : 1 ≤ k) (h_lin : ∀ j, d j ≤ 1) (h_ne : d ≠ 0)
    (h_level : (m - 1 - DiagPhase.twoAdicVal c) + d.sum (fun _ e => e) ≤ k) :
    IsCliffordHierarchyDyadic k
      (diagonalGateEquiv (DiagPhase.realPhase
        (MvPolynomial.monomial d c : DiagPhase n m))) := by
  apply cgk_forward_sharp _ hk
  · intro d' hd' j
    have hd'd : d' = d :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd')
    rw [hd'd]
    exact h_lin j
  · rw [MvPolynomial.coeff_monomial, if_neg h_ne]
  · have h_sup : (MvPolynomial.monomial d c : DiagPhase n m).support.sup
        (fun d' => DiagPhase.effLevelMonom m
          ((MvPolynomial.monomial d c : DiagPhase n m).coeff d') d') ≤ k := by
      apply Finset.sup_le
      intro d' hd'
      have hd'd : d' = d :=
        Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd')
      subst hd'd
      rw [MvPolynomial.coeff_monomial, if_pos rfl]
      exact h_level
    exact h_sup

/-! ## The loose collapse at k ≥ 2

At every level `k ≥ 2` the loose and dyadic hierarchies COINCIDE — a
fact CGK never state. The engine: a level-1 member that is a CONJUGATE
`U P U⁻¹` of a Pauli squares to `±id` (conjugation preserves
`pauliOperator_squared`), so its global phase `β` satisfies `β² = ±1`,
forcing `β ∈ {1, −1, i, −i}` — dyadic. Levels above 2 collapse by
induction through the step rule. -/

private lemma exp_I_pi_div_two :
    Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private lemma exp_I_three_pi_div_two :
    Complex.exp (Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ)) = -Complex.I := by
  have h : Complex.I * ((3 * Real.pi / 2 : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I + Complex.I * ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_pi_mul_I, exp_I_pi_div_two]
  ring

/-- A unit whose square is `±1` is one of the four fourth roots of
unity, hence a dyadic scalar (witnessed at precision ≤ 2). -/
private lemma isDyadicScalar_of_sq_eq (β : ℂˣ)
    (h : (β : ℂ) ^ 2 = 1 ∨ (β : ℂ) ^ 2 = -1) :
    IsDyadicScalar β := by
  rcases h with h1 | hneg
  · -- β² = 1: β = ±1.
    have hfac : ((β : ℂ) - 1) * ((β : ℂ) + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp hfac with hz | hz
    · have hval : (β : ℂ) = 1 := by linear_combination hz
      obtain ⟨m', c, hw⟩ := isDyadicScalar_one
      exact ⟨m', c, hval.trans (by simpa using hw)⟩
    · have hval : (β : ℂ) = -1 := by linear_combination hz
      obtain ⟨m', c, hw⟩ := isDyadicScalar_neg_one
      exact ⟨m', c, hval.trans (by simpa using hw)⟩
  · -- β² = −1: β = ±i.
    have hfac : ((β : ℂ) - Complex.I) * ((β : ℂ) + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination hneg - hI
    rcases mul_eq_zero.mp hfac with hz | hz
    · -- β = i: witness precision 2, residue 1 (angle π/2).
      have hval : (β : ℂ) = Complex.I := by linear_combination hz
      refine ⟨2, 1, ?_⟩
      have hc : (((1 : ZMod (2 ^ 2)).val : ℕ) : ℝ) = 1 := by
        norm_num [show ((1 : ZMod (2 ^ 2)).val : ℕ) = 1 from by decide]
      rw [hval,
        show ((2 * Real.pi * (((1 : ZMod (2 ^ 2)).val : ℕ) : ℝ) / (2 : ℝ) ^ 2 : ℝ))
          = (Real.pi / 2 : ℝ) from by rw [hc]; ring]
      exact exp_I_pi_div_two.symm
    · -- β = −i: witness precision 2, residue 3 (angle 3π/2).
      have hval : (β : ℂ) = -Complex.I := by linear_combination hz
      refine ⟨2, 3, ?_⟩
      have hc : (((3 : ZMod (2 ^ 2)).val : ℕ) : ℝ) = 3 := by
        norm_num [show ((3 : ZMod (2 ^ 2)).val : ℕ) = 3 from by decide]
      rw [hval,
        show ((2 * Real.pi * (((3 : ZMod (2 ^ 2)).val : ℕ) : ℝ) / (2 : ℝ) ^ 2 : ℝ))
          = (3 * Real.pi / 2 : ℝ) from by rw [hc]; ring]
      exact exp_I_three_pi_div_two.symm

/-- Two scalar multiples of the identity on `QubitSpace n` agree only
if the scalars do (evaluate at the constant-one state). -/
private lemma smul_id_injective_qubit {c₁ c₂ : ℂ}
    (h : (c₁ • LinearMap.id : QubitSpace n →ₗ[ℂ] QubitSpace n)
       = c₂ • LinearMap.id) : c₁ = c₂ := by
  have h' := congrArg
    (fun L : QubitSpace n →ₗ[ℂ] QubitSpace n => L (fun _ => (1 : ℂ)) 0) h
  simpa using h'

/-- The square of a conjugated Pauli is the conjugation-invariant sign
`(-1)^{p.Z·p.X}` times the identity. -/
private lemma conjEquiv_pauliEquiv_sq
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (p : Pauli n) :
    (conjEquiv U (pauliEquiv p)).toLinearMap
        ∘ₗ (conjEquiv U (pauliEquiv p)).toLinearMap
      = ((-1 : ℂ) ^ (zDotVal p p.X)) • LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  have hsq := congrArg
    (fun L : QubitSpace n →ₗ[ℂ] QubitSpace n => L (U.symm ψ))
    (pauliOperator_squared p)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hsq
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [conjEquiv_apply, conjEquiv_apply, LinearEquiv.symm_apply_apply]
  calc U (pauliEquiv p (pauliEquiv p (U.symm ψ)))
      = U (((-1 : ℂ) ^ (zDotVal p p.X)) • U.symm ψ) := by
        rw [show pauliEquiv p (pauliEquiv p (U.symm ψ))
            = pauliOperator p (pauliOperator p (U.symm ψ)) from rfl, hsq]
    _ = ((-1 : ℂ) ^ (zDotVal p p.X)) • U (U.symm ψ) := LinearEquiv.map_smul U _ _
    _ = ((-1 : ℂ) ^ (zDotVal p p.X)) • ψ := by rw [LinearEquiv.apply_symm_apply]

/-- Inverting the loose level-1 constructor. -/
private lemma isPhasedPauli_of_level_one
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchy 1 U) : IsPhasedPauli U := by
  cases h with
  | base hb => exact hb
  | step hstep => cases hstep 0

/-- **The collapse engine**: a loose level-1 CONJUGATE `U P U⁻¹` is a
DYADIC phased Pauli — its phase squares to `±1` by the squared-Pauli
sign comparison. -/
private lemma conj_phasedPauli_dyadic
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} {p : Pauli n}
    (h1 : IsCliffordHierarchy 1 (conjEquiv U (pauliEquiv p))) :
    IsPhasedPauliDyadic (conjEquiv U (pauliEquiv p)) := by
  obtain ⟨β, q, hβq⟩ := isPhasedPauli_of_level_one h1
  refine ⟨β, q, ?_, hβq⟩
  have hV2 := conjEquiv_pauliEquiv_sq U p
  have hV2' : (conjEquiv U (pauliEquiv p)).toLinearMap
        ∘ₗ (conjEquiv U (pauliEquiv p)).toLinearMap
      = ((β : ℂ) ^ 2 * (-1 : ℂ) ^ (zDotVal q q.X)) • LinearMap.id := by
    rw [hβq, LinearMap.smul_comp, LinearMap.comp_smul, pauliOperator_squared,
      smul_smul, smul_smul]
    congr 1
    ring
  have h_eq : (β : ℂ) ^ 2 * (-1 : ℂ) ^ (zDotVal q q.X)
      = (-1 : ℂ) ^ (zDotVal p p.X) :=
    smul_id_injective_qubit (hV2'.symm.trans hV2)
  have h2 : (β : ℂ) ^ 2
      = (-1 : ℂ) ^ (zDotVal p p.X) * (-1 : ℂ) ^ (zDotVal q q.X) := by
    have hcancel : (-1 : ℂ) ^ (zDotVal q q.X) * (-1 : ℂ) ^ (zDotVal q q.X) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc (β : ℂ) ^ 2
        = (β : ℂ) ^ 2 * (-1 : ℂ) ^ (zDotVal q q.X)
            * (-1 : ℂ) ^ (zDotVal q q.X) := by
          rw [mul_assoc, hcancel, mul_one]
      _ = (-1 : ℂ) ^ (zDotVal p p.X) * (-1 : ℂ) ^ (zDotVal q q.X) := by
          rw [h_eq]
  apply isDyadicScalar_of_sq_eq
  rw [h2, ← pow_add]
  rcases Nat.even_or_odd (zDotVal p p.X + zDotVal q q.X) with he | ho
  · exact Or.inl he.neg_one_pow
  · exact Or.inr ho.neg_one_pow

/-- **The loose collapse**: at every level `k ≥ 2`, loose hierarchy
membership implies dyadic hierarchy membership. -/
theorem isCliffordHierarchyDyadic_of_two_le :
    ∀ k : ℕ, 2 ≤ k → ∀ U : QubitSpace n ≃ₗ[ℂ] QubitSpace n,
      IsCliffordHierarchy k U → IsCliffordHierarchyDyadic k U := by
  intro k
  induction k with
  | zero => omega
  | succ k' ihk =>
    intro hk U h
    cases h with
    | base hb => omega
    | step hstep =>
      by_cases hk2 : 2 ≤ k'
      · exact .step (fun p => ihk hk2 _ (hstep p))
      · have hk1 : k' = 1 := by omega
        subst hk1
        exact .step (fun p => .base (conj_phasedPauli_dyadic (hstep p)))

/-- **Loose = dyadic at every level `k ≥ 2`** — a structural fact CGK
never state: above the base, the hierarchy cannot see global phases at
all, so restricting the base scalars to dyadic ones changes nothing. -/
theorem isCliffordHierarchy_iff_dyadic_of_two_le {k : ℕ} (hk : 2 ≤ k)
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} :
    IsCliffordHierarchy k U ↔ IsCliffordHierarchyDyadic k U :=
  ⟨isCliffordHierarchyDyadic_of_two_le k hk U,
    IsCliffordHierarchyDyadic.toCliffordHierarchy⟩

/-- **The two-sided CGK classification against the PLAIN hierarchy**
(`k ≥ 2`): the loose collapse transports the dyadic main theorem. -/
theorem cgk_diagonal_iff {n k : ℕ} (hk : 2 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f) :
    IsCliffordHierarchy k U ↔
      ∃ (α : ℂˣ) (P : DiagPhase n k),
        DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
        DiagPhase.effectiveLevel P ≤ k ∧
        U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  rw [isCliffordHierarchy_iff_dyadic_of_two_le hk]
  exact cgk_diagonal_dyadic_iff hk U h_diag

end FTQCLib.Hilbert

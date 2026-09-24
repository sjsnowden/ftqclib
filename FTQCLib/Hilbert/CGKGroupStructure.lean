/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKExactness

set_option linter.unusedSectionVars false

/-! # The diagonal hierarchy groups (CGK Theorem 1 at p = 2)

The diagonal gates at each dyadic hierarchy level form a GROUP — CGK's
Theorem 1 (after Zeng–Chen–Chuang) at `p = 2`, packaged as a `Subgroup`
of the automorphism group of `QubitSpace n`
(`diagonalDyadicSubgroup`). Closure under composition and inverse runs
through the classification: witnesses add and negate, the effective
level of a sum is bounded by the max, and the global phases multiply
(dyadic phase algebra at `k = 1`, arbitrary units at `k ≥ 2`).

The carrier (strict diagonal-gate form) forces unimodular phases, so
the group statements here are against the genuine `U(1)` (`Circle`) —
matching CGK's `U(1) × ∏ ℤ` exactly at `k ≥ 2` (the explicit, corrected
isomorphism is `cgkDiagonalParametrization` in §4–5). The one
convention difference sits at `k = 1`, where the dyadic base constrains
phases to dyadic roots of unity while CGK put all of `U(1)` at every
level by fiat.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## §1 Helper inventory -/

/-- Dyadic scalars are closed under inversion: the inverse angle is the
complementary residue. -/
theorem IsDyadicScalar.inv {α : ℂˣ} (hα : IsDyadicScalar α) :
    IsDyadicScalar α⁻¹ := by
  obtain ⟨m, c, hc⟩ := hα
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  refine ⟨m, -c, ?_⟩
  have hαinv : ((α⁻¹ : ℂˣ) : ℂ)
      = (Complex.exp (Complex.I *
          (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m) : ℝ) : ℂ)))⁻¹ := by
    rw [← hc]
    exact Units.val_inv_eq_inv_val α
  rw [hαinv, ← Complex.exp_neg]
  by_cases hc0 : c = 0
  · subst hc0
    norm_num
  · haveI : NeZero c := ⟨hc0⟩
    have hval : (-c).val = 2 ^ m - c.val := ZMod.val_neg_of_ne_zero c
    rw [hval]
    rw [show Complex.I *
          (((2 * Real.pi * ((2 ^ m - c.val : ℕ) : ℝ) / (2 : ℝ) ^ m) : ℝ) : ℂ)
        = ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
          + -(Complex.I *
              (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m) : ℝ) : ℂ)) from by
      have hle : c.val ≤ 2 ^ m := le_of_lt (ZMod.val_lt c)
      have hne : ((2 : ℂ)) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
      push_cast [Nat.cast_sub hle]
      field_simp
      ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- The effective level of a sum is bounded by the max (public binary
form of the finite-sum bound). -/
lemma effectiveLevel_add_le' {m : ℕ} (P Q : DiagPhase n m) :
    DiagPhase.effectiveLevel (P + Q)
      ≤ max (DiagPhase.effectiveLevel P) (DiagPhase.effectiveLevel Q) := by
  apply Finset.sup_le
  intro d hd
  have hcoeff : (P + Q).coeff d = P.coeff d + Q.coeff d :=
    MvPolynomial.coeff_add d P Q
  have h_ne : (P + Q).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  by_cases hP0 : P.coeff d = 0
  · have hQd : (P + Q).coeff d = Q.coeff d := by rw [hcoeff, hP0, zero_add]
    have hQ_ne : Q.coeff d ≠ 0 := fun h0 => h_ne (by rw [hQd, h0])
    refine le_trans ?_ (le_max_right _ _)
    rw [show DiagPhase.effLevelMonom m ((P + Q).coeff d) d
        = DiagPhase.effLevelMonom m (Q.coeff d) d from by rw [hQd]]
    exact Finset.le_sup (f := fun d => DiagPhase.effLevelMonom m (Q.coeff d) d)
      (MvPolynomial.mem_support_iff.mpr hQ_ne)
  · by_cases hQ0 : Q.coeff d = 0
    · have hPd : (P + Q).coeff d = P.coeff d := by rw [hcoeff, hQ0, add_zero]
      refine le_trans ?_ (le_max_left _ _)
      rw [show DiagPhase.effLevelMonom m ((P + Q).coeff d) d
          = DiagPhase.effLevelMonom m (P.coeff d) d from by rw [hPd]]
      exact Finset.le_sup (f := fun d => DiagPhase.effLevelMonom m (P.coeff d) d)
        (MvPolynomial.mem_support_iff.mpr hP0)
    · have h1 : DiagPhase.effLevelMonom m (P.coeff d) d
          ≤ DiagPhase.effectiveLevel P :=
        Finset.le_sup (f := fun d => DiagPhase.effLevelMonom m (P.coeff d) d)
          (MvPolynomial.mem_support_iff.mpr hP0)
      have h2 : DiagPhase.effLevelMonom m (Q.coeff d) d
          ≤ DiagPhase.effectiveLevel Q :=
        Finset.le_sup (f := fun d => DiagPhase.effLevelMonom m (Q.coeff d) d)
          (MvPolynomial.mem_support_iff.mpr hQ0)
      have hv := DiagPhase.twoAdicVal_add_ge_min (P.coeff d) (Q.coeff d)
      unfold DiagPhase.effLevelMonom at h1 h2 ⊢
      rw [hcoeff]
      omega

/-- The effective level is invariant under negation. -/
lemma effectiveLevel_neg' {m : ℕ} (P : DiagPhase n m) :
    DiagPhase.effectiveLevel (-P) = DiagPhase.effectiveLevel P := by
  unfold DiagPhase.effectiveLevel
  rw [MvPolynomial.support_neg]
  apply Finset.sup_congr rfl
  intro d _
  unfold DiagPhase.effLevelMonom
  rw [MvPolynomial.coeff_neg, DiagPhase.twoAdicVal_neg]

private lemma isMultilinear_add' {m : ℕ} {P Q : DiagPhase n m}
    (hP : DiagPhase.IsMultilinear P) (hQ : DiagPhase.IsMultilinear Q) :
    DiagPhase.IsMultilinear (P + Q) := by
  intro d hd j
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h j
  · exact hQ d h j

private lemma isMultilinear_neg' {m : ℕ} {P : DiagPhase n m}
    (hP : DiagPhase.IsMultilinear P) :
    DiagPhase.IsMultilinear (-P) := by
  intro d hd j
  rw [MvPolynomial.support_neg] at hd
  exact hP d hd j

/-- The real phase of a sum matches the sum of real phases mod `2π`.

Public because the kernel map of the kernel frame uses it: the homomorphism
law `K_{P+Q} = K_P ∘ K_Q` needs this mod-`2π` reconciliation, since
`realPhase` is additive only modulo `2π·ℤ`. -/
lemma realPhase_add_diff_int {m : ℕ} (P Q : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    ∃ kI : ℤ,
      (DiagPhase.realPhase P v + DiagPhase.realPhase Q v)
        - DiagPhase.realPhase (P + Q) v = 2 * Real.pi * (kI : ℝ) := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have h_eval : (P + Q).eval v = P.eval v + Q.eval v := by
    unfold DiagPhase.eval
    rw [map_add]
  set A : ℕ := (P.eval v).val
  set B : ℕ := (Q.eval v).val
  set C : ℕ := ((P + Q).eval v).val
  have h_zmod : (((A : ℤ) + (B : ℤ) - (C : ℤ)) : ZMod (2 ^ m)) = 0 := by
    push_cast
    have hA : ((A : ℕ) : ZMod (2 ^ m)) = P.eval v := ZMod.natCast_zmod_val _
    have hB : ((B : ℕ) : ZMod (2 ^ m)) = Q.eval v := ZMod.natCast_zmod_val _
    have hC : ((C : ℕ) : ZMod (2 ^ m)) = (P + Q).eval v :=
      ZMod.natCast_zmod_val _
    rw [hA, hB, hC, h_eval]
    ring
  have h_dvd : ((2 ^ m : ℕ) : ℤ) ∣ ((A : ℤ) + (B : ℤ) - (C : ℤ)) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at h_zmod ⊢
    convert h_zmod using 1
  obtain ⟨kI, hk⟩ := h_dvd
  refine ⟨kI, ?_⟩
  unfold DiagPhase.realPhase
  have hpow_ne : ((2 : ℝ) ^ m : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk_real : (A : ℝ) + (B : ℝ) - (C : ℝ) = (kI : ℝ) * (2 : ℝ) ^ m := by
    have h_int_eq : ((A : ℤ) + (B : ℤ) - (C : ℤ)) = ((2 ^ m : ℕ) : ℤ) * kI := hk
    have h_real_eq : (A : ℝ) + (B : ℝ) - (C : ℝ)
        = ((2 : ℝ) ^ m) * (kI : ℝ) := by exact_mod_cast h_int_eq
    linarith
  field_simp
  linarith

/-- The real phase of a negation matches the negated real phase mod `2π`. -/
private lemma realPhase_neg_diff_int {m : ℕ} (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    ∃ kI : ℤ,
      (-(DiagPhase.realPhase P v)) - DiagPhase.realPhase (-P) v
        = 2 * Real.pi * (kI : ℝ) := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have h_eval : (-P).eval v = -(P.eval v) := by
    unfold DiagPhase.eval
    rw [map_neg]
  set A : ℕ := (P.eval v).val
  set C : ℕ := ((-P).eval v).val
  have h_zmod : (((-(A : ℤ)) - (C : ℤ)) : ZMod (2 ^ m)) = 0 := by
    push_cast
    have hA : ((A : ℕ) : ZMod (2 ^ m)) = P.eval v := ZMod.natCast_zmod_val _
    have hC : ((C : ℕ) : ZMod (2 ^ m)) = (-P).eval v := ZMod.natCast_zmod_val _
    rw [hA, hC, h_eval]
    ring
  have h_dvd : ((2 ^ m : ℕ) : ℤ) ∣ ((-(A : ℤ)) - (C : ℤ)) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at h_zmod ⊢
    convert h_zmod using 1
  obtain ⟨kI, hk⟩ := h_dvd
  refine ⟨kI, ?_⟩
  unfold DiagPhase.realPhase
  have hpow_ne : ((2 : ℝ) ^ m : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk_real : (-(A : ℝ)) - (C : ℝ) = (kI : ℝ) * (2 : ℝ) ^ m := by
    have h_int_eq : ((-(A : ℤ)) - (C : ℤ)) = ((2 ^ m : ℕ) : ℤ) * kI := hk
    have h_real_eq : (-(A : ℝ)) - (C : ℝ)
        = ((2 : ℝ) ^ m) * (kI : ℝ) := by exact_mod_cast h_int_eq
    linarith
  field_simp
  linarith

/-- The inverse of a diagonal gate is the gate of the negated pattern,
at the `LinearEquiv` level. -/
lemma diagonalGateEquiv_symm (f : (Fin n → ZMod 2) → ℝ) :
    (diagonalGateEquiv f).symm = diagonalGateEquiv (fun v => -(f v)) := by
  apply LinearEquiv.ext
  intro ψ
  rw [diagonalGateEquiv_symm_apply, diagonalGateEquiv_apply]

/-- The inverse of a scaled equivalence. -/
lemma scaleEquiv_symm' (α : ℂˣ) (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    (scaleEquiv α V).symm = scaleEquiv α⁻¹ V.symm := by
  apply LinearEquiv.ext
  intro ψ
  rw [scaleEquiv_symm_apply, scaleEquiv_apply]

/-- Composition of scaled equivalences. -/
lemma scaleEquiv_trans_scaleEquiv (α β : ℂˣ)
    (A B : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    (scaleEquiv α A).trans (scaleEquiv β B)
      = scaleEquiv (α * β) (A.trans B) := by
  apply LinearEquiv.ext
  intro ψ
  simp only [LinearEquiv.trans_apply, scaleEquiv_apply, map_smul,
    smul_smul, Units.val_mul]

/-- The real phase of the zero polynomial is the zero pattern. -/
private lemma realPhase_zero_poly (m : ℕ) :
    DiagPhase.realPhase (0 : DiagPhase n m) = (fun _ => 0) := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  funext v
  unfold DiagPhase.realPhase
  have h0 : (0 : DiagPhase n m).eval v = 0 := by
    unfold DiagPhase.eval
    rw [map_zero]
  rw [h0, ZMod.val_zero]
  simp

/-! ## §2 The diagonal subgroup (CGK Theorem 1, p = 2) -/

/-- Classification with the phase constrained dyadic when `k = 1`
(uniform interface for the closure proofs). -/
private lemma classify_dyadic_phase {k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h : IsCliffordHierarchyDyadic k U) :
    ∃ (α : ℂˣ) (P : DiagPhase n k),
      (2 ≤ k ∨ IsDyadicScalar α) ∧ DiagPhase.IsMultilinear P ∧
      P.coeff 0 = 0 ∧ DiagPhase.effectiveLevel P ≤ k ∧
      U = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  by_cases hk2 : 2 ≤ k
  · obtain ⟨α, P, h_mul, h_c0, h_eff, h_eq⟩ :=
      cgk_diagonal_classify hk U h_diag h
    exact ⟨α, P, Or.inl hk2, h_mul, h_c0, h_eff, h_eq⟩
  · have hk1 : k = 1 := by omega
    subst hk1
    obtain ⟨α, P, h_dy, h_mul, h_c0, h_eff, h_eq⟩ :=
      (cgk_diagonal_dyadic_iff_one U h_diag).mp h
    exact ⟨α, P, Or.inr h_dy, h_mul, h_c0, h_eff, h_eq⟩

/-- Membership construction with the matching phase discipline. -/
private lemma construct_dyadic_phase {k m : ℕ} (hk : 1 ≤ k) {α : ℂˣ}
    {P : DiagPhase n m}
    (hα : 2 ≤ k ∨ IsDyadicScalar α)
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ k) :
    IsCliffordHierarchyDyadic k
      (scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P))) := by
  rcases hα with hk2 | h_dy
  · exact cgk_diagonal_construct_of_two_le hk2 α h_mul h_const h_eff
  · exact cgk_diagonal_construct hk h_dy h_mul h_const h_eff

/-- **CGK Theorem 1 at p = 2 (diagonal sector)**: the diagonal gates at
dyadic hierarchy level `k ≥ 1` form a subgroup of the automorphism group
of `QubitSpace n`. -/
noncomputable def diagonalDyadicSubgroup (n k : ℕ) (hk : 1 ≤ k) :
    Subgroup ((QubitSpace n) ≃ₗ[ℂ] QubitSpace n) where
  carrier := {U | (∃ f, U = diagonalGateEquiv f)
    ∧ IsCliffordHierarchyDyadic k U}
  one_mem' := by
    constructor
    · exact ⟨0, diagonalGateEquiv_zero.symm⟩
    · have h_mem : IsCliffordHierarchyDyadic k
          (diagonalGateEquiv (DiagPhase.realPhase (0 : DiagPhase n 1))) := by
        apply cgk_forward_sharp _ hk
        · intro d hd j
          simp at hd
        · rw [MvPolynomial.coeff_zero]
        · rw [DiagPhase.effectiveLevel_zero]
          omega
      rw [realPhase_zero_poly, show (fun _ => (0:ℝ)) = (0 : (Fin n → ZMod 2) → ℝ)
        from rfl, diagonalGateEquiv_zero] at h_mem
      exact h_mem
  mul_mem' := by
    rintro U V ⟨⟨f, rfl⟩, hU⟩ ⟨⟨g, rfl⟩, hV⟩
    constructor
    · -- diagonal: U * V = V.trans U = D (g + f)
      refine ⟨g + f, ?_⟩
      show diagonalGateEquiv f * diagonalGateEquiv g
          = diagonalGateEquiv (g + f)
      rw [LinearEquiv.mul_eq_trans]
      exact (diagonalGateEquiv_add g f).symm
    · -- membership via witness addition
      obtain ⟨α, P, hα, hP_mul, hP_c0, hP_eff, hP_eq⟩ :=
        classify_dyadic_phase hk _ ⟨f, rfl⟩ hU
      obtain ⟨β, Q, hβ, hQ_mul, hQ_c0, hQ_eff, hQ_eq⟩ :=
        classify_dyadic_phase hk _ ⟨g, rfl⟩ hV
      have h_prod : diagonalGateEquiv f * diagonalGateEquiv g
          = scaleEquiv (β * α)
              (diagonalGateEquiv (DiagPhase.realPhase (Q + P))) := by
        rw [LinearEquiv.mul_eq_trans, hP_eq, hQ_eq,
          scaleEquiv_trans_scaleEquiv]
        congr 1
        rw [← diagonalGateEquiv_add]
        apply diagonalGateEquiv_eq_of_diff_two_pi
        intro v
        exact realPhase_add_diff_int Q P v
      rw [h_prod]
      apply construct_dyadic_phase hk
      · rcases hα with hk2 | hα_dy
        · exact Or.inl hk2
        · rcases hβ with hk2 | hβ_dy
          · exact Or.inl hk2
          · exact Or.inr (hβ_dy.mul hα_dy)
      · exact isMultilinear_add' hQ_mul hP_mul
      · rw [MvPolynomial.coeff_add, hQ_c0, hP_c0, add_zero]
      · exact le_trans (effectiveLevel_add_le' Q P)
          (max_le hQ_eff hP_eff)
  inv_mem' := by
    rintro U ⟨⟨f, rfl⟩, hU⟩
    constructor
    · -- diagonal: U⁻¹ = (D f).symm = D (−f)
      exact ⟨fun v => -(f v), diagonalGateEquiv_symm f⟩
    · obtain ⟨α, P, hα, hP_mul, hP_c0, hP_eff, hP_eq⟩ :=
        classify_dyadic_phase hk _ ⟨f, rfl⟩ hU
      have h_inv : (diagonalGateEquiv f)⁻¹
          = scaleEquiv α⁻¹
              (diagonalGateEquiv (DiagPhase.realPhase (-P))) := by
        show (diagonalGateEquiv f).symm = _
        rw [hP_eq, scaleEquiv_symm', diagonalGateEquiv_symm]
        congr 1
        apply diagonalGateEquiv_eq_of_diff_two_pi
        intro v
        exact realPhase_neg_diff_int P v
      rw [h_inv]
      apply construct_dyadic_phase hk
      · rcases hα with hk2 | hα_dy
        · exact Or.inl hk2
        · exact Or.inr hα_dy.inv
      · exact isMultilinear_neg' hP_mul
      · rw [MvPolynomial.coeff_neg, hP_c0, neg_zero]
      · rw [effectiveLevel_neg']
        exact hP_eff

/-- Membership in the diagonal subgroup, unfolded. -/
lemma mem_diagonalDyadicSubgroup_iff {k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    U ∈ diagonalDyadicSubgroup n k hk
      ↔ (∃ f, U = diagonalGateEquiv f) ∧ IsCliffordHierarchyDyadic k U :=
  Iff.rfl

/-- At `k ≥ 2` the same subgroup carries the PLAIN hierarchy (the loose
collapse): CGK Theorem 1 against the unrestricted phase convention. -/
lemma mem_diagonalDyadicSubgroup_iff_clifford {k : ℕ} (hk2 : 2 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    U ∈ diagonalDyadicSubgroup n k (by omega)
      ↔ (∃ f, U = diagonalGateEquiv f) ∧ IsCliffordHierarchy k U := by
  rw [mem_diagonalDyadicSubgroup_iff]
  constructor
  · rintro ⟨h_diag, h⟩
    exact ⟨h_diag, h.toCliffordHierarchy⟩
  · rintro ⟨h_diag, h⟩
    exact ⟨h_diag, (isCliffordHierarchy_iff_dyadic_of_two_le hk2).mp h⟩

/-! ## §3 Indicator exponents and the coefficient extension

The bridge between coefficient families indexed by subsets and
multilinear polynomials: the exponent vector of a squarefree monomial
is the indicator `∑ i ∈ S, single i 1`, and a constant-free multilinear
polynomial of effective level ≤ k IS the strict Möbius assembly of its
own indicator coefficients. -/

/-- The indicator exponent vector of a subset. -/
noncomputable def indS (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

lemma indS_apply (S : Finset (Fin n)) (j : Fin n) :
    indS S j = if j ∈ S then 1 else 0 := by
  classical
  unfold indS
  rw [Finsupp.finset_sum_apply]
  simp_rw [Finsupp.single_apply]
  exact Finset.sum_ite_eq' S j (fun _ => 1)

lemma indS_entries_le (S : Finset (Fin n)) : ∀ j, indS S j ≤ 1 := by
  intro j
  rw [indS_apply]
  split_ifs <;> omega

lemma indS_support (S : Finset (Fin n)) : (indS S).support = S := by
  ext j
  rw [Finsupp.mem_support_iff, indS_apply]
  split_ifs with h <;> simp [h]

lemma indS_injective : Function.Injective (indS (n := n)) := by
  intro S T h
  rw [← indS_support S, ← indS_support T, h]

lemma indS_ne_zero {S : Finset (Fin n)} (hS : S.Nonempty) : indS S ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hS
  have := congrArg (fun d : Fin n →₀ ℕ => d i) h0
  simp only [Finsupp.coe_zero, Pi.zero_apply] at this
  rw [indS_apply, if_pos hi] at this
  omega

lemma indS_sum (S : Finset (Fin n)) :
    (indS S).sum (fun _ e => e) = S.card := by
  unfold Finsupp.sum
  rw [indS_support]
  rw [show ∑ j ∈ S, indS S j = ∑ j ∈ S, 1 from
    Finset.sum_congr rfl (fun j hj => by rw [indS_apply, if_pos hj])]
  rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- A multilinear exponent vector is the indicator of its support. -/
lemma eq_indS_of_entries_le {d : Fin n →₀ ℕ} (hd : ∀ j, d j ≤ 1) :
    d = indS d.support := by
  ext j
  rw [indS_apply]
  by_cases hj : j ∈ d.support
  · rw [if_pos hj]
    have h1 := Finsupp.mem_support_iff.mp hj
    have h2 := hd j
    omega
  · rw [if_neg hj]
    exact Finsupp.notMem_support_iff.mp hj

/-- The coefficient of the strict assembly at the indicator of a
filtered subset. -/
lemma assembly_coeff_indS {k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k))
    {T : Finset (Fin n)} (hT : T.Nonempty ∧ T.card ≤ k) :
    (strictMobiusAssemblyPoly cS).coeff (indS T) = cS T := by
  classical
  unfold strictMobiusAssemblyPoly
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single T
    (fun S hS hne => by
      rw [monomialOfFinset_eq_monomial, MvPolynomial.C_mul_monomial, mul_one,
        MvPolynomial.coeff_monomial]
      change (if indS S = indS T then cS S else 0) = 0
      rw [if_neg (fun h => hne (indS_injective h))]
      )
    (fun habs => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩) habs)]
  rw [monomialOfFinset_eq_monomial, MvPolynomial.C_mul_monomial, mul_one,
    MvPolynomial.coeff_monomial]
  change (if indS T = indS T then cS T else 0) = cS T
  rw [if_pos rfl]

/-- The strict assembly has no coefficients away from filtered
indicators. -/
lemma assembly_coeff_eq_zero {k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k))
    {e : Fin n →₀ ℕ}
    (he : ∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k → e ≠ indS S) :
    (strictMobiusAssemblyPoly cS).coeff e = 0 := by
  classical
  unfold strictMobiusAssemblyPoly
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [Finset.mem_filter] at hS
  rw [monomialOfFinset_eq_monomial, MvPolynomial.C_mul_monomial, mul_one,
    MvPolynomial.coeff_monomial]
  change (if indS S = e then cS S else 0) = 0
  rw [if_neg (fun h => he S hS.2.1 hS.2.2 h.symm)]

/-- The strict assembly is multilinear (indicator exponents only). -/
lemma assembly_isMultilinear {k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k)) :
    DiagPhase.IsMultilinear (strictMobiusAssemblyPoly cS) := by
  classical
  intro e he j
  by_cases hind : ∃ S : Finset (Fin n), S.Nonempty ∧ S.card ≤ k ∧ e = indS S
  · obtain ⟨S, _, _, rfl⟩ := hind
    exact indS_entries_le S j
  · refine absurd (assembly_coeff_eq_zero cS ?_)
      (MvPolynomial.mem_support_iff.mp he)
    intro S h1 h2 heq
    exact hind ⟨S, h1, h2, heq⟩

/-- The strict assembly is constant-free. -/
lemma assembly_coeff_zero' {k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k)) :
    (strictMobiusAssemblyPoly cS).coeff 0 = 0 := by
  apply assembly_coeff_eq_zero
  intro S hS _ h0
  exact indS_ne_zero hS h0.symm

/-- **The coefficient extension**: every constant-free multilinear
polynomial of effective level ≤ k at precision k IS the strict Möbius
assembly of its own indicator coefficients. -/
theorem eq_assembly_of_multilinear {k : ℕ} {P : DiagPhase n k}
    (h_mul : DiagPhase.IsMultilinear P) (h_c0 : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ k) :
    P = strictMobiusAssemblyPoly (fun S => P.coeff (indS S)) := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases he : ∃ T : Finset (Fin n), (T.Nonempty ∧ T.card ≤ k) ∧ e = indS T
  · obtain ⟨T, hT, rfl⟩ := he
    rw [assembly_coeff_indS _ hT]
  · rw [assembly_coeff_eq_zero _
      (fun S h1 h2 heq => he ⟨S, ⟨h1, h2⟩, heq⟩)]
    by_contra hP
    apply he
    have h_mem : e ∈ P.support := MvPolynomial.mem_support_iff.mpr hP
    have h_entries : ∀ j, e j ≤ 1 := fun j => h_mul e h_mem j
    have h_eq : e = indS e.support := eq_indS_of_entries_le h_entries
    have h_ne : e.support.Nonempty := by
      rcases Finset.eq_empty_or_nonempty e.support with h0 | h1
      · exfalso
        apply hP
        rw [Finsupp.support_eq_empty.mp h0]
        exact h_c0
      · exact h1
    have h_card : e.support.card ≤ k := by
      have h_le : DiagPhase.effLevelMonom k (P.coeff e) e ≤ k :=
        le_trans (Finset.le_sup
          (f := fun d => DiagPhase.effLevelMonom k (P.coeff d) d) h_mem) h_eff
      unfold DiagPhase.effLevelMonom at h_le
      have h_sum : e.sum (fun _ x => x) = e.support.card := by
        rw [h_eq, indS_sum, indS_support]
      omega
    exact ⟨e.support, ⟨h_ne, h_card⟩, h_eq⟩

/-! ## §4 The corrected Corollaries 1–2: the component group and the
parametrization homomorphism

CGK's printed n-qudit Corollary 2 exponent `⌊(w − wt a)/(p−1)⌋`
contradicts their own single-qudit Corollary 1 (at `p = 2`, level `k`,
the single-qubit factor must be `ℤ/2^k`, not `ℤ/2^(k−1)`). The correct
component for the monomial slot `S` is `ℤ/2^(k−|S|+1)` — exactly the
precisions delivered by the strict Möbius machinery. The global-phase
factor is the genuine `U(1)` (`Circle`): the diagonal subgroup's
carrier forces unimodular phases. -/

/-- The index of monomial slots at level `k`: nonempty subsets of size
at most `k`. -/
def CGKIndex (n k : ℕ) := {S : Finset (Fin n) // S.Nonempty ∧ S.card ≤ k}

noncomputable instance (k : ℕ) : Fintype (CGKIndex n k) := by
  unfold CGKIndex
  classical
  infer_instance

instance (k : ℕ) : DecidableEq (CGKIndex n k) := by
  unfold CGKIndex
  infer_instance

/-- The component group of the corrected CGK Corollary 2 at level `k`:
one cyclic factor `ℤ/2^(k−|S|+1)` per slot. -/
abbrev CGKComponents (n k : ℕ) : Type :=
  ∀ S : CGKIndex n k, ZMod (2 ^ (k - S.val.card + 1))

private lemma cgkIndex_le {k : ℕ} (S : Finset (Fin n))
    (h : S.Nonempty ∧ S.card ≤ k) : k - S.card + 1 ≤ k := by
  have h1 : 1 ≤ S.card := Finset.card_pos.mpr h.1
  have h2 := h.2
  omega

/-- The assembled polynomial of a component family. -/
noncomputable def cgkAssemble {k : ℕ} (c : CGKComponents n k) :
    DiagPhase n k :=
  strictMobiusAssemblyPoly (fun S =>
    if h : S.Nonempty ∧ S.card ≤ k
    then dmapTo (k - S.card + 1) k (c ⟨S, h⟩) else 0)

/-- The assembled polynomial of a component family is multilinear. -/
lemma cgkAssemble_isMultilinear {k : ℕ} (c : CGKComponents n k) :
    DiagPhase.IsMultilinear (cgkAssemble c) :=
  assembly_isMultilinear _

/-- The assembled polynomial of a component family has zero constant term. -/
lemma cgkAssemble_coeff_zero {k : ℕ} (c : CGKComponents n k) :
    (cgkAssemble c).coeff 0 = 0 :=
  assembly_coeff_zero' _

/-- The assembled polynomial of a level-`k` component family has effective level at most `k`. -/
lemma cgkAssemble_effectiveLevel_le {k : ℕ} (hk : 1 ≤ k)
    (c : CGKComponents n k) :
    DiagPhase.effectiveLevel (cgkAssemble c) ≤ k := by
  apply strictMobiusAssemblyPoly_effectiveLevel_le hk
  · intro S hS hSk
    rw [dif_pos ⟨hS, hSk⟩]
    have hle : k - S.card + 1 ≤ k := cgkIndex_le S ⟨hS, hSk⟩
    rw [dmapTo_val hle]
    have hexp : k - (k - S.card + 1) = S.card - 1 := by
      have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
      omega
    rw [hexp]
    exact dvd_mul_right _ _
  · intro S hS
    rw [dif_neg hS]

private lemma assembly_add {k : ℕ} (c1 c2 : Finset (Fin n) → ZMod (2 ^ k)) :
    strictMobiusAssemblyPoly (fun S => c1 S + c2 S)
      = strictMobiusAssemblyPoly c1 + strictMobiusAssemblyPoly c2 := by
  unfold strictMobiusAssemblyPoly
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_add, add_mul]

private lemma assembly_congr_filter {k : ℕ}
    {c1 c2 : Finset (Fin n) → ZMod (2 ^ k)}
    (h : ∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k → c1 S = c2 S) :
    strictMobiusAssemblyPoly c1 = strictMobiusAssemblyPoly c2 := by
  unfold strictMobiusAssemblyPoly
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mem_filter] at hS
  rw [h S hS.2.1 hS.2.2]

/-- Assembly is additive in the component family. -/
lemma cgkAssemble_add {k : ℕ} (c c' : CGKComponents n k) :
    cgkAssemble (c + c') = cgkAssemble c + cgkAssemble c' := by
  unfold cgkAssemble
  rw [← assembly_add]
  congr 1
  funext S
  by_cases h : S.Nonempty ∧ S.card ≤ k
  · rw [dif_pos h, dif_pos h, dif_pos h]
    exact dmapTo_add (cgkIndex_le S h) _ _
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

private lemma cgkAssemble_zero {k : ℕ} :
    cgkAssemble (0 : CGKComponents n k) = 0 := by
  unfold cgkAssemble strictMobiusAssemblyPoly
  apply Finset.sum_eq_zero
  intro S hS
  rw [Finset.mem_filter] at hS
  show MvPolynomial.C (if h : S.Nonempty ∧ S.card ≤ k
      then dmapTo (k - S.card + 1) k ((0 : CGKComponents n k) ⟨S, h⟩) else 0)
    * monomialOfFinset S = 0
  rw [dif_pos hS.2, show (0 : CGKComponents n k) ⟨S, hS.2⟩ = 0 from rfl,
    dmapTo_zero, map_zero, zero_mul]

/-- Adding polynomials multiplies the gates (mod-2π bookkeeping). -/
private lemma diag_gate_poly_add {k : ℕ} (P Q : DiagPhase n k) :
    diagonalGateEquiv (DiagPhase.realPhase (P + Q))
      = (diagonalGateEquiv (DiagPhase.realPhase P)).trans
          (diagonalGateEquiv (DiagPhase.realPhase Q)) := by
  rw [← diagonalGateEquiv_add]
  apply diagonalGateEquiv_eq_of_diff_two_pi
  intro v
  obtain ⟨kI, hkI⟩ := realPhase_add_diff_int P Q v
  refine ⟨-kI, ?_⟩
  push_cast
  have : DiagPhase.realPhase P v + DiagPhase.realPhase Q v
      - DiagPhase.realPhase (P + Q) v = 2 * Real.pi * (kI : ℝ) := hkI
  show DiagPhase.realPhase (P + Q) v
      - (DiagPhase.realPhase P v + DiagPhase.realPhase Q v) = _
  linarith

/-- The parametrization map, function level: a circle phase and a
component family give a diagonal level-`k` gate. -/
noncomputable def cgkParamFun {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k)
    (x : Circle × Multiplicative (CGKComponents n k)) :
    ↥(diagonalDyadicSubgroup n k hk1) := by
  refine ⟨scaleEquiv (Circle.toUnits x.1)
    (diagonalGateEquiv (DiagPhase.realPhase
      (cgkAssemble (Multiplicative.toAdd x.2)))), ?_, ?_⟩
  · -- diagonal: the circle phase folds into the pattern
    set θ : ℝ := Complex.arg (x.1 : ℂ) with hθ_def
    have hζ : Circle.toUnits x.1 = expUnit (Complex.I * (θ : ℂ)) := by
      apply Units.ext
      rw [Circle.toUnits_apply, expUnit_val]
      show (x.1 : ℂ) = _
      conv_lhs => rw [← Circle.exp_arg x.1]
      rw [Circle.coe_exp, mul_comm]
    refine ⟨fun v => θ + DiagPhase.realPhase
      (cgkAssemble (Multiplicative.toAdd x.2)) v, ?_⟩
    rw [hζ, scaleEquiv_expUnit_diagonalGateEquiv]
  · exact cgk_diagonal_construct_of_two_le hk2 _
      (cgkAssemble_isMultilinear _) (cgkAssemble_coeff_zero _)
      (cgkAssemble_effectiveLevel_le hk1 _)

/-- The parametrization as a monoid homomorphism. -/
noncomputable def cgkParamHom {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    (Circle × Multiplicative (CGKComponents n k))
      →* ↥(diagonalDyadicSubgroup n k hk1) where
  toFun := cgkParamFun hk1 hk2
  map_one' := by
    apply Subtype.ext
    show scaleEquiv (Circle.toUnits 1)
        (diagonalGateEquiv (DiagPhase.realPhase
          (cgkAssemble (Multiplicative.toAdd (1 : Multiplicative
            (CGKComponents n k)))))) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (CGKComponents n k))
        = 0 from rfl, cgkAssemble_zero, realPhase_zero_poly,
      show (fun _ : Fin n → ZMod 2 => (0 : ℝ))
        = (0 : (Fin n → ZMod 2) → ℝ) from rfl,
      diagonalGateEquiv_zero, map_one, scaleEquiv_one]
    rfl
  map_mul' := by
    intro x y
    apply Subtype.ext
    show scaleEquiv (Circle.toUnits (x.1 * y.1))
        (diagonalGateEquiv (DiagPhase.realPhase
          (cgkAssemble (Multiplicative.toAdd (x.2 * y.2)))))
      = ((cgkParamFun hk1 hk2 x : (QubitSpace n) ≃ₗ[ℂ] QubitSpace n)
          * (cgkParamFun hk1 hk2 y : (QubitSpace n) ≃ₗ[ℂ] QubitSpace n))
    rw [show Multiplicative.toAdd (x.2 * y.2)
        = Multiplicative.toAdd x.2 + Multiplicative.toAdd y.2 from rfl]
    rw [LinearEquiv.mul_eq_trans]
    show _ = ((cgkParamFun hk1 hk2 y :
        (QubitSpace n) ≃ₗ[ℂ] QubitSpace n)).trans
      ((cgkParamFun hk1 hk2 x : (QubitSpace n) ≃ₗ[ℂ] QubitSpace n))
    unfold cgkParamFun
    simp only []
    rw [scaleEquiv_trans_scaleEquiv, cgkAssemble_add, diag_gate_poly_add]
    rw [show Circle.toUnits (x.1 * y.1)
        = Circle.toUnits y.1 * Circle.toUnits x.1 from by
      rw [map_mul, mul_comm]]
    congr 1
    rw [← diag_gate_poly_add, ← diag_gate_poly_add, add_comm]

/-! ## §5 Bijectivity, the isomorphism, and the generating set -/

/-- **The diagonal level-`k` group is ABELIAN** (as CGK's Corollaries
require): diagonal gates commute since their phase patterns add. -/
noncomputable instance {k : ℕ} {hk : 1 ≤ k} :
    CommGroup ↥(diagonalDyadicSubgroup n k hk) :=
  { (inferInstance : Group ↥(diagonalDyadicSubgroup n k hk)) with
    mul_comm := by
      rintro ⟨U, ⟨f, rfl⟩, hU⟩ ⟨V, ⟨g, rfl⟩, hV⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      show diagonalGateEquiv f * diagonalGateEquiv g
          = diagonalGateEquiv g * diagonalGateEquiv f
      rw [LinearEquiv.mul_eq_trans, LinearEquiv.mul_eq_trans,
        ← diagonalGateEquiv_add, ← diagonalGateEquiv_add, add_comm] }

lemma dmapTo_injective {m k : ℕ} (h : m ≤ k) :
    Function.Injective (dmapTo m k) := by
  intro a b hab
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have hval := congrArg ZMod.val hab
  rw [dmapTo_val h, dmapTo_val h] at hval
  have hv : a.val = b.val :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hval
  rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hv]

private lemma scaleEquiv_left_cancel {u : ℂˣ}
    {X Y : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : scaleEquiv u X = scaleEquiv u Y) : X = Y := by
  have h2 := congrArg (scaleEquiv u⁻¹) h
  rwa [scaleEquiv_scaleEquiv, scaleEquiv_scaleEquiv, inv_mul_cancel,
    scaleEquiv_one, scaleEquiv_one] at h2

/-- Equal gates of constant-free multilinear precision-`k` polynomials
force the polynomials equal. -/
private lemma poly_eq_of_gate_eq {k : ℕ} {P Q : DiagPhase n k}
    (hPm : DiagPhase.IsMultilinear P) (hQm : DiagPhase.IsMultilinear Q)
    (hPc : P.coeff 0 = 0) (hQc : Q.coeff 0 = 0)
    (h : diagonalGateEquiv (DiagPhase.realPhase P)
        = diagonalGateEquiv (DiagPhase.realPhase Q)) : P = Q := by
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  apply multilinear_eval_injective hPm hQm
  intro v
  have h' : diagonalGateEquiv (DiagPhase.realPhase Q)
      = scaleEquiv 1 (diagonalGateEquiv (DiagPhase.realPhase P)) := by
    rw [scaleEquiv_one]
    exact h.symm
  have hval := eval_val_mul_eq_of_eq_scaleEquiv hPc hQc h' v
  have hv : (Q.eval v).val = (P.eval v).val :=
    Nat.eq_of_mul_eq_mul_right (by positivity) hval
  rw [← ZMod.natCast_zmod_val (P.eval v),
    ← ZMod.natCast_zmod_val (Q.eval v), hv]

/-- Equal scaled diagonal gates of constant-free polynomials force the
phases equal. -/
private lemma units_eq_of_scale_diag_eq {k₁ k₂ : ℕ} {u₁ u₂ : ℂˣ}
    {P : DiagPhase n k₁} {Q : DiagPhase n k₂}
    (hPc : P.coeff 0 = 0) (hQc : Q.coeff 0 = 0)
    (h : scaleEquiv u₁ (diagonalGateEquiv (DiagPhase.realPhase P))
        = scaleEquiv u₂ (diagonalGateEquiv (DiagPhase.realPhase Q))) :
    u₁ = u₂ := by
  have h_at0 := congrArg (fun L : QubitSpace n ≃ₗ[ℂ] QubitSpace n
    => L (computational 0)) h
  simp only [scaleEquiv_apply, diagonalGateEquiv_apply,
    diagonalGate_computational] at h_at0
  rw [realPhase_zero_input hPc, realPhase_zero_input hQc] at h_at0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_smul] at h_at0
  apply Units.ext
  have h_eval0 := congrFun h_at0 (0 : Fin n → ZMod 2)
  simp only [Pi.smul_apply, computational_self, smul_eq_mul,
    mul_one] at h_eval0
  exact h_eval0

private lemma cgkAssemble_coeff_indS {k : ℕ} (c : CGKComponents n k)
    (S : CGKIndex n k) :
    (cgkAssemble c).coeff (indS S.val)
      = dmapTo (k - S.val.card + 1) k (c S) := by
  unfold cgkAssemble
  rw [assembly_coeff_indS _ S.prop, dif_pos S.prop]
  rfl

private lemma cgkParam_injective {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    Function.Injective (cgkParamFun (n := n) hk1 hk2) := by
  intro x y hxy
  have h_amb : scaleEquiv (Circle.toUnits x.1)
      (diagonalGateEquiv (DiagPhase.realPhase
        (cgkAssemble (Multiplicative.toAdd x.2))))
    = scaleEquiv (Circle.toUnits y.1)
      (diagonalGateEquiv (DiagPhase.realPhase
        (cgkAssemble (Multiplicative.toAdd y.2)))) := congrArg
    (Subtype.val : ↥(diagonalDyadicSubgroup n k hk1) → _) hxy
  have h_u : Circle.toUnits x.1 = Circle.toUnits y.1 :=
    units_eq_of_scale_diag_eq (cgkAssemble_coeff_zero _)
      (cgkAssemble_coeff_zero _) h_amb
  have h_ζ : x.1 = y.1 := by
    apply Circle.ext
    have h_v := congrArg Units.val h_u
    rw [Circle.toUnits_apply, Circle.toUnits_apply] at h_v
    exact h_v
  rw [h_u] at h_amb
  have h_gate := scaleEquiv_left_cancel h_amb
  have h_poly := poly_eq_of_gate_eq (cgkAssemble_isMultilinear _)
    (cgkAssemble_isMultilinear _) (cgkAssemble_coeff_zero _)
    (cgkAssemble_coeff_zero _) h_gate
  have h_c : Multiplicative.toAdd x.2 = Multiplicative.toAdd y.2 := by
    funext S
    have hcoeff := congrArg
      (fun R : DiagPhase n k => R.coeff (indS S.val)) h_poly
    simp only [cgkAssemble_coeff_indS] at hcoeff
    exact dmapTo_injective (cgkIndex_le S.val S.prop) hcoeff
  refine Prod.ext h_ζ ?_
  exact Multiplicative.toAdd.injective h_c

private lemma cgkParam_surjective {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    Function.Surjective (cgkParamFun (n := n) hk1 hk2) := by
  rintro ⟨U, h_diag, h_mem⟩
  obtain ⟨α, P, hPm, hPc, hPe, hU_eq⟩ :=
    cgk_diagonal_classify hk1 U h_diag h_mem
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  obtain ⟨f, hf⟩ := h_diag
  -- the phase is unimodular: read it off the zero basis state
  have hα_val : (α : ℂ) = Complex.exp (Complex.I * ((f 0 : ℝ) : ℂ)) := by
    have h2 : diagonalGateEquiv f
        = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)) := by
      rw [← hf]
      exact hU_eq
    have h_at0 := congrArg (fun L : QubitSpace n ≃ₗ[ℂ] QubitSpace n
      => L (computational 0)) h2
    simp only [scaleEquiv_apply, diagonalGateEquiv_apply,
      diagonalGate_computational] at h_at0
    rw [realPhase_zero_input hPc] at h_at0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      one_smul] at h_at0
    have h_eval0 := congrFun h_at0 (0 : Fin n → ZMod 2)
    simp only [Pi.smul_apply, computational_self, smul_eq_mul,
      mul_one] at h_eval0
    exact h_eval0.symm
  have hα_norm : ‖(α : ℂ)‖ = 1 := by
    rw [hα_val, Complex.norm_exp]
    simp
  set ζ : Circle := ⟨(α : ℂ), mem_sphere_zero_iff_norm.mpr hα_norm⟩
    with hζ_def
  have hζ_units : Circle.toUnits ζ = α := by
    apply Units.ext
    rw [Circle.toUnits_apply]
    rfl
  -- the components: divide out the embedding
  set c : CGKComponents n k := fun S =>
    (((P.coeff (indS S.val)).val / 2 ^ (S.val.card - 1) : ℕ)
      : ZMod (2 ^ (k - S.val.card + 1))) with hc_def
  have h_key : ∀ (S : Finset (Fin n)) (hS : S.Nonempty ∧ S.card ≤ k),
      dmapTo (k - S.card + 1) k (c ⟨S, hS⟩) = P.coeff (indS S) := by
    intro S hS
    haveI : NeZero ((2 : ℕ) ^ (k - S.card + 1)) :=
      ⟨pow_ne_zero _ (by norm_num)⟩
    have hle : k - S.card + 1 ≤ k := cgkIndex_le S hS
    have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hS.1
    have hexp : k - (k - S.card + 1) = S.card - 1 := by omega
    have h_dvd : 2 ^ (S.card - 1) ∣ (P.coeff (indS S)).val := by
      by_cases hc0 : P.coeff (indS S) = 0
      · rw [hc0, ZMod.val_zero]
        exact dvd_zero _
      · have h_supp : indS S ∈ P.support :=
          MvPolynomial.mem_support_iff.mpr hc0
        have h_le : DiagPhase.effLevelMonom k (P.coeff (indS S)) (indS S) ≤ k :=
          le_trans (Finset.le_sup
            (f := fun d => DiagPhase.effLevelMonom k (P.coeff d) d) h_supp) hPe
        unfold DiagPhase.effLevelMonom at h_le
        rw [indS_sum] at h_le
        have hv := DiagPhase.twoAdicVal_lt_of_ne_zero hc0
        rw [DiagPhase.pow_dvd_val_iff hc0 (S.card - 1)]
        omega
    set x : ℕ := (P.coeff (indS S)).val with hx_def
    set q : ℕ := x / 2 ^ (S.card - 1) with hq_def
    have hq_mul : 2 ^ (S.card - 1) * q = x := Nat.mul_div_cancel' h_dvd
    have hx_lt : x < 2 ^ k := ZMod.val_lt _
    have hq_lt : q < 2 ^ (k - S.card + 1) := by
      have h2k : (2 : ℕ) ^ k = 2 ^ (S.card - 1) * 2 ^ (k - S.card + 1) := by
        rw [← pow_add]
        congr 1
        omega
      by_contra hq
      have hge : 2 ^ (k - S.card + 1) ≤ q := Nat.le_of_not_lt hq
      have hcontra : (2 : ℕ) ^ k ≤ x := by
        rw [h2k, ← hq_mul]
        exact Nat.mul_le_mul_left _ hge
      omega
    have hcval : (c ⟨S, hS⟩).val = q := by
      show (((x / 2 ^ (S.card - 1) : ℕ)
        : ZMod (2 ^ (k - S.card + 1)))).val = q
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt hq_lt
    have hval_eq : (dmapTo (k - S.card + 1) k (c ⟨S, hS⟩)).val = x := by
      rw [dmapTo_val hle, hcval, hexp]
      exact hq_mul
    rw [← ZMod.natCast_zmod_val (dmapTo (k - S.card + 1) k (c ⟨S, hS⟩)),
      hval_eq, hx_def, ZMod.natCast_zmod_val]
  have h_assemble : cgkAssemble c = P := by
    calc cgkAssemble c
        = strictMobiusAssemblyPoly (fun S => P.coeff (indS S)) := by
          apply assembly_congr_filter
          intro S h1 h2
          rw [dif_pos ⟨h1, h2⟩]
          exact h_key S ⟨h1, h2⟩
      _ = P := (eq_assembly_of_multilinear hPm hPc hPe).symm
  refine ⟨(ζ, Multiplicative.ofAdd c), ?_⟩
  apply Subtype.ext
  show scaleEquiv (Circle.toUnits ζ)
      (diagonalGateEquiv (DiagPhase.realPhase
        (cgkAssemble (Multiplicative.toAdd (Multiplicative.ofAdd c))))) = U
  rw [show Multiplicative.toAdd (Multiplicative.ofAdd c) = c from rfl,
    h_assemble, hζ_units]
  exact hU_eq.symm

/-- **CGK Corollaries 1–2 at p = 2, CORRECTED** (`k ≥ 2`): the diagonal
level-`k` group is `U(1) × ∏_{∅ ≠ S, |S| ≤ k} ℤ/2^(k−|S|+1)`. The
`n = 1` instance is their Corollary 1; the general statement REPLACES
their printed Corollary 2, whose exponent contradicts Corollary 1. -/
noncomputable def cgkDiagonalParametrization {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    (Circle × Multiplicative (CGKComponents n k))
      ≃* ↥(diagonalDyadicSubgroup n k hk1) :=
  MulEquiv.ofBijective (cgkParamHom hk1 hk2)
    ⟨cgkParam_injective hk1 hk2, cgkParam_surjective hk1 hk2⟩

/-- **The generating set (CGK Definition 5, corrected)**: circle phases
and single-monomial gates generate the diagonal level-`k` group. -/
theorem cgk_generating_set {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    Subgroup.closure
      (Set.range (fun ζ : Circle => cgkParamFun hk1 hk2 (ζ, 1))
        ∪ Set.range (fun p : (S : CGKIndex n k)
              × ZMod (2 ^ (k - S.val.card + 1)) =>
            cgkParamFun hk1 hk2
              (1, Multiplicative.ofAdd (Pi.single p.1 p.2))))
      = (⊤ : Subgroup ↥(diagonalDyadicSubgroup n k hk1)) := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨ζ, c⟩, rfl⟩ := cgkParam_surjective hk1 hk2 x
  have h_split : ((ζ, c) : Circle × Multiplicative (CGKComponents n k))
      = (ζ, 1) * (1, c) := by
    refine Prod.ext ?_ ?_
    · show ζ = ζ * 1
      rw [mul_one]
    · show c = 1 * c
      rw [one_mul]
  rw [show cgkParamFun hk1 hk2 (ζ, c) = cgkParamHom hk1 hk2 (ζ, c)
    from rfl, h_split, map_mul]
  apply mul_mem
  · exact Subgroup.subset_closure (Or.inl ⟨ζ, rfl⟩)
  · have h_dec : c = ∏ S : CGKIndex n k,
        Multiplicative.ofAdd (Pi.single S (Multiplicative.toAdd c S)) := by
      apply Multiplicative.toAdd.injective
      rw [show Multiplicative.toAdd (∏ S : CGKIndex n k,
          Multiplicative.ofAdd (Pi.single S (Multiplicative.toAdd c S)))
        = ∑ S : CGKIndex n k, Pi.single S (Multiplicative.toAdd c S)
        from rfl]
      exact (Finset.univ_sum_single (Multiplicative.toAdd c)).symm
    rw [show ((1 : Circle), c)
        = MonoidHom.inr Circle (Multiplicative (CGKComponents n k)) c
      from rfl, h_dec, map_prod, map_prod]
    apply prod_mem
    intro S _
    exact Subgroup.subset_closure
      (Or.inr ⟨⟨S, Multiplicative.toAdd c S⟩, rfl⟩)

end FTQCLib.Hilbert

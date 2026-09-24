/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ProjectiveHierarchy
import FTQCLib.Hilbert.CGKReverseStrict

set_option linter.unusedSectionVars false

/-! # Shared utilities for the sharp CGK forward direction

Supporting lemmas for the sharp forward direction of the
Cui–Gottesman–Krishna classification (the two-sided statement lives in
`FTQCLib/Hilbert/CGKTwoSided.lean`):

* `constProject` interaction with multilinearity and `effectiveLevel`
  (the projection only deletes the constant monomial, so both are
  inherited);
* `isDyadicScalar_expUnit_dyadic` — the global phases produced by
  splitting a constant term off a phase polynomial are dyadic scalars;
* `scaleEquiv_expUnit_diagonalGateEquiv` — scaling a diagonal gate by
  `exp(I·θ)` is the diagonal gate of the shifted phase pattern;
* `diagonalGateEquiv_constProject_split` — the constant-split identity:
  every polynomial diagonal gate factors as a dyadic global phase times
  the gate of its constant-free projection;
* `realPhase_shiftBy_diff_int` — the shift-difference of `realPhase P`
  matches `realPhase (shiftBy s P)` modulo `2π·ℤ`, for arbitrary `P`
  (the multilinear-reduction-free form of the bridge used by
  `cgk_forward`);
* `scalarEquiv_iff_eq_scaleEquiv` — `ScalarEquiv` as an equation
  between linear equivalences;
* `boolReduce_coeff_zero` — the multilinear reduction preserves a
  vanishing constant coefficient.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## `constProject`: support, multilinearity, effective level -/

/-- Away from the constant monomial, `constProject` does not change
coefficients. -/
theorem constProject_coeff_of_ne_zero {n m : ℕ} (P : DiagPhase n m)
    {d : Fin n →₀ ℕ} (hd : d ≠ 0) :
    (constProject P).coeff d = P.coeff d := by
  unfold constProject
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C,
    if_neg (fun h => hd h.symm), sub_zero]

/-- The support of `constProject P` is contained in that of `P` (the
projection only deletes the constant monomial). -/
theorem constProject_support_subset {n m : ℕ} (P : DiagPhase n m) :
    (constProject P).support ⊆ P.support := by
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  by_cases h0 : d = 0
  · subst h0
    exact absurd (constProject_coeff_zero P) hd
  · rwa [constProject_coeff_of_ne_zero P h0] at hd

/-- `constProject` preserves multilinearity. -/
theorem constProject_isMultilinear {n m : ℕ} {P : DiagPhase n m}
    (h_mul : DiagPhase.IsMultilinear P) :
    DiagPhase.IsMultilinear (constProject P) :=
  fun d hd k => h_mul d (constProject_support_subset P hd) k

/-- `constProject` does not raise the effective level: the surviving
monomials are unchanged. -/
theorem constProject_effectiveLevel_le {n m : ℕ} (P : DiagPhase n m) :
    DiagPhase.effectiveLevel (constProject P) ≤ DiagPhase.effectiveLevel P := by
  unfold DiagPhase.effectiveLevel
  apply Finset.sup_le
  intro d hd
  have h0 : d ≠ 0 := by
    intro h
    subst h
    exact absurd (constProject_coeff_zero P) (MvPolynomial.mem_support_iff.mp hd)
  rw [constProject_coeff_of_ne_zero P h0]
  exact Finset.le_sup (f := fun d => DiagPhase.effLevelMonom m (P.coeff d) d)
    (constProject_support_subset P hd)

/-! ## Dyadic scalars from `expUnit` -/

/-- The global phase split off a `DiagPhase n m` constant coefficient is
a dyadic scalar, witnessed at precision `m`. -/
theorem isDyadicScalar_expUnit_dyadic {m : ℕ} (c : ZMod (2 ^ m)) :
    IsDyadicScalar (expUnit (Complex.I *
      (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m) : ℝ) : ℂ))) :=
  ⟨m, c, by rw [expUnit_val]⟩

/-! ## Scaling a diagonal gate is a phase shift -/

/-- Scaling a diagonal gate by `exp(I·θ)` produces the diagonal gate of
the pointwise-shifted phase pattern `θ + f`. -/
theorem scaleEquiv_expUnit_diagonalGateEquiv (θ : ℝ)
    (f : (Fin n → ZMod 2) → ℝ) :
    scaleEquiv (expUnit (Complex.I * (θ : ℂ))) (diagonalGateEquiv f)
      = diagonalGateEquiv (fun v => θ + f v) := by
  refine LinearEquiv.toLinearMap_injective ?_
  rw [scaleEquiv_toLinearMap, diagonalGateEquiv_toLinearMap,
    diagonalGateEquiv_toLinearMap]
  apply LinearMap.ext
  intro ψ
  funext v
  change ((expUnit (Complex.I * (θ : ℂ)) : ℂˣ) : ℂ)
        * (diagonalGate f ψ v)
      = diagonalGate (fun v => θ + f v) ψ v
  rw [diagonalGate_apply, diagonalGate_apply, expUnit_val, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## The constant-split identity -/

/-- **The constant-split identity.** Every polynomial diagonal gate
factors as the dyadic global phase of its constant coefficient times
the diagonal gate of its constant-free projection:
`D_{realPhase P} = exp(I·2π·(P.coeff 0).val/2^m) • D_{realPhase (constProject P)}`. -/
theorem diagonalGateEquiv_constProject_split {n m : ℕ} (P : DiagPhase n m) :
    diagonalGateEquiv (DiagPhase.realPhase P)
      = scaleEquiv
          (expUnit (Complex.I *
            (((2 * Real.pi * ((P.coeff 0).val : ℝ) / (2 : ℝ) ^ m) : ℝ) : ℂ)))
          (diagonalGateEquiv (DiagPhase.realPhase (constProject P))) := by
  rw [scaleEquiv_expUnit_diagonalGateEquiv]
  apply diagonalGateEquiv_eq_of_diff_two_pi
  intro v
  obtain ⟨J, hJ⟩ := realPhase_constProject_diff P v
  refine ⟨-J, ?_⟩
  rw [hJ]
  push_cast
  ring

/-! ## The shift-difference bridge for arbitrary polynomials

`cgk_forward`'s bridge lemma is stated for `boolReduce P`; the proof
only uses `shiftBy_eval_eq`, so it holds for every polynomial. This is
the form the sharp forward induction consumes (its polynomials are
already multilinear, so no reduction is involved). -/

/-- The shift-difference of `realPhase P` matches the `realPhase` of
`shiftBy s P` modulo `2π·ℤ`, for every `P : DiagPhase n m`. -/
theorem realPhase_shiftBy_diff_int {n m : ℕ}
    (P : FTQCLib.Hierarchy.DiagPhase n m) (s : Fin n → ZMod 2) :
    ∀ v : Fin n → ZMod 2, ∃ kI : ℤ,
      (DiagPhase.realPhase P (v + s) - DiagPhase.realPhase P v)
        - DiagPhase.realPhase (FTQCLib.Hilbert.DiagPhase.shiftBy s P) v
        = 2 * Real.pi * (kI : ℝ) := by
  intro v
  have h_eval :
      (FTQCLib.Hilbert.DiagPhase.shiftBy s P).eval v
        = P.eval (v + s) - P.eval v :=
    FTQCLib.Hilbert.DiagPhase.shiftBy_eval_eq s P v
  set A : ℕ := (P.eval (v + s)).val
  set B : ℕ := (P.eval v).val
  set C : ℕ := ((FTQCLib.Hilbert.DiagPhase.shiftBy s P).eval v).val
  have h_zmod : (((A : ℤ) - (B : ℤ) - (C : ℤ)) : ZMod (2 ^ m)) = 0 := by
    push_cast
    have hA : ((A : ℕ) : ZMod (2 ^ m)) = P.eval (v + s) :=
      ZMod.natCast_zmod_val _
    have hB : ((B : ℕ) : ZMod (2 ^ m)) = P.eval v :=
      ZMod.natCast_zmod_val _
    have hC : ((C : ℕ) : ZMod (2 ^ m))
        = (FTQCLib.Hilbert.DiagPhase.shiftBy s P).eval v :=
      ZMod.natCast_zmod_val _
    rw [hA, hB, hC, h_eval]
    ring
  have h_dvd : ((2 ^ m : ℕ) : ℤ) ∣ ((A : ℤ) - (B : ℤ) - (C : ℤ)) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at h_zmod ⊢
    convert h_zmod using 1
  obtain ⟨kI, hk⟩ := h_dvd
  refine ⟨kI, ?_⟩
  unfold DiagPhase.realPhase
  have hpow_ne : ((2 : ℝ) ^ m : ℝ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk_real : (A : ℝ) - (B : ℝ) - (C : ℝ) = (kI : ℝ) * (2 : ℝ) ^ m := by
    have h_int_eq : ((A : ℤ) - (B : ℤ) - (C : ℤ)) = ((2 ^ m : ℕ) : ℤ) * kI := hk
    have h_real_eq : (A : ℝ) - (B : ℝ) - (C : ℝ) = ((2 : ℝ) ^ m) * (kI : ℝ) := by
      exact_mod_cast h_int_eq
    linarith
  field_simp
  linarith

/-! ## `ScalarEquiv` as an equation -/

/-- `ScalarEquiv U V` holds exactly when `U` is a unit scaling of `V`
as a linear equivalence. -/
theorem scalarEquiv_iff_eq_scaleEquiv
    {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} :
    ScalarEquiv U V ↔ ∃ α : ℂˣ, U = scaleEquiv α V := by
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, LinearEquiv.toLinearMap_injective
      (by rw [scaleEquiv_toLinearMap]; exact hα)⟩
  · rintro ⟨α, rfl⟩
    exact ⟨α, by rw [scaleEquiv_toLinearMap]⟩

/-! ## `boolReduce` preserves a vanishing constant coefficient -/

/-- The multilinear reduction preserves a vanishing constant
coefficient: the only monomial whose shadow is the zero exponent vector
is the constant monomial itself. -/
theorem boolReduce_coeff_zero {n m : ℕ} {P : DiagPhase n m}
    (h : P.coeff 0 = 0) :
    (DiagPhase.boolReduce P).coeff 0 = 0 := by
  unfold DiagPhase.boolReduce
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero ?_
  intro d _
  rw [MvPolynomial.coeff_monomial]
  by_cases hbs : DiagPhase.boolShadow d = 0
  · rw [if_pos hbs]
    have hsupp := DiagPhase.boolShadow_support d
    rw [hbs, Finsupp.support_zero] at hsupp
    have hd0 : d = 0 := Finsupp.support_eq_empty.mp hsupp.symm
    rw [hd0]
    exact h
  · rw [if_neg hbs]

/-! ## The sharp forward base case

A constant-free multilinear polynomial of effective level at most `1`
forces every monomial into the shape `2^(m−1)·X_i`: the diagonal gate
is then EXACTLY the pure-Z Pauli of the support pattern (realPhase is
`π·(parity)` pointwise, with no residual phase). This is the base case
the sharp forward induction bottoms out at — recognizing Z-Paulis where
the unsharp `cgk_forward` only recognized constants. -/

/-- The underlying linear map of `pauliEquiv p` is `pauliOperator p`
(definitional; stated for rewriting). -/
lemma pauliEquiv_toLinearMap_eq (p : Pauli n) :
    (pauliEquiv p).toLinearMap = pauliOperator p :=
  LinearMap.ext fun _ => rfl

/-- Every element of `ZMod (2^0) = ZMod 1` is zero. -/
private lemma zmod_two_pow_zero_eq_zero (c : ZMod (2 ^ 0)) : c = 0 := by
  haveI : NeZero ((2 : ℕ) ^ 0) := ⟨by norm_num⟩
  have hlt := ZMod.val_lt c
  have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
  have hv : c.val = 0 := by omega
  rw [← ZMod.natCast_zmod_val c, hv, Nat.cast_zero]

/-- A nonzero element of `ZMod (2^m)` whose 2-adic valuation is at least
`m − 1` is exactly `2^(m−1)`: its value is a positive multiple of
`2^(m−1)` below `2^m`, and the only such multiple is `2^(m−1)` itself. -/
lemma eq_two_pow_pred_of_twoAdicVal_ge {m : ℕ} {c : ZMod (2 ^ m)}
    (hc : c ≠ 0) (h_val : m - 1 ≤ DiagPhase.twoAdicVal c) :
    c = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have hdvd : 2 ^ (m - 1) ∣ c.val := (DiagPhase.pow_dvd_val_iff hc (m - 1)).mpr h_val
  have hlt : c.val < 2 ^ m := ZMod.val_lt c
  have hval_ne : c.val ≠ 0 := fun h =>
    hc (by rw [← ZMod.natCast_zmod_val c, h, Nat.cast_zero])
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · subst hm0
      have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      omega
    · exact hm
  obtain ⟨t, ht⟩ := hdvd
  have h2m : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have ht2 : t < 2 := by
    by_contra h2
    have h2' : 2 ≤ t := Nat.le_of_not_lt h2
    have hmul : 2 ^ (m - 1) * 2 ≤ 2 ^ (m - 1) * t := Nat.mul_le_mul_left _ h2'
    omega
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at ht
    exact hval_ne ht
  have ht1 : t = 1 := by omega
  have hval : c.val = 2 ^ (m - 1) := by rw [ht, ht1, Nat.mul_one]
  rw [← ZMod.natCast_zmod_val c, hval]

/-- Support normal form at effective level ≤ 1: every monomial of a
constant-free multilinear polynomial with `effectiveLevel ≤ 1` is
`2^(m−1)·X_i` for some `i`. -/
lemma support_form_of_effLevel_le_one {m : ℕ} {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ 1) :
    ∀ d ∈ P.support, (∃ i : Fin n, d = Finsupp.single i 1)
      ∧ P.coeff d = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  intro d hd
  have hc_ne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hd_ne : d ≠ 0 := by
    intro h
    rw [h] at hc_ne
    exact hc_ne h_const
  have h_sup : P.support.sup
      (fun d => DiagPhase.effLevelMonom m (P.coeff d) d) ≤ 1 := h_eff
  have h_mono : DiagPhase.effLevelMonom m (P.coeff d) d ≤ 1 :=
    le_trans (Finset.le_sup
      (f := fun d => DiagPhase.effLevelMonom m (P.coeff d) d) hd) h_sup
  unfold DiagPhase.effLevelMonom at h_mono
  have h_sum_pos : 1 ≤ d.sum (fun _ e => e) := by
    by_contra hcon
    have h0 : d.sum (fun _ e => e) = 0 := by omega
    unfold Finsupp.sum at h0
    apply hd_ne
    ext i
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hi : i ∈ d.support
    · exact Finset.sum_eq_zero_iff.mp h0 i hi
    · exact Finsupp.notMem_support_iff.mp hi
  have h_sum_one : d.sum (fun _ e => e) = 1 := by omega
  have h_vge : m - 1 ≤ DiagPhase.twoAdicVal (P.coeff d) := by omega
  refine ⟨?_, eq_two_pow_pred_of_twoAdicVal_ge hc_ne h_vge⟩
  have h_card_le : d.support.card ≤ d.sum (fun _ e => e) := by
    unfold Finsupp.sum
    calc d.support.card = ∑ _i ∈ d.support, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ d.support, d i :=
          Finset.sum_le_sum (fun i hi =>
            Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  have h_card_pos : 0 < d.support.card :=
    Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr hd_ne)
  have h_card : d.support.card = 1 := by omega
  obtain ⟨i, _hi_ne, hd_eq⟩ := Finsupp.card_support_eq_one.mp h_card
  have hb_sum : (Finsupp.single i (d i)).sum (fun _ e => e) = d i :=
    Finsupp.sum_single_index rfl
  rw [hd_eq] at h_sum_one
  rw [hb_sum] at h_sum_one
  exact ⟨i, by rw [hd_eq, h_sum_one]⟩

/-- The pure-Z Pauli read off the support of a polynomial: `Z_i` is set
exactly when the monomial `X_i` appears. -/
private noncomputable def zPauliOfSupport {m : ℕ} (P : DiagPhase n m) : Pauli n where
  X := 0
  Z := fun i => if Finsupp.single i (1 : ℕ) ∈ P.support then 1 else 0

@[simp] private lemma zPauliOfSupport_X {m : ℕ} (P : DiagPhase n m) :
    (zPauliOfSupport P).X = 0 := rfl

@[simp] private lemma zPauliOfSupport_Z {m : ℕ} (P : DiagPhase n m) (i : Fin n) :
    (zPauliOfSupport P).Z i
      = if Finsupp.single i (1 : ℕ) ∈ P.support then 1 else 0 := rfl

/-- The support of an effective-level-≤-1 constant-free multilinear
polynomial is the image of its `X_i`-index set under `single · 1`. -/
private lemma support_eq_image_of_effLevel_le_one {m : ℕ} {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ 1) :
    P.support = (Finset.univ.filter
        (fun i => Finsupp.single i (1 : ℕ) ∈ P.support)).image
      (fun i => Finsupp.single i (1 : ℕ)) := by
  ext d
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hd
    obtain ⟨⟨i, hi⟩, _⟩ := support_form_of_effLevel_le_one h_const h_eff d hd
    exact ⟨i, by rw [← hi]; exact hd, hi.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact hi

/-- Evaluation in normal form: at every binary input, a constant-free
multilinear polynomial of effective level ≤ 1 evaluates to
`2^(m−1) · (zDot parity count)`, as a natural-number cast. -/
private lemma eval_eq_of_effLevel_le_one {m : ℕ} {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ 1) (v : Fin n → ZMod 2) :
    P.eval v = ((2 ^ (m - 1) * zDotVal (zPauliOfSupport P) v : ℕ)
      : ZMod (2 ^ m)) := by
  classical
  set A : Finset (Fin n) := Finset.univ.filter
    (fun i => Finsupp.single i (1 : ℕ) ∈ P.support) with hA
  have h_zdot : zDotVal (zPauliOfSupport P) v = ∑ i ∈ A, (v i).val := by
    rw [hA, Finset.sum_filter]
    unfold zDotVal
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : Finsupp.single i (1 : ℕ) ∈ P.support
    · simp [hi]
    · simp [hi]
  have h_supp := support_eq_image_of_effLevel_le_one h_const h_eff
  have h_inj : ∀ x ∈ A, ∀ y ∈ A,
      Finsupp.single x (1 : ℕ) = Finsupp.single y (1 : ℕ) → x = y :=
    fun x _ y _ h => Finsupp.single_left_injective (by norm_num) h
  conv_lhs => rw [show P = ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)
    from (MvPolynomial.support_sum_monomial_coeff P).symm]
  unfold DiagPhase.eval
  rw [map_sum, h_supp, ← hA, Finset.sum_image h_inj]
  have h_term : ∀ i ∈ A,
      MvPolynomial.eval (DiagPhase.liftBinary v)
        (MvPolynomial.monomial (Finsupp.single i (1 : ℕ))
          (P.coeff (Finsupp.single i (1 : ℕ))))
      = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) * (((v i).val : ℕ) : ZMod (2 ^ m)) := by
    intro i hi
    have hi_mem : Finsupp.single i (1 : ℕ) ∈ P.support := by
      rw [hA] at hi
      exact (Finset.mem_filter.mp hi).2
    rw [MvPolynomial.eval_monomial,
      (support_form_of_effLevel_le_one h_const h_eff _ hi_mem).2]
    congr 1
    rw [Finsupp.prod_single_index (by rw [pow_zero])]
    rw [pow_one]
    rfl
  rw [Finset.sum_congr rfl h_term, h_zdot]
  push_cast
  rw [Finset.mul_sum]

/-- The real phase of an effective-level-≤-1 constant-free multilinear
polynomial is exactly the pure-Z phase pattern of its support Pauli. -/
private lemma realPhase_eq_of_effLevel_le_one {m : ℕ} {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ 1) (v : Fin n → ZMod 2) :
    DiagPhase.realPhase P v = phasedZPattern (zPauliOfSupport P) v := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  unfold DiagPhase.realPhase phasedZPattern
  rw [eval_eq_of_effLevel_le_one h_const h_eff v, ZMod.val_natCast]
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · -- m = 0: both sides vanish (the support is empty, so the count is 0).
    subst hm0
    have h_supp : P.support = ∅ := by
      ext d
      simp only [MvPolynomial.mem_support_iff, Finset.notMem_empty, iff_false,
        ne_eq, not_not]
      exact zmod_two_pow_zero_eq_zero _
    have h_zdot : zDotVal (zPauliOfSupport P) v = 0 := by
      unfold zDotVal
      apply Finset.sum_eq_zero
      intro i _
      simp [h_supp]
    rw [h_zdot]
    norm_num
  · -- m ≥ 1: 2^(m−1)·K mod 2^m = 2^(m−1)·(K mod 2), then real arithmetic.
    have h2m : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2m, Nat.mul_mod_mul_left]
    have h2mR : ((2 : ℝ)) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2mR]
    have hpow_ne : ((2 : ℝ)) ^ (m - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp

/-- **The base-case structure theorem.** A constant-free multilinear
polynomial of effective level at most `1` realizes EXACTLY a pure-Z
Pauli — no residual phase. -/
theorem diagonalGateEquiv_eq_pauliEquiv_of_effLevel_le_one {m : ℕ}
    {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ 1) :
    ∃ p : Pauli n, p.X = 0 ∧
      diagonalGateEquiv (DiagPhase.realPhase P) = pauliEquiv p := by
  refine ⟨zPauliOfSupport P, rfl, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [show DiagPhase.realPhase P = phasedZPattern (zPauliOfSupport P)
    from funext (realPhase_eq_of_effLevel_le_one h_const h_eff)]
  rw [diagonalGateEquiv_phasedZPattern_eq_pauliOperator _ rfl,
    pauliEquiv_toLinearMap_eq]

/-- **The sharp forward base case**: a constant-free multilinear
polynomial of effective level ≤ 1 gives a diagonal gate at DYADIC
hierarchy level 1. -/
theorem cgk_forward_sharp_base {m : ℕ} {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ 1) :
    IsCliffordHierarchyDyadic 1 (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  obtain ⟨p, _, h_eq⟩ :=
    diagonalGateEquiv_eq_pauliEquiv_of_effLevel_le_one h_const h_eff
  rw [h_eq]
  exact IsCliffordHierarchyDyadic.pauli p

/-! ## The sharp forward induction

The induction clones `cgk_forward_of_strictDrop`'s descent with three
changes that buy the sharp bound: the polynomial is kept multilinear
throughout (no `boolReduce` inside the loop), every descent step splits
the freshly created constant term into a dyadic global phase, and the
recursion bottoms out at the Z-Pauli base case (`cgk_forward_sharp_base`)
instead of constants-only — eliminating the off-by-one of `cgk_forward`.
The conclusion lands in the DYADIC hierarchy: every scalar produced by
the descent is an `expUnit` of a dyadic angle. -/

private theorem cgk_forward_sharp_aux {n m : ℕ} (k' : ℕ) :
    ∀ P : FTQCLib.Hierarchy.DiagPhase n m,
      DiagPhase.IsMultilinear P → P.coeff 0 = 0 →
      DiagPhase.effectiveLevel P ≤ k' + 1 →
      IsCliffordHierarchyDyadic (k' + 1)
        (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  induction k' with
  | zero =>
    intro P _h_mul h_const h_eff
    exact cgk_forward_sharp_base h_const h_eff
  | succ k'' ih =>
    intro P h_mul h_const h_eff
    by_cases h_le1 : DiagPhase.effectiveLevel P ≤ 1
    · exact (cgk_forward_sharp_base h_const h_le1).mono (by omega)
    · have h_eff_pos : 0 < DiagPhase.effectiveLevel P := by omega
      refine .step (fun q => ?_)
      rw [conjEquiv_diagonalGateEquiv_general,
        diagonalGateEquiv_eq_of_diff_two_pi (realPhase_shiftBy_diff_int P q.X),
        diagonalGateEquiv_constProject_split
          (FTQCLib.Hilbert.DiagPhase.shiftBy q.X P)]
      have h_drop : DiagPhase.effectiveLevel
          (FTQCLib.Hilbert.DiagPhase.shiftBy q.X P) ≤ k'' + 1 := by
        by_cases hqX : q.X = 0
        · rw [hqX, FTQCLib.Hilbert.DiagPhase.shiftBy_zero]
          simp [DiagPhase.effectiveLevel_zero]
        · have h_strict := shiftByStrictDrop_general n m P h_mul h_eff_pos q.X hqX
          omega
      have h_ih := ih (constProject (FTQCLib.Hilbert.DiagPhase.shiftBy q.X P))
        (constProject_isMultilinear
          (FTQCLib.Hilbert.DiagPhase.shiftBy_isMultilinear q.X h_mul))
        (constProject_coeff_zero _)
        (le_trans (constProject_effectiveLevel_le _) h_drop)
      exact (h_ih.dyadic_scale (isDyadicScalar_expUnit_dyadic _)).mul_pauli_right q

/-- **The sharp forward direction of Cui–Gottesman–Krishna** (dyadic
form): a constant-free multilinear phase polynomial of effective level
at most `k` gives a diagonal gate at DYADIC hierarchy level `k`, for
every `k ≥ 1`.

This is `cgk_forward` made sharp: at the standard gates the certified
level drops by one (T at `C₃` rather than `C₄`, S at `C₂`, Z at `C₁` —
see the gate suite in `FTQCLib/Hilbert/CGKGateTests.lean`). -/
theorem cgk_forward_sharp {n m : ℕ} (P : FTQCLib.Hierarchy.DiagPhase n m) {k : ℕ}
    (hk : 1 ≤ k)
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0)
    (h_eff : DiagPhase.effectiveLevel P ≤ k) :
    IsCliffordHierarchyDyadic k (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact cgk_forward_sharp_aux k' P h_mul h_const h_eff

/-- The sharp forward direction for an ARBITRARY phase polynomial: the
hypothesis is on the constant-free multilinear normal form
`constProject (boolReduce P)`. Subsumes `cgk_forward` (whose hypothesis
`effectiveLevel (boolReduce P) + 1 ≤ k` is strictly stronger) and lands
in the dyadic hierarchy besides. -/
theorem cgk_forward_sharp' {n m : ℕ} (P : FTQCLib.Hierarchy.DiagPhase n m) {k : ℕ}
    (hk : 1 ≤ k)
    (h_eff : DiagPhase.effectiveLevel
      (constProject (DiagPhase.boolReduce P)) ≤ k) :
    IsCliffordHierarchyDyadic k (diagonalGateEquiv (DiagPhase.realPhase P)) := by
  rw [diagonalGateEquiv_realPhase_boolReduce,
    diagonalGateEquiv_constProject_split (DiagPhase.boolReduce P)]
  exact (cgk_forward_sharp (constProject (DiagPhase.boolReduce P)) hk
      (constProject_isMultilinear (boolReduce_isMultilinear P))
      (constProject_coeff_zero _) h_eff).dyadic_scale
    (isDyadicScalar_expUnit_dyadic _)

/-- The sharp forward direction against the loose operational
hierarchy. -/
theorem cgk_forward_sharp_clifford {n m : ℕ}
    (P : FTQCLib.Hierarchy.DiagPhase n m) {k : ℕ} (hk : 1 ≤ k)
    (h_eff : DiagPhase.effectiveLevel
      (constProject (DiagPhase.boolReduce P)) ≤ k) :
    IsCliffordHierarchy k (diagonalGateEquiv (DiagPhase.realPhase P)) :=
  (cgk_forward_sharp' P hk h_eff).toCliffordHierarchy

/-- Poly-encodability at level `k` puts the gate at DYADIC hierarchy
level `k` (not `k + 1`): the effective level of the constant-free
multilinear normal form is bounded by `P.level`. -/
theorem IsCliffordHierarchyPolyEncodable.toCliffordHierarchyDyadic_sharp
    {n k : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hk : 1 ≤ k)
    (h : IsCliffordHierarchyPolyEncodable k U) :
    IsCliffordHierarchyDyadic k U := by
  obtain ⟨m, P, rfl, h_level⟩ := h
  apply cgk_forward_sharp' P hk
  calc DiagPhase.effectiveLevel (constProject (DiagPhase.boolReduce P))
      ≤ DiagPhase.effectiveLevel (DiagPhase.boolReduce P) :=
        constProject_effectiveLevel_le _
    _ ≤ DiagPhase.effectiveLevel P := effectiveLevel_boolReduce_le _
    _ ≤ P.level := DiagPhase.effectiveLevel_le_level P
    _ ≤ k := h_level

/-- **The off-by-one of `IsCliffordHierarchyPolyEncodable.toCliffordHierarchy`
removed**: poly-encodability at level `k` gives loose hierarchy
membership at level `k` itself. This discharges the sharp statement
held in abeyance in `CGKForward.lean`. -/
theorem IsCliffordHierarchyPolyEncodable.toCliffordHierarchy_sharp
    {n k : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hk : 1 ≤ k)
    (h : IsCliffordHierarchyPolyEncodable k U) :
    IsCliffordHierarchy k U :=
  (h.toCliffordHierarchyDyadic_sharp hk).toCliffordHierarchy

end FTQCLib.Hilbert

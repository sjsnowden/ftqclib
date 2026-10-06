/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Codes.AJOGeneral

set_option linter.unusedSectionVars false

/-! # The one-shot precision lift

`liftTo k h P` multiplies a phase polynomial's coefficients by `2^(k−m)`,
preserving the real phase, support, multilinearity, constant-freeness, and
the effective level EXACTLY. No iterated lifts, no index casts.

Frame-pure: rests only on `DiagPhase` (`FTQCLib/Hierarchy/EffectiveLevel.lean`)
and the binary-vector support (`FTQCLib/Codes/AJOGeneral.lean`), with no
dependence on the Hilbert-space layer. Moved out of
`FTQCLib/Hilbert/CGKExactness.lean` so the carrier modules can use it
without importing Hilbert.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Hierarchy

variable {n : ℕ}

/-- The coefficient map of the precision lift: multiply the value by
`2^(k−m)` and read it in `ZMod (2^k)`. (Public: also serves as the
component embedding of the corrected CGK Corollary 2 in
`FTQCLib/Hilbert/CGKGroupStructure.lean`.) -/
def dmapTo (m k : ℕ) (c : ZMod (2 ^ m)) : ZMod (2 ^ k) :=
  ((2 ^ (k - m) * c.val : ℕ) : ZMod (2 ^ k))

lemma dmapTo_zero (m k : ℕ) : dmapTo m k 0 = 0 := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  unfold dmapTo
  rw [ZMod.val_zero, Nat.mul_zero, Nat.cast_zero]

lemma dmapTo_add {m k : ℕ} (h : m ≤ k) (a b : ZMod (2 ^ m)) :
    dmapTo m k (a + b) = dmapTo m k a + dmapTo m k b := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  unfold dmapTo
  rw [ZMod.val_add, ← Nat.cast_add, ← Nat.mul_add]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  have h1 : (a.val + b.val) % 2 ^ m ≡ a.val + b.val [MOD 2 ^ m] :=
    Nat.mod_modEq _ _
  have h2 := Nat.ModEq.mul_left' (c := 2 ^ (k - m)) h1
  have h3 : (2 : ℕ) ^ (k - m) * 2 ^ m = 2 ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rwa [h3] at h2

/-- The lift's coefficient map, bundled (for `map_sum`). -/
def dmapHom {m k : ℕ} (h : m ≤ k) : ZMod (2 ^ m) →+ ZMod (2 ^ k) :=
  AddMonoidHom.mk' (dmapTo m k) (dmapTo_add h)

lemma dmapTo_val {m k : ℕ} (h : m ≤ k) (c : ZMod (2 ^ m)) :
    (dmapTo m k c).val = 2 ^ (k - m) * c.val := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  unfold dmapTo
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have h3 : (2 : ℕ) ^ (k - m) * 2 ^ m = 2 ^ k := by
    rw [← pow_add]
    congr 1
    omega
  calc 2 ^ (k - m) * c.val < 2 ^ (k - m) * 2 ^ m := by
        exact mul_lt_mul_of_pos_left (ZMod.val_lt c) (by positivity)
    _ = 2 ^ k := h3

lemma dmapTo_eq_zero_iff {m k : ℕ} (h : m ≤ k) (c : ZMod (2 ^ m)) :
    dmapTo m k c = 0 ↔ c = 0 := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  constructor
  · intro h0
    have hv : (dmapTo m k c).val = 0 := by rw [h0, ZMod.val_zero]
    rw [dmapTo_val h] at hv
    have hpow : (0 : ℕ) < 2 ^ (k - m) := by positivity
    have hc : c.val = 0 := by
      rcases Nat.mul_eq_zero.mp hv with h' | h'
      · omega
      · exact h'
    rw [← ZMod.natCast_zmod_val c, hc, Nat.cast_zero]
  · intro h0
    rw [h0]
    exact dmapTo_zero m k

/-- The precision lift `DiagPhase n m → DiagPhase n k` (for `m ≤ k`):
multiply every coefficient by `2^(k−m)`. -/
noncomputable def liftTo {n m : ℕ} (k : ℕ) (_h : m ≤ k)
    (P : DiagPhase n m) : DiagPhase n k :=
  ∑ d ∈ P.support, MvPolynomial.monomial d (dmapTo m k (P.coeff d))

lemma liftTo_coeff {n m : ℕ} (k : ℕ) (h : m ≤ k) (P : DiagPhase n m)
    (d : Fin n →₀ ℕ) :
    (liftTo k h P).coeff d = dmapTo m k (P.coeff d) := by
  classical
  unfold liftTo
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ P.support
  · rw [Finset.sum_eq_single d
      (fun e _ hne => by rw [MvPolynomial.coeff_monomial, if_neg hne])
      (fun habs => absurd hd habs)]
    rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · have hc : P.coeff d = 0 := not_ne_iff.mp
      (fun hne => hd (MvPolynomial.mem_support_iff.mpr hne))
    rw [hc, dmapTo_zero]
    apply Finset.sum_eq_zero
    intro e he
    rw [MvPolynomial.coeff_monomial]
    by_cases hde : e = d
    · subst hde
      exact absurd he hd
    · rw [if_neg hde]

lemma liftTo_support {n m : ℕ} (k : ℕ) (h : m ≤ k) (P : DiagPhase n m) :
    (liftTo k h P).support = P.support := by
  ext d
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff,
    liftTo_coeff k h P d]
  constructor
  · intro hne h0
    exact hne (by rw [h0, dmapTo_zero])
  · intro hne h0
    exact hne ((dmapTo_eq_zero_iff h _).mp h0)

lemma liftTo_isMultilinear {n m : ℕ} (k : ℕ) (h : m ≤ k)
    {P : DiagPhase n m} (h_mul : DiagPhase.IsMultilinear P) :
    DiagPhase.IsMultilinear (liftTo k h P) := by
  intro d hd j
  rw [liftTo_support k h P] at hd
  exact h_mul d hd j

lemma liftTo_coeff_zero {n m : ℕ} (k : ℕ) (h : m ≤ k)
    {P : DiagPhase n m} (h_const : P.coeff 0 = 0) :
    (liftTo k h P).coeff 0 = 0 := by
  rw [liftTo_coeff k h P 0, h_const, dmapTo_zero]

/-- The lift's evaluation: multiply the value by `2^(k−m)` (as a
`dmapTo`-image). -/
lemma liftTo_eval {n m : ℕ} (k : ℕ) (h : m ≤ k) (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    (liftTo k h P).eval v = dmapTo m k (P.eval v) := by
  classical
  -- A product of binary values `(liftBinary v i)^e` over an exponent vector
  -- is the indicator of support containment. No multilinearity hypothesis:
  -- binary values are idempotent under positive powers.
  --
  -- (Local restatement of the identically-proved fact used by
  -- `multilinear_eval_injective` et al. in `FTQCLib/Hilbert/CGKExactness.lean`;
  -- kept as a `have`, not a top-level declaration, so this module's
  -- declaration set does not gain an entry beyond the moved 18.)
  have hprod : ∀ {m' : ℕ} (d : Fin n →₀ ℕ),
      (d.prod fun i e => (DiagPhase.liftBinary (m := m') v) i ^ e)
        = if d.support ⊆ FTQCLib.Codes.supp v then 1 else 0 := by
    intro m' d
    unfold Finsupp.prod
    by_cases hsub : d.support ⊆ FTQCLib.Codes.supp v
    · rw [if_pos hsub]
      apply Finset.prod_eq_one
      intro i hi
      have hiv : v i = 1 := (Finset.mem_filter.mp (hsub hi)).2
      have h1 : DiagPhase.liftBinary (m := m') v i = 1 := by
        unfold DiagPhase.liftBinary
        rw [hiv, show ((1 : ZMod 2)).val = 1 from rfl, Nat.cast_one]
      show DiagPhase.liftBinary (m := m') v i ^ d i = 1
      rw [h1, one_pow]
    · rw [if_neg hsub]
      obtain ⟨i, hi_mem, hi_not⟩ := Finset.not_subset.mp hsub
      apply Finset.prod_eq_zero hi_mem
      have hvi0 : v i = 0 := by
        have hne : ¬ v i = 1 := fun h1 =>
          hi_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
        haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
        have hval := ZMod.val_lt (v i)
        have hne_val : (v i).val ≠ 1 := fun h =>
          hne (by rw [← ZMod.natCast_zmod_val (v i), h, Nat.cast_one])
        have h0 : (v i).val = 0 := by omega
        rw [← ZMod.natCast_zmod_val (v i), h0, Nat.cast_zero]
      have h0 : DiagPhase.liftBinary (m := m') v i = 0 := by
        unfold DiagPhase.liftBinary
        rw [hvi0, show ((0 : ZMod 2)).val = 0 from rfl, Nat.cast_zero]
      show DiagPhase.liftBinary (m := m') v i ^ d i = 0
      rw [h0]
      exact zero_pow (Finsupp.mem_support_iff.mp hi_mem)
  have hform : ∀ (M : ℕ) (cc : (Fin n →₀ ℕ) → ZMod (2 ^ M)),
      MvPolynomial.eval (DiagPhase.liftBinary v)
          (∑ d ∈ P.support, MvPolynomial.monomial d (cc d))
        = ∑ d ∈ P.support,
            (if d.support ⊆ FTQCLib.Codes.supp v then cc d else 0) := by
    intro M cc
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [MvPolynomial.eval_monomial, hprod]
    by_cases hd : d.support ⊆ FTQCLib.Codes.supp v
    · rw [if_pos hd, if_pos hd, mul_one]
    · rw [if_neg hd, if_neg hd, mul_zero]
  unfold liftTo DiagPhase.eval
  rw [hform k (fun d => dmapTo m k (P.coeff d))]
  conv_rhs => rw [show P = ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)
    from (MvPolynomial.support_sum_monomial_coeff P).symm]
  rw [hform m (fun d => P.coeff d)]
  rw [show dmapTo m k (∑ d ∈ P.support,
        if d.support ⊆ FTQCLib.Codes.supp v then P.coeff d else 0)
      = ∑ d ∈ P.support, dmapTo m k
          (if d.support ⊆ FTQCLib.Codes.supp v then P.coeff d else 0)
    from map_sum (dmapHom h) _ _]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d.support ⊆ FTQCLib.Codes.supp v
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd, dmapTo_zero]

/-- The lift preserves the real phase EXACTLY. -/
lemma liftTo_realPhase {n m : ℕ} (k : ℕ) (h : m ≤ k) (P : DiagPhase n m) :
    DiagPhase.realPhase (liftTo k h P) = DiagPhase.realPhase P := by
  funext v
  unfold DiagPhase.realPhase
  rw [liftTo_eval k h P v, dmapTo_val h]
  have h3 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - m) * (2 : ℝ) ^ m := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k - m) := by positivity
  have hpos' : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [h3]
  push_cast
  field_simp

/-- The lift shifts the 2-adic valuation of a nonzero coefficient by
exactly `k − m`. -/
private lemma twoAdicVal_dmapTo {m k : ℕ} (h : m ≤ k) {c : ZMod (2 ^ m)}
    (hc : c ≠ 0) :
    DiagPhase.twoAdicVal (dmapTo m k c) = (k - m) + DiagPhase.twoAdicVal c := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have hc' : dmapTo m k c ≠ 0 := fun h0 => hc ((dmapTo_eq_zero_iff h c).mp h0)
  have hval_ne : c.val ≠ 0 := fun h0 =>
    hc (by rw [← ZMod.natCast_zmod_val c, h0, Nat.cast_zero])
  rw [DiagPhase.twoAdicVal_of_ne_zero hc', DiagPhase.twoAdicVal_of_ne_zero hc,
    dmapTo_val h]
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hval_ne]
  simp [Nat.prime_two]

/-- The lift preserves the effective level EXACTLY. -/
lemma liftTo_effectiveLevel {n m : ℕ} (k : ℕ) (h : m ≤ k)
    (P : DiagPhase n m) :
    DiagPhase.effectiveLevel (liftTo k h P) = DiagPhase.effectiveLevel P := by
  unfold DiagPhase.effectiveLevel
  rw [liftTo_support k h P]
  apply Finset.sup_congr rfl
  intro d hd
  rw [liftTo_coeff k h P d]
  have hc : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  unfold DiagPhase.effLevelMonom
  rw [twoAdicVal_dmapTo h hc]
  have hv := DiagPhase.twoAdicVal_lt_of_ne_zero hc
  omega

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKGateTests

set_option linter.unusedSectionVars false

/-! # Exactness of the CGK levels: witness uniqueness and the precision lift

The two-sided classification (`FTQCLib/Hilbert/CGKTwoSided.lean`) characterizes
MEMBERSHIP at each level. This file supplies the exactness layer that turns
the iff family into CGK's exact level assignments (their Theorems 2–3 at
`p = 2`):

* **uniqueness core** — a multilinear polynomial over `ZMod (2^m)` is
  determined by its values on binary inputs (`multilinear_eval_injective`);
  the engine is the zeta transform: evaluating at the indicator of a set `T`
  sums the coefficients of monomials supported inside `T`, so a
  least-support monomial of a nonzero polynomial survives alone;
* **gate → values bridge** — equal diagonal gates up to a global unit force
  the unit to `1` (constant-free phases vanish at the zero input) and the
  phases to agree EXACTLY (both lie in `[0, 2π)`), giving the
  cross-precision value identity `(Q.eval v).val · 2^{m₁} =
  (P.eval v).val · 2^{m₂}`;
* **one-shot precision lift** — `liftTo k h P` multiplies coefficients by
  `2^(k−m)`, preserving the real phase, support, multilinearity,
  constant-freeness, and the effective level EXACTLY. No iterated lifts, no
  index casts.

The pointed exactness theorem `cgk_exact_level` and the exact gate levels
build on these in the later sections of this file.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase
open FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ}

/-! ## §1 The uniqueness core -/

/-- A product of binary values `(liftBinary v i)^e` over an exponent vector
is the indicator of support containment. No multilinearity hypothesis:
binary values are idempotent under positive powers. -/
private lemma prod_liftBinary_pow_eq_ite {m : ℕ} (d : Fin n →₀ ℕ)
    (v : Fin n → ZMod 2) :
    (d.prod fun i e => (DiagPhase.liftBinary (m := m) v) i ^ e)
      = if d.support ⊆ FTQCLib.Codes.supp v then 1 else 0 := by
  classical
  unfold Finsupp.prod
  by_cases hsub : d.support ⊆ FTQCLib.Codes.supp v
  · rw [if_pos hsub]
    apply Finset.prod_eq_one
    intro i hi
    have hiv : v i = 1 := (Finset.mem_filter.mp (hsub hi)).2
    have h1 : DiagPhase.liftBinary (m := m) v i = 1 := by
      unfold DiagPhase.liftBinary
      rw [hiv, show ((1 : ZMod 2)).val = 1 from rfl, Nat.cast_one]
    show DiagPhase.liftBinary (m := m) v i ^ d i = 1
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
    have h0 : DiagPhase.liftBinary (m := m) v i = 0 := by
      unfold DiagPhase.liftBinary
      rw [hvi0, show ((0 : ZMod 2)).val = 0 from rfl, Nat.cast_zero]
    show DiagPhase.liftBinary (m := m) v i ^ d i = 0
    rw [h0]
    exact zero_pow (Finsupp.mem_support_iff.mp hi_mem)

/-- Evaluating at the indicator of `T` sums the coefficients of monomials
supported inside `T` (the zeta transform of the coefficient function). -/
private lemma eval_charFn_eq_subset_sum {m : ℕ} (P : DiagPhase n m)
    (T : Finset (Fin n)) :
    P.eval (charFn T)
      = ∑ d ∈ P.support.filter (fun d => d.support ⊆ T), P.coeff d := by
  classical
  conv_lhs => rw [show P = ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)
    from (MvPolynomial.support_sum_monomial_coeff P).symm]
  unfold DiagPhase.eval
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  rw [MvPolynomial.eval_monomial, prod_liftBinary_pow_eq_ite, supp_charFn]
  by_cases h : d.support ⊆ T
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Two exponent vectors with entries ≤ 1 and equal support are equal. -/
private lemma multilinear_eq_of_support_eq {d e : Fin n →₀ ℕ}
    (hd : ∀ k, d k ≤ 1) (he : ∀ k, e k ≤ 1)
    (h : d.support = e.support) : d = e := by
  ext i
  by_cases hi : i ∈ d.support
  · have hi' : i ∈ e.support := h ▸ hi
    have h1 := Finsupp.mem_support_iff.mp hi
    have h2 := Finsupp.mem_support_iff.mp hi'
    have := hd i
    have := he i
    omega
  · have hi' : i ∉ e.support := h ▸ hi
    rw [Finsupp.notMem_support_iff.mp hi, Finsupp.notMem_support_iff.mp hi']

private lemma isMultilinear_sub' {m : ℕ} {P Q : DiagPhase n m}
    (hP : DiagPhase.IsMultilinear P) (hQ : DiagPhase.IsMultilinear Q) :
    DiagPhase.IsMultilinear (P - Q) := by
  intro d hd k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ P Q hd) with h | h
  · exact hP d h k
  · exact hQ d h k

/-- A multilinear polynomial vanishing at every binary input is zero: a
least-support monomial survives alone in the evaluation at its own support
indicator. -/
private lemma multilinear_eval_zero_eq_zero {m : ℕ} {P : DiagPhase n m}
    (h_mul : DiagPhase.IsMultilinear P)
    (h_eval : ∀ v, P.eval v = 0) : P = 0 := by
  classical
  by_contra hP
  have h_ne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hP (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨d₀, hd₀_mem, hd₀_min⟩ :=
    P.support.exists_min_image (fun d => d.support.card) h_ne
  have h_at := h_eval (charFn d₀.support)
  rw [eval_charFn_eq_subset_sum P d₀.support] at h_at
  have h_filter : P.support.filter (fun d => d.support ⊆ d₀.support) = {d₀} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hd_mem, hd_sub⟩
      exact multilinear_eq_of_support_eq (fun k => h_mul d hd_mem k)
        (fun k => h_mul d₀ hd₀_mem k)
        (Finset.eq_of_subset_of_card_le hd_sub (hd₀_min d hd_mem))
    · rintro rfl
      exact ⟨hd₀_mem, Finset.Subset.refl _⟩
  rw [h_filter, Finset.sum_singleton] at h_at
  exact (MvPolynomial.mem_support_iff.mp hd₀_mem) h_at

/-- **Witness uniqueness at a common precision**: multilinear polynomials
over `ZMod (2^m)` agreeing on every binary input are equal. -/
theorem multilinear_eval_injective {m : ℕ} {P Q : DiagPhase n m}
    (hP : DiagPhase.IsMultilinear P) (hQ : DiagPhase.IsMultilinear Q)
    (h_eval : ∀ v, P.eval v = Q.eval v) : P = Q := by
  have h0 : ∀ v, (P - Q).eval v = 0 := by
    intro v
    unfold DiagPhase.eval
    have hv := h_eval v
    unfold DiagPhase.eval at hv
    rw [map_sub, hv, sub_self]
  exact sub_eq_zero.mp
    (multilinear_eval_zero_eq_zero (isMultilinear_sub' hP hQ) h0)

/-! ## §2 The gate → values bridge -/

/-- A constant-free polynomial has vanishing real phase at the zero input. -/
theorem realPhase_zero_input {m : ℕ} {P : DiagPhase n m}
    (h_const : P.coeff 0 = 0) :
    DiagPhase.realPhase P 0 = 0 := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  unfold DiagPhase.realPhase
  have h_eval : P.eval 0 = 0 := by
    unfold DiagPhase.eval
    have hl : DiagPhase.liftBinary (m := m) (0 : Fin n → ZMod 2)
        = (0 : Fin n → ZMod (2 ^ m)) := by
      funext i
      unfold DiagPhase.liftBinary
      rw [show ((0 : Fin n → ZMod 2) i) = 0 from rfl,
        show ((0 : ZMod 2)).val = 0 from rfl, Nat.cast_zero]
      rfl
    rw [hl, MvPolynomial.eval_zero]
    exact h_const
  rw [h_eval, ZMod.val_zero]
  simp

private lemma realPhase_nonneg {m : ℕ} (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    0 ≤ DiagPhase.realPhase P v := by
  unfold DiagPhase.realPhase
  positivity

private lemma realPhase_lt_two_pi {m : ℕ} (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    DiagPhase.realPhase P v < 2 * Real.pi := by
  haveI : NeZero ((2 : ℕ) ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  unfold DiagPhase.realPhase
  have h_val : ((P.eval v).val : ℝ) < (2 : ℝ) ^ m := by
    exact_mod_cast ZMod.val_lt (P.eval v)
  have h_pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  rw [div_lt_iff₀ h_pos]
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  exact mul_lt_mul_of_pos_left h_val hπ

/-- Scaling by the unit `1` is the identity. -/
lemma scaleEquiv_one (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    scaleEquiv 1 V = V := by
  apply LinearEquiv.toLinearMap_injective
  rw [scaleEquiv_toLinearMap, Units.val_one, one_smul]

/-- **The gate forces the values.** If the diagonal gates of two
constant-free polynomials (any precisions) agree up to a global unit, the
unit is `1` and the evaluation values satisfy the exact cross-precision
identity. -/
theorem eval_val_mul_eq_of_eq_scaleEquiv {m₁ m₂ : ℕ}
    {P : DiagPhase n m₁} {Q : DiagPhase n m₂} {α : ℂˣ}
    (hP : P.coeff 0 = 0) (hQ : Q.coeff 0 = 0)
    (h : diagonalGateEquiv (DiagPhase.realPhase Q)
        = scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)))
    (v : Fin n → ZMod 2) :
    (Q.eval v).val * 2 ^ m₁ = (P.eval v).val * 2 ^ m₂ := by
  haveI : NeZero ((2 : ℕ) ^ m₁) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero ((2 : ℕ) ^ m₂) := ⟨pow_ne_zero _ (by norm_num)⟩
  -- Step 1: the unit is 1 (compare at the zero basis state).
  have h_at0 := congrArg
    (fun L : QubitSpace n ≃ₗ[ℂ] QubitSpace n => L (computational 0)) h
  simp only [scaleEquiv_apply, diagonalGateEquiv_apply,
    diagonalGate_computational] at h_at0
  rw [realPhase_zero_input hQ, realPhase_zero_input hP] at h_at0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at h_at0
  have h_α : (α : ℂˣ) = 1 := by
    have h_eval0 := congrFun h_at0 (0 : Fin n → ZMod 2)
    simp only [Pi.smul_apply, computational_self, smul_eq_mul, mul_one] at h_eval0
    exact Units.ext h_eval0.symm
  -- Step 2: the gates are equal outright.
  rw [h_α, scaleEquiv_one] at h
  -- Step 3: phases agree mod 2π, hence exactly (both in [0, 2π)).
  obtain ⟨kint, hk⟩ := diagonalGateEquiv_eq_pointwise_two_pi h v
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hQ0 := realPhase_nonneg Q v
  have hQ2 := realPhase_lt_two_pi Q v
  have hP0 := realPhase_nonneg P v
  have hP2 := realPhase_lt_two_pi P v
  have hk0 : kint = 0 := by
    have hb1 : (-1 : ℝ) < (kint : ℝ) := by nlinarith
    have hb2 : ((kint : ℝ)) < 1 := by nlinarith
    have h1 : (-1 : ℤ) < kint := by exact_mod_cast hb1
    have h2 : kint < 1 := by exact_mod_cast hb2
    omega
  rw [hk0] at hk
  push_cast at hk
  have h_phase : DiagPhase.realPhase Q v = DiagPhase.realPhase P v := by
    linarith
  -- Step 4: clear denominators.
  unfold DiagPhase.realPhase at h_phase
  have h2m₁ : (0 : ℝ) < (2 : ℝ) ^ m₁ := by positivity
  have h2m₂ : (0 : ℝ) < (2 : ℝ) ^ m₂ := by positivity
  have hπ' : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_real : ((Q.eval v).val : ℝ) * (2 : ℝ) ^ m₁
      = ((P.eval v).val : ℝ) * (2 : ℝ) ^ m₂ := by
    rw [div_eq_div_iff (ne_of_gt h2m₂) (ne_of_gt h2m₁)] at h_phase
    nlinarith
  exact_mod_cast h_real

/-! ## §3 The one-shot precision lift -/

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
  have hform : ∀ (M : ℕ) (cc : (Fin n →₀ ℕ) → ZMod (2 ^ M)),
      MvPolynomial.eval (DiagPhase.liftBinary v)
          (∑ d ∈ P.support, MvPolynomial.monomial d (cc d))
        = ∑ d ∈ P.support,
            (if d.support ⊆ FTQCLib.Codes.supp v then cc d else 0) := by
    intro M cc
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [MvPolynomial.eval_monomial, prod_liftBinary_pow_eq_ite]
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

/-! ## §4 Pointed exactness: CGK Theorems 2–3 completed at p = 2

For the polynomial in hand — not just some witness — membership at level
`k` is EQUIVALENT to `effectiveLevel ≤ k`. The forward direction is
`cgk_forward_sharp`; the reverse extracts the precision-`k` witness from
the classification, matches value tables through the precision lift, and
transports the effective level along the lift. -/

/-- Matching value tables across the lift forces polynomial equality.

Used by the kernel-frame representation theorem (`rt_inj`): the injectivity
of the kernel map reduces (after killing the global scalar at `0`) to this
value-table equality across the precision lift. -/
lemma eq_liftTo_of_val_table {n m k : ℕ} (h : m ≤ k)
    {P : DiagPhase n m} {Q : DiagPhase n k}
    (hP_mul : DiagPhase.IsMultilinear P) (hQ_mul : DiagPhase.IsMultilinear Q)
    (h_vals : ∀ v, 2 ^ (k - m) * (P.eval v).val = (Q.eval v).val) :
    liftTo k h P = Q := by
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  apply multilinear_eval_injective (liftTo_isMultilinear k h hP_mul) hQ_mul
  intro v
  rw [liftTo_eval k h P v]
  have hval : (dmapTo m k (P.eval v)).val = (Q.eval v).val := by
    rw [dmapTo_val h]
    exact h_vals v
  rw [← ZMod.natCast_zmod_val (dmapTo m k (P.eval v)), hval,
    ZMod.natCast_zmod_val]

/-- Composition of scalings. -/
lemma scaleEquiv_scaleEquiv (α β : ℂˣ) (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    scaleEquiv α (scaleEquiv β V) = scaleEquiv (α * β) V := by
  apply LinearEquiv.toLinearMap_injective
  rw [scaleEquiv_toLinearMap, scaleEquiv_toLinearMap, scaleEquiv_toLinearMap,
    smul_smul, Units.val_mul]

/-- **Pointed exactness (CGK Theorems 2–3, p = 2).** For a constant-free
multilinear phase polynomial, hierarchy membership at level `k ≥ 1` is
EQUIVALENT to `effectiveLevel ≤ k`. -/
theorem cgk_exact_level {n m : ℕ} {P : DiagPhase n m} {k : ℕ} (hk : 1 ≤ k)
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0) :
    IsCliffordHierarchyDyadic k (diagonalGateEquiv (DiagPhase.realPhase P))
      ↔ DiagPhase.effectiveLevel P ≤ k := by
  constructor
  · intro h
    obtain ⟨α, Q, hQ_mul, hQ_c0, hQ_eff, hQ_eq⟩ :=
      cgk_diagonal_classify hk _ ⟨_, rfl⟩ h
    have h_vals := eval_val_mul_eq_of_eq_scaleEquiv hQ_c0 h_const hQ_eq
    -- h_vals v : (P.eval v).val * 2^k = (Q.eval v).val * 2^m
    by_cases hmk : m ≤ k
    · -- lift P to precision k; it must BE the witness.
      have h_table : ∀ v, 2 ^ (k - m) * (P.eval v).val = (Q.eval v).val := by
        intro v
        have h2 : (2 : ℕ) ^ k = 2 ^ (k - m) * 2 ^ m := by
          rw [← pow_add]
          congr 1
          omega
        have hv' : (P.eval v).val * (2 ^ (k - m) * 2 ^ m)
            = (Q.eval v).val * 2 ^ m := by
          rw [← h2]
          exact h_vals v
        rw [← Nat.mul_assoc] at hv'
        have h_eq := Nat.eq_of_mul_eq_mul_right
          (by positivity : (0 : ℕ) < 2 ^ m) hv'
        rw [Nat.mul_comm]
        exact h_eq
      have h_eq := eq_liftTo_of_val_table hmk h_mul hQ_mul h_table
      calc DiagPhase.effectiveLevel P
          = DiagPhase.effectiveLevel (liftTo k hmk P) :=
            (liftTo_effectiveLevel k hmk P).symm
        _ = DiagPhase.effectiveLevel Q := by rw [h_eq]
        _ ≤ k := hQ_eff
    · -- lift the witness to precision m; it must BE P.
      have hkm : k ≤ m := by omega
      have h_table : ∀ v, 2 ^ (m - k) * (Q.eval v).val = (P.eval v).val := by
        intro v
        have h2 : (2 : ℕ) ^ m = 2 ^ (m - k) * 2 ^ k := by
          rw [← pow_add]
          congr 1
          omega
        have hv' : (P.eval v).val * 2 ^ k
            = (Q.eval v).val * (2 ^ (m - k) * 2 ^ k) := by
          rw [← h2]
          exact h_vals v
        rw [← Nat.mul_assoc] at hv'
        have h_eq := Nat.eq_of_mul_eq_mul_right
          (by positivity : (0 : ℕ) < 2 ^ k) hv'
        rw [Nat.mul_comm]
        exact h_eq.symm
      have h_eq := eq_liftTo_of_val_table hkm hQ_mul h_mul h_table
      calc DiagPhase.effectiveLevel P
          = DiagPhase.effectiveLevel (liftTo m hkm Q) := by rw [h_eq]
        _ = DiagPhase.effectiveLevel Q := liftTo_effectiveLevel m hkm Q
        _ ≤ k := hQ_eff
  · intro h_eff
    exact cgk_forward_sharp P hk h_mul h_const h_eff

/-- Pointed exactness with a free global phase (`k ≥ 2`). -/
theorem cgk_exact_level_scaled {n m : ℕ} {P : DiagPhase n m} {k : ℕ}
    (hk : 2 ≤ k) (α : ℂˣ)
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0) :
    IsCliffordHierarchyDyadic k
        (scaleEquiv α (diagonalGateEquiv (DiagPhase.realPhase P)))
      ↔ DiagPhase.effectiveLevel P ≤ k := by
  constructor
  · intro h
    have h' := IsCliffordHierarchyDyadic.scale_of_two_le hk α⁻¹ h
    rw [scaleEquiv_scaleEquiv, inv_mul_cancel, scaleEquiv_one] at h'
    exact (cgk_exact_level (by omega) h_mul h_const).mp h'
  · intro h_eff
    exact cgk_diagonal_construct_of_two_le hk α h_mul h_const h_eff

/-- Pointed exactness against the PLAIN hierarchy (`k ≥ 2`). -/
theorem cgk_exact_level_clifford {n m : ℕ} {P : DiagPhase n m} {k : ℕ}
    (hk : 2 ≤ k)
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0) :
    IsCliffordHierarchy k (diagonalGateEquiv (DiagPhase.realPhase P))
      ↔ DiagPhase.effectiveLevel P ≤ k := by
  rw [isCliffordHierarchy_iff_dyadic_of_two_le hk]
  exact cgk_exact_level (by omega) h_mul h_const

/-! ## §5 Exact gate levels

The pointed exactness theorem instantiated at the standard gates: each
membership iff pins the EXACT level (Z = 1, S = 2, T = 3, CS = 3,
CCZ = 3), upgrading the membership-only guards of
`FTQCLib/Hilbert/CGKGateTests.lean`. -/

private lemma not_dyadic_zero {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} :
    ¬ IsCliffordHierarchyDyadic 0 U := by
  intro h
  cases h

private lemma isMultilinear_monomial {m : ℕ} {d : Fin n →₀ ℕ}
    (c : ZMod (2 ^ m)) (hd : ∀ j, d j ≤ 1) :
    DiagPhase.IsMultilinear (MvPolynomial.monomial d c) := by
  intro e he j
  have h := MvPolynomial.support_monomial_subset he
  rw [Finset.mem_singleton] at h
  subst h
  exact hd j

private lemma coeff_zero_monomial_of_ne {m : ℕ} {d : Fin n →₀ ℕ}
    (c : ZMod (2 ^ m)) (hd : d ≠ 0) :
    (MvPolynomial.monomial d c : DiagPhase n m).coeff 0 = 0 := by
  rw [MvPolynomial.coeff_monomial, if_neg hd]

private lemma effLevel_monomial_one {m : ℕ} (d : Fin n →₀ ℕ)
    (h1 : (1 : ZMod (2 ^ m)) ≠ 0) (hval : (1 : ZMod (2 ^ m)).val = 1) :
    DiagPhase.effectiveLevel (MvPolynomial.monomial d (1 : ZMod (2 ^ m)))
      = (m - 1) + d.sum (fun _ e => e) := by
  rw [DiagPhase.effectiveLevel_monomial_eq h1]
  unfold DiagPhase.effLevelMonom
  rw [twoAdicVal_one_eq_zero h1 hval, Nat.sub_zero]

private lemma single_entries_le (i : Fin n) :
    ∀ j, (Finsupp.single i (1 : ℕ)) j ≤ 1 := by
  intro j
  rw [Finsupp.single_apply]
  split_ifs <;> omega

private lemma single_sum' (i : Fin n) :
    (Finsupp.single i (1 : ℕ)).sum (fun _ e => e) = 1 :=
  Finsupp.sum_single_index rfl

private lemma pair_entries_le {i j : Fin n} (hij : i ≠ j) :
    ∀ l, (Finsupp.single i (1 : ℕ) + Finsupp.single j 1 : Fin n →₀ ℕ) l ≤ 1 := by
  intro l
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h1 : i = l <;> by_cases h2 : j = l
  · exact absurd (h1.trans h2.symm) hij
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

private lemma pair_ne_zero {i j : Fin n} (hij : i ≠ j) :
    Finsupp.single i (1 : ℕ) + Finsupp.single j 1 ≠ 0 := by
  intro h0
  have h := congrArg (fun d : Fin n →₀ ℕ => d i) h0
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [Finsupp.single_apply, if_pos rfl, Finsupp.single_apply,
    if_neg (fun hji => hij hji.symm)] at h
  omega

private lemma pair_sum {i j : Fin n} :
    (Finsupp.single i (1 : ℕ) + Finsupp.single j 1).sum (fun _ e => e) = 2 := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

private lemma triple_entries_le {i j l : Fin n}
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ∀ w, (Finsupp.single i (1 : ℕ) + Finsupp.single j 1
      + Finsupp.single l 1 : Fin n →₀ ℕ) w ≤ 1 := by
  intro w
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  by_cases h1 : i = w <;> by_cases h2 : j = w <;> by_cases h3 : l = w
  · exact absurd (h1.trans h2.symm) hij
  · exact absurd (h1.trans h2.symm) hij
  · exact absurd (h1.trans h3.symm) hil
  · simp [h1, h2, h3]
  · exact absurd (h2.trans h3.symm) hjl
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]
  · simp [h1, h2, h3]

private lemma triple_ne_zero {i j l : Fin n}
    (hij : i ≠ j) (hil : i ≠ l) :
    Finsupp.single i (1 : ℕ) + Finsupp.single j 1 + Finsupp.single l 1 ≠ 0 := by
  intro h0
  have h := congrArg (fun d : Fin n →₀ ℕ => d i) h0
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h
  rw [Finsupp.single_apply, if_pos rfl, Finsupp.single_apply,
    if_neg (fun hji => hij hji.symm), Finsupp.single_apply,
    if_neg (fun hli => hil hli.symm)] at h
  omega

private lemma triple_sum {i j l : Fin n} :
    (Finsupp.single i (1 : ℕ) + Finsupp.single j 1
      + Finsupp.single l 1).sum (fun _ e => e) = 3 := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl,
    Finsupp.sum_single_index rfl]

private lemma csPoly_eq_monomial (i j : Fin n) :
    csPoly i j = MvPolynomial.monomial
      (Finsupp.single i 1 + Finsupp.single j 1) (1 : ZMod (2 ^ 2)) := by
  unfold csPoly
  rw [X_eq_monomial, X_eq_monomial, MvPolynomial.monomial_mul, one_mul]

private lemma cczPoly_eq_monomial (i j l : Fin n) :
    cczPoly i j l = MvPolynomial.monomial
      (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single l 1)
      (1 : ZMod (2 ^ 1)) := by
  unfold cczPoly
  rw [X_eq_monomial, X_eq_monomial, X_eq_monomial,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, one_mul, one_mul]

/-- The Z gate's EXACT level: member of level `k` iff `1 ≤ k`. -/
theorem zGate_exact_level (i : Fin n) (k : ℕ) :
    IsCliffordHierarchyDyadic k
        (diagonalGateEquiv (DiagPhase.realPhase (rzGatePoly i 1)))
      ↔ 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact iff_of_false not_dyadic_zero (by omega)
  · rw [show rzGatePoly i 1
        = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 1))
      from X_eq_monomial i]
    rw [cgk_exact_level hk
      (isMultilinear_monomial _ (single_entries_le i))
      (coeff_zero_monomial_of_ne _ (Finsupp.single_ne_zero.mpr one_ne_zero)),
      effLevel_monomial_one _ (by decide) (by decide), single_sum']

/-- The S gate's EXACT level: member of level `k` iff `2 ≤ k`. -/
theorem sGate_exact_level (i : Fin n) (k : ℕ) :
    IsCliffordHierarchyDyadic k
        (diagonalGateEquiv (DiagPhase.realPhase (rzGatePoly i 2)))
      ↔ 2 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact iff_of_false not_dyadic_zero (by omega)
  · rw [show rzGatePoly i 2
        = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 2))
      from X_eq_monomial i]
    rw [cgk_exact_level hk
      (isMultilinear_monomial _ (single_entries_le i))
      (coeff_zero_monomial_of_ne _ (Finsupp.single_ne_zero.mpr one_ne_zero)),
      effLevel_monomial_one _ (by decide) (by decide), single_sum']

/-- The T gate's EXACT level: member of level `k` iff `3 ≤ k`. -/
theorem tGate_exact_level (i : Fin n) (k : ℕ) :
    IsCliffordHierarchyDyadic k
        (diagonalGateEquiv (DiagPhase.realPhase (tGatePoly i)))
      ↔ 3 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact iff_of_false not_dyadic_zero (by omega)
  · rw [show tGatePoly i
        = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 3))
      from X_eq_monomial i]
    rw [cgk_exact_level hk
      (isMultilinear_monomial _ (single_entries_le i))
      (coeff_zero_monomial_of_ne _ (Finsupp.single_ne_zero.mpr one_ne_zero)),
      effLevel_monomial_one _ (by decide) (by decide), single_sum']

/-- The CS gate's EXACT level: member of level `k` iff `3 ≤ k`. -/
theorem csGate_exact_level (i j : Fin n) (hij : i ≠ j) (k : ℕ) :
    IsCliffordHierarchyDyadic k
        (diagonalGateEquiv (DiagPhase.realPhase (csPoly i j)))
      ↔ 3 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact iff_of_false not_dyadic_zero (by omega)
  · rw [csPoly_eq_monomial i j]
    rw [cgk_exact_level hk
      (isMultilinear_monomial _ (pair_entries_le hij))
      (coeff_zero_monomial_of_ne _ (pair_ne_zero hij)),
      effLevel_monomial_one _ (by decide) (by decide), pair_sum]

/-- The CCZ gate's EXACT level: member of level `k` iff `3 ≤ k`. -/
theorem cczGate_exact_level (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (k : ℕ) :
    IsCliffordHierarchyDyadic k
        (diagonalGateEquiv (DiagPhase.realPhase (cczPoly i j l)))
      ↔ 3 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact iff_of_false not_dyadic_zero (by omega)
  · rw [cczPoly_eq_monomial i j l]
    rw [cgk_exact_level hk
      (isMultilinear_monomial _ (triple_entries_le hij hjl hil))
      (coeff_zero_monomial_of_ne _ (triple_ne_zero hij hil)),
      effLevel_monomial_one _ (by decide) (by decide), triple_sum]

/-! ### Strictness corollaries -/

/-- T is NOT at dyadic level 2. -/
theorem tGate_not_mem_dyadic_two (i : Fin n) :
    ¬ IsCliffordHierarchyDyadic 2
      (diagonalGateEquiv (DiagPhase.realPhase (tGatePoly i))) := by
  rw [tGate_exact_level i 2]
  omega

/-- S is NOT at dyadic level 1. -/
theorem sGate_not_mem_dyadic_one (i : Fin n) :
    ¬ IsCliffordHierarchyDyadic 1
      (diagonalGateEquiv (DiagPhase.realPhase (rzGatePoly i 2))) := by
  rw [sGate_exact_level i 1]
  omega

/-- CS is NOT at dyadic level 2. -/
theorem csGate_not_mem_dyadic_two (i j : Fin n) (hij : i ≠ j) :
    ¬ IsCliffordHierarchyDyadic 2
      (diagonalGateEquiv (DiagPhase.realPhase (csPoly i j))) := by
  rw [csGate_exact_level i j hij 2]
  omega

/-- CCZ is NOT at dyadic level 2. -/
theorem cczGate_not_mem_dyadic_two (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ¬ IsCliffordHierarchyDyadic 2
      (diagonalGateEquiv (DiagPhase.realPhase (cczPoly i j l))) := by
  rw [cczGate_exact_level i j l hij hjl hil 2]
  omega

/-- T is NOT at PLAIN hierarchy level 2 (so T is not Clifford-squared even
with arbitrary phases). -/
theorem tGate_not_mem_clifford_two (i : Fin n) :
    ¬ IsCliffordHierarchy 2
      (diagonalGateEquiv (DiagPhase.realPhase (tGatePoly i))) := by
  rw [isCliffordHierarchy_iff_dyadic_of_two_le (le_refl 2)]
  exact tGate_not_mem_dyadic_two i

/-- CS is NOT at PLAIN hierarchy level 2. -/
theorem csGate_not_mem_clifford_two (i j : Fin n) (hij : i ≠ j) :
    ¬ IsCliffordHierarchy 2
      (diagonalGateEquiv (DiagPhase.realPhase (csPoly i j))) := by
  rw [isCliffordHierarchy_iff_dyadic_of_two_le (le_refl 2)]
  exact csGate_not_mem_dyadic_two i j hij

/-- CCZ is NOT at PLAIN hierarchy level 2. -/
theorem cczGate_not_mem_clifford_two (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    ¬ IsCliffordHierarchy 2
      (diagonalGateEquiv (DiagPhase.realPhase (cczPoly i j l))) := by
  rw [isCliffordHierarchy_iff_dyadic_of_two_le (le_refl 2)]
  exact cczGate_not_mem_dyadic_two i j l hij hjl hil

end FTQCLib.Hilbert

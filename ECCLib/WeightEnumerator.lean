/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.MacWilliams

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The homogeneous weight enumerator and the weight distribution

`MacWilliams.lean` proves the MacWilliams identity in evaluated single-variable form
(`macwilliams`, `weightEnum C z`). That form cannot express the canonical *transform* — it only
reaches the line `X = 1` — and it never exposes the weight-distribution numbers `Aᵢ`. This file
adds the reusable objects a coding-theory consumer actually builds against:

* **`homWeightEnum C X Y = Σ_{x∈C} X^{n−wt x} Y^{wt x}`** — the two-variable homogeneous enumerator,
  with `homWeightEnum C 1 z = weightEnum C z`;
* **`homMacwilliams`** — the homogeneous MacWilliams transform
  `|C| · homWeightEnum(C^⊥) X Y = homWeightEnum C (X+(q−1)Y) (X−Y)`, valid at *every* `X, Y ∈ ℂ`
  (the `X = 0` line — pure top weight — is unreachable from the single-variable form). Proved as
  weight statistics of the DFT bridge, exactly like `macwilliams`, with a bivariate Krawtchouk sum;
* **`weightPoly C : Polynomial ℂ`** with `eval z = weightEnum C z` and
  `coeff i = Aᵢ = #{x∈C : wt x = i}` (`weightDist`) — so the weight distribution is extractable data
  (what LP bounds, dual-distance, and self-dual arguments consume).
-/

namespace ECCLib.Coding

open ECCLib.Heisenberg

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Bound file-wide, not per-section: `hammingNorm` must elaborate with the SAME `DecidableEq F`
-- in the definitions and in every consumer's rewrite patterns, or `rw` cannot match.
variable [DecidableEq F]

/-! ## The homogeneous (two-variable) weight enumerator -/

open Classical in
/-- The **homogeneous weight enumerator** `W_C(X,Y) = Σ_{x∈C} X^{n−wt x} Y^{wt x}`, homogeneous of
degree `n = |ι|`. -/
noncomputable def homWeightEnum (C : Submodule F (ι → F)) (X Y : ℂ) : ℂ :=
  ∑ x : ι → F, indicator C x * (X ^ (Fintype.card ι - hammingNorm x) * Y ^ hammingNorm x)

open Classical in
/-- `W_C(1, z)` is the single-variable enumerator. -/
theorem homWeightEnum_one (C : Submodule F (ι → F)) (z : ℂ) :
    homWeightEnum C 1 z = weightEnum C z := by
  unfold homWeightEnum weightEnum
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [one_pow, one_mul]

section Bivariate

/-- `∏_i (if y_i = 0 then X else Y) = X^{n−wt y}·Y^{wt y}`. -/
lemma prod_ite_pow (X Y : ℂ) (y : ι → F) :
    (∏ i, if y i = 0 then X else Y)
      = X ^ (Fintype.card ι - hammingNorm y) * Y ^ hammingNorm y := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => y i = 0)
  rw [Finset.card_univ] at hsplit
  have hwt : (Finset.univ.filter (fun i => ¬ y i = 0)).card = hammingNorm y := rfl
  rw [hwt]
  congr 2
  omega

/-- **The bivariate one-dimensional Krawtchouk sum**:
`Σ_t (if t=0 then X else Y)·ψ(ts) = X+(q−1)Y` at `s=0`, `X−Y` otherwise. -/
lemma homKrawtchouk_sum {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (X Y : ℂ) (s : F) :
    ∑ t : F, (if t = 0 then X else Y) * ψ (t * s)
      = if s = 0 then X + ((Fintype.card F : ℂ) - 1) * Y else X - Y := by
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  by_cases hs : s = 0
  · subst hs
    rw [if_pos rfl]
    rw [Finset.sum_congr rfl fun t _ => by rw [mul_zero, AddChar.map_zero_eq_one, mul_one]]
    have h1 : (Finset.univ.filter (fun t : F => t = 0)).card = 1 := by
      rw [Finset.filter_eq' Finset.univ (0 : F), if_pos (Finset.mem_univ 0),
        Finset.card_singleton]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset F)) (p := fun t : F => t = 0)
    rw [Finset.card_univ] at hsplit
    have h2 : (Finset.univ.filter (fun t : F => ¬ t = 0)).card = Fintype.card F - 1 := by omega
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h2, one_smul, nsmul_eq_mul,
      Nat.cast_sub hq1, Nat.cast_one]
  · rw [if_neg hs]
    have hsplit : ∀ t : F, (if t = 0 then X else Y) * ψ (t * s)
        = Y * ψ (t * s) + (if t = 0 then (X - Y) * ψ (t * s) else 0) := by
      intro t
      by_cases ht : t = 0
      · rw [if_pos ht, if_pos ht]; ring
      · rw [if_neg ht, if_neg ht]; ring
    rw [Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_add_distrib]
    have hzero : ∑ t : F, Y * ψ (t * s) = 0 := by
      rw [← Finset.mul_sum]
      have hchar : ∑ t : F, ψ (t * s) = 0 := by
        have hne : AddChar.mulShift ψ s ≠ 1 := ECCLib.mulShift_ne_one hψ hs
        have hsum := AddChar.sum_eq_zero_of_ne_one hne
        rw [← hsum]
        exact Finset.sum_congr rfl fun t _ => by rw [AddChar.mulShift_apply, mul_comm]
      rw [hchar, mul_zero]
    have hdelta : ∑ t : F, (if t = 0 then (X - Y) * ψ (t * s) else 0) = X - Y := by
      rw [Finset.sum_ite_eq' Finset.univ (0 : F) (fun t => (X - Y) * ψ (t * s))]
      rw [if_pos (Finset.mem_univ 0), zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [hzero, hdelta, zero_add]

/-- **The bivariate coordinatewise Krawtchouk factorization**:
`Σ_y X^{n−wt y}Y^{wt y}·ψ⟨y,x⟩ = (X+(q−1)Y)^{n−wt x}·(X−Y)^{wt x}`. -/
lemma homKrawtchouk_pi {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (X Y : ℂ) (x : ι → F) :
    ∑ y : ι → F, (X ^ (Fintype.card ι - hammingNorm y) * Y ^ hammingNorm y) * ψ (pairing y x)
      = (X + ((Fintype.card F : ℂ) - 1) * Y) ^ (Fintype.card ι - hammingNorm x)
        * (X - Y) ^ hammingNorm x := by
  classical
  have hfac : ∀ y : ι → F,
      (X ^ (Fintype.card ι - hammingNorm y) * Y ^ hammingNorm y) * ψ (pairing y x)
      = ∏ i : ι, ((if y i = 0 then X else Y) * ψ (y i * x i)) := by
    intro y
    rw [Finset.prod_mul_distrib]
    congr 1
    · rw [prod_ite_pow]
    · unfold pairing
      rw [addChar_map_sum]
  rw [Finset.sum_congr rfl fun y _ => hfac y, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset F)
      (fun (i : ι) (t : F) => (if t = 0 then X else Y) * ψ (t * x i))]
  rw [Finset.prod_congr rfl fun i _ => homKrawtchouk_sum hψ X Y (x i)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => x i = 0)
  rw [Finset.card_univ] at hsplit
  have hwt : (Finset.univ.filter (fun i => ¬ x i = 0)).card = hammingNorm x := rfl
  rw [hwt]
  congr 2
  omega

open Classical in
/-- **The homogeneous MacWilliams identity**:
`|C| · W_{C^⊥}(X,Y) = W_C(X+(q−1)Y, X−Y)`, at every `X, Y ∈ ℂ`. Weight statistics of the DFT bridge
`𝓕(𝟙_C) = |C|·𝟙_{C^⊥}`, with the bivariate Krawtchouk factorization. -/
theorem homMacwilliams (C : Submodule F (ι → F)) (X Y : ℂ) :
    (Nat.card C : ℂ) * homWeightEnum (dualCode C) X Y
      = homWeightEnum C (X + ((Fintype.card F : ℂ) - 1) * Y) (X - Y) := by
  obtain ⟨ψ, hψ⟩ := exists_ne_one_addChar F
  have hbridge : ∀ y : ι → F,
      (Nat.card C : ℂ) * indicator (dualCode C) y = fourierOp ψ (indicator C) y := by
    intro y
    rw [fourierOp_indicator hψ C]
    simp
  unfold homWeightEnum
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun y _ => by
    rw [show (Nat.card C : ℂ) * (indicator (dualCode C) y *
        (X ^ (Fintype.card ι - hammingNorm y) * Y ^ hammingNorm y))
        = ((Nat.card C : ℂ) * indicator (dualCode C) y) *
        (X ^ (Fintype.card ι - hammingNorm y) * Y ^ hammingNorm y) from by ring,
      hbridge y, fourierOp_apply, Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← homKrawtchouk_pi hψ X Y x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

open Classical in
/-- Sanity: the homogeneous identity specializes at `X = 1` to the single-variable `macwilliams`
statement — `|C|·W_{C^⊥}(z) = W_C(1+(q−1)z, 1−z)`. -/
theorem macwilliams_of_homMacwilliams (C : Submodule F (ι → F)) (z : ℂ) :
    (Nat.card C : ℂ) * weightEnum (dualCode C) z
      = homWeightEnum C (1 + ((Fintype.card F : ℂ) - 1) * z) (1 - z) := by
  rw [← homWeightEnum_one (dualCode C) z, homMacwilliams C 1 z]

end Bivariate

/-! ## The weight distribution -/

section Distribution

open Classical in
/-- The **weight distribution** `Aᵢ = #{x ∈ C : wt(x) = i}`. -/
noncomputable def weightDist (C : Submodule F (ι → F)) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : ι → F => x ∈ C ∧ hammingNorm x = i)).card

open Classical in
/-- The **weight enumerator as a polynomial** `W_C(t) = Σ_{x∈C} t^{wt x}`, whose `i`-th coefficient
is the weight-distribution number `Aᵢ`. -/
noncomputable def weightPoly (C : Submodule F (ι → F)) : Polynomial ℂ :=
  ∑ x : ι → F, Polynomial.C (indicator C x) * Polynomial.X ^ hammingNorm x

open Classical in
/-- Evaluating `weightPoly` recovers the single-variable enumerator. -/
theorem weightPoly_eval (C : Submodule F (ι → F)) (z : ℂ) :
    (weightPoly C).eval z = weightEnum C z := by
  unfold weightPoly weightEnum
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

open Classical in
/-- **The coefficients of `weightPoly` are the weight distribution**: `[t^i] W_C = Aᵢ`. -/
theorem weightPoly_coeff (C : Submodule F (ι → F)) (i : ℕ) :
    (weightPoly C).coeff i = (weightDist C i : ℂ) := by
  unfold weightPoly weightDist
  rw [Polynomial.finset_sum_coeff]
  have hterm : ∀ x : ι → F,
      (Polynomial.C (indicator C x) * Polynomial.X ^ hammingNorm x).coeff i
      = if (x ∈ C ∧ hammingNorm x = i) then (1 : ℂ) else 0 := by
    intro x
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    unfold indicator
    by_cases h1 : x ∈ C
    · by_cases h2 : hammingNorm x = i
      · simp [h1, h2]
      · simp [h1, h2, Ne.symm h2]
    · simp [h1]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_boole]

open Classical in
/-- `A₀ = 1`: the only weight-zero codeword is `0`, and it is in every code. -/
theorem weightDist_zero (C : Submodule F (ι → F)) : weightDist C 0 = 1 := by
  unfold weightDist
  have hset : (Finset.univ.filter (fun x : ι → F => x ∈ C ∧ hammingNorm x = 0)) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hwt⟩
      exact hammingNorm_eq_zero.mp hwt
    · rintro rfl
      exact ⟨C.zero_mem, hammingNorm_zero⟩
  rw [hset, Finset.card_singleton]

end Distribution

end ECCLib.Coding

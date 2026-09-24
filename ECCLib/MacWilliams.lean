/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Codes
import ECCLib.MonomialWeil

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# MacWilliams as the `w`-transform of weight statistics

The structural chain, each link a theorem in this file:

* **`w` normalizes the monomial group** (`fourierMap_comp_dilMap`, `fourierOp_comp_dilOp`,
  `fourierMap_comp_permMap`, `fourierOp_comp_permOp`): conjugation by the Weyl element inverts
  dilations and fixes permutations — at the symplectic level and at the operator level. This is
  *why* the DFT acts on weight data at all: it normalizes the group whose invariant weight is.
* **The Krawtchouk sums** (`krawtchouk_sum`, `krawtchouk_pi`): the one-dimensional character sum
  `Σ_t z^{[t≠0]}ψ(ts)` — `1+(q−1)z` at `s = 0`, `1−z` otherwise — and its coordinatewise
  factorization `Σ_y z^{wt y}ψ⟨y,x⟩ = (1+(q−1)z)^{n−wt x}(1−z)^{wt x}`.
* **The MacWilliams identity** (`macwilliams`), in its division-free sum form:

  `|C| · W_{C^⊥}(z) = Σ_{x∈C} (1+(q−1)z)^{n−wt(x)} · (1−z)^{wt(x)}`

  proved as *weight statistics of the bridge theorem* `𝓕(𝟙_C) = |C|·𝟙_{C^⊥}`: sum the bridge
  against `z^{wt}`, swap, factorize coordinatewise. The dual's weight distribution is completely
  determined by the code's — the distance-transfer inference channel (`weightEnum_dualCode_eq`).
* **Sanity at `z = 1`** (`weightEnum_one`, `macwilliams_one`): the identity degenerates to
  `|C^⊥|·|C| = q^n`, reproducing `card_dualCode_mul_card` — derived *from* `macwilliams`, not from
  the Poisson layer, as the designed cross-check.
-/

namespace ECCLib.Coding

open ECCLib.Heisenberg

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## `w` normalizes the monomial group -/

section Normalizes

/-- `w · D_d = D_{d⁻¹} · w` at the symplectic level: conjugating a dilation by the Weyl element
inverts it. -/
theorem fourierMap_comp_dilMap (d : ι → F) :
    Heis.fourierMap (F := F) ∘ Heis.dilMap d
      = Heis.dilMap (fun i => (d i)⁻¹) ∘ Heis.fourierMap := by
  funext x
  refine Heis.ext ?_ ?_ rfl
  · funext i
    simp only [Function.comp_apply, Heis.fourierMap, Heis.dilMap_pos, Heis.dilMap_mom]
  · funext i
    simp only [Function.comp_apply, Heis.fourierMap, Heis.dilMap_pos, Heis.dilMap_mom,
      Pi.neg_apply, inv_inv]
    ring

/-- `w` commutes with permutations at the symplectic level. -/
theorem fourierMap_comp_permMap (σ : Equiv.Perm ι) :
    Heis.fourierMap (F := F) ∘ Heis.permMap σ = Heis.permMap σ ∘ Heis.fourierMap := by
  funext x
  refine Heis.ext ?_ ?_ rfl
  all_goals
    funext i
    simp only [Function.comp_apply, Heis.fourierMap, Heis.permMap_pos, Heis.permMap_mom,
      Pi.neg_apply]

/-- `𝓕 ∘ D_d = D_{d⁻¹} ∘ 𝓕` at the operator level — the DFT normalizes the dilation operators. -/
theorem fourierOp_comp_dilOp (ψ : AddChar F ℂ) {d : ι → F} (hd : ∀ i, d i ≠ 0) :
    fourierOp ψ ∘ₗ dilOp d = dilOp (fun i => (d i)⁻¹) ∘ₗ fourierOp ψ := by
  refine LinearMap.ext fun f => ?_
  funext y
  simp only [LinearMap.comp_apply, fourierOp_apply, dilOp_apply, inv_inv]
  rw [← Equiv.sum_comp (Equiv.piCongrRight fun i : ι => Equiv.mulLeft₀ (d i) (hd i))
    (fun x => ψ (pairing y x) * f (fun i => (d i)⁻¹ * x i))]
  refine Finset.sum_congr rfl fun v _ => ?_
  change ψ (pairing y fun i => d i * v i) * f (fun i => (d i)⁻¹ * (d i * v i))
      = ψ (pairing (fun i => d i * y i) v) * f v
  have harg : (fun i => (d i)⁻¹ * (d i * v i)) = v := by
    funext i
    rw [← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  have hpair : pairing y (fun i => d i * v i) = pairing (fun i => d i * y i) v := by
    unfold pairing
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [harg, hpair]

/-- `𝓕 ∘ P_σ = P_σ ∘ 𝓕` at the operator level — the DFT commutes with permutation operators. -/
theorem fourierOp_comp_permOp (ψ : AddChar F ℂ) (σ : Equiv.Perm ι) :
    fourierOp ψ ∘ₗ permOp σ = permOp σ ∘ₗ fourierOp ψ := by
  refine LinearMap.ext fun f => ?_
  funext y
  simp only [LinearMap.comp_apply, fourierOp_apply, permOp_apply]
  rw [← Equiv.sum_comp (Equiv.piCongrLeft' (fun _ : ι => F) σ)
    (fun x => ψ (pairing y x) * f (fun i => x (σ i)))]
  refine Finset.sum_congr rfl fun v _ => ?_
  change ψ (pairing y fun i => v (σ.symm i)) * f (fun i => v (σ.symm (σ i)))
      = ψ (pairing (fun i => y (σ i)) v) * f v
  have harg : (fun i => v (σ.symm (σ i))) = v := by
    funext i
    rw [Equiv.symm_apply_apply]
  have hpair : pairing y (fun i => v (σ.symm i)) = pairing (fun i => y (σ i)) v := by
    unfold pairing
    rw [← Equiv.sum_comp σ (fun i => y i * v (σ.symm i))]
    exact Finset.sum_congr rfl fun j _ => by rw [Equiv.symm_apply_apply]
  rw [harg, hpair]

end Normalizes

/-! ## The Krawtchouk sums -/

section Krawtchouk

variable [DecidableEq F]

/-- **The one-dimensional Krawtchouk sum**: `Σ_t z^{[t≠0]}·ψ(ts) = 1+(q−1)z` at `s = 0` and `1−z`
otherwise. These two values are the entries of the MacWilliams transform. -/
lemma krawtchouk_sum {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (z : ℂ) (s : F) :
    ∑ t : F, (if t = 0 then 1 else z) * ψ (t * s)
      = if s = 0 then 1 + ((Fintype.card F : ℂ) - 1) * z else 1 - z := by
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
    have h2 : (Finset.univ.filter (fun t : F => ¬ t = 0)).card = Fintype.card F - 1 := by
      omega
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h2, one_smul, nsmul_eq_mul,
      Nat.cast_sub hq1, Nat.cast_one]
  · rw [if_neg hs]
    have hsplit : ∀ t : F, (if t = 0 then (1 : ℂ) else z) * ψ (t * s)
        = z * ψ (t * s) + (if t = 0 then (1 - z) * ψ (t * s) else 0) := by
      intro t
      by_cases ht : t = 0
      · rw [if_pos ht, if_pos ht]
        ring
      · rw [if_neg ht, if_neg ht]
        ring
    rw [Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_add_distrib]
    have hzero : ∑ t : F, z * ψ (t * s) = 0 := by
      rw [← Finset.mul_sum]
      have hchar : ∑ t : F, ψ (t * s) = 0 := by
        have hne : AddChar.mulShift ψ s ≠ 1 := ECCLib.mulShift_ne_one hψ hs
        have hsum := AddChar.sum_eq_zero_of_ne_one hne
        rw [← hsum]
        exact Finset.sum_congr rfl fun t _ => by rw [AddChar.mulShift_apply, mul_comm]
      rw [hchar, mul_zero]
    have hdelta : ∑ t : F, (if t = 0 then (1 - z) * ψ (t * s) else 0) = 1 - z := by
      rw [Finset.sum_ite_eq' Finset.univ (0 : F) (fun t => (1 - z) * ψ (t * s))]
      rw [if_pos (Finset.mem_univ 0), zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [hzero, hdelta, zero_add]

/-- **The coordinatewise Krawtchouk factorization**:
`Σ_y z^{wt y}·ψ⟨y,x⟩ = (1+(q−1)z)^{n−wt x}·(1−z)^{wt x}`. -/
lemma krawtchouk_pi {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (z : ℂ) (x : ι → F) :
    ∑ y : ι → F, z ^ hammingNorm y * ψ (pairing y x)
      = (1 + ((Fintype.card F : ℂ) - 1) * z) ^ (Fintype.card ι - hammingNorm x)
        * (1 - z) ^ hammingNorm x := by
  classical
  have hfac : ∀ y : ι → F, z ^ hammingNorm y * ψ (pairing y x)
      = ∏ i : ι, ((if y i = 0 then 1 else z) * ψ (y i * x i)) := by
    intro y
    rw [Finset.prod_mul_distrib]
    congr 1
    · unfold hammingNorm
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, one_mul]
    · unfold pairing
      rw [addChar_map_sum]
  rw [Finset.sum_congr rfl fun y _ => hfac y, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset F)
      (fun (i : ι) (t : F) => (if t = 0 then 1 else z) * ψ (t * x i))]
  rw [Finset.prod_congr rfl fun i _ => krawtchouk_sum hψ z (x i)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => x i = 0)
  rw [Finset.card_univ] at hsplit
  have hwt : (Finset.univ.filter (fun i => ¬ x i = 0)).card = hammingNorm x := rfl
  rw [hwt]
  congr 2
  omega

end Krawtchouk

/-! ## The weight enumerator and the MacWilliams identity -/

section MacWilliams

variable [DecidableEq F]

open Classical in
/-- The **weight enumerator** `W_C(z) = Σ_{x∈C} z^{wt(x)}`, as a function of `z : ℂ`. -/
noncomputable def weightEnum (C : Submodule F (ι → F)) (z : ℂ) : ℂ :=
  ∑ x : ι → F, indicator C x * z ^ hammingNorm x

open Classical in
/-- **The MacWilliams identity** (division-free sum form):
`|C|·W_{C^⊥}(z) = Σ_{x∈C} (1+(q−1)z)^{n−wt x}·(1−z)^{wt x}` — proved as weight statistics of the
bridge theorem `𝓕(𝟙_C) = |C|·𝟙_{C^⊥}`. The dual code's weight distribution is completely
determined by the code's. -/
theorem macwilliams (C : Submodule F (ι → F)) (z : ℂ) :
    (Nat.card C : ℂ) * weightEnum (dualCode C) z
      = ∑ x : ι → F, indicator C x *
          ((1 + ((Fintype.card F : ℂ) - 1) * z) ^ (Fintype.card ι - hammingNorm x)
            * (1 - z) ^ hammingNorm x) := by
  obtain ⟨ψ, hψ⟩ := exists_ne_one_addChar F
  have hbridge : ∀ y : ι → F, (Nat.card C : ℂ) * indicator (dualCode C) y
      = fourierOp ψ (indicator C) y := by
    intro y
    rw [fourierOp_indicator hψ C]
    simp
  unfold weightEnum
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun y _ => by
    rw [show (Nat.card C : ℂ) * (indicator (dualCode C) y * z ^ hammingNorm y)
        = ((Nat.card C : ℂ) * indicator (dualCode C) y) * z ^ hammingNorm y from by ring,
      hbridge y, fourierOp_apply, Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← krawtchouk_pi hψ z x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

open Classical in
/-- `W_C(1) = |C|`. -/
theorem weightEnum_one (C : Submodule F (ι → F)) : weightEnum C 1 = (Nat.card C : ℂ) := by
  unfold weightEnum indicator
  rw [Finset.sum_congr rfl fun x _ => by rw [one_pow, mul_one]]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
/-- **Sanity at `z = 1`**: the MacWilliams identity degenerates to `|C^⊥|·|C| = q^n` — derived from
`macwilliams`, reproducing `card_dualCode_mul_card` as the designed cross-check. -/
theorem macwilliams_one (C : Submodule F (ι → F)) :
    (Nat.card C : ℂ) * (Nat.card (dualCode C) : ℂ) = (Fintype.card (ι → F) : ℂ) := by
  have h := macwilliams C 1
  rw [weightEnum_one] at h
  rw [h]
  have hterm : ∀ x : ι → F, indicator C x *
      ((1 + ((Fintype.card F : ℂ) - 1) * 1) ^ (Fintype.card ι - hammingNorm x)
        * (1 - 1) ^ hammingNorm x)
      = if x = 0 then ((Fintype.card F : ℂ)) ^ (Fintype.card ι) else 0 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl]
      have h0 : hammingNorm (0 : ι → F) = 0 := hammingNorm_zero
      rw [h0, Nat.sub_zero, pow_zero, mul_one]
      rw [show indicator C (0 : ι → F) = 1 from by unfold indicator; rw [if_pos C.zero_mem]]
      rw [one_mul]
      congr 1
      ring
    · rw [if_neg hx]
      have hwt : hammingNorm x ≠ 0 := by
        rw [hammingNorm_ne_zero_iff]
        exact hx
      rw [show ((1 : ℂ) - 1) = 0 from by ring, zero_pow hwt, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [Finset.sum_ite_eq' Finset.univ (0 : ι → F)
    (fun _ => ((Fintype.card F : ℂ)) ^ (Fintype.card ι))]
  rw [if_pos (Finset.mem_univ 0), Fintype.card_fun]
  push_cast
  ring

open Classical in
/-- **Distance transfer**: the dual code's weight enumerator — hence its whole weight distribution
and minimum distance — is determined by the code's, in closed form. -/
theorem weightEnum_dualCode_eq (C : Submodule F (ι → F)) (z : ℂ) :
    weightEnum (dualCode C) z
      = (Nat.card C : ℂ)⁻¹ * ∑ x : ι → F, indicator C x *
          ((1 + ((Fintype.card F : ℂ) - 1) * z) ^ (Fintype.card ι - hammingNorm x)
            * (1 - z) ^ hammingNorm x) := by
  have hpos : (Nat.card C : ℂ) ≠ 0 := by
    have : 0 < Nat.card C := Nat.card_pos
    exact_mod_cast this.ne'
  rw [← macwilliams C z]
  field_simp

end MacWilliams

/-! ## Weight shells as monomial orbits -/

section Shells

variable [DecidableEq F]

open Classical in
/-- **The forward orbit construction**: two vectors of equal Hamming weight differ by a monomial map
— a permutation matching support to support (assembled from `Fintype.equivOfCardEq` on supports and
cosupports via `Equiv.subtypeCongr`) followed by the diagonal scaling that fixes the values. -/
theorem exists_monomial_of_hammingNorm_eq {x y : ι → F} (h : hammingNorm x = hammingNorm y) :
    ∃ (σ : Equiv.Perm ι) (d : ι → F), (∀ i, d i ≠ 0) ∧ y = fun i => d i * x (σ i) := by
  have hcard : Fintype.card {i // y i ≠ 0} = Fintype.card {i // x i ≠ 0} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h.symm
  have hcardc : Fintype.card {i // ¬ y i ≠ 0} = Fintype.card {i // ¬ x i ≠ 0} := by
    have h1 : Fintype.card {i // ¬ y i ≠ 0}
        = Fintype.card ι - Fintype.card {i // y i ≠ 0} := Fintype.card_subtype_compl _
    have h2 : Fintype.card {i // ¬ x i ≠ 0}
        = Fintype.card ι - Fintype.card {i // x i ≠ 0} := Fintype.card_subtype_compl _
    rw [h1, h2, hcard]
  let e₁ : {i // y i ≠ 0} ≃ {i // x i ≠ 0} := Fintype.equivOfCardEq hcard
  let e₂ : {i // ¬ y i ≠ 0} ≃ {i // ¬ x i ≠ 0} := Fintype.equivOfCardEq hcardc
  let σ : Equiv.Perm ι := Equiv.subtypeCongr e₁ e₂
  have hpos : ∀ i, y i ≠ 0 → x (σ i) ≠ 0 := by
    intro i hi
    have hσ : σ i = (e₁ ⟨i, hi⟩ : ι) := by
      change (Equiv.sumCompl fun j => x j ≠ 0)
        ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl fun j => y j ≠ 0).symm i)) = _
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun j => y j ≠ 0) (a := i) hi]
      rfl
    rw [hσ]
    exact (e₁ ⟨i, hi⟩).2
  have hneg : ∀ i, y i = 0 → x (σ i) = 0 := by
    intro i hi
    have hni : ¬ y i ≠ 0 := by simpa using hi
    have hσ : σ i = (e₂ ⟨i, hni⟩ : ι) := by
      change (Equiv.sumCompl fun j => x j ≠ 0)
        ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl fun j => y j ≠ 0).symm i)) = _
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun j => y j ≠ 0) (a := i) hni]
      rfl
    rw [hσ]
    have h2 := (e₂ ⟨i, hni⟩).2
    simpa using h2
  refine ⟨σ, fun i => if y i = 0 then 1 else y i * (x (σ i))⁻¹, fun i => ?_, ?_⟩
  · change (if y i = 0 then (1 : F) else y i * (x (σ i))⁻¹) ≠ 0
    by_cases hi : y i = 0
    · rw [if_pos hi]
      exact one_ne_zero
    · rw [if_neg hi]
      exact mul_ne_zero hi (inv_ne_zero (hpos i hi))
  · funext i
    change y i = (if y i = 0 then (1 : F) else y i * (x (σ i))⁻¹) * x (σ i)
    by_cases hi : y i = 0
    · rw [if_pos hi, one_mul, hneg i hi]
      exact hi
    · rw [if_neg hi, mul_assoc, inv_mul_cancel₀ (hpos i hi), mul_one]

open Classical in
/-- **Weight shells are the monomial orbits**: two vectors have the same Hamming weight iff a
monomial map (permutation × diagonal units) carries one to the other. Weight is the *complete*
invariant of the frame-fixing group — the group-theoretic identity of "distance data". -/
theorem hammingNorm_eq_iff_monomial {x y : ι → F} :
    hammingNorm x = hammingNorm y ↔
      ∃ (σ : Equiv.Perm ι) (d : ι → F), (∀ i, d i ≠ 0) ∧ y = fun i => d i * x (σ i) := by
  constructor
  · exact exists_monomial_of_hammingNorm_eq
  · rintro ⟨σ, d, hd, rfl⟩
    rw [hammingNorm_dil hd (fun j => x (σ j))]
    have hp := hammingNorm_perm σ⁻¹ x
    rw [inv_inv] at hp
    exact hp.symm

end Shells

end ECCLib.Coding

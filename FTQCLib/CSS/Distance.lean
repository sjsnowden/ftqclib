/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Logical
import FTQCLib.Stabilizer.Error

set_option linter.unusedSectionVars false

/-! # Distance for CSS codes

For a stabilizer code the \emph{distance} is the minimum weight of a
non-trivial logical operator. For a CSS code the distance splits along
the $X$/$Z$ type structure of the stabilizer: any non-trivial logical
contributes either a non-trivial $X$-type logical (when its $X$-support
is not in $\operatorname{im}(H_X^\top)$) or a non-trivial $Z$-type
logical (otherwise). The minimum-weight $X$- and $Z$-logicals are
therefore enough to compute the code distance.

We use `ℕ∞` for distances so that codes with no logicals of a given
type get distance `⊤`, and the formula
$d(S_\mathrm{CSS}) = \min(d_X, d_Z)$ holds without degenerate-case
caveats.

This file proves:

* **E5a (X-distance, Z-distance)** `cssXDistance`, `cssZDistance` —
  definitions.
* **E5b (block projections)** `cssXStabilizer_Z_eq_zero` etc.: each
  X-stabilizer has `Z = 0` and its X-part lies in `im(H_X^\top)`;
  symmetric Z-side statements.
* **E5c (X/Z lifting)** `cssXStabilizer_of_X_mem_subspace` and the
  symmetric `cssZStabilizer_of_Z_mem_subspace`.
* **E5d (S decomposition)** `mem_cssStabilizer_iff` — `p ∈ S_CSS` iff
  `p.X ∈ im(H_X^\top)` and `p.Z ∈ im(H_Z^\top)`.
* **E5e (N(S) decomposition)** `mem_normalizer_cssStabilizer_iff`.
* **E5f (X-lift to N(S))** `cssXGen_ofMem_carrier_mem_normalizer` (and
  Z-side symmetric).
* **E5g (non-trivial pure-type logical)** `cssXGen_isNontrivialLogical`
  and `cssZGen_isNontrivialLogical`.
* **E5h (distance bounds)** `distance_le_cssXDistance`,
  `distance_le_cssZDistance`.
* **E5i (distance equality)** `cssDistance_eq` — the equality
  `d(S_\mathrm{CSS}) = \min(d_X, d_Z)` in `ℕ∞`.
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli FTQCLib.Stabilizer Matrix

variable {n r_X r_Z : ℕ}

/-! ## Distance definitions -/

/-- The X-distance of a CSS code: the infimum (in `ℕ∞`) of Hamming
weights of non-trivial X-type logical vectors. -/
noncomputable def cssXDistance
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) : ℕ∞ :=
  ⨅ (v : Fin n → ZMod 2)
    (_ : v ∈ cssXLogicalCarrier H_Z)
    (_ : v ∉ cssXLogicalSubspace H_X),
    ((Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card : ℕ∞)

/-- The Z-distance of a CSS code. -/
noncomputable def cssZDistance
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) : ℕ∞ :=
  ⨅ (v : Fin n → ZMod 2)
    (_ : v ∈ cssZLogicalCarrier H_X)
    (_ : v ∉ cssZLogicalSubspace H_Z),
    ((Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card : ℕ∞)

/-! ## Block-projection lemmas -/

/-- Every element of the X-stabilizer subspace has `Z`-part zero. -/
theorem cssXStabilizer_Z_eq_zero
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {p : Pauli n} (hp : p ∈ cssXStabilizer H_X) : p.Z = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro y ⟨i, rfl⟩; rfl
  · rfl
  · intros x y _ _ hx hy
    rw [Z_add, hx, hy, zero_add]
  · intros c x _ hx
    rw [Z_smul, hx, smul_zero]

/-- Every element of the Z-stabilizer subspace has `X`-part zero. -/
theorem cssZStabilizer_X_eq_zero
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {p : Pauli n} (hp : p ∈ cssZStabilizer H_Z) : p.X = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro y ⟨i, rfl⟩; rfl
  · rfl
  · intros x y _ _ hx hy
    rw [X_add, hx, hy, zero_add]
  · intros c x _ hx
    rw [X_smul, hx, smul_zero]

/-- The X-part of an X-stabilizer is in `im(H_X^\top)`. -/
theorem cssXStabilizer_X_mem_subspace
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    {p : Pauli n} (hp : p ∈ cssXStabilizer H_X) :
    p.X ∈ cssXLogicalSubspace H_X := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro y ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    change Matrix.mulVecLin H_Xᵀ (Pi.single i 1) j = H_X i j
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_def,
      Matrix.transpose_transpose]
  · exact Submodule.zero_mem _
  · intros x y _ _ hx hy
    rw [X_add]; exact Submodule.add_mem _ hx hy
  · intros c x _ hx
    rw [X_smul]; exact Submodule.smul_mem _ _ hx

/-- The Z-part of a Z-stabilizer is in `im(H_Z^\top)`. -/
theorem cssZStabilizer_Z_mem_subspace
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    {p : Pauli n} (hp : p ∈ cssZStabilizer H_Z) :
    p.Z ∈ cssZLogicalSubspace H_Z := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro y ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    change Matrix.mulVecLin H_Zᵀ (Pi.single i 1) j = H_Z i j
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_def,
      Matrix.transpose_transpose]
  · exact Submodule.zero_mem _
  · intros x y _ _ hx hy
    rw [Z_add]; exact Submodule.add_mem _ hx hy
  · intros c x _ hx
    rw [Z_smul]; exact Submodule.smul_mem _ _ hx

/-! ## Lifting subspace-vectors to Pauli-level stabilizers -/

/-- An X-only Pauli `(v, 0)` is in `cssXStabilizer` when `v ∈ im(H_X^\top)`. -/
theorem cssXStabilizer_of_X_mem_subspace
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalSubspace H_X) :
    (⟨v, 0⟩ : Pauli n) ∈ cssXStabilizer H_X := by
  obtain ⟨u, hu⟩ := hv
  have key : (⟨v, 0⟩ : Pauli n) = ∑ i : Fin r_X, u i • cssXGen H_X i := by
    ext j
    · change v j = (∑ i, u i • cssXGen H_X i).X j
      rw [X_finsetSum, Finset.sum_apply]
      have hv_apply : v j = (Matrix.mulVecLin H_Xᵀ u) j := by rw [hu]
      rw [hv_apply]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_transpose,
        Matrix.vecMul, dotProduct, cssXGen, X_smul, Pi.smul_apply,
        smul_eq_mul, mul_comm]
    · change (0 : ZMod 2) = (∑ i, u i • cssXGen H_X i).Z j
      rw [Z_finsetSum, Finset.sum_apply]
      symm
      refine Finset.sum_eq_zero (fun i _ => ?_)
      change u i • (cssXGen H_X i).Z j = 0
      change u i • (0 : Fin n → ZMod 2) j = 0
      simp
  rw [key]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- A Z-only Pauli `(0, v)` is in `cssZStabilizer` when `v ∈ im(H_Z^\top)`. -/
theorem cssZStabilizer_of_Z_mem_subspace
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    {v : Fin n → ZMod 2} (hv : v ∈ cssZLogicalSubspace H_Z) :
    (⟨0, v⟩ : Pauli n) ∈ cssZStabilizer H_Z := by
  obtain ⟨u, hu⟩ := hv
  have key : (⟨0, v⟩ : Pauli n) = ∑ i : Fin r_Z, u i • cssZGen H_Z i := by
    ext j
    · change (0 : ZMod 2) = (∑ i, u i • cssZGen H_Z i).X j
      rw [X_finsetSum, Finset.sum_apply]
      symm
      refine Finset.sum_eq_zero (fun i _ => ?_)
      change u i • (cssZGen H_Z i).X j = 0
      change u i • (0 : Fin n → ZMod 2) j = 0
      simp
    · change v j = (∑ i, u i • cssZGen H_Z i).Z j
      rw [Z_finsetSum, Finset.sum_apply]
      have hv_apply : v j = (Matrix.mulVecLin H_Zᵀ u) j := by rw [hu]
      rw [hv_apply]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_transpose,
        Matrix.vecMul, dotProduct, cssZGen, Z_smul, Pi.smul_apply,
        smul_eq_mul, mul_comm]
  rw [key]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-! ## Direct-sum decomposition -/

/-- **E5d:** a Pauli is in `S_CSS` iff its X-part is in `im(H_X^\top)`
and its Z-part is in `im(H_Z^\top)`. -/
theorem mem_cssStabilizer_iff
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (p : Pauli n) :
    p ∈ cssStabilizer H_X H_Z ↔
      p.X ∈ cssXLogicalSubspace H_X ∧ p.Z ∈ cssZLogicalSubspace H_Z := by
  refine ⟨fun hp => ?_, fun ⟨hX, hZ⟩ => ?_⟩
  · rw [cssStabilizer, Submodule.mem_sup] at hp
    obtain ⟨pX, hpX, pZ, hpZ, rfl⟩ := hp
    have hpX_Z : pX.Z = 0 := cssXStabilizer_Z_eq_zero hpX
    have hpZ_X : pZ.X = 0 := cssZStabilizer_X_eq_zero hpZ
    refine ⟨?_, ?_⟩
    · rw [X_add, hpZ_X, add_zero]
      exact cssXStabilizer_X_mem_subspace H_X hpX
    · rw [Z_add, hpX_Z, zero_add]
      exact cssZStabilizer_Z_mem_subspace H_Z hpZ
  · have hX_pauli : (⟨p.X, 0⟩ : Pauli n) ∈ cssXStabilizer H_X :=
      cssXStabilizer_of_X_mem_subspace H_X hX
    have hZ_pauli : (⟨0, p.Z⟩ : Pauli n) ∈ cssZStabilizer H_Z :=
      cssZStabilizer_of_Z_mem_subspace H_Z hZ
    have hsum : (⟨p.X, 0⟩ : Pauli n) + ⟨0, p.Z⟩ = p := by
      ext i
      · change p.X i + 0 = p.X i; rw [add_zero]
      · change 0 + p.Z i = p.Z i; rw [zero_add]
    rw [cssStabilizer, ← hsum]
    exact Submodule.add_mem_sup hX_pauli hZ_pauli

/-! ## CSS normalizer -/

/-- An X-type Pauli `(v, 0)` with `v ∈ ker(H_Z)` lies in `N(S_CSS)`. -/
theorem cssXGen_ofMem_carrier_mem_normalizer
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z) :
    (⟨v, 0⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) := by
  rintro q hq
  rw [cssStabilizer, Submodule.mem_sup] at hq
  obtain ⟨qX, hqX, qZ, hqZ, rfl⟩ := hq
  rw [omega_add_right]
  have h_qX_zero : omega (⟨v, 0⟩ : Pauli n) qX = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hqX
    · rintro y ⟨j, rfl⟩
      simp [omega, cssXGen]
    · simp
    · intros y z _ _ hy hz; rw [omega_add_right, hy, hz, zero_add]
    · intros c y _ hy; rw [omega_smul_right, hy, mul_zero]
  rw [h_qX_zero, zero_add]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hqZ
  · rintro y ⟨j, rfl⟩
    have hZv : H_Z *ᵥ v = 0 := hv
    have hZvj : (H_Z *ᵥ v) j = 0 := by rw [hZv]; rfl
    have h_eq : omega (⟨v, 0⟩ : Pauli n) (cssZGen H_Z j) = (H_Z *ᵥ v) j := by
      simp [omega, cssZGen, Matrix.mulVec, dotProduct, mul_comm]
    rw [h_eq, hZvj]
  · simp
  · intros y z _ _ hy hz; rw [omega_add_right, hy, hz, zero_add]
  · intros c y _ hy; rw [omega_smul_right, hy, mul_zero]

/-- A Z-type Pauli `(0, v)` with `v ∈ ker(H_X)` lies in `N(S_CSS)`. -/
theorem cssZGen_ofMem_carrier_mem_normalizer
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {v : Fin n → ZMod 2} (hv : v ∈ cssZLogicalCarrier H_X) :
    (⟨0, v⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) := by
  rintro q hq
  rw [cssStabilizer, Submodule.mem_sup] at hq
  obtain ⟨qX, hqX, qZ, hqZ, rfl⟩ := hq
  rw [omega_add_right]
  have h_qZ_zero : omega (⟨0, v⟩ : Pauli n) qZ = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hqZ
    · rintro y ⟨j, rfl⟩
      simp [omega, cssZGen]
    · simp
    · intros y z _ _ hy hz; rw [omega_add_right, hy, hz, zero_add]
    · intros c y _ hy; rw [omega_smul_right, hy, mul_zero]
  have h_qX_zero : omega (⟨0, v⟩ : Pauli n) qX = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hqX
    · rintro y ⟨j, rfl⟩
      have hXv : H_X *ᵥ v = 0 := hv
      have hXvj : (H_X *ᵥ v) j = 0 := by rw [hXv]; rfl
      have h_eq : omega (⟨0, v⟩ : Pauli n) (cssXGen H_X j) = (H_X *ᵥ v) j := by
        simp [omega, cssXGen, Matrix.mulVec, dotProduct, mul_comm]
      rw [h_eq, hXvj]
    · simp
    · intros y z _ _ hy hz; rw [omega_add_right, hy, hz, zero_add]
    · intros c y _ hy; rw [omega_smul_right, hy, mul_zero]
  rw [h_qX_zero, h_qZ_zero, add_zero]

/-- **E5e:** a Pauli is in `N(S_CSS)` iff its X-part is in `ker(H_Z)`
and its Z-part is in `ker(H_X)`. -/
theorem mem_normalizer_cssStabilizer_iff
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (e : Pauli n) :
    e ∈ normalizer (cssStabilizer H_X H_Z) ↔
      e.X ∈ cssXLogicalCarrier H_Z ∧ e.Z ∈ cssZLogicalCarrier H_X := by
  refine ⟨fun he => ?_, fun ⟨hX, hZ⟩ => ?_⟩
  · refine ⟨?_, ?_⟩
    · change Matrix.mulVecLin H_Z e.X = 0
      ext j
      have := he (cssZGen H_Z j) (Submodule.mem_sup_right
        (Submodule.subset_span ⟨j, rfl⟩))
      have h_eq : omega e (cssZGen H_Z j) = (Matrix.mulVecLin H_Z e.X) j := by
        simp [omega, cssZGen, Matrix.mulVec, dotProduct, mul_comm]
      rw [← h_eq, this]; rfl
    · change Matrix.mulVecLin H_X e.Z = 0
      ext j
      have := he (cssXGen H_X j) (Submodule.mem_sup_left
        (Submodule.subset_span ⟨j, rfl⟩))
      have h_eq : omega e (cssXGen H_X j) = (Matrix.mulVecLin H_X e.Z) j := by
        simp [omega, cssXGen, Matrix.mulVec, dotProduct, mul_comm]
      rw [← h_eq, this]; rfl
  · have hX_pauli : (⟨e.X, 0⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) :=
      cssXGen_ofMem_carrier_mem_normalizer hX
    have hZ_pauli : (⟨0, e.Z⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) :=
      cssZGen_ofMem_carrier_mem_normalizer hZ
    have hsum : (⟨e.X, 0⟩ : Pauli n) + ⟨0, e.Z⟩ = e := by
      ext i
      · change e.X i + 0 = e.X i; rw [add_zero]
      · change 0 + e.Z i = e.Z i; rw [zero_add]
    rw [← hsum]
    exact Submodule.add_mem _ hX_pauli hZ_pauli

/-! ## Non-trivial logicals -/

/-- An X-only vector `v ∈ ker(H_Z) \ im(H_X^\top)` lifts to a
non-trivial logical of weight equal to the Hamming weight of `v`. -/
theorem cssXGen_isNontrivialLogical
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {v : Fin n → ZMod 2} (hv_carrier : v ∈ cssXLogicalCarrier H_Z)
    (hv_subspace : v ∉ cssXLogicalSubspace H_X) :
    (⟨v, 0⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) ∧
      (⟨v, 0⟩ : Pauli n) ∉ cssStabilizer H_X H_Z ∧
      weight (⟨v, 0⟩ : Pauli n) =
        (Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card := by
  refine ⟨cssXGen_ofMem_carrier_mem_normalizer hv_carrier, ?_, ?_⟩
  · intro h_stab
    exact hv_subspace ((mem_cssStabilizer_iff H_X H_Z _).mp h_stab).1
  · exact weight_of_Z_zero rfl

/-- A Z-only vector `v ∈ ker(H_X) \ im(H_Z^\top)` lifts to a
non-trivial logical of weight equal to the Hamming weight of `v`. -/
theorem cssZGen_isNontrivialLogical
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {v : Fin n → ZMod 2} (hv_carrier : v ∈ cssZLogicalCarrier H_X)
    (hv_subspace : v ∉ cssZLogicalSubspace H_Z) :
    (⟨0, v⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) ∧
      (⟨0, v⟩ : Pauli n) ∉ cssStabilizer H_X H_Z ∧
      weight (⟨0, v⟩ : Pauli n) =
        (Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card := by
  refine ⟨cssZGen_ofMem_carrier_mem_normalizer hv_carrier, ?_, ?_⟩
  · intro h_stab
    exact hv_subspace ((mem_cssStabilizer_iff H_X H_Z _).mp h_stab).2
  · exact weight_of_X_zero rfl

/-! ## Distance bounds -/

/-- The Hamming weight of the X-coordinate is bounded by the full
weight. -/
theorem hamming_X_le_weight (e : Pauli n) :
    (Finset.univ.filter (fun i : Fin n => e.X i ≠ 0)).card ≤ weight e := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, Or.inl hi.2⟩

theorem hamming_Z_le_weight (e : Pauli n) :
    (Finset.univ.filter (fun i : Fin n => e.Z i ≠ 0)).card ≤ weight e := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, Or.inr hi.2⟩

/-- **E5h (≤ X-side):** `d(S_CSS) ≤ d_X` in `ℕ∞`. -/
theorem distance_le_cssXDistance
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    distance (cssStabilizer H_X H_Z) ≤ cssXDistance H_X H_Z := by
  unfold cssXDistance
  refine le_iInf fun v => le_iInf fun hv_carrier =>
    le_iInf fun hv_subspace => ?_
  obtain ⟨hN, hnS, hwt⟩ :=
    cssXGen_isNontrivialLogical hv_carrier hv_subspace
  exact (distance_le_weight hN hnS).trans (by exact_mod_cast hwt.le)

/-- **E5h (≤ Z-side):** `d(S_CSS) ≤ d_Z` in `ℕ∞`. -/
theorem distance_le_cssZDistance
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    distance (cssStabilizer H_X H_Z) ≤ cssZDistance H_X H_Z := by
  unfold cssZDistance
  refine le_iInf fun v => le_iInf fun hv_carrier =>
    le_iInf fun hv_subspace => ?_
  obtain ⟨hN, hnS, hwt⟩ :=
    cssZGen_isNontrivialLogical hv_carrier hv_subspace
  exact (distance_le_weight hN hnS).trans (by exact_mod_cast hwt.le)

/-- **E5i (distance equality):** for a CSS code,
$d(S_\mathrm{CSS}) = \min(d_X, d_Z)$ as `ℕ∞`. -/
theorem cssDistance_eq
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    distance (cssStabilizer H_X H_Z) =
      min (cssXDistance H_X H_Z) (cssZDistance H_X H_Z) := by
  refine le_antisymm ?_ ?_
  · exact le_min (distance_le_cssXDistance H_X H_Z)
      (distance_le_cssZDistance H_X H_Z)
  · unfold distance
    refine le_iInf fun e => le_iInf fun heN => le_iInf fun heS => ?_
    obtain ⟨hX_in_ker, hZ_in_ker⟩ :=
      (mem_normalizer_cssStabilizer_iff H_X H_Z e).mp heN
    have hOr : e.X ∉ cssXLogicalSubspace H_X ∨
        e.Z ∉ cssZLogicalSubspace H_Z := by
      by_contra h
      apply heS
      rw [mem_cssStabilizer_iff]
      refine ⟨?_, ?_⟩
      · by_contra hX; exact h (Or.inl hX)
      · by_contra hZ; exact h (Or.inr hZ)
    rcases hOr with hX_out | hZ_out
    · -- min ≤ cssXDistance ≤ weight of (e.X, 0) ≤ weight e
      have h1 : cssXDistance H_X H_Z ≤
          ((Finset.univ.filter (fun i : Fin n => e.X i ≠ 0)).card : ℕ∞) := by
        unfold cssXDistance
        exact iInf_le_of_le e.X
          (iInf_le_of_le hX_in_ker (iInf_le _ hX_out))
      calc min (cssXDistance H_X H_Z) (cssZDistance H_X H_Z)
          ≤ cssXDistance H_X H_Z := min_le_left _ _
        _ ≤ ((Finset.univ.filter (fun i : Fin n => e.X i ≠ 0)).card : ℕ∞) := h1
        _ ≤ (weight e : ℕ∞) := by exact_mod_cast hamming_X_le_weight e
    · have h1 : cssZDistance H_X H_Z ≤
          ((Finset.univ.filter (fun i : Fin n => e.Z i ≠ 0)).card : ℕ∞) := by
        unfold cssZDistance
        exact iInf_le_of_le e.Z
          (iInf_le_of_le hZ_in_ker (iInf_le _ hZ_out))
      calc min (cssXDistance H_X H_Z) (cssZDistance H_X H_Z)
          ≤ cssZDistance H_X H_Z := min_le_right _ _
        _ ≤ ((Finset.univ.filter (fun i : Fin n => e.Z i ≠ 0)).card : ℕ∞) := h1
        _ ≤ (weight e : ℕ∞) := by exact_mod_cast hamming_Z_le_weight e

/-! ## Per-type detection and correction

The X-error and Z-error stories run in parallel. In each case the
detection/correction radius is set by a specific distance and policed
by a specific check matrix.

For an `X`-error `(v, 0)`:
- stays undetected iff `v ∈ ker(H_Z) = cssXLogicalCarrier`;
- is trivial iff `v ∈ im(H_X^T) = cssXLogicalSubspace`;
- distance is `d_X = cssXDistance`;
- detected by the Z-checks (rows of `H_Z`).

For a `Z`-error `(0, v)`:
- stays undetected iff `v ∈ ker(H_X) = cssZLogicalCarrier`;
- is trivial iff `v ∈ im(H_Z^T) = cssZLogicalSubspace`;
- distance is `d_Z = cssZDistance`;
- detected by the X-checks (rows of `H_X`).

The reason: a Z-check is a tensor product of `Z`'s, which commutes with
the identity and anticommutes with an `X` at the same qubit. So `Z`-checks
sense `X`-content. Symmetrically, `X`-checks sense `Z`-content. The
symplectic pairing makes this exact: for a Z-check `(0, w)` and an error
`e`, `ω((0, w), e) = ⟨w, e.X⟩`, which depends only on `e.X`.
-/

/-- Hamming-weight sub-additivity for vectors in `(ZMod 2)^n`. -/
theorem hamming_sub_le (v1 v2 : Fin n → ZMod 2) :
    (Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card ≤
      (Finset.univ.filter (fun i => v1 i ≠ 0)).card +
      (Finset.univ.filter (fun i => v2 i ≠ 0)).card := by
  apply le_trans _ (Finset.card_union_le _ _)
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : v1 i = 0
  · right
    intro h2
    apply hi
    change v1 i - v2 i = 0
    rw [h1, h2, sub_self]
  · left
    exact h1

/-- **X-error detection (CSS):** an X-only error `(v, 0)` of Hamming
weight `< d_X` is either an `X`-stabilizer (in `im(H_X^\top)`, harmless)
or it anticommutes with some Z-check (`v ∉ ker(H_Z)`, detected).

The detecting check is one of the rows of `H_Z`; concretely, `H_Z v ≠ 0`
identifies which Z-check anticommutes with the error. -/
theorem cssX_detect_of_weight_lt
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    {v : Fin n → ZMod 2}
    (h : ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℕ∞) <
      cssXDistance H_X H_Z) :
    v ∈ cssXLogicalSubspace H_X ∨ v ∉ cssXLogicalCarrier H_Z := by
  rw [or_iff_not_imp_left]
  intro h_not_sub h_in_car
  have h_dist_le : cssXDistance H_X H_Z ≤
      ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℕ∞) := by
    unfold cssXDistance
    exact iInf_le_of_le v (iInf_le_of_le h_in_car (iInf_le _ h_not_sub))
  exact absurd h_dist_le (not_le.mpr h)

/-- **Z-error detection (CSS):** a Z-only error `(0, v)` of Hamming
weight `< d_Z` is either a `Z`-stabilizer (in `im(H_Z^\top)`, harmless)
or it anticommutes with some X-check (`v ∉ ker(H_X)`, detected by an
X-check). -/
theorem cssZ_detect_of_weight_lt
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    {v : Fin n → ZMod 2}
    (h : ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℕ∞) <
      cssZDistance H_X H_Z) :
    v ∈ cssZLogicalSubspace H_Z ∨ v ∉ cssZLogicalCarrier H_X := by
  rw [or_iff_not_imp_left]
  intro h_not_sub h_in_car
  have h_dist_le : cssZDistance H_X H_Z ≤
      ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℕ∞) := by
    unfold cssZDistance
    exact iInf_le_of_le v (iInf_le_of_le h_in_car (iInf_le _ h_not_sub))
  exact absurd h_dist_le (not_le.mpr h)

/-- **X-error correction (CSS):** two X-only errors `(v_1, 0)`,
`(v_2, 0)` of Hamming weight `≤ t` with `2t < d_X` and the same
Z-syndrome (same anticommutation pattern with Z-checks, i.e.
`H_Z v_1 = H_Z v_2`) differ by an X-stabilizer.

The Z-syndrome is what the Z-checks (rows of `H_Z`) measure; X-errors
with the same Z-syndrome are indistinguishable by Z-checks, and the
hypothesis `2t < d_X` says any two such errors of weight `≤ t` differ
by an X-stabilizer, so the decoder picks either of them and acts on the
codespace the same way. -/
theorem cssX_correct_of_weights_le
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    {v1 v2 : Fin n → ZMod 2} {t : ℕ}
    (ht : (2 * t : ℕ∞) < cssXDistance H_X H_Z)
    (h1 : (Finset.univ.filter (fun i => v1 i ≠ 0)).card ≤ t)
    (h2 : (Finset.univ.filter (fun i => v2 i ≠ 0)).card ≤ t)
    (h_syn : Matrix.mulVecLin H_Z v1 = Matrix.mulVecLin H_Z v2) :
    v1 - v2 ∈ cssXLogicalSubspace H_X := by
  have h_in_ker : v1 - v2 ∈ cssXLogicalCarrier H_Z := by
    change Matrix.mulVecLin H_Z (v1 - v2) = 0
    rw [map_sub, h_syn, sub_self]
  by_contra h_not_in_sub
  have h_dist_le : cssXDistance H_X H_Z ≤
      ((Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card : ℕ∞) := by
    unfold cssXDistance
    exact iInf_le_of_le (v1 - v2)
      (iInf_le_of_le h_in_ker (iInf_le _ h_not_in_sub))
  have h_wt : (Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card ≤ 2 * t := by
    have hsub := hamming_sub_le v1 v2
    omega
  have h_wt_cast : ((Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card : ℕ∞) ≤
      (2 * t : ℕ∞) := by exact_mod_cast h_wt
  exact absurd (le_trans h_dist_le h_wt_cast) (not_le.mpr ht)

/-- **Z-error correction (CSS):** two Z-only errors with the same
X-syndrome (`H_X v_1 = H_X v_2`) and weight `≤ t` with `2t < d_Z`
differ by a Z-stabilizer.

The X-syndrome is what the X-checks (rows of `H_X`) measure. -/
theorem cssZ_correct_of_weights_le
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    {v1 v2 : Fin n → ZMod 2} {t : ℕ}
    (ht : (2 * t : ℕ∞) < cssZDistance H_X H_Z)
    (h1 : (Finset.univ.filter (fun i => v1 i ≠ 0)).card ≤ t)
    (h2 : (Finset.univ.filter (fun i => v2 i ≠ 0)).card ≤ t)
    (h_syn : Matrix.mulVecLin H_X v1 = Matrix.mulVecLin H_X v2) :
    v1 - v2 ∈ cssZLogicalSubspace H_Z := by
  have h_in_ker : v1 - v2 ∈ cssZLogicalCarrier H_X := by
    change Matrix.mulVecLin H_X (v1 - v2) = 0
    rw [map_sub, h_syn, sub_self]
  by_contra h_not_in_sub
  have h_dist_le : cssZDistance H_X H_Z ≤
      ((Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card : ℕ∞) := by
    unfold cssZDistance
    exact iInf_le_of_le (v1 - v2)
      (iInf_le_of_le h_in_ker (iInf_le _ h_not_in_sub))
  have h_wt : (Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card ≤ 2 * t := by
    have hsub := hamming_sub_le v1 v2
    omega
  have h_wt_cast : ((Finset.univ.filter (fun i => (v1 - v2) i ≠ 0)).card : ℕ∞) ≤
      (2 * t : ℕ∞) := by exact_mod_cast h_wt
  exact absurd (le_trans h_dist_le h_wt_cast) (not_le.mpr ht)

end FTQCLib.CSS

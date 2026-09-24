/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Distance
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.unusedSectionVars false

/-! # C3: Rank and dimension formulas for CSS codes

For a CSS code given by parity-check matrices `H_X` and `H_Z`,

    dim(S_CSS) = rank(H_X) + rank(H_Z),
    dim(L_X)  = dim(L_Z)  = k = n − rank(H_X) − rank(H_Z),
    dim(L(S)) = 2k.

These follow from three facts assembled here:

* `cssXStabilizer ≃ₗ cssXLogicalSubspace` via the X-projection
  `(v, 0) ↦ v` (and Z-side symmetric). Hence `dim(cssXStabilizer) =
  dim(cssXLogicalSubspace)`.
* `dim(cssXLogicalSubspace) = rank(H_X^T) = rank(H_X)` because
  `cssXLogicalSubspace = LinearMap.range (mulVecLin H_X^T)` by
  definition.
* `cssXStabilizer ⊓ cssZStabilizer = ⊥` because the X-side has
  `Z`-coordinate zero, the Z-side has `X`-coordinate zero, and their
  intersection is the zero Pauli.

This file proves:

* **C3a** `pauliXEmbed_injective`, `pauliZEmbed_injective` — the X-only
  and Z-only embeddings.
* **C3b** `cssXStabilizer_eq_map`, `cssZStabilizer_eq_map` — identifying
  the stabilizer rowspans as images of the matrix-level subspaces.
* **C3c** `finrank_cssXStabilizer`, `finrank_cssZStabilizer` —
  `dim(cssXStabilizer) = rank(H_X)` and Z-side.
* **C3d** `cssXStabilizer_inf_cssZStabilizer_eq_bot` — trivial
  intersection.
* **C3e** `finrank_cssStabilizer` — `dim(S_CSS) = rank(H_X) + rank(H_Z)`.
* **C3f** `finrank_cssXLogical`, `finrank_cssZLogical` — logical-space
  dimension formula via rank-nullity on `mulVecLin H_Z` and `H_X`.
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli FTQCLib.Stabilizer Matrix

variable {n r_X r_Z : ℕ}

/-! ## X- and Z-only embeddings -/

/-- The X-only embedding `v ↦ ⟨v, 0⟩` as a linear map. -/
def pauliXEmbed : (Fin n → ZMod 2) →ₗ[ZMod 2] Pauli n where
  toFun v := ⟨v, 0⟩
  map_add' u v := by ext <;> simp
  map_smul' c v := by ext <;> simp

/-- The Z-only embedding `v ↦ ⟨0, v⟩` as a linear map. -/
def pauliZEmbed : (Fin n → ZMod 2) →ₗ[ZMod 2] Pauli n where
  toFun v := ⟨0, v⟩
  map_add' u v := by ext <;> simp
  map_smul' c v := by ext <;> simp

theorem pauliXEmbed_injective : Function.Injective (pauliXEmbed (n := n)) := by
  intro u v h
  exact congrArg Pauli.X h

theorem pauliZEmbed_injective : Function.Injective (pauliZEmbed (n := n)) := by
  intro u v h
  exact congrArg Pauli.Z h

@[simp] lemma pauliXEmbed_apply (v : Fin n → ZMod 2) :
    pauliXEmbed v = ⟨v, 0⟩ := rfl

@[simp] lemma pauliZEmbed_apply (v : Fin n → ZMod 2) :
    pauliZEmbed v = ⟨0, v⟩ := rfl

/-! ## Identifying CSS stabilizer rowspans as images of the matrix-level subspaces -/

/-- **C3b (X-side):** the X-stabilizer rowspan is the image of
`cssXLogicalSubspace` under the X-only embedding. -/
theorem cssXStabilizer_eq_map (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) :
    cssXStabilizer H_X =
      (cssXLogicalSubspace H_X).map pauliXEmbed := by
  apply le_antisymm
  · -- cssXStabilizer ≤ map: for x ∈ cssXStabilizer, x = ⟨x.X, 0⟩ with x.X ∈ subspace
    intro x hx
    refine ⟨x.X, cssXStabilizer_X_mem_subspace H_X hx, ?_⟩
    ext i
    · rfl
    · change (0 : Fin n → ZMod 2) i = x.Z i
      rw [cssXStabilizer_Z_eq_zero hx]
  · -- map ≤ cssXStabilizer: for v ∈ subspace, ⟨v, 0⟩ ∈ cssXStabilizer
    rintro _ ⟨v, hv, rfl⟩
    exact cssXStabilizer_of_X_mem_subspace H_X hv

/-- **C3b (Z-side):** symmetric. -/
theorem cssZStabilizer_eq_map (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    cssZStabilizer H_Z =
      (cssZLogicalSubspace H_Z).map pauliZEmbed := by
  apply le_antisymm
  · intro x hx
    refine ⟨x.Z, cssZStabilizer_Z_mem_subspace H_Z hx, ?_⟩
    ext i
    · change (0 : Fin n → ZMod 2) i = x.X i
      rw [cssZStabilizer_X_eq_zero hx]
    · rfl
  · rintro _ ⟨v, hv, rfl⟩
    exact cssZStabilizer_of_Z_mem_subspace H_Z hv

/-! ## Stabilizer rowspan dimensions -/

/-- **C3c (X-side):** `dim(cssXStabilizer) = rank(H_X)`. -/
theorem finrank_cssXStabilizer (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssXStabilizer H_X) = H_X.rank := by
  rw [cssXStabilizer_eq_map,
    (Submodule.equivMapOfInjective _ pauliXEmbed_injective _).finrank_eq.symm]
  change H_Xᵀ.rank = H_X.rank
  exact Matrix.rank_transpose H_X

/-- **C3c (Z-side):** `dim(cssZStabilizer) = rank(H_Z)`. -/
theorem finrank_cssZStabilizer (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssZStabilizer H_Z) = H_Z.rank := by
  rw [cssZStabilizer_eq_map,
    (Submodule.equivMapOfInjective _ pauliZEmbed_injective _).finrank_eq.symm]
  change H_Zᵀ.rank = H_Z.rank
  exact Matrix.rank_transpose H_Z

/-! ## X-Z block intersection is trivial -/

/-- **C3d:** the X-stabilizer rowspan and the Z-stabilizer rowspan
intersect trivially. An element of the intersection has `Z = 0` (from
the X-side) and `X = 0` (from the Z-side), hence is zero. -/
theorem cssXStabilizer_inf_cssZStabilizer_eq_bot
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    cssXStabilizer H_X ⊓ cssZStabilizer H_Z = ⊥ := by
  apply Submodule.eq_bot_iff _ |>.mpr
  intro x hx
  have hX_Z : x.Z = 0 := cssXStabilizer_Z_eq_zero hx.1
  have hZ_X : x.X = 0 := cssZStabilizer_X_eq_zero hx.2
  ext i
  · rw [hZ_X]; rfl
  · rw [hX_Z]; rfl

/-! ## C3e: dim(cssStabilizer) = rank(H_X) + rank(H_Z) -/

/-- **C3e:** the CSS stabilizer subspace dimension equals the sum of the
X- and Z-check ranks. -/
theorem finrank_cssStabilizer
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssStabilizer H_X H_Z) = H_X.rank + H_Z.rank := by
  have h_inf : Module.finrank (ZMod 2)
      (cssXStabilizer H_X ⊓ cssZStabilizer H_Z : Submodule (ZMod 2) (Pauli n)) = 0 := by
    rw [cssXStabilizer_inf_cssZStabilizer_eq_bot, finrank_bot]
  have h_sum := Submodule.finrank_sup_add_finrank_inf_eq
    (cssXStabilizer H_X) (cssZStabilizer H_Z)
  rw [h_inf, add_zero] at h_sum
  rw [cssStabilizer, h_sum, finrank_cssXStabilizer, finrank_cssZStabilizer]

/-! ## C3f: X/Z-logical space dimensions -/

/-- The X-logical carrier `ker(H_Z) ⊆ (ZMod 2)^n` has dimension
`n − rank(H_Z)`, by rank-nullity on `mulVecLin H_Z`. -/
theorem finrank_cssXLogicalCarrier (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssXLogicalCarrier H_Z) = n - H_Z.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin H_Z)
  rw [show Module.finrank (ZMod 2) (Fin n → ZMod 2) = n from by
    rw [Module.finrank_pi, Fintype.card_fin]] at h
  unfold cssXLogicalCarrier
  -- finrank (range mulVecLin H_Z) = rank H_Z by def
  have h_rank : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin H_Z)) =
      H_Z.rank := rfl
  rw [h_rank] at h
  omega

/-- The Z-logical carrier `ker(H_X)` has dimension `n − rank(H_X)`. -/
theorem finrank_cssZLogicalCarrier (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssZLogicalCarrier H_X) = n - H_X.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin H_X)
  rw [show Module.finrank (ZMod 2) (Fin n → ZMod 2) = n from by
    rw [Module.finrank_pi, Fintype.card_fin]] at h
  unfold cssZLogicalCarrier
  have h_rank : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin H_X)) =
      H_X.rank := rfl
  rw [h_rank] at h
  omega

/-- **C3f (X-side):** the X-logical space has dimension
`k = n − rank(H_X) − rank(H_Z)`. -/
theorem finrank_cssXLogical
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} (h : IsCSSPair H_X H_Z) :
    Module.finrank (ZMod 2) (cssXLogical H_X H_Z) =
      n - H_X.rank - H_Z.rank := by
  unfold cssXLogical
  -- Rank-nullity on the quotient (cssXLogicalCarrier H_Z) / (subspace.comap subtype)
  have h_sum := Submodule.finrank_quotient_add_finrank
    ((cssXLogicalSubspace H_X).comap (cssXLogicalCarrier H_Z).subtype)
  -- finrank carrier = n - rank H_Z
  rw [finrank_cssXLogicalCarrier] at h_sum
  -- finrank (subspace.comap subtype) = finrank subspace via comapSubtypeEquivOfLe
  have h_le : cssXLogicalSubspace H_X ≤ cssXLogicalCarrier H_Z :=
    cssXLogicalSubspace_le_cssXLogicalCarrier h
  have h_comap_eq : Module.finrank (ZMod 2)
      ((cssXLogicalSubspace H_X).comap (cssXLogicalCarrier H_Z).subtype) =
      Module.finrank (ZMod 2) (cssXLogicalSubspace H_X) :=
    (Submodule.comapSubtypeEquivOfLe h_le).finrank_eq
  -- finrank subspace = rank H_X
  have h_sub : Module.finrank (ZMod 2) (cssXLogicalSubspace H_X) = H_X.rank := by
    unfold cssXLogicalSubspace
    change H_Xᵀ.rank = H_X.rank
    exact Matrix.rank_transpose H_X
  rw [h_comap_eq, h_sub] at h_sum
  omega

/-- **C3f (Z-side):** the Z-logical space has dimension
`k = n − rank(H_X) − rank(H_Z)`. -/
theorem finrank_cssZLogical
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} (h : IsCSSPair H_X H_Z) :
    Module.finrank (ZMod 2) (cssZLogical H_X H_Z) =
      n - H_X.rank - H_Z.rank := by
  unfold cssZLogical
  have h_sum := Submodule.finrank_quotient_add_finrank
    ((cssZLogicalSubspace H_Z).comap (cssZLogicalCarrier H_X).subtype)
  rw [finrank_cssZLogicalCarrier] at h_sum
  have h_le : cssZLogicalSubspace H_Z ≤ cssZLogicalCarrier H_X :=
    cssZLogicalSubspace_le_cssZLogicalCarrier h
  have h_comap_eq : Module.finrank (ZMod 2)
      ((cssZLogicalSubspace H_Z).comap (cssZLogicalCarrier H_X).subtype) =
      Module.finrank (ZMod 2) (cssZLogicalSubspace H_Z) :=
    (Submodule.comapSubtypeEquivOfLe h_le).finrank_eq
  have h_sub : Module.finrank (ZMod 2) (cssZLogicalSubspace H_Z) = H_Z.rank := by
    unfold cssZLogicalSubspace
    change H_Zᵀ.rank = H_Z.rank
    exact Matrix.rank_transpose H_Z
  rw [h_comap_eq, h_sub] at h_sum
  omega

end FTQCLib.CSS

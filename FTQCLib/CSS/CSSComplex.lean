/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Rank

set_option linter.unusedSectionVars false

/-! # The two standard CSS definitions coincide

A CSS code is presented two standard ways, and this file proves they
name the same object:

* **commutation form** (`IsCSSPair`): a pair `(H_X, H_Z)` with
  `H_X * H_Zᵀ = 0`;
* **classical-codes form** (Calderbank–Shor–Steane): the dual code
  `C_Zᵀ = im H_Zᵀ` is contained in the X-code `C_X = ker H_X`.

* `isCSSPair_iff_dual_containment` — the equivalence
  `H_X H_Zᵀ = 0  ↔  im H_Zᵀ ⊆ ker H_X` (commutation ⟺ dual-containment).
* `cssZLogical` is, by its definition in `FTQCLib.CSS.Logical`, the classical
  quotient `C_X / C_Zᵀ = ker H_X / im H_Zᵀ`; `cssZLogical_finrank_eq_classical`
  records that its dimension is the classical CSS count `dim C_X − dim C_Zᵀ`,
  which `finrank_cssZLogical` already equals `n − rk H_X − rk H_Z`.
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli FTQCLib.Stabilizer Matrix

variable {n r_X r_Z : ℕ}

/-- Converse of `cssZLogicalSubspace_le_cssZLogicalCarrier`: if the dual
Z-code `im H_Zᵀ` lies inside the X-code `ker H_X`, the CSS commutation
`H_X H_Zᵀ = 0` holds. -/
theorem isCSSPair_of_subspace_le
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h : cssZLogicalSubspace H_Z ≤ cssZLogicalCarrier H_X) :
    IsCSSPair H_X H_Z := by
  have hcomp : (Matrix.mulVecLin H_X).comp (Matrix.mulVecLin H_Zᵀ) = 0 := by
    rw [← LinearMap.range_le_ker_iff]; exact h
  rw [← Matrix.mulVecLin_mul] at hcomp
  have key : ∀ v, (H_X * H_Zᵀ) *ᵥ v = 0 := by
    intro v
    have e := LinearMap.congr_fun hcomp v
    simp only [Matrix.mulVecLin_apply, LinearMap.zero_apply] at e
    exact e
  unfold IsCSSPair
  ext i j
  have e := congrFun (key (Pi.single j (1 : ZMod 2))) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at e
  simpa using e

/-- **CSS commutation ⟺ classical dual-containment.** The operator-form
condition `H_X H_Zᵀ = 0` and the classical-codes condition
`C_Zᵀ = im H_Zᵀ ⊆ ker H_X = C_X` define the same set of CSS codes. -/
theorem isCSSPair_iff_dual_containment
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} :
    IsCSSPair H_X H_Z ↔ cssZLogicalSubspace H_Z ≤ cssZLogicalCarrier H_X :=
  ⟨cssZLogicalSubspace_le_cssZLogicalCarrier, isCSSPair_of_subspace_le⟩

/-- `dim (im H_Zᵀ) = rank H_Z` (the dual Z-code has dimension `rk H_Z`). -/
theorem finrank_cssZLogicalSubspace
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssZLogicalSubspace H_Z) = H_Z.rank := by
  have h : Module.finrank (ZMod 2) (cssZLogicalSubspace H_Z) = (H_Zᵀ).rank := rfl
  rw [h, Matrix.rank_transpose]

/-- **Homological count = classical count.** The Z-logical space
`cssZLogical = ker H_X / im H_Zᵀ = C_X / C_Zᵀ` has dimension
`dim C_X − dim C_Zᵀ`, the classical CSS logical-qubit count. -/
theorem cssZLogical_finrank_eq_classical
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} (h : IsCSSPair H_X H_Z) :
    Module.finrank (ZMod 2) (cssZLogical H_X H_Z) =
      Module.finrank (ZMod 2) (cssZLogicalCarrier H_X) -
        Module.finrank (ZMod 2) (cssZLogicalSubspace H_Z) := by
  rw [finrank_cssZLogical h, finrank_cssZLogicalCarrier, finrank_cssZLogicalSubspace]

end FTQCLib.CSS

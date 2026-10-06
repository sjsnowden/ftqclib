/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Rank
import FTQCLib.CSS.SurfaceCode

/-!
# Check: T34, the toric and planar surface codes

T34.2's witness rows (`docs/STEPS.md`, the unit, phase 2) on the frozen statement of
`FTQCLib/CSS/SurfaceCode.lean`, all at `L = 3`. Every row is about an object a T34 headline names:
the toric code `toricCode 3` and its complex (`toricCode_k`, `toricCode_distance`,
`toricCode_independentGens`), and the planar code `planarCode 3` and its relative complex
(`planarCode_k`, `planarCode_distance`). No row uses a T34 headline. Each `k` is computed from the
code's own check matrices, `k = n - rank H_X - rank H_Z` (`finrank_cssZLogical`, from
`CSS/Rank.lean`), with each rank certified by two matrix identities decided by the kernel: a
factorisation `M = E F` through `r` columns bounds it above, and a section `A M B = 1` of size `r`
bounds it below (`rank_eq_of_factor_of_section`, below). A string is shown not to be a boundary by a
cocycle that meets it once: a cocycle `c` has `c ⬝ᵥ ∂ w = 0` for every `w`.

The rows:

* **The `L = 3` toric code (agreement).** `k = 2`, from the ranks `8` of its `9 × 18` star and
  plaquette matrices, as Dennis et al. count (`2(L² - 1)` independent checks on `2L²` qubits); the
  horizontal loop `torusRowLoop 3` is a cycle of weight `3` that is not a boundary, since the
  horizontal edges leaving the column `x = 0` (a cut, a cocycle) meet it in one edge.
* **The distance's edge, `D3` (discriminating).** At `L = 3` every cycle of weight at most `2` is a
  boundary (it is zero: the star matrix's columns are nonzero and pairwise distinct), while the
  weight-`3` cycle `torusRowLoop 3` is not. The distance is `3`, not `2` and not `4`.
* **The `L = 3` planar code (agreement).** `k = 1`, from the ranks `6` of its `6 × 13` star and
  plaquette matrices, as Dennis et al. count (`L² + (L - 1)² - 2L(L - 1)`); the rough-to-rough
  string `planarZString 3` is a relative cycle of weight `3` that is not a relative boundary, since
  the smooth-to-smooth string `planarXString 3`, a relative cocycle, meets it in one edge.
* **The full star set is dependent (discriminating).** On the `L = 3` torus all nine stars sum to
  zero, and so do all nine plaquettes, so the nine stars are not linearly independent: the full set
  is not the independent generating set `toricGens`, which drops one of each.
* **The `L = 3` toric code is inhabited (inhabitation).** `toricCode 3` is a CSS pair with a nonzero
  `H_X`: the hypotheses of the CSS theorems hold together on a concrete object.

Scope (standard 7.3): the four rows above are about `L = 3` alone and prove nothing about other
sizes.

General facts a later step may need, stated privately here (they belong in `FTQCLib.CSS.Rank`):
`rank_eq_of_factor_of_section` and `not_mem_range_of_dotProduct`; and in
`FTQCLib.CSS.BasedComplex`: `eq_zero_of_mulVec_eq_zero_of_card_le_two`.
-/

namespace FTQCLib.CSS.SurfaceCodeCheck

-- mutant: torusStep_swap | FTQCLib/CSS/SurfaceCode.lean | ![(1, 0), (0, 1)] j | ![(0, 1), (1, 0)] j

open FTQCLib.CSS Matrix

/-! ## Axiom sweep — every theorem of `FTQCLib.CSS.SurfaceCode` -/

/-- info: 'FTQCLib.CSS.sum_torusVertexEdge_mul_torusEdgeFace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.sum_torusVertexEdge_mul_torusEdgeFace

/-- info: 'FTQCLib.CSS.toricCode_eq_koszul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.toricCode_eq_koszul

/-- info: 'FTQCLib.CSS.toricCode_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.toricCode_k

/-- info: 'FTQCLib.CSS.toricCode_independentGens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.toricCode_independentGens

/-- info: 'FTQCLib.CSS.toricCode_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.toricCode_distance

/-- info: 'FTQCLib.CSS.onRoughBoundary_of_d_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.onRoughBoundary_of_d_ne_zero

/-- info: 'FTQCLib.CSS.planarCode_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.planarCode_k

/-- info: 'FTQCLib.CSS.planarCode_independentGens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.planarCode_independentGens

/-- info: 'FTQCLib.CSS.planarCode_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.planarCode_distance

/-! ## Ranks and boundaries over `ZMod 2` -/

/-- The `0/1` matrix whose row `i` has its ones at the columns listed in `rows[i]`. -/
def ofSupports {m n : ℕ} (rows : List (List ℕ)) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if (j : ℕ) ∈ rows.getD i [] then 1 else 0

/-- The matrix that selects the columns `columns[k]`, `k < r`, of a matrix it multiplies on the
right. -/
def columnSelection {n r : ℕ} (columns : List ℕ) : Matrix (Fin n) (Fin r) (ZMod 2) :=
  Matrix.of fun j k => if (j : ℕ) = columns.getD k 0 then 1 else 0

/-- A matrix that factors through `r` columns and has a section of size `r` has rank `r`. -/
private theorem rank_eq_of_factor_of_section {m n r : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (E : Matrix (Fin m) (Fin r) (ZMod 2)) (F : Matrix (Fin r) (Fin n) (ZMod 2))
    (A : Matrix (Fin r) (Fin m) (ZMod 2)) (B : Matrix (Fin n) (Fin r) (ZMod 2))
    (h_factor : E * F = M) (h_section : A * M * B = 1) : M.rank = r := by
  apply le_antisymm
  · rw [← h_factor]
    exact (rank_mul_le_left E F).trans (rank_le_width E)
  · have h_one : (1 : Matrix (Fin r) (Fin r) (ZMod 2)).rank = r := by
      rw [rank_one, Fintype.card_fin]
    rw [← h_one, ← h_section]
    exact (rank_mul_le_left (A * M) B).trans (rank_mul_le_right A M)

/-- A vector met an odd number of times by a cocycle of `M` is not in the range of `M`. -/
private theorem not_mem_range_of_dotProduct {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (c v : Fin m → ZMod 2) (h_cocycle : c ᵥ* M = 0) (h_meet : c ⬝ᵥ v ≠ 0) :
    v ∉ LinearMap.range M.mulVecLin := by
  rintro ⟨w, rfl⟩
  apply h_meet
  rw [Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, h_cocycle, zero_dotProduct]

/-- A nonzero element of `ZMod 2` is `1`. -/
private theorem eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

/-- If the columns of `M` are nonzero and pairwise distinct, then the only vector of weight at most
`2` in its kernel is zero. -/
private theorem eq_zero_of_mulVec_eq_zero_of_card_le_two {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) (ZMod 2)) (h_column : ∀ a, (fun s => M s a) ≠ 0)
    (h_pair : ∀ a b, a ≠ b → (fun s => M s a + M s b) ≠ 0) (v : Fin n → ZMod 2)
    (h_kernel : M *ᵥ v = 0) (h_weight : (Finset.univ.filter fun j => v j ≠ 0).card ≤ 2) :
    v = 0 := by
  set support := Finset.univ.filter fun j => v j ≠ 0 with h_support
  have h_indicator : v = fun j => if j ∈ support then 1 else 0 := by
    funext j
    by_cases h : v j = 0
    · simp [h_support, h]
    · simp [h_support, eq_one_of_ne_zero _ h]
  have h_apply : M *ᵥ v = fun s => ∑ j ∈ support, M s j := by
    funext s
    rw [h_indicator]
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h_apply] at h_kernel
  have h_cases : support.card = 0 ∨ support.card = 1 ∨ support.card = 2 := by omega
  rcases h_cases with h_zero | h_one | h_two
  · rw [Finset.card_eq_zero] at h_zero
    rw [h_indicator, h_zero]
    funext j
    simp
  · obtain ⟨a, h_a⟩ := Finset.card_eq_one.mp h_one
    rw [h_a] at h_kernel
    simp only [Finset.sum_singleton] at h_kernel
    exact absurd h_kernel (h_column a)
  · obtain ⟨a, b, h_ne, h_ab⟩ := Finset.card_eq_two.mp h_two
    rw [h_ab] at h_kernel
    simp only [Finset.sum_pair h_ne] at h_kernel
    exact absurd h_kernel (h_pair a b h_ne)

/-! ## The `L = 3` toric code -/

/-- The horizontal edges leaving the column `x = 0` of the `L = 3` torus: a cut across the
horizontal direction, a cocycle. -/
def torusColumnCut : Fin ((torusComplex 3).cells 1) → ZMod 2 := fun ℓ =>
  if ((torusEdgeEquiv 3).symm ℓ).1 = 0 ∧ ((torusEdgeEquiv 3).symm ℓ).2.1 = 0 then 1 else 0

/-- The star matrix of the `L = 3` torus has rank `8`: its nine rows sum to zero, and eight of
its columns carry an invertible `8 × 8` block. -/
private theorem toricThree_rank_X : (toricCode 3).1.rank = 8 :=
  rank_eq_of_factor_of_section _
    (ofSupports [[0], [1], [2], [3], [4], [5], [6], [7], [0, 1, 2, 3, 4, 5, 6, 7]])
    (ofSupports [[0, 6, 9, 11], [1, 7, 9, 10], [2, 8, 10, 11], [0, 3, 12, 14], [1, 4, 12, 13],
      [2, 5, 13, 14], [3, 6, 15, 17], [4, 7, 15, 16]])
    (ofSupports [[3, 6], [4, 7], [0, 1, 2, 3, 4, 6, 7], [6], [7], [0, 1, 2, 3, 4, 5, 6, 7],
      [0, 3, 6], [0, 1, 3, 4, 6, 7]])
    (columnSelection [0, 1, 2, 3, 4, 5, 9, 10]) (by decide +kernel) (by decide +kernel)

/-- The plaquette matrix of the `L = 3` torus has rank `8`. -/
private theorem toricThree_rank_Z : (toricCode 3).2.rank = 8 :=
  rank_eq_of_factor_of_section _
    (ofSupports [[0], [1], [2], [3], [4], [5], [6], [7], [0, 1, 2, 3, 4, 5, 6, 7]])
    (ofSupports [[0, 1, 9, 12], [1, 2, 10, 13], [0, 2, 11, 14], [3, 4, 12, 15], [4, 5, 13, 16],
      [3, 5, 14, 17], [6, 7, 9, 15], [7, 8, 10, 16]])
    (ofSupports [[2], [1], [5], [4], [0, 1, 2, 3, 4, 5, 6, 7], [7], [0, 1, 2, 3, 4, 5],
      [3, 4, 5]])
    (columnSelection [0, 1, 3, 4, 6, 7, 9, 12]) (by decide +kernel) (by decide +kernel)

/-- `torusRowLoop 3` is a cycle of weight `3` that is not a boundary: the column cut is a cocycle
and meets it in one edge. -/
private theorem toricThree_rowLoop :
    torusRowLoop 3 ∈ (torusComplex 3).cycles 1 ∧
      torusRowLoop 3 ∉ (torusComplex 3).boundaries 1 ∧
      (Finset.univ.filter fun ℓ => torusRowLoop 3 ℓ ≠ 0).card = 3 := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    decide +kernel
  · exact not_mem_range_of_dotProduct _ torusColumnCut _ (by decide +kernel) (by decide +kernel)

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h90d1802c273b
-- row: agreement
theorem toricThree_k_and_rowLoop :
    Module.finrank (ZMod 2) (cssZLogical (toricCode 3).1 (toricCode 3).2) = 2 ∧
      torusRowLoop 3 ∈ (torusComplex 3).cycles 1 ∧
      torusRowLoop 3 ∉ (torusComplex 3).boundaries 1 ∧
      (Finset.univ.filter fun ℓ => torusRowLoop 3 ℓ ≠ 0).card = 3 := by
  have h_pair : IsCSSPair (toricCode 3).1 (toricCode 3).2 := cssOfComplex_isCSSPair _ 1
  refine ⟨?_, toricThree_rowLoop⟩
  rw [finrank_cssZLogical h_pair, toricThree_rank_X, toricThree_rank_Z]

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h1c1a0d539819
-- row: discriminating D3
theorem toricThree_distance_edge :
    (∀ v ∈ (torusComplex 3).cycles 1,
        (Finset.univ.filter fun ℓ => v ℓ ≠ 0).card ≤ 2 → v ∈ (torusComplex 3).boundaries 1) ∧
      torusRowLoop 3 ∈ (torusComplex 3).cycles 1 ∧
      torusRowLoop 3 ∉ (torusComplex 3).boundaries 1 ∧
      (Finset.univ.filter fun ℓ => torusRowLoop 3 ℓ ≠ 0).card = 3 := by
  refine ⟨fun v h_cycle h_weight => ?_, toricThree_rowLoop⟩
  rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h_cycle
  rw [eq_zero_of_mulVec_eq_zero_of_card_le_two _ (by decide +kernel) (by decide +kernel) v
    h_cycle h_weight]
  exact Submodule.zero_mem _

/-! ## The `L = 3` planar code -/

/-- The interior vertices of the `L = 3` grid, the cells of degree `0` outside the rough
boundaries, in increasing order. -/
def planarVertexCell : Fin ((roughBoundary 3).cellSet 0)ᶜ.card → Fin ((gridComplex 3).cells 0) :=
  fun b => Fin.cast (by decide +kernel)
    ((![1, 2, 5, 6, 9, 10] : Fin 6 → Fin 12) (Fin.cast (by decide +kernel) b))

/-- The edges of the `L = 3` grid outside the rough boundaries, in increasing order. -/
def planarEdgeCell : Fin ((roughBoundary 3).cellSet 1)ᶜ.card → Fin ((gridComplex 3).cells 1) :=
  fun b => Fin.cast (by decide +kernel)
    ((![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 14, 15] : Fin 13 → Fin 17)
      (Fin.cast (by decide +kernel) b))

/-- The faces of the `L = 3` grid, none on the rough boundaries, in increasing order. -/
def planarFaceCell : Fin ((roughBoundary 3).cellSet 2)ᶜ.card → Fin ((gridComplex 3).cells 2) :=
  fun b => Fin.cast (by decide +kernel) b

/-- `otherCell 0` is `planarVertexCell`: both are increasing onto the cells outside the rough
boundaries, and such a map is unique. -/
private theorem otherCell_zero : ⇑((roughBoundary 3).otherCell 0) = planarVertexCell :=
  (Finset.orderEmbOfFin_unique rfl (f := planarVertexCell) (by decide +kernel)
    (by unfold StrictMono; decide +kernel)).symm

/-- `otherCell 1` is `planarEdgeCell`. -/
private theorem otherCell_one : ⇑((roughBoundary 3).otherCell 1) = planarEdgeCell :=
  (Finset.orderEmbOfFin_unique rfl (f := planarEdgeCell) (by decide +kernel)
    (by unfold StrictMono; decide +kernel)).symm

/-- `otherCell 2` is `planarFaceCell`. -/
private theorem otherCell_two : ⇑((roughBoundary 3).otherCell 2) = planarFaceCell :=
  (Finset.orderEmbOfFin_unique rfl (f := planarFaceCell) (by decide +kernel)
    (by unfold StrictMono; decide +kernel)).symm

/-- The star matrix of the `L = 3` patch, on the grid's cells. -/
private theorem planarThree_X_eq :
    (planarCode 3).1 = ((gridComplex 3).d 0).submatrix planarVertexCell planarEdgeCell := by
  show ((gridComplex 3).d 0).submatrix ((roughBoundary 3).otherCell 0)
    ((roughBoundary 3).otherCell 1) = _
  rw [otherCell_zero, otherCell_one]

/-- The plaquette matrix of the `L = 3` patch, on the grid's cells. -/
private theorem planarThree_Z_eq :
    (planarCode 3).2 = (((gridComplex 3).d 1).submatrix planarEdgeCell planarFaceCell)ᵀ := by
  show (((gridComplex 3).d 1).submatrix ((roughBoundary 3).otherCell 1)
    ((roughBoundary 3).otherCell 2))ᵀ = _
  rw [otherCell_one, otherCell_two]

/-- `planarZString 3` on the grid's cells. -/
private theorem planarZString_eq : planarZString 3 = fun b =>
    if ((gridCellEquiv 3 1 (planarEdgeCell b)).1 : ℕ) = 0 ∧
      ((gridCellEquiv 3 1 (planarEdgeCell b)).2.1 : ℕ) = 0 then 1 else 0 := by
  unfold planarZString
  rw [otherCell_one]
  rfl

/-- `planarXString 3` on the grid's cells. -/
private theorem planarXString_eq : planarXString 3 = fun b =>
    if ((gridCellEquiv 3 1 (planarEdgeCell b)).1 : ℕ) = 0 ∧
      ((gridCellEquiv 3 1 (planarEdgeCell b)).2.2 : ℕ) = 0 then 1 else 0 := by
  unfold planarXString
  rw [otherCell_one]
  rfl

/-- The star matrix of the `L = 3` patch has rank `6`: its six rows are independent. -/
private theorem planarThree_rank_X : (planarCode 3).1.rank = 6 := by
  rw [planarThree_X_eq]
  exact rank_eq_of_factor_of_section _ (ofSupports [[0], [1], [2], [3], [4], [5]])
    (ofSupports [[0, 1, 9], [1, 2, 10], [3, 4, 9, 11], [4, 5, 10, 12], [6, 7, 11], [7, 8, 12]])
    (ofSupports [[0, 1], [1], [2, 3], [3], [4, 5], [5]])
    (columnSelection [0, 1, 3, 4, 6, 7]) (by decide +kernel) (by decide +kernel)

/-- The plaquette matrix of the `L = 3` patch has rank `6`: its six rows are independent. -/
private theorem planarThree_rank_Z : (planarCode 3).2.rank = 6 := by
  rw [planarThree_Z_eq]
  exact rank_eq_of_factor_of_section _ (ofSupports [[0], [1], [2], [3], [4], [5]])
    (ofSupports [[0, 3, 9], [1, 4, 9, 10], [2, 5, 10], [3, 6, 11], [4, 7, 11, 12], [5, 8, 12]])
    (ofSupports [[0, 3], [1, 4], [2, 5], [3], [4], [5]])
    (columnSelection [0, 1, 2, 3, 4, 5]) (by decide +kernel) (by decide +kernel)

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hc1165ba8cd2d
-- row: agreement
theorem planarThree_k_and_zString :
    Module.finrank (ZMod 2) (cssZLogical (planarCode 3).1 (planarCode 3).2) = 1 ∧
      planarZString 3 ∈ (planarComplex 3).cycles 1 ∧
      planarZString 3 ∉ (planarComplex 3).boundaries 1 ∧
      (Finset.univ.filter fun ℓ => planarZString 3 ℓ ≠ 0).card = 3 := by
  have h_pair : IsCSSPair (planarCode 3).1 (planarCode 3).2 := cssOfComplex_isCSSPair _ 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [finrank_cssZLogical h_pair, planarThree_rank_X, planarThree_rank_Z]
    decide +kernel
  · rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    change (planarCode 3).1 *ᵥ planarZString 3 = 0
    rw [planarThree_X_eq, planarZString_eq]
    decide +kernel
  · change planarZString 3 ∉ LinearMap.range ((planarCode 3).2)ᵀ.mulVecLin
    refine not_mem_range_of_dotProduct _ (planarXString 3) _ ?_ ?_
    · rw [planarThree_Z_eq, planarXString_eq]
      decide +kernel
    · rw [planarXString_eq, planarZString_eq]
      decide +kernel
  · rw [planarZString_eq]
    decide +kernel

/-! ## The torus's relations -/

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h90d1802c273b
-- row: discriminating
theorem toricThree_stars_dependent :
    ∑ s, (toricCode 3).1 s = 0 ∧ ∑ P, (toricCode 3).2 P = 0 ∧
      ¬ LinearIndependent (ZMod 2) (cssXGen (toricCode 3).1) := by
  have h_stars : ∑ s, (toricCode 3).1 s = 0 := by decide +kernel
  refine ⟨h_stars, by decide +kernel, ?_⟩
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun _ => 1, ?_, ⟨0, by decide⟩, one_ne_zero⟩
  calc ∑ s, (1 : ZMod 2) • cssXGen (toricCode 3).1 s
      = pauliXEmbed (∑ s, (toricCode 3).1 s) := by
        simp only [one_smul, map_sum]
        rfl
    _ = 0 := by rw [h_stars, map_zero]

/-! ## The `L = 3` toric code is inhabited -/

-- row: inhabitation
theorem toricThree_isCSSPair_nontrivial :
    IsCSSPair (toricCode 3).1 (toricCode 3).2 ∧ (toricCode 3).1 ≠ 0 :=
  ⟨cssOfComplex_isCSSPair _ 1, by decide +kernel⟩

end FTQCLib.CSS.SurfaceCodeCheck

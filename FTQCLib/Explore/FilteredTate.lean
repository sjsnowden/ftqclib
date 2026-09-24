/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Explore.FactorizationHomology
import FTQCLib.Frame.CurvatureObstruction
import FTQCLib.Frame.MobiusProductTower

set_option linter.style.longLine false

/-! # The filtered Tate computation: from constants to every level

`FTQCLib.Explore.FactorizationHomology` proved the two ends of the dichotomy: the Tate complex of
the shift action is globally exact (free action), yet alive on the constants sector (trivial
action). This file computes the middle — the whole level filtration — by **diagonalizing the shift
in the Möbius basis**.

**The two laws** (everything below is bookkeeping over them):

* `mobiusCoeff_funcDerivG_of_notMem` — `i ∉ S`: `c_S(D_i f) = c_{S∪{i}}(f)` (the difference moves a
  coefficient one slot down);
* `mobiusCoeff_funcDerivG_of_mem`  — `i ∈ S`: `c_S(D_i f) = −2·c_S(f)` (the `D² = −2D` defect, seen
  per-coefficient).

**The graded action is not trivial.** The natural guess "the shift acts trivially on the associated
graded" is FALSE over `ℤ/4`: on top-degree coefficients the shift acts by the **sign character** —
`c_S(T_i f) = −c_S(f)` on slots containing `i`, `= c_S(f)` off them (`mobiusCoeff_shiftOp_top`). The
trivial action only appears on the `i ∉ S` slots (which is why the constants sector, `S = ∅`,
behaved that way in `FactorizationHomology`). Over `𝔽₂`-valued phases `−1 = 1` and the graded action
IS trivial — the twist is exactly the `−2`/band arithmetic again, the interaction–precision coupling
of the degree×resolution lattice appearing in the filtration.

**Results.**

* Filtration preservation: `D`, `T`, `N` all preserve `DegLE d` (`degLE_funcDerivG` etc.) — the
  level filtration is a filtration of the Tate complex.
* The graded action: on top coefficients the norm is `0` on slots containing `i` and multiplication
  by `2` off them (`mobiusCoeff_normOp_top`); the shift is the sign character
  (`mobiusCoeff_shiftOp_top`).
* **The obstruction, sharp:** any within-degree witness `N g = f` (`deg g ≤ d`) forces every top
  coefficient of `f` (off `i`) to be doubled: `c_S(f) = c_S(g) + c_S(g)`
  (`top_two_divisible_of_normOp_witness`). Hence the relative class is nonzero whenever some top
  coefficient is not 2-divisible (`relative_class_of_top_not_divisible`).
  `FactorizationHomology.constants_relative_class` falls out as the `d = 0`, `S = ∅` case
  (`constants_relative_class_revisited` + the literal corollary `constants_relative_class'`).
* **The death schedule:** the hyperplane-section witness has degree exactly one higher —
  `c_T(witness) = −c_{T∖{i}}(f)` on slots containing `i`, `= c_T(f)` off
  (`mobiusCoeff_hyperplane_witness`), so `DegLE d f ⟹ DegLE (d+1) witness`
  (`degLE_hyperplane_witness`) and every degree-`d` relative class dies at degree `d + 1`
  (`class_dies_one_up`). Combined with the obstruction: the class of `f` lives at level `d` iff a
  top coefficient resists division by 2, and its lifetime is exactly one degree.
* **The whole-group face:** for the full translation action of `(𝔽₂)ⁿ` (the regular, free action)
  the zeroth Tate group vanishes — every invariant is a full norm, with the delta-function witness
  (`invariant_is_fullNorm`).

An exploratory file, not part of the `FTQCLib` target. -/

namespace FTQCLib.Explore.FilteredTate

open FTQCLib.Hierarchy.BooleanMobius FTQCLib.Explore.LieClosure FTQCLib.Explore.FactorizationHomology

variable {n : ℕ} {A : Type*} [AddCommGroup A]

/-! ## Additivity of the Möbius coefficient over an arbitrary `AddCommGroup`

(The existing `mobiusCoeff_add` lemmas live over `CommRing R` / `ZMod 4`; the Tate complex runs over any
`AddCommGroup` codomain, so we prove the additive version here.) -/

theorem funcDerivG_add (i : Fin n) (f g : (Fin n → ZMod 2) → A) :
    funcDerivG i (f + g) = funcDerivG i f + funcDerivG i g := by
  funext v
  simp only [funcDerivG_apply, Pi.add_apply]
  abel

theorem funcDerivSubset_add (S : Finset (Fin n)) (f g : (Fin n → ZMod 2) → A) :
    funcDerivSubset S (f + g) = funcDerivSubset S f + funcDerivSubset S g := by
  induction S using Finset.induction_on with
  | empty => simp [funcDerivSubset_empty]
  | @insert j S hj ih =>
      rw [funcDerivSubset_insert hj, funcDerivSubset_insert hj, funcDerivSubset_insert hj, ih,
        funcDerivG_add]

theorem mobiusCoeff_add' (S : Finset (Fin n)) (f g : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (f + g) = mobiusCoeff S f + mobiusCoeff S g := by
  simp only [mobiusCoeff_apply, funcDerivSubset_add, Pi.add_apply]

theorem mobiusCoeff_zero (S : Finset (Fin n)) :
    mobiusCoeff S (0 : (Fin n → ZMod 2) → A) = 0 := by
  rw [mobiusCoeff_eq_alt_sum]
  simp

/-! ## The diagonalization: `D`, `T`, `N` in the Möbius basis -/

/-- Iterated differences commute with a single difference (order-independence, subset form). -/
theorem funcDerivSubset_funcDerivG (S : Finset (Fin n)) (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset S (funcDerivG i f) = funcDerivG i (funcDerivSubset S f) := by
  induction S using Finset.induction_on with
  | empty => simp [funcDerivSubset_empty]
  | @insert j S hj ih =>
      rw [funcDerivSubset_insert hj, funcDerivSubset_insert hj, ih]
      exact funcDerivG_comm j i _

/-- `D² = −2D`, restated from the factorization `D(D+2) = 0` (`FTQCLib/Frame/CurvatureObstruction.lean`). -/
theorem funcDerivG_sq (i : Fin n) (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG i f) = -((2 : ℤ) • funcDerivG i f) :=
  eq_neg_of_add_eq_zero_left (FTQCLib.Frame.Curvature.funcDerivG_factorization i f)

/-- **First law:** off-slot, the difference moves a Möbius coefficient one slot down:
`c_S(D_i f) = c_{S∪{i}}(f)` for `i ∉ S`. -/
theorem mobiusCoeff_funcDerivG_of_notMem {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (funcDerivG i f) = mobiusCoeff (insert i S) f := by
  rw [mobiusCoeff_apply, mobiusCoeff_apply, funcDerivSubset_insert hi, funcDerivSubset_funcDerivG]

/-- **Second law:** on-slot, the difference is multiplication by `−2`:
`c_S(D_i f) = −2·c_S(f)` for `i ∈ S`. This is `D² = −2D` seen per-coefficient. -/
theorem mobiusCoeff_funcDerivG_of_mem {i : Fin n} {S : Finset (Fin n)} (hi : i ∈ S)
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (funcDerivG i f) = -((2 : ℤ) • mobiusCoeff S f) := by
  obtain ⟨S', hi', rfl⟩ : ∃ S', i ∉ S' ∧ S = insert i S' :=
    ⟨S.erase i, Finset.notMem_erase i S, (Finset.insert_erase hi).symm⟩
  rw [mobiusCoeff_apply, mobiusCoeff_apply, funcDerivSubset_insert hi',
    funcDerivSubset_insert hi', funcDerivSubset_funcDerivG, funcDerivG_sq]
  simp

/-- Coefficients of a shift-invariant phase vanish on every slot containing `i`
(`D_i f = 0` ⟺ `f` is independent of the `i`-th coordinate). -/
theorem mobiusCoeff_eq_zero_of_deriv_zero {i : Fin n} {f : (Fin n → ZMod 2) → A}
    (hf : funcDerivG i f = 0) {S : Finset (Fin n)} (hi : i ∈ S) :
    mobiusCoeff S f = 0 := by
  obtain ⟨S', hi', rfl⟩ : ∃ S', i ∉ S' ∧ S = insert i S' :=
    ⟨S.erase i, Finset.notMem_erase i S, (Finset.insert_erase hi).symm⟩
  have h := mobiusCoeff_funcDerivG_of_notMem hi' f
  rw [hf, mobiusCoeff_zero] at h
  exact h.symm

/-- The shift on coefficients, off-slot: upper-triangular, `c_S(T_i f) = c_S(f) + c_{S∪{i}}(f)`. -/
theorem mobiusCoeff_shiftOp_of_notMem {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (shiftOp i f) = mobiusCoeff S f + mobiusCoeff (insert i S) f := by
  rw [shiftOp_eq_add_funcDerivG, mobiusCoeff_add', mobiusCoeff_funcDerivG_of_notMem hi]

/-- The shift on coefficients, on-slot: **the sign character**, `c_S(T_i f) = −c_S(f)`. -/
theorem mobiusCoeff_shiftOp_of_mem {i : Fin n} {S : Finset (Fin n)} (hi : i ∈ S)
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (shiftOp i f) = -(mobiusCoeff S f) := by
  rw [shiftOp_eq_add_funcDerivG, mobiusCoeff_add', mobiusCoeff_funcDerivG_of_mem hi, two_zsmul]
  abel

/-- The norm on coefficients, on-slot: **exactly zero** — slots containing `i` are unreachable by `N_i`. -/
theorem mobiusCoeff_normOp_of_mem {i : Fin n} {S : Finset (Fin n)} (hi : i ∈ S)
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (normOp i f) = 0 := by
  have h : normOp i f = shiftOp i f + f := rfl
  rw [h, mobiusCoeff_add', mobiusCoeff_shiftOp_of_mem hi, neg_add_cancel]

/-- The norm on coefficients, off-slot: `c_S(N_i f) = c_{S∪{i}}(f) + 2·c_S(f)`. -/
theorem mobiusCoeff_normOp_of_notMem {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (f : (Fin n → ZMod 2) → A) :
    mobiusCoeff S (normOp i f) = mobiusCoeff (insert i S) f + (2 : ℤ) • mobiusCoeff S f := by
  have h : normOp i f = shiftOp i f + f := rfl
  rw [h, mobiusCoeff_add', mobiusCoeff_shiftOp_of_notMem hi, two_zsmul]
  abel

/-! ## The level filtration and its preservation -/

/-- Möbius degree ≤ `d` over an arbitrary `AddCommGroup` codomain. Agrees definitionally with the
`CommRing` version `FTQCLib.Frame.MobiusTower.MobiusDegLE` (see `degLE_iff_mobiusDegLE`). -/
def DegLE (d : ℕ) (f : (Fin n → ZMod 2) → A) : Prop :=
  ∀ S : Finset (Fin n), d < S.card → mobiusCoeff S f = 0

/-- The compatibility with the existing ring-coefficient degree predicate: definitional. -/
theorem degLE_iff_mobiusDegLE {N : ℕ} {R : Type*} [CommRing R] (d : ℕ)
    (f : (Fin N → ZMod 2) → R) :
    DegLE d f ↔ FTQCLib.Frame.MobiusTower.MobiusDegLE d f := Iff.rfl

/-- `D_i` preserves the level filtration. -/
theorem degLE_funcDerivG {d : ℕ} {f : (Fin n → ZMod 2) → A} (hf : DegLE d f) (i : Fin n) :
    DegLE d (funcDerivG i f) := by
  intro S hS
  by_cases hi : i ∈ S
  · rw [mobiusCoeff_funcDerivG_of_mem hi, hf S hS, smul_zero, neg_zero]
  · rw [mobiusCoeff_funcDerivG_of_notMem hi,
      hf _ (by rw [Finset.card_insert_of_notMem hi]; omega)]

/-- `T_i` preserves the level filtration. -/
theorem degLE_shiftOp {d : ℕ} {f : (Fin n → ZMod 2) → A} (hf : DegLE d f) (i : Fin n) :
    DegLE d (shiftOp i f) := by
  intro S hS
  by_cases hi : i ∈ S
  · rw [mobiusCoeff_shiftOp_of_mem hi, hf S hS, neg_zero]
  · rw [mobiusCoeff_shiftOp_of_notMem hi, hf S hS,
      hf _ (by rw [Finset.card_insert_of_notMem hi]; omega), add_zero]

/-- `N_i` preserves the level filtration. -/
theorem degLE_normOp {d : ℕ} {f : (Fin n → ZMod 2) → A} (hf : DegLE d f) (i : Fin n) :
    DegLE d (normOp i f) := by
  intro S hS
  by_cases hi : i ∈ S
  · rw [mobiusCoeff_normOp_of_mem hi]
  · rw [mobiusCoeff_normOp_of_notMem hi, hf S hS,
      hf _ (by rw [Finset.card_insert_of_notMem hi]; omega), smul_zero, add_zero]

/-! ## The graded action: the sign character, not the trivial action -/

/-- **The graded shift action is the sign character.** On a top-degree coefficient (`|S| = d`), the shift
acts by `−1` on slots containing `i` and by `+1` off them. Over `ℤ/4` this is NOT trivial — a
"trivial graded action" holds only off-slot (and identically over `𝔽₂`, where `−1 = 1`). -/
theorem mobiusCoeff_shiftOp_top {d : ℕ} {f : (Fin n → ZMod 2) → A} (hf : DegLE d f)
    {S : Finset (Fin n)} (hS : S.card = d) (i : Fin n) :
    mobiusCoeff S (shiftOp i f) = if i ∈ S then -(mobiusCoeff S f) else mobiusCoeff S f := by
  by_cases hi : i ∈ S
  · rw [if_pos hi, mobiusCoeff_shiftOp_of_mem hi]
  · rw [if_neg hi, mobiusCoeff_shiftOp_of_notMem hi,
      hf (insert i S) (by rw [Finset.card_insert_of_notMem hi]; omega), add_zero]

/-- **The graded norm:** `0` on slots containing `i`, multiplication by `2` off them. The `d = 0` case
(`S = ∅`, always off-slot) is `normOp_constFn`: "the norm is doubling on constants". -/
theorem mobiusCoeff_normOp_top {d : ℕ} {f : (Fin n → ZMod 2) → A} (hf : DegLE d f)
    {S : Finset (Fin n)} (hS : S.card = d) (i : Fin n) :
    mobiusCoeff S (normOp i f) = if i ∈ S then 0 else (2 : ℤ) • mobiusCoeff S f := by
  by_cases hi : i ∈ S
  · rw [if_pos hi, mobiusCoeff_normOp_of_mem hi]
  · rw [if_neg hi, mobiusCoeff_normOp_of_notMem hi,
      hf (insert i S) (by rw [Finset.card_insert_of_notMem hi]; omega), zero_add]

/-! ## The obstruction: within-degree witnesses force 2-divisibility at the top -/

/-- **The sharp obstruction.** If `N_i g = f` with `deg g ≤ d`, then every top coefficient of `f` on a slot
off `i` is doubled: `c_S(f) = c_S(g) + c_S(g)`. (On slots containing `i`, `c_S(f) = 0` automatically.) -/
theorem top_two_divisible_of_normOp_witness {d : ℕ} {i : Fin n}
    {f g : (Fin n → ZMod 2) → A} (hg : DegLE d g) (hN : normOp i g = f)
    {S : Finset (Fin n)} (hS : S.card = d) (hiS : i ∉ S) :
    mobiusCoeff S f = mobiusCoeff S g + mobiusCoeff S g := by
  have h := congrArg (mobiusCoeff S) hN
  rw [mobiusCoeff_normOp_of_notMem hiS,
    hg _ (by rw [Finset.card_insert_of_notMem hiS]; omega), zero_add, two_zsmul] at h
  exact h.symm

/-- **The relative Tate class at level `d` is nonzero** whenever some top coefficient of `f` (off `i`)
is not 2-divisible: no witness of degree ≤ `d` exists. -/
theorem relative_class_of_top_not_divisible {d : ℕ} {i : Fin n} {f : (Fin n → ZMod 2) → A}
    {S : Finset (Fin n)} (hS : S.card = d) (hiS : i ∉ S)
    (hnd : ∀ a : A, mobiusCoeff S f ≠ a + a) :
    ¬ ∃ g, DegLE d g ∧ normOp i g = f := by
  rintro ⟨g, hg, hN⟩
  exact hnd _ (top_two_divisible_of_normOp_witness hg hN hS hiS)

/-- Constants have degree 0. -/
theorem degLE_zero_constFn (c : A) : DegLE 0 (constFn c : (Fin n → ZMod 2) → A) := by
  intro S hS
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega)
  exact mobiusCoeff_eq_zero_of_deriv_zero (funcDerivG_constFn j c) hj

/-- **The constants class of `FactorizationHomology`, re-derived as the `d = 0`, `S = ∅` case** — and
strengthened: no witness of ANY degree-0 shape exists, not just no constant one. -/
theorem constants_relative_class_revisited (i : Fin n) :
    ¬ ∃ g : (Fin n → ZMod 2) → ZMod 4, DegLE 0 g ∧ normOp i g = constFn 1 := by
  refine relative_class_of_top_not_divisible (S := (∅ : Finset (Fin n))) rfl
    (Finset.notMem_empty i) ?_
  intro a
  rw [mobiusCoeff_apply, funcDerivSubset_empty]
  change (1 : ZMod 4) ≠ a + a
  revert a
  decide

/-- The literal statement of `FactorizationHomology.constants_relative_class` as a corollary of the
filtered version. -/
theorem constants_relative_class' (i : Fin n) :
    ¬ ∃ c : ZMod 4, normOp i (constFn c : (Fin n → ZMod 2) → ZMod 4) = constFn 1 := by
  rintro ⟨c, hc⟩
  exact constants_relative_class_revisited i ⟨constFn c, degLE_zero_constFn c, hc⟩

/-! ## The death schedule: every relative class dies exactly one degree up -/

/-- The Möbius coefficients of the hyperplane-section witness `v ↦ if v i = 0 then f v else 0`:
`c_T = c_T(f)` off `i`, `c_T = −c_{T∖{i}}(f)` on `i`. So the witness costs exactly one slot in the
`i`-direction — degree `d + 1` from degree `d`. -/
theorem mobiusCoeff_hyperplane_witness (i : Fin n) (f : (Fin n → ZMod 2) → A)
    (T : Finset (Fin n)) :
    mobiusCoeff T (fun v => if v i = 0 then f v else 0)
      = if i ∈ T then -(mobiusCoeff (T.erase i) f) else mobiusCoeff T f := by
  have hchar : ∀ U : Finset (Fin n), charFn U i = 0 ↔ i ∉ U := by
    intro U
    rw [charFn_apply]
    by_cases hU : i ∈ U
    · simp [hU]
    · simp [hU]
  by_cases hi : i ∈ T
  · -- on-slot: split the powerset of `T = insert i T'` and kill the `i ∈ U` half
    obtain ⟨T', hi', rfl⟩ : ∃ T', i ∉ T' ∧ T = insert i T' :=
      ⟨T.erase i, Finset.notMem_erase i T, (Finset.insert_erase hi).symm⟩
    rw [if_pos hi, Finset.erase_insert hi']
    rw [mobiusCoeff_eq_alt_sum, mobiusCoeff_eq_alt_sum, Finset.powerset_insert]
    rw [Finset.sum_union (by
      rw [Finset.disjoint_left]
      intro U hU hU'
      obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU'
      exact hi' (Finset.mem_powerset.mp hU (Finset.mem_insert_self i W)))]
    have himage : ∑ U ∈ Finset.image (insert i) T'.powerset,
        ((-1 : ℤ) ^ ((insert i T').card - U.card)) • (if charFn U i = 0 then f (charFn U) else 0)
          = 0 := by
      refine Finset.sum_eq_zero fun U hU => ?_
      obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU
      rw [if_neg (by rw [hchar]; exact fun h => h (Finset.mem_insert_self i W)), smul_zero]
    rw [himage, add_zero]
    have hstep : ∀ U ∈ T'.powerset,
        ((-1 : ℤ) ^ ((insert i T').card - U.card)) • (if charFn U i = 0 then f (charFn U) else 0)
          = -(((-1 : ℤ) ^ (T'.card - U.card)) • f (charFn U)) := by
      intro U hU
      have hUsub := Finset.mem_powerset.mp hU
      have hUcard : U.card ≤ T'.card := Finset.card_le_card hUsub
      have hUi : i ∉ U := fun h => hi' (hUsub h)
      rw [if_pos ((hchar U).mpr hUi), Finset.card_insert_of_notMem hi',
        show T'.card + 1 - U.card = (T'.card - U.card) + 1 by omega, pow_succ, mul_neg_one,
        neg_smul]
    rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib]
  · -- off-slot: every `U ⊆ T` misses `i`, the indicator is invisible
    rw [if_neg hi, mobiusCoeff_eq_alt_sum, mobiusCoeff_eq_alt_sum]
    refine Finset.sum_congr rfl fun U hU => ?_
    have hUi : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    rw [if_pos ((hchar U).mpr hUi)]

/-- The hyperplane-section witness raises degree by exactly one. -/
theorem degLE_hyperplane_witness {d : ℕ} {f : (Fin n → ZMod 2) → A} (hf : DegLE d f) (i : Fin n) :
    DegLE (d + 1) (fun v => if v i = 0 then f v else 0) := by
  intro T hT
  rw [mobiusCoeff_hyperplane_witness]
  by_cases hi : i ∈ T
  · rw [if_pos hi, hf _ (by rw [Finset.card_erase_of_mem hi]; omega), neg_zero]
  · rw [if_neg hi]
    exact hf _ (by omega)

private lemma coord_shift' (i : Fin n) (v : Fin n → ZMod 2) :
    (v + (Pi.single i 1 : Fin n → ZMod 2)) i = v i + 1 := by
  simp [Pi.single_eq_same]

private lemma zmod2_cases' (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- The hyperplane-section witness is a genuine norm-preimage (the construction of
`exists_normOp_of_deriv_zero`, restated with the explicit witness so its degree is visible). -/
theorem normOp_hyperplane_witness (i : Fin n) (f : (Fin n → ZMod 2) → A)
    (hf : funcDerivG i f = 0) :
    normOp i (fun v => if v i = 0 then f v else 0) = f := by
  have hinv : ∀ v, f (v + Pi.single i 1) = f v := fun v => by
    have h := congrFun hf v
    simp only [funcDerivG_apply, Pi.zero_apply] at h
    exact sub_eq_zero.mp h
  funext v
  simp only [normOp_apply]
  rcases zmod2_cases' (v i) with hv | hv
  · rw [if_neg (by rw [coord_shift', hv]; decide), if_pos hv, zero_add]
  · rw [if_pos (by rw [coord_shift', hv]; decide), if_neg (by rw [hv]; decide), add_zero, hinv]

/-- **The death schedule.** Every shift-invariant phase of degree ≤ `d` is a norm of something of degree
≤ `d + 1`: the relative class at level `d` dies exactly one level up, by an explicit witness. Together with
`relative_class_of_top_not_divisible` (it cannot die at level `d` when a top coefficient resists 2), the
lifetime of a filtered Tate class is exactly one degree. -/
theorem class_dies_one_up {i : Fin n} {f : (Fin n → ZMod 2) → A}
    (hf : funcDerivG i f = 0) {d : ℕ} (hfd : DegLE d f) :
    ∃ g, DegLE (d + 1) g ∧ normOp i g = f :=
  ⟨fun v => if v i = 0 then f v else 0, degLE_hyperplane_witness hfd i,
    normOp_hyperplane_witness i f hf⟩

/-! ## The whole-group face: the regular action of `(𝔽₂)ⁿ` is Tate-acyclic in degree 0 -/

/-- The norm of the **full** translation group: `(N_G f)(v) = Σ_{w ∈ (𝔽₂)ⁿ} f(v + w)`. -/
noncomputable def fullNorm (f : (Fin n → ZMod 2) → A) : (Fin n → ZMod 2) → A :=
  fun v => ∑ w : Fin n → ZMod 2, f (v + w)

/-- **Invariants are full norms** (`Ĥ⁰` of the regular action vanishes): a phase invariant under every
shift is the full norm of a delta function. The whole-group form of the freeness used in
`FactorizationHomology` — one statement packaging all `n` directions. -/
theorem invariant_is_fullNorm {f : (Fin n → ZMod 2) → A}
    (hf : ∀ w v, f (v + w) = f v) :
    ∃ g, fullNorm g = f := by
  classical
  refine ⟨fun v => if v = 0 then f 0 else 0, ?_⟩
  funext v
  have hself : ∀ u : Fin n → ZMod 2, u + u = 0 := by
    intro u
    funext j
    have : ∀ x : ZMod 2, x + x = 0 := by decide
    simp [this]
  have hcond : ∀ w : Fin n → ZMod 2, v + w = 0 → w = v := by
    intro w h
    have h2 : v + (v + w) = v + 0 := by rw [h]
    rw [← add_assoc, hself v, zero_add, add_zero] at h2
    exact h2
  have hterm : ∀ w : Fin n → ZMod 2,
      ((if v + w = 0 then f 0 else 0 : A)) = if w = v then f 0 else 0 := by
    intro w
    by_cases hw : w = v
    · rw [if_pos hw, if_pos (by rw [hw]; exact hself v)]
    · rw [if_neg hw, if_neg (fun h => hw (hcond w h))]
  calc fullNorm (fun v => if v = 0 then f 0 else 0) v
      = ∑ w : Fin n → ZMod 2, if w = v then f 0 else 0 :=
        Finset.sum_congr rfl fun w _ => hterm w
    _ = f 0 := by
        rw [Finset.sum_ite_eq' Finset.univ v fun _ => f 0, if_pos (Finset.mem_univ v)]
    _ = f v := by
        have h0 := hf v 0
        rw [zero_add] at h0
        exact h0.symm

/-! ## The synthesis: the relative Tate group computed exactly

The obstruction above says within-degree witnesses force doubled top coefficients. This part proves the
converse by synthesizing the witness from prescribed Möbius coefficients, giving the full iff
(`normOp_witness_degLE_iff`): **the relative class of `f` at level `d` vanishes iff every top coefficient
off `i` is doubled.** The top coefficients mod 2 are a complete invariant of the level-`d` relative Tate
group — over `ℤ/4` the group is `∏_{|S| = d, i ∉ S} ℤ/2`, at every level and every `n`. -/

/-- The Möbius "monomial": the `A`-valued indicator of `S ⊆ supp v` — the basis function synthesizing a
single prescribed coefficient. -/
def basisFn (S : Finset (Fin n)) (a : A) : (Fin n → ZMod 2) → A :=
  fun v => if S ⊆ FTQCLib.Codes.supp v then a else 0

/-- `(−1)^(k−j) = (−1)^k · (−1)^j` for `j ≤ k`. -/
private lemma neg_one_pow_sub {k j : ℕ} (hj : j ≤ k) :
    ((-1 : ℤ)) ^ (k - j) = (-1) ^ k * (-1) ^ j := by
  have h1 : ((-1 : ℤ)) ^ (k - j) * (-1) ^ j = (-1) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have h2 : ((-1 : ℤ)) ^ j * (-1) ^ j = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j, rfl⟩
  calc ((-1 : ℤ)) ^ (k - j) = (-1) ^ (k - j) * ((-1) ^ j * (-1) ^ j) := by rw [h2, mul_one]
    _ = ((-1) ^ (k - j) * (-1) ^ j) * (-1) ^ j := by ring
    _ = (-1) ^ k * (-1) ^ j := by rw [h1]

/-- **The delta property:** `basisFn S a` has Möbius coefficient `a` at `S` and `0` at every other slot. -/
theorem mobiusCoeff_basisFn (S T : Finset (Fin n)) (a : A) :
    mobiusCoeff T (basisFn S a) = if T = S then a else 0 := by
  classical
  rw [mobiusCoeff_eq_alt_sum]
  simp only [basisFn, supp_charFn]
  by_cases hST : S ⊆ T
  · have hsplit : ∀ U ∈ T.powerset,
        ((-1 : ℤ) ^ (T.card - U.card)) • (if S ⊆ U then a else 0)
          = if S ⊆ U then ((-1 : ℤ) ^ (T.card - U.card)) • a else 0 := by
      intro U _
      split <;> simp
    rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter]
    have himg : T.powerset.filter (fun U => S ⊆ U)
        = (T \ S).powerset.image (fun W => S ∪ W) := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      constructor
      · rintro ⟨hUT, hSU⟩
        exact ⟨U \ S, Finset.sdiff_subset_sdiff hUT (Finset.Subset.refl S),
          Finset.union_sdiff_of_subset hSU⟩
      · rintro ⟨W, hW, rfl⟩
        exact ⟨Finset.union_subset hST (hW.trans Finset.sdiff_subset),
          Finset.subset_union_left⟩
    have hinj : ∀ W₁ ∈ (T \ S).powerset, ∀ W₂ ∈ (T \ S).powerset,
        S ∪ W₁ = S ∪ W₂ → W₁ = W₂ := by
      have hd : ∀ W ∈ (T \ S).powerset, Disjoint S W := fun W hW =>
        Finset.disjoint_left.mpr fun x hxS hxW =>
          (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hW hxW)).2 hxS
      intro W₁ h₁ W₂ h₂ h
      have hc := congrArg (· \ S) h
      simpa [Finset.union_sdiff_cancel_left (hd W₁ h₁),
        Finset.union_sdiff_cancel_left (hd W₂ h₂)] using hc
    rw [himg, Finset.sum_image hinj]
    have hterm : ∀ W ∈ (T \ S).powerset,
        ((-1 : ℤ) ^ (T.card - (S ∪ W).card)) • a
          = ((-1 : ℤ) ^ (T \ S).card) • (((-1 : ℤ) ^ W.card) • a) := by
      intro W hW
      have hWsub := Finset.mem_powerset.mp hW
      have hdisj : Disjoint S W := Finset.disjoint_left.mpr fun x hxS hxW =>
        (Finset.mem_sdiff.mp (hWsub hxW)).2 hxS
      have hcard : (S ∪ W).card = S.card + W.card := Finset.card_union_of_disjoint hdisj
      have hsd : (T \ S).card = T.card - S.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hST]
      have hSle : S.card ≤ T.card := Finset.card_le_card hST
      have hWle : W.card ≤ (T \ S).card := Finset.card_le_card hWsub
      rw [hcard, show T.card - (S.card + W.card) = (T \ S).card - W.card from by omega,
        neg_one_pow_sub hWle, mul_smul]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.sum_smul,
      Finset.sum_powerset_neg_one_pow_card]
    by_cases hTS' : T = S
    · subst hTS'
      simp
    · have hne : ¬(T \ S = ∅) := fun h =>
        hTS' (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h) hST)
      rw [if_neg hne, if_neg hTS', zero_smul, smul_zero]
  · rw [if_neg (fun h : T = S => hST (by rw [h]))]
    refine Finset.sum_eq_zero fun U hU => ?_
    rw [if_neg (fun hSU => hST (hSU.trans (Finset.mem_powerset.mp hU))), smul_zero]

/-- Two phases with the same Möbius coefficients are equal (coefficient extensionality). -/
theorem funext_of_mobiusCoeff_eq {f g : (Fin n → ZMod 2) → A}
    (h : ∀ S, mobiusCoeff S f = mobiusCoeff S g) : f = g := by
  funext v
  rw [eq_sum_mobiusCoeff f v, eq_sum_mobiusCoeff g v]
  exact Finset.sum_congr rfl fun S _ => h S

/-- Möbius coefficients of finite sums (`AddCommGroup` codomain). -/
theorem mobiusCoeff_sum' {α : Type*} (s : Finset α) (h : α → (Fin n → ZMod 2) → A)
    (S : Finset (Fin n)) :
    mobiusCoeff S (∑ x ∈ s, h x) = ∑ x ∈ s, mobiusCoeff S (h x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mobiusCoeff_zero]
  | @insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mobiusCoeff_add', ih]

/-- The synthesized norm-preimage: prescribed halves on the top slots, coefficient-raising
(`S ↦ S ∪ {i}`) on the lower slots. -/
noncomputable def syntheticWitness (i : Fin n) (f : (Fin n → ZMod 2) → A) (d : ℕ)
    (half : Finset (Fin n) → A) : (Fin n → ZMod 2) → A :=
  (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = d ∧ i ∉ S),
      basisFn S (half S))
  + (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card < d ∧ i ∉ S),
      basisFn (insert i S) (mobiusCoeff S f))

/-- The coefficients of the synthesized witness, slot by slot. -/
theorem mobiusCoeff_syntheticWitness (i : Fin n) (f : (Fin n → ZMod 2) → A) (d : ℕ)
    (half : Finset (Fin n) → A) (R : Finset (Fin n)) :
    mobiusCoeff R (syntheticWitness i f d half)
      = (if R.card = d ∧ i ∉ R then half R else 0)
        + (if i ∈ R ∧ (R.erase i).card < d then mobiusCoeff (R.erase i) f else 0) := by
  classical
  rw [syntheticWitness, mobiusCoeff_add', mobiusCoeff_sum', mobiusCoeff_sum']
  congr 1
  · rw [Finset.sum_congr rfl fun S _ => mobiusCoeff_basisFn S R (half S),
      Finset.sum_ite_eq _ R half]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · by_cases hiR : i ∈ R
    · have hcong : ∀ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card < d ∧ i ∉ S),
          mobiusCoeff R (basisFn (insert i S) (mobiusCoeff S f))
            = if R.erase i = S then mobiusCoeff S f else 0 := by
        intro S hS
        obtain ⟨-, hiS⟩ := (Finset.mem_filter.mp hS).2
        rw [mobiusCoeff_basisFn]
        by_cases hRS : R = insert i S
        · rw [if_pos hRS, if_pos (by rw [hRS]; exact Finset.erase_insert hiS)]
        · rw [if_neg hRS, if_neg (fun h => hRS (by rw [← h, Finset.insert_erase hiR]))]
      rw [Finset.sum_congr rfl hcong,
        Finset.sum_ite_eq _ (R.erase i) (fun S => mobiusCoeff S f)]
      simp [hiR]
    · rw [Finset.sum_eq_zero, if_neg (fun h => hiR h.1)]
      intro S hS
      rw [mobiusCoeff_basisFn,
        if_neg (fun h => hiR (by rw [h]; exact Finset.mem_insert_self i S))]

/-- **The synthesis:** if every top coefficient of `f` off `i` is doubled, a within-degree norm-preimage
exists — built explicitly from the halves and the raised lower coefficients. -/
theorem exists_normOp_witness_of_top_divisible {d : ℕ} {i : Fin n}
    {f : (Fin n → ZMod 2) → A} (hf : funcDerivG i f = 0) (hfd : DegLE d f)
    (hdiv : ∀ S : Finset (Fin n), S.card = d → i ∉ S → ∃ a : A, mobiusCoeff S f = a + a) :
    ∃ g, DegLE d g ∧ normOp i g = f := by
  classical
  have hchoice : ∀ S : Finset (Fin n), ∃ a : A,
      S.card = d → i ∉ S → mobiusCoeff S f = a + a := by
    intro S
    by_cases hS : S.card = d ∧ i ∉ S
    · obtain ⟨a, ha⟩ := hdiv S hS.1 hS.2
      exact ⟨a, fun _ _ => ha⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hS⟩
  choose half hhalf using hchoice
  refine ⟨syntheticWitness i f d half, ?_, ?_⟩
  · intro T hT
    rw [mobiusCoeff_syntheticWitness,
      if_neg (fun h => absurd h.1 (by omega)),
      if_neg (fun h => absurd h.2 (by rw [Finset.card_erase_of_mem h.1]; omega)), add_zero]
  · apply funext_of_mobiusCoeff_eq
    intro T
    by_cases hiT : i ∈ T
    · rw [mobiusCoeff_normOp_of_mem hiT, mobiusCoeff_eq_zero_of_deriv_zero hf hiT]
    · rw [mobiusCoeff_normOp_of_notMem hiT, mobiusCoeff_syntheticWitness,
        mobiusCoeff_syntheticWitness]
      have h1 : ¬((insert i T).card = d ∧ i ∉ insert i T) :=
        fun h => h.2 (Finset.mem_insert_self i T)
      have h2 : (insert i T).erase i = T := Finset.erase_insert hiT
      simp only [h2]
      rw [if_neg h1]
      have hmem : i ∈ insert i T := Finset.mem_insert_self i T
      rcases lt_trichotomy T.card d with hlt | heq | hgt
      · rw [if_pos ⟨hmem, hlt⟩, if_neg (fun h => absurd h.1 (by omega)),
          if_neg (fun h => hiT h.1)]
        simp
      · rw [if_neg (fun h => absurd h.2 (by omega)), if_pos ⟨heq, hiT⟩,
          if_neg (fun h => hiT h.1), hhalf T heq hiT, two_zsmul]
        abel
      · rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega)),
          if_neg (fun h => hiT h.1), hfd T (by omega)]
        simp

/-- **The relative Tate group at level `d`, computed exactly.** For a shift-invariant `f` of degree ≤ `d`:
a norm-preimage of degree ≤ `d` exists **iff** every top coefficient of `f` on a slot off `i` is doubled.
The top coefficients mod doubling are a complete invariant of the level-`d` relative class — over `ℤ/4` the
relative Tate group is `∏_{|S| = d, i ∉ S} ℤ/2`, at every level and every `n`. The constants class of
`FactorizationHomology` is the `d = 0` point of this computation; `class_dies_one_up` is its lifetime. -/
theorem normOp_witness_degLE_iff {d : ℕ} {i : Fin n} {f : (Fin n → ZMod 2) → A}
    (hf : funcDerivG i f = 0) (hfd : DegLE d f) :
    (∃ g, DegLE d g ∧ normOp i g = f)
      ↔ ∀ S : Finset (Fin n), S.card = d → i ∉ S → ∃ a : A, mobiusCoeff S f = a + a := by
  constructor
  · rintro ⟨g, hg, hN⟩ S hS hiS
    exact ⟨mobiusCoeff S g, top_two_divisible_of_normOp_witness hg hN hS hiS⟩
  · exact exists_normOp_witness_of_top_divisible hf hfd

/-! ## The Jennings comparison

Compared with Jennings (1941): the frame's phase functions are the group algebra `A[(𝔽₂)ⁿ]`, the
Möbius basis is Jennings's weighted basis at `p = 2` (squarefree products, Thm 3.2), and the slot
counts match his Poincaré series `(1+x)ⁿ` (Thm 3.7). The identification below: **the level
filtration is detected by squarefree derivative products over any coefficients** — `DegLE d f` iff
every `funcDerivSubset S f` with `|S| > d` vanishes identically. Over `𝔽₂`-valued phases,
`D² = −2D = 0` makes squarefree products generate the augmentation powers, so there the frame's
level filtration IS the Jennings/dimension-subgroup filtration. Over `ℤ/2^m` the two diverge by
exactly the band arithmetic (`D² = −2D ≠ 0`: the ideal powers impose the 2-divisibility staircase,
not the bare degree); the identification of the augmentation filtration with the
degree×resolution staircase is not formalized here. -/

/-- **The iterated diagonalization law:** `c_T(D^S f) = (−2)^{|T∩S|} · c_{T∪S}(f)` — the two single-step
laws, closed under iteration. -/
theorem mobiusCoeff_funcDerivSubset (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → A)
    (T : Finset (Fin n)) :
    mobiusCoeff T (funcDerivSubset S f)
      = ((-2 : ℤ) ^ (T ∩ S).card) • mobiusCoeff (T ∪ S) f := by
  classical
  induction S using Finset.induction_on generalizing T with
  | empty => simp [funcDerivSubset_empty]
  | @insert i S hi ih =>
      rw [funcDerivSubset_insert hi]
      by_cases hiT : i ∈ T
      · have hins : T ∩ insert i S = insert i (T ∩ S) := Finset.inter_insert_of_mem hiT
        have hcup : T ∪ insert i S = T ∪ S := by
          rw [Finset.union_insert, Finset.insert_eq_self.mpr (Finset.mem_union_left S hiT)]
        rw [mobiusCoeff_funcDerivG_of_mem hiT, ih T, hins, hcup,
          Finset.card_insert_of_notMem (fun h => hi (Finset.mem_inter.mp h).2),
          ← neg_smul, ← mul_smul, ← pow_succ']
      · have hins : T ∩ insert i S = T ∩ S := Finset.inter_insert_of_notMem hiT
        have h2 : (insert i T) ∩ S = T ∩ S := Finset.insert_inter_of_notMem hi
        have hcup : insert i T ∪ S = T ∪ insert i S := by
          rw [Finset.insert_union, Finset.union_insert]
        rw [mobiusCoeff_funcDerivG_of_notMem hiT, ih (insert i T), h2, hcup, hins]

/-- **The level filtration is detected by squarefree derivative products** (over any coefficient group):
`deg f ≤ d` iff every iterated difference in more than `d` distinct directions vanishes identically. Over
`𝔽₂`-valued phases this IS the Jennings/augmentation-power filtration (`D² = 0` there); over `ℤ/2^m` the
ideal powers are strictly finer (the 2-divisibility staircase). -/
theorem degLE_iff_funcDerivSubset_eq_zero (d : ℕ) (f : (Fin n → ZMod 2) → A) :
    DegLE d f ↔ ∀ S : Finset (Fin n), d < S.card → funcDerivSubset S f = 0 := by
  constructor
  · intro hf S hS
    refine funext_of_mobiusCoeff_eq fun T => ?_
    rw [mobiusCoeff_funcDerivSubset, mobiusCoeff_zero,
      hf (T ∪ S) (lt_of_lt_of_le hS (Finset.card_le_card Finset.subset_union_right)), smul_zero]
  · intro h S hS
    rw [mobiusCoeff_apply, h S hS]
    rfl

end FTQCLib.Explore.FilteredTate

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.PolarForm
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Check: the polar matrix and the polarization law

Witness rows for `FTQCLib.Hierarchy.PolarForm`, then the axiom rows. The witness rows, by property:

* **Precision zero.** Every polar matrix is zero at `m = 0` (`polarMatrix_precision_zero`), and
  at `m = 0` two distinct matrices carry the same datum (`two_datum_precision_zero`): the `1 ≤ m`
  of `eq_of_isShiftDatum_top` is load-bearing.
* **Precision one.** The `S` exponent's matrix is zero (`polarMatrix_sGate_one`) while the unit
  the `2 ≤ m` reading gives is not (`single_ne_zero_fin_one`): the `2 ≤ m` of `polarMatrix_sGate`
  is load-bearing.
* **The mixed `S·CZ` form at precision two** has the matrix `!![1, 1; 1, 0]`
  (`polarMatrix_mixed`): a non-alternating rank-two matrix in one reading, which neither
  instance theorem covers.
* **The square cell.** `X₀²` at precision two is not multilinear, has level at most two, and has
  the zero matrix (`not_isMultilinear_czGate_self`, `polarMatrix_czGate_self`).
* **The level-three boundary.** `T` at precision three (`not_isShiftDatum_T`) and `CS` at
  precision two (`not_isShiftDatum_CS`) carry no datum for any matrix: their shifts take values
  off the top-bit lattice. Together with the built cubic row of `AffineDifferenceCheck` this is
  the boundary of the class in the frame's own arithmetic.

`decide` runs through neither `MvPolynomial.coeff` nor `DiagPhase.eval`; the coefficient rows
are `rw` rows, and the evaluation rows rewrite to concrete values before deciding.
-/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial Matrix

/-! ## Witness rows -/

/-- At precision zero every polar matrix is zero. -/
theorem polarMatrix_precision_zero {n : ℕ} (D : DiagPhase n 0) : polarMatrix D = 0 := by
  haveI : Subsingleton (ZMod (2 ^ 0)) := by
    rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
  ext i j
  by_cases h : i = j
  · subst h
    rw [polarMatrix_apply_self, if_pos (Subsingleton.elim _ _), Matrix.zero_apply]
  · rw [polarMatrix_apply_of_ne _ h, if_pos (Subsingleton.elim _ _), Matrix.zero_apply]

/-- At precision zero the zero function carries the datum of every matrix: two distinct matrices
carry it, so uniqueness needs `1 ≤ m`. -/
theorem two_datum_precision_zero :
    IsShiftDatum (fun _ : Fin 1 → ZMod 2 => (0 : ZMod (2 ^ 0)))
        (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) ⊤
      ∧ IsShiftDatum (fun _ : Fin 1 → ZMod 2 => (0 : ZMod (2 ^ 0)))
        (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) ⊤
      ∧ (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) ≠ 1 := by
  haveI : Subsingleton (ZMod (2 ^ 0)) := by
    rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
  refine ⟨fun v _ => ⟨0, fun w => Subsingleton.elim _ _⟩,
    fun v _ => ⟨0, fun w => Subsingleton.elim _ _⟩, ?_⟩
  decide

/-- The unit the `2 ≤ m` reading of `S` gives is not the zero matrix `polarMatrix_sGate_one`
reads at precision one. -/
theorem single_ne_zero_fin_one :
    (Matrix.single (0 : Fin 1) 0 (1 : ZMod 2)) ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  rw [Matrix.single_apply_same, Matrix.zero_apply] at this
  exact one_ne_zero this

/-- The mixed `S·CZ` exponent at precision two. -/
noncomputable abbrev mixedSCZ : DiagPhase 2 2 := sGate 2 0 + czGate 2 0 1

theorem coeff_single_mixedSCZ (j : Fin 2) :
    mixedSCZ.coeff (Finsupp.single j 1) = if (0 : Fin 2) = j then 1 else 0 := by
  rw [coeff_add, coeff_single_sGate, czGate_eq_monomial, coeff_monomial,
    if_neg (Ne.symm (single_ne_single_add_single (by decide)))]
  fin_cases j <;> simp

theorem polarMatrix_mixed_00 : polarMatrix mixedSCZ 0 0 = 1 := by
  rw [polarMatrix_apply_self, coeff_single_mixedSCZ, if_pos rfl,
    if_neg (by decide : (2 : ZMod (2 ^ 2)) * 1 ≠ 0)]

theorem polarMatrix_mixed_01 : polarMatrix mixedSCZ 0 1 = 1 := by
  rw [polarMatrix_apply_of_ne _ (by decide), coeff_add, coeff_pair_sGate _ _ (by decide),
    czGate_eq_monomial, coeff_monomial, if_pos rfl, zero_add,
    if_neg (by decide : (2 : ZMod (2 ^ 2)) ^ (2 - 1) ≠ 0)]

theorem polarMatrix_mixed_10 : polarMatrix mixedSCZ 1 0 = 1 := by
  rw [polarMatrix_apply_of_ne _ (by decide), coeff_add, coeff_pair_sGate _ _ (by decide),
    czGate_eq_monomial, coeff_monomial, if_pos (add_comm _ _), zero_add,
    if_neg (by decide : (2 : ZMod (2 ^ 2)) ^ (2 - 1) ≠ 0)]

theorem polarMatrix_mixed_11 : polarMatrix mixedSCZ 1 1 = 0 := by
  rw [polarMatrix_apply_self, coeff_single_mixedSCZ, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
    mul_zero, if_pos rfl]

/-- The mixed form's matrix: `!![1, 1; 1, 0]` — the `S` diagonal at bit `0`, the `CZ` pair. -/
theorem polarMatrix_mixed : polarMatrix mixedSCZ = !![1, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact polarMatrix_mixed_00
  · exact polarMatrix_mixed_01
  · exact polarMatrix_mixed_10
  · exact polarMatrix_mixed_11

/-- The square cell is not multilinear. -/
theorem not_isMultilinear_czGate_self : ¬ IsMultilinear (czGate 2 (0 : Fin 1) 0) := by
  intro h
  rw [czGate_eq_monomial, ← Finsupp.single_add, show (1 + 1 : ℕ) = 2 from rfl] at h
  have hmem : Finsupp.single (0 : Fin 1) 2 ∈
      (monomial (Finsupp.single (0 : Fin 1) 2) ((2 : ZMod (2 ^ 2)) ^ (2 - 1)) :
        DiagPhase 1 2).support := by
    rw [MvPolynomial.support_monomial, if_neg (by decide), Finset.mem_singleton]
  have := h _ hmem 0
  rw [Finsupp.single_eq_same] at this
  omega

/-- The shift of `T` at precision three along its bit: the values `1` and `7`. -/
theorem eval_T (v : Fin 1 → ZMod 2) :
    DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 3) v = ((v 0).val : ZMod (2 ^ 3)) := by
  rw [show (MvPolynomial.X 0 : DiagPhase 1 3) = monomial (Finsupp.single 0 1) 1 from rfl,
    eval_monomial_single, one_mul]

/-- **`T` carries no datum**: at precision three no matrix makes its shift dyadic-affine. -/
theorem not_isShiftDatum_T :
    ¬ ∃ M : Matrix (Fin 1) (Fin 1) (ZMod 2),
      IsShiftDatum (DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 3)) M ⊤ := by
  rintro ⟨M, h⟩
  obtain ⟨c, hc⟩ := h (Pi.single 0 1) Submodule.mem_top
  have h0 := hc 0
  have h1 := hc (Pi.single 0 1)
  simp only [eval_T, zero_add, dotProduct_zero, ZMod.val_zero, Nat.cast_zero, mul_zero,
    add_zero, Pi.single_eq_same, Pi.zero_apply, sub_zero, zmod_two_val_one, Nat.cast_one] at h0
  simp only [eval_T, Pi.add_apply, Pi.single_eq_same, zmod_two_one_add_one, ZMod.val_zero,
    Nat.cast_zero, zmod_two_val_one, Nat.cast_one, zero_sub] at h1
  generalize M *ᵥ Pi.single 0 1 ⬝ᵥ Pi.single 0 1 = t at h1
  rw [← h0] at h1
  revert t
  decide

/-- The `CS` exponent at precision two, `X₀ X₁`, as a monomial. -/
theorem cs_eq_monomial :
    (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 2) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [show (MvPolynomial.X 0 : DiagPhase 2 2) = monomial (Finsupp.single 0 1) 1 from rfl,
    show (MvPolynomial.X 1 : DiagPhase 2 2) = monomial (Finsupp.single 1 1) 1 from rfl,
    monomial_mul, mul_one]

theorem eval_CS (v : Fin 2 → ZMod 2) :
    DiagPhase.eval (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 2) v =
      ((v 0).val : ZMod (2 ^ 2)) * ((v 1).val : ZMod (2 ^ 2)) := by
  rw [cs_eq_monomial, eval_monomial_pair _ (by decide), one_mul]

/-- **`CS` carries no datum**: at precision two its shift along the first bit takes the values
`0, 1, 0, 3`, three values where a dyadic-affine function takes two. -/
theorem not_isShiftDatum_CS :
    ¬ ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 2),
      IsShiftDatum (DiagPhase.eval (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 2)) M ⊤ := by
  rintro ⟨M, h⟩
  obtain ⟨c, hc⟩ := h (Pi.single 0 1) Submodule.mem_top
  have h0 := hc 0
  have h1 := hc (Pi.single 1 1)
  simp only [eval_CS, zero_add, dotProduct_zero, ZMod.val_zero, Nat.cast_zero, mul_zero,
    add_zero, Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.zero_apply, sub_zero, zmod_two_val_one, Nat.cast_one] at h0
  simp only [eval_CS, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add, add_zero, zmod_two_val_one,
    zmod_two_val_zero, Nat.cast_one, Nat.cast_zero, mul_one, sub_zero] at h1
  generalize M *ᵥ Pi.single 0 1 ⬝ᵥ Pi.single 1 1 = t at h1
  rw [← h0] at h1
  revert t
  decide

/-! ## Axiom rows (every declaration of the topic module) -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.zmod_two_cases' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_two_cases

/-- info: 'FTQCLib.Hierarchy.DiagPhase.zmod_two_val_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_two_val_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.zmod_two_val_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_two_val_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.zmod_two_one_add_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_two_one_add_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.val_add_bits' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_add_bits

/-- info: 'FTQCLib.Hierarchy.DiagPhase.val_mul_bits' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_mul_bits

/-- info: 'FTQCLib.Hierarchy.DiagPhase.val_sq_bit' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_sq_bit

/-- info: 'FTQCLib.Hierarchy.DiagPhase.single_add_single_eq_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms single_add_single_eq_iff

/-- info: 'FTQCLib.Hierarchy.DiagPhase.single_ne_single_add_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms single_ne_single_add_single

/-- info: 'FTQCLib.Hierarchy.DiagPhase.single_two_ne_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms single_two_ne_single

/-- info: 'FTQCLib.Hierarchy.DiagPhase.single_two_ne_single_add_single' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms single_two_ne_single_add_single

/-- info: 'FTQCLib.Hierarchy.DiagPhase.zero_ne_single_add_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zero_ne_single_add_single

/-- info: 'FTQCLib.Hierarchy.DiagPhase.exponent_cases_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exponent_cases_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_apply_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_apply_self

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_apply_of_ne' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_apply_of_ne

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_isSymm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_isSymm

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_sub_C' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_sub_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.topPairing' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topPairing

/-- info: 'FTQCLib.Hierarchy.DiagPhase.topPairing_add' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topPairing_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.topPairing_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topPairing_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.topPairing_single_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topPairing_single_self

/-- info: 'FTQCLib.Hierarchy.DiagPhase.topPairing_single_pair' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topPairing_single_pair

/-- info: 'FTQCLib.Hierarchy.DiagPhase.PolarLaw' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolarLaw

/-- info: 'FTQCLib.Hierarchy.DiagPhase.PolarLaw.add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolarLaw.add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.PolarLaw.zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolarLaw.zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.PolarLaw.sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolarLaw.sum

/-- info: 'FTQCLib.Hierarchy.DiagPhase.monoMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monoMatrix

/-- info: 'FTQCLib.Hierarchy.DiagPhase.monoMatrix_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monoMatrix_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.monoMatrix_single_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monoMatrix_single_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.monoMatrix_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monoMatrix_single

/-- info: 'FTQCLib.Hierarchy.DiagPhase.monoMatrix_pair' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monoMatrix_pair

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_eq_sum_monoMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_eq_sum_monoMatrix

/-- info: 'FTQCLib.Hierarchy.DiagPhase.four_mul_eq_zero_of_effLevelMonom_single_le_two' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms four_mul_eq_zero_of_effLevelMonom_single_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eq_two_pow_pred_of_effLevelMonom_le_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_two_pow_pred_of_effLevelMonom_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_monomial_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_monomial_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_monomial_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_monomial_single

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_monomial_single_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_monomial_single_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_monomial_pair' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_monomial_pair

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarLaw_monomial' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarLaw_monomial

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_eq_sum_support' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_eq_sum_support

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_add_sub_eval_eq_of_effectiveLevel_le_two' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_add_sub_eval_eq_of_effectiveLevel_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsShiftDatum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsShiftDatum

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsShiftDatum.mono' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsShiftDatum.mono

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isShiftDatum_polarMatrix_of_effectiveLevel_le_two' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isShiftDatum_polarMatrix_of_effectiveLevel_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.const_eq_of_shift' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms const_eq_of_shift

/-- info: 'FTQCLib.Hierarchy.DiagPhase.two_mul_eval_sub_eval_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_eval_sub_eval_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.bit_eq_of_two_pow_pred_mul_val_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bit_eq_of_two_pow_pred_mul_val_eq

/-- info: 'FTQCLib.Hierarchy.DiagPhase.symm_on_of_isShiftDatum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symm_on_of_isShiftDatum

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eq_of_isShiftDatum_top' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_isShiftDatum_top

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_sub_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_sub_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.coeff_boolReduce_sub_C' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_boolReduce_sub_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_boolReduce_sub_C' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_boolReduce_sub_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isShiftDatum_polarMatrix_boolReduce_of_levelExt_le_two'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isShiftDatum_polarMatrix_boolReduce_of_levelExt_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.sGate_eq_monomial' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sGate_eq_monomial

/-- info: 'FTQCLib.Hierarchy.DiagPhase.czGate_eq_monomial' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czGate_eq_monomial

/-- info: 'FTQCLib.Hierarchy.DiagPhase.coeff_single_sGate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_single_sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.coeff_pair_sGate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_pair_sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_sGate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_sGate_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_sGate_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_czGate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_czGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.polarMatrix_czGate_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_czGate_self

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_sGate_le_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_sGate_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.effectiveLevel_czGate_le_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_czGate_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.coeff_zero_sGate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_zero_sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.coeff_zero_czGate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coeff_zero_czGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.levelExt_sGate_le_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms levelExt_sGate_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.levelExt_czGate_le_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms levelExt_czGate_le_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.two_pow_pred_mul_val_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_pow_pred_mul_val_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.IsShiftDatum.add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsShiftDatum.add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isMultilinear_sGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isMultilinear_sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.isMultilinear_czGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isMultilinear_czGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_sGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.boolReduce_czGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_czGate

end FTQCLib.Hierarchy.DiagPhase

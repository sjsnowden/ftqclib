/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.DyadicCharacter

/-!
# Acceptance rows for the dyadic character

* **Values at the two smallest precisions**, each reached by Mathlib's own evaluation of the
  exponential: `charOf 1 1 = −1` (`exp(iπ)`), `charOf 2 1 = i` (`cos(π/2) + i·sin(π/2)`), and
  `charOf 0 z = 1` for every `z` (the trivial ring).
* **Agreement on the sign lemma**: `charOf_two_pow_mul` at `m = 1`, `t = 1` gives `charOf 1 1 = −1`,
  the same value the direct evaluation gives.
* **`1 ≤ m` is load-bearing in the sign lemma**: at `m = 0` the left side is `charOf 0 1 = 1` while
  `(−1)^1 = −1`. The parity lemmas carry no hypothesis: they rest on `two_pow_pred_mul_two`, which
  holds at every `m` (the ring is trivial at `m = 0`).
* **Injectivity is discriminating**: `charOf 1 0 ≠ charOf 1 1`, and at `m = 2` the four residues
  have four distinct characters (`1, i, −1, −i`).
* **The parity lemma on a witness**: `2^{m−1}·3 = 2^{m−1}·1` at `m = 2` (kernel row).

The values are in `ℂ`, so no row is a kernel row except the `ZMod 4` identities — forced, not
skipped. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy

/-! ## Values -/

/-- At precision `1` the residue `1` is the sign `−1`. -/
theorem charOf_one_one : charOf 1 1 = -1 := by
  unfold charOf
  have hval : ((1 : ZMod (2 ^ 1)).val : ℝ) = 1 := by
    have h : (1 : ZMod (2 ^ 1)).val = 1 := by decide
    rw [h]
    norm_num
  rw [hval]
  have hπ : ((2 * Real.pi * (1 : ℝ) / (2 : ℝ) ^ 1 : ℝ) : ℂ) = (Real.pi : ℂ) := by
    push_cast
    ring
  rw [hπ, mul_comm]
  exact Complex.exp_pi_mul_I

/-- At precision `2` the residue `1` is `i`. -/
theorem charOf_two_one : charOf 2 1 = Complex.I := by
  unfold charOf
  have hval : ((1 : ZMod (2 ^ 2)).val : ℝ) = 1 := by
    have h : (1 : ZMod (2 ^ 2)).val = 1 := by decide
    rw [h]
    norm_num
  rw [hval]
  have hπ : ((2 * Real.pi * (1 : ℝ) / (2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hπ, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- At precision `0` every residue has character `1`: the exponent ring is trivial. -/
theorem charOf_zero_prec (z : ZMod (2 ^ 0)) : charOf 0 z = 1 := by
  unfold charOf
  have h : z.val = 0 := by
    haveI : NeZero (2 ^ 0) := ⟨by norm_num⟩
    have hlt := ZMod.val_lt z
    norm_num at hlt
    rw [hlt]
    exact ZMod.val_zero
  rw [h]
  simp

/-! ## Agreement, and the load-bearing hypothesis of the sign lemma -/

/-- **Agreement.** The sign lemma at `m = 1`, `t = 1` reaches the value the direct evaluation
gives. -/
theorem sign_lemma_agrees :
    charOf 1 ((2 : ZMod (2 ^ 1)) ^ (1 - 1) * ((1 : ℕ) : ZMod (2 ^ 1))) = charOf 1 1 := by
  rw [charOf_two_pow_mul le_rfl 1, charOf_one_one]
  simp

/-- **`1 ≤ m` is load-bearing.** At `m = 0` the sign lemma's statement is false: its left side is
`1` and its right side is `−1`. -/
theorem sign_lemma_needs_hm :
    charOf 0 ((2 : ZMod (2 ^ 0)) ^ (0 - 1) * ((1 : ℕ) : ZMod (2 ^ 0))) ≠ (-1 : ℂ) ^ 1 := by
  rw [charOf_zero_prec]
  norm_num

/-! ## Injectivity is discriminating -/

/-- At precision `1` the two residues have distinct characters. -/
theorem charOf_one_injective_witness : charOf 1 0 ≠ charOf 1 1 := by
  rw [charOf_zero, charOf_one_one]
  norm_num

/-- At precision `2` the residues `0`, `1`, `2`, `3` have characters `1`, `i`, `−1`, `−i`. -/
theorem charOf_two_values :
    charOf 2 0 = 1 ∧ charOf 2 1 = Complex.I ∧ charOf 2 2 = -1 ∧ charOf 2 3 = -Complex.I := by
  refine ⟨charOf_zero 2, charOf_two_one, ?_, ?_⟩
  · have h : (2 : ZMod (2 ^ 2)) = 1 + 1 := by decide
    rw [h, charOf_add, charOf_two_one, Complex.I_mul_I]
  · have h : (3 : ZMod (2 ^ 2)) = 1 + 1 + 1 := by decide
    rw [h, charOf_add, charOf_add, charOf_two_one, Complex.I_mul_I]
    ring

/-- The four characters at precision `2` are pairwise distinct. -/
theorem charOf_two_distinct :
    charOf 2 0 ≠ charOf 2 1 ∧ charOf 2 1 ≠ charOf 2 2 ∧ charOf 2 2 ≠ charOf 2 3
      ∧ charOf 2 0 ≠ charOf 2 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := charOf_two_values
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0, h1]
    intro h
    have := congrArg Complex.im h
    simp at this
  · rw [h1, h2]
    intro h
    have := congrArg Complex.im h
    simp at this
  · rw [h2, h3]
    intro h
    have := congrArg Complex.re h
    simp at this
  · rw [h0, h2]
    norm_num

/-! ## The parity lemma on a witness -/

/-- At `m = 2`, `2^{m−1}·3 = 2^{m−1}·1` in `ZMod 4` — the top bit reads parity (kernel row). -/
theorem parity_witness :
    (2 : ZMod (2 ^ 2)) ^ (2 - 1) * ((3 : ℕ) : ZMod (2 ^ 2))
      = (2 : ZMod (2 ^ 2)) ^ (2 - 1) * ((1 : ℕ) : ZMod (2 ^ 2)) := by decide

/-- The same identity through the lemma. -/
theorem parity_witness_agrees :
    (2 : ZMod (2 ^ 2)) ^ (2 - 1) * ((3 : ℕ) : ZMod (2 ^ 2))
      = (2 : ZMod (2 ^ 2)) ^ (2 - 1) * ((1 : ℕ) : ZMod (2 ^ 2)) :=
  two_pow_pred_mul_eq_of_cast_eq (by decide)

/-! ## The quarter turn and the two branch pairs -/

/-- **Agreement.** The quarter-turn lemma at `m = 2`, `t = 1` gives `charOf 2 1 = i`, the direct
value. -/
theorem quarter_lemma_agrees :
    charOf 2 ((2 : ZMod (2 ^ 2)) ^ (2 - 2) * ((1 : ℕ) : ZMod (2 ^ 2))) = charOf 2 1 := by
  rw [charOf_two_pow_sub_two_mul le_rfl 1, charOf_two_one]
  simp

/-- **`2 ≤ m` is load-bearing.** At `m = 1` the residue `2^{m−2}` truncates to `2^{m−1}`, whose
character is `−1`, not `i`. -/
theorem quarter_lemma_needs_hm :
    charOf 1 ((2 : ZMod (2 ^ 1)) ^ (1 - 2) * ((1 : ℕ) : ZMod (2 ^ 1))) ≠ Complex.I ^ 1 := by
  have h : (2 : ZMod (2 ^ 1)) ^ (1 - 2) * ((1 : ℕ) : ZMod (2 ^ 1)) = 1 := by decide
  rw [h, charOf_one_one, pow_one]
  intro h
  have := congrArg Complex.re h
  simp at this

/-- **The rotate shape is empty at precision one**: no residue has `2a = 2^{m−1}` in `ZMod 2`. -/
theorem no_rotate_at_one : ∀ a : ZMod (2 ^ 1), 2 * a ≠ (2 : ZMod (2 ^ 1)) ^ (1 - 1) := by
  decide

/-- At `m = 2` the residue `1` is a rotate constant. -/
theorem rotate_constant_two : (2 : ZMod (2 ^ 2)) * 1 = (2 : ZMod (2 ^ 2)) ^ (2 - 1) := by decide

/-- The rotate pair's left side at `m = 2`, `a = 1`, `b = 1`. -/
noncomputable def rotateLeft : ℂ :=
  1 + charOf 2 (1 + (2 : ZMod (2 ^ 2)) ^ (2 - 1) * (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ 2)))

/-- The rotate pair's right side at `m = 2`, `a = 1`, `b = 1`. -/
noncomputable def rotateRight : ℂ :=
  (1 + charOf 2 1) * charOf 2 (-1 * (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ 2)))

/-- **Agreement on the rotate pair**: both sides are `1 − i`, by direct evaluation. -/
theorem rotate_pair_agrees : rotateLeft = 1 - Complex.I ∧ rotateRight = 1 - Complex.I := by
  obtain ⟨-, h1, -, h3⟩ := charOf_two_values
  have hl : (1 + (2 : ZMod (2 ^ 2)) ^ (2 - 1) * (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ 2))) = 3 := by
    decide
  have hr : (-1 * (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ 2)) : ZMod (2 ^ 2)) = 3 := by decide
  refine ⟨?_, ?_⟩
  · unfold rotateLeft
    rw [hl, h3]
    ring
  · unfold rotateRight
    rw [hr, h3, h1]
    linear_combination (-1 : ℂ) * Complex.I_sq

/-- The rotate pair through the lemma, on the same instance. -/
theorem rotate_pair_lemma : rotateLeft = rotateRight :=
  one_add_charOf_rotate (by norm_num) rotate_constant_two 1

/-- **The collapse pair** at `m = 1`: `b = 1` gives `0`, `b = 0` gives `2`. -/
theorem collapse_pair_values :
    1 + charOf 1 ((2 : ZMod (2 ^ 1)) ^ (1 - 1) * (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ 1))) = 0
    ∧ 1 + charOf 1 ((2 : ZMod (2 ^ 1)) ^ (1 - 1) * (((0 : ZMod 2).val : ℕ) : ZMod (2 ^ 1)))
      = 2 := by
  refine ⟨?_, ?_⟩
  · rw [one_add_charOf_two_pow_pred le_rfl 1]
    simp
  · rw [one_add_charOf_two_pow_pred le_rfl 0]
    simp

/-- The rotate scale at `m = 2`, `a = 1` is `1 + i`, nonzero (through the lemma). -/
theorem rotate_scale_ne_zero : 1 + charOf 2 1 ≠ 0 :=
  one_add_charOf_ne_zero (by norm_num) rotate_constant_two

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_one_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_one_one

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_two_one

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_zero_prec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_zero_prec

/-- info: 'FTQCLib.Frame.Walkthrough.sign_lemma_agrees' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_lemma_agrees

/-- info: 'FTQCLib.Frame.Walkthrough.sign_lemma_needs_hm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_lemma_needs_hm

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_one_injective_witness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_one_injective_witness

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_values' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_two_values

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_distinct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_two_distinct

/-- info: 'FTQCLib.Frame.Walkthrough.parity_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parity_witness

/-- info: 'FTQCLib.Frame.Walkthrough.parity_witness_agrees' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parity_witness_agrees

/-- info: 'FTQCLib.Frame.Walkthrough.zeta_pow_two_pow_sub_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeta_pow_two_pow_sub_two

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_pow_sub_two_mul' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_two_pow_sub_two_mul

/-- info: 'FTQCLib.Frame.Walkthrough.one_add_charOf_two_pow_pred' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_add_charOf_two_pow_pred

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_neg_of_two_mul_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_neg_of_two_mul_eq

/-- info: 'FTQCLib.Frame.Walkthrough.one_add_charOf_rotate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_add_charOf_rotate

/-- info: 'FTQCLib.Frame.Walkthrough.one_add_charOf_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_add_charOf_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.quarter_lemma_agrees' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quarter_lemma_agrees

/-- info: 'FTQCLib.Frame.Walkthrough.quarter_lemma_needs_hm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quarter_lemma_needs_hm

/-- info: 'FTQCLib.Frame.Walkthrough.rotate_pair_agrees' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rotate_pair_agrees

/-- info: 'FTQCLib.Frame.Walkthrough.collapse_pair_values' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collapse_pair_values

/-- info: 'FTQCLib.Frame.Walkthrough.no_rotate_at_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms no_rotate_at_one

/-- info: 'FTQCLib.Frame.Walkthrough.rotate_constant_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms rotate_constant_two

/-- info: 'FTQCLib.Frame.Walkthrough.rotateLeft' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms rotateLeft

/-- info: 'FTQCLib.Frame.Walkthrough.rotateRight' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms rotateRight

/-- info: 'FTQCLib.Frame.Walkthrough.rotate_pair_lemma' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rotate_pair_lemma

/-- info: 'FTQCLib.Frame.Walkthrough.rotate_scale_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rotate_scale_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.charOf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf

/-- info: 'FTQCLib.Frame.Walkthrough.exp_realPhase_eq_charOf' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exp_realPhase_eq_charOf

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_add

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_zero

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_ne_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_sub_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_sub_mul

/-- info: 'FTQCLib.Frame.Walkthrough.zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeta

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_eq_zeta_pow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_eq_zeta_pow

/-- info: 'FTQCLib.Frame.Walkthrough.zeta_eq_exp' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zeta_eq_exp

/-- info: 'FTQCLib.Frame.Walkthrough.isPrimitiveRoot_zeta' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isPrimitiveRoot_zeta

/-- info: 'FTQCLib.Frame.Walkthrough.zeta_pow_mod' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zeta_pow_mod

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_injective

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_eq_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms charOf_eq_iff

/-- info: 'FTQCLib.Frame.Walkthrough.zeta_pow_two_pow_pred' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zeta_pow_two_pow_pred

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_pow_mul' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_two_pow_mul

/-- info: 'FTQCLib.Frame.Walkthrough.two_pow_pred_mul_natCast_mod' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms two_pow_pred_mul_natCast_mod

/-- info: 'FTQCLib.Frame.Walkthrough.two_pow_pred_mul_eq_of_cast_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_pow_pred_mul_eq_of_cast_eq

/-- info: 'FTQCLib.Frame.Walkthrough.neg_one_pow_eq_of_cast_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms neg_one_pow_eq_of_cast_eq

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_cast_two_add_right' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zDot_cast_two_add_right

end FTQCLib.Frame.Walkthrough

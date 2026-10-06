/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.UnreadBits
import FTQCLib.Carrier.DiagonalInjectionCheck

/-!
# Check: witness for T27, equality up to unread bits on one read bit

T27's witness (`docs/STEPS.md`, T27.2): the rows of `docs/framing/T27.md` ("Search space", the
table of rows) at `n = 1`, on the frozen statement of `UnreadBits.lean`. Every row is about the
objects the headline theorems name, `UnreadEq` (the Gram data `gram` of `amp`) and the extended
theory `UnreadDerivable`, and all but the two underivability rows below are computed without any
of T27's theorems: an amplitude is read off `amp_pos`/`amp_neg` and the exponent sums `ampCore`
(height four, sixteen terms each, expanded here), a run off `amp_run` (T05), the drop off
`amp_dropFreeBit` (T10), and the Gram data by summing over the one unread bit. A derivation is a
single move of `UnreadMove`, a constructor, so no soundness theorem is used.

The values `r` below are the exponent sums at the words `(x, u) = (0,0), (0,1), (1,0), (1,1)`,
each amplitude `c · r / 4` at height four (`ampCore_four`).

* **A1 (agreement).** The Bell state and H on its unread bit (`bellH`, the run of `[H u]`):
  both have the identity as Gram data, the move (b) relates them, and they are not `StateEq`.
* **A2 (agreement).** No unread bit: `∣+⟩` and its negation by the constant diagonal letter `1`
  (`negPlus`): `UnreadEq 0`, related by move (b), not `StateEq`, and the second is the first times
  `−1`, the unit-modulus scalar of `unreadEq_zero_iff`'s right side, computed here directly.
* **D1 (discriminating).** `δ_{u=0}` at both read words (`deltaUnreadZero`, Gram data all ones)
  against the Bell state (the identity): not `UnreadEq`.
* **D2 (discriminating).** The Bell state against its image under `[[3, −4], [4, 3]]/5` on the
  unread bit (`rotState (2/5)`, `r = 6, 8, −8, 6` at `c = 2/5`): `UnreadEq` and not `StateEq`, at
  the scale ratio `2/5`, which is not dyadic: this pair fails by D9's scale gap.
* **O1 (discriminating, with an inhabitation row).** `r = 10, 0, 0, 10` (`tenBell`) against
  `r = 6, 8, −8, 6` (`rotState 1`), both at `m = 1`, `h = 4`, `c = 1`: `UnreadEq`, not
  `StateEq`, at scale ratio one; both are carriers and the ratio is dyadic, the hypotheses of
  `unreadEq_derivable_iff` held together. That O1 is not derivable is the row O1-underivable.
* **O2 (discriminating, two rows).** At `m = 3`: `r = 10, 0, 0, 10` (`tenBellThree`) against
  `r = 10, 0, 0, 6 + 8i` (`phaseState`): `UnreadEq`, not `StateEq`, ratio one; and the Gram sum
  without the conjugate differs at `x = y = 1` (`100` against `(6 + 8i)²`), the row that catches
  T27.4's planned mutant, invisible at `m = 1` where every amplitude is real.
* **O4 (discriminating).** No unread bit, at `m = 3`: `r = 10` against `r = 6 + 8i` at both read
  words: `UnreadEq 0`, not `StateEq`, ratio one, and the unconjugated product differs.
* **C1 (discriminating).** The unqualified drop: `dropFreeBit`'s hypothesis holds for the Bell
  state's unread bit, `DeterminedByUnread` does not, and the drop changes the Gram data (all ones
  against the identity): it restores the coherence the environment held.
* **O1-underivable and O2-underivable (discriminating).** O1's and O2's pairs, equal Gram data at
  a dyadic scale ratio, are not derivable: a read function of the second lies outside the
  `ℤ[ζ_{2^∞}, ½]`-module of the first's (it would need `3/5`, and for O2 `(3 + 4i)/5`, whose sum
  with its conjugate is `6/5`), and a derivation keeps that module (`readModule_eq_of_derivable`,
  through
  `not_unreadDerivable_of_readFunction_not_mem`). These two use T27's theorems, as the plan's row
  says ("through `readModule_eq_of_derivable`"); every other row is computed without them. Added by
  the run session after run 9b (docs/STEPS.md, entry 2026-10-01j): run 9b's T27.4 went green
  without them.

Each row the plan's "Named rows" table names (docs/STEPS.md) carries its name on its marker,
`-- row: <kind> <name>`, and the gate requires it (docs/GATES.md, entry 2026-10-01).

Scope (standard 7.3): these rows show each class of the note's table nonempty at `n = k = 1` (and
`k = 0`); they prove nothing about other cells.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## Sums over words -/

/-- A sum over the sixteen words of four bits, bit by bit. -/
private theorem sum_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → ZMod 2) → M) :
    ∑ y, F y
      = ∑ a : ZMod 2, ∑ b : ZMod 2, ∑ c : ZMod 2, ∑ d : ZMod 2, F ![a, b, c, d] := by
  simp only [sum_fin_cons (N := 3), sum_fin_cons (N := 2), sum_fin_cons (N := 1), sum_fin_cons (N := 0),
    Fintype.sum_unique]
  rfl

/-! ## Exponents at height four and their sums

Each exponent is written on the `N` free bits and the four summation variables `y`, and its
character sum `Σ_y charOf m (Q (w, y))` is the `r` of the note's table at the word `w`. At `m = 1`
the sum is `16 − 2·#{y : Q = 1}`. -/

/-- The summation variable `y_j`, the free bit `N + j` of the exponent's variables. -/
noncomputable def sumVar {N m : ℕ} (j : Fin 4) : DiagPhase (N + 4) m :=
  MvPolynomial.X (Fin.natAdd N j)

/-- The free bit `w_i` among the exponent's variables. -/
noncomputable def wordVar {N m : ℕ} (i : Fin N) : DiagPhase (N + 4) m :=
  MvPolynomial.X (Fin.castAdd 4 i)

/-- `y₀ y₁ (y₂ ∨ y₃)`: one at three of the sixteen `y`, so its sign sum at `m = 1` is `10`. -/
noncomputable def exponentTen {N m : ℕ} : DiagPhase (N + 4) m :=
  sumVar 0 * sumVar 1 * (sumVar 2 + sumVar 3 - sumVar 2 * sumVar 3)

/-- `r = 10` at `m = 1`, at every word. -/
theorem sum_exponentTen (N : ℕ) (w : Fin N → ZMod 2) :
    ∑ y : Fin 4 → ZMod 2,
      charOf 1 (DiagPhase.eval (exponentTen (N := N)) (Fin.append w y)) = 10 := by
  rw [sum_four]
  simp only [sum_zmod_two, exponentTen, sumVar, DiagPhase.eval, map_mul, map_add, map_sub,
    MvPolynomial.eval_X, DiagPhase.liftBinary, Fin.append_right, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ZMod.val_zero, ZMod.val_one,
    Nat.cast_zero, Nat.cast_one, Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_mul, mul_one,
    one_mul, add_zero, sub_zero, charOf_zero]
  have h1 : (1 : ZMod (2 ^ 1)) + 1 - 1 = 1 := by decide
  rw [h1, charOf_one_one]
  norm_num [charOf_one_one]

/-- `r = 10` at `m = 3`, by the exponent `4·exponentTen`, at every word. -/
theorem sum_exponentTen_three (N : ℕ) (w : Fin N → ZMod 2) :
    ∑ y : Fin 4 → ZMod 2,
      charOf 3 (DiagPhase.eval (MvPolynomial.C 4 * exponentTen (N := N)) (Fin.append w y))
        = 10 := by
  rw [sum_four]
  simp only [sum_zmod_two, exponentTen, sumVar, DiagPhase.eval, map_mul, map_add, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C, DiagPhase.liftBinary, Fin.append_right,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    ZMod.val_zero, ZMod.val_one,
    Nat.cast_zero, Nat.cast_one, Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_mul, mul_one,
    one_mul, add_zero, sub_zero, charOf_zero, add_sub_cancel_right, charOf_three_four]
  norm_num [charOf_three_four]

/-- `1 + 1 = 0` in `ZMod 2`. -/
private theorem one_add_one_two : (1 : ZMod (2 ^ 1)) + 1 = 0 := by decide

/-- Expand a character sum over the sixteen `y` and evaluate each term. -/
local macro "word_sum" : tactic =>
  `(tactic| (
    rw [sum_four]
    simp only [sum_zmod_two, DiagPhase.eval, map_mul, map_add, map_sub,
      MvPolynomial.eval_X, MvPolynomial.eval_C, map_one, DiagPhase.liftBinary, Fin.append_right,
      Fin.append_left, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one,
      Matrix.head_cons, Matrix.tail_cons, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add,
      sub_zero, sub_self, add_sub_cancel_right, one_add_one_two, charOf_zero, charOf_one_one,
      charOf_three_four, charOf_three_two]
    norm_num [one_add_one_two, charOf_one_one, charOf_three_four, charOf_three_two]
    try ring))

/-- `y₀y₁ + (1 − y₀)y₁y₂y₃`: one at five `y`, sign sum `6`. -/
noncomputable def exponentSix {N : ℕ} : DiagPhase (N + 4) 1 :=
  sumVar 0 * sumVar 1 + (1 - sumVar 0) * sumVar 1 * sumVar 2 * sumVar 3

/-- `y₀y₁`: one at four `y`, sign sum `8`. -/
noncomputable def exponentEight {N : ℕ} : DiagPhase (N + 4) 1 := sumVar 0 * sumVar 1

/-- The exponent of `r = 6, 8, −8, 6`: `exponentSix` where `x = u`, `exponentEight` at `(0, 1)`,
and its complement at `(1, 0)`. -/
noncomputable def rotationExponent : DiagPhase ((1 + 1) + 4) 1 :=
  (1 + wordVar 0 + wordVar 1) * exponentSix + (wordVar 0 + wordVar 1) * (exponentEight + wordVar 0)

/-- `r(0, 0) = 6`. -/
theorem sum_rotationExponent_00 : ∑ y : Fin 4 → ZMod 2,
    charOf 1 (DiagPhase.eval rotationExponent (Fin.append (![0, 0] : Fin (1 + 1) → ZMod 2) y))
      = 6 := by
  simp only [rotationExponent, exponentSix, exponentEight, sumVar, wordVar]
  word_sum

/-- `r(0, 1) = 8`. -/
theorem sum_rotationExponent_01 : ∑ y : Fin 4 → ZMod 2,
    charOf 1 (DiagPhase.eval rotationExponent (Fin.append (![0, 1] : Fin (1 + 1) → ZMod 2) y))
      = 8 := by
  simp only [rotationExponent, exponentSix, exponentEight, sumVar, wordVar]
  word_sum

/-- `r(1, 0) = −8`. -/
theorem sum_rotationExponent_10 : ∑ y : Fin 4 → ZMod 2,
    charOf 1 (DiagPhase.eval rotationExponent (Fin.append (![1, 0] : Fin (1 + 1) → ZMod 2) y))
      = -8 := by
  simp only [rotationExponent, exponentSix, exponentEight, sumVar, wordVar]
  word_sum

/-- `r(1, 1) = 6`. -/
theorem sum_rotationExponent_11 : ∑ y : Fin 4 → ZMod 2,
    charOf 1 (DiagPhase.eval rotationExponent (Fin.append (![1, 1] : Fin (1 + 1) → ZMod 2) y))
      = 6 := by
  simp only [rotationExponent, exponentSix, exponentEight, sumVar, wordVar]
  word_sum

/-- `2y₀ + 4(1 − y₀)y₁y₂y₃` at `m = 3`: `i` at eight `y`, `−1` at one, `1` at seven, so the sum
is `6 + 8i`. -/
noncomputable def exponentSixEightI {N : ℕ} : DiagPhase (N + 4) 3 :=
  MvPolynomial.C 2 * sumVar 0
    + MvPolynomial.C 4 * (1 - sumVar 0) * sumVar 1 * sumVar 2 * sumVar 3

/-- `r = 6 + 8i` at `m = 3`, at every word. -/
theorem sum_exponentSixEightI (N : ℕ) (w : Fin N → ZMod 2) : ∑ y : Fin 4 → ZMod 2,
    charOf 3 (DiagPhase.eval (exponentSixEightI (N := N)) (Fin.append w y))
      = 6 + 8 * Complex.I := by
  simp only [exponentSixEightI, sumVar]
  word_sum

/-- The exponent of `r = 10, ·, ·, 6 + 8i` on the Bell support: `4·exponentTen` at `x = 0`,
`exponentSixEightI` at `x = 1`. -/
noncomputable def phaseExponent : DiagPhase ((1 + 1) + 4) 3 :=
  (1 - wordVar 0) * (MvPolynomial.C 4 * exponentTen) + wordVar 0 * exponentSixEightI

/-- `r(0, 0) = 10`. -/
theorem sum_phaseExponent_00 : ∑ y : Fin 4 → ZMod 2,
    charOf 3 (DiagPhase.eval phaseExponent (Fin.append (![0, 0] : Fin (1 + 1) → ZMod 2) y))
      = 10 := by
  simp only [phaseExponent, exponentSixEightI, exponentTen, sumVar, wordVar]
  word_sum

/-- `r(1, 1) = 6 + 8i`. -/
theorem sum_phaseExponent_11 : ∑ y : Fin 4 → ZMod 2,
    charOf 3 (DiagPhase.eval phaseExponent (Fin.append (![1, 1] : Fin (1 + 1) → ZMod 2) y))
      = 6 + 8 * Complex.I := by
  simp only [phaseExponent, exponentSixEightI, exponentTen, sumVar, wordVar]
  word_sum

/-! ## Amplitudes -/

/-- With full support (`L = lagNoZ N`, `x₀ = 0`), every word reads `ampCore`. -/
private theorem amp_noZ {N : ℕ} {S : KernelSumState N} (hL : S.L = lagNoZ N) (hx : S.x₀ = 0)
    (w : Fin N → ZMod 2) : amp S w = ampCore S.m S.h S.Q S.c w := by
  refine amp_pos ⟨⟨w, 0⟩, ?_, ?_⟩
  · rw [hL]
    rfl
  · rw [hx, zero_add]

/-- The carrier `(5/2)·(∣00⟩ + ∣11⟩)` at `m = 1`, `h = 4`, `c = 1`: `r = 10, 0, 0, 10`. -/
noncomputable def tenBell : KernelSumState (1 + 1) := ⟨1, 4, exponentTen, 1, bellL, 0⟩

/-- The carrier with `r = 6, 8, −8, 6` at `m = 1`, `h = 4`, full support, scale `c`. -/
noncomputable def rotState (c : ℂ) : KernelSumState (1 + 1) :=
  ⟨1, 4, rotationExponent, c, lagNoZ (1 + 1), 0⟩

/-- `tenBell` at `m = 3`: the exponent `4·exponentTen`. -/
noncomputable def tenBellThree : KernelSumState (1 + 1) :=
  ⟨3, 4, MvPolynomial.C 4 * exponentTen, 1, bellL, 0⟩

/-- The carrier with `r = 10, 0, 0, 6 + 8i` at `m = 3`, `h = 4`, `c = 1`. -/
noncomputable def phaseState : KernelSumState (1 + 1) := ⟨3, 4, phaseExponent, 1, bellL, 0⟩

/-- No unread bit: `r = 10` at both read words, `m = 3`, `h = 4`, `c = 1`. -/
noncomputable def tenPoint : KernelSumState (1 + 0) :=
  ⟨3, 4, MvPolynomial.C 4 * exponentTen, 1, lagNoZ (1 + 0), 0⟩

/-- No unread bit: `r = 6 + 8i` at both read words, `m = 3`, `h = 4`, `c = 1`. -/
noncomputable def sixEightIPoint : KernelSumState (1 + 0) :=
  ⟨3, 4, exponentSixEightI, 1, lagNoZ (1 + 0), 0⟩

/-! The amplitudes of the height-four states, word by word. -/

theorem amp_tenBell_00 : amp tenBell ![0, 0] = 5 / 2 := by
  rw [amp_bell_on rfl rfl (by decide)]
  change ampCore 1 4 exponentTen 1 _ = _
  rw [ampCore_four, sum_exponentTen]
  norm_num

theorem amp_tenBell_11 : amp tenBell ![1, 1] = 5 / 2 := by
  rw [amp_bell_on rfl rfl (by decide)]
  change ampCore 1 4 exponentTen 1 _ = _
  rw [ampCore_four, sum_exponentTen]
  norm_num

theorem amp_tenBell_01 : amp tenBell ![0, 1] = 0 := amp_bell_off rfl rfl (by decide)
theorem amp_tenBell_10 : amp tenBell ![1, 0] = 0 := amp_bell_off rfl rfl (by decide)

theorem amp_tenBellThree_00 : amp tenBellThree ![0, 0] = 5 / 2 := by
  rw [amp_bell_on rfl rfl (by decide)]
  change ampCore 3 4 (MvPolynomial.C 4 * exponentTen) 1 _ = _
  rw [ampCore_four, sum_exponentTen_three]
  norm_num

theorem amp_tenBellThree_11 : amp tenBellThree ![1, 1] = 5 / 2 := by
  rw [amp_bell_on rfl rfl (by decide)]
  change ampCore 3 4 (MvPolynomial.C 4 * exponentTen) 1 _ = _
  rw [ampCore_four, sum_exponentTen_three]
  norm_num

theorem amp_tenBellThree_01 : amp tenBellThree ![0, 1] = 0 := amp_bell_off rfl rfl (by decide)
theorem amp_tenBellThree_10 : amp tenBellThree ![1, 0] = 0 := amp_bell_off rfl rfl (by decide)

theorem amp_phaseState_00 : amp phaseState ![0, 0] = 5 / 2 := by
  rw [amp_bell_on rfl rfl (by decide)]
  change ampCore 3 4 phaseExponent 1 _ = _
  rw [ampCore_four, sum_phaseExponent_00]
  norm_num

theorem amp_phaseState_11 : amp phaseState ![1, 1] = (6 + 8 * Complex.I) / 4 := by
  rw [amp_bell_on rfl rfl (by decide)]
  change ampCore 3 4 phaseExponent 1 _ = _
  rw [ampCore_four, sum_phaseExponent_11]
  ring

theorem amp_phaseState_01 : amp phaseState ![0, 1] = 0 := amp_bell_off rfl rfl (by decide)
theorem amp_phaseState_10 : amp phaseState ![1, 0] = 0 := amp_bell_off rfl rfl (by decide)

theorem amp_rotState_00 (c : ℂ) : amp (rotState c) ![0, 0] = c * 6 / 4 := by
  rw [amp_noZ rfl rfl]
  change ampCore 1 4 rotationExponent c _ = _
  rw [ampCore_four, sum_rotationExponent_00]
  ring

theorem amp_rotState_01 (c : ℂ) : amp (rotState c) ![0, 1] = c * 8 / 4 := by
  rw [amp_noZ rfl rfl]
  change ampCore 1 4 rotationExponent c _ = _
  rw [ampCore_four, sum_rotationExponent_01]
  ring

theorem amp_rotState_10 (c : ℂ) : amp (rotState c) ![1, 0] = -(c * 8 / 4) := by
  rw [amp_noZ rfl rfl]
  change ampCore 1 4 rotationExponent c _ = _
  rw [ampCore_four, sum_rotationExponent_10]
  ring

theorem amp_rotState_11 (c : ℂ) : amp (rotState c) ![1, 1] = c * 6 / 4 := by
  rw [amp_noZ rfl rfl]
  change ampCore 1 4 rotationExponent c _ = _
  rw [ampCore_four, sum_rotationExponent_11]
  ring

theorem amp_tenPoint (w : Fin (1 + 0) → ZMod 2) : amp tenPoint w = 5 / 2 := by
  rw [amp_noZ rfl rfl]
  change ampCore 3 4 (MvPolynomial.C 4 * exponentTen) 1 _ = _
  rw [ampCore_four, sum_exponentTen_three]
  norm_num

theorem amp_sixEightIPoint (w : Fin (1 + 0) → ZMod 2) :
    amp sixEightIPoint w = (6 + 8 * Complex.I) / 4 := by
  rw [amp_noZ rfl rfl]
  change ampCore 3 4 exponentSixEightI 1 _ = _
  rw [ampCore_four, sum_exponentSixEightI]
  ring

/-! ## The Bell state, H on its unread bit, and `δ_{u=0}` -/

/-- The Bell state is `1` on its support. -/
private theorem amp_bellState_diag {w : Fin 2 → ZMod 2} (hw : w 0 = w 1) :
    amp bellState w = 1 := by
  rw [amp_bell_on rfl rfl hw]
  change ampCore 1 0 (0 : DiagPhase (2 + 0) 1) 1 w = 1
  rw [ampCore_zero, realPhase_zero_poly]
  simp

/-! The Bell state's amplitudes, and those of `bellH` from the referee `walshTransform`. -/

theorem amp_bellState_00 : amp bellState ![0, 0] = 1 := amp_bellState_diag (by decide)
theorem amp_bellState_11 : amp bellState ![1, 1] = 1 := amp_bellState_diag (by decide)
theorem amp_bellState_01 : amp bellState ![0, 1] = 0 := amp_bell_off rfl rfl (by decide)
theorem amp_bellState_10 : amp bellState ![1, 0] = 0 := amp_bell_off rfl rfl (by decide)

/-- The Bell state with H on its unread bit: the run of the one-letter word `[H u]`. -/
noncomputable def bellH : KernelSumState (1 + 1) :=
  run (liftUnread 1 ([GateLetter.hadamard 0] : GateWord 1 1)) bellState

/-- `bellH`'s amplitude is the Walsh transform at the unread bit (`amp_run`). -/
private theorem amp_bellH : amp bellH = walshTransform 1 (amp bellState) := by
  exact (amp_run (liftUnread 1 ([GateLetter.hadamard 0] : GateWord 1 1))
    (S := (bellState : KernelSumState (1 + 1))) isCarrier_bellState rfl).trans rfl

/-- Setting bit `1` of a two-bit word. -/
private theorem update_one (a b c : ZMod 2) :
    Function.update (![a, b] : Fin 2 → ZMod 2) 1 c = ![a, c] := by
  funext i
  fin_cases i <;> rfl

theorem amp_bellH_00 : amp bellH ![0, 0] = 1 / (Real.sqrt 2 : ℂ) := by
  rw [amp_bellH]
  unfold walshTransform
  simp only [update_one, amp_bellState_00, amp_bellState_01]
  simp

theorem amp_bellH_01 : amp bellH ![0, 1] = 1 / (Real.sqrt 2 : ℂ) := by
  rw [amp_bellH]
  unfold walshTransform
  simp only [update_one, amp_bellState_00, amp_bellState_01]
  simp

theorem amp_bellH_10 : amp bellH ![1, 0] = 1 / (Real.sqrt 2 : ℂ) := by
  rw [amp_bellH]
  unfold walshTransform
  simp only [update_one, amp_bellState_10, amp_bellState_11]
  simp [signOf_zero]

theorem amp_bellH_11 : amp bellH ![1, 1] = -(1 / (Real.sqrt 2 : ℂ)) := by
  rw [amp_bellH]
  unfold walshTransform
  simp only [update_one, amp_bellState_10, amp_bellState_11]
  simp [signOf_one]

/-- The Lagrangian `⟨X₀, Z₁⟩` of `∣+⟩ ⊗ ∣0⟩`: no `X` on bit `1`, no `Z` on bit `0`. -/
def unreadZeroL : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X 1 = 0 ∧ p.Z 0 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hp hq => ⟨by simp [hp.1, hq.1], by simp [hp.2, hq.2]⟩
  smul_mem' := fun c _ hp => ⟨by simp [hp.1], by simp [hp.2]⟩

/-- `δ_{u=0}` at both read words: `∣+⟩ ⊗ ∣0⟩` at `m = 1`, `h = 0`, `c = 1`. -/
noncomputable def deltaUnreadZero : KernelSumState (1 + 1) := ⟨1, 0, 0, 1, unreadZeroL, 0⟩

/-- `δ_{u=0}`: one where the unread bit is `0`, zero elsewhere. -/
private theorem amp_deltaUnreadZero (a b : ZMod 2) :
    amp deltaUnreadZero ![a, b] = if b = 0 then 1 else 0 := by
  by_cases hb : b = 0
  · rw [if_pos hb]
    refine (amp_pos ⟨⟨![a, b], 0⟩, by change _ ∈ unreadZeroL; exact ⟨hb, rfl⟩,
      (zero_add _).symm⟩).trans ?_
    change ampCore 1 0 (0 : DiagPhase (2 + 0) 1) 1 ![a, b] = 1
    rw [ampCore_zero, realPhase_zero_poly]
    simp
  · rw [if_neg hb]
    refine amp_neg fun ⟨p, hp, hpw⟩ => hb ?_
    change (![a, b] : Fin 2 → ZMod 2) = 0 + p.X at hpw
    rw [zero_add] at hpw
    have h1 := congrFun hpw 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    rw [h1]
    exact hp.1

/-! ## The Gram data on one read bit -/

/-- The read word `x = a` on one read bit. -/
def readWord (a : ZMod 2) : Fin 1 → ZMod 2 := fun _ => a

/-- Every word on one bit is `readWord` of its bit. -/
private theorem eq_readWord (x : Fin 1 → ZMod 2) : x = readWord (x 0) := by
  funext i
  fin_cases i
  rfl

/-- A read word and an unread word on one bit each. -/
private theorem append_readWord (a b : ZMod 2) :
    (Fin.append (readWord a) (readWord b) : Fin (1 + 1) → ZMod 2) = ![a, b] := by
  funext i
  fin_cases i <;> rfl

/-- A sum over the two words of one bit. -/
private theorem sum_fin_one {M : Type*} [AddCommMonoid M] (F : (Fin 1 → ZMod 2) → M) :
    ∑ u, F u = F (readWord 0) + F (readWord 1) := by
  rw [show (Finset.univ : Finset (Fin 1 → ZMod 2)) = {readWord 0, readWord 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The Gram data with one unread bit, its two terms. -/
private theorem gram_one (f : (Fin (1 + 1) → ZMod 2) → ℂ) (a b : ZMod 2) :
    gram f (readWord a) (readWord b)
      = f ![a, 0] * starRingEnd ℂ (f ![b, 0]) + f ![a, 1] * starRingEnd ℂ (f ![b, 1]) := by
  unfold gram
  rw [sum_fin_one, append_readWord, append_readWord, append_readWord, append_readWord]

/-- `UnreadEq 1` from the Gram data at the four pairs of read bits. -/
private theorem unreadEq_one_of {S T : KernelSumState (1 + 1)}
    (h : ∀ a b : ZMod 2,
      gram (amp S) (readWord a) (readWord b) = gram (amp T) (readWord a) (readWord b)) :
    UnreadEq 1 S T := by
  intro x y
  rw [eq_readWord x, eq_readWord y]
  exact h _ _

/-! ## No unread bit: `f` and `−f` -/

/-- `−1` times the register `∣+⟩` on one read bit and no unread bit: the run of the constant
diagonal letter `1` at `m = 1`, a word on the (zero) unread bits. -/
noncomputable def negPlus : KernelSumState (1 + 0) :=
  run (liftUnread 1 ([GateLetter.diagonal (MvPolynomial.C 1)] : GateWord 0 1))
    (plusRegister (1 + 0))

/-- `negPlus` is `−1` everywhere: the letter's referee `charOf 1 1 · f` (`amp_run`). -/
private theorem amp_negPlus (w : Fin (1 + 0) → ZMod 2) : amp negPlus w = -1 := by
  have h := amp_run (liftUnread 1 ([GateLetter.diagonal (MvPolynomial.C 1)] : GateWord 0 1))
    (isCarrier_plusRegister (1 + 0)) rfl
  unfold negPlus
  rw [h]
  change charOf 1 (DiagPhase.eval (MvPolynomial.rename (Fin.natAdd 1) (MvPolynomial.C 1)) w)
      * amp (plusRegister (1 + 0)) w = -1
  rw [amp_plusRegister, MvPolynomial.rename_C]
  simp only [DiagPhase.eval, MvPolynomial.eval_C, charOf_one_one, mul_one]

/-! ## The unqualified drop on the Bell state -/

/-- `dropFreeBit`'s hypothesis at the Bell state's unread bit: `e₁ ∉ π_X(bellL)`. -/
private theorem single_unread_not_mem_shadow :
    (Pi.single (Fin.natAdd 1 (0 : Fin (0 + 1))) 1 : Fin (1 + 0 + 1) → ZMod 2)
      ∉ Submodule.map xProj bellL := by
  intro h
  obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp h
  rw [xProj_apply] at hpX
  have h0 := congrFun hpX 0
  have h1 := congrFun hpX 1
  rw [hp.1] at h0
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- The unqualified drop of the Bell state's unread bit is the constant `1`
(`amp_dropFreeBit`: the sum of `amp` over both values of the bit). -/
private theorem amp_dropBell (w : Fin (1 + 0) → ZMod 2) :
    amp (dropUnread (n := 1) (k := 0) 0 bellState) w = 1 := by
  unfold dropUnread
  rw [amp_dropFreeBit _ _ single_unread_not_mem_shadow]
  change ∑ β : ZMod 2, amp bellState (Fin.insertNth (Fin.last 1) β w) = 1
  simp only [Fin.insertNth_last', sum_zmod_two]
  have hs : ∀ β : ZMod 2, (Fin.snoc w β : Fin 2 → ZMod 2) = ![w 0, β] := by
    intro β
    funext i
    fin_cases i <;> rfl
  rw [hs, hs]
  rcases zmod_two_dichotomy (w 0) with h | h <;> rw [h]
  · rw [amp_bellState_00, amp_bellState_01, add_zero]
  · rw [amp_bellState_10, amp_bellState_11, zero_add]

/-! ## Carriers -/

private theorem isCarrier_tenBell : IsCarrier tenBell := by
  refine ⟨le_rfl, bellL_isStabilizer, bellL_coisotropic, fun h => ?_⟩
  have h0 := congrFun h ![0, 0]
  rw [amp_tenBell_00] at h0
  norm_num at h0

private theorem isCarrier_rotState_one : IsCarrier (rotState 1) := by
  refine ⟨le_rfl, isStabilizer_lagNoZ _, orthogonal_lagNoZ _, fun h => ?_⟩
  have h0 := congrFun h ![0, 0]
  rw [amp_rotState_00] at h0
  norm_num at h0

private theorem isCarrier_tenBellThree : IsCarrier tenBellThree := by
  refine ⟨show 1 ≤ 3 by norm_num, bellL_isStabilizer, bellL_coisotropic, fun h => ?_⟩
  have h0 := congrFun h ![0, 0]
  rw [amp_tenBellThree_00] at h0
  norm_num at h0

private theorem isCarrier_phaseState : IsCarrier phaseState := by
  refine ⟨show 1 ≤ 3 by norm_num, bellL_isStabilizer, bellL_coisotropic, fun h => ?_⟩
  have h0 := congrFun h ![0, 0]
  rw [amp_phaseState_00] at h0
  norm_num at h0

private theorem isCarrier_tenPoint : IsCarrier tenPoint := by
  refine ⟨show 1 ≤ 3 by norm_num, isStabilizer_lagNoZ _, orthogonal_lagNoZ _, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [amp_tenPoint] at h0
  norm_num at h0

private theorem isCarrier_sixEightIPoint : IsCarrier sixEightIPoint := by
  refine ⟨show 1 ≤ 3 by norm_num, isStabilizer_lagNoZ _, orthogonal_lagNoZ _, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [amp_sixEightIPoint] at h0
  have h1 := congrArg Complex.re h0
  norm_num at h1

/-- `unreadZeroL` is isotropic. -/
private theorem isStabilizer_unreadZeroL : IsStabilizer unreadZeroL := by
  intro p hp q hq
  rw [omega_eq_dotF2]
  simp only [dotF2, Fin.sum_univ_two]
  rw [hp.1, hp.2, hq.1, hq.2]
  ring

/-- `unreadZeroL` contains its symplectic complement: `Z₁` forces `X₁ = 0`, `X₀` forces
`Z₀ = 0`. -/
private theorem orthogonal_unreadZeroL :
    LinearMap.BilinForm.orthogonal omegaBilin unreadZeroL ≤ unreadZeroL := by
  intro q hq
  have hx := hq (⟨0, Pi.single 1 1⟩ : Pauli 2) ⟨rfl, rfl⟩
  have hz := hq (⟨Pi.single 0 1, 0⟩ : Pauli 2) ⟨rfl, rfl⟩
  change omega (⟨0, Pi.single 1 1⟩ : Pauli 2) q = 0 at hx
  change omega (⟨Pi.single 0 1, 0⟩ : Pauli 2) q = 0 at hz
  rw [omega_eq_dotF2, dotF2_single_left] at hx hz
  simp only [dotF2, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add] at hx hz
  exact ⟨hx, hz⟩

private theorem isCarrier_deltaUnreadZero : IsCarrier deltaUnreadZero := by
  refine ⟨le_rfl, isStabilizer_unreadZeroL, orthogonal_unreadZeroL, fun h => ?_⟩
  have h0 := congrFun h ![0, 0]
  rw [amp_deltaUnreadZero, if_pos rfl] at h0
  exact one_ne_zero h0

/-! ## The rows -/

/-- `1/√2` is real. -/
private theorem conj_inv_sqrt_two :
    starRingEnd ℂ (1 / (Real.sqrt 2 : ℂ)) = 1 / (Real.sqrt 2 : ℂ) := by
  rw [map_div₀, map_one, Complex.conj_ofReal]

/-- `(1/√2)² = 1/2`. -/
private theorem inv_sqrt_two_mul_self :
    1 / (Real.sqrt 2 : ℂ) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul, sqrt_two_mul_self]

-- row: agreement A1
/-- **A1.** The Bell state and H on its unread bit have the same Gram data, the identity, and the
move (b) with the word `[H u]` relates them; they are not `StateEq` (`0` against `1/√2` at
`(0, 1)`). The relation and the extended theory agree on the pair. -/
theorem row_bell_hadamard_unread :
    UnreadEq 1 bellState bellH ∧ UnreadDerivable (⟨1, bellState⟩ : UnreadState 1) ⟨1, bellH⟩ ∧
      ¬ StateEq bellState bellH := by
  refine ⟨unreadEq_one_of fun a b => ?_,
    Relation.EqvGen.rel _ _ (UnreadMove.runUnread _ isCarrier_bellState rfl), fun h => ?_⟩
  · rcases zmod_two_dichotomy a with rfl | rfl <;> rcases zmod_two_dichotomy b with rfl | rfl <;>
      simp only [gram_one, amp_bellState_00, amp_bellState_01, amp_bellState_10, amp_bellState_11,
        amp_bellH_00, amp_bellH_01, amp_bellH_10, amp_bellH_11, map_neg, map_one, map_zero,
        conj_inv_sqrt_two, mul_one, mul_zero, add_zero, zero_add, mul_neg, neg_mul,
        neg_neg, inv_sqrt_two_mul_self] <;> norm_num
  · have h01 := congrFun h ![0, 1]
    rw [amp_bellState_01, amp_bellH_01] at h01
    exact one_div_ne_zero ofReal_sqrt_two_ne_zero h01.symm

-- row: agreement A2
/-- **A2.** With no unread bit, `∣+⟩` and its negation by the constant diagonal letter `1` have
the same Gram data and the move (b) relates them; they are not `StateEq`, and the second is the
first times `−1`, the unit-modulus scalar `unreadEq_zero_iff` names, read off the amplitudes. -/
theorem row_neg_no_unread :
    UnreadEq 0 (plusRegister (1 + 0)) negPlus ∧
      UnreadDerivable (⟨0, plusRegister (1 + 0)⟩ : UnreadState 1) ⟨0, negPlus⟩ ∧
      ¬ StateEq (plusRegister (1 + 0)) negPlus ∧
      amp negPlus = (-1 : ℂ) • amp (plusRegister (1 + 0)) := by
  refine ⟨fun x y => ?_,
    Relation.EqvGen.rel _ _ (UnreadMove.runUnread _ (isCarrier_plusRegister (1 + 0)) rfl),
    fun h => ?_, ?_⟩
  · rw [gram_zero, gram_zero, amp_plusRegister, amp_plusRegister, amp_negPlus, amp_negPlus]
    simp
  · have h0 := congrFun h 0
    rw [amp_plusRegister, amp_negPlus] at h0
    norm_num at h0
  · funext w
    rw [amp_negPlus, Pi.smul_apply, amp_plusRegister, smul_eq_mul, mul_one]

-- row: discriminating D1
/-- **D1.** `δ_{u=0}` at both read words (Gram data all ones) against the Bell state (the
identity), both carriers: not `UnreadEq`, at the read words `(0, 1)`. -/
theorem row_delta_against_bell :
    IsCarrier deltaUnreadZero ∧ IsCarrier bellState ∧ ¬ UnreadEq 1 deltaUnreadZero bellState := by
  refine ⟨isCarrier_deltaUnreadZero, isCarrier_bellState, fun h => ?_⟩
  have h01 := h (readWord 0) (readWord 1)
  rw [gram_one, gram_one, amp_deltaUnreadZero, amp_deltaUnreadZero, amp_deltaUnreadZero,
    amp_deltaUnreadZero, amp_bellState_00, amp_bellState_01, amp_bellState_10,
    amp_bellState_11] at h01
  norm_num at h01

/-- `UnreadEq 1` of two states whose amplitudes are tabulated above, case by case. -/
local macro "gram_cases" : tactic =>
  `(tactic| (
    refine unreadEq_one_of fun a b => ?_
    rcases zmod_two_dichotomy a with ha | ha <;> rcases zmod_two_dichotomy b with hb | hb <;>
      subst ha hb <;>
      simp only [gram_one, amp_bellState_00, amp_bellState_01, amp_bellState_10,
        amp_bellState_11, amp_tenBell_00, amp_tenBell_01, amp_tenBell_10, amp_tenBell_11,
        amp_rotState_00,
        amp_rotState_01, amp_rotState_10, amp_rotState_11, amp_tenBellThree_00,
        amp_tenBellThree_01, amp_tenBellThree_10, amp_tenBellThree_11, amp_phaseState_00,
        amp_phaseState_01, amp_phaseState_10, amp_phaseState_11, map_ofNat, map_div₀, map_mul,
        map_add, map_neg, map_zero, map_one, Complex.conj_I] <;>
      apply Complex.ext <;> simp <;> norm_num))

-- row: discriminating D2
/-- **D2.** The Bell state against its image under the rotation `[[3, −4], [4, 3]]/5` on the
unread bit, `(3, 4, −4, 3)/5`: the same Gram data (the identity) and not `StateEq`; the scale ratio
`2/5` is not dyadic, so the pair fails by D9's scale gap, not by the isometry. -/
theorem row_bell_rotated :
    UnreadEq 1 bellState (rotState (2 / 5)) ∧ ¬ StateEq bellState (rotState (2 / 5)) ∧
      ¬ IsDyadicRatio ((rotState (2 / 5)).c / bellState.c) := by
  refine ⟨by gram_cases, fun h => ?_, ?_⟩
  · have h01 := congrFun h ![0, 1]
    rw [amp_bellState_01, amp_rotState_01] at h01
    norm_num at h01
  · change ¬ IsDyadicRatio ((2 / 5 : ℂ) / 1)
    rw [div_one]
    exact not_isDyadicRatio_two_fifths

-- row: discriminating O1
/-- **O1.** `r = 10, 0, 0, 10` against `r = 6, 8, −8, 6`, both at `m = 1`, `h = 4`, `c = 1`:
the same Gram data (`25/4` times the identity; the cross term is `6·(−8) + 8·6 = 0`), not
`StateEq`, at scale ratio one. -/
theorem row_ten_against_rotation :
    UnreadEq 1 tenBell (rotState 1) ∧ ¬ StateEq tenBell (rotState 1) ∧
      (rotState 1).c / tenBell.c = 1 := by
  refine ⟨by gram_cases, fun h => ?_, by norm_num [rotState, tenBell]⟩
  have h01 := congrFun h ![0, 1]
  rw [amp_tenBell_01, amp_rotState_01] at h01
  norm_num at h01

-- row: inhabitation
/-- **O1's hypotheses.** Both states of O1 are carriers and their scale ratio is dyadic: the
hypotheses of `unreadEq_derivable_iff`, with its scale clause, hold together on a pair with equal
Gram data. -/
theorem row_ten_rotation_hypotheses :
    IsCarrier tenBell ∧ IsCarrier (rotState 1) ∧ IsDyadicRatio ((rotState 1).c / tenBell.c) := by
  refine ⟨isCarrier_tenBell, isCarrier_rotState_one, 1, 0, 0, by norm_num, ?_⟩
  norm_num [rotState, tenBell]

-- row: discriminating O2
/-- **O2.** At `m = 3`, `r = 10, 0, 0, 10` against `r = 10, 0, 0, 6 + 8i`: both carriers, the
same Gram data (`|6 + 8i|² = 100`), not `StateEq` (the imaginary parts differ at `(1, 1)`), scale
ratio one. -/
theorem row_ten_against_phase :
    IsCarrier tenBellThree ∧ IsCarrier phaseState ∧ UnreadEq 1 tenBellThree phaseState ∧
      ¬ StateEq tenBellThree phaseState ∧ phaseState.c / tenBellThree.c = 1 := by
  refine ⟨isCarrier_tenBellThree, isCarrier_phaseState, by gram_cases, fun h => ?_,
    by norm_num [phaseState, tenBellThree]⟩
  have h11 := congrArg Complex.im (congrFun h ![1, 1])
  rw [amp_tenBellThree_11, amp_phaseState_11] at h11
  norm_num at h11

-- row: discriminating
/-- **O2, the conjugate.** Without the conjugate the sum over the unread bit at `x = y = 1`
separates O2's pair: `(5/2)²` is real, `((6 + 8i)/4)²` is not. A Gram sum that dropped the
conjugate would refute O2's `UnreadEq`; at `m = 1` no row sees it. -/
theorem row_ten_against_phase_unconjugated :
    ∑ u : Fin 1 → ZMod 2, amp tenBellThree (Fin.append (readWord 1) u)
        * amp tenBellThree (Fin.append (readWord 1) u)
      ≠ ∑ u : Fin 1 → ZMod 2, amp phaseState (Fin.append (readWord 1) u)
        * amp phaseState (Fin.append (readWord 1) u) := by
  rw [sum_fin_one, sum_fin_one, append_readWord, append_readWord, amp_tenBellThree_10,
    amp_tenBellThree_11, amp_phaseState_10, amp_phaseState_11]
  intro h
  have him := congrArg Complex.im h
  norm_num at him

-- row: discriminating O4
/-- **O4.** No unread bit, at `m = 3`: `r = 10` against `r = 6 + 8i` at both read words. Both
carriers, `UnreadEq 0`, not `StateEq`, scale ratio one, and the unconjugated product
`f(0)·f(0)` differs. -/
theorem row_ten_against_phase_no_unread :
    IsCarrier tenPoint ∧ IsCarrier sixEightIPoint ∧ UnreadEq 0 tenPoint sixEightIPoint ∧
      ¬ StateEq tenPoint sixEightIPoint ∧ sixEightIPoint.c / tenPoint.c = 1 ∧
      amp tenPoint 0 * amp tenPoint 0 ≠ amp sixEightIPoint 0 * amp sixEightIPoint 0 := by
  refine ⟨isCarrier_tenPoint, isCarrier_sixEightIPoint, fun x y => ?_, fun h => ?_,
    by norm_num [sixEightIPoint, tenPoint], ?_⟩
  · rw [gram_zero, gram_zero, amp_tenPoint, amp_tenPoint, amp_sixEightIPoint, amp_sixEightIPoint]
    simp only [map_ofNat, map_div₀, map_mul, map_add, Complex.conj_I]
    apply Complex.ext <;> simp <;> norm_num
  · have h0 := congrArg Complex.im (congrFun h 0)
    rw [amp_tenPoint, amp_sixEightIPoint] at h0
    norm_num at h0
  · rw [amp_tenPoint, amp_sixEightIPoint]
    intro h
    have him := congrArg Complex.im h
    norm_num at him

-- row: discriminating C1
/-- **C1.** The unqualified drop of the Bell state's unread bit: `dropFreeBit`'s hypothesis
`e₁ ∉ π_X(L)` holds (the support determines `u = x`), the move's hypothesis `DeterminedByUnread`
does not (`e₁ = (1, 1) + e₀`), and the drop changes the Gram data from the identity to all ones,
at the read words `(0, 1)`. -/
theorem row_unqualified_drop :
    (Pi.single (Fin.natAdd 1 (0 : Fin (0 + 1))) 1 : Fin (1 + 0 + 1) → ZMod 2)
        ∉ Submodule.map xProj bellState.L ∧
      ¬ DeterminedByUnread (n := 1) (k := 1) bellState 0 ∧
      gram (amp (dropUnread (n := 1) (k := 0) 0 bellState))
        ≠ gram (n := 1) (k := 1) (amp bellState) := by
  refine ⟨single_unread_not_mem_shadow, fun hj => hj ?_, fun h => ?_⟩
  · have hsum : (Pi.single (Fin.natAdd 1 (0 : Fin 1)) 1 : Fin (1 + 1) → ZMod 2)
        = ![1, 1] + Pi.single (Fin.castAdd 1 (0 : Fin 1)) 1 := by
      decide
    rw [hsum]
    refine Submodule.add_mem_sup (Submodule.mem_map.mpr ⟨⟨![1, 1], 0⟩, ⟨rfl, rfl⟩, rfl⟩) ?_
    exact Submodule.subset_span ⟨0, rfl⟩
  · have h01 := congrFun (congrFun h (readWord 0)) (readWord 1)
    rw [gram_zero, amp_dropBell, amp_dropBell, gram_one, amp_bellState_00, amp_bellState_01,
      amp_bellState_10, amp_bellState_11] at h01
    norm_num at h01

/-- The read functions of `f`, combined with coefficients `c` in the ring, at the read word `a`. -/
private theorem span_readFunction_apply (f : (Fin (1 + 1) → ZMod 2) → ℂ)
    (c : (Fin 1 → ZMod 2) → dyadicCyclotomicRing) (a : ZMod 2) :
    (∑ u, c u • readFunction f u) (readWord a)
      = (c (readWord 0) : ℂ) * f ![a, 0] + (c (readWord 1) : ℂ) * f ![a, 1] := by
  rw [Finset.sum_apply, sum_fin_one]
  simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, readFunction, append_readWord]

-- row: discriminating O1-underivable
/-- **O1 is not derivable.** The read function of `rotState 1` at `u = 0` is `(6/4, −8/4)`; in the
module of `tenBell`'s read functions `(5/2, 0)` and `(0, 5/2)` it would need the coefficient `3/5`,
which is not in `ℤ[ζ_{2^∞}, ½]` (`intCast_div_five_not_mem_dyadicCyclotomicRing`). With O1's equal
Gram data and dyadic scale ratio (rows O1 and its hypotheses), the pair is outside the derivable
set by the invariant `readModule_eq_of_derivable`, through
`not_unreadDerivable_of_readFunction_not_mem`: the obstruction is the isometry, not the scale. -/
theorem row_ten_rotation_not_derivable :
    ¬ UnreadDerivable (n := 1) ⟨1, tenBell⟩ ⟨1, rotState 1⟩ := by
  refine not_unreadDerivable_of_readFunction_not_mem (B := ⟨1, rotState 1⟩) (readWord 0)
    fun h => ?_
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  have h0 := congrFun hc (readWord 0)
  rw [span_readFunction_apply, amp_tenBell_00, amp_tenBell_01] at h0
  change _ = amp (rotState 1) (Fin.append (readWord 0) (readWord 0)) at h0
  rw [append_readWord, amp_rotState_00] at h0
  have hc0 : (c (readWord 0) : ℂ) = ((3 : ℤ) : ℂ) / 5 := by
    push_cast
    linear_combination (2 / 5 : ℂ) * h0
  exact intCast_div_five_not_mem_dyadicCyclotomicRing (by decide) (hc0 ▸ (c (readWord 0)).2)

-- row: discriminating O2-underivable
/-- **O2 is not derivable.** The read function of `phaseState` at `u = 1` is `(0, (6 + 8i)/4)`; in
the module of `tenBellThree`'s read functions it would need the coefficient `(3 + 4i)/5`, and then,
the ring being closed under conjugation, `6/5 = (3 + 4i)/5 + (3 − 4i)/5` would lie in it, which it
does not. Equal Gram data at scale ratio one (row O2), not derivable, at `m = 3`. -/
theorem row_ten_phase_not_derivable :
    ¬ UnreadDerivable (n := 1) ⟨1, tenBellThree⟩ ⟨1, phaseState⟩ := by
  refine not_unreadDerivable_of_readFunction_not_mem (B := ⟨1, phaseState⟩) (readWord 1)
    fun h => ?_
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h
  have h1 := congrFun hc (readWord 1)
  rw [span_readFunction_apply, amp_tenBellThree_10, amp_tenBellThree_11] at h1
  change _ = amp phaseState (Fin.append (readWord 1) (readWord 1)) at h1
  rw [append_readWord, amp_phaseState_11] at h1
  set z : ℂ := (c (readWord 1) : ℂ) with hz
  have hz' : z = (3 + 4 * Complex.I) / 5 := by linear_combination (2 / 5 : ℂ) * h1
  have hmem : z ∈ dyadicCyclotomicRing := (c (readWord 1)).2
  have hsum : z + starRingEnd ℂ z = ((6 : ℤ) : ℂ) / 5 := by
    rw [hz', map_div₀, map_add, map_mul, Complex.conj_I]
    push_cast
    simp only [map_ofNat]
    ring
  exact intCast_div_five_not_mem_dyadicCyclotomicRing (by decide)
    (hsum ▸ Subring.add_mem _ hmem (starRingEnd_mem_dyadicCyclotomicRing hmem))

/-! ## The mutant: the Gram sum's conjugate -/

-- mutant: gram_drop_conjugate | FTQCLib/Carrier/UnreadBits.lean
--   | f (Fin.append x u) * starRingEnd ℂ (f (Fin.append y u))
--   | f (Fin.append x u) * f (Fin.append y u)

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_equivalence' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_equivalence

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_of_stateEq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_of_stateEq

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_zero_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_zero_iff

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_of_eqvGen_carrierRule' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_of_eqvGen_carrierRule

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_of_run_unread' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_of_run_unread

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_of_dropUnread' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_of_dropUnread

/-- info: 'FTQCLib.Frame.Walkthrough.gram_eq_of_derivable' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gram_eq_of_derivable

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_iff_exists_isometry' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_iff_exists_isometry

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_derivable_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unreadEq_derivable_iff

/-- info: 'FTQCLib.Frame.Walkthrough.readModule_eq_of_derivable' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms readModule_eq_of_derivable

/-- info: 'FTQCLib.Frame.Walkthrough.exists_two_pow_mul_isIntegral' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_two_pow_mul_isIntegral

/-- info: 'FTQCLib.Frame.Walkthrough.starRingEnd_mem_dyadicCyclotomicRing' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms starRingEnd_mem_dyadicCyclotomicRing

/-- info: 'FTQCLib.Frame.Walkthrough.exists_two_pow_mul_eq_int_of_ratCast_mem' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_two_pow_mul_eq_int_of_ratCast_mem

/-- info: 'FTQCLib.Frame.Walkthrough.intCast_div_five_not_mem_dyadicCyclotomicRing' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms intCast_div_five_not_mem_dyadicCyclotomicRing

/-- info: 'FTQCLib.Frame.Walkthrough.not_unreadDerivable_of_readFunction_not_mem' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_unreadDerivable_of_readFunction_not_mem

/-- info: 'FTQCLib.Frame.Walkthrough.gram_eq_mul_conjTranspose' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gram_eq_mul_conjTranspose

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_iff_mul_conjTranspose_eq' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unreadEq_iff_mul_conjTranspose_eq

/-- info: 'FTQCLib.Frame.Walkthrough.unreadEq_iff_exists_unitary_mul' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unreadEq_iff_exists_unitary_mul

/-- info: 'FTQCLib.Frame.Walkthrough.gram_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.gram_zero

end FTQCLib.Frame.Walkthrough

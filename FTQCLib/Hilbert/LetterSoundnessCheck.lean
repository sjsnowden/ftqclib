/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.LetterSoundness

/-!
# Check: a letter's referee against its Hilbert gate on basis states

T18's witness (`docs/STEPS.md`, T18.2): rows on the frozen statement of `LetterSoundness.lean`,
computed from the definitions of the frame's referee `letterAmp` (through `walshTransform`,
`charOf`, `DiagPhase.cnotBitMap`) and of T17's Hilbert gate `letterGate` (through `hadamardGate`,
`diagonalGate`, `cnotGate`), never through `letterAmp_eq_gate` or `runAmp_eq_wordGate`. Both are
now proved, at T18.3: `letterAmp_eq_gate` for every letter, `runAmp_eq_wordGate` for every word.
The agreement and discriminating rows below are the witness's: they do not use either theorem,
computing each side from its own definition instead. The inhabitation row below is new at this
step; it uses `letterAmp_eq_gate` directly, on a concrete letter and a concrete word, as the
object the sweep below also names.

**Conventions.** A word `ab` on two bits is `![a, b]`: its first letter is bit `0`. The basis state
`|x⟩` is `ket x`, the function that is `1` at the word `x` and `0` elsewhere. Each side of an
agreement row is computed separately, from its own definition, to an explicit function, and the
row joins the two computations.

* **H on bit 0 of `|01⟩` (agreement).** Both sides are `(|01⟩ + |11⟩)/√2` (`hadamardOutput`):
  `1/√2` at the words whose bit `1` is `1`, and `0` elsewhere.
* **T at `m = 3` on `|1⟩` (agreement).** The letter is `diagonal (tGatePoly 0)` on one bit, the
  exponent `x₀` in `ZMod 8`; both sides are `e^{iπ/4}|1⟩` (`tOutput`).
* **CNOT from bit 0 to bit 1 on `|10⟩` (agreement).** Both sides are `|11⟩`.
* **CNOT with control and target swapped (discriminating).** On `|10⟩` the referee of CNOT from
  bit `0` to bit `1` is `|11⟩`, while the Hilbert gate of CNOT from bit `1` to bit `0` leaves
  `|10⟩` where it is: at the word `11` the first is `1` and the second `0`. So the referee of a
  CNOT letter is not the gate with its bits swapped, which a convention error in `cnotBitMap` or
  `cnotPerm` would produce.

Every row is about `letterAmp g`, the object `letterAmp_eq_gate` names, on a concrete letter and a
concrete basis state, compared with `letterGate g'` there.
-/

namespace FTQCLib.Hilbert.LetterSoundnessCheck

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert FTQCLib.Frame.Walkthrough

/-! ## The instance -/

/-- The basis state `|x⟩`: `1` at the word `x`, `0` elsewhere. -/
noncomputable def ket {n : ℕ} (x : Fin n → ZMod 2) : QubitSpace n :=
  fun w => if w = x then 1 else 0

/-- The H letter on bit `0` of two bits. -/
def hadamardZero : GateLetter 2 3 := .hadamard 0

/-- The T letter on one bit at precision `3`: the exponent `x₀` in `ZMod 8`. -/
noncomputable def tLetter : GateLetter 1 3 := .diagonal (DiagPhase.tGatePoly 0)

/-- CNOT with control bit `0` and target bit `1`. -/
def cnotZeroOne : GateLetter 2 3 := .cnot 0 1 (by decide)

/-- CNOT with control bit `1` and target bit `0`: `cnotZeroOne` with its bits swapped. -/
def cnotOneZero : GateLetter 2 3 := .cnot 1 0 (by decide)

/-- `(|01⟩ + |11⟩)/√2`: `1/√2` at the words whose bit `1` is `1`, `0` elsewhere. -/
noncomputable def hadamardOutput : QubitSpace 2 :=
  fun w => if w 1 = 1 then invSqrt2 else 0

/-- `e^{iπ/4}|1⟩` on one bit. -/
noncomputable def tOutput : QubitSpace 1 :=
  fun w => if w 0 = 1 then Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) else 0

/-! ## Private computations -/

private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

private theorem word_two_eq (w : Fin 2 → ZMod 2) : w = ![w 0, w 1] := by
  funext i
  fin_cases i <;> rfl

private theorem sum_zmod2 (f : ZMod 2 → ℂ) : ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

private theorem update_two_zero (a b c : ZMod 2) :
    Function.update ![a, b] (0 : Fin 2) c = ![c, b] := by
  funext i
  fin_cases i <;> rfl

private theorem cnotBitMap_zero_one (a b : ZMod 2) :
    DiagPhase.cnotBitMap 0 1 ![a, b] = ![a, b + a] := by
  funext i
  fin_cases i <;> rfl

private theorem cnotPerm_zero_one (a b : ZMod 2) : cnotPerm 0 1 ![a, b] = ![a, b + a] := by
  funext i
  fin_cases i <;> rfl

private theorem cnotPerm_one_zero (a b : ZMod 2) : cnotPerm 1 0 ![a, b] = ![a + b, b] := by
  funext i
  fin_cases i <;> rfl

private theorem one_div_sqrt_two : 1 / (Real.sqrt 2 : ℂ) = invSqrt2 := by
  rw [invSqrt2, Complex.ofReal_inv, one_div]

/-- The exponent of T at a one-bit word whose bit is `1` has value `1` in `ZMod 8`. -/
private theorem tGatePoly_eval_val (w : Fin 1 → ZMod 2) (hw : w 0 = 1) :
    ((DiagPhase.tGatePoly 0 : DiagPhase 1 3).eval w).val = 1 := by
  rw [DiagPhase.tGatePoly, DiagPhase.eval_X, hw]
  decide

/-- The phase angle of an exponent of value `1` at precision `3` is `π/4`. -/
private theorem angle_of_val_one : 2 * Real.pi * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 3 = Real.pi / 4 := by
  push_cast
  ring

/-- The referee of H on bit `0` of `|01⟩`, from `walshTransform`. -/
private theorem letterAmp_hadamardZero :
    letterAmp hadamardZero (ket ![0, 1]) = hadamardOutput := by
  funext w
  rw [word_two_eq w]
  simp only [hadamardZero, letterAmp, walshTransform, hadamardOutput, ket, one_div_sqrt_two]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    rw [h0, h1] <;> simp [update_two_zero, signOf]

/-- The Hilbert gate of H on bit `0` of `|01⟩`, from `hadamardGate`. -/
private theorem letterGate_hadamardZero :
    letterGate hadamardZero (ket ![0, 1]) = hadamardOutput := by
  funext w
  rw [word_two_eq w]
  simp only [hadamardZero, letterGate, hadamardGate_apply, hadamardOutput, ket]
  rw [sum_zmod2]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    rw [h0, h1] <;> simp [update_two_zero]

/-- The referee of T at `m = 3` on `|1⟩`, from `charOf`. -/
private theorem letterAmp_tLetter : letterAmp tLetter (ket ![1]) = tOutput := by
  funext w
  have hw : w = ![w 0] := by
    funext i
    fin_cases i
    rfl
  simp only [tLetter, letterAmp, tOutput, ket, charOf]
  rcases zmod2_cases (w 0) with h0 | h0
  · rw [hw, h0]
    simp
  · rw [tGatePoly_eval_val w h0, angle_of_val_one, hw, h0]
    simp

/-- The Hilbert gate of T at `m = 3` on `|1⟩`, from `diagonalGate` and `realPhase`. -/
private theorem letterGate_tLetter : letterGate tLetter (ket ![1]) = tOutput := by
  funext w
  have hw : w = ![w 0] := by
    funext i
    fin_cases i
    rfl
  simp only [tLetter, letterGate, diagonalGate_apply, tOutput, ket, DiagPhase.realPhase]
  rcases zmod2_cases (w 0) with h0 | h0
  · rw [hw, h0]
    simp
  · rw [tGatePoly_eval_val w h0, angle_of_val_one, hw, h0]
    simp

/-- The referee of CNOT from bit `0` to bit `1` on `|10⟩`, from `cnotBitMap`. -/
private theorem letterAmp_cnotZeroOne : letterAmp cnotZeroOne (ket ![1, 0]) = ket ![1, 1] := by
  funext w
  rw [word_two_eq w]
  simp only [cnotZeroOne, letterAmp, ket, cnotBitMap_zero_one]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    rw [h0, h1] <;> simp [zmod2_one_add_one]

/-- The Hilbert gate of CNOT from bit `0` to bit `1` on `|10⟩`, from `cnotGate`. -/
private theorem letterGate_cnotZeroOne : letterGate cnotZeroOne (ket ![1, 0]) = ket ![1, 1] := by
  funext w
  rw [word_two_eq w]
  simp only [cnotZeroOne, letterGate, LinearEquiv.coe_coe, cnotGate_apply, ket,
    cnotPerm_zero_one]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    rw [h0, h1] <;> simp [zmod2_one_add_one]

/-- The Hilbert gate of CNOT from bit `1` to bit `0` on `|10⟩` at the word `11` is `0`. -/
private theorem letterGate_cnotOneZero_at :
    letterGate cnotOneZero (ket ![1, 0]) ![1, 1] = 0 := by
  simp only [cnotOneZero, letterGate, LinearEquiv.coe_coe, cnotGate_apply, ket,
    cnotPerm_one_zero]
  simp [zmod2_one_add_one]

/-! ## Rows -/

/-- **H on bit 0 of `|01⟩`.** The referee and the Hilbert gate agree there. -/
-- row: agreement
theorem letterAmp_hadamardZero_ket :
    letterAmp hadamardZero (ket ![0, 1]) = letterGate hadamardZero (ket ![0, 1]) := by
  rw [letterAmp_hadamardZero, letterGate_hadamardZero]

/-- **T at `m = 3` on `|1⟩`.** The referee and the Hilbert gate agree there. -/
-- row: agreement
theorem letterAmp_tLetter_ket : letterAmp tLetter (ket ![1]) = letterGate tLetter (ket ![1]) := by
  rw [letterAmp_tLetter, letterGate_tLetter]

/-- **CNOT on `|10⟩`.** The referee and the Hilbert gate agree there. -/
-- row: agreement
theorem letterAmp_cnotZeroOne_ket :
    letterAmp cnotZeroOne (ket ![1, 0]) = letterGate cnotZeroOne (ket ![1, 0]) := by
  rw [letterAmp_cnotZeroOne, letterGate_cnotZeroOne]

/-- **CNOT against its swap on `|10⟩`.** The referee of CNOT from bit `0` to bit `1` differs from
the Hilbert gate of CNOT from bit `1` to bit `0` at the word `11`: `1` against `0`. -/
-- row: discriminating
theorem letterAmp_cnotZeroOne_ne_swap :
    letterAmp cnotZeroOne (ket ![1, 0]) ![1, 1] ≠ letterGate cnotOneZero (ket ![1, 0]) ![1, 1] := by
  rw [letterAmp_cnotZeroOne, letterGate_cnotOneZero_at]
  simp [ket]

/-- **The headline holds together at a concrete letter.** `letterAmp_eq_gate`'s hypotheses are
just the letter `g`'s own type; at the concrete letter `cnotZeroOne` it gives an equality of
functions, read pointwise at `|10⟩`: the referee and the Hilbert gate agree there, by the headline
theorem itself, not by recomputing either side. -/
-- row: inhabitation
theorem letterAmp_eq_gate_cnotZeroOne_inhabits :
    letterAmp cnotZeroOne (ket ![1, 0]) = letterGate cnotZeroOne (ket ![1, 0]) := by
  rw [letterAmp_eq_gate]

end FTQCLib.Hilbert.LetterSoundnessCheck

/-! ## The axiom sweep — build-failing, every public theorem of the topic module -/

/-- info: 'FTQCLib.Hilbert.letterAmp_eq_gate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.letterAmp_eq_gate

/-- info: 'FTQCLib.Hilbert.runAmp_eq_wordGate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.runAmp_eq_wordGate

/-! ## Declared mutants, aimed at a definition's conclusion a proof uses -/

-- mutant: one_div_sqrt_two | FTQCLib/Hilbert/LetterSoundness.lean
--   | 1 / (Real.sqrt 2 : ℂ) = invSqrt2
--   | 1 / (Real.sqrt 2 : ℂ) = -invSqrt2
-- mutant: zmod2_val_one | FTQCLib/Hilbert/LetterSoundness.lean | (1 : ZMod 2).val = 1
--   | (1 : ZMod 2).val = 0

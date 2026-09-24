/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.LastVariable

/-!
# Acceptance rows for the last variable of a phase exponent

* **The coupling's difference** (discriminating, the frame's own instance): the difference of the
  Hadamard coupling `c·X₀·X_last` along the last variable is `c·X₀` — a polynomial identity through
  `bind₁`, not through evaluation.
* **A constant has no difference; the last variable itself has difference `1`** — the two ends of
  the additivity lemmas, as polynomial identities.
* **Agreement**: the difference of `X₀·X₁` at `m = 1` read through `lastDiff_eval` and through the
  bridge `lastDiff_eval_eq_funcDerivEval` give the same value at the word `1`.

`DiagPhase.eval` is noncomputable, so the evaluation rows are `rw` rows on named exponents, not
kernel rows; the polynomial identities are closed by the `bind₁` lemmas. -/

namespace FTQCLib.Hierarchy.DiagPhase

variable {m : ℕ}

/-! ## The two bits as constants -/

/-- The bit `1` casts to `1`. -/
theorem cast_val_one : (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ m)) = 1 := by
  rw [show (1 : ZMod 2).val = 1 by decide, Nat.cast_one]

/-- The bit `0` casts to `0`. -/
theorem cast_val_zero : (((0 : ZMod 2).val : ℕ) : ZMod (2 ^ m)) = 0 := by
  rw [ZMod.val_zero, Nat.cast_zero]

/-! ## The coupling's difference -/

/-- The Hadamard coupling `c·X₀·X_last` on two variables differences to `c·X₀`. -/
theorem lastDiff_coupling (c : ZMod (2 ^ m)) :
    lastDiff (MvPolynomial.C c * (MvPolynomial.X (Fin.castSucc 0) * MvPolynomial.X (Fin.last 1))
        : DiagPhase 2 m)
      = MvPolynomial.C c * MvPolynomial.X 0 := by
  unfold lastDiff snocFreeze
  rw [map_mul, map_mul, map_mul, map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_C_right,
    MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right,
    MvPolynomial.bind₁_X_right, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_last,
    cast_val_one, cast_val_zero, map_one, map_zero]
  ring

/-! ## The two ends -/

/-- The last variable itself has difference `1`. -/
theorem lastDiff_X_last : lastDiff (MvPolynomial.X (Fin.last 1) : DiagPhase 2 m) = 1 := by
  unfold lastDiff snocFreeze
  rw [MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right, Fin.snoc_last, Fin.snoc_last,
    cast_val_one, cast_val_zero, map_one, map_zero, sub_zero]

/-- A constant has difference `0` (through the lemma). -/
theorem lastDiff_C_two : lastDiff (MvPolynomial.C (2 : ZMod (2 ^ 2)) : DiagPhase 2 2) = 0 :=
  lastDiff_C 2

/-! ## Agreement of the two evaluation routes -/

/-- The word `![1]` extended by a bit is the two-bit word `![1, b]`. -/
theorem snoc_one (b : ZMod 2) :
    (Fin.snoc (![1] : Fin 1 → ZMod 2) b : Fin 2 → ZMod 2) = ![1, b] := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
    rfl
  · intro j
    rw [Fin.snoc_castSucc]
    fin_cases j
    rfl

/-- `X₀·X₁` at `m = 1` evaluates to the product of the bits. -/
theorem eval_XX (v : Fin 2 → ZMod 2) :
    DiagPhase.eval (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1) v
      = ((v 0).val : ZMod (2 ^ 1)) * ((v 1).val : ZMod (2 ^ 1)) := by
  unfold DiagPhase.eval DiagPhase.liftBinary
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]

/-- Through `lastDiff_eval`: the difference of `X₀·X₁` along `X₁` at the word `1` is `1`. -/
theorem lastDiff_XX_direct :
    (lastDiff (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)).eval ![1] = 1 := by
  rw [lastDiff_eval, snoc_one, snoc_one, eval_XX, eval_XX]
  decide

/-- Through the bridge: the same value from the functional derivative on the zero slice. -/
theorem lastDiff_XX_bridge :
    (lastDiff (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)).eval ![1]
      = funcDerivEval (Fin.last 1) (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)
          (Fin.snoc ![1] 0) :=
  lastDiff_eval_eq_funcDerivEval _ _

/-- **Agreement.** The functional derivative on the zero slice is `1` as well. -/
theorem funcDerivEval_XX_slice :
    funcDerivEval (Fin.last 1) (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1)
        (Fin.snoc ![1] 0) = 1 := by
  rw [← lastDiff_XX_bridge, lastDiff_XX_direct]

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Hierarchy.DiagPhase.snocFreeze' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms snocFreeze

/-- info: 'FTQCLib.Hierarchy.DiagPhase.snocFreeze_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms snocFreeze_eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.snocFreeze_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms snocFreeze_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.snocFreeze_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms snocFreeze_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms lastDiff

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_eval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_add

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_C

/-- info: 'FTQCLib.Hierarchy.DiagPhase.snoc_zero_add_single_last' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms snoc_zero_add_single_last

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_eval_eq_funcDerivEval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_eval_eq_funcDerivEval

/-- info: 'FTQCLib.Hierarchy.DiagPhase.cast_val_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cast_val_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.cast_val_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cast_val_zero

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_coupling' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_coupling

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_C_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_C_two

/-- info: 'FTQCLib.Hierarchy.DiagPhase.snoc_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms snoc_one

/-- info: 'FTQCLib.Hierarchy.DiagPhase.eval_XX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms eval_XX

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_XX_bridge' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_XX_bridge

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_X_last' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_X_last

/-- info: 'FTQCLib.Hierarchy.DiagPhase.lastDiff_XX_direct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lastDiff_XX_direct

/-- info: 'FTQCLib.Hierarchy.DiagPhase.funcDerivEval_XX_slice' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms funcDerivEval_XX_slice

end FTQCLib.Hierarchy.DiagPhase

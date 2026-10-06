/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.GateWordPrecision

/-!
# Check: a gate word read at a higher precision

The axiom sweep of `GateWordPrecision.lean`, one row of each kind, and one mutant.

* **Agreement.** The empty word raised to any precision is still the empty word's referee, the
  identity, as `runAmp_precWord` says.
* **Discriminating.** Raised to precision two, `Z` still acts as `Z`: at `x = 1` it multiplies
  by `−1`, so the raised word is not the identity.
* **Inhabitation.** `runAmp_precWord` on the one-letter word `Z` at precision one, raised to two.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Hierarchy

-- row: agreement
/-- The empty word, raised, runs as the identity. -/
theorem runAmp_precWord_nil (ψ : (Fin 1 → ZMod 2) → ℂ) :
    runAmp (([] : GateWord 1 1).map (precLetter (M' := 2) (by norm_num))) ψ = ψ :=
  runAmp_precWord _ [] ψ

-- row: discriminating
/-- `Z` at precision one, raised to two, still acts as `Z`, not as the identity: at `x = 1` it
multiplies by `−1`. -/
theorem runAmp_precWord_Z_ne_one :
    runAmp ([GateLetter.diagonal (MvPolynomial.X 0)].map
      (precLetter (N := 1) (M := 1) (M' := 2) (by norm_num))) (fun _ => 1) ![1] ≠ 1 := by
  have hbit : DiagPhase.liftBinary (m := 1) ![(1 : ZMod 2)] 0 = 1 := by decide
  rw [runAmp_precWord, runAmp_cons]
  change charOf 1 (DiagPhase.eval (MvPolynomial.X 0) ![1]) * 1 ≠ 1
  rw [DiagPhase.eval, MvPolynomial.eval_X, hbit, charOf_one_one, mul_one]
  norm_num

-- row: inhabitation
/-- `runAmp_precWord` on the word `Z` at precision one, raised to two. -/
theorem runAmp_precWord_Z (ψ : (Fin 1 → ZMod 2) → ℂ) :
    runAmp ([GateLetter.diagonal (MvPolynomial.X 0)].map
      (precLetter (N := 1) (M := 1) (M' := 2) (by norm_num))) ψ
      = runAmp ([GateLetter.diagonal (MvPolynomial.X 0)] : GateWord 1 1) ψ :=
  runAmp_precWord _ _ ψ

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-! ## The axiom sweep -/

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_precWord' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_precWord

/-! ## Declared mutants -/

-- mutant: prec_drops_diagonal | FTQCLib/Carrier/GateWordPrecision.lean | .diagonal (FTQCLib.Hilbert.liftTo M' hM D) | .diagonal 0

end FTQCLib.Frame.Walkthrough

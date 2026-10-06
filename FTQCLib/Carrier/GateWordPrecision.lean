/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.GateWord
import FTQCLib.Carrier.PrecisionGauge

/-!
# A gate word read at a higher precision

A word at precision `M` is a word at every precision `M' ≥ M`: its diagonal exponents lifted by
R7 (`liftTo`), its H and CNOT letters unchanged, its referee the same (`runAmp_precWord`). This is
the lowest module that imports both the word type (`GateWord.lean`) and the lift's character
identity (`charOf_eval_liftTo`, `PrecisionGauge.lean`), so the fact lives here, once (docs/STEPS.md,
entry 2026-10-01n); before, it was private to `UnreadBits.lean`.

## Main definitions

* `precLetter` — a letter at precision `M`, read at precision `M' ≥ M`.

## Main results

* `runAmp_precWord` — raising a word's precision leaves its referee unchanged.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Hierarchy

/-- A letter at precision `M`, read at precision `M' ≥ M`: the diagonal exponent lifted (R7). -/
noncomputable def precLetter {N M M' : ℕ} (hM : M ≤ M') :
    GateLetter N M → GateLetter N M'
  | .hadamard i => .hadamard i
  | .diagonal D => .diagonal (FTQCLib.Hilbert.liftTo M' hM D)
  | .cnot i j hij => .cnot i j hij

/-- Raising a word's precision leaves its referee unchanged. -/
theorem runAmp_precWord {N M M' : ℕ} (hM : M ≤ M') (W : GateWord N M)
    (ψ : (Fin N → ZMod 2) → ℂ) : runAmp (W.map (precLetter hM)) ψ = runAmp W ψ := by
  induction W generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runAmp (gs.map (precLetter hM)) (letterAmp (precLetter hM g) ψ) = _
    rw [ih, runAmp_cons]
    congr 1
    cases g with
    | hadamard i => rfl
    | diagonal D =>
      funext w
      change charOf M' (DiagPhase.eval (FTQCLib.Hilbert.liftTo M' hM D) w) * ψ w
        = charOf M (DiagPhase.eval D w) * ψ w
      rw [charOf_eval_liftTo]
    | cnot i j hij => rfl

end FTQCLib.Frame.Walkthrough

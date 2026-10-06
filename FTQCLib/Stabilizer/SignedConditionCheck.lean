/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.SignedCondition

/-!
# Check: the measurement update on a frame signed Lagrangian

Rows on `measChi` (`FTQCLib/Stabilizer/SignedCondition.lean`), on one qubit, with the frame
`trivialFrame` (`L = ⊥`, `χ = 0`), conditioned on `X` with witness `Z` (`ω(Z, X) = 1`).

* **Agreement.** The measured `X` gets the outcome label: `2` at label `2`.
* **Discriminating.** The update moves the sign: at label `2` the sign of `X` is `2`, where the
  unconditioned `χ` gives `0`.
* **Discriminating.** The two outcome labels give different signs on `X`.
* **Inhabitation.** `measChi_self`'s hypothesis `ω(M, Q) = 1` holds for `M = Z`, `Q = X`.

What no row tests: the character law of the result, which `measChi` does not claim (the module's
implementation note); anything at `n ≥ 2`. `condition_eq_pauliCondition`
(`FTQCLib/Carrier/ConditionFloor.lean`) reads `measChi` off a floor.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer

/-- The one-qubit frame with no stabilizer: `L = ⊥` and `χ = 0`. -/
noncomputable def trivialFrame : FrameSignedStab 1 where
  L := ⊥
  chi := 0
  chi_zero := rfl
  valid := by
    intro p hp q hq
    rw [Submodule.mem_bot] at hp hq
    subst hp hq
    rw [betaFrame_self, Pi.zero_apply, Pi.zero_apply, add_zero, add_zero]

-- row: inhabitation
/-- `Z` anticommutes with `X`: the witness hypothesis of `measChi_self`. -/
theorem omega_pauliz_paulix_zero : omega (pauliz (0 : Fin 1)) (paulix 0) = 1 := by
  decide

-- row: agreement
/-- The measured `X` gets the outcome label `2`. -/
theorem measChi_trivialFrame_x : measChi trivialFrame (paulix 0) (pauliz 0) 2 (paulix 0) = 2 :=
  measChi_self trivialFrame 2 omega_pauliz_paulix_zero

-- row: discriminating
/-- The update moves the sign: the unconditioned `χ` gives `X` the sign `0`. -/
theorem measChi_trivialFrame_x_ne_chi :
    measChi trivialFrame (paulix 0) (pauliz 0) 2 (paulix 0) ≠ trivialFrame.chi (paulix 0) := by
  rw [measChi_trivialFrame_x]
  decide

-- row: discriminating
/-- The two outcome labels give `X` different signs. -/
theorem measChi_trivialFrame_x_labels :
    measChi trivialFrame (paulix 0) (pauliz 0) 0 (paulix 0)
      ≠ measChi trivialFrame (paulix 0) (pauliz 0) 2 (paulix 0) := by
  rw [measChi_self trivialFrame 0 omega_pauliz_paulix_zero, measChi_trivialFrame_x]
  decide

/-! ## Axiom sweep -/

/-- info: 'FTQCLib.Frame.measChi_of_not_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.measChi_of_not_mem

/-- info: 'FTQCLib.Frame.measChi_of_omega_eq_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.measChi_of_omega_eq_zero

/-- info: 'FTQCLib.Frame.measChi_of_omega_eq_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.measChi_of_omega_eq_one

/-- info: 'FTQCLib.Frame.measChi_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.measChi_self

/-- info: 'FTQCLib.Stabilizer.mem_K_of_omega_M_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Stabilizer.mem_K_of_omega_M_one

/-- info: 'FTQCLib.Stabilizer.mem_K_of_omega_M_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Stabilizer.mem_K_of_omega_M_zero

/-! ## Declared mutants -/

-- mutant: measChi_label | FTQCLib/Stabilizer/SignedCondition.lean | e + S.chi (g + Q) + betaFrame Q (g + Q)) else 0 | S.chi (g + Q) + betaFrame Q (g + Q)) else 0

end FTQCLib.Frame

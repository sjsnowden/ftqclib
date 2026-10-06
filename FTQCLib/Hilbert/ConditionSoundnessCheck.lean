/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ConditionSoundness
import FTQCLib.Carrier.HadamardTotality
import FTQCLib.Carrier.ConditioningCheck

/-!
# Check: the frame's projection against the Born projector on one bit

T19's witness (`docs/STEPS.md`, T19.2): rows on the frozen statement of `ConditionSoundness.lean`,
computed from the definitions of the frame's projection `pauliProjection` (through
`SignedPauli.act` and `pauliAct`) and of the Born projector `bornProjector` (through
`pauliHermitian`), never through `pauliProjection_eq_bornProjector`, `toQState_amp_condition` or
`pauliProjection_eq_bornProjection`. Each side of a row is computed separately, from its own
definition, to an explicit function on one bit, and the row joins the two computations.
T19.3 then proved every headline of `ConditionSoundness.lean`, including
`pauliProjection_eq_bornProjector` and `frameToHilbert_measChi`: none is `sorry`'d or left
unproved, and the witness rows below use only `pauliProjection`'s, `bornProjector`'s and
`frameToHilbert`'s own definitions, never these headlines.

**Conventions.** A word on one bit is a function `Fin 1 → ZMod 2`, read at bit `0`. The plus state
`|+⟩` is `plusState`, `1/√2` at both words; the basis state `|0⟩` is `ketZero`. `Z` is
`⟨0, 1⟩` and `Y` is `⟨1, 1⟩` as a `Pauli 1`: the frame acts by `Y = i X Z`, so
`Y|0⟩ = i|1⟩`. The values below were also computed numerically at T19.0
(`docs/fidelity/T19.md`, the last item of "Computed in this step").

* **Z-conditioning of `|+⟩` at outcome `0` (agreement).** `pauliProjection` of `+Z` at `b = 0` on
  `|+⟩`, read through `toQState`, is the basis state `0` over `√2` (`zOutput`), and so is
  `bornProjector Z 1` on the image of `|+⟩`.
* **Y-conditioning of `|0⟩` at outcome `0` (agreement, the factor `i`).** The frame's projection of
  `+Y` at `b = 0` on `|0⟩` and `bornProjector Y 1` on its image are both `½(|0⟩ + i|1⟩)`
  (`yOutput`). The factor `i` is the one an odd number of Y brings, which is why conditioning on
  `Y` works at precision `m = 2` (`conditionPrecision_yPlus`).
* **The sign flipped (agreement).** The frame's projection of `−Y` at `b = 0` on `|0⟩` is
  `½(|0⟩ − i|1⟩)` (`yOutputFlipped`), the other projector `bornProjector Y (−1)` on its image.
* **The sign flipped (discriminating).** The frame's projection of `−Y` at `b = 0` on `|0⟩` is not
  `bornProjector Y 1` on its image, the projector with the sign dropped: at the word `1` the first
  is `−½ i` and the second `½ i`. A convention that lost `P.sign` in `SignedPauli.act`, or in the
  label `(−1)^{sign + b}`, would make the two equal.

Every agreement and discriminating row is about `pauliProjection P b f` read through `toQState`,
the object `pauliProjection_eq_bornProjector` names, on a concrete Pauli, outcome and state,
compared with `bornProjector` there.

* **`toQState_amp_condition`'s hypotheses hold together (inhabitation).** A carrier state with a
  co-isotropic Lagrangian, a Pauli with its sign, and an outcome, hold together on `bellState`
  (co-isotropic by `bellL_coisotropic`, `FTQCLib/Carrier/HadamardTotality.lean`), `z0Bell`
  (`FTQCLib/Carrier/ConditioningCheck.lean`), and outcome `0`: exhibiting the instance exhibits
  all three at once (`toQState_amp_condition_instance`).
-/

namespace FTQCLib.Hilbert.ConditionSoundnessCheck

open FTQCLib FTQCLib.Pauli FTQCLib.Hilbert FTQCLib.Stabilizer FTQCLib.Frame.Walkthrough

/-! ## The instance -/

/-- `Z` on one bit. -/
def zPauliOne : Pauli 1 := ⟨0, fun _ => 1⟩

/-- `Y` on one bit: both an X- and a Z-support bit. -/
def yPauliOne : Pauli 1 := ⟨fun _ => 1, fun _ => 1⟩

/-- `+Z` on one bit. -/
def zPlus : SignedPauli 1 := ⟨0, zPauliOne⟩

/-- `+Y` on one bit. -/
def yPlus : SignedPauli 1 := ⟨0, yPauliOne⟩

/-- `−Y` on one bit: `yPlus` with its sign flipped. -/
def yMinus : SignedPauli 1 := ⟨1, yPauliOne⟩

/-- The plus state `|+⟩`: `1/√2` at both words. -/
noncomputable def plusState : QubitSpace 1 := fun _ => invSqrt2

/-- The basis state `|0⟩`: `1` at the word `0`, `0` at the word `1`. -/
noncomputable def ketZero : QubitSpace 1 := fun w => if w 0 = 0 then 1 else 0

/-- The basis state `0` over `√2`. -/
noncomputable def zOutput : QubitSpace 1 := fun w => if w 0 = 0 then invSqrt2 else 0

/-- `½(|0⟩ + i|1⟩)`. -/
noncomputable def yOutput : QubitSpace 1 :=
  fun w => if w 0 = 0 then 2⁻¹ else 2⁻¹ * Complex.I

/-- `½(|0⟩ − i|1⟩)`. -/
noncomputable def yOutputFlipped : QubitSpace 1 :=
  fun w => if w 0 = 0 then 2⁻¹ else -(2⁻¹ * Complex.I)

/-! ## Private computations -/

private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

/-- The Born projector, pointwise: `½(ψ w + ε · H(Q) ψ w)`. -/
private theorem bornProjector_apply_fun (Q : Pauli 1) (ε : ℂ) (ψ : QState 1)
    (w : Fin 1 → ZMod 2) :
    bornProjector Q ε ψ w
      = 2⁻¹ * (ψ w + ε * (Complex.I ^ xzWeight Q *
          ((-1 : ℂ) ^ zDotVal Q (w - Q.X) * ψ (w - Q.X)))) := by
  simp only [bornProjector, LinearMap.smul_apply, PiLp.smul_apply, LinearMap.add_apply,
    PiLp.add_apply, LinearMap.id_apply, pauliHermitian_apply_fun, smul_eq_mul]

/-- A word on one bit is the constant word `0` or the constant word `1`. -/
private theorem word_one_cases (w : Fin 1 → ZMod 2) : w = (fun _ => 0) ∨ w = (fun _ => 1) := by
  rcases zmod2_cases (w 0) with h | h
  · left
    funext i
    rw [Subsingleton.elim i 0, h]
  · right
    funext i
    rw [Subsingleton.elim i 0, h]

/-- The frame's projection of `+Z` at `b = 0` on `|+⟩`, from `SignedPauli.act` and `pauliAct`. -/
private theorem pauliProjection_zPlus :
    pauliProjection zPlus 0 plusState = zOutput := by
  funext w
  rcases word_one_cases w with rfl | rfl <;>
    simp [pauliProjection, SignedPauli.act, pauliAct, zPlus, zPauliOne, plusState, zOutput,
      yWeight, zDot]
  ring

/-- The Born projector of `Z` at `ε = 1` on `|+⟩`, from `pauliHermitian`. -/
private theorem bornProjector_zPlus :
    toQState.symm (bornProjector zPauliOne ((-1 : ℂ) ^ (zPlus.sign.val + (0 : ZMod 2).val))
      (toQState plusState)) = zOutput := by
  funext w
  rw [toQState_symm_apply, bornProjector_apply_fun]
  rcases word_one_cases w with rfl | rfl <;>
    simp [zPlus, zPauliOne, plusState, zOutput, xzWeight, zDotVal]
  ring

/-- The frame's projection of `Y` with sign `s` at `b = 0` on `|0⟩`, from `SignedPauli.act`. -/
private theorem pauliProjection_y (s : ZMod 2) (w : Fin 1 → ZMod 2) :
    pauliProjection ⟨s, yPauliOne⟩ 0 ketZero w
      = if w 0 = 0 then 2⁻¹ else 2⁻¹ * ((-1 : ℂ) ^ s.val * Complex.I) := by
  rcases word_one_cases w with rfl | rfl <;>
    simp [pauliProjection, SignedPauli.act, pauliAct, yPauliOne, ketZero, yWeight, zDot,
      zmod2_one_add_one]

/-- The Born projector of `Y` at `ε` on `|0⟩`, from `pauliHermitian`. -/
private theorem bornProjector_y (ε : ℂ) (w : Fin 1 → ZMod 2) :
    toQState.symm (bornProjector yPauliOne ε (toQState ketZero)) w
      = if w 0 = 0 then 2⁻¹ else 2⁻¹ * (ε * Complex.I) := by
  rw [toQState_symm_apply, bornProjector_apply_fun]
  rcases word_one_cases w with rfl | rfl <;>
    simp [yPauliOne, ketZero, xzWeight, zDotVal]

/-! ## Rows -/

/-- **Z-conditioning of `|+⟩` at outcome `0`.** The frame's projection and the Born projector
both give the basis state `0` over `√2`, each computed from its own definition. -/
-- row: agreement
theorem zPlus_plus_agreement :
    toQState (pauliProjection zPlus 0 plusState)
      = bornProjector zPlus.pauli ((-1 : ℂ) ^ (zPlus.sign.val + (0 : ZMod 2).val))
          (toQState plusState) := by
  apply toQState.symm.injective
  rw [LinearEquiv.symm_apply_apply, pauliProjection_zPlus]
  exact bornProjector_zPlus.symm

/-- **Y-conditioning of `|0⟩` at outcome `0`, the factor `i`.** The frame's projection of `+Y` and
`bornProjector Y 1` both give `½(|0⟩ + i|1⟩)`. -/
-- row: agreement
theorem yPlus_ketZero_agreement :
    toQState (pauliProjection yPlus 0 ketZero)
      = bornProjector yPlus.pauli ((-1 : ℂ) ^ (yPlus.sign.val + (0 : ZMod 2).val))
          (toQState ketZero) := by
  apply toQState.symm.injective
  funext w
  rw [LinearEquiv.symm_apply_apply, yPlus, pauliProjection_y, bornProjector_y]
  simp [ZMod.val_zero]

/-- Both sides of the `+Y` row are `½(|0⟩ + i|1⟩)`, the factor `i` at the word `1`. -/
theorem pauliProjection_yPlus_eq_yOutput : pauliProjection yPlus 0 ketZero = yOutput := by
  funext w
  rw [yPlus, pauliProjection_y, yOutput]
  simp [ZMod.val_zero]

/-- Conditioning on `+Y` lifts precision `1` to `2`, for the factor `i`. -/
theorem conditionPrecision_yPlus : conditionPrecision 1 yPlus = 2 := by
  simp [conditionPrecision, yPlus, yPauliOne, yWeight, zDot]

/-- **The sign flipped gives the other projector.** The frame's projection of `−Y` at `b = 0` is
`bornProjector Y (−1)`: `½(|0⟩ − i|1⟩)`. -/
-- row: agreement
theorem yMinus_ketZero_agreement :
    toQState (pauliProjection yMinus 0 ketZero)
      = bornProjector yMinus.pauli ((-1 : ℂ) ^ (yMinus.sign.val + (0 : ZMod 2).val))
          (toQState ketZero) := by
  apply toQState.symm.injective
  funext w
  rw [LinearEquiv.symm_apply_apply, yMinus, pauliProjection_y, bornProjector_y]
  simp [ZMod.val_zero]

/-- Both sides of the `−Y` row are `½(|0⟩ − i|1⟩)`. -/
theorem pauliProjection_yMinus_eq_yOutputFlipped :
    pauliProjection yMinus 0 ketZero = yOutputFlipped := by
  funext w
  rw [yMinus, pauliProjection_y, yOutputFlipped]
  simp

/-- **The sign is not dropped.** The frame's projection of `−Y` at `b = 0` on `|0⟩` is not the Born
projector with the sign dropped, `bornProjector Y 1`: at the word `1` the first is `−½ i`, the
second `½ i`. -/
-- row: discriminating
theorem yMinus_ne_signDropped :
    toQState (pauliProjection yMinus 0 ketZero) ≠ bornProjector yPauliOne 1 (toQState ketZero) := by
  intro h
  have hw := congrArg (fun ψ : QState 1 => toQState.symm ψ (fun _ => 1)) h
  simp only [LinearEquiv.symm_apply_apply] at hw
  rw [yMinus, pauliProjection_y, bornProjector_y] at hw
  simp only [one_ne_zero, if_false, ZMod.val_one, pow_one, one_mul] at hw
  have hI : Complex.I = 0 := by linear_combination (-1 : ℂ) * hw
  exact Complex.I_ne_zero hI

/-! ## Inhabitation: `toQState_amp_condition`'s hypotheses, together on the Bell state -/

-- row: inhabitation
/-- **Inhabitation.** `toQState_amp_condition`'s hypotheses — a carrier state with a co-isotropic
Lagrangian, a Pauli with its sign, and an outcome — hold together on `bellState` (co-isotropic by
`bellL_coisotropic`), `z0Bell`, and outcome `0`: exhibiting the instance exhibits all three at
once. -/
example := toQState_amp_condition bellState bellL_coisotropic z0Bell (0 : ZMod 2)

/-! ## The aimed mutants -/

-- mutant: iZ4_outcomeChi_scale | FTQCLib/Hilbert/ConditionSoundness.lean
--   | iZ4 (outcomeChi P b) = (-1 : ℂ) ^ (P.sign.val + b.val)
--   | iZ4 (outcomeChi P b) = (2 : ℂ) * (-1 : ℂ) ^ (P.sign.val + b.val)

-- mutant: pauliProjection_eq_bornProjector_sign | FTQCLib/Hilbert/ConditionSoundness.lean
--   | bornProjector P.pauli ((-1 : ℂ) ^ (P.sign.val + b.val)) (toQState f)
--   | bornProjector P.pauli ((-1 : ℂ) ^ b.val) (toQState f)

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Hilbert.toQState_pauliAct' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.toQState_pauliAct

/-- info: 'FTQCLib.Hilbert.toQState_signedPauliAct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.toQState_signedPauliAct

/-- info: 'FTQCLib.Hilbert.iZ4_outcomeChi' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.iZ4_outcomeChi

/-- info: 'FTQCLib.Hilbert.iZ4_outcomeChi_mul_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.iZ4_outcomeChi_mul_self

/-- info: 'FTQCLib.Hilbert.pauliProjection_eq_bornProjector' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.pauliProjection_eq_bornProjector

/-- info: 'FTQCLib.Hilbert.toQState_amp_condition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.toQState_amp_condition

/-- info: 'FTQCLib.Hilbert.pauliProjection_eq_bornProjection' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.pauliProjection_eq_bornProjection

/-- info: 'FTQCLib.Hilbert.frameToHilbert_measChi' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.frameToHilbert_measChi

/-- info: 'FTQCLib.Hilbert.frameToHilbert_chartOf_condition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Hilbert.frameToHilbert_chartOf_condition

end FTQCLib.Hilbert.ConditionSoundnessCheck

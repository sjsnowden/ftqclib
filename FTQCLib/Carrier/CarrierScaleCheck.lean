/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierScale

/-!
# Check: the scale along a protocol

The axiom sweep of `CarrierScale.lean`, one row of each kind, and one mutant.

* **Agreement.** Halving twice by `√2` is halving by `2`: the scale `ScaledBy.div_sqrt_two` reaches
  in two steps is the one `ScaledBy.div_two` reaches in one, and the two nonzero scales `1/√2` and
  `1/2`, tracked from `1`, have a dyadic ratio (`isDyadicRatio_of_scaledBy`).
* **Discriminating.** A zero scale stays zero: `1` is not scaled from `0`. A definition of
  `ScaledBy` that dropped the factor `c` would admit it.
* **Inhabitation.** Every scale is scaled to zero, the scale off a `restrictZ` slice.
-/

namespace FTQCLib.Frame.Walkthrough

-- row: agreement
/-- Two divisions by `√2` and one by `2` reach the same scale, and the scales `1/√2` and `1/2`,
each tracked from `1`, have a dyadic ratio. -/
theorem scaledBy_sqrt_two_twice :
    (1 : ℂ) / (Real.sqrt 2 : ℂ) / (Real.sqrt 2 : ℂ) = 1 / 2 ∧
      IsDyadicRatio ((1 / 2 : ℂ) / (1 / (Real.sqrt 2 : ℂ))) := by
  refine ⟨by rw [div_div, sqrt_two_mul_self], ?_⟩
  exact isDyadicRatio_of_scaledBy (ScaledBy.div_sqrt_two 1) (ScaledBy.div_two 1)
    (one_div_ne_zero ofReal_sqrt_two_ne_zero) (by norm_num)

-- row: discriminating
/-- A zero scale stays zero: `1` is not `0` times a power of `√2`. -/
theorem not_scaledBy_zero_one : ¬ ScaledBy 0 1 := by
  rintro (h | ⟨e, h⟩)
  · exact one_ne_zero h
  · rw [mul_zero] at h
    exact one_ne_zero h

-- row: inhabitation
/-- Every scale is scaled to zero. -/
theorem scaledBy_zero (c : ℂ) : ScaledBy c 0 :=
  Or.inl rfl

/-! ## Axiom sweep -/

/-- info: 'FTQCLib.Frame.Walkthrough.ScaledBy.refl' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ScaledBy.refl

/-- info: 'FTQCLib.Frame.Walkthrough.ScaledBy.trans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ScaledBy.trans

/-- info: 'FTQCLib.Frame.Walkthrough.ScaledBy.div_sqrt_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ScaledBy.div_sqrt_two

/-- info: 'FTQCLib.Frame.Walkthrough.ScaledBy.div_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ScaledBy.div_two

/-- info: 'FTQCLib.Frame.Walkthrough.scaledBy_applyLetter' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.scaledBy_applyLetter

/-- info: 'FTQCLib.Frame.Walkthrough.scaledBy_run' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.scaledBy_run

/-- info: 'FTQCLib.Frame.Walkthrough.scaledBy_condition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.scaledBy_condition

/-- info: 'FTQCLib.Frame.Walkthrough.scaledBy_interpret' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.scaledBy_interpret

/-- info: 'FTQCLib.Frame.Walkthrough.scaledBy_restrictZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.scaledBy_restrictZ

/-- info: 'FTQCLib.Frame.Walkthrough.scaledBy_restrictLast' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.scaledBy_restrictLast

/-- info: 'FTQCLib.Frame.Walkthrough.isDyadicRatio_of_scaledBy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isDyadicRatio_of_scaledBy

/-- info: 'FTQCLib.Frame.Walkthrough.eqvGen_carrierRule_of_scaledBy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.eqvGen_carrierRule_of_scaledBy

/-! ## Declared mutants, aimed at the definition the proofs use -/

-- mutant: scaledBy_base | FTQCLib/Carrier/CarrierScale.lean | (Real.sqrt 2 : ℂ) ^ e * c | 2 ^ e * c

end FTQCLib.Frame.Walkthrough

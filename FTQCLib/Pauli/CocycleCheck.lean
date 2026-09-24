/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle

/-!
# Check: the Pauli cocycle data

Axiom rows for every declaration of `FTQCLib.Pauli.Cocycle`, each under a build-failing `#guard_msgs`.
`zDot`, `yWeight`, `betaFrame` and the `ZMod 4` arithmetic the sign bookkeeping runs on, plus
`qForm`, the quadratic refinement of `ω`.

The witness rows for these objects live beside their consumers; this module is the sweep.
-/

namespace FTQCLib.Pauli

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Pauli.zDot' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot

/-- info: 'FTQCLib.Pauli.yWeight' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight

/-- info: 'FTQCLib.Pauli.zDot_zero_left' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot_zero_left

/-- info: 'FTQCLib.Pauli.yWeight_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight_zero

/-- info: 'FTQCLib.Pauli.pauli_add_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauli_add_self

/-- info: 'FTQCLib.Pauli.betaFrame' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms betaFrame

/-- info: 'FTQCLib.Pauli.betaFrame_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms betaFrame_self

/-- info: 'FTQCLib.Pauli.zDot_cast_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot_cast_two

/-- info: 'FTQCLib.Pauli.two_mul_natCast_four' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_mul_natCast_four

/-- info: 'FTQCLib.Pauli.two_val_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_val_add

/-- info: 'FTQCLib.Pauli.val_add_cast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_add_cast

/-- info: 'FTQCLib.Pauli.val_add_two_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_add_two_mul

/-- info: 'FTQCLib.Pauli.two_zDot_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_add

/-- info: 'FTQCLib.Pauli.val_add_mul_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms val_add_mul_two

/-- info: 'FTQCLib.Pauli.two_zDot_add_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_add_right

/-- info: 'FTQCLib.Pauli.two_zDot_swap_of_omega' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_swap_of_omega

/-- info: 'FTQCLib.Pauli.zDot_zero_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot_zero_right

/-- info: 'FTQCLib.Pauli.zmod_two_eq_zero_or_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zmod_two_eq_zero_or_one

/-- info: 'FTQCLib.Pauli.two_zDot_smul_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_smul_right

/-- info: 'FTQCLib.Pauli.two_zDot_smul_left' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_smul_left

/-- info: 'FTQCLib.Pauli.two_zDot_sum_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_sum_right

/-- info: 'FTQCLib.Pauli.two_zDot_sum_left' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_zDot_sum_left

/-- info: 'FTQCLib.Pauli.betaFrame_swap' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms betaFrame_swap

/-- info: 'FTQCLib.Pauli.betaFrame_cocycle' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms betaFrame_cocycle

/-- info: 'FTQCLib.Pauli.qForm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm

/-- info: 'FTQCLib.Pauli.qForm_eq_yWeight_cast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_eq_yWeight_cast

end FTQCLib.Pauli

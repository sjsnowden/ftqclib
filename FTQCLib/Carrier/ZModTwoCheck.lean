/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ZModTwo

/-!
# Check: two facts about `ZMod 2`

The axiom sweep of `ZModTwo.lean`, one row of each kind, and one mutant.

* **Agreement.** `sum_zmod_two` on the identity: `0 + 1 = 1`, computed directly.
* **Discriminating.** The two bits differ, so the dichotomy's two cases are not one.
* **Inhabitation.** `zmod_two_dichotomy` at `1`.
-/

namespace FTQCLib.Frame.Walkthrough

-- row: agreement
/-- The sum of the two bits, by `sum_zmod_two`, is `1`, as computed. -/
theorem sum_zmod_two_id : ∑ t : ZMod 2, t = 1 := by
  rw [sum_zmod_two]
  decide

-- row: discriminating
/-- The two bits are different. -/
theorem zmod_two_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

-- row: inhabitation
/-- The dichotomy at `1` takes its second case. -/
theorem zmod_two_dichotomy_one : (1 : ZMod 2) = 0 ∨ (1 : ZMod 2) = 1 := zmod_two_dichotomy 1

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-! ## The axiom sweep -/

/-- info: 'FTQCLib.Frame.Walkthrough.zmod_two_dichotomy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.zmod_two_dichotomy

/-- info: 'FTQCLib.Frame.Walkthrough.sum_zmod_two' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_zmod_two

/-! ## Declared mutants -/

-- mutant: sum_drops_one | FTQCLib/Carrier/ZModTwo.lean | ∑ t, f t = f 0 + f 1 := | ∑ t, f t = f 0 :=

end FTQCLib.Frame.Walkthrough

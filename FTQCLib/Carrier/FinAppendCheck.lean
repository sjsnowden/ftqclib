/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FinAppend
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-!
# Check: tuples on `Fin (n + k)` split by `Fin.append`

The axiom sweep of `FinAppend.lean`, one row of each kind, and one mutant.

* **Agreement.** `update_append_natAdd` on `![false] ++ ![false]`, updated to `true` at the
  last coordinate, agrees with `![false, true]` computed directly.
* **Discriminating.** The update lands in the last coordinate, not the first: the result is not
  `![true, false]`.
* **Inhabitation.** `castAdd_ne_natAdd` at `n = k = 1`: coordinate `0` is not coordinate `1`.
-/

namespace FTQCLib.Frame.Walkthrough

-- row: agreement
/-- Updating the last coordinate of `![false] ++ ![false]` to `true` gives `![false, true]`. -/
theorem update_append_natAdd_example :
    Function.update (Fin.append ![false] ![false]) (Fin.natAdd 1 (0 : Fin 1)) true
      = ![false, true] := by
  rw [update_append_natAdd]
  decide

-- row: discriminating
/-- The update is not at the first coordinate. -/
theorem update_append_natAdd_example_ne :
    Function.update (Fin.append ![false] ![false]) (Fin.natAdd 1 (0 : Fin 1)) true
      ≠ ![true, false] := by
  rw [update_append_natAdd]
  intro h
  exact absurd (congrFun h 0) (by decide)

-- row: inhabitation
/-- At `n = k = 1` the two coordinates differ. -/
theorem castAdd_ne_natAdd_example : Fin.castAdd 1 (0 : Fin 1) ≠ Fin.natAdd 1 (0 : Fin 1) :=
  castAdd_ne_natAdd 0 0

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-! ## The axiom sweep -/

/-- info: 'FTQCLib.Frame.Walkthrough.castAdd_ne_natAdd' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.castAdd_ne_natAdd

/-- info: 'FTQCLib.Frame.Walkthrough.update_append_natAdd' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.update_append_natAdd

/-- info: 'FTQCLib.Frame.Walkthrough.insertNth_natAdd_append' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.insertNth_natAdd_append

/-- info: 'FTQCLib.Frame.Walkthrough.append_comp_castAdd' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.append_comp_castAdd

/-- info: 'FTQCLib.Frame.Walkthrough.append_comp_natAdd' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.append_comp_natAdd

/-- info: 'FTQCLib.Frame.Walkthrough.sum_fin_cons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_fin_cons

/-! ## Declared mutants -/

-- mutant: update_ignored | FTQCLib/Carrier/FinAppend.lean | (Function.update u i b) := by | u := by

end FTQCLib.Frame.Walkthrough

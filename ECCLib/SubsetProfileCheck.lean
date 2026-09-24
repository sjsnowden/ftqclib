/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.SubsetProfile
import Mathlib.Data.Fintype.Card

/-!
# Checks for `ECCLib/SubsetProfile.lean`

Axiom sweeps, and kernel rows evaluating the profile count at a concrete carrier — including
one with the two profile sizes **unequal**, which is the case the old fixed-size form could
not even state.
-/

namespace ECCLib

/-- info: 'ECCLib.card_filter_profile' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_filter_profile

/-- info: 'ECCLib.card_filter_profile_powersetCard' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_filter_profile_powersetCard

/-! ## Kernel rows

`Ω = {0,1,2,3}`, `x = {0,1}` in `Fin 4`: profile `(1, 2)` — one point inside `x`, two outside
— gives `C(2,1)·C(2,2) = 2`, and the kernel confirms the filter agrees. The `(1, 2)` profile
has unequal coordinates, which the fixed-size-only form could not express. -/

example :
    ((Finset.univ : Finset (Fin 4)).powerset.filter
        (fun U => (U ∩ ({0, 1} : Finset (Fin 4))).card = 1
          ∧ (U \ ({0, 1} : Finset (Fin 4))).card = 2)).card = 2 := by decide

example : (2 : ℕ).choose 1 * (2 : ℕ).choose 2 = 2 := by decide

/-- The fixed-size corollary at `J(4,2)`-shaped data: `k = 2`, `t = 1` against `x = {0,1}`
gives `C(2,1)·C(2,1) = 4`. -/
example :
    (((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
        (fun U => (U ∩ ({0, 1} : Finset (Fin 4))).card = 1)).card = 4 := by decide

end ECCLib

/-- info: 'ECCLib.card_powersetCard_filter_superset' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_powersetCard_filter_superset

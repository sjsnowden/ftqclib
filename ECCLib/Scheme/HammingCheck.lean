/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Hamming

/-!
# Checks for the Hamming orbit classification and its boundaries

Kernel rows on the primal side only (character-indexed statements are not decidable):

* **Transitivity decided at the toys**: `(ZMod 3)ˣ` IS transitive on the nonzero alphabet
  (the field case), `(ZMod 4)ˣ` is NOT (the `n = 1` face of the `ZMod 4` obstruction), and
  under the units the weight-1 shell `{1,2,3}` of `ZMod 4` splits into THREE orbits
  (`{0}`, `{1,3}`, `{2}`).
* **The Klein row**: four explicit automorphisms of the Pauli alphabet move any nonzero element
  to any other (`klein_list_trans`, decided in `Hamming.lean`); without its shears the list
  does not suffice.
* **The axiom sweep** on the orbit classification and both boundary theorems, build-failing —
  note `weight_one_shell_not_an_orbit` needs no `Classical.choice` at all.
-/

namespace ECCLib.Scheme

/-- The field case is transitive on the nonzero alphabet. -/
example : TransOnNonzero (ZMod 3)ˣ (ZMod 3) := by
  unfold TransOnNonzero
  decide
/-- The `n = 1` face of the `ZMod 4` obstruction: the units are NOT transitive on `{1,2,3}`. -/
example : ¬ TransOnNonzero (ZMod 4)ˣ (ZMod 4) := by
  unfold TransOnNonzero
  decide
/-- Concretely, the weight-1 shell of `ZMod 4` is a union of two unit-orbits, `{1,3}` and `{2}`:
three orbits in all. -/
example : (orbits (ZMod 4)ˣ (ZMod 4)).card = 3 := by decide
/-- `2` is not in the orbit of `1`. -/
example : (2 : ZMod 4) ∉ orb (ZMod 4)ˣ (1 : ZMod 4) := by decide
/-- The Klein alphabet: the identity and the three transpositions suffice (re-decided here). -/
example : ∀ a b : ZMod 2 × ZMod 2, a ≠ 0 → b ≠ 0 →
    ∃ g ∈ [(1 : AddAut (ZMod 2 × ZMod 2)), kleinSwap, kleinShearL, kleinShearR], g a = b := by
  decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.exists_monomial_of_hammingNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.exists_monomial_of_hammingNorm_eq

/-- info: 'ECCLib.Scheme.hammingNorm_eq_iff_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.hammingNorm_eq_iff_monomial

/-- info: 'ECCLib.Scheme.hammingNorm_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.hammingNorm_monomial

/-- info: 'ECCLib.Scheme.orbit_eq_shell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbit_eq_shell

/-- info: 'ECCLib.Scheme.weight_one_shell_not_an_orbit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.weight_one_shell_not_an_orbit

/-- info: 'ECCLib.Scheme.no_transitive_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.no_transitive_group

/-- info: 'ECCLib.Scheme.klein_transOnNonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.klein_transOnNonzero

/-- info: 'ECCLib.Scheme.klein_orbit_eq_shell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.klein_orbit_eq_shell

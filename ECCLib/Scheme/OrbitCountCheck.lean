/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitCount
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance checks for the orbit-count layer

This layer is about vectors, not characters, so unlike the dual-side modules it admits kernel
rows — and the bridge `card_orbitRel_quotient` is what lets an abstract orbit count be
computed rather than argued.

**The agreement row.** That the units of `ZMod 4` are not transitive on `{1,2,3}` is decided
directly in `HammingCheck.lean`, by evaluating the predicate. Here the same fact is obtained
by a completely different route: the kernel computes three orbits, three is not two, and the
orbit-count equivalence does the rest. Two independent derivations of one fact.
-/

namespace ECCLib.Scheme

open MulAction

/-- **The kernel row.** `ZMod 4` under its units has three orbits — `{0}`, `{1,3}` and `{2}` —
computed by the kernel and transported to the quotient Burnside is stated over. -/
example : Nat.card (orbitRel.Quotient (ZMod 4)ˣ (ZMod 4)) = 3 := by
  rw [card_orbitRel_quotient]
  decide

/-- **The agreement row.** Non-transitivity at `ZMod 4`, derived from the kernel-computed
orbit count instead of from the predicate. -/
example : ¬ TransOnNonzero (ZMod 4)ˣ (ZMod 4) := by
  have hcard : 2 ≤ Nat.card (ZMod 4) := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hthree : Nat.card (orbitRel.Quotient (ZMod 4)ˣ (ZMod 4)) = 3 := by
    rw [card_orbitRel_quotient]
    decide
  rw [transOnNonzero_iff_card_orbits_eq_two hcard, hthree]
  decide

/-- The same fact as `HammingCheck.lean` decides it, for comparison. -/
example : ¬ TransOnNonzero (ZMod 4)ˣ (ZMod 4) := by
  unfold TransOnNonzero
  decide

/-- **The positive side**, at a prime field: two orbits, `{0}` and the units. -/
example : Nat.card (orbitRel.Quotient (ZMod 3)ˣ (ZMod 3)) = 2 := by
  rw [card_orbitRel_quotient]
  decide

/-- **The Mathlib-native reading**, instantiated against MATHLIB's own restricted action on
the nonzero elements of a ring (`Units.instMulActionSubtypeNeOfNat`), for which the
compatibility hypothesis is `rfl`. Declaring a bespoke instance here instead was tried and
collided with this one — the A5 diamond, measured. -/
example : IsPretransitive (ZMod 3)ˣ {w : ZMod 3 // w ≠ 0} := by
  rw [← transOnNonzero_iff_isPretransitive (fun _ _ => rfl)]
  unfold TransOnNonzero
  decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.quotient_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.quotient_eq_zero_iff

/-- info: 'ECCLib.Scheme.transOnNonzero_iff_isPretransitive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transOnNonzero_iff_isPretransitive

/-- info: 'ECCLib.Scheme.transOnNonzero_iff_card_orbits_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transOnNonzero_iff_card_orbits_eq_two

/-- info: 'ECCLib.Scheme.card_orbitRel_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_orbitRel_quotient

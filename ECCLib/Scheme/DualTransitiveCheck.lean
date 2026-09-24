/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.DualTransitive
import ECCLib.Scheme.Hamming

/-!
# Checks for dual transitivity

**The discriminating row.** `transOnNonzero_dual_iff` is an equivalence, and the row that
shows it is instantiates the FAILING direction: the units of `ZMod 4` are not transitive on
`{1,2,3}`, and therefore not transitive on the nontrivial characters either. A one-directional
transfer theorem could not prove that.

**The payoff row.** At the Klein alphabet the hypothesis does hold, so the nontrivial
characters of `ZMod 2 × ZMod 2` form a single orbit under its full automorphism group — the
dual-side statement the Hamming instance needs, and the dual counterpart of
`klein_transOnNonzero`.
-/

namespace ECCLib.Scheme

/-- **The discriminating row**, using the equivalence in the direction a one-way transfer does
not provide. -/
example : ¬ TransOnNonzero (ZMod 4)ˣ (AddChar (ZMod 4) ℂ) := by
  intro h
  have hprimal : TransOnNonzero (ZMod 4)ˣ (ZMod 4) := transOnNonzero_dual_iff.mp h
  revert hprimal
  unfold TransOnNonzero
  decide

/-- **The payoff row.** At the Klein (Pauli) alphabet the nontrivial characters form a single
orbit under the full automorphism group. -/
example : TransOnNonzero (AddAut (ZMod 2 × ZMod 2)) (AddChar (ZMod 2 × ZMod 2) ℂ) :=
  transOnNonzero_dual klein_transOnNonzero

/-- The prime-field row, from a decided primal fact. -/
example : TransOnNonzero (ZMod 3)ˣ (AddChar (ZMod 3) ℂ) := by
  refine transOnNonzero_dual ?_
  unfold TransOnNonzero
  decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.transOnNonzero_dual_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transOnNonzero_dual_iff

/-- info: 'ECCLib.Scheme.transOnNonzero_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transOnNonzero_dual

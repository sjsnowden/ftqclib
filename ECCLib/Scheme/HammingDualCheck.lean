/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingDual

/-!
# Checks for the dual side of the Hamming instance

There are NO `decide` rows here, and that is forced rather than chosen: every statement of
this module is indexed by characters, whose `Fintype`/`DecidableEq` instances are Mathlib's
classical ones. The checks are therefore the axiom sweep plus the discriminating row
below.

**The discriminating row.** `shellSet_stable` carries NO transitivity hypothesis, and the
instantiation that proves the point is `A = ZMod 4`, where transitivity FAILS
(`¬ TransOnNonzero (ZMod 4)ˣ (ZMod 4)`, decided in `HammingCheck.lean`, and
`no_transitive_group` for every automorphism group): the dual shells are stable there even
though the primal shells are not orbits. A version of stability that had leaned on
transitivity could not accept this instantiation.
-/

namespace ECCLib.Scheme

/-- **The discriminating row**: stability of the dual shells at `ZMod 4`, where the alphabet
admits NO transitive automorphism group — so this row could not be proved by any argument
routed through `TransOnNonzero`. -/
example (k : ℕ) {φ : AddAut (Fin 3 → ZMod 4)}
    (hφ : φ ∈ monomialSubgroup (Fin 3) (ZMod 4) (ZMod 4)ˣ)
    {ξ : AddChar (Fin 3 → ZMod 4) ℂ} (hξ : ξ ∈ shellSet (Fin 3) (ZMod 4) k) :
    φ • ξ ∈ shellSet (Fin 3) (ZMod 4) k :=
  shellSet_stable (G := (ZMod 4)ˣ) k hφ hξ

/-- The same at the Klein (Pauli) alphabet, where transitivity DOES hold — the two
instantiations share one proof. -/
example (k : ℕ) {φ : AddAut (Fin 3 → ZMod 2 × ZMod 2)}
    (hφ : φ ∈ monomialSubgroup (Fin 3) (ZMod 2 × ZMod 2) (AddAut (ZMod 2 × ZMod 2)))
    {ξ : AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ}
    (hξ : ξ ∈ shellSet (Fin 3) (ZMod 2 × ZMod 2) k) :
    φ • ξ ∈ shellSet (Fin 3) (ZMod 2 × ZMod 2) k :=
  shellSet_stable (G := AddAut (ZMod 2 × ZMod 2)) k hφ hξ

/-- The consumer form: the dual class sum of a shell is a class function for the monomial
group — what `Spectrum.qEnt_smul` wants at the Hamming instance. -/
example (k : ℕ) {φ : AddAut (Fin 3 → ZMod 4)}
    (hφ : φ ∈ monomialSubgroup (Fin 3) (ZMod 4) (ZMod 4)ˣ) (v : Fin 3 → ZMod 4) :
    qEnt (shellSet (Fin 3) (ZMod 4) k) (φ • v) = qEnt (shellSet (Fin 3) (ZMod 4) k) v :=
  qEnt_shellSet_smul (G := (ZMod 4)ˣ) k hφ v

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.coordChar_scaleAut_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coordChar_scaleAut_smul

/-- info: 'ECCLib.Scheme.coordChar_permAut_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coordChar_permAut_smul

/-- info: 'ECCLib.Scheme.dualWeight_monomial_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.dualWeight_monomial_smul

/-- info: 'ECCLib.Scheme.mem_shellSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_shellSet_iff

/-- info: 'ECCLib.Scheme.shellSet_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.shellSet_stable

/-- info: 'ECCLib.Scheme.qEnt_shellSet_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.qEnt_shellSet_smul

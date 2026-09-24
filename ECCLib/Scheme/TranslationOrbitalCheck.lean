/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.TranslationOrbital
import ECCLib.Scheme.OrbitalSpectrumCheck

/-!
# Checks for the translation bridge

Axiom sweeps, and the row that pins the most important negative result: the translation layer's
commutativity is **not** an instance of the general layer's.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.schemeAlgebra_eq_permCommutant' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.schemeAlgebra_eq_permCommutant

/-- info: 'ECCLib.Scheme.orbital_iff_sub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbital_iff_sub

/-- info: 'ECCLib.Scheme.orbProjBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbProjBasis

/-- info: 'ECCLib.Scheme.linearIndependent_orbProjSub' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.linearIndependent_orbProjSub

/-- info: 'ECCLib.Scheme.card_orbits_dual_eq_card_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_orbits_dual_eq_card_orbits

/-- info: 'ECCLib.Scheme.schemeAlgebra_eq_orbitalAlgebra' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.schemeAlgebra_eq_orbitalAlgebra

/-- info: 'ECCLib.Scheme.finrank_schemeAlgebra_of_orbital' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.finrank_schemeAlgebra_of_orbital

/-- info: 'ECCLib.Scheme.card_orbits_prod_eq_card_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_orbits_prod_eq_card_orbits

/-! ## The negative row, stated as two compiled facts side by side

**Fact one: the translation-scheme algebra is commutative for EVERY `H`,** with no hypothesis on the
action whatsoever. Its proof is `Matrix.circulant_mul_comm` — translation-invariance.

**Fact two: self-pairing can FAIL** at a legitimate action, compiled next door as
`not_isSelfPaired_Cyc3`: the regular action of a group of odd order cannot swap a pair, since
that would need `2g = 0` with `g = y − x`.

Together these say the general layer's route to commutativity is *not* the translation layer's. Two
independent sufficient conditions feed one interface, and neither implies the other — which is
exactly why `Scheme/OrbitalSpectrum.lean` takes commutativity as a hypothesis instead of deriving
it from self-pairing. -/

section Negative

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {H : Type*} [Group H] [Fintype H] [DistribMulAction H V]

/-- Fact one: commutativity of the translation-scheme algebra, for every `H`, with no self-pairing
anywhere in sight. -/
example {M N : Matrix V V ℂ} (hM : M ∈ schemeAlgebra H V) (hN : N ∈ schemeAlgebra H V) :
    M * N = N * M :=
  schemeAlgebra_mul_comm hM hN

omit [Fintype H] in
/-- ...so the translation layer discharges the spectral layer's interface from its own side. -/
theorem isCommutative_schemeAlgebra : Subalgebra.IsCommutative (schemeAlgebra H V) :=
  ⟨fun a b => Subtype.ext (schemeAlgebra_mul_comm a.2 b.2)⟩

end Negative

/-- Fact two, restated here so the pair sits together: self-pairing is not automatic. -/
example : ¬ IsSelfPaired Cyc3 Cyc3 := not_isSelfPaired_Cyc3

/-! ## What is deliberately absent

No row asserts that the general eigenmatrix identity implies `Scheme/Spectrum.lean`'s `PQ_eq`, or
that anything here subsumes `Scheme/LP.lean`. Both claims are false — see the module docstring
of `Scheme/TranslationOrbital.lean` for why. -/

end ECCLib.Scheme

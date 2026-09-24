/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.TranslationSpectrum
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance rows for the canonical translation spectrum

The identification and its consumer are noncomputable (`translationSpectrumEquiv` is a
`choose`), so no kernel row can evaluate them; acceptance is the build-failing axiom sweep
plus a fully **constructed** instantiation of `splitChar_adj_eq_pEnt` at the cyclotomic toy
`(ZMod 3)ˣ` on `ZMod 3` — every hypothesis is discharged by `orb_mem_orbits`/`self_mem_orb`,
so the row cannot be satisfied vacuously.
-/

namespace ECCLib.Scheme

/-- `splitChar_adj_eq_pEnt` instantiates at a live carrier with every hypothesis constructed:
at `(ZMod 3)ˣ` on `ZMod 3`, the split character of an orbit adjacency at the spectral index
of a dual orbit is the classical `P`-entry. -/
example (χ : AddChar (ZMod 3) ℂ) (v : ZMod 3) :
    ECCLib.splitChar ℂ ↥(schemeAlgebra (ZMod 3)ˣ (ZMod 3))
      (translationSpectrumEquiv ⟨orb (ZMod 3)ˣ χ, orb_mem_orbits χ⟩)
      ⟨adj (orb (ZMod 3)ˣ v), adj_mem_schemeAlgebra (orb_mem_orbits v)⟩
      = pEnt (orb (ZMod 3)ˣ v) χ :=
  splitChar_adj_eq_pEnt (orb_mem_orbits v) _ (self_mem_orb χ)

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.translationCommutative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.translationCommutative

/-- info: 'ECCLib.Scheme.translationReduced' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.translationReduced

/-- info: 'ECCLib.Scheme.translationSpecFintype' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.translationSpecFintype

/-- info: 'ECCLib.Scheme.translationSpecDecEq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.translationSpecDecEq

/-- info: 'ECCLib.Scheme.completeOrthogonalIdempotents_orbProjSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.completeOrthogonalIdempotents_orbProjSub

/-- info: 'ECCLib.Scheme.card_orbits_dual_eq_card_maximalSpectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_orbits_dual_eq_card_maximalSpectrum

/-- info: 'ECCLib.Scheme.exists_equiv_orbProjSub_eq_primitiveIdempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.exists_equiv_orbProjSub_eq_primitiveIdempotent

/-- info: 'ECCLib.Scheme.translationSpectrumEquiv' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.translationSpectrumEquiv

/-- info: 'ECCLib.Scheme.orbProjSub_eq_primitiveIdempotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbProjSub_eq_primitiveIdempotent

/-- info: 'ECCLib.Scheme.splitChar_adj_eq_pEnt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.splitChar_adj_eq_pEnt

/-- info: 'ECCLib.Scheme.spectralMult_translationSpectrumEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.spectralMult_translationSpectrumEquiv

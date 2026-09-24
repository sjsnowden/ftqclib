/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonSpectrum

/-!
# Checks for `ECCLib/Scheme/JohnsonSpectrum.lean`

Axiom sweeps, and the non-vacuity rows: every instance hypothesis of the main theorem
is dischargeable at a live carrier, and the main theorem itself instantiates at `J(4,2)`.
No row touches the group — `Fintype (Equiv.Perm (Fin n))` is `n!`, and
`Scheme/JohnsonCheck.lean` records where deciding through it dies.
-/

namespace ECCLib.Scheme.Johnson

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.Johnson.card_kSub' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_kSub

/-- info: 'ECCLib.Scheme.Johnson.johnsonCommutative' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonCommutative

/-- info: 'ECCLib.Scheme.Johnson.johnsonSpecFintype' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonSpecFintype

/-- info: 'ECCLib.Scheme.Johnson.johnsonSpecDecEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonSpecDecEq

/-- info: 'ECCLib.Scheme.Johnson.orbWidth' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.orbWidth

/-- info: 'ECCLib.Scheme.Johnson.interCard_eq_orbWidth' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.interCard_eq_orbWidth

/-- info: 'ECCLib.Scheme.Johnson.mem_orbital_iff_interCard_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.mem_orbital_iff_interCard_eq

/-- info: 'ECCLib.Scheme.Johnson.orbWidth_le' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.orbWidth_le

/-- info: 'ECCLib.Scheme.Johnson.pairA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.pairA

/-- info: 'ECCLib.Scheme.Johnson.pairB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.pairB

/-- info: 'ECCLib.Scheme.Johnson.injective_sumElim_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.injective_sumElim_pair

/-- info: 'ECCLib.Scheme.Johnson.johnsonVec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonVec

/-- info: 'ECCLib.Scheme.Johnson.johnsonVec_ne_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonVec_ne_zero

/-- info: 'ECCLib.Scheme.Johnson.orbitalAdj_mulVec_johnsonVec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.orbitalAdj_mulVec_johnsonVec

/-- info: 'ECCLib.Scheme.Johnson.johnsonMu' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonMu

/-- info: 'ECCLib.Scheme.Johnson.exists_orbWidth_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.exists_orbWidth_eq

/-- info: 'ECCLib.Scheme.Johnson.isCommonEigenvector_johnsonVec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.isCommonEigenvector_johnsonVec

/-- info: 'ECCLib.Scheme.Johnson.johnsonChi_apply_orbitalBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonChi_apply_orbitalBasis

/-- info: 'ECCLib.Scheme.Johnson.exists_equiv_eigenmatrixP_eq_eberlein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.exists_equiv_eigenmatrixP_eq_eberlein

/-- info: 'ECCLib.Scheme.Johnson.johnsonSpectrumEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.johnsonSpectrumEquiv

/-- info: 'ECCLib.Scheme.Johnson.eigenmatrixP_johnson' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.eigenmatrixP_johnson

/-! ## Non-vacuity: the main theorem instantiates at a live carrier -/

section Live

/-- The carrier guard at `J(4,2)`, discharged once; `local`, so nothing leaks from a check
module. -/
local instance kSub42Nonempty : Nonempty (KSub 4 2) := KSub.nonempty (by norm_num)

/-- The spectrum equivalence exists at a live carrier. -/
noncomputable example : Fin (min 2 (4 - 2) + 1)
    ≃ MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin 4)) (KSub 4 2)) :=
  johnsonSpectrumEquiv

/-- The main theorem, live at `J(4,2)`: nothing in the statement is vacuously quantified. -/
example (jj : Fin (min 2 (4 - 2) + 1))
    (Ω : ↥(orbits (Equiv.Perm (Fin 4)) (KSub 4 2 × KSub 4 2))) :
    eigenmatrixP (johnsonSpectrumEquiv jj) Ω
      = ((ECCLib.Delsarte.eberlein 4 2 (2 - orbWidth Ω) (jj : ℕ) : ℤ) : ℂ) :=
  eigenmatrixP_johnson jj Ω

/-- info: 'ECCLib.Scheme.Johnson.kSub42Nonempty' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.kSub42Nonempty

end Live

end ECCLib.Scheme.Johnson

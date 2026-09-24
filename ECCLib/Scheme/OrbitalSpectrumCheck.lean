/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitalSpectrum
import ECCLib.Scheme.Johnson

/-!
# Checks for the orbital spectrum

Axiom sweeps, the discriminating row that self-pairing is a genuine restriction, the
instance-diamond check on the derived `CommRing`, the
control row on the eigenvalue extraction, and the Johnson instantiation of the eigenvalue
theorem — the non-vacuity witness that every instance hypothesis of the spectral layer is
simultaneously dischargeable at a live carrier.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.linearIndependent_of_orthogonalIdempotents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.linearIndependent_of_orthogonalIdempotents

/-- info: 'ECCLib.Scheme.isReduced_orbitalAlgebra' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isReduced_orbitalAlgebra

/-- info: 'ECCLib.Scheme.conjTranspose_mem_orbitalAlgebra' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.conjTranspose_mem_orbitalAlgebra

/-- info: 'ECCLib.Scheme.card_maximalSpectrum_eq_card_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_maximalSpectrum_eq_card_orbits

/-- info: 'ECCLib.Scheme.eigenmatrixP_mul_eigenmatrixQ' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eigenmatrixP_mul_eigenmatrixQ

/-- info: 'ECCLib.Scheme.eigenmatrixQ_mul_eigenmatrixP' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eigenmatrixQ_mul_eigenmatrixP

/-- info: 'ECCLib.Scheme.mul_comm_of_isSelfPaired' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mul_comm_of_isSelfPaired

/-- info: 'ECCLib.Scheme.coe_idemBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coe_idemBasis

/-- info: 'ECCLib.Scheme.orthogonalIdempotents_idemBasis' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orthogonalIdempotents_idemBasis

/-- info: 'ECCLib.Scheme.mul_idemBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mul_idemBasis

/-- info: 'ECCLib.Scheme.eigenmatrixP_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eigenmatrixP_apply

/-- info: 'ECCLib.Scheme.orbitalBasis_mul_idemBasis' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbitalBasis_mul_idemBasis

/-- info: 'ECCLib.Scheme.orbitalAdj_mul_orbitalIdem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbitalAdj_mul_orbitalIdem

/-- info: 'ECCLib.Scheme.coe_orbitalIdem_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coe_orbitalIdem_ne_zero

/-- info: 'ECCLib.Scheme.smul_orbitalIdem_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.smul_orbitalIdem_injective

/-- info: 'ECCLib.Scheme.eigenmatrixP_mem_spectrum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eigenmatrixP_mem_spectrum

/-- info: 'ECCLib.Scheme.eigenmatrixQ_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eigenmatrixQ_apply

/-- info: 'ECCLib.Scheme.idemBasis_eq_sum_repr' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.idemBasis_eq_sum_repr

/-- info: 'ECCLib.Scheme.orbitalIdem_eq_sum_repr' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbitalIdem_eq_sum_repr

/-- info: 'ECCLib.Scheme.repr_idemBasis_eq_entry' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.repr_idemBasis_eq_entry

/-- info: 'ECCLib.Scheme.eigenmatrixQ_eq_card_mul_entry' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eigenmatrixQ_eq_card_mul_entry

/-! ## Discriminating row — self-pairing is a real restriction, not a formality

A cyclic group acting on itself by translation is **not** self-paired once the order exceeds two:
swapping `x` and `y` would need `g + x = y` and `g + y = x`, hence `2g = 0` with `g = y - x`, which
in odd order forces `x = y`.

Its orbital algebra is nonetheless **commutative**, and the general layer knows it:
`mul_comm_of_regular` proves that a regular action of an abelian group has a commutative
orbital algebra. So this is not merely an illustration — it is a **separating example**, compiled
below, and it is what makes `isSelfPaired_iff_forall_isSymm` a statement about *symmetry* rather
than about commutativity.

This is also why commutativity enters the spectral layer as a hypothesis
(`Subalgebra.IsCommutative`) rather than as a conclusion of self-pairing: three independent
sufficient conditions feed one interface, and none implies another.

The translation layer's own instance of this, at `ZMod 7` with the doubling action, is a bridge
row and is recorded with the bridge. -/

abbrev Cyc3 : Type := Multiplicative (ZMod 3)

/-- The regular action of a group of odd order is not self-paired. -/
theorem not_isSelfPaired_Cyc3 : ¬ IsSelfPaired Cyc3 Cyc3 := by
  unfold IsSelfPaired
  decide

/-- **Commutative but NOT self-paired, at one object.** The separating example the iff needs:
`Subalgebra.IsCommutative` is strictly weaker than `IsSelfPaired`, so
`isSelfPaired_iff_forall_isSymm` cannot be strengthened by swapping `IsSymm` for commutativity.
Both halves concern the same object, `Cyc3` acting on itself; `mul_comm_of_regular` supplies the
commutativity. -/
theorem commutative_not_isSelfPaired_Cyc3 :
    Subalgebra.IsCommutative (orbitalAlgebra ℂ Cyc3 Cyc3) ∧ ¬ IsSelfPaired Cyc3 Cyc3 :=
  ⟨isCommutative_of_regular, not_isSelfPaired_Cyc3⟩

/-- info: 'ECCLib.Scheme.commutative_not_isSelfPaired_Cyc3' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.commutative_not_isSelfPaired_Cyc3

/-- ...and the general theory applies to it, with commutativity supplied rather than assumed:
the instance is a theorem. -/
example : IsReduced ↥(orbitalAlgebra ℂ Cyc3 Cyc3) :=
  letI := isCommutative_of_regular (G := Cyc3) (R := ℂ)
  isReduced_orbitalAlgebra

/-- The ring-independence corollary, exercised: symmetry over `ℤ` and over `ℂ` are the same
condition, so `Cyc3` fails both. -/
example : ¬ (∀ M : Matrix Cyc3 Cyc3 ℤ, M ∈ orbitalAlgebra ℤ Cyc3 Cyc3 → M.IsSymm) :=
  fun h => not_isSelfPaired_Cyc3 (isSelfPaired_of_forall_isSymm h)

/-! ## Instance-diamond check

An explicit `rfl` comparing the derived `CommRing` against Mathlib's
`Subalgebra.toCommRing` wherever both apply — i.e. over a commutative ambient algebra. If this
row ever fails, the derived instance must become `scoped` and every consumer pays an
`open scoped`. It does not fail. -/

example (S : Subalgebra ℂ ℂ) [Subalgebra.IsCommutative S] :
    (Subalgebra.instCommRingOfIsCommutative S) = (S.toCommRing) := rfl

/-- info: 'ECCLib.Scheme.idemBasis_repr_eq_splitChar' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.idemBasis_repr_eq_splitChar

/-! ## Control row — the eigenvalue extraction returns known values on known elements

The identity matrix lies in the algebra and fixes every idempotent, so the extracted
coefficient must be `1`. If `mul_idemBasis`'s extraction returned garbage (or zero), this row
would fail. This is the control for the orientation pin. -/

section Control

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]
variable [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
variable [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
variable [Nonempty X]

theorem repr_one_idemBasis (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    idemBasis.repr (1 : ↥(orbitalAlgebra ℂ G X)) I = 1 := by
  have h := mul_idemBasis (1 : ↥(orbitalAlgebra ℂ G X)) I
  rw [one_mul] at h
  refine (smul_orbitalIdem_injective (c := 1) (d := idemBasis.repr 1 I) I ?_).symm
  rw [one_smul]
  have h2 := congrArg (Subtype.val (p := fun M => M ∈ orbitalAlgebra ℂ G X)) h
  rw [← congrFun coe_idemBasis I]
  simpa using h2

end Control

/-- info: 'ECCLib.Scheme.repr_one_idemBasis' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.repr_one_idemBasis

/-! ## The Johnson instantiation — non-vacuity of the whole instance stack

The spectral layer's hypotheses are `Subalgebra.IsCommutative`, `Fintype`/`DecidableEq` on the
spectrum, and `Nonempty X`. Every one is dischargeable at the Johnson carrier, and the
eigenvalue theorem holds there **live** — so nothing in the layer is vacuously quantified over
an empty instance space. The instances are `local`: their proper home is
`Scheme/JohnsonSpectrum.lean`, and leaking them from a check module would let every downstream
file silently depend on a leaf. -/

section JohnsonLive

open Johnson

variable {n k : ℕ}

local instance johnsonComm :
    Subalgebra.IsCommutative (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) :=
  isCommutative_johnsonAlgebra ℂ

noncomputable local instance johnsonSpecFintype :
    Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) := by
  haveI : IsArtinianRing ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) :=
    IsArtinianRing.of_finite ℂ _
  exact Fintype.ofFinite _

noncomputable local instance johnsonSpecDecEq :
    DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) :=
  Classical.decEq _

/-- **The eigenvalue theorem, live at the Johnson carrier.** `Nonempty (KSub n k)` is supplied
by `KSub.nonempty` from `k ≤ n`, so nothing here is hypothetically quantified. -/
theorem johnson_orbitalAdj_mul_orbitalIdem [Nonempty (KSub n k)]
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) :
    orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)) *
        ((orbitalIdem I : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) :
          Matrix (KSub n k) (KSub n k) ℂ)
      = eigenmatrixP I Ω •
          ((orbitalIdem I : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) :
            Matrix (KSub n k) (KSub n k) ℂ) :=
  orbitalAdj_mul_orbitalIdem Ω I

end JohnsonLive

/-- info: 'ECCLib.Scheme.johnson_orbitalAdj_mul_orbitalIdem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.johnson_orbitalAdj_mul_orbitalIdem

/-- info: 'ECCLib.Scheme.johnsonComm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.johnsonComm

/-- info: 'ECCLib.Scheme.johnsonSpecFintype' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.johnsonSpecFintype

/-- info: 'ECCLib.Scheme.johnsonSpecDecEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.johnsonSpecDecEq

end ECCLib.Scheme

/-- info: 'ECCLib.Scheme.sum_spectralMult_mul_eigenmatrixP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_spectralMult_mul_eigenmatrixP

/-- info: 'ECCLib.Scheme.eq_spectralMult_of_forall_sum_mul_eigenmatrixP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eq_spectralMult_of_forall_sum_mul_eigenmatrixP

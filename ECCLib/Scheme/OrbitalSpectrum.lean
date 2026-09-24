/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.SelfPaired
import ECCLib.Matrix.SpectralDetermination
import ECCLib.SplitAlgebra
import ECCLib.StructureConstants
import ECCLib.Matrix.CommStarMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The spectrum of a commutative orbital algebra

A commutative orbital algebra over `ℂ` splits as a product of copies of `ℂ`, one for each
maximal ideal. Its primitive idempotents are therefore a second basis, alongside the orbital
indicators, and the two change-of-basis matrices between them are Delsarte's eigenmatrices
`P` and `Q`.

## Main definitions

* `orbitalSplit` — the splitting.
* `orbitalIdem` — the primitive idempotents.
* `idemBasis` — those idempotents, as a basis.
* `eigenmatrixP`, `eigenmatrixQ` — the two change-of-basis matrices, in Delsarte's orientation.

## Main results

* `isReduced_orbitalAlgebra` — a commutative orbital algebra over `ℂ` is reduced.
* `eigenmatrixP_mul_eigenmatrixQ` — **`P * Q = |X| • 1`**, and its transpose-side partner.
* `orbitalAdj_mul_orbitalIdem` — **the eigenvalue theorem**: each orbital adjacency matrix acts
  on each primitive idempotent by the corresponding `P`-entry. This is what makes `P` an
  *eigen*matrix rather than a change of basis, and it pins the orientation of the two names.
* `eigenmatrixQ_eq_card_mul_entry` — `Q`'s entries are `|X|` times entries of the idempotent
  matrices: the other half of the orientation pin.

## Orientation

The two names are easy to attach the wrong way around: the product identity `P·Q = |X|·1` is
symmetric in the pair and does not distinguish them. The orientation is therefore pinned by
content. The eigenvalue theorem below extracts the coefficient in the *idempotent* basis, which
is `P`'s side only in this orientation, and `eigenmatrixQ_eq_card_mul_entry` pins the other
half.

## What `P * Q = |X| • 1` is, and what it is not

It is the statement that two mutually inverse change-of-basis matrices are mutually inverse,
scaled. The `|X|` is **Delsarte's normalisation, carried by the definition of `Q`** — it is
bookkeeping, not content, and this file says so rather than presenting the identity as a
theorem about schemes.

In particular this does **not** generalise `Scheme/Spectrum.lean`'s `PQ_eq`. That result is a
summation identity over dual orbits with a choice of representatives, and it *is* character
orthogonality — genuine content about a translation scheme. The statement here is broader in
indexing and weaker in content. Neither implies the other formally.

What this layer does buy that `Scheme/Spectrum.lean` does not: the index here is
`MaximalSpectrum`, which
is canonical, so `P` and `Q` need no choice of representatives at all.

## The commutativity hypothesis

Commutativity enters as `Subalgebra.IsCommutative`, an instance hypothesis, and is never
derived here. `Scheme/SelfPaired.lean` supplies one way to discharge it; the translation layer
supplies another, from circulancy, and neither implies the other. Keeping it a hypothesis is
what lets both consume this layer.

## Implementation notes

`Fintype` and `DecidableEq` on the maximal spectrum are taken as instance hypotheses rather than
manufactured inside each statement. Both are always satisfiable — `Fintype.ofFinite` and
`Classical.decEq` — but `MaximalSpectrum` carries only `Finite`, and `CompleteOrthogonalIdempotents`
together with `Basis.toMatrix` need the stronger forms. Supplying them at the section boundary
keeps the statements readable and the choice immaterial, since `Fintype` is a subsingleton.

Reducedness comes from `Matrix/CommStarMatrix.lean` and needs **both** commutativity and
⋆-closure. ⋆-closure is free here — it holds for any permutation commutant with no hypothesis on
the action — but commutativity is not, and dropping it makes the statement false: the full
matrix algebra is ⋆-closed and has nonzero nilpotents.
-/

namespace ECCLib.Scheme

open Matrix Finset

/-! ## Linear independence of an orthogonal idempotent family

Stated for an arbitrary algebra over a field: nonzero orthogonal idempotents are independent.
Verified absent from Mathlib v4.29.1. -/

theorem linearIndependent_of_orthogonalIdempotents {k A ι : Type*} [Field k] [Ring A]
    [Algebra k A] {e : ι → A} (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0) :
    LinearIndependent k e := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  have hmul : (∑ i ∈ s, g i • e i) * e j = 0 := by rw [hg, zero_mul]
  rw [Finset.sum_mul, Finset.sum_eq_single j] at hmul
  · rw [smul_mul_assoc, (he.idem j).eq] at hmul
    exact (smul_eq_zero.mp hmul).resolve_right (hne j)
  · intro i _ hij
    rw [smul_mul_assoc, he.ortho hij, smul_zero]
  · intro h
    exact absurd hj h

section Spectrum

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]

/-- The orbital algebra over `ℂ` is `⋆`-closed, with no hypothesis on the action. This is the
`orbitalAlgebra` face of `conjTranspose_mem_permCommutant`, and it holds by definitional
unfolding because `orbitalAlgebra` *is* a `permCommutant`. -/
theorem conjTranspose_mem_orbitalAlgebra {M : Matrix X X ℂ}
    (hM : M ∈ orbitalAlgebra ℂ G X) : Mᴴ ∈ orbitalAlgebra ℂ G X :=
  conjTranspose_mem_permCommutant hM

variable [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]

/-- **A commutative orbital algebra over `ℂ` is reduced.** Both hypotheses are load-bearing:
⋆-closure is free, commutativity is not. -/
instance isReduced_orbitalAlgebra : IsReduced ↥(orbitalAlgebra ℂ G X) :=
  isReduced_of_commute_of_conjTranspose_mem _
    (fun M hM N hN => congrArg Subtype.val
      (Subalgebra.IsCommutative.mul_comm' (⟨M, hM⟩ : ↥(orbitalAlgebra ℂ G X)) ⟨N, hN⟩))
    (fun _ hM => conjTranspose_mem_orbitalAlgebra hM)

/-- The number of maximal ideals is the number of orbitals: the two bases have the same size,
which is what makes `P` and `Q` square. Stated with `Nat.card`, so it needs no `Fintype` on a
spectrum that carries only `Finite`. -/
theorem card_maximalSpectrum_eq_card_orbits :
    Nat.card (MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) = (orbits G (X × X)).card := by
  rw [ECCLib.card_maximalSpectrum_eq_finrank ℂ ↥(orbitalAlgebra ℂ G X),
    finrank_orbitalAlgebra]

variable [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
variable [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]

/-- The splitting of a commutative orbital algebra into one copy of `ℂ` per maximal ideal. -/
noncomputable def orbitalSplit :
    ↥(orbitalAlgebra ℂ G X) ≃ₐ[ℂ] (MaximalSpectrum ↥(orbitalAlgebra ℂ G X) → ℂ) :=
  ECCLib.splitAlgEquiv ℂ ↥(orbitalAlgebra ℂ G X)

/-- The primitive idempotents. -/
noncomputable def orbitalIdem (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    ↥(orbitalAlgebra ℂ G X) :=
  ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I

omit [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] in
theorem orbitalIdem_ne_zero (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    orbitalIdem (G := G) (X := X) I ≠ 0 :=
  ECCLib.primitiveIdempotent_ne_zero I

theorem completeOrthogonalIdempotents_orbitalIdem :
    CompleteOrthogonalIdempotents (orbitalIdem (G := G) (X := X)) :=
  ECCLib.completeOrthogonalIdempotents_primitiveIdempotent

omit [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] in
theorem linearIndependent_orbitalIdem :
    LinearIndependent ℂ (orbitalIdem (G := G) (X := X)) := by
  haveI : IsArtinianRing ↥(orbitalAlgebra ℂ G X) :=
    IsArtinianRing.of_finite ℂ ↥(orbitalAlgebra ℂ G X)
  haveI : Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) := Fintype.ofFinite _
  exact linearIndependent_of_orthogonalIdempotents
    completeOrthogonalIdempotents_orbitalIdem.toOrthogonalIdempotents orbitalIdem_ne_zero


/-! Nonemptiness of the spectrum is needed only for the bundled basis below. It is **derived,
not hypothesised**: `[Nonempty X]` makes the algebra nontrivial, and Mathlib supplies
`Nonempty (MaximalSpectrum _)` from nontriviality
(`Mathlib/RingTheory/Spectrum/Maximal/Basic.lean`). -/

variable [Nonempty X]

/-- **The primitive idempotents, as a basis.** -/
noncomputable def idemBasis :
    Module.Basis (MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) ℂ ↥(orbitalAlgebra ℂ G X) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_orbitalIdem
    (by rw [← Nat.card_eq_fintype_card]
        exact ECCLib.card_maximalSpectrum_eq_finrank ℂ ↥(orbitalAlgebra ℂ G X))

/-- The idempotent basis is the family of primitive idempotents. -/
theorem coe_idemBasis :
    ⇑(idemBasis (G := G) (X := X)) = orbitalIdem (G := G) (X := X) :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem orthogonalIdempotents_idemBasis :
    OrthogonalIdempotents (⇑(idemBasis (G := G) (X := X))) := by
  rw [coe_idemBasis]
  exact completeOrthogonalIdempotents_orbitalIdem.toOrthogonalIdempotents

/-- Every element of the algebra acts on a primitive idempotent by a scalar — the eigenvalue
equation inside the algebra, `mul_basis_eq_repr_smul` at the idempotent basis. -/
theorem mul_idemBasis (M : ↥(orbitalAlgebra ℂ G X))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    M * idemBasis I = idemBasis.repr M I • idemBasis I :=
  mul_basis_eq_repr_smul _ orthogonalIdempotents_idemBasis M I

/-! ## The eigenmatrices

`P` and `Q` are the two change-of-basis matrices between the orbital basis and the idempotent
basis, in **Delsarte's orientation**: `P` expands the orbital indicators in the idempotents, so
its entries are the eigenvalues (`orbitalAdj_mul_orbitalIdem`); `Q`, carrying the `|X|`
normalisation, expands the idempotents in the indicators, so its entries are scaled matrix
entries of the idempotents (`eigenmatrixQ_eq_card_mul_entry`). Both contents are theorems, so
the orientation is machine-checked rather than a naming convention. -/

/-- **The first eigenmatrix** (Delsarte's `P`): row a maximal ideal, column an orbital. The
entry is the coefficient of the orbital indicator's expansion over the idempotents —
equivalently, **the eigenvalue of that orbital's adjacency matrix on that idempotent's block**
(`orbitalAdj_mul_orbitalIdem`). -/
noncomputable def eigenmatrixP :
    Matrix (MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) ↥(orbits G (X × X)) ℂ :=
  idemBasis.toMatrix (orbitalBasis (R := ℂ) (G := G) (X := X))

/-- **The second eigenmatrix** (Delsarte's `Q`), carrying his `|X|` normalisation in its
definition. The factor is bookkeeping for the product identities; the content statement is
`eigenmatrixQ_eq_card_mul_entry`. -/
noncomputable def eigenmatrixQ :
    Matrix ↥(orbits G (X × X)) (MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) ℂ :=
  (Fintype.card X : ℂ) • (orbitalBasis (R := ℂ) (G := G) (X := X)).toMatrix idemBasis

/-- **`P * Q = |X| • 1`.** Two mutually inverse change-of-basis matrices are mutually inverse. -/
theorem eigenmatrixP_mul_eigenmatrixQ :
    eigenmatrixP (G := G) (X := X) * eigenmatrixQ (G := G) (X := X)
      = (Fintype.card X : ℂ) • 1 := by
  rw [eigenmatrixP, eigenmatrixQ, Matrix.mul_smul,
    Module.Basis.toMatrix_mul_toMatrix_flip]

/-- The partner identity on the orbital index. -/
theorem eigenmatrixQ_mul_eigenmatrixP :
    eigenmatrixQ (G := G) (X := X) * eigenmatrixP (G := G) (X := X)
      = (Fintype.card X : ℂ) • 1 := by
  rw [eigenmatrixP, eigenmatrixQ, Matrix.smul_mul,
    Module.Basis.toMatrix_mul_toMatrix_flip]

/-! ## What the entries are -/

/-- **The idempotent-basis coordinates are the split characters**: the bridge between the
change-of-basis picture and the character picture, and what turns the determination theorem's
conclusion into statements about `eigenmatrixP`. -/
theorem idemBasis_repr_eq_splitChar (M : ↥(orbitalAlgebra ℂ G X))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    idemBasis.repr M I = ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ G X) I M := by
  conv_lhs => rw [← ECCLib.sum_splitChar_smul_primitiveIdempotent
    (K := ℂ) (A := ↥(orbitalAlgebra ℂ G X)) M]
  rw [show (∑ I', ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ G X) I' M
        • ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I')
      = ∑ I', ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ G X) I' M • idemBasis I' from
    Finset.sum_congr rfl fun I' _ => by
      rw [show ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I'
        = orbitalIdem (G := G) (X := X) I' from rfl, ← congrFun coe_idemBasis I']]
  rw [map_sum, Finsupp.finset_sum_apply]
  rw [Finset.sum_congr rfl fun I' _ => by
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self]]
  simp [Finsupp.single_apply, eq_comm]

/-- The `P`-entry, as a coefficient in the idempotent basis. -/
theorem eigenmatrixP_apply (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X))
    (Ω : ↥(orbits G (X × X))) :
    eigenmatrixP (G := G) (X := X) I Ω
      = idemBasis.repr
          ⟨orbitalAdj ℂ (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩ I := by
  simp only [eigenmatrixP, Module.Basis.toMatrix_apply, coe_orbitalBasis]

/-- The eigenvalue statement, inside the algebra. -/
theorem orbitalBasis_mul_idemBasis (Ω : ↥(orbits G (X × X)))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    orbitalBasis (R := ℂ) Ω * idemBasis I
      = eigenmatrixP (G := G) (X := X) I Ω • idemBasis I := by
  rw [eigenmatrixP, Module.Basis.toMatrix_apply]
  exact mul_idemBasis _ _

/-- **The eigenvalue theorem, as an identity of actual matrices**: each orbital adjacency
matrix acts on each primitive idempotent by the corresponding `P`-entry. This is the content
pin for the orientation of `eigenmatrixP`: under the transposed orientation this statement
is false, and its proof — which extracts the coefficient in the idempotent basis — cannot
close. -/
theorem orbitalAdj_mul_orbitalIdem (Ω : ↥(orbits G (X × X)))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    orbitalAdj ℂ (Ω : Finset (X × X)) *
        ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
      = eigenmatrixP (G := G) (X := X) I Ω •
          ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) := by
  have h := congrArg (Subtype.val (p := fun M => M ∈ orbitalAlgebra ℂ G X))
    (orbitalBasis_mul_idemBasis (G := G) (X := X) Ω I)
  rw [← congrFun coe_idemBasis I]
  simpa [val_orbitalBasis] using h

omit [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] [Nonempty X] in
theorem coe_orbitalIdem_ne_zero (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) ≠ 0 := by
  intro h
  exact orbitalIdem_ne_zero I (Subtype.ext (by simpa using h))

omit [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] [Nonempty X] in
/-- The scalar in the eigenvalue equation is unique, because the idempotent is nonzero. -/
theorem smul_orbitalIdem_injective {c d : ℂ} (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X))
    (h : c • ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
      = d • ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)) :
    c = d := by
  by_contra hcd
  have hsub : c - d ≠ 0 := sub_ne_zero.mpr hcd
  have h0 : (c - d) • ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) :
      Matrix X X ℂ) = 0 := by rw [sub_smul, h, sub_self]
  exact coe_orbitalIdem_ne_zero I ((smul_eq_zero.mp h0).resolve_left hsub)

/-- The `P`-entry really is a spectral value of the adjacency matrix, in Mathlib's sense. -/
theorem eigenmatrixP_mem_spectrum (Ω : ↥(orbits G (X × X)))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    eigenmatrixP (G := G) (X := X) I Ω
      ∈ spectrum ℂ (orbitalAdj ℂ (Ω : Finset (X × X)) : Matrix X X ℂ) := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨N, hN⟩ := hunit.exists_left_inv
  refine coe_orbitalIdem_ne_zero I ?_
  have hkill : (algebraMap ℂ (Matrix X X ℂ) (eigenmatrixP (G := G) (X := X) I Ω)
        - orbitalAdj ℂ (Ω : Finset (X × X)))
      * ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) = 0 := by
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      orbitalAdj_mul_orbitalIdem, sub_self]
  have h1 : N * ((algebraMap ℂ (Matrix X X ℂ) (eigenmatrixP (G := G) (X := X) I Ω)
        - orbitalAdj ℂ (Ω : Finset (X × X)))
      * ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)) = 0 := by
    rw [hkill, mul_zero]
  rwa [← mul_assoc, hN, one_mul] at h1

/-- The `Q`-entry, unnormalised: the coefficient of the idempotent's expansion over the orbital
indicators. Definitional. -/
theorem eigenmatrixQ_apply (Ω : ↥(orbits G (X × X)))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    eigenmatrixQ (G := G) (X := X) Ω I
      = (Fintype.card X : ℂ)
        * (orbitalBasis (R := ℂ) (G := G) (X := X)).repr (idemBasis I) Ω :=
  rfl

/-- Each idempotent expanded over the orbital basis, inside the algebra. -/
theorem idemBasis_eq_sum_repr (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    idemBasis (G := G) (X := X) I
      = ∑ Ω : ↥(orbits G (X × X)),
          (orbitalBasis (R := ℂ) (G := G) (X := X)).repr (idemBasis I) Ω
            • orbitalBasis (R := ℂ) Ω :=
  (orbitalBasis.sum_repr (idemBasis I)).symm

/-- Each idempotent, as an actual matrix, expanded over the orbital indicators. -/
theorem orbitalIdem_eq_sum_repr (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
      = ∑ Ω : ↥(orbits G (X × X)),
          (orbitalBasis (R := ℂ) (G := G) (X := X)).repr (idemBasis I) Ω
            • orbitalAdj ℂ (Ω : Finset (X × X)) := by
  rw [← congrFun coe_idemBasis I]
  have h := congrArg (Subtype.val (p := fun M => M ∈ orbitalAlgebra ℂ G X))
    (idemBasis_eq_sum_repr (G := G) (X := X) I)
  rw [h]
  simp [val_orbitalBasis]

/-- The expansion coefficients are the entries of the idempotent matrices: any pair in the
orbital reads the coefficient off. -/
theorem repr_idemBasis_eq_entry {Ω : ↥(orbits G (X × X))} {p : X × X}
    (hp : p ∈ (Ω : Finset (X × X))) (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    (orbitalBasis (R := ℂ) (G := G) (X := X)).repr (idemBasis I) Ω
      = ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) p.1 p.2 := by
  rw [orbitalIdem_eq_sum_repr, Matrix.sum_apply, Finset.sum_eq_single Ω]
  · simp [orbitalAdj, hp]
  · intro Ω' _ hne
    have hnot : p ∉ (Ω' : Finset (X × X)) := fun hp' =>
      hne (Subtype.ext (eq_of_mem_orbits_of_mem Ω'.2 Ω.2 hp' hp))
    simp [orbitalAdj, hnot]
  · intro hc
    exact absurd (Finset.mem_univ Ω) hc

/-- **The entries of `Q` are `|X|` times entries of the idempotent matrices** — the other half
of the orientation pin: `Q` holds matrix entries, `P` holds eigenvalues. -/
theorem eigenmatrixQ_eq_card_mul_entry {Ω : ↥(orbits G (X × X))} {p : X × X}
    (hp : p ∈ (Ω : Finset (X × X))) (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    eigenmatrixQ (G := G) (X := X) Ω I
      = (Fintype.card X : ℂ)
        * ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) p.1 p.2 := by
  rw [eigenmatrixQ_apply, repr_idemBasis_eq_entry hp]

/-! ## The trace system in eigenmatrix form, and its uniqueness

The multiplicities pair against the rows of `P` to the traces of the adjacencies
(`sum_spectralMult_mul_eigenmatrixP`), and `Q P = |X| • 1` makes them the **only** vector
that does (`eq_spectralMult_of_forall_sum_mul_eigenmatrixP`) — the characterisation the
carriers' closed forms certify against. -/

/-- **The trace system, in `P` form**: the multiplicities against a `P`-column recover the
trace of that orbital's adjacency. -/
theorem sum_spectralMult_mul_eigenmatrixP (Ω : ↥(orbits G (X × X))) :
    ∑ I, (spectralMult (orbitalAlgebra ℂ G X) I : ℂ) * eigenmatrixP (G := G) (X := X) I Ω
      = (orbitalAdj ℂ (Ω : Finset (X × X))).trace := by
  have h := sum_spectralMult_mul_splitChar_eq_trace
    (S := orbitalAlgebra ℂ G X)
    ⟨orbitalAdj ℂ (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩
  rw [show (((⟨orbitalAdj ℂ (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩ :
      ↥(orbitalAlgebra ℂ G X)) : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
      = orbitalAdj ℂ (Ω : Finset (X × X)) from rfl] at h
  rw [← h]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [eigenmatrixP_apply, idemBasis_repr_eq_splitChar]

/-- **The trace system determines the multiplicities**: any vector pairing against every
`P`-column to the adjacency traces is the multiplicity vector, because `Q P = |X| • 1`. -/
theorem eq_spectralMult_of_forall_sum_mul_eigenmatrixP
    {m : MaximalSpectrum ↥(orbitalAlgebra ℂ G X) → ℂ}
    (hm : ∀ Ω : ↥(orbits G (X × X)),
      ∑ I, m I * eigenmatrixP (G := G) (X := X) I Ω
        = (orbitalAdj ℂ (Ω : Finset (X × X))).trace)
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    m I = (spectralMult (orbitalAlgebra ℂ G X) I : ℂ) := by
  set d : MaximalSpectrum ↥(orbitalAlgebra ℂ G X) → ℂ :=
    fun I => m I - (spectralMult (orbitalAlgebra ℂ G X) I : ℂ) with hd
  have hvec : d ᵥ* eigenmatrixP (G := G) (X := X) = 0 := by
    funext Ω
    rw [Matrix.vecMul, Pi.zero_apply, dotProduct]
    rw [show ∑ J, d J * eigenmatrixP (G := G) (X := X) J Ω
        = ∑ J, (m J * eigenmatrixP (G := G) (X := X) J Ω
            - (spectralMult (orbitalAlgebra ℂ G X) J : ℂ)
              * eigenmatrixP (G := G) (X := X) J Ω) from
      Finset.sum_congr rfl fun J _ => by rw [hd]; ring]
    rw [Finset.sum_sub_distrib, hm Ω, sum_spectralMult_mul_eigenmatrixP Ω, sub_self]
  have hcard : (Fintype.card X : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h1 := congrArg (fun v => v ᵥ* eigenmatrixQ (G := G) (X := X)) hvec
  simp only [Matrix.vecMul_vecMul, eigenmatrixP_mul_eigenmatrixQ, Matrix.zero_vecMul] at h1
  rw [Matrix.vecMul_smul, Matrix.vecMul_one] at h1
  have h2 := congrFun h1 I
  rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h2
  have hdI : d I = 0 := (mul_eq_zero.mp h2).resolve_left hcard
  rw [hd] at hdI
  exact sub_eq_zero.mp hdI

end Spectrum

end ECCLib.Scheme

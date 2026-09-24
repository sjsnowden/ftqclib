/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Pi

/-!
# Reduced finite algebras over an algebraically closed field split

A commutative algebra that is reduced and finite-dimensional over an algebraically closed field
is isomorphic to a product of copies of the field, one for each maximal ideal. Mathlib has the
first half of this — `IsArtinianRing.equivPi` decomposes such a ring as a product of its
**residue fields** — and this file supplies the second, that over an algebraically closed base
each residue field is the base itself.

Everything else the spectral theory of an association scheme needs is a corollary of that one
equivalence: the primitive idempotents are the preimages of `Pi.single`, and the number of them
is the dimension.

## Main definitions

* `splitAlgEquivOfBijectiveResidue` — the splitting, from the weakest hypothesis that supports it.
* `splitAlgEquiv` — its `IsAlgClosed` corollary.
* `primitiveIdempotent` — the preimage of `Pi.single`.
* `splitChar` — the character at a maximal ideal: one coordinate of the splitting.
* `equivAlgHom` — the maximal spectrum **is** the character set `A →ₐ[K] K`.

## Main results

* `card_maximalSpectrum_eq_finrank` — the number of maximal ideals is the dimension.
* `completeOrthogonalIdempotents_primitiveIdempotent` — they are complete and orthogonal.
* `mul_primitiveIdempotent` — the eigenvalue equation: `a · eᵢ = χᵢ(a) • eᵢ`.
* `sum_splitChar_smul_primitiveIdempotent` — every element is the character-weighted sum of
  the primitive idempotents.
* `exists_equiv_primitiveIdempotent` — **uniqueness of the primitive decomposition**: a
  complete orthogonal family of nonzero idempotents of the right cardinality is the primitive
  family up to a bijection of indices.
* `algHom_ext_of_ker_eq` — characters with equal kernels are equal, at
  `[CommRing K] [Ring A]`.
* `isReduced_of_splitEquiv`, `moduleFinite_of_splitEquiv` — the converses: the conclusion
  *implies* two of the hypotheses, so those are forced rather than chosen.

## On the hypotheses

Of the hypotheses, exactly one can be weakened.
`IsAlgClosed K` is **not** the weakest hypothesis: what the proof consumes is only that each
residue map `K → A ⧸ I` is bijective, and that is strictly weaker, since it holds over `ℝ`
whenever `A` is a field. So the general form takes it as an explicit hypothesis and
`splitAlgEquiv` is a corollary — which also lets the general form avoid `Ideal.Quotient.field`
entirely, dropping a `Field` instance from the proof.

Of the other hypotheses, `IsReduced A` and `Module.Finite K A` are forced rather than
convenient: the conclusion implies both, proved here as `isReduced_of_splitEquiv` and
`moduleFinite_of_splitEquiv`. `Module.Finite` in particular resists every weakening considered —
`IsArtinianRing` alone and `Finite (MaximalSpectrum A)` alone are both refuted by `RatFunc ℂ`,
`FiniteDimensional` is the same class by `Iff.rfl`, and the pair
`[IsArtinianRing A] [Algebra.IsIntegral K A]` is equivalent rather than weaker, so it costs a
second class to discharge and buys nothing.

## Implementation notes

`IsArtinianRing` is **derived**, via `IsArtinianRing.of_finite`, never assumed.

`MaximalSpectrum A` is `Finite` but not `Fintype`, so `Fintype` and `DecidableEq` appear only on
the statements that genuinely need them — `Pi.single` and the finite sums inside
`CompleteOrthogonalIdempotents`. The counting theorem is stated with `Nat.card` and needs
neither. `primitiveIdempotent_ne_zero` needs no `[Nontrivial A]`: if `A` is trivial its maximal
spectrum is empty and there is no index to instantiate.

## Relation to Mathlib's Wedderburn–Artin

**The splitting itself is not new.** Mathlib has
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
(`RingTheory/SimpleModule/IsAlgClosed.lean`): a finite-dimensional semisimple algebra over an
algebraically closed field is a product of matrix algebras. A commutative Artinian reduced ring is
semisimple (`IsArtinianRing.isSemisimpleRing_of_isReduced`, `Artinian/Module.lean:648`), and
commutativity forces every block to be `1 × 1` — which is this file's conclusion. So the
mathematical content here is the commutative case of Wedderburn–Artin, reached by a different
route (residue fields via `IsArtinianRing.equivPi`) rather than by new theory.

**What is specific to this file.** Three things, which a one-line corollary of Mathlib's
theorem would not provide. (i) The index is `MaximalSpectrum A`, which is
**canonical**; Mathlib's conclusion is indexed by `Fin n` with block sizes, and that difference is
exactly what makes the eigenmatrices downstream representative-free. (ii) The hypothesis is the
weakest the proof consumes — pointwise bijectivity of the residue maps, strictly weaker than
`IsAlgClosed`. (iii) It produces a *chosen* `AlgEquiv` rather than a `Nonempty`.

**The identification is not proved here.** That `splitAlgEquiv` is the commutative case of
Mathlib's theorem is stated as a fact about the mathematics, not as a theorem in this file. No
Mathlib file mentions both `MaximalSpectrum` and `IsAlgClosed`, so the canonically-indexed form
is absent from Mathlib; the splitting is not.
-/

namespace ECCLib

open Module

section Split

variable (K A : Type*) [Field K] [CommRing A] [IsReduced A] [Algebra K A] [Module.Finite K A]

/-- **The splitting, from the weakest hypothesis that supports it**: each residue map is
bijective. Strictly weaker than `IsAlgClosed K`, which is the corollary below. -/
noncomputable def splitAlgEquivOfBijectiveResidue
    (h : ∀ I : MaximalSpectrum A, Function.Bijective (algebraMap K (A ⧸ I.asIdeal))) :
    A ≃ₐ[K] (MaximalSpectrum A → K) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact ((IsArtinianRing.equivPi A).restrictScalars K).trans
    (AlgEquiv.piCongrRight fun I =>
      (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ I.asIdeal)) (h I)).symm)

variable {K A}

omit [IsReduced A] in
/-- Over an algebraically closed base every residue map is bijective, so `IsAlgClosed` really
is a strengthening of the hypothesis above rather than a different one. -/
theorem bijective_algebraMap_residue [IsAlgClosed K] (I : MaximalSpectrum A) :
    Function.Bijective (algebraMap K (A ⧸ I.asIdeal)) := by
  haveI : I.asIdeal.IsMaximal := I.isMaximal
  haveI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  haveI : Module.Finite K (A ⧸ I.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral K (A ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite K _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

variable (K A)

/-- **A reduced finite algebra over an algebraically closed field is a product of copies of the
field**, indexed by its maximal ideals. -/
noncomputable def splitAlgEquiv [IsAlgClosed K] : A ≃ₐ[K] (MaximalSpectrum A → K) :=
  splitAlgEquivOfBijectiveResidue K A bijective_algebraMap_residue

/-- The number of maximal ideals is the dimension. Stated with `Nat.card`, which needs no
`Fintype` on a spectrum that only has `Finite`. -/
theorem card_maximalSpectrum_eq_finrank [IsAlgClosed K] :
    Nat.card (MaximalSpectrum A) = finrank K A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  rw [(splitAlgEquiv K A).toLinearEquiv.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

/-- The primitive idempotent at a maximal ideal: the preimage of the indicator. -/
noncomputable def primitiveIdempotent [IsAlgClosed K] [DecidableEq (MaximalSpectrum A)]
    (I : MaximalSpectrum A) : A :=
  (splitAlgEquiv K A).symm (Pi.single I 1)

variable {K A}

/-- Each primitive idempotent is nonzero. No `[Nontrivial A]` is needed: a trivial `A` has an
empty maximal spectrum, so there is no `I` to instantiate. -/
theorem primitiveIdempotent_ne_zero [IsAlgClosed K] [DecidableEq (MaximalSpectrum A)]
    (I : MaximalSpectrum A) : primitiveIdempotent K A I ≠ 0 := by
  intro h
  have h0 : (Pi.single I 1 : MaximalSpectrum A → K) = 0 := by
    simpa [primitiveIdempotent] using congrArg (splitAlgEquiv K A) h
  simpa using congrFun h0 I

/-- Each primitive idempotent is idempotent, with no `Fintype` on the spectrum: `Pi.single`
squares to itself coordinatewise. -/
theorem isIdempotentElem_primitiveIdempotent [IsAlgClosed K]
    [DecidableEq (MaximalSpectrum A)] (I : MaximalSpectrum A) :
    IsIdempotentElem (primitiveIdempotent K A I) := by
  unfold IsIdempotentElem
  apply (splitAlgEquiv K A).injective
  rw [map_mul, primitiveIdempotent, AlgEquiv.apply_symm_apply]
  funext J
  rcases eq_or_ne J I with h | h <;> simp [Pi.single_apply, h]

/-- The primitive idempotents form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_primitiveIdempotent [IsAlgClosed K]
    [Fintype (MaximalSpectrum A)] [DecidableEq (MaximalSpectrum A)] :
    CompleteOrthogonalIdempotents (primitiveIdempotent K A) :=
  (CompleteOrthogonalIdempotents.single (I := MaximalSpectrum A) (fun _ => K)).map
    (f := ((splitAlgEquiv K A).symm : (MaximalSpectrum A → K) ≃ₐ[K] A).toAlgHom.toRingHom)

end Split

/-! ## The characters

The splitting, read one coordinate at a time: each maximal ideal gives an algebra character
`A →ₐ[K] K`, these characters are the whole of `A →ₐ[K] K` (`equivAlgHom`), and every element
acts on each primitive idempotent by its character value (`mul_primitiveIdempotent` — the
eigenvalue equation of the split algebra). The spectral layers downstream phrase every
eigenvalue statement through these characters. -/

/-- Two algebra homomorphisms into the scalar ring with equal kernels are equal. No field on
either side, no commutativity of `A`: subtraction in `K` is all the proof uses (and is why
`CommSemiring K` genuinely fails). Mathlib has no such lemma. -/
theorem algHom_ext_of_ker_eq {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    {f g : A →ₐ[K] K} (h : RingHom.ker (f : A →+* K) = RingHom.ker (g : A →+* K)) :
    f = g := by
  ext a
  have hker : a - algebraMap K A (g a) ∈ RingHom.ker (g : A →+* K) := by
    simp [RingHom.mem_ker]
  rw [← h, RingHom.mem_ker, map_sub] at hker
  have hc : f (algebraMap K A (g a)) = g a := by simp
  have h2 : f a = f (algebraMap K A (g a)) := sub_eq_zero.mp hker
  rw [h2, hc]

section Characters

variable (K A : Type*) [Field K] [CommRing A] [IsReduced A] [Algebra K A] [Module.Finite K A]
variable [IsAlgClosed K]

/-- The **character at a maximal ideal**: the `I`-coordinate of the splitting. Needs neither
`Fintype` nor `DecidableEq` on the spectrum — it is one coordinate of the existing
equivalence. -/
noncomputable def splitChar (I : MaximalSpectrum A) : A →ₐ[K] K :=
  (Pi.evalAlgHom K (fun _ => K) I).comp (splitAlgEquiv K A).toAlgHom

variable {K A}

theorem splitChar_apply (I : MaximalSpectrum A) (a : A) :
    splitChar K A I a = splitAlgEquiv K A a I := rfl

theorem splitChar_primitiveIdempotent [DecidableEq (MaximalSpectrum A)]
    (I J : MaximalSpectrum A) :
    splitChar K A I (primitiveIdempotent K A J) = if I = J then 1 else 0 := by
  rw [splitChar_apply, primitiveIdempotent, AlgEquiv.apply_symm_apply, Pi.single_apply]

/-- **The eigenvalue equation of the split algebra**: every element acts on each primitive
idempotent by its character value. -/
theorem mul_primitiveIdempotent [DecidableEq (MaximalSpectrum A)] (a : A)
    (I : MaximalSpectrum A) :
    a * primitiveIdempotent K A I = splitChar K A I a • primitiveIdempotent K A I := by
  apply (splitAlgEquiv K A).injective
  rw [map_mul, map_smul, primitiveIdempotent, AlgEquiv.apply_symm_apply]
  funext J
  rcases eq_or_ne J I with h | h <;> simp [h, splitChar_apply]

/-- Every element is the character-weighted sum of the primitive idempotents. -/
theorem sum_splitChar_smul_primitiveIdempotent [Fintype (MaximalSpectrum A)]
    [DecidableEq (MaximalSpectrum A)] (a : A) :
    ∑ I, splitChar K A I a • primitiveIdempotent K A I = a := by
  apply (splitAlgEquiv K A).injective
  rw [map_sum]
  funext J
  simp only [map_smul, primitiveIdempotent, AlgEquiv.apply_symm_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, splitChar_apply]
  simp

/-- The characters separate the maximal ideals. -/
theorem splitChar_injective : Function.Injective (splitChar (K := K) (A := A)) := by
  intro I J h
  classical
  by_contra hne
  have hI := splitChar_primitiveIdempotent (K := K) (A := A) I I
  have hJ := splitChar_primitiveIdempotent (K := K) (A := A) J I
  rw [if_pos rfl] at hI
  rw [if_neg (fun hc => hne hc.symm)] at hJ
  rw [h, hJ] at hI
  exact zero_ne_one hI

/-- Every character is a `splitChar`: a character takes each primitive idempotent to `0` or
`1`, their images sum to `1`, orthogonality allows at most one `1` — and the weighted-sum
expansion then identifies the character with that coordinate's `splitChar`. No kernel argument
anywhere. -/
theorem splitChar_surjective : Function.Surjective (splitChar (K := K) (A := A)) := by
  intro φ
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hidem : ∀ J, φ (primitiveIdempotent K A J) = 0 ∨ φ (primitiveIdempotent K A J) = 1 :=
    fun J => IsIdempotentElem.iff_eq_zero_or_one.mp
      (((completeOrthogonalIdempotents_primitiveIdempotent (K := K) (A := A)).idem J).map φ)
  have hsum : ∑ J, φ (primitiveIdempotent K A J) = 1 := by
    rw [← map_sum,
      (completeOrthogonalIdempotents_primitiveIdempotent (K := K) (A := A)).complete, map_one]
  obtain ⟨J₀, hJ₀⟩ : ∃ J, φ (primitiveIdempotent K A J) = 1 := by
    by_contra hno
    simp only [not_exists] at hno
    rw [Finset.sum_congr rfl
      (fun J _ => (hidem J).resolve_right (hno J)), Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  refine ⟨J₀, ?_⟩
  ext a
  conv_rhs => rw [← sum_splitChar_smul_primitiveIdempotent (K := K) (A := A) a]
  rw [map_sum, Finset.sum_eq_single J₀]
  · rw [map_smul, smul_eq_mul, hJ₀, mul_one]
  · intro J _ hJ
    have h0 : φ (primitiveIdempotent K A J) = 0 := by
      rcases hidem J with h | h
      · exact h
      · have horth := congrArg φ
          ((completeOrthogonalIdempotents_primitiveIdempotent
            (K := K) (A := A)).toOrthogonalIdempotents.ortho hJ)
        rw [map_mul, h, hJ₀, one_mul, map_zero] at horth
        exact absurd horth one_ne_zero
    rw [map_smul, smul_eq_mul, h0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ J₀) h

variable (K A)

/-- **The maximal spectrum is the character set.** Mathlib does not state a bijection between
`MaximalSpectrum A` and `A →ₐ[K] K`. -/
noncomputable def equivAlgHom : MaximalSpectrum A ≃ (A →ₐ[K] K) :=
  Equiv.ofBijective (splitChar (K := K) (A := A)) ⟨splitChar_injective, splitChar_surjective⟩

variable {K A}

theorem equivAlgHom_apply (I : MaximalSpectrum A) : equivAlgHom K A I = splitChar K A I := rfl

/-- **The determination pigeonhole**: an injective family of characters, of the algebra's full
dimension, is the whole spectrum — an equivalence matching `splitChar`. No `Fintype` or
`DecidableEq` on the spectrum in the statement; both are manufactured inside. -/
theorem exists_equiv_splitChar_of_injective {ι : Type*} [Fintype ι] {φ : ι → (A →ₐ[K] K)}
    (hφ : Function.Injective φ) (hcard : Fintype.card ι = finrank K A) :
    ∃ σ : ι ≃ MaximalSpectrum A, ∀ i, φ i = splitChar K A (σ i) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  set f : ι → MaximalSpectrum A := fun i => (equivAlgHom K A).symm (φ i) with hf
  have hfinj : Function.Injective f := fun i j h =>
    hφ ((equivAlgHom K A).symm.injective h)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by
      rw [hcard, ← Nat.card_eq_fintype_card (α := MaximalSpectrum A),
        card_maximalSpectrum_eq_finrank K A]⟩
  refine ⟨Equiv.ofBijective f hbij, fun i => ?_⟩
  have : equivAlgHom K A (f i) = φ i := (equivAlgHom K A).apply_symm_apply (φ i)
  rw [← this]
  rfl

/-- **Uniqueness of the primitive decomposition**: a complete orthogonal family of nonzero
idempotents, of the same cardinality as the spectrum, IS the family of primitive idempotents up
to a bijection of indices.

The cardinality hypothesis is load-bearing: without `hcard`, `ι := Unit` with `e := 1` is a
complete orthogonal family of nonzero idempotents in any split algebra with several maximal ideals,
and no bijection exists. -/
theorem exists_equiv_primitiveIdempotent [Fintype (MaximalSpectrum A)]
    [DecidableEq (MaximalSpectrum A)] {ι : Type*} [Fintype ι] {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hcard : Fintype.card ι = Fintype.card (MaximalSpectrum A)) :
    ∃ σ : ι ≃ MaximalSpectrum A, ∀ i, e i = primitiveIdempotent K A (σ i) := by
  classical
  set F := splitAlgEquiv K A with hF
  set g : ι → MaximalSpectrum A → K := fun i => F (e i) with hg
  have hg01 : ∀ i I, g i I = 0 ∨ g i I = 1 := fun i I =>
    IsIdempotentElem.iff_eq_zero_or_one.mp
      (congrFun ((he.idem i).map (F : A ≃ₐ[K] (MaximalSpectrum A → K))) I)
  have hsum : ∀ I, ∑ i, g i I = 1 := by
    intro I
    have h1 : (∑ i, g i) = 1 := by
      simp only [hg, ← map_sum, he.complete, map_one]
    simpa using congrFun h1 I
  have hortho : ∀ {i j}, i ≠ j → ∀ I, g i I * g j I = 0 := by
    intro i j hij I
    have h0 := congrArg (fun x => F x I) (he.toOrthogonalIdempotents.ortho hij)
    simpa [hg] using h0
  have hexu : ∀ I, ∃ i, g i I = 1 ∧ ∀ j, g j I = 1 → j = i := by
    intro I
    obtain ⟨i, _, hi⟩ : ∃ i ∈ Finset.univ, g i I ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum I]; exact one_ne_zero)
    refine ⟨i, (hg01 i I).resolve_left hi, fun j hj => ?_⟩
    by_contra hji
    have h0 := hortho hji I
    rw [hj, (hg01 i I).resolve_left hi, one_mul] at h0
    exact one_ne_zero h0
  choose τ hτ1 hτu using hexu
  have hτsurj : Function.Surjective τ := by
    intro i
    have hgi : g i ≠ 0 := fun h0 => hne i (F.injective (by rw [map_zero]; exact h0))
    obtain ⟨I, hI⟩ : ∃ I, g i I ≠ 0 := by
      by_contra hno
      simp only [not_exists, not_not] at hno
      exact hgi (funext hno)
    exact ⟨I, (hτu I i ((hg01 i I).resolve_left hI)).symm⟩
  have hτbij : Function.Bijective τ :=
    (Fintype.bijective_iff_surjective_and_card τ).mpr ⟨hτsurj, hcard.symm⟩
  refine ⟨(Equiv.ofBijective τ hτbij).symm, fun i => ?_⟩
  apply F.injective
  have hFP : F (primitiveIdempotent K A ((Equiv.ofBijective τ hτbij).symm i))
      = Pi.single ((Equiv.ofBijective τ hτbij).symm i) 1 := by
    rw [hF, primitiveIdempotent, AlgEquiv.apply_symm_apply]
  rw [hFP]
  change g i = Pi.single ((Equiv.ofBijective τ hτbij).symm i) 1
  funext I
  have hτcoe : ∀ J, (Equiv.ofBijective τ hτbij) J = τ J := fun _ => rfl
  rcases eq_or_ne I ((Equiv.ofBijective τ hτbij).symm i) with h | h
  · have hti : τ I = i := by
      rw [h, ← hτcoe]
      exact (Equiv.ofBijective τ hτbij).apply_symm_apply i
    rw [h, Pi.single_eq_same, ← h, ← hti]
    exact hτ1 I
  · rw [Pi.single_eq_of_ne h]
    rcases hg01 i I with h0 | h1
    · exact h0
    · exfalso
      apply h
      rw [hτu I i h1, ← hτcoe]
      exact ((Equiv.ofBijective τ hτbij).symm_apply_apply I).symm

end Characters

/-! ## The hypotheses are forced, not chosen

Two of the hypotheses above are implied by the conclusion, so no weakening of them is possible. -/

/-- A split algebra is reduced: the hypothesis `IsReduced A` is forced. -/
theorem isReduced_of_splitEquiv (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (e : A ≃ₐ[K] (MaximalSpectrum A → K)) : IsReduced A :=
  isReduced_of_injective e.toRingEquiv.toRingHom e.injective

/-- A split algebra is finite: the hypothesis `Module.Finite K A` is forced. -/
theorem moduleFinite_of_splitEquiv (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Finite (MaximalSpectrum A)] (e : A ≃ₐ[K] (MaximalSpectrum A → K)) : Module.Finite K A :=
  Module.Finite.equiv e.symm.toLinearEquiv

end ECCLib

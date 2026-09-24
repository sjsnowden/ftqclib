/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.TranslationOrbital
import ECCLib.Matrix.SpectralDetermination

/-!
# The canonical spectrum of a translation scheme

The dual-orbit idempotents `orbProj` **are** the primitive idempotents of the scheme algebra:
a complete orthogonal family of nonzero idempotents of the spectrum's cardinality, identified
by the uniqueness theorem `exists_equiv_primitiveIdempotent`. The identification hands every
`P`-entry to the split characters (`splitChar_adj_eq_pEnt`): in the **canonical**
`MaximalSpectrum` index, the character value of an orbit adjacency is its classical `P`-entry
`pEnt`, representative-free across the dual orbit.

`Scheme/TranslationOrbital.lean` reached `orbProjBasis` by *recognition* (independence plus
cardinality), without the identification up to permutation; this module uses that
identification.

## Main definitions

* `translationSpectrumEquiv` — the dual orbits ≃ the maximal spectrum.

## Main results

* `orbProjSub_eq_primitiveIdempotent` — the identification.
* `splitChar_adj_eq_pEnt` — **the `P`-entries are the character values**, canonically indexed.

## Implementation notes

The results are stated on `↥(schemeAlgebra H V)` and its own `MaximalSpectrum`. The orbital
form (`eigenmatrixP` over `orbitalAlgebra ℂ ↥(permGroup H V) V`) is available by transporting
along `schemeAlgebra_eq_orbitalAlgebra`; it is deliberately not materialised here — the
character form IS the canonical content (`idemBasis_repr_eq_splitChar` is the general bridge),
and the transport would trade one `▸` for every statement.
-/

namespace ECCLib.Scheme

open Finset Matrix

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {H : Type*} [Group H] [Fintype H] [DistribMulAction H V]

instance translationCommutative : Subalgebra.IsCommutative (schemeAlgebra H V) :=
  ⟨fun a b => Subtype.ext (schemeAlgebra_mul_comm a.2 b.2)⟩

instance translationReduced : IsReduced ↥(schemeAlgebra H V) := by
  haveI : Subalgebra.IsCommutative
      (orbitalAlgebra ℂ ↥(permGroup H V) V) :=
    schemeAlgebra_eq_orbitalAlgebra (H := H) (V := V) ▸
      translationCommutative (H := H) (V := V)
  rw [schemeAlgebra_eq_orbitalAlgebra]
  exact isReduced_orbitalAlgebra

noncomputable instance translationSpecFintype :
    Fintype (MaximalSpectrum ↥(schemeAlgebra H V)) := by
  haveI : IsArtinianRing ↥(schemeAlgebra H V) := IsArtinianRing.of_finite ℂ _
  exact Fintype.ofFinite _

noncomputable instance translationSpecDecEq :
    DecidableEq (MaximalSpectrum ↥(schemeAlgebra H V)) :=
  Classical.decEq _

/-- The dual-orbit idempotents are **complete**: they sum to the identity in the scheme
algebra, lifting `sum_orbProj` to the subtype. -/
theorem completeOrthogonalIdempotents_orbProjSub :
    CompleteOrthogonalIdempotents (orbProjSub (H := H) (V := V)) := by
  refine ⟨orthogonalIdempotents_orbProjSub, ?_⟩
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum]
  rw [show (∑ S : ↥(orbits H (AddChar V ℂ)), ((orbProjSub (H := H) (V := V) S :
      ↥(schemeAlgebra H V)) : Matrix V V ℂ))
      = ∑ S : ↥(orbits H (AddChar V ℂ)), orbProj (S : Finset (AddChar V ℂ)) from rfl]
  rw [Finset.sum_coe_sort (orbits H (AddChar V ℂ)) (fun S => orbProj S)]
  rw [sum_orbProj]
  rfl

/-- The cardinality input for the identification: as many dual orbits as maximal ideals. -/
theorem card_orbits_dual_eq_card_maximalSpectrum :
    Fintype.card ↥(orbits H (AddChar V ℂ))
      = Fintype.card (MaximalSpectrum ↥(schemeAlgebra H V)) := by
  rw [card_orbits_dual_eq_finrank_schemeAlgebra,
    ← ECCLib.card_maximalSpectrum_eq_finrank ℂ ↥(schemeAlgebra H V),
    Nat.card_eq_fintype_card]

/-- **The identification**: the dual-orbit
idempotents are the primitive idempotents, up to a bijection of indices. -/
theorem exists_equiv_orbProjSub_eq_primitiveIdempotent :
    ∃ σ : ↥(orbits H (AddChar V ℂ)) ≃ MaximalSpectrum ↥(schemeAlgebra H V),
      ∀ S, orbProjSub (H := H) (V := V) S
        = ECCLib.primitiveIdempotent ℂ ↥(schemeAlgebra H V) (σ S) :=
  ECCLib.exists_equiv_primitiveIdempotent
    completeOrthogonalIdempotents_orbProjSub orbProjSub_ne_zero
    card_orbits_dual_eq_card_maximalSpectrum

/-- The spectrum equivalence of a translation scheme, as data. -/
noncomputable def translationSpectrumEquiv :
    ↥(orbits H (AddChar V ℂ)) ≃ MaximalSpectrum ↥(schemeAlgebra H V) :=
  (exists_equiv_orbProjSub_eq_primitiveIdempotent (H := H) (V := V)).choose

theorem orbProjSub_eq_primitiveIdempotent (S : ↥(orbits H (AddChar V ℂ))) :
    orbProjSub (H := H) (V := V) S
      = ECCLib.primitiveIdempotent ℂ ↥(schemeAlgebra H V)
          (translationSpectrumEquiv S) :=
  (exists_equiv_orbProjSub_eq_primitiveIdempotent (H := H) (V := V)).choose_spec S

/-- **The `P`-entries of a translation scheme are the split-character values, canonically
indexed**: at the spectral index of a dual orbit, the character of an orbit adjacency is the
classical `pEnt` at any member of that dual orbit. -/
theorem splitChar_adj_eq_pEnt {R : Finset V} (hR : R ∈ orbits H V)
    (S : ↥(orbits H (AddChar V ℂ))) {χ₀ : AddChar V ℂ}
    (hχ₀ : χ₀ ∈ (S : Finset (AddChar V ℂ))) :
    ECCLib.splitChar ℂ ↥(schemeAlgebra H V) (translationSpectrumEquiv S)
      ⟨adj R, adj_mem_schemeAlgebra hR⟩ = pEnt R χ₀ := by
  have h1 := ECCLib.mul_primitiveIdempotent (K := ℂ) (A := ↥(schemeAlgebra H V))
    (⟨adj R, adj_mem_schemeAlgebra hR⟩ : ↥(schemeAlgebra H V))
    (translationSpectrumEquiv S)
  rw [← orbProjSub_eq_primitiveIdempotent] at h1
  have h2 := congrArg (Subtype.val (p := fun M => M ∈ schemeAlgebra H V)) h1
  have h3 : adj R * orbProj (S : Finset (AddChar V ℂ))
      = ECCLib.splitChar ℂ ↥(schemeAlgebra H V) (translationSpectrumEquiv S)
          ⟨adj R, adj_mem_schemeAlgebra hR⟩ • orbProj (S : Finset (AddChar V ℂ)) := by
    simpa [orbProjSub] using h2
  have h4 := adj_mul_orbProj hR S.2 hχ₀
  have h5 : ECCLib.splitChar ℂ ↥(schemeAlgebra H V) (translationSpectrumEquiv S)
      ⟨adj R, adj_mem_schemeAlgebra hR⟩ • orbProj (S : Finset (AddChar V ℂ))
      = pEnt R χ₀ • orbProj (S : Finset (AddChar V ℂ)) := by
    rw [← h3, h4]
  have hne : orbProj (S : Finset (AddChar V ℂ)) ≠ 0 :=
    fun hz => orbProjSub_ne_zero S (Subtype.ext (by simpa [orbProjSub] using hz))
  obtain ⟨i, hi⟩ : ∃ p : V × V, orbProj (S : Finset (AddChar V ℂ)) p.1 p.2 ≠ 0 := by
    by_contra hno
    simp only [not_exists, not_not] at hno
    exact hne (Matrix.ext fun i j => hno (i, j))
  have hcell := congrFun (congrFun h5 i.1) i.2
  simp only [Matrix.smul_apply, smul_eq_mul] at hcell
  exact mul_right_cancel₀ hi hcell

/-- **The multiplicity at a dual orbit is its size**: the identification sends `orbProjSub` to
the primitive idempotent, whose trace is the multiplicity, and `orbProj` is a sum of
`card S` unit-trace projectors. -/
theorem spectralMult_translationSpectrumEquiv (S : ↥(orbits H (AddChar V ℂ))) :
    spectralMult (schemeAlgebra H V) (translationSpectrumEquiv S)
      = (S : Finset (AddChar V ℂ)).card := by
  have h1 : ((ECCLib.primitiveIdempotent ℂ ↥(schemeAlgebra H V)
        (translationSpectrumEquiv S) : ↥(schemeAlgebra H V)) : Matrix V V ℂ).trace
      = (spectralMult (schemeAlgebra H V) (translationSpectrumEquiv S) : ℂ) :=
    trace_coe_primitiveIdempotent _
  rw [← orbProjSub_eq_primitiveIdempotent] at h1
  rw [show ((orbProjSub (H := H) (V := V) S : ↥(schemeAlgebra H V)) : Matrix V V ℂ)
      = orbProj (S : Finset (AddChar V ℂ)) from rfl] at h1
  rw [show (orbProj (S : Finset (AddChar V ℂ))).trace
      = ((S : Finset (AddChar V ℂ)).card : ℂ) from by
    rw [orbProj, Matrix.trace_sum, Finset.sum_congr rfl fun χ _ => trace_charProj χ,
      Finset.sum_const, nsmul_eq_mul, mul_one]] at h1
  exact_mod_cast h1.symm

end ECCLib.Scheme

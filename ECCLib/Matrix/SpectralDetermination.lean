/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.CommutativeSubalgebra
import ECCLib.Matrix.CommonEigenvector
import ECCLib.SplitAlgebra
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Spectral determination for commutative matrix subalgebras

When does a family of common eigenvectors pin down the whole spectrum of a commutative reduced
matrix subalgebra over `ℂ`? Answer: when the eigenvalue functionals are pairwise distinct and
there are as many vectors as the algebra has dimensions
(`exists_equiv_splitChar_of_isCommonEigenvector`). This is the shared theorem both the
translation-scheme and the orbital-scheme carriers consume: the hypothesis mentions no group,
no orbit, no metric structure.

The module also carries the multiplicity layer: the rank of a primitive idempotent is its
trace (`trace_coe_primitiveIdempotent`), the ranks sum to the carrier
(`sum_spectralMult_eq_card`), and the trace system
(`sum_spectralMult_mul_splitChar_eq_trace`) that characterises the multiplicities once the
eigenmatrix is invertible.

## Main definitions

* `spectralMult` — the rank of a primitive idempotent, as a matrix.

## Main results

* `exists_equiv_splitChar_of_isCommonEigenvector` — **the determination theorem**.
* `trace_eq_finrank_range_of_isIdempotentElem` — rank of an idempotent matrix = its trace,
  over any field, with no `DecidableEq` on the index (the endomorphism form plus a six-line
  transfer supplies the matrix theorem, and the `Module.Free`/`Module.Finite` side instances
  fire automatically).
* `sum_spectralMult_eq_card`, `sum_spectralMult_mul_splitChar_eq_trace` — the multiplicity
  layer.

## Implementation notes

`[IsReduced ↥S]` is the hypothesis, not ⋆-closure: it is strictly weaker, and each consumer
already discharges it (`isReduced_orbitalAlgebra` for orbital algebras;
`isReduced_of_commute_of_conjTranspose_mem` for any permutation commutant).
`Module.Finite ℂ ↥S` is an instance found from finite-dimensionality of the ambient matrix
algebra and is never stated.
-/

namespace ECCLib.Scheme

open Matrix Module

/-! ## Rank of an idempotent matrix = its trace -/

/-- **Rank = trace for idempotent matrices**, over any field, with no `DecidableEq` on the
index type: the statement uses `mulVecLin`, which needs only `Fintype`. -/
theorem trace_eq_finrank_range_of_isIdempotentElem {K : Type*} [Field K] {X : Type*}
    [Fintype X] (E : Matrix X X K) (hE : IsIdempotentElem E) :
    E.trace = (finrank K (LinearMap.range E.mulVecLin) : K) := by
  classical
  have hidem : IsIdempotentElem (Matrix.toLin' E) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE.eq]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [Matrix.trace_toLin'_eq] at htr
  exact htr

section Determination

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {S : Subalgebra ℂ (Matrix X X ℂ)}
variable [Subalgebra.IsCommutative S] [IsReduced ↥S]

/-- **The determination theorem**: a family of common eigenvectors with pairwise-distinct
eigenvalue functionals, of cardinality the algebra's dimension, pins the whole spectrum — an
equivalence onto `MaximalSpectrum ↥S` under which each functional **is** the split character. -/
theorem exists_equiv_splitChar_of_isCommonEigenvector {ι : Type*} [Fintype ι]
    {v : ι → X → ℂ} {χ : ι → ↥S → ℂ} (hv : ∀ i, IsCommonEigenvector S (v i) (χ i))
    (hsep : Function.Injective χ) (hcard : Fintype.card ι = finrank ℂ ↥S) :
    ∃ σ : ι ≃ MaximalSpectrum ↥S, ∀ i, χ i = ⇑(ECCLib.splitChar ℂ ↥S (σ i)) := by
  have hφ : Function.Injective (fun i => (hv i).algHom) := fun i j h => by
    apply hsep
    have h2 : (hv i).algHom = (hv j).algHom := h
    rw [← (hv i).coe_algHom, ← (hv j).coe_algHom, h2]
  obtain ⟨σ, hσ⟩ := ECCLib.exists_equiv_splitChar_of_injective hφ hcard
  exact ⟨σ, fun i => by rw [← hσ i]; rfl⟩

end Determination

/-! ## The multiplicity layer -/

section Multiplicity

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {S : Subalgebra ℂ (Matrix X X ℂ)}
variable [Subalgebra.IsCommutative S] [IsReduced ↥S]
variable [Fintype (MaximalSpectrum ↥S)] [DecidableEq (MaximalSpectrum ↥S)]

variable (S) in
/-- The **spectral multiplicity** at a maximal ideal: the rank of its primitive idempotent,
as a matrix acting on `X → ℂ`. -/
noncomputable def spectralMult (I : MaximalSpectrum ↥S) : ℕ :=
  finrank ℂ (LinearMap.range
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).mulVecLin)

omit [Fintype (MaximalSpectrum ↥S)] in
/-- The coercion of a primitive idempotent is an idempotent matrix. -/
theorem isIdempotentElem_coe_primitiveIdempotent (I : MaximalSpectrum ↥S) :
    IsIdempotentElem ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ) :=
  (ECCLib.isIdempotentElem_primitiveIdempotent I).map (Subalgebra.val S)

omit [Fintype (MaximalSpectrum ↥S)] in
/-- **The multiplicity is the trace of the idempotent.** -/
theorem trace_coe_primitiveIdempotent (I : MaximalSpectrum ↥S) :
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).trace
      = (spectralMult S I : ℂ) :=
  trace_eq_finrank_range_of_isIdempotentElem _ (isIdempotentElem_coe_primitiveIdempotent I)

/-- **The multiplicities sum to the size of the carrier**: the idempotents sum to `1`, and the
identity matrix has trace `|X|`. -/
theorem sum_spectralMult_eq_card : ∑ I, spectralMult S I = Fintype.card X := by
  have hsum : ∑ I, ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ)
      = (1 : Matrix X X ℂ) := by
    rw [← AddSubmonoidClass.coe_finset_sum,
      ECCLib.completeOrthogonalIdempotents_primitiveIdempotent.complete,
      OneMemClass.coe_one]
  have htr := congrArg Matrix.trace hsum
  rw [Matrix.trace_sum, Matrix.trace_one] at htr
  have hcast : ∑ I, (spectralMult S I : ℂ) = (Fintype.card X : ℂ) := by
    rw [← htr]
    exact Finset.sum_congr rfl fun I _ => (trace_coe_primitiveIdempotent I).symm
  exact_mod_cast hcast

omit [Fintype (MaximalSpectrum ↥S)] in
/-- Coercions of distinct primitive idempotents multiply to zero. -/
theorem coe_primitiveIdempotent_mul_coe {I J : MaximalSpectrum ↥S} (hIJ : I ≠ J) :
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ)
        * ((ECCLib.primitiveIdempotent ℂ ↥S J : ↥S) : Matrix X X ℂ) = 0 := by
  haveI : IsArtinianRing ↥S := IsArtinianRing.of_finite ℂ _
  haveI : Fintype (MaximalSpectrum ↥S) := Fintype.ofFinite _
  have h := (ECCLib.completeOrthogonalIdempotents_primitiveIdempotent
    (K := ℂ) (A := ↥S)).ortho hIJ
  have h2 := congrArg (Subtype.val (p := fun M => M ∈ S)) h
  simpa using h2

/-- **The rank of any member of the algebra is the sum of the multiplicities over the support
of its character vector.** The member is its character expansion; cutting to the support
idempotent changes nothing, and the support idempotent's rank is its trace. -/
theorem rank_coe_eq_sum_spectralMult (M : ↥S) :
    Matrix.rank ((M : ↥S) : Matrix X X ℂ)
      = ∑ I ∈ Finset.univ.filter
          (fun I => ECCLib.splitChar ℂ ↥S I M ≠ 0), spectralMult S I := by
  classical
  set c : MaximalSpectrum ↥S → ℂ := fun I => ECCLib.splitChar ℂ ↥S I M with hc
  set E : MaximalSpectrum ↥S → Matrix X X ℂ :=
    fun I => ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ) with hE
  set supp : Finset (MaximalSpectrum ↥S) := Finset.univ.filter (fun I => c I ≠ 0) with hsupp
  have hEE : ∀ I J, E I * E J = if I = J then E I else 0 := by
    intro I J
    rcases eq_or_ne I J with rfl | hIJ
    · rw [if_pos rfl]
      exact (isIdempotentElem_coe_primitiveIdempotent I).eq
    · rw [if_neg hIJ]
      exact coe_primitiveIdempotent_mul_coe hIJ
  have hM : ((M : ↥S) : Matrix X X ℂ) = ∑ I, c I • E I := by
    conv_lhs => rw [← ECCLib.sum_splitChar_smul_primitiveIdempotent (K := ℂ) (A := ↥S) M]
    rw [AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun I _ => rfl
  set F : Matrix X X ℂ := ∑ I ∈ supp, E I with hF
  set T : Matrix X X ℂ := ∑ I ∈ supp, (c I)⁻¹ • E I with hT
  have hFidem : IsIdempotentElem F := by
    unfold IsIdempotentElem
    rw [hF, Finset.sum_mul_sum]
    rw [show ∑ I ∈ supp, ∑ J ∈ supp, E I * E J
        = ∑ I ∈ supp, ∑ J ∈ supp, if I = J then E I else 0 from
      Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => hEE I J]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Finset.sum_ite_eq supp I fun _ => E I, if_pos hI]
  have hME : ∀ J, ((M : ↥S) : Matrix X X ℂ) * E J = c J • E J := by
    intro J
    have h := ECCLib.mul_primitiveIdempotent (K := ℂ) (A := ↥S) M J
    calc ((M : ↥S) : Matrix X X ℂ) * E J
        = ((M * ECCLib.primitiveIdempotent ℂ ↥S J : ↥S) : Matrix X X ℂ) := rfl
      _ = ((ECCLib.splitChar ℂ ↥S J M
            • ECCLib.primitiveIdempotent ℂ ↥S J : ↥S) : Matrix X X ℂ) := by rw [h]
      _ = c J • E J := rfl
  have hMT : ((M : ↥S) : Matrix X X ℂ) * T = F := by
    rw [hT, Finset.mul_sum, hF]
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [Matrix.mul_smul, hME J, smul_smul,
      inv_mul_cancel₀ (Finset.mem_filter.mp hJ).2, one_smul]
  have hMF : ((M : ↥S) : Matrix X X ℂ) * F = ((M : ↥S) : Matrix X X ℂ) := by
    rw [hF, Finset.mul_sum]
    rw [show ∑ J ∈ supp, ((M : ↥S) : Matrix X X ℂ) * E J = ∑ J ∈ supp, c J • E J from
      Finset.sum_congr rfl fun J _ => hME J]
    conv_rhs => rw [hM]
    exact Finset.sum_subset (Finset.filter_subset _ _) fun I _ hI => by
      have hcI : c I = 0 := by
        by_contra hne
        exact hI (Finset.mem_filter.mpr ⟨Finset.mem_univ I, hne⟩)
      rw [hcI, zero_smul]
  have hrank : Matrix.rank ((M : ↥S) : Matrix X X ℂ) = Matrix.rank F := by
    apply le_antisymm
    · calc Matrix.rank ((M : ↥S) : Matrix X X ℂ)
          = Matrix.rank (((M : ↥S) : Matrix X X ℂ) * F) := by rw [hMF]
        _ ≤ Matrix.rank F := Matrix.rank_mul_le_right _ _
    · calc Matrix.rank F = Matrix.rank (((M : ↥S) : Matrix X X ℂ) * T) := by rw [hMT]
        _ ≤ Matrix.rank ((M : ↥S) : Matrix X X ℂ) := Matrix.rank_mul_le_left _ _
  have htr : Matrix.trace F = (Matrix.rank F : ℂ) :=
    trace_eq_finrank_range_of_isIdempotentElem F hFidem
  have htrF : Matrix.trace F = ∑ I ∈ supp, (spectralMult S I : ℂ) := by
    rw [hF, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun I _ => trace_coe_primitiveIdempotent I
  have hfin : ((Matrix.rank ((M : ↥S) : Matrix X X ℂ) : ℕ) : ℂ)
      = ∑ I ∈ supp, (spectralMult S I : ℂ) := by
    rw [hrank, ← htr, htrF]
  exact_mod_cast hfin

/-- **The trace system**: pairing the multiplicities against the characters recovers the trace
of any member of the algebra. Since `P` is invertible, this characterises the multiplicities —
the closed forms at each carrier are instances of this one identity. -/
theorem sum_spectralMult_mul_splitChar_eq_trace (M : ↥S) :
    ∑ I, (spectralMult S I : ℂ) * ECCLib.splitChar ℂ ↥S I M
      = ((M : ↥S) : Matrix X X ℂ).trace := by
  conv_rhs => rw [← ECCLib.sum_splitChar_smul_primitiveIdempotent (K := ℂ) (A := ↥S) M]
  rw [AddSubmonoidClass.coe_finset_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Subalgebra.coe_smul, Matrix.trace_smul, trace_coe_primitiveIdempotent, smul_eq_mul,
    mul_comm]

/-- **The product-trace row**: the multiplicities against a product of character values
recover the trace of the product — `splitChar` is an algebra map, so this is the trace
system read at `a * b`. The two-ways trace computation behind every orthogonality relation
downstream. -/
theorem sum_spectralMult_mul_splitChar_mul_splitChar (a b : ↥S) :
    ∑ I, (spectralMult S I : ℂ)
        * (ECCLib.splitChar ℂ ↥S I a * ECCLib.splitChar ℂ ↥S I b)
      = (((a * b : ↥S) : Matrix X X ℂ)).trace := by
  rw [← sum_spectralMult_mul_splitChar_eq_trace]
  exact Finset.sum_congr rfl fun I _ => by rw [map_mul]

end Multiplicity

end ECCLib.Scheme

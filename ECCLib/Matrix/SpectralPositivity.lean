/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.SpectralDetermination
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Positivity of the primitive idempotents

In a commutative reduced `⋆`-closed matrix algebra the primitive idempotents are **Hermitian**,
hence **positive semidefinite** — they are the orthogonal projections onto the common
eigenspaces, which is what turns the spectral decomposition into inequalities.

The Hermitian statement is where the work is, and the route is a trace argument over the
existing spectral toolkit: `Eᴴ` lies in the algebra (`⋆`-closure), is idempotent, so its
character values are `0` or `1`; the Frobenius nonvanishing `trace(E·Eᴴ) ≠ 0` forces the
character at `E`'s own maximal ideal to be `1`; and `trace(Eᴴ) = conj(trace E)` — the
multiplicity again — pins every other value to `0`, because every multiplicity is
positive. The expansion over the idempotents then reads `Eᴴ = E`, and positive
semidefiniteness follows as `E = Eᴴ·E`.

## Main results

* `spectralMult_ne_zero` — every multiplicity is positive.
* `conjTranspose_coe_primitiveIdempotent` — **the idempotents are Hermitian** under
  `⋆`-closure of the algebra.
* `posSemidef_coe_primitiveIdempotent` — hence positive semidefinite.

The counterexample in the check module shows the `⋆`-closure hypothesis is load-bearing:
idempotency alone never gives Hermitian (`!![1,1;0,0]`).
-/

namespace ECCLib.Scheme

open Matrix Module
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {S : Subalgebra ℂ (Matrix X X ℂ)}
variable [Subalgebra.IsCommutative S] [IsReduced ↥S]
variable [Fintype (MaximalSpectrum ↥S)] [DecidableEq (MaximalSpectrum ↥S)]

omit [Fintype (MaximalSpectrum ↥S)] in
/-- The coercion of a primitive idempotent is nonzero. -/
theorem coe_primitiveIdempotent_ne_zero (I : MaximalSpectrum ↥S) :
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ) ≠ 0 := by
  intro h
  exact ECCLib.primitiveIdempotent_ne_zero I (Subtype.ext (by simpa using h))

omit [Fintype (MaximalSpectrum ↥S)] in
/-- **Every spectral multiplicity is positive**: the multiplicity is the rank of the
primitive idempotent, and the idempotent is nonzero. -/
theorem spectralMult_ne_zero (I : MaximalSpectrum ↥S) : spectralMult S I ≠ 0 := by
  intro h
  refine coe_primitiveIdempotent_ne_zero I ?_
  have h' : Module.finrank ℂ (LinearMap.range
      ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).mulVecLin) = 0 := h
  have hlin : ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).mulVecLin
      = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h')
  ext i j
  have h1 : ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).mulVec
      (Pi.single j 1) = 0 := by
    rw [← Matrix.mulVecLin_apply, hlin]
    rfl
  have h2 := congrFun h1 i
  rwa [Matrix.mulVec_single_one] at h2

omit [Fintype (MaximalSpectrum ↥S)] in
/-- **The primitive idempotents of a `⋆`-closed algebra are Hermitian.** The trace route:
`Eᴴ` is an idempotent member of the algebra, so its character values are `0`/`1`; the
Frobenius nonvanishing `trace(E·Eᴴ) ≠ 0` forces the value `1` at `E`'s own ideal, and
`trace(Eᴴ) = conj(trace E)` with positive multiplicities forces `0` everywhere else. -/
theorem conjTranspose_coe_primitiveIdempotent
    (hstar : ∀ M ∈ S, Mᴴ ∈ S) (I : MaximalSpectrum ↥S) :
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ)ᴴ
      = ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ) := by
  classical
  haveI : IsArtinianRing ↥S := IsArtinianRing.of_finite ℂ _
  haveI : Fintype (MaximalSpectrum ↥S) := Fintype.ofFinite _
  set E : ↥S := ECCLib.primitiveIdempotent ℂ ↥S I with hEdef
  set Eh : ↥S := ⟨((E : ↥S) : Matrix X X ℂ)ᴴ, hstar _ (E : ↥S).2⟩ with hEhdef
  set c : MaximalSpectrum ↥S → ℂ := fun J => ECCLib.splitChar ℂ ↥S J Eh with hcdef
  have hidem : Eh * Eh = Eh := by
    apply Subtype.ext
    change ((E : ↥S) : Matrix X X ℂ)ᴴ * ((E : ↥S) : Matrix X X ℂ)ᴴ
        = ((E : ↥S) : Matrix X X ℂ)ᴴ
    rw [← Matrix.conjTranspose_mul, (isIdempotentElem_coe_primitiveIdempotent I).eq]
  have hc01 : ∀ J, c J = 0 ∨ c J = 1 := by
    intro J
    have hsq : c J * c J = c J := by
      rw [hcdef]
      dsimp only
      rw [← map_mul, hidem]
    by_cases ha : c J = 0
    · exact Or.inl ha
    · exact Or.inr (mul_left_cancel₀ ha (hsq.trans (mul_one (c J)).symm))
  have htrace_sys : ((E * Eh : ↥S) : Matrix X X ℂ).trace
      = (spectralMult S I : ℂ) * c I := by
    rw [← sum_spectralMult_mul_splitChar_eq_trace (E * Eh)]
    rw [Finset.sum_eq_single I (fun J _ hJ => ?_)
      (fun h => absurd (Finset.mem_univ I) h)]
    · rw [map_mul, hEdef, ECCLib.splitChar_primitiveIdempotent, if_pos rfl,
        one_mul]
    · rw [map_mul, hEdef, ECCLib.splitChar_primitiveIdempotent, if_neg hJ,
        zero_mul, mul_zero]
  have hfrob : ((E * Eh : ↥S) : Matrix X X ℂ).trace ≠ 0 := by
    rw [show ((E * Eh : ↥S) : Matrix X X ℂ)
        = ((E : ↥S) : Matrix X X ℂ) * ((E : ↥S) : Matrix X X ℂ)ᴴ from rfl,
      Ne, Matrix.trace_mul_conjTranspose_self_eq_zero_iff]
    exact coe_primitiveIdempotent_ne_zero I
  have hcI : c I = 1 := by
    rcases hc01 I with h0 | h1
    · exact absurd (by rw [htrace_sys, h0, mul_zero]) hfrob
    · exact h1
  have htrEh : ∑ J, (spectralMult S J : ℂ) * c J = (spectralMult S I : ℂ) := by
    have h1 := sum_spectralMult_mul_splitChar_eq_trace Eh
    rw [show ((Eh : ↥S) : Matrix X X ℂ) = ((E : ↥S) : Matrix X X ℂ)ᴴ from rfl,
      Matrix.trace_conjTranspose, trace_coe_primitiveIdempotent, star_natCast] at h1
    exact h1
  have hzero : ∀ J, J ≠ I → c J = 0 := by
    have hsplit : ∑ J ∈ Finset.univ.erase I, (spectralMult S J : ℂ) * c J = 0 := by
      have h2 := htrEh
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ I), hcI, mul_one] at h2
      exact left_eq_add.mp h2.symm
    have hnat : ∑ J ∈ (Finset.univ.erase I).filter (fun J => c J = 1),
        spectralMult S J = 0 := by
      have hC : ((∑ J ∈ (Finset.univ.erase I).filter (fun J => c J = 1),
          spectralMult S J : ℕ) : ℂ)
          = ∑ J ∈ Finset.univ.erase I, (spectralMult S J : ℂ) * c J := by
        push_cast
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun J _ => ?_
        rcases hc01 J with h0 | h1
        · rw [h0, if_neg (show ¬((0 : ℂ) = 1) by norm_num), mul_zero]
        · rw [h1, if_pos rfl, mul_one]
      rw [hsplit] at hC
      exact_mod_cast hC
    intro J hJ
    rcases hc01 J with h0 | h1
    · exact h0
    · exact absurd (Finset.sum_eq_zero_iff.mp hnat J
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hJ, Finset.mem_univ J⟩, h1⟩))
        (spectralMult_ne_zero J)
  have hEh_eq : Eh = E := by
    have hexp := ECCLib.sum_splitChar_smul_primitiveIdempotent (K := ℂ)
      (A := ↥S) Eh
    rw [← hexp, Finset.sum_eq_single I (fun J _ hJ => by rw [show ECCLib.splitChar
        ℂ ↥S J Eh = c J from rfl, hzero J hJ, zero_smul])
      (fun h => absurd (Finset.mem_univ I) h)]
    rw [show ECCLib.splitChar ℂ ↥S I Eh = c I from rfl, hcI, one_smul, hEdef]
  exact congrArg (fun M : ↥S => (M : Matrix X X ℂ)) hEh_eq

omit [Fintype (MaximalSpectrum ↥S)] in
/-- The Hermitian reading, in Mathlib's vocabulary. -/
theorem isHermitian_coe_primitiveIdempotent
    (hstar : ∀ M ∈ S, Mᴴ ∈ S) (I : MaximalSpectrum ↥S) :
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).IsHermitian :=
  conjTranspose_coe_primitiveIdempotent hstar I

omit [Fintype (MaximalSpectrum ↥S)] in
/-- **The primitive idempotents of a `⋆`-closed algebra are positive semidefinite**:
Hermitian idempotents factor as `E = Eᴴ·E`. -/
theorem posSemidef_coe_primitiveIdempotent
    (hstar : ∀ M ∈ S, Mᴴ ∈ S) (I : MaximalSpectrum ↥S) :
    ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ).PosSemidef := by
  have h : ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ)
      = ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ)ᴴ
        * ((ECCLib.primitiveIdempotent ℂ ↥S I : ↥S) : Matrix X X ℂ) := by
    rw [conjTranspose_coe_primitiveIdempotent hstar I,
      (isIdempotentElem_coe_primitiveIdempotent I).eq]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end ECCLib.Scheme

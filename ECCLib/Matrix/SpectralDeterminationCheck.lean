/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.SpectralDetermination
import ECCLib.Scheme.Spectrum

/-!
# Checks for `ECCLib/Matrix/SpectralDetermination.lean`

Axiom sweeps, and the **Hamming vacuity row**: a check that the shared layer really is
carrier-agnostic, at the translation-scheme carrier. A character of
the translation-scheme carrier is a common eigenvector of the **whole** scheme algebra —
every member, not just the adjacencies — with no hypothesis beyond the carrier's own
instances, and its functional is therefore an algebra character of the scheme algebra through
the general `algHom`.

**What the row does NOT show**: the full determination at Hamming (the separating family, the
cardinality, and the `kraw` identification). This row pins only that the shared layer's
hypothesis is dischargeable by the translation-scheme carrier's existing supply
(`circulant_mulVec_char`), which is the vacuity check: a shared theorem only the orbital
carrier can use is not a shared theorem.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.trace_eq_finrank_range_of_isIdempotentElem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.trace_eq_finrank_range_of_isIdempotentElem

/-- info: 'ECCLib.Scheme.exists_equiv_splitChar_of_isCommonEigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.exists_equiv_splitChar_of_isCommonEigenvector

/-- info: 'ECCLib.Scheme.spectralMult' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.spectralMult

/-- info: 'ECCLib.Scheme.isIdempotentElem_coe_primitiveIdempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isIdempotentElem_coe_primitiveIdempotent

/-- info: 'ECCLib.Scheme.trace_coe_primitiveIdempotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.trace_coe_primitiveIdempotent

/-- info: 'ECCLib.Scheme.sum_spectralMult_eq_card' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_spectralMult_eq_card

/-- info: 'ECCLib.Scheme.sum_spectralMult_mul_splitChar_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_spectralMult_mul_splitChar_eq_trace

/-! ## The Hamming vacuity row -/

section HammingVacuity

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {H : Type*} [Group H] [DistribMulAction H V]

/-- **A character of the carrier is a common eigenvector of the whole scheme algebra.** Every
member of `schemeAlgebra H V` is a circulant, and `circulant_mulVec_char` already proves every
character is an eigenvector of every circulant; the functional reads the eigenvalue off at
`0`, where every character takes the value `1`. -/
theorem isCommonEigenvector_char (χ : AddChar V ℂ) :
    IsCommonEigenvector (schemeAlgebra H V) ⇑χ
      (fun M => ((M : Matrix V V ℂ) *ᵥ ⇑χ) 0) where
  ne_zero h := by
    have h0 := congrFun h 0
    simp only [AddChar.map_zero_eq_one, Pi.zero_apply] at h0
    exact one_ne_zero h0
  mulVec_eq M := by
    obtain ⟨k, -, hk⟩ := (mem_schemeAlgebra_iff_circulant (M : Matrix V V ℂ)).mp M.2
    rw [hk, circulant_mulVec_char]
    congr 1
    simp [AddChar.map_zero_eq_one]

/-- ...and its functional is an algebra character of the scheme algebra, through the general
layer with nothing supplied but the carrier's own instances. -/
noncomputable example (χ : AddChar V ℂ) : ↥(schemeAlgebra H V) →ₐ[ℂ] ℂ :=
  (isCommonEigenvector_char (H := H) χ).algHom

end HammingVacuity

/-- info: 'ECCLib.Scheme.isCommonEigenvector_char' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCommonEigenvector_char

end ECCLib.Scheme

/-- info: 'ECCLib.Scheme.coe_primitiveIdempotent_mul_coe' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coe_primitiveIdempotent_mul_coe

/-- info: 'ECCLib.Scheme.rank_coe_eq_sum_spectralMult' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.rank_coe_eq_sum_spectralMult

/-- info: 'ECCLib.Scheme.sum_spectralMult_mul_splitChar_mul_splitChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_spectralMult_mul_splitChar_mul_splitChar

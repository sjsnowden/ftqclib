/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Spectrum
import ECCLib.FiniteFourier

/-!
# The bridge to the library's Fourier transform

The scheme layer is plain-sum with the conjugate on the `P` side; the library's
`ECCLib.fourierT f ξ = 𝔼_x f x · conj(ξ x)` is 𝔼-normalised. One lemma relates
them (`eig_eq_card_mul_fourierT`, no sign), and the transform intertwines the
contragredient action (`fourierT_smul_smul`). This is the ONLY scheme module importing
`FiniteFourier`, so that the core scheme layer does not inherit the Gowers-norm imports.
-/

namespace ECCLib.Scheme

open Finset
open scoped BigOperators ComplexConjugate

variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- **Normalisation bridge**: the scheme eigenvalue is `|V|` times the library's
𝔼-normalised transform — no conjugate, no sign. -/
theorem eig_eq_card_mul_fourierT (k : V → ℂ) (χ : AddChar V ℂ) :
    eig k χ = (Fintype.card V : ℂ) * ECCLib.fourierT k χ := by
  have hN : (Fintype.card V : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eig, ECCLib.fourierT, Fintype.expect_eq_sum_div_card]
  field_simp

/-- **Fourier equivariance**: the transform intertwines the contragredient action. -/
theorem fourierT_smul_smul {H : Type*} [Group H] [DistribMulAction H V] (h : H)
    (f : V → ℂ) (ξ : AddChar V ℂ) :
    ECCLib.fourierT (fun x => f (h⁻¹ • x)) (h • ξ) = ECCLib.fourierT f ξ := by
  unfold ECCLib.fourierT
  refine (Fintype.expect_equiv (MulAction.toPerm h) _ _ ?_).symm
  intro y
  simp [MulAction.toPerm, contra_smul_apply]

end ECCLib.Scheme

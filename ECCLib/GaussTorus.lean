/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.MonomialWeil
import ECCLib.GaussSum

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The Gauss sum as the change of basis between eigenbases

The translation side of the Heisenberg group is diagonalized by *additive* characters
(`pairingChar`); the torus inside the monomial group is diagonalized by *multiplicative* characters.
This file states the transition between the two eigenbases and identifies its coefficient:

* `mulVec χ` — the torus eigenvectors: products `y ↦ ∏ᵢ χᵢ(yᵢ)` of multiplicative characters
  (Mathlib's `MulChar` is already extended by zero, so no support bookkeeping);
* `dilOp_mulVec` — they *are* eigenvectors of the dilation operators, unconditionally;
* `gauss_transition` / **`fourierOp_mulVec`** — the DFT of a torus eigenvector is the **Gauss sum**
  times the dual eigenvector: `𝓕(mulVec χ) = (∏ᵢ g(χᵢ,ψ)) · mulVec χ⁻¹`. The Gauss sum is exactly
  the matrix coefficient of the DFT between the multiplicative and additive eigenbases — the
  conceptual reason it appears in every weight formula for codes with monomial symmetry (the
  McEliece mechanism; this file does not treat the cyclic-code application or McEliece's
  theorem itself);
* `fourierOp_mulVec_quadChar` — at the quadratic character the coefficient is `(quadGaussSum ψ)^n`
  and the dual character is itself: **the quadratic torus eigenvector is an eigenvector of the DFT
  with eigenvalue `Tr(𝓕)`** — the Gauss sum, the trace of the DFT, and the torus in one statement.
-/

namespace ECCLib.Coding

open ECCLib.Heisenberg

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Torus eigenvectors -/

/-- The torus eigenvector attached to a family of multiplicative characters:
`y ↦ ∏ᵢ χᵢ(yᵢ)`. `MulChar` is zero on nonunits, so this is already the extended object. -/
noncomputable def mulVec (χ : ι → MulChar F ℂ) : (ι → F) → ℂ := fun y => ∏ i, χ i (y i)

/-- **`mulVec χ` is an eigenvector of every dilation operator** — unconditionally, `MulChar` being
multiplicative on all of `F`. -/
theorem dilOp_mulVec (d : ι → F) (χ : ι → MulChar F ℂ) :
    dilOp d (mulVec χ) = (∏ i, χ i ((d i)⁻¹)) • mulVec χ := by
  funext y
  simp only [dilOp_apply, Pi.smul_apply, smul_eq_mul]
  change ∏ i, χ i ((d i)⁻¹ * y i) = (∏ i, χ i ((d i)⁻¹)) * ∏ i, χ i (y i)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => map_mul (χ i) _ _

/-! ## The transition coefficient -/

/-- **The one-dimensional transition**: `Σ_t χ(t)ψ(st) = χ⁻¹(s)·g(χ,ψ)`. At `s = 0` both sides
vanish (`χ ≠ 1` orthogonality on the left, `χ⁻¹(0) = 0` on the right); at `s ≠ 0` it is Mathlib's
`gaussSum_mulShift` with the unit `χ⁻¹(s)·χ(s) = 1` in place of division. -/
lemma gauss_transition {χ : MulChar F ℂ} (hχ : χ ≠ 1) (ψ : AddChar F ℂ) (s : F) :
    ∑ t : F, χ t * ψ (s * t) = χ⁻¹ s * gaussSum χ ψ := by
  by_cases hs : s = 0
  · subst hs
    rw [Finset.sum_congr rfl fun t _ => by rw [zero_mul, AddChar.map_zero_eq_one, mul_one]]
    rw [MulChar.sum_eq_zero_of_ne_one hχ, MulChar.map_nonunit χ⁻¹ not_isUnit_zero, zero_mul]
  · have hms := gaussSum_mulShift χ ψ (Units.mk0 s hs)
    rw [show ((Units.mk0 s hs : Fˣ) : F) = s from rfl] at hms
    have hgs : gaussSum χ (AddChar.mulShift ψ s) = ∑ t : F, χ t * ψ (s * t) := by
      unfold gaussSum
      exact Finset.sum_congr rfl fun t _ => by rw [AddChar.mulShift_apply]
    rw [hgs] at hms
    have hone : χ⁻¹ s * χ s = 1 := by
      rw [MulChar.inv_apply', ← map_mul, inv_mul_cancel₀ hs, map_one]
    calc ∑ t : F, χ t * ψ (s * t)
        = (χ⁻¹ s * χ s) * ∑ t : F, χ t * ψ (s * t) := by rw [hone, one_mul]
      _ = χ⁻¹ s * (χ s * ∑ t : F, χ t * ψ (s * t)) := by ring
      _ = χ⁻¹ s * gaussSum χ ψ := by rw [hms]

/-- **The transition theorem**: the DFT of a torus eigenvector is the product of
Gauss sums times the *dual* eigenvector — `𝓕(mulVec χ) = (∏ᵢ g(χᵢ,ψ)) · mulVec χ⁻¹`. The Gauss sum
is the change-of-basis coefficient between the monomial (multiplicative) eigenbasis and the
translation (additive) eigenbasis. -/
theorem fourierOp_mulVec {ψ : AddChar F ℂ} (χ : ι → MulChar F ℂ) (hχ : ∀ i, χ i ≠ 1) :
    fourierOp ψ (mulVec χ)
      = (∏ i, gaussSum (χ i) ψ) • mulVec (fun i => (χ i)⁻¹) := by
  funext y
  rw [fourierOp_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hfac : ∀ x : ι → F, ψ (pairing y x) * mulVec χ x
      = ∏ i, (χ i (x i) * ψ (y i * x i)) := by
    intro x
    unfold mulVec pairing
    rw [addChar_map_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun x _ => hfac x, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset F)
      (fun (i : ι) (t : F) => χ i t * ψ (y i * t))]
  rw [Finset.prod_congr rfl fun i _ => gauss_transition (hχ i) ψ (y i),
    Finset.prod_mul_distrib]
  change (∏ i, (χ i)⁻¹ (y i)) * ∏ i, gaussSum (χ i) ψ
      = (∏ i, gaussSum (χ i) ψ) * ∏ i, (χ i)⁻¹ (y i)
  ring

/-! ## The quadratic eigenvector: Gauss sum, DFT trace and torus in one statement -/

section Quadratic

variable [DecidableEq F]

/-- **The quadratic torus eigenvector is an eigenvector of the DFT itself**, with eigenvalue
`(quadGaussSum ψ)^{|ι|} = Tr(𝓕)`: the quadratic character is self-dual (`χ₂⁻¹ = χ₂`), so the
transition theorem closes into an eigenvalue equation, and its coefficient is exactly the Gauss
sum to the power identified as the trace of the DFT
(`trace_fourierOp_eq_quadGaussSum_pow`). -/
theorem fourierOp_mulVec_quadChar (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) :
    fourierOp ψ (mulVec (fun _ : ι => quadCharC F))
      = ((ECCLib.quadGaussSum ψ) ^ Fintype.card ι) •
          mulVec (fun _ : ι => quadCharC F) := by
  rw [fourierOp_mulVec (fun _ => quadCharC F) (fun _ => quadCharC_ne_one hF)]
  rw [Finset.prod_const, Finset.card_univ, ← quadGaussSum_eq_gaussSum hF hψ]
  congr 1
  funext i
  rw [MulChar.IsQuadratic.inv quadCharC_isQuadratic]

end Quadratic

end ECCLib.Coding

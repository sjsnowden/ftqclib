/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GaussSumFq

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Computational witnesses for the Gauss sums

Small-parameter checks at `p = 3`, each in **two routes proving the same statement**: an
*independent* route (direct finite expansion + elementary complex arithmetic, never invoking the
general theorem) and an instance of the general theorem. The agreement of the two routes is the
witness — it is what would fail under a sign, convention, or off-by-one error in the definitions.

The concrete character is **exactly the object of the general theorems**: `AddChar.zmodChar 3` on
`stdRoot 3 = exp(2πi/3)`. A fresh character would check nothing.

Witnesses covered: the definite sign `g = i√3` at `p = 3`; `‖g‖² = 3`; the value law
`g(2) = χ₂(2)·g = −g`, whose independent side is *exactly* the cyclotomic relation `1+ω+ω² = 0`;
the `𝔽₉` instance (general theorem + arithmetic only; see its docstring for the scope);
`(i√3)² = −3`, the number Davenport–Hasse's square produces at `p = 3, m = 2`.
-/

namespace ECCLib.Witness

open ECCLib ECCLib.GaussSign

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The concrete additive character at `p = 3` — the object of the general theorems. -/
noncomputable def ψ₃ : AddChar (ZMod 3) ℂ :=
  AddChar.zmodChar 3 ((stdRoot_isPrimitiveRoot (p := 3) (by norm_num)).pow_eq_one)

/-- `ω = exp(2πi/3)`. -/
noncomputable def ω : ℂ := stdRoot 3

/-! ## The ω-toolkit -/

theorem ω_pow_three : ω ^ 3 = 1 :=
  (stdRoot_isPrimitiveRoot (p := 3) (by norm_num)).pow_eq_one

theorem ω_ne_one : ω ≠ 1 :=
  (stdRoot_isPrimitiveRoot (p := 3) (by norm_num)).ne_one (by norm_num)

/-- The cyclotomic relation `1 + ω + ω² = 0` — the engine of every `p = 3` witness. -/
theorem omega_cubic : 1 + ω + ω ^ 2 = 0 := by
  have hfac : (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 := by ring
  have h0 : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by rw [hfac, ω_pow_three, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) ω_ne_one
  · exact h

theorem ψ₃_apply (a : ZMod 3) : ψ₃ a = ω ^ a.val := by
  unfold ψ₃ ω
  rw [AddChar.zmodChar_apply]

/-! ## The definite sign at `p = 3` -/

/-- **Independent step (i)**: the direct three-term expansion `Σψ(x²) = 1 + 2ω`. No general
theorem. -/
theorem quadGaussSum_three_expand : quadGaussSum ψ₃ = 1 + 2 * ω := by
  unfold quadGaussSum
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show ((0 : ZMod 3) ^ 2) = 0 from by decide, show ((1 : ZMod 3) ^ 2) = 1 from by decide,
    show ((2 : ZMod 3) ^ 2) = 1 from by decide]
  rw [AddChar.map_zero_eq_one, ψ₃_apply 1, show (1 : ZMod 3).val = 1 from rfl, pow_one]
  ring

/-- **Independent step (ii)**: `1 + 2·exp(2πi/3) = i·√3`, by Euler's formula and the known
values of `cos/sin` at `2π/3`. No general theorem, no Gauss sum. -/
theorem one_add_two_omega : (1 : ℂ) + 2 * ω = Complex.I * sqrtp 3 := by
  have hω : ω = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    unfold ω stdRoot
    congr 1
    push_cast
    ring
  rw [hω, Complex.exp_ofReal_mul_I]
  rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring]
  rw [Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold sqrtp
  push_cast
  ring

/-- **Route A (independent)**: expansion + Euler give `g = i√3`. -/
theorem witness_sign_three_independent : quadGaussSum ψ₃ = Complex.I * sqrtp 3 := by
  rw [quadGaussSum_three_expand, one_add_two_omega]

/-- **Route B (via the general theorem)**: `quadGaussSum_sign_char` at `p = 3`. Routes A and B prove
the same statement by disjoint arguments — that agreement is the witness. -/
theorem witness_sign_three_general : quadGaussSum ψ₃ = Complex.I * sqrtp 3 := by
  have h := quadGaussSum_sign_char (p := 3) (by norm_num)
  rw [if_neg (by norm_num)] at h
  exact h

/-! ## The modulus -/

/-- **Route A (independent)**: from route A's value, `‖g‖² = 3`. -/
theorem witness_normSq_three_independent : ‖quadGaussSum ψ₃‖ ^ 2 = 3 := by
  rw [witness_sign_three_independent, norm_mul, Complex.norm_I, one_mul]
  unfold sqrtp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]
  norm_num

/-- **Route B (via the general theorem)**: `quadGaussSum_normSq` at `F = ZMod 3`. -/
theorem witness_normSq_three_general : ‖quadGaussSum ψ₃‖ ^ 2 = 3 := by
  have hF : ringChar (ZMod 3) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hψ1 : ψ₃ ≠ 1 :=
    ne_one_of_isPrimitive
      (AddChar.zmodChar_primitive_of_primitive_root 3 (stdRoot_isPrimitiveRoot (by norm_num)))
  have h := quadGaussSum_normSq hF hψ1
  rw [ZMod.card] at h
  exact_mod_cast h

/-! ## The value law at `a = 2` -/

/-- **Independent step**: the direct expansion `Σψ(2x²) = 1 + 2ω²`. -/
theorem gen_two_expand : quadGaussSumGen ψ₃ 2 = 1 + 2 * ω ^ 2 := by
  unfold quadGaussSumGen
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show ((2 : ZMod 3) * 0 ^ 2) = 0 from by decide, show ((2 : ZMod 3) * 1 ^ 2) = 2 from by decide,
    show ((2 : ZMod 3) * 2 ^ 2) = 2 from by decide]
  rw [AddChar.map_zero_eq_one, ψ₃_apply 2, show (2 : ZMod 3).val = 2 from rfl]
  ring

/-- **Route A (independent)**: `g(2) = −g`, and the equality is *exactly* the cyclotomic
relation `1 + ω + ω² = 0` — a pure convention check on the value law. -/
theorem witness_value_law_independent : quadGaussSumGen ψ₃ 2 = -(quadGaussSum ψ₃) := by
  rw [gen_two_expand, quadGaussSum_three_expand]
  linear_combination 2 * omega_cubic

/-- **Route B (via the general theorem)**: the value law `g(a) = χ₂(a)·g(1)` at `a = 2`, with
`χ₂(2) = −1` over `ZMod 3` computed by `decide`. -/
theorem witness_value_law_general : quadGaussSumGen ψ₃ 2 = -(quadGaussSum ψ₃) := by
  have hψ1 : ψ₃ ≠ 1 :=
    ne_one_of_isPrimitive
      (AddChar.zmodChar_primitive_of_primitive_root 3 (stdRoot_isPrimitiveRoot (by norm_num)))
  rw [quadGaussSumGen_eq_quadraticChar_mul hψ1 (by decide : (2 : ZMod 3) ≠ 0)]
  rw [quadCharC_apply, show quadraticChar (ZMod 3) 2 = -1 from by decide]
  push_cast
  ring

/-! ## The Davenport–Hasse square -/

/-- `(i√3)² = −3` — the number the Davenport–Hasse relation's square must produce at
`p = 3, m = 2`. Pure arithmetic, no general theorem. -/
theorem witness_dh_square : (Complex.I * sqrtp 3) ^ 2 = -3 := by
  rw [mul_pow, Complex.I_sq, sqrtp_sq]
  push_cast
  ring

/-! ## The `𝔽₉` instance (scope: general theorem + arithmetic, not independent)

The `quadGaussSum_sign_fq` instance at `E = GaloisField 3 2` evaluates to the **rational** value
`(−1)^{2−1}·(i√3)² = 3`. The route below through the general theorem is real (the instance pipeline
— algebra instances, `finrank = 2` — genuinely applies, and the arithmetic goes through
`witness_dh_square`). An *independent* route (expanding the nine-term sum over a concrete `𝔽₉`) is
**not attempted**: `GaloisField` is a polynomial-quotient construction with no decidable arithmetic,
so the direct expansion has no cheap engine. -/

noncomputable instance : Fintype (GaloisField 3 2) := Fintype.ofFinite _

/-- **Via the general theorem and arithmetic**: the `𝔽₉` Gauss sum is the rational number `3`. -/
theorem witness_fq_nine_general :
    ECCLib.quadGaussSum
        ((AddChar.zmodChar 3
            ((stdRoot_isPrimitiveRoot (p := 3) (Fact.out : Nat.Prime 3).pos.ne').pow_eq_one)).compAddMonoidHom
          (Algebra.trace (ZMod 3) (GaloisField 3 2)).toAddMonoidHom)
      = 3 := by
  have h := ECCLib.GaussSumFq.quadGaussSum_sign_fq (p := 3) (by norm_num) (GaloisField 3 2)
  rw [GaloisField.finrank 3 (by norm_num)] at h
  rw [if_neg (by norm_num)] at h
  rw [h, pow_one, neg_one_mul, mul_pow, Complex.I_sq, sqrtp_sq]
  push_cast
  ring

end ECCLib.Witness

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GowersNorm

/-!
# The `U²` inverse theorem — the detector base case

The **`U²` inverse theorem** is the sound-and-complete *detector* base case of higher-order Fourier
analysis: a large `U²` (Gowers) norm forces correlation with a single **linear phase** — one Fourier
coefficient. Unlike `U^k` for `k ≥ 3` (which needs nilsequences / nonclassical polynomials), `k = 2`
is elementary Fourier analysis: the inverse reduces to a single character via the `ℓ⁴ → ℓ^∞` step.

This file formalizes the **inverse deduction** and its self-contained engine on the frame's own
`ECCLib.gowersNorm 2`, isolating exactly the two analytic inputs that connect to a Fourier
transform:

* `exists_ge_sum_pow_four` — the `ℓ⁴ ≤ ℓ^∞ · ℓ²` engine (no Fourier; the detector mechanism).
* `u2_inverse_of_fourier` — the inverse: given the **`U²`–Fourier identity**
  `gowersInner 2 f = Σ_ξ |a ξ|⁴` and **Parseval** `Σ_ξ |a ξ|² = 𝔼_x |f x|²`, a `1`-bounded `f` has a
  coefficient `‖a ξ‖ ≥ ‖f‖_{U²}²`.

The convention: `a : ι → ℂ` is the `𝔼`-normalized
Fourier transform (`a ξ = 𝔼_x f x · conj (χ_ξ x)`), so the identity is the **plain sum** `Σ_ξ|a ξ|⁴`
and Parseval carries the `𝔼` on the space side. Both hypotheses are proven mathematics at `k = 2`
(Tao, *HOFA* §1.5 Ex. 2; operator form BBCvH 2605.26983 Prop 17); here they are named as the
Fourier-construction interface. Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

/-- **The detector engine (`ℓ⁴ ≤ ℓ^∞ · ℓ²`).** For any finite family `a`, some index `ξ` witnesses
`Σ_i |a i|⁴ ≤ |a ξ|² · Σ_i |a i|²`: pick `ξ` maximizing `|a|²`, then `|a i|⁴ = |a i|²·|a i|² ≤
|a ξ|²·|a i|²` termwise. Self-contained — no Fourier analysis. -/
lemma exists_ge_sum_pow_four {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℂ) :
    ∃ ξ : ι, ∑ i, ‖a i‖ ^ 4 ≤ ‖a ξ‖ ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
  obtain ⟨ξ, -, hξ⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) (fun i => ‖a i‖ ^ 2)
  refine ⟨ξ, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h4 : ‖a i‖ ^ 4 = ‖a i‖ ^ 2 * ‖a i‖ ^ 2 := by ring
  rw [h4]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← hξ]
  exact Finset.le_sup' (fun i => ‖a i‖ ^ 2) (Finset.mem_univ i)

variable {V : Type*} [AddCommGroup V] [Fintype V] [Nonempty V]

omit [Nonempty V] in
/-- `gowersInner 2 f` is the nonnegative real `𝔼_{h} ‖𝔼_x (∂_h f)(x)‖²` (the `U²` box average),
cast into `ℂ`. Restates `gowersInner_succ_ofReal` at `d = 1`. -/
lemma gowersInner_two_ofReal (f : V → ℂ) :
    gowersInner 2 f
      = ((Finset.expect Finset.univ
          (fun h' : Fin 1 → V =>
            ‖Finset.expect Finset.univ (iterMderiv (List.ofFn h') f)‖ ^ 2) : ℝ) : ℂ) :=
  gowersInner_succ_ofReal 1 f

/-- **The `U²` inverse theorem (max-coefficient form).** Suppose `a : ι → ℂ` satisfies the
`U²`–Fourier **identity** `gowersInner 2 f = Σ_ξ ‖a ξ‖⁴` and **Parseval** `Σ_ξ ‖a ξ‖² = 𝔼_x ‖f x‖²`,
and `f` is `1`-bounded. Then some coefficient dominates the squared `U²` norm:
`‖f‖_{U²}² ≤ ‖a ξ‖`. Equivalently, a function with no linear-phase correlation has small `U²` norm —
the completeness half of "`U²` detects linear structure."

Proof: `‖f‖_{U²}² = (Σ‖a‖⁴)^{1/2}`; the engine gives a `ξ` with `Σ‖a‖⁴ ≤ ‖a ξ‖²·Σ‖a‖²`; Parseval and
`|f| ≤ 1` bound `Σ‖a‖² = 𝔼‖f‖² ≤ 1`; so `Σ‖a‖⁴ ≤ ‖a ξ‖²` and `(Σ‖a‖⁴)^{1/2} ≤ ‖a ξ‖`. -/
theorem u2_inverse_of_fourier {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : V → ℂ) (a : ι → ℂ)
    (hident : gowersInner 2 f = ((∑ ξ, ‖a ξ‖ ^ 4 : ℝ) : ℂ))
    (hparseval : ∑ ξ, ‖a ξ‖ ^ 2 = Finset.expect Finset.univ (fun x => ‖f x‖ ^ 2))
    (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ∃ ξ : ι, gowersNorm 2 f ^ 2 ≤ ‖a ξ‖ := by
  set S : ℝ := ∑ ξ, ‖a ξ‖ ^ 4 with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => by positivity)
  -- ‖f‖_{U²} = S^{1/4}
  have hnorm : gowersNorm 2 f = S ^ ((1 : ℝ) / 4) := by
    rw [gowersNorm_eq, hident, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
    norm_num
  -- Σ‖a‖² ≤ 1
  have hT : ∑ ξ, ‖a ξ‖ ^ 2 ≤ 1 := by
    rw [hparseval]
    calc Finset.expect Finset.univ (fun x => ‖f x‖ ^ 2)
        ≤ Finset.expect Finset.univ (fun _ : V => (1 : ℝ)) :=
          Finset.expect_le_expect (fun x _ => pow_le_one₀ (norm_nonneg _) (hbound x))
      _ = 1 := Finset.expect_const Finset.univ_nonempty 1
  -- the engine picks the dominating coefficient
  obtain ⟨ξ, hξ⟩ := exists_ge_sum_pow_four a
  refine ⟨ξ, ?_⟩
  have hSle : S ≤ ‖a ξ‖ ^ 2 := by
    calc S ≤ ‖a ξ‖ ^ 2 * ∑ ξ, ‖a ξ‖ ^ 2 := hξ
      _ ≤ ‖a ξ‖ ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left hT (by positivity)
      _ = ‖a ξ‖ ^ 2 := mul_one _
  -- (S^{1/4})² = S^{1/2} ≤ (‖a ξ‖²)^{1/2} = ‖a ξ‖
  have e1 : (S ^ ((1 : ℝ) / 4)) ^ 2 = S ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast (S ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hS]
    norm_num
  have e2 : (‖a ξ‖ ^ 2) ^ ((1 : ℝ) / 2) = ‖a ξ‖ := by
    rw [← Real.rpow_natCast ‖a ξ‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  calc gowersNorm 2 f ^ 2 = (S ^ ((1 : ℝ) / 4)) ^ 2 := by rw [hnorm]
    _ = S ^ ((1 : ℝ) / 2) := e1
    _ ≤ (‖a ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hS hSle (by norm_num)
    _ = ‖a ξ‖ := e2

end ECCLib

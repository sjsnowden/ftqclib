/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.InverseU2
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

set_option linter.style.longLine false

/-!
# The finite-abelian Fourier transform and the `U²` inverse theorem

This file builds the **𝔼-normalized discrete Fourier transform** on an arbitrary finite abelian group
`V`, proves inversion, Parseval, and the **`U²`–Fourier identity**
`‖f‖_{U²}⁴ = Σ_ξ |f̂(ξ)|⁴`, and uses them to discharge the two analytic hypotheses of
`ECCLib.u2_inverse_of_fourier`. The payoff is a **hypothesis-free `U²` inverse theorem**
(`u2_inverse`) on the frame's own `ECCLib.gowersNorm 2`: a `1`-bounded function correlates with
a single character at least as strongly as its squared `U²` norm.

## Why this is built from scratch

Mathlib upstreams the *character-orthogonality* layer (`AddChar.sum_apply_eq_ite`,
`AddChar.expect_eq_ite`, `AddChar.complexBasis`) but **not** a general finite-abelian discrete Fourier
transform with Parseval — the only concrete DFT in Mathlib (`Analysis.Fourier.ZMod`) is cyclic
(`ZMod N`) and plain-sum-normalized. The frame's domain is `Fin n → ZMod p`, a *product* group; so the
transform, its inversion, Parseval, the autocorrelation–Fourier identity, and the `U²` identity are all
constructed here directly from the two orthogonality relations.

## Convention (matching `ECCLib.gowersInner`)

The transform carries the **expectation** `𝔼` on the space side and a **plain sum** on the dual side:

    f̂(ξ) = 𝔼_{x ∈ V} f(x) · conj(ξ x),      ‖f‖_{U²}⁴ = Σ_{ξ ∈ V̂} |f̂(ξ)|⁴.

This is the factor-free convention (Tao, *HOFA* §1.5 Ex. 2; arXiv:2508.08968).
`gowersInner` uses `Finset.expect`, so `f̂` does too.

The engine of the whole file is one reusable Parseval-type lemma, `expect_normSq_sum_char`:
`𝔼_h ‖Σ_ξ c_ξ · ξ(h)‖² = Σ_ξ ‖c_ξ‖²`. Parseval is its `c = f̂`, inversion instance; the `U²` identity
is its `c_ξ = f̂(ξ)·conj f̂(ξ)`, autocorrelation instance.
-/

namespace ECCLib

open scoped BigOperators ComplexConjugate
open Finset

variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- The **𝔼-normalized discrete Fourier transform**: `f̂(ξ) = 𝔼_x f(x)·conj(ξ x)`. -/
noncomputable def fourierT (f : V → ℂ) (ξ : AddChar V ℂ) : ℂ :=
  Finset.expect Finset.univ (fun x => f x * conj (ξ x))

/-- **Group orthogonality (𝔼-normalized):** `𝔼_x ξ(x)·conj(η x) = δ_{ξ,η}`. The character `ξ - η`
averages to `1` if trivial and `0` otherwise (`AddChar.expect_eq_ite`). -/
lemma expect_char_mul_conj (ξ η : AddChar V ℂ) :
    Finset.expect Finset.univ (fun x => ξ x * conj (η x)) = if ξ = η then 1 else 0 := by
  have h : (fun x => ξ x * conj (η x)) = (fun x => (ξ - η) x) := by
    funext x; rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
  rw [h, AddChar.expect_eq_ite (ξ - η)]; simp only [sub_eq_zero]

open scoped Classical in
/-- **Dual orthogonality:** `Σ_ξ ξ(a)·conj(ξ b) = |V|·δ_{a,b}` (`AddChar.sum_apply_eq_ite`). -/
lemma sum_char_mul_conj (a b : V) :
    ∑ ξ : AddChar V ℂ, ξ a * conj (ξ b) = if a = b then (Fintype.card V : ℂ) else 0 := by
  have h : (fun ξ : AddChar V ℂ => ξ a * conj (ξ b)) = (fun ξ => ξ (a - b)) := by
    funext ξ; rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  rw [h, AddChar.sum_apply_eq_ite (a - b)]; simp only [sub_eq_zero]

variable [Nonempty V]

/-- **Fourier inversion:** `f(x) = Σ_ξ f̂(ξ)·ξ(x)`. Expand `f̂`, swap `𝔼_y` past the dual sum, and
collapse by dual orthogonality. -/
lemma fourier_inversion (f : V → ℂ) (x : V) :
    ∑ ξ : AddChar V ℂ, fourierT f ξ * ξ x = f x := by
  classical
  simp only [fourierT, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have hstep : ∀ y : V, ∑ ξ : AddChar V ℂ, (f y * conj (ξ y)) * ξ x
      = f y * (if x = y then (Fintype.card V : ℂ) else 0) := by
    intro y
    rw [← sum_char_mul_conj x y, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun ξ _ => by ring)
  simp only [hstep]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [mul_div_assoc, div_self (by exact_mod_cast Fintype.card_ne_zero), mul_one]

omit [Nonempty V] in
/-- `z·conj z = ‖z‖²` cast into `ℂ`. -/
lemma conj_key (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [Nonempty V] in
/-- **The Parseval engine (complex form).** For any dual-indexed coefficients `c`,
`𝔼_h (Σ_ξ c_ξ ξ h)·conj(Σ_ξ c_ξ ξ h) = Σ_ξ c_ξ·conj(c_ξ)`: expand the product into a double character
sum and collapse by group orthogonality. -/
lemma expect_sum_char_mul_conj_sum (c : AddChar V ℂ → ℂ) :
    Finset.expect Finset.univ
        (fun h => (∑ ξ : AddChar V ℂ, c ξ * ξ h) * conj (∑ ξ : AddChar V ℂ, c ξ * ξ h))
      = ∑ ξ : AddChar V ℂ, c ξ * conj (c ξ) := by
  have hpt : ∀ h : V,
      (∑ ξ : AddChar V ℂ, c ξ * ξ h) * conj (∑ ξ : AddChar V ℂ, c ξ * ξ h)
      = ∑ ξ : AddChar V ℂ, ∑ η : AddChar V ℂ, (c ξ * conj (c η)) * (ξ h * conj (η h)) := by
    intro h
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun ξ _ => Finset.sum_congr rfl (fun η _ => by rw [map_mul]; ring))
  simp only [hpt, Finset.expect_sum_comm]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  have hcol : ∀ η : AddChar V ℂ,
      Finset.expect Finset.univ (fun h => (c ξ * conj (c η)) * (ξ h * conj (η h)))
      = if ξ = η then c ξ * conj (c η) else 0 := by
    intro η
    rw [← Finset.mul_expect, expect_char_mul_conj, mul_ite, mul_one, mul_zero]
  simp only [hcol]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

omit [Nonempty V] in
/-- **The Parseval engine (real form):** `𝔼_h ‖Σ_ξ c_ξ ξ(h)‖² = Σ_ξ ‖c_ξ‖²`. Both Parseval and the
`U²` identity are instances of this. -/
lemma expect_normSq_sum_char (c : AddChar V ℂ → ℂ) :
    Finset.expect Finset.univ (fun h => ‖∑ ξ : AddChar V ℂ, c ξ * ξ h‖ ^ 2)
      = ∑ ξ : AddChar V ℂ, ‖c ξ‖ ^ 2 := by
  have h := expect_sum_char_mul_conj_sum c
  have hL : ∀ h : V, (∑ ξ : AddChar V ℂ, c ξ * ξ h) * conj (∑ ξ : AddChar V ℂ, c ξ * ξ h)
      = ((‖∑ ξ : AddChar V ℂ, c ξ * ξ h‖ ^ 2 : ℝ) : ℂ) := fun _ => conj_key _
  have hR : ∀ ξ : AddChar V ℂ, c ξ * conj (c ξ) = ((‖c ξ‖ ^ 2 : ℝ) : ℂ) := fun _ => conj_key _
  simp only [hL, hR] at h
  rw [← Complex.ofReal_expect, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- **Parseval / Plancherel:** `Σ_ξ ‖f̂(ξ)‖² = 𝔼_x ‖f x‖²`. Immediate from the engine at `c = f̂`,
using inversion `Σ_ξ f̂(ξ) ξ(x) = f x`. -/
lemma parseval_real (f : V → ℂ) :
    ∑ ξ : AddChar V ℂ, ‖fourierT f ξ‖ ^ 2 = Finset.expect Finset.univ (fun x => ‖f x‖ ^ 2) := by
  rw [← expect_normSq_sum_char (fourierT f)]
  exact Finset.expect_congr rfl (fun x _ => by rw [fourier_inversion])

/-- **Autocorrelation–Fourier identity:** the `U²` box average `𝔼_x f(x+h)·conj(f x)` has Fourier
coefficients `‖f̂(ξ)‖²`: `𝔼_x f(x+h)·conj(f x) = Σ_ξ (f̂(ξ)·conj f̂(ξ))·ξ(h)`. Substitute inversion for
both `f`'s and collapse the double character sum by group orthogonality. -/
lemma autocorr_fourier (f : V → ℂ) (h : V) :
    Finset.expect Finset.univ (fun x => f (x + h) * conj (f x))
      = ∑ ξ : AddChar V ℂ, (fourierT f ξ * conj (fourierT f ξ)) * ξ h := by
  have hpt : ∀ x : V, f (x + h) * conj (f x)
      = ∑ ξ : AddChar V ℂ, ∑ η : AddChar V ℂ,
          (fourierT f ξ * conj (fourierT f η)) * (ξ (x + h) * conj (η x)) := by
    intro x
    rw [← fourier_inversion f (x + h), ← fourier_inversion f x, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun ξ _ => Finset.sum_congr rfl (fun η _ => by rw [map_mul]; ring))
  simp only [hpt, Finset.expect_sum_comm]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  have hcol : ∀ η : AddChar V ℂ,
      Finset.expect Finset.univ
          (fun x => (fourierT f ξ * conj (fourierT f η)) * (ξ (x + h) * conj (η x)))
      = if ξ = η then (fourierT f ξ * conj (fourierT f η)) * ξ h else 0 := by
    intro η
    have hxh : ∀ x : V, (fourierT f ξ * conj (fourierT f η)) * (ξ (x + h) * conj (η x))
        = ((fourierT f ξ * conj (fourierT f η)) * ξ h) * (ξ x * conj (η x)) := by
      intro x; rw [AddChar.map_add_eq_mul]; ring
    simp only [hxh]
    rw [← Finset.mul_expect, expect_char_mul_conj, mul_ite, mul_one, mul_zero]
  simp only [hcol]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

/-- **The `U²`–Fourier identity:** `gowersInner 2 f = Σ_ξ ‖f̂(ξ)‖⁴` (as the nonnegative real cast into
`ℂ`). Reindex the `U²` box average over `Fin 1 → V` to `V`, substitute the autocorrelation identity,
and apply the Parseval engine to the coefficients `f̂(ξ)·conj f̂(ξ)` (whose norm-square is `‖f̂(ξ)‖⁴`). -/
lemma gowersInner_two_eq_sum (f : V → ℂ) :
    gowersInner 2 f = ((∑ ξ : AddChar V ℂ, ‖fourierT f ξ‖ ^ 4 : ℝ) : ℂ) := by
  rw [gowersInner_succ_ofReal 1 f]
  congr 1
  have hB : ∀ h' : Fin 1 → V,
      Finset.expect Finset.univ (iterMderiv (List.ofFn h') f)
      = Finset.expect Finset.univ (fun x => f (x + h' 0) * conj (f x)) :=
    fun h' => Finset.expect_congr rfl (fun x _ => by rw [iterMderiv_ofFn_one])
  simp only [hB]
  rw [Fintype.expect_equiv (Equiv.funUnique (Fin 1) V)
      (fun h' : Fin 1 → V => ‖Finset.expect Finset.univ (fun x => f (x + h' 0) * conj (f x))‖ ^ 2)
      (fun h : V => ‖Finset.expect Finset.univ (fun x => f (x + h) * conj (f x))‖ ^ 2)
      (fun h' => by simp only [Equiv.funUnique_apply, Fin.default_eq_zero])]
  simp only [autocorr_fourier]
  rw [expect_normSq_sum_char (fun ξ => fourierT f ξ * conj (fourierT f ξ))]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [norm_mul, Complex.norm_conj]; ring

/-- **The `U²` inverse theorem (hypothesis-free).** A `1`-bounded function on any finite abelian group
correlates with some character `ξ` at least as strongly as its squared `U²` norm:
`‖f‖_{U²}² ≤ ‖f̂(ξ)‖`. Discharges the two Fourier hypotheses of `u2_inverse_of_fourier` via
`gowersInner_two_eq_sum` (the `U²` identity) and `parseval_real`. This is the sound-and-complete
detector base case: no linear-phase correlation forces a small `U²` norm. -/
theorem u2_inverse (f : V → ℂ) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    ∃ ξ : AddChar V ℂ, gowersNorm 2 f ^ 2 ≤ ‖fourierT f ξ‖ := by
  haveI : Nonempty (AddChar V ℂ) := ⟨0⟩
  exact u2_inverse_of_fourier f (fourierT f)
    (gowersInner_two_eq_sum f) (parseval_real f) hbound

end ECCLib

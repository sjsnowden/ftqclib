/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Derivative
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

set_option linter.style.longLine false

/-!
# The Gowers uniformity norm

The **Gowers uniformity norm** of order `d`,
`‖f‖_{U^d} = |𝔼_{x,h₁,…,h_d} ∂_{h₁}⋯∂_{h_d} f(x)|^{1/2^d}`, built from the **multiplicative derivative**
`∂_h f(x) = f(x+h)·conj(f x)` and the finite average `𝔼` (Mathlib's `Finset.expect`). This is the founding
object of higher-order Fourier analysis (Gowers 1998/2001); its very definition is unformalized in any proof
assistant prior to this file.

Mathlib-only; FTQCLib-independent. The domain `V` is a finite additive group (`𝔽_p^n` at
`V = Fin n → ZMod p`).
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V]

/-- The **multiplicative derivative** `∂_h f (x) = f(x + h) · conj(f x)`. -/
noncomputable def mderiv (h : V) (f : V → ℂ) : V → ℂ := fun x => f (x + h) * star (f x)

/-- The **iterated multiplicative derivative** over a list of directions. -/
noncomputable def iterMderiv (hs : List V) (f : V → ℂ) : V → ℂ := hs.foldr mderiv f

@[simp] lemma iterMderiv_nil (f : V → ℂ) : iterMderiv ([] : List V) f = f := rfl

lemma iterMderiv_cons (h : V) (hs : List V) (f : V → ℂ) :
    iterMderiv (h :: hs) f = mderiv h (iterMderiv hs f) := rfl

/-- A single multiplicative derivative, evaluated: `∂_{h} f (x) = f(x + h₀) · conj(f x)`. -/
lemma iterMderiv_ofFn_one (h : Fin 1 → V) (f : V → ℂ) (x : V) :
    iterMderiv (List.ofFn h) f x = f (x + h 0) * (starRingEnd ℂ) (f x) := by
  simp only [iterMderiv, mderiv, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
    starRingEnd_apply]

/-- The shear `(x, h) ↦ (x, x + h₀)` used to reindex the `U¹` average. -/
private def gowersEquiv : (V × (Fin 1 → V)) ≃ (V × V) where
  toFun p := (p.1, p.1 + p.2 0)
  invFun q := (q.1, fun _ => q.2 - q.1)
  left_inv := by
    rintro ⟨x, h⟩; simp only [add_sub_cancel_left, Prod.mk.injEq, true_and]
    funext i; fin_cases i; rfl
  right_inv := by rintro ⟨x, z⟩; simp only [Prod.mk.injEq, true_and]; abel

/-- Complex conjugation commutes with the finite average. -/
lemma conj_expect {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (starRingEnd ℂ) (Finset.expect Finset.univ g)
      = Finset.expect Finset.univ (fun i => (starRingEnd ℂ) (g i)) := by
  apply Complex.ext
  · simp [Complex.conj_re, Complex.re_expect]
  · simp [Complex.conj_im, Complex.im_expect, Finset.expect_neg_distrib]

variable [Fintype V]

/-- The **Gowers uniformity norm** of order `d`:
`‖f‖_{U^d} = |𝔼_{x,h₁,…,h_d} (∂_{h₁}⋯∂_{h_d} f)(x)|^{1/2^d}`, averaging the iterated multiplicative
derivative over the base point `x` and the `d` shift directions. -/
noncomputable def gowersNorm (d : ℕ) (f : V → ℂ) : ℝ :=
  ‖Finset.expect Finset.univ (fun p : V × (Fin d → V) => iterMderiv (List.ofFn p.2) f p.1)‖
    ^ ((1 : ℝ) / 2 ^ d)

/-- The Gowers norm is nonnegative. -/
theorem gowersNorm_nonneg (d : ℕ) (f : V → ℂ) : 0 ≤ gowersNorm d f :=
  Real.rpow_nonneg (norm_nonneg _) _

/-- The inner `U¹` average factors as `conj(𝔼 f) · 𝔼 f = |𝔼 f|²`. -/
private lemma gowers_inner (f : V → ℂ) :
    Finset.expect Finset.univ (fun p : V × (Fin 1 → V) => iterMderiv (List.ofFn p.2) f p.1)
      = (starRingEnd ℂ) (Finset.expect Finset.univ f) * Finset.expect Finset.univ f := by
  simp only [iterMderiv_ofFn_one]
  rw [Fintype.expect_equiv gowersEquiv (fun p => f (p.1 + p.2 0) * (starRingEnd ℂ) (f p.1))
      (fun q => (starRingEnd ℂ) (f q.1) * f q.2) (fun p => mul_comm _ _),
    ← Finset.univ_product_univ,
    Finset.expect_product' Finset.univ Finset.univ (fun x z => (starRingEnd ℂ) (f x) * f z),
    ← Finset.expect_mul_expect, conj_expect]

/-- **The `U¹` identity:** `‖f‖_{U¹} = |𝔼 f|`, the modulus of the mean. (So `U¹` is only a *semi*norm — it
vanishes on every mean-zero function.) This is the base case of the Gowers hierarchy. -/
theorem gowersNorm_one (f : V → ℂ) : gowersNorm 1 f = ‖Finset.expect Finset.univ f‖ := by
  rw [gowersNorm, gowers_inner, norm_mul, Complex.norm_conj, ← pow_two,
    ← Real.rpow_natCast ‖Finset.expect Finset.univ f‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-! ### Monotonicity of the Gowers norms — the Gowers–Cauchy–Schwarz inequality -/

/-- **Cauchy–Schwarz for the finite average:** `‖𝔼 G‖² ≤ 𝔼 ‖G‖²`. -/
lemma norm_expect_sq_le {ι : Type*} [Fintype ι] [Nonempty ι] (G : ι → ℂ) :
    ‖Finset.expect Finset.univ G‖ ^ 2 ≤ Finset.expect Finset.univ (fun i => ‖G i‖ ^ 2) := by
  calc ‖Finset.expect Finset.univ G‖ ^ 2
      ≤ (Finset.expect Finset.univ (fun i => ‖G i‖)) ^ 2 := by
        gcongr; exact RCLike.norm_expect_le (K := ℝ)
    _ ≤ Finset.expect Finset.univ (fun i => ‖G i‖ ^ 2) := by
        simpa using
          Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖G i‖) (fun _ => (1 : ℝ))

/-- The **inner Gowers average** of order `d`: `gowersNorm d f = ‖gowersInner d f‖ ^ (1 / 2^d)`. -/
noncomputable def gowersInner (d : ℕ) (f : V → ℂ) : ℂ :=
  Finset.expect Finset.univ (fun p : V × (Fin d → V) => iterMderiv (List.ofFn p.2) f p.1)

lemma gowersNorm_eq (d : ℕ) (f : V → ℂ) :
    gowersNorm d f = ‖gowersInner d f‖ ^ ((1 : ℝ) / 2 ^ d) := rfl

omit [Fintype V] in
/-- Peeling the first difference off a Gowers product: `∂_{h} f = ∂_{h₀}(∂_{h₁…} f)`. -/
lemma iterMderiv_ofFn_peel {d : ℕ} (h : Fin (d + 1) → V) (f : V → ℂ) (x : V) :
    iterMderiv (List.ofFn h) f x
      = iterMderiv (List.ofFn (fun _ : Fin 1 => h 0))
          (iterMderiv (List.ofFn (fun i => h i.succ)) f) x := by
  rw [List.ofFn_succ, iterMderiv_cons]
  simp only [iterMderiv, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]

/-- The reindex `(x, h) ↦ (h∘succ, (x, ·↦h₀))` peeling one direction out of the `U^{d+1}` average. -/
private def peelEquiv (d : ℕ) : (V × (Fin (d + 1) → V)) ≃ ((Fin d → V) × (V × (Fin 1 → V))) where
  toFun p := (fun i => p.2 i.succ, (p.1, fun _ => p.2 0))
  invFun q := (q.2.1, Fin.cons (q.2.2 0) q.1)
  left_inv := fun ⟨x, h⟩ => by
    simp only [Prod.mk.injEq, true_and]; exact Fin.cons_self_tail h
  right_inv := fun ⟨h', x, k⟩ => by
    simp only [Fin.cons_zero, Fin.cons_succ, Prod.mk.injEq, true_and]
    funext i; fin_cases i; rfl

/-- **Peeling one direction:** `gowersInner (d+1) f = 𝔼_{h'} gowersInner 1 (∂_{h'} f)`. -/
lemma gowersInner_succ (d : ℕ) (f : V → ℂ) :
    gowersInner (d + 1) f
      = Finset.expect Finset.univ
          (fun h' : Fin d → V => gowersInner 1 (iterMderiv (List.ofFn h') f)) := by
  rw [gowersInner, Fintype.expect_equiv (peelEquiv d)
      (fun p => iterMderiv (List.ofFn p.2) f p.1)
      (fun q => iterMderiv (List.ofFn q.2.2) (iterMderiv (List.ofFn q.1) f) q.2.1)
      (fun p => iterMderiv_ofFn_peel p.2 f p.1),
    ← Finset.univ_product_univ, Finset.expect_product]
  rfl

/-- **Fubini form:** `gowersInner d f = 𝔼_{h'} 𝔼_x (∂_{h'} f)(x)`. -/
lemma gowersInner_eq (d : ℕ) (f : V → ℂ) :
    gowersInner d f
      = Finset.expect Finset.univ
          (fun h' : Fin d → V => Finset.expect Finset.univ (iterMderiv (List.ofFn h') f)) := by
  rw [gowersInner, Fintype.expect_equiv (Equiv.prodComm V (Fin d → V))
      (fun p => iterMderiv (List.ofFn p.2) f p.1)
      (fun q => iterMderiv (List.ofFn q.1) f q.2) (fun p => rfl),
    ← Finset.univ_product_univ,
    Finset.expect_product' Finset.univ Finset.univ (fun h' x => iterMderiv (List.ofFn h') f x)]

private lemma gowersInner_one (f : V → ℂ) :
    gowersInner 1 f
      = (starRingEnd ℂ) (Finset.expect Finset.univ f) * Finset.expect Finset.univ f :=
  gowers_inner f

private lemma conj_mul_eq_normSq (z : ℂ) : (starRingEnd ℂ z) * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The `(d+1)`-fold Gowers inner product as a nonnegative real:** `𝔼_{h'} ‖𝔼_x (∂_{h'} f)(x)‖²`. -/
lemma gowersInner_succ_ofReal (d : ℕ) (f : V → ℂ) :
    gowersInner (d + 1) f
      = ((Finset.expect Finset.univ
          (fun h' : Fin d → V =>
            ‖Finset.expect Finset.univ (iterMderiv (List.ofFn h') f)‖ ^ 2) : ℝ) : ℂ) := by
  rw [gowersInner_succ, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun h' _ => ?_)
  rw [gowersInner_one, conj_mul_eq_normSq]

/-- **Gowers–Cauchy–Schwarz at the inner-product level:** `‖gowersInner d f‖² ≤ ‖gowersInner (d+1) f‖`.
The `(d+1)`-fold inner product is `𝔼_{h'} |𝔼_x (∂_{h'} f)(x)|²`, and Cauchy–Schwarz beats it below by the
`d`-fold one `𝔼_{h'} 𝔼_x (∂_{h'} f)(x)`. -/
lemma norm_gowersInner_sq_le (d : ℕ) (f : V → ℂ) :
    ‖gowersInner d f‖ ^ 2 ≤ ‖gowersInner (d + 1) f‖ := by
  have hd1 := gowersInner_succ_ofReal d f
  rw [gowersInner_eq, hd1, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.expect_nonneg (fun _ _ => sq_nonneg _))]
  haveI : Nonempty (Fin d → V) := ⟨0⟩
  exact norm_expect_sq_le _

/-- **Monotonicity of the Gowers norms (Gowers–Cauchy–Schwarz):** `‖f‖_{U^d} ≤ ‖f‖_{U^{d+1}}`. -/
theorem gowersNorm_le_succ (d : ℕ) (f : V → ℂ) : gowersNorm d f ≤ gowersNorm (d + 1) f := by
  rw [gowersNorm_eq, gowersNorm_eq]
  have h1 : (‖gowersInner d f‖ ^ 2) ^ ((1 : ℝ) / 2 ^ (d + 1))
      = ‖gowersInner d f‖ ^ ((1 : ℝ) / 2 ^ d) := by
    rw [← Real.rpow_natCast ‖gowersInner d f‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    rw [pow_succ]; field_simp; ring
  rw [← h1]
  exact Real.rpow_le_rpow (by positivity) (norm_gowersInner_sq_le d f) (by positivity)

/-- **Monotonicity in the order:** `k ≤ d ⟹ ‖f‖_{U^k} ≤ ‖f‖_{U^d}` (iterate `gowersNorm_le_succ`). -/
lemma gowersNorm_mono {k d : ℕ} (hkd : k ≤ d) (f : V → ℂ) :
    gowersNorm k f ≤ gowersNorm d f := by
  induction hkd with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (gowersNorm_le_succ _ f)

/-- **The mean is controlled by every Gowers norm:** `‖𝔼 f‖ ≤ ‖f‖_{U^d}` for `d ≥ 1`. This is the degenerate
(single-function) case of the generalized von Neumann inequality; the full multilinear form — controlling an
average against a system of linear forms, via the Gowers–Cauchy–Schwarz box inner product — is not formalized
here (it is a substantial separate development, absent from Mathlib). -/
lemma norm_expect_le_gowersNorm {d : ℕ} (hd : 1 ≤ d) (f : V → ℂ) :
    ‖Finset.expect Finset.univ f‖ ≤ gowersNorm d f := by
  rw [← gowersNorm_one f]
  exact gowersNorm_mono hd f

end ECCLib

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.MonomialWeil

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The Gauss collapse: the multiplier appears when a word leaves the monomial group

`MonomialWeil` shows the Weil representation is *tame* on the monomial group: substitution
operators, cocycle invariant, no scalar. This file proves the contrast theorem — the price of
leaving `M` through the Weyl element:

* `sum_quadChirp` — the one-dimensional completed square:
  `Σ_t ψ(½a·t² + tb) = ψ(−½a⁻¹·b²) · g(½a)`, `g` the generalized quadratic Gauss sum;
* `sum_quadChirp_pi` — its coordinatewise power over `𝔽_q^ι` (the same
  `addChar_map_sum`/`piFinset` factorization as the trace computation);
* **`fourierOp_chirp_fourierOp`** — the collapse: `𝓕 ∘ chirp_a ∘ 𝓕` equals
  `g(½a)^{|ι|}` times a word in a chirp, a DFT, and a *monomial* operator (`dilOp`):

  `𝓕 ∘ C_a ∘ 𝓕 = g(½a)^n • (C_{−a⁻¹} ∘ 𝓕 ∘ D_{−a⁻¹} ∘ C_{−a⁻¹})`.

  Collapsing one `w`-pair through a chirp produces exactly one Gauss-sum factor per coordinate —
  nothing else in the calculus produces any scalar at all;
* `collapse_scalar_factorization` — via the value law `g(c) = χ₂(c)·g(1)`, the multiplier
  factors as `(χ₂(½a))^n · (quadGaussSum ψ)^n`: a quadratic-character part (the `χ₂(det)`-type
  multiplier) times the `w`-normalization `Tr(𝓕)` part. This is where
  `quadGaussSumGen_eq_quadraticChar_mul` is consumed.
-/

namespace ECCLib.Heisenberg

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [Fintype F] [DecidableEq ι]

/-! ## Pairing helpers for constant scalings -/

lemma pairing_constMul_left (c : F) (y y' : ι → F) :
    pairing (fun i => c * y i) y' = c * pairing y y' := by
  unfold pairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma pairing_constMul_right (c : F) (y y' : ι → F) :
    pairing y (fun i => c * y' i) = c * pairing y y' := by
  unfold pairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The completed square, in one dimension and coordinatewise -/

/-- **The one-dimensional Gauss reduction**: `Σ_t ψ(½a·t² + tb) = ψ(−½a⁻¹b²) · g(½a)`. -/
lemma sum_quadChirp (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (ψ : AddChar F ℂ) (b : F) :
    ∑ t : F, ψ ((2 : F)⁻¹ * a * t ^ 2 + t * b)
      = ψ (-((2 : F)⁻¹ * a⁻¹) * b ^ 2) * ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a) := by
  have hexp : ∀ t : F, (2 : F)⁻¹ * a * t ^ 2 + t * b
      = (2 : F)⁻¹ * a * (t + a⁻¹ * b) ^ 2 + -((2 : F)⁻¹ * a⁻¹) * b ^ 2 := by
    intro t
    field_simp
    ring
  rw [Finset.sum_congr rfl fun t _ => by rw [hexp t, AddChar.map_add_eq_mul]]
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  change _ = ∑ x : F, ψ ((2 : F)⁻¹ * a * x ^ 2)
  exact Equiv.sum_comp (Equiv.addRight (a⁻¹ * b)) (fun s => ψ ((2 : F)⁻¹ * a * s ^ 2))

/-- **The coordinatewise power**: over `𝔽_q^ι` the quadratic-plus-linear character sum is the
one-dimensional Gauss factor to the `|ι|`, times the completed-square phase of the shift. -/
lemma sum_quadChirp_pi (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (ψ : AddChar F ℂ) (b : ι → F) :
    ∑ y : ι → F, ψ ((2 : F)⁻¹ * (a * pairing y y) + pairing y b)
      = (ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a)) ^ (Fintype.card ι)
        * ψ (-((2 : F)⁻¹ * a⁻¹) * pairing b b) := by
  classical
  have hchar : ∀ y : ι → F, ψ ((2 : F)⁻¹ * (a * pairing y y) + pairing y b)
      = ∏ i : ι, ψ ((2 : F)⁻¹ * a * (y i) ^ 2 + (y i) * (b i)) := by
    intro y
    rw [← addChar_map_sum]
    congr 1
    unfold pairing
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun y _ => hchar y, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset F)
      (fun (i : ι) (t : F) => ψ ((2 : F)⁻¹ * a * t ^ 2 + t * (b i)))]
  rw [Finset.prod_congr rfl fun i _ => sum_quadChirp h2 ha ψ (b i)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm]
  congr 1
  rw [← addChar_map_sum]
  congr 1
  unfold pairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The collapse theorem -/

open Classical in
/-- **The Gauss collapse** (the multiplier theorem): collapsing `𝓕 ∘ chirp_a ∘ 𝓕`
produces the Gauss-sum multiplier `g(½a)^{|ι|}` against a word in a chirp, a DFT, and a *monomial*
operator. On the monomial group itself no scalar ever appears (`dilOp_comp_weyl`); leaving it
through `w` costs exactly one Gauss sum per coordinate. -/
theorem fourierOp_chirp_fourierOp (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) {a : F} (ha : a ≠ 0) :
    fourierOp (ι := ι) ψ ∘ₗ chirp ψ (fun y => fun i => a * y i) ∘ₗ fourierOp ψ
      = (ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a)) ^ (Fintype.card ι) •
        (chirp ψ (fun y => fun i => -a⁻¹ * y i) ∘ₗ fourierOp ψ
          ∘ₗ dilOp (fun _ => -a⁻¹) ∘ₗ chirp ψ (fun y => fun i => -a⁻¹ * y i)) := by
  have hna : (-a⁻¹ : F) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ha)
  have h22 : (2 : F)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  refine LinearMap.ext fun f => ?_
  funext z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    fourierOp_apply, chirp, LinearMap.coe_mk, AddHom.coe_mk, dilOp_apply]
  -- ### The left side: swap the sums and collapse the inner one by the completed square.
  have hL : ∑ y : ι → F, ψ (pairing z y) *
        (ψ ((2 : F)⁻¹ * pairing (fun i => a * y i) y) * ∑ x : ι → F, ψ (pairing y x) * f x)
      = ∑ x : ι → F,
          ((ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a)) ^ (Fintype.card ι)
            * ψ (-((2 : F)⁻¹ * a⁻¹) * pairing (x + z) (x + z))) * f x := by
    have h1 : ∀ y : ι → F, ψ (pairing z y) *
          (ψ ((2 : F)⁻¹ * pairing (fun i => a * y i) y) * ∑ x : ι → F, ψ (pairing y x) * f x)
        = ∑ x : ι → F, ψ ((2 : F)⁻¹ * (a * pairing y y) + pairing y (x + z)) * f x := by
      intro y
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pairing_constMul_left]
      rw [show ψ (pairing z y) * (ψ ((2 : F)⁻¹ * (a * pairing y y)) * (ψ (pairing y x) * f x))
          = (ψ ((2 : F)⁻¹ * (a * pairing y y)) * (ψ (pairing y x) * ψ (pairing z y))) * f x
        from by ring]
      congr 1
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      rw [pairing_add_right, pairing_symm z y]
    rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, sum_quadChirp_pi h2 ha ψ (x + z)]
  rw [hL]
  -- ### The right side: reindex the sum along `u = −a·x` and identify the coefficients.
  have hinv : ((-a⁻¹ : F))⁻¹ = -a := by rw [inv_neg, inv_inv]
  simp only [hinv]
  set e : (ι → F) ≃ (ι → F) :=
    Equiv.piCongrRight (fun _ : ι => Equiv.mulLeft₀ (-a) (neg_ne_zero.mpr ha)) with he
  have hR : ∑ x : ι → F, ψ (pairing z x) *
        (ψ ((2 : F)⁻¹ * pairing (fun i => -a⁻¹ * (-a * x i)) fun i => -a * x i)
          * f fun i => -a * x i)
      = ∑ u : ι → F, ψ (-a⁻¹ * pairing z u) *
          (ψ ((2 : F)⁻¹ * (-a⁻¹ * pairing u u)) * f u) := by
    rw [← Equiv.sum_comp e (fun u => ψ (-a⁻¹ * pairing z u) *
      (ψ ((2 : F)⁻¹ * (-a⁻¹ * pairing u u)) * f u))]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hex : e x = fun i => -a * x i := rfl
    rw [hex]
    congr 1
    · -- ψ⟨z,x⟩ = ψ(−a⁻¹·⟨z, −a·x⟩)
      rw [pairing_constMul_right]
      rw [show (-a⁻¹ : F) * (-a * pairing z x) = (a⁻¹ * a) * pairing z x from by ring,
        inv_mul_cancel₀ ha, one_mul]
    · -- the chirp factors agree
      congr 2
      rw [pairing_constMul_left]
  rw [hR]
  -- ### Match coefficients: the completed-square phase splits into the three chirp phases.
  rw [pairing_constMul_left, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hexp : -((2 : F)⁻¹ * a⁻¹) * pairing (u + z) (u + z)
      = (2 : F)⁻¹ * (-a⁻¹ * pairing z z) + (-a⁻¹ * pairing z u
        + (2 : F)⁻¹ * (-a⁻¹ * pairing u u)) := by
    rw [pairing_add_right, pairing_add_left, pairing_add_left, pairing_symm u z]
    linear_combination (-(pairing z u) * a⁻¹) * h22
  rw [show (ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a)) ^ (Fintype.card ι)
        * ψ (-((2 : F)⁻¹ * a⁻¹) * pairing (u + z) (u + z)) * f u
      = (ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a)) ^ (Fintype.card ι)
        * (ψ (-((2 : F)⁻¹ * a⁻¹) * pairing (u + z) (u + z)) * f u) from by ring]
  congr 1
  rw [hexp, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- **The multiplier factorization** (consuming the value law `g(c) = χ₂(c)·g(1)`): the collapse
scalar splits as quadratic character times `w`-normalization, `g(½a)^n = χ₂(½a)^n · g(1)^n`. The
`χ₂` part is the `χ₂(det)`-type multiplier of the Levi; the `g(1)^n = Tr(𝓕)` part is the
normalization the linearization already pinned. -/
theorem collapse_scalar_factorization [DecidableEq F] {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) (h2 : (2 : F) ≠ 0) :
    (ECCLib.quadGaussSumGen ψ ((2 : F)⁻¹ * a)) ^ (Fintype.card ι)
      = (ECCLib.quadCharC F ((2 : F)⁻¹ * a)) ^ (Fintype.card ι)
        * (ECCLib.quadGaussSum ψ) ^ (Fintype.card ι) := by
  rw [ECCLib.quadGaussSumGen_eq_quadraticChar_mul hψ
    (mul_ne_zero (inv_ne_zero h2) ha), mul_pow]

end ECCLib.Heisenberg

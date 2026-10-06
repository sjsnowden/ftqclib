/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Equal Gram data is a unitary between two families of vectors

For two families `v w : ι → κ → 𝕜` of vectors indexed by the same set, the **Gram data** of `v` is
`Σ_u v x u · conj (v y u)` at each pair `x, y`. This file proves that `v` and `w` have the same Gram
data exactly when one unitary matrix on `κ` carries every `v x` to `w x`: the linear algebra behind
purification, which `FTQCLib/Carrier/UnreadBits.lean` (T27, `docs/TARGETS.md`) reads with `κ` the
unread words and `ι` the read words, `v x` and `w x` the unread vectors of two states.

The proof of the forward direction works in `EuclideanSpace 𝕜 κ`, where the Gram data is the inner
product. Equal Gram data makes `Σ_x c_x v x ↦ Σ_x c_x w x` a well-defined linear isometry from the
span of `v` into the space: the two combinations have the same norm, so a combination of `v` that
vanishes is one of `w` that vanishes. Mathlib's `LinearIsometry.extend` extends it to the whole
space, and its matrix in the standard orthonormal basis is unitary
(`LinearIsometryEquiv.toMatrix_mem_unitaryGroup`). The unitary is not unique unless `v` spans, and
the statement only claims existence. The converse holds over any commutative star ring.

The file is linear algebra over `𝕜` and `Matrix` alone: it imports no module of this library, so
the topic module can import it.

## Main results

* `exists_isometry_of_gram_eq` — equal Gram data gives a unitary carrying `v` to `w`.
* `gram_eq_of_isometry` — a unitary carrying `v` to `w` gives equal Gram data.
-/

namespace FTQCLib.Frame.Walkthrough

open WithLp
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype κ]

/-! ## The Gram data as an inner product -/

/-- A Gram sum is the inner product in `EuclideanSpace`, conjugate-linear in its first argument. -/
private theorem sum_mul_conj_eq_inner (a b : κ → 𝕜) :
    ∑ u, a u * starRingEnd 𝕜 (b u) = ⟪toLp 2 b, toLp 2 a⟫_𝕜 := by
  rw [EuclideanSpace.inner_toLp_toLp]
  rfl

/-! ## The isometry on the span -/

section Span

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f g : ι → E}

/-- Equal inner products of two families give equal inner products of their combinations with the
same coefficients. -/
private theorem inner_linearCombination_eq (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜)
    (c d : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 f c, Finsupp.linearCombination 𝕜 f d⟫_𝕜 =
      ⟪Finsupp.linearCombination 𝕜 g c, Finsupp.linearCombination 𝕜 g d⟫_𝕜 := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    inner_smul_left, inner_smul_right, h]

/-- Equal inner products give combinations of equal norm. -/
private theorem norm_linearCombination_eq (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜)
    (c : ι →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜 g c‖ = ‖Finsupp.linearCombination 𝕜 f c‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜),
    inner_linearCombination_eq h c c]

/-- A combination of `f` that vanishes is a combination of `g` that vanishes, so the map between
the spans is well defined. -/
private theorem ker_le_ker (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜) :
    LinearMap.ker (Finsupp.linearCombination 𝕜 f) ≤
      LinearMap.ker (Finsupp.linearCombination 𝕜 g) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  rw [← norm_eq_zero, norm_linearCombination_eq h c, hc, norm_zero]

/-- The linear map from the span of `f` that sends `Σ c_i f i` to `Σ c_i g i`. -/
private noncomputable def spanMap (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜) :
    LinearMap.range (Finsupp.linearCombination 𝕜 f) →ₗ[𝕜] E :=
  ((LinearMap.ker (Finsupp.linearCombination 𝕜 f)).liftQ (Finsupp.linearCombination 𝕜 g)
    (ker_le_ker h)).comp (Finsupp.linearCombination 𝕜 f).quotKerEquivRange.symm.toLinearMap

private theorem spanMap_apply (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜) (c : ι →₀ 𝕜) :
    spanMap h ⟨Finsupp.linearCombination 𝕜 f c, LinearMap.mem_range_self _ c⟩ =
      Finsupp.linearCombination 𝕜 g c := by
  simp only [spanMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- `spanMap` keeps norms, so it is a linear isometry from the span of `f`. -/
private noncomputable def spanIsometry (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜) :
    LinearMap.range (Finsupp.linearCombination 𝕜 f) →ₗᵢ[𝕜] E where
  toLinearMap := spanMap h
  norm_map' := by
    rintro ⟨_, c, rfl⟩
    rw [spanMap_apply h c, norm_linearCombination_eq h c]
    rfl

private theorem apply_mem_range (x : ι) :
    f x ∈ LinearMap.range (Finsupp.linearCombination 𝕜 f) :=
  ⟨Finsupp.single x 1, by rw [Finsupp.linearCombination_single, one_smul]⟩

private theorem spanIsometry_apply (h : ∀ i j, ⟪f i, f j⟫_𝕜 = ⟪g i, g j⟫_𝕜) (x : ι) :
    spanIsometry h ⟨f x, apply_mem_range x⟩ = g x := by
  have hx := spanMap_apply h (Finsupp.single x 1)
  simp only [Finsupp.linearCombination_single, one_smul] at hx
  exact hx

end Span

/-! ## Equal Gram data exactly when a unitary carries one family to the other -/

/-- **Equal Gram data gives a unitary.** If `v` and `w` have the same Gram data
`Σ_u v x u · conj (v y u)` at every pair `x, y`, one unitary matrix carries every `v x` to `w x`.
The unitary is unique only when the `v x` span `𝕜^κ`. -/
theorem exists_isometry_of_gram_eq [DecidableEq κ] (v w : ι → κ → 𝕜)
    (h : ∀ x y, ∑ u, v x u * starRingEnd 𝕜 (v y u) = ∑ u, w x u * starRingEnd 𝕜 (w y u)) :
    ∃ U ∈ Matrix.unitaryGroup κ 𝕜, ∀ x, Matrix.mulVec U (v x) = w x := by
  have hvw : ∀ i j, ⟪toLp 2 (v i), toLp 2 (v j)⟫_𝕜 = ⟪toLp 2 (w i), toLp 2 (w j)⟫_𝕜 :=
    fun i j => by rw [← sum_mul_conj_eq_inner, ← sum_mul_conj_eq_inner, h]
  let extension := ((spanIsometry hvw).extend).toLinearIsometryEquiv rfl
  let basis := EuclideanSpace.basisFun κ 𝕜
  refine ⟨_, extension.toMatrix_mem_unitaryGroup basis basis, fun x => ?_⟩
  have hx := LinearMap.toMatrix_mulVec_repr basis.toBasis basis.toBasis
    extension.toLinearEquiv.toLinearMap (toLp 2 (v x))
  have hU : extension (toLp 2 (v x)) = toLp 2 (w x) := by
    simp only [extension, LinearIsometry.coe_toLinearIsometryEquiv]
    exact (LinearIsometry.extend_apply _ ⟨_, apply_mem_range x⟩).trans (spanIsometry_apply hvw x)
  have hrepr : ∀ y : EuclideanSpace 𝕜 κ, ⇑(basis.toBasis.repr y) = ofLp y := fun y =>
    funext fun i => by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rw [hrepr, hrepr, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, hU, ofLp_toLp,
    ofLp_toLp] at hx
  exact hx

/-- **A unitary gives equal Gram data.** If one unitary matrix carries every `v x` to `w x`, then
`v` and `w` have the same Gram data `Σ_u v x u · conj (v y u)`, over any commutative star ring. -/
theorem gram_eq_of_isometry {R : Type*} [CommRing R] [StarRing R] [DecidableEq κ]
    {v w : ι → κ → R} {U : Matrix κ κ R} (hU : U ∈ Matrix.unitaryGroup κ R)
    (hvw : ∀ x, Matrix.mulVec U (v x) = w x) (x y : ι) :
    ∑ u, v x u * starRingEnd R (v y u) = ∑ u, w x u * starRingEnd R (w y u) := by
  have hsum : ∀ a b : κ → R, ∑ u, a u * starRingEnd R (b u) = dotProduct (star b) a :=
    fun a b => by
      rw [dotProduct_comm]
      rfl
  rw [hsum, hsum, ← hvw x, ← hvw y, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU,
    Matrix.vecMul_one]

end FTQCLib.Frame.Walkthrough

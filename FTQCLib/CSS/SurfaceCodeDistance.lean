/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.BasedComplex

/-!
# Lemmas for the surface codes' distance

The linear algebra behind the cut argument of `CSS/SurfaceCode.lean`, stated for any based
complex: cocycles are orthogonal to boundaries and coboundaries to cycles, and a subspace that
exceeds a smaller one by at most `t` dimensions, with `t` elements dual to `t` functionals that
vanish on the smaller one, has no element outside the smaller one on which all the functionals
vanish. On the torus the functionals are the counts mod 2 of a chain's edges on the cuts across
it, and the dual elements are the loops around it.

## Main statements

* `FTQCLib.CSS.mem_of_finrank_le_of_apply_eq_zero`: the dimension argument.
* `BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries` and
  `BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles`: the orthogonality of
  cocycles and boundaries, and of coboundaries and cycles.

## Implementation notes

Inferred, not sourced (docs/fidelity/T34.md, Claims 6 and 13): the cited paper states the
surface codes' distance without proof, and these lemmas are the general part of the inferred
cut argument.
-/

namespace FTQCLib.CSS

/-- **A dimension argument for membership.** Let `B ≤ Z` with `dim Z ≤ dim B + t`, and let `t`
functionals `φ j` vanish on `B` while `t` elements `z k` of `Z` are dual to them,
`φ j (z k) = δ_{jk}`. Then `Z = B ⊕ span z`, so an element of `Z` on which every `φ j` vanishes
lies in `B`. -/
theorem mem_of_finrank_le_of_apply_eq_zero {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (Z B : Submodule K V)
    (hBZ : B ≤ Z) (hdim : Module.finrank K Z ≤ Module.finrank K B + Fintype.card ι)
    (φ : ι → V →ₗ[K] K) (hφB : ∀ j, ∀ b ∈ B, φ j b = 0) (z : ι → V) (hz : ∀ k, z k ∈ Z)
    (hφz : ∀ j k, φ j (z k) = if j = k then 1 else 0) {v : V} (hv : v ∈ Z)
    (hφv : ∀ j, φ j v = 0) : v ∈ B := by
  have hcoef : ∀ (c : ι → K) (j : ι), φ j (∑ k, c k • z k) = c j := by
    intro c j
    simp only [map_sum, map_smul, hφz, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hS : Module.finrank K (Submodule.span K (Set.range z)) = Fintype.card ι := by
    refine finrank_span_eq_card (Fintype.linearIndependent_iff.2 fun c hc j => ?_)
    rw [← hcoef c j, hc, map_zero]
  have hinf : B ⊓ Submodule.span K (Set.range z) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxS⟩ := Submodule.mem_inf.1 hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxS
    rw [Submodule.mem_bot]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← hcoef c k, hφB k _ hxB, zero_smul]
  have hsup : B ⊔ Submodule.span K (Set.range z) = Z := by
    refine Submodule.eq_of_le_of_finrank_le (sup_le hBZ (Submodule.span_le.2 ?_)) ?_
    · rintro _ ⟨k, rfl⟩
      exact hz k
    · have h := Submodule.finrank_sup_add_finrank_inf_eq B (Submodule.span K (Set.range z))
      rw [hinf, finrank_bot, add_zero, hS] at h
      omega
  rw [← hsup] at hv
  obtain ⟨b, hb, s, hs, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hs
  have hc : ∀ k, c k = 0 := by
    intro k
    have h := hφv k
    rw [map_add, hφB k b hb, zero_add, hcoef] at h
    exact h
  have h0 : ∑ k, c k • z k = 0 := Finset.sum_eq_zero fun k _ => by rw [hc k, zero_smul]
  rw [h0, add_zero]
  exact hb

namespace BasedComplex

/-- A cocycle is orthogonal to every boundary: `u ⬝ (∂ f) = (δ u) ⬝ f = 0`. -/
theorem dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries {C : BasedComplex} {i : ℕ}
    {u b : Fin (C.cells i) → ZMod 2} (hu : u ∈ C.cocycles i) (hb : b ∈ C.boundaries i) :
    u ⬝ᵥ b = 0 := by
  rw [BasedComplex.boundaries, LinearMap.mem_range] at hb
  obtain ⟨f, rfl⟩ := hb
  rw [BasedComplex.cocycles, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    BasedComplex.coboundary] at hu
  rw [Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hu,
    zero_dotProduct]

/-- A coboundary is orthogonal to every cycle: `(δ g) ⬝ v = g ⬝ (∂ v) = 0`. -/
theorem dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles {C : BasedComplex} {i : ℕ}
    {c v : Fin (C.cells i) → ZMod 2} (hc : c ∈ C.coboundaries i) (hv : v ∈ C.cycles i) :
    c ⬝ᵥ v = 0 := by
  rw [BasedComplex.coboundaries, LinearMap.mem_range] at hc
  obtain ⟨g, rfl⟩ := hc
  rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hv,
    dotProduct_zero]

end BasedComplex

end FTQCLib.CSS

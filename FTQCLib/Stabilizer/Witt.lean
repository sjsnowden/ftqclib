/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Logical
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.unusedSectionVars false

/-! # Witt: symplectic-basis existence on `N(S)/S`

For a non-degenerate symplectic `F_2`-space, Witt's theorem says there
exists a symplectic basis: indexed families `(X̄_i, Z̄_i)` of size `k`
with `ω(X̄_i, Z̄_j) = δ_{ij}` and zero on same-type pairs.

This file contains:

* **The case `k = 1`:** `exists_symplecticPair_of_logicalQuotient_nontrivial`
  — if `L(S)` is non-trivial then at least one symplectic pair exists.
* **Helpers for the full theorem:** hyperbolic-pair existence,
  alt-symmetry, and span-orthogonal disjointness. The full theorem
  `exists_symplecticBasis_of_nondeg_alt` — the recursive construction
  yielding a basis of size `k = finrank V / 2` — is in
  `FTQCLib.Stabilizer.WittBasis`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-- **Witt (k = 1):** if `N(S)/S` is non-trivial (i.e., contains a
non-zero element), then there is at least one symplectic pair: an
`(x, y)` of cosets with `ω_{L(S)}(x, y) = 1`. -/
theorem exists_symplecticPair_of_logicalQuotient_nontrivial
    {S : Submodule (ZMod 2) (Pauli n)}
    (h : ∃ x : logicalQuotient S, x ≠ 0) :
    ∃ x y : logicalQuotient S, omegaQ x y = 1 := by
  obtain ⟨x, hx⟩ := h
  by_contra hno
  apply hx
  apply omegaQ_nondegenerate
  intro y
  have hZ2 : omegaQ x y = 0 ∨ omegaQ x y = 1 := by
    have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact this _
  rcases hZ2 with h0 | h1
  · exact h0
  · exact absurd ⟨x, y, h1⟩ hno

/-- The dual of `exists_symplecticPair_of_logicalQuotient_nontrivial`,
unfolded through `omegaQBilin`. -/
theorem omegaQBilin_ne_zero_of_logicalQuotient_nontrivial
    {S : Submodule (ZMod 2) (Pauli n)}
    (h : ∃ x : logicalQuotient S, x ≠ 0) :
    ∃ x y : logicalQuotient S, omegaQBilin S x y = 1 := by
  obtain ⟨x, y, hxy⟩ := exists_symplecticPair_of_logicalQuotient_nontrivial h
  induction x using Quotient.inductionOn with
  | _ x_rep =>
  induction y using Quotient.inductionOn with
  | _ y_rep =>
    refine ⟨Submodule.Quotient.mk x_rep, Submodule.Quotient.mk y_rep, ?_⟩
    exact hxy

/-! ## Helper lemmas for the inductive construction -/

section Witt

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- For a non-degenerate bilinear form `B` and a non-zero `v`, there
exists `w` with `B v w = 1`. Specialised to `ZMod 2` where the only
non-zero value is 1. -/
lemma exists_pair_eq_one
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hN : LinearMap.BilinForm.Nondegenerate B)
    {v : V} (hv : v ≠ 0) :
    ∃ w : V, B v w = 1 := by
  by_contra hno
  apply hv
  apply hN.1
  intro y
  have hZ2 : B v y = 0 ∨ B v y = 1 := by
    have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact this _
  rcases hZ2 with h0 | h1
  · exact h0
  · exact absurd ⟨y, h1⟩ hno

/-- In characteristic 2 with an alternating bilinear form, `B w v = B v w`:
the symmetry sign disappears. -/
lemma BilinForm_alt_symm
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hA : B.IsAlt)
    (v w : V) : B w v = B v w := by
  have h_neg : -B v w = B w v := LinearMap.BilinForm.IsAlt.neg_eq hA v w
  rw [show (-B v w : ZMod 2) = B v w from CharTwo.neg_eq _] at h_neg
  exact h_neg.symm

/-- If `B v w = 1` and `B` is alternating, then `span{v, w}` and its
`B`-orthogonal complement are disjoint as `F_2`-submodules. -/
lemma disjoint_span_pair_orthogonal
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hA : B.IsAlt)
    {v w : V} (h : B v w = 1) :
    Disjoint (Submodule.span (ZMod 2) {v, w})
             (LinearMap.BilinForm.orthogonal B
                (Submodule.span (ZMod 2) {v, w})) := by
  rw [Submodule.disjoint_def]
  intro x hx_span hx_ortho
  rw [Submodule.mem_span_pair] at hx_span
  obtain ⟨a, b, rfl⟩ := hx_span
  have hv_mem : v ∈ Submodule.span (ZMod 2) {v, w} :=
    Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩
  have hw_mem : w ∈ Submodule.span (ZMod 2) {v, w} :=
    Submodule.mem_span_pair.mpr ⟨0, 1, by simp⟩
  have h_vx : B v (a • v + b • w) = 0 := hx_ortho v hv_mem
  have h_wx : B w (a • v + b • w) = 0 := hx_ortho w hw_mem
  have h_wv : B w v = B v w := BilinForm_alt_symm B hA v w
  have h_b : b = 0 := by
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul,
        hA.self_eq_zero v, smul_zero, zero_add,
        h, smul_eq_mul, mul_one] at h_vx
    exact h_vx
  have h_a : a = 0 := by
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul,
        hA.self_eq_zero w, smul_zero, add_zero,
        h_wv, h, smul_eq_mul, mul_one] at h_wx
    exact h_wx
  rw [h_a, h_b, zero_smul, zero_smul, add_zero]

end Witt

/-! ## Outline of the full Witt induction

The `k = 1` case (`exists_symplecticPair_of_logicalQuotient_nontrivial`)
plus the helpers above (`exists_pair_eq_one`, `BilinForm_alt_symm`,
`disjoint_span_pair_orthogonal`) supply the inductive step of the full
Witt theorem, carried out in `FTQCLib.Stabilizer.WittBasis`:

1. Pick non-zero `v ∈ V` (using `Module.finrank V > 0` ⇒ `Nontrivial V`).
2. Apply `exists_pair_eq_one` to obtain `w` with `B v w = 1`.
3. Let `W := Submodule.span (ZMod 2) {v, w}`; show `finrank W = 2`.
4. Apply `disjoint_span_pair_orthogonal` to get
   `Disjoint W (B.orthogonal W)`.
5. Apply Mathlib's `nondegenerate_restrict_of_disjoint_orthogonal` to
   get `(B.restrict W).Nondegenerate`.
6. Apply Mathlib's `isCompl_orthogonal_of_restrict_nondegenerate` (with
   `hA.isRefl`) to get `IsCompl W (B.orthogonal W)`.
7. Compute `finrank (B.orthogonal W) = finrank V − 2` via
   Mathlib's `finrank_orthogonal`.
8. Establish `(B.restrict (B.orthogonal W)).Nondegenerate` (use the
   symmetric `Disjoint` derived from `orthogonal_orthogonal`).
9. Strong-induct on `finrank V`: recurse on `↥(B.orthogonal W)` with
   `B.restrict (B.orthogonal W)` (non-deg alternating, finrank `n−2`).
10. Combine the recursively-found basis with `(v, w)` via
    `Fin.cons` to obtain a symplectic basis of size `k+1` for `V`.

Steps 3 (concrete finrank of a two-element span) and 10 (the `Fin.cons`
glue plus four case-splits verifying the symplectic-pair conditions) are
in `FTQCLib.Stabilizer.WittSpanPair` and `FTQCLib.Stabilizer.WittFinCons`.
-/

end FTQCLib.Stabilizer

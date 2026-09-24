/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Witt
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.Finite.Basic

set_option linter.unusedSectionVars false

/-! # Restriction of a non-degenerate alternating form to an orthogonal complement

This file provides the missing inductive-step ingredient for Witt's theorem:
if `B` is a non-degenerate alternating bilinear form on a finite-dimensional
`F_2`-vector space and `W` is a subspace with `W ∩ W^⊥ = 0`, then the
restriction of `B` to `W^⊥` is again non-degenerate.

The proof passes through the double-orthogonal identity
`B^⊥(B^⊥(W)) = W` (valid for non-degenerate reflexive forms on finite-dim
spaces) so that disjointness of `W^⊥` and `W^⊥⊥` reduces to the given
`Disjoint W (B.orthogonal W)`.
-/

namespace FTQCLib.Stabilizer

/-- If `B` is a non-degenerate alternating bilinear form on a
finite-dimensional `F_2`-space `V` and `W ⊆ V` satisfies
`W ⊓ B.orthogonal W = 0`, then `B` restricted to `B.orthogonal W` is also
non-degenerate. This is the symmetric counterpart of Mathlib's
`nondegenerate_restrict_of_disjoint_orthogonal`, obtained via the
double-orthogonal-complement identity. -/
theorem nondegenerate_restrict_orthogonal_of_disjoint
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hN : LinearMap.BilinForm.Nondegenerate B) (hA : B.IsAlt)
    (W : Submodule (ZMod 2) V)
    (hDisj : Disjoint W (LinearMap.BilinForm.orthogonal B W)) :
    (LinearMap.BilinForm.restrict B (LinearMap.BilinForm.orthogonal B W)).Nondegenerate := by
  have hRefl : B.IsRefl := hA.isRefl
  -- Double-orthogonal identity: `B^⊥(B^⊥(W)) = W`.
  have hDouble : LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B W) = W :=
    LinearMap.BilinForm.orthogonal_orthogonal hN hRefl W
  -- Disjointness is symmetric.
  have hDisj' : Disjoint (LinearMap.BilinForm.orthogonal B W) W := hDisj.symm
  -- Substitute the double-orthogonal identity to rewrite `W` as `B^⊥(B^⊥(W))`.
  have hDisj'' :
      Disjoint (LinearMap.BilinForm.orthogonal B W)
               (LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B W)) := by
    rw [hDouble]
    exact hDisj'
  -- Apply Mathlib's `nondegenerate_restrict_of_disjoint_orthogonal` with
  -- `W' := B.orthogonal W`.
  exact LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B hRefl hDisj''

end FTQCLib.Stabilizer

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Witt
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.unusedSectionVars false

/-! # `finrank` of a symplectic pair span

If `B` is an alternating bilinear form on a `ZMod 2`-module `V` and
`B v w = 1`, then `v` and `w` are linearly independent, so the span
`Submodule.span (ZMod 2) {v, w}` has rank exactly `2`. This is step
(3) of the Witt-recursion outline in `FTQCLib/Stabilizer/Witt.lean`.

The proof has two parts:

1. `LinearIndependent.pair_iff` reduces linear independence of
   `![v, w]` to: for all `s t : ZMod 2`, `s • v + t • w = 0` forces
   `s = t = 0`. Applying `B v ·` and `B w ·` to the relation and
   using `hA.self_eq_zero`, `B v w = 1`, and the char-2 alt-symmetry
   `BilinForm_alt_symm` gives `s = t = 0` directly.

2. `finrank_span_eq_card` converts the rank of the span of a linearly
   independent family of size `2` to `2`, after rewriting
   `({v, w} : Set V) = Set.range ![v, w]` via `Matrix.range_cons` and
   `Matrix.range_empty`.
-/

namespace FTQCLib.Stabilizer

open Submodule Module Matrix

section Witt

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `v` and `w` are linearly independent whenever `B v w = 1` and `B`
is alternating. Computed by applying `B v ·` and `B w ·` to the
relation `s • v + t • w = 0`. -/
lemma linearIndependent_pair_of_pair_eq_one
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hA : B.IsAlt)
    {v w : V} (h : B v w = 1) :
    LinearIndependent (ZMod 2) ![v, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h_wv : B w v = B v w := BilinForm_alt_symm B hA v w
  have h_v : t = 0 := by
    have := congrArg (B v) hst
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul,
        hA.self_eq_zero v, smul_zero, zero_add, h, smul_eq_mul, mul_one,
        map_zero] at this
    exact this
  have h_w : s = 0 := by
    have := congrArg (B w) hst
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul,
        hA.self_eq_zero w, smul_zero, add_zero,
        h_wv, h, smul_eq_mul, mul_one, map_zero] at this
    exact this
  exact ⟨h_w, h_v⟩

/-- **Witt step 3:** If `B v w = 1` for an alternating bilinear form
`B` on a `ZMod 2`-module, then `Submodule.span (ZMod 2) {v, w}` has
`finrank` equal to `2`. -/
theorem finrank_span_pair_of_pair_eq_one
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hA : B.IsAlt)
    {v w : V} (h : B v w = 1) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v, w} : Set V)) = 2 := by
  have h_li : LinearIndependent (ZMod 2) ![v, w] :=
    linearIndependent_pair_of_pair_eq_one B hA h
  have h_range : ({v, w} : Set V) = Set.range ![v, w] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
        Set.union_empty, Set.singleton_union]
  rw [h_range]
  have h_card : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![v, w])) =
      Fintype.card (Fin 2) := finrank_span_eq_card h_li
  rw [h_card, Fintype.card_fin]

end Witt

end FTQCLib.Stabilizer

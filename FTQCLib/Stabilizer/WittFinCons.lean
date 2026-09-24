/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Witt

set_option linter.unusedSectionVars false

/-! # WittFinCons: extending a symplectic basis by a hyperbolic pair

This file supplies the `Fin.cons` glue lemma that combines a hyperbolic
pair `(v, w)` with a size-`k` symplectic basis on a disjoint subspace
into a size-`k+1` symplectic basis.

Used by the inductive step of full Witt (`exists_symplecticBasis_of_nondeg_alt`)
in `FTQCLib.Stabilizer.Witt`.
-/

namespace FTQCLib.Stabilizer

/-- **Witt inductive step glue.**

Given a size-`k` symplectic basis `(e', f')` and a hyperbolic pair
`(v, w)` such that `v` and `w` are `B`-orthogonal to all of `e' i`
and `f' i`, produce a size-`k+1` symplectic basis `(e, f)` with
`e 0 = v`, `f 0 = w`, `e i.succ = e' i`, `f i.succ = f' i`.

This is purely the `Fin.cons` combinator plus four case splits on
`(i, j) ∈ {(0, 0), (0, succ), (succ, 0), (succ, succ)}`. -/
theorem extend_symplecticBasis
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hA : B.IsAlt)
    {k : ℕ} {e' f' : Fin k → V} {v w : V}
    (hvw : B v w = 1)
    (hve : ∀ i, B v (e' i) = 0)
    (hvf : ∀ i, B v (f' i) = 0)
    (hwe : ∀ i, B w (e' i) = 0)
    (hwf : ∀ i, B w (f' i) = 0)
    (hef : ∀ i j, B (e' i) (f' j) = if i = j then 1 else 0)
    (hee : ∀ i j, B (e' i) (e' j) = 0)
    (hff : ∀ i j, B (f' i) (f' j) = 0) :
    ∃ e f : Fin (k + 1) → V,
      e 0 = v ∧ f 0 = w ∧
      (∀ i : Fin k, e i.succ = e' i) ∧ (∀ i : Fin k, f i.succ = f' i) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (f i) (f j) = 0) := by
  refine ⟨Fin.cons v e', Fin.cons w f', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cons_zero _ _
  · exact Fin.cons_zero _ _
  · intro i; exact Fin.cons_succ _ _ _
  · intro i; exact Fin.cons_succ _ _ _
  · -- symplectic-pair condition `B (e i) (f j) = δ_{ij}`
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, if_true]
        exact hvw
      | succ j' =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hne : (0 : Fin (k + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
        rw [if_neg hne]
        exact hvf j'
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hne : (i'.succ : Fin (k + 1)) ≠ 0 := Fin.succ_ne_zero i'
        rw [if_neg hne]
        -- goal: B (e' i') w = 0; use alt-symmetry then hwe
        rw [BilinForm_alt_symm B hA]
        exact hwe i'
      | succ j' =>
        simp only [Fin.cons_succ]
        rw [hef i' j']
        by_cases hij : i' = j'
        · subst hij
          rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hij, if_neg (fun h => hij (Fin.succ_injective k h))]
  · -- isotropy on e: `B (e i) (e j) = 0`
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact hA.self_eq_zero v
      | succ j' =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact hve j'
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        -- goal: B (e' i') v = 0; use alt-symmetry then hve
        rw [BilinForm_alt_symm B hA]
        exact hve i'
      | succ j' =>
        simp only [Fin.cons_succ]
        exact hee i' j'
  · -- isotropy on f: `B (f i) (f j) = 0`
    intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact hA.self_eq_zero w
      | succ j' =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact hwf j'
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        -- goal: B (f' i') w = 0; use alt-symmetry then hwf
        rw [BilinForm_alt_symm B hA]
        exact hwf i'
      | succ j' =>
        simp only [Fin.cons_succ]
        exact hff i' j'

end FTQCLib.Stabilizer

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Elements

/-! # Equivariant bijections induce equivalences of action groupoids (frame-pure)

Reusable, frame-pure heart of the **Clifford-equivariant floor upgrade** (the floor chart of
`SCat ≌ OCat`): an `M`-equivariant bijection `e : X ≃ Y` lifts to an equivalence of action
categories `ActionCategory M X ≌ ActionCategory M Y`.

`FTQCLib/Hilbert/CategoricalEquivalence.lean` built this by hand for the single bijection
`stabProjector`. Here it is the general statement (Mathlib has `CategoryOfElements.map` but not this
packaged form), so any future equivariant bijection — the floor's `(L,χ) ↔ floor` map once a
frame-native gate action exists — plugs in. No `FTQCLib.Hilbert` import: pure category theory. -/

namespace FTQCLib.Frame

open CategoryTheory

universe u

variable {M : Type*} [Monoid M] {X Y : Type u} [MulAction M X] [MulAction M Y]

/-- An `M`-equivariant bijection `e : X ≃ Y`, packaged as a natural transformation of the two action
functors. Its single naturality square **is** equivariance. -/
def equivariantNat (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    actionAsFunctor M X ⟶ actionAsFunctor M Y where
  app _ := ⇑e
  naturality _ _ g := by funext x; exact he g x

@[simp] theorem equivariantNat_app (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) (x) :
    (equivariantNat e he).app x = ⇑e := rfl

/-- The functor `ActionCategory M X ⥤ ActionCategory M Y` induced by an equivariant bijection: on
objects `x ↦ e x`, identity on the underlying group element of each morphism. -/
def actionFunctorOfEquiv (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    ActionCategory M X ⥤ ActionCategory M Y :=
  CategoryOfElements.map (equivariantNat e he)

instance (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    (actionFunctorOfEquiv e he).Faithful where
  map_injective h := Subtype.ext (congrArg (·.1) h)

instance (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    (actionFunctorOfEquiv e he).Full where
  map_surjective {A B} k := by
    refine ⟨⟨k.1, ?_⟩, Subtype.ext rfl⟩
    apply e.injective
    have hnat := congr_fun ((equivariantNat e he).naturality k.1) A.2
    simp only [types_comp_apply, equivariantNat_app] at hnat
    exact hnat.trans k.2

instance (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    (actionFunctorOfEquiv e he).EssSurj where
  mem_essImage B := by
    refine ⟨⟨B.1, e.symm B.2⟩, ⟨eqToIso ?_⟩⟩
    exact congrArg (fun y => (⟨B.1, y⟩ : ActionCategory M Y)) (e.apply_symm_apply B.2)

instance (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    (actionFunctorOfEquiv e he).IsEquivalence where

/-- **Equivariant bijection ⟹ equivalence of action groupoids.** An `M`-equivariant bijection
`e : X ≃ Y` induces `ActionCategory M X ≌ ActionCategory M Y`. The assembler the floor chart plugs
into: with a frame-native gate action and the floor `↔ (L,χ)` equivariant bijection, it yields the
floor chart of `SCat ≌ OCat`. -/
noncomputable def actionCategoryCongr (e : X ≃ Y) (he : ∀ (m : M) (x : X), e (m • x) = m • e x) :
    ActionCategory M X ≌ ActionCategory M Y :=
  (actionFunctorOfEquiv e he).asEquivalence

end FTQCLib.Frame

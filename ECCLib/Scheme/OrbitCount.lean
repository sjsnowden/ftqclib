/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Orbits
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finite.Card

/-!
# Transitivity on the nonzero elements, as an orbit count

A group acting on an abelian group always fixes `0`, so `{0}` is an orbit by itself.
Transitivity on everything else therefore says exactly that there are **two** orbits, and
that is the form in which transitivity can be compared across a duality — orbit counts are
numbers, and numbers transport where elements do not.

* `TransOnNonzero` is the predicate (moved here from the Hamming layer, which is not its
  home: it mentions no coordinates and no weights).
* `transOnNonzero_iff_isPretransitive` reads it as Mathlib's `IsPretransitive` on the
  subtype of nonzero elements, so Mathlib's API applies (the restricted action is a
  parameter, not a new instance — see the note there).
* `transOnNonzero_iff_card_orbits_eq_two` is the orbit-count form.
* `quotientOrbitsEquiv` identifies Mathlib's `orbitRel.Quotient` — which carries no `Fintype`
  instance, the reason `Orbits.lean` built its own `Finset` of orbits — with that `Finset`,
  so an abstract orbit count can be checked by kernel computation.

Nothing here mentions characters.

## Main definitions

* `TransOnNonzero` — transitivity of a group on the nonzero elements of an abelian group.
* `quotientOrbitsEquiv` — Mathlib's orbit quotient as the `Finset` of orbits.

## Main results

* `transOnNonzero_iff_isPretransitive` — the Mathlib-native reading.
* `transOnNonzero_iff_card_orbits_eq_two` — transitivity on the nonzero elements is having
  two orbits.
* `card_orbitRel_quotient` — the abstract orbit count is the computable one.

## Implementation notes

`TransOnNonzero` lives here rather than in the Hamming layer that first used it: it mentions
no coordinates and no weights. The restricted action in `transOnNonzero_iff_isPretransitive`
is a parameter with a compatibility hypothesis, not an instance — Mathlib already carries
`MulAction Mˣ {w // w ≠ 0}`, and a bespoke instance collides with it.
-/

namespace ECCLib.Scheme

open MulAction

variable {W : Type*} [AddCommGroup W] {G : Type*} [Group G] [DistribMulAction G W]

/-! ## The predicate -/

/-- Transitivity of a group on the nonzero elements of an abelian group. -/
def TransOnNonzero (G : Type*) [Group G] (A : Type*) [AddCommGroup A]
    [DistribMulAction G A] : Prop :=
  ∀ a b : A, a ≠ 0 → b ≠ 0 → ∃ g : G, g • a = b

/-- **The Mathlib-native reading**: transitivity on the nonzero elements is pretransitivity of
the action restricted to them.

The restricted action is taken as a PARAMETER, with a compatibility hypothesis, rather than
declared here: Mathlib already carries
`MulAction Mˣ {w // w ≠ 0}` for a monoid acting on a ring, so a bespoke instance collides at
exactly the alphabets this development uses (`OrbitCountCheck` instantiates this against
Mathlib's own instance, where the compatibility is `rfl`). -/
theorem transOnNonzero_iff_isPretransitive [MulAction G {w : W // w ≠ 0}]
    (hcompat : ∀ (g : G) (w : {w : W // w ≠ 0}), ((g • w : {w : W // w ≠ 0}) : W) = g • (w : W)) :
    TransOnNonzero G W ↔ IsPretransitive G {w : W // w ≠ 0} := by
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, hg⟩ := h a b a.2 b.2
    exact ⟨g, Subtype.ext ((hcompat g a).trans hg)⟩
  · rintro ⟨h⟩ a b ha hb
    obtain ⟨g, hg⟩ := h ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨g, ((hcompat g ⟨a, ha⟩).symm.trans (congrArg Subtype.val hg))⟩

/-! ## The orbit count -/

/-- The class of `0` contains nothing else: every `g` fixes `0`, so its orbit is `{0}`. -/
theorem quotient_eq_zero_iff (w : W) :
    (Quotient.mk'' w : orbitRel.Quotient G W) = Quotient.mk'' 0 ↔ w = 0 := by
  rw [Quotient.eq'', orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    rw [smul_zero] at hg
    exact hg.symm
  · rintro rfl
    exact ⟨1, by simp⟩

/-- **Transitivity on the nonzero elements is exactly having two orbits.** One orbit is
`{0}`; transitivity says the complement is the other. The hypothesis `2 ≤ |W|` is what makes
the complement nonempty, so that the count is `2` rather than `1`. -/
theorem transOnNonzero_iff_card_orbits_eq_two [Finite W] (h2 : 2 ≤ Nat.card W) :
    TransOnNonzero G W ↔ Nat.card (orbitRel.Quotient G W) = 2 := by
  classical
  have hnt : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨w₀, hw₀⟩ : ∃ w : W, w ≠ 0 := exists_ne 0
  rw [Nat.card_eq_two_iff' (Quotient.mk'' (0 : W) : orbitRel.Quotient G W)]
  constructor
  · intro htr
    refine ⟨Quotient.mk'' w₀, fun hcon => hw₀ ((quotient_eq_zero_iff w₀).mp hcon), ?_⟩
    intro y hy
    induction y using Quotient.inductionOn' with
    | h w =>
      have hw : w ≠ 0 := fun hcon => hy ((quotient_eq_zero_iff (G := G) w).mpr hcon)
      obtain ⟨g, hg⟩ := htr w₀ w hw₀ hw
      rw [Quotient.eq'', orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, hg⟩
  · rintro ⟨y, -, huniq⟩ a b ha hb
    have hA : (Quotient.mk'' a : orbitRel.Quotient G W) = y :=
      huniq _ fun hcon => ha ((quotient_eq_zero_iff a).mp hcon)
    have hB : (Quotient.mk'' b : orbitRel.Quotient G W) = y :=
      huniq _ fun hcon => hb ((quotient_eq_zero_iff b).mp hcon)
    have hab : (Quotient.mk'' a : orbitRel.Quotient G W) = Quotient.mk'' b := hA.trans hB.symm
    rw [Quotient.eq'', orbitRel_apply, MulAction.mem_orbit_iff] at hab
    obtain ⟨g, hg⟩ := hab
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/-! ## The bridge to Mathlib's orbit quotient

`quotientOrbitsEquiv` and `card_orbitRel_quotient` used to live here, under this file's
`[AddCommGroup W]` / `[DistribMulAction G W]` context. They need neither, and that context made
them unusable for any carrier without additive structure. They now sit in `Scheme/Orbits.lean`
at a bare `MulAction`; their full names are unchanged, so consumers are unaffected. -/

end ECCLib.Scheme

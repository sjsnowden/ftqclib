/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Annihilator

/-!
# Acceptance checks for the annihilator layer

No `decide` rows: every statement here is indexed by characters, whose `Fintype`/`DecidableEq`
instances are Mathlib's classical ones. Acceptance is the axiom sweep plus the rows below.

**The agreement row.** Read at `H = ⊥`, the closure identity `H^⊥⊥ = H` says: a vector on
which *every* character is trivial is `0`. Mathlib proves that independently, from the
existence of a complex basis of characters (`AddChar.forall_apply_eq_zero`). Deriving it from
the correspondence checks the correspondence against a different proof of the same fact —
and it is the sharpest such check available, since it is exactly the separation statement the
counting argument never makes directly.

**The consistency rows.** The correspondence must carry the extreme subgroups to each other
in both directions; `charAnnihSubgroup_bot`/`_top` are proved by hand, and the pre-annihilator
versions are then forced.
-/

namespace ECCLib

/-- **The agreement row.** Separation, derived from `H^⊥⊥ = H` at `H = ⊥`. -/
example {V : Type*} [AddCommGroup V] [Finite V] (a : V) (h : ∀ χ : AddChar V ℂ, χ a = 1) :
    a = 0 := by
  have hmem : a ∈ charAnnihPre (charAnnihSubgroup (⊥ : AddSubgroup V)) := by
    rw [charAnnihSubgroup_bot]
    exact fun χ _ => h χ
  rwa [charAnnihPre_charAnnihSubgroup, AddSubgroup.mem_bot] at hmem

/-- The same statement as Mathlib proves it, for comparison. -/
example {V : Type*} [AddCommGroup V] [Finite V] (a : V) (h : ∀ χ : AddChar V ℂ, χ a = 1) :
    a = 0 := AddChar.forall_apply_eq_zero.mp h

/-- **Consistency row.** The pre-annihilator of everything is trivial — forced by the
correspondence together with `charAnnihSubgroup_bot`, not proved separately. -/
example {V : Type*} [AddCommGroup V] [Finite V] :
    charAnnihPre (⊤ : AddSubgroup (AddChar V ℂ)) = (⊥ : AddSubgroup V) := by
  rw [← charAnnihSubgroup_bot (V := V), charAnnihPre_charAnnihSubgroup]

/-- **Consistency row.** The pre-annihilator of the trivial subgroup is everything. -/
example {V : Type*} [AddCommGroup V] [Finite V] :
    charAnnihPre (⊥ : AddSubgroup (AddChar V ℂ)) = (⊤ : AddSubgroup V) := by
  rw [← charAnnihSubgroup_top (V := V), charAnnihPre_charAnnihSubgroup]

/-- **The lattice bijection is a bijection**, in both roundtrip directions. -/
example {V : Type*} [AddCommGroup V] [Finite V] (H : AddSubgroup V) :
    charAnnihEquiv.symm (charAnnihEquiv H) = H := charAnnihEquiv.left_inv H

example {V : Type*} [AddCommGroup V] [Finite V] (S : AddSubgroup (AddChar V ℂ)) :
    charAnnihEquiv (charAnnihEquiv.symm S) = S := charAnnihEquiv.right_inv S

/-- **The size relations agree at the extremes**: `|⊥^⊥| = |V̂| = |V|`. -/
example {V : Type*} [AddCommGroup V] [Fintype V] :
    Nat.card (charAnnihSubgroup (⊥ : AddSubgroup V)) = Fintype.card V := by
  rw [charAnnihSubgroup_bot, AddSubgroup.card_top, Nat.card_eq_fintype_card, AddChar.card_eq]

end ECCLib

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.sum_char_over_subgroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_char_over_subgroup

/-- info: 'ECCLib.card_annihilator_mul_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_annihilator_mul_card

/-- info: 'ECCLib.card_charAnnihSubgroup_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_charAnnihSubgroup_mul

/-- info: 'ECCLib.card_charAnnihPre_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_charAnnihPre_mul

/-- info: 'ECCLib.charAnnihPre_charAnnihSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.charAnnihPre_charAnnihSubgroup

/-- info: 'ECCLib.charAnnihSubgroup_charAnnihPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.charAnnihSubgroup_charAnnihPre

/-- info: 'ECCLib.charAnnihEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.charAnnihEquiv

/-- info: 'ECCLib.card_ker_mul_card_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_ker_mul_card_range

/-- info: 'ECCLib.card_charAnnihSubgroup_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_charAnnihSubgroup_range

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# The character annihilator, and the duality of subgroup lattices

For a finite abelian group `V` and a subgroup `H ≤ V`, the **annihilator** `H^⊥` is the set of
characters trivial on `H`. Dually, a subgroup `S` of the dual has a **pre-annihilator** `S^⊥`
back inside `V`. This module builds both as subgroups, proves the size relations, and closes
the correspondence: the two operations are mutually inverse, so the subgroup lattices of `V`
and of its dual are in order-reversing bijection (`charAnnihEquiv`).

Everything rests on one lemma, **restricted character orthogonality**
`sum_char_over_subgroup` (Delsarte 1973, Thm 6.2): summing a character over a subgroup gives
`|H|` when the character is trivial there and `0` otherwise. Both size relations are that
lemma double-counted, the second one against `AddChar.doubleDualEmb`; no quotient character
theory is used anywhere, which is what keeps the module elementary.

`charAnnih` is the `Finset` view of `charAnnihSubgroup`, kept because the coding layer
counts with it. The two agree on the nose (`coe_charAnnih`, `card_charAnnihSubgroup`).

This module imports no `ECCLib.*` and no Fourier transform — it is a leaf over
Mathlib, and `ECCLib.PoissonSummation` builds on it rather than the other way round.

## Main definitions

* `charAnnihSubgroup` — the annihilator `H^⊥` of a subgroup, as a subgroup of the dual.
* `charAnnihPre` — the pre-annihilator `S^⊥` of a subgroup of the dual, back inside `V`.
* `charAnnih` — the `Finset` view of `charAnnihSubgroup`, for counting.
* `charAnnihEquiv` — the resulting bijection of subgroup lattices.

## Main results

* `sum_char_over_subgroup` — restricted character orthogonality.
* `card_charAnnihSubgroup_mul` / `card_charAnnihPre_mul` — the two size relations.
* `charAnnihPre_charAnnihSubgroup` / `charAnnihSubgroup_charAnnihPre` — `H^⊥⊥ = H`, both sides.
* `card_charAnnihSubgroup_range` — annihilating an image counts the kernel.

## Implementation notes

Both closure identities are proved by counting: the composite contains the original and has
the same size. No separating character is ever produced, which is what keeps the module free
of quotient character theory.

The module is split into four sections by instance need — `Defs` (no finiteness),
`WithFintype`, `WithFinite`, `FinsetView` — so the definitions and the adjunction inequalities
hold with no finiteness hypothesis at all.

## References

Delsarte 1973, Theorem 6.2, for restricted character orthogonality.
-/

namespace ECCLib

open scoped BigOperators
open Finset

/-! ## The annihilator, as a subgroup of the dual

No finiteness is needed to define it, or to see that it reverses inclusions and swaps the
extreme subgroups. -/

section Defs

variable {V : Type*} [AddCommGroup V]

/-- The **character annihilator** `H^⊥` of a subgroup `H ≤ V`: the characters trivial on `H`. -/
def charAnnihSubgroup (H : AddSubgroup V) : AddSubgroup (AddChar V ℂ) where
  carrier := {χ | ∀ h ∈ H, χ h = 1}
  zero_mem' := fun h _ => by simp
  add_mem' := fun {χ η} hχ hη h hh => by
    rw [AddChar.add_apply, hχ h hh, hη h hh, one_mul]
  neg_mem' := fun {χ} hχ h hh => by
    rw [AddChar.neg_apply', hχ h hh, inv_one]

@[simp] theorem mem_charAnnihSubgroup {H : AddSubgroup V} {χ : AddChar V ℂ} :
    χ ∈ charAnnihSubgroup H ↔ ∀ h ∈ H, χ h = 1 := Iff.rfl

theorem charAnnihSubgroup_antitone {H K : AddSubgroup V} (h : H ≤ K) :
    charAnnihSubgroup K ≤ charAnnihSubgroup H :=
  fun _ hχ x hx => hχ x (h hx)

@[simp] theorem charAnnihSubgroup_bot :
    charAnnihSubgroup (⊥ : AddSubgroup V) = ⊤ := by
  ext χ
  simp only [mem_charAnnihSubgroup, AddSubgroup.mem_top, iff_true]
  intro h hh
  rw [AddSubgroup.mem_bot.mp hh]
  simp

@[simp] theorem charAnnihSubgroup_top :
    charAnnihSubgroup (⊤ : AddSubgroup V) = ⊥ := by
  ext χ
  rw [mem_charAnnihSubgroup, AddSubgroup.mem_bot]
  constructor
  · intro hχ
    ext x
    rw [hχ x (AddSubgroup.mem_top x), AddChar.zero_apply]
  · rintro rfl x _
    exact AddChar.zero_apply x

/-- The **pre-annihilator** `S^⊥` of a subgroup `S` of the dual: the vectors killed by every
character in `S`. -/
def charAnnihPre (S : AddSubgroup (AddChar V ℂ)) : AddSubgroup V where
  carrier := {a | ∀ χ ∈ S, χ a = 1}
  zero_mem' := fun χ _ => by simp
  add_mem' := fun {a b} ha hb χ hχ => by
    rw [χ.map_add_eq_mul, ha χ hχ, hb χ hχ, one_mul]
  neg_mem' := fun {a} ha χ hχ => by
    rw [χ.map_neg_eq_inv, ha χ hχ, inv_one]

@[simp] theorem mem_charAnnihPre {S : AddSubgroup (AddChar V ℂ)} {a : V} :
    a ∈ charAnnihPre S ↔ ∀ χ ∈ S, χ a = 1 := Iff.rfl

theorem charAnnihPre_antitone {S T : AddSubgroup (AddChar V ℂ)} (h : S ≤ T) :
    charAnnihPre T ≤ charAnnihPre S :=
  fun _ ha χ hχ => ha χ (h hχ)

/-- Half of the Galois connection: a subgroup lies inside the pre-annihilator of its
annihilator. (The reverse inclusion is `charAnnihPre_charAnnihSubgroup`, and needs counting.) -/
theorem le_charAnnihPre_charAnnihSubgroup (H : AddSubgroup V) :
    H ≤ charAnnihPre (charAnnihSubgroup H) :=
  fun _ hh _ hχ => hχ _ hh

/-- The same, read on the dual side. -/
theorem le_charAnnihSubgroup_charAnnihPre (S : AddSubgroup (AddChar V ℂ)) :
    S ≤ charAnnihSubgroup (charAnnihPre S) :=
  fun _ hχ _ ha => ha _ hχ

end Defs

/-! ## The `Finset` view

Kept because the coding layer counts with it, and because `Finset` membership is what the
existing consumers (`ECCLib.Codes`) are written against. -/

section WithFintype

variable {V : Type*} [AddCommGroup V] [Fintype V]

open Classical in
/-- The annihilator as a `Finset`, for counting. Agrees with `charAnnihSubgroup` on the
nose (`coe_charAnnih`). -/
noncomputable def charAnnih (H : AddSubgroup V) : Finset (AddChar V ℂ) :=
  Finset.univ.filter (fun ξ => ∀ h ∈ H, ξ h = 1)

open Classical in
@[simp] theorem mem_charAnnih {H : AddSubgroup V} {ξ : AddChar V ℂ} :
    ξ ∈ charAnnih H ↔ ∀ h ∈ H, ξ h = 1 := by
  simp [charAnnih]

open Classical in
theorem coe_charAnnih (H : AddSubgroup V) :
    (charAnnih H : Set (AddChar V ℂ)) = charAnnihSubgroup H := by
  ext ξ
  simp

open Classical in
theorem card_charAnnihSubgroup (H : AddSubgroup V) :
    Nat.card (charAnnihSubgroup H) = (charAnnih H).card := by
  rw [← SetLike.coe_sort_coe, ← coe_charAnnih, Finset.coe_sort_coe, Nat.card_eq_finsetCard]

open Classical in
@[simp] theorem one_mem_charAnnih (H : AddSubgroup V) : (1 : AddChar V ℂ) ∈ charAnnih H := by
  simp [mem_charAnnih, AddChar.one_apply]

open Classical in
theorem charAnnih_antitone {H K : AddSubgroup V} (h : H ≤ K) : charAnnih K ⊆ charAnnih H := by
  intro ξ hξ
  rw [mem_charAnnih] at hξ ⊢
  exact fun x hx => hξ x (h hx)

open Classical in
@[simp] theorem charAnnih_bot : charAnnih (⊥ : AddSubgroup V) = Finset.univ := by
  ext ξ
  simp only [mem_charAnnih, Finset.mem_univ, iff_true]
  intro h hh
  rw [AddSubgroup.mem_bot.mp hh]
  simp

open Classical in
theorem charAnnih_top : charAnnih (⊤ : AddSubgroup V) = {1} := by
  ext ξ
  rw [mem_charAnnih, Finset.mem_singleton]
  constructor
  · intro hξ
    apply DFunLike.ext
    intro x
    rw [hξ x (AddSubgroup.mem_top x), AddChar.one_apply]
  · rintro rfl x _
    exact AddChar.one_apply x

/-! ## Restricted character orthogonality, and the size relation -/

open Classical in
/-- **Restricted character orthogonality** (Delsarte 1973, Thm 6.2). Summing a character over a
subgroup `H` gives `|H|` when the character is trivial on `H` (i.e. `ξ ∈ H^⊥`), and `0`
otherwise. -/
theorem sum_char_over_subgroup (H : AddSubgroup V) (ξ : AddChar V ℂ) :
    ∑ x : H, ξ (x : V) = if (∀ h ∈ H, ξ h = 1) then (Nat.card H : ℂ) else 0 := by
  set ξ' : AddChar H ℂ := ξ.compAddMonoidHom H.subtype with hξ'
  have hval : ∀ x : H, ξ' x = ξ (x : V) := fun x => by rw [hξ', AddChar.compAddMonoidHom_apply]; rfl
  have hsum : ∑ x : H, ξ (x : V) = ∑ x : H, ξ' x := by simp_rw [hval]
  have hiff : (ξ' = 1) ↔ (∀ h ∈ H, ξ h = 1) := by
    constructor
    · intro h1 h hh
      have hh1 : ξ' ⟨h, hh⟩ = 1 := by rw [h1]; exact AddChar.one_apply _
      rwa [hval] at hh1
    · intro hP
      apply DFunLike.ext
      intro x
      rw [hval x, hP x.1 x.2, AddChar.one_apply]
  by_cases hP : (∀ h ∈ H, ξ h = 1)
  · rw [if_pos hP, hsum, AddChar.sum_eq_card_of_eq_one (hiff.mpr hP), Nat.card_eq_fintype_card]
  · rw [if_neg hP, hsum, AddChar.sum_eq_zero_of_ne_one (fun h => hP (hiff.mp h))]

open Classical in
/-- **The annihilator size relation** `|H^⊥| · |H| = |V|`. Double-count `∑_ξ ∑_{x∈H} ξ(x)`:
by `sum_char_over_subgroup` it is `|H^⊥|·|H|`; by dual orthogonality (`AddChar.sum_apply_eq_ite`,
only `x = 0` survives) it is `|V|`. -/
theorem card_annihilator_mul_card (H : AddSubgroup V) :
    (charAnnih H).card * Nat.card H = Fintype.card V := by
  have hcond : ∀ ξ : AddChar V ℂ,
      (∑ x : H, ξ (x : V)) = if ξ ∈ charAnnih H then (Nat.card H : ℂ) else 0 := by
    intro ξ; rw [sum_char_over_subgroup]; simp only [mem_charAnnih]
  have lhs : (∑ ξ : AddChar V ℂ, ∑ x : H, ξ (x : V))
      = ((charAnnih H).card : ℂ) * (Nat.card H : ℂ) := by
    simp_rw [hcond]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have rhs : (∑ ξ : AddChar V ℂ, ∑ x : H, ξ (x : V)) = (Fintype.card V : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [AddChar.sum_apply_eq_ite, ZeroMemClass.coe_eq_zero]
    rw [Finset.sum_ite_eq' Finset.univ (0 : H)]
    simp
  have key : ((charAnnih H).card : ℂ) * (Nat.card H : ℂ) = (Fintype.card V : ℂ) :=
    lhs.symm.trans rhs
  exact_mod_cast key

open Classical in
/-- Counting subgroup members through a filter. -/
theorem card_filter_mem (K : AddSubgroup V) :
    (Finset.univ.filter (fun a : V => a ∈ K)).card = Nat.card K := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end WithFintype

/-! ## The size relations and the correspondence

These are `Nat.card` statements, so they need only finiteness; the `Fintype` the proofs use is
supplied locally. -/

section WithFinite

variable {V : Type*} [AddCommGroup V] [Finite V]

/-- The size relation in subgroup form. -/
theorem card_charAnnihSubgroup_mul (H : AddSubgroup V) :
    Nat.card (charAnnihSubgroup H) * Nat.card H = Nat.card V := by
  haveI : Fintype V := Fintype.ofFinite V
  rw [card_charAnnihSubgroup, Nat.card_eq_fintype_card (α := V)]
  exact card_annihilator_mul_card H

open Classical in
/-- **The pre-annihilator size relation** `|S^⊥| · |S| = |V|`. The same double count as
`card_annihilator_mul_card`, run on the other side: the inner sum is
`sum_char_over_subgroup` applied inside the DUAL group to `AddChar.doubleDualEmb a`, and the
outer sum is `AddChar.sum_eq_ite`. -/
theorem card_charAnnihPre_mul (S : AddSubgroup (AddChar V ℂ)) :
    Nat.card (charAnnihPre S) * Nat.card S = Nat.card V := by
  haveI : Fintype V := Fintype.ofFinite V
  have hinner : ∀ a : V, (∑ χ : S, (χ : AddChar V ℂ) a)
      = if a ∈ charAnnihPre S then (Nat.card S : ℂ) else 0 := by
    intro a
    simpa using sum_char_over_subgroup (V := AddChar V ℂ) S (AddChar.doubleDualEmb a)
  have lhs : (∑ a : V, ∑ χ : S, (χ : AddChar V ℂ) a)
      = (Nat.card (charAnnihPre S) : ℂ) * (Nat.card S : ℂ) := by
    simp_rw [hinner]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
      card_filter_mem]
  have rhs : (∑ a : V, ∑ χ : S, (χ : AddChar V ℂ) a) = (Nat.card V : ℂ) := by
    rw [Finset.sum_comm]
    have hchar : ∀ χ : S, (∑ a : V, (χ : AddChar V ℂ) a)
        = if (χ : AddChar V ℂ) = 0 then (Fintype.card V : ℂ) else 0 :=
      fun χ => AddChar.sum_eq_ite _
    simp_rw [hchar, ZeroMemClass.coe_eq_zero]
    rw [Finset.sum_ite_eq' Finset.univ (0 : S)]
    simp [Nat.card_eq_fintype_card]
  have key : (Nat.card (charAnnihPre S) : ℂ) * (Nat.card S : ℂ) = (Nat.card V : ℂ) :=
    lhs.symm.trans rhs
  exact_mod_cast key

/-! ## The correspondence

Both closure identities are proved by counting, not by exhibiting a separating character:
each composite contains the original subgroup, and the two size relations force the sizes to
agree, so finiteness closes the gap. -/

/-- **`H^⊥⊥ = H`.** -/
@[simp] theorem charAnnihPre_charAnnihSubgroup (H : AddSubgroup V) :
    charAnnihPre (charAnnihSubgroup H) = H := by
  have hpos : 0 < Nat.card (charAnnihSubgroup H) := Nat.card_pos
  have h1 := card_charAnnihPre_mul (charAnnihSubgroup H)
  have h2 : Nat.card H * Nat.card (charAnnihSubgroup H) = Nat.card V := by
    rw [mul_comm]
    exact card_charAnnihSubgroup_mul H
  have hcard : Nat.card (charAnnihPre (charAnnihSubgroup H)) = Nat.card H :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  exact (AddSubgroup.eq_of_le_of_card_ge (le_charAnnihPre_charAnnihSubgroup H) hcard.le).symm

/-- **`S^⊥⊥ = S`**, the same statement read on the dual side. -/
@[simp] theorem charAnnihSubgroup_charAnnihPre (S : AddSubgroup (AddChar V ℂ)) :
    charAnnihSubgroup (charAnnihPre S) = S := by
  have hpos : 0 < Nat.card (charAnnihPre S) := Nat.card_pos
  have h1 := card_charAnnihSubgroup_mul (charAnnihPre S)
  have h2 : Nat.card S * Nat.card (charAnnihPre S) = Nat.card V := by
    rw [mul_comm]
    exact card_charAnnihPre_mul S
  have hcard : Nat.card (charAnnihSubgroup (charAnnihPre S)) = Nat.card S :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  exact (AddSubgroup.eq_of_le_of_card_ge (le_charAnnihSubgroup_charAnnihPre S) hcard.le).symm

/-- **The subgroup lattices of a finite abelian group and of its dual are in bijection**, and
the bijection reverses inclusion (`charAnnihSubgroup_antitone`, `charAnnihPre_antitone`). -/
def charAnnihEquiv : AddSubgroup V ≃ AddSubgroup (AddChar V ℂ) where
  toFun := charAnnihSubgroup
  invFun := charAnnihPre
  left_inv := charAnnihPre_charAnnihSubgroup
  right_inv := charAnnihSubgroup_charAnnihPre

/-! ## Annihilating an image

The case the fixed-point count needs: for an endomorphism `f`, the annihilator of `range f`
is the size of `ker f`, because both are computed against `|V|`. -/

omit [Finite V] in
/-- **First isomorphism theorem in cardinal form**: `|ker f| · |range f| = |V|`. -/
theorem card_ker_mul_card_range (f : V →+ V) :
    Nat.card (AddMonoidHom.ker f) * Nat.card (AddMonoidHom.range f) = Nat.card V := by
  rw [← AddSubgroup.index_ker f, AddSubgroup.card_mul_index]

/-- **The annihilator of an image counts the kernel**: `|(range f)^⊥| = |ker f|`. -/
theorem card_charAnnihSubgroup_range (f : V →+ V) :
    Nat.card (charAnnihSubgroup (AddMonoidHom.range f)) = Nat.card (AddMonoidHom.ker f) := by
  have hpos : 0 < Nat.card (AddMonoidHom.range f) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos
    ((card_charAnnihSubgroup_mul _).trans (card_ker_mul_card_range f).symm)

end WithFinite

/-! ## Finset corollaries -/

section FinsetView

variable {V : Type*} [AddCommGroup V] [Fintype V]

open Classical in
/-- `card_charAnnihSubgroup_range` in the `Finset` view. -/
theorem card_charAnnih_range (f : V →+ V) :
    (charAnnih (AddMonoidHom.range f)).card = Nat.card (AddMonoidHom.ker f) := by
  rw [← card_charAnnihSubgroup, card_charAnnihSubgroup_range]

end FinsetView

end ECCLib

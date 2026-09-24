/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

/-!
# Counting subsets by their intersection profile with a fixed set

For a fixed `x ⊆ Ω`, the subsets of `Ω` with prescribed **profile** — `m` elements inside `x`
and `d` elements outside — number `C(#x, m) · C(#(Ω \ x), d)`. The profile
`(#(U ∩ x), #(U \ x))` is the interface deliberately: the two coordinates are independent,
so **no truncated subtraction appears in any intermediate index**. Formulations indexed by
`k − t` or similar differences are exposed to `ℕ`-truncation exactly in the indices this
interface avoids.

Stated over an arbitrary `[DecidableEq α]` ambient `Finset` — no `Fintype`, no `Fin n`.

## Main results

* `card_filter_profile` — the profile count.
* `card_filter_profile_powersetCard` — the fixed-size corollary: among the `k`-subsets, those
  meeting `x` in exactly `t` elements number `C(#x, t) · C(#(Ω \ x), k − t)`.

## Implementation notes

This is the generalisation of `ECCLib.Scheme.Johnson.card_filter_inter_card_eq`
(`Scheme/Johnson.lean`), which derives from it; the pair-difference computations of the
Johnson spectrum also use it. The `card_bij'` argument (profile ↦ the pair of pieces, pieces ↦
their union) is carried out here at strictly weaker hypotheses and with the two sizes
decoupled.
-/

namespace ECCLib

open Finset

variable {α : Type*} [DecidableEq α]

/-- **The profile count**: subsets of `Ω` with `m` elements inside `x` and `d` elements
outside number `C(#x, m) · C(#(Ω \ x), d)`. -/
theorem card_filter_profile {Ω x : Finset α} (hx : x ⊆ Ω) (m d : ℕ) :
    (Ω.powerset.filter fun U => #(U ∩ x) = m ∧ #(U \ x) = d).card
      = (#x).choose m * (#(Ω \ x)).choose d := by
  classical
  have hprod : ((x.powersetCard m) ×ˢ ((Ω \ x).powersetCard d)).card
      = (#x).choose m * (#(Ω \ x)).choose d := by
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]
  rw [← hprod]
  refine Finset.card_bij' (fun U _ => (U ∩ x, U \ x)) (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_powerset] at hU
    obtain ⟨hUΩ, hm, hd⟩ := hU
    simp only [Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨Finset.inter_subset_right, hm⟩,
      fun a ha => Finset.mem_sdiff.mpr
        ⟨hUΩ (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp ha).2⟩, hd⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powersetCard] at hp
    obtain ⟨⟨hA, hAcard⟩, hB, hBcard⟩ := hp
    have hBx : ∀ a ∈ p.2, a ∉ x := fun a ha => (Finset.mem_sdiff.mp (hB ha)).2
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset (hA.trans hx)
      (fun a ha => (Finset.mem_sdiff.mp (hB ha)).1), ?_, ?_⟩
    · have : (p.1 ∪ p.2) ∩ x = p.1 := by
        rw [Finset.union_inter_distrib_right]
        have h1 : p.1 ∩ x = p.1 := Finset.inter_eq_left.mpr hA
        have h2 : p.2 ∩ x = ∅ :=
          Finset.eq_empty_of_forall_notMem fun a ha =>
            hBx a (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp ha).2
        rw [h1, h2, Finset.union_empty]
      rw [this, hAcard]
    · have : (p.1 ∪ p.2) \ x = p.2 := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨ha | ha, hax⟩
          · exact absurd (hA ha) hax
          · exact ha
        · intro h
          exact ⟨Or.inr h, hBx a h⟩
      rw [this, hBcard]
  · intro U hU
    ext a
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powersetCard] at hp
    obtain ⟨⟨hA, -⟩, hB, -⟩ := hp
    have hBx : ∀ a ∈ p.2, a ∉ x := fun a ha => (Finset.mem_sdiff.mp (hB ha)).2
    refine Prod.ext ?_ ?_
    · ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hb | hb, hax⟩
        · exact hb
        · exact absurd hax (hBx a hb)
      · intro h
        exact ⟨Or.inl h, hA h⟩
    · ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨ha | ha, hax⟩
        · exact absurd (hA ha) hax
        · exact ha
      · intro h
        exact ⟨Or.inr h, hBx a h⟩

/-- **The fixed-size corollary**: among the `k`-subsets of `Ω`, those meeting `x` in exactly
`t` elements number `C(#x, t) · C(#(Ω \ x), k − t)`. The guard `t ≤ k` is what makes the size
split `#U = t + (k − t)` faithful. -/
theorem card_filter_profile_powersetCard {Ω x : Finset α} (hx : x ⊆ Ω) {k t : ℕ}
    (ht : t ≤ k) :
    ((Ω.powersetCard k).filter fun U => #(U ∩ x) = t).card
      = (#x).choose t * (#(Ω \ x)).choose (k - t) := by
  classical
  rw [← card_filter_profile hx t (k - t)]
  congr 1
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hUΩ, hUcard⟩, hm⟩
    refine ⟨hUΩ, hm, ?_⟩
    have hsum := Finset.card_sdiff_add_card_inter U x
    omega
  · rintro ⟨hUΩ, hm, hd⟩
    refine ⟨⟨hUΩ, ?_⟩, hm⟩
    have hsum := Finset.card_sdiff_add_card_inter U x
    omega

/-- **Counting the `c`-subsets of `U` through a prescribed subset**: strip the prescribed part
off. The guard `#A ≤ c` is necessary — below it the filter is empty while the right side is `1`. -/
theorem card_powersetCard_filter_superset {A U : Finset α} (hAU : A ⊆ U) {c : ℕ}
    (hAc : #A ≤ c) :
    ((U.powersetCard c).filter fun C => A ⊆ C).card = (#U - #A).choose (c - #A) := by
  classical
  have hcardUA : #(U \ A) = #U - #A := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAU]
  have hsub : ∀ C ∈ (U.powersetCard c).filter fun C => A ⊆ C,
      A ⊆ C ∧ C ⊆ U ∧ #C = c := by
    intro C hC
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hC
    exact ⟨hC.2, hC.1.1, hC.1.2⟩
  rw [show (#U - #A).choose (c - #A) = ((U \ A).powersetCard (c - #A)).card by
    rw [Finset.card_powersetCard, hcardUA]]
  apply Finset.card_nbij' (i := fun C => C \ A) (j := fun D => D ∪ A)
  · intro C hC
    obtain ⟨hAC, hCU, hCc⟩ := hsub C hC
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.sdiff_subset_sdiff hCU Finset.Subset.rfl, ?_⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAC, hCc]
  · intro D hD
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hD
    have hdisj : Disjoint D A :=
      Finset.disjoint_left.mpr fun x hxD hxA => (Finset.mem_sdiff.mp (hD.1 hxD)).2 hxA
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.union_subset (hD.1.trans Finset.sdiff_subset) hAU, ?_⟩,
      Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, hD.2]
    omega
  · intro C hC
    exact Finset.sdiff_union_of_subset (hsub C hC).1
  · intro D hD
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hD
    have hdisj : Disjoint D A :=
      Finset.disjoint_left.mpr fun x hxD hxA => (Finset.mem_sdiff.mp (hD.1 hxD)).2 hxA
    change (D ∪ A) \ A = D
    rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hdisj]

end ECCLib

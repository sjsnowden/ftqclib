/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Basic

/-!
# Pair-difference functions on subsets

Fix a system of `t` disjoint pairs `(a i, b i)` of points. The **pair-difference function**
sends a subset `K` to the product `∏ i ([a i ∈ K] − [b i ∈ K])`. These are the harmonic
functions of the subset lattice in their cheapest clothing: they vanish unless `K` separates
every pair, transversal subsets give value `±1`, and moving `K` by the swap of one pair
negates the value. Downstream they are the common eigenvectors of the Johnson scheme.

Mentions no group, no scheme, no `Fin n` carrier: the pair system is a pair of maps into an
arbitrary `[DecidableEq α]`, and the values live in an arbitrary commutative ring.

## Main definitions

* `pairDiff R a b K` — the signed product.

## Main results

* `pairDiff_eq_zero_of_mem_iff` — vanishing on any non-separating subset.
* `pairDiff_map_swap` — the swap of one pair negates the value.
* `exists_card_eq_and_pairDiff_eq_one` — a transversal of any admissible size exists, with
  value exactly `1` (stated with value `1` rather than `≠ 0`, so no nontriviality or
  zero-divisor hypothesis is spent).

## Implementation notes

The pair system is two maps `a b : Fin t → α` with the single hypothesis
`Function.Injective (Sum.elim a b)`, which carries all `2t` distinctness facts at once — the
encoding chosen over the alternatives (a `Finset` of pairs
costs a disjointness predicate plus subtype products; a sign vector cannot express the
pairing). Hypotheses are carried only where a statement needs them: the definition and the
vanishing lemma need no injectivity at all.
-/

namespace ECCLib

open Finset

variable {α : Type*} [DecidableEq α] {t : ℕ}

/-- The **pair-difference function**: the signed product `∏ i ([a i ∈ K] − [b i ∈ K])`. -/
def pairDiff (R : Type*) [CommRing R] (a b : Fin t → α) (K : Finset α) : R :=
  ∏ i, ((if a i ∈ K then (1 : R) else 0) - if b i ∈ K then 1 else 0)

variable {R : Type*} [CommRing R] {a b : Fin t → α}

/-- A subset that fails to separate some pair is killed: the factor at that pair vanishes. -/
theorem pairDiff_eq_zero_of_mem_iff {K : Finset α} {i : Fin t} (h : a i ∈ K ↔ b i ∈ K) :
    pairDiff R a b K = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  by_cases hm : a i ∈ K
  · rw [if_pos hm, if_pos (h.mp hm), sub_self]
  · rw [if_neg hm, if_neg (fun hb => hm (h.mpr hb)), sub_self]

/-- On a transversal — every `a i` in, every `b i` out — the value is exactly `1`. -/
theorem pairDiff_eq_one {K : Finset α} (ha : ∀ i, a i ∈ K) (hb : ∀ i, b i ∉ K) :
    pairDiff R a b K = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [if_pos (ha i), if_neg (hb i), sub_zero]

/-- **The swap of one pair negates the value**: pushing `K` forward along
`Equiv.swap (a i) (b i)` flips the `i`-th factor and fixes every other, because the pair
system is injective. This is the involution behind every vanishing shell sum downstream. -/
theorem pairDiff_map_swap (hab : Function.Injective (Sum.elim a b)) (i : Fin t)
    (K : Finset α) :
    pairDiff R a b (K.map (Equiv.swap (a i) (b i)).toEmbedding) = -pairDiff R a b K := by
  have hmem : ∀ x : α, x ∈ K.map (Equiv.swap (a i) (b i)).toEmbedding
      ↔ Equiv.swap (a i) (b i) x ∈ K := by
    intro x
    rw [Finset.mem_map_equiv]
    have : (Equiv.swap (a i) (b i)).symm = Equiv.swap (a i) (b i) := Equiv.symm_swap _ _
    rw [this]
  have hfac : ∀ j : Fin t,
      ((if a j ∈ K.map (Equiv.swap (a i) (b i)).toEmbedding then (1 : R) else 0)
          - if b j ∈ K.map (Equiv.swap (a i) (b i)).toEmbedding then 1 else 0)
        = (if j = i then (-1 : R) else 1)
          * ((if a j ∈ K then (1 : R) else 0) - if b j ∈ K then 1 else 0) := by
    intro j
    rcases eq_or_ne j i with rfl | hji
    · simp only [hmem, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [if_true, neg_one_mul, neg_sub]
    · have hja : a j ≠ a i := fun h =>
        hji (Sum.inl_injective (@hab (Sum.inl j) (Sum.inl i) h))
      have hjb : a j ≠ b i := fun h => Sum.inl_ne_inr (@hab (Sum.inl j) (Sum.inr i) h)
      have hba : b j ≠ a i := fun h => Sum.inr_ne_inl (@hab (Sum.inr j) (Sum.inl i) h)
      have hbb : b j ≠ b i := fun h =>
        hji (Sum.inr_injective (@hab (Sum.inr j) (Sum.inr i) h))
      simp only [hmem, Equiv.swap_apply_of_ne_of_ne hja hjb,
        Equiv.swap_apply_of_ne_of_ne hba hbb]
      rw [if_neg hji, one_mul]
  rw [pairDiff, pairDiff, Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ i fun _ => (-1 : R)]
  simp

omit [DecidableEq α] in
/-- **A transversal of any admissible size exists, with its memberships exposed**: take the
`a`-points and pad from outside the pair system. The guard `k + t ≤ #α` is exactly what
leaves room for the padding. -/
theorem exists_transversal [Fintype α]
    (hab : Function.Injective (Sum.elim a b)) {k : ℕ} (htk : t ≤ k)
    (hkn : k + t ≤ Fintype.card α) :
    ∃ K : Finset α, K.card = k ∧ (∀ i, a i ∈ K) ∧ ∀ i, b i ∉ K := by
  classical
  have hainj : Function.Injective a := fun j j' h =>
    Sum.inl_injective (@hab (Sum.inl j) (Sum.inl j') h)
  set A : Finset α := Finset.image a Finset.univ with hA
  set B : Finset α := Finset.image b Finset.univ with hB
  have hAcard : A.card = t := by
    rw [hA, Finset.card_image_of_injective _ hainj, Finset.card_univ, Fintype.card_fin]
  have houtside : k - t ≤ ((Finset.univ : Finset α) \ (A ∪ B)).card := by
    have hABcard : (A ∪ B).card ≤ 2 * t := by
      calc (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
        _ ≤ t + t := by
            refine Nat.add_le_add (le_of_eq hAcard) ?_
            calc B.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
              _ = t := by rw [Finset.card_univ, Fintype.card_fin]
        _ = 2 * t := (two_mul t).symm
    have := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (A ∪ B) : A ∪ B ⊆ Finset.univ)
    have hcard_univ : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
    omega
  obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq houtside
  refine ⟨A ∪ C, ?_, ?_⟩
  · have hdisj : Disjoint A C := by
      refine Finset.disjoint_left.mpr fun x hx hxc => ?_
      have := hCsub hxc
      rw [Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_union_left _ hx)
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hCcard]
    omega
  · refine ⟨fun i => Finset.mem_union_left _ ?_, fun i hbi => ?_⟩
    · exact Finset.mem_image_of_mem a (Finset.mem_univ i)
    · rcases Finset.mem_union.mp hbi with hbA | hbC
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hbA
        exact Sum.inl_ne_inr (@hab (Sum.inl j) (Sum.inr i) hj)
      · have := hCsub hbC
        rw [Finset.mem_sdiff] at this
        exact this.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ i)))

/-- **A transversal of any admissible size exists, with value `1`** (stated with value `1`
rather than `≠ 0`, so no nontriviality or zero-divisor hypothesis is spent). -/
theorem exists_card_eq_and_pairDiff_eq_one [Fintype α]
    (hab : Function.Injective (Sum.elim a b)) {k : ℕ} (htk : t ≤ k)
    (hkn : k + t ≤ Fintype.card α) :
    ∃ K : Finset α, K.card = k ∧ pairDiff R a b K = 1 := by
  obtain ⟨K, hcard, ha, hb⟩ := exists_transversal hab htk hkn
  exact ⟨K, hcard, pairDiff_eq_one ha hb⟩

end ECCLib

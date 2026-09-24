/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.PairHarmonic
import ECCLib.SubsetProfile
import ECCLib.Delsarte.Eberlein
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Shell sums of pair-difference functions are Eberlein multiples

**The engine of the Johnson spectrum**: summing a pair-difference function over the shell
`{L : #L = k, #(K ∩ L) = w}` around any `k`-subset `K` returns the Eberlein number
`E_{k−w}(t)` times the value at `K`. Downstream this is precisely the statement that the
pair-difference functions are common eigenvectors of the Johnson scheme, with the Eberlein
numbers as eigenvalues — but this module knows no scheme, no group, and no matrix: the
identity is a fact about finite sets and one alternating sum.

## Main results

* `pairDiff_eq_sum_pattern` — the expansion of a pair-difference value over exact patterns.
* `card_shell_pattern` — the pattern count, subtraction-free.
* `sum_shell_pairDiff` — **the shell-sum identity**, for any pair system and any `K`.

## The proof, in stages

A non-separated pair kills both sides: the swap of that pair is an involution of the shell
that negates the summand (`pairDiff_map_swap`), and the value at `K` has a vanishing factor.
For separating `K` the identity is first proved when every pair meets `K` positively
(`a i ∈ K`, `b i ∉ K`): expand the product into a signed sum of exact-pattern indicators,
count the shell members with a given pattern by the profile count of
`ECCLib/SubsetProfile.lean` — the pattern pins the trace of `L` on the `2t` pair
points, and what remains is a free profile choice outside them — and the resulting
alternating sum is `eberlein` after one `Nat.choose_symm`. The general separating case
reduces to the positive case by flipping pairs one at a time, which negates both sides.
-/

namespace ECCLib

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {t : ℕ} {a b : Fin t → α}

/-! ## The pattern expansion -/

omit [Fintype α] in
/-- Each raw factor `[a∈L] − [b∈L]` splits into the difference of the two **exact** events:
`a` in and `b` out, minus `b` in and `a` out. An algebraic identity of the four cases. -/
theorem pairDiff_factor_split {R : Type*} [CommRing R] (L : Finset α) (i : Fin t) :
    ((if a i ∈ L then (1 : R) else 0) - if b i ∈ L then 1 else 0)
      = (if a i ∈ L ∧ b i ∉ L then (1 : R) else 0)
        - if b i ∈ L ∧ a i ∉ L then 1 else 0 := by
  by_cases ha : a i ∈ L <;> by_cases hb : b i ∈ L <;> simp [ha, hb]

/-- The **exact pattern** of a pair system on a subset, as a `Prop`: outside `T` the pair
meets positively (`a` in, `b` out), on `T` negatively. -/
def PairPattern (a b : Fin t → α) (T : Finset (Fin t)) (L : Finset α) : Prop :=
  (∀ i, i ∉ T → a i ∈ L ∧ b i ∉ L) ∧ ∀ i ∈ T, b i ∈ L ∧ a i ∉ L

instance decidablePairPattern (T : Finset (Fin t)) (L : Finset α) :
    Decidable (PairPattern a b T L) := by
  unfold PairPattern; infer_instance

omit [Fintype α] in
/-- **The pattern expansion**: a pair-difference value is the signed sum of exact-pattern
indicators, the sign counting the negatively-met pairs. -/
theorem pairDiff_eq_sum_pattern {R : Type*} [CommRing R] (L : Finset α) :
    pairDiff R a b L
      = ∑ T ∈ (Finset.univ : Finset (Fin t)).powerset,
          (-1) ^ #T * if PairPattern a b T L then (1 : R) else 0 := by
  rw [pairDiff]
  rw [show (∏ i, ((if a i ∈ L then (1 : R) else 0) - if b i ∈ L then 1 else 0))
      = ∏ i, ((if a i ∈ L ∧ b i ∉ L then (1 : R) else 0)
          - if b i ∈ L ∧ a i ∉ L then 1 else 0) from
    Finset.prod_congr rfl fun i _ => pairDiff_factor_split L i]
  rw [Finset.prod_sub]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.prod_boole, Finset.prod_boole, mul_assoc]
  congr 1
  have hiff : (∀ i ∈ Finset.univ \ T, a i ∈ L ∧ b i ∉ L)
      ↔ ∀ i, i ∉ T → a i ∈ L ∧ b i ∉ L := by
    constructor
    · intro h i hi
      exact h i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
    · intro h i hi
      exact h i (Finset.mem_sdiff.mp hi).2
  by_cases h1 : ∀ i, i ∉ T → a i ∈ L ∧ b i ∉ L
  · by_cases h2 : ∀ i ∈ T, b i ∈ L ∧ a i ∉ L
    · rw [if_pos (hiff.mpr h1), if_pos h2,
        if_pos (show PairPattern a b T L from ⟨h1, h2⟩), mul_one]
    · rw [if_neg h2, mul_zero,
        if_neg (show ¬PairPattern a b T L from fun hc => h2 hc.2)]
  · rw [if_neg fun hc => h1 (hiff.mp hc), zero_mul,
      if_neg (show ¬PairPattern a b T L from fun hc => h1 hc.1)]

/-! ## The pattern count

A subset with pattern `T` is pinned on the `2t` pair points — it contains exactly the pattern
set `patternSet a b T` there — and is a free profile choice outside them. The count is
therefore a profile count of `SubsetProfile.lean`, stated **subtraction-free**: every
cardinality on the right is the cardinality of a named set. -/

/-- All `2t` pair points. -/
def pairSupport (a b : Fin t → α) : Finset α :=
  Finset.univ.image a ∪ Finset.univ.image b

/-- The trace a pattern-`T` subset leaves on the pair points: the `a`-points off `T` and the
`b`-points on `T`. -/
def patternSet (a b : Fin t → α) (T : Finset (Fin t)) : Finset α :=
  (Finset.univ \ T).image a ∪ T.image b

section PatternCount

variable (hab : Function.Injective (Sum.elim a b))

include hab

omit [Fintype α] [DecidableEq α] in
theorem a_ne_b (i j : Fin t) : a i ≠ b j := fun h =>
  Sum.inl_ne_inr (@hab (Sum.inl i) (Sum.inr j) h)

omit [Fintype α] [DecidableEq α] in
theorem injective_a : Function.Injective a := fun i j h =>
  Sum.inl_injective (@hab (Sum.inl i) (Sum.inl j) h)

omit [Fintype α] [DecidableEq α] in
theorem injective_b : Function.Injective b := fun i j h =>
  Sum.inr_injective (@hab (Sum.inr i) (Sum.inr j) h)

omit [Fintype α] in
/-- Membership in the pattern set, by cases on which pair a point comes from. -/
theorem mem_patternSet_a {T : Finset (Fin t)} {i : Fin t} :
    a i ∈ patternSet a b T ↔ i ∉ T := by
  rw [patternSet, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      rw [← injective_a hab hji]
      exact (Finset.mem_sdiff.mp hj).2
    · obtain ⟨j, -, hji⟩ := Finset.mem_image.mp h
      exact absurd hji.symm (a_ne_b hab i j)
  · intro h
    exact Or.inl (Finset.mem_image_of_mem a
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩))

omit [Fintype α] in
theorem mem_patternSet_b {T : Finset (Fin t)} {i : Fin t} :
    b i ∈ patternSet a b T ↔ i ∈ T := by
  rw [patternSet, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨j, -, hji⟩ := Finset.mem_image.mp h
      exact absurd hji (a_ne_b hab j i)
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
      rw [← injective_b hab hji]
      exact hj
  · intro h
    exact Or.inr (Finset.mem_image_of_mem b h)

omit [Fintype α] hab in
/-- The pattern set sits inside the pair support. -/
theorem patternSet_subset_pairSupport {T : Finset (Fin t)} :
    patternSet a b T ⊆ pairSupport a b := by
  rw [patternSet, pairSupport]
  exact Finset.union_subset_union (Finset.image_subset_image (Finset.sdiff_subset))
    (Finset.image_subset_image (Finset.subset_univ T))

omit [Fintype α] in
theorem card_patternSet (T : Finset (Fin t)) : #(patternSet a b T) = t := by
  have hdisj : Disjoint ((Finset.univ \ T).image a) (T.image b) := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx'
    exact a_ne_b hab i j hj.symm
  rw [patternSet, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (injective_a hab),
    Finset.card_image_of_injective _ (injective_b hab)]
  have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have h2 : #(Finset.univ : Finset (Fin t)) = t := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

omit [Fintype α] in
/-- A pattern-`T` subset meets the pair support in exactly the pattern set. -/
theorem pattern_inter_pairSupport {T : Finset (Fin t)} {L : Finset α}
    (hL : PairPattern a b T L) : L ∩ pairSupport a b = patternSet a b T := by
  ext x
  rw [Finset.mem_inter, pairSupport, Finset.mem_union]
  constructor
  · rintro ⟨hxL, hx | hx⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [mem_patternSet_a hab]
      intro hiT
      exact (hL.2 i hiT).2 hxL
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [mem_patternSet_b hab]
      by_contra hiT
      exact (hL.1 i hiT).2 hxL
  · intro hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact ⟨(hL.1 i (Finset.mem_sdiff.mp hi).2).1,
        Or.inl (Finset.mem_image_of_mem a (Finset.mem_univ i))⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact ⟨(hL.2 i hi).1, Or.inr (Finset.mem_image_of_mem b (Finset.mem_univ i))⟩

omit [Fintype α] hab in
theorem mem_pairSupport_a (i : Fin t) : a i ∈ pairSupport a b :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ i))

omit [Fintype α] hab in
theorem mem_pairSupport_b (i : Fin t) : b i ∈ pairSupport a b :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ i))

/-- **The pattern count, subtraction-free**: the `(t+m+d)`-subsets with pattern `T` whose
`K`-intersection exceeds the pinned part `K ∩ patternSet` by exactly `m` are a free profile
choice outside the pair support. Every cardinality on the right names a set. -/
theorem card_shell_pattern (K : Finset α) (T : Finset (Fin t)) (m d : ℕ) :
    #((Finset.univ.powersetCard (t + m + d)).filter fun L =>
        #(K ∩ L) = #(K ∩ patternSet a b T) + m ∧ PairPattern a b T L)
      = (#(K \ pairSupport a b)).choose m
        * (#(Finset.univ \ (K ∪ pairSupport a b))).choose d := by
  classical
  have hx_sub : K \ pairSupport a b ⊆ Finset.univ \ pairSupport a b :=
    fun y hy => Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, (Finset.mem_sdiff.mp hy).2⟩
  have hPdiff : (Finset.univ \ pairSupport a b) \ (K \ pairSupport a b)
      = Finset.univ \ (K ∪ pairSupport a b) := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
    tauto
  rw [← hPdiff, ← card_filter_profile hx_sub m d]
  refine Finset.card_bij' (fun L _ => L \ pairSupport a b)
    (fun L' _ => L' ∪ patternSet a b T) ?_ ?_ ?_ ?_
  · intro L hL
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hL
    obtain ⟨⟨-, hLcard⟩, hKL, hpat⟩ := hL
    have hLpS : L ∩ pairSupport a b = patternSet a b T :=
      pattern_inter_pairSupport hab hpat
    have hLpS_card : #(L ∩ pairSupport a b) = t := by
      rw [hLpS]; exact card_patternSet hab T
    have hL'card : #(L \ pairSupport a b) = m + d := by
      have := Finset.card_sdiff_add_card_inter L (pairSupport a b)
      omega
    have hint : (L \ pairSupport a b) ∩ (K \ pairSupport a b)
        = (K ∩ L) \ pairSupport a b := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hKL_split := Finset.card_sdiff_add_card_inter (K ∩ L) (pairSupport a b)
    have hKLpS : (K ∩ L) ∩ pairSupport a b = K ∩ patternSet a b T := by
      rw [Finset.inter_assoc, hLpS]
    have hm : #((L \ pairSupport a b) ∩ (K \ pairSupport a b)) = m := by
      rw [hint]
      rw [hKLpS] at hKL_split
      omega
    have hd : #((L \ pairSupport a b) \ (K \ pairSupport a b)) = d := by
      have := Finset.card_sdiff_add_card_inter (L \ pairSupport a b)
        (K \ pairSupport a b)
      omega
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun y hy => Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ y, (Finset.mem_sdiff.mp hy).2⟩, hm, hd⟩
  · intro L' hL'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hL'
    obtain ⟨hL'P, hm, hd⟩ := hL'
    have hL'pS : ∀ y ∈ L', y ∉ pairSupport a b :=
      fun y hy => (Finset.mem_sdiff.mp (hL'P hy)).2
    have hdisj : Disjoint L' (patternSet a b T) :=
      Finset.disjoint_left.mpr fun y hy hy' =>
        hL'pS y hy (patternSet_subset_pairSupport hy')
    have hL'card : #L' = m + d := by
      have := Finset.card_sdiff_add_card_inter L' (K \ pairSupport a b)
      omega
    have hpat : PairPattern a b T (L' ∪ patternSet a b T) := by
      constructor
      · intro i hi
        refine ⟨Finset.mem_union_right _ ((mem_patternSet_a hab).mpr hi), ?_⟩
        intro hbi
        rcases Finset.mem_union.mp hbi with h | h
        · exact hL'pS _ h (mem_pairSupport_b i)
        · exact hi ((mem_patternSet_b hab).mp h)
      · intro i hi
        refine ⟨Finset.mem_union_right _ ((mem_patternSet_b hab).mpr hi), ?_⟩
        intro hai
        rcases Finset.mem_union.mp hai with h | h
        · exact hL'pS _ h (mem_pairSupport_a i)
        · exact ((mem_patternSet_a hab).mp h) hi
    have hKint : K ∩ (L' ∪ patternSet a b T)
        = ((K \ pairSupport a b) ∩ L') ∪ (K ∩ patternSet a b T) := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hyK, hyL | hyP⟩
        · exact Or.inl ⟨⟨hyK, hL'pS y hyL⟩, hyL⟩
        · exact Or.inr ⟨hyK, hyP⟩
      · rintro (⟨⟨hyK, -⟩, hyL⟩ | ⟨hyK, hyP⟩)
        · exact ⟨hyK, Or.inl hyL⟩
        · exact ⟨hyK, Or.inr hyP⟩
    have hKdisj : Disjoint ((K \ pairSupport a b) ∩ L') (K ∩ patternSet a b T) :=
      Finset.disjoint_left.mpr fun y hy hy' => by
        have h1 := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).2
        exact h1 (patternSet_subset_pairSupport (Finset.mem_inter.mp hy').2)
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_, hpat⟩
    · rw [Finset.card_union_of_disjoint hdisj, hL'card, card_patternSet hab T]
      omega
    · rw [hKint, Finset.card_union_of_disjoint hKdisj]
      have hcomm : (K \ pairSupport a b) ∩ L' = L' ∩ (K \ pairSupport a b) :=
        Finset.inter_comm _ _
      rw [hcomm, hm]
      omega
  · intro L hL
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hL
    have hLpS : L ∩ pairSupport a b = patternSet a b T :=
      pattern_inter_pairSupport hab hL.2.2
    ext y
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hy, -⟩ | hy)
      · exact hy
      · have hmem : y ∈ L ∩ pairSupport a b := by rw [hLpS]; exact hy
        exact (Finset.mem_inter.mp hmem).1
    · intro hy
      by_cases hpS : y ∈ pairSupport a b
      · refine Or.inr ?_
        rw [← hLpS]
        exact Finset.mem_inter.mpr ⟨hy, hpS⟩
      · exact Or.inl ⟨hy, hpS⟩
  · intro L' hL'
    simp only [Finset.mem_filter, Finset.mem_powerset] at hL'
    have hL'pS : ∀ y ∈ L', y ∉ pairSupport a b :=
      fun y hy => (Finset.mem_sdiff.mp (hL'.1 hy)).2
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hy | hy, hpS⟩
      · exact hy
      · exact absurd (patternSet_subset_pairSupport hy) hpS
    · intro hy
      exact ⟨Or.inl hy, hL'pS y hy⟩

/-- Guard failure one: a pattern subset always meets `K` in at least the pinned part, so a
shell below it is empty of that pattern. -/
theorem card_shell_pattern_eq_zero_low {K : Finset α} {k w : ℕ} (T : Finset (Fin t))
    (hlow : w < #(K ∩ patternSet a b T)) :
    #((Finset.univ.powersetCard k).filter fun L =>
        #(K ∩ L) = w ∧ PairPattern a b T L) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro L hL ⟨hw, hpat⟩
  have hsub : K ∩ patternSet a b T ⊆ K ∩ L := by
    intro y hy
    obtain ⟨hyK, hyP⟩ := Finset.mem_inter.mp hy
    refine Finset.mem_inter.mpr ⟨hyK, ?_⟩
    have hLpS := pattern_inter_pairSupport hab hpat
    rw [← hLpS] at hyP
    exact (Finset.mem_inter.mp hyP).1
  have := Finset.card_le_card hsub
  omega

/-- Guard failure two: a pattern subset of size `k` has only `k − t` free points, so its
`K`-intersection cannot exceed the pinned part by more than that. -/
theorem card_shell_pattern_eq_zero_high {K : Finset α} {k w : ℕ} (T : Finset (Fin t))
    (hhigh : #(K ∩ patternSet a b T) + k < w + t) :
    #((Finset.univ.powersetCard k).filter fun L =>
        #(K ∩ L) = w ∧ PairPattern a b T L) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro L hL ⟨hw, hpat⟩
  rw [Finset.mem_powersetCard] at hL
  have hLpS : L ∩ pairSupport a b = patternSet a b T :=
    pattern_inter_pairSupport hab hpat
  have hLsplit := Finset.card_sdiff_add_card_inter L (pairSupport a b)
  have hLpS_card : #(L ∩ pairSupport a b) = t := by
    rw [hLpS]; exact card_patternSet hab T
  have hKLsplit := Finset.card_sdiff_add_card_inter (K ∩ L) (pairSupport a b)
  have hKLpS : (K ∩ L) ∩ pairSupport a b = K ∩ patternSet a b T := by
    rw [Finset.inter_assoc, hLpS]
  have hfree : (K ∩ L) \ pairSupport a b ⊆ L \ pairSupport a b := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hy1).2, hy2⟩
  have hle := Finset.card_le_card hfree
  rw [hKLpS] at hKLsplit
  omega

omit [Fintype α] in
theorem card_pairSupport : #(pairSupport a b) = 2 * t := by
  have hdisj : Disjoint (Finset.univ.image a) (Finset.univ.image b) := by
    refine Finset.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx'
    exact a_ne_b hab i j hj.symm
  rw [pairSupport, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (injective_a hab),
    Finset.card_image_of_injective _ (injective_b hab), Finset.card_univ,
    Fintype.card_fin]
  omega

section Positive

variable {K : Finset α} (hpos : ∀ i, a i ∈ K ∧ b i ∉ K)

include hpos

omit [Fintype α] hab in
theorem inter_pairSupport_pos : K ∩ pairSupport a b = Finset.univ.image a := by
  ext y
  rw [Finset.mem_inter, pairSupport, Finset.mem_union]
  constructor
  · rintro ⟨hyK, hy | hy⟩
    · exact hy
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact absurd hyK (hpos i).2
  · intro hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨(hpos i).1, Or.inl (Finset.mem_image_of_mem a (Finset.mem_univ i))⟩

omit [Fintype α] in
theorem card_inter_patternSet_pos (T : Finset (Fin t)) :
    #(K ∩ patternSet a b T) = #(Finset.univ \ T) := by
  have h : K ∩ patternSet a b T = (Finset.univ \ T).image a := by
    ext y
    rw [Finset.mem_inter, patternSet, Finset.mem_union]
    constructor
    · rintro ⟨hyK, hy | hy⟩
      · exact hy
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        exact absurd hyK (hpos i).2
    · intro hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨(hpos i).1, Or.inl (Finset.mem_image_of_mem a hi)⟩
  rw [h, Finset.card_image_of_injective _ (injective_a hab)]

omit [Fintype α] in
theorem card_sdiff_pairSupport_pos : #(K \ pairSupport a b) + t = #K := by
  have h1 := Finset.card_sdiff_add_card_inter K (pairSupport a b)
  have h2 : #(K ∩ pairSupport a b) = t := by
    rw [inter_pairSupport_pos hpos,
      Finset.card_image_of_injective _ (injective_a hab), Finset.card_univ,
      Fintype.card_fin]
  omega

theorem card_compl_union_pos :
    #(Finset.univ \ (K ∪ pairSupport a b)) + #K + t = Fintype.card α := by
  have h1 := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (K ∪ pairSupport a b))
  have h2 : #(K ∪ pairSupport a b) + #(K ∩ pairSupport a b)
      = #K + #(pairSupport a b) := Finset.card_union_add_card_inter K (pairSupport a b)
  have h3 : #(K ∩ pairSupport a b) = t := by
    rw [inter_pairSupport_pos hpos,
      Finset.card_image_of_injective _ (injective_a hab), Finset.card_univ,
      Fintype.card_fin]
  have h4 := card_pairSupport hab (b := b)
  have h5 : #(Finset.univ : Finset α) = Fintype.card α := Finset.card_univ
  omega

/-- **The shell-sum identity, positive case**: when every pair meets `K` positively the value
at `K` is `1`, and the shell sum is the Eberlein number itself. -/
theorem sum_shell_pairDiff_pos {k w : ℕ} (hK : #K = k) (hw : w ≤ k) :
    ∑ L ∈ (Finset.univ.powersetCard k).filter (fun L => #(K ∩ L) = w),
        pairDiff ℤ a b L
      = Delsarte.eberlein (Fintype.card α) k (k - w) t := by
  classical
  have htk : t ≤ k := by
    have hsub : Finset.univ.image a ⊆ K := fun y hy => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact (hpos i).1
    have hcards := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ (injective_a hab), Finset.card_univ,
      Fintype.card_fin, hK] at hcards
  have hkt : #(K \ pairSupport a b) + t = k := by
    rw [← hK]; exact card_sdiff_pairSupport_pos hab hpos
  have hn : #(Finset.univ \ (K ∪ pairSupport a b)) + k + t = Fintype.card α := by
    rw [← hK]; exact card_compl_union_pos hab hpos
  have hc1 : #(K \ pairSupport a b) = k - t := by omega
  have hc2 : #(Finset.univ \ (K ∪ pairSupport a b)) = Fintype.card α - k - t := by omega
  have hcount : ∀ T : Finset (Fin t),
      (#(((Finset.univ.powersetCard k).filter fun L => #(K ∩ L) = w).filter
        (PairPattern a b T)) : ℤ)
      = if t ≤ w + #T ∧ w + #T ≤ k
        then ((k - t).choose (w + #T - t) : ℤ)
          * ((Fintype.card α - k - t).choose (k - w - #T) : ℤ)
        else 0 := by
    intro T
    rw [Finset.filter_filter]
    have hTt : #T ≤ t := by
      have := Finset.card_le_card (Finset.subset_univ T)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    have hcT : #(K ∩ patternSet a b T) + #T = t := by
      have h1 := card_inter_patternSet_pos hab hpos T
      have h2 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
      have h3 : #(Finset.univ : Finset (Fin t)) = t := by
        rw [Finset.card_univ, Fintype.card_fin]
      omega
    by_cases hg : t ≤ w + #T ∧ w + #T ≤ k
    · obtain ⟨hg1, hg2⟩ := hg
      have hm : #(K ∩ patternSet a b T) + (w + #T - t) = w := by omega
      have hkform : t + (w + #T - t) + (k - w - #T) = k := by omega
      rw [if_pos ⟨hg1, hg2⟩]
      have hcs := card_shell_pattern hab K T (w + #T - t) (k - w - #T)
      rw [hkform, hc1, hc2] at hcs
      rw [show ((Finset.univ.powersetCard k).filter fun L =>
          #(K ∩ L) = w ∧ PairPattern a b T L)
          = ((Finset.univ.powersetCard k).filter fun L =>
          #(K ∩ L) = #(K ∩ patternSet a b T) + (w + #T - t) ∧ PairPattern a b T L) from
        Finset.filter_congr fun L _ => by rw [hm]]
      rw [hcs]
      push_cast
      ring
    · rw [if_neg hg]
      rcases Nat.lt_or_ge (w + #T) t with h | h
      · have hlow : w < #(K ∩ patternSet a b T) := by omega
        rw [card_shell_pattern_eq_zero_low hab T hlow]
        norm_num
      · have hg2 : k < w + #T := by omega
        have hhigh : #(K ∩ patternSet a b T) + k < w + t := by omega
        rw [card_shell_pattern_eq_zero_high hab T hhigh]
        norm_num
  rw [Finset.sum_congr rfl fun L (_ : L ∈ _) =>
    pairDiff_eq_sum_pattern (a := a) (b := b) (R := ℤ) L]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun T (_ : T ∈ _) => (Finset.mul_sum _ _ _).symm]
  rw [Finset.sum_congr rfl fun T (_ : T ∈ _) => by rw [Finset.sum_boole, hcount T]]
  rw [Finset.sum_powerset]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ _) =>
    Finset.sum_powersetCard r Finset.univ (fun r =>
      (-1) ^ r * if t ≤ w + r ∧ w + r ≤ k
        then ((k - t).choose (w + r - t) : ℤ)
          * ((Fintype.card α - k - t).choose (k - w - r) : ℤ)
        else 0)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Delsarte.eberlein]
  refine (Finset.sum_subset (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))) ?_).symm.trans
    ((Finset.sum_congr rfl ?_).trans
      (Finset.sum_subset (s₁ := Finset.range (min t (k - w) + 1))
        (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega))) ?_))
  · intro r hr hrS
    rw [Finset.mem_range] at hr hrS
    have hguard : ¬(t ≤ w + r ∧ w + r ≤ k) := fun hc => by omega
    rw [if_neg hguard]
    ring
  · intro r hr
    rw [Finset.mem_range] at hr
    have hrt : r ≤ t := by omega
    have hrkw : r ≤ k - w := by omega
    by_cases hg1 : t ≤ w + r
    · have hgs : t ≤ w + r ∧ w + r ≤ k := ⟨hg1, by omega⟩
      rw [if_pos hgs]
      have hsymm : (k - t).choose (w + r - t) = (k - t).choose ((k - w) - r) := by
        rw [← Nat.choose_symm (by omega : w + r - t ≤ k - t)]
        congr 1
        omega
      rw [hsymm]
      ring
    · rw [if_neg fun hc => hg1 hc.1]
      have hz : (k - t).choose ((k - w) - r) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      push_cast
      ring
  · intro r hr hrS
    rw [Finset.mem_range] at hr hrS
    have hrt : t < r := by omega
    rw [Nat.choose_eq_zero_of_lt hrt]
    push_cast
    ring

end Positive

/-- **A non-separated pair kills the shell sum**: the swap of that pair fixes `K`, hence
permutes the shell, and negates the summand — an involution argument. -/
theorem sum_shell_pairDiff_eq_zero {K : Finset α} {k w : ℕ} {i : Fin t}
    (hns : a i ∈ K ↔ b i ∈ K) :
    ∑ L ∈ (Finset.univ.powersetCard k).filter (fun L => #(K ∩ L) = w),
        pairDiff ℤ a b L = 0 := by
  classical
  have hKfix : ∀ y, Equiv.swap (a i) (b i) y ∈ K ↔ y ∈ K := by
    intro y
    rcases eq_or_ne y (a i) with rfl | hya
    · rw [Equiv.swap_apply_left]
      exact hns.symm
    · rcases eq_or_ne y (b i) with rfl | hyb
      · rw [Equiv.swap_apply_right]
        exact hns
      · rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hmemmap : ∀ (L : Finset α) (y : α),
      y ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding ↔ Equiv.swap (a i) (b i) y ∈ L := by
    intro L y
    rw [Finset.mem_map_equiv, Equiv.symm_swap]
  have hinter : ∀ L : Finset α,
      K ∩ L.map (Equiv.swap (a i) (b i)).toEmbedding
        = (K ∩ L).map (Equiv.swap (a i) (b i)).toEmbedding := by
    intro L
    ext y
    rw [Finset.mem_inter, hmemmap, hmemmap, Finset.mem_inter, ← hKfix y]
  have hmem : ∀ L ∈ (Finset.univ.powersetCard k).filter (fun L => #(K ∩ L) = w),
      L.map (Equiv.swap (a i) (b i)).toEmbedding
        ∈ (Finset.univ.powersetCard k).filter (fun L => #(K ∩ L) = w) := by
    intro L hL
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hL ⊢
    exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hL.1.2⟩,
      by rw [hinter L, Finset.card_map]; exact hL.2⟩
  refine Finset.sum_involution
    (fun L _ => L.map (Equiv.swap (a i) (b i)).toEmbedding)
    (fun L _ => by rw [pairDiff_map_swap hab]; ring)
    (fun L _ hne heq => hne ?_) hmem (fun L _ => ?_)
  · have heq' : L.map (Equiv.swap (a i) (b i)).toEmbedding = L := heq
    refine pairDiff_eq_zero_of_mem_iff (i := i) ?_
    constructor
    · intro ha
      have h1 : a i ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding := by rw [heq']; exact ha
      rw [hmemmap, Equiv.swap_apply_left] at h1
      exact h1
    · intro hb
      have h1 : b i ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding := by rw [heq']; exact hb
      rw [hmemmap, Equiv.swap_apply_right] at h1
      exact h1
  · ext y
    rw [hmemmap, hmemmap, Equiv.swap_apply_self]

end PatternCount

/-! ## The flip reduction and the full identity -/

omit [Fintype α] in
/-- Flipping one pair negates the value everywhere: the `i₀`-th factor reverses, the rest are
untouched. No injectivity is needed. -/
theorem pairDiff_update_flip {R : Type*} [CommRing R] (i₀ : Fin t) (L : Finset α) :
    pairDiff R (Function.update a i₀ (b i₀)) (Function.update b i₀ (a i₀)) L
      = -pairDiff R a b L := by
  have hfac : ∀ j : Fin t,
      ((if Function.update a i₀ (b i₀) j ∈ L then (1 : R) else 0)
          - if Function.update b i₀ (a i₀) j ∈ L then 1 else 0)
        = (if j = i₀ then (-1 : R) else 1)
          * ((if a j ∈ L then (1 : R) else 0) - if b j ∈ L then 1 else 0) := by
    intro j
    rcases eq_or_ne j i₀ with rfl | hj
    · rw [Function.update_self, Function.update_self, if_pos rfl, neg_one_mul, neg_sub]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, if_neg hj, one_mul]
  rw [pairDiff, pairDiff, Finset.prod_congr rfl fun j _ => hfac j,
    Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i₀ fun _ => (-1 : R)]
  simp

omit [Fintype α] [DecidableEq α] in
/-- Flipping one pair preserves injectivity of the pair system: the flipped system is the old
one composed with the swap of the two slots. -/
theorem injective_sumElim_update (hab : Function.Injective (Sum.elim a b)) (i₀ : Fin t) :
    Function.Injective
      (Sum.elim (Function.update a i₀ (b i₀)) (Function.update b i₀ (a i₀))) := by
  have hcomp : Sum.elim (Function.update a i₀ (b i₀)) (Function.update b i₀ (a i₀))
      = Sum.elim a b ∘ (Equiv.swap (Sum.inl i₀) (Sum.inr i₀)) := by
    funext s
    rcases s with j | j
    · rcases eq_or_ne j i₀ with rfl | hj
      · simp [Function.update_self, Equiv.swap_apply_left]
      · rw [Function.comp_apply,
          Equiv.swap_apply_of_ne_of_ne (fun h => hj (Sum.inl_injective h)) Sum.inl_ne_inr]
        simp [Function.update_of_ne hj]
    · rcases eq_or_ne j i₀ with rfl | hj
      · simp [Function.update_self, Equiv.swap_apply_right]
      · rw [Function.comp_apply,
          Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (fun h => hj (Sum.inr_injective h))]
        simp [Function.update_of_ne hj]
  rw [hcomp]
  exact hab.comp (Equiv.injective _)

/-- The induction workhorse: the identity for separating `K`, by induction on the number of
negatively-met pairs, flipping one at a time. -/
theorem sum_shell_pairDiff_sep {K : Finset α} {k w : ℕ} (hK : #K = k) (hw : w ≤ k) :
    ∀ (N : ℕ) (a b : Fin t → α), Function.Injective (Sum.elim a b) →
      (∀ i, (a i ∈ K ∧ b i ∉ K) ∨ (b i ∈ K ∧ a i ∉ K)) →
      #(Finset.univ.filter fun i => b i ∈ K) = N →
      ∑ L ∈ (Finset.univ.powersetCard k).filter (fun L => #(K ∩ L) = w),
          pairDiff ℤ a b L
        = Delsarte.eberlein (Fintype.card α) k (k - w) t * pairDiff ℤ a b K := by
  intro N
  induction N with
  | zero =>
    intro a b hab hsep hcount
    have hbK : ∀ i, b i ∉ K := by
      intro i hbi
      have : i ∈ Finset.univ.filter fun i => b i ∈ K :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbi⟩
      rw [Finset.card_eq_zero.mp hcount] at this
      exact absurd this (Finset.notMem_empty i)
    have hpos : ∀ i, a i ∈ K ∧ b i ∉ K := fun i =>
      ((hsep i).resolve_right fun hc => hbK i hc.1).imp id id
    rw [sum_shell_pairDiff_pos hab hpos hK hw, pairDiff_eq_one (fun i => (hpos i).1) hbK,
      mul_one]
  | succ n ih =>
    intro a b hab hsep hcount
    have hne : (Finset.univ.filter fun i => b i ∈ K).Nonempty := by
      rw [← Finset.card_pos, hcount]
      omega
    obtain ⟨i₀, hi₀⟩ := hne
    have hbi₀ : b i₀ ∈ K := (Finset.mem_filter.mp hi₀).2
    have hneg : b i₀ ∈ K ∧ a i₀ ∉ K :=
      (hsep i₀).resolve_left fun hc => hc.2 hbi₀
    set a' := Function.update a i₀ (b i₀) with ha'
    set b' := Function.update b i₀ (a i₀) with hb'
    have hab' := injective_sumElim_update hab i₀
    have hsep' : ∀ i, (a' i ∈ K ∧ b' i ∉ K) ∨ (b' i ∈ K ∧ a' i ∉ K) := by
      intro i
      rcases eq_or_ne i i₀ with rfl | hi
      · rw [ha', hb']
        rw [Function.update_self, Function.update_self]
        exact Or.inl ⟨hneg.1, hneg.2⟩
      · rw [ha', hb', Function.update_of_ne hi, Function.update_of_ne hi]
        exact hsep i
    have hcount' : #(Finset.univ.filter fun i => b' i ∈ K) = n := by
      have hset : (Finset.univ.filter fun i => b' i ∈ K)
          = (Finset.univ.filter fun i => b i ∈ K).erase i₀ := by
        ext j
        rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
        constructor
        · intro ⟨hju, hjb⟩
          rcases eq_or_ne j i₀ with rfl | hj
          · rw [hb', Function.update_self] at hjb
            exact absurd hjb hneg.2
          · rw [hb', Function.update_of_ne hj] at hjb
            exact ⟨hj, hju, hjb⟩
        · intro ⟨hj, hju, hjb⟩
          rw [hb', Function.update_of_ne hj]
          exact ⟨hju, hjb⟩
      rw [hset, Finset.card_erase_of_mem hi₀, hcount]
      omega
    have hih := ih a' b' hab' hsep' hcount'
    rw [Finset.sum_congr rfl fun L (_ : L ∈ _) => pairDiff_update_flip i₀ L,
      Finset.sum_neg_distrib, pairDiff_update_flip i₀ K, mul_neg] at hih
    exact neg_inj.mp hih

/-- **The shell-sum identity**: for any pair system and any `k`-subset `K`, summing the
pair-difference function over the shell `{L : #L = k, #(K ∩ L) = w}` gives the Eberlein
number `E_{k−w}(t)` times the value at `K`. This is the whole combinatorial content of "the
pair-difference functions are common eigenvectors of the Johnson scheme". -/
theorem sum_shell_pairDiff (hab : Function.Injective (Sum.elim a b)) {K : Finset α}
    {k w : ℕ} (hK : #K = k) (hw : w ≤ k) :
    ∑ L ∈ (Finset.univ.powersetCard k).filter (fun L => #(K ∩ L) = w),
        pairDiff ℤ a b L
      = Delsarte.eberlein (Fintype.card α) k (k - w) t * pairDiff ℤ a b K := by
  by_cases hsep : ∀ i, ¬(a i ∈ K ↔ b i ∈ K)
  · refine sum_shell_pairDiff_sep hK hw _ a b hab (fun i => ?_) rfl
    by_cases haK : a i ∈ K
    · exact Or.inl ⟨haK, fun hbK => hsep i ⟨fun _ => hbK, fun _ => haK⟩⟩
    · by_cases hbK : b i ∈ K
      · exact Or.inr ⟨hbK, haK⟩
      · exact absurd ⟨fun h => absurd h haK, fun h => absurd h hbK⟩ (hsep i)
  · simp only [not_forall, not_not] at hsep
    obtain ⟨i, hi⟩ := hsep
    rw [sum_shell_pairDiff_eq_zero hab hi, pairDiff_eq_zero_of_mem_iff hi, mul_zero]

/-! ## Star and subset sums

The Johnson-scheme multiplicity computation (`Scheme/JohnsonMultiplicity.lean`) needs the
pair-difference sums over two further families: the **star** of a fixed base (the `k`-sets
containing it) and the `c`-subsets of a fixed set. The mechanism is the shell sum's: the flip
involution kills every sum the base leaves free, and on a transversal base the sum is a pure
count, delivered by `card_powersetCard_filter_superset`. -/

section StarSubset

variable {R : Type*} [CommRing R]

/-- **A pair untouched by the base kills the star sum**: the flip of that pair is an
involution on the star. -/
theorem sum_star_pairDiff_eq_zero (hab : Function.Injective (Sum.elim a b)) {A : Finset α}
    {k : ℕ} {i : Fin t} (hai : a i ∉ A) (hbi : b i ∉ A) :
    ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K), pairDiff R a b K = 0 := by
  have hmemmap : ∀ (L : Finset α) (y : α),
      y ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding ↔ Equiv.swap (a i) (b i) y ∈ L := by
    intro L y
    rw [Finset.mem_map_equiv, Equiv.symm_swap]
  have hAfix : ∀ y ∈ A, Equiv.swap (a i) (b i) y = y := fun y hy =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hai (h ▸ hy)) (fun h => hbi (h ▸ hy))
  have hmem : ∀ L ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K),
      L.map (Equiv.swap (a i) (b i)).toEmbedding
        ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K) := by
    intro L hL
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hL ⊢
    refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hL.1.2⟩, fun y hy => ?_⟩
    rw [hmemmap, hAfix y hy]
    exact hL.2 hy
  refine Finset.sum_involution
    (fun L _ => L.map (Equiv.swap (a i) (b i)).toEmbedding)
    (fun L _ => by rw [pairDiff_map_swap hab]; ring)
    (fun L _ hne heq => hne ?_) hmem (fun L _ => ?_)
  · have heq' : L.map (Equiv.swap (a i) (b i)).toEmbedding = L := heq
    refine pairDiff_eq_zero_of_mem_iff (i := i) ?_
    constructor
    · intro ha
      have h1 : a i ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding := by rw [heq']; exact ha
      rw [hmemmap, Equiv.swap_apply_left] at h1
      exact h1
    · intro hb
      have h1 : b i ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding := by rw [heq']; exact hb
      rw [hmemmap, Equiv.swap_apply_right] at h1
      exact h1
  · ext y
    rw [hmemmap, hmemmap, Equiv.swap_apply_self]

/-- **The star-and-avoid count**: `k`-sets through a base that itself avoids the `b`-points,
avoiding all `b`-points. The base need not contain the `a`-points. -/
theorem card_star_avoid (hab : Function.Injective (Sum.elim a b)) {A : Finset α} {k : ℕ}
    (hb : ∀ i, b i ∉ A) (hAk : #A ≤ k) :
    ((Finset.univ.powersetCard k).filter (fun K => A ⊆ K ∧ ∀ i, b i ∉ K)).card
      = (Fintype.card α - t - #A).choose (k - #A) := by
  classical
  have hbinj : Function.Injective b := fun j j' h =>
    Sum.inr_injective (@hab (Sum.inr j) (Sum.inr j') h)
  set B : Finset α := Finset.image b Finset.univ with hB
  have hsets : (Finset.univ.powersetCard k).filter (fun K => A ⊆ K ∧ ∀ i, b i ∉ K)
      = ((Finset.univ \ B).powersetCard k).filter (fun K => A ⊆ K) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hKcard⟩, hAK, hbK⟩
      refine ⟨⟨fun y hy => Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyB => ?_⟩, hKcard⟩,
        hAK⟩
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hyB
      exact hbK i (hi ▸ hy)
    · rintro ⟨⟨hKU, hKcard⟩, hAK⟩
      exact ⟨⟨Finset.subset_univ _, hKcard⟩, hAK, fun i hiK =>
        (Finset.mem_sdiff.mp (hKU hiK)).2
          (Finset.mem_image_of_mem b (Finset.mem_univ i))⟩
  rw [hsets, card_powersetCard_filter_superset
    (fun y hy => Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, fun hyB => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hyB
      exact hb i (hi ▸ hy)⟩) hAk]
  congr 2
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ B), Finset.card_univ,
    hB, Finset.card_image_of_injective _ hbinj, Finset.card_univ, Fintype.card_fin]

/-- **The star evaluation**: over a base containing every `a`-point and no `b`-point, the star
sum counts the extensions avoiding the `b`-points. -/
theorem sum_star_pairDiff_transversal (hab : Function.Injective (Sum.elim a b))
    {A : Finset α} {k : ℕ} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∉ A) (hAk : #A ≤ k) :
    ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K), pairDiff R a b K
      = ((Fintype.card α - t - #A).choose (k - #A) : R) := by
  classical
  have hval : ∀ K ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K),
      pairDiff R a b K = if ∀ i, b i ∉ K then 1 else 0 := by
    intro K hK
    have hAK : A ⊆ K := (Finset.mem_filter.mp hK).2
    by_cases hbK : ∀ i, b i ∉ K
    · rw [if_pos hbK]
      exact pairDiff_eq_one (fun i => hAK (ha i)) hbK
    · rw [if_neg hbK]
      simp only [not_forall, not_not] at hbK
      obtain ⟨i, hbi⟩ := hbK
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [if_pos (hAK (ha i)), if_pos hbi, sub_self]
  rw [Finset.sum_congr rfl hval, Finset.sum_boole, Finset.filter_filter,
    card_star_avoid hab hb hAk]

omit [Fintype α] in
/-- **A pair not split by the ambient set kills the subset sum**: both endpoints inside flip,
both outside vanish factor-wise. -/
theorem sum_powersetCard_pairDiff_eq_zero (hab : Function.Injective (Sum.elim a b))
    {K : Finset α} {c : ℕ} {i : Fin t} (hmem : a i ∈ K ↔ b i ∈ K) :
    ∑ B ∈ K.powersetCard c, pairDiff R a b B = 0 := by
  by_cases haK : a i ∈ K
  · have hbK := hmem.mp haK
    have hmemmap : ∀ (L : Finset α) (y : α),
        y ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding ↔ Equiv.swap (a i) (b i) y ∈ L := by
      intro L y
      rw [Finset.mem_map_equiv, Equiv.symm_swap]
    have hKmem : ∀ L ∈ K.powersetCard c,
        L.map (Equiv.swap (a i) (b i)).toEmbedding ∈ K.powersetCard c := by
      intro L hL
      rw [Finset.mem_powersetCard] at hL ⊢
      refine ⟨fun y hy => ?_, by rw [Finset.card_map]; exact hL.2⟩
      rw [hmemmap] at hy
      rcases eq_or_ne y (a i) with rfl | hya
      · exact haK
      rcases eq_or_ne y (b i) with rfl | hyb
      · exact hbK
      · rw [Equiv.swap_apply_of_ne_of_ne hya hyb] at hy
        exact hL.1 hy
    refine Finset.sum_involution
      (fun L _ => L.map (Equiv.swap (a i) (b i)).toEmbedding)
      (fun L _ => by rw [pairDiff_map_swap hab]; ring)
      (fun L _ hne heq => hne ?_) hKmem (fun L _ => ?_)
    · have heq' : L.map (Equiv.swap (a i) (b i)).toEmbedding = L := heq
      refine pairDiff_eq_zero_of_mem_iff (i := i) ?_
      constructor
      · intro ha
        have h1 : a i ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding := by rw [heq']; exact ha
        rw [hmemmap, Equiv.swap_apply_left] at h1
        exact h1
      · intro hb
        have h1 : b i ∈ L.map (Equiv.swap (a i) (b i)).toEmbedding := by rw [heq']; exact hb
        rw [hmemmap, Equiv.swap_apply_right] at h1
        exact h1
    · ext y
      rw [hmemmap, hmemmap, Equiv.swap_apply_self]
  · have hbK : b i ∉ K := fun h => haK (hmem.mpr h)
    refine Finset.sum_eq_zero fun B hB => ?_
    rw [Finset.mem_powersetCard] at hB
    exact pairDiff_eq_zero_of_mem_iff (i := i)
      ⟨fun h => absurd (hB.1 h) haK, fun h => absurd (hB.1 h) hbK⟩

omit [Fintype α] in
/-- **The subset evaluation**: inside a transversal ambient set, the subset sum counts the
`c`-subsets through the `a`-points. -/
theorem sum_powersetCard_pairDiff_transversal (hab : Function.Injective (Sum.elim a b))
    {K : Finset α} {c : ℕ} (ha : ∀ i, a i ∈ K) (hb : ∀ i, b i ∉ K) (htc : t ≤ c) :
    ∑ B ∈ K.powersetCard c, pairDiff R a b B = ((#K - t).choose (c - t) : R) := by
  classical
  have hainj : Function.Injective a := fun j j' h =>
    Sum.inl_injective (@hab (Sum.inl j) (Sum.inl j') h)
  set A₀ : Finset α := Finset.image a Finset.univ with hA₀
  have hval : ∀ B ∈ K.powersetCard c, pairDiff R a b B = if A₀ ⊆ B then 1 else 0 := by
    intro B hB
    have hBK := (Finset.mem_powersetCard.mp hB).1
    by_cases hAB : A₀ ⊆ B
    · rw [if_pos hAB]
      refine pairDiff_eq_one (fun i => hAB (Finset.mem_image_of_mem a (Finset.mem_univ i)))
        (fun i hbi => hb i (hBK hbi))
    · rw [if_neg hAB]
      obtain ⟨y, hyA, hyB⟩ := Finset.not_subset.mp hAB
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hyA
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [if_neg (hi ▸ hyB), if_neg (fun hbi => hb i (hBK hbi)), sub_self]
  rw [Finset.sum_congr rfl hval, Finset.sum_boole]
  have hcardA₀ : #A₀ = t := by
    rw [hA₀, Finset.card_image_of_injective _ hainj, Finset.card_univ, Fintype.card_fin]
  rw [card_powersetCard_filter_superset
    (fun y hy => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy
      exact hi ▸ ha i)
    (hcardA₀ ▸ htc), hcardA₀]

end StarSubset

end ECCLib

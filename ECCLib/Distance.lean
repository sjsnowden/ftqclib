/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Codes
import Mathlib.InformationTheory.Hamming

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Minimum distance and the Singleton bound

The distance layer's opening: the minimum distance of a linear code and the Singleton bound, the
first of the specifications the verified decoders will be checked against.

* **`minDist C`** — `sInf` of the Hamming weights of the nonzero codewords, as a **total**
  `ℕ`-valued function with junk value `0` at `C = ⊥` (`Nat.sInf ∅ = 0`). The convention is harmless:
  `minDist_eq_zero_iff` says the junk value occurs *exactly* at `⊥` (a weight-0 vector is `0`), so
  `minDist C ≥ 1` on every nontrivial code. Statements are kept **additive** (`d + k ≤ n + 1`)
  so ℕ-subtraction never appears in an interface.
* API: `minDist_le_of_mem`, `exists_minDist` (the distance is attained), `minDist_pos`,
  `minDist_le_card`, and `minDist_le_hammingDist` (any two distinct codewords are at least
  `minDist` apart — the decoding-radius fact).
* **`singleton_bound`** — `minDist C + finrank F C ≤ n + 1`, **unconditional** (at `C = ⊥` it
  reads `0 + 0 ≤ n + 1`; the junk convention is what makes the hypothesis-free statement true).
  Proof: delete `d − 1` coordinates — the restriction `LinearMap.funLeft` to the complement is
  injective on `C`, since a codeword vanishing there has weight `≤ d − 1 < d`; then count.
-/

namespace ECCLib.Coding

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Bound file-wide (the WeightEnumerator lesson): `hammingNorm`'s instance must be the same in
-- the definition and in every consumer's rewrite patterns.
variable [DecidableEq F]

/-! ## The minimum distance -/

/-- The **minimum distance** of a code: the least Hamming weight of a nonzero codeword, with junk
value `0` at `C = ⊥` (`Nat.sInf ∅ = 0`; see `minDist_eq_zero_iff`). -/
noncomputable def minDist (C : Submodule F (ι → F)) : ℕ :=
  sInf (hammingNorm '' {x : ι → F | x ∈ C ∧ x ≠ 0})

/-- The distance lower-bounds the weight of every nonzero codeword. -/
theorem minDist_le_of_mem {C : Submodule F (ι → F)} {x : ι → F} (hx : x ∈ C) (hx0 : x ≠ 0) :
    minDist C ≤ hammingNorm x :=
  Nat.sInf_le ⟨x, ⟨hx, hx0⟩, rfl⟩

/-- **The distance is attained**: a nontrivial code has a nonzero codeword of weight exactly
`minDist C`. -/
theorem exists_minDist {C : Submodule F (ι → F)} (h : C ≠ ⊥) :
    ∃ x ∈ C, x ≠ 0 ∧ hammingNorm x = minDist C := by
  obtain ⟨x, hxC, hx0⟩ := (Submodule.ne_bot_iff C).mp h
  obtain ⟨y, ⟨hyC, hy0⟩, hwt⟩ :=
    Nat.sInf_mem (⟨hammingNorm x, ⟨x, ⟨hxC, hx0⟩, rfl⟩⟩ :
      (hammingNorm '' {x : ι → F | x ∈ C ∧ x ≠ 0}).Nonempty)
  exact ⟨y, hyC, hy0, hwt⟩

/-- The junk value occurs exactly at the zero code. -/
theorem minDist_eq_zero_iff {C : Submodule F (ι → F)} : minDist C = 0 ↔ C = ⊥ := by
  constructor
  · intro h
    by_contra hbot
    obtain ⟨x, _, hx0, hwt⟩ := exists_minDist hbot
    rw [h] at hwt
    exact hx0 (hammingNorm_eq_zero.mp hwt)
  · intro h
    subst h
    have hset : {x : ι → F | x ∈ (⊥ : Submodule F (ι → F)) ∧ x ≠ 0} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Submodule.mem_bot, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hne⟩
      exact hne rfl
    unfold minDist
    rw [hset, Set.image_empty, Nat.sInf_empty]

/-- A nontrivial code has distance at least `1`. -/
theorem minDist_pos {C : Submodule F (ι → F)} (h : C ≠ ⊥) : 0 < minDist C :=
  Nat.pos_of_ne_zero fun h0 => h (minDist_eq_zero_iff.mp h0)

/-- A nontrivial code has distance at most `n`. -/
theorem minDist_le_card {C : Submodule F (ι → F)} (h : C ≠ ⊥) :
    minDist C ≤ Fintype.card ι := by
  obtain ⟨x, _, _, hwt⟩ := exists_minDist h
  rw [← hwt]
  exact hammingNorm_le_card_fintype

/-- **Distinct codewords are at least `minDist` apart** — the fact the decoding radius rests on:
by linearity, `x − y` is a nonzero codeword and `hammingDist x y = hammingNorm (x − y)`. -/
theorem minDist_le_hammingDist {C : Submodule F (ι → F)} {x y : ι → F}
    (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) : minDist C ≤ hammingDist x y := by
  rw [hammingDist_eq_hammingNorm]
  exact minDist_le_of_mem (C.add_mem (C.neg_mem hx) hy) fun h => hne (neg_add_eq_zero.mp h)

/-! ## The Singleton bound -/

/-- The weight is bounded by the cardinality of any Finset containing the support. -/
lemma hammingNorm_le_card_of_subset {x : ι → F} {S : Finset ι}
    (h : ∀ i, x i ≠ 0 → i ∈ S) : hammingNorm x ≤ S.card := by
  have hsub : Finset.univ.filter (fun i => ¬ x i = 0) ⊆ S := fun i hi =>
    h i (Finset.mem_filter.mp hi).2
  calc hammingNorm x = (Finset.univ.filter (fun i => ¬ x i = 0)).card := rfl
    _ ≤ S.card := Finset.card_le_card hsub

/-- **The Singleton bound**, unconditional: `d + k ≤ n + 1` for every linear code (at `C = ⊥` it
degenerates to `0 + 0 ≤ n + 1` — the junk convention is what makes the hypothesis-free form
true). Proof: choose `d − 1` coordinates; restriction to the complementary coordinates is
injective on `C` — a codeword vanishing there has weight `≤ d − 1 < d`, so it is zero — and
counting gives `q^k ≤ q^{n−(d−1)}`. -/
theorem singleton_bound (C : Submodule F (ι → F)) :
    minDist C + Module.finrank F C ≤ Fintype.card ι + 1 := by
  classical
  by_cases hbot : C = ⊥
  · subst hbot
    rw [minDist_eq_zero_iff.mpr rfl, finrank_bot]
    omega
  · obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
      (show minDist C - 1 ≤ (Finset.univ : Finset ι).card by
        rw [Finset.card_univ]
        have := minDist_le_card hbot
        omega)
    let π : (ι → F) →ₗ[F] ({ i : ι // i ∉ S } → F) := LinearMap.funLeft F F Subtype.val
    have hker : ∀ x ∈ C, π x = 0 → x = 0 := by
      intro x hxC hx0
      by_contra hne
      have hsupp : ∀ i, x i ≠ 0 → i ∈ S := by
        intro i hi
        by_contra hiS
        exact hi (congrFun hx0 ⟨i, hiS⟩)
      have hle : hammingNorm x ≤ S.card := hammingNorm_le_card_of_subset hsupp
      have hge : minDist C ≤ hammingNorm x := minDist_le_of_mem hxC hne
      have hpos : 0 < minDist C := minDist_pos hbot
      rw [hScard] at hle
      omega
    have hinj : Function.Injective (fun c : ↥C => π (c : ι → F)) := by
      intro a b hab
      have hab' : π (a : ι → F) = π (b : ι → F) := hab
      have h0 : π ((a : ι → F) - (b : ι → F)) = 0 := by
        rw [map_sub, hab', sub_self]
      exact Subtype.ext (sub_eq_zero.mp (hker _ (C.sub_mem a.2 b.2) h0))
    have hcard : Nat.card C ≤ Nat.card ({ i : ι // i ∉ S } → F) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective _ hinj
    have hC : Nat.card C = Fintype.card F ^ Module.finrank F C := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := ↥C)]
    have hsubc : Fintype.card { i : ι // i ∉ S }
        = Fintype.card ι - (minDist C - 1) := by
      have h1 : Fintype.card { i : ι // i ∉ S }
          = Fintype.card ι - Fintype.card { i : ι // i ∈ S } :=
        Fintype.card_subtype_compl _
      have h2 : Fintype.card { i : ι // i ∈ S } = S.card := Fintype.card_coe S
      rw [h1, h2, hScard]
    have hfun : Nat.card ({ i : ι // i ∉ S } → F)
        = Fintype.card F ^ (Fintype.card ι - (minDist C - 1)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, hsubc]
    rw [hC, hfun] at hcard
    have hk : Module.finrank F C ≤ Fintype.card ι - (minDist C - 1) :=
      (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp hcard
    have h1 : 0 < minDist C := minDist_pos hbot
    have h2 : minDist C ≤ Fintype.card ι := minDist_le_card hbot
    omega

end ECCLib.Coding

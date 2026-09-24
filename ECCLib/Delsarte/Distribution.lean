/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The distance distribution of an arbitrary code

`pairCount C i` is the unnormalised distance distribution — the number of ORDERED pairs
of codewords at Hamming distance `i`. It is `|C|` times the literature's normalised
`A_i` (Cohn–Zhao arXiv:1212.1913, §II) and `|C|` times McKinley's distribution vector
(4.1). Kept ℕ-valued and division-free; the carrier is a bare `Finset` of words over
ANY `DecidableEq` alphabet — no group, no field, no linearity.

The minimum distance enters every consumer as the hypothesis
`∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y`, never through a junk-valued `minDist`
function.
-/

namespace ECCLib.Delsarte

variable {ι : Type*} [Fintype ι] {β : Type*} [DecidableEq β]

/-- The unnormalised distance distribution: ordered pairs of codewords at distance `i`. -/
def pairCount (C : Finset (ι → β)) (i : ℕ) : ℕ :=
  ((C ×ˢ C).filter fun p => hammingDist p.1 p.2 = i).card

/-- Distance zero counts the diagonal: `N₀ = |C|`. -/
@[simp] theorem pairCount_zero (C : Finset (ι → β)) : pairCount C 0 = C.card := by
  unfold pairCount
  rw [eq_comm]
  apply Finset.card_nbij (i := fun x => (x, x))
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product]
    exact ⟨⟨hx, hx⟩, by simp⟩
  · intro x _ y _ hxy
    exact congrArg Prod.fst hxy
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
    obtain ⟨⟨h1, _⟩, hd⟩ := hp
    have : p.1 = p.2 := by rwa [← hammingDist_eq_zero]
    exact ⟨p.1, by simpa using h1, by rw [Prod.ext_iff]; exact ⟨rfl, this⟩⟩

/-- Total mass: `Σᵢ Nᵢ = |C|²`. -/
theorem sum_pairCount (C : Finset (ι → β)) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1), pairCount C i = C.card ^ 2 := by
  rw [sq, ← Finset.card_product]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : (ι → β) × (ι → β) => hammingDist p.1 p.2)
    (t := Finset.range (Fintype.card ι + 1))
    (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hammingDist_le_card_fintype)))]
  rfl

/-- The distance gap: below a hypothesis-carried lower bound `d`, all nonzero-distance
counts vanish. -/
theorem pairCount_eq_zero_of_lt {C : Finset (ι → β)} {d : ℕ}
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y)
    {i : ℕ} (h0 : i ≠ 0) (hi : i < d) :
    pairCount C i = 0 := by
  unfold pairCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hp
  simp only [Finset.mem_product] at hp
  intro hdist
  have hne : x ≠ y := by
    intro heq
    subst heq
    simp [hammingDist_self] at hdist
    exact h0 hdist.symm
  have hdd : hammingDist x y = i := hdist
  have := hd x hp.1 y hp.2 hne
  omega

end ECCLib.Delsarte

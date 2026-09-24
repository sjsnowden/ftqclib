/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.ReedMuller

set_option linter.unusedSectionVars false

/-!
# Reed's majority-logic decoder for RM(1,m)

A second verified decoder for the first-order Reed–Muller code `rm1` of `ReedMuller.lean` — Reed's
1954 majority-logic algorithm at first order. Where the Walsh–Hadamard decoder `fwhtDec` correlates
against all `2^(m+1)` codewords, Reed's decoder recovers each message bit by a
**majority vote**: for the coefficient of `xᵢ`, every point `x` casts the vote
`y x + y (x + eᵢ)` — which equals `a₀ i` exactly when neither `x` nor `x + eᵢ` is corrupted,
because the affine part telescopes (`pairing eᵢ a₀ = a₀ i`, characteristic 2). At most `2t`
of the `2^m` votes are bad, so the strict majority stands whenever `4t < 2^m` — the same
full half-distance radius as `fwhtDec_corrects`, at per-bit counting cost instead of
exhaustive correlation.

Votes are `Finset.card`s of decidable filters (each unordered pair `{x, x+eᵢ}` is counted
twice, which preserves majority) — no list machinery, and the decoder stays computable and
kernel-decidable. `Corrects` is proved directly (a bounded-distance statement, not a
minimum-distance-decoding claim).

Main results:

* `reedDec` — the computable decoder (total: always `some`);
* `reedDec_corrects` — `4t < 2^m ⟹ Corrects (reedDec m) (rm1 m) t`;
* worked examples at `m = 3`: the SAME corrupted transmission as in `ReedMuller.lean`
  (`rmSent + rmErr`) healed by `reedDec` — by theorem, by live kernel evaluation, and an
  **agreement row**: `reedDec` and `fwhtDec` return the same answer on it, by `decide`.
-/

namespace ECCLib.Coding

open ECCLib.Heisenberg

variable (m : ℕ)

/-! ## The decoder -/

/-- The 1-votes count for the coefficient of `xᵢ`: over ALL points `x`, the vote
`y x + y (x + eᵢ)` (each unordered pair counted twice — majority unaffected). -/
def votes1 (y : (Fin m → ZMod 2) → ZMod 2) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun x : Fin m → ZMod 2 => y x + y (x + Pi.single i 1) = 1).card

/-- **Reed's majority-logic decoder** for `RM(1,m)`: recover each linear coefficient by
majority vote over the difference quotients, then the constant term by majority over the
residual. Computable, per-bit counting cost. -/
def reedDec (y : (Fin m → ZMod 2) → ZMod 2) : Option ((Fin m → ZMod 2) → ZMod 2) :=
  let a : Fin m → ZMod 2 := fun i => if 2 ^ m < 2 * votes1 m y i then 1 else 0
  let b : ZMod 2 :=
    if 2 ^ m < 2 * (Finset.univ.filter fun x => y x + pairing x a = 1).card then 1 else 0
  some (affEval m (a, b))

/-! ## The counting lemmas -/

private lemma card_filter_univ (p : (Fin m → ZMod 2) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card + (Finset.univ.filter fun x => ¬ p x).card = 2 ^ m := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → ZMod 2))) (p := p)
  rwa [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h

/-- Shifting the argument is a support-preserving involution (characteristic 2). -/
private lemma card_shift (e : (Fin m → ZMod 2) → ZMod 2) (s : Fin m → ZMod 2) :
    (Finset.univ.filter fun x => e (x + s) ≠ 0).card
      = (Finset.univ.filter fun x => e x ≠ 0).card := by
  have hself : ∀ v : Fin m → ZMod 2, v + v = 0 := by
    intro v
    funext i
    have h2 : ∀ u : ZMod 2, u + u = 0 := by decide
    simpa using h2 (v i)
  refine Finset.card_bij' (fun x _ => x + s) (fun x _ => x + s) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rwa [add_assoc, hself, add_zero]
  · intro x _
    change x + s + s = x
    rw [add_assoc, hself, add_zero]
  · intro x _
    change x + s + s = x
    rw [add_assoc, hself, add_zero]

/-- At most `2·wt(e)` votes are bad: a bad vote needs an error at `x` or at `x + s`. -/
private lemma card_bad_le (e : (Fin m → ZMod 2) → ZMod 2) (s : Fin m → ZMod 2) :
    (Finset.univ.filter fun x => e x + e (x + s) ≠ 0).card ≤ 2 * hammingNorm e := by
  have hsub : (Finset.univ.filter fun x => e x + e (x + s) ≠ 0)
      ⊆ (Finset.univ.filter fun x => e x ≠ 0)
        ∪ (Finset.univ.filter fun x => e (x + s) ≠ 0) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : e x = 0
    · by_cases h2 : e (x + s) = 0
      · exact absurd (by rw [h1, h2, add_zero]) hx.2
      · exact Or.inr ⟨Finset.mem_univ _, h2⟩
    · exact Or.inl ⟨Finset.mem_univ _, h1⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter fun x : Fin m → ZMod 2 => e x ≠ 0)
    (Finset.univ.filter fun x => e (x + s) ≠ 0)
  have h3 := card_shift m e s
  have hn : (Finset.univ.filter fun x : Fin m → ZMod 2 => e x ≠ 0).card = hammingNorm e := rfl
  omega

/-! ## Correctness -/

/-- **The correction guarantee**: Reed's decoder corrects `t` errors whenever `4t < 2^m` —
the same full half-distance radius as the Walsh–Hadamard decoder, at counting cost. -/
theorem reedDec_corrects {t : ℕ} (ht : 4 * t < 2 ^ m) :
    Corrects (reedDec m) (rm1 m) t := by
  intro c hc e he
  obtain ⟨⟨a₀, b₀⟩, rfl⟩ := LinearMap.mem_range.mp hc
  have hself2 : ∀ u : ZMod 2, u + u = 0 := by decide
  have hcase : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  -- the vote identity: the affine part telescopes to the coefficient
  have hvote : ∀ (i : Fin m) (x : Fin m → ZMod 2),
      (affEval m (a₀, b₀) + e) x + (affEval m (a₀, b₀) + e) (x + Pi.single i 1)
        = a₀ i + (e x + e (x + Pi.single i 1)) := by
    intro i x
    simp only [Pi.add_apply, affEval_apply]
    rw [pairing_add_left, pairing_single]
    linear_combination hself2 (pairing x a₀) + hself2 b₀
  -- the linear coefficients are recovered
  have ha : (fun i => if 2 ^ m < 2 * votes1 m (affEval m (a₀, b₀) + e) i then (1 : ZMod 2)
      else 0) = a₀ := by
    funext i
    have hbad := card_bad_le m e (Pi.single i 1)
    have hpart := card_filter_univ m (fun x => e x + e (x + Pi.single i 1) ≠ 0)
    have hv1 : votes1 m (affEval m (a₀, b₀) + e) i
        = (Finset.univ.filter fun x =>
            a₀ i + (e x + e (x + Pi.single i 1)) = 1).card := by
      unfold votes1
      exact congrArg Finset.card (Finset.filter_congr fun x _ => by rw [hvote i x])
    rcases hcase (a₀ i) with h0 | h1
    · have hle : votes1 m (affEval m (a₀, b₀) + e) i ≤ 2 * hammingNorm e := by
        rw [hv1, h0]
        refine le_trans (Finset.card_le_card ?_) hbad
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have h := hx.2
        rw [zero_add] at h
        rw [h]
        exact one_ne_zero
      rw [if_neg (by omega), h0]
    · have hge : 2 ^ m ≤ votes1 m (affEval m (a₀, b₀) + e) i + 2 * hammingNorm e := by
        rw [hv1, h1]
        have hcongr : (Finset.univ.filter fun x : Fin m → ZMod 2 =>
              (1 : ZMod 2) + (e x + e (x + Pi.single i 1)) = 1)
            = Finset.univ.filter fun x => ¬ (e x + e (x + Pi.single i 1) ≠ 0) := by
          refine Finset.filter_congr fun x _ => ?_
          have h : ∀ u : ZMod 2, ((1 : ZMod 2) + u = 1) ↔ ¬ (u ≠ 0) := by decide
          exact h _
        rw [hcongr]
        omega
      rw [if_pos (by omega), h1]
  -- the constant term is recovered from the residual
  have hres : ∀ x, (affEval m (a₀, b₀) + e) x + pairing x a₀ = b₀ + e x := by
    intro x
    simp only [Pi.add_apply, affEval_apply]
    linear_combination hself2 (pairing x a₀)
  have hb : (if 2 ^ m < 2 * (Finset.univ.filter fun x =>
      (affEval m (a₀, b₀) + e) x + pairing x a₀ = 1).card then (1 : ZMod 2) else 0)
      = b₀ := by
    have hv : (Finset.univ.filter fun x =>
          (affEval m (a₀, b₀) + e) x + pairing x a₀ = 1).card
        = (Finset.univ.filter fun x => b₀ + e x = 1).card :=
      congrArg Finset.card (Finset.filter_congr fun x _ => by rw [hres x])
    have hpart := card_filter_univ m (fun x => e x ≠ 0)
    have hwt : (Finset.univ.filter fun x : Fin m → ZMod 2 => e x ≠ 0).card
        = hammingNorm e := rfl
    rcases hcase b₀ with h0 | h1
    · have hle : (Finset.univ.filter fun x =>
          (affEval m (a₀, b₀) + e) x + pairing x a₀ = 1).card ≤ hammingNorm e := by
        rw [hv, h0, ← hwt]
        refine Finset.card_le_card ?_
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have h := hx.2
        rw [zero_add] at h
        rw [h]
        exact one_ne_zero
      rw [if_neg (by omega), h0]
    · have hge : 2 ^ m ≤ (Finset.univ.filter fun x =>
          (affEval m (a₀, b₀) + e) x + pairing x a₀ = 1).card + hammingNorm e := by
        rw [hv, h1]
        have hcongr : (Finset.univ.filter fun x : Fin m → ZMod 2 =>
              (1 : ZMod 2) + e x = 1)
            = Finset.univ.filter fun x => ¬ (e x ≠ 0) := by
          refine Finset.filter_congr fun x _ => ?_
          have h : ∀ u : ZMod 2, ((1 : ZMod 2) + u = 1) ↔ ¬ (u ≠ 0) := by decide
          exact h _
        rw [hcongr]
        omega
      rw [if_pos (by omega), h1]
  simp only [reedDec]
  rw [ha, hb]

/-! ## Worked examples — the `ReedMuller.lean` transmission, healed by the second decoder -/

/-- `RM(1,3)` corrects one error through Reed's decoder. -/
theorem reedDec_corrects_one : Corrects (reedDec 3) (rm1 3) 1 :=
  reedDec_corrects 3 (by norm_num)

/-- **The corrected transmission, by theorem** — the SAME corrupted word as in
`ReedMuller.lean`. -/
theorem reedDec_transmission : reedDec 3 (rmSent + rmErr) = some rmSent :=
  reedDec_corrects_one rmSent (LinearMap.mem_range_self _ _) rmErr (by decide)

/-- **The corrected transmission, by evaluation**: the kernel runs the majority votes. -/
example : reedDec 3 (rmSent + rmErr) = some rmSent := by decide

/-- **The agreement row**: two verified decoders — exhaustive correlation and majority
logic — return the same answer on the same corrupted word, machine-checked. -/
example : reedDec 3 (rmSent + rmErr) = fwhtDec 3 (rmSent + rmErr) := by decide

end ECCLib.Coding

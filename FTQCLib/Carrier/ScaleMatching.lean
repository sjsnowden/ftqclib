/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.BackwardConstructions

/-!
# Scale matching

A helper module for `RewriteCompleteness.lean` (T07, `docs/TARGETS.md`): given a carrier state and
a target dyadic factor `charOf m b * √2^e` at the state's own precision `m`, a chain of
`CarrierRuleWithin` steps — an unused bound bit added (`exists_unusedBit`), a pad by halving
(`exists_pad`, iterated) or another unused bit (iterated) to reach the needed power of `√2`, and one
gauge rewrite R1 (`GaugeStep.addC`) to reach the needed root of unity — brings a new carrier state,
related to the input, whose scale is exactly the input's scale times that factor. Assembling this
against an arbitrary dyadic ratio (`IsDyadicRatio`, decision D9, whose root of unity may have order
larger than `2^m`) is `RewriteCompleteness.lean`'s concern, after a lift to a large enough
precision; this module only ever produces roots of unity of order dividing `2^m`, at a fixed
precision.

## Main results

* `exists_scale_match` — over a carrier state `⟨m, h, Q, c, L, x₀⟩`, a residue `b : ZMod (2^m)` and
  an integer `e`, there is a carrier state at the same precision, related to the input by a chain of
  `CarrierRuleWithin` steps, with scale `charOf m b * c * √2^e`.

## Implementation notes

* The height changes along the chain; matching it to another state's is `exists_pad`'s and
  `exists_unusedBit`'s concern (already public, `BackwardConstructions.lean`), not this lemma's.
* One `exists_unusedBit` first, unconditionally, reaches height at least one; from there `√2^e` is
  reached by `e + 1` more pads (`e + 1 ≥ 0`) or `−(e + 1)` more unused bits (`e + 1 < 0`), each
  iterated by an induction private to this module. The root of unity is reached last, by one R1 that
  leaves every other field alone: `Q₀ − C b` gauges to `Q₀` with the scale gaining `charOf m b`,
  read backwards from the constructor (`GaugeStep.addC` with parameter `−b`).
* Everything here is frame-pure: no `FTQCLib.Hilbert` module and nothing from `FTQCLib/Explore/`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

section Helpers

/-! ### Iterating the two `√2`-scaling constructions -/

/-- **Iterated unused bits.** Over a carrier state `⟨m, h, Q, c, L, x₀⟩`, adding `k` unused bound
bits one at a time reaches a carrier state at the same precision, with scale `c / √2^k`, related to
the input by a chain of `CarrierRuleWithin` steps. -/
private theorem exists_unusedBit_iter {m : ℕ} (k : ℕ) {h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) :
    ∃ Q' : DiagPhase (n + (h + k)) m,
      IsCarrier (⟨m, h + k, Q', c / (Real.sqrt 2 : ℂ) ^ k, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + k, Q', c / (Real.sqrt 2 : ℂ) ^ k, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  induction k with
  | zero => exact ⟨Q, by simpa using hS, by simpa using Relation.EqvGen.refl _⟩
  | succ k ih =>
      obtain ⟨Qk, hCk, hChk⟩ := ih
      obtain ⟨Qk1, hCk1, hChk1⟩ := exists_unusedBit hCk
      have heq : c / (Real.sqrt 2 : ℂ) ^ (k + 1)
          = c / (Real.sqrt 2 : ℂ) ^ k / (Real.sqrt 2 : ℂ) := by
        rw [pow_succ, div_div]
      refine ⟨Qk1, by rw [heq]; exact hCk1, by
        rw [heq]
        exact Relation.EqvGen.trans _ _ _ hChk1 hChk⟩

/-- **Iterated pads.** Over a carrier state `⟨m, h + 1, Q, c, L, x₀⟩`, padding `k` times reaches a
carrier state at the same precision, with scale `c * √2^k`, related to the input by a chain of
`CarrierRuleWithin` steps. -/
private theorem exists_pad_iter {m : ℕ} (k h : ℕ) {Q : DiagPhase (n + (h + 1)) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) :
    ∃ Q' : DiagPhase (n + (h + k + 1)) m,
      IsCarrier (⟨m, h + k + 1, Q', c * (Real.sqrt 2 : ℂ) ^ k, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + k + 1, Q', c * (Real.sqrt 2 : ℂ) ^ k, L, x₀⟩ ⟨m, h + 1, Q, c, L, x₀⟩ := by
  induction k with
  | zero => exact ⟨Q, by simpa using hS, by simpa using Relation.EqvGen.refl _⟩
  | succ k ih =>
      obtain ⟨Qk, hCk, hChk⟩ := ih
      obtain ⟨Qk1, hCk1, hChk1⟩ := exists_pad hCk
      have heq : c * (Real.sqrt 2 : ℂ) ^ (k + 1)
          = c * (Real.sqrt 2 : ℂ) ^ k * (Real.sqrt 2 : ℂ) := by
        rw [pow_succ]; ring
      refine ⟨Qk1, by rw [heq]; exact hCk1, by
        rw [heq]
        exact Relation.EqvGen.trans _ _ _ hChk1 hChk⟩

end Helpers

section ScaleMatch

/-- **Scale matching.** Over a carrier state `⟨m, h, Q, c, L, x₀⟩`, a residue `b : ZMod (2^m)` and
an integer `e`, there is a carrier state at the same precision, related to the input by a chain of
`CarrierRuleWithin` steps, with scale `charOf m b * c * √2^e`: one unused bit reaches height at
least one, `e + 1` further pads or `−(e + 1)` further unused bits reach the power of `√2`, and one
R1 reaches the root of unity. -/
theorem exists_scale_match {m h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) (b : ZMod (2 ^ m)) (e : ℤ) :
    ∃ (h' : ℕ) (Q' : DiagPhase (n + h') m),
      IsCarrier (⟨m, h', Q', charOf m b * c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h', Q', charOf m b * c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  have hm : 1 ≤ m := hS.1
  -- Step 1: one unused bit, unconditionally, reaches height at least one.
  obtain ⟨Q1, hC1, hCh1⟩ := exists_unusedBit hS
  -- Step 2: reach the power of `√2`, from height `h + 1`.
  obtain ⟨h'', Q2, hC2, hCh2, hscale2⟩ :
      ∃ (h'' : ℕ) (Q2 : DiagPhase (n + h'') m),
        IsCarrier (⟨m, h'', Q2, c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩ : KernelSumState n) ∧
        Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
          ⟨m, h'', Q2, c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩
          ⟨m, h + 1, Q1, c / (Real.sqrt 2 : ℂ), L, x₀⟩ ∧ True := by
    by_cases hge : 0 ≤ e + 1
    · set k : ℕ := (e + 1).toNat with hk
      have hke : (k : ℤ) = e + 1 := by rw [hk, Int.toNat_of_nonneg hge]
      obtain ⟨Q2, hC2, hCh2⟩ := exists_pad_iter k h hC1
      have heq : c / (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) ^ k = c * (Real.sqrt 2 : ℂ) ^ e := by
        have hz : (Real.sqrt 2 : ℂ) ^ k = (Real.sqrt 2 : ℂ) ^ (e + 1) := by
          rw [← zpow_natCast (Real.sqrt 2 : ℂ) k, hke]
        rw [hz, zpow_add₀ ofReal_sqrt_two_ne_zero, zpow_one]
        field_simp
      rw [heq] at hC2 hCh2
      exact ⟨h + k + 1, Q2, hC2, hCh2, trivial⟩
    · set k : ℕ := (-(e + 1)).toNat with hk
      have hke : (k : ℤ) = -(e + 1) := by rw [hk, Int.toNat_of_nonneg (by omega)]
      obtain ⟨Q2, hC2, hCh2⟩ := exists_unusedBit_iter (h := h + 1) (Q := Q1)
        (c := c / (Real.sqrt 2 : ℂ)) k hC1
      have heq : c / (Real.sqrt 2 : ℂ) / (Real.sqrt 2 : ℂ) ^ k = c * (Real.sqrt 2 : ℂ) ^ e := by
        have hz : (Real.sqrt 2 : ℂ) ^ k = (Real.sqrt 2 : ℂ) ^ (-(e + 1)) := by
          rw [← zpow_natCast (Real.sqrt 2 : ℂ) k, hke]
        rw [hz, zpow_neg, zpow_add₀ ofReal_sqrt_two_ne_zero, zpow_one]
        field_simp
      rw [heq] at hC2 hCh2
      exact ⟨h + 1 + k, Q2, hC2, hCh2, trivial⟩
  clear hC1
  -- Step 3: reach the root of unity, by one R1.
  have hstep : CarrierRule
      (⟨m, h'', Q2 - MvPolynomial.C b, charOf m b * c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩ :
        KernelSumState n)
      (⟨m, h'', Q2, c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩ : KernelSumState n) := by
    have hstep0 := CarrierRule.gauge
      (GaugeStep.addC (n := n) Q2 (-b) (charOf m b * c * (Real.sqrt 2 : ℂ) ^ e) L x₀)
    have hscale : charOf m b * c * (Real.sqrt 2 : ℂ) ^ e * charOf m (-b)
        = c * (Real.sqrt 2 : ℂ) ^ e := by
      have h0 : b + (-b) = (0 : ZMod (2 ^ m)) := by ring
      have hone : charOf m b * charOf m (-b) = 1 := by
        rw [← charOf_add, h0, charOf_zero]
      rw [mul_right_comm (charOf m b * c) ((Real.sqrt 2 : ℂ) ^ e) (charOf m (-b)),
        mul_right_comm (charOf m b) c (charOf m (-b)), hone, one_mul]
    have hQeq : Q2 + MvPolynomial.C (-b) = Q2 - MvPolynomial.C b := by
      rw [map_neg]; ring
    rw [hQeq, hscale] at hstep0
    exact hstep0
  have hCX : IsCarrier
      (⟨m, h'', Q2 - MvPolynomial.C b, charOf m b * c * (Real.sqrt 2 : ℂ) ^ e, L, x₀⟩ :
        KernelSumState n) :=
    isCarrier_of_stateEq hC2 (stateEq_of_carrierRule hstep) hm hC2.2.1 hC2.2.2.1
  exact ⟨h'', Q2 - MvPolynomial.C b, hCX,
    Relation.EqvGen.trans _ _ _ (eqvGen_carrierRuleWithin_of_carrierRule hstep hCX rfl hC2 rfl)
      (Relation.EqvGen.trans _ _ _ hCh2 hCh1)⟩

end ScaleMatch

end FTQCLib.Frame.Walkthrough

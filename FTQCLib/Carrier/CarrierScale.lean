/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Protocol
import FTQCLib.Carrier.ConditionFloor

/-!
# The scale along a protocol

Every step a protocol or its processing takes multiplies a carrier state's scale `c` by an integer
power of `√2`, or sets it to zero: a letter by `1` or `1/√2` (H's free rule), a conditioning by
`1/√2` or `1/2`, `restrictZ` by `1/√2` or to zero off its slice, and the bulk forms by products of
these. Two states reached from one scale this way have a dyadic ratio of scales (decision D9),
which is the half of `rewrite_complete` that `StateEq` does not give. So a statement that a
processed branch is related to a unitary's output by T07's rules (`Relation.EqvGen CarrierRule`)
needs only `StateEq` and the two scales tracked from the input's.

The capstones of phase 2 (`HInject.lean`, `RemoteCH.lean`, `DiagonalInjection.lean`) each proved
these facts privately, in two copies (docs/STEPS.md, entry 2026-10-01g); they live here, once.

## Main definitions

* `ScaledBy c c'` — `c'` is `c` times an integer power of `√2`, or zero.

## Main results

* `scaledBy_applyLetter`, `scaledBy_run`, `scaledBy_condition`, `scaledBy_interpret`,
  `scaledBy_restrictZ`, `scaledBy_restrictLast` — each step scales by a power of `√2`, or to zero.
* `isDyadicRatio_of_scaledBy` — two nonzero scales tracked from one have a dyadic ratio.
* `eqvGen_carrierRule_of_scaledBy` — two carrier states that are `StateEq`, with scales tracked
  from one, are related by T07's rules.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## Scaling by a power of `√2` -/

/-- `c'` is `c` times an integer power of `√2`, or zero. -/
def ScaledBy (c c' : ℂ) : Prop :=
  c' = 0 ∨ ∃ e : ℤ, c' = (Real.sqrt 2 : ℂ) ^ e * c

/-- Every scale is scaled by `√2^0`. -/
theorem ScaledBy.refl (c : ℂ) : ScaledBy c c :=
  Or.inr ⟨0, by rw [zpow_zero, one_mul]⟩

/-- Scalings compose. -/
theorem ScaledBy.trans {a c d : ℂ} (h1 : ScaledBy a c) (h2 : ScaledBy c d) : ScaledBy a d := by
  rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl h2
  rcases h1 with h1 | ⟨e1, h1⟩
  · exact Or.inl (by rw [h2, h1, mul_zero])
  exact Or.inr ⟨e2 + e1, by rw [h2, h1, zpow_add₀ ofReal_sqrt_two_ne_zero, mul_assoc]⟩

/-- Dividing by `√2` is a scaling. -/
theorem ScaledBy.div_sqrt_two (c : ℂ) : ScaledBy c (c / (Real.sqrt 2 : ℂ)) :=
  Or.inr ⟨-1, by rw [zpow_neg_one, div_eq_inv_mul]⟩

/-- Dividing by `2` is a scaling. -/
theorem ScaledBy.div_two (c : ℂ) : ScaledBy c (c / 2) :=
  Or.inr ⟨-2, by
    rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sqrt_two_sq_complex,
      div_eq_inv_mul]⟩

/-! ## Each step scales by a power of `√2` -/

/-- A letter scales by `1` or `1/√2`. -/
theorem scaledBy_applyLetter {m : ℕ} (g : GateLetter n m) (S : KernelSumState n) :
    ScaledBy S.c (applyLetter g S).c := by
  cases g with
  | hadamard k =>
    rw [applyLetter_hadamard]
    unfold applyH
    split
    · exact ScaledBy.div_sqrt_two S.c
    · exact ScaledBy.refl S.c
  | diagonal D =>
    change ScaledBy S.c (if hm : S.m = m then applyDiagSum S (hm ▸ D) else S).c
    split
    · exact ScaledBy.refl S.c
    · exact ScaledBy.refl S.c
  | cnot i k hik => exact ScaledBy.refl S.c

/-- A word scales by a power of `√2`. -/
theorem scaledBy_run {m : ℕ} (gs : GateWord n m) (S : KernelSumState n) :
    ScaledBy S.c (run gs S).c := by
  induction gs generalizing S with
  | nil => exact ScaledBy.refl S.c
  | cons g gs ih =>
    rw [run_cons]
    exact (scaledBy_applyLetter g S).trans (ih _)

/-- Conditioning scales by `1/√2` or `1/2`. -/
theorem scaledBy_condition (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    ScaledBy S.c (condition S P b).c := by
  unfold condition
  split
  · exact ScaledBy.div_sqrt_two S.c
  · exact ScaledBy.div_two S.c

/-- A protocol's interpretation scales by a power of `√2`. -/
theorem scaledBy_interpret {m k : ℕ} (p : Protocol m n k) (S : KernelSumState n) :
    ScaledBy S.c (p.interpret S).c := by
  induction p with
  | nil => exact ScaledBy.refl S.c
  | word p w ih =>
    rw [Protocol.interpret_word]
    exact ih.trans (scaledBy_run w _)
  | condition p P hP ih =>
    rw [Protocol.interpret_condition]
    exact ih.trans (scaledBy_condition (appendFreeBit (p.interpret S)) P.appendZ 0)

/-- `restrictZ` scales by `1/√2`, or to zero off the slice. -/
theorem scaledBy_restrictZ (j : Fin (n + 1)) (b : ZMod 2) (S : KernelSumState (n + 1)) :
    ScaledBy S.c (restrictZ j b S).c := by
  have hC := scaledBy_condition S (signedZ j) b
  change ScaledBy S.c (sliceZ j b (condition S (signedZ j) b)).c
  unfold sliceZ
  split
  · exact hC
  · exact Or.inl rfl

/-- Dropping the last `k` free bits scales by a power of `√2`, or to zero. -/
theorem scaledBy_restrictLast :
    ∀ (k : ℕ) (o : Fin k → ZMod 2) (T : KernelSumState (n + k)),
      ScaledBy T.c (restrictLast k o T).c
  | 0, _, T => ScaledBy.refl T.c
  | k + 1, o, T =>
    (scaledBy_restrictZ (Fin.last (n + k)) (o (Fin.last k)) T).trans
      (scaledBy_restrictLast k (Fin.init o) _)

/-! ## Scales tracked from one have a dyadic ratio -/

/-- Two nonzero scales, each `c` times a power of `√2`, have a dyadic ratio. -/
theorem isDyadicRatio_of_scaledBy {c c₁ c₂ : ℂ} (h₁ : ScaledBy c c₁) (h₂ : ScaledBy c c₂)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) : IsDyadicRatio (c₂ / c₁) := by
  rcases h₁ with h₁ | ⟨e₁, h₁⟩
  · exact absurd h₁ hc₁
  rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact absurd h₂ hc₂
  have hc : c ≠ 0 := by
    rintro rfl
    exact hc₁ (by rw [h₁, mul_zero])
  refine ⟨1, 0, e₂ - e₁, by norm_num, ?_⟩
  rw [one_mul, h₁, h₂, zpow_sub₀ ofReal_sqrt_two_ne_zero]
  have := zpow_ne_zero e₁ ofReal_sqrt_two_ne_zero
  field_simp

/-- **Related by T07's rules.** Two carrier states that are `StateEq`, whose scales are each a
scale `c` times a power of `√2`, are related by `Relation.EqvGen CarrierRule`
(`rewrite_complete`). -/
theorem eqvGen_carrierRule_of_scaledBy {S T : KernelSumState n} {c : ℂ} (hS : IsCarrier S)
    (hT : IsCarrier T) (hST : StateEq S T) (hcS : ScaledBy c S.c) (hcT : ScaledBy c T.c) :
    Relation.EqvGen CarrierRule S T :=
  (rewrite_complete hS hT).mpr ⟨hST,
    isDyadicRatio_of_scaledBy hcS hcT (c_ne_zero_of_isCarrier hS) (c_ne_zero_of_isCarrier hT)⟩

end FTQCLib.Frame.Walkthrough

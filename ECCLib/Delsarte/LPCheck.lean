/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.LP

set_option linter.style.longLine false

/-!
# The LP bound — regression checks

A concrete integer certificate discharged field-by-field by `decide`, driven through
the floor form to an end-to-end kernel-backed Delsarte bound
(`A₂(4,3) ≤ 2` — the LP optimum 8/3 is fractional, so this instance EXERCISES the
floor); a machine-checked demonstration that the banned ceiling form loses a unit on
exactly this instance; and the build-failing axiom sweep.
-/

namespace ECCLib.Delsarte

/-- An independently verified certificate for `(q, n, d) = (2, 4, 3)`: `β = (3, 1, 0, 0, 1)`,
value `f(0) = 8`, LP optimum `8/3`. -/
def cert243 : LPCert 2 4 3 where
  beta := fun k => if k = 0 then 3 else if k = 1 then 1 else if k = 4 then 1 else 0
  beta_nonneg := by
    intro k
    split_ifs <;> norm_num
  beta_zero_pos := by norm_num
  neg := by decide

theorem check_cert243_value : cert243.value = 8 := by decide

/-- The floor lands on the sharp answer: `⌊8/3⌋ = 2 = A₂(4,3)`. -/
theorem check_cert243_floor : (cert243.value / cert243.beta 0).toNat = 2 := by decide

/-- **Floor, not ceiling, machine-checked**: the ceiling form `value ≤ M·β₀` CANNOT
reach `M = 2` on this instance (`8 ≤ 6` is false) — the ceiling form provably loses a
unit exactly where the LP optimum is fractional. The floor form above reaches 2. -/
theorem check_ceiling_loses_unit : ¬ (cert243.value ≤ 2 * cert243.beta 0) := by decide

/-- The certificate transported to the concrete carrier types. -/
def cert243' : LPCert (Fintype.card (ZMod 2)) (Fintype.card (Fin 4)) 3 := cert243

/-- **An end-to-end Delsarte LP bound**: every binary code of
length 4 with pairwise distances ≥ 3 has at most 2 codewords. Sharp
(`{0000, 1110}` attains it). -/
theorem check_A2_4_3 (C : Finset (Fin 4 → ZMod 2))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ hammingDist x y) : C.card ≤ 2 := by
  have h := cert243'.card_le_floor C hd
  have hval : (cert243'.value / cert243'.beta 0).toNat = 2 := by decide
  omega

/-- Sharpness witness: the code `{0000, 1110}` has 2 words at distance 3. -/
def attain243 : Finset (Fin 4 → ZMod 2) := {![0, 0, 0, 0], ![1, 1, 1, 0]}

theorem check_attain243_card : attain243.card = 2 := by decide
theorem check_attain243_dist :
    ∀ x ∈ attain243, ∀ y ∈ attain243, x ≠ y → 3 ≤ hammingDist x y := by decide

end ECCLib.Delsarte

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Delsarte.delsarte_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.delsarte_nonneg

/-- info: 'ECCLib.Delsarte.delsarte_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.delsarte_feasible

/-- info: 'ECCLib.Delsarte.LPCert.mul_le_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.LPCert.mul_le_value

/-- info: 'ECCLib.Delsarte.LPCert.card_mul_le_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.LPCert.card_mul_le_value

/-- info: 'ECCLib.Delsarte.LPCert.card_mul_le_value_alphabet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.LPCert.card_mul_le_value_alphabet

/-- info: 'ECCLib.Delsarte.LPCert.card_le_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.LPCert.card_le_floor

/-- info: 'ECCLib.Delsarte.LPCert.card_le_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.LPCert.card_le_of_strict

/-- info: 'ECCLib.Delsarte.check_A2_4_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.check_A2_4_3

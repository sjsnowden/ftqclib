/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierAmplitude
import FTQCLib.Examples.HadamardRaise

/-!
# Check: the carrier's denotation and its gauge

Each gauge rewrite has a hypothesis, and each row here shows one is load-bearing on a one-qubit
record at precision one with the flat exponent, where `amp` is computed by hand through
`ampCore_zero`.

* **R3 (`amp_congr_xProj`).** The shadow matters: the point state `L = ⊥` and the flat state
  `L = ⊤` at the same offset have different denotations (`control_shadow_matters`), so the shadow
  equality is not decorative.
* **R2 (`amp_offset_add_mem`).** Translating the offset by a vector *outside* the shadow moves the
  denotation (`control_x0_off_shadow_matters`), so `v ∈ π_X(L)` is not decorative.
* **R1 (`amp_add_C`).** Adding the constant `1` to the exponent at `m = 1` without touching the
  scale flips the sign (`control_const_needs_c`), so the phase on `c` is not decorative.
* **R4, R5 (`amp_congr_support`, `amp_rename_bound`).** Changing the exponent *on* the support
  moves the denotation (`control_support_exponent_matters`), so the evaluation hypotheses are not
  decorative; at `h = 0` the identity is the only bijection of the bound words, and this row is
  the `σ = id` instance for R5 as well.

The agreement row reaches one record two ways: by R1 the constant `1` at `m = 1` is the scale
`exp(iπ)`, and `exp(iπ) = −1` by Mathlib, so the record with exponent `C 1` and scale `1` is the
state with exponent `0` and scale `−1` (`agreement_const_is_sign`).

`StateEq` is not trivial: the point and flat states are not state-equal (`stateEq_not_trivial`).

What no row here tests: anything with a bound register (`h ≥ 1`) — the bound-register rows belong
with the carrier's closure under `H` (`CarrierStateHadamardCheck`); the co-isotropy of `L` (not a
hypothesis of any gauge theorem). The denotation is `ℂ`-valued and noncomputable (`Complex.exp`), so
no row is a kernel row — the absence is forced, not skipped. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## Hand-computed values on the one-qubit examples -/

/-- `amp` at the flat `n = 1`, `m = 1`, `h = 0` state with `L = ⊤` and `x₀ = 0` is `1`
everywhere. -/
theorem control_amp_top (w : Fin 1 → ZMod 2) :
    amp (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) w = 1 := by
  have hsup : ∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 1)), w = (0 : Fin 1 → ZMod 2) + p.X :=
    ⟨⟨w, 0⟩, Submodule.mem_top, by funext j; simp⟩
  rw [amp_pos (S := (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1)) hsup]
  change ampCore 1 0 (0 : DiagPhase (1 + 0) 1) 1 w = 1
  rw [ampCore_zero]
  have h0 : DiagPhase.realPhase (0 : DiagPhase (1 + 0) 1) w = 0 := by
    unfold DiagPhase.realPhase DiagPhase.eval
    simp
  rw [h0]
  simp

/-- `amp` off the support of the point state `L = ⊥`, `x₀ = y`, is zero. -/
theorem control_amp_bot_off {y w : Fin 1 → ZMod 2} (hne : w ≠ y) :
    amp (⟨1, 0, 0, 1, ⊥, y⟩ : KernelSumState 1) w = 0 := by
  refine amp_neg (S := (⟨1, 0, 0, 1, ⊥, y⟩ : KernelSumState 1)) ?_
  rintro ⟨p, hp, hw⟩
  rw [Submodule.mem_bot] at hp
  subst hp
  exact hne (by simpa using hw)

/-- `amp` at the word `0` of the point state at the origin is `1`. -/
theorem control_amp_bot_on :
    amp (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1) 0 = 1 := by
  have hsup : ∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 1)),
      (0 : Fin 1 → ZMod 2) = (0 : Fin 1 → ZMod 2) + p.X :=
    ⟨0, Submodule.zero_mem _, by simp⟩
  rw [amp_pos (S := (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1)) hsup]
  change ampCore 1 0 (0 : DiagPhase (1 + 0) 1) 1 0 = 1
  rw [ampCore_zero]
  have h0 : DiagPhase.realPhase (0 : DiagPhase (1 + 0) 1) 0 = 0 := by
    unfold DiagPhase.realPhase DiagPhase.eval
    simp
  rw [h0]
  simp

/-- The flat state with the constant `1` in the exponent at `m = 1` has amplitude `−1` at `0`. -/
theorem control_amp_top_const :
    amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1, 1, ⊤, 0⟩ : KernelSumState 1) 0
      = -1 := by
  have hsup : ∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 1)),
      (0 : Fin 1 → ZMod 2) = (0 : Fin 1 → ZMod 2) + p.X :=
    ⟨0, Submodule.mem_top, by simp⟩
  rw [amp_pos (S := (⟨1, 0, (0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1, 1, ⊤, 0⟩
    : KernelSumState 1)) hsup]
  change ampCore 1 0 ((0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1) 1 0 = -1
  rw [ampCore_zero]
  have hev : DiagPhase.realPhase ((0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1) 0
      = Real.pi := by
    have he : DiagPhase.eval ((0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1) 0
        = (1 : ZMod (2 ^ 1)) := by
      rw [DiagPhase.eval_add, DiagPhase.eval_C]
      simp [DiagPhase.eval]
    have hval : (1 : ZMod (2 ^ 1)).val = 1 := by decide
    unfold DiagPhase.realPhase
    rw [he, hval]
    norm_num
  rw [hev, one_mul, mul_comm]
  exact Complex.exp_pi_mul_I

/-- The flat state with the exponent `X 0` at `m = 1` has amplitude `−1` at the word `1`. -/
theorem control_amp_top_X :
    amp (⟨1, 0, MvPolynomial.X 0, 1, ⊤, 0⟩ : KernelSumState 1) ![1] = -1 := by
  have hsup : ∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 1)),
      (![1] : Fin 1 → ZMod 2) = (0 : Fin 1 → ZMod 2) + p.X :=
    ⟨⟨![1], 0⟩, Submodule.mem_top, by funext j; simp⟩
  rw [amp_pos (S := (⟨1, 0, MvPolynomial.X 0, 1, ⊤, 0⟩ : KernelSumState 1)) hsup]
  change ampCore 1 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 1) 1 ![1] = -1
  rw [ampCore_zero]
  have hev : DiagPhase.realPhase (MvPolynomial.X 0 : DiagPhase (1 + 0) 1) ![1] = Real.pi := by
    have he : DiagPhase.eval (MvPolynomial.X 0 : DiagPhase (1 + 0) 1) ![1]
        = (1 : ZMod (2 ^ 1)) := by
      rw [DiagPhase.eval_X]
      decide
    have hval : (1 : ZMod (2 ^ 1)).val = 1 := by decide
    unfold DiagPhase.realPhase
    rw [he, hval]
    norm_num
  rw [hev, one_mul, mul_comm]
  exact Complex.exp_pi_mul_I

/-! ## The hypotheses of the gauge rewrites are load-bearing -/

/-- **R3's control.** `amp` genuinely depends on the X-shadow: the point and flat states differ. -/
theorem control_shadow_matters :
    amp (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1) ≠ amp (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) := by
  intro hEq
  have h1 : amp (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1) ![1] = 0 :=
    control_amp_bot_off (by decide)
  have h2 : amp (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) ![1] = 1 := control_amp_top _
  rw [hEq, h2] at h1
  exact one_ne_zero h1

/-- **R2's control.** Translating `x₀` by a vector *outside* the shadow moves `amp`. -/
theorem control_x0_off_shadow_matters :
    amp (⟨1, 0, 0, 1, ⊥, (0 : Fin 1 → ZMod 2) + ![1]⟩ : KernelSumState 1)
      ≠ amp (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1) := by
  intro hEq
  have h1 : amp (⟨1, 0, 0, 1, ⊥, (0 : Fin 1 → ZMod 2) + ![1]⟩ : KernelSumState 1) 0 = 0 := by
    refine amp_neg (S := (⟨1, 0, 0, 1, ⊥, (0 : Fin 1 → ZMod 2) + ![1]⟩ : KernelSumState 1)) ?_
    rintro ⟨p, hp, hw⟩
    rw [Submodule.mem_bot] at hp
    subst hp
    have := congrFun hw 0
    revert this
    simp
  have h2 : amp (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1) 0 = 1 := control_amp_bot_on
  rw [hEq, h2] at h1
  exact one_ne_zero h1

/-- **R1's control.** Adding a constant to the exponent *without* changing `c` moves `amp`: at
`m = 1`, `a = 1`, the constant is the global sign `−1`. -/
theorem control_const_needs_c :
    amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1, 1, ⊤, 0⟩ : KernelSumState 1)
      ≠ amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1), 1, ⊤, 0⟩ : KernelSumState 1) := by
  intro hEq
  have h1 := control_amp_top_const
  have h2 : amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1), 1, ⊤, 0⟩ : KernelSumState 1) 0 = 1 :=
    control_amp_top _
  rw [hEq, h2] at h1
  exact absurd h1 (by norm_num)

/-- **R4's and R5's control.** Changing the exponent *on* the support moves `amp`: the flat
state with exponent `X 0` differs from the flat state with exponent `0`. -/
theorem control_support_exponent_matters :
    amp (⟨1, 0, MvPolynomial.X 0, 1, ⊤, 0⟩ : KernelSumState 1)
      ≠ amp (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) := by
  intro hEq
  have h1 := control_amp_top_X
  have h2 : amp (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) ![1] = 1 := control_amp_top _
  rw [hEq, h2] at h1
  exact absurd h1 (by norm_num)

/-! ## Agreement: the constant `1` at `m = 1` is the sign `−1` -/

/-- **Agreement row.** By R1 the record with exponent `C 1` and scale `1` is the record with
exponent `0` and scale `exp(iπ)`; by Mathlib `exp(iπ) = −1`. -/
theorem agreement_const_is_sign :
    amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1) + MvPolynomial.C 1, 1, ⊤, 0⟩ : KernelSumState 1)
      = amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1), -1, ⊤, 0⟩ : KernelSumState 1) := by
  rw [amp_add_C]
  have hval : (((1 : ZMod (2 ^ 1)).val : ℕ) : ℝ) = 1 := by
    have h : (1 : ZMod (2 ^ 1)).val = 1 := by decide
    rw [h]
    norm_num
  have hπ : ((2 * Real.pi * (((1 : ZMod (2 ^ 1)).val : ℕ) : ℝ) / (2 : ℝ) ^ 1 : ℝ) : ℂ)
      = (Real.pi : ℂ) := by
    rw [hval]
    push_cast
    ring
  have hc : (1 : ℂ) * Complex.exp (Complex.I
      * ((2 * Real.pi * (((1 : ZMod (2 ^ 1)).val : ℕ) : ℝ) / (2 : ℝ) ^ 1 : ℝ) : ℂ)) = -1 := by
    rw [hπ, one_mul, mul_comm]
    exact Complex.exp_pi_mul_I
  rw [hc]

/-- The agreement row's two sides, evaluated at the word `0`, both give `−1`. -/
theorem agreement_const_is_sign_value :
    amp (⟨1, 0, (0 : DiagPhase (1 + 0) 1), -1, ⊤, 0⟩ : KernelSumState 1) 0 = -1 := by
  rw [← agreement_const_is_sign]
  exact control_amp_top_const

/-! ## `StateEq` is not trivial -/

/-- The point state and the flat state are not state-equal. -/
theorem stateEq_not_trivial :
    ¬ StateEq (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1) (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) :=
  control_shadow_matters

/-- The setoid's relation agrees with `StateEq` on the witnesses. -/
theorem stateSetoid_not_trivial :
    ¬ stateSetoid 1 (⟨1, 0, 0, 1, ⊥, 0⟩ : KernelSumState 1)
        (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 1) :=
  fun h => stateEq_not_trivial ((stateSetoid_rel _ _).mp h)

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.amp' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp

/-- info: 'FTQCLib.Frame.Walkthrough.amp_pos' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_pos

/-- info: 'FTQCLib.Frame.Walkthrough.amp_neg' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_neg

/-- info: 'FTQCLib.Frame.Walkthrough.mem_support_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms mem_support_iff

/-- info: 'FTQCLib.Frame.Walkthrough.StateEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms StateEq

/-- info: 'FTQCLib.Frame.Walkthrough.StateEq.refl' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms StateEq.refl

/-- info: 'FTQCLib.Frame.Walkthrough.StateEq.symm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms StateEq.symm

/-- info: 'FTQCLib.Frame.Walkthrough.StateEq.trans' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms StateEq.trans

/-- info: 'FTQCLib.Frame.Walkthrough.stateSetoid' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms stateSetoid

/-- info: 'FTQCLib.Frame.Walkthrough.stateSetoid_rel' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms stateSetoid_rel

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_add_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ampCore_add_C

/-- info: 'FTQCLib.Frame.Walkthrough.amp_add_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_add_C

/-- info: 'FTQCLib.Frame.Walkthrough.amp_offset_add_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_offset_add_mem

/-- info: 'FTQCLib.Frame.Walkthrough.amp_congr_xProj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_congr_xProj

/-- info: 'FTQCLib.Frame.Walkthrough.zeroZ' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zeroZ

/-- info: 'FTQCLib.Frame.Walkthrough.map_xProj_zeroZ' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms map_xProj_zeroZ

/-- info: 'FTQCLib.Frame.Walkthrough.amp_zeroZ' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_zeroZ

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_congr' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ampCore_congr

/-- info: 'FTQCLib.Frame.Walkthrough.amp_congr_support' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_congr_support

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_reindex' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ampCore_reindex

/-- info: 'FTQCLib.Frame.Walkthrough.amp_rename_bound' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_rename_bound

end FTQCLib.Frame.Walkthrough

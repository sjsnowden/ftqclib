/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PrecisionGauge
import FTQCLib.Carrier.DyadicCharacter

/-!
# Check: the precision lift as a gauge rewrite (R7), on a concrete instance

T02's witness: a carrier state at precision two lifted to precision three, with its amplitude
unchanged, and the discriminating row that makes the `2^(k−m)` scaling in `dmapTo`
(`FTQCLib/Hierarchy/PrecisionLift.lean`) load-bearing: carrying the same numeral over to the
higher precision without scaling it is a different state.

One qubit, `m = 2` lifted to `k = 3`, flat record (`L = ⊤`, `x₀ = 0`) so every `w` is on support
and `amp` reduces to `ampCore` (`amp_pos`, as in `CarrierAmplitudeCheck.control_amp_top`); `h = 0`
so `ampCore` reduces to the single term (`ampCore_zero`). The exponent is the constant `1` (a
quarter turn at precision two); `liftTo` scales it to `2` at precision three (`2/8`, the same
angle, `1/4` of a turn) — the agreement row is the exact instance of R7, drawn directly from
`FTQCLib.Hilbert.liftTo_realPhase`, not from the theorem (`FTQCLib.Frame.Walkthrough.amp_liftTo`)
this instance witnesses. Carrying the numeral `1` over unscaled instead reads `1/8` of a turn — a
different angle — and `charOf_eq_iff` (`DyadicCharacter.lean`) turns the difference of angles into
the difference of amplitudes.

R7 on a whole carrier state, `liftPrecision`, is the same record: on `Stwo` at `k = 3` it is `Slift`
by definition, and its amplitude lemma reads the agreement row again at the state level.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## The flat one-qubit record: every `w` is on support -/

/-- Every `w : Fin 1 → ZMod 2` is on the support of the flat record `L = ⊤`, `x₀ = 0`
(as `CarrierAmplitudeCheck.control_amp_top`). -/
theorem mem_support_flat_one (w : Fin 1 → ZMod 2) :
    ∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 1)), w = (0 : Fin 1 → ZMod 2) + p.X :=
  ⟨⟨w, 0⟩, Submodule.mem_top, by funext j; simp⟩

/-! ## The instance: `m = 2` lifted to `k = 3`, exponent the constant `1` -/

/-- The precision-two exponent: the constant `1` (a quarter turn). -/
noncomputable def Qtwo : DiagPhase 1 2 := MvPolynomial.C (1 : ZMod (2 ^ 2))

/-- The precision-two record. -/
noncomputable def Stwo : KernelSumState 1 := ⟨2, 0, Qtwo, 1, ⊤, 0⟩

/-- The precision-three record correctly lifted from `Qtwo` by `FTQCLib.Hilbert.liftTo`, which
scales the coefficient by `2^(3-2) = 2`. -/
noncomputable def Slift : KernelSumState 1 :=
  ⟨3, 0, FTQCLib.Hilbert.liftTo 3 (by norm_num) Qtwo, 1, ⊤, 0⟩

/-- The precision-three record carrying the same numeral `1` over **unscaled** — the nearest
wrong object to `Slift`: same shape, same numeral, the `2^(k−m)` doubling missing. -/
noncomputable def Swrong : KernelSumState 1 :=
  ⟨3, 0, (MvPolynomial.C (1 : ZMod (2 ^ 3)) : DiagPhase 1 3), 1, ⊤, 0⟩

/-- **Agreement.** Lifting `Qtwo` from precision two to precision three leaves `amp` unchanged:
the instance of R7 this witness step tests, from `liftTo_realPhase` (exact, already proved). -/
-- row: agreement
theorem amp_Slift_eq_amp_Stwo : amp Slift = amp Stwo := by
  funext w
  rw [amp_pos (S := Slift) (mem_support_flat_one w), amp_pos (S := Stwo) (mem_support_flat_one w)]
  change ampCore 3 0 (FTQCLib.Hilbert.liftTo 3 (by norm_num) Qtwo) 1 w = ampCore 2 0 Qtwo 1 w
  rw [ampCore_zero, ampCore_zero, FTQCLib.Hilbert.liftTo_realPhase]

/-- `amp Swrong` at `w = 0`, read off through `charOf`. -/
theorem amp_Swrong_zero : amp Swrong (0 : Fin 1 → ZMod 2) = charOf 3 (1 : ZMod (2 ^ 3)) := by
  rw [amp_pos (S := Swrong) (mem_support_flat_one 0)]
  change ampCore 3 0 (MvPolynomial.C (1 : ZMod (2 ^ 3)) : DiagPhase 1 3) 1
      (0 : Fin 1 → ZMod 2) = charOf 3 (1 : ZMod (2 ^ 3))
  rw [ampCore_zero, exp_realPhase_eq_charOf, DiagPhase.eval_C, one_mul]

/-- `amp Slift` at `w = 0`, read off through `charOf`: the numeral `1`, correctly doubled by
`dmapTo` to `2` at precision three. -/
theorem amp_Slift_zero : amp Slift (0 : Fin 1 → ZMod 2) = charOf 3 (2 : ZMod (2 ^ 3)) := by
  rw [amp_pos (S := Slift) (mem_support_flat_one 0)]
  change ampCore 3 0 (FTQCLib.Hilbert.liftTo 3 (by norm_num) Qtwo) 1
      (0 : Fin 1 → ZMod 2) = charOf 3 (2 : ZMod (2 ^ 3))
  rw [ampCore_zero, exp_realPhase_eq_charOf, FTQCLib.Hilbert.liftTo_eval]
  unfold Qtwo
  rw [DiagPhase.eval_C, one_mul]
  congr 1

/-- **Discriminating.** The unscaled carry-over `Swrong` is a different state from the correctly
lifted `Slift`: at `w = 0` their amplitudes are the characters of `1` and `2` in `ZMod 8`, two
different residues (`decide`), so `charOf_eq_iff` separates the amplitudes — the `2^(k−m)`
scaling in `dmapTo` is not decorative. -/
-- row: discriminating
theorem amp_Swrong_ne_amp_Slift : amp Swrong ≠ amp Slift := by
  intro hfun
  have hw := congrFun hfun (0 : Fin 1 → ZMod 2)
  rw [amp_Swrong_zero, amp_Slift_zero] at hw
  exact absurd ((charOf_eq_iff 3 _ _).mp hw) (by decide)

/-- **Agreement, at the state level.** `liftPrecision` on `Stwo` at precision three is `Slift`, by
definition, and `amp_liftPrecision` gives the amplitude of `amp_Slift_eq_amp_Stwo` again. -/
-- row: agreement
theorem amp_liftPrecision_Stwo :
    liftPrecision Stwo 3 (show 2 ≤ 3 by norm_num) = Slift
      ∧ amp (liftPrecision Stwo 3 (show 2 ≤ 3 by norm_num)) = amp Stwo :=
  ⟨rfl, amp_liftPrecision Stwo 3 (show 2 ≤ 3 by norm_num)⟩

/-- **Agreement, the character of a lifted exponent.** `charOf_eval_liftTo` on `Qtwo` at `w = 0`:
the character of the lifted value `2` at precision three is the character of `1` at precision two,
both a quarter turn. -/
-- row: agreement
theorem charOf_eval_liftTo_Qtwo :
    charOf 3 ((FTQCLib.Hilbert.liftTo 3 (by norm_num) Qtwo).eval (0 : Fin 1 → ZMod 2))
      = charOf 2 (Qtwo.eval (0 : Fin 1 → ZMod 2)) :=
  charOf_eval_liftTo 3 (by norm_num) Qtwo 0

/-- **Inhabitation.** The hypotheses of `amp_liftTo` (the headline theorem: `m ≤ k`, an exponent
at precision `m`, an amplitude, a Lagrangian and a base point) hold together: applied to
`m = 2`, `k = 3`, `hmk : 2 ≤ 3`, `Qtwo`, `c = 1`, `L = ⊤`, `x₀ = 0`, the flat one-qubit
instance used throughout this witness. -/
-- row: inhabitation
example := amp_liftTo (n := 1) (m := 2) (h := 0) 3 (by norm_num) Qtwo 1 ⊤ (0 : Fin 1 → ZMod 2)

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

namespace FTQCLib.Frame.Walkthrough

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_liftTo' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_liftTo

/-- info: 'FTQCLib.Frame.Walkthrough.amp_liftTo' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_liftTo

/-- info: 'FTQCLib.Frame.Walkthrough.stateEq_liftTo' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_liftTo

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_eval_liftTo' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charOf_eval_liftTo

/-- info: 'FTQCLib.Frame.Walkthrough.liftPrecision' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.amp_liftPrecision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_liftPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_liftPrecision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_liftPrecision

end FTQCLib.Frame.Walkthrough

-- mutant: amp_liftTo_hmk_dir | FTQCLib/Carrier/PrecisionGauge.lean | theorem amp_liftTo {m h : ℕ} (k : ℕ) (hmk : m ≤ k) | theorem amp_liftTo {m h : ℕ} (k : ℕ) (hmk : k ≤ m)

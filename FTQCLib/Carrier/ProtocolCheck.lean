/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Protocol
import FTQCLib.Carrier.FeedForwardCheck
import FTQCLib.Carrier.GateWordCheck

/-!
# Check: protocols on `∣++⟩`

T14's witness (`docs/STEPS.md`, T14.2): rows on the frozen statement of `Protocol.lean`, on the
instance of T13.2 (`FeedForwardCheck.lean`): `∣++⟩` (`plusPlusState`) conditioned on `Z₀Z₁`
(`zzParity`) and corrected by `X₀` controlled by the outcome bit.

* **Row 1 (agreement).** T13.2's protocol as a term, `bellProtocol` (condition on `Z₀Z₁`, then
  `X₀` controlled by the outcome bit, at precision `1`): its branch at every outcome string is
  the evaluation of T13.2's corrected state (`correctOutcome`) at that outcome.
* **Row 2 (agreement).** Its branch at every outcome string is the Bell state's amplitude.
* **Row 3 (discriminating).** Two terms with two outcome bits: condition on `Z₀Z₁` (outcome bit
  `2`), then on `+I` (outcome bit `3`, whose outcome `1` has amplitude zero), then `X₀`
  controlled by one outcome bit. The term reading bit `2` (`rightProtocol`) and the term reading
  bit `3`, the wrong outcome bit (`wrongProtocol`), have different branches at the outcome string
  `(1, 0)`: at the data word `(0, 0)` the first has amplitude `1` and the second `0`.
* **Row 4 (inhabitation).** The hypotheses of `amp_interpret` and `branch_weights_sum` hold
  together for `bellProtocol` on the Bell state (`bellState`, `isCarrier_bellState`): a carrier
  state at the protocol's precision `1`. Not on `∣++⟩`: T13.2's record of it takes `L = ⊤`, which
  is co-isotropic but not isotropic, so it is not a carrier state, and rows 1 to 3, which use only
  co-isotropy, are computed without `amp_interpret`.

`amp_interpret` (proved at T14.3.1), `branch_weights_sum` (T14.3.2) and `protocol_complete`
(T14.3.3) are now proved. No row below uses any of the three: every amplitude above is computed
directly from `amp_conditionOutcome` (`Conditioning.lean`) and `amp_run_controlledPauliWord`
(`FeedForward.lean`), with the precision along the run from `interpret_m`, matching what the three
headline theorems conclude in general.

Frame form (D5): the rows compare amplitude functions on the free bits; no `FTQCLib.Hilbert`
object is named, and `Protocol.lean` imports none.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer
open Protocol

/-! ## The instance -/

/-- `Z₀Z₁` has no Y. -/
theorem yWeight_zzParity : yWeight zzParity.pauli = 0 := by
  unfold yWeight zDot zzParity
  simp

/-- `Z₀Z₁` needs no precision above `1`. -/
theorem zzParity_precision : yWeight zzParity.pauli % 2 = 1 → 2 ≤ 1 := by
  rw [yWeight_zzParity]
  intro h
  exact absurd h (by decide)

/-- **T13.2's protocol as a term**: condition `∣++⟩`'s bits on `Z₀Z₁`, the outcome a new free bit
`2`, then `X₀` controlled by that bit, at precision `1`. -/
noncomputable def bellProtocol : Protocol 1 2 1 :=
  ((nil : Protocol 1 2 0).condition zzParity zzParity_precision).word
    (controlledPauliWord (Fin.last 2) xFirst.appendId)

/-- The conditioned state is at precision `1`, by `interpret_m`. -/
theorem conditionOutcome_plusPlusState_m : (conditionOutcome plusPlusState zzParity).m = 1 :=
  interpret_m ((nil : Protocol 1 2 0).condition zzParity zzParity_precision) le_rfl rfl

/-- `X₀`, extended by the identity, has X-part `0` at the outcome bit. -/
theorem xFirst_appendId_X_last : xFirst.appendId.pauli.X (Fin.last 2) = 0 := by
  show (Fin.snoc (Pi.single (0 : Fin 2) (1 : ZMod 2)) (0 : ZMod 2) : Fin 3 → ZMod 2)
      (Fin.last 2) = 0
  rw [Fin.snoc_last]

/-- `X₀`, extended by the identity, needs no precision above `1`. -/
theorem xFirst_appendId_precision : yWeight xFirst.appendId.pauli % 2 = 1 → 2 ≤ 1 := by
  rw [yWeight_xFirst_appendId]
  intro h
  exact absurd h (by decide)

/-- The interpretation of `bellProtocol` has the amplitude of T13.2's corrected state: both are
the referee of the controlled `X₀` on the same conditioned state. -/
theorem amp_bellProtocol_interpret :
    amp (bellProtocol.interpret plusPlusState)
      = amp (correctOutcome plusPlusState zzParity xFirst) := by
  rw [amp_correctOutcome_plusPlusState]
  exact amp_run_controlledPauliWord _ _ xFirst_appendId_X_last le_rfl
    xFirst_appendId_precision _ conditionOutcome_plusPlusState_m

/-! ## Two outcome bits -/

/-- `+I` on three bits: conditioning on it creates an outcome bit whose outcome `1` has
amplitude zero. -/
def identityThree : SignedPauli 3 := ⟨0, 0⟩

/-- `X₀` with sign `+`, on the two data bits and two outcome bits. -/
def xFirstFour : SignedPauli 4 := ⟨0, ⟨Pi.single (0 : Fin 4) 1, 0⟩⟩

/-- `+I` needs no precision above `1`. -/
theorem identityThree_precision : yWeight identityThree.pauli % 2 = 1 → 2 ≤ 1 := by
  show yWeight (0 : Pauli 3) % 2 = 1 → 2 ≤ 1
  rw [yWeight_zero]
  intro h
  exact absurd h (by decide)

/-- `X₀` on four bits has no Y. -/
theorem yWeight_xFirstFour : yWeight xFirstFour.pauli = 0 := by
  unfold yWeight zDot xFirstFour
  simp

/-- `X₀` on four bits needs no precision above `1`. -/
theorem xFirstFour_precision : yWeight xFirstFour.pauli % 2 = 1 → 2 ≤ 1 := by
  rw [yWeight_xFirstFour]
  intro h
  exact absurd h (by decide)

/-- Condition on `Z₀Z₁` (outcome bit `2`), then on `+I` (outcome bit `3`). -/
noncomputable def twoOutcomeProtocol : Protocol 1 2 2 :=
  ((nil : Protocol 1 2 0).condition zzParity zzParity_precision).condition identityThree
    identityThree_precision

/-- **The right feed-forward**: `X₀` controlled by outcome bit `2`, the `Z₀Z₁` outcome. -/
noncomputable def rightProtocol : Protocol 1 2 2 :=
  twoOutcomeProtocol.word (controlledPauliWord (Fin.natAdd 2 (0 : Fin 2)) xFirstFour)

/-- **The wrong feed-forward**: `X₀` controlled by outcome bit `3`, the `+I` outcome. -/
noncomputable def wrongProtocol : Protocol 1 2 2 :=
  twoOutcomeProtocol.word (controlledPauliWord (Fin.natAdd 2 (1 : Fin 2)) xFirstFour)

/-- The state after `Z₀Z₁` keeps `∣++⟩`'s co-isotropic Lagrangian, extended by the new bit: the
X-part of `Z₀Z₁ ⊗ Z` is `0`, in every shadow, so conditioning is the bound constructor. -/
theorem conditionOutcome_plusPlusState_orth :
    LinearMap.BilinForm.orthogonal omegaBilin (conditionOutcome plusPlusState zzParity).L
      ≤ (conditionOutcome plusPlusState zzParity).L := by
  have hX : zzParity.appendZ.pauli.X ∈ Submodule.map xProj (appendFreeBit plusPlusState).L := by
    have h0 : zzParity.appendZ.pauli.X = 0 := by
      funext i
      show (Fin.snoc (0 : Fin 2 → ZMod 2) (0 : ZMod 2) : Fin 3 → ZMod 2) i = 0
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        rfl
    rw [h0]
    exact Submodule.zero_mem _
  unfold conditionOutcome
  rw [condition_of_mem hX, conditionBound_L]
  exact orthogonal_appendFreeBit_le plusPlusState plusPlusState_orth

/-- The state after both conditioning letters is at precision `1`, by `interpret_m`. -/
theorem twoOutcomeProtocol_m : (twoOutcomeProtocol.interpret plusPlusState).m = 1 :=
  interpret_m twoOutcomeProtocol le_rfl rfl

/-- The state after both conditioning letters: `Π_{v₃}(+I)` of the `Z₀Z₁`-conditioned
amplitude. -/
theorem amp_twoOutcomeProtocol (v : Fin 4 → ZMod 2) :
    amp (twoOutcomeProtocol.interpret plusPlusState) v
      = pauliProjection identityThree (v (Fin.last 3))
          (amp (conditionOutcome plusPlusState zzParity)) (Fin.init v) := by
  show amp (conditionOutcome (conditionOutcome plusPlusState zzParity) identityThree) v = _
  rw [amp_conditionOutcome _ conditionOutcome_plusPlusState_orth]

/-- The state after both conditioning letters, at every word: `1` where outcome bit `3` is `0` and
the data bits' parity is outcome bit `2`, `0` elsewhere. -/
theorem amp_twoOutcomeProtocol_eq (v : Fin 4 → ZMod 2) :
    amp (twoOutcomeProtocol.interpret plusPlusState) v
      = if v 3 = 0 then (if v 0 + v 1 = v 2 then 1 else 0) else 0 := by
  rw [amp_twoOutcomeProtocol]
  unfold pauliProjection SignedPauli.act pauliAct identityThree
  simp only [X_zero, add_zero, yWeight_zero, zDot_zero_left, pow_zero, one_mul, ZMod.val_zero,
    amp_conditionOutcome_plusPlusState]
  have h3 : v (Fin.last 3) = v 3 := rfl
  have i0 : Fin.init (Fin.init v) 0 = v 0 := rfl
  have i1 : Fin.init (Fin.init v) 1 = v 1 := rfl
  have i2 : Fin.init v (Fin.last 2) = v 2 := rfl
  rw [h3, i0, i1, i2]
  rcases zmod_two_eq_zero_or_one (v 3) with h | h <;> rw [h]
  · rw [if_pos rfl]
    split_ifs <;> norm_num
  · simp only [ZMod.val_one, pow_one]
    norm_num
    split_ifs <;> norm_num

/-- `X₀` on four bits has X-part `0` at every outcome bit. -/
theorem xFirstFour_X_natAdd (j : Fin 2) : xFirstFour.pauli.X (Fin.natAdd 2 j) = 0 := by
  fin_cases j <;> decide

/-- The run of a controlled `X₀` after the two conditioning letters, controlled by outcome bit
`j`. -/
theorem amp_controlled_twoOutcome (j : Fin 2) :
    amp (run (controlledPauliWord (Fin.natAdd 2 j) xFirstFour : GateWord 4 1)
        (twoOutcomeProtocol.interpret plusPlusState))
      = fun v => if v (Fin.natAdd 2 j) = 1
          then xFirstFour.act (amp (twoOutcomeProtocol.interpret plusPlusState)) v
          else amp (twoOutcomeProtocol.interpret plusPlusState) v :=
  amp_run_controlledPauliWord _ _ (xFirstFour_X_natAdd j) le_rfl xFirstFour_precision _
    twoOutcomeProtocol_m

/-- The word `(0, 0)` with the outcome string `(1, 0)`. -/
def wordOneZero : Fin 4 → ZMod 2 := Fin.append (fun _ : Fin 2 => 0) ![1, 0]

/-- The right term's branch at `(1, 0)`, at the data word `(0, 0)`, is `1`. -/
theorem rightProtocol_branch_value :
    rightProtocol.branch plusPlusState ![1, 0] (fun _ => 0) = 1 := by
  show amp (run _ (twoOutcomeProtocol.interpret plusPlusState)) wordOneZero = 1
  rw [amp_controlled_twoOutcome]
  have hc : wordOneZero (Fin.natAdd 2 (0 : Fin 2)) = 1 := rfl
  simp only [hc, if_true]
  unfold SignedPauli.act pauliAct
  rw [yWeight_xFirstFour, amp_twoOutcomeProtocol_eq]
  have hz : zDot xFirstFour.pauli (wordOneZero + xFirstFour.pauli.X) = 0 := by
    unfold zDot xFirstFour
    simp
  rw [hz]
  have e3 : (wordOneZero + xFirstFour.pauli.X) 3 = 0 := by decide
  have e0 : (wordOneZero + xFirstFour.pauli.X) 0 = 1 := by decide
  have e1 : (wordOneZero + xFirstFour.pauli.X) 1 = 0 := by decide
  have e2 : (wordOneZero + xFirstFour.pauli.X) 2 = 1 := by decide
  rw [e3, e0, e1, e2]
  unfold xFirstFour
  simp

/-- The wrong term's branch at `(1, 0)`, at the data word `(0, 0)`, is `0`. -/
theorem wrongProtocol_branch_value :
    wrongProtocol.branch plusPlusState ![1, 0] (fun _ => 0) = 0 := by
  show amp (run _ (twoOutcomeProtocol.interpret plusPlusState)) wordOneZero = 0
  rw [amp_controlled_twoOutcome]
  have hc : wordOneZero (Fin.natAdd 2 (1 : Fin 2)) = 0 := rfl
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  simp only [hc, h01, if_false]
  rw [amp_twoOutcomeProtocol_eq]
  have e3 : wordOneZero 3 = 0 := rfl
  have e0 : wordOneZero 0 = 0 := rfl
  have e1 : wordOneZero 1 = 0 := rfl
  have e2 : wordOneZero 2 = 1 := rfl
  rw [e3, e0, e1, e2]
  simp [h01]

/-! ## Rows -/

-- source: papers/measurement_calculus/
-- danos_kashefi_panangaden_quant-ph_0412135_measurement_calculus paragraph:hde3702006de9
/-- **Agreement.** T13.2's protocol as a term: its branch at every outcome string `o` is T13.2's
corrected state (`correctOutcome`) evaluated at the outcome `o 0`. -/
-- row: agreement
theorem bellProtocol_branch_eq_correctOutcome (o : Fin 1 → ZMod 2) :
    bellProtocol.branch plusPlusState o
      = fun w : Fin 2 → ZMod 2 => amp (correctOutcome plusPlusState zzParity xFirst)
          (Fin.snoc w (o 0) : Fin 3 → ZMod 2) := by
  funext w
  unfold branch
  rw [amp_bellProtocol_interpret, Fin.append_right_eq_snoc]

/-- **Agreement.** The branch of T13.2's protocol at every outcome string is the Bell state's
amplitude. -/
-- row: agreement
theorem bellProtocol_branch_eq_bellState (o : Fin 1 → ZMod 2) :
    bellProtocol.branch plusPlusState o = amp bellState := by
  rw [bellProtocol_branch_eq_correctOutcome]
  exact correctOutcome_plusPlusState_eq_bellState (o 0)

/-- **Discriminating.** The feed-forward reading outcome bit `3` (the `+I` outcome) in place of
outcome bit `2` (the `Z₀Z₁` outcome) changes the branch at the outcome string `(1, 0)`: at the
data word `(0, 0)` the right term has amplitude `1` and the wrong term `0`. -/
-- row: discriminating
theorem rightProtocol_branch_ne_wrongProtocol :
    rightProtocol.branch plusPlusState ![1, 0] ≠ wrongProtocol.branch plusPlusState ![1, 0] := by
  intro h
  have h00 := congrFun h (fun _ => 0)
  rw [rightProtocol_branch_value, wrongProtocol_branch_value] at h00
  exact one_ne_zero h00

/-- **Inhabitation.** The hypotheses of `amp_interpret` and `branch_weights_sum` hold together for
T13.2's protocol: the Bell state is a carrier state at the protocol's precision `1`. -/
-- row: inhabitation
theorem amp_interpret_hypotheses_bellProtocol : IsCarrier bellState ∧ bellState.m = 1 :=
  ⟨isCarrier_bellState, rfl⟩

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.brecOn.eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.brecOn.eq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.condition.inj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.condition.inj

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.condition.injEq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.condition.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.condition.sizeOf_spec' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.condition.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpretAmp_condition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpretAmp_condition

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpretAmp_nil' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpretAmp_nil

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpretAmp_word' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpretAmp_word

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpret_condition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpret_condition

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpret_nil' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpret_nil

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpret_word' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpret_word

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.nil.sizeOf_spec' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.nil.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.word.inj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.word.inj

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.word.injEq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.word.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.word.sizeOf_spec' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.word.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.interpret_m' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.interpret_m

/-- info: 'FTQCLib.Frame.Walkthrough.amp_interpret' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_interpret

/-- info: 'FTQCLib.Frame.Walkthrough.branch_weights_sum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.branch_weights_sum

/-- info: 'FTQCLib.Frame.Walkthrough.protocol_complete' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.protocol_complete

/-- info: 'FTQCLib.Frame.Walkthrough.branchWeight_condition_nil' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.branchWeight_condition_nil

/-- info: 'FTQCLib.Frame.Walkthrough.sum_sum_append' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_sum_append

/-- info: 'FTQCLib.Frame.Walkthrough.append_pair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.append_pair

/-! ## Mutants -/

-- mutant: branch_weights_sum_conclusion | FTQCLib/Carrier/Protocol.lean
--   | = ampNormSq S
--   | = ampNormSq S + 1

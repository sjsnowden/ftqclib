/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FeedForward
import FTQCLib.Carrier.HadamardAmplitude

/-!
# Check: feed-forward and reconvergence on `∣++⟩`

T13's witness (`docs/STEPS.md`, T13.2): rows on the frozen statement of `FeedForward.lean`, on one
small instance. The input is `∣++⟩` on the carrier (`plusPlusState`: `L = ⊤`, zero offset, flat
exponent, scale `1`, so its amplitude is `1` at every word). It is conditioned on `Z₀Z₁`
(`zzParity`) with the outcome as a new last free bit (`conditionOutcome`), and corrected by `X₀`
(`xFirst`) controlled by that bit (`correctOutcome`).

`reconverge` is proved, at T13.3. No row below uses it: every row is computed from
`amp_conditionOutcome` (`Conditioning.lean`) for the conditioned state and
`amp_run_controlledPauliWord` (`FeedForward.lean`) for the correction, on this instance, matching
what `reconverge` concludes in general (Row 2).

* **Row 1 (agreement).** With the correction, both evaluations of the outcome bit are the Bell
  state's amplitude (`bellState`, `HadamardAmplitude.lean`): `1` on the diagonal, `0` off it.
* **Row 2 (agreement).** Both evaluations are the outcome-`0` projection `Π_0` of the input, the
  conclusion `reconverge` states.
* **Row 3 (discriminating).** Without the correction the two branches differ at the free word
  `(0,0)`: outcome `0` has amplitude `1` there and outcome `1` has `0` (outcome `1` is the
  odd-parity state, not the Bell state).
* **Row 4 (inhabitation).** The hypotheses of `reconverge` hold together on this instance:
  co-isotropy of `⊤`, `X₀` stabilizes the input's amplitude, `X₀` anticommutes with `Z₀Z₁`, and
  `X₀` has no Y.

Frame form (D5): the guide `branch_reconverges` is stated through Hilbert definitions; these rows
compare amplitudes on the free bits, and no `FTQCLib.Hilbert` module is imported here directly.
The Bell state's amplitude here is the unnormalised `1` on the diagonal, the scale `bellState`
carries; the projection `Π_0` of `∣++⟩`'s all-ones amplitude has the same values.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## The instance -/

/-- `∣++⟩` on the carrier: `L = ⊤`, zero offset, flat exponent, scale `1`, `m = 1`. -/
noncomputable def plusPlusState : KernelSumState 2 := ⟨1, 0, 0, 1, ⊤, 0⟩

/-- `Z₀Z₁` with sign `+`. -/
def zzParity : SignedPauli 2 := ⟨0, ⟨0, fun _ => 1⟩⟩

/-- `X₀` with sign `+`. -/
def xFirst : SignedPauli 2 := ⟨0, ⟨Pi.single (0 : Fin 2) 1, 0⟩⟩

/-! ## Helpers -/

/-- `1 + 1 = 0` in `ZMod 2`. -/
theorem one_add_one_zmod_two_feedForward : (1 : ZMod 2) + 1 = 0 := by decide

/-- `0 ≠ 1` in `ZMod 2`. -/
theorem zero_ne_one_zmod_two_feedForward : (0 : ZMod 2) ≠ 1 := by decide

/-- The amplitude of a flat, height-zero, scale-one state at precision one is `1`. -/
theorem ampCore_flat_feedForward (w : Fin 2 → ZMod 2) :
    ampCore 1 0 (0 : DiagPhase (2 + 0) 1) 1 w = 1 := by
  rw [ampCore_zero, realPhase_zero_poly]
  simp

/-- `∣++⟩`'s amplitude is `1` at every word. -/
theorem amp_plusPlusState : amp plusPlusState = fun _ => 1 := by
  funext w
  have hw : ∃ p ∈ plusPlusState.L, w = plusPlusState.x₀ + p.X :=
    ⟨⟨w, 0⟩, Submodule.mem_top, by
      show w = (0 : Fin 2 → ZMod 2) + w
      rw [zero_add]⟩
  rw [amp_pos hw]
  exact ampCore_flat_feedForward w

/-- The Bell state's amplitude: `1` on the diagonal, `0` off it. -/
theorem amp_bellState_feedForward (w : Fin 2 → ZMod 2) :
    amp bellState w = if w 0 = w 1 then 1 else 0 := by
  by_cases h : w 0 = w 1
  · have hw : ∃ p ∈ bellState.L, w = bellState.x₀ + p.X :=
      ⟨⟨w, 0⟩, mem_bellL.2 ⟨h, rfl⟩, by
        show w = (0 : Fin 2 → ZMod 2) + w
        rw [zero_add]⟩
    rw [if_pos h, amp_pos hw]
    exact ampCore_flat_feedForward w
  · rw [if_neg h, amp_neg]
    rintro ⟨p, hp, hw⟩
    change w = (0 : Fin 2 → ZMod 2) + p.X at hw
    rw [zero_add] at hw
    rw [hw] at h
    exact h (mem_bellL.1 hp).1

/-- `⊤` is co-isotropic. -/
theorem plusPlusState_orth :
    LinearMap.BilinForm.orthogonal omegaBilin plusPlusState.L ≤ plusPlusState.L :=
  fun _ _ => Submodule.mem_top

/-- The projection of the all-ones amplitude onto `Z₀Z₁ = (−1)^b`: `1` where the parity is `b`. -/
theorem pauliProjection_zzParity (b : ZMod 2) (u : Fin 2 → ZMod 2) :
    pauliProjection zzParity b (fun _ => 1) u = if u 0 + u 1 = b then 1 else 0 := by
  unfold pauliProjection SignedPauli.act pauliAct yWeight zDot zzParity
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.zero_apply, add_zero, ZMod.val_zero,
    mul_zero, pow_zero, one_mul, mul_one, ZMod.val_one]
  rcases zmod_two_eq_zero_or_one (u 0) with h0 | h0 <;>
    rcases zmod_two_eq_zero_or_one (u 1) with h1 | h1 <;>
    rcases zmod_two_eq_zero_or_one b with hb | hb <;>
    simp only [h0, h1, hb, ZMod.val_zero, ZMod.val_one] <;>
    norm_num <;> decide

/-- The conditioned state: at `(w, b)` it is `1` where `w`'s parity is `b`. -/
theorem amp_conditionOutcome_plusPlusState (v : Fin 3 → ZMod 2) :
    amp (conditionOutcome plusPlusState zzParity) v
      = if Fin.init v 0 + Fin.init v 1 = v (Fin.last 2) then 1 else 0 := by
  rw [amp_conditionOutcome plusPlusState plusPlusState_orth zzParity, amp_plusPlusState]
  exact pauliProjection_zzParity _ _

/-- The conditioned state's precision is positive. -/
theorem one_le_conditionOutcome_plusPlusState_m :
    1 ≤ (conditionOutcome plusPlusState zzParity).m := by
  unfold conditionOutcome condition
  split_ifs
  · exact one_le_conditionPrecision (appendFreeBit plusPlusState).m zzParity.appendZ
  · exact one_le_conditionPrecision (appendFreeBit plusPlusState).m zzParity.appendZ

/-- `X₀` extended by the identity has no Y. -/
theorem yWeight_xFirst_appendId : yWeight xFirst.appendId.pauli = 0 := by
  unfold yWeight zDot SignedPauli.appendId pauliSnoc xFirst
  simp [Fin.snoc]

/-- The corrected state, by the referee of the controlled Pauli. -/
theorem amp_correctOutcome_plusPlusState :
    amp (correctOutcome plusPlusState zzParity xFirst)
      = fun v => if v (Fin.last 2) = 1
          then xFirst.appendId.act (amp (conditionOutcome plusPlusState zzParity)) v
          else amp (conditionOutcome plusPlusState zzParity) v := by
  unfold correctOutcome
  refine amp_run_controlledPauliWord _ _ ?_ one_le_conditionOutcome_plusPlusState_m ?_ _ rfl
  · show (Fin.snoc (Pi.single (0 : Fin 2) (1 : ZMod 2)) (0 : ZMod 2) : Fin 3 → ZMod 2)
        (Fin.last 2) = 0
    rw [Fin.snoc_last]
  · rw [yWeight_xFirst_appendId]
    intro h
    exact absurd h (by decide)

/-- The corrected state at `(w, b)`, on the four words and two outcomes. -/
theorem amp_correctOutcome_plusPlusState_snoc (w : Fin 2 → ZMod 2) (b : ZMod 2) :
    amp (correctOutcome plusPlusState zzParity xFirst) (Fin.snoc w b : Fin 3 → ZMod 2)
      = if w 0 = w 1 then 1 else 0 := by
  rw [amp_correctOutcome_plusPlusState]
  rcases zmod_two_eq_zero_or_one b with hb | hb <;> subst hb
  · simp only [Fin.snoc_last, show (0 : ZMod 2) ≠ 1 from by decide, if_false]
    rw [amp_conditionOutcome_plusPlusState]
    simp only [Fin.init_snoc, Fin.snoc_last]
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_one (w 1) with h1 | h1 <;>
      simp [h0, h1, one_add_one_zmod_two_feedForward]
  · simp only [Fin.snoc_last, if_true]
    unfold SignedPauli.act pauliAct
    simp only [amp_conditionOutcome_plusPlusState]
    unfold zDot SignedPauli.appendId pauliSnoc xFirst
    simp only [Fin.init, Pi.add_apply, Fin.snoc_last]
    simp only [Fin.snoc, yWeight, zDot]
    rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_one (w 1) with h1 | h1 <;>
      simp [h0, h1, one_add_one_zmod_two_feedForward]

/-! ## Rows -/

/-- **Agreement.** `Z₀Z₁` measured on `∣++⟩` with the outcome as a free bit, then `X₀` controlled by
that bit: both evaluations of the outcome bit are the Bell state's amplitude. -/
-- row: agreement
theorem correctOutcome_plusPlusState_eq_bellState (b : ZMod 2) :
    (fun w : Fin 2 → ZMod 2 =>
        amp (correctOutcome plusPlusState zzParity xFirst) (Fin.snoc w b : Fin 3 → ZMod 2))
      = amp bellState := by
  funext w
  rw [amp_correctOutcome_plusPlusState_snoc, amp_bellState_feedForward]

/-- **Agreement.** Both evaluations are the outcome-`0` projection of the input's amplitude, the
conclusion `reconverge` states, computed without it. -/
-- row: agreement
theorem correctOutcome_plusPlusState_eq_projection (b : ZMod 2) :
    (fun w : Fin 2 → ZMod 2 =>
        amp (correctOutcome plusPlusState zzParity xFirst) (Fin.snoc w b : Fin 3 → ZMod 2))
      = pauliProjection zzParity 0 (amp plusPlusState) := by
  funext w
  rw [amp_correctOutcome_plusPlusState_snoc, amp_plusPlusState, pauliProjection_zzParity]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;>
    rcases zmod_two_eq_zero_or_one (w 1) with h1 | h1 <;>
    simp [h0, h1, one_add_one_zmod_two_feedForward]

/-- **Discriminating.** Without the correction the two branches differ: at the free word `(0,0)`
outcome `0` has amplitude `1` and outcome `1` has amplitude `0`. -/
-- row: discriminating
theorem conditionOutcome_plusPlusState_branches_ne :
    (fun w : Fin 2 → ZMod 2 =>
        amp (conditionOutcome plusPlusState zzParity) (Fin.snoc w 0 : Fin 3 → ZMod 2))
      ≠ (fun w : Fin 2 → ZMod 2 =>
        amp (conditionOutcome plusPlusState zzParity) (Fin.snoc w 1 : Fin 3 → ZMod 2)) := by
  intro h
  have h00 := congrFun h (fun _ => 0)
  simp only [amp_conditionOutcome_plusPlusState, Fin.init_snoc, Fin.snoc_last, add_zero,
    if_true, zero_ne_one_zmod_two_feedForward, if_false] at h00
  exact one_ne_zero h00

/-- **Inhabitation.** The hypotheses of `reconverge` hold together on `∣++⟩`, `Z₀Z₁` and `X₀`:
co-isotropy, `X₀` stabilizes the all-ones amplitude, `X₀` anticommutes with `Z₀Z₁`, and `X₀` has
no Y. -/
-- row: inhabitation
theorem reconverge_hypotheses_plusPlusState :
    LinearMap.BilinForm.orthogonal omegaBilin plusPlusState.L ≤ plusPlusState.L
      ∧ xFirst.act (amp plusPlusState) = amp plusPlusState
      ∧ omega xFirst.pauli zzParity.pauli = 1
      ∧ (yWeight xFirst.pauli % 2 = 1 → 2 ≤ (conditionOutcome plusPlusState zzParity).m) := by
  have hy : yWeight xFirst.pauli = 0 := by
    unfold yWeight zDot xFirst
    simp
  refine ⟨plusPlusState_orth, ?_, ?_, ?_⟩
  · rw [amp_plusPlusState]
    funext w
    unfold SignedPauli.act pauliAct
    rw [hy]
    unfold zDot xFirst
    simp
  · unfold omega xFirst zzParity
    simp
  · rw [hy]
    intro h
    exact absurd h (by decide)

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_controlledShiftWord' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_controlledShiftWord

/-- info: 'FTQCLib.Frame.Walkthrough.letterAmp_controlledDiagonal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.letterAmp_controlledDiagonal

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_controlledPauliWord' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_controlledPauliWord

/-- info: 'FTQCLib.Frame.Walkthrough.amp_run_of_forall_ne_hadamard' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_run_of_forall_ne_hadamard

/-- info: 'FTQCLib.Frame.Walkthrough.controlledPauliWord_ne_hadamard' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.controlledPauliWord_ne_hadamard

/-- info: 'FTQCLib.Frame.Walkthrough.amp_run_controlledPauliWord' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_run_controlledPauliWord

/-- info: 'FTQCLib.Frame.Walkthrough.reconverge' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.reconverge

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.cnot.congr_simp' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.cnot.congr_simp

/-! ## Mutants -/

-- mutant: reconverge_conclusion | FTQCLib/Carrier/FeedForward.lean | pauliProjection P 0 (amp S) | pauliProjection P 1 (amp S)

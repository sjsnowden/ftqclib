/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.GateWord
import FTQCLib.Carrier.CarrierStateCheck
import FTQCLib.Carrier.CliffordWordFloor

/-!
# Check: witness for T05, gate words on carrier registers at any height

Two states carry the rows: `bellState` (`HadamardAmplitude.lean`, `n = 2`, `m = 1`, `h = 0`), and
`heightOneState` below, built by the free H rule off `KX` (`CarrierStateCheck.lean`) so its `h = 1`
is not asserted but computed, with `IsCarrier` for free from `isCarrier_applyHFiner`.

The agreement rows tie `run` to the letter-level operations `GateWord.lean` already states the
word type in terms of: a one-letter run is `applyLetter`, and a diagonal-then-CNOT run is the
composite `applyCnotSum` after `applyDiagSum`, read off `run_cons`/`run_nil` and the `applyLetter_*`
equations, no new machinery. A further agreement row is the one `GateWord.lean`'s docstring
promises: on a floor, the floor runner `runNormal` of `CliffordWordFloor.lean` and `run` agree in
amplitude on any two words whose letters have the same referees, letter by letter
(`amp_runNormal_eq_amp_run`, from `runNormal_floor` and `amp_run`), shown on `KX` with `H` then
`S`. The inhabitation rows instantiate `amp_run` and `isCarrier_run` — the frozen statement
itself — on these words and states, exhibiting their hypotheses (`IsCarrier`, the precision
match) held together on a concrete case.

The discriminating row swaps a diagonal letter and a CNOT in a two-letter word on `bellState`: the
diagonal gate reads bit `1`, which the CNOT (control `0`, target `1`) moves, so evaluating the
diagonal before or after the CNOT reads a different bit value at the word `(1,0)` — `amp` of the
two runs there are `-1` and `1`, by the referees `amp_applyDiagSum`/`amp_applyCnotSum` proved in
`CarrierClifford.lean`, not by `amp_run`, so the row does not rest on the theorem it checks. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## The height-one state: the free H rule off `KX` -/

/-- **The height-one state.** The free rule `applyHFiner` at `KX`'s X-supported bit: one
summation variable is adjoined, so `h = 1` (`applyHFiner`'s field, not asserted here). -/
noncomputable def heightOneState : KernelSumState 1 :=
  applyHFiner (0 : Fin 1) (ofKernelState KX)

/-- **Carrier.** `isCarrier_applyHFiner`, proved in `CarrierStateHadamard.lean`, closes this
independently of `GateWord.lean`. -/
theorem isCarrier_heightOneState : IsCarrier heightOneState :=
  isCarrier_applyHFiner (0 : Fin 1) isCarrier_KX pi_single_zero_mem_shadow_lagX

/-- The height-one state's precision is `1`, `KX`'s own. -/
theorem heightOneState_m : heightOneState.m = 1 := rfl

/-! ## `bellState`: carrier and its support point `(1,1)` -/

/-- **Carrier.** `bellState.m = 1`, `bellL` is a stabilizer (`bellL_isStabilizer`) and
co-isotropic (`bellL_coisotropic`); the amplitude at `(1,1)` is nonzero
(`amp_bellState_one_one`). -/
theorem isCarrier_bellState : IsCarrier bellState :=
  ⟨le_refl 1, bellL_isStabilizer, bellL_coisotropic, by
    intro hzero
    have h11 : amp bellState (![1, 1] : Fin 2 → ZMod 2) = 0 := congrFun hzero _
    rw [amp_bellState_one_one] at h11
    exact one_ne_zero h11⟩

/-! ## Agreement: `run` against the letter-level operations -/

/-- **Agreement.** A one-letter H word's run is `applyH`, read off `run_cons`, `run_nil` and
`applyLetter_hadamard` — no new machinery beyond `GateWord.lean`'s own equations. -/
-- row: agreement
theorem run_hadamard_heightOneState :
    run ([GateLetter.hadamard (0 : Fin 1)] : GateWord 1 1) heightOneState
      = applyH 0 heightOneState := by
  rw [run_cons, run_nil, applyLetter_hadamard]

/-- **Agreement.** The referee of that run is the Walsh transform (`amp_applyH`, already proved
on a carrier state). -/
-- row: agreement
theorem amp_run_hadamard_heightOneState :
    amp (run ([GateLetter.hadamard (0 : Fin 1)] : GateWord 1 1) heightOneState)
      = walshTransform 0 (amp heightOneState) := by
  rw [run_hadamard_heightOneState]
  exact amp_applyH isCarrier_heightOneState 0

/-- **Agreement.** A two-letter word `[diagonal D, cnot i j]`'s run is the composite
`applyCnotSum` after `applyDiagSum`, read off `run_cons`, `run_nil` and the `applyLetter_*`
equations (`S` given explicitly to `applyLetter_diagonal` since its letter's precision index is
`S.m`, not a free unification variable). -/
-- row: agreement
theorem run_diag_cnot_bellState (D : DiagPhase 2 1) (hij : (0 : Fin 2) ≠ 1) :
    run ([GateLetter.diagonal D, GateLetter.cnot 0 1 hij] : GateWord 2 1) bellState
      = applyCnotSum 0 1 (applyDiagSum bellState D) := by
  have h1 : applyLetter (GateLetter.diagonal D) bellState = applyDiagSum bellState D :=
    applyLetter_diagonal (S := bellState) D
  have h2 : applyLetter (GateLetter.cnot (0 : Fin 2) 1 hij) (applyDiagSum bellState D)
      = applyCnotSum 0 1 (applyDiagSum bellState D) :=
    applyLetter_cnot (m := 1) hij (applyDiagSum bellState D)
  rw [run_cons, run_cons, run_nil, h1, h2]

/-! ## Agreement: `run` against the floor runner `runNormal` -/

/-- The floor alphabet's H has the referee of the gate word's H, by definition. -/
theorem gateAmp_eq_letterAmp_hadamard {n m : ℕ} (k : Fin n) :
    gateAmp (NormalGate.H k : NormalGate n m)
      = letterAmp (GateLetter.hadamard k : GateLetter n m) := rfl

/-- The floor alphabet's diagonal letter has the referee of the gate word's, by definition. -/
theorem gateAmp_eq_letterAmp_diagonal {n m : ℕ} (D : DiagPhase n m) :
    gateAmp (NormalGate.Diag D) = letterAmp (GateLetter.diagonal D) := rfl

/-- The floor alphabet's CNOT has the referee of the gate word's, by definition. -/
theorem gateAmp_eq_letterAmp_cnot {n m : ℕ} {i j : Fin n} (hij : i ≠ j) :
    gateAmp (NormalGate.Cnot i j : NormalGate n m)
      = letterAmp (GateLetter.cnot i j hij : GateLetter n m) := rfl

/-- Two words whose letters have the same referees, letter by letter, have the same referee. -/
theorem runNormalAmp_eq_runAmp {n m : ℕ} {gs : List (NormalGate n m)} {gs' : GateWord n m}
    (hlet : List.Forall₂ (fun g g' => gateAmp g = letterAmp g') gs gs')
    (f : (Fin n → ZMod 2) → ℂ) : runNormalAmp gs f = runAmp gs' f := by
  induction hlet generalizing f with
  | nil => rfl
  | cons hg _ ih => rw [runNormalAmp_cons, runAmp_cons, hg, ih]

/-- **Agreement: the floor runner and `run`, letter by letter in amplitude, on a floor.** For a
well-formed floor word `gs` and a gate word `gs'` whose letters have the same referees one by one,
the two runs on a height-zero floor at the words' precision have the same amplitude:
`runNormal_floor` and `amp_run` reduce both to their referees, which agree letter by letter. -/
-- row: agreement
theorem amp_runNormal_eq_amp_run {n m : ℕ} (gs : List (NormalGate n m)) (hwf : WordWF gs)
    (gs' : GateWord n m) (hlet : List.Forall₂ (fun g g' => gateAmp g = letterAmp g') gs gs')
    {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) (hm : S.m = m) :
    amp (runNormal gs S) = amp (run gs' S) := by
  rw [(runNormal_floor gs hwf hF h0 hm).2.2.2, amp_run gs' hF.1 hm, runNormalAmp_eq_runAmp hlet]

/-- **Agreement, on an instance.** On the floor `KX`, the floor word `H, S` and the gate word
`H, S` at precision one have the same amplitude: the floor runner eliminates the bound bit its H
would adjoin, `run` keeps it, and the amplitudes agree. -/
-- row: agreement
theorem amp_runNormal_eq_amp_run_KX :
    amp (runNormal [NormalGate.H 0, sLetter 1 0] (ofKernelState KX))
      = amp (run ([GateLetter.hadamard 0, GateLetter.diagonal (sGate 1 0)] : GateWord 1 1)
          (ofKernelState KX)) := by
  refine amp_runNormal_eq_amp_run _ ?_ _ (.cons rfl (.cons rfl .nil)) isFloor_KX rfl rfl
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  exacts [hLetter_wf 0, sLetter_wf 1 0]

/-! ## Inhabitation: the frozen statement's hypotheses, held together -/

/-- **Inhabitation.** `amp_run`'s hypotheses — a carrier state at the word's precision — hold
together on `heightOneState` and a one-letter H word: exhibiting the instance exhibits both at
once. -/
-- row: inhabitation
example := amp_run ([GateLetter.hadamard (0 : Fin 1)] : GateWord 1 1) isCarrier_heightOneState
  heightOneState_m

/-- **Inhabitation.** `isCarrier_run`'s hypotheses, on the same word and state. -/
-- row: inhabitation
example := isCarrier_run ([GateLetter.hadamard (0 : Fin 1)] : GateWord 1 1)
  isCarrier_heightOneState heightOneState_m

/-- **Inhabitation.** The same two hypotheses on `bellState` and a two-letter diagonal-then-CNOT
word. -/
-- row: inhabitation
example := amp_run ([GateLetter.diagonal (0 : DiagPhase 2 1), GateLetter.cnot 0 1
  (by decide : (0 : Fin 2) ≠ 1)] : GateWord 2 1) isCarrier_bellState (rfl : bellState.m = 1)

/-! ## Discriminating: the order of two letters -/

/-- The diagonal exponent reading bit `1`: `X₁`. -/
noncomputable def diagBit1 : DiagPhase 2 1 := MvPolynomial.X (1 : Fin 2)

/-- `diagBit1`'s value is bit `1`'s value, cast into `ZMod 2`. -/
theorem eval_diagBit1 (w : Fin 2 → ZMod 2) :
    DiagPhase.eval diagBit1 w = ((w 1).val : ZMod 2) := by
  unfold diagBit1 DiagPhase.eval DiagPhase.liftBinary
  simp

/-- CNOT (control `0`, target `1`) sends `(1,0)` to `(1,1)`: the target reads the control. -/
theorem cnotBitMap_ten :
    cnotBitMap (0 : Fin 2) 1 (![1, 0] : Fin 2 → ZMod 2) = (![1, 1] : Fin 2 → ZMod 2) := by
  unfold cnotBitMap
  funext i
  fin_cases i <;> simp

/-- `diagBit1` at `(1,0)` is `0`: bit `1` reads `0` there. -/
theorem eval_diagBit1_ten : DiagPhase.eval diagBit1 (![1, 0] : Fin 2 → ZMod 2) = 0 := by
  rw [eval_diagBit1]; decide

/-- `diagBit1` at `(1,1)` is `1`: bit `1` reads `1` there. -/
theorem eval_diagBit1_eleven : DiagPhase.eval diagBit1 (![1, 1] : Fin 2 → ZMod 2) = 1 := by
  rw [eval_diagBit1]; decide

/-- The dyadic character at `1`, precision one, is `-1`: the top bit `2^{1-1} = 1` times `1` reads
the odd parity `(-1)^1`. -/
theorem charOf_one_val_one : charOf 1 (1 : ZMod 2) = -1 := by
  have h := charOf_two_pow_mul (m := 1) (le_refl 1) 1
  norm_num at h
  exact h

/-- **Diagonal then CNOT**, read at `(1,0)`: the diagonal reads bit `1` *after* the CNOT has moved
it — `diagBit1` at the CNOT-image `(1,1)` is `1`, so the character is `-1`; `bellState`'s
amplitude at `(1,1)` is `1`. -/
theorem amp_run_diag_then_cnot_ten :
    amp (run ([GateLetter.diagonal diagBit1, GateLetter.cnot 0 1 Fin.zero_ne_one] :
      GateWord 2 1) bellState) (![1, 0] : Fin 2 → ZMod 2) = -1 := by
  rw [run_diag_cnot_bellState diagBit1 Fin.zero_ne_one]
  have step1 : amp (applyCnotSum (0 : Fin 2) 1 (applyDiagSum bellState diagBit1))
      (![1, 0] : Fin 2 → ZMod 2)
      = amp (applyDiagSum bellState diagBit1) (cnotBitMap 0 1 (![1, 0] : Fin 2 → ZMod 2)) :=
    congrFun (amp_applyCnotSum Fin.zero_ne_one (applyDiagSum bellState diagBit1)) _
  rw [step1, cnotBitMap_ten]
  have step2 : amp (applyDiagSum bellState diagBit1) (![1, 1] : Fin 2 → ZMod 2)
      = charOf 1 (DiagPhase.eval diagBit1 (![1, 1] : Fin 2 → ZMod 2))
        * amp bellState (![1, 1] : Fin 2 → ZMod 2) :=
    congrFun (amp_applyDiagSum bellState diagBit1) _
  rw [step2, eval_diagBit1_eleven, amp_bellState_one_one, mul_one]
  exact charOf_one_val_one

/-- **CNOT then diagonal**, read at `(1,0)`: the diagonal reads bit `1` *before* the CNOT — at the
original point `(1,0)`, `diagBit1` is `0`, so the character is `1`; the CNOT still moves `(1,0)` to
`bellState`'s support point `(1,1)`, amplitude `1`. Same word, letters swapped, same read-out
point: the value differs from the row below. -/
theorem amp_run_cnot_then_diag_ten :
    amp (run ([GateLetter.cnot 0 1 Fin.zero_ne_one, GateLetter.diagonal diagBit1] :
      GateWord 2 1) bellState) (![1, 0] : Fin 2 → ZMod 2) = 1 := by
  have h1 : applyLetter (GateLetter.cnot (0 : Fin 2) 1 Fin.zero_ne_one) bellState
      = applyCnotSum 0 1 bellState := applyLetter_cnot (m := 1) Fin.zero_ne_one bellState
  have h2 : applyLetter (GateLetter.diagonal diagBit1) (applyCnotSum 0 1 bellState)
      = applyDiagSum (applyCnotSum 0 1 bellState) diagBit1 :=
    applyLetter_diagonal (S := applyCnotSum 0 1 bellState) diagBit1
  rw [run_cons, run_cons, run_nil, h1, h2]
  have step1 : amp (applyDiagSum (applyCnotSum 0 1 bellState) diagBit1) (![1, 0] : Fin 2 → ZMod 2)
      = charOf 1 (DiagPhase.eval diagBit1 (![1, 0] : Fin 2 → ZMod 2))
        * amp (applyCnotSum 0 1 bellState) (![1, 0] : Fin 2 → ZMod 2) :=
    congrFun (amp_applyDiagSum (applyCnotSum 0 1 bellState) diagBit1) _
  rw [step1, eval_diagBit1_ten]
  have step2 : amp (applyCnotSum (0 : Fin 2) 1 bellState) (![1, 0] : Fin 2 → ZMod 2)
      = amp bellState (cnotBitMap 0 1 (![1, 0] : Fin 2 → ZMod 2)) :=
    congrFun (amp_applyCnotSum Fin.zero_ne_one bellState) _
  rw [step2, cnotBitMap_ten, amp_bellState_one_one, mul_one]
  exact charOf_zero 1

/-- **Discriminating.** Swapping the diagonal letter and the CNOT in the same two-letter word,
read at the same point `(1,0)`, tells the two orders apart: `-1 ≠ 1`. -/
-- row: discriminating
theorem run_diag_cnot_ne_cnot_diag :
    amp (run ([GateLetter.diagonal diagBit1, GateLetter.cnot 0 1 Fin.zero_ne_one] :
      GateWord 2 1) bellState) (![1, 0] : Fin 2 → ZMod 2)
      ≠ amp (run ([GateLetter.cnot 0 1 Fin.zero_ne_one, GateLetter.diagonal diagBit1] :
      GateWord 2 1) bellState) (![1, 0] : Fin 2 → ZMod 2) := by
  rw [amp_run_diag_then_cnot_ten, amp_run_cnot_then_diag_ten]
  norm_num

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.hadamard.inj' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.hadamard.inj

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.hadamard.injEq' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.hadamard.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.hadamard.sizeOf_spec' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.hadamard.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.diagonal.inj' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.diagonal.inj

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.diagonal.injEq' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.diagonal.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.diagonal.sizeOf_spec' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.diagonal.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.cnot.inj' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.cnot.inj

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.cnot.injEq' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.cnot.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.cnot.sizeOf_spec' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.cnot.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_nil' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_nil

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_cons' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_cons

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_append' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_append

/-- info: 'FTQCLib.Frame.Walkthrough.applyH_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyH_m

/-- info: 'FTQCLib.Frame.Walkthrough.applyH_of_representer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyH_of_representer

/-- info: 'FTQCLib.Frame.Walkthrough.applyH_of_no_representer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyH_of_no_representer

/-- info: 'FTQCLib.Frame.Walkthrough.applyH_cover' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyH_cover

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyH' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyH

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyH' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyH

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyDiagSum' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyDiagSum

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyLetter' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyLetter

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyLetter' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyLetter

/-- info: 'FTQCLib.Frame.Walkthrough.applyLetter_hadamard' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyLetter_hadamard

/-- info: 'FTQCLib.Frame.Walkthrough.applyLetter_diagonal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyLetter_diagonal

/-- info: 'FTQCLib.Frame.Walkthrough.applyLetter_cnot' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyLetter_cnot

/-- info: 'FTQCLib.Frame.Walkthrough.applyLetter_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyLetter_m

/-- info: 'FTQCLib.Frame.Walkthrough.run_nil' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_nil

/-- info: 'FTQCLib.Frame.Walkthrough.run_cons' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_cons

/-- info: 'FTQCLib.Frame.Walkthrough.run_append' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_append

/-- info: 'FTQCLib.Frame.Walkthrough.run_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms run_m

/-- info: 'FTQCLib.Frame.Walkthrough.amp_run' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_run

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_run' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_run

/-- info: 'FTQCLib.Frame.Walkthrough.sum_normSq_letterAmp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_normSq_letterAmp

/-- info: 'FTQCLib.Frame.Walkthrough.sum_normSq_runAmp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_normSq_runAmp

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_czGate_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.charOf_czGate_eval

/-- info: 'FTQCLib.Frame.Walkthrough.innerSum_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.innerSum_self

/-- info: 'FTQCLib.Frame.Walkthrough.innerSum_add_smul_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.innerSum_add_smul_self

/-- info: 'FTQCLib.Frame.Walkthrough.letterAmp_add_smul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.letterAmp_add_smul

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_add_smul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_add_smul

/-- info: 'FTQCLib.Frame.Walkthrough.innerSum_runAmp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.innerSum_runAmp

/-- info: 'FTQCLib.Frame.Walkthrough.padZero_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.padZero_self

/-- info: 'FTQCLib.Frame.Walkthrough.padZero_padZero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.padZero_padZero

/-- info: 'FTQCLib.Frame.Walkthrough.padZero_update' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.padZero_update

/-- info: 'FTQCLib.Frame.Walkthrough.letterAmp_invLetter' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.letterAmp_invLetter

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_invWord' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_invWord

/-- info: 'FTQCLib.Frame.Walkthrough.letterAmp_widenLetter' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.letterAmp_widenLetter

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_widenWord' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_widenWord

/-- info: 'FTQCLib.Frame.Walkthrough.Realizes.append' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Realizes.append

/-- info: 'FTQCLib.Frame.Walkthrough.realizes_swap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.realizes_swap

/-- info: 'FTQCLib.Frame.Walkthrough.exists_realizes_perm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_realizes_perm

/-- info: 'FTQCLib.Frame.Walkthrough.realizes_flip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.realizes_flip

/-- info: 'FTQCLib.Frame.Walkthrough.exists_realizes_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_realizes_add

/-- info: 'FTQCLib.Frame.Walkthrough.exists_realizes_xor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_realizes_xor

/-- info: 'FTQCLib.Frame.Walkthrough.exists_realizes_insertLast' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_realizes_insertLast

end FTQCLib.Frame.Walkthrough

-- mutant: applyLetter_cnot_identity | FTQCLib/Carrier/GateWord.lean | => applyCnotSum i j S | => S

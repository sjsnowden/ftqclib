/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CliffordFloorGeneration
import FTQCLib.Examples.CarrierStateCheck

/-!
# Check: every symplectic map is a Clifford word on the floor

Axiom rows for every declaration of `FTQCLib.Examples.CliffordFloorGeneration`, and the witnesses:

* **The four identifications, independently at small `n`** — each proved again by the kernel
  (`decide`) rather than by the general argument, so a slip in one of the general proofs would show
  up here.
* **The word order** — `wordLin [H 0, H 1]` applies `H 0` first, matching the group's `x * y`
  convention (which applies `y` first) through `wordLin_append`.
* **The precision boundary** — the phase gate's map is a well-formed word at `m = 2`
  (`exists_word_phaseAt_two`) and is **not** at `m = 1` (`not_exists_word_phaseAt_one`), separated
  by the invariant `qForm`. This is what makes the `2 ≤ m` of `exists_wordWF_wordLin_eq`
  load-bearing rather than decorative.
* **The main theorem on a concrete floor** — the uniform record on one qubit at precision two, with
  every symplectic map realised on it, and the Hadamard instance.

`decide` cannot run through `DiagPhase.eval`; the amplitude rows are `rw` rows.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer FTQCLib.Gates Module

variable {n : ℕ}

/-! ## The identifications, independently at small `n` (controls for the general proofs) -/

/-- H at one qubit, by the kernel. -/
theorem swap_eq_hadamard_one :
    ∀ p : Pauli 1, pauliSwapOn ({0} : Finset (Fin 1)) p = hadamardAt 0 p := by
  decide

/-- S at one qubit, by the kernel. -/
theorem shear_eq_phase_one :
    ∀ p : Pauli 1, zShearBy (shearLin 0 (Pi.single 0 1)) p = phaseAt 0 p := by
  decide

/-- CZ at two qubits, by the kernel. -/
theorem shear_eq_cz_two :
    ∀ p : Pauli 2, zShearBy (shearLin 0 (Pi.single 1 1)) p = czAt 0 1 (by decide) p := by
  decide

/-- CNOT at two qubits, by the kernel. -/
theorem cnot_eq_cnotAt_two : ∀ p : Pauli 2, cnotPauli 0 1 p = cnotAt 0 1 (by decide) p := by
  decide

/-! ## The word order is the one the group forces -/

/-- `x * y` applies `y` first, so the word for it is `gs_y ++ gs_x` — the composite of the two
letters, checked on the kernel at two qubits. -/
theorem word_order_two :
    ∀ p : Pauli 2,
      wordLin ([NormalGate.H 0, NormalGate.H 1] : List (NormalGate 2 2)) p
        = hadamardAt 1 (hadamardAt 0 p) := by
  decide

/-! ## The precision boundary: the same map, realised at `m = 2` and not at `m = 1` -/

/-- At precision two the phase gate **is** a well-formed word's map. -/
theorem exists_word_phaseAt_two (k : Fin n) :
    ∃ gs : List (NormalGate n 2), WordWF gs ∧
      wordLin gs = (phaseAt k : Pauli n →ₗ[ZMod 2] Pauli n) :=
  ⟨[sLetter 2 k], fun g hg => by
    rw [List.mem_singleton] at hg; subst hg; exact sLetter_wf 2 k,
    by rw [wordLin_singleton, letterLin_sLetter le_rfl]⟩

/-- **Discriminating.** At precision one it is not — the row that makes `2 ≤ m` load-bearing in
`exists_wordWF_wordLin_eq` rather than decorative. -/
theorem not_exists_word_phaseAt_one (k : Fin n) :
    ¬ ∃ gs : List (NormalGate n 1), WordWF gs ∧
        wordLin gs = (phaseAt k : Pauli n →ₗ[ZMod 2] Pauli n) :=
  not_exists_wordWF_wordLin_eq_phaseAt k

/-- The invariant that separates them: every word preserves `q` at precision one, and the phase
gate moves it. -/
theorem qForm_separates (k : Fin n) :
    qForm (phaseAt k (paulix k)) = qForm (paulix k) + 1 := by
  rw [qForm_phaseAt, paulix_X, Pi.single_eq_same]

/-! ## The main theorem on a concrete floor -/

/-- The uniform record on one qubit at precision two, stabilizer `⟨X₀⟩`. -/
noncomputable def KG : KernelState 1 := ⟨2, 0, 1, lagX, 0⟩

theorem amp_KG (w : Fin 1 → ZMod 2) : amp (ofKernelState KG) w = 1 := by
  rw [amp_ofKernelState_pos KG (lagX_support w)]
  change (1 : ℂ) * charOf 2 (DiagPhase.eval (0 : DiagPhase 1 2) w) = 1
  rw [show DiagPhase.eval (0 : DiagPhase 1 2) w = 0 by unfold DiagPhase.eval; simp, charOf_zero,
    one_mul]

theorem isCarrier_KG : IsCarrier (ofKernelState KG) := by
  refine ⟨by decide, isStabilizer_span_singleton (paulix 0), ?_, ?_⟩
  · exact orthogonal_le_of_lagrangian (isStabilizer_span_singleton (paulix 0))
      (finrank_span_singleton (by decide))
  · intro h
    have h0 := congrFun h 0
    rw [amp_KG] at h0
    exact one_ne_zero h0

theorem isFloor_KG : IsFloor (ofKernelState KG) := by
  refine ⟨isCarrier_KG, ?_⟩
  intro g hg
  change g ∈ Submodule.span (ZMod 2) {paulix 0} at hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  refine ⟨0, ?_⟩
  funext w
  have hy : yWeight (a • paulix (0 : Fin 1)) = 0 := by simp [yWeight, zDot, paulix]
  have hz : ∀ v : Fin 1 → ZMod 2, zDot (a • paulix (0 : Fin 1)) v = 0 := by
    intro v; simp [zDot, paulix]
  simp only [pauliAct, hy, hz, pow_zero, one_mul, amp_KG, ZMod.val_zero]

/-- **The main theorem, end to end.** Every symplectic map on one qubit is realised by a
well-formed word on this floor, at precision two: the run is a height-zero floor at precision
two whose Lagrangian is the map's image of `⟨X₀⟩`. -/
theorem exists_runNormal_KG {T : Pauli 1 ≃ₗ[ZMod 2] Pauli 1} (hT : IsClifford T) :
    ∃ gs : List (NormalGate 1 2), WordWF gs ∧
      IsFloor (runNormal gs (ofKernelState KG)) ∧ (runNormal gs (ofKernelState KG)).h = 0 ∧
      (runNormal gs (ofKernelState KG)).m = 2 ∧
      (runNormal gs (ofKernelState KG)).L
        = Submodule.map (T : Pauli 1 →ₗ[ZMod 2] Pauli 1) (ofKernelState KG).L ∧
      amp (runNormal gs (ofKernelState KG)) = runNormalAmp gs (amp (ofKernelState KG)) :=
  exists_runNormal_of_isClifford le_rfl hT isFloor_KG rfl rfl

/-- Instantiated at the Hadamard gate, whose `IsClifford` is the built one. -/
theorem exists_runNormal_KG_hadamard :
    ∃ gs : List (NormalGate 1 2), WordWF gs ∧
      IsFloor (runNormal gs (ofKernelState KG)) ∧ (runNormal gs (ofKernelState KG)).h = 0 ∧
      (runNormal gs (ofKernelState KG)).m = 2 ∧
      (runNormal gs (ofKernelState KG)).L
        = Submodule.map (hadamardAt (0 : Fin 1) : Pauli 1 →ₗ[ZMod 2] Pauli 1)
            (ofKernelState KG).L ∧
      amp (runNormal gs (ofKernelState KG)) = runNormalAmp gs (amp (ofKernelState KG)) :=
  exists_runNormal_KG (hadamardAt_isClifford 0)

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_singleton_eq_hadamardAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_singleton_eq_hadamardAt

/-- info: 'FTQCLib.Frame.Walkthrough.zShearBy_shearLin_self_eq_phaseAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zShearBy_shearLin_self_eq_phaseAt

/-- info: 'FTQCLib.Frame.Walkthrough.zShearBy_shearLin_ne_eq_czAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zShearBy_shearLin_ne_eq_czAt

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_eq_cnotAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_eq_cnotAt

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_H' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_H

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_sLetter' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_sLetter

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_czLetter' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_czLetter

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_Cnot' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_Cnot

/-- info: 'FTQCLib.Frame.Walkthrough.wordLin_singleton' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordLin_singleton

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_involutive' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_involutive

/-- info: 'FTQCLib.Frame.Walkthrough.wordWF_reverse' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordWF_reverse

/-- info: 'FTQCLib.Frame.Walkthrough.wordLin_reverse_comp' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordLin_reverse_comp

/-- info: 'FTQCLib.Frame.Walkthrough.coe_mul_linearMap' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coe_mul_linearMap

/-- info: 'FTQCLib.Frame.Walkthrough.exists_wordWF_of_mem_bigGateSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_wordWF_of_mem_bigGateSet

/-- info: 'FTQCLib.Frame.Walkthrough.exists_wordWF_wordLin_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_wordWF_wordLin_eq

/-- info: 'FTQCLib.Frame.Walkthrough.exists_runNormal_of_isClifford' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_runNormal_of_isClifford

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_polarMatrix_self_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_polarMatrix_self_zero

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_zShearBy_of_self_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_zShearBy_of_self_zero

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_pauliSwapOn_singleton' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_pauliSwapOn_singleton

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_cnotPauli' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_letterLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_letterLin

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_wordLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_wordLin

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_phaseAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_phaseAt

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_wordWF_wordLin_eq_phaseAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_wordWF_wordLin_eq_phaseAt

/-- info: 'FTQCLib.Frame.Walkthrough.swap_eq_hadamard_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms swap_eq_hadamard_one

/-- info: 'FTQCLib.Frame.Walkthrough.shear_eq_phase_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shear_eq_phase_one

/-- info: 'FTQCLib.Frame.Walkthrough.shear_eq_cz_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shear_eq_cz_two

/-- info: 'FTQCLib.Frame.Walkthrough.cnot_eq_cnotAt_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnot_eq_cnotAt_two

/-- info: 'FTQCLib.Frame.Walkthrough.word_order_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms word_order_two

/-- info: 'FTQCLib.Frame.Walkthrough.exists_word_phaseAt_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_word_phaseAt_two

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_word_phaseAt_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_word_phaseAt_one

/-- info: 'FTQCLib.Frame.Walkthrough.qForm_separates' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qForm_separates

/-- info: 'FTQCLib.Frame.Walkthrough.KG' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KG

/-- info: 'FTQCLib.Frame.Walkthrough.amp_KG' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_KG

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_KG' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_KG

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_KG' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_KG

/-- info: 'FTQCLib.Frame.Walkthrough.exists_runNormal_KG' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_runNormal_KG

/-- info: 'FTQCLib.Frame.Walkthrough.exists_runNormal_KG_hadamard' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_runNormal_KG_hadamard

end FTQCLib.Frame.Walkthrough

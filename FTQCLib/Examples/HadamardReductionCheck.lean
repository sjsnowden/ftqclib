/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardReduction

/-!
# Acceptance rows for the reduction

The control is aimed at `hqfree`, the one hypothesis `amp_ofKernelState_applyHPinned` carries
beyond `amp_hRaise_zero_ofKernelState`. On the one-qubit state whose exponent *reads* the pinned
bit (`q = X₀` at `m = 2`, support the single word `1`, i.e. the phase-`i` copy of that word),
`applyHPinned` gives amplitude `1/√2` at the word `0` where the referee gives `i/√2`: the frozen
value `i` is lost. So `hqfree` is load-bearing — and on the same state `hRaise` at `u = 0` *is*
the Walsh transform, by the theorem, with no exponent hypothesis. That pair of rows is the content
of the defect item `d1` stated as facts. The premise rows pin that pinning holds there and that
`hqfree` genuinely fails.

The agreement rows take the classical register `1` on one qubit, where both constructors are
certified: the reduction theorem says their amplitudes are equal; two explicit evaluations put the
common value at the word `1` at `−1/√2`; and the referee's value there is the same number.

The kernel rows decide the `u = 0` branch data: `raiseConst` collapses to the pinned bit, and the
zero representer pairs to nothing. No amplitude row is a kernel row (`Complex.exp`). -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## Shared facts -/

/-- `realPhase` of the zero exponent vanishes. -/
theorem realPhase_zero_poly'' {N m : ℕ} (v : Fin N → ZMod 2) :
    DiagPhase.realPhase (0 : DiagPhase N m) v = 0 := by
  unfold DiagPhase.realPhase DiagPhase.eval
  rw [map_zero, ZMod.val_zero]
  simp

/-- `1/√2 ≠ 0`. -/
theorem one_div_sqrt_two_ne_zero'' : (1 / (Real.sqrt 2 : ℂ)) ≠ 0 :=
  one_div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))

/-- `e^{iπ/2} = i`. -/
theorem exp_I_pi_div_two : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-! ## Control — `hqfree` is load-bearing -/

/-- The one-qubit state whose exponent reads its pinned bit: support `{1}`, phase `i^{w₀}`. -/
noncomputable def readState : KernelState 1 where
  m := 2
  q := MvPolynomial.X 0
  c := 1
  L := Lz
  x₀ := ![1]

/-- The control's premise: pinning holds (`L = Lz`), so the refuted hypothesis is `hqfree`. -/
example : ∀ p ∈ readState.L, p.X 0 = 0 := by
  intro p hp
  have h : p.X = 0 := mem_Lz.mp hp
  rw [h]
  rfl

/-- The control's other premise: `hqfree` fails — the exponent `X₀` sees the flip of bit `0`. -/
example :
    ¬ ∀ (w : Fin 1 → ZMod 2) (b : ZMod 2),
        DiagPhase.eval readState.q (Function.update w 0 b) = DiagPhase.eval readState.q w := by
  intro h
  have h1 := h ![0] 1
  change DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 2) (Function.update ![0] 0 1)
    = DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 2) ![0] at h1
  rw [DiagPhase.eval_X, DiagPhase.eval_X] at h1
  revert h1
  decide

/-- The input amplitude at `0`: off the support. -/
theorem amp_readState_zero : amp (ofKernelState readState) ![0] = 0 := by
  refine amp_neg ?_
  rintro ⟨p, hp, h⟩
  have hX : p.X = 0 := mem_Lz.mp hp
  change (![0] : Fin 1 → ZMod 2) = ![1] + p.X at h
  rw [hX, add_zero] at h
  have h0 := congrFun h 0
  revert h0
  decide

/-- The input amplitude at `1`: the phase `i`. -/
theorem amp_readState_one : amp (ofKernelState readState) ![1] = Complex.I := by
  have hsup : ∃ p ∈ (ofKernelState readState).L,
      (![1] : Fin 1 → ZMod 2) = (ofKernelState readState).x₀ + p.X :=
    ⟨⟨0, 0⟩, mem_Lz.mpr rfl, by decide⟩
  rw [amp_pos hsup]
  change ampCore 2 0 (MvPolynomial.X 0 : DiagPhase 1 2) 1 ![1] = Complex.I
  rw [ampCore_zero, one_mul]
  have hph : @DiagPhase.realPhase (1 + 0) 2 (MvPolynomial.X 0 : DiagPhase 1 2) ![1]
      = Real.pi / 2 := by
    unfold DiagPhase.realPhase
    change 2 * Real.pi * ((DiagPhase.eval (MvPolynomial.X 0 : DiagPhase 1 2) ![1]).val : ℝ)
      / (2 : ℝ) ^ 2 = Real.pi / 2
    rw [DiagPhase.eval_X]
    have hv : ((((![1] : Fin 1 → ZMod 2) 0).val : ZMod (2 ^ 2))).val = 1 := by decide
    rw [hv]
    push_cast
    ring
  rw [hph]
  exact exp_I_pi_div_two

/-- The referee at `0` on the reading state: `i/√2`. -/
theorem walsh_readState_zero :
    walshTransform 0 (amp (ofKernelState readState)) ![0]
      = (1 / (Real.sqrt 2 : ℂ)) * Complex.I := by
  unfold walshTransform
  rw [show Function.update (![0] : Fin 1 → ZMod 2) 0 0 = ![0] from by decide,
    show Function.update (![0] : Fin 1 → ZMod 2) 0 1 = ![1] from by decide,
    amp_readState_zero, amp_readState_one]
  change (1 / (Real.sqrt 2 : ℂ)) * (0 + signOf 0 * Complex.I) = (1 / (Real.sqrt 2 : ℂ)) * Complex.I
  unfold signOf
  rw [if_pos rfl]
  ring

/-- **Control — `hqfree` is load-bearing.** `applyHPinned` on the reading state gives `1/√2` at the
word `0`; the referee gives `i/√2`. A version of `amp_ofKernelState_applyHPinned` without `hqfree`
is refuted here. -/
example :
    amp (ofKernelState (applyHPinned 0 readState)) ![0]
      ≠ walshTransform 0 (amp (ofKernelState readState)) ![0] := by
  rw [walsh_readState_zero]
  have hsup : ∃ p ∈ (ofKernelState (applyHPinned 0 readState)).L,
      (![0] : Fin 1 → ZMod 2) = (ofKernelState (applyHPinned 0 readState)).x₀ + p.X := by
    refine ⟨⟨0, 0⟩, ?_, ?_⟩
    · change (⟨0, 0⟩ : Pauli 1) ∈ Submodule.map (pauliSwapOn {0}) Lz
      exact Submodule.zero_mem _
    · change (![0] : Fin 1 → ZMod 2) = Function.update ![1] 0 0 + (⟨0, 0⟩ : Pauli 1).X
      decide
  rw [amp_pos hsup]
  change ampCore readState.m 0 (applyHPinned 0 readState).q ((1 : ℂ) / (Real.sqrt 2 : ℂ)) ![0]
    ≠ (1 / (Real.sqrt 2 : ℂ)) * Complex.I
  rw [ampCore_zero]
  have hev : @DiagPhase.eval (1 + 0) readState.m (applyHPinned 0 readState).q ![0] = 0 := by
    rw [applyHPinned_q_eval]
    simp only [readState]
    rw [DiagPhase.eval_X]
    decide
  have hph : @DiagPhase.realPhase (1 + 0) readState.m (applyHPinned 0 readState).q ![0] = 0 := by
    unfold DiagPhase.realPhase
    rw [hev]
    simp
  rw [hph]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  intro h
  have h1 : (1 : ℂ) = Complex.I := by
    have h' : (1 / (Real.sqrt 2 : ℂ)) * 1 = (1 / (Real.sqrt 2 : ℂ)) * Complex.I := by
      rw [mul_one]; exact h
    exact mul_left_cancel₀ one_div_sqrt_two_ne_zero'' h'
  have h2 := congrArg Complex.re h1
  simp at h2

/-- **The companion: `hRaise` at `u = 0` is right where `applyHPinned` is wrong.** On the same
reading state the raising rule is the Walsh transform, by the theorem, with no hypothesis on the
exponent — the content of the defect item `d1`, stated as a fact. -/
example :
    amp (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState readState))
      = walshTransform 0 (amp (ofKernelState readState)) :=
  amp_hRaise_zero_ofKernelState 0 readState orthogonal_omegaBilin_Lz.le
    (fun p hp => by rw [show p.X = 0 from mem_Lz.mp hp]; rfl) (by decide)

/-! ## Agreement — the classical register `1` on one qubit, three ways -/

/-- **Agreement, theorem route.** On the classical register both constructors have the same
amplitude, by the reduction theorem with `hqfree` discharged. -/
example :
    amp (ofKernelState (applyHPinned 0 (classical ![1])))
      = amp (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState (classical ![1]))) :=
  amp_ofKernelState_applyHPinned_eq_hRaise 0 (classical ![1]) (classical_qfree 0 ![1])

/-- The output support of `H` on the classical register `1` contains the word `1`. -/
theorem classical_one_out_support :
    ∃ p ∈ (ofKernelState (applyHPinned 0 (classical (![1] : Fin 1 → ZMod 2)))).L,
      (![1] : Fin 1 → ZMod 2)
        = (ofKernelState (applyHPinned 0 (classical (![1] : Fin 1 → ZMod 2)))).x₀ + p.X := by
  refine ⟨pauliSwapOn {0} ⟨0, ![1]⟩, Submodule.mem_map_of_mem (mem_Lz.mpr rfl), ?_⟩
  funext j
  fin_cases j
  simp [pauliSwapOn_X, ofKernelState, applyHPinned, classical]

/-- **Agreement, explicit route (pinned side).** `applyHPinned` on the register `1` at the word `1`:
exponent `1`, phase `π`, amplitude `−1/√2`. -/
example :
    amp (ofKernelState (applyHPinned 0 (classical (![1] : Fin 1 → ZMod 2)))) ![1]
      = -(1 / (Real.sqrt 2 : ℂ)) := by
  rw [amp_pos classical_one_out_support]
  change ampCore (classical (![1] : Fin 1 → ZMod 2)).m 0
    (applyHPinned 0 (classical (![1] : Fin 1 → ZMod 2))).q
    ((1 : ℂ) / (Real.sqrt 2 : ℂ)) ![1] = -(1 / (Real.sqrt 2 : ℂ))
  rw [ampCore_zero]
  have h0 : ∀ v : Fin 1 → ZMod 2, DiagPhase.eval (0 : DiagPhase 1 1) v = 0 := fun v => by
    simp [DiagPhase.eval]
  have hev : @DiagPhase.eval (1 + 0) (classical (![1] : Fin 1 → ZMod 2)).m
      (applyHPinned 0 (classical (![1] : Fin 1 → ZMod 2))).q ![1] = 1 := by
    rw [applyHPinned_q_eval]
    simp only [classical]
    rw [h0]
    decide
  have hph : @DiagPhase.realPhase (1 + 0) (classical (![1] : Fin 1 → ZMod 2)).m
      (applyHPinned 0 (classical (![1] : Fin 1 → ZMod 2))).q ![1] = Real.pi := by
    unfold DiagPhase.realPhase
    rw [hev]
    have hv : ((1 : ZMod (2 ^ (classical (![1] : Fin 1 → ZMod 2)).m))).val = 1 := by decide
    rw [hv]
    change 2 * Real.pi * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 1 = Real.pi
    norm_num
  rw [hph, show Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I from by ring,
    Complex.exp_pi_mul_I]
  ring

/-- **Agreement, explicit route (raising side).** `hRaise` at `u = 0` on the register `1` at the
word `1`: the frozen exponent is still `0`, the sign gives phase `π`, amplitude `−1/√2`. -/
example :
    amp (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))) ![1]
      = -(1 / (Real.sqrt 2 : ℂ)) := by
  have hsup : ∃ p ∈ (hRaise 0 (0 : Fin 1 → ZMod 2)
        (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))).L,
      (![1] : Fin 1 → ZMod 2)
        = (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))).x₀
          + p.X := classical_one_out_support
  rw [amp_pos hsup]
  change ampCore (classical (![1] : Fin 1 → ZMod 2)).m 0
    (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))).Q
    ((1 : ℂ) / (Real.sqrt 2 : ℂ)) ![1] = -(1 / (Real.sqrt 2 : ℂ))
  rw [ampCore_zero]
  have h0 : ∀ v : Fin 1 → ZMod 2, DiagPhase.eval (0 : DiagPhase 1 1) v = 0 := fun v => by
    simp [DiagPhase.eval]
  have hev : @DiagPhase.eval (1 + 0) (classical (![1] : Fin 1 → ZMod 2)).m
      (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))).Q ![1]
      = 1 := by
    rw [hRaise_zero_ofKernelState_eval]
    simp only [classical]
    rw [h0]
    decide
  have hph : @DiagPhase.realPhase (1 + 0) (classical (![1] : Fin 1 → ZMod 2)).m
      (hRaise 0 (0 : Fin 1 → ZMod 2) (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))).Q ![1]
      = Real.pi := by
    unfold DiagPhase.realPhase
    rw [hev]
    have hv : ((1 : ZMod (2 ^ (classical (![1] : Fin 1 → ZMod 2)).m))).val = 1 := by decide
    rw [hv]
    change 2 * Real.pi * ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 1 = Real.pi
    norm_num
  rw [hph, show Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I from by ring,
    Complex.exp_pi_mul_I]
  ring

/-- **Agreement, referee.** The Walsh transform of the register `1` at the word `1` is `−1/√2`. -/
example :
    walshTransform 0 (amp (ofKernelState (classical (![1] : Fin 1 → ZMod 2)))) ![1]
      = -(1 / (Real.sqrt 2 : ℂ)) := by
  unfold walshTransform
  have h0 : amp (ofKernelState (classical (![1] : Fin 1 → ZMod 2))) ![0] = 0 := by
    refine amp_neg ?_
    rintro ⟨p, hp, h⟩
    have hX : p.X = 0 := mem_Lz.mp hp
    change (![0] : Fin 1 → ZMod 2) = ![1] + p.X at h
    rw [hX, add_zero] at h
    have h0 := congrFun h 0
    revert h0
    decide
  have h1 : amp (ofKernelState (classical (![1] : Fin 1 → ZMod 2))) ![1] = 1 := by
    have hsup : ∃ p ∈ (ofKernelState (classical (![1] : Fin 1 → ZMod 2))).L,
        (![1] : Fin 1 → ZMod 2) = (ofKernelState (classical (![1] : Fin 1 → ZMod 2))).x₀ + p.X :=
      ⟨⟨0, 0⟩, mem_Lz.mpr rfl, by decide⟩
    rw [amp_pos hsup]
    change ampCore 1 0 (0 : DiagPhase (1 + 0) 1) 1 ![1] = 1
    rw [ampCore_zero, realPhase_zero_poly'']
    simp
  rw [show Function.update (![1] : Fin 1 → ZMod 2) 0 0 = ![0] from by decide,
    show Function.update (![1] : Fin 1 → ZMod 2) 0 1 = ![1] from by decide, h0, h1]
  change (1 / (Real.sqrt 2 : ℂ)) * (0 + signOf 1 * 1) = -(1 / (Real.sqrt 2 : ℂ))
  unfold signOf
  rw [if_neg (by decide)]
  ring

/-! ## Kernel rows — the `u = 0` branch data -/

/-- `raiseConst` at `u = 0` is the pinned bit. -/
example : raiseConst 0 (0 : Fin 1 → ZMod 2) (![1] : Fin 1 → ZMod 2) = 1 := by decide

/-- The zero representer pairs to nothing. -/
example : dotF2 (0 : Fin 3 → ZMod 2) (![1, 1, 0] : Fin 3 → ZMod 2) = 0 := by decide

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_zero_left' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms dotF2_zero_left

/-- info: 'FTQCLib.Frame.Walkthrough.raiseConst_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms raiseConst_zero

/-- info: 'FTQCLib.Frame.Walkthrough.hSignPoly_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms hSignPoly_eval

/-- info: 'FTQCLib.Frame.Walkthrough.applyHPinned_q_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms applyHPinned_q_eval

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_zero_ofKernelState_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hRaise_zero_ofKernelState_eval

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_applyHPinned_eq_hRaise' depends on
axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms amp_ofKernelState_applyHPinned_eq_hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hRaise_zero_ofKernelState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_hRaise_zero_ofKernelState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_applyHPinned' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_ofKernelState_applyHPinned

/-- info: 'FTQCLib.Frame.Walkthrough.classical_pinned' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms classical_pinned

/-- info: 'FTQCLib.Frame.Walkthrough.classical_qfree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms classical_qfree

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_applyHPinned_classical' depends on
axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms amp_ofKernelState_applyHPinned_classical

end FTQCLib.Frame.Walkthrough

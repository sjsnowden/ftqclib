/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ControlledHadamard
import FTQCLib.Carrier.GateWordCheck

/-!
# Check: witness for T08, controlled-H on carrier registers at any height

The rows below are about the referee `controlledHAmp` and the word's shape, independent of
`amp_controlledHWord`'s own proof, which is complete and gets its own axiom sweep below with the
lemmas it is built from (`sandwichWord`, `runAmp_sandwichWord_update_zero`,
`runAmp_sandwichWord_update_one`, `controlledHWord_eq_append`, `runAmp_controlledHWord`).

**On basis inputs** (`controlledHAmp` itself, the referee `T08` states the word against): on a
delta function at a point with control bit `0`, `controlledHAmp` is the identity, read off its own
`if`; on a delta function at a point with control bit `1`, it is the single-bit Walsh transform of
that delta, computed to the concrete value `1/√2` at two named output points — the point itself
and the point with the target bit flipped, matching the Walsh spread that a controlled-Z would not
produce.

**On a height-one input**: a fresh two-qubit carrier `heightOneState2` (the product `|+⟩ ⊗ |0⟩`,
Lagrangian `prodL = ⟨X₀, Z₁⟩` given by its constraints, in `bellL`'s style — coisotropy discharged
directly against the two generators, no rank computation) raised to height one at bit `0` by the
free rule `applyHFiner`, exactly as `GateWordCheck.lean`'s `heightOneState` is, but on two qubits so
its control and target (`0`, `1`) are distinct free bits. `amp_controlledHWord`'s hypotheses — a
carrier state, at the word's precision, control ≠ target, and a precision at least three and at
least the state's own — hold together on it: an inhabitation row.

**Discriminating against CZ**: on the delta at `![1,0]` (control bit `1`), read at the output point
`![1,1]`, `controlledHAmp` is `1/√2` (the Walsh spread reaches the point with the target bit
flipped) while CZ's referee (`letterAmp` of the diagonal letter `czGate`) is `0` there (a diagonal
gate never moves a delta's support off its input point) — the two controlled gates differ, named
at this input.

**The word on a basis input**: the controlled-H word's own referee (`runAmp`) at the same delta
and output point is the same `1/√2`, through `runAmp_controlledHWord`. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

-- source: papers/clifford_hierarchy/Barenco_1995_elementary_gates_quant-ph_9503016 lemma:5.1

/-! ## A delta function on the amplitude domain -/

/-- The amplitude delta at a point: `1` there, `0` elsewhere. -/
noncomputable def deltaAmp {n : ℕ} (p w : Fin n → ZMod 2) : ℂ := if w = p then 1 else 0

@[simp] theorem deltaAmp_self {n : ℕ} (p : Fin n → ZMod 2) : deltaAmp p p = 1 := if_pos rfl

theorem deltaAmp_of_ne {n : ℕ} {p w : Fin n → ZMod 2} (h : w ≠ p) : deltaAmp p w = 0 := if_neg h

/-! ## Basis inputs: `controlledHAmp` at the control bit's two values -/

/-- **Agreement, control bit `0`.** On a basis input whose control bit is `0`, `controlledHAmp` is
the identity: read at the input point itself, the output is the input's own value `1`, exactly
`controlledHAmp`'s own `if`. -/
-- row: agreement
theorem controlledHAmp_basis_control_zero :
    controlledHAmp (0 : Fin 2) 1 (deltaAmp (![0, 0] : Fin 2 → ZMod 2))
        (![0, 0] : Fin 2 → ZMod 2) = 1 := by
  simp [controlledHAmp]

/-- `Function.update` on `![1, 0]` at bit `1` to `0` is `![1, 0]` itself: bit `1` is already `0`. -/
theorem update_ten_one_zero :
    Function.update (![1, 0] : Fin 2 → ZMod 2) 1 0 = (![1, 0] : Fin 2 → ZMod 2) := by
  funext i
  fin_cases i <;> simp [Function.update]

/-- `Function.update` on `![1, 0]` at bit `1` to `1` is `![1, 1]`. -/
theorem update_ten_one_one :
    Function.update (![1, 0] : Fin 2 → ZMod 2) 1 1 = (![1, 1] : Fin 2 → ZMod 2) := by
  funext i
  fin_cases i <;> simp [Function.update]

/-- `Function.update` on `![1, 1]` at bit `1` to `0` is `![1, 0]`. -/
theorem update_eleven_one_zero :
    Function.update (![1, 1] : Fin 2 → ZMod 2) 1 0 = (![1, 0] : Fin 2 → ZMod 2) := by
  funext i
  fin_cases i <;> simp [Function.update]

/-- `Function.update` on `![1, 1]` at bit `1` to `1` is `![1, 1]` itself. -/
theorem update_eleven_one_one :
    Function.update (![1, 1] : Fin 2 → ZMod 2) 1 1 = (![1, 1] : Fin 2 → ZMod 2) := by
  funext i
  fin_cases i <;> simp [Function.update]

/-- The two points `![1,0]` and `![1,1]` are distinct. -/
theorem ten_ne_eleven : (![1, 0] : Fin 2 → ZMod 2) ≠ (![1, 1] : Fin 2 → ZMod 2) := by
  intro h
  have := congrFun h 1
  simp at this

/-- **Agreement, control bit `1`, read at the input point.** `controlledHAmp` on the delta at
`![1,0]` (control bit `1`), at `![1,0]` itself, is the Walsh transform's value there, computed to
`1/√2`. -/
-- row: agreement
theorem controlledHAmp_basis_control_one_ten :
    controlledHAmp (0 : Fin 2) 1 (deltaAmp (![1, 0] : Fin 2 → ZMod 2))
        (![1, 0] : Fin 2 → ZMod 2) = 1 / (Real.sqrt 2 : ℂ) := by
  unfold controlledHAmp
  rw [if_neg (by decide : ¬ (![1, 0] : Fin 2 → ZMod 2) 0 = 0)]
  unfold walshTransform
  rw [update_ten_one_zero, update_ten_one_one, deltaAmp_self,
    deltaAmp_of_ne ten_ne_eleven.symm]
  change (1 / (Real.sqrt 2 : ℂ)) * (1 + signOf ((![1, 0] : Fin 2 → ZMod 2) 1) * 0) = _
  norm_num [signOf]

/-- **Basis input, read at the target-flipped point.** The same run, read at `![1,1]` (the target
bit flipped from the input), is the same value `1/√2`: the Walsh transform spreads the delta to
both points that agree with it off the target bit. This is the point the discriminating row below
reuses against CZ. -/
-- row: agreement
theorem controlledHAmp_basis_control_one_eleven :
    controlledHAmp (0 : Fin 2) 1 (deltaAmp (![1, 0] : Fin 2 → ZMod 2))
        (![1, 1] : Fin 2 → ZMod 2) = 1 / (Real.sqrt 2 : ℂ) := by
  unfold controlledHAmp
  rw [if_neg (by decide : ¬ (![1, 1] : Fin 2 → ZMod 2) 0 = 0)]
  unfold walshTransform
  rw [update_eleven_one_zero, update_eleven_one_one, deltaAmp_self,
    deltaAmp_of_ne ten_ne_eleven.symm]
  change (1 / (Real.sqrt 2 : ℂ)) * (1 + signOf ((![1, 1] : Fin 2 → ZMod 2) 1) * 0) = _
  norm_num [signOf]

/-! ## A height-one input on two qubits: `prodL = ⟨X₀, Z₁⟩`, the product `|+⟩ ⊗ |0⟩` -/

/-- The product Lagrangian `⟨X₀, Z₁⟩`, by its constraints: no `X` on bit `1`, no `Z` on bit `0` —
`bellL`'s style, so coisotropy is discharged directly against the two generators below, with no
rank computation. -/
def prodL : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X 1 = 0 ∧ p.Z 0 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hp hq => ⟨by simp [hp.1, hq.1], by simp [hp.2, hq.2]⟩
  smul_mem' := fun _ _ hp => ⟨by simp [hp.1], by simp [hp.2]⟩

@[simp] theorem mem_prodL {p : Pauli 2} : p ∈ prodL ↔ p.X 1 = 0 ∧ p.Z 0 = 0 := Iff.rfl

/-- `prodL` is isotropic: on its two constraints the two sums defining `ω` vanish term by term. -/
theorem prodL_isStabilizer : IsStabilizer prodL := by
  intro p hp q hq
  show omega p q = 0
  unfold omega
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hp.1, hp.2, hq.1, hq.2]

/-- `prodL` is co-isotropic, discharged directly against its two generators `X₀` and `Z₁`
(`bellL_coisotropic`'s technique, no rank computation): anything ω-orthogonal to `X₀` has no `Z` on
bit `0`, and anything ω-orthogonal to `Z₁` has no `X` on bit `1` — exactly `prodL`'s constraints. -/
theorem prodL_coisotropic : LinearMap.BilinForm.orthogonal omegaBilin prodL ≤ prodL := by
  intro q hq
  have ha := hq (paulix 0) (mem_prodL.mpr ⟨by decide, rfl⟩)
  have hb := hq (pauliz 1) (mem_prodL.mpr ⟨rfl, by decide⟩)
  change omega (paulix 0) q = 0 at ha
  change omega (pauliz 1) q = 0 at hb
  rw [show (paulix (0 : Fin 2)) = (⟨Pi.single 0 1, 0⟩ : Pauli 2) from rfl, omega_pureX,
    dotF2_single_left] at ha
  rw [show (pauliz (1 : Fin 2)) = (⟨0, Pi.single 1 1⟩ : Pauli 2) from rfl, omega_pureZ,
    dotF2_single_left] at hb
  exact mem_prodL.mpr ⟨hb, ha⟩

/-- The flat-exponent, scale-`1`, `L = prodL` record at precision `1`. -/
noncomputable def KP : KernelState 2 := ⟨1, 0, 1, prodL, 0⟩

/-- `KP` denotes `1` at the origin: flat exponent, the trivial Pauli witnesses the origin's own
support. -/
theorem amp_KP_zero : amp (ofKernelState KP) (0 : Fin 2 → ZMod 2) = 1 := by
  rw [amp_ofKernelState_pos KP ⟨0, prodL.zero_mem, by simp [KP]⟩]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 2 1) (0 : Fin 2 → ZMod 2)) = 1
  rw [eval_zero_poly, charOf_zero, mul_one]

/-- `KP` is a carrier: positive precision, `prodL` a Lagrangian, nonzero at the origin. -/
theorem isCarrier_KP : IsCarrier (ofKernelState KP) := by
  refine ⟨le_rfl, prodL_isStabilizer, prodL_coisotropic, ?_⟩
  intro hzero
  have h0 := congrFun hzero (0 : Fin 2 → ZMod 2)
  rw [amp_KP_zero] at h0
  exact one_ne_zero h0

/-- Bit `0` of `prodL` is X-supported: `paulix 0 ∈ prodL` maps to `Pi.single 0 1` under `xProj`. -/
theorem pi_single_zero_mem_shadow_prodL :
    (Pi.single (0 : Fin 2) 1 : Fin 2 → ZMod 2) ∈ Submodule.map xProj prodL :=
  Submodule.mem_map.mpr ⟨paulix 0, mem_prodL.mpr ⟨by decide, rfl⟩, by simp⟩

/-- **The height-one input, on two qubits.** The free rule `applyHFiner` at bit `0` (X-supported):
one summation variable is adjoined, `h = 1`, and bits `0`, `1` stay distinct free bits, so a
controlled-H with control `0` and target `1` (or the reverse) applies to it. -/
noncomputable def heightOneState2 : KernelSumState 2 := applyHFiner (0 : Fin 2) (ofKernelState KP)

/-- **Carrier**, from `isCarrier_applyHFiner`, independent of `ControlledHadamard.lean`. -/
theorem isCarrier_heightOneState2 : IsCarrier heightOneState2 :=
  isCarrier_applyHFiner (0 : Fin 2) isCarrier_KP pi_single_zero_mem_shadow_prodL

/-- `heightOneState2`'s precision is `1`, `KP`'s own (`applyHFiner` does not change it). -/
theorem heightOneState2_m : heightOneState2.m = 1 := rfl

/-! ## Inhabitation: the frozen statement's hypotheses, on the height-one input -/

/-- **Inhabitation.** `amp_controlledHWord`'s hypotheses — a carrier state, distinct control and
target bits, and a precision at least three and at least the state's own (`1 ≤ 3`) — hold together
on `heightOneState2` with control `0` and target `1`: exhibiting the instance exhibits all four at
once. -/
-- row: inhabitation
example := amp_controlledHWord (S := heightOneState2) isCarrier_heightOneState2
  (show (0 : Fin 2) ≠ 1 by decide) 3 (by rw [heightOneState2_m]; norm_num) (by norm_num)

/-! ## Discriminating: against CZ, at the point the Walsh spread reaches -/

/-- CZ's referee: the diagonal letter's own `letterAmp`, `charOf` of `czGate`'s phase times the
input — the object controlled-H is not, read at the same delta and the same output point as
`controlledHAmp_basis_control_one_eleven`. A diagonal letter never moves a delta's support off its
input point, so it is `0` at `![1,1]` on the delta at `![1,0]`. -/
theorem czAmp_ten_at_eleven :
    letterAmp (m := 1) (.diagonal (czGate 1 (0 : Fin 2) 1))
        (deltaAmp (![1, 0] : Fin 2 → ZMod 2)) (![1, 1] : Fin 2 → ZMod 2) = 0 := by
  change charOf 1 ((czGate 1 (0 : Fin 2) 1).eval (![1, 1] : Fin 2 → ZMod 2))
      * deltaAmp (![1, 0] : Fin 2 → ZMod 2) (![1, 1] : Fin 2 → ZMod 2) = 0
  rw [deltaAmp_of_ne ten_ne_eleven.symm, mul_zero]

/-- **Discriminating.** At the delta on `![1,0]`, read at `![1,1]`: controlled-H's referee is
`1/√2` (the Walsh spread reaches the target-flipped point,
`controlledHAmp_basis_control_one_eleven`) while CZ's referee is `0` there
(`czAmp_ten_at_eleven`) — the two controlled gates differ, named at this input and this output
point. -/
-- row: discriminating
theorem controlledHAmp_ne_czAmp :
    controlledHAmp (0 : Fin 2) 1 (deltaAmp (![1, 0] : Fin 2 → ZMod 2)) (![1, 1] : Fin 2 → ZMod 2)
      ≠ letterAmp (m := 1) (.diagonal (czGate 1 (0 : Fin 2) 1))
          (deltaAmp (![1, 0] : Fin 2 → ZMod 2)) (![1, 1] : Fin 2 → ZMod 2) := by
  rw [controlledHAmp_basis_control_one_eleven, czAmp_ten_at_eleven]
  have h2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have h2' : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast h2
  exact one_div_ne_zero h2'

/-! ## The word on a basis input -/

/-- **Agreement, the word against the referee.** The controlled-H word at precision three, control
`0`, target `1`, run by its referee `runAmp` on the delta at `![1,0]` and read at `![1,1]`, is
`1/√2`: the value `controlledHAmp_basis_control_one_eleven` computes from the matrix, reached here
through `runAmp_controlledHWord`. -/
-- row: agreement
theorem runAmp_controlledHWord_basis_control_one_eleven :
    runAmp (controlledHWord 3 le_rfl (show (0 : Fin 2) ≠ 1 by decide))
        (deltaAmp (![1, 0] : Fin 2 → ZMod 2)) (![1, 1] : Fin 2 → ZMod 2)
      = 1 / (Real.sqrt 2 : ℂ) := by
  rw [runAmp_controlledHWord]
  exact controlledHAmp_basis_control_one_eleven

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.controlledHAmp' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms controlledHAmp

/-- info: 'FTQCLib.Frame.Walkthrough.controlledHWord' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms controlledHWord

/-- info: 'FTQCLib.Frame.Walkthrough.sandwichWord' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sandwichWord

/-- info: 'FTQCLib.Frame.Walkthrough.controlledHWord_eq_append' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms controlledHWord_eq_append

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_sandwichWord_update_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_sandwichWord_update_zero

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_sandwichWord_update_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_sandwichWord_update_one

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_controlledHWord' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_controlledHWord

/-- info: 'FTQCLib.Frame.Walkthrough.amp_controlledHWord' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_controlledHWord

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_controlledHWord_basis_control_one_eleven' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runAmp_controlledHWord_basis_control_one_eleven

/-! Congruence lemmas Lean generates in `ControlledHadamard.lean` for `simp`; public declarations of the module,
so the sweep covers them too. -/

/-- info: 'FTQCLib.Frame.Walkthrough.GateLetter.cnot.congr_simp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.GateLetter.cnot.congr_simp

/-- info: 'FTQCLib.Frame.Walkthrough.controlledHWord.congr_simp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.controlledHWord.congr_simp

/-- info: 'FTQCLib.Frame.Walkthrough.sum_normSq_controlledHAmp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_normSq_controlledHAmp

end FTQCLib.Frame.Walkthrough

-- mutant: swap_ct | FTQCLib/Carrier/ControlledHadamard.lean
--   | = controlledHAmp c t (amp S)
--   | = controlledHAmp t c (amp S)

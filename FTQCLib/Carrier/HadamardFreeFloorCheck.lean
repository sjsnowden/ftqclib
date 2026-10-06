/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.HadamardFreeFloor
import FTQCLib.Carrier.CarrierStateCheck

/-!
# Check: witness for T03, floor closure of the free H rule

T03's witness: `KX` (`FTQCLib.Carrier.CarrierStateCheck`, `L = ⟨X⟩` on one qubit, already on the
floor by `isFloor_KX`) has no `Z`-support at bit `0` (`lagX_no_Z`), so it meets the hypotheses of
`isFloor_applyHFree` at `ε = 0` with the free part of the exponent `q₀ = 0` (`hq_KX`, `hq0free_KX`)
— the **inhabitation** row: the frozen statement's hypotheses hold together on a concrete state,
independently of `isFloor_applyHFree`'s proof (proved since, T03.3).

The **discriminating** row does not use the theorem either: `applyHFree` is an unconditional field
transformer, so its output's denotation is computable directly from `amp_ofKernelState_pos` and
`amp_ofKernelState_neg`, without assuming the closure theorem. Every Lagrangian element of
`applyHFree`'s output has no `X`-support at bit `0` (`swapX_lagX_X_zero`, `pauliSwapOn` moves `X`
to `Z`), so the output's support is the singleton offset `Function.update 0 0 ε`
(`applyHFree_KX_support`). At `ε = 0` the offset is `0`, so `amp` at the word `0` is the nonzero
value `c · 1 = √2` (`amp_applyHFree_zero_zero`); at `ε = 1` the offset is `Function.update 0 0 1 ≠
0`, so the word `0` is off support and `amp` there is `0` (`amp_applyHFree_one_zero`). The two
runs of `applyHFree` on the same input, differing only in `ε`, are told apart at the word `0`
(`amp_applyHFree_ne_at_zero`) — `ε` is not decorative in the free rule's recollapse.

What no row here tests: `isCarrier_applyHFree` and `amp_ofKernelState_applyHFree`'s Walsh-transform
denotation, and `chartOf_applyHFree`'s certificate rewrite — proved since, in
`HadamardFreeFloor.lean`; this step only witnesses `isFloor_applyHFree`'s statement, as the target
names it. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## `KX`'s Lagrangian has no `Z`-support at bit `0` -/

/-- Every element of `lagX = ⟨X⟩` has no `Z`-support at bit `0`: `X` carries no `Z`-part. -/
theorem lagX_no_Z : ∀ p ∈ lagX, p.Z (0 : Fin 1) = 0 := by
  intro p hp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  simp

/-- The dyadic sign at `ε = 0` is the zero exponent: nothing is emitted. -/
theorem hSignPoly_zero_one (i : Fin 1) : hSignPoly i (0 : ZMod 2) 1 = 0 := by
  unfold hSignPoly
  simp

/-- `KX.q` is the flat exponent, split as `0 + hSignPoly 0 0 1` (`ε = 0` emits nothing). -/
theorem hq_KX : KX.q = (0 : DiagPhase 1 1) + hSignPoly (0 : Fin 1) (0 : ZMod 2) 1 := by
  rw [hSignPoly_zero_one, add_zero]
  rfl

/-- `q₀ = 0` is free of every bit: the flat exponent's evaluation never sees an update. -/
theorem hq0free_KX : ∀ (w : Fin 1 → ZMod 2) (b : ZMod 2),
    DiagPhase.eval (0 : DiagPhase 1 1) (Function.update w 0 b)
      = DiagPhase.eval (0 : DiagPhase 1 1) w := by
  intro w b
  simp [eval_zero_poly]

/-- **Inhabitation.** The hypotheses of `isFloor_applyHFree` (a floor input, no `Z`-support at the
bit, and the exponent split with a bit-free `q₀`) hold together on `KX` at `ε = 0`. -/
-- row: inhabitation
example : IsFloor (ofKernelState (applyHFree (0 : Fin 1) (0 : ZMod 2) KX)) :=
  isFloor_applyHFree (0 : Fin 1) (0 : ZMod 2) isFloor_KX lagX_no_Z 0 hq_KX hq0free_KX

/-! ## The output's support, computed directly (no `sorry`) -/

/-- `pauliSwapOn {0}` sends every element of `⟨X⟩` to a Pauli with no `X`-support at bit `0`: the
swap moves `X` to `Z`. -/
theorem swapX_lagX_X_zero (p : Pauli 1) (hp : p ∈ Submodule.map (pauliSwapOn {0}) lagX) :
    p.X 0 = 0 := by
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hq
  simp

/-- **The output's support is its offset.** `applyHFree`'s Lagrangian on `KX` carries no
`X`-support at bit `0`, so the only point of the support coset is the offset itself. -/
theorem applyHFree_KX_support (ε : ZMod 2) (w : Fin 1 → ZMod 2) :
    (∃ p ∈ (applyHFree (0 : Fin 1) ε KX).L, w = (applyHFree (0 : Fin 1) ε KX).x₀ + p.X) ↔
      w = (applyHFree (0 : Fin 1) ε KX).x₀ := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hX : p.X = 0 := by
      funext i
      fin_cases i
      exact swapX_lagX_X_zero p hp
    simp [hX]
  · rintro rfl
    exact ⟨0, Submodule.zero_mem _, by simp⟩

/-- At `ε = 0` the output's offset is `0`: updating `KX`'s flat offset at bit `0` to `0` changes
nothing. -/
theorem applyHFree_KX_x0_zero :
    (applyHFree (0 : Fin 1) (0 : ZMod 2) KX).x₀ = (0 : Fin 1 → ZMod 2) := by
  funext i
  fin_cases i
  simp [applyHFree, KX]

/-- At `ε = 1` the output's offset is not `0`: bit `0` now reads `1`. -/
theorem applyHFree_KX_x0_one_ne_zero :
    (applyHFree (0 : Fin 1) (1 : ZMod 2) KX).x₀ ≠ (0 : Fin 1 → ZMod 2) := by
  intro h
  have h0 := congrFun h (0 : Fin 1)
  simp [applyHFree, KX] at h0

/-! ## The discriminating row -/

/-- `applyHFree` at `ε = 0` on `KX`, read at the word `0`: on support, the nonzero value `√2`. -/
theorem amp_applyHFree_zero_zero :
    amp (ofKernelState (applyHFree (0 : Fin 1) (0 : ZMod 2) KX)) (0 : Fin 1 → ZMod 2)
      = (Real.sqrt 2 : ℂ) := by
  rw [amp_ofKernelState_pos _ ((applyHFree_KX_support 0 0).mpr applyHFree_KX_x0_zero.symm)]
  simp only [applyHFree, KX]
  rw [DiagPhase.eval_add, eval_zero_poly, eval_hSignPoly_one]
  norm_num [charOf_zero]

/-- `applyHFree` at `ε = 1` on `KX`, read at the word `0`: off support, `0`. -/
theorem amp_applyHFree_one_zero :
    amp (ofKernelState (applyHFree (0 : Fin 1) (1 : ZMod 2) KX)) (0 : Fin 1 → ZMod 2) = 0 := by
  apply amp_ofKernelState_neg
  rw [applyHFree_KX_support]
  exact fun h => applyHFree_KX_x0_one_ne_zero h.symm

/-- **Discriminating.** The free rule's two runs on `KX`, differing only in the recollapsed value
`ε`, are told apart at the word `0`: `√2 ≠ 0`. -/
-- row: discriminating
theorem amp_applyHFree_ne_at_zero :
    amp (ofKernelState (applyHFree (0 : Fin 1) (0 : ZMod 2) KX)) (0 : Fin 1 → ZMod 2)
      ≠ amp (ofKernelState (applyHFree (0 : Fin 1) (1 : ZMod 2) KX)) (0 : Fin 1 → ZMod 2) := by
  rw [amp_applyHFree_zero_zero, amp_applyHFree_one_zero]
  intro h
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact (Complex.ofReal_ne_zero.mpr hpos.ne') h

/-! ## The agreement row -/

/-- **Agreement.** The general Walsh-transform theorem, instantiated on `KX` at `ε = 0`, gives the
same value at the word `0` as the direct computation `amp_applyHFree_zero_zero`: `√2`. -/
-- row: agreement
theorem amp_ofKernelState_applyHFree_agrees_KX :
    amp (ofKernelState (applyHFree (0 : Fin 1) (0 : ZMod 2) KX)) (0 : Fin 1 → ZMod 2)
      = walshTransform (0 : Fin 1) (amp (ofKernelState KX)) (0 : Fin 1 → ZMod 2) :=
  congrFun (amp_ofKernelState_applyHFree (0 : Fin 1) (0 : ZMod 2) KX 0 hq_KX hq0free_KX
    isCarrier_KX.2.2.1 lagX_no_Z isCarrier_KX.1) (0 : Fin 1 → ZMod 2)

/-! ## The axiom sweep — build-failing, one guard per declaration of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_applyHFree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_ofKernelState_applyHFree

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyHFree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyHFree

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyHFree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyHFree

/-- info: 'FTQCLib.Frame.Walkthrough.chartOf_applyHFree' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartOf_applyHFree

end FTQCLib.Frame.Walkthrough

-- mutant: hx0 | FTQCLib/Carrier/HadamardFreeFloor.lean | (hx0 : x₀ i = 0) | (hx0 : x₀ i = 1)

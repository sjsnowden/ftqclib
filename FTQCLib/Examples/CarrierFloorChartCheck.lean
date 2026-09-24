/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierFloorChart
import FTQCLib.Examples.CarrierStateCheck

/-!
# Check: the floor chart at the offset

* **Two records of one state.** The two-qubit graph state `L = ⟨X₀Z₁, Z₀X₁⟩`, `q = X₀X₁`, at
  `m = 1`, recorded with offsets `00` and `01`, has one denotation (`amp_graphState_eq`). The
  decode read at the origin (`rawChiOld`, the formula `2·q(w)` with the coset correction, kept
  here as the reference), gives `0` and `2` at the generator `X₀Z₁`
  (`rawChiOld_graphState_ne`): that chart was not a function of the state. The decode at the
  offset gives `0` at both (`chiAt_graphState_00`, `chiAt_graphState_01`) — the state's own
  character — so `chiAt` agrees where the origin decode disagreed.
* **The character is the eigenphase, on `KX`.** `chiAt KX X = 0` (kernel row after the flat
  exponent evaluates), and `chiAt_eq_character` gives `pauliAct X amp = i^0 · amp`; the direct
  computation gives the same (`character_KX_direct`).
* **`1 ≤ m` is load-bearing in `shiftConsistent_eAt_iff`.** At `m = 0` the exponent law holds
  trivially (the exponent ring is trivial) while the chart exponent `eAt` is `0` and the shift
  recurrence demands `2·(g.Z·u)`: on `L = ⟨Y⟩` and `u = e₀` it fails (`hm1_load_bearing`).
* **`toFour` values** at precisions `1` and `2` (kernel rows).

Not tested here: `m ≤ 2` in the chart theorems — the chart is defined at precision at most `2` by
construction (the `ZMod 4` exponent), so the hypothesis is the chart's domain, not a guard on a
claim that could hold beyond it. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Module

/-! ## `toFour` values -/

/-- At precision `1`, `toFour` doubles. -/
theorem toFour_one_one : toFour 1 1 = 2 := by decide

/-- At precision `2`, `toFour` is the identity. -/
theorem toFour_two_three : toFour 2 3 = 3 := by decide

/-! ## Two records of the graph state -/

/-- The graph-state Lagrangian `⟨X₀Z₁, Z₀X₁⟩`. -/
def graphL : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X 0 = p.Z 1 ∧ p.X 1 = p.Z 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hp hq => ⟨by simp [hp.1, hq.1], by simp [hp.2, hq.2]⟩
  smul_mem' := fun c _ hp => ⟨by simp [hp.1], by simp [hp.2]⟩

/-- The graph state's record, with a chosen coset offset. -/
noncomputable def graphState (x₀ : Fin 2 → ZMod 2) : KernelState 2 where
  m := 1
  q := MvPolynomial.X 0 * MvPolynomial.X 1
  c := 1
  L := graphL
  x₀ := x₀

/-- Every word is on the support, whatever the offset: the shadow is everything. -/
theorem graphState_support (x₀ w : Fin 2 → ZMod 2) :
    ∃ p ∈ (ofKernelState (graphState x₀)).L, w = (ofKernelState (graphState x₀)).x₀ + p.X := by
  have key : ∀ w x₀ : Fin 2 → ZMod 2, w = x₀ + (w + x₀) := by decide
  refine ⟨⟨w + x₀, ![(w + x₀) 1, (w + x₀) 0]⟩, ?_, key w x₀⟩
  change (w + x₀) 0 = (![(w + x₀) 1, (w + x₀) 0] : Fin 2 → ZMod 2) 1
    ∧ (w + x₀) 1 = (![(w + x₀) 1, (w + x₀) 0] : Fin 2 → ZMod 2) 0
  exact ⟨rfl, rfl⟩

/-- **One denotation.** The two offsets give the same amplitude. -/
theorem amp_graphState_eq :
    amp (ofKernelState (graphState ![0, 0])) = amp (ofKernelState (graphState ![0, 1])) := by
  funext w
  rw [amp_pos (graphState_support ![0, 0] w), amp_pos (graphState_support ![0, 1] w)]
  rfl

/-- The generator `X₀Z₁`. -/
def gXZ : Pauli 2 := ⟨![1, 0], ![0, 1]⟩

/-- `X₀Z₁` is in the graph-state Lagrangian. -/
theorem gXZ_mem : gXZ ∈ graphL := ⟨rfl, rfl⟩

/-- The exponent evaluates to the product of the two bits. -/
theorem eval_graph_q (v : Fin 2 → ZMod 2) :
    DiagPhase.eval (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase 2 1) v
      = ((v 0).val : ZMod (2 ^ 1)) * ((v 1).val : ZMod (2 ^ 1)) := by
  rw [DiagPhase.eval_mul, DiagPhase.eval_X, DiagPhase.eval_X]

/-- The chart exponent read at the origin: `2·q(w)`. Kept as the reference that fails at a
nonzero offset. -/
noncomputable def eOfOld (K : KernelState 2) : (Fin 2 → ZMod 2) → ZMod 4 :=
  fun w => 2 * ((DiagPhase.eval K.q w).val : ZMod 4)

/-- The decode read at the origin: `chiOfE (eOfOld K) g − 2·(g.Z·x₀)`. -/
noncomputable def rawChiOld (K : KernelState 2) (g : Pauli 2) : ZMod 4 :=
  chiOfE (eOfOld K) g - 2 * ((zDot g K.x₀ : ℕ) : ZMod 4)

/-- **The origin decode differs.** `rawChiOld` at `X₀Z₁` is `0` for offset `00` and `2` for `01`. -/
theorem rawChiOld_graphState_ne :
    rawChiOld (graphState ![0, 0]) gXZ ≠ rawChiOld (graphState ![0, 1]) gXZ := by
  unfold rawChiOld chiOfE eOfOld
  simp only [graphState, eval_graph_q]
  decide

/-- **The new decode agrees**: `chiAt` at `X₀Z₁` is `0` for offset `00`. -/
theorem chiAt_graphState_00 : chiAt (graphState ![0, 0]) gXZ = 0 := by
  unfold chiAt chiOfE eAt
  simp only [graphState, eval_graph_q]
  decide

/-- **The new decode agrees**: `chiAt` at `X₀Z₁` is `0` for offset `01` as well. -/
theorem chiAt_graphState_01 : chiAt (graphState ![0, 1]) gXZ = 0 := by
  unfold chiAt chiOfE eAt
  simp only [graphState, eval_graph_q]
  decide

/-- **The main row, frame-pure.** Two records with one denotation: the origin decode differs, the
offset decode agrees. -/
theorem d2_repaired :
    amp (ofKernelState (graphState ![0, 0])) = amp (ofKernelState (graphState ![0, 1]))
      ∧ rawChiOld (graphState ![0, 0]) gXZ ≠ rawChiOld (graphState ![0, 1]) gXZ
      ∧ chiAt (graphState ![0, 0]) gXZ = chiAt (graphState ![0, 1]) gXZ :=
  ⟨amp_graphState_eq, rawChiOld_graphState_ne, by rw [chiAt_graphState_00, chiAt_graphState_01]⟩

/-! ## The character is the eigenphase, on `KX` -/

/-- `chiAt KX X = 0`. -/
theorem chiAt_KX_X : chiAt KX (paulix 0) = 0 := by
  unfold chiAt chiOfE eAt
  simp only [KX, eval_zero_poly]
  decide

/-- Through the theorem: `X` acts on `KX`'s denotation by `i^{chiAt KX X} = 1`. -/
theorem character_KX :
    pauliAct (paulix 0) (amp (ofKernelState KX))
      = fun w => Complex.I ^ (chiAt KX (paulix 0)).val * amp (ofKernelState KX) w :=
  chiAt_eq_character KX isFloor_KX (by decide)
    (by change _ ∈ Submodule.span (ZMod 2) {paulix 0}; exact Submodule.mem_span_singleton_self _)

/-- Directly: `X` shifts the constant function to itself. -/
theorem character_KX_direct :
    pauliAct (paulix 0) (amp (ofKernelState KX)) = fun w => amp (ofKernelState KX) w := by
  funext w
  have hy : yWeight (paulix 0 : Pauli 1) = 0 := by decide
  have hz : ∀ v : Fin 1 → ZMod 2, zDot (paulix (0 : Fin 1)) v = 0 := by
    intro v
    simp [zDot, paulix]
  simp only [pauliAct, hy, hz, pow_zero, one_mul, amp_KX]

/-- The two agree: the theorem's scalar is `1`. -/
theorem character_KX_agrees :
    (fun w => Complex.I ^ (chiAt KX (paulix 0)).val * amp (ofKernelState KX) w)
      = fun w => amp (ofKernelState KX) w := by
  rw [chiAt_KX_X]
  simp

/-! ## `1 ≤ m` is load-bearing -/

/-- The precision-`0` record with the stale Lagrangian `⟨Y⟩`. -/
noncomputable def K0m : KernelState 1 := ⟨0, 0, 1, Submodule.span (ZMod 2) {paulix 0 + pauliz 0}, 0⟩

/-- At precision `0` the exponent law holds trivially. -/
theorem shiftLaw_K0m : ShiftLaw K0m := by
  intro g _
  haveI : Subsingleton (ZMod (2 ^ K0m.m)) := by
    change Subsingleton (ZMod (2 ^ 0))
    rw [pow_zero]
    exact inferInstanceAs (Subsingleton (ZMod 1))
  exact ⟨0, fun _ _ => Subsingleton.elim _ _⟩

/-- At precision `0` the chart exponent is not shift-consistent on `⟨Y⟩`. -/
theorem not_shiftConsistent_K0m : ¬ ShiftConsistent K0m.L (eAt K0m) := by
  intro h
  have hmem : paulix 0 + pauliz 0 ∈ K0m.L := Submodule.mem_span_singleton_self _
  have hu : (![1] : Fin 1 → ZMod 2) ∈ supportSpace K0m.L := by
    rw [supportSpace_eq_map_xProj]
    exact Submodule.mem_map.mpr ⟨paulix 0 + pauliz 0, hmem, by decide⟩
  have hrec := h (paulix 0 + pauliz 0) hmem ![1] hu
  have he : ∀ u, eAt K0m u = 0 := by
    intro u
    unfold eAt toFour
    have h4 : (2 : ZMod 4) ^ (2 - K0m.m) = 0 := by decide
    rw [h4, zero_mul]
  rw [he, he, he] at hrec
  have hz : zDot (paulix 0 + pauliz 0 : Pauli 1) ![1] = 1 := by decide
  rw [hz] at hrec
  revert hrec
  decide

/-- **`1 ≤ m` is load-bearing.** Without it `shiftConsistent_eAt_iff` would be false on `K0m`. -/
theorem hm1_load_bearing : ShiftLaw K0m ∧ ¬ ShiftConsistent K0m.L (eAt K0m) :=
  ⟨shiftLaw_K0m, not_shiftConsistent_K0m⟩

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.toFour' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms toFour

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms toFour_zero

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms toFour_add

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_sub' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms toFour_sub

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_injective' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms toFour_injective

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_two_pow_pred_mul' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toFour_two_pow_pred_mul

/-- info: 'FTQCLib.Frame.Walkthrough.toFour_two_pow_pred_mul_natCast' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toFour_two_pow_pred_mul_natCast

/-- info: 'FTQCLib.Frame.Walkthrough.eAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eAt

/-- info: 'FTQCLib.Frame.Walkthrough.eAt_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms eAt_zero

/-- info: 'FTQCLib.Frame.Walkthrough.supportSpace_eq_map_xProj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supportSpace_eq_map_xProj

/-- info: 'FTQCLib.Frame.Walkthrough.mem_shadow_iff_support' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_shadow_iff_support

/-- info: 'FTQCLib.Frame.Walkthrough.shiftConsistent_eAt_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftConsistent_eAt_iff

/-- info: 'FTQCLib.Frame.Walkthrough.chiAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chiAt

/-- info: 'FTQCLib.Frame.Walkthrough.decodeAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms decodeAt

/-- info: 'FTQCLib.Frame.Walkthrough.chiAt_eq_fullChi' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chiAt_eq_fullChi

/-- info: 'FTQCLib.Frame.Walkthrough.chiAt_valid' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms chiAt_valid

/-- info: 'FTQCLib.Frame.Walkthrough.zeta_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zeta_one

/-- info: 'FTQCLib.Frame.Walkthrough.zeta_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zeta_two

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_eq_I_pow_toFour' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms charOf_eq_I_pow_toFour

/-- info: 'FTQCLib.Frame.Walkthrough.chiAt_eq_character' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chiAt_eq_character

end FTQCLib.Frame.Walkthrough

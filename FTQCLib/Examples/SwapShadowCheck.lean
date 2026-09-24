/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.SwapShadow

/-!
# Check: the swapped shadow and alignment at a bit

Four Lagrangians presented by their constraints, so that membership is definitional:
`⟨Y₀⟩` and `⟨X₀⟩` on one qubit, the graph-state Lagrangian `⟨X₀Z₁, Z₀X₁⟩` and `⟨X₀, X₁⟩` on two.

* **Rotate, aligned** (`⟨Y₀⟩`, bit `0`): the reader `Y₀` has Z-entry `1`; the swapped shadow is the
  shadow, through the theorem and by an explicit witness.
* **Rotate, not aligned** (`⟨X₀⟩`, bit `0`) — discriminating: no reader has Z-entry `1`, and
  the swapped shadow loses the word `1`.
* **Collapse, aligned** (`⟨X₀Z₁, Z₀X₁⟩`, bit `0`, datum `σ = (1,1)`): `X₀Z₁ = ⟨e₀, σ + e₀⟩` is
  in `L`; the swapped shadow is the even words `{00, 11}`, through the theorem (with the isotropy
  of the graph Lagrangian) and by an explicit witness for `11`, and it omits `10`.
* **Collapse, stale `L`** (`⟨X₀, X₁⟩`, the same datum) — discriminating: the alignment does not
  hold, the cut `⟨σ, v⟩ = 0` still admits `11`, and the unaligned swap's shadow does not contain
  it. The alignment hypothesis is load-bearing.
* **Alignment by a shear**: the shear at `0` by `e₀` carries `⟨X₀⟩` to a rotate-aligned subspace
  (through the theorem), with `X₀ ↦ Y₀` by the kernel.
* **The coherence identity** (`map_pauliSwapOn_eq_pauliCondition`): on `⟨X₀⟩` the swap's image is
  the conditioning by `Z₀` (the output Lagrangian `⟨Z₀⟩` of the eliminating H on the uniform
  record); on the graph Lagrangian it is the conditioning by `Z₀Z₁` (the Bell Lagrangian: `Z₀Z₁`
  and `X₀X₁` in it); on the stale `⟨X₀, X₁⟩`, where the alignment
  does not hold, `X₁` is in the swap's image and not in the conditioning — the hypothesis is
  load-bearing.

Shadow membership is discharged by explicit witnesses or by the theorems, never by `decide` on a
`Submodule.map`; the `Pauli` and `ZMod 2` facts are kernel rows. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## The Lagrangians -/

/-- `⟨Y₀⟩` on one qubit: equal X- and Z-entries. -/
def lagY : Submodule (ZMod 2) (Pauli 1) where
  carrier := {p | p.X 0 = p.Z 0}
  zero_mem' := rfl
  add_mem' := fun hp hq => by
    simp only [Set.mem_setOf_eq, X_add, Z_add, Pi.add_apply] at *
    rw [hp, hq]
  smul_mem' := fun c _ hp => by
    simp only [Set.mem_setOf_eq, X_smul, Z_smul, Pi.smul_apply] at *
    rw [hp]

@[simp] theorem mem_lagY {p : Pauli 1} : p ∈ lagY ↔ p.X 0 = p.Z 0 := Iff.rfl

/-- `⟨X₀⟩` on one qubit: no Z-part. -/
def lagX1 : Submodule (ZMod 2) (Pauli 1) where
  carrier := {p | p.Z 0 = 0}
  zero_mem' := rfl
  add_mem' := fun hp hq => by
    simp only [Set.mem_setOf_eq, Z_add, Pi.add_apply] at *
    rw [hp, hq, add_zero]
  smul_mem' := fun c _ hp => by
    simp only [Set.mem_setOf_eq, Z_smul, Pi.smul_apply] at *
    rw [hp, smul_zero]

@[simp] theorem mem_lagX1 {p : Pauli 1} : p ∈ lagX1 ↔ p.Z 0 = 0 := Iff.rfl

/-- The graph-state Lagrangian `⟨X₀Z₁, Z₀X₁⟩`: each Z-entry equals the other X-entry. -/
def graphL : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.Z 0 = p.X 1 ∧ p.Z 1 = p.X 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hp hq => ⟨by simp only [X_add, Z_add, Pi.add_apply]; rw [hp.1, hq.1],
    by simp only [X_add, Z_add, Pi.add_apply]; rw [hp.2, hq.2]⟩
  smul_mem' := fun c _ hp => ⟨by simp only [X_smul, Z_smul, Pi.smul_apply]; rw [hp.1],
    by simp only [X_smul, Z_smul, Pi.smul_apply]; rw [hp.2]⟩

@[simp] theorem mem_graphL {p : Pauli 2} : p ∈ graphL ↔ p.Z 0 = p.X 1 ∧ p.Z 1 = p.X 0 := Iff.rfl

/-- The graph-state Lagrangian is isotropic. -/
theorem graphL_isStabilizer : IsStabilizer graphL := by
  intro p hp q hq
  unfold omega
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hp.1, hp.2, hq.1, hq.2]
  exact (show ∀ a b c d : ZMod 2, a * b + c * d + (c * d + a * b) = 0 by decide) _ _ _ _

/-- `⟨X₀, X₁⟩` on two qubits: no Z-part. -/
def lagXX : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.Z = 0}
  zero_mem' := rfl
  add_mem' := fun hp hq => by
    simp only [Set.mem_setOf_eq, Z_add] at *
    rw [hp, hq, add_zero]
  smul_mem' := fun c _ hp => by
    simp only [Set.mem_setOf_eq, Z_smul] at *
    rw [hp, smul_zero]

@[simp] theorem mem_lagXX {p : Pauli 2} : p ∈ lagXX ↔ p.Z = 0 := Iff.rfl

/-! ## Rotate, aligned: `⟨Y₀⟩` -/

/-- `Y₀` is an aligned reader of bit `0` in `⟨Y₀⟩`. -/
theorem alignedRotate_lagY : AlignedRotate lagY 0 :=
  ⟨paulix 0 + pauliz 0, ⟨mem_lagY.mpr (by decide), by decide⟩, by decide⟩

/-- Through the theorem: the swapped shadow of `⟨Y₀⟩` is its shadow, at every word. -/
theorem shadow_swap_lagY (v : Fin 1 → ZMod 2) :
    v ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) lagY) ↔ v ∈ Submodule.map xProj lagY :=
  mem_xProj_map_pauliSwapOn_iff_of_alignedRotate alignedRotate_lagY v

/-- By witness: the word `1` is in the swapped shadow (the swap fixes `Y₀`). -/
theorem one_mem_shadow_swap_lagY :
    (![1] : Fin 1 → ZMod 2) ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) lagY) :=
  Submodule.mem_map.mpr ⟨pauliSwapOn {0} (paulix 0 + pauliz 0),
    Submodule.mem_map_of_mem (mem_lagY.mpr (by decide)), by decide⟩

/-! ## Rotate, not aligned: `⟨X₀⟩` -/

/-- No reader of bit `0` in `⟨X₀⟩` has Z-entry `1`. -/
theorem not_alignedRotate_lagX1 : ¬ AlignedRotate lagX1 0 := by
  rintro ⟨g, ⟨hg, -⟩, hZ⟩
  rw [mem_lagX1] at hg
  rw [hg] at hZ
  exact absurd hZ (by decide)

/-- **Discriminating.** The unaligned swap loses the word `1`: the swapped shadow of `⟨X₀⟩` is the
shadow of `⟨Z₀⟩`. -/
theorem one_not_mem_shadow_swap_lagX1 :
    (![1] : Fin 1 → ZMod 2) ∉ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) lagX1) := by
  rintro ⟨q, hq, hqv⟩
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
  rw [mem_lagX1] at hp
  have h0 := congrFun hqv 0
  rw [xProj_pauliSwapOn_singleton, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one, xProj_apply, hp, add_zero, CharTwo.add_self_eq_zero] at h0
  exact absurd h0 (by decide)

/-! ## Collapse, aligned: the graph state at bit `0` -/

/-- `X₀Z₁ = ⟨e₀, σ + e₀⟩` with `σ = (1,1)` lies in the graph Lagrangian. -/
theorem alignedCollapse_graphL : AlignedCollapse graphL 0 ![1, 1] :=
  mem_graphL.mpr ⟨by decide, by decide⟩

/-- Through the theorem: the swapped shadow is the shadow cut by `v₀ + v₁ = 0`. -/
theorem shadow_swap_graphL (v : Fin 2 → ZMod 2) :
    v ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) graphL)
      ↔ v ∈ Submodule.map xProj graphL ∧ dotF2 ![1, 1] v = 0 :=
  mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse alignedCollapse_graphL (by decide)
    (orth_of_alignedCollapse graphL_isStabilizer alignedCollapse_graphL) v

/-- The word `11` is in the shadow of the graph Lagrangian (`Y₀Y₁` reads it). -/
theorem eleven_mem_shadow_graphL :
    (![1, 1] : Fin 2 → ZMod 2) ∈ Submodule.map xProj graphL :=
  Submodule.mem_map.mpr ⟨⟨![1, 1], ![1, 1]⟩, mem_graphL.mpr ⟨rfl, rfl⟩, by decide⟩

/-- Through the theorem: `11` survives the collapse cut. -/
theorem eleven_mem_shadow_swap_graphL :
    (![1, 1] : Fin 2 → ZMod 2) ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) graphL) :=
  (shadow_swap_graphL _).mpr ⟨eleven_mem_shadow_graphL, by decide⟩

/-- **Agreement.** By witness: the swap at `0` of `Z₀X₁ ∈ graphL` is `X₀X₁`, whose X-part is
`11`. -/
theorem eleven_mem_shadow_swap_graphL_witness :
    (![1, 1] : Fin 2 → ZMod 2) ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) graphL) :=
  Submodule.mem_map.mpr ⟨pauliSwapOn {0} ⟨![0, 1], ![1, 0]⟩,
    Submodule.mem_map_of_mem (mem_graphL.mpr ⟨rfl, rfl⟩), by decide⟩

/-- Through the theorem: `10` is cut away. -/
theorem ten_not_mem_shadow_swap_graphL :
    (![1, 0] : Fin 2 → ZMod 2) ∉ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) graphL) := by
  intro h
  have h' := ((shadow_swap_graphL _).mp h).2
  exact absurd h' (by decide)

/-! ## Collapse, stale `L`: `⟨X₀, X₁⟩` with the same datum -/

/-- `⟨X₀, X₁⟩` is not collapse-aligned at bit `0` for the datum `(1,1)`: the Pauli would need
Z-part `e₁`. -/
theorem not_alignedCollapse_lagXX : ¬ AlignedCollapse lagXX 0 ![1, 1] := by
  intro h
  rw [AlignedCollapse, mem_lagXX] at h
  have h1 := congrFun h 1
  exact absurd h1 (by decide)

/-- The cut still admits `11`: the datum's prediction holds on the shadow. -/
theorem eleven_mem_cut_lagXX :
    (![1, 1] : Fin 2 → ZMod 2) ∈ Submodule.map xProj lagXX ∧ dotF2 ![1, 1] ![1, 1] = 0 :=
  ⟨Submodule.mem_map.mpr ⟨⟨![1, 1], 0⟩, mem_lagXX.mpr rfl, by decide⟩, by decide⟩

/-- **Discriminating.** The unaligned swap's shadow does not contain `11`: with no Z-part, the swap
zeroes entry `0`. The alignment hypothesis of the collapse theorem is load-bearing. -/
theorem eleven_not_mem_shadow_swap_lagXX :
    (![1, 1] : Fin 2 → ZMod 2) ∉ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) lagXX) := by
  rintro ⟨q, hq, hqv⟩
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
  rw [mem_lagXX] at hp
  have h0 := congrFun hqv 0
  rw [xProj_pauliSwapOn_singleton, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one, xProj_apply, hp, Pi.zero_apply, add_zero, CharTwo.add_self_eq_zero] at h0
  exact absurd h0 (by decide)

/-! ## Alignment by a shear -/

/-- `X₀` reads bit `0` in `⟨X₀⟩`. -/
theorem isReader_lagX1 : IsReader lagX1 0 (paulix 0) := ⟨mem_lagX1.mpr rfl, by decide⟩

/-- Through the theorem: the shear at `0` by `e₀` makes `⟨X₀⟩` rotate-aligned. -/
theorem alignedRotate_shear_lagX1 :
    AlignedRotate (Submodule.map (zShear 0 ((1 + (paulix 0 : Pauli 1).Z 0) • Pi.single 0 1)) lagX1)
      0 :=
  alignedRotate_map_zShear_of_reader isReader_lagX1

/-- By the kernel: that shear is the shear by `e₀`, and it sends `X₀` to `Y₀`. -/
theorem shear_lagX1_reader :
    zShear 0 ((1 + (paulix 0 : Pauli 1).Z 0) • Pi.single 0 1) (paulix 0 : Pauli 1)
      = paulix 0 + pauliz 0 := by
  decide

/-! ## The coherence identity on the instances: `⟨X₀⟩`, the graph Lagrangian, the stale control -/

/-- `⟨X₀⟩` is isotropic. -/
theorem lagX1_isStabilizer : IsStabilizer lagX1 := by
  intro p hp q hq
  have hp' : p.Z 0 = 0 := hp
  have hq' : q.Z 0 = 0 := hq
  unfold omega
  rw [Fin.sum_univ_one, Fin.sum_univ_one, hp', hq', zero_mul, mul_zero, add_zero]

/-- `X₀ = ⟨e₀, σ + e₀⟩` with `σ = ![1]` lies in `⟨X₀⟩`: collapse alignment at bit `0`. -/
theorem alignedCollapse_lagX1 : AlignedCollapse lagX1 0 ![1] :=
  mem_lagX1.mpr (by decide)

/-- `Z^{![1]}` is `Z₀`. -/
theorem zPauli_one : zPauli ![1] = pauliz (0 : Fin 1) := by
  ext i <;> fin_cases i <;> rfl

/-- **The uniform record at the Lagrangian.** The swap's image of `⟨X₀⟩` is the conditioning of
`⟨X₀⟩` by `Z₀`. -/
theorem swap_lagX1_eq_pauliCondition :
    Submodule.map (pauliSwapOn {(0 : Fin 1)}) lagX1 = pauliCondition lagX1 (pauliz 0) := by
  rw [← zPauli_one]
  exact map_pauliSwapOn_eq_pauliCondition lagX1_isStabilizer alignedCollapse_lagX1 rfl

/-- Hence `Z₀` is in the swap's image — the output Lagrangian `⟨Z₀⟩` of the
eliminating H on the uniform record. -/
theorem pauliz_mem_swap_lagX1 : pauliz 0 ∈ Submodule.map (pauliSwapOn {(0 : Fin 1)}) lagX1 := by
  rw [swap_lagX1_eq_pauliCondition]
  exact pauliCondition_mem _ _

/-- **The Bell record at the Lagrangian.** The swap's image of the graph Lagrangian is its
conditioning by `Z^{(1,1)} = Z₀Z₁`. -/
theorem swap_graphL_eq_pauliCondition :
    Submodule.map (pauliSwapOn {(0 : Fin 2)}) graphL = pauliCondition graphL (zPauli ![1, 1]) :=
  map_pauliSwapOn_eq_pauliCondition graphL_isStabilizer alignedCollapse_graphL rfl

/-- `Z^{(1,1)} = Z₀ + Z₁`. -/
theorem zPauli_one_one : zPauli ![1, 1] = pauliz (0 : Fin 2) + pauliz 1 := by
  ext i <;> fin_cases i <;> rfl

/-- `Z₀Z₁` is in the swap's image of the graph Lagrangian — the Bell record's Lagrangian. -/
theorem zz_mem_swap_graphL :
    pauliz 0 + pauliz 1 ∈ Submodule.map (pauliSwapOn {(0 : Fin 2)}) graphL := by
  rw [swap_graphL_eq_pauliCondition, ← zPauli_one_one]
  exact pauliCondition_mem _ _

/-- `X₀X₁` is in the conditioning of the graph Lagrangian by `Z₀Z₁`: through the identity it is the
swap of `Z₀X₁`. -/
theorem xx_mem_pauliCondition_graphL :
    paulix 0 + paulix 1 ∈ pauliCondition graphL (zPauli ![1, 1]) := by
  rw [← swap_graphL_eq_pauliCondition]
  exact Submodule.mem_map.mpr ⟨pauliz 0 + paulix 1, mem_graphL.mpr ⟨by decide, by decide⟩,
    by ext i <;> fin_cases i <;> decide⟩

/-- **Control (stale `L`, first half).** On `⟨X₀, X₁⟩` the identity's hypothesis is not met
(`not_alignedCollapse_lagXX`); `X₁` is in the swap's image. -/
theorem x1_mem_swap_lagXX : paulix 1 ∈ Submodule.map (pauliSwapOn {(0 : Fin 2)}) lagXX :=
  Submodule.mem_map.mpr ⟨paulix 1, mem_lagXX.mpr rfl, by ext i <;> fin_cases i <;> decide⟩

/-- **Control (stale `L`, second half).** `X₁` is not in the conditioning of `⟨X₀, X₁⟩` by `Z₀Z₁`:
the identity's conclusion is false where its hypothesis is not met. -/
theorem x1_not_mem_pauliCondition_lagXX : paulix 1 ∉ pauliCondition lagXX (zPauli ![1, 1]) := by
  have hQ : zPauli ![1, 1] ∉ lagXX := fun h => by
    have h0 : (zPauli ![1, 1]).Z = 0 := h
    exact absurd (congrFun h0 0) (by decide)
  rw [pauliCondition_of_not_mem hQ, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Submodule.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  obtain ⟨haL, haO⟩ := Submodule.mem_inf.mp ha
  have hω : omega (zPauli ![1, 1]) a = 0 :=
    LinearMap.BilinForm.mem_orthogonal_iff.mp haO _ (Submodule.mem_span_singleton_self _)
  have haZ : a.Z = 0 := haL
  have ha' : a = paulix 1 + c • zPauli ![1, 1] := by
    rw [← hab, add_assoc, pauli_add_self, add_zero]
  subst ha'
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, add_zero] at hω
    unfold omega at hω
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at hω
    revert hω
    decide
  · rw [one_smul] at haZ
    exact absurd (congrFun haZ 0) (by decide)

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_add_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_add_right

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_smul_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_smul_right

/-- info: 'FTQCLib.Frame.Walkthrough.omega_eq_dotF2' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms omega_eq_dotF2

/-- info: 'FTQCLib.Frame.Walkthrough.add_self_word' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_self_word

/-- info: 'FTQCLib.Frame.Walkthrough.IsReader' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsReader

/-- info: 'FTQCLib.Frame.Walkthrough.exists_reader_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_reader_iff

/-- info: 'FTQCLib.Frame.Walkthrough.omega_reader' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms omega_reader

/-- info: 'FTQCLib.Frame.Walkthrough.reader_Z_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_Z_eq

/-- info: 'FTQCLib.Frame.Walkthrough.AlignedRotate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlignedRotate

/-- info: 'FTQCLib.Frame.Walkthrough.AlignedCollapse' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlignedCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.single_mem_of_alignedRotate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms single_mem_of_alignedRotate

/-- info: 'FTQCLib.Frame.Walkthrough.single_mem_of_alignedCollapse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms single_mem_of_alignedCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.xProj_pauliSwapOn_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xProj_pauliSwapOn_mem

/-- info: 'FTQCLib.Frame.Walkthrough.mem_xProj_map_pauliSwapOn_iff_of_alignedRotate' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_xProj_map_pauliSwapOn_iff_of_alignedRotate

/-- info: 'FTQCLib.Frame.Walkthrough.mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.map_xProj_map_of_X_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms map_xProj_map_of_X_eq

/-- info: 'FTQCLib.Frame.Walkthrough.map_xProj_map_zShearBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms map_xProj_map_zShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.map_xProj_map_zShear' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms map_xProj_map_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_map_zShear' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_map_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.alignedRotate_map_zShear_of_reader' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedRotate_map_zShear_of_reader

/-- info: 'FTQCLib.Frame.Walkthrough.alignedCollapse_map_zShear_of_reader' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedCollapse_map_zShear_of_reader

/-- info: 'FTQCLib.Frame.Walkthrough.exists_alignedRotate_map_zShear' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_alignedRotate_map_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.exists_alignedCollapse_map_zShear' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_alignedCollapse_map_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.orth_of_alignedCollapse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orth_of_alignedCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lagY' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lagY

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lagX1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.mem_graphL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lagXX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lagXX

/-- info: 'FTQCLib.Frame.Walkthrough.lagY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagY

/-- info: 'FTQCLib.Frame.Walkthrough.lagX1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.graphL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphL

/-- info: 'FTQCLib.Frame.Walkthrough.graphL_isStabilizer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graphL_isStabilizer

/-- info: 'FTQCLib.Frame.Walkthrough.lagXX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagXX

/-- info: 'FTQCLib.Frame.Walkthrough.alignedRotate_lagY' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedRotate_lagY

/-- info: 'FTQCLib.Frame.Walkthrough.shadow_swap_lagY' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadow_swap_lagY

/-- info: 'FTQCLib.Frame.Walkthrough.one_mem_shadow_swap_lagY' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_mem_shadow_swap_lagY

/-- info: 'FTQCLib.Frame.Walkthrough.not_alignedRotate_lagX1' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_alignedRotate_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.one_not_mem_shadow_swap_lagX1' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_not_mem_shadow_swap_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.alignedCollapse_graphL' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedCollapse_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.shadow_swap_graphL' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shadow_swap_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.eleven_mem_shadow_graphL' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eleven_mem_shadow_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.eleven_mem_shadow_swap_graphL' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eleven_mem_shadow_swap_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.eleven_mem_shadow_swap_graphL_witness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eleven_mem_shadow_swap_graphL_witness

/-- info: 'FTQCLib.Frame.Walkthrough.ten_not_mem_shadow_swap_graphL' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ten_not_mem_shadow_swap_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.not_alignedCollapse_lagXX' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_alignedCollapse_lagXX

/-- info: 'FTQCLib.Frame.Walkthrough.eleven_mem_cut_lagXX' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eleven_mem_cut_lagXX

/-- info: 'FTQCLib.Frame.Walkthrough.eleven_not_mem_shadow_swap_lagXX' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eleven_not_mem_shadow_swap_lagXX

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_lagX1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.alignedRotate_shear_lagX1' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedRotate_shear_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.shear_lagX1_reader' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shear_lagX1_reader

/-- info: 'FTQCLib.Frame.Walkthrough.zPauli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zPauli

/-- info: 'FTQCLib.Frame.Walkthrough.zPauli_X' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zPauli_X

/-- info: 'FTQCLib.Frame.Walkthrough.zPauli_Z' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zPauli_Z

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_comm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_comm

/-- info: 'FTQCLib.Frame.Walkthrough.omega_zPauli' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms omega_zPauli

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_singleton_eq_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_singleton_eq_self

/-- info: 'FTQCLib.Frame.Walkthrough.pauliSwapOn_reader_eq_zPauli' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSwapOn_reader_eq_zPauli

/-- info: 'FTQCLib.Frame.Walkthrough.map_pauliSwapOn_eq_pauliCondition' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms map_pauliSwapOn_eq_pauliCondition

/-- info: 'FTQCLib.Frame.Walkthrough.lagX1_isStabilizer' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagX1_isStabilizer

/-- info: 'FTQCLib.Frame.Walkthrough.alignedCollapse_lagX1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alignedCollapse_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.zPauli_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zPauli_one

/-- info: 'FTQCLib.Frame.Walkthrough.swap_lagX1_eq_pauliCondition' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms swap_lagX1_eq_pauliCondition

/-- info: 'FTQCLib.Frame.Walkthrough.pauliz_mem_swap_lagX1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliz_mem_swap_lagX1

/-- info: 'FTQCLib.Frame.Walkthrough.swap_graphL_eq_pauliCondition' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms swap_graphL_eq_pauliCondition

/-- info: 'FTQCLib.Frame.Walkthrough.zPauli_one_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zPauli_one_one

/-- info: 'FTQCLib.Frame.Walkthrough.zz_mem_swap_graphL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zz_mem_swap_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.xx_mem_pauliCondition_graphL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xx_mem_pauliCondition_graphL

/-- info: 'FTQCLib.Frame.Walkthrough.x1_mem_swap_lagXX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x1_mem_swap_lagXX

/-- info: 'FTQCLib.Frame.Walkthrough.x1_not_mem_pauliCondition_lagXX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x1_not_mem_pauliCondition_lagXX

end FTQCLib.Frame.Walkthrough

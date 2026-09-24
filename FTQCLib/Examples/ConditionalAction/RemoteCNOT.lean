/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.Inject

/-! # Remote CNOT through a Bell pair — the Heisenberg action verified

A non-local `CNOT(a→b)` realized by local CNOTs into a shared Bell pair, two measurements, and two
conditional Pauli actions (`X_b^x`, `Z_a^z`). This file verifies the gate's action on the data Paulis by
*support transport* — the Lagrangian flow, which is outcome-independent (the conditional actions touch
only signs). `CNOT(a→b)` sends `X_a ↦ X_aX_b`, `Z_b ↦ Z_aZ_b`, `Z_a ↦ Z_a`, `X_b ↦ X_b`; the two
non-trivial images are read off the `|+0⟩` run here.

Qubits: `a = 0` (control), `b = 1` (target), `A = 2` / `B = 3` (the Bell pair). Protocol:
`CNOT(a→A)` → measure `Z_A` → `CNOT(B→b)` → measure `X_B`. No error correction — the conditional
actions are conditional actions, not corrections. -/

namespace FTQCLib.RemoteCNOT

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Hilbert FTQCLib.Teleport FTQCLib.Inject FTQCLib.SInjection

/-- Generic Clifford support transport: if `g ∈ L` and the Clifford's symplectic image of `g` is `g'`,
then `g' ∈ (cliffordActionPure …).L`. -/
theorem cnot_image {m : ℕ} (i j : Fin m) (hij : i ≠ j) (S : PureSignedStab m) {g g' : Pauli m}
    (hg : g ∈ S.toSignedStab.L)
    (himg : (cliffordToSymplectic (isCliffordOperator_cnotGate i j hij)).toLinearMap g = g') :
    g' ∈ (injClifford (isCliffordOperator_cnotGate i j hij) S).toSignedStab.L := by
  rw [injClifford_L, ← himg]
  exact Submodule.mem_map_of_mem hg

/-! ## The `|+0⟩` input and the protocol -/

/-- `|+⟩_a |0⟩_b ⊗ |Φ⁺⟩_{AB}` stabilizers: `X_a, Z_b, X_AX_B, Z_AZ_B`. -/
noncomputable def Lin : Submodule (ZMod 2) (Pauli 4) :=
  Submodule.span (ZMod 2) {paulix 0, pauliz 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3}

theorem Lin_isStabilizer : IsStabilizer Lin :=
  isStabilizer_span_of_pairwise (by
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> decide)

theorem Lin_finrank : Module.finrank (ZMod 2) Lin = 4 := by
  have hli : LinearIndependent (ZMod 2)
      ![paulix 0, pauliz 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3] :=
    linearIndependent_of_omega_dual (n := 4) (k := 4)
      (v := ![paulix 0, pauliz 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3])
      (w := ![pauliz 0, paulix 1, pauliz 2, paulix 2]) (by decide)
  have hrange : ({paulix 0, pauliz 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3} : Set (Pauli 4))
      = Set.range ![paulix 0, pauliz 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩, ⟨3, by simp⟩]
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  have hspan : Lin = Submodule.span (ZMod 2)
      (Set.range ![paulix 0, pauliz 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3]) := by
    unfold Lin; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-- The input state. -/
noncomputable def inSt : PureSignedStab 4 := mkPureSlab Lin_isStabilizer Lin_finrank

/-- Witness: the CNOT(0→2) Clifford on the data. -/
noncomputable def cn1 : PureSignedStab 4 :=
  injClifford (isCliffordOperator_cnotGate 0 2 (by decide)) inSt

/-- The CNOT(3→1) Clifford, applied after the first measurement. -/
noncomputable def cnotB1 (S : PureSignedStab 4) : PureSignedStab 4 :=
  injClifford (isCliffordOperator_cnotGate 3 1 (by decide)) S

/-! ## Support transport through the protocol

We track the Lagrangian only (outcome-independent), so the conditioning outcome is fixed to `+1`. The
two CNOT images are computed by `decide` on the symplectic map. -/

-- Input generators (in `inSt.L = Lin`).
theorem X0_in : paulix 0 ∈ inSt.toSignedStab.L := Submodule.subset_span (by simp)
theorem Z1_in : pauliz 1 ∈ inSt.toSignedStab.L := Submodule.subset_span (by simp)
theorem XX_in : paulix 2 + paulix 3 ∈ inSt.toSignedStab.L := Submodule.subset_span (by simp)
theorem ZZ_in : pauliz 2 + pauliz 3 ∈ inSt.toSignedStab.L := Submodule.subset_span (by simp)

-- Their images in `cn1.L` (after `CNOT(0→2)`):  X₀↦X₀X₂, Z₁↦Z₁, X₂X₃↦X₂X₃, Z₂Z₃↦Z₀Z₂Z₃.
theorem X0X2_cn1 : paulix 0 + paulix 2 ∈ cn1.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt X0_in (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem XX_cn1 : paulix 2 + paulix 3 ∈ cn1.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt XX_in (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem Z1_cn1 : pauliz 1 ∈ cn1.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt Z1_in (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem ZZZ_cn1 : pauliz 0 + pauliz 2 + pauliz 3 ∈ cn1.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt ZZ_in (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)

/-- `X₀X₃ = X₀X₂ + X₂X₃` survives in `cn1.L`. -/
theorem X0X3_cn1 : paulix 0 + paulix 3 ∈ cn1.toSignedStab.L := by
  have h : (paulix 0 + paulix 3 : Pauli 4) = (paulix 0 + paulix 2) + (paulix 2 + paulix 3) := by decide
  rw [h]; exact add_mem X0X2_cn1 XX_cn1

theorem Z2_not_mem_cn1 : pauliz 2 ∉ cn1.toSignedStab.L := by
  intro h
  have h0 : omega (pauliz 2) (paulix 2 + paulix 3) = 0 := cn1.isStab _ h _ XX_cn1
  rw [show omega (pauliz 2) (paulix 2 + paulix 3) = 1 from by decide] at h0
  exact one_ne_zero h0

/-- After measuring `Z_A = Z₂` (outcome fixed to `+1`). -/
noncomputable def m1 : PureSignedStab 4 :=
  injStepWith cn1 Z2_not_mem_cn1 (by norm_num : (1 : ℂ) * 1 = 1) (paulix 2 + paulix 3) XX_cn1 (by decide)

theorem m1_L : m1.toSignedStab.L = pauliCondition cn1.toSignedStab.L (pauliz 2) := rfl

-- Survivors in `m1.L` (commute with Z₂).
theorem Z1_m1 : pauliz 1 ∈ m1.toSignedStab.L := by
  rw [m1_L]; exact mem_pauliCondition_of_commute Z2_not_mem_cn1 Z1_cn1 (by decide)
theorem ZZZ_m1 : pauliz 0 + pauliz 2 + pauliz 3 ∈ m1.toSignedStab.L := by
  rw [m1_L]; exact mem_pauliCondition_of_commute Z2_not_mem_cn1 ZZZ_cn1 (by decide)
theorem X0X3_m1 : paulix 0 + paulix 3 ∈ m1.toSignedStab.L := by
  rw [m1_L]; exact mem_pauliCondition_of_commute Z2_not_mem_cn1 X0X3_cn1 (by decide)
theorem Z2_m1 : pauliz 2 ∈ m1.toSignedStab.L := by
  rw [m1_L]; exact pauliCondition_mem _ _

/-- After `CNOT(3→1)`. -/
noncomputable def cn2 : PureSignedStab 4 := cnotB1 m1

-- Images in `cn2.L` (after `CNOT(3→1)`):  Z₁↦Z₁Z₃, Z₀Z₂Z₃↦Z₀Z₂Z₃, X₀X₃↦X₀X₃X₁, Z₂↦Z₂.
theorem Z1Z3_cn2 : pauliz 1 + pauliz 3 ∈ cn2.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1 Z1_m1 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem ZZZ_cn2 : pauliz 0 + pauliz 2 + pauliz 3 ∈ cn2.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1 ZZZ_m1 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem X0X3X1_cn2 : paulix 0 + paulix 3 + paulix 1 ∈ cn2.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1 X0X3_m1 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem Z2_cn2 : pauliz 2 ∈ cn2.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1 Z2_m1 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)

/-- `Z₀Z₁Z₂ = Z₁Z₃ + Z₀Z₂Z₃` survives in `cn2.L`. -/
theorem ZZZ012_cn2 : pauliz 0 + pauliz 1 + pauliz 2 ∈ cn2.toSignedStab.L := by
  have h : (pauliz 0 + pauliz 1 + pauliz 2 : Pauli 4)
      = (pauliz 1 + pauliz 3) + (pauliz 0 + pauliz 2 + pauliz 3) := by decide
  rw [h]; exact add_mem Z1Z3_cn2 ZZZ_cn2

theorem X3_not_mem_cn2 : paulix 3 ∉ cn2.toSignedStab.L := by
  intro h
  have h0 : omega (paulix 3) (pauliz 1 + pauliz 3) = 0 := cn2.isStab _ h _ Z1Z3_cn2
  rw [show omega (paulix 3) (pauliz 1 + pauliz 3) = 1 from by decide] at h0
  exact one_ne_zero h0

/-- After measuring `X_B = X₃` — the output state of the (support-level) remote CNOT. -/
noncomputable def outSt : PureSignedStab 4 :=
  injStepWith cn2 X3_not_mem_cn2 (by norm_num : (1 : ℂ) * 1 = 1) (pauliz 1 + pauliz 3) Z1Z3_cn2 (by decide)

theorem outSt_L : outSt.toSignedStab.L = pauliCondition cn2.toSignedStab.L (paulix 3) := rfl

/-- **`X_aX_b` stabilizes the output** — `X₀X₁ = X₀X₃X₁ + X₃`, the image of `X_a` under `CNOT(a→b)`. -/
theorem remoteCNOT_XaXb : paulix 0 + paulix 1 ∈ outSt.toSignedStab.L := by
  rw [outSt_L, show paulix 0 + paulix 1 = (paulix 0 + paulix 3 + paulix 1) + paulix 3 from by decide]
  exact add_mem
    (mem_pauliCondition_of_commute X3_not_mem_cn2 X0X3X1_cn2 (by decide))
    (pauliCondition_mem _ _)

/-- **`Z_aZ_b` stabilizes the output** — `Z₀Z₁ = Z₀Z₁Z₂ + Z₂`, the image of `Z_b` under `CNOT(a→b)`.
With `remoteCNOT_XaXb`, the data `(a,b)` comes out a Bell pair `= CNOT|+0⟩`. -/
theorem remoteCNOT_ZaZb : pauliz 0 + pauliz 1 ∈ outSt.toSignedStab.L := by
  rw [outSt_L, show pauliz 0 + pauliz 1 = (pauliz 0 + pauliz 1 + pauliz 2) + pauliz 2 from by decide]
  exact add_mem
    (mem_pauliCondition_of_commute X3_not_mem_cn2 ZZZ012_cn2 (by decide))
    (mem_pauliCondition_of_commute X3_not_mem_cn2 Z2_cn2 (by decide))

/-! ## The `|0+⟩` run — the two fixed generators `Z_a ↦ Z_a`, `X_b ↦ X_b`

Same protocol on `|0⟩_a |+⟩_b ⊗ |Φ⁺⟩_{AB}` (stabilizers `Z_a, X_b, X_AX_B, Z_AZ_B`). `Z_a = Z₀` and
`X_b = X₁` ride through the protocol untouched and land directly in the output Lagrangian. -/

noncomputable def Lin2 : Submodule (ZMod 2) (Pauli 4) :=
  Submodule.span (ZMod 2) {pauliz 0, paulix 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3}

theorem Lin2_isStabilizer : IsStabilizer Lin2 :=
  isStabilizer_span_of_pairwise (by
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> decide)

theorem Lin2_finrank : Module.finrank (ZMod 2) Lin2 = 4 := by
  have hli : LinearIndependent (ZMod 2)
      ![pauliz 0, paulix 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3] :=
    linearIndependent_of_omega_dual (n := 4) (k := 4)
      (v := ![pauliz 0, paulix 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3])
      (w := ![paulix 0, pauliz 1, pauliz 2, paulix 2]) (by decide)
  have hrange : ({pauliz 0, paulix 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3} : Set (Pauli 4))
      = Set.range ![pauliz 0, paulix 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩, ⟨3, by simp⟩]
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  have hspan : Lin2 = Submodule.span (ZMod 2)
      (Set.range ![pauliz 0, paulix 1, paulix 2 + paulix 3, pauliz 2 + pauliz 3]) := by
    unfold Lin2; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

noncomputable def inSt2 : PureSignedStab 4 := mkPureSlab Lin2_isStabilizer Lin2_finrank

theorem Z0_in2 : pauliz 0 ∈ inSt2.toSignedStab.L := Submodule.subset_span (by simp)
theorem X1_in2 : paulix 1 ∈ inSt2.toSignedStab.L := Submodule.subset_span (by simp)
theorem XX_in2 : paulix 2 + paulix 3 ∈ inSt2.toSignedStab.L := Submodule.subset_span (by simp)
theorem ZZ_in2 : pauliz 2 + pauliz 3 ∈ inSt2.toSignedStab.L := Submodule.subset_span (by simp)

noncomputable def cn1b : PureSignedStab 4 :=
  injClifford (isCliffordOperator_cnotGate 0 2 (by decide)) inSt2

theorem Z0_cn1b : pauliz 0 ∈ cn1b.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt2 Z0_in2 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem X1_cn1b : paulix 1 ∈ cn1b.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt2 X1_in2 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem XX_cn1b : paulix 2 + paulix 3 ∈ cn1b.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt2 XX_in2 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem ZZZ_cn1b : pauliz 0 + pauliz 2 + pauliz 3 ∈ cn1b.toSignedStab.L :=
  cnot_image 0 2 (by decide) inSt2 ZZ_in2 (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)

theorem Z2_not_mem_cn1b : pauliz 2 ∉ cn1b.toSignedStab.L := by
  intro h
  have h0 : omega (pauliz 2) (paulix 2 + paulix 3) = 0 := cn1b.isStab _ h _ XX_cn1b
  rw [show omega (pauliz 2) (paulix 2 + paulix 3) = 1 from by decide] at h0
  exact one_ne_zero h0

noncomputable def m1b : PureSignedStab 4 :=
  injStepWith cn1b Z2_not_mem_cn1b (by norm_num : (1 : ℂ) * 1 = 1) (paulix 2 + paulix 3) XX_cn1b
    (by decide)

theorem m1b_L : m1b.toSignedStab.L = pauliCondition cn1b.toSignedStab.L (pauliz 2) := rfl

theorem Z0_m1b : pauliz 0 ∈ m1b.toSignedStab.L := by
  rw [m1b_L]; exact mem_pauliCondition_of_commute Z2_not_mem_cn1b Z0_cn1b (by decide)
theorem X1_m1b : paulix 1 ∈ m1b.toSignedStab.L := by
  rw [m1b_L]; exact mem_pauliCondition_of_commute Z2_not_mem_cn1b X1_cn1b (by decide)
theorem ZZZ_m1b : pauliz 0 + pauliz 2 + pauliz 3 ∈ m1b.toSignedStab.L := by
  rw [m1b_L]; exact mem_pauliCondition_of_commute Z2_not_mem_cn1b ZZZ_cn1b (by decide)

noncomputable def cn2b : PureSignedStab 4 := cnotB1 m1b

theorem Z0_cn2b : pauliz 0 ∈ cn2b.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1b Z0_m1b (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem X1_cn2b : paulix 1 ∈ cn2b.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1b X1_m1b (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
theorem ZZZ_cn2b : pauliz 0 + pauliz 2 + pauliz 3 ∈ cn2b.toSignedStab.L :=
  cnot_image 3 1 (by decide) m1b ZZZ_m1b (by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)

theorem X3_not_mem_cn2b : paulix 3 ∉ cn2b.toSignedStab.L := by
  intro h
  have h0 : omega (paulix 3) (pauliz 0 + pauliz 2 + pauliz 3) = 0 := cn2b.isStab _ h _ ZZZ_cn2b
  rw [show omega (paulix 3) (pauliz 0 + pauliz 2 + pauliz 3) = 1 from by decide] at h0
  exact one_ne_zero h0

noncomputable def outSt2 : PureSignedStab 4 :=
  injStepWith cn2b X3_not_mem_cn2b (by norm_num : (1 : ℂ) * 1 = 1) (pauliz 0 + pauliz 2 + pauliz 3)
    ZZZ_cn2b (by decide)

theorem outSt2_L : outSt2.toSignedStab.L = pauliCondition cn2b.toSignedStab.L (paulix 3) := rfl

/-- **`Z_a` stabilizes the output unchanged** — `Z₀ ∈ L_out`  (`Z_a ↦ Z_a` under `CNOT(a→b)`). -/
theorem remoteCNOT_Za : pauliz 0 ∈ outSt2.toSignedStab.L := by
  rw [outSt2_L]; exact mem_pauliCondition_of_commute X3_not_mem_cn2b Z0_cn2b (by decide)

/-- **`X_b` stabilizes the output unchanged** — `X₁ ∈ L_out`  (`X_b ↦ X_b` under `CNOT(a→b)`). With
`remoteCNOT_XaXb`/`_ZaZb`, all four data generators transform exactly as `CNOT(a→b)`. -/
theorem remoteCNOT_Xb : paulix 1 ∈ outSt2.toSignedStab.L := by
  rw [outSt2_L]; exact mem_pauliCondition_of_commute X3_not_mem_cn2b X1_cn2b (by decide)

/-! ## The conditional-action sign engine

The corrections `X_B^x`, `Z_a^z` are conditional Pauli *actions* that adjust the output *signs* (the
feed-forward), not the Lagrangian. The mechanism is the selective sign flip: the conditional action
`Z_a` flips the sign of `X_aX_b` (they anticommute) and leaves `Z_aZ_b` alone (they commute). So `Z_a^z`
retargets exactly the generator whose sign carries the `z`-outcome, which is what makes the corrected
output outcome-independent. (Shown on the `|+0⟩` output; the same `cliffordAction_pauliEquiv_sign`
mechanism drives the full feed-forward.) -/

/-- The conditional action `Z_a` flips the sign of `X_aX_b` (`ω(Z_a, X_aX_b) = 1`). -/
theorem Za_flips_XaXb :
    (cliffordActionPure (isCliffordOperator_pauliEquiv (pauliz 0)) outSt).toSignedStab.sign
        (paulix 0 + paulix 1)
      = - outSt.toSignedStab.sign (paulix 0 + paulix 1) := by
  rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_sign,
      show (omega (pauliz 0) (paulix 0 + paulix 1)).val = 1 from by decide]
  ring

/-- The conditional action `Z_a` leaves the sign of `Z_aZ_b` unchanged (`ω(Z_a, Z_aZ_b) = 0`). -/
theorem Za_fixes_ZaZb :
    (cliffordActionPure (isCliffordOperator_pauliEquiv (pauliz 0)) outSt).toSignedStab.sign
        (pauliz 0 + pauliz 1)
      = outSt.toSignedStab.sign (pauliz 0 + pauliz 1) := by
  rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_sign,
      show (omega (pauliz 0) (pauliz 0 + pauliz 1)).val = 0 from by decide]
  ring

/-! ## Feed-forward: the conditional `Z_a` correction makes `X_aX_b`'s sign outcome-independent

We now run the protocol with the *outcomes free*. Each measurement's outcome `ε` satisfies `ε² = 1`, so
`ε = ±1`; the Lagrangian is outcome-blind (which is why the support transport above could fix `ε = 1`), so
the outcome lives entirely in the signs. The output sign on `X_aX_b = X₀X₁` carries a clean factor of the
*second* outcome `ε₂`: the measured generator `X₃` sits on the `ε₂`-coset (`injStepWith_sign_of_one`), the
surviving `X₀X₃X₁` is outcome-blind (`injStepWith_sign_of_zero`), and the `valid` cocycle law multiplies
them (`outSt'_sign_XaXb_ratio`). The conditional action `Z_a = Z₀` flips exactly that sign
(`Za_flips_XaXb`), so applying it precisely when `ε₂ = -1` cancels the factor: the corrected output sign
equals the canonical `ε₂ = 1` value for *both* outcomes (`remoteCNOT_XaXb_feedforward`). The first outcome
`ε₁` is left free throughout — the result holds whatever was measured first. -/

/-- The protocol's first measurement, first outcome `ε₁` free. -/
noncomputable def m1' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) : PureSignedStab 4 :=
  injStepWith cn1 Z2_not_mem_cn1 hε₁ (paulix 2 + paulix 3) XX_cn1 (by decide)

/-- After `CNOT(3→1)`, first outcome free. -/
noncomputable def cn2' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) : PureSignedStab 4 := cnotB1 (m1' ε₁ hε₁)

-- The Lagrangian is outcome-blind, so the membership facts transfer from the `ε = 1` run by defeq.
theorem X3_not_mem_cn2' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) :
    paulix 3 ∉ (cn2' ε₁ hε₁).toSignedStab.L := X3_not_mem_cn2
theorem Z1Z3_cn2' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) :
    pauliz 1 + pauliz 3 ∈ (cn2' ε₁ hε₁).toSignedStab.L := Z1Z3_cn2
theorem X0X3X1_cn2' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) :
    paulix 0 + paulix 3 + paulix 1 ∈ (cn2' ε₁ hε₁).toSignedStab.L := X0X3X1_cn2

/-- The protocol output with *both* outcomes free. -/
noncomputable def outSt' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    PureSignedStab 4 :=
  injStepWith (cn2' ε₁ hε₁) (X3_not_mem_cn2' ε₁ hε₁) hε₂ (pauliz 1 + pauliz 3)
    (Z1Z3_cn2' ε₁ hε₁) (by decide)

/-- **`X_aX_b`'s output sign carries a clean factor of the second outcome `ε₂`.** -/
theorem outSt'_sign_XaXb_ratio (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (outSt' ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (paulix 0 + paulix 1)
      = ε₂ * (outSt' ε₁ hε₁ 1 (one_mul 1)).toSignedStab.sign (paulix 0 + paulix 1) := by
  -- The measured generator X₃ is on the ε-coset (ω(Z₁Z₃, X₃) = 1).
  have hX3 : ∀ (e : ℂ) (he : e * e = 1),
      (outSt' ε₁ hε₁ e he).toSignedStab.sign (paulix 3)
        = e * (cn2' ε₁ hε₁).toSignedStab.sign (paulix 3 + paulix 3)
            * pauliPhase (paulix 3) (paulix 3 + paulix 3) := fun e he =>
    injStepWith_sign_of_one (cn2' ε₁ hε₁) (X3_not_mem_cn2' ε₁ hε₁) he
      (pauliz 1 + pauliz 3) (Z1Z3_cn2' ε₁ hε₁) (by decide) (pauliCondition_mem _ _) (by decide)
  -- The survivor X₀X₃X₁ is outcome-blind (ω(Z₁Z₃, X₀X₃X₁) = 0).
  have hXXX : ∀ (e : ℂ) (he : e * e = 1),
      (outSt' ε₁ hε₁ e he).toSignedStab.sign (paulix 0 + paulix 3 + paulix 1)
        = (cn2' ε₁ hε₁).toSignedStab.sign (paulix 0 + paulix 3 + paulix 1) := fun e he =>
    injStepWith_sign_of_zero (cn2' ε₁ hε₁) (X3_not_mem_cn2' ε₁ hε₁) he
      (pauliz 1 + pauliz 3) (Z1Z3_cn2' ε₁ hε₁) (by decide)
      (mem_pauliCondition_of_commute (X3_not_mem_cn2' ε₁ hε₁) (X0X3X1_cn2' ε₁ hε₁) (by decide))
      (by decide)
  -- The cocycle law: sign(X₀X₁) = sign(X₃)·sign(X₀X₃X₁)·pauliPhase, for each outcome.
  have hvalid : ∀ (e : ℂ) (he : e * e = 1),
      (outSt' ε₁ hε₁ e he).toSignedStab.sign (paulix 3)
          * (outSt' ε₁ hε₁ e he).toSignedStab.sign (paulix 0 + paulix 3 + paulix 1)
          * pauliPhase (paulix 0 + paulix 3 + paulix 1 : Pauli 4) (paulix 3)
        = (outSt' ε₁ hε₁ e he).toSignedStab.sign (paulix 0 + paulix 1) := by
    intro e he
    have hmemA : (paulix 0 + paulix 3 + paulix 1) ∈ (outSt' ε₁ hε₁ e he).toSignedStab.L :=
      mem_pauliCondition_of_commute (X3_not_mem_cn2' ε₁ hε₁) (X0X3X1_cn2' ε₁ hε₁) (by decide)
    have hmemB : paulix 3 ∈ (outSt' ε₁ hε₁ e he).toSignedStab.L := pauliCondition_mem _ _
    have hv := (outSt' ε₁ hε₁ e he).toSignedStab.valid _ hmemA _ hmemB
    rwa [show (paulix 0 + paulix 3 + paulix 1) + paulix 3 = paulix 0 + paulix 1 from by decide] at hv
  rw [← hvalid ε₂ hε₂, ← hvalid 1 (one_mul 1), hX3 ε₂ hε₂, hX3 1 (one_mul 1),
    hXXX ε₂ hε₂, hXXX 1 (one_mul 1)]
  ring

/-- The conditional action `Z_a` flips `X_aX_b`'s sign, for any outcomes (`ω(Z_a, X_aX_b) = 1`). -/
theorem Za_flips_XaXb' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (cliffordActionPure (isCliffordOperator_pauliEquiv (pauliz 0))
          (outSt' ε₁ hε₁ ε₂ hε₂)).toSignedStab.sign (paulix 0 + paulix 1)
      = - (outSt' ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (paulix 0 + paulix 1) := by
  rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_sign,
      show (omega (pauliz 0) (paulix 0 + paulix 1)).val = 1 from by decide]
  ring

open Classical in
/-- The output with the conditional `Z_a = Z₀` action applied exactly when `ε₂ = -1`. -/
noncomputable def correctedXaXb (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    PureSignedStab 4 :=
  if ε₂ = 1 then outSt' ε₁ hε₁ ε₂ hε₂
  else cliffordActionPure (isCliffordOperator_pauliEquiv (pauliz 0)) (outSt' ε₁ hε₁ ε₂ hε₂)

/-- **Feed-forward determinism for `X_aX_b`.** Whatever the second outcome `ε₂ = ±1`, the conditional
`Z_a` action lands the output sign on `X_aX_b` at its canonical `ε₂ = 1` value: the gate is deterministic
in the measured outcome. (`ε₁` is free — it holds for either first outcome too.) This is the feed-forward
closing the loop: the `Z_a^{ε₂}` action exactly cancels the outcome the measurement wrote into the sign. -/
theorem remoteCNOT_XaXb_feedforward (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (correctedXaXb ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (paulix 0 + paulix 1)
      = (outSt' ε₁ hε₁ 1 (one_mul 1)).toSignedStab.sign (paulix 0 + paulix 1) := by
  unfold correctedXaXb
  rcases mul_self_eq_one_iff.mp hε₂ with h | h
  · subst h; rw [if_pos rfl]
  · subst h
    rw [if_neg (by norm_num : (-1 : ℂ) ≠ 1), Za_flips_XaXb' ε₁ hε₁ (-1) hε₂,
      outSt'_sign_XaXb_ratio ε₁ hε₁ (-1) hε₂]
    ring

/-! ## Feed-forward: the symmetric `X_b` correction for `Z_aZ_b`

The mirror image. `Z_aZ_b = Z₀Z₁` carries a factor of the *first* outcome `ε₁`, which entered two steps
earlier — measuring `Z_A = Z₂`. The output sign on `Z₂` traces back through the second measurement
(outcome-blind, `injStepWith_sign_of_zero`), the `CNOT(3→1)` (the sign-transport `cliffordAction_sign`,
which `Z₂` is fixed by), and the first measurement (`injStepWith_sign_of_one`, where the `ε₁` enters). The
survivor `Z₀Z₁Z₂` is outcome-blind, so the `valid` cocycle leaves `Z_aZ_b`'s sign with a clean factor of
`ε₁` (`outSt'_sign_ZaZb_ratio`). The conditional action `X_b = X₁` flips it (`Xb_flips_ZaZb`), cancelling
the factor — the `ε₂` is left free here, mirror to `ε₁` in the `X_aX_b` half. -/

/-- `Z₀Z₁Z₂Z₃ ∈ cn1.L`  (`= Z₁ + Z₀Z₂Z₃`). -/
theorem ZZZZ_cn1 : pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3 ∈ cn1.toSignedStab.L := by
  rw [show (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3 : Pauli 4)
      = pauliz 1 + (pauliz 0 + pauliz 2 + pauliz 3) from by decide]
  exact add_mem Z1_cn1 ZZZ_cn1

theorem Z2_cn2' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) : pauliz 2 ∈ (cn2' ε₁ hε₁).toSignedStab.L := Z2_cn2
theorem ZZZ012_cn2' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) :
    pauliz 0 + pauliz 1 + pauliz 2 ∈ (cn2' ε₁ hε₁).toSignedStab.L := ZZZ012_cn2

/-- **CNOT sign-transport for `cn2'`.** Using the *forward* symplectic image `Φ g = p` kills the `.symm`
(`Φ⁻¹∘Φ = id`): the sign at `p` is `cliffordSign(g)` times the pre-`CNOT` sign at `g`. -/
theorem cn2'_sign_of_image (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) {g p : Pauli 4}
    (hgp : (cliffordToSymplectic (isCliffordOperator_cnotGate 3 1 (by decide))).toLinearMap g = p) :
    (cn2' ε₁ hε₁).toSignedStab.sign p
      = cliffordSign (isCliffordOperator_cnotGate (3 : Fin 4) 1 (by decide)) g
        * (m1' ε₁ hε₁).toSignedStab.sign g := by
  unfold cn2' cnotB1 injClifford
  rw [cliffordActionPure_toSignedStab, cliffordAction_sign,
    show (cliffordToSymplectic (isCliffordOperator_cnotGate 3 1 (by decide))).symm p = g from by
      rw [← hgp, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]]

/-- **`Z_aZ_b`'s output sign carries a clean factor of the first outcome `ε₁`.** -/
theorem outSt'_sign_ZaZb_ratio (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (outSt' ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1)
      = ε₁ * (outSt' 1 (one_mul 1) ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1) := by
  -- Z₂: outcome-blind 2nd measurement → CNOT bridge (Φ fixes Z₂) → ε₁-coset 1st measurement.
  have hZ2 : ∀ (e : ℂ) (he : e * e = 1),
      (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 2)
        = cliffordSign (isCliffordOperator_cnotGate (3 : Fin 4) 1 (by decide)) (pauliz 2)
          * (e * cn1.toSignedStab.sign (pauliz 2 + pauliz 2)
              * pauliPhase (pauliz 2 : Pauli 4) (pauliz 2 + pauliz 2)) := by
    intro e he
    have h1 : (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 2)
        = (cn2' e he).toSignedStab.sign (pauliz 2) :=
      injStepWith_sign_of_zero (cn2' e he) (X3_not_mem_cn2' e he) hε₂ (pauliz 1 + pauliz 3)
        (Z1Z3_cn2' e he) (by decide)
        (mem_pauliCondition_of_commute (X3_not_mem_cn2' e he) (Z2_cn2' e he) (by decide)) (by decide)
    have h2 : (cn2' e he).toSignedStab.sign (pauliz 2)
        = cliffordSign (isCliffordOperator_cnotGate (3 : Fin 4) 1 (by decide)) (pauliz 2)
          * (m1' e he).toSignedStab.sign (pauliz 2) :=
      cn2'_sign_of_image e he (by
        simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
          cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
    have h3 : (m1' e he).toSignedStab.sign (pauliz 2)
        = e * cn1.toSignedStab.sign (pauliz 2 + pauliz 2)
            * pauliPhase (pauliz 2 : Pauli 4) (pauliz 2 + pauliz 2) :=
      injStepWith_sign_of_one cn1 Z2_not_mem_cn1 he (paulix 2 + paulix 3) XX_cn1 (by decide)
        (pauliCondition_mem _ _) (by decide)
    rw [h1, h2, h3]
  -- Z₀Z₁Z₂: outcome-blind at both measurements (its CNOT preimage is Z₀Z₁Z₂Z₃).
  have hZZZ : ∀ (e : ℂ) (he : e * e = 1),
      (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2)
        = cliffordSign (isCliffordOperator_cnotGate (3 : Fin 4) 1 (by decide))
              (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3)
          * cn1.toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3) := by
    intro e he
    have h1 : (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2)
        = (cn2' e he).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2) :=
      injStepWith_sign_of_zero (cn2' e he) (X3_not_mem_cn2' e he) hε₂ (pauliz 1 + pauliz 3)
        (Z1Z3_cn2' e he) (by decide)
        (mem_pauliCondition_of_commute (X3_not_mem_cn2' e he) (ZZZ012_cn2' e he) (by decide)) (by decide)
    have h2 : (cn2' e he).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2)
        = cliffordSign (isCliffordOperator_cnotGate (3 : Fin 4) 1 (by decide))
              (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3)
          * (m1' e he).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3) :=
      cn2'_sign_of_image e he (by
        simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
          cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]; decide)
    have h3 : (m1' e he).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3)
        = cn1.toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3) :=
      injStepWith_sign_of_zero cn1 Z2_not_mem_cn1 he (paulix 2 + paulix 3) XX_cn1 (by decide)
        (mem_pauliCondition_of_commute Z2_not_mem_cn1 ZZZZ_cn1 (by decide)) (by decide)
    rw [h1, h2, h3]
  -- cocycle law: sign(Z₀Z₁) = sign(Z₂)·sign(Z₀Z₁Z₂)·pauliPhase.
  have hvalid : ∀ (e : ℂ) (he : e * e = 1),
      (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 2)
          * (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1 + pauliz 2)
          * pauliPhase (pauliz 0 + pauliz 1 + pauliz 2 : Pauli 4) (pauliz 2)
        = (outSt' e he ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1) := by
    intro e he
    have hmemA : (pauliz 0 + pauliz 1 + pauliz 2) ∈ (outSt' e he ε₂ hε₂).toSignedStab.L :=
      mem_pauliCondition_of_commute (X3_not_mem_cn2' e he) (ZZZ012_cn2' e he) (by decide)
    have hmemB : pauliz 2 ∈ (outSt' e he ε₂ hε₂).toSignedStab.L :=
      mem_pauliCondition_of_commute (X3_not_mem_cn2' e he) (Z2_cn2' e he) (by decide)
    have hv := (outSt' e he ε₂ hε₂).toSignedStab.valid _ hmemA _ hmemB
    rwa [show (pauliz 0 + pauliz 1 + pauliz 2) + pauliz 2 = (pauliz 0 + pauliz 1 : Pauli 4)
        from by decide] at hv
  rw [← hvalid ε₁ hε₁, ← hvalid 1 (one_mul 1), hZ2 ε₁ hε₁, hZ2 1 (one_mul 1),
    hZZZ ε₁ hε₁, hZZZ 1 (one_mul 1)]
  ring

/-- The conditional action `X_b` flips `Z_aZ_b`'s sign, for any outcomes (`ω(X_b, Z_aZ_b) = 1`). -/
theorem Xb_flips_ZaZb' (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (cliffordActionPure (isCliffordOperator_pauliEquiv (paulix 1))
          (outSt' ε₁ hε₁ ε₂ hε₂)).toSignedStab.sign (pauliz 0 + pauliz 1)
      = - (outSt' ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1) := by
  rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_sign,
      show (omega (paulix 1) (pauliz 0 + pauliz 1)).val = 1 from by decide]
  ring

open Classical in
/-- The output with the conditional `X_b = X₁` action applied exactly when `ε₁ = -1`. -/
noncomputable def correctedZaZb (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    PureSignedStab 4 :=
  if ε₁ = 1 then outSt' ε₁ hε₁ ε₂ hε₂
  else cliffordActionPure (isCliffordOperator_pauliEquiv (paulix 1)) (outSt' ε₁ hε₁ ε₂ hε₂)

/-- **Feed-forward determinism for `Z_aZ_b`.** Whatever the first outcome `ε₁ = ±1`, the conditional
`X_b` action lands the output sign on `Z_aZ_b` at its canonical `ε₁ = 1` value. Together with
`remoteCNOT_XaXb_feedforward`, *both* data generators are pinned to their canonical signs for every pair
of outcomes — the remote CNOT is a deterministic gate, not a random process. -/
theorem remoteCNOT_ZaZb_feedforward (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (correctedZaZb ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1)
      = (outSt' 1 (one_mul 1) ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1) := by
  unfold correctedZaZb
  rcases mul_self_eq_one_iff.mp hε₁ with h | h
  · subst h; rw [if_pos rfl]
  · subst h
    rw [if_neg (by norm_num : (-1 : ℂ) ≠ 1), Xb_flips_ZaZb' (-1) hε₁ ε₂ hε₂,
      outSt'_sign_ZaZb_ratio (-1) hε₁ ε₂ hε₂]
    ring

/-! ## The reusable feed-forward core

Both `remoteCNOT_XaXb_feedforward` and `remoteCNOT_ZaZb_feedforward` are instances of a single fact, with
no remote CNOT, no Bell pair, no codes in sight: if a measurement writes its outcome `ε` into a
generator `g`'s sign as a free factor, then a conditional Pauli action `C` that anticommutes with `g`
(`ω(C,g)=1`), applied exactly when `ε = -1`, cancels it — the corrected sign is outcome-independent. Only
the outcome-as-a-factor (`hratio`) and the anticommutation (`hCg`) are used; the protocol, the cocycle
values, the `cliffordSign` never appear. The concrete theorems above are kept as the explicit worked
instances; the `example`s below re-derive them from this core, confirming it is genuinely general (the two
fix opposite outcomes — `ε₁` vs `ε₂` — and curry the run differently). -/

open Classical in
/-- A Pauli action `C` gated on an outcome `ε ∈ {±1}`: applied exactly when `ε = -1`. -/
noncomputable def condAction {n : ℕ} (C : Pauli n) (ε : ℂ) (S : PureSignedStab n) : PureSignedStab n :=
  if ε = 1 then S else cliffordActionPure (isCliffordOperator_pauliEquiv C) S

/-- **The feed-forward core.** If the outcome `ε` enters `g`'s sign as a free factor (`hratio`) and the
correction `C` anticommutes with `g` (`hCg`), then the conditionally-corrected sign is
outcome-independent: equal to the canonical `ε = 1` value for every `ε = ±1`. This is what "the gate is
deterministic in the measured outcome" means, stripped of the example. -/
theorem condAction_feedforward {n : ℕ} (C : Pauli n)
    (St : (ε : ℂ) → ε * ε = 1 → PureSignedStab n) (g : Pauli n) (hCg : omega C g = 1)
    (hratio : ∀ (ε : ℂ) (hε : ε * ε = 1),
      (St ε hε).toSignedStab.sign g = ε * (St 1 (one_mul 1)).toSignedStab.sign g)
    (ε : ℂ) (hε : ε * ε = 1) :
    (condAction C ε (St ε hε)).toSignedStab.sign g = (St 1 (one_mul 1)).toSignedStab.sign g := by
  unfold condAction
  rcases mul_self_eq_one_iff.mp hε with h | h
  · subst h; rw [if_pos rfl]
  · subst h
    rw [if_neg (by norm_num : (-1 : ℂ) ≠ 1), cliffordActionPure_toSignedStab,
      cliffordAction_pauliEquiv_sign, show (omega C g).val = 1 from by rw [hCg]; rfl, hratio (-1) hε]
    ring

/-- `remoteCNOT_XaXb_feedforward` is the `g = X₀X₁`, `C = Z₀`, vary-`ε₂` instance of the core. -/
example (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (correctedXaXb ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (paulix 0 + paulix 1)
      = (outSt' ε₁ hε₁ 1 (one_mul 1)).toSignedStab.sign (paulix 0 + paulix 1) :=
  condAction_feedforward (pauliz 0) (fun e he => outSt' ε₁ hε₁ e he) (paulix 0 + paulix 1)
    (by decide) (outSt'_sign_XaXb_ratio ε₁ hε₁) ε₂ hε₂

/-- `remoteCNOT_ZaZb_feedforward` is the `g = Z₀Z₁`, `C = X₁`, vary-`ε₁` instance of the core. -/
example (ε₁ : ℂ) (hε₁ : ε₁ * ε₁ = 1) (ε₂ : ℂ) (hε₂ : ε₂ * ε₂ = 1) :
    (correctedZaZb ε₁ hε₁ ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1)
      = (outSt' 1 (one_mul 1) ε₂ hε₂).toSignedStab.sign (pauliz 0 + pauliz 1) :=
  condAction_feedforward (paulix 1) (fun e he => outSt' e he ε₂ hε₂) (pauliz 0 + pauliz 1)
    (by decide) (fun e he => outSt'_sign_ZaZb_ratio e he ε₂ hε₂) ε₁ hε₁

end FTQCLib.RemoteCNOT

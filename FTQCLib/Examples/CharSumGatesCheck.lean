/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CharSumGates

/-!
# Check: the frame-pure carrier operations

Axiom rows for every declaration of `CharSumGates`, and the rows that pin the
symplectic CNOT lift: the naive lift `cnotPauliOld` (the same `cnotBitMap i j` on both blocks) is
not symplectic — on the pair `Z₀, X₁` it turns a vanishing form into `1` — while
`cnotPauli` (`cnotBitMap i j` on X, `cnotBitMap j i` on Z) preserves it there; and `cnotPauli`
acts on the generators as the CNOT conjugation table `X₀ ↦ X₀X₁`, `X₁ ↦ X₁`, `Z₀ ↦ Z₀`,
`Z₁ ↦ Z₀Z₁`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase

/-! ## The naive lift, as the discriminating row -/

/-- The naive lift: `cnotBitMap i j` on both blocks. -/
noncomputable def cnotPauliOld {n : ℕ} (i j : Fin n) : Pauli n →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨cnotBitMap i j p.X, cnotBitMap i j p.Z⟩
  map_add' p q := by apply Pauli.ext <;> simp only [X_add, Z_add, cnotBitMap_add]
  map_smul' c p := by
    apply Pauli.ext <;> simp only [X_smul, Z_smul, cnotBitMap_smul, RingHom.id_apply]

/-- **Discriminating.** The naive lift is not symplectic: on `Z₀, X₁` (form `0`) it gives `1`. -/
theorem cnotPauliOld_not_symplectic :
    omega (cnotPauliOld (0 : Fin 2) 1 (pauliz 0)) (cnotPauliOld (0 : Fin 2) 1 (paulix 1)) = 1 ∧
      omega (pauliz (0 : Fin 2)) (paulix 1) = 0 := by
  decide

/-- `cnotPauli` preserves the form on the same pair. -/
theorem cnotPauli_symplectic_pair :
    omega (cnotPauli (0 : Fin 2) 1 (pauliz 0)) (cnotPauli (0 : Fin 2) 1 (paulix 1)) =
      omega (pauliz (0 : Fin 2)) (paulix 1) := by
  decide

/-! ## The conjugation table -/

/-- `X₀ ↦ X₀X₁`. -/
theorem cnotPauli_paulix_control : cnotPauli (0 : Fin 2) 1 (paulix 0) = paulix 0 + paulix 1 := by
  ext i <;> fin_cases i <;> decide

/-- `X₁ ↦ X₁`. -/
theorem cnotPauli_paulix_target : cnotPauli (0 : Fin 2) 1 (paulix 1) = paulix 1 := by
  ext i <;> fin_cases i <;> decide

/-- `Z₀ ↦ Z₀`. -/
theorem cnotPauli_pauliz_control : cnotPauli (0 : Fin 2) 1 (pauliz 0) = pauliz 0 := by
  ext i <;> fin_cases i <;> decide

/-- `Z₁ ↦ Z₀Z₁`. -/
theorem cnotPauli_pauliz_target : cnotPauli (0 : Fin 2) 1 (pauliz 1) = pauliz 0 + pauliz 1 := by
  ext i <;> fin_cases i <;> decide

/-- The naive lift sends `Z₀` to `Z₀Z₁` instead. -/
theorem cnotPauliOld_pauliz_control :
    cnotPauliOld (0 : Fin 2) 1 (pauliz 0) = pauliz 0 + pauliz 1 := by
  ext i <;> fin_cases i <;> decide

/-- The bit map on a word. -/
theorem cnotBitMap_word : cnotBitMap (0 : Fin 2) 1 ![1, 0] = ![1, 1] := by
  decide

/-- The bit map as an addition, on a word. -/
theorem cnotBitMap_eq_add_word :
    cnotBitMap (0 : Fin 2) 1 ![1, 0] =
      ![1, 0] + ((![1, 0] : Fin 2 → ZMod 2) 0) • (Pi.single 1 1 : Fin 2 → ZMod 2) :=
  cnotBitMap_eq_add_smul_single 0 1 _

/-- The involution on a word (`i ≠ j`). -/
theorem cnotBitMap_involutive_word : cnotBitMap (0 : Fin 2) 1 (cnotBitMap 0 1 ![1, 1]) = ![1, 1] :=
  cnotBitMap_involutive 0 1 (by decide) _

/-- The involution of the lift on `Y₀`. -/
theorem cnotPauli_cnotPauli_word :
    cnotPauli (0 : Fin 2) 1 (cnotPauli 0 1 (paulix 0 + pauliz 0)) = paulix 0 + pauliz 0 :=
  cnotPauli_cnotPauli 0 1 (by decide) _

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Frame.Walkthrough.ofKernelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofKernelState

/-- info: 'FTQCLib.Frame.Walkthrough.append_fin0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms append_fin0

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_zero

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagSum

/-- info: 'FTQCLib.Frame.Walkthrough.eval_rename_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_rename_castAdd

/-- info: 'FTQCLib.Frame.Walkthrough.realPhase_rename_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realPhase_rename_castAdd

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_add

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_smul

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_involutive

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_eq_add_smul_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_eq_add_smul_single

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_X

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_Z

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_cnotPauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauliEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauliEquiv

/-- info: 'FTQCLib.Frame.Walkthrough.finrank_map_cnotPauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finrank_map_cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.applyCnotSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyCnotSum

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_castAdd_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_castAdd_append

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_affinePushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_affinePushforward

/-- info: 'FTQCLib.Frame.Walkthrough.cnotSum_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotSum_support

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauliOld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauliOld

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauliOld_not_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauliOld_not_symplectic

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_symplectic_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_symplectic_pair

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_paulix_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_paulix_control

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_paulix_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_paulix_target

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_pauliz_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_pauliz_control

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_pauliz_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_pauliz_target

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauliOld_pauliz_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauliOld_pauliz_control

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_word

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_eq_add_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_eq_add_word

/-- info: 'FTQCLib.Frame.Walkthrough.cnotBitMap_involutive_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotBitMap_involutive_word

/-- info: 'FTQCLib.Frame.Walkthrough.cnotPauli_cnotPauli_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotPauli_cnotPauli_word

end FTQCLib.Frame.Walkthrough

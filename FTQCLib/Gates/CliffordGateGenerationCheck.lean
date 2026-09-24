/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Gates.CliffordGateGeneration

/-!
# Check: the Clifford gates generate the symplectic group

Axiom rows for every declaration of `FTQCLib.Gates.CliffordGateGeneration`, each under a build-failing
`#guard_msgs`, plus the witness that the module is frame-pure: the four gate families lie in
`bigGateSet`, and the generation theorem is available with no `FTQCLib.Hilbert` in scope.

The private induction helper `transvection_mem_aux` is swept through its public consequence
`transvection_mem`.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

/-! ## The generators are in the generating set -/

/-- The four families are members, on one and two qubits. -/
theorem bigGateSet_members_two :
    (hadamardAt (0 : Fin 2) ∈ bigGateSet 2) ∧ (phaseAt (0 : Fin 2) ∈ bigGateSet 2) ∧
      (cnotAt (0 : Fin 2) 1 (by decide) ∈ bigGateSet 2) ∧
      (czAt (0 : Fin 2) 1 (by decide) ∈ bigGateSet 2) :=
  ⟨hadamardAt_mem_bigGateSet 0, phaseAt_mem_bigGateSet 0, cnotAt_mem_bigGateSet 0 1 (by decide),
    czAt_mem_bigGateSet 0 1 (by decide)⟩

/-- The generation theorem, instantiated: every symplectic map on two qubits is in the closure. -/
theorem mem_closure_of_isClifford_two {T : Pauli 2 ≃ₗ[ZMod 2] Pauli 2} (hT : IsClifford T) :
    T ∈ Subgroup.closure (bigGateSet 2) := by
  rw [closure_bigGateSet_eq_spSubgroup]
  exact hT

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Gates.isClifford_symm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isClifford_symm

/-- info: 'FTQCLib.Gates.spSubgroup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spSubgroup

/-- info: 'FTQCLib.Gates.mem_spSubgroup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_spSubgroup

/-- info: 'FTQCLib.Gates.cliffordGateGens' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cliffordGateGens

/-- info: 'FTQCLib.Gates.SpGeneratedByCliffordGates' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SpGeneratedByCliffordGates

/-- info: 'FTQCLib.Gates.transvectionGens_omega' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvectionGens_omega

/-- info: 'FTQCLib.Gates.transvectionEquiv_closure_eq_spSubgroup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvectionEquiv_closure_eq_spSubgroup

/-- info: 'FTQCLib.Gates.transvectionEquiv_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvectionEquiv_zero

/-- info: 'FTQCLib.Gates.bigGateSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bigGateSet

/-- info: 'FTQCLib.Gates.hadamardAt_mem_bigGateSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hadamardAt_mem_bigGateSet

/-- info: 'FTQCLib.Gates.phaseAt_mem_bigGateSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseAt_mem_bigGateSet

/-- info: 'FTQCLib.Gates.cnotAt_mem_bigGateSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotAt_mem_bigGateSet

/-- info: 'FTQCLib.Gates.czAt_mem_bigGateSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czAt_mem_bigGateSet

/-- info: 'FTQCLib.Gates.closure_bigGateSet_le_spSubgroup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closure_bigGateSet_le_spSubgroup

/-- info: 'FTQCLib.Gates.trans_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trans_mem

/-- info: 'FTQCLib.Gates.transvectionEquiv_pauliz_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvectionEquiv_pauliz_mem

/-- info: 'FTQCLib.Gates.transvectionEquiv_pauliy_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvectionEquiv_pauliy_mem

/-- info: 'FTQCLib.Gates.transvectionEquiv_paulix_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvectionEquiv_paulix_mem

/-- info: 'FTQCLib.Gates.pauliSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliSupport

/-- info: 'FTQCLib.Gates.mem_pauliSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_pauliSupport

/-- info: 'FTQCLib.Gates.eq_zero_of_card_pauliSupport_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_zero_of_card_pauliSupport_zero

/-- info: 'FTQCLib.Gates.transvection_mem_of_card_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvection_mem_of_card_one

/-- info: 'FTQCLib.Gates.exists_normalize' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_normalize

/-- info: 'FTQCLib.Gates.cnot_clears' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnot_clears

/-- info: 'FTQCLib.Gates.support_reduction' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_reduction

/-- info: 'FTQCLib.Gates.transvection_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms transvection_mem

/-- info: 'FTQCLib.Gates.closure_bigGateSet_eq_spSubgroup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closure_bigGateSet_eq_spSubgroup

/-- info: 'FTQCLib.Gates.spGeneratedByCliffordGates' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spGeneratedByCliffordGates

/-- info: 'FTQCLib.Gates.bigGateSet_members_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bigGateSet_members_two

/-- info: 'FTQCLib.Gates.mem_closure_of_isClifford_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_closure_of_isClifford_two

end FTQCLib.Gates

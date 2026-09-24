/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import FTQCLib.Gates.CZ
import FTQCLib.Gates.Phase
import FTQCLib.Stabilizer.ZShear

/-!
# Acceptance rows for the Z-shear at a bit

* **Agreement with the gate maps** (kernel rows): the shear at `0` by `e₀` is the phase-gate map
  `phaseAt 0` on one qubit, and the shear at `0` by `e₁` is the controlled-Z map `czAt 0 1` on two
  qubits — pointwise on every Pauli.
* **The reader row**: the shear at `0` by `e₀` sends `Y₀` to `X₀` (the alignment the eliminating
  Hadamard uses on the rotate witness).
* **Symplecticity and involution on every pair** of two-qubit Paulis, by the kernel, for the
  `CZ` shear.
* **The symmetrising terms are load-bearing** (discriminating): the map that adds `(p.X 0)·e₁` to
  the Z-part and nothing else is not symplectic — `ω(X₀, X₁) = 0` but the images pair to `1`.
* **The shear by a matrix** (kernel rows): the shear by the `1 × 1` unit matrix is `phaseAt 0` on
  one qubit; the rank-four polar matrix of `CZ₀₁ · CZ₂₃` is the row of no shear at one bit, and its
  shear is the composite of the two `CZ` shears on every four-qubit Pauli; the mixed `S · CZ` matrix
  of the polar-form rows has a symmetric pairing through `isSymmPairing_mulVecLin`.
* **The symmetry hypothesis is load-bearing** (discriminating): the pairing of `!![0, 1; 0, 0]` is
  not symmetric and its shear moves some `ω`; on the line `⟨e₀⟩` that pairing is symmetric, and the
  on-shadow theorem carries the isotropic line `⟨X₀⟩` through the shear that the total theorem
  cannot.

`Pauli n` is finite with decidable equality and `ω` is `ZMod 2`-valued, so every row is a kernel
row. -/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli FTQCLib.Gates

/-! ## Agreement with the gate maps -/

/-- The shear at `0` by `e₀` is the phase gate on one qubit. -/
theorem zShear_eq_phaseAt : ∀ p : Pauli 1, zShear 0 (Pi.single 0 1) p = phaseAt 0 p := by
  decide

/-- The shear at `0` by `e₁` is the controlled-Z map on two qubits. -/
theorem zShear_eq_czAt : ∀ p : Pauli 2, zShear 0 (Pi.single 1 1) p = czAt 0 1 (by decide) p := by
  decide

/-! ## The reader row -/

/-- The shear at `0` by `e₀` sends `Y₀` to `X₀`. -/
theorem zShear_Y_eq_X : zShear 0 (Pi.single 0 1) (paulix 0 + pauliz 0 : Pauli 1) = paulix 0 := by
  decide

/-- The same through the reader lemma. -/
theorem zShear_Y_eq_X_lemma :
    zShear 0 (Pi.single 0 1) (paulix 0 + pauliz 0 : Pauli 1)
      = ⟨Pi.single 0 1, (paulix 0 + pauliz 0 : Pauli 1).Z + Pi.single 0 1⟩ :=
  zShear_reader 0 (Pi.single 0 1) (g := paulix 0 + pauliz 0) (by decide)

/-! ## Symplecticity and involution, exhaustively on two qubits -/

/-- The `CZ` shear preserves `ω` on every pair of two-qubit Paulis. -/
theorem omega_zShear_two :
    ∀ p q : Pauli 2,
      omega (zShear 0 (Pi.single 1 1) p) (zShear 0 (Pi.single 1 1) q) = omega p q := by
  decide

/-- The `CZ` shear is an involution on every two-qubit Pauli. -/
theorem zShear_zShear_two :
    ∀ p : Pauli 2, zShear 0 (Pi.single 1 1) (zShear 0 (Pi.single 1 1) p) = p := by
  decide

/-! ## The symmetrising terms are load-bearing -/

/-- The map that adds `(p.X 0)·e₁` to the Z-part and nothing else. -/
def halfShear (p : Pauli 2) : Pauli 2 := ⟨p.X, p.Z + (p.X 0) • (Pi.single 1 1 : Fin 2 → ZMod 2)⟩

/-- **Discriminating.** The half shear is not symplectic: `X₀` and `X₁` commute, their images do
not. -/
theorem halfShear_not_symplectic :
    omega (halfShear (paulix 0 : Pauli 2)) (halfShear (paulix 1 : Pauli 2))
      ≠ omega (paulix 0 : Pauli 2) (paulix 1) := by
  decide

/-- The full shear agrees with `ω` on the same pair. -/
theorem zShear_symplectic_on_pair :
    omega (zShear 0 (Pi.single 1 1) (paulix 0 : Pauli 2)) (zShear 0 (Pi.single 1 1) (paulix 1))
      = omega (paulix 0 : Pauli 2) (paulix 1) :=
  omega_zShear 0 (Pi.single 1 1) _ _

/-! ## The shear by a matrix -/

/-- The shear by the `1 × 1` unit matrix is the phase gate on one qubit. -/
theorem zShearBy_one_eq_phaseAt :
    ∀ p : Pauli 1, zShearBy (Matrix.mulVecLin !![(1 : ZMod 2)]) p = phaseAt 0 p := by
  decide

/-- The polar matrix of `CZ₀₁ · CZ₂₃`: rank four. -/
def polar4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

open Matrix in
/-- **No shear at one bit has the rank-four row**: for every bit and vector some X-part separates
the two. The shear by a linear map is the object the class needs. -/
theorem not_exists_shearRow_eq_polar4 :
    ∀ (k : Fin 4) (d : Fin 4 → ZMod 2), ∃ v, shearRow k d v ≠ polar4 *ᵥ v := by
  decide

open Matrix in
/-- The rank-four row is the sum of two one-bit rows. -/
theorem polar4_mulVec_eq :
    ∀ v, polar4 *ᵥ v = shearRow 0 (Pi.single 1 1) v + shearRow 2 (Pi.single 3 1) v := by
  decide

/-- The fold on the rank-four row: pushing by the sum of the two rows is pushing by the two
one-bit shears in turn, for every subspace of the four-qubit Paulis. -/
theorem map_rank4_eq_foldl (L : Submodule (ZMod 2) (Pauli 4)) :
    Submodule.map (zShearBy (shearLin 0 (Pi.single 1 1) + shearLin 2 (Pi.single 3 1))) L =
      Submodule.map (zShear 2 (Pi.single 3 1)) (Submodule.map (zShear 0 (Pi.single 1 1)) L) :=
  map_zShearBy_add _ _ L

/-- The shear by the rank-four matrix is the composite of the two `CZ` shears, on every
four-qubit Pauli — through the group law and the row identity, not by enumeration. -/
theorem zShearBy_polar4_eq (p : Pauli 4) :
    zShearBy (Matrix.mulVecLin polar4) p
      = zShear 0 (Pi.single 1 1) (zShear 2 (Pi.single 3 1) p) := by
  have h : Matrix.mulVecLin polar4 = shearLin 0 (Pi.single 1 1) + shearLin 2 (Pi.single 3 1) :=
    LinearMap.ext (fun v => polar4_mulVec_eq v)
  rw [h, zShearBy_add]
  rfl

/-- The mixed `S · CZ` matrix of the polar-form rows is symmetric, so its pairing is. -/
theorem isSymmPairing_mixed : IsSymmPairing (Matrix.mulVecLin !![(1 : ZMod 2), 1; 1, 0]) :=
  isSymmPairing_mulVecLin (Matrix.IsSymm.ext (by decide))

/-! ## The symmetry hypothesis is load-bearing -/

/-- The asymmetric matrix. -/
def asym : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]

/-- Its pairing is not symmetric. -/
theorem not_isSymmPairing_asym : ¬ IsSymmPairing (Matrix.mulVecLin asym) := by
  unfold IsSymmPairing
  decide

/-- **Discriminating.** The shear by the asymmetric matrix is not symplectic: some pair's `ω`
moves. -/
theorem zShearBy_asym_not_symplectic :
    ∃ p q : Pauli 2,
      omega (zShearBy (Matrix.mulVecLin asym) p) (zShearBy (Matrix.mulVecLin asym) q)
        ≠ omega p q := by
  decide

/-- On the line `⟨e₀⟩` the asymmetric pairing is symmetric. -/
theorem isSymmPairingOn_asym_line :
    IsSymmPairingOn (Matrix.mulVecLin asym) (Submodule.span (ZMod 2) {Pi.single 0 1}) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  clear hx hy
  revert a b
  decide

/-- The line `⟨X₀⟩` is isotropic. -/
theorem isStabilizer_line : IsStabilizer (Submodule.span (ZMod 2) {(paulix 0 : Pauli 2)}) := by
  intro p hp q hq
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
  clear hp hq
  revert a b
  decide

/-- The on-shadow theorem carries `⟨X₀⟩` through the shear by the asymmetric matrix, whose total
pairing is not symmetric: symmetry on the X-parts moved is the hypothesis the class rule has. -/
theorem isStabilizer_map_zShearBy_asym_line :
    IsStabilizer (Submodule.map (zShearBy (Matrix.mulVecLin asym))
      (Submodule.span (ZMod 2) {(paulix 0 : Pauli 2)})) :=
  isStabilizer_map_zShearBy_of_symm_on isSymmPairingOn_asym_line
    (fun p hp => by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
      exact Submodule.mem_span_singleton.mpr ⟨a, by rw [X_smul, paulix_X]⟩)
    isStabilizer_line

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Stabilizer.shearRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shearRow

/-- info: 'FTQCLib.Stabilizer.shearRow_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearRow_add

/-- info: 'FTQCLib.Stabilizer.shearRow_smul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearRow_smul

/-- info: 'FTQCLib.Stabilizer.shearRow_single' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearRow_single

/-- info: 'FTQCLib.Stabilizer.sum_shearRow_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sum_shearRow_mul

/-- info: 'FTQCLib.Stabilizer.zShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zShear

/-- info: 'FTQCLib.Stabilizer.zShear_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zShear_X

/-- info: 'FTQCLib.Stabilizer.zShear_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zShear_Z

/-- info: 'FTQCLib.Stabilizer.zShear_reader' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_reader

/-- info: 'FTQCLib.Stabilizer.zShear_zShear' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_zShear

/-- info: 'FTQCLib.Stabilizer.zShearEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearEquiv

/-- info: 'FTQCLib.Stabilizer.omega_zShear' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms omega_zShear

/-- info: 'FTQCLib.Stabilizer.isStabilizer_map_zShear' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_map_zShear

/-- info: 'FTQCLib.Stabilizer.zShear_eq_phaseAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_eq_phaseAt

/-- info: 'FTQCLib.Stabilizer.zShear_eq_czAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_eq_czAt

/-- info: 'FTQCLib.Stabilizer.zShear_Y_eq_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_Y_eq_X

/-- info: 'FTQCLib.Stabilizer.zShear_Y_eq_X_lemma' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_Y_eq_X_lemma

/-- info: 'FTQCLib.Stabilizer.omega_zShear_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms omega_zShear_two

/-- info: 'FTQCLib.Stabilizer.zShear_zShear_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_zShear_two

/-- info: 'FTQCLib.Stabilizer.halfShear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms halfShear

/-- info: 'FTQCLib.Stabilizer.halfShear_not_symplectic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms halfShear_not_symplectic

/-- info: 'FTQCLib.Stabilizer.zShear_symplectic_on_pair' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zShear_symplectic_on_pair

/-- info: 'FTQCLib.Stabilizer.zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy

/-- info: 'FTQCLib.Stabilizer.zShearBy_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_X

/-- info: 'FTQCLib.Stabilizer.zShearBy_Z' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_Z

/-- info: 'FTQCLib.Stabilizer.zShearBy_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_zShearBy

/-- info: 'FTQCLib.Stabilizer.zShearByEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearByEquiv

/-- info: 'FTQCLib.Stabilizer.zShearBy_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_add

/-- info: 'FTQCLib.Stabilizer.IsSymmPairingOn' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsSymmPairingOn

/-- info: 'FTQCLib.Stabilizer.IsSymmPairing' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsSymmPairing

/-- info: 'FTQCLib.Stabilizer.IsSymmPairing.on' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms IsSymmPairing.on

/-- info: 'FTQCLib.Stabilizer.omega_zShearBy_of_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms omega_zShearBy_of_eq

/-- info: 'FTQCLib.Stabilizer.omega_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms omega_zShearBy

/-- info: 'FTQCLib.Stabilizer.omega_zShearBy_of_mem' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms omega_zShearBy_of_mem

/-- info: 'FTQCLib.Stabilizer.isStabilizer_map_zShearBy_of_symm_on' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_map_zShearBy_of_symm_on

/-- info: 'FTQCLib.Stabilizer.isStabilizer_map_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_map_zShearBy

/-- info: 'FTQCLib.Stabilizer.isSymmPairing_mulVecLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isSymmPairing_mulVecLin

/-- info: 'FTQCLib.Stabilizer.shearLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearLin

/-- info: 'FTQCLib.Stabilizer.shearLin_apply' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearLin_apply

/-- info: 'FTQCLib.Stabilizer.isSymmPairing_shearLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isSymmPairing_shearLin

/-- info: 'FTQCLib.Stabilizer.zShear_eq_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShear_eq_zShearBy

/-- info: 'FTQCLib.Stabilizer.zShearBy_one_eq_phaseAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_one_eq_phaseAt

/-- info: 'FTQCLib.Stabilizer.polar4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms polar4

/-- info: 'FTQCLib.Stabilizer.not_exists_shearRow_eq_polar4' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms not_exists_shearRow_eq_polar4

/-- info: 'FTQCLib.Stabilizer.polar4_mulVec_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms polar4_mulVec_eq

/-- info: 'FTQCLib.Stabilizer.zShearBy_polar4_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_polar4_eq

/-- info: 'FTQCLib.Stabilizer.isSymmPairing_mixed' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isSymmPairing_mixed

/-- info: 'FTQCLib.Stabilizer.asym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms asym

/-- info: 'FTQCLib.Stabilizer.not_isSymmPairing_asym' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms not_isSymmPairing_asym

/-- info: 'FTQCLib.Stabilizer.zShearBy_asym_not_symplectic' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_asym_not_symplectic

/-- info: 'FTQCLib.Stabilizer.isSymmPairingOn_asym_line' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isSymmPairingOn_asym_line

/-- info: 'FTQCLib.Stabilizer.isStabilizer_line' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_line

/-- info: 'FTQCLib.Stabilizer.isStabilizer_map_zShearBy_asym_line' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms isStabilizer_map_zShearBy_asym_line

/-- info: 'FTQCLib.Stabilizer.zShearBy_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms zShearBy_zero

/-- info: 'FTQCLib.Stabilizer.map_zShearBy_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms map_zShearBy_add

/-- info: 'FTQCLib.Stabilizer.map_zShearBy_list_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms map_zShearBy_list_sum

/-- info: 'FTQCLib.Stabilizer.map_rank4_eq_foldl' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms map_rank4_eq_foldl

/-- info: 'FTQCLib.Stabilizer.shearRow_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearRow_zero

/-- info: 'FTQCLib.Stabilizer.shearRow_single_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearRow_single_self

/-- info: 'FTQCLib.Stabilizer.shearRow_single_ne' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms shearRow_single_ne

/-- info: 'FTQCLib.Stabilizer.map_zShearBy_finset_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms map_zShearBy_finset_sum

end FTQCLib.Stabilizer

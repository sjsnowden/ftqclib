/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import FTQCLib.Examples.CarrierClifford
import FTQCLib.Stabilizer.ZShearCheck
import FTQCLib.Examples.HadamardEliminationCheck

/-!
# Check: the Clifford gates on the carrier

Axiom rows for every declaration of `CarrierClifford`, and worked examples:

* **The Pauli signs** under `S`, `CZ` and `CNOT`, read off the two intertwinings: `S` at the
  reader `Y₀` (scalar `−1`, and end to end: the `Y₀` stabilizer of `KS`, the uniform record
  after `S`, is carried by `S` to `X₀`, which acts on `applyS KS` — the uniform support with the
  sign `(−1)^{x₀}` — by `−1`); `CZ` at `X₀X₁Z₁` (`−1`) and at `X₀Z₁` (`+1`); `CNOT` at
  `X₀X₁Z₁` (`+1`) and at `X₀Z₁` (`−1`).
* **The `i = j` control** — the index-driven shear `(i, e_i)` does not carry the datum of `Z_i`
  (`czGate m i i`); the zero shear does.
* **The class rule** — the `m = 1` `S` control (the index-driven shear does not carry the datum of
  `sGate 1 0`, the class rule's zero shear does); the three signs re-derived from the closed
  scalar `(−i)^A · (−1)^B · charOf m c`; the `yWeight` identity and the closed scalar on three
  general shears (`S ⊗ S`, the all-ones matrix, the rank-four `CZ₀₁ · CZ₂₃` rows) at `X₀`, `X₀X₁`,
  `X₀Z₁`, with two datum constants tied to their exponents; the rank-four datum from additivity,
  and **no shear at one bit carries it** (uniqueness at `⊤` against the `ZShearCheck` row); the
  class rule on `KS` through `applyS_eq_applyDiagPolar`.
* **The Bell record from `CZ`** — the uniform record on two registers (`Kpp`, support
  `{00, 01, 10, 11}`), `CZ` by `applyCZ`, then H at bit `0` = the Bell record: a floor at
  height `0` with the datum `σ = e₀ + e₁` (two bits), amplitudes `√2` at `00` and `0` at `01`; on
  the stale Lagrangian the collapse alignment does not hold (`not_alignedCollapse_stale`).
* **The Bell pair from `CNOT`** — from the record on `{00}` (`K00`), H at bit `0` through
  `hFloor`, then `CNOT`: a floor at height `0`, amplitudes `1/√2` at `00` and `11`, `0` at `01`.
* **A two-qubit rotate** at `m = 3` with the two-bit datum: the record `K5` on `⟨Y₀, Z₁⟩`
  (support `{00, 10}`, exponent `2·X₀`), the reader `Y₀Z₁`, residue `2`, scale `(1 + i)/√2`; the
  raise branch has no representer there and the raise formula gives the wrong amplitude at `0`
  (the `raiseForm` control).

`decide` cannot run through `DiagPhase.eval`; every evaluation row is an `rw` row.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer Module

/-! ## The Pauli signs under `S`, `CZ` and `CNOT` -/

/-- The `S` scalar at the reader `Y₀`, read off `pauliAct_zShear_of_shift`: `−1`. -/
theorem sSign_Y :
    Complex.I ^ yWeight (zShear (0 : Fin 1) (Pi.single 0 1) (paulix 0 + pauliz 0)) *
        (Complex.I ^ yWeight (paulix 0 + pauliz 0 : Pauli 1))⁻¹ *
        (-1) ^ (dotF2 (shearRow 0 (Pi.single 0 1) (paulix 0 + pauliz 0 : Pauli 1).X)
          (paulix 0 + pauliz 0 : Pauli 1).X).val * charOf 2 1 = -1 := by
  have h1 : yWeight (zShear (0 : Fin 1) (Pi.single 0 1) (paulix 0 + pauliz 0)) = 0 := by decide
  have h2 : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have h3 : (dotF2 (shearRow 0 (Pi.single 0 1) (paulix 0 + pauliz 0 : Pauli 1).X)
      (paulix 0 + pauliz 0 : Pauli 1).X).val = 1 := by decide
  rw [h1, h2, h3, charOf_two_one, pow_zero, pow_one, pow_one, one_mul, mul_comm _ (-1 : ℂ),
    mul_assoc, inv_mul_cancel₀ Complex.I_ne_zero, mul_one]

/-- The `S` datum on the reader `Y₀`, with the explicit constant `1`. -/
theorem sShift_Y (w : Fin 1 → ZMod 2) :
    (sGate 2 0).eval (w + (paulix 0 + pauliz 0 : Pauli 1).X) - (sGate 2 0).eval w =
      1 + (2 : ZMod (2 ^ 2)) ^ (2 - 1) *
        (((dotF2 (shearRow 0 (Pi.single 0 1) (paulix 0 + pauliz 0 : Pauli 1).X) w).val : ℕ) :
          ZMod (2 ^ 2)) := by
  rw [sGate_eval, sGate_eval]
  have hX : (paulix 0 + pauliz 0 : Pauli 1).X = Pi.single 0 1 := by decide
  rw [hX, shearRow_single_self, dotF2_smul_left, dotF2_single_left, Pi.add_apply,
    Pi.single_eq_same]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0] <;> decide

/-- **The `S` sign, end to end.** The `Y₀` stabilizer of `KS` (the uniform record after `S`) is
carried by `S` to `X₀`, which acts on `applyS KS` — the uniform support with the sign `(−1)^{x₀}` —
by `−1`. -/
theorem pauliAct_X_applyS_KS :
    pauliAct (paulix 0) (amp (applyS (ofKernelState KS) 0)) =
      fun w => -1 * amp (applyS (ofKernelState KS) 0) w := by
  have hZ : zShear (0 : Fin 1) (Pi.single 0 1) (paulix 0 + pauliz 0) = paulix 0 := by
    ext i <;> fin_cases i <;> decide
  have hamp : amp (applyS (ofKernelState KS) 0) =
      fun w => charOf 2 ((sGate 2 0).eval w) * amp (ofKernelState KS) w := by
    rw [amp_applyS]
    funext w
    rw [sGate_eval]
    exact rfl
  rw [hamp, ← hZ, pauliAct_zShear_of_shift (m := 2) (by decide) (sGate 2 0) 0 (Pi.single 0 1)
    (paulix 0 + pauliz 0) (amp (ofKernelState KS)) 1 sShift_Y, pauliAct_Y_KS, sSign_Y]

/-- The `CZ` scalar at `X₀X₁Z₁` (`m = 1`): `−1`. -/
theorem czSign_XXZ :
    Complex.I ^ yWeight (zShear (0 : Fin 2) (Pi.single 1 1) (paulix 0 + paulix 1 + pauliz 1)) *
        (Complex.I ^ yWeight (paulix 0 + paulix 1 + pauliz 1 : Pauli 2))⁻¹ *
        (-1) ^ (dotF2 (shearRow 0 (Pi.single 1 1) (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X)
          (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X).val * charOf 1 1 = -1 := by
  have h1 : yWeight (zShear (0 : Fin 2) (Pi.single 1 1) (paulix 0 + paulix 1 + pauliz 1)) = 1 := by
    decide
  have h2 : yWeight (paulix 0 + paulix 1 + pauliz 1 : Pauli 2) = 1 := by decide
  have h3 : (dotF2 (shearRow 0 (Pi.single 1 1) (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X)
      (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X).val = 0 := by decide
  rw [h1, h2, h3, charOf_one_one]
  simp

/-- The `CZ` scalar at `X₀Z₁` (`m = 1`): `+1`. -/
theorem czSign_XZ :
    Complex.I ^ yWeight (zShear (0 : Fin 2) (Pi.single 1 1) (paulix 0 + pauliz 1)) *
        (Complex.I ^ yWeight (paulix 0 + pauliz 1 : Pauli 2))⁻¹ *
        (-1) ^ (dotF2 (shearRow 0 (Pi.single 1 1) (paulix 0 + pauliz 1 : Pauli 2).X)
          (paulix 0 + pauliz 1 : Pauli 2).X).val * charOf 1 0 = 1 := by
  have h1 : yWeight (zShear (0 : Fin 2) (Pi.single 1 1) (paulix 0 + pauliz 1)) = 0 := by decide
  have h2 : yWeight (paulix 0 + pauliz 1 : Pauli 2) = 0 := by decide
  have h3 : (dotF2 (shearRow 0 (Pi.single 1 1) (paulix 0 + pauliz 1 : Pauli 2).X)
      (paulix 0 + pauliz 1 : Pauli 2).X).val = 0 := by decide
  rw [h1, h2, h3, charOf_zero]
  simp

/-- The `CZ` datum constants at those two Paulis: `1` at `X₀X₁Z₁`, `0` at `X₀Z₁`. -/
theorem czConst_rows :
    (2 : ZMod (2 ^ 1)) ^ (1 - 1) *
        ((((paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X 0).val : ZMod (2 ^ 1)) *
          (((paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X 1).val : ZMod (2 ^ 1))) = 1 ∧
      (2 : ZMod (2 ^ 1)) ^ (1 - 1) *
        ((((paulix 0 + pauliz 1 : Pauli 2).X 0).val : ZMod (2 ^ 1)) *
          (((paulix 0 + pauliz 1 : Pauli 2).X 1).val : ZMod (2 ^ 1))) = 0 := by
  decide

/-- The `CNOT` sign exponent at `X₀X₁Z₁`: `0` (sign `+1`). -/
theorem cnotSign_XXZ :
    ((paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X 0 *
      (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).Z 1 *
      (1 + (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X 1 +
        (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).Z 0)).val = 0 := by
  decide

/-- The `CNOT` sign exponent at `X₀Z₁`: `1` (sign `−1`). -/
theorem cnotSign_XZ :
    ((paulix 0 + pauliz 1 : Pauli 2).X 0 * (paulix 0 + pauliz 1 : Pauli 2).Z 1 *
      (1 + (paulix 0 + pauliz 1 : Pauli 2).X 1 + (paulix 0 + pauliz 1 : Pauli 2).Z 0)).val = 1 := by
  decide

/-! ## The `i = j` control -/

/-- **Discriminating.** The index-driven shear `(0, e₀)` does not carry the datum of `Z₀`
(`czGate 1 0 0`) at `n = 1`. -/
theorem not_diagShiftDatum_cz_self :
    ¬ DiagShiftDatum (czGate 1 (0 : Fin 1) 0) 0 (Pi.single 0 1) ⊤ := by
  intro h
  obtain ⟨c, hc⟩ := h (Pi.single 0 1) Submodule.mem_top
  have h0 := hc 0
  have h1 := hc (Pi.single 0 1)
  clear hc
  rw [czGate_eval, czGate_eval] at h0 h1
  revert h0 h1 c
  decide

/-- The zero shear carries it. -/
theorem diagShiftDatum_cz_self_zero : DiagShiftDatum (czGate 1 (0 : Fin 1) 0) 0 0 ⊤ :=
  diagShiftDatum_czGate_self le_rfl 0 ⊤

/-! ## The class rule on the carrier -/

/-- **The `m = 1` control.** At precision one the index-driven shear `(0, e₀)` does not carry the
datum of `S` (`sGate 1 0`, which reads as `Z`). -/
theorem not_diagShiftDatum_sGate_one :
    ¬ DiagShiftDatum (sGate 1 (0 : Fin 1)) 0 (Pi.single 0 1) ⊤ := by
  intro h
  obtain ⟨c, hc⟩ := h (Pi.single 0 1) Submodule.mem_top
  have h0 := hc 0
  have h1 := hc (Pi.single 0 1)
  clear hc
  rw [sGate_eval, sGate_eval, shearLin_apply, shearRow_single_self] at h0 h1
  revert h0 h1 c
  decide

/-- At precision one the class rule reads the zero shear for `S`: the datum with the zero map. -/
theorem diagShiftDatumBy_sGate_one_zero : DiagShiftDatumBy (sGate 1 (0 : Fin 1)) 0 ⊤ := by
  have h := diagShiftDatumBy_polarMatrix (sGate 1 (0 : Fin 1)) (levelExt_sGate_le_two 1 0) ⊤
  rwa [boolReduce_sGate, polarMatrix_sGate_one, Matrix.mulVecLin_zero] at h

/-- `charOf 2 2 = −1`. -/
theorem charOf_two_two : charOf 2 2 = -1 := by
  rw [show (2 : ZMod (2 ^ 2)) = 1 + 1 by decide, charOf_add, charOf_two_one, Complex.I_mul_I]

/-- **The `S` sign from the closed form**: at the reader `Y₀`, `A = 1`, `B = 1`, `c = 1`:
`(−i)·(−1)·i = −1`. -/
theorem sSign_Y_closed :
    (-Complex.I) ^ shearCount (shearLin 0 (Pi.single 0 1)) (paulix 0 + pauliz 0 : Pauli 1).X *
        (-1) ^ shearTriple (shearLin 0 (Pi.single 0 1)) (paulix 0 + pauliz 0 : Pauli 1) *
        charOf 2 1 = -1 := by
  have hA : shearCount (shearLin 0 (Pi.single 0 1)) (paulix 0 + pauliz 0 : Pauli 1).X = 1 := by
    decide
  have hB : shearTriple (shearLin 0 (Pi.single 0 1)) (paulix 0 + pauliz 0 : Pauli 1) = 1 := by
    decide
  rw [hA, hB, charOf_two_one, pow_one, pow_one]
  linear_combination Complex.I_mul_I

/-- **The `CZ` sign from the closed form** at `X₀X₁Z₁` (`m = 1`): `A = 2`, `B = 1`, `c = 1`:
`(−i)²·(−1)·(−1) = −1`. -/
theorem czSign_XXZ_closed :
    (-Complex.I) ^ shearCount (shearLin 0 (Pi.single 1 1))
        (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X *
      (-1) ^ shearTriple (shearLin 0 (Pi.single 1 1)) (paulix 0 + paulix 1 + pauliz 1 : Pauli 2) *
      charOf 1 1 = -1 := by
  have hA : shearCount (shearLin 0 (Pi.single 1 1))
      (paulix 0 + paulix 1 + pauliz 1 : Pauli 2).X = 2 := by decide
  have hB : shearTriple (shearLin 0 (Pi.single 1 1))
      (paulix 0 + paulix 1 + pauliz 1 : Pauli 2) = 1 := by decide
  rw [hA, hB, charOf_one_one]
  linear_combination Complex.I_mul_I

/-- **The `CZ` sign from the closed form** at `X₀Z₁` (`m = 1`): `A = 0`, `B = 0`, `c = 0`: `+1`. -/
theorem czSign_XZ_closed :
    (-Complex.I) ^ shearCount (shearLin 0 (Pi.single 1 1)) (paulix 0 + pauliz 1 : Pauli 2).X *
      (-1) ^ shearTriple (shearLin 0 (Pi.single 1 1)) (paulix 0 + pauliz 1 : Pauli 2) *
      charOf 1 0 = 1 := by
  have hA : shearCount (shearLin 0 (Pi.single 1 1)) (paulix 0 + pauliz 1 : Pauli 2).X = 0 := by
    decide
  have hB : shearTriple (shearLin 0 (Pi.single 1 1)) (paulix 0 + pauliz 1 : Pauli 2) = 0 := by
    decide
  rw [hA, hB, charOf_zero]
  simp

/-- The shear map of `S ⊗ S`: the identity matrix on two bits. -/
def ssLin : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) := Matrix.mulVecLin !![1, 0; 0, 1]

/-- The shear map of `S₀ · S₁ · CZ₀₁`: the all-ones matrix. -/
def fullLin : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) := Matrix.mulVecLin !![1, 1; 1, 1]

/-- The rank-four shear: the two `CZ` rows. -/
def rank4Lin : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  shearLin 0 (Pi.single 1 1) + shearLin 2 (Pi.single 3 1)

/-- The `yWeight` identity on `S ⊗ S` at `X₀X₁` and `X₀Z₁`, by the kernel. -/
theorem yWeight_ss_rows :
    (((yWeight (zShearBy ssLin (paulix 0 + paulix 1 : Pauli 2)) : ℕ) : ZMod 4) =
        ((yWeight (paulix 0 + paulix 1 : Pauli 2) : ℕ) : ZMod 4) +
          ((shearCount ssLin (paulix 0 + paulix 1 : Pauli 2).X : ℕ) : ZMod 4) -
            2 * ((shearTriple ssLin (paulix 0 + paulix 1 : Pauli 2) : ℕ) : ZMod 4)) ∧
      (((yWeight (zShearBy ssLin (paulix 0 + pauliz 1 : Pauli 2)) : ℕ) : ZMod 4) =
        ((yWeight (paulix 0 + pauliz 1 : Pauli 2) : ℕ) : ZMod 4) +
          ((shearCount ssLin (paulix 0 + pauliz 1 : Pauli 2).X : ℕ) : ZMod 4) -
            2 * ((shearTriple ssLin (paulix 0 + pauliz 1 : Pauli 2) : ℕ) : ZMod 4)) := by
  decide

/-- The `yWeight` identity on the all-ones shear at `X₀` and `X₀X₁`, by the kernel. -/
theorem yWeight_full_rows :
    (((yWeight (zShearBy fullLin (paulix 0 : Pauli 2)) : ℕ) : ZMod 4) =
        ((yWeight (paulix 0 : Pauli 2) : ℕ) : ZMod 4) +
          ((shearCount fullLin (paulix 0 : Pauli 2).X : ℕ) : ZMod 4) -
            2 * ((shearTriple fullLin (paulix 0 : Pauli 2) : ℕ) : ZMod 4)) ∧
      (((yWeight (zShearBy fullLin (paulix 0 + paulix 1 : Pauli 2)) : ℕ) : ZMod 4) =
        ((yWeight (paulix 0 + paulix 1 : Pauli 2) : ℕ) : ZMod 4) +
          ((shearCount fullLin (paulix 0 + paulix 1 : Pauli 2).X : ℕ) : ZMod 4) -
            2 * ((shearTriple fullLin (paulix 0 + paulix 1 : Pauli 2) : ℕ) : ZMod 4)) := by
  decide

/-- The `yWeight` identity on the rank-four shear at `X₀` and `X₀X₁`, by the kernel. -/
theorem yWeight_rank4_rows :
    (((yWeight (zShearBy rank4Lin (paulix 0 : Pauli 4)) : ℕ) : ZMod 4) =
        ((yWeight (paulix 0 : Pauli 4) : ℕ) : ZMod 4) +
          ((shearCount rank4Lin (paulix 0 : Pauli 4).X : ℕ) : ZMod 4) -
            2 * ((shearTriple rank4Lin (paulix 0 : Pauli 4) : ℕ) : ZMod 4)) ∧
      (((yWeight (zShearBy rank4Lin (paulix 0 + paulix 1 : Pauli 4)) : ℕ) : ZMod 4) =
        ((yWeight (paulix 0 + paulix 1 : Pauli 4) : ℕ) : ZMod 4) +
          ((shearCount rank4Lin (paulix 0 + paulix 1 : Pauli 4).X : ℕ) : ZMod 4) -
            2 * ((shearTriple rank4Lin (paulix 0 + paulix 1 : Pauli 4) : ℕ) : ZMod 4)) := by
  decide

/-- The datum constant of `S₀ · S₁` along `e₀ + e₁` at precision two is `2`, with the pairing of
`ssLin`. -/
theorem ssShift_XX (w : Fin 2 → ZMod 2) :
    DiagPhase.eval (sGate 2 0 + sGate 2 1) (w + (paulix 0 + paulix 1 : Pauli 2).X) -
        DiagPhase.eval (sGate 2 0 + sGate 2 1) w =
      2 + (2 : ZMod (2 ^ 2)) ^ (2 - 1) *
        (((dotF2 (ssLin (paulix 0 + paulix 1 : Pauli 2).X) w).val : ℕ) : ZMod (2 ^ 2)) := by
  rw [eval_add, eval_add, sGate_eval, sGate_eval, sGate_eval, sGate_eval]
  revert w
  decide

/-- The closed scalar of `S ⊗ S` at `X₀X₁` (`A = 2`, `B = 0`, `c = 2`): `(−i)²·(−1) = 1`. -/
theorem scalar_ss_XX :
    (-Complex.I) ^ shearCount ssLin (paulix 0 + paulix 1 : Pauli 2).X *
      (-1) ^ shearTriple ssLin (paulix 0 + paulix 1 : Pauli 2) * charOf 2 2 = 1 := by
  have hA : shearCount ssLin (paulix 0 + paulix 1 : Pauli 2).X = 2 := by decide
  have hB : shearTriple ssLin (paulix 0 + paulix 1 : Pauli 2) = 0 := by decide
  rw [hA, hB, charOf_two_two]
  linear_combination -Complex.I_mul_I

/-- The closed scalar of `S ⊗ S` at `X₀Z₁` (`A = 1`, `B = 0`, `c = 1`): `(−i)·i = 1`. -/
theorem scalar_ss_XZ :
    (-Complex.I) ^ shearCount ssLin (paulix 0 + pauliz 1 : Pauli 2).X *
      (-1) ^ shearTriple ssLin (paulix 0 + pauliz 1 : Pauli 2) * charOf 2 1 = 1 := by
  have hA : shearCount ssLin (paulix 0 + pauliz 1 : Pauli 2).X = 1 := by decide
  have hB : shearTriple ssLin (paulix 0 + pauliz 1 : Pauli 2) = 0 := by decide
  rw [hA, hB, charOf_two_one]
  linear_combination -Complex.I_mul_I

/-- The datum constant of `S₀ · S₁ · CZ₀₁` along `e₀` at precision two is `1`, with the pairing of
the all-ones matrix. -/
theorem fullShift_X (w : Fin 2 → ZMod 2) :
    DiagPhase.eval (sGate 2 0 + sGate 2 1 + czGate 2 0 1) (w + (paulix 0 : Pauli 2).X) -
        DiagPhase.eval (sGate 2 0 + sGate 2 1 + czGate 2 0 1) w =
      1 + (2 : ZMod (2 ^ 2)) ^ (2 - 1) *
        (((dotF2 (fullLin (paulix 0 : Pauli 2).X) w).val : ℕ) : ZMod (2 ^ 2)) := by
  rw [eval_add, eval_add, eval_add, eval_add, sGate_eval, sGate_eval, sGate_eval, sGate_eval,
    czGate_eval, czGate_eval]
  revert w
  decide

/-- The closed scalar of the all-ones shear at `X₀` (`A = 1`, `B = 0`, `c = 1`): `(−i)·i = 1`. -/
theorem scalar_full_X :
    (-Complex.I) ^ shearCount fullLin (paulix 0 : Pauli 2).X *
      (-1) ^ shearTriple fullLin (paulix 0 : Pauli 2) * charOf 2 1 = 1 := by
  have hA : shearCount fullLin (paulix 0 : Pauli 2).X = 1 := by decide
  have hB : shearTriple fullLin (paulix 0 : Pauli 2) = 0 := by decide
  rw [hA, hB, charOf_two_one]
  linear_combination -Complex.I_mul_I

/-- The closed scalar of the all-ones shear at `X₀X₁` (`A = 0`, `B = 0`, `c = 0`): `1`. -/
theorem scalar_full_XX :
    (-Complex.I) ^ shearCount fullLin (paulix 0 + paulix 1 : Pauli 2).X *
      (-1) ^ shearTriple fullLin (paulix 0 + paulix 1 : Pauli 2) * charOf 2 0 = 1 := by
  have hA : shearCount fullLin (paulix 0 + paulix 1 : Pauli 2).X = 0 := by decide
  have hB : shearTriple fullLin (paulix 0 + paulix 1 : Pauli 2) = 0 := by decide
  rw [hA, hB, charOf_zero]
  simp

/-- The closed scalar of the rank-four shear at `X₀` (`A = 0`, `B = 0`, `c = 0`): `1`. -/
theorem scalar_rank4_X :
    (-Complex.I) ^ shearCount rank4Lin (paulix 0 : Pauli 4).X *
      (-1) ^ shearTriple rank4Lin (paulix 0 : Pauli 4) * charOf 2 0 = 1 := by
  have hA : shearCount rank4Lin (paulix 0 : Pauli 4).X = 0 := by decide
  have hB : shearTriple rank4Lin (paulix 0 : Pauli 4) = 0 := by decide
  rw [hA, hB, charOf_zero]
  simp

/-- The closed scalar of the rank-four shear at `X₀X₁` (`A = 2`, `B = 0`, `c = 2`): `1`. -/
theorem scalar_rank4_XX :
    (-Complex.I) ^ shearCount rank4Lin (paulix 0 + paulix 1 : Pauli 4).X *
      (-1) ^ shearTriple rank4Lin (paulix 0 + paulix 1 : Pauli 4) * charOf 2 2 = 1 := by
  have hA : shearCount rank4Lin (paulix 0 + paulix 1 : Pauli 4).X = 2 := by decide
  have hB : shearTriple rank4Lin (paulix 0 + paulix 1 : Pauli 4) = 0 := by decide
  rw [hA, hB, charOf_two_two]
  linear_combination -Complex.I_mul_I

/-- The rank-four exponent `CZ₀₁ · CZ₂₃` at precision two. -/
noncomputable def D4 : DiagPhase 4 2 := czGate 2 0 1 + czGate 2 2 3

/-- Its datum with the sum of the two `CZ` rows, from the additivity of the datum. -/
theorem diagShiftDatumBy_D4 : DiagShiftDatumBy D4 rank4Lin ⊤ :=
  DiagShiftDatumBy.add (diagShiftDatum_czGate (m := 2) (by decide) (by decide) ⊤)
    (diagShiftDatum_czGate (m := 2) (by decide) (by decide) ⊤)

/-- **No shear at one bit carries the rank-four datum**: uniqueness at `⊤` against the two-row
datum, and the `ZShearCheck` row that no one-bit row is the rank-four matrix. -/
theorem not_exists_diagShiftDatum_rank4 :
    ¬ ∃ (k : Fin 4) (d : Fin 4 → ZMod 2), DiagShiftDatum D4 k d ⊤ := by
  rintro ⟨k, d, h⟩
  have heq : shearLin k d = rank4Lin := eq_of_diagShiftDatumBy_top (by decide) h diagShiftDatumBy_D4
  obtain ⟨v, hv⟩ := not_exists_shearRow_eq_polar4 k d
  apply hv
  rw [polar4_mulVec_eq]
  have := congrArg (fun M => M v) heq
  simpa [rank4Lin] using this

/-- **The `S` sign end to end, through the class rule**: `applyDiagPolar` on `KS` with the `S`
exponent is `applyS`, and `X₀` acts on it by `−1`. -/
theorem pauliAct_X_applyDiagPolar_KS :
    pauliAct (paulix 0) (amp (applyDiagPolar (ofKernelState KS) (sGate 2 0))) =
      fun w => -1 * amp (applyDiagPolar (ofKernelState KS) (sGate 2 0)) w := by
  have h := applyS_eq_applyDiagPolar (ofKernelState KS) le_rfl 0
  change applyS (ofKernelState KS) 0 = applyDiagPolar (ofKernelState KS) (sGate 2 0) at h
  rw [← h]
  exact pauliAct_X_applyS_KS

/-! ## The uniform record on two registers, `CZ`, then H at bit `0` = the Bell record -/

/-- The all-`X` Lagrangian on two bits, constraint-presented. -/
def lagPP : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.Z = 0}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [Z_add, hp, hq, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Z_smul, hp, smul_zero]

theorem mem_lagPP {p : Pauli 2} : p ∈ lagPP ↔ p.Z = 0 := Iff.rfl

/-- The uniform record on two registers at `m = 1`: support `{00, 01, 10, 11}`, exponent `0`. -/
noncomputable def Kpp : KernelState 2 := ⟨1, 0, 1, lagPP, 0⟩

/-- Every word is on its support. -/
theorem support_Kpp (w : Fin 2 → ZMod 2) : ∃ p ∈ Kpp.L, w = Kpp.x₀ + p.X :=
  ⟨⟨w, 0⟩, rfl, by change w = 0 + w; rw [zero_add]⟩

/-- `Kpp` denotes the constant `1`. -/
theorem amp_Kpp (w : Fin 2 → ZMod 2) : amp (ofKernelState Kpp) w = 1 := by
  rw [amp_ofKernelState_pos Kpp (support_Kpp w)]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 2 1) w) = 1
  rw [eval_zero_diag, charOf_zero, one_mul]

theorem isStabilizer_lagPP : IsStabilizer lagPP := by
  intro p hp q hq
  rw [mem_lagPP] at hp hq
  rw [omega_eq_dotF2, hp, hq]
  unfold dotF2
  simp

theorem orthogonal_lagPP : LinearMap.BilinForm.orthogonal omegaBilin lagPP ≤ lagPP := by
  intro q hq
  rw [mem_lagPP]
  funext k
  have h := hq (⟨Pi.single k 1, 0⟩ : Pauli 2) (mem_lagPP.mpr rfl)
  change omega (⟨Pi.single k 1, 0⟩ : Pauli 2) q = 0 at h
  rw [omega_eq_dotF2, dotF2_single_left] at h
  have h0 : dotF2 (0 : Fin 2 → ZMod 2) q.X = 0 := by
    unfold dotF2
    simp
  rw [h0, zero_add] at h
  exact h

theorem isCarrier_Kpp : IsCarrier (ofKernelState Kpp) := by
  refine ⟨le_rfl, isStabilizer_lagPP, orthogonal_lagPP, ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [amp_Kpp] at h0
  exact one_ne_zero h0

theorem isFloor_Kpp : IsFloor (ofKernelState Kpp) := by
  refine ⟨isCarrier_Kpp, fun g hg => ⟨0, ?_⟩⟩
  change g.Z = 0 at hg
  funext w
  have hy : yWeight g = 0 := by
    unfold yWeight zDot
    simp [hg]
  have hz : zDot g (w + g.X) = 0 := by
    unfold zDot
    simp [hg]
  simp only [pauliAct, amp_Kpp, hy, hz, pow_zero, ZMod.val_zero, one_mul]

/-- The `CZ`'d record as a kernel state: exponent `X₀X₁`, the graph Lagrangian. -/
noncomputable def K3 : KernelState 2 :=
  ⟨1, (0 : DiagPhase 2 1) + MvPolynomial.rename (Fin.castAdd 0) (czGate 1 (0 : Fin 2) 1), 1,
    Submodule.map (zShear 0 (Pi.single 1 1)) lagPP, 0⟩

/-- It is `applyCZ` on the uniform record `Kpp`. -/
theorem ofKernelState_K3 : ofKernelState K3 = applyCZ (ofKernelState Kpp) 0 1 := rfl

/-- The `CZ`'d record is a floor (through `isFloor_applyCZ`). -/
theorem isFloor_K3 : IsFloor (ofKernelState K3) := by
  rw [ofKernelState_K3]
  exact isFloor_applyCZ isFloor_Kpp (by decide)

/-- `X₀Z₁` is in the graph Lagrangian. -/
theorem XZ_mem_K3 : (⟨Pi.single 0 1, Pi.single 1 1⟩ : Pauli 2) ∈ K3.L := by
  refine Submodule.mem_map.mpr ⟨⟨Pi.single 0 1, 0⟩, rfl, ?_⟩
  ext i <;> fin_cases i <;> decide

/-- `Z₀X₁` is in the graph Lagrangian. -/
theorem ZX_mem_K3 : (⟨Pi.single 1 1, Pi.single 0 1⟩ : Pauli 2) ∈ K3.L := by
  refine Submodule.mem_map.mpr ⟨⟨Pi.single 1 1, 0⟩, rfl, ?_⟩
  ext i <;> fin_cases i <;> decide

/-- The `CZ`'d amplitude: `(−1)^{w₀ w₁}`. -/
theorem amp_K3 (w : Fin 2 → ZMod 2) :
    amp (ofKernelState K3) w =
      charOf 1 (((w 0).val : ZMod (2 ^ 1)) * ((w 1).val : ZMod (2 ^ 1))) := by
  rw [ofKernelState_K3]
  change amp (applyDiagShear (ofKernelState Kpp) (czGate 1 0 1) 0 (Pi.single 1 1)) w = _
  rw [amp_applyDiagShear, amp_applyDiagSum]
  beta_reduce
  rw [amp_Kpp, mul_one]
  change charOf 1 (DiagPhase.eval (n := 2) (m := 1) (czGate 1 0 1) w) = _
  rw [czGate_eval]
  simp only [Nat.sub_self, pow_zero, one_mul]

/-- The reader `X₀Z₁` at bit `0`. -/
theorem isReader_XZ_K3 : IsReader K3.L 0 (⟨Pi.single 0 1, Pi.single 1 1⟩ : Pauli 2) :=
  ⟨XZ_mem_K3, rfl⟩

/-- The Bell record, the eliminating H at bit `0` on `K3` (`CZ` on the uniform record). -/
noncomputable def bell3 : KernelSumState 2 := hElimFloor 0 K3 ⟨Pi.single 0 1, Pi.single 1 1⟩

theorem isFloor_bell3 : IsFloor bell3 := isFloor_hElimFloor isFloor_K3 isReader_XZ_K3

theorem bell3_h : bell3.h = 0 := hElimFloor_h _ _ _

/-- The datum is two-bit: `σ = e₀ + e₁`. -/
theorem floorSigma_XZ_K3 :
    floorSigma 0 (⟨Pi.single 0 1, Pi.single 1 1⟩ : Pauli 2) = Pi.single 0 1 + Pi.single 1 1 := by
  decide

theorem amp_bell3 : amp bell3 = walshTransform 0 (amp (ofKernelState K3)) :=
  amp_hElimFloor isFloor_K3 isReader_XZ_K3

/-- The Bell record: the amplitude at `00` is `√2`. -/
theorem amp_bell3_00 : amp bell3 ![0, 0] = Real.sqrt 2 := by
  rw [amp_bell3]
  unfold walshTransform
  rw [amp_K3, amp_K3]
  have e0 : (Function.update (![0, 0] : Fin 2 → ZMod 2) 0 0) 0 = 0 := by decide
  have e1 : (Function.update (![0, 0] : Fin 2 → ZMod 2) 0 0) 1 = 0 := by decide
  have f0 : (Function.update (![0, 0] : Fin 2 → ZMod 2) 0 1) 0 = 1 := by decide
  have f1 : (Function.update (![0, 0] : Fin 2 → ZMod 2) 0 1) 1 = 0 := by decide
  have g0 : (![0, 0] : Fin 2 → ZMod 2) 0 = 0 := by decide
  rw [e0, e1, f0, f1, g0, signOf_zero', ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide]
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, one_mul, charOf_zero, one_add_one_eq_two]
  exact one_div_sqrt_two_mul_two

/-- The Bell record: the amplitude at `01` is `0`. -/
theorem amp_bell3_01 : amp bell3 ![0, 1] = 0 := by
  rw [amp_bell3]
  unfold walshTransform
  rw [amp_K3, amp_K3]
  have e0 : (Function.update (![0, 1] : Fin 2 → ZMod 2) 0 0) 0 = 0 := by decide
  have e1 : (Function.update (![0, 1] : Fin 2 → ZMod 2) 0 0) 1 = 1 := by decide
  have f0 : (Function.update (![0, 1] : Fin 2 → ZMod 2) 0 1) 0 = 1 := by decide
  have f1 : (Function.update (![0, 1] : Fin 2 → ZMod 2) 0 1) 1 = 1 := by decide
  have g0 : (![0, 1] : Fin 2 → ZMod 2) 0 = 0 := by decide
  rw [e0, e1, f0, f1, g0, signOf_zero', ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide]
  simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, charOf_zero, charOf_one_one]
  ring

/-- **Discriminating.** On the stale Lagrangian `⟨X₀, X₁⟩` (the `CZ` without the shear) the collapse
alignment at the datum `e₀ + e₁` does not hold: `X₀Z₁ ∉ ⟨X₀, X₁⟩`. -/
theorem not_alignedCollapse_stale : ¬ AlignedCollapse lagPP 0 (Pi.single 0 1 + Pi.single 1 1) := by
  intro h
  rw [AlignedCollapse, mem_lagPP] at h
  have h1 := congrFun h 1
  revert h1
  decide

/-! ## `{00}`, H at bit `0` through `hFloor`, then `CNOT` = the Bell pair -/

/-- The all-`Z` Lagrangian on two bits, constraint-presented. -/
def lagZZ : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X = 0}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [X_add, hp, hq, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [X_smul, hp, smul_zero]

theorem mem_lagZZ {p : Pauli 2} : p ∈ lagZZ ↔ p.X = 0 := Iff.rfl

/-- The record on the single word `{00}` at `m = 1`: Lagrangian `⟨Z₀, Z₁⟩`, exponent `0`. -/
noncomputable def K00 : KernelState 2 := ⟨1, 0, 1, lagZZ, 0⟩

/-- Its support is the word `0`. -/
theorem support_K00 (w : Fin 2 → ZMod 2) : (∃ p ∈ K00.L, w = K00.x₀ + p.X) ↔ w = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.X = 0 at hp
    change 0 + p.X = 0
    rw [hp, add_zero]
  · rintro rfl
    exact ⟨0, rfl, by change (0 : Fin 2 → ZMod 2) = 0 + 0; rw [add_zero]⟩

theorem amp_K00_zero : amp (ofKernelState K00) 0 = 1 := by
  rw [amp_ofKernelState_pos K00 ((support_K00 0).mpr rfl)]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 2 1) 0) = 1
  rw [eval_zero_diag, charOf_zero, one_mul]

theorem amp_K00_ne (w : Fin 2 → ZMod 2) (hw : w ≠ 0) : amp (ofKernelState K00) w = 0 :=
  amp_ofKernelState_neg K00 (fun h => hw ((support_K00 w).mp h))

theorem isStabilizer_lagZZ : IsStabilizer lagZZ := by
  intro p hp q hq
  rw [mem_lagZZ] at hp hq
  rw [omega_eq_dotF2, hp, hq]
  unfold dotF2
  simp

theorem orthogonal_lagZZ : LinearMap.BilinForm.orthogonal omegaBilin lagZZ ≤ lagZZ := by
  intro q hq
  rw [mem_lagZZ]
  funext k
  have h := hq (⟨0, Pi.single k 1⟩ : Pauli 2) (mem_lagZZ.mpr rfl)
  change omega (⟨0, Pi.single k 1⟩ : Pauli 2) q = 0 at h
  rw [omega_eq_dotF2, dotF2_single_left] at h
  have h0 : dotF2 (0 : Fin 2 → ZMod 2) q.Z = 0 := by
    unfold dotF2
    simp
  rw [h0, add_zero] at h
  exact h

theorem isCarrier_K00 : IsCarrier (ofKernelState K00) := by
  refine ⟨le_rfl, isStabilizer_lagZZ, orthogonal_lagZZ, ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [amp_K00_zero] at h0
  exact one_ne_zero h0

theorem isFloor_K00 : IsFloor (ofKernelState K00) := by
  refine ⟨isCarrier_K00, fun g hg => ⟨0, ?_⟩⟩
  change g.X = 0 at hg
  funext w
  have hy : yWeight g = 0 := by
    unfold yWeight
    rw [hg]
    unfold zDot
    simp
  simp only [pauliAct, hy, pow_zero, ZMod.val_zero, one_mul, hg, add_zero]
  by_cases hw : w = 0
  · subst hw
    have hz : zDot g (0 : Fin 2 → ZMod 2) = 0 := by
      unfold zDot
      simp
    rw [hz, pow_zero, one_mul]
  · rw [amp_K00_ne w hw, mul_zero]

/-- The Bell pair, H at bit `0` through `hFloor` then `CNOT`. -/
noncomputable def bell12 : KernelSumState 2 := applyCnotSum 0 1 (hFloor 0 K00)

theorem isFloor_bell12 : IsFloor bell12 :=
  isFloor_applyCnotSum (by decide) (isFloor_hFloor isFloor_K00 0)

theorem bell12_h : bell12.h = 0 := by
  change (hFloor 0 K00).h = 0
  exact hFloor_h 0 K00

theorem amp_bell12 (w : Fin 2 → ZMod 2) :
    amp bell12 w = walshTransform 0 (amp (ofKernelState K00)) (cnotBitMap 0 1 w) := by
  change amp (applyCnotSum 0 1 (hFloor 0 K00)) w = _
  rw [amp_applyCnotSum (by decide), amp_hFloor isFloor_K00 0]

/-- The Bell pair: the amplitude at `00` is `1/√2`. -/
theorem amp_bell12_00 : amp bell12 ![0, 0] = 1 / (Real.sqrt 2 : ℂ) := by
  rw [amp_bell12]
  have hc : cnotBitMap (0 : Fin 2) 1 ![0, 0] = 0 := by decide
  rw [hc]
  unfold walshTransform
  have h1 : Function.update (0 : Fin 2 → ZMod 2) 0 0 = 0 := by decide
  have h2 : Function.update (0 : Fin 2 → ZMod 2) 0 1 ≠ 0 := by decide
  rw [h1, amp_K00_zero, amp_K00_ne _ h2, Pi.zero_apply, signOf_zero', mul_zero, add_zero, mul_one]

/-- The Bell pair: the amplitude at `11` is `1/√2`. -/
theorem amp_bell12_11 : amp bell12 ![1, 1] = 1 / (Real.sqrt 2 : ℂ) := by
  rw [amp_bell12]
  have hc : cnotBitMap (0 : Fin 2) 1 ![1, 1] = ![1, 0] := by decide
  rw [hc]
  unfold walshTransform
  have h1 : Function.update (![1, 0] : Fin 2 → ZMod 2) 0 0 = 0 := by decide
  have h2 : Function.update (![1, 0] : Fin 2 → ZMod 2) 0 1 ≠ 0 := by decide
  have h3 : (![1, 0] : Fin 2 → ZMod 2) 0 = 1 := by decide
  rw [h1, amp_K00_zero, amp_K00_ne _ h2, h3, signOf_one', mul_zero, add_zero, mul_one]

/-- The Bell pair: the amplitude at `01` is `0`. -/
theorem amp_bell12_01 : amp bell12 ![0, 1] = 0 := by
  rw [amp_bell12]
  have hc : cnotBitMap (0 : Fin 2) 1 ![0, 1] = ![0, 1] := by decide
  rw [hc]
  unfold walshTransform
  have h1 : Function.update (![0, 1] : Fin 2 → ZMod 2) 0 0 ≠ 0 := by decide
  have h2 : Function.update (![0, 1] : Fin 2 → ZMod 2) 0 1 ≠ 0 := by decide
  rw [amp_K00_ne _ h1, amp_K00_ne _ h2, mul_zero, add_zero, mul_zero]

/-! ## The two-qubit rotate at `m = 3` with the two-bit datum -/

/-- `⟨Y₀, Z₁⟩`, constraint-presented. -/
def lagYZ : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X 1 = 0 ∧ p.Z 0 = p.X 0}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [X_add, Z_add, Pi.add_apply, Pi.add_apply, Pi.add_apply, hp.1, hq.1, hp.2, hq.2, add_zero]
    exact ⟨rfl, rfl⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [X_smul, Z_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hp.1, hp.2, smul_zero]
    exact ⟨rfl, rfl⟩

theorem mem_lagYZ {p : Pauli 2} : p ∈ lagYZ ↔ p.X 1 = 0 ∧ p.Z 0 = p.X 0 := Iff.rfl

/-- The record on `⟨Y₀, Z₁⟩` at `m = 3`: support `{00, 10}`, exponent `2·X₀`. -/
noncomputable def K5 : KernelState 2 := ⟨3, MvPolynomial.C 2 * MvPolynomial.X 0, 1, lagYZ, 0⟩

theorem eval_K5q (v : Fin 2 → ZMod 2) :
    DiagPhase.eval K5.q v = 2 * ((v 0).val : ZMod (2 ^ K5.m)) := by
  change DiagPhase.eval (MvPolynomial.C 2 * MvPolynomial.X 0 : DiagPhase 2 3) v =
    2 * ((v 0).val : ZMod (2 ^ 3))
  rw [eval_mul, eval_C, eval_X]

/-- Its support is `{w : w₁ = 0}`. -/
theorem support_K5 (w : Fin 2 → ZMod 2) : (∃ p ∈ K5.L, w = K5.x₀ + p.X) ↔ w 1 = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.X 1 = 0 ∧ p.Z 0 = p.X 0 at hp
    change (0 + p.X) 1 = 0
    rw [zero_add]
    exact hp.1
  · intro hw
    refine ⟨⟨w, (w 0) • Pi.single 0 1⟩, mem_lagYZ.mpr ⟨hw, ?_⟩, ?_⟩
    · change (w 0) • (Pi.single 0 1 : Fin 2 → ZMod 2) 0 = w 0
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · change w = 0 + w
      rw [zero_add]

theorem amp_K5 (w : Fin 2 → ZMod 2) (hw : w 1 = 0) :
    amp (ofKernelState K5) w = charOf 3 (2 * ((w 0).val : ZMod (2 ^ 3))) := by
  rw [amp_ofKernelState_pos K5 ((support_K5 w).mpr hw), eval_K5q]
  change (1 : ℂ) * charOf 3 (2 * ((w 0).val : ZMod (2 ^ 3))) = _
  rw [one_mul]

theorem amp_K5_ne (w : Fin 2 → ZMod 2) (hw : w 1 ≠ 0) : amp (ofKernelState K5) w = 0 :=
  amp_ofKernelState_neg K5 (fun h => hw ((support_K5 w).mp h))

theorem isStabilizer_lagYZ : IsStabilizer lagYZ := by
  intro p hp q hq
  rw [mem_lagYZ] at hp hq
  rw [omega_eq_dotF2]
  unfold dotF2
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hp.1, hq.1, hp.2, hq.2]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination (p.X 0 * q.X 0) * h2

theorem orthogonal_lagYZ : LinearMap.BilinForm.orthogonal omegaBilin lagYZ ≤ lagYZ := by
  intro q hq
  rw [mem_lagYZ]
  have hY := hq (⟨Pi.single 0 1, Pi.single 0 1⟩ : Pauli 2) (mem_lagYZ.mpr ⟨rfl, rfl⟩)
  have hZ := hq (⟨0, Pi.single 1 1⟩ : Pauli 2) (mem_lagYZ.mpr ⟨rfl, rfl⟩)
  change omega (⟨Pi.single 0 1, Pi.single 0 1⟩ : Pauli 2) q = 0 at hY
  change omega (⟨0, Pi.single 1 1⟩ : Pauli 2) q = 0 at hZ
  rw [omega_eq_dotF2, dotF2_single_left, dotF2_single_left] at hY
  rw [omega_eq_dotF2, dotF2_single_left] at hZ
  have h0 : dotF2 (0 : Fin 2 → ZMod 2) q.Z = 0 := by
    unfold dotF2
    simp
  rw [h0, add_zero] at hZ
  refine ⟨hZ, ?_⟩
  have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact key _ _ hY

theorem isCarrier_K5 : IsCarrier (ofKernelState K5) := by
  refine ⟨by decide, isStabilizer_lagYZ, orthogonal_lagYZ, ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [amp_K5 0 rfl] at h0
  exact charOf_ne_zero _ _ h0

/-- The exponent law on `K5`: the defect along `g = (a·e₀, a·e₀ + b·e₁)` is `2a`. -/
theorem shiftLaw_K5 : ShiftLaw K5 := by
  intro g hg
  change g.X 1 = 0 ∧ g.Z 0 = g.X 0 at hg
  refine ⟨2 * ((g.X 0).val : ZMod (2 ^ K5.m)), ?_⟩
  intro w hw
  have hw1 : w 1 = 0 := (support_K5 w).mp hw
  rw [eval_K5q, eval_K5q]
  unfold zDot
  rw [Fin.sum_univ_two, hw1, hg.2, Pi.add_apply]
  rcases zmod_two_eq_zero_or_one (g.X 0) with ha | ha <;>
    rcases zmod_two_eq_zero_or_one (g.Z 1) with hb | hb <;>
    rcases zmod_two_eq_zero_or_one (w 0) with hw0 | hw0 <;>
    rw [ha, hb, hw0] <;> decide

theorem isFloor_K5 : IsFloor (ofKernelState K5) :=
  (isFloor_iff_shiftLaw K5 isCarrier_K5).mpr shiftLaw_K5

/-- The reader `Y₀Z₁` at bit `0`. -/
theorem isReader_YZ_K5 :
    IsReader K5.L 0 (⟨Pi.single 0 1, Pi.single 0 1 + Pi.single 1 1⟩ : Pauli 2) :=
  ⟨mem_lagYZ.mpr ⟨rfl, by decide⟩, rfl⟩

/-- Its datum is two-bit: `σ = e₀ + e₁`. -/
theorem floorSigma_YZ :
    floorSigma 0 (⟨Pi.single 0 1, Pi.single 0 1 + Pi.single 1 1⟩ : Pauli 2) =
      Pi.single 0 1 + Pi.single 1 1 := by
  decide

/-- The residue along the reader is `2` (so `2κ = 4 = 2^{m−1}`, rotate). -/
theorem floorKappa_K5 :
    floorKappa K5 (⟨Pi.single 0 1, Pi.single 0 1 + Pi.single 1 1⟩ : Pauli 2) = 2 := by
  unfold floorKappa
  rw [eval_K5q, eval_K5q]
  have hz : zDot (⟨Pi.single 0 1, Pi.single 0 1 + Pi.single 1 1⟩ : Pauli 2) K5.x₀ = 0 := by
    decide
  rw [hz]
  decide

/-- The eliminating H at bit `0` on `K5`. -/
noncomputable def rot5 : KernelSumState 2 :=
  hElimFloor 0 K5 ⟨Pi.single 0 1, Pi.single 0 1 + Pi.single 1 1⟩

theorem isFloor_rot5 : IsFloor rot5 := isFloor_hElimFloor isFloor_K5 isReader_YZ_K5

theorem rot5_h : rot5.h = 0 := hElimFloor_h _ _ _

/-- It is the rotate eliminator with `a = 2` and `Λ = xorForm (e₀ + e₁) 0`. -/
theorem rot5_eq :
    rot5 = hElimRotate 0 (ofKernelState K5) 2
      (xorForm (h := 0) (m := 3) (Pi.single 0 1 + Pi.single 1 1) 0) := by
  unfold rot5 hElimFloor
  rw [if_neg (by decide), floorKappa_K5, floorSigma_YZ]
  exact rfl

/-- The quarter turn at `m = 3`: `charOf 3 2 = i`. -/
theorem charOf_three_two : charOf 3 2 = Complex.I := by
  have h := charOf_two_pow_sub_two_mul (m := 3) (by decide) 1
  simpa using h

/-- The rotated `K5`: the scale is `(1 + i)/√2`. -/
theorem rot5_c : rot5.c = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [rot5_eq]
  change (1 : ℂ) * (1 + charOf 3 2) / (Real.sqrt 2 : ℂ) = _
  rw [charOf_three_two, one_mul]

theorem amp_rot5 : amp rot5 = walshTransform 0 (amp (ofKernelState K5)) :=
  amp_hElimFloor isFloor_K5 isReader_YZ_K5

/-- The rotated `K5`: the amplitude at `00` is `(1 + i)/√2`. -/
theorem amp_rot5_00 : amp rot5 ![0, 0] = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [amp_rot5]
  unfold walshTransform
  have h1 : Function.update (![0, 0] : Fin 2 → ZMod 2) 0 0 = ![0, 0] := by decide
  have h2 : Function.update (![0, 0] : Fin 2 → ZMod 2) 0 1 = ![1, 0] := by decide
  rw [h1, h2, amp_K5 _ (by decide), amp_K5 _ (by decide)]
  have g0 : (![0, 0] : Fin 2 → ZMod 2) 0 = 0 := by decide
  have g1 : (![1, 0] : Fin 2 → ZMod 2) 0 = 1 := by decide
  rw [g0, g1, signOf_zero', ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, charOf_zero, charOf_three_two, one_mul]
  ring

/-- The rotated `K5`: the amplitude at `10` is `(1 − i)/√2`. -/
theorem amp_rot5_10 : amp rot5 ![1, 0] = (1 - Complex.I) / (Real.sqrt 2 : ℂ) := by
  rw [amp_rot5]
  unfold walshTransform
  have h1 : Function.update (![1, 0] : Fin 2 → ZMod 2) 0 0 = ![0, 0] := by decide
  have h2 : Function.update (![1, 0] : Fin 2 → ZMod 2) 0 1 = ![1, 0] := by decide
  rw [h1, h2, amp_K5 _ (by decide), amp_K5 _ (by decide)]
  have g0 : (![0, 0] : Fin 2 → ZMod 2) 0 = 0 := by decide
  have g1 : (![1, 0] : Fin 2 → ZMod 2) 0 = 1 := by decide
  rw [g0, g1, signOf_one', ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, charOf_zero, charOf_three_two]
  ring

/-- **The `raiseForm` control (1).** Bit `0` is X-supported on `K5`, so no representer exists and
`hRaise`'s certificate hypothesis is not available: the bit belongs to the eliminating branch. -/
theorem no_representer_K5 :
    ¬ ∃ u : Fin 2 → ZMod 2, u 0 = 0 ∧ ∀ v ∈ Submodule.map xProj K5.L, dotF2 u v = v 0 := by
  rintro ⟨u, hu0, hrep⟩
  have h := hrep (Pi.single 0 1) (Submodule.mem_map_of_mem isReader_YZ_K5.1)
  rw [dotF2_single, Pi.single_eq_same, hu0] at h
  exact zero_ne_one h

/-- The raise exponent on `K5` with `u = 0`, at the word `0`: `0`. -/
theorem raise_exponent_K5_eval :
    DiagPhase.eval (n := 2 + 0) (m := 3)
      (raiseSubst (n := 2) (h := 0) (m := 3) 0 0 (raiseConst (n := 2) 0 0 0)
          (MvPolynomial.C 2 * MvPolynomial.X 0) +
        MvPolynomial.C ((2 : ZMod (2 ^ 3)) ^ (3 - 1)) *
          raiseForm (n := 2) (h := 0) (m := 3) 0 (raiseConst (n := 2) 0 0 0) *
          MvPolynomial.X (Fin.castAdd 0 0)) 0 = 0 := by
  rw [eval_add, eval_mul, raiseSubst_zero_eval, freezeAt_eval]
  have hu : Function.update (0 : Fin (2 + 0) → ZMod 2) (Fin.castAdd 0 0)
      (raiseConst (n := 2) 0 0 0) = 0 := by
    decide
  rw [hu]
  simp only [eval_mul, eval_C, eval_X, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero,
    add_zero]

/-- **The `raiseForm` control (2).** The raise formula with `u = 0` at bit `0` gives `1/√2` at the
word `0`, while the Walsh transform gives `(1 + i)/√2`. -/
theorem amp_hRaise_K5_ne :
    amp (hRaise 0 0 (ofKernelState K5)) 0 ≠ walshTransform 0 (amp (ofKernelState K5)) 0 := by
  have hw : walshTransform 0 (amp (ofKernelState K5)) 0 = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
    unfold walshTransform
    have h1 : Function.update (0 : Fin 2 → ZMod 2) 0 0 = ![0, 0] := by decide
    have h2 : Function.update (0 : Fin 2 → ZMod 2) 0 1 = ![1, 0] := by decide
    rw [h1, h2, amp_K5 _ (by decide), amp_K5 _ (by decide)]
    have g0 : (![0, 0] : Fin 2 → ZMod 2) 0 = 0 := by decide
    have g1 : (![1, 0] : Fin 2 → ZMod 2) 0 = 1 := by decide
    rw [g0, g1, Pi.zero_apply, signOf_zero', ZMod.val_zero,
      show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one,
      charOf_zero, charOf_three_two, one_mul]
    ring
  have hsupp : ∃ p ∈ (hRaise 0 0 (ofKernelState K5)).L,
      (0 : Fin 2 → ZMod 2) = (hRaise 0 0 (ofKernelState K5)).x₀ + p.X :=
    ⟨0, Submodule.zero_mem _, by decide⟩
  rw [hw, amp_pos hsupp]
  change ampCore 3 0 _ (1 / (Real.sqrt 2 : ℂ)) 0 ≠ _
  rw [ampCore_zero, exp_realPhase_eq_charOf]
  have hQ : charOf 3 (DiagPhase.eval (n := 2 + 0) (m := 3) (hRaise 0 0 (ofKernelState K5)).Q 0) =
      charOf 3 (DiagPhase.eval (n := 2 + 0) (m := 3)
        (raiseSubst (n := 2) (h := 0) (m := 3) 0 0 (raiseConst (n := 2) 0 0 0)
            (MvPolynomial.C 2 * MvPolynomial.X 0) +
          MvPolynomial.C ((2 : ZMod (2 ^ 3)) ^ (3 - 1)) *
            raiseForm (n := 2) (h := 0) (m := 3) 0 (raiseConst (n := 2) 0 0 0) *
            MvPolynomial.X (Fin.castAdd 0 0)) 0) := rfl
  rw [hQ, raise_exponent_K5_eval, charOf_zero, mul_one]
  intro h
  have h' : (1 : ℂ) = 1 + Complex.I := by
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)
    field_simp at h
    linear_combination h
  have : Complex.I = 0 := by linear_combination -h'
  exact Complex.I_ne_zero this

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_of_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_of_scalar

/-- info: 'FTQCLib.Frame.Walkthrough.neg_one_pow_val_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neg_one_pow_val_add

/-- info: 'FTQCLib.Frame.Walkthrough.neg_one_pow_zDot_zShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neg_one_pow_zDot_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShear

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShear_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShear_m

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShear_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShear_h

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShear_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShear_L

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShear_x₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShear_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyDiagSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyDiagSum

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyDiagShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyDiagShear

/-- info: 'FTQCLib.Frame.Walkthrough.finrank_map_zShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finrank_map_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyDiagShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyDiagShear

/-- info: 'FTQCLib.Frame.Walkthrough.DiagShiftDatum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagShiftDatum

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_zShear_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_zShear_of_shift

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyDiagShear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyDiagShear

/-- info: 'FTQCLib.Hierarchy.DiagPhase.sGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sGate

/-- info: 'FTQCLib.Hierarchy.DiagPhase.czGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czGate

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatum_sGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatum_sGate

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatum_czGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatum_czGate

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatum_czGate_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatum_czGate_self

/-- info: 'FTQCLib.Frame.Walkthrough.applyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyS

/-- info: 'FTQCLib.Frame.Walkthrough.applyCZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyCZ

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyS

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyCZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyCZ

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyS

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyS

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyCZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyCZ

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyCZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyCZ

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_swap

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_cnotBitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dotF2_cnotBitMap

/-- info: 'FTQCLib.Frame.Walkthrough.omega_cnotPauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms omega_cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_map_cnotPauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isStabilizer_map_cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyCnotSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyCnotSum

/-- info: 'FTQCLib.Frame.Walkthrough.cnot_sum_erase_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnot_sum_erase_erase

/-- info: 'FTQCLib.Frame.Walkthrough.sum_split_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_split_two

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_cnotPauli_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight_cnotPauli_cast

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_cnotPauli_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zDot_cnotPauli_cast

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_cnotPauli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_cnotPauli

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyCnotSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyCnotSum

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyCnotSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyCnotSum

/-- info: 'FTQCLib.Frame.Walkthrough.sSign_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sSign_Y

/-- info: 'FTQCLib.Frame.Walkthrough.sShift_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sShift_Y

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_X_applyS_KS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_X_applyS_KS

/-- info: 'FTQCLib.Frame.Walkthrough.czSign_XXZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czSign_XXZ

/-- info: 'FTQCLib.Frame.Walkthrough.czSign_XZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czSign_XZ

/-- info: 'FTQCLib.Frame.Walkthrough.czConst_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czConst_rows

/-- info: 'FTQCLib.Frame.Walkthrough.cnotSign_XXZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotSign_XXZ

/-- info: 'FTQCLib.Frame.Walkthrough.cnotSign_XZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotSign_XZ

/-- info: 'FTQCLib.Frame.Walkthrough.not_diagShiftDatum_cz_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_diagShiftDatum_cz_self

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatum_cz_self_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatum_cz_self_zero

/-- info: 'FTQCLib.Frame.Walkthrough.lagPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagPP

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lagPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lagPP

/-- info: 'FTQCLib.Frame.Walkthrough.Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.support_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.amp_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_lagPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isStabilizer_lagPP

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_lagPP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orthogonal_lagPP

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K3

/-- info: 'FTQCLib.Frame.Walkthrough.ofKernelState_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofKernelState_K3

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_K3

/-- info: 'FTQCLib.Frame.Walkthrough.XZ_mem_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms XZ_mem_K3

/-- info: 'FTQCLib.Frame.Walkthrough.ZX_mem_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZX_mem_K3

/-- info: 'FTQCLib.Frame.Walkthrough.amp_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_K3

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_XZ_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_XZ_K3

/-- info: 'FTQCLib.Frame.Walkthrough.bell3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bell3

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_bell3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_bell3

/-- info: 'FTQCLib.Frame.Walkthrough.bell3_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bell3_h

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_XZ_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_XZ_K3

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell3

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell3_00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell3_00

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell3_01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell3_01

/-- info: 'FTQCLib.Frame.Walkthrough.not_alignedCollapse_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_alignedCollapse_stale

/-- info: 'FTQCLib.Frame.Walkthrough.lagZZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagZZ

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lagZZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lagZZ

/-- info: 'FTQCLib.Frame.Walkthrough.K00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K00

/-- info: 'FTQCLib.Frame.Walkthrough.support_K00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_K00

/-- info: 'FTQCLib.Frame.Walkthrough.amp_K00_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_K00_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_K00_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_K00_ne

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_lagZZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isStabilizer_lagZZ

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_lagZZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orthogonal_lagZZ

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_K00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_K00

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_K00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_K00

/-- info: 'FTQCLib.Frame.Walkthrough.bell12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bell12

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_bell12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_bell12

/-- info: 'FTQCLib.Frame.Walkthrough.bell12_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bell12_h

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell12

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell12_00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell12_00

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell12_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell12_11

/-- info: 'FTQCLib.Frame.Walkthrough.amp_bell12_01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_bell12_01

/-- info: 'FTQCLib.Frame.Walkthrough.lagYZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lagYZ

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lagYZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lagYZ

/-- info: 'FTQCLib.Frame.Walkthrough.K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms K5

/-- info: 'FTQCLib.Frame.Walkthrough.eval_K5q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_K5q

/-- info: 'FTQCLib.Frame.Walkthrough.support_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms support_K5

/-- info: 'FTQCLib.Frame.Walkthrough.amp_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_K5

/-- info: 'FTQCLib.Frame.Walkthrough.amp_K5_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_K5_ne

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_lagYZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isStabilizer_lagYZ

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_lagYZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orthogonal_lagYZ

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_K5

/-- info: 'FTQCLib.Frame.Walkthrough.shiftLaw_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftLaw_K5

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_K5

/-- info: 'FTQCLib.Frame.Walkthrough.isReader_YZ_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isReader_YZ_K5

/-- info: 'FTQCLib.Frame.Walkthrough.floorSigma_YZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorSigma_YZ

/-- info: 'FTQCLib.Frame.Walkthrough.floorKappa_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms floorKappa_K5

/-- info: 'FTQCLib.Frame.Walkthrough.rot5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rot5

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_rot5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_rot5

/-- info: 'FTQCLib.Frame.Walkthrough.rot5_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rot5_h

/-- info: 'FTQCLib.Frame.Walkthrough.rot5_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rot5_eq

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_three_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charOf_three_two

/-- info: 'FTQCLib.Frame.Walkthrough.rot5_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rot5_c

/-- info: 'FTQCLib.Frame.Walkthrough.amp_rot5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_rot5

/-- info: 'FTQCLib.Frame.Walkthrough.amp_rot5_00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_rot5_00

/-- info: 'FTQCLib.Frame.Walkthrough.amp_rot5_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_rot5_10

/-- info: 'FTQCLib.Frame.Walkthrough.no_representer_K5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_representer_K5

/-- info: 'FTQCLib.Frame.Walkthrough.raise_exponent_K5_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms raise_exponent_K5_eval

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hRaise_K5_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hRaise_K5_ne

/-- info: 'FTQCLib.Frame.Walkthrough.neg_one_pow_zDot_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neg_one_pow_zDot_zShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShearBy_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShearBy_m

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShearBy_h' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShearBy_h

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShearBy_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShearBy_L

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShearBy_x₀' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShearBy_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyDiagShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyDiagShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.finrank_map_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finrank_map_zShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyDiagShearBy_of_symm_on' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyDiagShearBy_of_symm_on

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyDiagShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyDiagShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.DiagShiftDatumBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagShiftDatumBy

/-- info: 'FTQCLib.Frame.Walkthrough.DiagShiftDatumBy.mono' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagShiftDatumBy.mono

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatumBy_mulVecLin_iff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatumBy_mulVecLin_iff

/-- info: 'FTQCLib.Frame.Walkthrough.DiagShiftDatumBy.add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DiagShiftDatumBy.add

/-- info: 'FTQCLib.Frame.Walkthrough.isSymmPairingOn_of_diagShiftDatumBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isSymmPairingOn_of_diagShiftDatumBy

/-- info: 'FTQCLib.Frame.Walkthrough.eq_of_diagShiftDatumBy_top' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_diagShiftDatumBy_top

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_zShearBy_of_shift' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_zShearBy_of_shift

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyDiagShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyDiagShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.shearCount' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shearCount

/-- info: 'FTQCLib.Frame.Walkthrough.shearTriple' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shearTriple

/-- info: 'FTQCLib.Frame.Walkthrough.bit_val_add_mul_cast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bit_val_add_mul_cast

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_zShearBy_cast' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight_zShearBy_cast

/-- info: 'FTQCLib.Frame.Walkthrough.shearScalar_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shearScalar_eq

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_zShearBy_of_shift_closed' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_zShearBy_of_shift_closed

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar_m

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar_h' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar_h

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar_L

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar_x₀' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyDiagPolar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyDiagPolar

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyDiagPolar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_applyDiagPolar

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatumBy_polarMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatumBy_polarMatrix

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_applyDiagPolar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_applyDiagPolar

/-- info: 'FTQCLib.Frame.Walkthrough.upperSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms upperSupport

/-- info: 'FTQCLib.Frame.Walkthrough.pairMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairMatrix

/-- info: 'FTQCLib.Frame.Walkthrough.pairMatrix_apply_of_ne' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairMatrix_apply_of_ne

/-- info: 'FTQCLib.Frame.Walkthrough.pairMatrix_apply_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairMatrix_apply_self

/-- info: 'FTQCLib.Frame.Walkthrough.pairMatrix_apply_swap' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairMatrix_apply_swap

/-- info: 'FTQCLib.Frame.Walkthrough.eq_sum_pairMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_sum_pairMatrix

/-- info: 'FTQCLib.Frame.Walkthrough.mulVecLin_single_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulVecLin_single_self

/-- info: 'FTQCLib.Frame.Walkthrough.mulVecLin_single_pair' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulVecLin_single_pair

/-- info: 'FTQCLib.Frame.Walkthrough.mulVecLin_pairMatrix' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulVecLin_pairMatrix

/-- info: 'FTQCLib.Frame.Walkthrough.mulVecLin_eq_sum_shearLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulVecLin_eq_sum_shearLin

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar_L_eq_foldl' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar_L_eq_foldl

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagShear_eq_applyDiagShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagShear_eq_applyDiagShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatum_eq_diagShiftDatumBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatum_eq_diagShiftDatumBy

/-- info: 'FTQCLib.Frame.Walkthrough.applyS_eq_applyDiagPolar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyS_eq_applyDiagPolar

/-- info: 'FTQCLib.Frame.Walkthrough.applyCZ_eq_applyDiagPolar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyCZ_eq_applyDiagPolar

/-- info: 'FTQCLib.Frame.Walkthrough.not_diagShiftDatum_sGate_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_diagShiftDatum_sGate_one

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatumBy_sGate_one_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatumBy_sGate_one_zero

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charOf_two_two

/-- info: 'FTQCLib.Frame.Walkthrough.sSign_Y_closed' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sSign_Y_closed

/-- info: 'FTQCLib.Frame.Walkthrough.czSign_XXZ_closed' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czSign_XXZ_closed

/-- info: 'FTQCLib.Frame.Walkthrough.czSign_XZ_closed' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czSign_XZ_closed

/-- info: 'FTQCLib.Frame.Walkthrough.ssLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ssLin

/-- info: 'FTQCLib.Frame.Walkthrough.fullLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullLin

/-- info: 'FTQCLib.Frame.Walkthrough.rank4Lin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank4Lin

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_ss_rows' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight_ss_rows

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_full_rows' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight_full_rows

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_rank4_rows' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yWeight_rank4_rows

/-- info: 'FTQCLib.Frame.Walkthrough.ssShift_XX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ssShift_XX

/-- info: 'FTQCLib.Frame.Walkthrough.scalar_ss_XX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_ss_XX

/-- info: 'FTQCLib.Frame.Walkthrough.scalar_ss_XZ' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_ss_XZ

/-- info: 'FTQCLib.Frame.Walkthrough.fullShift_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullShift_X

/-- info: 'FTQCLib.Frame.Walkthrough.scalar_full_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_full_X

/-- info: 'FTQCLib.Frame.Walkthrough.scalar_full_XX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_full_XX

/-- info: 'FTQCLib.Frame.Walkthrough.scalar_rank4_X' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_rank4_X

/-- info: 'FTQCLib.Frame.Walkthrough.scalar_rank4_XX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scalar_rank4_XX

/-- info: 'FTQCLib.Frame.Walkthrough.D4' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms D4

/-- info: 'FTQCLib.Frame.Walkthrough.diagShiftDatumBy_D4' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagShiftDatumBy_D4

/-- info: 'FTQCLib.Frame.Walkthrough.not_exists_diagShiftDatum_rank4' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_exists_diagShiftDatum_rank4

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_X_applyDiagPolar_KS' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauliAct_X_applyDiagPolar_KS

/-- info: 'FTQCLib.Frame.Walkthrough.mulVecLin_polarMatrix_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mulVecLin_polarMatrix_add

/-- info: 'FTQCLib.Frame.Walkthrough.applyDiagPolar_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyDiagPolar_add

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.QubitSpace
import FTQCLib.Pauli.Basis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedSectionVars false

/-! # Pauli operators on the qubit Hilbert space

For each `p : Pauli n` (an F_2-symplectic Pauli with X-support `p.X`
and Z-support `p.Z`), the corresponding unitary operator on
`QubitSpace n` acts on a computational-basis vector `|v⟩` as

  `pauliOperator p |v⟩ = (-1)^{p.Z · v} |v + p.X⟩`,

where `p.Z · v = ∑_i (p.Z i).val * (v i).val` is the F_2 dot product
read as a parity (0 or 1). The result is the bit-flipped basis vector
`|v + p.X⟩` carrying a `±1` phase determined by the Z-support against
the input bits.

This is the standard Heisenberg-picture action of a Pauli operator on
computational basis states, modulo a global phase. We omit the global
phase (the `i^{p.X · p.Z}` factor that would make the operator
self-adjoint when both X- and Z-support are non-zero) because our
chapter 3 work is modulo global phase throughout.

This file defines:

* **`pauliOperator p`** — the operator action.
* **`pauliOperator_X`**, **`pauliOperator_Z`** — the action of pure
  `X`-Pauli and pure `Z`-Pauli operators, as sanity checks.
* **`pauliOperator_zero`** — `pauliOperator 0` is the identity.

We work with linear maps on `QubitSpace n`, not the `unitary` subgroup
of `Matrix.unitaryGroup`; the operational hierarchy on the Lean side
will reason about linear maps and use unitarity as an invariant
preserved by construction.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-- The F_2 dot product `p.Z · v` of a Z-support against a binary
input, read as an integer (parity) in {0, 1}. -/
noncomputable def zDotVal (p : Pauli n) (v : Fin n → ZMod 2) : ℕ :=
  ∑ i, ((p.Z i).val * (v i).val)

/-- The Pauli operator `pauliOperator p` acts on a computational-basis
vector `|v⟩` as `(-1)^{p.Z · v} |v + p.X⟩`.

Linearly extended: for an arbitrary `ψ : QubitSpace n`, the operator
sends `ψ` to the function `w ↦ (-1)^{p.Z · (w - p.X)} · ψ(w - p.X)`,
which when evaluated at `w = v + p.X` recovers the basis action
above. (Note `(w - p.X) = v` for `w = v + p.X`.)

The `(-1)^{p.Z · v}` factor is the `±1` sign that arises from
anti-commutation between Z's and X's on the same qubit: a `Z`-support
bit at position `i` flips sign exactly when the input vector has a
`1` at position `i`. -/
noncomputable def pauliOperator (p : Pauli n) :
    QubitSpace n →ₗ[ℂ] QubitSpace n where
  toFun ψ := fun w => (-1 : ℂ)^(zDotVal p (w - p.X)) * ψ (w - p.X)
  map_add' ψ φ := by
    funext w
    simp [mul_add]
  map_smul' c ψ := by
    funext w
    simp
    ring

/-- The action of `pauliOperator p` on a computational basis vector. -/
theorem pauliOperator_computational (p : Pauli n) (v : Fin n → ZMod 2) :
    pauliOperator p (computational v) =
      (-1 : ℂ)^(zDotVal p v) • computational (v + p.X) := by
  funext w
  unfold pauliOperator computational
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hw : w = v + p.X
  · subst hw
    have hzdot : v + p.X - p.X = v := by ring
    rw [hzdot]
    simp [Pi.smul_apply]
  · -- w ≠ v + p.X. Need to show both sides are 0.
    have h1 : w - p.X ≠ v := by
      intro heq
      apply hw
      have : w = v + p.X := by
        have : w - p.X + p.X = w := by ring
        rw [← this, heq]
      exact this
    simp only [Pi.smul_apply, smul_eq_mul, if_neg h1, if_neg hw, mul_zero]

/-- The pure `X`-Pauli `paulix i` flips bit `i`: `pauliOperator (paulix i) |v⟩ = |v ⊕ e_i⟩`,
no phase since `Z`-support is zero. -/
theorem pauliOperator_paulix (i : Fin n) (v : Fin n → ZMod 2) :
    pauliOperator (paulix i) (computational v) = computational (v + Pi.single i 1) := by
  rw [pauliOperator_computational]
  unfold zDotVal
  simp [paulix]

/-- Helper: `(pauliz i).Z j` is `1` if `j = i` and `0` otherwise.
The proof goes through `Function.update`, whose elaboration handles
the non-dependent `Fin n → ZMod 2` codomain cleanly. -/
private theorem pauliz_Z_apply (i j : Fin n) :
    (pauliz i).Z j = (if j = i then (1 : ZMod 2) else (0 : ZMod 2)) := by
  have hZ : (pauliz i).Z = Function.update (0 : Fin n → ZMod 2) i 1 := rfl
  rw [hZ, Function.update_apply]
  -- Function.update_apply gives if j = i then 1 else 0 j; the else
  -- branch is `(0 : Fin n → ZMod 2) j = 0`.
  by_cases hji : j = i
  · rw [if_pos hji, if_pos hji]
  · rw [if_neg hji, if_neg hji]
    rfl

/-- Helper: the F_2 dot product `(pauliz i).Z · v` equals `(v i).val`. -/
theorem zDotVal_pauliz (i : Fin n) (v : Fin n → ZMod 2) :
    zDotVal (pauliz i) v = (v i).val := by
  unfold zDotVal
  rw [Finset.sum_eq_single i]
  · -- Main case
    rw [pauliz_Z_apply, if_pos rfl]
    haveI : Fact (1 < 2) := ⟨by norm_num⟩
    rw [ZMod.val_one 2, one_mul]
  · intros j _ hji
    rw [pauliz_Z_apply, if_neg hji, ZMod.val_zero, Nat.zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The pure `Z`-Pauli `pauliz i` applies a `±1` phase determined by
bit `i`: `pauliOperator (pauliz i) |v⟩ = (-1)^{v_i} |v⟩`. -/
theorem pauliOperator_pauliz (i : Fin n) (v : Fin n → ZMod 2) :
    pauliOperator (pauliz i) (computational v) =
      (-1 : ℂ)^((v i).val) • computational v := by
  rw [pauliOperator_computational]
  have hX : (pauliz i).X = 0 := rfl
  rw [hX, add_zero]
  congr 1
  rw [zDotVal_pauliz]

/-- Helper: the F_2 dot product against the zero Pauli is always 0. -/
private theorem zDotVal_zero (v : Fin n → ZMod 2) :
    zDotVal (0 : Pauli n) v = 0 := by
  unfold zDotVal
  refine Finset.sum_eq_zero ?_
  intro i _
  have : ((0 : Pauli n).Z i).val = 0 := by
    change ((0 : ZMod 2)).val = 0
    exact ZMod.val_zero
  rw [this]
  ring

/-- The zero Pauli `0 : Pauli n` is the identity operator. -/
@[simp] theorem pauliOperator_zero :
    pauliOperator (0 : Pauli n) = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext w
  unfold pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  rw [show (0 : Pauli n).X = 0 from rfl, sub_zero, zDotVal_zero, pow_zero, one_mul]

end FTQCLib.Hilbert

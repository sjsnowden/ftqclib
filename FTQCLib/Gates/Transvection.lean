/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Gates.Clifford

/-! # Symplectic transvections and the Clifford gates

A **symplectic transvection** by a vector `v` is the map `τ_v : u ↦ u + ω(v, u)·v` on the symplectic
space `Pauli n`. Over `𝔽₂` it is an involution (`ω(v,v) = 0`) and a symplectic automorphism, so
`τ_v ∈ Sp(2n, 𝔽₂)`. Transvections are the building blocks of the symplectic group: they generate
`Sp(V)` (Cartan–Dieudonné / Witt), and each Clifford gate is a transvection or a short transvection
word.

This file builds the transvection (`transvectionEquiv` and its `IsClifford` witness), the
conjugation law `g · τ_v · g⁻¹ = τ_{g v}` for symplectic `g` (which carries a single-qubit
transvection to any qubit), and the first gate identity `τ_{Z_k} = S_k`. It is the foundation for
the theorem that the Clifford gates generate `Sp(2n, 𝔽₂)` (`spGeneratedByCliffordGates`), which
gives the surjectivity of the Clifford-to-symplectic map.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {n : ℕ}

/-! ## The transvection -/

/-- The linear part of the symplectic transvection by `v`: `u ↦ u + ω(v, u)·v`. Built as
`id + smulRight (ω v) v`, so linearity is inherited from the bilinear form. -/
def transvectionLin (v : Pauli n) : Pauli n →ₗ[ZMod 2] Pauli n :=
  LinearMap.id + LinearMap.smulRight (omegaBilin v) v

@[simp] theorem transvectionLin_apply (v u : Pauli n) :
    transvectionLin v u = u + omega v u • v := rfl

/-- The transvection is an involution: `τ_v ∘ τ_v = id` (using `ω(v,v) = 0` over `𝔽₂`). -/
theorem transvectionLin_involutive (v : Pauli n) :
    transvectionLin v ∘ₗ transvectionLin v = LinearMap.id := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.comp_apply, transvectionLin_apply, LinearMap.id_coe, id_eq,
    omega_add_right, omega_smul_right, omega_self, mul_zero, add_zero]
  have hvv : omega v u • v + omega v u • v = (0 : Pauli n) := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  rw [add_assoc, hvv, add_zero]

/-- The symplectic transvection by `v`, as a linear automorphism of `Pauli n` (its own inverse). -/
def transvectionEquiv (v : Pauli n) : Pauli n ≃ₗ[ZMod 2] Pauli n :=
  LinearEquiv.ofLinear (transvectionLin v) (transvectionLin v)
    (transvectionLin_involutive v) (transvectionLin_involutive v)

@[simp] theorem transvectionEquiv_apply (v u : Pauli n) :
    transvectionEquiv v u = u + omega v u • v := by
  simp only [transvectionEquiv, LinearEquiv.ofLinear_apply, transvectionLin_apply]

/-- A transvection preserves the symplectic form, hence lies in `Sp(2n, 𝔽₂)`. -/
theorem transvectionEquiv_isClifford (v : Pauli n) : IsClifford (transvectionEquiv v) := by
  intro p q
  simp only [omegaBilin_apply, transvectionEquiv_apply, omega_add_left, omega_add_right,
    omega_smul_left, omega_smul_right, omega_self, mul_zero, add_zero]
  rw [omega_comm p v, mul_comm (omega v q) (omega v p), add_assoc, CharTwo.add_self_eq_zero,
    add_zero]

/-! ## The conjugation law -/

/-- **Conjugation law.** For symplectic `T`, conjugating a transvection by `T` gives the
transvection by the transported vector: `T · τ_v · T⁻¹ = τ_{T v}`. Carries a single-qubit
transvection to any qubit. -/
theorem transvectionEquiv_conj {T : Pauli n ≃ₗ[ZMod 2] Pauli n} (hT : IsClifford T)
    (v : Pauli n) :
    transvectionEquiv (T v) = (T.symm.trans (transvectionEquiv v)).trans T := by
  refine LinearEquiv.ext fun u => ?_
  have h : omega (T v) u = omega v (T.symm u) := by
    have := hT v (T.symm u)
    simpa only [omegaBilin_apply, LinearEquiv.apply_symm_apply] using this
  simp only [LinearEquiv.trans_apply, transvectionEquiv_apply, map_add, map_smul,
    LinearEquiv.apply_symm_apply]
  rw [h]

/-! ## Gate identities: the phase gate is a transvection -/

/-- `ω(Z_k, u) = u_X(k)`: the form against a pure `Z` reads off the `X`-coordinate. -/
theorem omega_pauliz_left (k : Fin n) (u : Pauli n) : omega (pauliz k) u = u.X k := by
  simp only [omega, pauliz_Z, pauliz_X, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hjk; rw [Pi.single_eq_of_ne hjk, zero_mul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-- `ω(X_k, u) = u_Z(k)`: the form against a pure `X` reads off the `Z`-coordinate. -/
theorem omega_paulix_left (k : Fin n) (u : Pauli n) : omega (paulix k) u = u.Z k := by
  simp only [omega, paulix_Z, paulix_X, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hjk; rw [Pi.single_eq_of_ne hjk, zero_mul]
  · intro hk; exact absurd (Finset.mem_univ k) hk

/-- **The phase gate `S_k` is the transvection by `Z_k`**: `τ_{Z_k} = S_k`. -/
theorem transvectionEquiv_pauliz (k : Fin n) : transvectionEquiv (pauliz k) = phaseAt k := by
  refine LinearEquiv.ext fun u => ?_
  rw [transvectionEquiv_apply, omega_pauliz_left]
  ext i
  · simp
  · by_cases hik : i = k
    · subst hik
      simp [Z_add, Z_smul, pauliz_Z, Pi.single_eq_same, Function.update_self, smul_eq_mul]
    · simp [Z_add, Z_smul, pauliz_Z, Pi.single_eq_of_ne hik, Function.update_of_ne hik]

/-! ## Gate identities: Hadamard, and the remaining single-qubit transvections -/

/-- Hadamard sends the pure `Z_k` to the pure `X_k`. -/
theorem hadamardAt_pauliz (k : Fin n) : hadamardAt k (pauliz k) = paulix k := by
  ext i
  · by_cases hik : i = k
    · subst hik
      simp [hadamardAt_X, pauliz_X, pauliz_Z, paulix_X, Pi.single_eq_same, Function.update_self]
    · simp [hadamardAt_X, pauliz_X, pauliz_Z, paulix_X, Pi.single_eq_of_ne hik,
        Function.update_of_ne hik]
  · by_cases hik : i = k
    · subst hik
      simp [hadamardAt_Z, pauliz_X, pauliz_Z, paulix_Z, Function.update_self]
    · simp [hadamardAt_Z, pauliz_X, pauliz_Z, paulix_Z, Pi.single_eq_of_ne hik,
        Function.update_of_ne hik]

/-- Char-2 cancellation helpers for the qubit-`k` blocks of `τ_{Y_k}`. -/
private lemma zmod2_aba (a b : ZMod 2) : a + (b + a) = b := by revert a b; decide

private lemma zmod2_aab (a b : ZMod 2) : a + (a + b) = b := by revert a b; decide

/-- **Hadamard is the transvection by `Y_k`**: `τ_{X_k + Z_k} = H_k`. -/
theorem transvectionEquiv_pauliy (k : Fin n) :
    transvectionEquiv (paulix k + pauliz k) = hadamardAt k := by
  refine LinearEquiv.ext fun u => ?_
  rw [transvectionEquiv_apply, omega_add_left, omega_paulix_left, omega_pauliz_left]
  ext i
  · by_cases hik : i = k
    · subst hik
      simp only [X_add, X_smul, paulix_X, pauliz_X, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, add_zero, smul_eq_mul, mul_one, hadamardAt_X,
        Function.update_self]
      exact zmod2_aba (u.X i) (u.Z i)
    · simp [X_add, X_smul, paulix_X, pauliz_X, Pi.single_eq_of_ne hik, hadamardAt_X,
        Function.update_of_ne hik]
  · by_cases hik : i = k
    · subst hik
      simp only [Z_add, Z_smul, paulix_Z, pauliz_Z, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, zero_add, smul_eq_mul, mul_one, hadamardAt_Z,
        Function.update_self]
      exact zmod2_aab (u.Z i) (u.X i)
    · simp [Z_add, Z_smul, paulix_Z, pauliz_Z, Pi.single_eq_of_ne hik, hadamardAt_Z,
        Function.update_of_ne hik]

/-- **The transvection by `X_k` is `H_k · S_k · H_k`** — derived from the conjugation law, since
`H_k` swaps `Z_k ↦ X_k`. -/
theorem transvectionEquiv_paulix (k : Fin n) :
    transvectionEquiv (paulix k)
      = ((hadamardAt k).symm.trans (phaseAt k)).trans (hadamardAt k) := by
  have h := transvectionEquiv_conj (hadamardAt_isClifford k) (pauliz k)
  rw [hadamardAt_pauliz, transvectionEquiv_pauliz] at h
  exact h

end FTQCLib.Gates

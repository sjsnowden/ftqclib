/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Inner
import FTQCLib.Hilbert.GateLifts

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # The Hadamard gate as a norm-1 continuous linear map on `QState`

For the SU(2) coverage theorem the frame needs `H` as an **operator** on the ℓ² space `QState n`,
composable with the diagonal-gate CLM `qDiagCLM` and of operator norm `1` (so it is a contraction the
telescoping bound of `OpNormTelescope` can absorb). The repo's `hadamardGate` (`GateLifts.lean`) lives on
the bare, unnormed `QubitSpace n`; we transport it across `toQState` exactly as `qDiagCLM` transports
`diagonalGate`, and prove `‖H‖ = 1` by routing through the frame's own results: `H = (X+Z)/√2` is a real
combination of the self-adjoint Hermitian Paulis (`pauliHermitian_isSymmetric`), hence symmetric, and it is
involutive (`hadamardGate_involutive`), so `⟪Hψ,Hψ⟫ = ⟪ψ, H(Hψ)⟫ = ⟪ψ,ψ⟫` — an isometry. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-- Hadamard on qubit `k`, transported to the ℓ² space `QState n` (mirrors `qPauli`/`qDiagonalGate`). -/
noncomputable def qHadamard (k : Fin n) : QState n →ₗ[ℂ] QState n :=
  toQState.toLinearMap ∘ₗ hadamardGate k ∘ₗ toQState.symm.toLinearMap

theorem qHadamard_apply (k : Fin n) (ψ : QState n) :
    qHadamard k ψ = toQState (hadamardGate k (toQState.symm ψ)) := rfl

/-- `H² = id` on `QState`, transported from `hadamardGate_involutive`. -/
theorem qHadamard_involutive (k : Fin n) (ψ : QState n) :
    qHadamard k (qHadamard k ψ) = ψ := by
  rw [qHadamard_apply, qHadamard_apply, LinearEquiv.symm_apply_apply, hadamardGate_involutive,
    LinearEquiv.apply_symm_apply]

private theorem xzWeight_paulix (k : Fin n) : xzWeight (paulix k) = 0 := by
  unfold xzWeight zDotVal; simp [paulix_Z]

private theorem xzWeight_pauliz (k : Fin n) : xzWeight (pauliz k) = 0 := by
  unfold xzWeight zDotVal; simp [pauliz_X]

/-- **`H = (X+Z)/√2` on `QState`.** The transported Hadamard is `1/√2` times the sum of the two Hermitian
Paulis on qubit `k` (both have `xzWeight = 0`, so the Hermitian phase is trivial). -/
theorem qHadamard_eq (k : Fin n) :
    qHadamard k = invSqrt2 • (pauliHermitian (paulix k) + pauliHermitian (pauliz k)) := by
  ext ψ
  rw [qHadamard_apply, hadamardGate_eq]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add,
    LinearMap.add_apply, LinearMap.smul_apply, pauliHermitian_apply, xzWeight_paulix,
    xzWeight_pauliz, pow_zero, one_smul, qPauli_apply]

/-- The transported Hadamard is symmetric: `⟪Hx,y⟫ = ⟪x,Hy⟫`. A real (`invSqrt2`) combination of the
symmetric Hermitian Paulis. -/
theorem qHadamard_isSymmetric (k : Fin n) : (qHadamard k).IsSymmetric := by
  have hsx := pauliHermitian_isSymmetric (paulix k)
  have hsz := pauliHermitian_isSymmetric (pauliz k)
  have hconj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
    rw [invSqrt2, Complex.conj_ofReal]
  intro x y
  rw [qHadamard_eq]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, hconj, hsx x y, hsz x y]

/-- **Norm preservation.** `H` is an isometry on `QState`: symmetric + involutive gives
`⟪Hψ,Hψ⟫ = ⟪ψ,ψ⟫`. -/
theorem qHadamard_norm (k : Fin n) (ψ : QState n) : ‖qHadamard k ψ‖ = ‖ψ‖ := by
  have hinner : inner ℂ (qHadamard k ψ) (qHadamard k ψ) = inner ℂ ψ ψ := by
    rw [qHadamard_isSymmetric k ψ (qHadamard k ψ), qHadamard_involutive]
  have hnormsq : ‖qHadamard k ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
  nlinarith [norm_nonneg (qHadamard k ψ), norm_nonneg ψ, hnormsq]

/-- Hadamard on `QState n` as a bundled `LinearIsometry`. -/
noncomputable def qHadamardIsom (k : Fin n) : QState n →ₗᵢ[ℂ] QState n where
  toLinearMap := qHadamard k
  norm_map' := qHadamard_norm k

/-- **Hadamard as a continuous linear map on `QState n`**, composable with `qDiagCLM`. -/
noncomputable def qHadamardCLM (k : Fin n) : QState n →L[ℂ] QState n :=
  (qHadamardIsom k).toContinuousLinearMap

@[simp] theorem qHadamardCLM_apply (k : Fin n) (ψ : QState n) :
    qHadamardCLM k ψ = qHadamard k ψ := rfl

/-- **`‖H‖ = 1`**: the transported Hadamard is a contraction (in fact an isometry). -/
theorem qHadamardCLM_norm (k : Fin n) : ‖qHadamardCLM k‖ = 1 :=
  (qHadamardIsom k).norm_toContinuousLinearMap

/-- `H ∘ H = id` as continuous linear maps. -/
theorem qHadamardCLM_comp_self (k : Fin n) :
    qHadamardCLM k ∘L qHadamardCLM k = ContinuousLinearMap.id ℂ (QState n) := by
  ext ψ
  simp only [ContinuousLinearMap.comp_apply, qHadamardCLM_apply, ContinuousLinearMap.coe_id',
    id_eq, qHadamard_involutive]

end FTQCLib.Hilbert

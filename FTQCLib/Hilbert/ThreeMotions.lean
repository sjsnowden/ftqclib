/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.GateLifts

/-! # The Weyl interplay, Hilbert-side (a receipt for the three-motions appendix)

`X = HZH`: conjugating the phase-flip `Z` by the Hadamard gives the bit-flip `X` — the Weyl (Fourier) element
swaps the two Pauli axes. This is a fact about Hilbert operators (`hadamardGate`, `pauliOperator`), *not* a
frame-native result — it runs alongside the frame's own field-footprint (`FTQCLib/Examples/ThreeMotionsFrame.lean`),
the way the Born-rule receipt runs alongside the certificate. It specializes the symplectic dictionary
`hadamardEquiv_conj` (H = the `X↔Z` swap on Paulis); the companion `CX = (I⊗H)·CZ·(I⊗H)` — the Weyl element
carrying the symmetric-shear entangler `CZ` to the permutation entangler `CX` — is the standard identity of
Bravyi–Maslov's Bruhat normal form, and is witnessed here by the pair `czGate_conj` / `cnotGate_conj`. -/

namespace FTQCLib.Frame.ThreeMotions

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Hilbert Complex

variable {n : ℕ}

/-- **`X = HZH`.** Conjugating the phase-flip `Z` by the Hadamard gives the bit-flip `X`: the Weyl element
swaps the two Pauli axes. Specializes `hadamardEquiv_conj` to a pure `Z` (whose `X·Z` sign is trivial). -/
theorem pauliX_eq_HZH (k : Fin n) (ψ : QubitSpace n) :
    hadamardGate k (pauliOperator (pauliz k) (hadamardGate k ψ)) = pauliOperator (paulix k) ψ := by
  have h := hadamardEquiv_conj k (pauliz k)
  have hcomp : (conjEquiv (hadamardEquiv k) (pauliEquiv (pauliz k))).toLinearMap
      = hadamardGate k ∘ₗ pauliOperator (pauliz k) ∘ₗ hadamardGate k := by
    apply LinearMap.ext; intro φ
    simp only [LinearEquiv.coe_coe, conjEquiv_apply, hadamardEquiv_symm_apply, hadamardEquiv_apply,
      pauliEquiv_apply, LinearMap.comp_apply]
  have hAt : hadamardAt k (pauliz k) = paulix k := by
    refine Pauli.ext (funext fun l => ?_) (funext fun l => ?_) <;>
      · simp only [hadamardAt_X, hadamardAt_Z, pauliz_X, pauliz_Z, paulix_X, paulix_Z,
          Function.update_apply, Pi.single_apply, Pi.zero_apply]
        by_cases hl : l = k <;> simp [hl]
  have hsign : ((pauliz k).X k).val * ((pauliz k).Z k).val = 0 := by simp [pauliz_X]
  rw [hcomp, hAt, hsign, pow_zero, Units.val_one, one_smul] at h
  have hψ := LinearMap.congr_fun h ψ
  simpa only [LinearMap.comp_apply] using hψ

end FTQCLib.Frame.ThreeMotions

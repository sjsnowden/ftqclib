/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Frame.MetaplecticAction

/-! # The entangling generator: an explicit cubic sign cochain

The single-qubit transvection actions (`S`, `√X`, `H`) on the frame `(L,χ)` were validated by a
single **quadratic** sign cochain, `tvSignZ p = 2·X_k·Z_k` (in `FTQCLib.Frame.MetaplecticAction`). The
first **entangling** transvection `τ_{X₀X₁}` provably cannot use a quadratic cochain — its
distortion is not even additive on an isotropic triple at `n = 3`
(`frameDistortion_entangling_not_additive_on_isotropic`).

This file exhibits the cochain the entangling gate **does** use: an explicit **cubic** one,

`entCochain p = 2·(X₀Z₀ + X₁Z₁ + (X₀+X₁)·Z₀·Z₁)`,

and proves that it validates the action. The first two terms are exactly the single-qubit cochains
on qubits `0` and `1`; the third, `(X₀+X₁)·Z₀·Z₁`, is the irreducible degree-3 coupling the
entangling gate forces. So the entangling generator is buildable frame-purely — the obstruction is
only to a *quadratic* sign, not to *any* sign.

The `Fintype`/`DecidableEq (Pauli n)` instances this file's `decide`s use are the canonical ones
in `FTQCLib/Pauli/Basic.lean`. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Gates

variable {n : ℕ}

/-- `Pauli` as a pair of bit-vectors — only to give `Fintype`/`DecidableEq` for the finite check. -/
def pauliProdEquiv (n : ℕ) : Pauli n ≃ (Fin n → ZMod 2) × (Fin n → ZMod 2) where
  toFun p := (p.X, p.Z)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


/-- **The explicit cubic sign cochain for the entangling transvection `τ_{X₀X₁}`.**
`c(p) = 2·(X₀Z₀ + X₁Z₁ + (X₀+X₁)·Z₀·Z₁)`: the two single-qubit cochains plus the cubic coupling. -/
def entCochain (p : Pauli 2) : ZMod 4 :=
  2 * ((((p.X 0).val * (p.Z 0).val + (p.X 1).val * (p.Z 1).val
    + ((p.X 0).val + (p.X 1).val) * (p.Z 0).val * (p.Z 1).val) : ℕ) : ZMod 4)

/-- **The cubic cochain validates the entangling transvection action.** Its twisted coboundary
equals the gate's distortion `β(τp,τq) − β(p,q)` — the identity that makes the transported character
valid, now with a genuinely **cubic** cochain where the single-qubit gates needed only a quadratic
one (`tvSign_validity`). So `τ_{X₀X₁}` admits a frame-native sign and its action is well defined.
A finite `decide` over the `16 × 16` cases at two qubits. -/
theorem entCochain_validity (p q : Pauli 2) :
    entCochain (transvectionEquiv (paulix 0 + paulix 1) p)
      + entCochain (transvectionEquiv (paulix 0 + paulix 1) q)
      - entCochain (transvectionEquiv (paulix 0 + paulix 1) (p + q))
      = betaFrame (transvectionEquiv (paulix 0 + paulix 1) p)
          (transvectionEquiv (paulix 0 + paulix 1) q)
        - betaFrame p q := by
  simp only [map_add, transvectionEquiv_apply]
  revert p q
  decide

/-- The entangling transvection `τ_{X₀X₁}` is an involution. -/
theorem tvXX_invol (x : Pauli 2) :
    transvectionEquiv (paulix 0 + paulix 1) (transvectionEquiv (paulix 0 + paulix 1) x) = x := by
  have h := LinearMap.congr_fun (transvectionLin_involutive (paulix 0 + paulix 1)) x
  simpa [transvectionEquiv, LinearEquiv.ofLinear_apply] using h

open Classical in
/-- **The frame-pure entangling-gate action on `(L,χ)`** (the two-qubit transvection `τ_{X₀X₁}`),
using the cubic cochain `entCochain`. Same template as `frameTransvectionZAction`: the Lagrangian
moves by the transvection, the character transports as `χ∘τ + entCochain∘τ`, and validity comes from
`S.valid` and `entCochain_validity`. So the entangling generator is a genuine frame-pure
endomorphism; the cubic sign was all it took. -/
noncomputable def frameTransvectionXXAction (S : FramePureSignedStab 2) :
    FramePureSignedStab 2 where
  toFrameSignedStab :=
    { L := S.L.map (transvectionEquiv (paulix 0 + paulix 1)).toLinearMap
      chi := fun p =>
        if p ∈ S.L.map (transvectionEquiv (paulix 0 + paulix 1)).toLinearMap
        then S.chi (transvectionEquiv (paulix 0 + paulix 1) p)
          + entCochain (transvectionEquiv (paulix 0 + paulix 1) p)
        else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), map_zero, S.chi_zero, zero_add]
        unfold entCochain; simp
      valid := by
        intro p hp q hq
        have hτp : transvectionEquiv (paulix 0 + paulix 1) p ∈ S.L := by
          obtain ⟨p₀, hp₀, hep₀⟩ := Submodule.mem_map.mp hp
          rw [← hep₀]
          change transvectionEquiv (paulix 0 + paulix 1)
            (transvectionEquiv (paulix 0 + paulix 1) p₀) ∈ S.L
          rw [tvXX_invol]; exact hp₀
        have hτq : transvectionEquiv (paulix 0 + paulix 1) q ∈ S.L := by
          obtain ⟨q₀, hq₀, heq₀⟩ := Submodule.mem_map.mp hq
          rw [← heq₀]
          change transvectionEquiv (paulix 0 + paulix 1)
            (transvectionEquiv (paulix 0 + paulix 1) q₀) ∈ S.L
          rw [tvXX_invol]; exact hq₀
        have hpq : p + q ∈ S.L.map (transvectionEquiv (paulix 0 + paulix 1)).toLinearMap :=
          Submodule.add_mem _ hp hq
        simp only [if_pos hp, if_pos hq, if_pos hpq, map_add]
        rw [S.valid _ hτp _ hτq]
        have hval := entCochain_validity p q
        rw [map_add] at hval
        linear_combination -hval }
  isStab := FTQCLib.Stabilizer.clifford_preserves_isStabilizer S.isStab (transvectionEquiv_isClifford _)
  full := by
    rw [FTQCLib.Stabilizer.clifford_preserves_finrank S.L (transvectionEquiv (paulix 0 + paulix 1))]
    exact S.full
  tight := fun p hp => if_neg hp

end FTQCLib.Frame

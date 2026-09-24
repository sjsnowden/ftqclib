/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.StabilizerState
import FTQCLib.Stabilizer.PauliCondition

/-! # Born collapse for stabilizer states

For a stabilizer state `ψ` of a full signed stabilizer `(L, χ)`, the expectation of a Hermitian
Pauli `Q` collapses to the character value:

  `⟨ψ, H(Q) ψ⟩ = χ(Q)` if `Q ∈ L`,  and `0` otherwise.

The `Q ∈ L` case is the eigenvalue equation (`Q` stabilizes `ψ` up to its sign `χ(Q) = ±1`); the
`Q ∉ L` case uses an anticommuting stabilizer `g` (`ω(g,Q)=1`), giving
`⟨ψ,H(Q)ψ⟩ = ⟨ψ, g H(Q) g ψ⟩ = −⟨ψ,H(Q)ψ⟩ = 0`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Stabilizer Complex Module

variable {n : ℕ}

/-- **Born collapse, eigenvalue case.** If `Q ∈ L`, the expectation is the sign `χ(Q)`. -/
theorem expectation_mem (S : SignedStab n) (ψ : QState n) (hψ : ‖ψ‖ = 1)
    (hstab : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {Q : Pauli n} (hQ : Q ∈ S.L) :
    expectation ψ Q = S.sign Q := by
  have hsq : S.sign Q * S.sign Q = 1 := sign_mul_self S hQ
  have hne : S.sign Q ≠ 0 := by intro h; rw [h, mul_zero] at hsq; exact zero_ne_one hsq
  have hinner : S.sign Q * expectation ψ Q = 1 := by
    have h1 : inner ℂ ψ ((S.sign Q • pauliHermitian Q) ψ) = inner ℂ ψ ψ := by rw [hstab Q hQ]
    rw [LinearMap.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ] at h1
    simpa [expectation] using h1
  have h2 : S.sign Q * expectation ψ Q = S.sign Q * S.sign Q := by rw [hinner, hsq]
  exact mul_left_cancel₀ hne h2

/-- Bridge: the parity of the cocycle exponent `zDotVal p q.X + zDotVal q p.X` is the symplectic
form `ω(p,q)` (cast to `ZMod 2`). -/
theorem omega_natCast (p q : Pauli n) :
    ((zDotVal p q.X + zDotVal q p.X : ℕ) : ZMod 2) = omega p q := by
  unfold zDotVal omega
  push_cast
  simp only [ZMod.natCast_zmod_val]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Cocycle antisymmetry: `pauliPhase q p = (-1)^{ω-exponent} · pauliPhase p q`. -/
theorem pauliPhase_swap (p q : Pauli n) :
    pauliPhase q p = ((-1 : ℂ) ^ (zDotVal p q.X + zDotVal q p.X)) * pauliPhase p q := by
  unfold pauliPhase
  rw [add_comm q p]
  have hpar : ((-1 : ℂ) ^ (zDotVal p q.X + zDotVal (p + q) (p + q).X))
      = ((-1 : ℂ) ^ (zDotVal p q.X + zDotVal q p.X))
          * ((-1 : ℂ) ^ (zDotVal q p.X + zDotVal (p + q) (p + q).X)) := by
    rw [← pow_add]
    apply neg_one_pow_eq_of_mod_two_eq
    omega
  rw [hpar]; ring

/-- Hermitian Paulis (anti)commute by the symplectic sign:
`H(p) ∘ H(q) = (-1)^{ω-exponent} • (H(q) ∘ H(p))`. -/
theorem pauliHermitian_swap (p q : Pauli n) :
    pauliHermitian p ∘ₗ pauliHermitian q
      = ((-1 : ℂ) ^ (zDotVal p q.X + zDotVal q p.X)) • (pauliHermitian q ∘ₗ pauliHermitian p) := by
  rw [pauliHermitian_mul_phase q p, pauliHermitian_mul_phase p q, add_comm q p, pauliPhase_swap,
    smul_smul]

/-- Anticommuting case: when `ω(p,q)=1`, `H(p) ∘ H(q) = −(H(q) ∘ H(p))`. -/
theorem pauliHermitian_anticomm {p q : Pauli n} (h : omega p q = 1) :
    pauliHermitian p ∘ₗ pauliHermitian q = -(pauliHermitian q ∘ₗ pauliHermitian p) := by
  rw [pauliHermitian_swap]
  have hodd : (-1 : ℂ) ^ (zDotVal p q.X + zDotVal q p.X) = -1 := by
    have hmod : (zDotVal p q.X + zDotVal q p.X) % 2 = 1 % 2 := by
      have hc : ((zDotVal p q.X + zDotVal q p.X : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) := by
        rw [omega_natCast, h, Nat.cast_one]
      exact (ZMod.natCast_eq_natCast_iff _ _ 2).mp hc
    rw [neg_one_pow_eq_of_mod_two_eq hmod, pow_one]
  rw [hodd, neg_one_smul]

/-- **Born collapse, off-stabilizer case.** For a *full* stabilizer (`L` a Lagrangian) and `Q ∉ L`,
the expectation vanishes: an anticommuting stabilizer `g` gives
`⟨ψ,H(Q)ψ⟩ = ⟨ψ, g H(Q) g ψ⟩ = −⟨ψ,H(Q)ψ⟩`. -/
theorem expectation_notMem (S : SignedStab n) (hS : IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) (ψ : QState n)
    (hstab : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {Q : Pauli n} (hQ : Q ∉ S.L) :
    expectation ψ Q = 0 := by
  obtain ⟨M, hM, hMQ⟩ := exists_anticommuting_of_not_mem_full hS hRank hQ
  have hanti : pauliHermitian M ∘ₗ pauliHermitian Q = -(pauliHermitian Q ∘ₗ pauliHermitian M) :=
    pauliHermitian_anticomm hMQ
  have hsgr : (starRingEnd ℂ) (S.sign M) = S.sign M := by
    rcases mul_self_eq_one_iff.mp (sign_mul_self S hM) with h | h <;> rw [h] <;> simp
  set G := S.sign M • pauliHermitian M with hG
  have hGψ : G ψ = ψ := hstab M hM
  have hGsym : ∀ x y : QState n, inner ℂ (G x) y = inner ℂ x (G y) := by
    intro x y
    simp only [hG, LinearMap.smul_apply, inner_smul_left, inner_smul_right, hsgr]
    rw [pauliHermitian_isSymmetric M x y]
  have hGHG : G ∘ₗ pauliHermitian Q ∘ₗ G = -(pauliHermitian Q) := by
    simp only [hG, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    rw [sign_mul_self S hM, one_smul, ← LinearMap.comp_assoc, hanti, LinearMap.neg_comp,
      LinearMap.comp_assoc, pauliHermitian_sq, LinearMap.comp_id]
  have e1 : inner ℂ ψ ((G ∘ₗ pauliHermitian Q ∘ₗ G) ψ) = expectation ψ Q := by
    change inner ℂ ψ ((G ∘ₗ pauliHermitian Q ∘ₗ G) ψ) =inner ℂ ψ (pauliHermitian Q ψ)
    simp only [LinearMap.comp_apply, hGψ]
    rw [← hGsym, hGψ]
  have e2 : inner ℂ ψ ((G ∘ₗ pauliHermitian Q ∘ₗ G) ψ) = - expectation ψ Q := by
    change inner ℂ ψ ((G ∘ₗ pauliHermitian Q ∘ₗ G) ψ) =- inner ℂ ψ (pauliHermitian Q ψ)
    rw [hGHG, LinearMap.neg_apply, inner_neg_right]
  have key : expectation ψ Q = - expectation ψ Q := e1.symm.trans e2
  have h2x : (2 : ℂ) * expectation ψ Q = 0 := by rw [two_mul]; nth_rewrite 2 [key]; ring
  exact (mul_eq_zero.mp h2x).resolve_left two_ne_zero

-- Born collapse: for a stabilizer state `ψ` of a full signed stabilizer `(L, χ)`, the
-- expectation of the Hermitian Pauli `Q` is the character value `χ(Q)` if `Q ∈ L`, else `0`.
open Classical in
theorem expectation_eq_eval (S : SignedStab n) (hS : IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) (ψ : QState n) (hψ : ‖ψ‖ = 1)
    (hstab : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) (Q : Pauli n) :
    expectation ψ Q = if Q ∈ S.L then S.sign Q else 0 := by
  by_cases hQ : Q ∈ S.L
  · rw [if_pos hQ]; exact expectation_mem S ψ hψ hstab hQ
  · rw [if_neg hQ]; exact expectation_notMem S hS hRank ψ hstab hQ

/-! ## Born probability (selective measurement) -/

/-- The selective projector `Π_{Q,ε} = ½(id + ε·H(Q))` onto the `ε`-eigenspace of `H(Q)`. -/
noncomputable def bornProjector (Q : Pauli n) (ε : ℂ) : QState n →ₗ[ℂ] QState n :=
  (2⁻¹ : ℂ) • (LinearMap.id + ε • pauliHermitian Q)

/-- The Born probability of outcome `ε` for measuring `H(Q)` in state `ψ`: the expectation
`⟨ψ, Π_{Q,ε} ψ⟩` of the projector (equals `‖Π_{Q,ε} ψ‖²` for the orthogonal projection). -/
noncomputable def bornProb (ψ : QState n) (Q : Pauli n) (ε : ℂ) : ℂ :=
  inner ℂ ψ (bornProjector Q ε ψ)

/-- `bornProb ψ Q ε = ½(⟨ψ,ψ⟩ + ε·⟨ψ,H(Q)ψ⟩)`. -/
theorem bornProb_eq (ψ : QState n) (Q : Pauli n) (ε : ℂ) :
    bornProb ψ Q ε = 2⁻¹ * (inner ℂ ψ ψ + ε * expectation ψ Q) := by
  unfold bornProb bornProjector expectation
  rw [LinearMap.smul_apply, inner_smul_right, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, inner_add_right, inner_smul_right]

-- **Born dichotomy (corollary of Born collapse).** For a stabilizer state, the measurement of
-- `H(Q)` has `bornProb = ½(1 + ε·χ(Q))` when `Q ∈ L` (so `±1`-deterministic for `ε = ±χ(Q)`)
-- and `½` when `Q ∉ L` (uniform).
open Classical in
theorem bornProb_eq_eval (S : SignedStab n) (hS : IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) (ψ : QState n) (hψ : ‖ψ‖ = 1)
    (hstab : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) (Q : Pauli n) (ε : ℂ) :
    bornProb ψ Q ε = 2⁻¹ * (1 + ε * (if Q ∈ S.L then S.sign Q else 0)) := by
  have hnorm : (inner ℂ ψ ψ : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  rw [bornProb_eq, expectation_eq_eval S hS hRank ψ hψ hstab Q, hnorm]

end FTQCLib.Hilbert

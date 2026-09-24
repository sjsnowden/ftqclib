/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.PauliCondition
import FTQCLib.Gates.Clifford

set_option linter.unusedSectionVars false

/-! # Gottesman–Knill: closure of the Lagrangian Grassmannian

The structural form of the Gottesman–Knill theorem in our algebraic-
symplectic framework: the Lagrangian Grassmannian
`Lag(n) ⊂ Gr(n, Pauli n)` — the set of full-rank isotropic subspaces
of `Pauli n` — is closed under

* the action of the Clifford group `Sp(2n, F₂)` on `Pauli n`, and
* the Pauli-conditioning operation `pauliCondition S Q`.

These are the two operations that arise in the standard "stabilizer
circuit" picture (Clifford gates + Pauli measurements). The closure
theorems here are stated and proved entirely on the side of the
F₂-symplectic structure on `Pauli n`; no state vectors, no probability
distributions, no measurement outcomes.

This file proves:

* `clifford_preserves_isStabilizer` — Cliffords preserve isotropy.
* `clifford_preserves_finrank` — Cliffords preserve `finrank`
  (Lagrangian to Lagrangian).
* `pauliCondition_preserves_isStabilizer` — re-export of
  `pauliCondition_isStabilizer` from `PauliCondition.lean`.
* `pauliCondition_preserves_finrank` — re-export of
  `pauliCondition_finrank`.

The composite `gottesman_knill_lagrangian_closure` packages the two
operations into a single statement: any composition of Clifford
actions and Pauli-conditioning steps applied to a Lagrangian stays
inside `Lag(n)`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli FTQCLib.Gates Module

variable {n : ℕ}

/-! ## Clifford closure -/

/-- Cliffords preserve the isotropy property of a stabilizer subspace.
For any Clifford `U : Pauli n ≃ₗ[ZMod 2] Pauli n` and any stabilizer
subspace `S`, the image `S.map U` is again a stabilizer subspace.

Proof: Clifford preserves `omegaBilin`, so the isotropy condition
`omega p q = 0` for `p, q ∈ S` transfers to `omega (U p) (U q) = 0`
for `U p, U q ∈ S.map U`. -/
theorem clifford_preserves_isStabilizer
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    {U : FTQCLib.Pauli n ≃ₗ[ZMod 2] FTQCLib.Pauli n} (hU : IsClifford U) :
    IsStabilizer (S.map U.toLinearMap) := by
  intro p hp q hq
  -- p ∈ S.map U means ∃ p₀ ∈ S, U p₀ = p; same for q.
  obtain ⟨p₀, hp₀_mem, hp₀_eq⟩ := hp
  obtain ⟨q₀, hq₀_mem, hq₀_eq⟩ := hq
  subst hp₀_eq
  subst hq₀_eq
  -- Use the Clifford property: omegaBilin (U p₀) (U q₀) = omegaBilin p₀ q₀.
  have h_pres := hU p₀ q₀
  -- omega and omegaBilin agree on application.
  change omega (U p₀) (U q₀) = 0
  have h_omega_eq : omega (U p₀) (U q₀) = omega p₀ q₀ := h_pres
  rw [h_omega_eq]
  exact hS p₀ hp₀_mem q₀ hq₀_mem

/-- Cliffords preserve `finrank` of a stabilizer subspace. For a
Lagrangian `S` with `finrank S = n`, the image `S.map U` is again
Lagrangian: `finrank (S.map U) = n`.

Proof: a linear equivalence preserves `finrank` on submodules
(`Submodule.finrank_map_linearEquiv`). -/
theorem clifford_preserves_finrank
    (S : Submodule (ZMod 2) (FTQCLib.Pauli n))
    (U : FTQCLib.Pauli n ≃ₗ[ZMod 2] FTQCLib.Pauli n) :
    finrank (ZMod 2) (S.map U.toLinearMap) = finrank (ZMod 2) S := by
  exact (Submodule.equivMapOfInjective U.toLinearMap U.injective S).finrank_eq.symm

/-! ## Pauli-conditioning closure (re-exports from PauliCondition) -/

/-- Pauli conditioning preserves the stabilizer property. (Re-export
of `pauliCondition_isStabilizer` from `FTQCLib/Stabilizer/PauliCondition.lean`
for use in the Gottesman–Knill statement.) -/
theorem pauliCondition_preserves_isStabilizer
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (Q : FTQCLib.Pauli n) :
    IsStabilizer (pauliCondition S Q) :=
  pauliCondition_isStabilizer hS Q

/-- Pauli conditioning preserves the Lagrangian property. (Re-export
of `pauliCondition_finrank`.) -/
theorem pauliCondition_preserves_finrank
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (hRank : finrank (ZMod 2) S = n) (Q : FTQCLib.Pauli n) :
    finrank (ZMod 2) (pauliCondition S Q) = n :=
  pauliCondition_finrank hS hRank Q

/-! ## Combined Gottesman–Knill statement -/

/-- **Gottesman–Knill, Lagrangian closure form.** Both fundamental
operations — Clifford action and Pauli conditioning — preserve the
Lagrangian property of a stabilizer subspace. This is the algebraic
core of the classical Gottesman–Knill theorem (Aaronson–Gottesman 2004,
Gottesman 1998), stated and proved entirely in the F₂-symplectic
structure on `Pauli n`. -/
theorem gottesman_knill_lagrangian_closure :
    -- (i) Clifford action preserves stabilizer + finrank
    (∀ (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) (U : FTQCLib.Pauli n ≃ₗ[ZMod 2] FTQCLib.Pauli n),
      IsStabilizer S → IsClifford U →
        IsStabilizer (S.map U.toLinearMap) ∧
        finrank (ZMod 2) (S.map U.toLinearMap) = finrank (ZMod 2) S)
    ∧
    -- (ii) Pauli conditioning preserves stabilizer + Lagrangian finrank
    (∀ (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) (Q : FTQCLib.Pauli n),
      IsStabilizer S →
        IsStabilizer (pauliCondition S Q) ∧
        (finrank (ZMod 2) S = n → finrank (ZMod 2) (pauliCondition S Q) = n)) := by
  refine ⟨?_, ?_⟩
  · intro S U hS hU
    exact ⟨clifford_preserves_isStabilizer hS hU, clifford_preserves_finrank S U⟩
  · intro S Q hS
    refine ⟨pauliCondition_preserves_isStabilizer hS Q, ?_⟩
    intro hRank
    exact pauliCondition_preserves_finrank hS hRank Q

/-! ## Clifford-equivariance of Pauli conditioning -/

/-- The ω-orthogonal complement commutes with the image of a Clifford
isomorphism: for any Clifford `U` and any subspace `W ⊆ Pauli n`,

  `(W.map U).orthogonal omegaBilin = (W.orthogonal omegaBilin).map U`.

This is the structural fact that ω-preserving isomorphisms transport
orthogonality. Used in the proof of `pauliCondition_map_of_clifford`. -/
private theorem orthogonal_map_of_clifford
    {U : FTQCLib.Pauli n ≃ₗ[ZMod 2] FTQCLib.Pauli n} (hU : IsClifford U)
    (W : Submodule (ZMod 2) (FTQCLib.Pauli n)) :
    LinearMap.BilinForm.orthogonal omegaBilin (W.map U.toLinearMap) =
      (LinearMap.BilinForm.orthogonal omegaBilin W).map U.toLinearMap := by
  ext p
  constructor
  · intro hp
    -- p ⊥ U w for all w ∈ W. Take q = U.symm p; then U q = p and q ⊥ w for all w.
    refine ⟨U.symm p, ?_, U.apply_symm_apply p⟩
    intro w hw
    -- Need: omegaBilin w (U.symm p) = 0.
    change omegaBilin w (U.symm p) = 0
    have h_pres : omegaBilin (U w) (U (U.symm p)) = omegaBilin w (U.symm p) := hU w (U.symm p)
    rw [U.apply_symm_apply] at h_pres
    have hUw_mem : U w ∈ W.map U.toLinearMap := ⟨w, hw, rfl⟩
    have hp_orth : omegaBilin (U w) p = 0 := hp (U w) hUw_mem
    rw [← h_pres]
    exact hp_orth
  · rintro ⟨q, hq_mem, rfl⟩
    intro y hy
    -- y ∈ W.map U.toLinearMap, so ∃ w ∈ W, U w = y.
    obtain ⟨w, hw, rfl⟩ := hy
    -- Need: omegaBilin (U w) (U q) = 0. Use ω-preservation + hq_mem.
    change omegaBilin (U w) (U q) = 0
    have h_pres : omegaBilin (U w) (U q) = omegaBilin w q := hU w q
    rw [h_pres]
    have hwq : omegaBilin w q = 0 := hq_mem w hw
    exact hwq

/-- **Clifford-equivariance of Pauli conditioning.** For any Clifford
`U : Pauli n ≃ₗ Pauli n`, any stabilizer subspace `S`, and any Pauli `Q`:

  `pauliCondition (S.map U) (U Q) = (pauliCondition S Q).map U`.

In words: Clifford action commutes with Pauli conditioning. As a
special case, taking `U = phaseAt i` (the symplectic representation
of conjugation by the phase gate `S_i`, which sends `paulix i ↦ paulix i + pauliz i`),
this exhibits Y-type conditioning as a Clifford-conjugate of X-type
conditioning. Combined with `clifford_preserves_isStabilizer`, this
shows that X-type + Z-type conditioning, together with the Clifford
group, generate all Pauli conditioning operations. -/
theorem pauliCondition_map_of_clifford
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    {U : FTQCLib.Pauli n ≃ₗ[ZMod 2] FTQCLib.Pauli n} (hU : IsClifford U)
    (Q : FTQCLib.Pauli n) :
    pauliCondition (S.map U.toLinearMap) (U Q) =
      (pauliCondition S Q).map U.toLinearMap := by
  classical
  by_cases hQS : Q ∈ S
  · have hUQS : U Q ∈ S.map U.toLinearMap := ⟨Q, hQS, rfl⟩
    rw [pauliCondition_of_mem hUQS, pauliCondition_of_mem hQS]
  · have hUQS : U Q ∉ S.map U.toLinearMap := by
      rintro ⟨Q', hQ'_mem, hQ'_eq⟩
      have hQQ' : Q = Q' := U.injective hQ'_eq.symm
      exact hQS (hQQ' ▸ hQ'_mem)
    rw [pauliCondition_of_not_mem hUQS, pauliCondition_of_not_mem hQS]
    -- Span step: span {U Q} = (span {Q}).map U.
    have hSpan :
        Submodule.span (ZMod 2) ({U Q} : Set (FTQCLib.Pauli n)) =
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))).map U.toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp
    rw [hSpan]
    -- Orthogonal step: (span {Q} .map U)^⊥ = (span {Q})^⊥ .map U.
    have hOrth := orthogonal_map_of_clifford hU
      (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)))
    rw [hOrth]
    -- Intersection step: (S.map U) ⊓ (X.map U) = (S ⊓ X).map U for U injective.
    rw [← Submodule.map_inf _ U.injective]
    -- Sum step: (A.map U) ⊔ (B.map U) = (A ⊔ B).map U.
    rw [← Submodule.map_sup]

end FTQCLib.Stabilizer

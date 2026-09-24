/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.StabilizerEquiv
import FTQCLib.Hilbert.LemSpan
import FTQCLib.Hilbert.Separation

/-! # `𝒮 ≃ 𝒪`, the faithful-representation core

This file assembles the operational fragment `𝒪` as a faithful representation of the symplectic
theory `𝒮`, on the common carrier `X` = pure stabilizer density operators `≅ (L, χ)` (the
stabilizer correspondence). The four ingredients, each established elsewhere, are:

* **object bijection** — `(L, χ) ↦ stabProjector` is injective (`stabProjector_inj`) and lands in
  the pure stabilizer densities (definitional surjectivity onto `X`);
* **`𝒪`-faithfulness** — a channel is determined by its action on `X`
  (`linearMap_ext_of_pureStabDensity`, via the pure-state span);
* **Clifford ↔ `Φ`** — conjugation by a Clifford `U` is the symplectic action `Φ(U)` on objects
  (`qConj_stabProjector`);
* **deterministic Lüders** — for `Q ∈ L` the correct-outcome Born projector fixes the object
  (`bornProjector_comp_stabProjector_self`).

The faithfulness lever is the **pure**-state span `pureStabDensity_span_top`, which is
strictly stronger than the Born-effect span used in `Separation.lean` (effects are not pure for
`n > 1`). -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli

variable {n : ℕ}

/-! ## `𝒪`-faithfulness via the pure-state span

A linear functional on channels is pinned down by its values on the pure stabilizer densities — the
carrier `X`. This is the separating property a *faithful* operational fragment requires, and it uses
the pure-state span (`pureStabDensity_span_top`), not the weaker effect span. -/

/-- **Operational faithfulness on the pure-state carrier.** A linear map out of
`End ℂ (QState n)` is determined by its values on the pure stabilizer densities `X`: two maps (in
particular two channels `End → End`, or two states `End → ℂ`) agreeing on every `IsPureStabDensity`
operator are equal. This is the faithfulness lever of the `𝒮 ≃ 𝒪` correspondence, resting on the
pure-state span `pureStabDensity_span_top`. -/
theorem linearMap_ext_of_pureStabDensity {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {F G : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] M}
    (h : ∀ ρ : QState n →ₗ[ℂ] QState n, IsPureStabDensity ρ → F ρ = G ρ) : F = G :=
  LinearMap.ext_on pureStabDensity_span_top (fun ρ hρ => h ρ hρ)

/-! ## The `𝒮 ≃ 𝒪` faithful-representation core

The theorem below bundles the four ingredients of the operational correspondence on the carrier
`X` = pure stabilizer densities. -/

/-- **`𝒮 ≃ 𝒪`: the faithful-representation core.** The operational fragment `𝒪`
faithfully represents the symplectic theory `𝒮` on the carrier `X` = pure stabilizer densities,
witnessed by four properties:

* **(i) object bijection** — `(L, χ) ↦ stabProjector` is injective (distinct signed Lagrangians
  give distinct densities) and surjects onto `X` (every pure stabilizer density is a
  `stabProjector S`);
* **(ii) `𝒪`-faithfulness** — a channel `End (QState n) → End (QState n)` is determined by its
  action on `X` (the separating pure-state span);
* **(iii) Clifford ↔ `Φ`** — conjugating a stabilizer projector by a Clifford `U` realizes the
  symplectic action `Φ(U)` on objects: `U · Π_S · U⁻¹ = Π_{Φ(U)·S}`;
* **(iv) deterministic Lüders** — for `Q ∈ L` the correct-outcome Born projector fixes the object,
  matching the classical conditioning that leaves `(L, χ)` unchanged.

Faithfulness (ii) is also available polymorphically as the standalone
`linearMap_ext_of_pureStabDensity`. -/
theorem stabilizer_operational_correspondence :
    -- (i) object bijection: injective on signed Lagrangians, and surjective onto `X`.
    (∀ S S' : SignedStab n, stabProjector S = stabProjector S' →
        S.L = S'.L ∧ ∀ p ∈ S.L, S.sign p = S'.sign p)
      ∧ (∀ ρ : QState n →ₗ[ℂ] QState n, IsPureStabDensity ρ →
        ∃ S : SignedStab n, ρ = stabProjector S)
    -- (ii) `𝒪`-faithfulness on the carrier `X` (channels are pinned down by their action on `X`).
      ∧ (∀ F G : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] (QState n →ₗ[ℂ] QState n),
        (∀ ρ : QState n →ₗ[ℂ] QState n, IsPureStabDensity ρ → F ρ = G ρ) → F = G)
    -- (iii) Clifford conjugation realizes the symplectic action `Φ` on objects.
      ∧ (∀ {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U) (S : SignedStab n),
        qConj U (stabProjector S) = stabProjector (cliffordAction hU S))
    -- (iv) deterministic Lüders: the correct-outcome Born projector fixes the object.
      ∧ (∀ (S : SignedStab n) {Q : Pauli n}, Q ∈ S.L →
        bornProjector Q (S.sign Q) ∘ₗ stabProjector S = stabProjector S) :=
  ⟨fun _ _ h => stabProjector_inj h,
    fun _ ⟨S, _, _, hρ⟩ => ⟨S, hρ⟩,
    fun _ _ h => linearMap_ext_of_pureStabDensity h,
    fun hU S => qConj_stabProjector hU S,
    fun S _ hQ => bornProjector_comp_stabProjector_self S hQ⟩

end FTQCLib.Hilbert

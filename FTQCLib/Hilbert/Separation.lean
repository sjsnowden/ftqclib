/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.StabilizerState
import FTQCLib.Hilbert.BornCollapse

/-! # The separation lemma — toward `pure stabilizer densities span Mₙ(ℂ)`

The first step is **trace-orthogonality** of the Hermitian Paulis:
`tr(H(q) ∘ H(p)) = 2ⁿ · δ_{p,q}`. This is the Hilbert–Schmidt orthogonality of the Pauli basis;
combined with a dimension count it shows the `4ⁿ` Hermitian Paulis are linearly independent, hence a
basis of `End ℂ (QState n)`, which is the engine of the separation lemma. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-- Over `𝔽₂`, every Pauli is its own additive inverse. -/
private theorem add_self_pauli (p : Pauli n) : p + p = 0 := by
  apply Pauli.ext
  · funext i
    change p.X i + p.X i = (0 : Pauli n).X i
    rw [X_zero, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  · funext i
    change p.Z i + p.Z i = (0 : Pauli n).Z i
    rw [Z_zero, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _

/-- The complex dimension of `QState n` is `2ⁿ`. -/
private theorem finrank_qstate : Module.finrank ℂ (QState n) = 2 ^ n := by
  change Module.finrank ℂ (EuclideanSpace ℂ (Fin n → ZMod 2)) = 2 ^ n
  rw [finrank_euclideanSpace, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The trace of the identity on `QState n` is the dimension `2ⁿ`. -/
private theorem trace_id_qstate :
    LinearMap.trace ℂ (QState n) LinearMap.id = (2 : ℂ) ^ n := by
  rw [LinearMap.trace_id, finrank_qstate]
  push_cast
  ring

/-- **Trace-orthogonality of the Hermitian Paulis** (Hilbert–Schmidt inner product):
`tr(H(q) ∘ H(p)) = 2ⁿ` if `p = q`, else `0`. -/
theorem trace_pauliHermitian_mul (p q : Pauli n) :
    LinearMap.trace ℂ (QState n) (pauliHermitian q ∘ₗ pauliHermitian p)
      = if p = q then (2 : ℂ) ^ n else 0 := by
  by_cases h : p = q
  · subst h
    rw [pauliHermitian_sq, trace_id_qstate, if_pos rfl]
  · have hpq_ne : p + q ≠ 0 := by
      intro hpq
      apply h
      calc p = p + (q + q) := by rw [add_self_pauli, add_zero]
        _ = (p + q) + q := by rw [add_assoc]
        _ = q := by rw [hpq, zero_add]
    rw [if_neg h, pauliHermitian_mul_phase, map_smul, pauliHermitian_trace, if_neg hpq_ne,
      smul_zero]

/-- **The Hermitian Paulis are linearly independent.** Pair `∑ g p · H(p) = 0` against `H(q)` with
the trace form: `tr(H(q) ∘ ∑ g p · H(p)) = g q · 2ⁿ = 0`, and `2ⁿ ≠ 0` forces each coefficient to
vanish. There are `|Pauli n| = 4ⁿ = dim (End ℂ (QState n))` of them, so they form a basis. -/
theorem linearIndependent_pauliHermitian :
    LinearIndependent ℂ (fun p : Pauli n => pauliHermitian p) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  -- Distribute `H(q) ∘ ·` over the finite sum.
  have comp_sum : ∀ s : Finset (Pauli n),
      pauliHermitian q ∘ₗ (∑ p ∈ s, g p • pauliHermitian p)
        = ∑ p ∈ s, g p • (pauliHermitian q ∘ₗ pauliHermitian p) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a t ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.comp_add, LinearMap.comp_smul, ih]
  have htr : LinearMap.trace ℂ (QState n)
      (∑ p, g p • (pauliHermitian q ∘ₗ pauliHermitian p)) = 0 := by
    rw [← comp_sum Finset.univ, hg, LinearMap.comp_zero, map_zero]
  rw [map_sum] at htr
  simp only [map_smul, smul_eq_mul, trace_pauliHermitian_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at htr
  rcases mul_eq_zero.mp htr with h | h
  · exact h
  · exact absurd h h2n

/-- Non-vacuity: distinct Paulis give distinct operators (`p ↦ H(p)` is injective). Rules out a
degenerate Born layer where every Pauli collapses to the same operator. -/
theorem pauliHermitian_injective :
    Function.Injective (fun p : Pauli n => pauliHermitian p) :=
  linearIndependent_pauliHermitian.injective

/-- **Pauli completeness:** the `4ⁿ` Hermitian Paulis span all of `End ℂ (QState n)`.
Linear independence plus the dimension count `|Pauli n| = 4ⁿ = (2ⁿ)² = dim (End ℂ (QState n))` makes
them a basis; in particular every operator — hence every channel's action — is determined by its
behaviour on the Pauli operators (the separation property). -/
theorem pauliHermitian_span_top :
    Submodule.span ℂ (Set.range (fun p : Pauli n => pauliHermitian p)) = ⊤ := by
  apply linearIndependent_pauliHermitian.span_eq_top_of_card_eq_finrank'
  rw [Module.finrank_linearMap, finrank_qstate]
  have e : Pauli n ≃ ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
    { toFun := fun p => (p.X, p.Z)
      invFun := fun xz => ⟨xz.1, xz.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Separation / channel extensionality.** A linear map out of `End ℂ (QState n)` is determined by
its values on the Hermitian Paulis: two maps (in particular, two channels `End → End`, or two states
`End → ℂ`) that agree on every `H(p)` are equal. This is the operational content of Pauli
completeness — it is what makes the operational fragment faithful. -/
theorem linearMap_ext_of_pauliHermitian {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {Φ Ψ : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] M}
    (h : ∀ p, Φ (pauliHermitian p) = Ψ (pauliHermitian p)) : Φ = Ψ :=
  LinearMap.ext_on_range pauliHermitian_span_top h

/-- Each Hermitian Pauli is a difference of the two Lüders measurement effects of `H(p)`:
`H(p) = ½(id + H(p)) − ½(id − H(p))`. -/
theorem pauliHermitian_eq_bornProjector_sub (p : Pauli n) :
    pauliHermitian p = bornProjector p 1 - bornProjector p (-1) := by
  simp only [bornProjector]
  module

/-- **The measurement effects span `End ℂ (QState n)`.** Since each Pauli is a difference of Born
projectors (`pauliHermitian_eq_bornProjector_sub`), the operationally accessible effects
`½(id ± H(Q))` already span the whole operator space — the operational form of separation. -/
theorem bornProjector_span_top :
    Submodule.span ℂ (Set.range (fun pe : Pauli n × ℂ => bornProjector pe.1 pe.2)) = ⊤ := by
  have hle : Submodule.span ℂ (Set.range (fun p : Pauli n => pauliHermitian p))
      ≤ Submodule.span ℂ (Set.range (fun pe : Pauli n × ℂ => bornProjector pe.1 pe.2)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    change pauliHermitian p ∈ _
    rw [pauliHermitian_eq_bornProjector_sub]
    exact Submodule.sub_mem _
      (Submodule.subset_span (Set.mem_range_self (p, 1)))
      (Submodule.subset_span (Set.mem_range_self (p, -1)))
  exact le_antisymm le_top (le_of_eq_of_le pauliHermitian_span_top.symm hle)

/-- **Operational faithfulness.** A linear map out of `End ℂ (QState n)` is determined by its values
on the Born measurement effects `½(id ± H(Q))`: two channels (or states) agreeing on every
`bornProjector p ε` are equal — the separation a faithful operational fragment uses. -/
theorem linearMap_ext_of_bornProjector {M : Type*} [AddCommMonoid M] [Module ℂ M]
    {Φ Ψ : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] M}
    (h : ∀ (p : Pauli n) (ε : ℂ), Φ (bornProjector p ε) = Ψ (bornProjector p ε)) : Φ = Ψ :=
  LinearMap.ext_on_range bornProjector_span_top (fun pe => h pe.1 pe.2)

/-! ## Pure stabilizer **density** operators

The stronger spanning statement: the **pure** stabilizer density operators (rank-1
`stabProjector` of a *full* Lagrangian) span `End ℂ (QState n)`. This is *stronger than* the
effects span above (`bornProjector p ε` is rank-`2^{n-1}`, not pure, for `n>1`). The reduction
below turns it into a per-Pauli membership: every `H(p)` is a combination of pure stabilizer
states — for `n=1` the four states `½(I±Z), ½(I+X), ½(I+Y)`, and in general a twisted-character
sum over a Lagrangian `L ∋ p` (`H(p) = ±∑_χ χ(p)·stabProjector(L,χ)`, by character
orthogonality). The membership and the spanning theorem `pureStabDensity_span_top` are in
`LemSpan.lean`. -/

/-- A **pure stabilizer density operator**: the (rank-1) `stabProjector` of a full Lagrangian
stabilizer state — `S.L` isotropic with `dim = n`. -/
def IsPureStabDensity (ρ : QState n →ₗ[ℂ] QState n) : Prop :=
  ∃ S : SignedStab n,
    FTQCLib.Stabilizer.IsStabilizer S.L ∧ Module.finrank (ZMod 2) S.L = n ∧ ρ = stabProjector S

/-- **Reduction for the spanning lemma.** The pure stabilizer densities span `End ℂ (QState n)`
once every
Hermitian Pauli lies in their span — then `pauliHermitian_span_top` finishes. -/
theorem pureStabDensity_span_top_of_pauliHermitian_mem
    (h : ∀ p : Pauli n, pauliHermitian p ∈ Submodule.span ℂ {ρ | IsPureStabDensity (n := n) ρ}) :
    Submodule.span ℂ {ρ : QState n →ₗ[ℂ] QState n | IsPureStabDensity ρ} = ⊤ := by
  have hle : Submodule.span ℂ (Set.range (fun p : Pauli n => pauliHermitian p))
      ≤ Submodule.span ℂ {ρ | IsPureStabDensity (n := n) ρ} := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact h p
  exact le_antisymm le_top (le_of_eq_of_le pauliHermitian_span_top.symm hle)

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Separation
import FTQCLib.Hilbert.AffineSymplectic

/-! # The stabilizer correspondence: object bijection + generator correspondence

The stabilizer correspondence exhibits the operational fragment `𝒪` as a faithful representation
of the symplectic theory `𝒮`, via two monoid actions on the common carrier `X` = pure stabilizer
density operators `≅ (L, χ)`. This file builds the **content** of that correspondence — the object
bijection and the generator correspondence — which is unconditional (it uses neither the
Clifford–symplectic lift, nor a channel category, nor the pure-state span). The categorical
equivalence is in `CategoricalEquivalence.lean`, and the faithfulness statement in
`StabilizerTheory.lean`.

## Object bijection

`stabProjector` is injective on `(L, χ|L)`: distinct signed Lagrangians give distinct density
operators. Combined with the density-operator certification (`stabProjector_idem`,
`stabProjector_isSelfAdjoint`, `stabProjector_trace`), the map `(L, χ) ↦ stabProjector` is a
bijection onto the pure stabilizer densities — the object half of the `𝒮 ≃ 𝒪` carrier
identification. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli

open scoped Classical

variable {n : ℕ}

/-- The coefficient of `H(p)` in `stabProjector S` against the Hermitian-Pauli basis: `2⁻ⁿ·sign(p)`
on `L`, else `0`. -/
noncomputable def stabCoeff (S : SignedStab n) (p : Pauli n) : ℂ :=
  if p ∈ S.L then (2 ^ n : ℂ)⁻¹ * S.sign p else 0

/-- `stabProjector` expanded over the full Hermitian-Pauli basis: `Π = ∑_p stabCoeff S p • H(p)`
(the off-`L` terms vanish, so the sum over `L` equals the sum over all Paulis). -/
theorem stabProjector_eq_sum_univ (S : SignedStab n) :
    stabProjector S = ∑ p : Pauli n, stabCoeff S p • pauliHermitian p := by
  have hzero : ∀ p ∈ (Finset.univ : Finset (Pauli n)),
      p ∉ (Set.toFinite (S.L : Set (Pauli n))).toFinset →
      stabCoeff S p • pauliHermitian p = 0 := by
    intro p _ hp
    rw [Set.Finite.mem_toFinset, SetLike.mem_coe] at hp
    simp only [stabCoeff, if_neg hp, zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  unfold stabProjector
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Set.Finite.mem_toFinset, SetLike.mem_coe] at hp
  simp only [stabCoeff, if_pos hp, mul_smul]

/-- The coefficient is nonzero exactly on `L`: `stabCoeff S p ≠ 0 ↔ p ∈ L` (signs are `±1 ≠ 0`). -/
theorem stabCoeff_ne_zero_iff (S : SignedStab n) (p : Pauli n) :
    stabCoeff S p ≠ 0 ↔ p ∈ S.L := by
  simp only [stabCoeff]
  constructor
  · intro h
    by_contra hp
    rw [if_neg hp] at h
    exact h rfl
  · intro hp
    rw [if_pos hp]
    have hs : S.sign p ≠ 0 := by
      intro h0
      have hsq := sign_mul_self S hp
      rw [h0, mul_zero] at hsq
      exact zero_ne_one hsq
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero n two_ne_zero)) hs

/-- Equal projectors have equal full-basis coefficients (the Hermitian Paulis are independent). -/
theorem stabCoeff_eq_of_proj_eq {S S' : SignedStab n} (h : stabProjector S = stabProjector S')
    (p : Pauli n) : stabCoeff S p = stabCoeff S' p := by
  have h2 : ∑ q : Pauli n, stabCoeff S q • pauliHermitian q
          = ∑ q : Pauli n, stabCoeff S' q • pauliHermitian q := by
    rw [← stabProjector_eq_sum_univ, ← stabProjector_eq_sum_univ, h]
  have hsub : ∑ q : Pauli n, (stabCoeff S q - stabCoeff S' q) • pauliHermitian q = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, h2, sub_self]
  have hli := (Fintype.linearIndependent_iff.mp linearIndependent_pauliHermitian)
    (fun q => stabCoeff S q - stabCoeff S' q) hsub p
  exact sub_eq_zero.mp hli

/-- **Object-bijection injectivity.** Distinct signed Lagrangians give distinct projectors:
`stabProjector S = stabProjector S'` forces `S.L = S'.L` and `S.sign = S'.sign` on `L`. Hence
`(L, χ|L) ↦ stabProjector` is injective — the object half of the `𝒮 ≃ 𝒪` carrier bijection. -/
theorem stabProjector_inj {S S' : SignedStab n} (h : stabProjector S = stabProjector S') :
    S.L = S'.L ∧ ∀ p ∈ S.L, S.sign p = S'.sign p := by
  have hcoeff := stabCoeff_eq_of_proj_eq h
  have hL : S.L = S'.L := by
    apply SetLike.ext
    intro p
    rw [← stabCoeff_ne_zero_iff S p, ← stabCoeff_ne_zero_iff S' p, hcoeff p]
  refine ⟨hL, fun p hp => ?_⟩
  have hp' : p ∈ S'.L := hL ▸ hp
  have hc := hcoeff p
  simp only [stabCoeff, if_pos hp, if_pos hp'] at hc
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero n two_ne_zero)) hc

/-! ## Generator correspondence I: Clifford conjugation ↔ Φ

The Heisenberg picture (Gottesman 1998: evolution of *operators*, `Cl_n = N(Pauli)`): conjugating a
Pauli observable by a Clifford `U` sends it to a signed Pauli at the `Φ(U)`-transformed position,
`U·H(p)·U⁻¹ = μ(p)·H(g p)` with `g = cliffordToSymplecticFun hU` and `μ(p) = ±1`. This is the
operator-level engine of "conjugation acts as `Φ(U)`" (the Clifford generator of the
correspondence). Conjugation is transported to `QState n` through `toQState`. -/

/-- A Clifford `U` on `QubitSpace n`, transported to `QState n` via `toQState`. -/
noncomputable def qClifford (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : QState n ≃ₗ[ℂ] QState n :=
  (toQState.symm.trans U).trans toQState

@[simp] theorem qClifford_apply (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (ψ : QState n) :
    qClifford U ψ = toQState (U (toQState.symm ψ)) := rfl

@[simp] theorem qClifford_symm_apply (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (ψ : QState n) :
    (qClifford U).symm ψ = toQState (U.symm (toQState.symm ψ)) := rfl

/-- The conjugation channel `A ↦ U A U⁻¹` on `QState n`, for a Clifford `U`. -/
noncomputable def qConj (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (A : QState n →ₗ[ℂ] QState n) :
    QState n →ₗ[ℂ] QState n :=
  (qClifford U).toLinearMap ∘ₗ A ∘ₗ (qClifford U).symm.toLinearMap

theorem qConj_apply (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (A : QState n →ₗ[ℂ] QState n)
    (ψ : QState n) : qConj U A ψ = qClifford U (A ((qClifford U).symm ψ)) := rfl

/-- Conjugation is `ℂ`-linear in the conjugated operator. -/
theorem qConj_smul (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (c : ℂ) (A : QState n →ₗ[ℂ] QState n) :
    qConj U (c • A) = c • qConj U A := by
  simp only [qConj, LinearMap.smul_comp, LinearMap.comp_smul]

/-- Conjugation fixes the identity: `U·id·U⁻¹ = id`. -/
theorem qConj_id (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    qConj U LinearMap.id = LinearMap.id := by
  ext ψ; simp [qConj_apply]

/-- Conjugation is multiplicative: `U·(A∘B)·U⁻¹ = (U·A·U⁻¹)∘(U·B·U⁻¹)`. -/
theorem qConj_comp (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (A B : QState n →ₗ[ℂ] QState n) :
    qConj U (A ∘ₗ B) = qConj U A ∘ₗ qConj U B := by
  ext ψ; simp [qConj_apply, LinearMap.comp_apply]

/-- **Heisenberg transport (raw Pauli).** Conjugating `qPauli p` by a Clifford `U` gives the
symplectic phase times the Pauli at the `Φ(U)`-transformed position:
`U·qPauli(p)·U⁻¹ = phase · qPauli(g p)`. -/
theorem qConj_qPauli {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (p : Pauli n) :
    qConj U (qPauli p)
      = (cliffordToSymplecticPhase hU p : ℂ) • qPauli (cliffordToSymplecticFun hU p) := by
  have hconj : (conjEquiv U (pauliEquiv p)).toLinearMap
      = (cliffordToSymplecticPhase hU p : ℂ) • pauliOperator (cliffordToSymplecticFun hU p) := by
    have h1 : (pauliEquiv p).toLinearMap = ((1 : ℂˣ) : ℂ) • pauliOperator p := by
      ext ψ; simp [pauliEquiv_apply]
    have hcsp := conjEquiv_smul_pauliOperator hU h1
    simpa using hcsp
  apply LinearMap.ext
  intro ψ
  have hc := LinearMap.congr_fun hconj (toQState.symm ψ)
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, pauliEquiv_apply, LinearMap.smul_apply] at hc
  simp only [qConj_apply, qClifford_apply, qClifford_symm_apply, qPauli_apply,
    LinearEquiv.symm_apply_apply, LinearMap.smul_apply]
  rw [hc, map_smul]

/-- The sign picked up when a Clifford conjugates a Hermitian Pauli: `μ(p)` in
`U·H(p)·U⁻¹ = μ(p)·H(g p)`, combining the symplectic phase with the `Iˣᶻ` Hermitian renormalization
at `p` and `g p`. (It is `±1`; see the structural involution argument.) -/
noncomputable def cliffordSign {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (p : Pauli n) : ℂ :=
  (Complex.I) ^ xzWeight p * (cliffordToSymplecticPhase hU p : ℂ)
    * ((Complex.I) ^ xzWeight (cliffordToSymplecticFun hU p))⁻¹

/-- **Heisenberg law (Hermitian Pauli).** Conjugating the Hermitian Pauli `H(p)` by a Clifford `U`
gives a sign times `H` at the `Φ(U)`-transformed position:
`U·H(p)·U⁻¹ = cliffordSign hU p · H(g p)`. This is the operator form of the correspondence's
Clifford generator (Gottesman 1998 Heisenberg picture). -/
theorem qConj_pauliHermitian {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (p : Pauli n) :
    qConj U (pauliHermitian p)
      = cliffordSign hU p • pauliHermitian (cliffordToSymplecticFun hU p) := by
  simp only [pauliHermitian]
  rw [qConj_smul, qConj_qPauli hU, smul_smul, smul_smul]
  congr 1
  rw [cliffordSign, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), mul_one]

/-- **The conjugation sign is `±1`.** `cliffordSign hU p` squares to one: conjugation carries the
involution `H(p)² = id` to `(μ·H(g p))² = μ²·id = id`, forcing `μ² = 1`. This matches `χ`
being a `{±1}`-character — a Clifford sends a stabilizer sign to a stabilizer sign. -/
theorem cliffordSign_mul_self {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (p : Pauli n) : cliffordSign hU p * cliffordSign hU p = 1 := by
  have key : (cliffordSign hU p * cliffordSign hU p) • (LinearMap.id : QState n →ₗ[ℂ] QState n)
      = LinearMap.id := by
    have h1 : qConj U (pauliHermitian p) ∘ₗ qConj U (pauliHermitian p) = LinearMap.id := by
      rw [← qConj_comp, pauliHermitian_sq, qConj_id]
    rwa [qConj_pauliHermitian, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
      pauliHermitian_sq] at h1
  have hfr : (Module.finrank ℂ (QState n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr := congrArg (LinearMap.trace ℂ (QState n)) key
  rw [map_smul, smul_eq_mul, LinearMap.trace_id] at htr
  exact mul_right_cancel₀ hfr (by rw [one_mul]; exact htr)

/-- The conjugation sign of the identity Pauli is `1`: `cliffordSign hU 0 = 1`. The symplectic image
`Φ(0) = 0` (`cliffordToSymplecticFun_zero`) and the phase `cliffordToSymplecticPhase hU 0 = 1`
(uniqueness applied to the trivial witness `conjEquiv U (pauliEquiv 0) = id`), while
`xzWeight 0 = 0`, so all three factors collapse to `1`. -/
theorem cliffordSign_zero {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U) :
    cliffordSign hU 0 = 1 := by
  have hwit : (conjEquiv U (pauliEquiv (0 : Pauli n))).toLinearMap
      = ((1 : ℂˣ) : ℂ) • pauliOperator (0 : Pauli n) := by
    apply LinearMap.ext
    intro ψ
    simp only [conjEquiv_apply, LinearEquiv.coe_coe, pauliEquiv_apply]
    rw [pauliOperator_zero]
    simp only [LinearMap.id_apply, Units.val_one, one_smul]
    rw [LinearEquiv.apply_symm_apply]
  have hphase : (cliffordToSymplecticPhase hU 0 : ℂ) = 1 :=
    (cliffordToSymplecticPhase_unique hU 0 hwit).symm
  have hxz : xzWeight (0 : Pauli n) = 0 := by simp [xzWeight, zDotVal]
  rw [cliffordSign, hphase, cliffordToSymplecticFun_zero, hxz]
  simp only [pow_zero, mul_one, inv_one]

/-- **The conjugation sign is a twisted cocycle.** Conjugation `qConj U` is multiplicative, so the
signs `μ = cliffordSign hU` satisfy a `pauliPhase`-twisted cocycle law tying the Pauli-product
phase at `a, b` to the phase at the `Φ`-images `Φa, Φb`:
`μ(a)·μ(b)·pauliPhase (Φa) (Φb) = μ(a+b)·pauliPhase a b`. This is the sign-bookkeeping that makes
the `cliffordAction` on signed stabilizers well defined (its `valid`). -/
theorem cliffordSign_cocycle {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (a b : Pauli n) :
    cliffordSign hU a * cliffordSign hU b
        * pauliPhase (cliffordToSymplecticFun hU a) (cliffordToSymplecticFun hU b)
      = cliffordSign hU (a + b) * pauliPhase a b := by
  have hcomp := qConj_comp U (pauliHermitian b) (pauliHermitian a)
  rw [pauliHermitian_mul_phase a b, qConj_smul, qConj_pauliHermitian hU, smul_smul,
    cliffordToSymplecticFun_add] at hcomp
  rw [qConj_pauliHermitian hU, qConj_pauliHermitian hU, LinearMap.smul_comp, LinearMap.comp_smul,
    smul_smul] at hcomp
  rw [pauliHermitian_mul_phase (cliffordToSymplecticFun hU a) (cliffordToSymplecticFun hU b),
    smul_smul] at hcomp
  -- Now `hcomp : c1 • H = c2 • H`; extract `c1 = c2` by composing with `H` then tracing.
  have hcomp' := congrArg
    (· ∘ₗ pauliHermitian (cliffordToSymplecticFun hU a + cliffordToSymplecticFun hU b)) hcomp
  simp only [LinearMap.smul_comp, pauliHermitian_sq] at hcomp'
  have hfr : (Module.finrank ℂ (QState n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr := congrArg (LinearMap.trace ℂ (QState n)) hcomp'
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, LinearMap.trace_id] at htr
  have heq := mul_right_cancel₀ hfr htr
  linear_combination -heq

/-! ## Bundling conjugation as a linear map on operators

`qConj U` is `ℂ`-linear in the conjugated operator `A` (it is
`A ↦ qClifford U ∘ A ∘ (qClifford U)⁻¹`, a composition of left- and
right-multiplications). Bundling it as a `LinearMap` lets `map_sum`/`map_smul`
push it through the finite Hermitian-Pauli expansion of `stabProjector`. -/

/-- Conjugation `A ↦ U A U⁻¹` bundled as a `ℂ`-linear endomorphism of `End (QState n)`. -/
noncomputable def qConjₗ (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] (QState n →ₗ[ℂ] QState n) where
  toFun A := qConj U A
  map_add' A B := by
    simp only [qConj, LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c A := by
    simp only [qConj, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply]

@[simp] theorem qConjₗ_apply (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (A : QState n →ₗ[ℂ] QState n) :
    qConjₗ U A = qConj U A := rfl

/-! ## Generator correspondence II: Lüders measurement ↔ conditioning (deterministic case)

For `Q ∈ L` the measurement is deterministic (`H(Q)` acts as the sign `χ(Q)`): the Born
projector `Π_{Q,ε} = ½(id + ε·H(Q))` applied to the state scales it by the outcome probability
`½(1 + ε·χ(Q))` — fixing it when `ε = χ(Q)` (matching `cond_{Q,ε}` leaving `(L,χ)` unchanged) and
annihilating it when `ε = -χ(Q)` (the probability-`0` outcome). The `Q ∉ L` case produces a new
Lagrangian; it is `ludersChannel_stabProjector_notMem` (`MeasurementCollapse.lean`). -/

/-- **Deterministic measurement (left action).** For `Q ∈ L`,
`Π_{Q,ε} · Π_S = ½(1 + ε·χ(Q)) · Π_S`: `H(Q)` absorbs into the stabilizer as the sign `χ(Q)`
(`stabProjector_absorb`), so the projector scales the state by the outcome probability. -/
theorem bornProjector_comp_stabProjector (S : SignedStab n) {Q : Pauli n} (hQ : Q ∈ S.L) (ε : ℂ) :
    bornProjector Q ε ∘ₗ stabProjector S = ((1 + ε * S.sign Q) / 2) • stabProjector S := by
  have hHQ : pauliHermitian Q ∘ₗ stabProjector S = S.sign Q • stabProjector S := by
    have hab := stabProjector_absorb S Q hQ
    rw [LinearMap.smul_comp] at hab
    have hχ := sign_mul_self S hQ
    calc pauliHermitian Q ∘ₗ stabProjector S
        = (S.sign Q * S.sign Q) • (pauliHermitian Q ∘ₗ stabProjector S) := by rw [hχ, one_smul]
      _ = S.sign Q • (S.sign Q • (pauliHermitian Q ∘ₗ stabProjector S)) := by rw [mul_smul]
      _ = S.sign Q • stabProjector S := by rw [hab]
  rw [bornProjector, LinearMap.smul_comp, LinearMap.add_comp, LinearMap.id_comp,
    LinearMap.smul_comp, hHQ, smul_smul]
  module

/-- **Correct outcome** `ε = χ(Q)`: the Born projector fixes the state, matching `cond_{Q,χ(Q)}`
leaving `(L,χ)` unchanged. -/
theorem bornProjector_comp_stabProjector_self (S : SignedStab n) {Q : Pauli n} (hQ : Q ∈ S.L) :
    bornProjector Q (S.sign Q) ∘ₗ stabProjector S = stabProjector S := by
  rw [bornProjector_comp_stabProjector S hQ, sign_mul_self S hQ,
    show ((1 + 1) / 2 : ℂ) = 1 by norm_num, one_smul]

/-- **Wrong outcome** `ε = -χ(Q)`: the Born projector annihilates the state (probability `0`). -/
theorem bornProjector_comp_stabProjector_zero (S : SignedStab n) {Q : Pauli n} (hQ : Q ∈ S.L) :
    bornProjector Q (-S.sign Q) ∘ₗ stabProjector S = 0 := by
  rw [bornProjector_comp_stabProjector S hQ,
    show (-S.sign Q) * S.sign Q = -(S.sign Q * S.sign Q) by ring, sign_mul_self S hQ,
    show ((1 + -1) / 2 : ℂ) = 0 by norm_num, zero_smul]

/-- The Born projector `Π_{Q,ε}` is self-adjoint when the outcome label `ε` is real
(`Π = ½(id + ε·H Q)`, with `id` and `H Q` self-adjoint and `2⁻¹` real). -/
theorem bornProjector_isSelfAdjoint {Q : Pauli n} {ε : ℂ} (hε : IsSelfAdjoint ε) :
    IsSelfAdjoint (bornProjector Q ε) := by
  unfold bornProjector
  refine IsSelfAdjoint.smul ?_ (IsSelfAdjoint.add ?_ (hε.smul (pauliHermitian_isSelfAdjoint Q)))
  · rw [isSelfAdjoint_iff]; simp
  · rw [isSelfAdjoint_iff, ← Module.End.one_eq_id, star_one]

/-- The selective **Lüders measurement channel** `A ↦ Π_{Q,ε} A Π_{Q,ε}` (two-sided), the genuine
operational measurement morphism of `𝒪` (conjunct (iv) of `stabilizer_operational_correspondence`
uses only the one-sided projector). -/
noncomputable def ludersChannel (Q : Pauli n) (ε : ℂ) (A : QState n →ₗ[ℂ] QState n) :
    QState n →ₗ[ℂ] QState n :=
  bornProjector Q ε ∘ₗ A ∘ₗ bornProjector Q ε

/-- **Deterministic measurement, correct outcome.** For `Q ∈ L`, the Lüders channel at the actual
sign `ε = χ(Q)` fixes the state: `Π_{Q,χ(Q)} Π_S Π_{Q,χ(Q)} = Π_S`. The right-hand absorption is the
adjoint of the left-hand one (both factors self-adjoint). -/
theorem ludersChannel_stabProjector_self (S : SignedStab n) {Q : Pauli n} (hQ : Q ∈ S.L) :
    ludersChannel Q (S.sign Q) (stabProjector S) = stabProjector S := by
  have hL : bornProjector Q (S.sign Q) ∘ₗ stabProjector S = stabProjector S :=
    bornProjector_comp_stabProjector_self S hQ
  have hR : stabProjector S ∘ₗ bornProjector Q (S.sign Q) = stabProjector S := by
    have h := congrArg star hL
    rw [← Module.End.mul_eq_comp, star_mul, stabProjector_isSelfAdjoint S,
      bornProjector_isSelfAdjoint (sign_isSelfAdjoint_of_mem S hQ)] at h
    rwa [Module.End.mul_eq_comp] at h
  change bornProjector Q (S.sign Q) ∘ₗ stabProjector S ∘ₗ bornProjector Q (S.sign Q)
    = stabProjector S
  rw [← LinearMap.comp_assoc, hL, hR]

/-- **Wrong outcome.** For `Q ∈ L`, the Lüders channel at `ε = -χ(Q)` annihilates the state
(probability-`0` branch). -/
theorem ludersChannel_stabProjector_zero (S : SignedStab n) {Q : Pauli n} (hQ : Q ∈ S.L) :
    ludersChannel Q (-S.sign Q) (stabProjector S) = 0 := by
  change bornProjector Q (-S.sign Q) ∘ₗ stabProjector S ∘ₗ bornProjector Q (-S.sign Q) = 0
  rw [← LinearMap.comp_assoc, bornProjector_comp_stabProjector_zero S hQ, LinearMap.zero_comp]

/-! ## The Clifford action on signed stabilizers (the `𝒮`-side generator)

A Clifford `U` acts on a signed stabilizer `S = (L, χ)` by transporting the Lagrangian through the
symplectic map `Φ = cliffordToSymplectic hU` and twisting the sign by the conjugation sign
`cliffordSign hU`. The cocycle laws of `χ` (`S.valid`) and of `cliffordSign`
(`cliffordSign_cocycle`) combine to make the result a genuine `SignedStab`; this is the `𝒮`-side of
the generator correspondence, matched on operators by `qConj_stabProjector`. -/

/-- **The Clifford action on signed stabilizers.** Push the Lagrangian `L` through the symplectic
map `Φ = cliffordToSymplectic hU` and twist the sign by `cliffordSign hU`. Its `valid` (cocycle) law
comes from `S.valid` and `cliffordSign_cocycle hU`. This realizes "`U` acts as `Φ(U)` on `(L, χ)`"
(the correspondence's Clifford generator), matched on operators by `qConj_stabProjector`. -/
noncomputable def cliffordAction {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (S : SignedStab n) : SignedStab n where
  L := Submodule.map (cliffordToSymplectic hU).toLinearMap S.L
  sign p := cliffordSign hU ((cliffordToSymplectic hU).symm p)
    * S.sign ((cliffordToSymplectic hU).symm p)
  sign_zero := by
    rw [map_zero, cliffordSign_zero hU, S.sign_zero, mul_one]
  valid := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hp
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hq
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    -- `p + q = Φ a + Φ b = Φ (a + b)`, so `Φ.symm (p+q) = a + b`.
    rw [← map_add, LinearEquiv.symm_apply_apply]
    -- Rewrite `pauliPhase (Φ a) (Φ b)` to the `cliffordToSymplecticFun` form for the cocycle.
    rw [cliffordToSymplectic_apply, cliffordToSymplectic_apply]
    have hv := S.valid a ha b hb
    have hc := cliffordSign_cocycle hU a b
    linear_combination cliffordSign hU (a + b) * hv + S.sign a * S.sign b * hc

/-- The Hermitian-Pauli coefficient of the Clifford-transported projector at the `Φ`-image `Φ p` is
the original coefficient times the conjugation sign:
`stabCoeff (cliffordAction hU S) (Φ p) = stabCoeff S p · cliffordSign hU p`. Membership transports
along the equivalence (`Submodule.mem_map_equiv`) and the sign field unfolds via `Φ.symm (Φ p) = p`.
This is the per-term bookkeeping behind `qConj_stabProjector`. -/
theorem stabCoeff_cliffordAction {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (S : SignedStab n) (p : Pauli n) :
    stabCoeff (cliffordAction hU S) (cliffordToSymplectic hU p)
      = stabCoeff S p * cliffordSign hU p := by
  have hmem : (cliffordToSymplectic hU p ∈ (cliffordAction hU S).L) ↔ p ∈ S.L := by
    change cliffordToSymplectic hU p ∈ Submodule.map (cliffordToSymplectic hU).toLinearMap S.L ↔ _
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  have hsign : (cliffordAction hU S).sign (cliffordToSymplectic hU p)
      = cliffordSign hU p * S.sign p := by
    change cliffordSign hU ((cliffordToSymplectic hU).symm (cliffordToSymplectic hU p))
        * S.sign ((cliffordToSymplectic hU).symm (cliffordToSymplectic hU p)) = _
    rw [LinearEquiv.symm_apply_apply]
  simp only [stabCoeff, hsign]
  by_cases hp : p ∈ S.L
  · rw [if_pos (hmem.mpr hp), if_pos hp]; ring
  · rw [if_neg (fun h => hp (hmem.mp h)), if_neg hp, zero_mul]

/-! ## Generator correspondence I, packaged: Clifford conjugation ↔ symplectic action

Conjugating a stabilizer projector by a Clifford `U` is the projector of the Clifford-acted signed
stabilizer: `U · Π_S · U⁻¹ = Π_{Φ(U)·S}`. This is the operator-side statement of the
correspondence's Clifford generator — the `𝒮`-action `cliffordAction` is faithfully mirrored by
conjugation on the carrier `X`. -/

/-- **Clifford conjugation acts as `Φ` on stabilizer projectors (the key lemma).**
`qConj U (stabProjector S) = stabProjector (cliffordAction hU S)`. Expanding `Π_S` over the
Hermitian-Pauli basis (`stabProjector_eq_sum_univ`), pushing `qConj` through the finite sum
(`qConjₗ`), and applying the Heisenberg law `qConj_pauliHermitian`, each term becomes
`stabCoeff S p · cliffordSign hU p · H(Φ p)`. Reindexing by the symplectic bijection
`Φ = cliffordToSymplectic hU` (`Finset.sum_nbij'`) and matching coefficients
(`stabCoeff_cliffordAction`) recovers `Π_{Φ(U)·S}`. This is the operator-level form of the
correspondence's Clifford generator (Gottesman 1998 Heisenberg picture). -/
theorem qConj_stabProjector {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (S : SignedStab n) :
    qConj U (stabProjector S) = stabProjector (cliffordAction hU S) := by
  rw [← qConjₗ_apply, stabProjector_eq_sum_univ S, map_sum,
    stabProjector_eq_sum_univ (cliffordAction hU S)]
  refine Finset.sum_nbij' (cliffordToSymplectic hU) (cliffordToSymplectic hU).symm
    (fun a _ => Finset.mem_univ _) (fun a _ => Finset.mem_univ _)
    (fun a _ => (cliffordToSymplectic hU).symm_apply_apply a)
    (fun a _ => (cliffordToSymplectic hU).apply_symm_apply a) (fun p _ => ?_)
  rw [map_smul, qConjₗ_apply, qConj_pauliHermitian hU, smul_smul, stabCoeff_cliffordAction hU S p,
    cliffordToSymplectic_apply]

end FTQCLib.Hilbert

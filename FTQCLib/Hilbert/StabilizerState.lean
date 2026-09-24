/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Inner
import Mathlib.Analysis.InnerProductSpace.Trace

/-! # Stabilizer states

The analytic core of the Born layer: the averaged Hermitian-Pauli projector of a signed stabilizer
group is a rank-one self-adjoint idempotent, so it projects onto a unique stabilizer state. The
first ingredient is the **character sum** over the `2ⁿ` computational labels,

  `∑_v (-1)^{a.Z · v} = 2ⁿ` if `a.Z = 0`, and `0` otherwise,

which makes the trace of a Hermitian Pauli `0` away from the identity. The `a.Z ≠ 0` case is a
sign-reversing involution (flip the `j`-th bit for a coordinate where `a.Z j = 1`).
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-- Character sum over the computational labels:
`∑_v (-1)^{a.Z · v}` is `2ⁿ` when `a.Z = 0` and `0` otherwise. -/
theorem sum_neg_one_pow_zDotVal (a : Pauli n) :
    (∑ v : Fin n → ZMod 2, ((-1 : ℂ) ^ (zDotVal a v))) = if a.Z = 0 then (2 : ℂ) ^ n else 0 := by
  by_cases hz : a.Z = 0
  · rw [if_pos hz]
    have hzero : ∀ v : Fin n → ZMod 2, zDotVal a v = 0 := by
      intro v
      simp only [zDotVal, hz, Pi.zero_apply, ZMod.val_zero, zero_mul, Finset.sum_const_zero]
    simp only [hzero, pow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hcard : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [hcard]
    push_cast
    ring
  · rw [if_neg hz]
    obtain ⟨j, hj⟩ : ∃ j, a.Z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    have hz1 : a.Z j = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hj
    have hsingle : zDotVal a (Pi.single j 1) = (a.Z j).val := by
      simp only [zDotVal]
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, show (ZMod.val (1 : ZMod 2)) = 1 by decide, mul_one]
      · intro i _ hij
        rw [Pi.single_eq_of_ne hij]
        simp
      · intro h
        exact absurd (Finset.mem_univ j) h
    have he : zDotVal a (Pi.single j 1) % 2 = 1 % 2 := by
      rw [hsingle, hz1]; decide
    refine Finset.sum_ninvolution (fun v => v + Pi.single j 1) ?_ ?_ ?_ ?_
    · intro v
      have hflip : (-1 : ℂ) ^ (zDotVal a (v + Pi.single j 1)) = -((-1 : ℂ) ^ (zDotVal a v)) := by
        rw [neg_one_pow_eq_of_mod_two_eq (zDotVal_add_right_mod_two a v (Pi.single j 1)), pow_add,
          neg_one_pow_eq_of_mod_two_eq he, pow_one]
        ring
      rw [hflip]; ring
    · intro v _ hcontra
      have h0 : (Pi.single j 1 : Fin n → ZMod 2) = 0 := by
        have hvv : v + Pi.single j 1 = v + 0 := by rw [add_zero]; exact hcontra
        exact add_left_cancel hvv
      have hjj := congrFun h0 j
      rw [Pi.single_eq_same, Pi.zero_apply] at hjj
      exact one_ne_zero hjj
    · intro v; exact Finset.mem_univ _
    · intro v
      change v + Pi.single j 1 + Pi.single j 1 = v
      have hee : (Pi.single j 1 : Fin n → ZMod 2) + Pi.single j 1 = 0 := by
        ext i; rw [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
      rw [add_assoc, hee, add_zero]

/-- The trace of a Hermitian Pauli: `2ⁿ` at the identity, `0` everywhere else. The diagonal
entry of `H(p)` in the computational basis is nonzero only when `p.X = 0`, and then summing the
signs is the character sum. -/
theorem pauliHermitian_trace (p : Pauli n) :
    LinearMap.trace ℂ (QState n) (pauliHermitian p) = if p = 0 then (2 : ℂ) ^ n else 0 := by
  rw [LinearMap.trace_eq_sum_inner (pauliHermitian p) (EuclideanSpace.basisFun (Fin n → ZMod 2) ℂ)]
  by_cases hpx : p.X = 0
  · have hxz : xzWeight p = 0 := by unfold xzWeight; rw [hpx]; unfold zDotVal; simp
    have hterm : ∀ v : Fin n → ZMod 2,
        (inner ℂ (EuclideanSpace.basisFun (Fin n → ZMod 2) ℂ v)
          (pauliHermitian p (EuclideanSpace.basisFun (Fin n → ZMod 2) ℂ v)) : ℂ)
        = (-1 : ℂ) ^ (zDotVal p v) := by
      intro v
      rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply, ← qComputational_eq_single,
        pauliHermitian_qComputational, PiLp.smul_apply, smul_eq_mul, qComputational_eq_single,
        EuclideanSpace.single_apply, hxz, pow_zero, one_mul, hpx, add_zero, if_pos rfl, mul_one]
    rw [Finset.sum_congr rfl (fun v _ => hterm v), sum_neg_one_pow_zDotVal]
    by_cases hpz : p.Z = 0
    · rw [if_pos hpz, if_pos (Pauli.ext hpx hpz)]
    · rw [if_neg hpz, if_neg (fun hp => hpz ((congrArg Pauli.Z hp).trans Z_zero))]
  · have hterm : ∀ v : Fin n → ZMod 2,
        (inner ℂ (EuclideanSpace.basisFun (Fin n → ZMod 2) ℂ v)
          (pauliHermitian p (EuclideanSpace.basisFun (Fin n → ZMod 2) ℂ v)) : ℂ) = 0 := by
      intro v
      have hne : ¬ (v = v + p.X) := by
        intro h
        apply hpx
        have hvv : v + (0 : Fin n → ZMod 2) = v + p.X := by rw [add_zero]; exact h
        exact (add_left_cancel hvv).symm
      rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply, ← qComputational_eq_single,
        pauliHermitian_qComputational, PiLp.smul_apply, smul_eq_mul, qComputational_eq_single,
        EuclideanSpace.single_apply, if_neg hne, mul_zero]
    rw [Finset.sum_congr rfl (fun v _ => hterm v), Finset.sum_const_zero,
      if_neg (fun hp => hpx ((congrArg Pauli.X hp).trans X_zero))]

/-- The pairwise Hermitian-Pauli product (the Pauli-product cocycle), derived from the triple
lemma at `(p, q, p+q)` (which sums to zero) by composing with the involution `H(p+q)`. The scalar
is a fourth root of unity; for commuting `p, q` it is `±1`. -/
theorem pauliHermitian_mul (p q : Pauli n) :
    pauliHermitian q ∘ₗ pauliHermitian p
      = (Complex.I ^ xzWeight p * Complex.I ^ xzWeight q * Complex.I ^ xzWeight (p + q)
          * (-1 : ℂ) ^ (zDotVal q p.X + zDotVal (p + q) (p + q).X)) • pauliHermitian (p + q) := by
  have hsum : p + q + (p + q) = 0 := by
    apply Pauli.ext
    · ext i
      change (p + q).X i + (p + q).X i = (0 : Pauli n).X i
      rw [X_zero, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _
    · ext i
      change (p + q).Z i + (p + q).Z i = (0 : Pauli n).Z i
      rw [Z_zero, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _
  have htriple := pauliHermitian_triple_of_sum_zero p q (p + q) hsum
  calc pauliHermitian q ∘ₗ pauliHermitian p
      = LinearMap.id ∘ₗ (pauliHermitian q ∘ₗ pauliHermitian p) := by rw [LinearMap.id_comp]
    _ = (pauliHermitian (p + q) ∘ₗ pauliHermitian (p + q)) ∘ₗ
          (pauliHermitian q ∘ₗ pauliHermitian p) := by
        rw [pauliHermitian_sq]
    _ = pauliHermitian (p + q)
          ∘ₗ (pauliHermitian (p + q) ∘ₗ pauliHermitian q ∘ₗ pauliHermitian p) := by
        rw [LinearMap.comp_assoc]
    _ = pauliHermitian (p + q)
          ∘ₗ ((Complex.I ^ xzWeight p * Complex.I ^ xzWeight q * Complex.I ^ xzWeight (p + q)
              * (-1 : ℂ) ^ (zDotVal q p.X + zDotVal (p + q) (p + q).X)) • LinearMap.id) := by
        rw [htriple]
    _ = _ := by rw [LinearMap.comp_smul, LinearMap.comp_id]

/-- The Pauli-product cocycle scalar, packaged: `H(q) ∘ H(p) = pauliPhase p q • H(p+q)`. -/
noncomputable def pauliPhase (p q : Pauli n) : ℂ :=
  Complex.I ^ xzWeight p * Complex.I ^ xzWeight q * Complex.I ^ xzWeight (p + q)
    * (-1 : ℂ) ^ (zDotVal q p.X + zDotVal (p + q) (p + q).X)

theorem pauliHermitian_mul_phase (p q : Pauli n) :
    pauliHermitian q ∘ₗ pauliHermitian p = pauliPhase p q • pauliHermitian (p + q) :=
  pauliHermitian_mul p q

/-- A **signed stabilizer**: a subspace `L` of `Pauli n` with a sign character `sign` such that the
operators `sign(p) • H(p)` for `p ∈ L` form a group of commuting involutions. The validity
condition `sign q · sign p · pauliPhase p q = sign (p+q)` is the β-twisted-character law that
trivializes the Pauli-product cocycle. -/
structure SignedStab (n : ℕ) where
  L : Submodule (ZMod 2) (Pauli n)
  sign : Pauli n → ℂ
  sign_zero : sign 0 = 1
  valid : ∀ p ∈ L, ∀ q ∈ L, sign q * sign p * pauliPhase p q = sign (p + q)

/-- The averaged Hermitian-Pauli projector `Π = 2⁻ⁿ ∑_{p∈L} sign(p) H(p)`. -/
noncomputable def stabProjector (S : SignedStab n) : QState n →ₗ[ℂ] QState n :=
  (2 ^ n : ℂ)⁻¹ • ∑ p ∈ (Set.toFinite (S.L : Set (Pauli n))).toFinset,
    S.sign p • pauliHermitian p

/-- The stabilizer projector has trace `1`: only the identity term `p = 0` survives the trace
(`tr H(0) = 2ⁿ`, `sign 0 = 1`), and `2⁻ⁿ · 2ⁿ = 1`. -/
theorem stabProjector_trace (S : SignedStab n) :
    LinearMap.trace ℂ (QState n) (stabProjector S) = 1 := by
  have hmem0 : (0 : Pauli n) ∈ (Set.toFinite (S.L : Set (Pauli n))).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact S.L.zero_mem
  have hterm : ∀ p ∈ (Set.toFinite (S.L : Set (Pauli n))).toFinset,
      LinearMap.trace ℂ (QState n) (S.sign p • pauliHermitian p)
        = S.sign p * (if p = 0 then (2 : ℂ) ^ n else 0) := by
    intro p _
    rw [map_smul, smul_eq_mul, pauliHermitian_trace]
  unfold stabProjector
  rw [map_smul, map_sum, Finset.sum_congr rfl hterm, Finset.sum_eq_single (0 : Pauli n)]
  · rw [if_pos rfl, S.sign_zero, one_mul, smul_eq_mul,
      inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero))]
  · intro p _ hp; rw [if_neg hp, mul_zero]
  · intro h; exact absurd hmem0 h

/-- In `Pauli n` (a `ZMod 2`-module) every element is its own negation: `x + x = 0`. -/
theorem pauli_add_self (x : Pauli n) : x + x = 0 := by
  apply Pauli.ext
  · ext i
    change x.X i + x.X i = (0 : Pauli n).X i
    rw [X_zero, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _
  · ext i
    change x.Z i + x.Z i = (0 : Pauli n).Z i
    rw [Z_zero, Pi.zero_apply]; exact CharTwo.add_self_eq_zero _

/-- The zero Pauli gives the identity: `H(0) = id` (`xzWeight 0 = 0`, `pauliOperator 0 = id`). -/
theorem pauliHermitian_zero : pauliHermitian (0 : Pauli n) = LinearMap.id := by
  ext ψ
  have hw : xzWeight (0 : Pauli n) = 0 := by simp [xzWeight, zDotVal]
  simp [pauliHermitian_apply, hw, qPauli_apply, pauliOperator_zero]

/-- The Pauli-product cocycle is **trivial on the diagonal**: `pauliPhase p p = 1`. Indeed
`H(p) ∘ H(p) = id` (`pauliHermitian_sq`), but also equals `pauliPhase p p • H(0)` (`p+p=0`), and
`H(0) = id` has trace `2ⁿ ≠ 0`, forcing the scalar to be `1`. This is what makes each stabilizer
sign square to one (`sign(p)² = 1`), hence a real `±1`. -/
theorem pauliPhase_self (p : Pauli n) : pauliPhase p p = 1 := by
  have h1 : (LinearMap.id : QState n →ₗ[ℂ] QState n) = pauliPhase p p • pauliHermitian 0 := by
    rw [← pauliHermitian_sq p, pauliHermitian_mul_phase, pauli_add_self]
  have htr := congrArg (LinearMap.trace ℂ (QState n)) h1
  rw [map_smul, pauliHermitian_trace, if_pos rfl, smul_eq_mul, ← pauliHermitian_zero,
    pauliHermitian_trace, if_pos rfl] at htr
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  have : pauliPhase p p * (2 : ℂ) ^ n = 1 * (2 : ℂ) ^ n := by rw [one_mul]; exact htr.symm
  exact mul_right_cancel₀ h2n this

/-- Left-composition distributes over a finite sum of operators. -/
private theorem comp_finset_sum (f : QState n →ₗ[ℂ] QState n) (s : Finset (Pauli n))
    (G : Pauli n → (QState n →ₗ[ℂ] QState n)) :
    f ∘ₗ (∑ p ∈ s, G p) = ∑ p ∈ s, f ∘ₗ G p := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, LinearMap.comp_add, ih, Finset.sum_insert ha]

/-- **Absorption.** Every stabilizer element `sign(g) • H(g)` (for `g ∈ L`) fixes the projector:
`(sign g • H g) ∘ Π = Π`. This is the group law (`valid`) summed over `L`, with the index
reshuffled by `p ↦ p + g`. -/
theorem stabProjector_absorb (S : SignedStab n) (g : Pauli n) (hg : g ∈ S.L) :
    (S.sign g • pauliHermitian g) ∘ₗ stabProjector S = stabProjector S := by
  unfold stabProjector
  rw [LinearMap.comp_smul]
  congr 1
  rw [comp_finset_sum]
  have hterm : ∀ p ∈ (Set.toFinite (S.L : Set (Pauli n))).toFinset,
      (S.sign g • pauliHermitian g) ∘ₗ (S.sign p • pauliHermitian p)
        = S.sign (p + g) • pauliHermitian (p + g) := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, pauliHermitian_mul_phase,
      smul_smul, S.valid p hp g hg]
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' (fun p => p + g) (fun p => p + g) ?_ ?_ ?_ ?_ ?_
  · intro a ha; rw [Set.Finite.mem_toFinset] at ha ⊢; exact S.L.add_mem ha hg
  · intro a ha; rw [Set.Finite.mem_toFinset] at ha ⊢; exact S.L.add_mem ha hg
  · intro a _; change a + g + g = a; rw [add_assoc, pauli_add_self, add_zero]
  · intro a _; change a + g + g = a; rw [add_assoc, pauli_add_self, add_zero]
  · intro a _; rfl

/-- Composition distributes over a finite sum in the left argument. -/
private theorem finset_sum_comp {s : Finset (Pauli n)} (f : QState n →ₗ[ℂ] QState n)
    (G : Pauli n → (QState n →ₗ[ℂ] QState n)) :
    (∑ p ∈ s, G p) ∘ₗ f = ∑ p ∈ s, G p ∘ₗ f := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, LinearMap.add_comp, ih, Finset.sum_insert ha]

/-- **Idempotency** of the stabilizer projector for a full Lagrangian (`|L| = 2ⁿ`): `Π² = Π`.
Expanding the left factor, every summand `(sign p • H p) ∘ Π = Π` by absorption, so
`Π² = 2⁻ⁿ · (2ⁿ · Π) = Π`. Together with `stabProjector_trace = 1` this makes `Π` a rank-one
projector — the pure state `|ψ⟩⟨ψ|`. -/
theorem stabProjector_idem (S : SignedStab n)
    (hcard : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card = 2 ^ n) :
    stabProjector S ∘ₗ stabProjector S = stabProjector S := by
  change ((2 ^ n : ℂ)⁻¹ • ∑ p ∈ (Set.toFinite (S.L : Set (Pauli n))).toFinset,
      S.sign p • pauliHermitian p) ∘ₗ stabProjector S = stabProjector S
  rw [LinearMap.smul_comp, finset_sum_comp,
    Finset.sum_congr rfl (fun p hp => stabProjector_absorb S p ((Set.Finite.mem_toFinset _).mp hp)),
    Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul (R := ℂ), smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero n two_ne_zero), one_smul]

/-- Stabilizer signs are `±1`: for `p ∈ L`, `sign(p)² = 1`. The validity law at `q = p` reads
`sign(p)² · pauliPhase p p = sign(p+p) = sign 0 = 1`, with `pauliPhase p p = 1` (`pauliPhase_self`)
and `p+p = 0`. -/
theorem sign_mul_self (S : SignedStab n) {p : Pauli n} (hp : p ∈ S.L) :
    S.sign p * S.sign p = 1 := by
  have h := S.valid p hp p hp
  rw [pauliPhase_self, mul_one, pauli_add_self, S.sign_zero] at h
  exact h

/-- Each stabilizer sign is real (`±1`), hence self-adjoint in `ℂ`. -/
theorem sign_isSelfAdjoint_of_mem (S : SignedStab n) {p : Pauli n} (hp : p ∈ S.L) :
    IsSelfAdjoint (S.sign p) := by
  rw [isSelfAdjoint_iff]
  rcases mul_self_eq_one_iff.mp (sign_mul_self S hp) with h | h
  · rw [h, star_one]
  · rw [h, star_neg, star_one]

/-- **Self-adjointness** of the stabilizer projector: `Π† = Π`. Each summand `sign(p) • H(p)` is
self-adjoint (`sign p` real for `p ∈ L`, `H(p)` Hermitian), as is the real prefactor `2⁻ⁿ`. With
idempotency (`stabProjector_idem`) and trace `1`, this certifies `Π` as a genuine pure-state
density. -/
theorem stabProjector_isSelfAdjoint (S : SignedStab n) : IsSelfAdjoint (stabProjector S) := by
  unfold stabProjector
  refine IsSelfAdjoint.smul ?_ ?_
  · rw [isSelfAdjoint_iff, star_inv₀, star_pow]; simp
  · rw [isSelfAdjoint_iff, star_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset] at hp
    rw [star_smul, sign_isSelfAdjoint_of_mem S hp, pauliHermitian_isSelfAdjoint p]

/-- The projector is nonzero (its trace is `1`). -/
theorem stabProjector_ne_zero (S : SignedStab n) : stabProjector S ≠ 0 := by
  intro h
  have htr := stabProjector_trace S
  rw [h, map_zero] at htr
  exact one_ne_zero htr.symm

/-- **Existence of a stabilizer state (prerequisite for Born collapse).** Every signed
stabilizer `S` has a nonzero vector fixed by every stabilizer element `sign(g) • H(g)`, `g ∈ L`
— obtained as any nonzero vector in the range of the (nonzero) projector, which absorption
fixes. -/
theorem exists_stabilizerState (S : SignedStab n) :
    ∃ ψ : QState n, ψ ≠ 0 ∧ ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ := by
  obtain ⟨φ, hφ⟩ := DFunLike.ne_iff.mp (stabProjector_ne_zero S)
  rw [LinearMap.zero_apply] at hφ
  refine ⟨stabProjector S φ, hφ, fun g hg => ?_⟩
  rw [← LinearMap.comp_apply, stabProjector_absorb S g hg]

end FTQCLib.Hilbert

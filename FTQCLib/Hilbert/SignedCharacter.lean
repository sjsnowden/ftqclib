/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.StabilizerEquiv
import Mathlib.FieldTheory.Finiteness

set_option linter.unusedSectionVars false

/-!
# The signed character formula for the qubit Clifford setting

The characteristic-2 sibling of the odd-`q` Weil character formula
(`ECCLib/WeilCharacter.lean`). There, conjugation by a Weil operator permutes the Weyl
basis **phase-free** (the `½ω` cocycle is `Sp`-invariant) and `Tr(W)·Tr(W⁻¹) = #Fix(ḡ)`, never
zero. Over `𝔽₂` a Clifford `U` conjugates the Hermitian Paulis only **up to signs** —
`qConj_pauliHermitian`: `U·H(p)·U⁻¹ = μ(p)·H(g p)` with `μ = cliffordSign hU` — and the formula
survives exactly in signed form:

* `signed_trace_mul_trace_inv` — `Tr(U)·Tr(U⁻¹) = Σ_{p : g p = p} μ(p)`, the **signed**
  fixed-point count;
* `cliffordSign_char_on_fix` — `μ` restricted to the fixed set is a `{±1}` group character (the
  `pauliPhase` twist cancels exactly there);
* `trace_eq_zero_of_fixed_sign_neg` — **individual vanishing**: one fixed `p₀` with `μ(p₀) = −1`
  forces `Tr(U) = 0` *and* `Tr(U⁻¹) = 0` (each separately — `H(p₀)` conjugates `U` to `−U`);
* `trace_mul_trace_inv_of_sign_trivial` — when `μ` is trivial on the fixed set the count is
  attained: `Tr(U)·Tr(U⁻¹) = 2^{dim ker(g−1)}`;
* witness `signed_trace_refl`: the identity Clifford attains `4^n = 2^{dim Fix}`, both routes.

The engine is the **Pauli twirl** `Σ_p H(p)·A·H(p) = (2^n·Tr A)•1`, proved by basis expansion
(`linearMap_ext_of_pauliHermitian`) — both sides are linear in `A`, and on `A = H(q)` the
anticommutation sign `pauliHermitian_swap` reduces it to the `ω`-character sum over `Pauli n`.

The sign character is data of the ℂˣ-class of `U`, **not** of `g` (Pauli multiples of `U`
sweep the characters of the fixed set): the possibility of trace-zero Cliffords — `Tr H = 0` —
is exactly the possibility of a nontrivial sign character on the fixed space, the section-level
face of the char-2 metaplectic non-splitting (`metaplecticNonSplit_two`). At odd `q` the sign is
forcibly trivial and the trace-1 canonical section exists; here neither holds.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-! ## `*`-form wrappers over the `∘ₗ`-form Pauli layer -/

lemma pauliH_mul_self (p : Pauli n) :
    pauliHermitian p * pauliHermitian p = (1 : QState n →ₗ[ℂ] QState n) := by
  rw [Module.End.mul_eq_comp, pauliHermitian_sq]
  rfl

lemma pauliH_swap (p q : Pauli n) :
    pauliHermitian p * pauliHermitian q
      = ((-1 : ℂ) ^ (zDotVal p q.X + zDotVal q p.X)) • (pauliHermitian q * pauliHermitian p) := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, pauliHermitian_swap]

lemma trace_pauliH_mul (p q : Pauli n) :
    LinearMap.trace ℂ (QState n) (pauliHermitian q * pauliHermitian p)
      = if p = q then (2 : ℂ) ^ n else 0 := by
  rw [Module.End.mul_eq_comp, trace_pauliHermitian_mul]

/-- `Tr(id) = 2ⁿ` on `QState n` — the private helper of `Separation.lean`, re-derived. -/
lemma trace_one_qstate :
    LinearMap.trace ℂ (QState n) (1 : QState n →ₗ[ℂ] QState n) = (2 : ℂ) ^ n := by
  have h := pauliHermitian_trace (0 : Pauli n)
  rw [pauliHermitian_zero, if_pos rfl] at h
  exact h

/-- `|Pauli n| = 2ⁿ·2ⁿ` (as a ℂ identity, the form the twirl consumes). -/
lemma card_pauli_complex :
    ((Fintype.card (Pauli n) : ℂ)) = (2 : ℂ) ^ n * (2 : ℂ) ^ n := by
  have hcard : Fintype.card (Pauli n) = 2 ^ n * 2 ^ n := by
    rw [show Fintype.card (Pauli n) = Fintype.card ((Fin n → ZMod 2) × (Fin n → ZMod 2)) from
      Fintype.card_congr ⟨fun p => (p.X, p.Z), fun v => ⟨v.1, v.2⟩, fun _ => rfl, fun _ => rfl⟩]
    rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard]
  push_cast
  ring

/-! ## The `ω`-character sum over `Pauli n` -/

/-- Parity conversion: the anticommutation exponent's `(−1)`-power is decided by `ω`. -/
lemma neg_one_pow_omega (p q : Pauli n) :
    ((-1 : ℂ)) ^ (zDotVal p q.X + zDotVal q p.X)
      = if omega p q = 0 then (1 : ℂ) else -1 := by
  classical
  have hcast := omega_natCast p q
  rcases Nat.even_or_odd (zDotVal p q.X + zDotVal q p.X) with he | ho
  · rw [Even.neg_one_pow he]
    obtain ⟨k, hk⟩ := he
    rw [hk] at hcast
    push_cast at hcast
    rw [CharTwo.add_self_eq_zero] at hcast
    rw [if_pos hcast.symm]
  · rw [Odd.neg_one_pow ho]
    obtain ⟨k, hk⟩ := ho
    have h1 : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        show ((2 : ℕ) : ZMod 2) = 0 from by decide, zero_mul, zero_add]
    rw [hk, h1] at hcast
    rw [if_neg (by rw [← hcast]; decide)]

open Classical in
/-- **The `ω`-character sum**: `Σ_p (−1)^{e(p,q)} = 4ⁿ·[q = 0]` — nondegeneracy of `ω` kills every
nonzero `q` by the sign-flipping shift `p ↦ p + r`. -/
lemma sum_neg_one_pow_omega (q : Pauli n) :
    (∑ p : Pauli n, ((-1 : ℂ)) ^ (zDotVal p q.X + zDotVal q p.X))
      = if q = 0 then (2 : ℂ) ^ n * (2 : ℂ) ^ n else 0 := by
  rw [Finset.sum_congr rfl fun p _ => neg_one_pow_omega p q]
  by_cases hq : q = 0
  · subst hq
    rw [if_pos rfl]
    have h : ∀ p : Pauli n, (if omega p 0 = 0 then (1 : ℂ) else -1) = 1 := by
      intro p
      rw [if_pos (omega_zero_right p)]
    rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, card_pauli_complex]
  · rw [if_neg hq]
    -- a direction `r` seeing `q`: `ω r q = 1`
    obtain ⟨r, hr⟩ : ∃ r, omega r q ≠ 0 := by
      by_contra h
      exact hq (omega_nondegenerate q (fun s => by
        rw [omega_comm]
        by_contra hs
        exact h ⟨s, hs⟩))
    have hr1 : omega r q = 1 := by
      have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact this _ hr
    -- the shift `p ↦ p + r` negates every term
    have hflip : ∀ p : Pauli n,
        (if omega (p + r) q = 0 then (1 : ℂ) else -1)
          = -(if omega p q = 0 then (1 : ℂ) else -1) := by
      intro p
      rw [omega_add_left, hr1]
      rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) (omega p q) with h | h
      · rw [h, if_pos rfl, if_neg (by decide : ¬((0 : ZMod 2) + 1 = 0))]
      · rw [h, if_neg (by decide : ¬((1 : ZMod 2) = 0)),
          if_pos (by decide : ((1 : ZMod 2) + 1 = 0))]
        norm_num
    have hshift : (∑ p : Pauli n, if omega (p + r) q = 0 then (1 : ℂ) else -1)
        = ∑ p : Pauli n, if omega p q = 0 then (1 : ℂ) else -1 :=
      Fintype.sum_equiv (Equiv.addRight r)
        (fun p => if omega (p + r) q = 0 then (1 : ℂ) else -1)
        (fun p => if omega p q = 0 then (1 : ℂ) else -1)
        (fun p => rfl)
    have hneg : (∑ p : Pauli n, if omega p q = 0 then (1 : ℂ) else -1)
        = -(∑ p : Pauli n, if omega p q = 0 then (1 : ℂ) else -1) := by
      conv_lhs => rw [← hshift]
      rw [Finset.sum_congr rfl fun p _ => hflip p, Finset.sum_neg_distrib]
    have h2 : (2 : ℂ) * (∑ p : Pauli n, if omega p q = 0 then (1 : ℂ) else -1) = 0 := by
      linear_combination hneg
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ## The Pauli twirl -/

/-- The twirl, packaged linearly in the conjugated operator. -/
noncomputable def twirlHom : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] (QState n →ₗ[ℂ] QState n) where
  toFun A := ∑ p : Pauli n, pauliHermitian p * A * pauliHermitian p
  map_add' A B := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [mul_add, add_mul]
  map_smul' c A := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [mul_smul_comm, smul_mul_assoc]

/-- The target of the twirl, packaged linearly. -/
noncomputable def traceSmulHom : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] (QState n →ₗ[ℂ] QState n) where
  toFun A := ((2 : ℂ) ^ n * LinearMap.trace ℂ (QState n) A) • (1 : QState n →ₗ[ℂ] QState n)
  map_add' A B := by rw [map_add, mul_add, add_smul]
  map_smul' c A := by
    rw [RingHom.id_apply, map_smul, smul_eq_mul, smul_smul, mul_left_comm]

/-- **The Pauli twirl**: `Σ_p H(p)·A·H(p) = (2ⁿ·Tr A)•1`. By linearity it suffices on the
Hermitian Pauli basis, where the anticommutation sign turns the sum into the `ω`-character sum. -/
theorem pauli_twirl (A : QState n →ₗ[ℂ] QState n) :
    (∑ p : Pauli n, pauliHermitian p * A * pauliHermitian p)
      = ((2 : ℂ) ^ n * LinearMap.trace ℂ (QState n) A) • (1 : QState n →ₗ[ℂ] QState n) := by
  classical
  have hext : (twirlHom : (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] (QState n →ₗ[ℂ] QState n))
      = traceSmulHom := by
    refine linearMap_ext_of_pauliHermitian fun q => ?_
    change (∑ p : Pauli n, pauliHermitian p * pauliHermitian q * pauliHermitian p)
        = ((2 : ℂ) ^ n * LinearMap.trace ℂ (QState n) (pauliHermitian q))
            • (1 : QState n →ₗ[ℂ] QState n)
    have hterm : ∀ p : Pauli n,
        pauliHermitian p * pauliHermitian q * pauliHermitian p
          = ((-1 : ℂ) ^ (zDotVal p q.X + zDotVal q p.X)) • pauliHermitian q := by
      intro p
      rw [pauliH_swap p q, smul_mul_assoc, mul_assoc, pauliH_mul_self, mul_one]
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.sum_smul, sum_neg_one_pow_omega,
      pauliHermitian_trace]
    by_cases hq : q = 0
    · subst hq
      rw [if_pos rfl, if_pos rfl, mul_comm]
      rw [show pauliHermitian (0 : Pauli n) = (1 : QState n →ₗ[ℂ] QState n) from by
        rw [pauliHermitian_zero]; rfl]
    · rw [if_neg hq, if_neg hq, mul_zero, zero_smul, zero_smul]
  exact congrFun (congrArg (fun f => f.toFun) hext) A

/-! ## The signed character formula -/

open Classical in
/-- **The signed character formula** (char-2 Weil character formula): for a Clifford `U` with
symplectic part `g` and sign `μ = cliffordSign hU`,
`Tr(U)·Tr(U⁻¹) = Σ_{p : g p = p} μ(p)` — the **signed** count of the fixed Pauli labels. The
left side is invariant under `U ↦ c•U`; the right side depends on the ℂˣ-class through `μ` alone.
Contrast the odd-`q` `weil_trace_mul_trace_inv`, where the count is unsigned and never zero. -/
theorem signed_trace_mul_trace_inv {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) :
    LinearMap.trace ℂ (QState n) (qClifford U).toLinearMap
        * LinearMap.trace ℂ (QState n) (qClifford U).symm.toLinearMap
      = ∑ p ∈ Finset.univ.filter (fun p : Pauli n => cliffordToSymplecticFun hU p = p),
          cliffordSign hU p := by
  classical
  set V : QState n →ₗ[ℂ] QState n := (qClifford U).toLinearMap with hV
  set Vinv : QState n →ₗ[ℂ] QState n := (qClifford U).symm.toLinearMap with hVinv
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  -- the double-counted sum: `S = Σ_p Tr(H p · (V · H p · V⁻¹))`
  have hconj : ∀ p : Pauli n, V * pauliHermitian p * Vinv = qConj U (pauliHermitian p) := by
    intro p
    rw [qConj, hV, hVinv, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
  set S : ℂ := ∑ p : Pauli n,
    LinearMap.trace ℂ (QState n) (pauliHermitian p * (V * pauliHermitian p * Vinv)) with hS
  -- way 1: regroup and hit the twirl at `V`
  have hway1 : S = (2 : ℂ) ^ n * LinearMap.trace ℂ (QState n) V
      * LinearMap.trace ℂ (QState n) Vinv := by
    have hregroup : ∀ p : Pauli n,
        pauliHermitian p * (V * pauliHermitian p * Vinv)
          = (pauliHermitian p * V * pauliHermitian p) * Vinv := by
      intro p
      noncomm_ring
    rw [hS, Finset.sum_congr rfl fun p _ => by rw [hregroup p], ← map_sum, ← Finset.sum_mul,
      pauli_twirl, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  -- way 2: the conjugation law and trace orthogonality
  have hway2 : S = (2 : ℂ) ^ n
      * ∑ p ∈ Finset.univ.filter (fun p : Pauli n => cliffordToSymplecticFun hU p = p),
          cliffordSign hU p := by
    have hterm : ∀ p : Pauli n,
        LinearMap.trace ℂ (QState n) (pauliHermitian p * (V * pauliHermitian p * Vinv))
          = if cliffordToSymplecticFun hU p = p
              then cliffordSign hU p * (2 : ℂ) ^ n else 0 := by
      intro p
      rw [hconj p, qConj_pauliHermitian hU, mul_smul_comm, map_smul, smul_eq_mul,
        trace_pauliH_mul (cliffordToSymplecticFun hU p) p]
      by_cases hfix : cliffordToSymplecticFun hU p = p
      · rw [if_pos hfix, if_pos hfix]
      · rw [if_neg hfix, if_neg hfix, mul_zero]
    rw [hS, Finset.sum_congr rfl fun p _ => hterm p, ← Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h := hway1.symm.trans hway2
  have h' : (2 : ℂ) ^ n * (LinearMap.trace ℂ (QState n) V * LinearMap.trace ℂ (QState n) Vinv)
      = (2 : ℂ) ^ n
        * ∑ p ∈ Finset.univ.filter (fun p : Pauli n => cliffordToSymplecticFun hU p = p),
            cliffordSign hU p := by
    rw [← mul_assoc]
    exact h
  exact mul_left_cancel₀ h2n h'

/-! ## The sign character on the fixed set, and the dichotomy -/

/-- `pauliPhase` never vanishes (a product of powers of `I` and `−1`). -/
lemma pauliPhase_ne_zero (p q : Pauli n) : pauliPhase p q ≠ 0 := by
  unfold pauliPhase
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero)
    (pow_ne_zero _ I_ne_zero)) (pow_ne_zero _ I_ne_zero))
    (pow_ne_zero _ (by norm_num))

/-- **The sign is a character on the fixed set**: for `a, b` fixed by `g`, the `pauliPhase` twist
in `cliffordSign_cocycle` cancels and `μ(a+b) = μ(a)·μ(b)`. (Off the fixed set `μ` is only the
twisted cocycle — do not strengthen.) -/
theorem cliffordSign_char_on_fix {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {a b : Pauli n}
    (ha : cliffordToSymplecticFun hU a = a) (hb : cliffordToSymplecticFun hU b = b) :
    cliffordSign hU (a + b) = cliffordSign hU a * cliffordSign hU b := by
  have h := cliffordSign_cocycle hU a b
  rw [ha, hb] at h
  exact (mul_right_cancel₀ (pauliPhase_ne_zero a b) h).symm

open Classical in
/-- **Trivial sign attains the count**: if `μ ≡ 1` on the fixed set, the product of traces is
`2^{dim ker(g−1)}` — the full unsigned fixed-point count, as at odd `q`. -/
theorem trace_mul_trace_inv_of_sign_trivial {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U)
    (htriv : ∀ p : Pauli n, cliffordToSymplecticFun hU p = p → cliffordSign hU p = 1) :
    LinearMap.trace ℂ (QState n) (qClifford U).toLinearMap
        * LinearMap.trace ℂ (QState n) (qClifford U).symm.toLinearMap
      = (2 : ℂ) ^ (Module.finrank (ZMod 2)
          (LinearMap.ker (cliffordToSymplecticLinear hU - LinearMap.id))) := by
  classical
  rw [signed_trace_mul_trace_inv hU]
  rw [Finset.sum_congr rfl fun p hp => htriv p (Finset.mem_filter.mp hp).2]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the filter card is the kernel card
  have hiff : ∀ p : Pauli n, (cliffordToSymplecticFun hU p = p)
      ↔ p ∈ LinearMap.ker (cliffordToSymplecticLinear hU - LinearMap.id) := by
    intro p
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact Iff.rfl
  have hcard : (Finset.univ.filter
        (fun p : Pauli n => cliffordToSymplecticFun hU p = p)).card
      = Fintype.card (LinearMap.ker (cliffordToSymplecticLinear hU - LinearMap.id)) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight hiff)
  rw [hcard, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  push_cast
  ring

/-! ## Individual vanishing -/

/-- **Individual vanishing** — the char-2 phenomenon: one fixed label with sign `−1` kills *both*
traces separately, not just their product. `H(p₀)` conjugates `U` to `−U`, so `Tr U = −Tr U`.
This is why no trace-1 canonical section exists over `𝔽₂` (the odd-`q` `weilNorm` mechanism), and
it is the section-level face of `metaplecticNonSplit_two`. Minimal instance: the Hadamard, with
`p₀` the `Y` label. -/
theorem trace_eq_zero_of_fixed_sign_neg {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {p₀ : Pauli n}
    (hfix : cliffordToSymplecticFun hU p₀ = p₀) (hneg : cliffordSign hU p₀ = -1) :
    LinearMap.trace ℂ (QState n) (qClifford U).toLinearMap = 0
      ∧ LinearMap.trace ℂ (QState n) (qClifford U).symm.toLinearMap = 0 := by
  classical
  set V : QState n →ₗ[ℂ] QState n := (qClifford U).toLinearMap with hV
  set Vinv : QState n →ₗ[ℂ] QState n := (qClifford U).symm.toLinearMap with hVinv
  have hVVinv : V * Vinv = 1 := by
    rw [hV, hVinv]
    refine LinearMap.ext fun ψ => ?_
    simp [Module.End.mul_eq_comp]
  have hVinvV : Vinv * V = 1 := by
    rw [hV, hVinv]
    refine LinearMap.ext fun ψ => ?_
    simp [Module.End.mul_eq_comp]
  -- the conjugation relation at `p₀`: `V·H(p₀)·V⁻¹ = −H(p₀)`
  have hrel : V * pauliHermitian p₀ * Vinv = -pauliHermitian p₀ := by
    have h : V * pauliHermitian p₀ * Vinv = qConj U (pauliHermitian p₀) := by
      rw [qConj, hV, hVinv, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearMap.comp_assoc]
    rw [h, qConj_pauliHermitian hU, hfix, hneg, neg_one_smul]
  -- hence `V·H(p₀) = −H(p₀)·V` and `Vinv·H(p₀) = −H(p₀)·Vinv`
  have hVrel : V * pauliHermitian p₀ = -(pauliHermitian p₀ * V) := by
    have h := congrArg (· * V) hrel
    simp only [neg_mul] at h
    rwa [mul_assoc, hVinvV, mul_one] at h
  have hVinvrel : Vinv * pauliHermitian p₀ = -(pauliHermitian p₀ * Vinv) := by
    -- conjugate `hrel` back by `V⁻¹`: `V⁻¹·H·V = −H`, then move one factor across
    have h1 : Vinv * (V * pauliHermitian p₀ * Vinv) * V
        = Vinv * (-pauliHermitian p₀) * V := by rw [hrel]
    have h2 : Vinv * (V * pauliHermitian p₀ * Vinv) * V = pauliHermitian p₀ := by
      calc Vinv * (V * pauliHermitian p₀ * Vinv) * V
          = (Vinv * V) * pauliHermitian p₀ * (Vinv * V) := by noncomm_ring
        _ = pauliHermitian p₀ := by rw [hVinvV, one_mul, mul_one]
    rw [h2] at h1
    rw [show Vinv * (-pauliHermitian p₀) * V = -(Vinv * pauliHermitian p₀ * V) from by
      noncomm_ring] at h1
    have h4 : Vinv * pauliHermitian p₀ * V = -pauliHermitian p₀ := by
      have := congrArg Neg.neg h1
      rw [neg_neg] at this
      exact this.symm
    have h5 := congrArg (· * Vinv) h4
    simp only [neg_mul] at h5
    rwa [mul_assoc, hVVinv, mul_one] at h5
  -- the trace-flip argument, once per factor
  have hflip : ∀ (A : QState n →ₗ[ℂ] QState n),
      A * pauliHermitian p₀ = -(pauliHermitian p₀ * A)
      → LinearMap.trace ℂ (QState n) A = 0 := by
    intro A hA
    have hkey : LinearMap.trace ℂ (QState n) A = -LinearMap.trace ℂ (QState n) A := by
      calc LinearMap.trace ℂ (QState n) A
          = LinearMap.trace ℂ (QState n) (A * (pauliHermitian p₀ * pauliHermitian p₀)) := by
            rw [pauliH_mul_self, mul_one]
        _ = LinearMap.trace ℂ (QState n) ((A * pauliHermitian p₀) * pauliHermitian p₀) := by
            rw [mul_assoc]
        _ = -LinearMap.trace ℂ (QState n) ((pauliHermitian p₀ * A) * pauliHermitian p₀) := by
            rw [hA, neg_mul, map_neg]
        _ = -LinearMap.trace ℂ (QState n) (pauliHermitian p₀ * (pauliHermitian p₀ * A)) := by
            rw [LinearMap.trace_mul_comm]
        _ = -LinearMap.trace ℂ (QState n) A := by
            rw [← mul_assoc, pauliH_mul_self, one_mul]
    have h2 : (2 : ℂ) * LinearMap.trace ℂ (QState n) A = 0 := by linear_combination hkey
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  exact ⟨hflip V hVrel, hflip Vinv hVinvrel⟩



/-! ## Witness: the identity Clifford (two routes)

Route A computes both traces directly (`2ⁿ` each); route B evaluates the signed sum through the
main theorem. The `H`/`S`/`CNOT` witnesses (the vanishing branch and two nontrivial attained
counts) are in `SignedCharacterWitness.lean`. -/

/-- `qClifford` of the identity is the identity. -/
theorem qClifford_one_toLinearMap :
    (qClifford (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)).toLinearMap
      = (1 : QState n →ₗ[ℂ] QState n) := by
  refine LinearMap.ext fun ψ => ?_
  exact toQState.apply_symm_apply ψ

/-- `qClifford` of the identity, inverse side. -/
theorem qClifford_one_symm_toLinearMap :
    (qClifford (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)).symm.toLinearMap
      = (1 : QState n →ₗ[ℂ] QState n) := by
  refine LinearMap.ext fun ψ => ?_
  exact toQState.apply_symm_apply ψ

/-- **Witness, route A (independent)**: at `U = 1` both traces are `2ⁿ` by direct computation, so
the product is `2ⁿ·2ⁿ = #Pauli n` — the whole label space is fixed with trivial sign. -/
theorem signed_trace_one_independent :
    LinearMap.trace ℂ (QState n) (qClifford (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)).toLinearMap
        * LinearMap.trace ℂ (QState n)
            (qClifford (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)).symm.toLinearMap
      = (2 : ℂ) ^ n * (2 : ℂ) ^ n := by
  rw [qClifford_one_toLinearMap, qClifford_one_symm_toLinearMap, trace_one_qstate]

open Classical in
/-- **Witness, route B (main-theorem instance)**: the signed sum of the main theorem, evaluated at
`U = 1`, is forced to the same `2ⁿ·2ⁿ` — the two routes meet. -/
theorem signed_sum_one_general :
    (∑ p ∈ Finset.univ.filter
        (fun p : Pauli n => cliffordToSymplecticFun (isCliffordOperator_one) p = p),
      cliffordSign (isCliffordOperator_one) p)
      = (2 : ℂ) ^ n * (2 : ℂ) ^ n := by
  rw [← signed_trace_mul_trace_inv (isCliffordOperator_one), signed_trace_one_independent]

end FTQCLib.Hilbert

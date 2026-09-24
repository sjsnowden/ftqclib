/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.LemSpan

/-! # Measurement collapse foundation: structural lemmas for the `Q ∉ L` development

This file collects three independent structural lemmas used in the analysis of a stabilizer
measurement whose Pauli `Q` lies *outside* the stabilizer Lagrangian `L` (the genuinely
collapsing, non-deterministic case). They are reusable building blocks, free of the surrounding
measurement narrative:

* `pauliCondition_K_inf_span_eq_bot` — the two summands of the conditioned Lagrangian
  `pauliCondition S Q = (S ⊓ ⟨Q⟩^⊥) ⊔ ⟨Q⟩` meet trivially, i.e. their intersection is `⊥`. This
  is the disjointness that lets one read off the conditioned dimension as a direct sum.
* `pauliPhase_zero_right` / `pauliPhase_zero_left` — the Pauli-product cocycle is normalized at the
  identity Pauli: `pauliPhase Q 0 = 1` and `pauliPhase 0 Q = 1`.
* `bornProjector_idem` — the selective Born projector `Π_{Q,ε} = ½(id + ε·H(Q))` is idempotent
  whenever `ε² = 1` (in particular for `ε = ±1`).
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## Disjointness of the conditioned-Lagrangian summands -/

/-- The two summands of the conditioned Lagrangian intersect trivially. For `Q ∉ S`, the
"orthogonal" part `S ⊓ ⟨Q⟩^⊥` and the "added generator" part `⟨Q⟩` meet only in `⊥`: any element
of the meet is a scalar multiple `c • Q` lying in `S`, and since `Q ∉ S` the coefficient `c` (over
`ZMod 2`) must be `0`. This disjointness underlies the direct-sum dimension count for
`pauliCondition S Q` in the `Q ∉ S` branch. -/
theorem pauliCondition_K_inf_span_eq_bot
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} {Q : FTQCLib.Pauli n} (hQS : Q ∉ S) :
    (S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)))) ⊓
      Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxT, hxR⟩ := hx
  have hxS : x ∈ S := (Submodule.mem_inf.mp hxT).1
  rw [Submodule.mem_span_singleton] at hxR
  obtain ⟨c, rfl⟩ := hxR
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with h0 | h1
  · rw [h0, zero_smul]
  · rw [h1, one_smul] at hxS
    exact absurd hxS hQS

/-! ## Normalization of the Pauli-product cocycle at the identity -/

/-- The cocycle is normalized on the right by the identity Pauli: `pauliPhase Q 0 = 1`.
From `H(0) ∘ H(Q) = pauliPhase Q 0 • H(Q+0)` (`pauliHermitian_mul_phase`), post-composing with
`H(Q)` and the involution `H(Q) ∘ H(Q) = id` with `H(0) = id` gives `id = pauliPhase Q 0 • id`,
so taking traces and cancelling `tr id = 2ⁿ ≠ 0` forces the scalar to `1`. -/
theorem pauliPhase_zero_right (Q : Pauli n) : pauliPhase Q 0 = 1 := by
  have h1 : (LinearMap.id : QState n →ₗ[ℂ] QState n) = pauliPhase Q 0 • LinearMap.id := by
    have h := pauliHermitian_mul_phase Q 0
    rw [pauliHermitian_zero, LinearMap.id_comp, add_zero] at h
    calc (LinearMap.id : QState n →ₗ[ℂ] QState n)
        = pauliHermitian Q ∘ₗ pauliHermitian Q := (pauliHermitian_sq Q).symm
      _ = (pauliPhase Q 0 • pauliHermitian Q) ∘ₗ pauliHermitian Q := by nth_rewrite 1 [h]; rfl
      _ = pauliPhase Q 0 • (pauliHermitian Q ∘ₗ pauliHermitian Q) := by rw [LinearMap.smul_comp]
      _ = pauliPhase Q 0 • LinearMap.id := by rw [pauliHermitian_sq]
  have htr := congrArg (LinearMap.trace ℂ (QState n)) h1
  rw [map_smul, ← pauliHermitian_zero, pauliHermitian_trace, if_pos rfl, smul_eq_mul] at htr
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  have : pauliPhase Q 0 * (2 : ℂ) ^ n = 1 * (2 : ℂ) ^ n := by rw [one_mul]; exact htr.symm
  exact mul_right_cancel₀ h2n this

/-- The Pauli-product cocycle is normalized on the left by the identity Pauli: `pauliPhase 0 Q = 1`.
From `H(Q) ∘ H(0) = pauliPhase 0 Q • H(0+Q)` (`pauliHermitian_mul_phase`), pre-composing with `H(Q)`
and using `H(Q) ∘ H(Q) = id` together with `H(0) = id` gives `id = pauliPhase 0 Q • id`, so the same
trace cancellation yields the scalar `1`. -/
theorem pauliPhase_zero_left (Q : Pauli n) : pauliPhase 0 Q = 1 := by
  have h1 : (LinearMap.id : QState n →ₗ[ℂ] QState n) = pauliPhase 0 Q • LinearMap.id := by
    have h := pauliHermitian_mul_phase 0 Q
    rw [pauliHermitian_zero, LinearMap.comp_id, zero_add] at h
    calc (LinearMap.id : QState n →ₗ[ℂ] QState n)
        = pauliHermitian Q ∘ₗ pauliHermitian Q := (pauliHermitian_sq Q).symm
      _ = pauliHermitian Q ∘ₗ (pauliPhase 0 Q • pauliHermitian Q) := by nth_rewrite 2 [h]; rfl
      _ = pauliPhase 0 Q • (pauliHermitian Q ∘ₗ pauliHermitian Q) := by rw [LinearMap.comp_smul]
      _ = pauliPhase 0 Q • LinearMap.id := by rw [pauliHermitian_sq]
  have htr := congrArg (LinearMap.trace ℂ (QState n)) h1
  rw [map_smul, ← pauliHermitian_zero, pauliHermitian_trace, if_pos rfl, smul_eq_mul] at htr
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  have : pauliPhase 0 Q * (2 : ℂ) ^ n = 1 * (2 : ℂ) ^ n := by rw [one_mul]; exact htr.symm
  exact mul_right_cancel₀ h2n this

/-! ## Idempotence of the selective Born projector -/

/-- The selective Born projector `Π_{Q,ε} = ½(id + ε·H(Q))` is idempotent when `ε² = 1`. Expanding
the composition and using the involution `H(Q) ∘ H(Q) = id` (`pauliHermitian_sq`), the cross terms
give `¼(2·id + 2ε·H(Q))`, which equals `½(id + ε·H(Q))` precisely because `ε² = 1` collapses the
`ε²·H(Q)∘H(Q) = ε²·id = id` contribution. In particular `Π_{Q,±1}` is a projector. -/
theorem bornProjector_idem {Q : Pauli n} {ε : ℂ} (hε : ε * ε = 1) :
    bornProjector Q ε ∘ₗ bornProjector Q ε = bornProjector Q ε := by
  unfold bornProjector
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.id_comp, LinearMap.comp_id, smul_smul, pauliHermitian_sq]
  match_scalars
  · linear_combination (4⁻¹ : ℂ) * hε
  · ring

/-! ## The post-measurement sign `χ'` and its validity

For a full Lagrangian `S : SignedStab n` with `Q ∉ S.L`, the conditioned Lagrangian
`L' = pauliCondition S.L Q = K ⊔ ⟨Q⟩` (with `K = S.L ⊓ Q^⊥`) carries an explicit post-measurement
signed-stabilizer structure `measSignedStab`. Its sign `measSign` is `S.sign` on `K` and, on the
`Q`-coset, the outcome label `ε` twisted by `S.sign` and a Pauli-product phase.

The `Q`-coset coefficient of `g ∈ L'` is read off by `δ(g) := ω(M, g)` for a fixed anticommuting
witness `M ∈ S.L`, `ω(M, Q) = 1` — *not* by `ω(·, Q)`, which vanishes on the isotropic `L'`.
-/

/-- The Pauli-product phase is a **symmetric coboundary** on any stabilizer (isotropic) subspace
`W`: there is a sign `β : Pauli n → ℂ` with `β 0 = 1`, `β p` a square root of one for `p ∈ W`, and
`pauliPhase p q = β p · β q · β (p + q)` for all `p, q ∈ W`. This is the reference sign of `W`
(`exists_refSign`) with the cocycle law solved for the phase; it trivializes every
`pauliPhase`-identity among commuting Paulis into `±1` bookkeeping. -/
theorem exists_phase_coboundary {W : Submodule (ZMod 2) (Pauli n)}
    (hW : FTQCLib.Stabilizer.IsStabilizer W) :
    ∃ β : Pauli n → ℂ, β 0 = 1 ∧ (∀ p ∈ W, β p * β p = 1) ∧
      ∀ p ∈ W, ∀ q ∈ W, pauliPhase p q = β p * β q * β (p + q) := by
  obtain ⟨β, hβ0, hβvalid⟩ := exists_refSign hW
  refine ⟨β, hβ0, ?_, ?_⟩
  · intro p hp
    have h := hβvalid p hp p hp
    rw [pauliPhase_self, mul_one, pauli_add_self, hβ0] at h
    exact h
  · intro p hp q hq
    have hsqp : β p * β p = 1 := by
      have h := hβvalid p hp p hp
      rw [pauliPhase_self, mul_one, pauli_add_self, hβ0] at h; exact h
    have hsqq : β q * β q = 1 := by
      have h := hβvalid q hq q hq
      rw [pauliPhase_self, mul_one, pauli_add_self, hβ0] at h; exact h
    have hv := hβvalid p hp q hq
    -- `β q · β p · pauliPhase p q = β (p+q)`; multiply by `β p · β q` and use `β p² = β q² = 1`.
    have hmul : (β p * β p) * (β q * β q) * pauliPhase p q = β p * β q * β (p + q) := by
      linear_combination (β p * β q) * hv
    rwa [hsqp, hsqq, one_mul, one_mul] at hmul

/-! ### Reading the `Q`-coset coefficient by `δ = ω(M, ·)` -/

/-- The conditioned Lagrangian `pauliCondition L Q` is isotropic against `Q`: `ω(g, Q) = 0` for
every `g` in it (`Q` lies in the isotropic `pauliCondition L Q`). This is why the `Q`-coset
coefficient cannot be read by `ω(·, Q)` and must instead be read by `ω(M, ·)`. -/
theorem omega_self_pauliCondition {L : Submodule (ZMod 2) (Pauli n)}
    (hS : FTQCLib.Stabilizer.IsStabilizer L) (Q : Pauli n) {g : Pauli n}
    (hg : g ∈ FTQCLib.Stabilizer.pauliCondition L Q) : omega g Q = 0 :=
  pauliCondition_isStabilizer hS Q g hg Q (pauliCondition_mem L Q)

/-- **Reading the `Q`-coefficient.** For `g ∈ pauliCondition L Q` with `δ(g) := ω(M, g) = 1` (the
anticommuting witness `M ∈ L`, `ω(M, Q) = 1`), the shifted element `g + Q` lands back in
`K = L ⊓ Q^⊥`. In the unique decomposition `g = k + c • Q` (the summands meet in `⊥`,
`pauliCondition_K_inf_span_eq_bot`), `ω(M, ·)` reads the coefficient `c` (it vanishes on `K ⊆ L` by
isotropy and is `1` on `Q`), so `δ(g) = 1` forces `c = 1` and `g + Q = k ∈ K`. -/
theorem mem_K_of_omega_M_one {L : Submodule (ZMod 2) (Pauli n)}
    (hS : FTQCLib.Stabilizer.IsStabilizer L) {Q M : Pauli n} (hQ : Q ∉ L) (hM : M ∈ L)
    (hMQ : omega M Q = 1) {g : Pauli n} (hg : g ∈ FTQCLib.Stabilizer.pauliCondition L Q)
    (hδ : omega M g = 1) :
    g + Q ∈ L ⊓ LinearMap.BilinForm.orthogonal omegaBilin
      (Submodule.span (ZMod 2) ({Q} : Set (Pauli n))) := by
  rw [pauliCondition_of_not_mem hQ, Submodule.mem_sup] at hg
  obtain ⟨k, hk, r, hr, hkr⟩ := hg
  rw [Submodule.mem_span_singleton] at hr
  obtain ⟨c, rfl⟩ := hr
  have hkL : k ∈ L := (Submodule.mem_inf.mp hk).1
  have hMk : omega M k = 0 := hS M hM k hkL
  -- `δ(g) = ω(M, k) + c · ω(M, Q) = c`, so `c = 1`.
  have hc : c = 1 := by
    rw [← hkr, omega_add_right, omega_smul_right, hMk, hMQ, mul_one, zero_add] at hδ
    exact hδ
  subst hc
  -- `g + Q = k + 1 • Q + Q = k`.
  have hgk : k + (1 : ZMod 2) • Q + Q = k := by
    rw [one_smul, add_assoc, pauli_add_self, add_zero]
  rw [← hkr, hgk]
  exact hk

/-- **Reading the `Q`-coefficient, `δ = 0` case.** For `g ∈ pauliCondition L Q` with
`δ(g) := ω(M, g) = 0`, `g` itself lies in `K = L ⊓ Q^⊥` (hence in `L`): the coefficient `c` read by
`ω(M, ·)` is `0`, so `g = k ∈ K`. -/
theorem mem_K_of_omega_M_zero {L : Submodule (ZMod 2) (Pauli n)}
    (hS : FTQCLib.Stabilizer.IsStabilizer L) {Q M : Pauli n} (hQ : Q ∉ L) (hM : M ∈ L)
    (hMQ : omega M Q = 1) {g : Pauli n} (hg : g ∈ FTQCLib.Stabilizer.pauliCondition L Q)
    (hδ : omega M g = 0) :
    g ∈ L ⊓ LinearMap.BilinForm.orthogonal omegaBilin
      (Submodule.span (ZMod 2) ({Q} : Set (Pauli n))) := by
  rw [pauliCondition_of_not_mem hQ, Submodule.mem_sup] at hg
  obtain ⟨k, hk, r, hr, hkr⟩ := hg
  rw [Submodule.mem_span_singleton] at hr
  obtain ⟨c, rfl⟩ := hr
  have hkL : k ∈ L := (Submodule.mem_inf.mp hk).1
  have hMk : omega M k = 0 := hS M hM k hkL
  have hc : c = 0 := by
    rw [← hkr, omega_add_right, omega_smul_right, hMk, hMQ, mul_one, zero_add] at hδ
    exact hδ
  subst hc
  rw [← hkr, zero_smul, add_zero]
  exact hk

/-! ### Cross-coset phase identities (the `valid` cocycle)

All Paulis below lie in a single stabilizer (commuting) subspace `W`, so every `pauliPhase` is a
`±1` symmetric coboundary (`exists_phase_coboundary`); the identities are then pure sign
bookkeeping, exactly the phase relations consumed by the four cases of `measSignedStab.valid`. -/

/-- **The cross-coset 2-cocycle (★).** For `a, b, Q` in a common stabilizer subspace `W`,
`pauliPhase Q b · pauliPhase Q a · pauliPhase (a+Q) (b+Q) = pauliPhase a b`. This is the
`δ = (1,1)` heart of `measSignedStab.valid`: it lets the two `Q`-coset signs recombine into the
stabilizer phase `pauliPhase a b` on `K`. -/
theorem pauliPhase_cross_cocycle {W : Submodule (ZMod 2) (Pauli n)}
    (hW : FTQCLib.Stabilizer.IsStabilizer W) {a b Q : Pauli n}
    (ha : a ∈ W) (hb : b ∈ W) (hQ : Q ∈ W) :
    pauliPhase Q b * pauliPhase Q a * pauliPhase (a + Q) (b + Q) = pauliPhase a b := by
  obtain ⟨β, _, hsq, hcob⟩ := exists_phase_coboundary hW
  have haQ : a + Q ∈ W := W.add_mem ha hQ
  have hbQ : b + Q ∈ W := W.add_mem hb hQ
  rw [hcob Q hQ b hb, hcob Q hQ a ha, hcob (a + Q) haQ (b + Q) hbQ, hcob a ha b hb,
    show a + Q + (b + Q) = a + b by rw [add_add_add_comm, pauli_add_self, add_zero],
    show Q + b = b + Q from add_comm Q b, show Q + a = a + Q from add_comm Q a]
  linear_combination
    (β a * β b * β (a + b) * (β (b + Q) * β (b + Q)) * (β (a + Q) * β (a + Q))) * hsq Q hQ
    + (β a * β b * β (a + b) * (β (a + Q) * β (a + Q))) * hsq (b + Q) hbQ
    + (β a * β b * β (a + b)) * hsq (a + Q) haQ

/-- **Mixed-coset shift (1,0).** For `a, q, Q` in a common stabilizer subspace `W`,
`pauliPhase Q a · pauliPhase (a+Q) q = pauliPhase a q · pauliPhase Q (a+q)`. This is the phase
relation for the `δ = (1,0)` case of `measSignedStab.valid` (`p` on the `Q`-coset, `q` on `K`). -/
theorem pauliPhase_mix_one_zero {W : Submodule (ZMod 2) (Pauli n)}
    (hW : FTQCLib.Stabilizer.IsStabilizer W) {a q Q : Pauli n}
    (ha : a ∈ W) (hq : q ∈ W) (hQ : Q ∈ W) :
    pauliPhase Q a * pauliPhase (a + Q) q = pauliPhase a q * pauliPhase Q (a + q) := by
  obtain ⟨β, _, hsq, hcob⟩ := exists_phase_coboundary hW
  have haQ : a + Q ∈ W := W.add_mem ha hQ
  have haq : a + q ∈ W := W.add_mem ha hq
  rw [hcob Q hQ a ha, hcob (a + Q) haQ q hq, hcob a ha q hq, hcob Q hQ (a + q) haq,
    show Q + a = a + Q from add_comm Q a, show a + Q + q = a + q + Q by
      rw [add_right_comm], show Q + (a + q) = a + q + Q from add_comm Q (a + q)]
  linear_combination
    (β Q * β a * β q * β (a + q + Q)) * hsq (a + Q) haQ
    - (β Q * β a * β q * β (a + q + Q)) * hsq (a + q) haq

/-- **Mixed-coset shift (0,1).** For `p, b, Q` in a common stabilizer subspace `W`,
`pauliPhase Q b · pauliPhase p (b+Q) = pauliPhase p b · pauliPhase Q (p+b)`. This is the phase
relation for the `δ = (0,1)` case of `measSignedStab.valid` (`p` on `K`, `q` on the `Q`-coset). -/
theorem pauliPhase_mix_zero_one {W : Submodule (ZMod 2) (Pauli n)}
    (hW : FTQCLib.Stabilizer.IsStabilizer W) {p b Q : Pauli n}
    (hp : p ∈ W) (hb : b ∈ W) (hQ : Q ∈ W) :
    pauliPhase Q b * pauliPhase p (b + Q) = pauliPhase p b * pauliPhase Q (p + b) := by
  obtain ⟨β, _, hsq, hcob⟩ := exists_phase_coboundary hW
  have hbQ : b + Q ∈ W := W.add_mem hb hQ
  have hpb : p + b ∈ W := W.add_mem hp hb
  rw [hcob Q hQ b hb, hcob p hp (b + Q) hbQ, hcob p hp b hb, hcob Q hQ (p + b) hpb,
    show Q + b = b + Q from add_comm Q b, show p + (b + Q) = p + b + Q by
      rw [← add_assoc], show Q + (p + b) = p + b + Q from add_comm Q (p + b)]
  linear_combination
    (β Q * β b * β p * β (p + b + Q)) * hsq (b + Q) hbQ
    - (β Q * β b * β p * β (p + b + Q)) * hsq (p + b) hpb

/-! ### The post-measurement sign `χ'` -/

open Classical in
/-- The **post-measurement sign** `χ'` on the conditioned Lagrangian `L' = pauliCondition S.L Q`.
On `K` (the `δ = 0` part, where `g ∈ S.L`) it is the original stabilizer sign `S.sign g`; on the
`Q`-coset (`δ = ω(M, g) = 1`) it is the outcome label `ε` twisted by the stabilizer sign of
`g + Q ∈ K` and a Pauli-product phase. Off `L'` it is `0`. The anticommuting witness `M ∈ S.L`
(with `ω(M, Q) = 1`) is a parameter; `δ(g) = ω(M, g)` reads the `Q`-coset coefficient. -/
noncomputable def measSign (S : SignedStab n) (Q M : Pauli n) (ε : ℂ) : Pauli n → ℂ :=
  fun g => if g ∈ FTQCLib.Stabilizer.pauliCondition S.L Q then
    (if omega M g = 0 then S.sign g else ε * S.sign (g + Q) * pauliPhase Q (g + Q)) else 0

/-- `χ'(0) = 1`: the identity lies in `L'` (zero), `δ(0) = ω(M, 0) = 0` selects the `S.sign` branch,
and `S.sign 0 = 1`. -/
theorem measSign_zero (S : SignedStab n) (Q M : Pauli n) (ε : ℂ) :
    measSign S Q M ε 0 = 1 := by
  classical
  rw [measSign, if_pos (FTQCLib.Stabilizer.pauliCondition S.L Q).zero_mem,
    if_pos (omega_zero_right M), S.sign_zero]

/-- `χ'(Q) = ε`: the measured Pauli lies in `L'` (`pauliCondition_mem`), `δ(Q) = ω(M, Q) = 1`
selects the twisted branch, and there `ε · S.sign (Q + Q) · pauliPhase Q (Q + Q) = ε · 1 · 1`
(`pauli_add_self`, `S.sign_zero`, `pauliPhase_zero_right`). This is the `g = Q` sanity instance. -/
theorem measSign_Q (S : SignedStab n) (Q M : Pauli n) (ε : ℂ) (hMQ : omega M Q = 1) :
    measSign S Q M ε Q = ε := by
  classical
  have hne : ¬ omega M Q = 0 := by rw [hMQ]; exact one_ne_zero
  rw [measSign, if_pos (FTQCLib.Stabilizer.pauliCondition_mem S.L Q), if_neg hne, pauli_add_self,
    S.sign_zero, pauliPhase_zero_right, mul_one, mul_one]

/-- On the `δ = 0` part of `L'`, `χ'` is the original sign: for `g ∈ L'` with `ω(M, g) = 0`,
`measSign S Q M ε g = S.sign g`. -/
theorem measSign_of_zero (S : SignedStab n) (Q M : Pauli n) (ε : ℂ) {g : Pauli n}
    (hg : g ∈ FTQCLib.Stabilizer.pauliCondition S.L Q) (hδ : omega M g = 0) :
    measSign S Q M ε g = S.sign g := by
  classical
  rw [measSign, if_pos hg, if_pos hδ]

/-- On the `Q`-coset (`δ = 1`) part of `L'`, `χ'` is the `ε`-twisted sign: for `g ∈ L'` with
`ω(M, g) = 1`, `measSign S Q M ε g = ε · S.sign (g + Q) · pauliPhase Q (g + Q)`. -/
theorem measSign_of_one (S : SignedStab n) (Q M : Pauli n) (ε : ℂ) {g : Pauli n}
    (hg : g ∈ FTQCLib.Stabilizer.pauliCondition S.L Q) (hδ : omega M g = 1) :
    measSign S Q M ε g = ε * S.sign (g + Q) * pauliPhase Q (g + Q) := by
  classical
  have hne : ¬ omega M g = 0 := by rw [hδ]; exact one_ne_zero
  rw [measSign, if_pos hg, if_neg hne]

/-! ### The post-measurement signed stabilizer -/

set_option linter.unusedVariables false in
/-- **The post-measurement signed stabilizer** on `L' = pauliCondition S.L Q`. For a full Lagrangian
`S` (`IsStabilizer S.L`, `finrank S.L = n`), an outside Pauli `Q ∉ S.L` with an anticommuting
witness `M ∈ S.L` (`ω(M, Q) = 1`), and an outcome label `ε` with `ε² = 1`, this packages the
conditioned Lagrangian together with the post-measurement sign `measSign` into a genuine
`SignedStab`. The `valid` cocycle law splits, via `δ = ω(M, ·) ∈ {0, 1}`, into four cases: `(0,0)`
is `S.valid` on `K`; `(1,0)`/`(0,1)` use the mixed-coset shifts; `(1,1)` uses the cross-coset
2-cocycle `pauliPhase_cross_cocycle` together with `S.valid` and `ε² = 1`. The projector identity
`ludersChannel Q ε (stabProjector S) = ½ • stabProjector (this)` is
`ludersChannel_stabProjector_measSignedStab` below.

The full-rank hypothesis `hRank` is carried for that projector identity (it pins `L'` to a full
Lagrangian); this construction needs only the supplied witness `M`, not the existence step that
`hRank` makes available. -/
noncomputable def measSignedStab (S : SignedStab n) (hS : FTQCLib.Stabilizer.IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n} (hQ : Q ∉ S.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.L) (hMQ : omega M Q = 1) : SignedStab n where
  L := FTQCLib.Stabilizer.pauliCondition S.L Q
  sign := measSign S Q M ε
  sign_zero := measSign_zero S Q M ε
  valid := by
    intro p hp q hq
    have hL'S : FTQCLib.Stabilizer.IsStabilizer (FTQCLib.Stabilizer.pauliCondition S.L Q) :=
      pauliCondition_isStabilizer hS Q
    have hQL' : Q ∈ FTQCLib.Stabilizer.pauliCondition S.L Q :=
      FTQCLib.Stabilizer.pauliCondition_mem S.L Q
    have hpqMem : p + q ∈ FTQCLib.Stabilizer.pauliCondition S.L Q :=
      (FTQCLib.Stabilizer.pauliCondition S.L Q).add_mem hp hq
    have hpQ : p + Q ∈ FTQCLib.Stabilizer.pauliCondition S.L Q :=
      (FTQCLib.Stabilizer.pauliCondition S.L Q).add_mem hp hQL'
    have hqQ : q + Q ∈ FTQCLib.Stabilizer.pauliCondition S.L Q :=
      (FTQCLib.Stabilizer.pauliCondition S.L Q).add_mem hq hQL'
    have hδpq : omega M (p + q) = omega M p + omega M q := omega_add_right M p q
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega M p) with hp0 | hp1
    · rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega M q) with hq0 | hq1
      · -- Case (0,0): both on K, reduce to `S.valid`.
        have hpqδ : omega M (p + q) = 0 := by rw [hδpq, hp0, hq0]; rfl
        rw [measSign_of_zero S Q M ε hp hp0, measSign_of_zero S Q M ε hq hq0,
          measSign_of_zero S Q M ε hpqMem hpqδ]
        have hpS : p ∈ S.L := (Submodule.mem_inf.mp (mem_K_of_omega_M_zero hS hQ hM hMQ hp hp0)).1
        have hqS : q ∈ S.L := (Submodule.mem_inf.mp (mem_K_of_omega_M_zero hS hQ hM hMQ hq hq0)).1
        exact S.valid p hpS q hqS
      · -- Case (0,1): p on K, q on Q-coset; `b := q + Q ∈ K`.
        have hpqδ : omega M (p + q) = 1 := by rw [hδpq, hp0, hq1]; rfl
        rw [measSign_of_zero S Q M ε hp hp0, measSign_of_one S Q M ε hq hq1,
          measSign_of_one S Q M ε hpqMem hpqδ,
          show p + q + Q = p + (q + Q) by rw [add_assoc]]
        have hpS : p ∈ S.L := (Submodule.mem_inf.mp (mem_K_of_omega_M_zero hS hQ hM hMQ hp hp0)).1
        have hbS : q + Q ∈ S.L :=
          (Submodule.mem_inf.mp (mem_K_of_omega_M_one hS hQ hM hMQ hq hq1)).1
        have hmix := pauliPhase_mix_zero_one hL'S hp hqQ hQL'
        rw [show q + Q + Q = q by rw [add_assoc, pauli_add_self, add_zero]] at hmix
        have hvalid := S.valid p hpS (q + Q) hbS
        linear_combination (ε * S.sign (q + Q) * S.sign p) * hmix
          + (ε * pauliPhase Q (p + (q + Q))) * hvalid
    · rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega M q) with hq0 | hq1
      · -- Case (1,0): p on Q-coset (`a := p + Q ∈ K`), q on K.
        have hpqδ : omega M (p + q) = 1 := by rw [hδpq, hp1, hq0]; rfl
        rw [measSign_of_one S Q M ε hp hp1, measSign_of_zero S Q M ε hq hq0,
          measSign_of_one S Q M ε hpqMem hpqδ,
          show p + q + Q = p + Q + q by rw [add_right_comm]]
        have haS : p + Q ∈ S.L :=
          (Submodule.mem_inf.mp (mem_K_of_omega_M_one hS hQ hM hMQ hp hp1)).1
        have hqS : q ∈ S.L := (Submodule.mem_inf.mp (mem_K_of_omega_M_zero hS hQ hM hMQ hq hq0)).1
        have hmix := pauliPhase_mix_one_zero hL'S hpQ hq hQL'
        rw [show p + Q + Q = p by rw [add_assoc, pauli_add_self, add_zero]] at hmix
        have hvalid := S.valid (p + Q) haS q hqS
        linear_combination (ε * S.sign q * S.sign (p + Q)) * hmix
          + (ε * pauliPhase Q (p + Q + q)) * hvalid
      · -- Case (1,1): both on Q-coset; `a := p + Q, b := q + Q ∈ K`, recombine via (★).
        have hpqδ : omega M (p + q) = 0 := by rw [hδpq, hp1, hq1]; rfl
        rw [measSign_of_one S Q M ε hp hp1, measSign_of_one S Q M ε hq hq1,
          measSign_of_zero S Q M ε hpqMem hpqδ]
        have haS : p + Q ∈ S.L :=
          (Submodule.mem_inf.mp (mem_K_of_omega_M_one hS hQ hM hMQ hp hp1)).1
        have hbS : q + Q ∈ S.L :=
          (Submodule.mem_inf.mp (mem_K_of_omega_M_one hS hQ hM hMQ hq hq1)).1
        have hstar := pauliPhase_cross_cocycle hL'S hpQ hqQ hQL'
        rw [show p + Q + Q = p by rw [add_assoc, pauli_add_self, add_zero],
          show q + Q + Q = q by rw [add_assoc, pauli_add_self, add_zero]] at hstar
        have hvalid := S.valid (p + Q) haS (q + Q) hbS
        rw [show p + Q + (q + Q) = p + q by
          rw [add_add_add_comm, pauli_add_self, add_zero]] at hvalid
        linear_combination (ε * ε * S.sign (p + Q) * S.sign (q + Q)) * hstar
          + (ε * ε) * hvalid + S.sign (p + q) * hε

/-- The carrier of `measSignedStab` is the conditioned Lagrangian, definitionally. -/
@[simp] theorem measSignedStab_L (S : SignedStab n) (hS : FTQCLib.Stabilizer.IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n} (hQ : Q ∉ S.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.L) (hMQ : omega M Q = 1) :
    (measSignedStab S hS hRank hQ hε M hM hMQ).L = FTQCLib.Stabilizer.pauliCondition S.L Q := rfl

/-! ## The projector identity for the `Q ∉ L` (collapsing) branch

The selective Lüders channel `A ↦ Π_{Q,ε} A Π_{Q,ε}` applied to a full stabilizer projector
`Π_S` produces, in the genuinely collapsing case `Q ∉ L`, the projector of the post-measurement
signed stabilizer `measSignedStab` rescaled by the outcome probability `½`:
`ludersChannel Q ε Π_S = ½ • Π_{measSignedStab}`. The proof expands `Π_S` over the Hermitian-Pauli
basis, applies a per-term two-sided absorption (a Hermitian Pauli commuting with `H(Q)` passes
through `Π` and is idempotently absorbed; an anticommuting one is annihilated), and matches the
surviving coefficients against the post-measurement sign.
-/

/-! ### Per-term two-sided absorption through the Born projector

For `Q ∉ L` the surviving stabilizer generators split by their commutation with `H(Q)`. A commuting
generator (`ω(p, Q) = 0`) passes through the Born projector and is absorbed idempotently; an
anticommuting one (`ω(p, Q) = 1`) is annihilated by the projector sandwich. These are the
sign-critical building blocks of the projector identity. -/

/-- The Born projector `Π_{Q,ε} = ½(id + ε·H(Q))` commutes with a Hermitian Pauli `H(p)` whenever
`H(p)` commutes with `H(Q)`, i.e. `ω(p, Q) = 0`: `Π` is a polynomial in `H(Q)`, so it inherits the
commutation `H(p) ∘ H(Q) = H(Q) ∘ H(p)` (`pauliHermitian_comm_of_omega_zero`). -/
theorem bornProjector_comm_of_omega_zero {p Q : Pauli n} (ε : ℂ) (h : omega p Q = 0) :
    bornProjector Q ε ∘ₗ pauliHermitian p = pauliHermitian p ∘ₗ bornProjector Q ε := by
  unfold bornProjector
  rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.id_comp, LinearMap.comp_id, LinearMap.smul_comp, LinearMap.comp_smul,
    pauliHermitian_comm_of_omega_zero h]

/-- **Commuting two-sided absorption.** If `ω(p, Q) = 0` then the projector sandwich of `H(p)`
collapses by one factor: `Π_{Q,ε} ∘ H(p) ∘ Π_{Q,ε} = H(p) ∘ Π_{Q,ε}` (for `ε² = 1`). The Hermitian
Pauli commutes past the leading `Π` (`bornProjector_comm_of_omega_zero`), then the two `Π` factors
fuse by idempotence (`bornProjector_idem`). -/
theorem bornProj_sandwich_comm {p Q : Pauli n} {ε : ℂ} (hε : ε * ε = 1) (h : omega p Q = 0) :
    bornProjector Q ε ∘ₗ pauliHermitian p ∘ₗ bornProjector Q ε
      = pauliHermitian p ∘ₗ bornProjector Q ε := by
  rw [← LinearMap.comp_assoc, bornProjector_comm_of_omega_zero ε h, LinearMap.comp_assoc,
    bornProjector_idem hε]

/-- A Hermitian Pauli anticommuting with `H(Q)` flips the outcome label as it passes through the
Born projector: for `ω(p, Q) = 1`, `H(p) ∘ Π_{Q,ε} = Π_{Q,−ε} ∘ H(p)`. The leading `id` part is
unchanged while the `H(Q)` part picks up a sign from `pauliHermitian_anticomm`. -/
theorem pauliHermitian_comp_bornProjector_anti {p Q : Pauli n} (ε : ℂ) (h : omega p Q = 1) :
    pauliHermitian p ∘ₗ bornProjector Q ε = bornProjector Q (-ε) ∘ₗ pauliHermitian p := by
  unfold bornProjector
  rw [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_id, LinearMap.id_comp, LinearMap.comp_smul, LinearMap.smul_comp,
    pauliHermitian_anticomm h, smul_neg, neg_smul]

/-- The two Born effects of opposite outcome labels sum to the identity (a resolution of identity):
`Π_{Q,ε} + Π_{Q,−ε} = id`. The `H(Q)` parts cancel and the two `½·id` halves add to `id`. -/
theorem bornProjector_add_neg (Q : Pauli n) (ε : ℂ) :
    bornProjector Q ε + bornProjector Q (-ε) = LinearMap.id := by
  unfold bornProjector
  simp only [neg_smul, smul_add, smul_smul]
  module

/-- The Born projectors of opposite outcome labels are orthogonal when `ε² = 1`:
`Π_{Q,ε} ∘ Π_{Q,−ε} = 0`. Writing `Π_{Q,−ε} = id − Π_{Q,ε}` (`bornProjector_add_neg`), the product
is `Π_{Q,ε} − Π_{Q,ε}² = Π_{Q,ε} − Π_{Q,ε} = 0` by idempotence (`bornProjector_idem`). -/
theorem bornProjector_comp_neg {Q : Pauli n} {ε : ℂ} (hε : ε * ε = 1) :
    bornProjector Q ε ∘ₗ bornProjector Q (-ε) = 0 := by
  have hsplit : bornProjector Q (-ε) = LinearMap.id - bornProjector Q ε :=
    eq_sub_of_add_eq' (bornProjector_add_neg Q ε)
  rw [hsplit, LinearMap.comp_sub, LinearMap.comp_id, bornProjector_idem hε, sub_self]

/-- **Anticommuting two-sided absorption (sign-critical).** If `ω(p, Q) = 1` then the projector
sandwich of `H(p)` vanishes: `Π_{Q,ε} ∘ H(p) ∘ Π_{Q,ε} = 0` (for `ε² = 1`). The Hermitian Pauli
anticommutes with `H(Q)`, so passing it across the trailing projector flips the outcome label
(`pauliHermitian_comp_bornProjector_anti`), leaving `Π_{Q,ε} ∘ Π_{Q,−ε}`, which is zero by
orthogonality (`bornProjector_comp_neg`). The sign flip here is what pins the rescaling to `½`. -/
theorem bornProj_sandwich_anti {p Q : Pauli n} {ε : ℂ} (hε : ε * ε = 1) (h : omega p Q = 1) :
    bornProjector Q ε ∘ₗ pauliHermitian p ∘ₗ bornProjector Q ε = 0 := by
  rw [pauliHermitian_comp_bornProjector_anti ε h, ← LinearMap.comp_assoc,
    bornProjector_comp_neg hε, LinearMap.zero_comp]

/-! ### Pushing the Lüders channel through the Hermitian-Pauli expansion

The Lüders channel `A ↦ Π A Π` is `ℂ`-linear in `A`, so bundling it as a `LinearMap` lets
`map_sum`/`map_smul` push it through the finite Hermitian-Pauli expansion of `stabProjector`. -/

/-- The Lüders channel `A ↦ Π_{Q,ε} A Π_{Q,ε}` bundled as a `ℂ`-linear endomorphism of
`End (QState n)`. -/
noncomputable def ludersChannelₗ (Q : Pauli n) (ε : ℂ) :
    (QState n →ₗ[ℂ] QState n) →ₗ[ℂ] (QState n →ₗ[ℂ] QState n) where
  toFun A := ludersChannel Q ε A
  map_add' A B := by
    simp only [ludersChannel, LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c A := by
    simp only [ludersChannel, LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply]

@[simp] theorem ludersChannelₗ_apply (Q : Pauli n) (ε : ℂ) (A : QState n →ₗ[ℂ] QState n) :
    ludersChannelₗ Q ε A = ludersChannel Q ε A := rfl

/-- **Per-term Lüders action on a Hermitian Pauli.** For `ε² = 1`, the Lüders channel sends `H(p)`
to `0` if `H(p)` anticommutes with `H(Q)` (`ω(p, Q) = 1`), and otherwise to a two-term combination
on the basis coordinates `p` and `p + Q`:
`Π H(p) Π = ½·H(p) + (½·ε·pauliPhase Q p)·H(p + Q)`. The commuting case uses
`bornProj_sandwich_comm` to drop one projector, then `pauliHermitian_mul_phase` to turn
`H(p) ∘ H(Q)` into a phase times `H(p + Q)`; the anticommuting case is `bornProj_sandwich_anti`. -/
theorem ludersChannel_pauliHermitian {Q : Pauli n} {ε : ℂ} (hε : ε * ε = 1) (p : Pauli n) :
    ludersChannel Q ε (pauliHermitian p)
      = if omega p Q = 0 then
          (2⁻¹ : ℂ) • pauliHermitian p
            + ((2⁻¹ : ℂ) * ε * pauliPhase Q p) • pauliHermitian (p + Q)
        else 0 := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega p Q) with h0 | h1
  · rw [if_pos h0]
    change bornProjector Q ε ∘ₗ pauliHermitian p ∘ₗ bornProjector Q ε = _
    rw [bornProj_sandwich_comm hε h0, bornProjector, LinearMap.comp_smul, LinearMap.comp_add,
      LinearMap.comp_id, LinearMap.comp_smul, pauliHermitian_mul_phase Q p,
      show Q + p = p + Q from add_comm Q p, smul_add, smul_smul, smul_smul, mul_assoc]
  · rw [if_neg (by rw [h1]; exact one_ne_zero)]
    exact bornProj_sandwich_anti hε h1

/-! ### Coefficient matching: the post-measurement projector identity

Expanding `Π_S` over the Hermitian-Pauli basis and applying the per-term Lüders action, the
surviving contributions land on the two parts of the conditioned Lagrangian `L' = K ⊔ (K + Q)`: a
commuting
generator `p ∈ K` contributes its diagonal `½·H(p)` and a shifted `½·ε·pauliPhase·H(p + Q)` onto the
`Q`-coset. Reindexing the shift by the involution `p ↦ p + Q` and matching against the
post-measurement sign `measSign` shows both sides have the same Hermitian-Pauli coefficient. -/

/-- Pointwise coefficient identity behind the projector identity. With `S' = measSignedStab …`, the
combined Hermitian-Pauli coefficient at `q` of the expanded Lüders channel — the diagonal piece
(from term `q`) plus the shifted piece (from term `q + Q`) — equals `½·stabCoeff S' q`. The three
cases are `q ∉ L'` (everything vanishes), `q ∈ K` (diagonal only, `measSign = S.sign`), and
`q ∈ K + Q` (shifted only, `measSign` is the `ε`-twisted sign). -/
theorem measLuders_coeff_eq (S : SignedStab n) (hS : FTQCLib.Stabilizer.IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n} (hQ : Q ∉ S.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.L) (hMQ : omega M Q = 1) (q : Pauli n) :
    (if omega q Q = 0 then (2⁻¹ : ℂ) * stabCoeff S q else 0)
        + (if omega (q + Q) Q = 0 then
            (2⁻¹ : ℂ) * ε * pauliPhase Q (q + Q) * stabCoeff S (q + Q) else 0)
      = (2⁻¹ : ℂ) * stabCoeff (measSignedStab S hS hRank hQ hε M hM hMQ) q := by
  classical
  set L' := FTQCLib.Stabilizer.pauliCondition S.L Q with hL'def
  -- `(q + Q) + Q = q` and `(q + Q) + q = Q` (char two).
  have hqQQ : q + Q + Q = q := by rw [add_assoc, pauli_add_self, add_zero]
  have hqQq : q + Q + q = Q := by rw [add_right_comm, pauli_add_self, zero_add]
  -- The shift condition `ω(q+Q,Q)` collapses to `ω(q,Q)`.
  have hshiftcond : omega (q + Q) Q = omega q Q := by rw [omega_add_left, omega_self, add_zero]
  rw [hshiftcond]
  -- `stabCoeff S'` unfolds through `measSign` and `L'` membership.
  have hS'coeff : stabCoeff (measSignedStab S hS hRank hQ hε M hM hMQ) q
      = if q ∈ L' then (2 ^ n : ℂ)⁻¹ * measSign S Q M ε q else 0 := rfl
  rw [hS'coeff]
  -- Membership of `q + Q ∈ K` forces `q ∉ L` (else `Q = (q+Q) + q ∈ L`), and vice versa.
  by_cases hqL' : q ∈ L'
  · -- `q ∈ L'`: then `ω(q,Q) = 0`, so both `if`-conditions fire.
    have hqQ0 : omega q Q = 0 := omega_self_pauliCondition hS Q hqL'
    simp only [if_pos hqQ0, if_pos hqL']
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega M q) with hδ0 | hδ1
    · -- `δ = 0`: `q ∈ K ⊆ L`, and `q + Q ∉ L` so the shift coefficient vanishes.
      have hqK := mem_K_of_omega_M_zero hS hQ hM hMQ (hL'def ▸ hqL') hδ0
      have hqL : q ∈ S.L := (Submodule.mem_inf.mp hqK).1
      have hqQnL : q + Q ∉ S.L := fun hcon => hQ (hqQq ▸ S.L.add_mem hcon hqL)
      rw [measSign_of_zero S Q M ε (hL'def ▸ hqL') hδ0]
      simp only [stabCoeff, if_pos hqL, if_neg hqQnL, mul_zero, add_zero]
    · -- `δ = 1`: `q + Q ∈ K ⊆ L`, and `q ∉ L` so the diagonal coefficient vanishes.
      have hqQK := mem_K_of_omega_M_one hS hQ hM hMQ (hL'def ▸ hqL') hδ1
      have hqQL : q + Q ∈ S.L := (Submodule.mem_inf.mp hqQK).1
      have hqnL : q ∉ S.L := fun hcon => hQ (hqQq ▸ S.L.add_mem hqQL hcon)
      rw [measSign_of_one S Q M ε (hL'def ▸ hqL') hδ1]
      simp only [stabCoeff, if_neg hqnL, if_pos hqQL, mul_zero, zero_add]
      ring
  · -- `q ∉ L'`: the diagonal vanishes and the shift vanishes; split on `ω(q,Q)`.
    rw [if_neg hqL']
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega q Q) with hqQ0 | hqQ1
    · -- `ω(q,Q) = 0`: both `q ∈ L` and `q + Q ∈ L` are impossible (each would put `q ∈ L'`).
      simp only [if_pos hqQ0]
      have hKmem : ∀ x : Pauli n, x ∈ S.L → omega x Q = 0 → x ∈ L' := by
        intro x hxL hxQ
        rw [hL'def, pauliCondition_of_not_mem hQ]
        refine Submodule.mem_sup.mpr ⟨x, Submodule.mem_inf.mpr ⟨hxL, ?_⟩, 0,
          Submodule.zero_mem _, add_zero x⟩
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        change omega (c • Q) x = 0
        rw [omega_smul_left, omega_comm Q x, hxQ, mul_zero]
      have hQL' : Q ∈ L' := hL'def ▸ FTQCLib.Stabilizer.pauliCondition_mem S.L Q
      have hqnL : q ∉ S.L := fun hcon => hqL' (hKmem q hcon hqQ0)
      have hqQnL : q + Q ∉ S.L := fun hcon => by
        have hqQmem : q + Q ∈ L' := hKmem (q + Q) hcon (by rw [hshiftcond]; exact hqQ0)
        exact hqL' (hqQQ ▸ L'.add_mem hqQmem hQL')
      simp only [stabCoeff, if_neg hqnL, if_neg hqQnL, mul_zero, add_zero]
    · -- `ω(q,Q) = 1`: both `if`-conditions are false.
      have hne : ¬ (omega q Q = 0) := by rw [hqQ1]; exact one_ne_zero
      rw [if_neg hne, if_neg hne, add_zero, mul_zero]

/-- **The projector identity for the collapsing branch.** For a full Lagrangian `S`, an outside
Pauli `Q ∉ L` with anticommuting witness `M ∈ L` (`ω(M, Q) = 1`), and an outcome label `ε` with
`ε² = 1`, the selective Lüders channel applied to `Π_S` produces the post-measurement projector
rescaled by the outcome probability `½`:
`ludersChannel Q ε (stabProjector S) = ½ • stabProjector (measSignedStab …)`.

Expanding `Π_S` over the Hermitian-Pauli basis and pushing the channel through the sum, each
generator `H(p)` contributes a diagonal piece `½·H(p)` and a shifted piece on `H(p + Q)`
(`ludersChannel_pauliHermitian`); anticommuting generators vanish. Reindexing the shifted pieces by
the involution `p ↦ p + Q` and matching coefficients against the post-measurement sign
(`measLuders_coeff_eq`) recovers the rescaled projector of the conditioned signed stabilizer. -/
theorem ludersChannel_stabProjector_measSignedStab (S : SignedStab n)
    (hS : FTQCLib.Stabilizer.IsStabilizer S.L) (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n}
    (hQ : Q ∉ S.L) {ε : ℂ} (hε : ε * ε = 1) (M : Pauli n) (hM : M ∈ S.L) (hMQ : omega M Q = 1) :
    ludersChannel Q ε (stabProjector S)
      = (2⁻¹ : ℂ) • stabProjector (measSignedStab S hS hRank hQ hε M hM hMQ) := by
  classical
  set S' := measSignedStab S hS hRank hQ hε M hM hMQ with hS'def
  -- Diagonal and shifted Hermitian-Pauli coefficients of the per-term Lüders action.
  set diagC : Pauli n → ℂ := fun p => if omega p Q = 0 then (2⁻¹ : ℂ) * stabCoeff S p else 0
    with hdiagC
  set shiftC : Pauli n → ℂ :=
    fun p => if omega p Q = 0 then (2⁻¹ : ℂ) * ε * pauliPhase Q p * stabCoeff S p else 0
    with hshiftC
  -- Per-term decomposition of `stabCoeff S p • (Π H(p) Π)` onto coordinates `p` and `p + Q`.
  have hterm : ∀ p : Pauli n, stabCoeff S p • ludersChannel Q ε (pauliHermitian p)
      = diagC p • pauliHermitian p + shiftC p • pauliHermitian (p + Q) := by
    intro p
    rw [ludersChannel_pauliHermitian hε p, hdiagC, hshiftC]
    by_cases hpq : omega p Q = 0
    · simp only [if_pos hpq, smul_add, smul_smul]
      congr 2 <;> ring
    · simp only [if_neg hpq, smul_zero, zero_smul, add_zero]
  -- LHS: expand `Π_S`, push the channel through the sum, decompose each term.
  have hLHS : ludersChannel Q ε (stabProjector S)
      = (∑ p : Pauli n, diagC p • pauliHermitian p)
        + ∑ p : Pauli n, shiftC p • pauliHermitian (p + Q) := by
    rw [← ludersChannelₗ_apply, stabProjector_eq_sum_univ S, map_sum]
    simp only [map_smul, ludersChannelₗ_apply, hterm]
    rw [Finset.sum_add_distrib]
  -- Reindex the shifted sum by the involution `p ↦ p + Q`.
  have hreindex : (∑ p : Pauli n, shiftC p • pauliHermitian (p + Q))
      = ∑ q : Pauli n, shiftC (q + Q) • pauliHermitian q := by
    rw [← Equiv.sum_comp (Equiv.addRight Q)
      (fun q => shiftC q • pauliHermitian (q + Q))]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [Equiv.coe_addRight]
    rw [show q + Q + Q = q by rw [add_assoc, pauli_add_self, add_zero]]
  -- RHS: expand the rescaled projector of `S'` over the basis.
  have hRHS : (2⁻¹ : ℂ) • stabProjector S'
      = ∑ q : Pauli n, ((2⁻¹ : ℂ) * stabCoeff S' q) • pauliHermitian q := by
    rw [stabProjector_eq_sum_univ S', Finset.smul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [smul_smul]
  rw [hLHS, hreindex, hRHS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← add_smul]
  congr 1
  exact measLuders_coeff_eq S hS hRank hQ hε M hM hMQ q

/-! ### The existence wrapper: the `Q ∉ L` measurement-collapse branch

For a full Lagrangian `S` and an outside Pauli `Q ∉ L`, measuring `H(Q)` with any unit-square
outcome label `ε` collapses the stabilizer projector to (half) the projector of a *new* full
Lagrangian — the conditioned `pauliCondition S.L Q` — equipped with the post-measurement sign. The
witness is `measSignedStab` for the anticommuting `M` supplied by
`exists_anticommuting_of_not_mem_full`. -/

/-- **Measurement collapse, `Q ∉ L` branch (existence form).** For a full Lagrangian `S`, an outside
Pauli `Q ∉ L`, and an outcome label `ε` with `ε² = 1`, the selective Lüders channel sends the
stabilizer projector to `½` times the projector of a new signed stabilizer on the conditioned
Lagrangian `pauliCondition S.L Q`. This is the genuinely collapsing (non-deterministic) measurement
case: the stabilizer group is updated by adjoining `Q` and removing the anticommuting generators,
with the new sign recording the outcome `ε`. The anticommuting witness is supplied by
`exists_anticommuting_of_not_mem_full` and the projector identity by
`ludersChannel_stabProjector_measSignedStab`. -/
theorem ludersChannel_stabProjector_notMem (S : SignedStab n)
    (hS : FTQCLib.Stabilizer.IsStabilizer S.L)
    (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n} (hQ : Q ∉ S.L) {ε : ℂ} (hε : ε * ε = 1) :
    ∃ S' : SignedStab n,
      S'.L = FTQCLib.Stabilizer.pauliCondition S.L Q ∧
      ludersChannel Q ε (stabProjector S) = (2⁻¹ : ℂ) • stabProjector S' := by
  obtain ⟨M, hM, hMQ⟩ := exists_anticommuting_of_not_mem_full hS hRank hQ
  exact ⟨measSignedStab S hS hRank hQ hε M hM hMQ, measSignedStab_L S hS hRank hQ hε M hM hMQ,
    ludersChannel_stabProjector_measSignedStab S hS hRank hQ hε M hM hMQ⟩

/-- **Measurement collapse, `Q ∉ L`, outcome `ε = +1`.** The `+1` instance of
`ludersChannel_stabProjector_notMem`. -/
theorem ludersChannel_stabProjector_notMem_pos (S : SignedStab n)
    (hS : FTQCLib.Stabilizer.IsStabilizer S.L) (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n}
    (hQ : Q ∉ S.L) :
    ∃ S' : SignedStab n,
      S'.L = FTQCLib.Stabilizer.pauliCondition S.L Q ∧
      ludersChannel Q 1 (stabProjector S) = (2⁻¹ : ℂ) • stabProjector S' :=
  ludersChannel_stabProjector_notMem S hS hRank hQ (by norm_num)

/-- **Measurement collapse, `Q ∉ L`, outcome `ε = −1`.** The `−1` instance of
`ludersChannel_stabProjector_notMem`. -/
theorem ludersChannel_stabProjector_notMem_neg (S : SignedStab n)
    (hS : FTQCLib.Stabilizer.IsStabilizer S.L) (hRank : finrank (ZMod 2) S.L = n) {Q : Pauli n}
    (hQ : Q ∉ S.L) :
    ∃ S' : SignedStab n,
      S'.L = FTQCLib.Stabilizer.pauliCondition S.L Q ∧
      ludersChannel Q (-1) (stabProjector S) = (2⁻¹ : ℂ) • stabProjector S' :=
  ludersChannel_stabProjector_notMem S hS hRank hQ (by norm_num)

end FTQCLib.Hilbert

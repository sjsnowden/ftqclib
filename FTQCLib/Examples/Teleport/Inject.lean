/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.SGadget

/-! # The composable gate-injection object

The Z-teleportation and S-gadget constructions share one skeleton — input full-Lagrangian state →
(Clifford entangle) → condition on an ancilla observable → read transported support + feed-forward sign
— but were each hand-assembled. This file factors that skeleton into ONE parameterized object, of which
the existing gadgets become *instances*.

Design: the sign-bearing object is a bespoke invariant-carrying step on `PureSignedStab` (the
carried `isStab`/`full` discharge the per-call `IsStabilizer`/`finrank` obligations; the
anticommuting witness is *derived* via `exists_anticommuting_of_not_mem_full`). This keeps `.sign` a
literal `measSign`, so feed-forward is a one-line corollary — the part that a pure operation-monoid
*word* cannot expose cleanly (its Lüders action returns `tighten (.choose …)`, severing the output
sign from `measSign`). The final section reconciles the two: the S-gadget is shown to be an
operation-monoid word *with* a readable sign.

The object is instantiated on the **S-gadget** (the harder, Clifford-entangled gadget):
`SoutS_sign_Yd_via_object` reproduces `SInjection.SoutS_sign_Yd` as an instance of the object, not a
hand-assembled `measSignedStab` term. -/

namespace FTQCLib.Inject

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Teleport FTQCLib.Hilbert FTQCLib.Gates FTQCLib.SInjection

/-! ## The input factory -/

/-- Build a pure signed Lagrangian from any stabilizer Lagrangian: the canonical valid sign, junk
zeroed off `L`. This is the shared constructor the per-gadget inputs (`SinPure`, `SinS`) were each
spelling out by hand. -/
noncomputable def mkPureSlab {n : ℕ} {L : Submodule (ZMod 2) (Pauli n)}
    (hStab : IsStabilizer L) (hRank : Module.finrank (ZMod 2) L = n) : PureSignedStab n :=
  ⟨tighten (refStab hStab),
    by rw [tighten_L]; exact hStab,
    by rw [tighten_L]; exact hRank,
    fun p hp => tighten_sign_not_mem _ hp⟩

/-- The S-gadget input is literally an instance of the factory (the duplication is removed). -/
example : SinS = mkPureSlab Lin_S_isStabilizer Lin_S_finrank := rfl

/-! ## The conditioning step (explicit witness): the de-atomizer

`measSignedStab` re-wrapped into the invariant-carrying carrier. The caller supplies only the measured
`Q`, the outcome `ε` (`ε²=1`), the off-membership `hQ`, and an anticommuting witness `(M, hM, hMQ)`; the
output's `isStab`/`full`/`tight` are re-established from the carried invariants. The witness is named so
that `.sign` stays an explicit `measSign` (this is what makes feed-forward readable). -/
noncomputable def injStepWith {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1) : PureSignedStab n :=
  ⟨measSignedStab S.toSignedStab S.isStab S.full hQ hε M hM hMQ,
    pauliCondition_isStabilizer S.isStab Q,
    pauliCondition_finrank S.isStab S.full Q,
    fun p hp => by
      have hp' : p ∉ pauliCondition S.toSignedStab.L Q := hp
      change measSign S.toSignedStab Q M ε p = 0
      unfold measSign
      rw [if_neg hp']⟩

/-- The conditioned Lagrangian is `pauliCondition` of the input's. -/
@[simp] theorem injStepWith_L {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1) :
    (injStepWith S hQ hε M hM hMQ).toSignedStab.L = pauliCondition S.toSignedStab.L Q := rfl

/-- **Feed-forward (the random/Q-coset branch).** On a generator `g` in the conditioned
Lagrangian with `ω(M,g)=1`, the outcome `ε` is a free factor in the sign — everything else
is `ε`-independent. This is the one-line corollary the whole design exists to keep. -/
theorem injStepWith_sign_of_one {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1)
    {g : Pauli n} (hg : g ∈ pauliCondition S.toSignedStab.L Q) (hδ : omega M g = 1) :
    (injStepWith S hQ hε M hM hMQ).toSignedStab.sign g
      = ε * S.toSignedStab.sign (g + Q) * pauliPhase Q (g + Q) := by
  change measSign S.toSignedStab Q M ε g = _
  exact measSign_of_one S.toSignedStab Q M ε hg hδ

/-- The determined/kept-slice branch (`ω(M,g)=0`): the sign passes through unchanged. -/
theorem injStepWith_sign_of_zero {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1)
    {g : Pauli n} (hg : g ∈ pauliCondition S.toSignedStab.L Q) (hδ : omega M g = 0) :
    (injStepWith S hQ hε M hM hMQ).toSignedStab.sign g = S.toSignedStab.sign g := by
  change measSign S.toSignedStab Q M ε g = _
  exact measSign_of_zero S.toSignedStab Q M ε hg hδ

/-- **The measured generator reads off its outcome.** Conditioning on `Q` (outcome `ε`) sets `Q`'s own
post-measurement sign to exactly `ε`: `Q` lies on its own `ε`-coset (`g = Q`, so `ω(M,Q)=1`), and
`Q + Q = 0` collapses the input-sign and cocycle factors to `1`. The conditioner-agnostic kernel the
conditioning truth tables (`sign gᵢ = sᵢ`, reference = the all-`+1` codeword) rest on — and the
`g = Q` specialisation of the same `injStepWith_sign_of_one` free factor the feed-forward ratios use. -/
theorem injStepWith_sign_self {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    (M : Pauli n) (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1) :
    (injStepWith S hQ hε M hM hMQ).toSignedStab.sign Q = ε := by
  rw [injStepWith_sign_of_one S hQ hε M hM hMQ (pauliCondition_mem _ _) hMQ,
      pauli_add_self, S.toSignedStab.sign_zero, pauliPhase_zero_right]
  ring

/-! ## The conditioning step (derived witness): no witness obligation at all

For a Lagrangian, `Q ∉ L` *forces* an anticommuting witness to exist, so `injStep` derives it —
the caller supplies only `Q`, `ε`, `hQ`. (Its `.sign` corollaries are stated against the derived
witness; the explicit-witness `injStepWith` form reproduces named-witness theorems verbatim.) -/
noncomputable def injStep {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1) : PureSignedStab n :=
  injStepWith S hQ hε
    (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose
    (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose_spec.1
    (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose_spec.2

@[simp] theorem injStep_L {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1) :
    (injStep S hQ hε).toSignedStab.L = pauliCondition S.toSignedStab.L Q := rfl

/-! ## Witness-independence: `injStep` is canonical

The post-measurement sign cannot depend on *which* anticommuting witness is chosen: on the conditioned
Lagrangian, `ω(M, g)` reads only `g`'s `Q`-coset. For two valid witnesses `M, M'`, the sum `M + M'`
commutes with `Q` (`ω = 1+1 = 0`), so it lies in the conditioned Lagrangian — which is isotropic — hence
`ω(M+M', g) = 0`, i.e. `ω(M,g) = ω(M',g)`. So `measSign` is witness-independent, and the explicit-witness
step equals the derived-witness `injStep`. This makes `injStep` a genuine function of `(Q, ε)` alone, and
is the key the operation-monoid bridge needs to identify the word's `.choose`-witness output. -/

/-- The coset reading `ω(M, ·)` on the conditioned Lagrangian is independent of the witness `M`. -/
theorem omega_witness_indep {n : ℕ} {S : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer S)
    {Q : Pauli n} (hQ : Q ∉ S) {M M' : Pauli n} (hM : M ∈ S) (hMQ : omega M Q = 1)
    (hM' : M' ∈ S) (hM'Q : omega M' Q = 1) {g : Pauli n} (hg : g ∈ pauliCondition S Q) :
    omega M g = omega M' g := by
  have hwQ : omega Q (M + M') = 0 := by
    rw [omega_comm, omega_add_left, hMQ, hM'Q]; decide
  have hwmem : M + M' ∈ pauliCondition S Q :=
    mem_pauliCondition_of_commute hQ (S.add_mem hM hM') hwQ
  have hzero : omega (M + M') g = 0 :=
    pauliCondition_isStabilizer hS Q (M + M') hwmem g hg
  rw [omega_add_left] at hzero
  exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ hzero

/-- `measSign` does not depend on the choice of anticommuting witness. -/
theorem measSign_witness_indep {n : ℕ} (S : SignedStab n) (hS : IsStabilizer S.L)
    {Q : Pauli n} (hQ : Q ∉ S.L) (ε : ℂ) {M M' : Pauli n} (hM : M ∈ S.L) (hMQ : omega M Q = 1)
    (hM' : M' ∈ S.L) (hM'Q : omega M' Q = 1) :
    measSign S Q M ε = measSign S Q M' ε := by
  funext g
  simp only [measSign]
  by_cases hg : g ∈ pauliCondition S.L Q
  · rw [if_pos hg, if_pos hg, omega_witness_indep hS hQ hM hMQ hM' hM'Q hg]
  · rw [if_neg hg, if_neg hg]

/-- Hence the conditioned state itself is witness-independent. -/
theorem measSignedStab_witness_indep {n : ℕ} (S : SignedStab n) (hS : IsStabilizer S.L)
    (hRank : Module.finrank (ZMod 2) S.L = n) {Q : Pauli n} (hQ : Q ∉ S.L) {ε : ℂ} (hε : ε * ε = 1)
    {M M' : Pauli n} (hM : M ∈ S.L) (hMQ : omega M Q = 1)
    (hM' : M' ∈ S.L) (hM'Q : omega M' Q = 1) :
    measSignedStab S hS hRank hQ hε M hM hMQ = measSignedStab S hS hRank hQ hε M' hM' hM'Q :=
  signedStab_ext rfl (measSign_witness_indep S hS hQ ε hM hMQ hM' hM'Q)

/-- **`injStep` is canonical:** the explicit-witness step equals the derived-witness `injStep`,
whichever valid witness is supplied. -/
theorem injStepWith_eq_injStep {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    {M : Pauli n} (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1) :
    injStepWith S hQ hε M hM hMQ = injStep S hQ hε :=
  pureSignedStab_ext
    (measSignedStab_witness_indep S.toSignedStab S.isStab S.full hQ hε hM hMQ
      (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose_spec.1
      (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose_spec.2)

/-! ## The Clifford entangle step (the uniform object surface for S/T) -/

/-- The Clifford-conjugation phase of a gadget (the CNOT entangle), as a `PureSignedStab` map. -/
noncomputable def injClifford {n : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : PureSignedStab n) : PureSignedStab n :=
  cliffordActionPure hU S

/-- The entangle step transforms `L` by the symplectic image of the Clifford. -/
theorem injClifford_L {n : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : PureSignedStab n) :
    (injClifford hU S).toSignedStab.L
      = Submodule.map (cliffordToSymplectic hU).toLinearMap S.toSignedStab.L :=
  cliffordAction_L hU S.toSignedStab

/-! ## Instance: the S-gadget, re-derived from the object

`SInjection.SoutS_sign_Yd` was a hand-assembled `measSignedStab` term over `cliffordAction`.
Here the same feed-forward sign falls out of `injClifford` + `injStepWith` +
`injStepWith_sign_of_one` — the gadget is an instance of the object, not a bespoke chain. -/

/-- The S-gadget's post-measurement state, as the object: entangle (CNOT) then condition on `Z₁`. -/
noncomputable def SoutS' (m : ℂ) (hm : m * m = 1) : PureSignedStab 2 :=
  injStepWith (injClifford (isCliffordOperator_cnotGate 0 1 (by decide)) SinS)
    (by
      change Za ∉ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L
      rw [Scnot_L]; exact Za_not_mem)
    hm gA
    (by
      change gA ∈ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L
      rw [Scnot_L]; exact gA_mem)
    (by decide)

/-- **The S-gadget feed-forward, as an instance of the object.** Matches `SInjection.SoutS_sign_Yd`
verbatim, but derived from the generic `injStepWith_sign_of_one` rather than a hand-built term. -/
theorem SoutS_sign_Yd_via_object (m : ℂ) (hm : m * m = 1) :
    (SoutS' m hm).toSignedStab.sign Yd
      = m * (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).sign
              (Yd + Za)
          * pauliPhase Za (Yd + Za) :=
  injStepWith_sign_of_one
    (injClifford (isCliffordOperator_cnotGate 0 1 (by decide)) SinS)
    (by
      change Za ∉ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L
      rw [Scnot_L]; exact Za_not_mem)
    hm gA
    (by
      change gA ∈ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L
      rw [Scnot_L]; exact gA_mem)
    (by decide)
    (by
      change Yd ∈ pauliCondition
        (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L Za
      rw [Scnot_L]; exact Yd_mem)
    (by decide)

/-! ## The operation-monoid bridge

The conditioning step is not merely *like* the operation monoid — it *is* it. The selective Lüders
generator `ludersChannelₗ Q ε`, acting on the pointed carrier, equals (weight-halved) `injStep`. The
existing `operationMonoid_luders_notMem_smul` states this only existentially (`∃ S'`); here the output is
pinned to the canonical `injStep`, because `injStep` uses the very witness the action's projector
identity (`ludersChannel_stabProjector_measSignedStab`) is computed against. So a gadget written as a
*word* in the monoid now has its feed-forward sign readable through `injStep` — the bridge toward
gadgets-are-words-with-readable-signs. -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **The Lüders generator acts as (weight-halved) `injStep`.** The monoid word's output is the
canonical conditioning step, not just *some* state of the right Lagrangian. -/
theorem operationMonoid_luders_smul_injStep {n : ℕ} (c : ℂˣ) (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1) :
    (⟨ludersChannelₗ Q ε, ludersChannelₗ_mem_operationMonoid Q hε⟩ : operationMonoid n)
        • some (c, S)
      = some (Units.mk0 ((c : ℂ) / 2) (div_ne_zero c.ne_zero two_ne_zero), injStep S hQ hε) := by
  change psiEquiv.symm ((⟨ludersChannelₗ Q ε, ludersChannelₗ_mem_operationMonoid Q hε⟩
      : operationMonoid n) • psiEquiv (some (c, S))) = _
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  change ludersChannelₗ Q ε ((psiEquiv (some (c, S))).1) = _
  simp only [psiEquiv_apply, psi_some, ludersChannelₗ_apply, Units.val_mk0]
  rw [← ludersChannelₗ_apply, map_smul, ludersChannelₗ_apply,
    ludersChannel_stabProjector_measSignedStab S.toSignedStab S.isStab S.full hQ hε
      (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose
      (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose_spec.1
      (exists_anticommuting_of_not_mem_full S.isStab S.full hQ).choose_spec.2,
    smul_smul, div_eq_mul_inv]
  rfl

/-! ## The S-gadget IS an operation-monoid word, with readable sign

The obstruction to building S as a word, rather than directly, is removed here. Package `cnotGate` as a
`cliffordSubgroup` element and the S-gadget becomes the word `(ludersₗ Z₁ m) * (qConjₗ CNOT)` acting on
the input — and it evaluates, by the two bridge lemmas + canonicality, to exactly the S-gadget state
`SoutS'` (Born weight ½). Its `Yd`-sign is then `SoutS_sign_Yd_via_object` (`m · (…) · pauliPhase`). So
the S-gadget is a word *with* readable feed-forward, on the gadget where the naive monoid route
loses the sign. -/

/-- `CNOT(0→1)` packaged as a Clifford-group element (`mem_cliffordSubgroup` is `Iff.rfl`). -/
noncomputable def Ucnot : cliffordSubgroup 2 :=
  ⟨cnotGate 0 1 (by decide), isCliffordOperator_cnotGate 0 1 (by decide)⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- The S-gadget as a single word in the operation monoid: entangle by `qConjₗ CNOT`, then measure by
the selective Lüders `ludersₗ Z₁` (outcome `m`). -/
noncomputable def sWord (m : ℂ) (hm : m * m = 1) : Option (ℂˣ × PureSignedStab 2) :=
  (⟨ludersChannelₗ Za m, ludersChannelₗ_mem_operationMonoid Za hm⟩
      * ⟨qConjₗ Ucnot.1, qConjₗ_mem_operationMonoid Ucnot⟩ : operationMonoid 2)
    • some (1, SinS)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The S-gadget word evaluates to the S-gadget state** (`SoutS'`, Born weight ½) — so a gadget is a
word, and (via `SoutS_sign_Yd_via_object`) its feed-forward sign is readable. -/
theorem sWord_eq (m : ℂ) (hm : m * m = 1) :
    sWord m hm = some (Units.mk0 (2⁻¹ : ℂ) (by norm_num), SoutS' m hm) := by
  have hQ : Za ∉ (cliffordActionPure Ucnot.2 SinS).toSignedStab.L := by
    change Za ∉ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L
    rw [Scnot_L]; exact Za_not_mem
  have hgA : gA ∈ (cliffordActionPure Ucnot.2 SinS).toSignedStab.L := by
    change gA ∈ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L
    rw [Scnot_L]; exact gA_mem
  have hstate : injStep (cliffordActionPure Ucnot.2 SinS) hQ hm = SoutS' m hm :=
    (injStepWith_eq_injStep (cliffordActionPure Ucnot.2 SinS) hQ hm hgA (by decide)).symm
  rw [sWord, mul_smul, operationMonoid_clifford_smul Ucnot 1 SinS,
    operationMonoid_luders_smul_injStep 1 (cliffordActionPure Ucnot.2 SinS) hQ hm, hstate,
    Option.some.injEq, Prod.mk.injEq]
  exact ⟨Units.ext (by simp), rfl⟩

/-! ## S† falls out: a second gate is just a new input

The de-atomization claim, stress-tested. `S†` differs from `S` only in the ancilla *resource* — `|−i⟩`
(stab `−Y₁`) instead of `|+i⟩` (stab `+Y₁`), i.e. the ancilla `Z₁`-conjugated. The support transport
and the gadget word are *identical* (`S` and `S†` both send `X₀ → Y₀` as 𝔽₂ vectors; `(S†)² = Z = S²`).
So `S†` is the *same word* on a *different input* `SinSdag`, with **no new gadget-specific machinery** —
only the input changes, and every generic lemma (`injClifford`, both bridges, canonicality) applies
verbatim. The `Z₁`-flip preserves `L` because Pauli conjugation is symplectically trivial
(`cliffordToSymplectic_pauliEquiv`). -/

/-- The S†-gadget input: `SinS`'s ancilla `Z₁`-conjugated (`|+i⟩ → |−i⟩`, stab `+Y₁ → −Y₁`). A genuinely
different `PureSignedStab` — the conjugate phase-gate resource. -/
noncomputable def SinSdag : PureSignedStab 2 :=
  injClifford (isCliffordOperator_pauliEquiv (pauliz 1)) SinS

/-- The `Z₁`-flip preserves the support (Pauli conjugation is symplectically trivial). -/
theorem SinSdag_L : SinSdag.toSignedStab.L = Lin_S := by
  unfold SinSdag
  rw [injClifford_L, cliffordToSymplectic_pauliEquiv, SinS_L]
  simp

/-- The CNOT transport of the S†-input lands on the same `Lcnot` (the support is gate-agnostic). -/
theorem ScnotDag_L :
    (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L = Lcnot := by
  have hX : (cliffordToSymplectic (isCliffordOperator_cnotGate (0 : Fin 2) 1 (by decide))).toLinearMap
      Xd = gA := by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]
    decide
  have hY : (cliffordToSymplectic (isCliffordOperator_cnotGate (0 : Fin 2) 1 (by decide))).toLinearMap
      Ya = gB := by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]
    decide
  rw [cliffordAction_L, SinSdag_L]
  unfold Lin_S Lcnot
  rw [Submodule.map_span, Set.image_pair, hX, hY]

/-- The S†-gadget post-measurement state — the *same* `injClifford`+`injStepWith` as S, on `SinSdag`. -/
noncomputable def SoutSdag' (m : ℂ) (hm : m * m = 1) : PureSignedStab 2 :=
  injStepWith (injClifford (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag)
    (by
      change Za ∉ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L
      rw [ScnotDag_L]; exact Za_not_mem)
    hm gA
    (by
      change gA ∈ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L
      rw [ScnotDag_L]; exact gA_mem)
    (by decide)

/-- **The S†-gadget feed-forward is readable**, the same one-line corollary as S — only the
`m`-independent factor differs (the flipped resource sign). -/
theorem SoutSdag_sign_Yd (m : ℂ) (hm : m * m = 1) :
    (SoutSdag' m hm).toSignedStab.sign Yd
      = m * (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).sign
              (Yd + Za)
          * pauliPhase Za (Yd + Za) :=
  injStepWith_sign_of_one
    (injClifford (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag)
    (by
      change Za ∉ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L
      rw [ScnotDag_L]; exact Za_not_mem)
    hm gA
    (by
      change gA ∈ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L
      rw [ScnotDag_L]; exact gA_mem)
    (by decide)
    (by
      change Yd ∈ pauliCondition
        (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L Za
      rw [ScnotDag_L]; exact Yd_mem)
    (by decide)

set_option synthInstance.maxHeartbeats 400000 in
/-- The S†-gadget as a word — the *same* word as S (`sWord`), only the input `SinS → SinSdag`. -/
noncomputable def sWordDag (m : ℂ) (hm : m * m = 1) : Option (ℂˣ × PureSignedStab 2) :=
  (⟨ludersChannelₗ Za m, ludersChannelₗ_mem_operationMonoid Za hm⟩
      * ⟨qConjₗ Ucnot.1, qConjₗ_mem_operationMonoid Ucnot⟩ : operationMonoid 2)
    • some (1, SinSdag)

set_option synthInstance.maxHeartbeats 400000 in
/-- **The S†-gadget word evaluates to the S†-gadget state** — same proof as `sWord_eq`, different input.
A second gate, for the price of one new `def`. -/
theorem sWordDag_eq (m : ℂ) (hm : m * m = 1) :
    sWordDag m hm = some (Units.mk0 (2⁻¹ : ℂ) (by norm_num), SoutSdag' m hm) := by
  have hQ : Za ∉ (cliffordActionPure Ucnot.2 SinSdag).toSignedStab.L := by
    change Za ∉ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L
    rw [ScnotDag_L]; exact Za_not_mem
  have hgA : gA ∈ (cliffordActionPure Ucnot.2 SinSdag).toSignedStab.L := by
    change gA ∈ (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).L
    rw [ScnotDag_L]; exact gA_mem
  have hstate : injStep (cliffordActionPure Ucnot.2 SinSdag) hQ hm = SoutSdag' m hm :=
    (injStepWith_eq_injStep (cliffordActionPure Ucnot.2 SinSdag) hQ hm hgA (by decide)).symm
  rw [sWordDag, mul_smul, operationMonoid_clifford_smul Ucnot 1 SinSdag,
    operationMonoid_luders_smul_injStep 1 (cliffordActionPure Ucnot.2 SinSdag) hQ hm, hstate,
    Option.some.injEq, Prod.mk.injEq]
  exact ⟨Units.ext (by simp), rfl⟩

/-! ## Pinning S† = −S: the resource-sign flip is visible at the output

The de-atomization above shows S† is the same word on a new input; this pins the *gate identity* — the
S†-gadget's feed-forward is exactly `−` the S-gadget's. The mechanism: the `Z₁`-conjugation flips the
sign of every element anticommuting with `Z₁` (`cliffordSign` of a Pauli conjugation is the commutation
phase `(−1)^ω`), and the relevant element `Xd+Ya` anticommutes with `Z₁`. -/

/-- The conjugation sign of a Pauli conjugation is the commutation phase `(−1)^{ω(r,p)}` (the symplectic
part is trivial, so the `Iˣᶻ` renormalizations cancel and only the phase survives). -/
theorem cliffordSign_pauliEquiv {n : ℕ} (r p : Pauli n) :
    cliffordSign (isCliffordOperator_pauliEquiv r) p = (-1 : ℂ) ^ (omega r p).val := by
  have hΦ : cliffordToSymplecticFun (isCliffordOperator_pauliEquiv r) p = p := by
    rw [← cliffordToSymplectic_apply, cliffordToSymplectic_pauliEquiv]; rfl
  rw [cliffordSign, hΦ, phase_pauliEquiv_eq, mul_right_comm,
    mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]

/-- A Pauli conjugation flips the sign exactly on the elements anticommuting with the Pauli (the support
is unchanged, so it reads the same element). -/
theorem cliffordAction_pauliEquiv_sign {n : ℕ} (r : Pauli n) (S : SignedStab n) (q : Pauli n) :
    (cliffordAction (isCliffordOperator_pauliEquiv r) S).sign q
      = (-1 : ℂ) ^ (omega r q).val * S.sign q := by
  have hΦ : (cliffordToSymplectic (isCliffordOperator_pauliEquiv r)).symm q = q := by
    rw [cliffordToSymplectic_pauliEquiv]; rfl
  rw [cliffordAction_sign, hΦ, cliffordSign_pauliEquiv]

/-- The S†-gadget's `m`-independent factor is `−` the S-gadget's: `Z₁` flips the sign of `Xd+Ya`
(which `ω(Z₁, Xd+Ya) = 1` certifies), and that is what the CNOT-transported `Yd+Za` reads. -/
theorem negFactor :
    (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinSdag.toSignedStab).sign (Yd + Za)
      = -(cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).sign
            (Yd + Za) := by
  have hΦinv :
      (cliffordToSymplectic (isCliffordOperator_cnotGate (0 : Fin 2) 1 (by decide))).symm (Yd + Za)
        = Xd + Ya := by
    rw [LinearEquiv.symm_apply_eq, map_add, cliffordToSymplectic_apply, cliffordToSymplectic_apply,
      cliffordToSymplecticFun_cnot, cliffordToSymplecticFun_cnot]
    decide
  have hexp : (-1 : ℂ) ^ (omega (pauliz 1) (Xd + Ya)).val = -1 := by
    norm_num [show (omega (pauliz 1) (Xd + Ya)).val = 1 from by decide]
  show (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide))
        (cliffordAction (isCliffordOperator_pauliEquiv (pauliz 1)) SinS.toSignedStab)).sign (Yd + Za)
      = -(cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).sign
            (Yd + Za)
  rw [cliffordAction_sign, cliffordAction_pauliEquiv_sign, cliffordAction_sign, hΦinv, hexp]
  ring

/-- **The S†-gadget feed-forward is exactly `−` the S-gadget's** — same outcome `m`, opposite sign. This
pins the gate identity: the gadget on `SinSdag` is the conjugate phase gate. -/
theorem SoutSdag_sign_Yd_eq_neg (m : ℂ) (hm : m * m = 1) :
    (SoutSdag' m hm).toSignedStab.sign Yd = -(SoutS' m hm).toSignedStab.sign Yd := by
  rw [SoutSdag_sign_Yd, SoutS_sign_Yd_via_object, negFactor]; ring

end FTQCLib.Inject

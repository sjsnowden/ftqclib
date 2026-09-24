/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.Inject

/-! # Entanglement swapping (the remote Bell pair) in the `(L,χ)` frame

Four qubits: data `a = 0`, photons `pA = 1`, `pB = 2`, data `b = 3`. The input is two Bell pairs —
matter–photon `(a, pA)` and photon–matter `(pB, b)`. A Bell-state measurement on the *inner*
photons `pA, pB` (conditioning on `X_{pA}X_{pB}` then `Z_{pA}Z_{pB}`) entangles the two distant
matter qubits `a, b`, which never interacted: afterwards `X_aX_b` and `Z_aZ_b` both stabilize the
state, so `(a,b)` is a Bell pair. The two measurement outcomes `(a,b)` form the **herald** — they
name *which* of the four Bell states the distant pair lands in, and they are forced into the signs
of `X_aX_b`, `Z_aZ_b`.

This is a 4-qubit instance of the teleportation conditioning (`ZTeleport.lean`), with one new
feature: the measurement here *creates* entanglement between qubits that never interacted, where
teleportation only *moved* a state. It also fixes the loop condition for the next step (the
`μ`-operator): a designated herald outcome counts as "success" (keep), the rest as "retry"
(reset). -/

namespace FTQCLib.EntSwap

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Teleport FTQCLib.Hilbert FTQCLib.Inject

/-! ## The encoding

`a = 0`, `pA = 1`, `pB = 2`, `b = 3`. Input generators are the two Bell pairs; the Bell measurement
is on the inner photons `pA, pB`. -/

/-- Input Bell-pair generator `X_aX_{pA}`. -/
def XXaA : Pauli 4 := paulix 0 + paulix 1
/-- Input Bell-pair generator `Z_aZ_{pA}`. -/
def ZZaA : Pauli 4 := pauliz 0 + pauliz 1
/-- Input Bell-pair generator `X_{pB}X_b`. -/
def XXBb : Pauli 4 := paulix 2 + paulix 3
/-- Input Bell-pair generator `Z_{pB}Z_b`. -/
def ZZBb : Pauli 4 := pauliz 2 + pauliz 3
/-- First Bell-measurement observable `X_{pA}X_{pB}` (outcome `a`). -/
def Qa : Pauli 4 := paulix 1 + paulix 2
/-- Second Bell-measurement observable `Z_{pA}Z_{pB}` (outcome `b`). -/
def Qb : Pauli 4 := pauliz 1 + pauliz 2
/-- The created distant generator `X_aX_b`. -/
def XaXb : Pauli 4 := paulix 0 + paulix 3
/-- The created distant generator `Z_aZ_b`. -/
def ZaZb : Pauli 4 := pauliz 0 + pauliz 3
/-- The `X`-survivor `X_aX_{pA} · X_{pB}X_b` — commutes with both measured observables; carries the
distant `X_aX_b` once `Qa` is added. -/
def Wx : Pauli 4 := XXaA + XXBb
/-- The `Z`-survivor `Z_aZ_{pA} · Z_{pB}Z_b` — commutes with both measured observables; carries the
distant `Z_aZ_b` once `Qb` is added. -/
def Wz : Pauli 4 := ZZaA + ZZBb

/-! ## The commutation facts (the `𝔽₂` bookkeeping the conditionings rest on) -/

-- The four input generators pairwise commute (two independent Bell pairs).
example : omega XXaA ZZaA = 0 := by decide
example : omega XXBb ZZBb = 0 := by decide
example : omega XXaA XXBb = 0 := by decide

-- The two Bell-measurement observables commute (a joint measurement).
example : omega Qa Qb = 0 := by decide
-- `Qa` anticommutes with the `Z`-type input on its support; `Qb` with the `X`-type input.
example : omega Qa ZZaA = 1 := by decide
example : omega Qb XXaA = 1 := by decide

-- The survivors commute with both observables, hence pass through the whole Bell measurement.
example : omega Qa Wx = 0 := by decide
example : omega Qb Wx = 0 := by decide
example : omega Qa Wz = 0 := by decide
example : omega Qb Wz = 0 := by decide

-- The distant generators decompose as survivor + one observable (the transport identities).
example : XaXb = Wx + Qa := by decide
example : ZaZb = Wz + Qb := by decide

/-! ## The input state is a Lagrangian

`L_in = ⟨X_aX_{pA}, Z_aZ_{pA}, X_{pB}X_b, Z_{pB}Z_b⟩` (two Bell pairs). -/

/-- The input Lagrangian (two Bell pairs). -/
noncomputable def Lin : Submodule (ZMod 2) (Pauli 4) :=
  Submodule.span (ZMod 2) {XXaA, ZZaA, XXBb, ZZBb}

/-- The four input generators pairwise commute. -/
theorem omega_pairwise_gens :
    ∀ p ∈ ({XXaA, ZZaA, XXBb, ZZBb} : Set (Pauli 4)),
      ∀ q ∈ ({XXaA, ZZaA, XXBb, ZZBb} : Set (Pauli 4)), omega p q = 0 := by
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> decide

/-- The input support is a stabilizer subspace (isotropic). -/
theorem Lin_isStabilizer : IsStabilizer Lin :=
  isStabilizer_span_of_pairwise omega_pairwise_gens

/-- `finrank L_in = 4` — the input is a *full* Lagrangian on 4 qubits. Independence via the `ω`-dual
family `Z_a, X_{pA}, Z_{pB}, X_b`. -/
theorem Lin_finrank : Module.finrank (ZMod 2) Lin = 4 := by
  have hli : LinearIndependent (ZMod 2) ![XXaA, ZZaA, XXBb, ZZBb] :=
    linearIndependent_of_omega_dual (w := ![pauliz 0, paulix 1, pauliz 2, paulix 3])
      (by decide)
  have hrange : ({XXaA, ZZaA, XXBb, ZZBb} : Set (Pauli 4))
      = Set.range ![XXaA, ZZaA, XXBb, ZZBb] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩, ⟨3, by simp⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hspan : Lin = Submodule.span (ZMod 2) (Set.range ![XXaA, ZZaA, XXBb, ZZBb]) := by
    unfold Lin; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-- The input signed stabilizer: support `L_in` with a reference sign. -/
noncomputable def Sin : SignedStab 4 := refStab Lin_isStabilizer

/-! ## The Bell measurement on the inner photons (two conditionings) -/

theorem XXaA_mem : XXaA ∈ Lin := Submodule.subset_span (by simp)
theorem ZZaA_mem : ZZaA ∈ Lin := Submodule.subset_span (by simp)
theorem XXBb_mem : XXBb ∈ Lin := Submodule.subset_span (by simp)
theorem ZZBb_mem : ZZBb ∈ Lin := Submodule.subset_span (by simp)

theorem Wx_mem : Wx ∈ Lin := add_mem XXaA_mem XXBb_mem
theorem Wz_mem : Wz ∈ Lin := add_mem ZZaA_mem ZZBb_mem

/-- `Qa = X_{pA}X_{pB} ∉ L_in`: it anticommutes with `Z_aZ_{pA} ∈ L_in`, but `L_in` is isotropic. -/
theorem Qa_not_mem : Qa ∉ Lin := by
  intro hQa
  have h0 : omega Qa ZZaA = 0 := Lin_isStabilizer Qa hQa ZZaA ZZaA_mem
  have h1 : omega Qa ZZaA = 1 := by decide
  rw [h1] at h0
  exact one_ne_zero h0

/-- **First conditioning** — measure `X_{pA}X_{pB}` (outcome `a`), anticommuting witness
`Z_aZ_{pA}`. -/
noncomputable def S1 (a : ℂ) (ha : a * a = 1) : SignedStab 4 :=
  measSignedStab Sin Lin_isStabilizer Lin_finrank Qa_not_mem ha ZZaA ZZaA_mem (by decide)

/-- `X_aX_{pA}` survives the first conditioning (commutes with `Qa`) — the witness for the
second. -/
theorem XXaA_mem_S1L : XXaA ∈ pauliCondition Lin Qa :=
  mem_pauliCondition_of_commute Qa_not_mem XXaA_mem (by decide)

/-- `Qb = Z_{pA}Z_{pB} ∉` the conditioned space — it anticommutes with the surviving `X_aX_{pA}`. -/
theorem Qb_not_mem_S1L : Qb ∉ pauliCondition Lin Qa := by
  intro hQb
  have h0 : omega Qb XXaA = 0 :=
    pauliCondition_isStabilizer Lin_isStabilizer Qa Qb hQb XXaA XXaA_mem_S1L
  have h1 : omega Qb XXaA = 1 := by decide
  rw [h1] at h0
  exact one_ne_zero h0

/-- **Second conditioning** — measure `Z_{pA}Z_{pB}` (outcome `b`), witness `X_aX_{pA}`.
Completes the Bell measurement; the post-state carries both outcomes in `χ`. -/
noncomputable def S2 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) : SignedStab 4 :=
  measSignedStab (S1 a ha)
    (pauliCondition_isStabilizer Lin_isStabilizer Qa)
    (pauliCondition_finrank Lin_isStabilizer Lin_finrank Qa)
    Qb_not_mem_S1L hb XXaA XXaA_mem_S1L (by decide)

/-! ## The distant pair is created (the main results)

`X_aX_b` and `Z_aZ_b` both land in the post-Bell-measurement support, so the two distant matter
qubits `a, b` — which never interacted — are a Bell pair. Each transports as `survivor +
observable`, with the survivor passing through both conditionings and the observable landing by
`pauliCondition_mem`. -/

theorem Wx_mem_S1L : Wx ∈ pauliCondition Lin Qa :=
  mem_pauliCondition_of_commute Qa_not_mem Wx_mem (by decide)

theorem Wz_mem_S1L : Wz ∈ pauliCondition Lin Qa :=
  mem_pauliCondition_of_commute Qa_not_mem Wz_mem (by decide)

theorem Wx_mem_S2L : Wx ∈ pauliCondition (pauliCondition Lin Qa) Qb :=
  mem_pauliCondition_of_commute Qb_not_mem_S1L Wx_mem_S1L (by decide)

theorem Wz_mem_S2L : Wz ∈ pauliCondition (pauliCondition Lin Qa) Qb :=
  mem_pauliCondition_of_commute Qb_not_mem_S1L Wz_mem_S1L (by decide)

theorem Qa_mem_S1L : Qa ∈ pauliCondition Lin Qa := pauliCondition_mem Lin Qa

/-- `Qa` survives the second conditioning (it commutes with `Qb` — joint measurement). -/
theorem Qa_mem_S2L : Qa ∈ pauliCondition (pauliCondition Lin Qa) Qb :=
  mem_pauliCondition_of_commute Qb_not_mem_S1L Qa_mem_S1L (by decide)

theorem Qb_mem_S2L : Qb ∈ pauliCondition (pauliCondition Lin Qa) Qb :=
  pauliCondition_mem (pauliCondition Lin Qa) Qb

theorem XaXb_mem_S1L : XaXb ∈ pauliCondition Lin Qa := by
  rw [show XaXb = Wx + Qa from by decide]
  exact add_mem Wx_mem_S1L Qa_mem_S1L

/-- **`X_aX_b` stabilizes the output** — the distant pair shares an `X`-correlation. -/
theorem XaXb_mem_S2L : XaXb ∈ pauliCondition (pauliCondition Lin Qa) Qb := by
  rw [show XaXb = Wx + Qa from by decide]
  exact add_mem Wx_mem_S2L Qa_mem_S2L

/-- **`Z_aZ_b` stabilizes the output** — the distant pair shares a `Z`-correlation. With
`XaXb_mem_S2L`, the two never-interacted matter qubits are a Bell pair. -/
theorem ZaZb_mem_S2L : ZaZb ∈ pauliCondition (pauliCondition Lin Qa) Qb := by
  rw [show ZaZb = Wz + Qb from by decide]
  exact add_mem Wz_mem_S2L Qb_mem_S2L

/-! ## The herald (feed-forward signs)

The two outcomes `(a,b)` are *forced into the distant pair's signs*. `X_aX_b` sits on the *kept*
slice of the second measurement (`ω(X_aX_{pA}, X_aX_b) = 0`) and on the `Qa`-coset of the first
(`ω(Z_aZ_{pA}, X_aX_b) = 1`), so its sign picks up exactly the outcome `a`. Dually `Z_aZ_b` sits
on the `Qb`-coset of the second measurement and the kept slice of the first, so its sign picks up
`b`. Reading the two signs tells you which of the four Bell states the distant pair is in — the
herald, as a proven fact. -/

/-- **`X_aX_b` carries outcome `a`.** -/
theorem S2_sign_XaXb (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (S2 a b ha hb).sign XaXb = a * Sin.sign Wx * pauliPhase Qa Wx := by
  change measSign (S1 a ha) Qb XXaA b XaXb = _
  rw [measSign_of_zero (S1 a ha) Qb XXaA b XaXb_mem_S2L (by decide)]
  change measSign Sin Qa ZZaA a XaXb = _
  rw [measSign_of_one Sin Qa ZZaA a XaXb_mem_S1L (by decide),
      show XaXb + Qa = Wx from by decide]

/-- **`Z_aZ_b` carries outcome `b`.** -/
theorem S2_sign_ZaZb (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (S2 a b ha hb).sign ZaZb = b * Sin.sign Wz * pauliPhase Qb Wz := by
  change measSign (S1 a ha) Qb XXaA b ZaZb = _
  rw [measSign_of_one (S1 a ha) Qb XXaA b ZaZb_mem_S2L (by decide),
      show ZaZb + Qb = Wz from by decide]
  change b * measSign Sin Qa ZZaA a Wz * pauliPhase Qb Wz = _
  rw [measSign_of_zero Sin Qa ZZaA a Wz_mem_S1L (by decide)]

/-! ## The swap as a word in the operation monoid

The atomistic `S1`/`S2` re-expressed: each Bell measurement is a *generator* of the operation
monoid (a selective Lüders `ludersChannelₗ Q ε`), and the swap is the **word** `moveQb * moveQa`
acting on the input. Composition is monoid multiplication; the action is the proven symplectic
update. -/

/-- The input as a pure signed Lagrangian on `L_in` (the input factory). -/
noncomputable def SinPure : PureSignedStab 4 := mkPureSlab Lin_isStabilizer Lin_finrank

@[simp] theorem SinPure_L : SinPure.toSignedStab.L = Lin := rfl

/-- First Bell measurement as a monoid generator (measure `X_{pA}X_{pB}`, outcome `a`). -/
noncomputable def moveQa (a : ℂ) (ha : a * a = 1) : operationMonoid 4 :=
  ⟨ludersChannelₗ Qa a, ludersChannelₗ_mem_operationMonoid Qa ha⟩

/-- Second Bell measurement as a generator (measure `Z_{pA}Z_{pB}`, outcome `b`). -/
noncomputable def moveQb (b : ℂ) (hb : b * b = 1) : operationMonoid 4 :=
  ⟨ludersChannelₗ Qb b, ludersChannelₗ_mem_operationMonoid Qb hb⟩

set_option synthInstance.maxHeartbeats 400000 in
-- raised: the operation-monoid `MulAction` on `Option (ℂˣ × PureSignedStab)` is synthesis-heavy.
/-- **The entanglement-swap gadget as a word in the operation monoid** — `moveQb * moveQa`
acting on the two-Bell-pair input; `S1`/`S2` are the action states of one composable object. -/
noncomputable def entSwapGadget (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    Option (ℂˣ × PureSignedStab 4) :=
  (moveQb b hb * moveQa a ha) • some ((1 : ℂˣ), SinPure)

set_option synthInstance.maxHeartbeats 400000 in
-- raised: the operation-monoid `MulAction` on `Option (ℂˣ × PureSignedStab)` is synthesis-heavy.
/-- The gadget-word lands in the doubly-conditioned (Bell-measured) support — the same support
as the atomistic `S2`, now produced by *composing two monoid generators*. -/
theorem entSwapGadget_eq (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    ∃ (c : ℂˣ) (S' : PureSignedStab 4),
      S'.toSignedStab.L = pauliCondition (pauliCondition Lin Qa) Qb ∧
      entSwapGadget a b ha hb = some (c, S') := by
  have hQa : Qa ∉ SinPure.toSignedStab.L := by rw [SinPure_L]; exact Qa_not_mem
  obtain ⟨S1', hS1'L, hS1'eq⟩ := operationMonoid_luders_notMem_smul 1 SinPure hQa ha
  have hQb : Qb ∉ S1'.toSignedStab.L := by rw [hS1'L, SinPure_L]; exact Qb_not_mem_S1L
  obtain ⟨S2', hS2'L, hS2'eq⟩ :=
    operationMonoid_luders_notMem_smul (Units.mk0 ((1 : ℂ) / 2) (by norm_num)) S1' hQb hb
  refine ⟨Units.mk0 ((1 : ℂ) / 2 / 2) (by norm_num), S2',
    by rw [hS2'L, hS1'L, SinPure_L], ?_⟩
  simp only [entSwapGadget, moveQa, moveQb, mul_smul]
  rw [hS1'eq]
  exact hS2'eq

end FTQCLib.EntSwap

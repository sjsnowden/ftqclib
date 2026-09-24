/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.MeasurementCollapse
import FTQCLib.Hilbert.CategoricalConditioningEquiv

/-! # Z-teleportation in the `(L,χ)` frame

Three qubits: `0` = data (a `Z`-eigenstate to be teleported), `1,2` = a Bell pair. The Bell
measurement is on qubits `0,1` (conditioning on `X₀X₁` then `Z₀Z₁`); the output lands on qubit `2`,
with a feed-forward Pauli correction read off the outcomes.

This file fixes the encoding, proves the pure-`𝔽₂` commutation facts the conditioning steps depend
on, carries out the two conditionings, and reads off the feed-forward sign. -/

namespace FTQCLib.Teleport

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Hilbert

/-- Data stabilizer `Z₀` (qubit 0). -/
def Z0 : Pauli 3 := pauliz 0
/-- Bell generator `X₁X₂`. -/
def XX12 : Pauli 3 := paulix 1 + paulix 2
/-- Bell generator `Z₁Z₂`. -/
def ZZ12 : Pauli 3 := pauliz 1 + pauliz 2
/-- First Bell-measurement observable `X₀X₁` (outcome `a`). -/
def Qa : Pauli 3 := paulix 0 + paulix 1
/-- Second Bell-measurement observable `Z₀Z₁` (outcome `b`). -/
def Qb : Pauli 3 := pauliz 0 + pauliz 1

/-! ## The commutation facts (the `𝔽₂` bookkeeping the conditionings rest on) -/

-- The input generators pairwise commute: `L_in = ⟨Z₀, X₁X₂, Z₁Z₂⟩` is isotropic.
example : omega Z0 XX12 = 0 := by decide
example : omega Z0 ZZ12 = 0 := by decide
example : omega XX12 ZZ12 = 0 := by decide

-- Conditioning on `Qa = X₀X₁`: it anticommutes with `Z₀` (the witness `M`) and with `Z₁Z₂`,
-- commutes with `X₁X₂`.
example : omega Qa Z0 = 1 := by decide
example : omega Qa XX12 = 0 := by decide
example : omega Qa ZZ12 = 1 := by decide

-- Conditioning on `Qb = Z₀Z₁`: it commutes with `Qa` (joint Bell measurement) and anticommutes
-- with `X₁X₂` (the witness `M` for the second step).
example : omega Qb Qa = 0 := by decide
example : omega Qb XX12 = 1 := by decide

/-! ## The input state is a Lagrangian

`L_in = ⟨Z₀, X₁X₂, Z₁Z₂⟩`. The reusable helper comes first — it serves any stabilizer-input gadget,
including the S-gadget input `⟨·, Y⟩` and the whole `2^k`-root-of-`Z` tower with `k ≤ 1`. -/

/-- **Reusable Lagrangian helper:** the span of a set of pairwise-commuting Paulis is isotropic (a
stabilizer subspace). Generator-level commutation lifts to the whole span by bilinearity of `omega`,
via a double `span_induction`. -/
theorem isStabilizer_span_of_pairwise {n : ℕ} {s : Set (Pauli n)}
    (h : ∀ p ∈ s, ∀ q ∈ s, omega p q = 0) :
    IsStabilizer (Submodule.span (ZMod 2) s) := by
  -- a generator commutes with all of the span
  have hgen : ∀ p ∈ s, ∀ q ∈ Submodule.span (ZMod 2) s, omega p q = 0 := by
    intro p hp q hq
    induction hq using Submodule.span_induction with
    | mem y hy => exact h p hp y hy
    | zero => exact omega_zero_right p
    | add y z _ _ ihy ihz => rw [omega_add_right, ihy, ihz, add_zero]
    | smul a y _ ihy => rw [omega_smul_right, ihy, mul_zero]
  -- all of the span commutes with all of the span
  intro p hp q hq
  induction hp using Submodule.span_induction with
  | mem x hx => exact hgen x hx q hq
  | zero => exact omega_zero_left q
  | add x y _ _ ihx ihy => rw [omega_add_left, ihx, ihy, add_zero]
  | smul a x _ ihx => rw [omega_smul_left, ihx, mul_zero]

/-- The input Lagrangian `L_in = ⟨Z₀, X₁X₂, Z₁Z₂⟩` (data `Z`-eigenstate ⊗ Bell pair). -/
noncomputable def Lin : Submodule (ZMod 2) (Pauli 3) :=
  Submodule.span (ZMod 2) {Z0, XX12, ZZ12}

/-- The three input generators pairwise commute. -/
theorem omega_pairwise_gens :
    ∀ p ∈ ({Z0, XX12, ZZ12} : Set (Pauli 3)),
      ∀ q ∈ ({Z0, XX12, ZZ12} : Set (Pauli 3)), omega p q = 0 := by
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> decide

/-- The input state's support is a stabilizer subspace (isotropic). -/
theorem Lin_isStabilizer : IsStabilizer Lin :=
  isStabilizer_span_of_pairwise omega_pairwise_gens

/-! ## The conditioning steps

`finrank L_in = 3` is proved once, through the symplectic-dual independence helper below; the
`measSignedStab` conditioning idiom below is the one reused for the S- and T-gadgets. -/

/-- **Reusable independence helper** (the `n`-vector generalization of `WittSpanPair`'s pair lemma):
a family of Paulis with an `ω`-dual family (`ω(v i, w j) = δ_{ij}`) is linearly independent. Applying
`ω(·, w j)` to a vanishing combination extracts the `j`-th coefficient. -/
theorem linearIndependent_of_omega_dual {n k : ℕ} {v w : Fin k → Pauli n}
    (h : ∀ i j, omega (v i) (w j) = if i = j then 1 else 0) :
    LinearIndependent (ZMod 2) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have e : omega (∑ i, g i • v i) (w j) = g j := by
    rw [← omegaBilin_apply, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, omegaBilin_apply, h, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j g]
    simp
  rw [hg, omega_zero_left] at e
  exact e.symm

/-- `finrank L_in = 3` — the input is a *full* Lagrangian. Independence of the three generators via
the `ω`-dual family `X₀, Z₁, X₁`. -/
theorem Lin_finrank : Module.finrank (ZMod 2) Lin = 3 := by
  have hli : LinearIndependent (ZMod 2) ![Z0, XX12, ZZ12] :=
    linearIndependent_of_omega_dual (w := ![paulix 0, pauliz 1, paulix 1]) (by decide)
  have hrange : ({Z0, XX12, ZZ12} : Set (Pauli 3)) = Set.range ![Z0, XX12, ZZ12] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hspan : Lin = Submodule.span (ZMod 2) (Set.range ![Z0, XX12, ZZ12]) := by
    unfold Lin; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-- The input signed stabilizer: support `L_in` with a reference sign. -/
noncomputable def Sin : SignedStab 3 := refStab Lin_isStabilizer

/-- `Z₀ ∈ L_in` (a generator of the span). -/
theorem Z0_mem : Z0 ∈ Lin := Submodule.subset_span (by simp)

/-- `X₀X₁ ∉ L_in`: it anticommutes with `Z₀ ∈ L_in`, but `L_in` is isotropic. (Reusable shape: an
anticommuting witness inside an isotropic subspace excludes membership.) -/
theorem Qa_not_mem : Qa ∉ Lin := by
  intro hQa
  have h0 : omega Qa Z0 = 0 := Lin_isStabilizer Qa hQa Z0 Z0_mem
  have h1 : omega Qa Z0 = 1 := by decide
  rw [h1] at h0
  exact one_ne_zero h0

/-- **First conditioning** — measure `X₀X₁` (outcome `a`), anticommuting witness `Z₀`. The first half
of the Bell measurement: `measSignedStab` conditions `L_in` on `Qa` and writes `a` into `χ`. -/
noncomputable def S1 (a : ℂ) (ha : a * a = 1) : SignedStab 3 :=
  measSignedStab Sin Lin_isStabilizer Lin_finrank Qa_not_mem ha Z0 Z0_mem (by decide)

/-! ## The second conditioning (completing the Bell measurement) -/

/-- **Reusable:** a generator that commutes with the measured `Q` survives into the conditioned space
`pauliCondition S Q` (it lands in the kept slice `S ⊓ Q^⊥`). -/
theorem mem_pauliCondition_of_commute {n : ℕ} {S : Submodule (ZMod 2) (Pauli n)} {Q g : Pauli n}
    (hQ : Q ∉ S) (hg : g ∈ S) (hgQ : omega Q g = 0) :
    g ∈ pauliCondition S Q := by
  rw [pauliCondition_of_not_mem hQ]
  apply Submodule.mem_sup_left
  rw [Submodule.mem_inf]
  refine ⟨hg, ?_⟩
  intro q hq
  change omega q g = 0
  rw [Submodule.mem_span_singleton] at hq
  obtain ⟨c, rfl⟩ := hq
  rw [omega_smul_left, hgQ]
  simp

/-- `X₁X₂` survives the first conditioning (it commutes with `Qa`) — the witness for the second step. -/
theorem XX12_mem_S1L : XX12 ∈ pauliCondition Lin Qa :=
  mem_pauliCondition_of_commute Qa_not_mem (Submodule.subset_span (by simp)) (by decide)

/-- `Z₀Z₁ ∉` the conditioned space — it anticommutes with the surviving `X₁X₂`. -/
theorem Qb_not_mem_S1L : Qb ∉ pauliCondition Lin Qa := by
  intro hQb
  have h0 : omega Qb XX12 = 0 :=
    pauliCondition_isStabilizer Lin_isStabilizer Qa Qb hQb XX12 XX12_mem_S1L
  have h1 : omega Qb XX12 = 1 := by decide
  rw [h1] at h0
  exact one_ne_zero h0

/-- **Second conditioning** — measure `Z₀Z₁` (outcome `b`), witness `X₁X₂`. Completes the Bell
measurement; the post-state `S2 a b` carries both outcomes in `χ`. -/
noncomputable def S2 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) : SignedStab 3 :=
  measSignedStab (S1 a ha)
    (pauliCondition_isStabilizer Lin_isStabilizer Qa)
    (pauliCondition_finrank Lin_isStabilizer Lin_finrank Qa)
    Qb_not_mem_S1L hb XX12 XX12_mem_S1L (by decide)

/-! ## The data generator lands on qubit 2 -/

/-- `Z₀Z₁Z₂` (= `Z₀ + Z₁Z₂`), the generator that commutes with both `Qa` and `Qb`, hence survives the
whole Bell measurement. -/
def ZZZ : Pauli 3 := Z0 + ZZ12

/-- `Z₂` on qubit 2 — the teleported data generator. -/
def Z2 : Pauli 3 := pauliz 2

/-- `Z₀Z₁Z₂` survives the *first* conditioning (commutes with `Qa`). -/
theorem ZZZ_mem_S1L : ZZZ ∈ pauliCondition Lin Qa :=
  mem_pauliCondition_of_commute Qa_not_mem
    (add_mem (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
    (by decide)

theorem ZZZ_mem_S2L : ZZZ ∈ pauliCondition (pauliCondition Lin Qa) Qb :=
  mem_pauliCondition_of_commute Qb_not_mem_S1L ZZZ_mem_S1L (by decide)

/-- **The data lands on qubit 2.** `Z₂ = Z₀Z₁Z₂ + Z₀Z₁` lies in the post-Bell-measurement support
`S2.L` — the teleported state's `Z`-generator, now on qubit 2 (`Qb = Z₀Z₁` is in `S2.L` by
`pauliCondition_mem`). -/
theorem Z2_mem_S2L : Z2 ∈ pauliCondition (pauliCondition Lin Qa) Qb := by
  have h : Z2 = ZZZ + Qb := by decide
  rw [h]
  exact add_mem ZZZ_mem_S2L (pauliCondition_mem _ Qb)

/-! ## The gadget as a word in the operation monoid

The atomistic `S1`/`S2` re-expressed. Each Bell measurement is a *generator* of the operation
monoid (a selective Lüders `ludersChannelₗ Q ε`); the gadget is the **word** `moveQb * moveQa` acting
on the input. Composition is monoid multiplication; the action is the proven symplectic update
(`operationMonoid_luders_notMem_smul`). The conditioning is a composable object. -/

/-- The input as a pure signed Lagrangian on `L_in`. -/
noncomputable def SinPure : PureSignedStab 3 :=
  ⟨tighten (refStab Lin_isStabilizer),
    by rw [tighten_L]; exact Lin_isStabilizer,
    by rw [tighten_L]; exact Lin_finrank,
    fun p hp => tighten_sign_not_mem _ hp⟩

@[simp] theorem SinPure_L : SinPure.toSignedStab.L = Lin := rfl

/-- First Bell measurement as an operation-monoid generator (measure `X₀X₁`, outcome `a`). -/
noncomputable def moveQa (a : ℂ) (ha : a * a = 1) : operationMonoid 3 :=
  ⟨ludersChannelₗ Qa a, ludersChannelₗ_mem_operationMonoid Qa ha⟩

/-- Second Bell measurement as a generator (measure `Z₀Z₁`, outcome `b`). -/
noncomputable def moveQb (b : ℂ) (hb : b * b = 1) : operationMonoid 3 :=
  ⟨ludersChannelₗ Qb b, ludersChannelₗ_mem_operationMonoid Qb hb⟩

/-- **The Bell-measurement gadget as a word in the operation monoid:** `moveQb * moveQa` acting on the
input. `S1`/`S2` are now the action states of one composable object, not hand-assembled terms. -/
noncomputable def bellGadget (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    Option (ℂˣ × PureSignedStab 3) :=
  (moveQb b hb * moveQa a ha) • some (1, SinPure)

/-- The gadget-word lands in the doubly-conditioned (Bell-measured) support — the same support as the
atomistic `S2`, now produced by *composing two monoid generators*. -/
theorem bellGadget_eq (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    ∃ (c : ℂˣ) (S' : PureSignedStab 3),
      S'.toSignedStab.L = pauliCondition (pauliCondition Lin Qa) Qb ∧
      bellGadget a b ha hb = some (c, S') := by
  have hQa : Qa ∉ SinPure.toSignedStab.L := by rw [SinPure_L]; exact Qa_not_mem
  obtain ⟨S1', hS1'L, hS1'eq⟩ := operationMonoid_luders_notMem_smul 1 SinPure hQa ha
  have hQb : Qb ∉ S1'.toSignedStab.L := by rw [hS1'L, SinPure_L]; exact Qb_not_mem_S1L
  obtain ⟨S2', hS2'L, hS2'eq⟩ :=
    operationMonoid_luders_notMem_smul (Units.mk0 ((1 : ℂ) / 2) (by norm_num)) S1' hQb hb
  refine ⟨Units.mk0 ((1 : ℂ) / 2 / 2) (by norm_num), S2',
    by rw [hS2'L, hS1'L, SinPure_L], ?_⟩
  simp only [bellGadget, moveQa, moveQb, mul_smul]
  rw [hS1'eq]
  exact hS2'eq

/-! ## The feed-forward sign (the outcome forces the correction)

The main result of the worked teleportation: the second outcome `b` is *forced into the data qubit's
sign*. `Z₂` lies on the `Qb`-coset of the second measurement (`ω(X₁X₂, Z₂) = 1`) and on the *kept*
slice of the first (`ω(Z₀, Z₀Z₁Z₂) = 0`), so the two `measSign` steps compose to a single factor of
`b` times the input contribution `Sin.sign(Z₀Z₁Z₂)` and a fixed cocycle phase. Reading off the sign
tells you exactly which `X₂` correction to apply — feed-forward as a proven fact. -/
theorem S2_sign_Z2 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (S2 a b ha hb).sign Z2 = b * Sin.sign ZZZ * pauliPhase Qb ZZZ := by
  show measSign (S1 a ha) Qb XX12 b Z2 = _
  rw [measSign_of_one (S1 a ha) Qb XX12 b Z2_mem_S2L (by decide),
      show Z2 + Qb = ZZZ from by decide]
  show b * measSign Sin Qa Z0 a ZZZ * pauliPhase Qb ZZZ = _
  rw [measSign_of_zero Sin Qa Z0 a ZZZ_mem_S1L (by decide)]

end FTQCLib.Teleport

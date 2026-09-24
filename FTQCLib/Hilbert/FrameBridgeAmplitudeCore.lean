/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.FrameBridgeAmplitude

/-! # Discharging the Dehaene–De Moor amplitude form `AmplitudePhaseForm`

This file reduces `AmplitudePhaseForm n`, the hypothesis of the bridge theorem
`stabilizerState_isLevel2Kernel_of_amplitudePhaseForm` (`FrameBridgeAmplitude.lean`), to the
Dehaene–De Moor core `CosetAmplitudeQuadForm n`.

`AmplitudePhaseForm n` asks, for a full Lagrangian `S`, a nonzero joint eigenvector `ψ`, and a base
point `x₀ ∈ supp ψ`, for a `BooleanQuadForm e` (a `ZMod 4`-valued, Boolean-degree-≤2,
precision-divisible phase) with `ψ w = ψ x₀ · iZ4 (e w)` on the support. The amplitude on the
support coset is pinned by `signedStab_amplitude_on_coset`:

  `ψ (x₀ + p.X) = (S.sign p · I^{xzWeight p} · (-1)^{zDotVal p x₀}) · ψ x₀`   for `p ∈ L`.

The reduction here separates two concerns:

* **The combinatorial / Dehaene–De Moor core** — that the per-coset amplitude *exponent*
  `F(p) = S.sign p · I^{xzWeight p} · (-1)^{zDotVal p x₀}` is realised, through the `μ₄` character
  `iZ4`, by a global Boolean quadratic form `e`. This is isolated as the named `Prop`
  `CosetAmplitudeQuadForm`. It is strictly the quadratic-form-existence content: a basis of `π_X(L)`
  lifted by `τ`, the order-2 sign data, the cocycle data, and the `iˣᶻ` / `(-1)^{·Z·x₀}` polynomial
  pieces (with the `zDotVal` cross-term correction). It carries no Hilbert-space content.

* **The Hilbert-space reduction** — that such an `e` *implies* `AmplitudePhaseForm`. This is proven
  unconditionally below: the support is the affine coset (`signedStab_support_iff`), and on it the
  amplitude is `F(p) · ψ x₀` (`signedStab_amplitude_on_coset`), which `iZ4 (e w)` reproduces.

So `amplitudePhaseForm_holds` is reduced to `CosetAmplitudeQuadForm`, which is discharged by
`cosetAmplitudeQuadForm_holds` in `FrameBridgeAmplitudeQuad.lean`; `#print axioms` stays at
`propext / Classical.choice / Quot.sound`.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hilbert FTQCLib.Hierarchy FTQCLib.Pauli FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ}

/-! ### The amplitude exponent `F` and its `μ₄` reading

`amplitudeFactor S x₀ p = S.sign p · I^{xzWeight p} · (-1)^{zDotVal p x₀}` is the `μ₄`-valued factor
that `signedStab_amplitude_on_coset` attaches to the support point `x₀ + p.X`. -/

/-- The amplitude factor on the support coset: `S.sign p · I^{xzWeight p} · (-1)^{zDotVal p x₀}`. -/
noncomputable def amplitudeFactor (S : SignedStab n) (x₀ : Fin n → ZMod 2) (p : Pauli n) : ℂ :=
  S.sign p * Complex.I ^ xzWeight p * (-1 : ℂ) ^ zDotVal p x₀

/-- **The Dehaene–De Moor core.** For a full Lagrangian `S`, a nonzero joint eigenvector
`ψ`, and a base point `x₀ ∈ supp ψ`, the per-coset amplitude *exponent* is realised by a global
Boolean quadratic form: there is `e : 𝔽₂ⁿ → ZMod 4` with `BooleanQuadForm e` such that for every
`p ∈ L`, the `μ₄` character `iZ4 (e (x₀ + p.X))` equals the amplitude factor
`S.sign p · I^{xzWeight p} · (-1)^{zDotVal p x₀}`.

This is the genuine quadratic-form-existence content of Dehaene–De Moor Thm 5(ii) (qubit, Z-type /
diagonal scope): the sign cocycle, lifted to a basis of `π_X(L)`, is a `ZMod 4` quadratic form; the
`iˣᶻ` and `(-1)^{·Z·x₀}` pieces are its polynomial parts. It is stated with no Hilbert-space
content — only the `Pauli`-level factor `amplitudeFactor` and the Boolean-Möbius `BooleanQuadForm` —
so it is strictly weaker than `AmplitudePhaseForm`, which it implies (the implication is proven
unconditionally below). -/
def CosetAmplitudeQuadForm (n : ℕ) : Prop :=
  ∀ (S : SignedStab n) (ψ : QState n),
    Module.finrank (ZMod 2) S.L = n → ψ ≠ 0 →
    (∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) →
    ∀ x₀ : Fin n → ZMod 2, ψ x₀ ≠ 0 →
    ∃ e : (Fin n → ZMod 2) → ZMod 4,
      BooleanQuadForm e ∧
      (∀ p ∈ S.L, iZ4 (e (x₀ + p.X)) = amplitudeFactor S x₀ p)

/-! ### The Hilbert-space reduction — `CosetAmplitudeQuadForm` implies `AmplitudePhaseForm` -/

/-- **The reduction.** Given the Dehaene–De Moor core `CosetAmplitudeQuadForm n`, the full amplitude
form `AmplitudePhaseForm n` holds. The support of `ψ` is the affine coset `x₀ + π_X(L)`
(`signedStab_support_iff`); on it the amplitude is `amplitudeFactor S x₀ p · ψ x₀`
(`signedStab_amplitude_on_coset`), which the quadratic form reproduces through `iZ4`. -/
theorem amplitudePhaseForm_of_cosetAmplitudeQuadForm (hc : CosetAmplitudeQuadForm n) :
    AmplitudePhaseForm n := by
  intro S ψ hL hψne hψfix x₀ hx₀ne
  obtain ⟨e, he, hmatch⟩ := hc S ψ hL hψne hψfix x₀ hx₀ne
  refine ⟨e, he, ?_⟩
  -- |L| = 2^n from finrank = n (needed for the support-iff).
  have hcard : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card = 2 ^ n := by
    have hnc : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card
        = Nat.card ↥(S.L : Set (Pauli n)) := by
      rw [← Set.ncard_eq_toFinset_card (S.L : Set (Pauli n)) (Set.toFinite _),
        ← Nat.card_coe_set_eq]
    rw [hnc, show Nat.card ↥(S.L : Set (Pauli n)) = Nat.card ↥S.L from rfl,
      Nat.card_eq_fintype_card, card_submodule_eq_pow_finrank hL]
  obtain ⟨x₁, hx₁iff⟩ := signedStab_support_iff S ψ hcard hψfix hψne
  -- Both `x₀` and the iff-base `x₁` are in the support; the iff is anchored at `x₁`, but the
  -- amplitude is anchored at `x₀`. We work directly from the per-`p` transport.
  intro w hw
  -- `w` is a support point, so `w = x₁ + p.X` for some `p ∈ L`; reanchor to `x₀`.
  obtain ⟨p, hp, rfl⟩ := (hx₁iff w).mp hw
  -- `x₀` is itself a support point at `x₁`: `x₀ = x₁ + p₀.X`.
  obtain ⟨p₀, hp₀, hx₀eq⟩ := (hx₁iff x₀).mp hx₀ne
  -- Then `w = x₁ + p.X = x₀ + (p - p₀).X` with `p - p₀ ∈ L`.
  have hwx₀ : x₁ + p.X = x₀ + (p - p₀).X := by
    rw [hx₀eq]
    have : (p - p₀).X = p.X - p₀.X := by
      simp [sub_eq_add_neg]
    rw [this]; abel
  have hmem : p - p₀ ∈ S.L := S.L.sub_mem hp hp₀
  rw [hwx₀, signedStab_amplitude_on_coset S ψ hψfix x₀ hmem]
  rw [hmatch (p - p₀) hmem]
  rw [amplitudeFactor]
  ring

/-! ### A differential criterion for `BooleanQuadForm`

`BooleanQuadForm e` is awkward to verify directly from the Möbius/powerset formula. We reduce it to
a purely *differential* condition on the iterated discrete derivative `funcDerivG`: if every third
difference of `e` vanishes and every second difference is even, then `e` is a `BooleanQuadForm`. The
`vanish` clause uses that `mobiusCoeff S e = funcDerivSubset S e 0` factors through any three of its
derivatives; the `dvd` clause is automatic for `|S| ≤ 1` and is the second-difference parity for
`|S| = 2` (and vacuous for `|S| ≥ 3` since the coefficient is then `0`). -/

section Differential

variable {A : Type*} [AddCommGroup A]

open BooleanMobius

/-- A single derivative `funcDerivG i` commutes past `funcDerivSubset S`. -/
theorem funcDerivG_funcDerivSubset_comm (i : Fin n) (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivSubset S f) = funcDerivSubset S (funcDerivG i f) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [funcDerivSubset_empty, funcDerivSubset_empty]
  | @insert j T hj ih =>
    rw [funcDerivSubset_insert hj, funcDerivG_comm, ih, funcDerivSubset_insert hj]

/-- Peeling an element from the *inside*: `funcDerivSubset (insert i S) f` is `funcDerivSubset S`
applied to the single derivative `funcDerivG i f`. The dual of `funcDerivSubset_insert`, obtained by
commuting the outer derivative all the way in. -/
theorem funcDerivSubset_insert' {i : Fin n} {S : Finset (Fin n)} (hi : i ∉ S)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset (insert i S) f = funcDerivSubset S (funcDerivG i f) := by
  rw [funcDerivSubset_insert hi, funcDerivG_funcDerivSubset_comm]

/-- `funcDerivSubset S` of the zero function is the zero function. -/
theorem funcDerivSubset_zero_fun (S : Finset (Fin n)) :
    funcDerivSubset S (0 : (Fin n → ZMod 2) → A) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [funcDerivSubset_empty]
  | @insert i T hi ih =>
    rw [funcDerivSubset_insert hi, ih]
    funext v; rw [funcDerivG_apply]; simp

/-- Factor `funcDerivSubset S` through one inside derivative for any `i ∈ S`. -/
theorem funcDerivSubset_factor {i : Fin n} {S : Finset (Fin n)} (hi : i ∈ S)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset S f = funcDerivSubset (S.erase i) (funcDerivG i f) := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [funcDerivSubset_insert' (Finset.notMem_erase i S)]

end Differential

/-- **Differential criterion for `BooleanQuadForm`.** If every third difference of `e` vanishes
(`∀ i j k, funcDerivG i (funcDerivG j (funcDerivG k e)) = 0`) and every Möbius coefficient at a pair
is even (`∀ S, S.card = 2 → 2 ∣ (mobiusCoeff S e).val`), then `e` is a `BooleanQuadForm`. The third
clause `dvd` for `|S| ≤ 1` is automatic (`2^0 = 1`), for `|S| = 2` is the parity hypothesis, and for
`|S| ≥ 3` follows from the vanishing (a `0` coefficient is divisible by anything). -/
theorem booleanQuadForm_of_differential {e : (Fin n → ZMod 2) → ZMod 4}
    (h3 : ∀ i j k : Fin n, funcDerivG i (funcDerivG j (funcDerivG k e)) = 0)
    (h2 : ∀ S : Finset (Fin n), S.card = 2 → 2 ∣ (mobiusCoeff S e).val) :
    BooleanQuadForm e := by
  classical
  -- the vanishing of high coefficients
  have hvanish : ∀ S : Finset (Fin n), 3 ≤ S.card → mobiusCoeff S e = 0 := by
    intro S hS
    -- pick three distinct elements i, j, k of S
    obtain ⟨i, hiS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j, hjS⟩ : (S.erase i).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hiS]; omega)
    obtain ⟨k, hkS⟩ : ((S.erase i).erase j).Nonempty :=
      Finset.card_pos.mp
        (by rw [Finset.card_erase_of_mem hjS, Finset.card_erase_of_mem hiS]; omega)
    -- Factor through the three inside derivatives, which compose to `0`.
    rw [mobiusCoeff_apply, funcDerivSubset_factor hiS, funcDerivSubset_factor hjS,
      funcDerivSubset_factor hkS, h3 k j i, funcDerivSubset_zero_fun]
    rfl
  refine ⟨hvanish, ?_⟩
  intro S
  rcases lt_trichotomy S.card 2 with hlt | heq | hgt
  · -- |S| ≤ 1: 2^(|S|-1) = 2^0 = 1 divides anything
    have : S.card - 1 = 0 := by omega
    rw [this, pow_zero]; exact one_dvd _
  · -- |S| = 2: parity hypothesis (2^(2-1) = 2)
    rw [heq]; exact h2 S heq
  · -- |S| ≥ 3: coefficient is zero
    rw [hvanish S (by omega), ZMod.val_zero]; exact dvd_zero _

/-! ### Coset well-definedness of the amplitude factor

The amplitude factor is constant on each `π_X(L)`-fibre: if `p, p' ∈ L` have the same X-part then
`amplitudeFactor S x₀ p = amplitudeFactor S x₀ p'`. Both equal `ψ (x₀ + p.X) / ψ x₀` through the
eigen-equation (`signedStab_amplitude_on_coset`), and `ψ x₀ ≠ 0`. This is what lets the quadratic
form be built from a *single* lift `τ (p.X)` of each X-class, independent of the Z-part. -/

/-- The amplitude factor depends only on the X-part of `p` (within `L`). -/
theorem amplitudeFactor_eq_of_X_eq (S : SignedStab n) (ψ : QState n)
    (hψfix : ∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ)
    {x₀ : Fin n → ZMod 2} (hx₀ : ψ x₀ ≠ 0)
    {p p' : Pauli n} (hp : p ∈ S.L) (hp' : p' ∈ S.L) (hX : p.X = p'.X) :
    amplitudeFactor S x₀ p = amplitudeFactor S x₀ p' := by
  have h1 := signedStab_amplitude_on_coset S ψ hψfix x₀ hp
  have h2 := signedStab_amplitude_on_coset S ψ hψfix x₀ hp'
  rw [hX] at h1
  rw [h1] at h2
  exact mul_right_cancel₀ hx₀ h2

/-! ### `AmplitudePhaseForm` reduced to the Dehaene–De Moor core

`amplitudePhaseForm_holds` follows from `amplitudePhaseForm_of_cosetAmplitudeQuadForm`. The core
`CosetAmplitudeQuadForm n` is the Dehaene–De Moor quadratic-form construction: a basis of `π_X(L)`
lifted by `τ`, with the order-2 sign data, the cocycle data, and the `iˣᶻ` / `(-1)^{·Z·x₀}`
polynomial pieces; it is discharged by `cosetAmplitudeQuadForm_holds`
(`FrameBridgeAmplitudeQuad.lean`). Everything around it — the differential criterion
`booleanQuadForm_of_differential`, the Hilbert-space reduction
`amplitudePhaseForm_of_cosetAmplitudeQuadForm`, and the coset well-definedness
`amplitudeFactor_eq_of_X_eq` — is proven unconditionally here. -/

/-- **The amplitude form, conditional on the Dehaene–De Moor core.** `AmplitudePhaseForm n` holds
given `CosetAmplitudeQuadForm n`. Combined with `cosetAmplitudeQuadForm_holds`, this feeds the
bridge theorem `stabilizerState_isLevel2Kernel_of_amplitudePhaseForm`
(`FrameBridgeAmplitude.lean`). -/
theorem amplitudePhaseForm_holds (hc : CosetAmplitudeQuadForm n) : AmplitudePhaseForm n :=
  amplitudePhaseForm_of_cosetAmplitudeQuadForm hc

end FTQCLib.Frame

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.FrameBridge
import FTQCLib.Hilbert.ProjectiveStrictLevel
import FTQCLib.Hierarchy.BooleanMobius

/-! # Discharging the (a2) amplitude clause of the bridge lemma

This file builds `stabStateAmplitudeForm_of_amplitudePhaseForm`, reducing the bridge amplitude
clause `StabStateAmplitudeForm n` — the hypothesis of `stabilizerState_isLevel2Kernel`
(`FrameBridge.lean`) — to the Dehaene–De Moor quadratic-form existence `AmplitudePhaseForm n`.

The construction has three layers.

* **Layer A — the `i`-power bridge.** At precision `m = 2`, the real phase of a `DiagPhase n 2`
  polynomial reconciles with an `i`-power: `exp(I · realPhase q w) = i^{(q.eval w).val}`. This is the
  `ZMod 4 = μ₄` reading.

* **Layer B — the Möbius assembly.** Given a `ZMod 4`-valued phase function `e : 𝔽₂ⁿ → ZMod 4` that is
  *genuinely degree ≤ 2 in the Boolean sense* (its Möbius coefficients of order `≥ 3` vanish) and whose
  Möbius coefficients carry the precision divisibility `2^{|S|-1} ∣ (mobiusCoeff S e).val`, the
  `strictMobiusAssemblyPoly` of those coefficients is a `q : DiagPhase n 2` with
  `effectiveLevel q ≤ 2` and `q.eval w = e w − e 0` everywhere. The truncation to `|S| ≤ 2` is exact
  (the higher coefficients vanish), and the dropped empty-set constant `e 0` is absorbed into the
  amplitude `c`. The recombination uses the `μ₄` character `iZ4`.

* **Layer C — the amplitude form.** For a full Lagrangian `S` and a nonzero joint eigenvector `ψ`, there
  is such an `e` with `i^{e w}` equal to the amplitude factor `F` on the support coset. The Dehaene–De
  Moor quadratic-form construction (a basis of `π_X(L)` lifted by `τ`, with the order-2 sign data
  `sᵢ`, the cocycle data `βᵢⱼ`, and the `iˣᶻ` / `(-1)^{·Z·x₀}` polynomial pieces) is isolated
  behind the named `Prop` `AmplitudePhaseForm`, discharged in `FrameBridgeAmplitudeCore.lean` and
  `FrameBridgeAmplitudeQuad.lean`. Everything around it — Layers A, B, the support clause, and the
  final assembly — is proven unconditionally here.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hilbert FTQCLib.Hierarchy FTQCLib.Pauli FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ}

/-! ### Layer A — the `i`-power bridge at precision `m = 2`

`realPhase q w = 2π · (q.eval w).val / 4`, so `exp(I · realPhase q w) = exp(2πi · k / 4) = i^k` with
`k = (q.eval w).val`. -/

/-- **The `i`-power bridge.** For a `DiagPhase n 2` polynomial `q`, the unit-modulus real phase
factor `exp(I · realPhase q w)` equals the `i`-power `i^{(q.eval w).val}`. The value group of a
precision-2 phase is `μ₄`, and this is the explicit identification. -/
theorem exp_realPhase_two_eq_iPow (q : DiagPhase n 2) (w : Fin n → ZMod 2) :
    Complex.exp (Complex.I * (DiagPhase.realPhase q w : ℂ))
      = Complex.I ^ (DiagPhase.eval q w).val := by
  set k : ℕ := (DiagPhase.eval q w).val with hk
  -- realPhase q w = (π / 2) * k.
  have hrp : DiagPhase.realPhase q w = (Real.pi / 2) * (k : ℝ) := by
    unfold DiagPhase.realPhase
    rw [← hk]
    have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
    rw [h4]; ring
  rw [hrp]
  -- exp(I · (π/2) · k) = (exp(I · π/2))^k = i^k.
  have hcast : Complex.I * ((((Real.pi / 2) * (k : ℝ)) : ℝ) : ℂ)
      = (k : ℂ) * ((Real.pi / 2 : ℝ) * Complex.I) := by
    push_cast; ring
  rw [hcast, Complex.exp_nat_mul]
  congr 1
  -- exp((π/2) · I) = i.
  rw [show ((Real.pi / 2 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) / 2 * Complex.I from by
    push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

/-! ### Layer B — the Möbius assembly

Given `e : 𝔽₂ⁿ → ZMod 4` with vanishing high-order Möbius coefficients and the per-`S` divisibility,
the strict assembly polynomial reproduces `e` and has effective level `≤ 2`. -/

/-- A `ZMod 4`-valued phase function `e` is **Boolean-degree ≤ 2 with precision divisibility** when
its Möbius coefficients of order `≥ 3` vanish and each coefficient at `S` is divisible by `2^{|S|-1}`
(the order-2 condition for `|S| = 2`, automatic for `|S| ≤ 1`). These are exactly the hypotheses the
strict assembly polynomial needs to be a level-≤2 frame exponent reproducing `e`. -/
structure BooleanQuadForm (e : (Fin n → ZMod 2) → ZMod 4) : Prop where
  vanish : ∀ S : Finset (Fin n), 3 ≤ S.card → mobiusCoeff S e = 0
  dvd : ∀ S : Finset (Fin n), 2 ^ (S.card - 1) ∣ (mobiusCoeff S e).val

/-- The assembled frame exponent of a `BooleanQuadForm`: the strict Möbius assembly of its truncated
Möbius coefficients (only non-empty `S` with `|S| ≤ 2` contribute). -/
noncomputable def quadFormPoly (e : (Fin n → ZMod 2) → ZMod 4) : DiagPhase n 2 :=
  strictMobiusAssemblyPoly
    (fun S => if S.Nonempty ∧ S.card ≤ 2 then mobiusCoeff S e else 0)

/-- **Layer B, level bound.** The assembled exponent of a `BooleanQuadForm` has effective
level `≤ 2`. -/
theorem quadFormPoly_effectiveLevel_le {e : (Fin n → ZMod 2) → ZMod 4}
    (he : BooleanQuadForm e) :
    DiagPhase.effectiveLevel (quadFormPoly e) ≤ 2 := by
  unfold quadFormPoly
  refine strictMobiusAssemblyPoly_effectiveLevel_le (by norm_num) _ ?_ ?_
  · intro S hS hSk
    rw [if_pos ⟨hS, hSk⟩]
    exact he.dvd S
  · intro S hS
    rw [if_neg hS]

/-- The empty-set Möbius coefficient is the value at `0`. -/
theorem mobiusCoeff_empty {A : Type*} [AddCommGroup A]
    (f : (Fin n → ZMod 2) → A) : mobiusCoeff (∅ : Finset (Fin n)) f = f 0 := by
  rw [mobiusCoeff_apply, funcDerivSubset_empty]

/-- **Layer B, evaluation.** The assembled exponent of a `BooleanQuadForm` evaluates to `e w − e 0`
everywhere. The strict assembly excludes the empty set (so the constant `e 0` is dropped) and
truncates to `|S| ≤ 2`; the truncation loses nothing because the order-`≥ 3` Möbius coefficients
vanish, and Möbius inversion reconstructs the rest. The dropped `e 0` is absorbed into `c`. -/
theorem quadFormPoly_eval {e : (Fin n → ZMod 2) → ZMod 4}
    (he : BooleanQuadForm e) (w : Fin n → ZMod 2) :
    DiagPhase.eval (quadFormPoly e) w = e w - e 0 := by
  classical
  unfold quadFormPoly
  rw [strictMobiusAssemblyPoly_eval]
  -- LHS = ∑_{S ⊆ supp w, S ≠ ∅, |S| ≤ 2} mobiusCoeff S e.
  have hsimp : ∀ S ∈ (FTQCLib.Codes.supp w).powerset.filter (fun S => S.Nonempty ∧ S.card ≤ 2),
      (if S.Nonempty ∧ S.card ≤ 2 then mobiusCoeff S e else 0) = mobiusCoeff S e := by
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [if_pos hS.2]
  rw [Finset.sum_congr rfl hsimp]
  -- Möbius inversion: e w = ∑_{S ⊆ supp w} mobiusCoeff S e.
  have hinv : e w = ∑ S ∈ (FTQCLib.Codes.supp w).powerset, mobiusCoeff S e := eq_sum_mobiusCoeff e w
  -- Split the full powerset sum into: {∅} ∪ {nonempty, |S| ≤ 2} ∪ {nonempty, |S| ≥ 3}.
  -- The ≥3 terms vanish; the ∅ term is e 0; the middle is our LHS.
  -- Reorganize: full sum = (filtered nonempty |S| ≤ 2 sum) + (∅ term) + (|S| ≥ 3 terms).
  have hsplit : ∑ S ∈ (FTQCLib.Codes.supp w).powerset, mobiusCoeff S e
      = (∑ S ∈ (FTQCLib.Codes.supp w).powerset.filter (fun S => S.Nonempty ∧ S.card ≤ 2),
            mobiusCoeff S e)
        + ∑ S ∈ (FTQCLib.Codes.supp w).powerset.filter (fun S => ¬ (S.Nonempty ∧ S.card ≤ 2)),
            mobiusCoeff S e := by
    rw [Finset.sum_filter_add_sum_filter_not]
  -- The complement filter splits further into ∅ (e 0) and |S| ≥ 3 (vanishing).
  have hcompl : ∑ S ∈ (FTQCLib.Codes.supp w).powerset.filter (fun S => ¬ (S.Nonempty ∧ S.card ≤ 2)),
        mobiusCoeff S e = e 0 := by
    -- Each S in this filter is either ∅ or has |S| ≥ 3 (since |S| ≤ 1 nonempty has card ≤ 2).
    -- For S = ∅: coeff = e 0; otherwise card ≥ 3 ⇒ coeff = 0.
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun S => S = ∅)]
    have h1 : ∑ S ∈ ((FTQCLib.Codes.supp w).powerset.filter
                (fun S => ¬ (S.Nonempty ∧ S.card ≤ 2))).filter (fun S => S = ∅),
          mobiusCoeff S e = e 0 := by
      rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
      · rw [mobiusCoeff_empty]
      · intro S hS hSne
        rw [Finset.mem_filter] at hS
        exact absurd hS.2 hSne
      · intro hmem
        exfalso
        apply hmem
        rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.empty_mem_powerset _, ?_⟩, rfl⟩
        intro ⟨hne, _⟩
        exact absurd rfl hne.ne_empty
    have h2 : ∑ S ∈ ((FTQCLib.Codes.supp w).powerset.filter
                (fun S => ¬ (S.Nonempty ∧ S.card ≤ 2))).filter (fun S => ¬ S = ∅),
          mobiusCoeff S e = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      rw [Finset.mem_filter, Finset.mem_filter] at hS
      obtain ⟨⟨_, hnot⟩, hSne⟩ := hS
      have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
      have hcard3 : 3 ≤ S.card := by
        by_contra hlt
        push_neg at hlt
        exact hnot ⟨hSnonempty, by omega⟩
      exact he.vanish S hcard3
    rw [h1, h2, add_zero]
  rw [hsplit, hcompl] at hinv
  -- hinv : e w = LHS + e 0, so LHS = e w − e 0.
  rw [hinv]; ring

/-! ### The `μ₄`-character `iZ4`

`iZ4 c = i^{c.val}` is a multiplicative character `ZMod 4 → ℂ`: `i` has order `4`, so the power
depends only on `c.val mod 4`, and `(a + b).val ≡ a.val + b.val (mod 4)`. This is what lets the
dropped constant `e 0` recombine in the assembly. -/

/-- The `μ₄` character `ZMod 4 → ℂˣ`, `c ↦ i^{c.val}`, as a complex value. -/
noncomputable def iZ4 (c : ZMod 4) : ℂ := Complex.I ^ c.val

/-- `iZ4` is multiplicative on `ZMod 4`: `iZ4 (a + b) = iZ4 a · iZ4 b`. -/
theorem iZ4_add (a b : ZMod 4) : iZ4 (a + b) = iZ4 a * iZ4 b := by
  unfold iZ4
  rw [← pow_add, Complex.I_pow_eq_pow_mod, Complex.I_pow_eq_pow_mod (a.val + b.val)]
  congr 1
  rw [ZMod.val_add a b]
  omega

/-- The reconstruction identity for `iZ4`: `iZ4 (e 0) · iZ4 (e w − e 0) = iZ4 (e w)`. -/
theorem iZ4_reconstruct (c d : ZMod 4) : iZ4 d * iZ4 (c - d) = iZ4 c := by
  rw [← iZ4_add]
  congr 1
  ring

/-! ### Layer C — the amplitude form, isolated behind a named `Prop`

For a full Lagrangian `S`, a nonzero joint eigenvector `ψ`, and a base point `x₀ ∈ supp`, there is a
`BooleanQuadForm e` (a degree-≤2, precision-divisible `ZMod 4`-valued phase) reproducing the amplitude
factor through the `μ₄` character: `ψ w = ψ x₀ · iZ4 (e w)` on the support.

This is the Dehaene–De Moor quadratic form (qubit, Z-type/diagonal scope): the core that
builds `e` from a basis of `π_X(L)` lifted by `τ` (`exists_piX_lift`), recording the order-2 sign
data `sᵢ = signLog (S.sign pᵢ)`, the cocycle data `βᵢⱼ = mu4Log (pauliPhase pᵢ pⱼ)`, and the `iˣᶻ` /
`(-1)^{·Z·x₀}` polynomial pieces (with the `zDotVal` cross-term correction, since `zDotVal` is
`.val`-valued and not additive). The amplitude factor `F(p) = S.sign p · iˣᶻ⁽ᵖ⁾ · (-1)^{p.Z·x₀}`
(`signedStab_amplitude_on_coset`) is `μ₄`-valued and quadratic *on `L`*, but not globally; the basis
construction makes `e` manifestly degree ≤ 2 everywhere, which the naive global Möbius of `F ∘ τ` does
not (it samples off `π_X(L)`). Isolated as a named `Prop`; everything around it (Layers A,
B, the support clause, the assembly) is proven unconditionally. -/
def AmplitudePhaseForm (n : ℕ) : Prop :=
  ∀ (S : SignedStab n) (ψ : QState n),
    Module.finrank (ZMod 2) S.L = n → ψ ≠ 0 →
    (∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) →
    ∀ x₀ : Fin n → ZMod 2, ψ x₀ ≠ 0 →
    ∃ e : (Fin n → ZMod 2) → ZMod 4,
      BooleanQuadForm e ∧
      (∀ w, ψ w ≠ 0 → ψ w = ψ x₀ * iZ4 (e w))

/-! ### `StabStateAmplitudeForm` from `AmplitudePhaseForm` -/

/-- **(a2) discharged.** The bridge amplitude clause `StabStateAmplitudeForm n` holds, conditional
only on the Dehaene–De Moor quadratic-form existence `AmplitudePhaseForm n`. The support clause comes
from the already-proven `signedStab_support_iff`; the level-≤2 exponent `q = quadFormPoly e` and the
phase reconciliation `ψ w = c · exp(I · realPhase q w)` come from Layers A and B together with the
`iZ4` reconstruction identity (the dropped constant `e 0` is absorbed into `c = ψ x₀ · iZ4 (e 0)`). -/
theorem stabStateAmplitudeForm_of_amplitudePhaseForm (ha : AmplitudePhaseForm n) :
    StabStateAmplitudeForm n := by
  intro S ψ hL hψne hψfix
  -- |L| = 2^n from finrank = n.
  have hcard : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card = 2 ^ n := by
    have hnc : (Set.toFinite (S.L : Set (Pauli n))).toFinset.card
        = Nat.card ↥(S.L : Set (Pauli n)) := by
      rw [← Set.ncard_eq_toFinset_card (S.L : Set (Pauli n)) (Set.toFinite _),
        ← Nat.card_coe_set_eq]
    rw [hnc]
    rw [show Nat.card ↥(S.L : Set (Pauli n)) = Nat.card ↥S.L from rfl,
      Nat.card_eq_fintype_card, card_submodule_eq_pow_finrank hL]
  -- Base point from the support-iff.
  obtain ⟨x₀, hx₀iff⟩ := signedStab_support_iff S ψ hcard hψfix hψne
  -- ψ x₀ ≠ 0 from the iff (take p = 0).
  have hx₀ne : ψ x₀ ≠ 0 := by
    rw [hx₀iff x₀]
    exact ⟨0, S.L.zero_mem, by simp⟩
  obtain ⟨e, he, hamp⟩ := ha S ψ hL hψne hψfix x₀ hx₀ne
  refine ⟨2, quadFormPoly e, ψ x₀ * iZ4 (e 0), x₀,
    quadFormPoly_effectiveLevel_le he, hx₀iff, ?_⟩
  intro w hw
  -- ψ w = ψ x₀ · iZ4 (e w) = ψ x₀ · iZ4 (e 0) · iZ4 (e w − e 0)
  --      = c · exp(I · realPhase q w).
  rw [hamp w hw, exp_realPhase_two_eq_iPow, quadFormPoly_eval he]
  -- Goal: ψ x₀ * iZ4 (e w) = (ψ x₀ * iZ4 (e 0)) * I^(e w − e 0).val
  show ψ x₀ * iZ4 (e w) = (ψ x₀ * iZ4 (e 0)) * Complex.I ^ (e w - e 0).val
  rw [mul_assoc, ← iZ4]
  rw [iZ4_reconstruct (e w) (e 0)]

/-- **Bridge theorem (conditional on the DDM core).** Composing
`stabStateAmplitudeForm_of_amplitudePhaseForm` with `stabilizerState_isLevel2Kernel`: every
full-rank sector has a unit stabilizer state realized as one of the kernel frame's level-≤2 objects
on its support coset, given the Dehaene–De Moor quadratic-form existence `AmplitudePhaseForm n`.
The unconditional form is `stabilizerState_isLevel2Kernel_unconditional`
(`FrameBridgeAmplitudeQuad.lean`). -/
theorem stabilizerState_isLevel2Kernel_of_amplitudePhaseForm (ha : AmplitudePhaseForm n)
    (S : SignedStab n) (hL : Module.finrank (ZMod 2) S.L = n) :
    ∃ (ψ : QState n) (m : ℕ) (q : DiagPhase n m) (c : ℂ) (x₀ : Fin n → ZMod 2),
      ‖ψ‖ = 1 ∧ (∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) ∧
        DiagPhase.effectiveLevel q ≤ 2 ∧
          (∀ w, ψ w ≠ 0 ↔ ∃ p ∈ S.L, w = x₀ + p.X) ∧
          (∀ w, ψ w ≠ 0 → ψ w = c * Complex.exp (Complex.I * (DiagPhase.realPhase q w : ℂ))) :=
  stabilizerState_isLevel2Kernel (stabStateAmplitudeForm_of_amplitudePhaseForm ha) S hL

end FTQCLib.Frame

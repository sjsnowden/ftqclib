/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CategoricalConditioning

/-! # The full conditioning equivalence `𝒮 ≃ 𝒪`

The equivalence between the symplectic theory and the operational fragment, including selective
Lüders, on the **sub-normalized** carrier.

* `𝒪`-side carrier = the scaled cone `{A // IsScaledStabDensity A}` (`CategoricalConditioning`);
* `𝒮`-side carrier = the **pointed** `Option (ℂˣ × PureSignedStab n)` (`none ↦ 0`,
  `some (c,S) ↦ c•Π_S`) — the basepoint absorbs the degenerate-`0` (wrong outcome → 0), no quotient;
* the bijection `psi` is equivariant for the **transported** `operationMonoid` action, giving the
  equivalence via `CategoryOfElements.map` exactly as for the conditioning-free equivalence
  (`stabilizerSymplecticEquivalence`). -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Stabilizer CategoryTheory

variable {n : ℕ}

/-- A canonical stabilizer signed Lagrangian on `L` (valid sign from `exists_refSign`). -/
noncomputable def refStab {L : Submodule (ZMod 2) (Pauli n)} (hS : IsStabilizer L) :
    SignedStab n where
  L := L
  sign := (exists_refSign hS).choose
  sign_zero := (exists_refSign hS).choose_spec.1
  valid := (exists_refSign hS).choose_spec.2

/-- The canonical pure signed Lagrangian on `allZ` (the `0`-witness; inhabits `PureSignedStab`). -/
noncomputable def canonicalPureStab (n : ℕ) : PureSignedStab n where
  toSignedStab := tighten (refStab (isStabilizer_allZ (n := n)))
  isStab := by rw [tighten_L]; exact isStabilizer_allZ
  full := by rw [tighten_L]; exact finrank_allZ
  tight := fun p hp => tighten_sign_not_mem _ hp

instance : Nonempty (PureSignedStab n) := ⟨canonicalPureStab n⟩

/-- `0` is a scaled stabilizer density (weight `0` on the canonical stab). -/
theorem isScaledStabDensity_zero : IsScaledStabDensity (0 : QState n →ₗ[ℂ] QState n) :=
  ⟨0, (canonicalPureStab n).toSignedStab, (canonicalPureStab n).isStab, (canonicalPureStab n).full,
    (zero_smul ℂ _).symm⟩

/-! ## The pointed bijection `psi : Option (ℂˣ × PureSignedStab) ≃ scaled cone` -/

/-- The object map: `none ↦ 0`, `some (c, S) ↦ c • Π_S`. -/
noncomputable def psi : Option (ℂˣ × PureSignedStab n) →
    {A : QState n →ₗ[ℂ] QState n // IsScaledStabDensity A}
  | none => ⟨0, isScaledStabDensity_zero⟩
  | some (c, S) => ⟨(c : ℂ) • stabProjector S.toSignedStab,
      ⟨c, S.toSignedStab, S.isStab, S.full, rfl⟩⟩

@[simp] theorem psi_none : (psi (n := n) none).1 = 0 := rfl

@[simp] theorem psi_some (c : ℂˣ) (S : PureSignedStab n) :
    (psi (some (c, S))).1 = (c : ℂ) • stabProjector S.toSignedStab := rfl

theorem psi_injective : Function.Injective (psi (n := n)) := by
  rintro (_ | ⟨c, S⟩) (_ | ⟨c', S'⟩) h
  · rfl
  · rw [Subtype.ext_iff, psi_none, psi_some] at h
    exact absurd h.symm (smul_ne_zero c'.ne_zero (stabProjector_ne_zero S'.toSignedStab))
  · rw [Subtype.ext_iff, psi_some, psi_none] at h
    exact absurd h (smul_ne_zero c.ne_zero (stabProjector_ne_zero S.toSignedStab))
  · rw [Subtype.ext_iff, psi_some, psi_some] at h
    have hc : (c : ℂ) = (c' : ℂ) := by
      have ht := congrArg (LinearMap.trace ℂ (QState n)) h
      rwa [map_smul, map_smul, stabProjector_trace, stabProjector_trace, smul_eq_mul, smul_eq_mul,
        mul_one, mul_one] at ht
    have hpi : stabProjector S.toSignedStab = stabProjector S'.toSignedStab := by
      rw [hc] at h
      exact smul_right_injective (QState n →ₗ[ℂ] QState n) c'.ne_zero h
    rw [Units.ext hc, phiObj_injective (Subtype.ext hpi)]

theorem psi_surjective : Function.Surjective (psi (n := n)) := by
  intro A
  by_cases hA : A.1 = 0
  · exact ⟨none, Subtype.ext (by rw [psi_none, hA])⟩
  · obtain ⟨c, S, hS, hfull, hAeq⟩ := A.2
    have hc0 : c ≠ 0 := fun h => hA (by rw [hAeq, h, zero_smul])
    refine ⟨some (Units.mk0 c hc0,
      ⟨tighten S, hS, hfull, fun p hp => tighten_sign_not_mem S hp⟩), ?_⟩
    apply Subtype.ext
    rw [psi_some, Units.val_mk0, hAeq]
    congr 1
    exact stabProjector_congr rfl (fun p hp => tighten_sign_mem S hp)

/-- The pointed bijection as an `Equiv`. -/
noncomputable def psiEquiv : Option (ℂˣ × PureSignedStab n) ≃
    {A : QState n →ₗ[ℂ] QState n // IsScaledStabDensity A} :=
  Equiv.ofBijective psi ⟨psi_injective, psi_surjective⟩

/-! ## The transported `𝒮`-side action and the equivalence -/

/-- The `𝒮`-side action: the operational monoid transported along `psiEquiv`. -/
noncomputable instance : MulAction (operationMonoid n) (Option (ℂˣ × PureSignedStab n)) where
  smul m x := psiEquiv.symm (m • psiEquiv x)
  one_smul x := by
    change psiEquiv.symm ((1 : operationMonoid n) • psiEquiv x) = x
    rw [one_smul, Equiv.symm_apply_apply]
  mul_smul m m' x := by
    change psiEquiv.symm ((m * m') • psiEquiv x)
      = psiEquiv.symm (m • psiEquiv (psiEquiv.symm (m' • psiEquiv x)))
    rw [mul_smul, Equiv.apply_symm_apply]

/-- `psi` is equivariant for the transported action (by construction). -/
theorem psi_smul (m : operationMonoid n) (x : Option (ℂˣ × PureSignedStab n)) :
    psi (m • x) = m • psi x :=
  psiEquiv.apply_symm_apply (m • psiEquiv x)

/-- The symplectic theory category with conditioning. -/
abbrev SCondCat (n : ℕ) := ActionCategory (operationMonoid n) (Option (ℂˣ × PureSignedStab n))

/-- The operational fragment category with conditioning. -/
abbrev OCondCat (n : ℕ) :=
  ActionCategory (operationMonoid n) {A : QState n →ₗ[ℂ] QState n // IsScaledStabDensity A}

/-- `psi` as a natural transformation of the action functors. -/
noncomputable def psiNat :
    actionAsFunctor (operationMonoid n) (Option (ℂˣ × PureSignedStab n)) ⟶
    actionAsFunctor (operationMonoid n) {A : QState n →ₗ[ℂ] QState n // IsScaledStabDensity A} where
  app _ := psi
  naturality _ _ g := by funext x; exact psi_smul g x

@[simp] theorem psiNat_app (x) : (psiNat (n := n)).app x = psi := rfl

/-- **The functor `𝒮 ⥤ 𝒪` (with conditioning)** induced by `psi`. -/
noncomputable def sToOCond : SCondCat n ⥤ OCondCat n := CategoryOfElements.map psiNat

instance : (sToOCond (n := n)).Faithful where
  map_injective h := Subtype.ext (congrArg (·.1) h)

instance : (sToOCond (n := n)).Full where
  map_surjective {X Y} k := by
    refine ⟨⟨k.1, ?_⟩, Subtype.ext rfl⟩
    apply psi_injective
    have hnat := congr_fun (psiNat.naturality k.1) X.2
    simp only [types_comp_apply, psiNat_app] at hnat
    exact hnat.trans k.2

instance : (sToOCond (n := n)).EssSurj where
  mem_essImage Y := by
    obtain ⟨x, hx⟩ := psi_surjective Y.2
    exact ⟨⟨Y.1, x⟩, ⟨eqToIso (congrArg (fun ρ => (⟨Y.1, ρ⟩ : OCondCat n)) hx)⟩⟩

instance : (sToOCond (n := n)).IsEquivalence where

/-- **`𝒮 ≃ 𝒪` with conditioning — the full equivalence.** The operational fragment
(Clifford conjugation + selective Lüders, on the scaled cone) is equivalent, as a
`CategoryTheory.Equivalence` of action categories of the generated operational monoid, to the
symplectic theory on the pointed signed-Lagrangian carrier. -/
noncomputable def stabilizerConditioningEquivalence : SCondCat n ≌ OCondCat n :=
  (sToOCond (n := n)).asEquivalence

/-! ## The transported action is the symplectic operation on generators

The `𝒮`-action is `operationMonoid` transported along `psi`. On the **Clifford
generator** it agrees with the *intrinsic* symplectic action `cliffordActionPure` — so the
equivalence's morphisms realize the symplectic operations, not merely a relabeling of `𝒪`. -/

@[simp] theorem psiEquiv_apply (x : Option (ℂˣ × PureSignedStab n)) : psiEquiv x = psi x := rfl

/-- A Clifford conjugation is an operation. -/
theorem qConjₗ_mem_operationMonoid (U : cliffordSubgroup n) :
    qConjₗ U.1 ∈ operationMonoid n :=
  Submonoid.subset_closure (Or.inl ⟨U, rfl⟩)

/-- **The transported Clifford generator acts as the symplectic `cliffordAction`.** -/
theorem operationMonoid_clifford_smul (U : cliffordSubgroup n) (c : ℂˣ) (S : PureSignedStab n) :
    (⟨qConjₗ U.1, qConjₗ_mem_operationMonoid U⟩ : operationMonoid n) • some (c, S)
      = some (c, cliffordActionPure U.2 S) := by
  have hstep : (⟨qConjₗ U.1, qConjₗ_mem_operationMonoid U⟩ : operationMonoid n)
        • psiEquiv (some (c, S))
      = psiEquiv (some (c, cliffordActionPure U.2 S)) := by
    apply Subtype.ext
    change qConjₗ U.1 ((psiEquiv (some (c, S))).1)
      = (psiEquiv (some (c, cliffordActionPure U.2 S))).1
    simp only [psiEquiv_apply, psi_some, qConjₗ_apply, cliffordActionPure_toSignedStab]
    rw [qConj_smul, qConj_stabProjector]
  change psiEquiv.symm (_ • psiEquiv (some (c, S))) = _
  rw [hstep, Equiv.symm_apply_apply]

/-- A selective Lüders (`ε² = 1`) is an operation. -/
theorem ludersChannelₗ_mem_operationMonoid (Q : Pauli n) {ε : ℂ} (hε : ε * ε = 1) :
    ludersChannelₗ Q ε ∈ operationMonoid n :=
  Submonoid.subset_closure (Or.inr ⟨Q, ε, hε, rfl⟩)

/-- **The transported deterministic Lüders generator (`Q ∈ L`, correct outcome) acts as the identity
`cond`** — matching `ludersChannel_stabProjector_self` (correct `Q ∈ L` outcome fixes the state). -/
theorem operationMonoid_luders_det_smul (c : ℂˣ) (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∈ S.toSignedStab.L) :
    (⟨ludersChannelₗ Q (S.toSignedStab.sign Q),
        ludersChannelₗ_mem_operationMonoid Q (sign_mul_self S.toSignedStab hQ)⟩ : operationMonoid n)
      • some (c, S) = some (c, S) := by
  have hsmul : ludersChannel Q (S.toSignedStab.sign Q) ((c : ℂ) • stabProjector S.toSignedStab)
      = (c : ℂ) • stabProjector S.toSignedStab := by
    rw [← ludersChannelₗ_apply, map_smul, ludersChannelₗ_apply,
      ludersChannel_stabProjector_self S.toSignedStab hQ]
  have hstep : (⟨ludersChannelₗ Q (S.toSignedStab.sign Q),
        ludersChannelₗ_mem_operationMonoid Q (sign_mul_self S.toSignedStab hQ)⟩ : operationMonoid n)
      • psiEquiv (some (c, S)) = psiEquiv (some (c, S)) := by
    apply Subtype.ext
    change ludersChannelₗ Q (S.toSignedStab.sign Q) ((psiEquiv (some (c, S))).1)
      = (psiEquiv (some (c, S))).1
    simp only [psiEquiv_apply, psi_some, ludersChannelₗ_apply]
    exact hsmul
  change psiEquiv.symm (_ • psiEquiv (some (c, S))) = _
  rw [hstep, Equiv.symm_apply_apply]

/-- **The transported non-deterministic Lüders generator (`Q ∉ L`, the collapse) acts as the
weighted `measSignedStab` conditioning** — `L ↦ pauliCondition L Q`, weight `c ↦ c/2` (Born `½`),
via `ludersChannel_stabProjector_notMem`. So the conditioning morphisms too realize the symplectic
measurement update — not merely a relabeling of `𝒪`. -/
theorem operationMonoid_luders_notMem_smul (c : ℂˣ) (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1) :
    ∃ S' : PureSignedStab n, S'.toSignedStab.L = pauliCondition S.toSignedStab.L Q ∧
      (⟨ludersChannelₗ Q ε, ludersChannelₗ_mem_operationMonoid Q hε⟩ : operationMonoid n)
          • some (c, S)
        = some (Units.mk0 ((c : ℂ) / 2) (div_ne_zero c.ne_zero two_ne_zero), S') := by
  obtain ⟨T, hTL, hluders⟩ :=
    ludersChannel_stabProjector_notMem S.toSignedStab S.isStab S.full hQ hε
  have hTstab : IsStabilizer T.L := by rw [hTL]; exact pauliCondition_isStabilizer S.isStab Q
  have hTfull : Module.finrank (ZMod 2) T.L = n := by
    rw [hTL]; exact pauliCondition_finrank S.isStab S.full Q
  refine ⟨⟨tighten T, by rw [tighten_L]; exact hTstab, by rw [tighten_L]; exact hTfull,
      fun p hp => tighten_sign_not_mem T hp⟩, by rw [tighten_L]; exact hTL, ?_⟩
  change psiEquiv.symm ((⟨ludersChannelₗ Q ε, ludersChannelₗ_mem_operationMonoid Q hε⟩
      : operationMonoid n) • psiEquiv (some (c, S))) = _
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  change ludersChannelₗ Q ε ((psiEquiv (some (c, S))).1) = _
  simp only [psiEquiv_apply, psi_some, ludersChannelₗ_apply, Units.val_mk0]
  rw [← ludersChannelₗ_apply, map_smul, ludersChannelₗ_apply, hluders, smul_smul,
    show stabProjector (tighten T) = stabProjector T from
      stabProjector_congr rfl (fun p hp => tighten_sign_mem T hp),
    div_eq_mul_inv]

end FTQCLib.Hilbert

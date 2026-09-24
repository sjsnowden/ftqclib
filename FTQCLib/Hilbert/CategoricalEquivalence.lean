/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CliffordGroupAction
import FTQCLib.Hilbert.StabilizerTheory
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Elements

/-! # The literal `𝒮 ≃ 𝒪` on the maximal subgroupoid

This file packages the proven faithful-representation core
(`stabilizer_operational_correspondence`) into a genuine `CategoryTheory.Equivalence` of the
**maximal subgroupoid** of the stabilizer–operational correspondence: the invertible (Clifford)
fragment, where `V⋊Sym(V)` is "the automorphisms of the maximal subgroupoid".

Both sides are `CategoryTheory.ActionCategory` of the **Clifford group** `cliffordSubgroup n`:

* `𝒮` over the signed Lagrangians `(L, χ)` (full-rank stabilizer, `χ` normalized to vanish off
  `L`), morphisms the symplectic action `cliffordAction`;
* `𝒪` over the pure stabilizer densities, morphisms Clifford conjugation `qConj`.

The equivariant bijection `stabProjector : PureSignedStab ≃ OCarrier` (injective by
`stabProjector_inj` + tightness, surjective by tightening, equivariant by `qConj_stabProjector`)
induces the equivalence via `CategoryOfElements.map`. The conditioning (Lüders) extension is in
`CategoricalConditioning.lean` and `CategoricalConditioningEquiv.lean`. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Stabilizer CategoryTheory

variable {n : ℕ}

/-! ## Carrier closure: a Clifford preserves stabilizer, rank, and tightness -/

/-- A Clifford symplectic map preserves the stabilizer (isotropy) property of a Lagrangian. -/
theorem cliffordAction_isStabilizer {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {S : SignedStab n} (hS : IsStabilizer S.L) :
    IsStabilizer (cliffordAction hU S).L := by
  intro p' hp' q' hq'
  rw [cliffordAction_L] at hp' hq'
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hp'
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hq'
  have h := cliffordToSymplectic_isClifford hU a b
  simp only [omegaBilin_apply] at h
  simpa only [LinearEquiv.coe_coe, h] using hS a ha b hb

/-- A Clifford symplectic map preserves the rank of a Lagrangian. -/
theorem cliffordAction_finrank {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : SignedStab n) :
    Module.finrank (ZMod 2) (cliffordAction hU S).L = Module.finrank (ZMod 2) S.L := by
  rw [cliffordAction_L, LinearEquiv.finrank_map_eq]

/-- The Clifford action preserves tightness (`sign = 0` off `L`). -/
theorem cliffordAction_tight {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {S : SignedStab n}
    (htight : ∀ p, p ∉ S.L → S.sign p = 0) :
    ∀ p, p ∉ (cliffordAction hU S).L → (cliffordAction hU S).sign p = 0 := by
  intro p hp
  rw [cliffordAction_sign]
  have hpre : (cliffordToSymplectic hU).symm p ∉ S.L := by
    intro hmem
    exact hp (by rw [cliffordAction_L]; exact ⟨_, hmem, LinearEquiv.apply_symm_apply _ _⟩)
  rw [htight _ hpre, mul_zero]

/-- `stabProjector` depends only on `(L, sign|_L)`: equal Lagrangians with signs agreeing on `L`
give the same projector. -/
theorem stabProjector_congr {S S' : SignedStab n} (hL : S.L = S'.L)
    (hsign : ∀ p ∈ S.L, S.sign p = S'.sign p) : stabProjector S = stabProjector S' := by
  rw [stabProjector_eq_sum_univ S, stabProjector_eq_sum_univ S']
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  simp only [stabCoeff]
  by_cases hp : p ∈ S.L
  · rw [if_pos hp, if_pos (hL ▸ hp), hsign p hp]
  · rw [if_neg hp, if_neg (hL ▸ hp)]

/-! ## The symplectic carrier `PureSignedStab` (signed Lagrangians, junk-free) -/

/-- A pure stabilizer state as the symplectic datum `(L, χ)`: a full-rank stabilizer Lagrangian with
its sign character, normalized to vanish off `L` so that `stabProjector` is injective. -/
structure PureSignedStab (n : ℕ) extends SignedStab n where
  isStab : IsStabilizer toSignedStab.L
  full : Module.finrank (ZMod 2) toSignedStab.L = n
  tight : ∀ p, p ∉ toSignedStab.L → toSignedStab.sign p = 0

/-- Two `PureSignedStab` are equal once their underlying `SignedStab` agree. -/
theorem pureSignedStab_ext {S S' : PureSignedStab n}
    (h : S.toSignedStab = S'.toSignedStab) : S = S' := by
  cases S; cases S'; cases h; rfl

/-- The Clifford action lifted to the junk-free symplectic carrier. -/
noncomputable def cliffordActionPure {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : PureSignedStab n) : PureSignedStab n where
  toSignedStab := cliffordAction hU S.toSignedStab
  isStab := cliffordAction_isStabilizer hU S.isStab
  full := by rw [cliffordAction_finrank]; exact S.full
  tight := cliffordAction_tight hU S.tight

@[simp] theorem cliffordActionPure_toSignedStab {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : PureSignedStab n) :
    (cliffordActionPure hU S).toSignedStab = cliffordAction hU S.toSignedStab := rfl

/-- `𝒮`-side action of the Clifford group on the symplectic carrier. -/
noncomputable instance : MulAction (cliffordSubgroup n) (PureSignedStab n) where
  smul U S := cliffordActionPure U.2 S
  one_smul S := by
    refine pureSignedStab_ext ?_
    change cliffordAction (1 : cliffordSubgroup n).2 S.toSignedStab = S.toSignedStab
    rw [cliffordAction_irrel (1 : cliffordSubgroup n).2 isCliffordOperator_one, cliffordAction_one]
  mul_smul U V S := by
    refine pureSignedStab_ext ?_
    change cliffordAction (U * V).2 S.toSignedStab
      = cliffordAction U.2 (cliffordAction V.2 S.toSignedStab)
    rw [cliffordAction_irrel (U * V).2 (isCliffordOperator_mul U.2 V.2), cliffordAction_mul]

@[simp] theorem smul_pureSignedStab_toSignedStab (U : cliffordSubgroup n) (S : PureSignedStab n) :
    (U • S).toSignedStab = cliffordAction U.2 S.toSignedStab := rfl

/-! ## The operational carrier `OCarrier` (pure stabilizer densities) -/

/-- The operational carrier: pure stabilizer density operators. -/
abbrev OCarrier (n : ℕ) : Type := {ρ : QState n →ₗ[ℂ] QState n // IsPureStabDensity ρ}

/-- Clifford conjugation preserves pure stabilizer density operators. -/
theorem qConj_isPureStabDensity {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    {ρ : QState n →ₗ[ℂ] QState n} (hρ : IsPureStabDensity ρ) : IsPureStabDensity (qConj U ρ) := by
  obtain ⟨S, hS, hfull, rfl⟩ := hρ
  rw [qConj_stabProjector hU]
  exact ⟨cliffordAction hU S, cliffordAction_isStabilizer hU hS, by
    rw [cliffordAction_finrank]; exact hfull, rfl⟩

/-- `𝒪`-side action of the Clifford group by conjugation. -/
noncomputable instance : MulAction (cliffordSubgroup n) (OCarrier n) where
  smul U ρ := ⟨qConj U.1 ρ.1, qConj_isPureStabDensity U.2 ρ.2⟩
  one_smul ρ := Subtype.ext (qConj_one ρ.1)
  mul_smul U V ρ := Subtype.ext (qConj_mul U.1 V.1 ρ.1)

@[simp] theorem smul_oCarrier_val (U : cliffordSubgroup n) (ρ : OCarrier n) :
    (U • ρ).1 = qConj U.1 ρ.1 := rfl

/-! ## The equivariant bijection `stabProjector : PureSignedStab ≃ OCarrier` -/

/-- The object map of the equivalence: a signed Lagrangian to its pure stabilizer density. -/
noncomputable def phiObj (S : PureSignedStab n) : OCarrier n :=
  ⟨stabProjector S.toSignedStab, S.toSignedStab, S.isStab, S.full, rfl⟩

@[simp] theorem phiObj_val (S : PureSignedStab n) :
    (phiObj S).1 = stabProjector S.toSignedStab := rfl

/-- `phiObj` is `cliffordSubgroup`-equivariant (the key lemma `qConj_stabProjector`). -/
theorem phiObj_smul (U : cliffordSubgroup n) (S : PureSignedStab n) :
    phiObj (U • S) = U • phiObj S := by
  apply Subtype.ext
  change stabProjector (cliffordAction U.2 S.toSignedStab)
    = qConj U.1 (stabProjector S.toSignedStab)
  exact (qConj_stabProjector U.2 S.toSignedStab).symm

/-- `phiObj` is injective: tightness removes the only ambiguity (`stabProjector_inj` already pins
`L` and `sign` on `L`). -/
theorem phiObj_injective : Function.Injective (phiObj (n := n)) := by
  intro S S' h
  have hp : stabProjector S.toSignedStab = stabProjector S'.toSignedStab := Subtype.ext_iff.mp h
  obtain ⟨hL, hsignL⟩ := stabProjector_inj hp
  refine pureSignedStab_ext (signedStab_ext hL ?_)
  funext p
  by_cases hpL : p ∈ S.toSignedStab.L
  · exact hsignL p hpL
  · rw [S.tight p hpL, S'.tight p (hL ▸ hpL)]

open Classical in
/-- Tighten a signed stabilizer: zero the junk off `L`. Preserves `L` and `sign` on `L`. -/
noncomputable def tighten (S : SignedStab n) : SignedStab n where
  L := S.L
  sign p := if p ∈ S.L then S.sign p else 0
  sign_zero := by rw [if_pos S.L.zero_mem, S.sign_zero]
  valid := by
    intro p hp q hq
    rw [if_pos hp, if_pos hq, if_pos (S.L.add_mem hp hq)]
    exact S.valid p hp q hq

@[simp] theorem tighten_L (S : SignedStab n) : (tighten S).L = S.L := rfl

open Classical in
theorem tighten_sign_mem (S : SignedStab n) {p : Pauli n} (hp : p ∈ S.L) :
    (tighten S).sign p = S.sign p := if_pos hp

open Classical in
theorem tighten_sign_not_mem (S : SignedStab n) {p : Pauli n} (hp : p ∉ S.L) :
    (tighten S).sign p = 0 := if_neg hp

/-- `phiObj` is surjective: every pure stabilizer density is the projector of a tightened stabilizer
signed Lagrangian. -/
theorem phiObj_surjective : Function.Surjective (phiObj (n := n)) := by
  intro ρ
  obtain ⟨S, hS, hfull, hρ⟩ := ρ.2
  refine ⟨⟨tighten S, hS, hfull, fun p hp => tighten_sign_not_mem S hp⟩, ?_⟩
  apply Subtype.ext
  change stabProjector (tighten S) = ρ.1
  rw [hρ]
  exact stabProjector_congr rfl (fun p hp => tighten_sign_mem S hp)

/-! ## The categories `𝒮`, `𝒪` and the equivalence

Both are `ActionCategory` of the Clifford group; the equivariant bijection `phiObj` induces the
equivalence via `CategoryOfElements.map`. -/

/-- The symplectic theory category `𝒮` — the action groupoid of the Clifford group on signed
Lagrangians. -/
abbrev SCat (n : ℕ) := ActionCategory (cliffordSubgroup n) (PureSignedStab n)

/-- The operational fragment category `𝒪` — the action groupoid of the Clifford group on pure
stabilizer densities. -/
abbrev OCat (n : ℕ) := ActionCategory (cliffordSubgroup n) (OCarrier n)

/-- The equivariant bijection `phiObj`, as a natural transformation of the action functors. -/
noncomputable def phiNat : actionAsFunctor (cliffordSubgroup n) (PureSignedStab n) ⟶
    actionAsFunctor (cliffordSubgroup n) (OCarrier n) where
  app _ := phiObj
  naturality _ _ g := by funext S; exact phiObj_smul g S

@[simp] theorem phiNat_app (x) : (phiNat (n := n)).app x = phiObj := rfl

/-- **The functor `𝒮 ⥤ 𝒪`** induced by `phiObj` (object map `(L,χ) ↦ Π`, identity on group
elements). -/
noncomputable def sToO : SCat n ⥤ OCat n := CategoryOfElements.map phiNat

instance : (sToO (n := n)).Faithful where
  map_injective h := Subtype.ext (congrArg (·.1) h)

instance : (sToO (n := n)).Full where
  map_surjective {X Y} k := by
    refine ⟨⟨k.1, ?_⟩, Subtype.ext rfl⟩
    apply phiObj_injective
    have hnat := congr_fun (phiNat.naturality k.1) X.2
    simp only [types_comp_apply, phiNat_app] at hnat
    exact hnat.trans k.2

instance : (sToO (n := n)).EssSurj where
  mem_essImage Y := by
    obtain ⟨S, hS⟩ := phiObj_surjective Y.2
    exact ⟨⟨Y.1, S⟩, ⟨eqToIso (congrArg (fun ρ : OCarrier n => (⟨Y.1, ρ⟩ : OCat n)) hS)⟩⟩

instance : (sToO (n := n)).IsEquivalence where

/-- **`𝒮 ≃ 𝒪` (maximal subgroupoid).** The literal `CategoryTheory.Equivalence` between the
symplectic theory `𝒮` and the operational fragment `𝒪` on the invertible (Clifford) fragment of the
stabilizer–operational correspondence: the functor `sToO` (the proven equivariant bijection `stabProjector`) is fully
faithful and essentially surjective. The conditioning (selective Lüders) extension is
`CategoricalConditioningEquiv.lean`. -/
noncomputable def stabilizerSymplecticEquivalence : SCat n ≌ OCat n :=
  (sToO (n := n)).asEquivalence

end FTQCLib.Hilbert

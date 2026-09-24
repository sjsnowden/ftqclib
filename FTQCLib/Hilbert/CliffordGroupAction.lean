/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.StabilizerEquiv
import FTQCLib.Hilbert.AffineSymplectic

/-! # Clifford-group action infrastructure (M1 for `prop:corr`'s `𝒮 ≃ 𝒪`)

The `CategoryTheory.ActionCategory` packaging of the note's `prop:corr` (`𝒮 ≃ 𝒪`) needs the Clifford
generators to assemble into genuine *group actions* (`MulAction`) on the two carriers. The Clifford
group `cliffordSubgroup n` and the homomorphism `Φ = cliffordToSp` already exist
(`AffineSymplectic.lean`); here we add the functoriality of the two generator families, i.e. the
`MulAction` axioms (`one_smul`, `mul_smul`) on the full `SignedStab n` / operator algebra:

* `qConj` (operator conjugation `A ↦ U A U⁻¹`) is multiplicative in `U`: `qConj_one`, `qConj_mul`;
* `cliffordSign` (the Heisenberg sign `μ`) is a crossed homomorphism: `cliffordSign_one`,
  `cliffordSign_mul`;
* `cliffordAction` (the symplectic action on `SignedStab`) is functorial: `cliffordAction_one`,
  `cliffordAction_mul`, with witness-irrelevance `cliffordAction_irrel`.

The carrier restriction and the equivalence are built on top in `CategoricalEquivalence.lean`. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates

variable {n : ℕ}

/-- Extensionality for `SignedStab` (it carries no auto-`@[ext]`): two are equal once their
Lagrangian `L` and sign function agree; the `Prop` fields close by proof irrelevance. -/
theorem signedStab_ext {S S' : SignedStab n} (hL : S.L = S'.L) (hsign : S.sign = S'.sign) :
    S = S' := by
  cases S with | mk L s sz v =>
  cases S' with | mk L' s' sz' v' =>
  subst hL; subst hsign; rfl

/-- The Lagrangian field of `cliffordAction` (definitional accessor). -/
@[simp] theorem cliffordAction_L {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : SignedStab n) :
    (cliffordAction hU S).L = Submodule.map (cliffordToSymplectic hU).toLinearMap S.L := rfl

/-- The sign field of `cliffordAction` (definitional accessor). -/
@[simp] theorem cliffordAction_sign {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (S : SignedStab n) (p : Pauli n) :
    (cliffordAction hU S).sign p
      = cliffordSign hU ((cliffordToSymplectic hU).symm p)
          * S.sign ((cliffordToSymplectic hU).symm p) := rfl

/-! ## `qConj` is multiplicative in the conjugating Clifford -/

/-- `qConj 1 A = A`: conjugation by the identity Clifford is trivial. -/
@[simp] theorem qConj_one (A : QState n →ₗ[ℂ] QState n) :
    qConj (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n) A = A := by
  ext ψ
  simp only [qConj_apply, qClifford_apply, qClifford_symm_apply, LinearEquiv.one_eq_refl,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply]

/-- `qConj (U*V) A = qConj U (qConj V A)`: conjugation is multiplicative in the conjugating Clifford
(`U*V` applies `V` first, matching `qClifford (U*V) = qClifford U ∘ qClifford V`). -/
theorem qConj_mul (U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (A : QState n →ₗ[ℂ] QState n) :
    qConj (U * V) A = qConj U (qConj V A) := by
  ext ψ
  simp only [qConj_apply, qClifford_apply, qClifford_symm_apply, LinearEquiv.mul_eq_trans,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]

/-! ## `cliffordSign` is a crossed homomorphism in the Clifford -/

/-- `cliffordSign 1 p = 1`: the identity Clifford picks up no sign. -/
theorem cliffordSign_one (p : Pauli n) :
    cliffordSign (isCliffordOperator_one (n := n)) p = 1 := by
  have hwit : (conjEquiv (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (pauliEquiv p)).toLinearMap
      = ((1 : ℂˣ) : ℂ) • pauliOperator p := by
    rw [conjEquiv_one]
    ext ψ
    simp [pauliEquiv_apply, Units.val_one]
  have hphase : (cliffordToSymplecticPhase (isCliffordOperator_one (n := n)) p : ℂ) = 1 := by
    rw [← cliffordToSymplecticPhase_unique (isCliffordOperator_one (n := n)) p hwit]
    simp
  rw [cliffordSign, hphase, cliffordToSymplecticFun_one, mul_one,
    mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero)]

/-- The two Heisenberg expansions of `qConj (U*V) (H p)` agree, so the signs satisfy the
crossed-homomorphism law `μ_{UV}(p) = μ_V(p)·μ_U(Φ_V p)`. -/
theorem cliffordSign_mul {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) (p : Pauli n) :
    cliffordSign (isCliffordOperator_mul hU hV) p
      = cliffordSign hV p * cliffordSign hU (cliffordToSymplecticFun hV p) := by
  set r := cliffordToSymplecticFun hU (cliffordToSymplecticFun hV p) with hr
  set c := cliffordSign hV p * cliffordSign hU (cliffordToSymplecticFun hV p) with hc
  have hpos : cliffordToSymplecticFun (isCliffordOperator_mul hU hV) p = r :=
    cliffordToSymplecticFun_mul hU hV p
  have hlhs : qConj (U * V) (pauliHermitian p)
      = cliffordSign (isCliffordOperator_mul hU hV) p • pauliHermitian r := by
    rw [qConj_pauliHermitian, hpos]
  have hrhs : qConj (U * V) (pauliHermitian p) = c • pauliHermitian r := by
    rw [qConj_mul, qConj_pauliHermitian hV, qConj_smul, qConj_pauliHermitian hU, smul_smul, hr, hc]
  have hsmul : cliffordSign (isCliffordOperator_mul hU hV) p • pauliHermitian r
      = c • pauliHermitian r := by rw [← hlhs, hrhs]
  have hcomp := congrArg (· ∘ₗ pauliHermitian r) hsmul
  simp only [LinearMap.smul_comp, pauliHermitian_sq] at hcomp
  have hfr : (Module.finrank ℂ (QState n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr := congrArg (LinearMap.trace ℂ (QState n)) hcomp
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, LinearMap.trace_id] at htr
  exact mul_right_cancel₀ hfr htr

/-! ## `cliffordAction` is a group action on `SignedStab n` -/

/-- Witness-irrelevance of the Clifford action: it depends only on `U`, not the Clifford proof
(`IsCliffordOperator U` is a `Prop`, hence a `Subsingleton`). -/
theorem cliffordAction_irrel {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h h' : IsCliffordOperator U) (S : SignedStab n) :
    cliffordAction h S = cliffordAction h' S := by
  rw [Subsingleton.elim h h']

/-- `cliffordAction 1 S = S`: the identity Clifford acts trivially (`one_smul`). -/
theorem cliffordAction_one (S : SignedStab n) :
    cliffordAction (isCliffordOperator_one (n := n)) S = S := by
  refine signedStab_ext ?_ ?_
  · simp only [cliffordAction_L, cliffordToSymplectic_one, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_toLinearMap, Submodule.map_id]
  · funext p
    simp only [cliffordAction_sign, cliffordToSymplectic_one, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply]
    rw [cliffordSign_one, one_mul]

/-- `cliffordAction (U*V) S = cliffordAction U (cliffordAction V S)`: the symplectic action is
functorial in the Clifford (the `mul_smul` axiom on `SignedStab`). -/
theorem cliffordAction_mul {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) (S : SignedStab n) :
    cliffordAction (isCliffordOperator_mul hU hV) S = cliffordAction hU (cliffordAction hV S) := by
  refine signedStab_ext ?_ ?_
  · simp only [cliffordAction_L, cliffordToSymplectic_comp hU hV]
    rw [← Submodule.map_comp]
    rfl
  · funext p
    simp only [cliffordAction_sign]
    set ΦU := cliffordToSymplectic hU with hΦU
    set ΦV := cliffordToSymplectic hV with hΦV
    have hpre : (cliffordToSymplectic (isCliffordOperator_mul hU hV)).symm p
        = ΦV.symm (ΦU.symm p) := by
      rw [cliffordToSymplectic_comp hU hV]; rfl
    rw [hpre]
    have hcs := cliffordSign_mul hU hV (ΦV.symm (ΦU.symm p))
    have hFunV : cliffordToSymplecticFun hV (ΦV.symm (ΦU.symm p)) = ΦU.symm p := by
      rw [← cliffordToSymplectic_apply]; exact LinearEquiv.apply_symm_apply ΦV _
    rw [hFunV] at hcs
    rw [hcs]
    ring

end FTQCLib.Hilbert

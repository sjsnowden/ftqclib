/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.SignedSymplectic
import FTQCLib.Hilbert.FloorChart
import FTQCLib.Hilbert.AffineSymplecticGroup

/-! # The faithful bridge `cliffordModPhase n →* SignedSymplectic n`

The abstract Clifford group mod phase injects into the computable `SignedSymplectic` model via its
conjugation action: symplectic part `cliffordToSymplectic`, sign part `clog ∘ cliffordSign`, with the
`valid` field being exactly `clog_cliffordSign_cocycle`. We only need this to be a **homomorphism
compatible with the symplectic projection** (injectivity is not used — the non-split discharge pushes
forward through `act`). -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame FTQCLib.Hilbert

variable {n : ℕ}

/-- The conjugation action on `cliffordSubgroup n`, valued in the computable model. -/
noncomputable def actSub : cliffordSubgroup n →* SignedSymplectic n where
  toFun U :=
    { g := cliffordToSymplectic U.2
      hg := cliffordToSymplectic_isClifford U.2
      s := fun p => clog (cliffordSign U.2 p)
      valid := by
        intro p q
        have h := clog_cliffordSign_cocycle U p q
        rw [frameDistortion, cliffordToSymplectic_apply, cliffordToSymplectic_apply]
        exact h }
  map_one' := by
    refine SignedSymplectic.ext ?_ ?_
    · show cliffordToSymplectic (1 : cliffordSubgroup n).2 = LinearEquiv.refl (ZMod 2) (Pauli n)
      rw [cliffordToSymplectic_irrel (1 : cliffordSubgroup n).2 isCliffordOperator_one,
        cliffordToSymplectic_one]; rfl
    · funext p
      show clog (cliffordSign isCliffordOperator_one p) = (0 : ZMod 4)
      rw [cliffordSign_one, clog_one]
  map_mul' U V := by
    refine SignedSymplectic.ext ?_ ?_
    · show cliffordToSymplectic (U * V).2
        = (cliffordToSymplectic V.2).trans (cliffordToSymplectic U.2)
      rw [cliffordToSymplectic_irrel (U * V).2 (isCliffordOperator_mul U.2 V.2),
        cliffordToSymplectic_comp]; rfl
    · funext p
      show clog (cliffordSign (isCliffordOperator_mul U.2 V.2) p)
        = clog (cliffordSign V.2 p) + clog (cliffordSign U.2 (cliffordToSymplectic V.2 p))
      rw [cliffordSign_mul U.2 V.2 p,
        clog_mul (isMu4_cliffordSign V.2 p) (isMu4_cliffordSign U.2 _),
        cliffordToSymplectic_apply]

/-- A global phase `α · id` picks up no conjugation sign: `cliffordSign = 1`. Conjugation by a scalar
is trivial, so the symplectic phase is `1` and the symplectic map is the identity, and the `I^{xz}`
renormalizations at `p` and `g p = p` cancel. -/
theorem cliffordSign_phaseInclusion (α : ℂˣ) (p : Pauli n) :
    cliffordSign (phaseInclusion n α).2 p = 1 := by
  have hg : cliffordToSp (phaseInclusion n α) = 1 :=
    MonoidHom.mem_ker.mp (phaseSubgroup_le_ker n ⟨α, rfl⟩)
  have hgfun : cliffordToSymplectic (phaseInclusion n α).2 = 1 := congrArg Subtype.val hg
  have hwit : (conjEquiv (phaseInclusion n α).val (pauliEquiv p)).toLinearMap
      = ((1 : ℂˣ) : ℂ) • pauliOperator p := by
    apply LinearMap.ext; intro ψ
    show conjEquiv (scaleEquiv α 1) (pauliEquiv p) ψ = ((1 : ℂˣ) : ℂ) • pauliOperator p ψ
    simp only [conjEquiv_apply, scaleEquiv_symm_apply, scaleEquiv_apply, LinearEquiv.one_eq_refl,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply, map_smul, smul_smul, Units.val_one, one_smul,
      pauliEquiv_apply]
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero α), one_smul]
  have hphase : (cliffordToSymplecticPhase (phaseInclusion n α).2 p : ℂ) = 1 := by
    rw [← cliffordToSymplecticPhase_unique (phaseInclusion n α).2 p hwit]; simp
  have hfun : cliffordToSymplecticFun (phaseInclusion n α).2 p = p := by
    rw [← cliffordToSymplectic_apply, hgfun]; rfl
  rw [cliffordSign, hphase, hfun, mul_one, mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero)]

/-- `actSub` kills global phases, so it descends to `cliffordModPhase`. -/
theorem actSub_phaseInclusion (α : ℂˣ) : actSub (phaseInclusion n α) = 1 := by
  refine SignedSymplectic.ext ?_ ?_
  · show cliffordToSymplectic (phaseInclusion n α).2 = LinearEquiv.refl (ZMod 2) (Pauli n)
    rw [← LinearEquiv.one_eq_refl]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp (phaseSubgroup_le_ker n ⟨α, rfl⟩))
  · funext p
    show clog (cliffordSign (phaseInclusion n α).2 p) = (0 : ZMod 4)
    rw [cliffordSign_phaseInclusion, clog_one]

theorem phaseSubgroup_le_ker_actSub : phaseSubgroup n ≤ (actSub (n := n)).ker := by
  rintro _ ⟨α, rfl⟩
  exact MonoidHom.mem_ker.mpr (actSub_phaseInclusion α)

/-- **The faithful bridge**, descended to `cliffordModPhase n`. -/
noncomputable def act : cliffordModPhase n →* SignedSymplectic n :=
  QuotientGroup.lift (phaseSubgroup n) actSub phaseSubgroup_le_ker_actSub

/-- **Projection-compatible:** the symplectic part of `act c` is `cliffordModPhaseToSp c`. This is
what the non-split discharge needs — it pins the `g`-part of a pushed-forward section to the chosen
`Sp` element. -/
@[simp] theorem act_g (c : cliffordModPhase n) :
    (act c).g = (cliffordModPhaseToSp n c).val := by
  induction c using QuotientGroup.induction_on with
  | _ U => rfl

end FTQCLib.Cohomology

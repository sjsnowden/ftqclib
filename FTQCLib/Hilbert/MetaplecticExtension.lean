/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.TransvectionLift
import FTQCLib.Frame.MetaplecticExtension

set_option linter.unusedSectionVars false

/-!
# The Hilbert realization: `MetaGate n` IS the projective Clifford group

The certificate layer for the frame-side extension (`FTQCLib/Frame/MetaplecticExtension.lean`),
following the floor-chart pattern — the object is defined frame-purely, and this file proves it
is exactly the projective Clifford group:

* `toMetaGate` — the gate datum of a Clifford operator (symplectic part + `clog` of the sign
  character), validity transported from `cliffordSign_cocycle`;
* `toMetaGate_mul` — multiplicativity: the crossed-homomorphism sign law IS the extension's
  group law;
* `toMetaGate_inj` — equal gate data ⟹ equal operators mod `ℂˣ` (the selection theorem
  `cliffordOperator_unique_of_sign` in extension form);
* `toMetaGate_surjective` — **the realization theorem**: every abstract `(g, c)` is realized
  (symplecticity from validity, base lift from `cliffordSymplecticLift_unconditional`, cochain
  correction by the fiber twist);
* anchors: `toMetaGate_rotGate` (the transvection lifts of `TransvectionLift.lean` land on
  `(τ_v, rotSign v)`) and `toMetaGate_pauliEquiv` (Pauli operators land on the kernel twists).
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame Complex

variable {n : ℕ}

private lemma zmod2_dichot : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

lemma cliffordSign_pm_one {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (p : Pauli n) :
    cliffordSign hU p = 1 ∨ cliffordSign hU p = -1 :=
  mul_self_eq_one_iff.mp (cliffordSign_mul_self hU p)

lemma isMu4_cliffordSign {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (p : Pauli n) :
    IsMu4 (cliffordSign hU p) := by
  rcases cliffordSign_pm_one hU p with h | h <;> rw [h] <;> unfold IsMu4 <;> tauto

/-- The `clog`-transported cocycle law for any Clifford operator's sign character. -/
lemma clog_sign_valid {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (a b : Pauli n) :
    clog (cliffordSign hU a) + clog (cliffordSign hU b)
        + betaFrame (cliffordToSymplecticFun hU a) (cliffordToSymplecticFun hU b)
      = clog (cliffordSign hU (a + b)) + betaFrame a b := by
  have hc := cliffordSign_cocycle hU a b
  rw [pauliPhase_eq_iZ4_betaFrame, pauliPhase_eq_iZ4_betaFrame,
    show cliffordSign hU a = iZ4 (clog (cliffordSign hU a)) from
      (iZ4_clog (isMu4_cliffordSign hU a)).symm,
    show cliffordSign hU b = iZ4 (clog (cliffordSign hU b)) from
      (iZ4_clog (isMu4_cliffordSign hU b)).symm,
    show cliffordSign hU (a + b) = iZ4 (clog (cliffordSign hU (a + b))) from
      (iZ4_clog (isMu4_cliffordSign hU (a + b))).symm,
    ← iZ4_add, ← iZ4_add, ← iZ4_add] at hc
  have h4 := congrArg clog hc
  rwa [clog_iZ4, clog_iZ4] at h4

/-- **The gate datum of a Clifford operator**: its symplectic part and the `clog` of its sign
character. -/
noncomputable def toMetaGate {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) : MetaGate n where
  g := cliffordToSymplectic hU
  c := fun p => clog (cliffordSign hU p)
  valid := fun a b => by
    simpa only [cliffordToSymplectic_apply] using clog_sign_valid hU a b

@[simp] lemma toMetaGate_g {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) : (toMetaGate hU).g = cliffordToSymplectic hU := rfl
@[simp] lemma toMetaGate_c {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (p : Pauli n) :
    (toMetaGate hU).c p = clog (cliffordSign hU p) := rfl

/-- `toMetaGate` is multiplicative: the crossed-homomorphism sign law becomes the extension's
group law. -/
theorem toMetaGate_mul {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) :
    toMetaGate (isCliffordOperator_mul hU hV) = toMetaGate hU * toMetaGate hV := by
  refine MetaGate.ext ?_ ?_
  · rw [MetaGate.mul_g, toMetaGate_g, toMetaGate_g, toMetaGate_g, cliffordToSymplectic_comp,
      LinearEquiv.mul_eq_trans]
  · funext p
    rw [toMetaGate_c, MetaGate.mul_c, toMetaGate_c, toMetaGate_c, toMetaGate_g,
      cliffordSign_mul hU hV p, cliffordToSymplectic_apply]
    rcases cliffordSign_pm_one hV p with h1 | h1 <;>
      rcases cliffordSign_pm_one hU (cliffordToSymplecticFun hV p) with h2 | h2 <;>
      rw [h1, h2] <;>
      simp only [mul_one, mul_neg, neg_neg, clog_one, clog_neg_one] <;>
      decide

/-- **Injectivity mod phase**: equal gate data forces equal operators up to `ℂˣ` — the selection
theorem `cliffordOperator_unique_of_sign` in extension form. -/
theorem toMetaGate_inj {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V)
    (h : toMetaGate hU = toMetaGate hV) :
    ∃ α : ℂˣ, V.toLinearMap = (α : ℂ) • U.toLinearMap := by
  have hg : cliffordToSymplectic hU = cliffordToSymplectic hV := congrArg MetaGate.g h
  have hcfun := congrArg MetaGate.c h
  have hsig : ∀ p, cliffordSign hU p = cliffordSign hV p := by
    intro p
    have hcp : clog (cliffordSign hU p) = clog (cliffordSign hV p) := congrFun hcfun p
    have h4 := congrArg iZ4 hcp
    rwa [iZ4_clog (isMu4_cliffordSign hU p), iZ4_clog (isMu4_cliffordSign hV p)] at h4
  exact cliffordOperator_unique_of_sign hU hV hg hsig

/-- **Surjectivity (the realization theorem)**: every abstract gate datum is realized by an
actual Clifford operator. Symplecticity comes from validity, the base lift from
`cliffordSymplecticLift_unconditional`, and the
cochain correction from the fiber twist plus the kernel classification. With `toMetaGate_mul`
and `toMetaGate_inj`, this says **`MetaGate n` is the projective Clifford group, presented
frame-purely.** -/
theorem toMetaGate_surjective (x : MetaGate n) :
    ∃ (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (hU : IsCliffordOperator U),
      toMetaGate hU = x := by
  obtain ⟨U₀, hU₀, hΦ⟩ := cliffordSymplecticLift_unconditional n x.g x.isClifford
  have hFun : ∀ a, cliffordToSymplecticFun hU₀ a = x.g a := by
    intro a
    rw [← cliffordToSymplectic_apply, hΦ]
  -- the cochain difference is additive
  have hadd : ∀ a b,
      (x.c (a + b) - clog (cliffordSign hU₀ (a + b)))
        = (x.c a - clog (cliffordSign hU₀ a)) + (x.c b - clog (cliffordSign hU₀ b)) := by
    intro a b
    have h1 := x.valid a b
    have h2 := clog_sign_valid hU₀ a b
    rw [hFun, hFun] at h2
    linear_combination h2 - h1
  obtain ⟨w, hw⟩ := exists_twist_of_additive
    (fun p => x.c p - clog (cliffordSign hU₀ p)) hadd
  -- correct the lift by the Pauli twist at `x.g w`
  refine ⟨pauliEquiv (x.g w) * U₀,
    isCliffordOperator_mul (isCliffordOperator_pauliEquiv (x.g w)) hU₀, ?_⟩
  refine MetaGate.ext ?_ ?_
  · rw [toMetaGate_g, cliffordToSymplectic_comp (isCliffordOperator_pauliEquiv (x.g w)) hU₀,
      cliffordToSymplectic_pauliEquiv, one_mul, hΦ]
  · funext p
    rw [toMetaGate_c, cliffordSign_pauli_twist hU₀ (x.g w) p, hFun]
    -- ω(x.g w, x.g p) = ω(w, p) by symplecticity
    have hωg : omega (x.g w) (x.g p) = omega w p := by
      have h := x.isClifford w p
      rwa [omegaBilin_apply, omegaBilin_apply] at h
    rw [hωg]
    have hwp := hw p
    -- x.c p = 2·ω(w,p) + clog μ₀ p
    have hxc : x.c p = ((2 * (omega w p).val : ℕ) : ZMod 4) + clog (cliffordSign hU₀ p) := by
      linear_combination hwp
    rw [hxc]
    rcases zmod2_dichot (omega w p) with hω | hω <;>
      rcases cliffordSign_pm_one hU₀ p with hμ | hμ <;>
      rw [hω, hμ] <;>
      simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, one_mul, neg_mul, neg_neg,
        mul_one, clog_one, clog_neg_one] <;>
      decide

/-! ## Anchors: the transvection family and the Pauli kernel land where they should -/

/-- The transvection data as an abstract gate. -/
noncomputable def rotMetaGate (v : Pauli n) : MetaGate n where
  g := transvectionEquiv v
  c := rotSign v
  valid := fun a b => by
    have h := rotSign_validity v (transvectionEquiv v a) (transvectionEquiv v b)
    rw [transvectionEquiv_invol, transvectionEquiv_invol,
      show transvectionEquiv v a + transvectionEquiv v b = transvectionEquiv v (a + b) from
        (map_add (transvectionEquiv v) a b).symm,
      transvectionEquiv_invol] at h
    linear_combination h

/-- The rotation lifts realize the transvection data:
`toMetaGate (rotGate v) = (τ_v, rotSign v)`. -/
theorem toMetaGate_rotGate (v : Pauli n) :
    toMetaGate (isCliffordOperator_rotGate v) = rotMetaGate v := by
  refine MetaGate.ext ?_ ?_
  · refine LinearEquiv.ext fun p => ?_
    rw [toMetaGate_g, cliffordToSymplectic_apply, cliffordFun_rotGate]
    rfl
  · funext p
    rw [toMetaGate_c, cliffordSign_rotGate, clog_iZ4]
    rfl

/-- Pauli operators land on the kernel twists: `toMetaGate (pauliEquiv w) = twistGate w`. -/
theorem toMetaGate_pauliEquiv (w : Pauli n) :
    toMetaGate (isCliffordOperator_pauliEquiv w) = twistGate w := by
  refine MetaGate.ext ?_ ?_
  · rw [toMetaGate_g, cliffordToSymplectic_pauliEquiv]
    rfl
  · funext p
    rw [toMetaGate_c, cliffordSign_pauliEquiv]
    show clog ((-1 : ℂ) ^ (omega w p).val) = ((2 * (omega w p).val : ℕ) : ZMod 4)
    rcases zmod2_dichot (omega w p) with h | h <;> rw [h] <;>
      simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, clog_one, clog_neg_one] <;>
      decide

end FTQCLib.Hilbert

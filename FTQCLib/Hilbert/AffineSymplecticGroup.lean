/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.AffineSymplectic
import FTQCLib.Hilbert.GateLifts
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.End


/-!
# The affine symplectic group `V ⋊ Sp(V)`

The isomorphism `Clₙ / (U(1)·Pauli) ≅ Sp(V)` (`cliffordQuotientEquivSp`) refines to the
finer statement `Clₙ / U(1) ≅ V ⋊ Sp(V)`, where the right-hand side is the **affine symplectic
group** of the Pauli phase space `V = Pauli n`. The translation part `V` is the Pauli subgroup mod
phase — the affine "byproduct" shifts — and the linear part `Sp(V)` is the conjugation action of
Cliffords modulo Paulis.

This file builds the right-hand side as a Mathlib `SemidirectProduct`. Since `V = Pauli n` is an
additive group, it enters as the multiplicative type tag `Multiplicative (Pauli n)`; the symplectic
group `spSubgroup n` acts through `spAction`, which sends a symplectic linear equivalence to its
underlying additive automorphism (transported across the `Multiplicative` tag by
`MulAutMultiplicative`).

The mul orders match: the automorphism group `Pauli n ≃ₗ[ZMod 2] Pauli n` and `AddAut (Pauli n)`
both compose as `f * g = g.trans f`, so `spAction` is a genuine homomorphism — `(t₁, g₁)(t₂, g₂) =
(t₁ + g₁ t₂, g₁ g₂)` is exactly affine composition. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates

variable {n : ℕ}

/-- The action of the symplectic group on the translation group `V = Pauli n`: a symplectic linear
equivalence acts as its underlying additive automorphism, transported across the `Multiplicative`
type tag. This is the structure map of the affine symplectic semidirect product. -/
noncomputable def spAction (n : ℕ) :
    spSubgroup n →* MulAut (Multiplicative (Pauli n)) where
  toFun g := (MulAutMultiplicative (Pauli n)).symm g.val.toAddEquiv
  map_one' := by
    have h1 : ((1 : spSubgroup n).val).toAddEquiv = (1 : AddAut (Pauli n)) :=
      AddEquiv.ext fun p => rfl
    rw [h1, map_one]
  map_mul' A B := by
    have hmul : ((A * B).val).toAddEquiv
        = (A.val).toAddEquiv * (B.val).toAddEquiv :=
      AddEquiv.ext fun p => rfl
    rw [hmul, map_mul]

/-- The **affine symplectic group** `V ⋊ Sp(V)` of the Pauli phase space — the right-hand side of
`Clₙ / U(1) ≅ V ⋊ Sp(V)`. Elements are pairs `(t, g)` of a translation `t ∈ V` and a symplectic
map `g ∈ Sp(V)`, multiplying as `(t₁, g₁)(t₂, g₂) = (t₁ + g₁ t₂, g₁ g₂)`. -/
abbrev affineSymplecticGroup (n : ℕ) : Type :=
  Multiplicative (Pauli n) ⋊[spAction n] spSubgroup n

/-- Projection of the affine symplectic group onto its linear part `Sp(V)`, forgetting the
translation. -/
noncomputable def affineToSp (n : ℕ) : affineSymplecticGroup n →* spSubgroup n :=
  SemidirectProduct.rightHom

theorem affineToSp_surjective (n : ℕ) : Function.Surjective (affineToSp n) :=
  SemidirectProduct.rightHom_surjective

/-- Inclusion of the translation group `V = Pauli n` into the affine symplectic group as the affine
shifts `(t, 1)`. Its range is exactly the kernel of the projection to `Sp(V)`. -/
noncomputable def translationIncl (n : ℕ) :
    Multiplicative (Pauli n) →* affineSymplecticGroup n :=
  SemidirectProduct.inl

theorem range_translationIncl_eq_ker_affineToSp (n : ℕ) :
    (translationIncl n).range = (affineToSp n).ker :=
  SemidirectProduct.range_inl_eq_ker_rightHom

/-! ## `Clₙ/U(1)`: the global-phase quotient and the descent of Φ

The left-hand side of `Clₙ/U(1) ≅ V ⋊ Sp(V)` is the Clifford group modulo the central subgroup of
global phases `U(1) = {α · id | α ∈ ℂˣ}`. We build it as `cliffordSubgroup n ⧸ phaseSubgroup n` and
descend the symplectic homomorphism `Φ = cliffordToSp` through it (global phases act trivially by
conjugation, so they lie in `ker Φ`). -/

/-- Conjugation by a global phase `α · id` is trivial: the scalar cancels against its inverse. -/
theorem conjEquiv_scaleEquiv_one (α : ℂˣ) (W : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    conjEquiv (scaleEquiv α 1) W = W := by
  apply LinearEquiv.ext
  intro ψ
  have hsymm : (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n).symm = 1 := inv_one
  simp only [conjEquiv_apply, scaleEquiv_apply, scaleEquiv_symm_apply, hsymm, LinearEquiv.coe_one,
    id_eq, map_smul]
  rw [smul_smul, Units.inv_mul, one_smul]

/-- A global phase `α · id` is a Clifford operator: it conjugates every Pauli to itself. -/
theorem isCliffordOperator_scaleEquiv_one (α : ℂˣ) :
    IsCliffordOperator (scaleEquiv α (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)) := by
  intro p
  rw [conjEquiv_scaleEquiv_one]
  exact isPhasedPauli_pauliEquiv p

/-- Global phases compose by multiplying the scalars. -/
theorem scaleEquiv_one_mul (α β : ℂˣ) :
    (scaleEquiv α (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)) * scaleEquiv β 1
      = scaleEquiv (α * β) 1 := by
  apply LinearEquiv.ext
  intro ψ
  simp only [LinearEquiv.mul_apply, scaleEquiv_apply, LinearEquiv.coe_one, id_eq, Units.val_mul,
    smul_smul]

/-- The global phases `U(1)` as a homomorphism into the Clifford group: `α ↦ α · id`. -/
noncomputable def phaseInclusion (n : ℕ) : ℂˣ →* cliffordSubgroup n where
  toFun α := ⟨scaleEquiv α 1, isCliffordOperator_scaleEquiv_one α⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro ψ
    simp only [scaleEquiv_apply, Units.val_one, LinearEquiv.coe_one, id_eq, one_smul,
      Subgroup.coe_one]
  map_mul' α β := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact (scaleEquiv_one_mul α β).symm

/-- Global phases are central in the Clifford group: `α · id` commutes with every Clifford `U`. -/
theorem phaseInclusion_central (α : ℂˣ) (U : cliffordSubgroup n) :
    phaseInclusion n α * U = U * phaseInclusion n α := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  apply LinearEquiv.ext
  intro ψ
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  change scaleEquiv α 1 (U.val ψ) = U.val (scaleEquiv α 1 ψ)
  simp only [scaleEquiv_apply, LinearEquiv.coe_one, id_eq, map_smul]

/-- The global-phase subgroup `U(1) ≤ Clₙ`, the central subgroup of scalar operators `α · id`. -/
noncomputable def phaseSubgroup (n : ℕ) : Subgroup (cliffordSubgroup n) :=
  (phaseInclusion n).range

instance phaseSubgroup_normal (n : ℕ) : (phaseSubgroup n).Normal := by
  constructor
  intro a ha g
  obtain ⟨α, rfl⟩ := ha
  have hc : g * phaseInclusion n α = phaseInclusion n α * g := (phaseInclusion_central α g).symm
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨α, rfl⟩

/-- Global phases lie in `ker Φ`: a scalar `α · id` induces the identity symplectic map. -/
theorem phaseSubgroup_le_ker (n : ℕ) :
    phaseSubgroup n ≤ (cliffordToSp (n := n)).ker := by
  intro a ha
  obtain ⟨α, rfl⟩ := ha
  rw [mem_cliffordToSp_ker_iff]
  refine ⟨α, 0, ?_⟩
  rw [show (phaseInclusion n α).val = scaleEquiv α 1 from rfl, scaleEquiv_toLinearMap,
    pauliOperator_zero]
  rfl

/-- **`Clₙ / U(1)`** — the Clifford group modulo global phase, the left-hand side of
`Clₙ / U(1) ≅ V ⋊ Sp(V)`. -/
abbrev cliffordModPhase (n : ℕ) : Type :=
  cliffordSubgroup n ⧸ phaseSubgroup n

/-- The symplectic homomorphism `Φ` descended to `Clₙ / U(1)` (global phases act trivially, so `Φ`
factors through the quotient). -/
noncomputable def cliffordModPhaseToSp (n : ℕ) : cliffordModPhase n →* spSubgroup n :=
  QuotientGroup.lift (phaseSubgroup n) (cliffordToSp (n := n)) (phaseSubgroup_le_ker n)

/-- The descended `Φ` is surjective — every symplectic automorphism is realized by a Clifford,
modulo phase (unconditional, from `surjective_cliffordToSp_of_gateLifts`). -/
theorem cliffordModPhaseToSp_surjective (n : ℕ) :
    Function.Surjective (cliffordModPhaseToSp n) := by
  intro T
  obtain ⟨U, hU⟩ :=
    surjective_cliffordToSp_of_gateLifts (cliffordGateGens_subset_range n) T
  refine ⟨QuotientGroup.mk U, ?_⟩
  simpa [cliffordModPhaseToSp] using hU

/-! ## The translation inclusion, the conjugation bridge, and the conditional iso -/

/-- Two Cliffords that agree up to a scalar `β · id` have the same class in `Clₙ / U(1)`: the scalar
is absorbed into the quotient by the global-phase subgroup. -/
theorem mk_eq_of_toLinearMap_smul {U V : cliffordSubgroup n} {β : ℂˣ}
    (h : U.val.toLinearMap = (β : ℂ) • V.val.toLinearMap) :
    (QuotientGroup.mk U : cliffordModPhase n) = QuotientGroup.mk V := by
  have hUV : U = phaseInclusion n β * V := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro ψ
    have hψ := LinearMap.congr_fun h ψ
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at hψ
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    change _ = scaleEquiv β 1 (V.val ψ)
    simp only [scaleEquiv_apply, LinearEquiv.coe_one, id_eq]
    exact hψ
  have hmem : phaseInclusion n β ∈ phaseSubgroup n := ⟨β, rfl⟩
  rw [hUV, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (phaseInclusion n β)).mpr hmem, one_mul]

/-- Variant of `mk_eq_of_toLinearMap_smul` with the scalar given as a nonzero complex number. -/
theorem mk_eq_of_toLinearMap_smul' {U V : cliffordSubgroup n} {c : ℂ} (hc : c ≠ 0)
    (h : U.val.toLinearMap = c • V.val.toLinearMap) :
    (QuotientGroup.mk U : cliffordModPhase n) = QuotientGroup.mk V :=
  mk_eq_of_toLinearMap_smul (β := Units.mk0 c hc) (by rwa [Units.val_mk0])

/-- A Pauli as an element of the Clifford group (the operator `pauliEquiv p`). -/
noncomputable def cliffordPauli (p : Pauli n) : cliffordSubgroup n :=
  ⟨pauliEquiv p, isCliffordOperator_pauliEquiv p⟩

/-- The zero Pauli is the identity Clifford. -/
theorem cliffordPauli_zero : cliffordPauli (0 : Pauli n) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro ψ
  simp only [cliffordPauli, LinearEquiv.coe_coe, pauliEquiv_apply, pauliOperator_zero,
    LinearMap.id_apply, Subgroup.coe_one, LinearEquiv.coe_one, id_eq]

/-- **The translation inclusion** `V = Pauli n → Clₙ / U(1)`, `p ↦ [pauliEquiv p]`. The Pauli
operators compose up to a sign `(-1)^…`, which dies in the quotient, so this is a homomorphism out
of the additive group `V` (presented multiplicatively). -/
noncomputable def pauliModPhase (n : ℕ) : Multiplicative (Pauli n) →* cliffordModPhase n where
  toFun m := QuotientGroup.mk (cliffordPauli (Multiplicative.toAdd m))
  map_one' := by
    change QuotientGroup.mk
      (cliffordPauli (Multiplicative.toAdd (1 : Multiplicative (Pauli n)))) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Pauli n)) = 0 from rfl, cliffordPauli_zero]
    exact (QuotientGroup.eq_one_iff 1).mpr (one_mem _)
  map_mul' a b := by
    set p := Multiplicative.toAdd a
    set q := Multiplicative.toAdd b
    change QuotientGroup.mk (cliffordPauli (p + q))
      = QuotientGroup.mk (cliffordPauli p) * QuotientGroup.mk (cliffordPauli q)
    rw [← QuotientGroup.mk_mul]
    refine (mk_eq_of_toLinearMap_smul'
      (U := cliffordPauli p * cliffordPauli q) (V := cliffordPauli (p + q))
      (c := (-1 : ℂ) ^ (zDotVal p q.X)) (pow_ne_zero _ (by norm_num)) ?_).symm
    change (cliffordPauli p * cliffordPauli q).val.toLinearMap
        = ((-1 : ℂ) ^ (zDotVal p q.X)) • (pauliEquiv (p + q)).toLinearMap
    rw [show (cliffordPauli p * cliffordPauli q).val.toLinearMap
          = ((pauliEquiv q).trans (pauliEquiv p)).toLinearMap from rfl,
      pauliEquiv_trans_toLinearMap, add_comm q p]

/-- The underlying linear map of `pauliEquiv p` is `pauliOperator p`. -/
theorem pauliEquiv_toLinearMap (p : Pauli n) :
    (pauliEquiv p).toLinearMap = pauliOperator p :=
  LinearMap.ext fun _ => rfl

/-- **The conjugation bridge, base case.** Conjugating the Pauli class `[pauliEquiv p]` by a
Clifford class `[U]` in `Clₙ / U(1)` realizes the symplectic action `Φ(U)` on `p`: the conjugation
phase dies in the quotient. This is the compatibility that makes the affine symplectic semidirect
product map into `Clₙ / U(1)`. -/
theorem mk_conj_cliffordPauli (U : cliffordSubgroup n) (p : Pauli n) :
    (QuotientGroup.mk U : cliffordModPhase n) * pauliModPhase n (Multiplicative.ofAdd p)
        * (QuotientGroup.mk U)⁻¹
      = pauliModPhase n (Multiplicative.ofAdd ((cliffordToSp U).val p)) := by
  rw [show pauliModPhase n (Multiplicative.ofAdd p) = QuotientGroup.mk (cliffordPauli p) from rfl,
    show pauliModPhase n (Multiplicative.ofAdd ((cliffordToSp U).val p))
      = QuotientGroup.mk (cliffordPauli ((cliffordToSp U).val p)) from rfl,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  refine mk_eq_of_toLinearMap_smul (β := cliffordToSymplecticPhase U.2 p) ?_
  have hconj : (U * cliffordPauli p * U⁻¹).val = conjEquiv U.val (pauliEquiv p) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hpauli : (pauliEquiv p).toLinearMap = ((1 : ℂˣ) : ℂ) • pauliOperator p := by
    rw [pauliEquiv_toLinearMap, Units.val_one, one_smul]
  rw [hconj, conjEquiv_smul_pauliOperator U.2 hpauli, one_mul]
  simp only [cliffordPauli, pauliEquiv_toLinearMap]
  congr 1

/-- **The conjugation bridge.** For any class `x ∈ Clₙ / U(1)`, conjugating a Pauli translation by
`x` acts as the symplectic image `Φ(x)` of `x`. -/
theorem conjBridge (x : cliffordModPhase n) (p : Pauli n) :
    x * pauliModPhase n (Multiplicative.ofAdd p) * x⁻¹
      = pauliModPhase n (Multiplicative.ofAdd ((cliffordModPhaseToSp n x).val p)) := by
  refine QuotientGroup.induction_on x (fun U => ?_)
  have hmk : cliffordModPhaseToSp n (QuotientGroup.mk U) = cliffordToSp U := rfl
  rw [hmk, mk_conj_cliffordPauli U p]

/-! ### The splitting and the conditional isomorphism -/

/-- The symplectic action on a translation: `g` acts as its underlying linear map. -/
@[simp] theorem spAction_apply (g : spSubgroup n) (m : Multiplicative (Pauli n)) :
    spAction n g m = Multiplicative.ofAdd (g.val (Multiplicative.toAdd m)) := rfl

/-- Pauli translations lie in the kernel of the descended `Φ`: they act trivially by conjugation. -/
theorem cliffordModPhaseToSp_pauliModPhase (m : Multiplicative (Pauli n)) :
    cliffordModPhaseToSp n (pauliModPhase n m) = 1 := by
  apply Subtype.ext
  exact cliffordToSymplectic_pauliEquiv (Multiplicative.toAdd m)

/-- A Clifford in `ker Φ` (a phased Pauli) is a Pauli translation in `Clₙ / U(1)`: the kernel of the
descended `Φ` is exactly the image of the translations. -/
theorem mk_mem_range_pauliModPhase (U : cliffordSubgroup n)
    (hU : U ∈ (cliffordToSp (n := n)).ker) :
    ∃ m, pauliModPhase n m = QuotientGroup.mk U := by
  rw [mem_cliffordToSp_ker_iff] at hU
  obtain ⟨α, r, hUval⟩ := hU
  refine ⟨Multiplicative.ofAdd r, (mk_eq_of_toLinearMap_smul (β := α) ?_).symm⟩
  rw [show (cliffordPauli (Multiplicative.toAdd (Multiplicative.ofAdd r))).val.toLinearMap
        = pauliOperator r from pauliEquiv_toLinearMap r]
  exact hUval

/-- The translation inclusion is injective at the identity: a trivial Pauli class forces `m = 1`. -/
theorem pauliModPhase_eq_one {m : Multiplicative (Pauli n)} (h : pauliModPhase n m = 1) :
    m = 1 := by
  obtain ⟨α, hα⟩ := (QuotientGroup.eq_one_iff _).mp h
  have hval : (scaleEquiv α 1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
      = pauliEquiv (Multiplicative.toAdd m) := congrArg Subtype.val hα
  have hone : pauliOperator (0 : Pauli n)
      = (1 : QubitSpace n ≃ₗ[ℂ] QubitSpace n).toLinearMap := by
    rw [pauliOperator_zero]; rfl
  have hlin : (α : ℂ) • pauliOperator (0 : Pauli n)
      = ((1 : ℂˣ) : ℂ) • pauliOperator (Multiplicative.toAdd m) := by
    have h2 := congrArg LinearEquiv.toLinearMap hval
    rw [scaleEquiv_toLinearMap, pauliEquiv_toLinearMap] at h2
    rw [hone, h2, Units.val_one, one_smul]
  have hrig := (phasedPauli_rigid hlin).1
  exact Multiplicative.toAdd.injective (hrig.symm.trans rfl)

/-- **The splitting `Prop`.** A group-hom section of the descended `Φ : Clₙ/U(1) → Sp(V)` —
equivalently, that the extension `1 → V → Clₙ/U(1) → Sp(V) → 1` splits, i.e. `Clₙ/U(1) ≅ V ⋊ Sp(V)`.
**This holds for n ≤ 1 and FAILS for n ≥ 2**: the extension is non-split for n ≥ 2 (Galindo,
arXiv:2603.24743, 2026; Mastel, arXiv:2307.05810, 2023 — the Clifford group is not a semidirect
product of Pauli and symplectic; the n = 1 case `S₄ = V₄ ⋊ S₃` is the exception). So this is NOT a
proof target; `cliffordAffineEquiv` below is the conditional statement, realized only at
n ≤ 1. -/
def CliffordSectionExists (n : ℕ) : Prop :=
  ∃ s : spSubgroup n →* cliffordModPhase n, ∀ g, cliffordModPhaseToSp n (s g) = g

/-- **Conditional on the splitting: `Clₙ / U(1) ≅ V ⋊ Sp(V)`.** Given a section of
`Φ : Clₙ/U(1) → Sp(V)`, the affine symplectic group is isomorphic to `Clₙ/U(1)`: `V` maps to the
Pauli classes (`pauliModPhase`), `Sp(V)` via the section, the semidirect conjugation matching
`conjBridge`; bijectivity uses `ker Φ = U(1)·Pauli` (`mem_cliffordToSp_ker_iff`). The hypothesis
`CliffordSectionExists n` holds only for n ≤ 1 (the extension is non-split for n ≥ 2), so this is a
correct conditional theorem, realized only at n ≤ 1. -/
noncomputable def cliffordAffineEquiv (n : ℕ) (hsplit : CliffordSectionExists n) :
    affineSymplecticGroup n ≃* cliffordModPhase n := by
  let s := hsplit.choose
  have hs : ∀ g, cliffordModPhaseToSp n (s g) = g := hsplit.choose_spec
  have hcompat : ∀ g, (pauliModPhase n).comp (spAction n g).toMonoidHom
      = (MulAut.conj (s g)).toMonoidHom.comp (pauliModPhase n) := by
    intro g
    refine MonoidHom.ext (fun m => ?_)
    obtain ⟨p, rfl⟩ : ∃ p, (Multiplicative.ofAdd p : Multiplicative (Pauli n)) = m :=
      ⟨Multiplicative.toAdd m, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, spAction_apply]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd p) = p from rfl, conjBridge (s g) p, hs g]
  refine MulEquiv.ofBijective (SemidirectProduct.lift (pauliModPhase n) s hcompat) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : pauliModPhase n a.left * s a.right = 1 := ha
    have hg : a.right = 1 := by
      have hc := congrArg (cliffordModPhaseToSp n) ha'
      rw [map_mul, cliffordModPhaseToSp_pauliModPhase, hs a.right, one_mul, map_one] at hc
      exact hc
    rw [hg, map_one, mul_one] at ha'
    exact SemidirectProduct.ext (pauliModPhase_eq_one ha') hg
  · intro x
    obtain ⟨U, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨Vg, hVg⟩ := QuotientGroup.mk_surjective (s (cliffordToSp U))
    have hVgsp : cliffordToSp Vg = cliffordToSp U := by
      have h1 : cliffordModPhaseToSp n (QuotientGroup.mk Vg) = cliffordToSp U := by
        rw [hVg]; exact hs (cliffordToSp U)
      exact h1
    have hW : (U * Vg⁻¹) ∈ (cliffordToSp (n := n)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hVgsp, mul_inv_cancel]
    obtain ⟨m, hm⟩ := mk_mem_range_pauliModPhase (U * Vg⁻¹) hW
    refine ⟨⟨m, cliffordToSp U⟩, ?_⟩
    change pauliModPhase n m * s (cliffordToSp U) = QuotientGroup.mk U
    rw [hm, ← hVg, ← QuotientGroup.mk_mul, mul_assoc, inv_mul_cancel, mul_one]

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Metaplectic

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The projective Weil representation

`Metaplectic.lean` built the linear representation on the *cover*: `weilMp : Mp →* GL(V)`, with
`mpProj : Mp →* Sp` surjective and central-scalar kernel. This file descends it to `Sp` itself:

* **`PGL V`** — `GL(V)` modulo the scalar subgroup (the image of `ℂˣ`, central, hence normal);
* **`weilProj : Sp →* PGL(V)`** — **the projective Weil representation**. Obtained by descent: the
  composite `Mp → GL → PGL` kills `ker mpProj` (its elements are scalars, by Schur), and `mpProj` is
  surjective, so the composite factors through `Sp`;
* **`weilProj_eq_of_intertwines`** — the characterization that makes it usable: `weilProj T` is the
  class of *any* Weil operator for `T`. This is the statement "the Weil representation is well
  defined projectively", as a `MonoidHom`.

Unconditional: no cocycle triviality, no splitting. With `Metaplectic.lean` this completes the
citation-free theory — linear on `Mp`, projective on `Sp`, and `1 → ℂˣ → Mp → Sp → 1` exact.
-/

namespace ECCLib.Metaplectic

open ECCLib.Heisenberg ECCLib.Siegel

/-! ## `PGL`: the projective linear group -/

section PGL

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The scalar units of `End ℂ V`, as the image of `ℂˣ` under the algebra map. -/
noncomputable def scalarHom : ℂˣ →* (Module.End ℂ V)ˣ :=
  Units.map (algebraMap ℂ (Module.End ℂ V)).toMonoidHom

@[simp] theorem scalarHom_coe (c : ℂˣ) :
    ((scalarHom V c : (Module.End ℂ V)ˣ) : Module.End ℂ V) = (c : ℂ) • LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp [scalarHom]

/-- The scalar subgroup of `GL(V)`. -/
noncomputable def scalarSubgroup : Subgroup (Module.End ℂ V)ˣ := (scalarHom V).range

theorem mem_scalarSubgroup_iff {u : (Module.End ℂ V)ˣ} :
    u ∈ scalarSubgroup V ↔ ∃ c : ℂˣ, scalarHom V c = u := Iff.rfl

/-- Scalars are central, so the scalar subgroup is normal. -/
instance : (scalarSubgroup V).Normal := by
  constructor
  rintro n hn g
  obtain ⟨c, rfl⟩ := hn
  refine ⟨c, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, scalarHom_coe, ← Module.End.one_eq_id,
    mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

/-- **`PGL(V)`** — the projective linear group, `GL(V)` modulo scalars. -/
abbrev PGL := (Module.End ℂ V)ˣ ⧸ scalarSubgroup V

/-- The quotient map `GL(V) → PGL(V)`. -/
noncomputable def toPGL : (Module.End ℂ V)ˣ →* PGL V := QuotientGroup.mk' _

end PGL

/-! ## The descent -/

section Projective

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ}

/-- A unit that is a scalar multiple of the identity lies in the scalar subgroup: the scalar is
automatically nonzero, since a unit cannot be `0`. -/
theorem mem_scalarSubgroup_of_eq_smul {u : (Module.End ℂ ((ι → F) → ℂ))ˣ} {c : ℂ}
    (h : (u : Module.End ℂ ((ι → F) → ℂ)) = c • LinearMap.id) :
    u ∈ scalarSubgroup ((ι → F) → ℂ) := by
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at h
    have h1 : (1 : Module.End ℂ ((ι → F) → ℂ)) = 0 := by
      rw [← u.mul_inv, h, zero_mul]
    exact one_ne_zero h1
  exact ⟨Units.mk0 c hc, Units.ext (by rw [scalarHom_coe]; exact h.symm)⟩

/-- **Two Weil operators for the same symplectic map have the same class in `PGL`.** This is
`weil_operator_unique` (Schur) in projective form, and it is what makes the projective
representation well defined. -/
theorem toPGL_eq_of_intertwines (hψ : ψ ≠ 1) {T : W F ι ≃ₗ[F] W F ι}
    {U U' : (Module.End ℂ ((ι → F) → ℂ))ˣ}
    (hU : Intertwines h2 ψ T U) (hU' : Intertwines h2 ψ T U') :
    toPGL ((ι → F) → ℂ) U = toPGL ((ι → F) → ℂ) U' := by
  obtain ⟨c, hc⟩ := weil_operator_unique h2 hψ U (U' : Module.End ℂ ((ι → F) → ℂ)) hU hU'
  symm
  unfold toPGL
  simp only [QuotientGroup.mk'_apply]
  refine QuotientGroup.eq_iff_div_mem.mpr ?_
  refine mem_scalarSubgroup_of_eq_smul (c := c) ?_
  rw [div_eq_mul_inv, Units.val_mul, hc, smul_mul_assoc, Units.mul_inv,
    ← Module.End.one_eq_id]

/-- A chosen Weil operator for each symplectic map (existence at every rank). -/
noncomputable def weilOp (hψ : ψ ≠ 1) (T : ↥(Sp F ι)) : (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  Classical.choose (hasWeilOperator_of_isSymplectic_svn h2 hψ (isSymplectic_heisOfSp T.2))

theorem weilOp_intertwines (hψ : ψ ≠ 1) (T : ↥(Sp F ι)) :
    Intertwines h2 ψ (T : W F ι ≃ₗ[F] W F ι) (weilOp h2 hψ T) :=
  Classical.choose_spec (hasWeilOperator_of_isSymplectic_svn h2 hψ (isSymplectic_heisOfSp T.2))

/-- **The projective Weil representation** `Sp →* PGL(V)`. The choice of operator is immaterial —
`toPGL_eq_of_intertwines` — so the class is well defined, and multiplicativity is closure of Weil
operators under composition. -/
noncomputable def weilProj (hψ : ψ ≠ 1) : ↥(Sp F ι) →* PGL ((ι → F) → ℂ) where
  toFun T := toPGL ((ι → F) → ℂ) (weilOp h2 hψ T)
  map_one' := by
    have hone : Intertwines h2 ψ ((1 : ↥(Sp F ι)) : W F ι ≃ₗ[F] W F ι) 1 := (Mp h2 ψ).one_mem
    rw [toPGL_eq_of_intertwines h2 hψ (weilOp_intertwines h2 hψ 1) hone]
    exact map_one _
  map_mul' T T' := by
    have hT : ((T, weilOp h2 hψ T) : ↥(Sp F ι) × (Module.End ℂ ((ι → F) → ℂ))ˣ) ∈ Mp h2 ψ :=
      weilOp_intertwines h2 hψ T
    have hT' : ((T', weilOp h2 hψ T') : ↥(Sp F ι) × (Module.End ℂ ((ι → F) → ℂ))ˣ) ∈ Mp h2 ψ :=
      weilOp_intertwines h2 hψ T'
    have hprod : Intertwines h2 ψ ((T * T' : ↥(Sp F ι)) : W F ι ≃ₗ[F] W F ι)
        (weilOp h2 hψ T * weilOp h2 hψ T') := (Mp h2 ψ).mul_mem hT hT'
    rw [toPGL_eq_of_intertwines h2 hψ (weilOp_intertwines h2 hψ (T * T')) hprod]
    exact map_mul _ _ _

/-- **The characterization**: `weilProj T` is the class of *any* Weil operator for `T`. This is the
usable form — "the Weil representation is well defined projectively", now as a homomorphism. -/
theorem weilProj_eq_of_intertwines (hψ : ψ ≠ 1) {T : ↥(Sp F ι)}
    {U : (Module.End ℂ ((ι → F) → ℂ))ˣ}
    (hU : Intertwines h2 ψ (T : W F ι ≃ₗ[F] W F ι) U) :
    weilProj h2 hψ T = toPGL ((ι → F) → ℂ) U :=
  toPGL_eq_of_intertwines h2 hψ (weilOp_intertwines h2 hψ T) hU

/-- **Consistency**: descending along the covering agrees with projecting the metaplectic
representation — `weilProj ∘ mpProj = toPGL ∘ weilMp`. -/
theorem weilProj_mpProj (hψ : ψ ≠ 1) (m : ↥(Mp (ι := ι) h2 ψ)) :
    weilProj h2 hψ (mpProj h2 ψ m) = toPGL ((ι → F) → ℂ) (weilMp h2 ψ m) :=
  weilProj_eq_of_intertwines h2 hψ m.2

end Projective

end ECCLib.Metaplectic

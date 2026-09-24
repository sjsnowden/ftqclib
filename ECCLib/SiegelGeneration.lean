/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.SymplecticGeneration
import ECCLib.WeilGeneration
import Mathlib.Tactic.Module

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# `Sp(2n, 𝔽_q) = ⟨shears, w⟩` — the Siegel generators

The Weil representation's explicit route (`WeilGeneration.lean`) writes every operator as a word in
the chirps (shears) and the DFT (the Weyl element `w`). That route was complete at rank one and
waited on the generation statement `Sp(2n,𝔽_q) = ⟨shears, w⟩` beyond it. This file proves it, at
every rank.

The engine is `SymplecticGeneration.transvections_generate_sp` (transvections generate `Sp`, any
field). It remains to place every transvection inside `⟨shears, w⟩`:

* a **pure-momentum** transvection `t_{(0,b),c}` *is* a momentum shear (rank-one `S = c·b⊗b`);
* a **pure-position** transvection `t_{(a,0),c}` is the `w`-conjugate of a momentum shear
  (`w · shear(S) · w⁻¹` is the position shear);
* a **mixed** transvection `t_{(a,b),c}` with `a ≠ 0` conjugates to a pure-position one by a momentum
  shear `S₀` chosen so that `S₀ a = b` — and such a symmetric `S₀` exists because the map
  `S ↦ S a` from symmetric maps to vectors is onto when `a ≠ 0` (the one genuinely new lemma,
  `exists_symLin_apply`).

The symplectic form is the position/momentum split `ω((p,m),(p',m')) = ⟨m',p⟩ − ⟨m,p'⟩` on
`W = (ι→F)×(ι→F)`, matching `Heis.symp`. Mathlib-only, so it lifts with the rest of `ECCLib`.
-/

namespace ECCLib.Siegel

open ECCLib.Heisenberg (pairing)

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Heisenberg vector space: positions × momenta. -/
abbrev W (F : Type*) (ι : Type*) := (ι → F) × (ι → F)

/-- Scalar out of the left slot of `pairing`. -/
theorem pairing_smul_left (s : F) (b y : ι → F) : pairing (s • b) y = s * pairing b y := by
  have h : (s • b) = (fun i => s * b i) := by funext i; simp
  rw [h, ECCLib.Heisenberg.pairing_mul_left]

/-- Scalar out of the right slot of `pairing`. -/
theorem pairing_smul_right (s : F) (b y : ι → F) : pairing b (s • y) = s * pairing b y := by
  have h : (s • y) = (fun i => s * y i) := by funext i; simp
  rw [h, ECCLib.Heisenberg.pairing_mul_right]

/-- `pairing b` as a bundled linear functional. -/
def pairingLM (b : ι → F) : (ι → F) →ₗ[F] F := ∑ i, (b i) • (LinearMap.proj i : (ι → F) →ₗ[F] F)

@[simp] theorem pairingLM_apply (b x : ι → F) : pairingLM b x = pairing b x := by
  simp only [pairingLM, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rfl

/-! ### The symplectic form -/

/-- `ω((p,m),(p',m')) = ⟨m',p⟩ − ⟨m,p'⟩`. -/
def omega : W F ι →ₗ[F] W F ι →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => pairing y.2 x.1 - pairing x.2 y.1)
    (fun x₁ x₂ y => by
      simp only [Prod.fst_add, Prod.snd_add]
      rw [ECCLib.Heisenberg.pairing_add_right, ECCLib.Heisenberg.pairing_add_left]
      ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd]
      rw [pairing_smul_right, pairing_smul_left, smul_eq_mul, mul_sub])
    (fun x y₁ y₂ => by
      simp only [Prod.fst_add, Prod.snd_add]
      rw [ECCLib.Heisenberg.pairing_add_left, ECCLib.Heisenberg.pairing_add_right]
      ring)
    (fun x c y => by
      simp only [Prod.smul_fst, Prod.smul_snd]
      rw [pairing_smul_left, pairing_smul_right, smul_eq_mul, mul_sub])

@[simp] theorem omega_apply (x y : W F ι) : omega x y = pairing y.2 x.1 - pairing x.2 y.1 := rfl

theorem omega_isAlt : (omega (F := F) (ι := ι)).IsAlt := fun x => by
  simp only [omega_apply, sub_self]

theorem omega_nondegenerate : (omega (F := F) (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx
    refine Prod.ext ?_ ?_
    · refine ECCLib.Heisenberg.eq_zero_of_pairing_left (F := F) x.1 fun p => ?_
      have h := hx (0, p)
      simp only [omega_apply, ECCLib.Heisenberg.pairing_zero_right, sub_zero] at h
      rw [ECCLib.Heisenberg.pairing_symm]; exact h
    · refine ECCLib.Heisenberg.eq_zero_of_pairing_left (F := F) x.2 fun p => ?_
      have h := hx (p, 0)
      simpa only [omega_apply, ECCLib.Heisenberg.pairing_zero_left, zero_sub,
        neg_eq_zero] using h
  · intro y hy
    refine Prod.ext ?_ ?_
    · refine ECCLib.Heisenberg.eq_zero_of_pairing_left (F := F) y.1 fun p => ?_
      have h := hy (0, p)
      simp only [omega_apply, ECCLib.Heisenberg.pairing_zero_right, zero_sub,
        neg_eq_zero] at h
      rw [ECCLib.Heisenberg.pairing_symm]; exact h
    · refine ECCLib.Heisenberg.eq_zero_of_pairing_left (F := F) y.2 fun p => ?_
      have h := hy (p, 0)
      simpa only [omega_apply, ECCLib.Heisenberg.pairing_zero_left, sub_zero] using h

/-! ### Symmetric linear maps and the two shear families -/

/-- A linear map self-adjoint for the pairing. -/
def IsSymLin (S : (ι → F) →ₗ[F] (ι → F)) : Prop := ∀ x y, pairing (S x) y = pairing (S y) x

/-- The momentum shear `(p,m) ↦ (p, m − S p)` as a linear automorphism (inverse: `S ↦ −S`). -/
def momShear (S : (ι → F) →ₗ[F] (ι → F)) : W F ι ≃ₗ[F] W F ι :=
  LinearEquiv.ofLinear
    (LinearMap.prod (LinearMap.fst F _ _) (LinearMap.snd F _ _ - S ∘ₗ LinearMap.fst F _ _))
    (LinearMap.prod (LinearMap.fst F _ _) (LinearMap.snd F _ _ + S ∘ₗ LinearMap.fst F _ _))
    (by ext x <;> simp) (by ext x <;> simp)

@[simp] theorem momShear_apply (S : (ι → F) →ₗ[F] (ι → F)) (x : W F ι) :
    momShear S x = (x.1, x.2 - S x.1) := rfl

/-- The Weyl element `(p,m) ↦ (m, −p)` (inverse: `(p,m) ↦ (−m, p)`).

*Disambiguation*: this is the Weyl element as a linear equivalence of the vector space `W`;
`Heis.fourierMap` is the same element on the Heisenberg group, `fourierOp` is its Weil operator
(the DFT), and `Heisenberg.weyl` is the unrelated ½-normalized Weyl *operator* (see that docstring
for the four-object glossary). -/
def weyl : W F ι ≃ₗ[F] W F ι :=
  LinearEquiv.ofLinear
    (LinearMap.prod (LinearMap.snd F _ _) (-LinearMap.fst F _ _))
    (LinearMap.prod (-LinearMap.snd F _ _) (LinearMap.fst F _ _))
    (by ext x <;> simp) (by ext x <;> simp)

@[simp] theorem weyl_apply (x : W F ι) : weyl x = (x.2, -x.1) := rfl

@[simp] theorem weyl_symm_apply (x : W F ι) : weyl.symm x = (-x.2, x.1) := rfl

theorem momShear_isSymplectic {S : (ι → F) →ₗ[F] (ι → F)} (hS : IsSymLin S) :
    SpGen.IsSymplecticEquiv omega (momShear S) := by
  intro x y
  simp only [omega_apply, momShear_apply]
  rw [ECCLib.Heisenberg.pairing_sub_left, ECCLib.Heisenberg.pairing_sub_left, hS y.1 x.1]
  ring

theorem weyl_isSymplectic : SpGen.IsSymplecticEquiv (omega (F := F) (ι := ι)) weyl := by
  intro x y
  simp only [omega_apply, weyl_apply, ECCLib.Heisenberg.pairing_neg_left]
  rw [ECCLib.Heisenberg.pairing_symm y.2 x.1, ECCLib.Heisenberg.pairing_symm y.1 x.2]
  ring

/-! ### The generating set -/

/-- The Siegel generators: all momentum shears, plus `w`. -/
def gens : Set (W F ι ≃ₗ[F] W F ι) :=
  {g | (∃ S, IsSymLin S ∧ g = momShear S) ∨ g = weyl}

theorem momShear_mem_closure {S : (ι → F) →ₗ[F] (ι → F)} (hS : IsSymLin S) :
    momShear S ∈ Subgroup.closure (gens (F := F) (ι := ι)) :=
  Subgroup.subset_closure (Or.inl ⟨S, hS, rfl⟩)

theorem weyl_mem_closure : weyl ∈ Subgroup.closure (gens (F := F) (ι := ι)) :=
  Subgroup.subset_closure (Or.inr rfl)

/-- Every generator is an isometry, so the whole generated subgroup consists of isometries. -/
theorem isSymplectic_of_mem_closure {g : W F ι ≃ₗ[F] W F ι}
    (hg : g ∈ Subgroup.closure (gens (F := F) (ι := ι))) :
    SpGen.IsSymplecticEquiv (omega (F := F) (ι := ι)) g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨S, hS, rfl⟩ | rfl
    · exact momShear_isSymplectic hS
    · exact weyl_isSymplectic
  | one => exact SpGen.isSymplecticEquiv_one (omega (F := F) (ι := ι))
  | mul a b _ _ iha ihb => exact SpGen.isSymplecticEquiv_mul (omega (F := F) (ι := ι)) iha ihb
  | inv a _ iha => exact SpGen.isSymplecticEquiv_inv (omega (F := F) (ι := ι)) iha

/-! ### The rank-one symmetric map `c·(b ⊗ b)` -/

/-- The symmetric rank-one map `x ↦ (c · ⟨b,x⟩) • b`. -/
def dyadShear (b : ι → F) (c : F) : (ι → F) →ₗ[F] (ι → F) :=
  LinearMap.smulRight (c • pairingLM b) b

@[simp] theorem dyadShear_apply (b : ι → F) (c : F) (x : ι → F) :
    dyadShear b c x = (c * pairing b x) • b := by
  simp only [dyadShear, LinearMap.smulRight_apply, LinearMap.smul_apply, pairingLM_apply,
    smul_eq_mul]

theorem dyadShear_isSymLin (b : ι → F) (c : F) : IsSymLin (dyadShear b c) := by
  intro x y
  simp only [dyadShear_apply]
  rw [pairing_smul_left, pairing_smul_left, ECCLib.Heisenberg.pairing_symm b x,
    ECCLib.Heisenberg.pairing_symm b y]
  ring

/-! ### Transvections as words in the generators -/

/-- A **pure-momentum transvection is a momentum shear**. -/
theorem transvection_pure_mom (b : ι → F) (c : F) :
    SpGen.transvectionEquiv omega omega_isAlt ((0 : ι → F), b) c = momShear (dyadShear b c) := by
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext fun u => ?_)
  have hom : omega ((0 : ι → F), b) u = - pairing b u.1 := by
    simp only [omega_apply, ECCLib.Heisenberg.pairing_zero_right, zero_sub]
  simp only [LinearEquiv.coe_toLinearMap, SpGen.transvectionEquiv_apply, hom, momShear_apply,
    dyadShear_apply]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_add, Prod.snd_neg, Prod.smul_snd, mul_neg, neg_smul]
    abel

/-- A **pure-position transvection is the `w`-conjugate of a momentum shear**. -/
theorem transvection_pure_pos (a : ι → F) (c : F) :
    SpGen.transvectionEquiv omega omega_isAlt (a, (0 : ι → F)) c
      = weyl * momShear (dyadShear a c) * weyl⁻¹ := by
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext fun u => ?_)
  have hom : omega (a, (0 : ι → F)) u = pairing a u.2 := by
    simp only [omega_apply, ECCLib.Heisenberg.pairing_zero_left, sub_zero,
      ECCLib.Heisenberg.pairing_symm u.2 a]
  simp only [LinearEquiv.coe_toLinearMap, SpGen.transvectionEquiv_apply, hom, LinearEquiv.mul_apply,
    LinearEquiv.coe_inv, weyl_symm_apply, momShear_apply, weyl_apply, dyadShear_apply, neg_neg]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, ECCLib.Heisenberg.pairing_neg_right]
    module
  · simp

/-! ### A symmetric map with prescribed value — the one new lemma -/

/-- `pairing` against a coordinate vector reads off that coordinate. -/
theorem pairing_single_left (i : ι) (y : ι → F) : pairing (Pi.single i (1 : F)) y = y i := by
  unfold pairing
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- The explicit symmetric map `S = ai⁻¹·(e_i⊗b + b⊗e_i) − (d·ai⁻²)·(e_i⊗e_i)`, self-adjoint for
*any* scalars, and (below) sending `a ↦ b` when `i` witnesses `a i ≠ 0`, `ai = a i`, `d = ⟨a,b⟩`. -/
def presShear (i : ι) (ai d : F) (b : ι → F) : (ι → F) →ₗ[F] (ι → F) :=
  ai⁻¹ • ((LinearMap.proj i).smulRight b + (pairingLM b).smulRight (Pi.single i (1 : F)))
    - (d * ai⁻¹ ^ 2) • (LinearMap.proj i).smulRight (Pi.single i (1 : F))

@[simp] theorem presShear_apply (i : ι) (ai d : F) (b x : ι → F) :
    presShear i ai d b x
      = ai⁻¹ • ((x i) • b + (pairing b x) • Pi.single i (1 : F))
        - (d * ai⁻¹ ^ 2) • ((x i) • Pi.single i (1 : F)) := by
  simp only [presShear, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, pairingLM_apply]

theorem presShear_isSymLin (i : ι) (ai d : F) (b : ι → F) : IsSymLin (presShear i ai d b) := by
  intro x y
  simp only [presShear_apply, ECCLib.Heisenberg.pairing_sub_left, pairing_smul_left,
    ECCLib.Heisenberg.pairing_add_left, pairing_single_left]
  rw [ECCLib.Heisenberg.pairing_symm b x, ECCLib.Heisenberg.pairing_symm b y]
  ring

/-- **The existence lemma**: when `a ≠ 0`, a symmetric linear map takes any prescribed value on `a`.
This is what lets a mixed transvection be conjugated to a pure-position one. -/
theorem exists_symLin_apply {a : ι → F} (ha : a ≠ 0) (b : ι → F) :
    ∃ S : (ι → F) →ₗ[F] (ι → F), IsSymLin S ∧ S a = b := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  simp only [Pi.zero_apply] at hi
  refine ⟨presShear i (a i) (pairing a b) b, presShear_isSymLin _ _ _ _, ?_⟩
  rw [presShear_apply, ECCLib.Heisenberg.pairing_symm b a]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with hj <;> field_simp [hi] <;> ring

/-! ### Every transvection lies in `⟨shears, w⟩`, so `⟨shears, w⟩ = Sp` -/

/-- **Every transvection is a word in the Siegel generators.** Pure-momentum: a shear.
Pure-position: a `w`-conjugate. Mixed (`v.1 ≠ 0`): a shear-conjugate of a pure-position one, the
conjugator chosen by `exists_symLin_apply`. -/
theorem transvection_mem_closure (v : W F ι) (c : F) :
    SpGen.transvectionEquiv omega omega_isAlt v c ∈ Subgroup.closure (gens (F := F) (ι := ι)) := by
  by_cases ha : v.1 = 0
  · have hv : v = ((0 : ι → F), v.2) := Prod.ext ha rfl
    rw [hv, transvection_pure_mom]
    exact momShear_mem_closure (dyadShear_isSymLin _ _)
  · obtain ⟨S₀, hS₀sym, hS₀⟩ := exists_symLin_apply ha v.2
    have hmov : momShear S₀ v = (v.1, (0 : ι → F)) := by
      rw [momShear_apply, hS₀, sub_self]
    have hconj := SpGen.transvectionEquiv_conj omega omega_isAlt (momShear_isSymplectic hS₀sym) v c
    rw [hmov] at hconj
    have ht : SpGen.transvectionEquiv omega omega_isAlt v c
        = (momShear S₀)⁻¹
            * SpGen.transvectionEquiv omega omega_isAlt (v.1, (0 : ι → F)) c * momShear S₀ := by
      rw [← hconj]; group
    rw [ht, transvection_pure_pos]
    refine mul_mem (mul_mem (inv_mem (momShear_mem_closure hS₀sym)) ?_)
      (momShear_mem_closure hS₀sym)
    exact mul_mem (mul_mem weyl_mem_closure (momShear_mem_closure (dyadShear_isSymLin _ _)))
      (inv_mem weyl_mem_closure)

/-- **`Sp(2n,𝔽_q) = ⟨shears, w⟩`** — the named gap, closed at every rank. An automorphism preserves
the symplectic form if and only if it is a word in the momentum shears and the Weyl element. Forward:
transvections generate (`transvections_generate_sp`) and each lies in `⟨shears, w⟩`
(`transvection_mem_closure`). Backward: every generator is an isometry. -/
theorem isSymplectic_iff_mem_closure {T : W F ι ≃ₗ[F] W F ι} :
    SpGen.IsSymplecticEquiv (omega (F := F) (ι := ι)) T
      ↔ T ∈ Subgroup.closure (gens (F := F) (ι := ι)) := by
  refine ⟨fun hT => ?_, isSymplectic_of_mem_closure⟩
  have hgen := SpGen.transvections_generate_sp (omega (F := F) (ι := ι)) omega_nondegenerate omega_isAlt hT
  have hsub : Subgroup.closure (SpGen.transvectionGens omega omega_isAlt)
      ≤ Subgroup.closure (gens (F := F) (ι := ι)) := by
    rw [Subgroup.closure_le]
    rintro g ⟨v, c, rfl⟩
    exact transvection_mem_closure v c
  exact hsub hgen

end ECCLib.Siegel

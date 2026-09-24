/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.MonomialGroup
import Mathlib.InformationTheory.Hamming

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The tame Weil operators of the monomial group

On the monomial group the Weil representation is *plain substitution* — no chirp, no Gauss sum, no
projective ambiguity. This file computes the operators and proves they are Weil operators:

* `permOp σ : f ↦ f(σ⁻¹·)` and `dilOp d : f ↦ f(d⁻¹·)` — substitution operators on the Schrödinger
  model, with composition laws and two-sided units (`permUnit`, `dilUnit`);
* `hasWeilOperator_permMap` / `hasWeilOperator_dilMap` — the intertwining relations, proved directly
  against `schrodinger` exactly as `hasWeilOperator_shear` was: the `ψ(½⟨m,p⟩)` cocycle scalar is
  *invariant* under the monomial substitution (`⟨d⁻¹m, dp⟩ = ⟨m,p⟩`), which is why no multiplier
  appears. These witnesses are *explicit*, unlike the existence already known from
  `inWeilGroup_of_isSymplectic`;
* **weight compatibility** (step 2): the operators permute the delta basis (`permOp_delta`,
  `dilOp_delta`) and the underlying monomial action preserves the Hamming weight
  (`hammingNorm_perm`, `hammingNorm_dil` — the pointwise-diagonal statement, alongside Mathlib's
  scalar `hammingNorm_smul`). So the tame operators are exactly the weight-compatible ones.

The contrast statement — what happens when a word *leaves* the monomial group through `w` — is
Section 2 step 3 (the Gauss collapse), in its own file.
-/

namespace ECCLib.Heisenberg

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-! ## The substitution operators -/

/-- Substitution by a permutation: `(P_σ f)(y) = f(σ⁻¹·y)`, `(σ⁻¹·y) i = y (σ i)`. -/
def permOp (σ : Equiv.Perm ι) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => f (fun i => y (σ i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma permOp_apply (σ : Equiv.Perm ι) (f : (ι → F) → ℂ) (y : ι → F) :
    permOp σ f y = f (fun i => y (σ i)) := rfl

/-- Substitution by a diagonal scaling: `(D_d f)(y) = f(d⁻¹·y)` (pointwise product). -/
def dilOp (d : ι → F) : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) where
  toFun f := fun y => f (fun i => (d i)⁻¹ * y i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma dilOp_apply (d : ι → F) (f : (ι → F) → ℂ) (y : ι → F) :
    dilOp d f y = f (fun i => (d i)⁻¹ * y i) := rfl

/-! ## Composition laws and units -/

theorem permOp_comp (σ τ : Equiv.Perm ι) :
    permOp (F := F) σ ∘ₗ permOp τ = permOp (σ * τ) := by
  refine LinearMap.ext fun f => ?_
  funext y
  simp only [LinearMap.comp_apply, permOp_apply, Equiv.Perm.mul_apply]

theorem dilOp_comp (d e : ι → F) :
    dilOp (F := F) d ∘ₗ dilOp e = dilOp (d * e) := by
  refine LinearMap.ext fun f => ?_
  funext y
  simp only [LinearMap.comp_apply, dilOp_apply, Pi.mul_apply]
  congr 1
  funext i
  rw [mul_inv]
  ring

@[simp] theorem permOp_one : permOp (F := F) (1 : Equiv.Perm ι) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  funext y
  simp [permOp_apply]

theorem dilOp_one : dilOp (F := F) (fun (_ : ι) => (1 : F)) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  funext y
  simp [dilOp_apply]

/-- The permutation operator as a unit of `End`. -/
noncomputable def permUnit (σ : Equiv.Perm ι) : (Module.End ℂ ((ι → F) → ℂ))ˣ where
  val := permOp σ
  inv := permOp σ⁻¹
  val_inv := by rw [Module.End.mul_eq_comp, permOp_comp, mul_inv_cancel, permOp_one]; rfl
  inv_val := by rw [Module.End.mul_eq_comp, permOp_comp, inv_mul_cancel, permOp_one]; rfl

/-- The dilation operator as a unit of `End`. -/
noncomputable def dilUnit {d : ι → F} (hd : ∀ i, d i ≠ 0) :
    (Module.End ℂ ((ι → F) → ℂ))ˣ where
  val := dilOp d
  inv := dilOp (fun i => (d i)⁻¹)
  val_inv := by
    rw [Module.End.mul_eq_comp, dilOp_comp]
    rw [show (d * fun i => (d i)⁻¹) = fun (_ : ι) => (1 : F) from
      funext fun i => mul_inv_cancel₀ (hd i), dilOp_one]
    rfl
  inv_val := by
    rw [Module.End.mul_eq_comp, dilOp_comp]
    rw [show ((fun i => (d i)⁻¹) * d) = fun (_ : ι) => (1 : F) from
      funext fun i => inv_mul_cancel₀ (hd i), dilOp_one]
    rfl

/-! ## The intertwining relations: explicit Weil operators, no multiplier -/

section Intertwining

variable [Fintype F] [DecidableEq ι]

/-- Reindexing invariance of the pairing under a permutation, mixed form:
`⟨b, y∘σ⟩ = ⟨b∘σ⁻¹, y⟩`. -/
lemma pairing_perm_right (σ : Equiv.Perm ι) (b y : ι → F) :
    pairing b (fun i => y (σ i)) = pairing (fun i => b (σ⁻¹ i)) y := by
  unfold pairing
  rw [← Equiv.sum_comp σ (fun i => b (σ⁻¹ i) * y i)]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- `⟨m, d⁻¹·y⟩ = ⟨d⁻¹·m, y⟩` — the diagonal is self-adjoint-with-inverse for the pairing. -/
lemma pairing_dil_right (d b y : ι → F) :
    pairing b (fun i => (d i)⁻¹ * y i) = pairing (fun i => (d i)⁻¹ * b i) y := by
  unfold pairing
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Substitution intertwines the Weyl operators along a permutation** — the `chirp_comp_weyl` of
the monomial world, cocycle scalar untouched. -/
theorem permOp_comp_weyl (ψ : AddChar F ℂ) (σ : Equiv.Perm ι) (p m : ι → F) :
    permOp (F := F) σ ∘ₗ weyl ψ p m
      = weyl ψ (fun i => p (σ⁻¹ i)) (fun i => m (σ⁻¹ i)) ∘ₗ permOp σ := by
  have hcocycle : pairing (fun i => m (σ⁻¹ i)) (fun i => p (σ⁻¹ i)) = pairing m p :=
    Heis.pairing_perm σ m p
  refine LinearMap.ext fun f => ?_
  funext y
  simp only [LinearMap.comp_apply, weyl, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    modulation_apply, translation_apply, permOp_apply, hcocycle]
  rw [pairing_perm_right]
  have harg : ((fun i => y (σ i)) + p) = (fun i => (y + fun j => p (σ⁻¹ j)) (σ i)) := by
    funext i
    simp only [Pi.add_apply]
    simp
  rw [harg]

/-- **Substitution intertwines the Weyl operators along a dilation**; `⟨d⁻¹m, dp⟩ = ⟨m,p⟩` keeps
the cocycle scalar fixed — exactly why no multiplier appears on the monomial group. -/
theorem dilOp_comp_weyl (ψ : AddChar F ℂ) {d : ι → F} (hd : ∀ i, d i ≠ 0) (p m : ι → F) :
    dilOp (F := F) d ∘ₗ weyl ψ p m
      = weyl ψ (fun i => d i * p i) (fun i => (d i)⁻¹ * m i) ∘ₗ dilOp d := by
  have hcocycle : pairing (fun i => (d i)⁻¹ * m i) (fun i => d i * p i) = pairing m p := by
    unfold pairing
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (d i)⁻¹ * m i * (d i * p i) = ((d i)⁻¹ * d i) * (m i * p i) from by ring,
      inv_mul_cancel₀ (hd i), one_mul]
  refine LinearMap.ext fun f => ?_
  funext y
  simp only [LinearMap.comp_apply, weyl, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    modulation_apply, translation_apply, dilOp_apply, hcocycle]
  rw [pairing_dil_right]
  have harg : ((fun i => (d i)⁻¹ * y i) + p)
      = (fun i => (d i)⁻¹ * (y + fun j => d j * p j) i) := by
    funext i
    simp only [Pi.add_apply]
    rw [mul_add, show (d i)⁻¹ * (d i * p i) = ((d i)⁻¹ * d i) * p i from by ring,
      inv_mul_cancel₀ (hd i), one_mul]
  rw [harg]

/-- **Permutations act by substitution** — the explicit Weil operator. -/
theorem hasWeilOperator_permMap (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (σ : Equiv.Perm ι) :
    HasWeilOperator h2 ψ (Heis.permMap σ) := by
  refine ⟨permUnit σ, fun x => ?_⟩
  change permOp σ * schrodinger h2 ψ x = schrodinger h2 ψ (Heis.permMap σ x) * permOp σ
  simp only [schrodinger_apply, Module.End.mul_eq_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [permOp_comp_weyl]
  rfl

/-- **Dilations act by substitution** — the explicit Weil operator, no multiplier. -/
theorem hasWeilOperator_dilMap (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    {d : ι → F} (hd : ∀ i, d i ≠ 0) :
    HasWeilOperator h2 ψ (Heis.dilMap d) := by
  refine ⟨dilUnit hd, fun x => ?_⟩
  change dilOp d * schrodinger h2 ψ x = schrodinger h2 ψ (Heis.dilMap d x) * dilOp d
  simp only [schrodinger_apply, Module.End.mul_eq_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  rw [dilOp_comp_weyl ψ hd]
  rfl

end Intertwining

/-! ## Weight compatibility: the tame operators are the weight-compatible ones -/

section Weight

open Classical in
/-- Permutation substitution permutes deltas. -/
theorem permOp_delta (σ : Equiv.Perm ι) (x : ι → F) :
    permOp σ (delta x) = delta (fun i => x (σ⁻¹ i)) := by
  funext y
  simp only [permOp_apply, delta]
  have hiff : ((fun i => y (σ i)) = x) ↔ (y = fun i => x (σ⁻¹ i)) := by
    constructor
    · intro h
      funext j
      have hj := congrFun h (σ⁻¹ j)
      simpa using hj
    · intro h
      funext i
      have hi := congrFun h (σ i)
      simpa using hi
  rw [if_congr hiff rfl rfl]

open Classical in
/-- Dilation substitution rescales deltas. -/
theorem dilOp_delta {d : ι → F} (hd : ∀ i, d i ≠ 0) (x : ι → F) :
    dilOp d (delta x) = delta (fun i => d i * x i) := by
  funext y
  simp only [dilOp_apply, delta]
  have hiff : ((fun i => (d i)⁻¹ * y i) = x) ↔ (y = fun i => d i * x i) := by
    constructor
    · intro h
      funext i
      change y i = d i * x i
      rw [← congrFun h i,
        show d i * ((d i)⁻¹ * y i) = (d i * (d i)⁻¹) * y i from by ring,
        mul_inv_cancel₀ (hd i), one_mul]
    · intro h
      funext i
      change (d i)⁻¹ * y i = x i
      rw [congrFun h i,
        show (d i)⁻¹ * (d i * x i) = ((d i)⁻¹ * d i) * x i from by ring,
        inv_mul_cancel₀ (hd i), one_mul]
  rw [if_congr hiff rfl rfl]

variable [DecidableEq F]

/-- The permutation action preserves the Hamming weight. -/
theorem hammingNorm_perm (σ : Equiv.Perm ι) (x : ι → F) :
    hammingNorm (fun i => x (σ⁻¹ i)) = hammingNorm x := by
  unfold hammingNorm
  refine Finset.card_bij' (fun i _ => σ⁻¹ i) (fun j _ => σ j) ?_ ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa using hj
  · intro i _
    simp
  · intro j _
    simp

/-- The diagonal-unit action preserves the Hamming weight — the pointwise-diagonal companion of
Mathlib's scalar `hammingNorm_smul`. -/
theorem hammingNorm_dil {d : ι → F} (hd : ∀ i, d i ≠ 0) (x : ι → F) :
    hammingNorm (fun i => d i * x i) = hammingNorm x := by
  unfold hammingNorm
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp [mul_eq_zero, hd i]

end Weight

end ECCLib.Heisenberg

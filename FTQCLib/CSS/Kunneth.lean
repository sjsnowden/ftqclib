/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Graded models and the retract behind Künneth over `𝔽₂`

The field case of Künneth (docs/fidelity/T43.md, Claim 9), on dimensions, for complexes whose
cells are `Fin (c i)` in each degree `i` and whose boundary `d i` is a matrix from degree `i + 1` to
degree `i`, over `ZMod 2`. `CSS/BasedComplex.lean` proves `finrank_homology_tensor` from these
facts.

## Main definitions

* `Kunneth.IsGraded`: a matrix between cells with degrees has degree `k` when each nonzero entry
  joins a row of degree `a` to a column of degree `a + k`; `degreeSpan`, `cyclesIn` and
  `boundariesIn` are the vectors, cycles and boundaries of one degree.
* `Kunneth.AllCells c N`: the cells of all degrees below `N` together, with the boundary
  `allBoundary`, the maps of degree `0` `allBlock` and the maps of degree `+1` `allRaise` on them.
* `Kunneth.IsSplitting`: a deformation retract of a complex onto cells with no boundary, by maps
  `f`, `g` of degree `0` and `s` of degree `+1` with `f g = 1`, `∂ g = 0`, `f ∂ = 0` and
  `∂ s + s ∂ = 1 + g f`.

## Main statements

* `Kunneth.exists_splitting`: every complex over `ZMod 2` has a splitting.
* `Kunneth.kronecker_retract`: the Kronecker product of two retracts is a retract of the tensor
  boundary `∂ ⊗ 1 + 1 ⊗ ∂'`, with `S = s ⊗ 1 + g f ⊗ s'`.
* `Kunneth.finrank_cyclesIn_of_retract`: under a graded retract the cycles of degree `n` have the
  dimension of the retract's cells of degree `n` plus that of the boundaries.
* `Kunneth.finrank_cycles_boundaries_eq_of_embedding`: a complex and a graded model of its cells of
  degrees `n - 1`, `n` and `n + 1` have cycles and boundaries of the same dimensions in degree `n`.

## Implementation notes

Every sign is `1` over `ZMod 2`, so the tensor boundary and the homotopy `S` carry none. The
splitting is built degree by degree: `s_i` is a right inverse of `d_i` on its image after a
projection onto that image chosen to vanish on the image of `s_{i-1}`, so that `s s = 0`; then
`1 + ∂ s + s ∂` is idempotent, and `f`, `g` factor it through its image (`exists_contraction`,
`exists_factor_of_idempotent`). On `AllCells c N` the boundary out of degree `N - 1` is cut, so the
splitting of the cut complex holds there as single matrices.
-/

namespace FTQCLib.CSS.Kunneth

open Matrix
open scoped Kronecker

/-- Over `ZMod 2` a matrix is its own negative. -/
theorem matrix_add_self_eq_zero {m n : Type*} (M : Matrix m n (ZMod 2)) : M + M = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero (M i j)

/-- Over `ZMod 2` a vector is its own negative. -/
theorem vector_add_self_eq_zero {m : Type*} (v : m → ZMod 2) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

/-- A matrix `M` between graded cell sets has degree `k`: `M x y` is zero unless the column `y` has
the degree of the row `x` plus `k`. -/
def IsGraded {ι ι' : Type*} (δr : ι → ℕ) (δc : ι' → ℕ) (k : ℤ) (M : Matrix ι ι' (ZMod 2)) :
    Prop :=
  ∀ x y, M x y ≠ 0 → (δc y : ℤ) = δr x + k

/-- The vectors supported on the cells of degree `n`. -/
def degreeSpan {ι : Type*} (δ : ι → ℕ) (n : ℕ) : Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {v | ∀ x, δ x ≠ n → v x = 0}
  add_mem' {v w} hv hw x hx := by simp [hv x hx, hw x hx]
  zero_mem' _ _ := rfl
  smul_mem' a v hv x hx := by simp [hv x hx]

/-- A matrix of degree `k` takes a vector supported in degree `m` to one supported in degree
`m - k`. -/
theorem IsGraded.mulVec_mem {ι ι' : Type*} [Fintype ι'] {δr : ι → ℕ} {δc : ι' → ℕ}
    {k : ℤ} {M : Matrix ι ι' (ZMod 2)} (hM : IsGraded δr δc k M) {m n : ℕ} (hmn : (m : ℤ) = n + k)
    {v : ι' → ZMod 2} (hv : v ∈ degreeSpan δc m) : M *ᵥ v ∈ degreeSpan δr n := by
  intro x hx
  refine Finset.sum_eq_zero fun y _ => ?_
  dsimp only
  by_cases hy : δc y = m
  · have hxy : M x y = 0 := by
      by_contra h
      have := hM x y h
      omega
    rw [hxy, zero_mul]
  · rw [hv y hy, mul_zero]

/-- Degrees add under products. -/
theorem IsGraded.mul {ι ι' ι'' : Type*} [Fintype ι'] {δ : ι → ℕ} {δ' : ι' → ℕ}
    {δ'' : ι'' → ℕ} {k l m : ℤ} {A : Matrix ι ι' (ZMod 2)} {B : Matrix ι' ι'' (ZMod 2)}
    (hA : IsGraded δ δ' k A) (hB : IsGraded δ' δ'' l B) (hm : k + l = m) :
    IsGraded δ δ'' m (A * B) := by
  intro x z hxz
  rw [Matrix.mul_apply] at hxz
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxz
  have h1 := hA x y (left_ne_zero_of_mul hy)
  have h2 := hB y z (right_ne_zero_of_mul hy)
  omega

/-- A sum of two matrices of degree `k` has degree `k`. -/
theorem IsGraded.add {ι ι' : Type*} {δ : ι → ℕ} {δ' : ι' → ℕ} {k : ℤ}
    {A B : Matrix ι ι' (ZMod 2)} (hA : IsGraded δ δ' k A) (hB : IsGraded δ δ' k B) :
    IsGraded δ δ' k (A + B) := by
  intro x y hxy
  rw [Matrix.add_apply] at hxy
  by_cases hA0 : A x y = 0
  · rw [hA0, zero_add] at hxy
    exact hB x y hxy
  · exact hA x y hA0

/-- The identity has degree `0`. -/
theorem IsGraded.one {ι : Type*} [DecidableEq ι] (δ : ι → ℕ) :
    IsGraded δ δ 0 (1 : Matrix ι ι (ZMod 2)) := by
  intro x y hxy
  rw [Matrix.one_apply] at hxy
  split_ifs at hxy with h
  · subst h
    simp
  · exact absurd rfl hxy

/-- Degrees add under Kronecker products, a pair of cells having the sum of their degrees. -/
theorem IsGraded.kronecker {ι₁ ι₁' ι₂ ι₂' : Type*} {δ₁ : ι₁ → ℕ} {δ₁' : ι₁' → ℕ}
    {δ₂ : ι₂ → ℕ} {δ₂' : ι₂' → ℕ} {k l m : ℤ} {A : Matrix ι₁ ι₁' (ZMod 2)}
    {B : Matrix ι₂ ι₂' (ZMod 2)} (hA : IsGraded δ₁ δ₁' k A) (hB : IsGraded δ₂ δ₂' l B)
    (hm : k + l = m) :
    IsGraded (fun x : ι₁ × ι₂ => δ₁ x.1 + δ₂ x.2) (fun y : ι₁' × ι₂' => δ₁' y.1 + δ₂' y.2) m
      (A ⊗ₖ B) := by
  intro x y hxy
  rw [kroneckerMap_apply] at hxy
  have h1 := hA x.1 y.1 (left_ne_zero_of_mul hxy)
  have h2 := hB x.2 y.2 (right_ne_zero_of_mul hxy)
  push_cast
  omega

/-- The cycles of degree `n` of a graded matrix `d` of degree `1`. -/
def cyclesIn {ι : Type*} [Fintype ι] (δ : ι → ℕ) (d : Matrix ι ι (ZMod 2)) (n : ℕ) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  degreeSpan δ n ⊓ LinearMap.ker d.mulVecLin

/-- The boundaries of degree `n` of a graded matrix `d` of degree `1`. -/
def boundariesIn {ι : Type*} [Fintype ι] (δ : ι → ℕ) (d : Matrix ι ι (ZMod 2)) (n : ℕ) :
    Submodule (ZMod 2) (ι → ZMod 2) :=
  (degreeSpan δ (n + 1)).map d.mulVecLin

/-- The matrix of the extension by zero along `e`. -/
def extendMatrix {ι κ : Type*} [DecidableEq ι] (e : κ → ι) : Matrix ι κ (ZMod 2) :=
  Matrix.of fun x σ => if e σ = x then 1 else 0

/-- The extension by zero along an injection is the vector on its image. -/
theorem extendMatrix_mulVec_apply {ι κ : Type*} [DecidableEq ι] [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) (v : κ → ZMod 2) (σ : κ) : (extendMatrix e *ᵥ v) (e σ) = v σ := by
  simp only [extendMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    rw [if_neg (fun h => hτ (he h)), zero_mul]
  · simp

/-- The extension by zero vanishes off the image. -/
theorem extendMatrix_mulVec_apply_of_forall_ne {ι κ : Type*} [DecidableEq ι] [Fintype κ] (e : κ → ι)
    (v : κ → ZMod 2) (x : ι) (hx : ∀ σ, e σ ≠ x) : (extendMatrix e *ᵥ v) x = 0 := by
  simp only [extendMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_eq_zero fun τ _ => by rw [if_neg (hx τ), zero_mul]

/-- The extension by zero along an injection is injective. -/
theorem extendMatrix_mulVecLin_injective {ι κ : Type*} [DecidableEq ι] [Fintype κ] {e : κ → ι}
    (he : Function.Injective e) : Function.Injective (extendMatrix e).mulVecLin := by
  intro v w h
  funext σ
  have := congrFun h (e σ)
  rwa [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, extendMatrix_mulVec_apply he,
    extendMatrix_mulVec_apply he] at this

/-- The vectors supported in degree `n` are the extensions by zero along an injection onto the
cells of degree `n`. -/
theorem degreeSpan_eq_range_extendMatrix {ι κ : Type*} [DecidableEq ι] [Fintype κ] {δ : ι → ℕ}
    {n : ℕ} {e : κ → ι} (he : Function.Injective e) (hr : ∀ x, (∃ σ, e σ = x) ↔ δ x = n) :
    degreeSpan δ n = LinearMap.range (extendMatrix e).mulVecLin := by
  ext v
  constructor
  · intro hv
    refine ⟨fun σ => v (e σ), funext fun x => ?_⟩
    rw [Matrix.mulVecLin_apply]
    by_cases hx : ∃ σ, e σ = x
    · obtain ⟨σ, rfl⟩ := hx
      exact extendMatrix_mulVec_apply he _ σ
    · rw [extendMatrix_mulVec_apply_of_forall_ne _ _ x (fun σ h => hx ⟨σ, h⟩)]
      exact (hv x (fun h => hx ((hr x).2 h))).symm
  · rintro ⟨w, rfl⟩ x hx
    rw [Matrix.mulVecLin_apply]
    exact extendMatrix_mulVec_apply_of_forall_ne _ _ x (fun σ h => hx ((hr x).1 ⟨σ, h⟩))

/-- A matrix restricted to the images of two embeddings, when its columns from the second image
vanish off the first. -/
theorem mul_extendMatrix {ι κ κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {e : κ → ι} {e' : κ' → ι} (he : Function.Injective e) (M : Matrix ι ι (ZMod 2))
    (B : Matrix κ κ' (ZMod 2)) (hent : ∀ σ τ, M (e σ) (e' τ) = B σ τ)
    (hzero : ∀ x τ, M x (e' τ) ≠ 0 → ∃ σ, e σ = x) :
    M * extendMatrix e' = extendMatrix e * B := by
  ext x τ
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hl : ∑ y, M x y * extendMatrix e' y τ = M x (e' τ) := by
    simp [extendMatrix]
  rw [hl]
  by_cases hx : ∃ σ, e σ = x
  · obtain ⟨σ, rfl⟩ := hx
    rw [hent, Finset.sum_eq_single σ]
    · simp [extendMatrix]
    · intro σ' _ h
      simp [extendMatrix, he.ne h]
    · simp
  · rw [Finset.sum_eq_zero fun σ _ => by simp [extendMatrix, show e σ ≠ x from fun h => hx ⟨σ, h⟩]]
    by_contra h
    exact hx (hzero x τ h)

/-- **A deformation retract onto cells with no boundary counts the homology.** If `G F` is
homotopic to the identity through `S`, `F G = 1`, `G` lands in the cycles and `F` kills the
boundaries, all graded, then the cycles of degree `n` are the image of `G` on the cells of degree
`n` and the boundaries, independently. -/
theorem finrank_cyclesIn_of_retract {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (δ : ι → ℕ) (δ' : ι' → ℕ) (d S : Matrix ι ι (ZMod 2))
    (F : Matrix ι' ι (ZMod 2)) (G : Matrix ι ι' (ZMod 2)) (hd : IsGraded δ δ 1 d)
    (hS : IsGraded δ δ (-1) S) (hF : IsGraded δ' δ 0 F) (hG : IsGraded δ δ' 0 G)
    (hdd : d * d = 0) (hFG : F * G = 1) (hdG : d * G = 0) (hFd : F * d = 0)
    (hdS : d * S + S * d = 1 + G * F) (n : ℕ) :
    Module.finrank (ZMod 2) (cyclesIn δ d n) =
      Fintype.card {a // δ' a = n} + Module.finrank (ZMod 2) (boundariesIn δ d n) := by
  have he : Function.Injective (Subtype.val : {a // δ' a = n} → ι') := Subtype.val_injective
  have hr : ∀ a, (∃ σ : {a // δ' a = n}, σ.val = a) ↔ δ' a = n :=
    fun a => ⟨by rintro ⟨σ, rfl⟩; exact σ.2, fun h => ⟨⟨a, h⟩, rfl⟩⟩
  have hspan := degreeSpan_eq_range_extendMatrix he hr
  have hinj : Function.Injective
      (G.mulVecLin ∘ₗ (extendMatrix (Subtype.val : {a // δ' a = n} → ι')).mulVecLin) := by
    intro u v huv
    apply extendMatrix_mulVecLin_injective he
    have := congrArg F.mulVecLin huv
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hFG, Matrix.one_mul] using this
  set R := LinearMap.range
    (G.mulVecLin ∘ₗ (extendMatrix (Subtype.val : {a // δ' a = n} → ι')).mulVecLin) with hR
  have hRfin : Module.finrank (ZMod 2) R = Fintype.card {a // δ' a = n} := by
    rw [hR, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hsup : cyclesIn δ d n = R ⊔ boundariesIn δ d n := by
    apply le_antisymm
    · rintro z ⟨hzn, hz0⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz0 hzn
      have h2 : d *ᵥ (S *ᵥ z) = z + G *ᵥ (F *ᵥ z) := by
        have := congrArg (fun M => M *ᵥ z) hdS
        simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hz0, Matrix.mulVec_zero, add_zero,
          Matrix.one_mulVec] at this
        exact this
      have hz : z = G *ᵥ (F *ᵥ z) + d *ᵥ (S *ᵥ z) := by
        rw [h2, add_comm z, ← add_assoc, vector_add_self_eq_zero, zero_add]
      rw [hz]
      refine Submodule.add_mem_sup ?_ ?_
      · have hFz : F *ᵥ z ∈ degreeSpan δ' n := hF.mulVec_mem (by simp) hzn
        rw [hspan] at hFz
        obtain ⟨u, hu⟩ := hFz
        exact ⟨u, by rw [LinearMap.comp_apply, hu, Matrix.mulVecLin_apply]⟩
      · exact Submodule.mem_map_of_mem (hS.mulVec_mem (by push_cast; ring) hzn)
    · refine sup_le ?_ ?_
      · rintro _ ⟨u, rfl⟩
        refine ⟨hG.mulVec_mem (m := n) (by simp) ?_, ?_⟩
        · rw [hspan]
          exact LinearMap.mem_range_self _ u
        · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply,
            Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hdG, Matrix.zero_mulVec]
      · rintro _ ⟨w, hw, rfl⟩
        refine ⟨hd.mulVec_mem (by push_cast; ring) hw, ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec, hdd, Matrix.zero_mulVec]
  have hinf : R ⊓ boundariesIn δ d n = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨⟨u, rfl⟩, ⟨w, -, hw⟩⟩
    rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hw ⊢
    have hu : extendMatrix (Subtype.val : {a // δ' a = n} → ι') *ᵥ u = 0 := by
      have := congrArg (fun v => F *ᵥ v) hw
      simp only [Matrix.mulVec_mulVec, hFd, hFG, Matrix.zero_mulVec, Matrix.one_mulVec] at this
      exact this.symm
    rw [hu, Matrix.mulVec_zero]
  have := Submodule.finrank_sup_add_finrank_inf_eq R (boundariesIn δ d n)
  rw [← hsup, hinf, finrank_bot, add_zero, hRfin] at this
  exact this

/-- **A based complex and a graded model of it have the same cycles and boundaries in degree `n`**,
when the cells of degrees `n - 1`, `n` and `n + 1` embed onto the model's cells of those degrees,
the incidences agreeing. -/
theorem finrank_cycles_boundaries_eq_of_embedding {ι : Type*} [Fintype ι] (δ : ι → ℕ)
    (d : Matrix ι ι (ZMod 2)) (hd : IsGraded δ δ 1 d) (n : ℕ) {mb m ma : ℕ}
    (A : Matrix (Fin mb) (Fin m) (ZMod 2)) (B : Matrix (Fin m) (Fin ma) (ZMod 2))
    (eb : Fin mb → ι) (e : Fin m → ι) (ea : Fin ma → ι) (heb : Function.Injective eb)
    (he : Function.Injective e) (hea : Function.Injective ea)
    (hrb : ∀ x, (∃ σ, eb σ = x) ↔ δ x + 1 = n) (hr : ∀ x, (∃ σ, e σ = x) ↔ δ x = n)
    (hra : ∀ x, (∃ σ, ea σ = x) ↔ δ x = n + 1)
    (hA : ∀ σ τ, d (eb σ) (e τ) = A σ τ) (hB : ∀ σ τ, d (e σ) (ea τ) = B σ τ) :
    Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
        Module.finrank (ZMod 2) (cyclesIn δ d n) ∧
      Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) =
        Module.finrank (ZMod 2) (boundariesIn δ d n) := by
  classical
  have hdA : d * extendMatrix e = extendMatrix eb * A :=
    mul_extendMatrix heb d A hA fun x τ hx => (hrb x).2 (by
    have h1 := hd x (e τ) hx
    have h2 := (hr (e τ)).1 ⟨τ, rfl⟩
    omega)
  have hdB : d * extendMatrix ea = extendMatrix e * B :=
    mul_extendMatrix he d B hB fun x τ hx => (hr x).2 (by
    have h1 := hd x (ea τ) hx
    have h2 := (hra (ea τ)).1 ⟨τ, rfl⟩
    omega)
  constructor
  · have hc : cyclesIn δ d n = (LinearMap.ker A.mulVecLin).map (extendMatrix e).mulVecLin := by
      ext z
      rw [cyclesIn, Submodule.mem_inf, degreeSpan_eq_range_extendMatrix he hr]
      constructor
      · rintro ⟨⟨v, rfl⟩, hz⟩
        refine ⟨v, ?_, rfl⟩
        apply extendMatrix_mulVecLin_injective heb
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec, hdA, ← Matrix.mulVec_mulVec] at hz
        simp only [Matrix.mulVecLin_apply]
        rw [hz, Matrix.mulVec_zero]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨⟨v, rfl⟩, ?_⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec, hdA, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    rw [hc, ← LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (extendMatrix_mulVecLin_injective he) _)]
  · have hb : boundariesIn δ d n =
        (LinearMap.range B.mulVecLin).map (extendMatrix e).mulVecLin := by
      rw [boundariesIn, degreeSpan_eq_range_extendMatrix hea hra, ← LinearMap.range_comp,
        ← Matrix.mulVecLin_mul, hdB, Matrix.mulVecLin_mul, LinearMap.range_comp]
    rw [hb, ← LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective _ (extendMatrix_mulVecLin_injective he) _)]

/-- A set of cells onto which an injection embeds has the injection's domain's size. -/
theorem card_subtype_of_embedding {κ ι : Type*} [Fintype κ] [Fintype ι] (P : ι → Prop)
    [DecidablePred P] (e : κ → ι) (he : Function.Injective e) (hr : ∀ x, (∃ σ, e σ = x) ↔ P x) :
    Fintype.card {x // P x} = Fintype.card κ :=
  (Fintype.card_congr (Equiv.ofBijective (fun σ => (⟨e σ, (hr _).1 ⟨σ, rfl⟩⟩ : {x // P x}))
    ⟨fun _ _ h => he (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨σ, rfl⟩ := (hr x).2 hx
      exact ⟨σ, rfl⟩⟩)).symm

/-- The cells of degree below `N` of a cell count `c`, all degrees together. -/
abbrev AllCells (c : ℕ → ℕ) (N : ℕ) : Type := Σ i : Fin N, Fin (c i)

/-- Two cells of `AllCells c N` are equal when their degrees and their indices are. -/
theorem allCells_mk_eq_mk_iff {c : ℕ → ℕ} {N : ℕ} {i j : Fin N} {σ : Fin (c i)} {τ : Fin (c j)} :
    (⟨i, σ⟩ : AllCells c N) = ⟨j, τ⟩ ↔ (i : ℕ) = j ∧ (σ : ℕ) = τ := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    obtain rfl : i = j := Fin.ext h1
    obtain rfl : σ = τ := Fin.ext h2
    rfl

/-- The identity on all the cells of degree below `N`, entrywise. -/
theorem one_allCells_apply {c : ℕ → ℕ} {N : ℕ} (x y : AllCells c N) :
    (1 : Matrix (AllCells c N) (AllCells c N) (ZMod 2)) x y =
      if (x.1 : ℕ) = y.1 ∧ (x.2 : ℕ) = y.2 then 1 else 0 := by
  obtain ⟨i, σ⟩ := x
  obtain ⟨j, τ⟩ := y
  rw [Matrix.one_apply]
  by_cases h : (i : ℕ) = j ∧ (σ : ℕ) = τ
  · rw [if_pos (allCells_mk_eq_mk_iff.2 h), if_pos h]
  · rw [if_neg (fun e => h (allCells_mk_eq_mk_iff.1 e)), if_neg h]

/-- A sum over all the cells whose terms vanish outside degree `k`. -/
theorem sum_allCells_eq_of_degree {c : ℕ → ℕ} {N : ℕ} (F : ∀ e : ℕ, Fin (c e) → ZMod 2) (k : ℕ)
    (hF : ∀ e, e ≠ k → ∀ ρ, F e ρ = 0) :
    ∑ y : AllCells c N, F y.1 y.2 = if k < N then ∑ ρ : Fin (c k), F k ρ else 0 := by
  rw [Fintype.sum_sigma]
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · intro e _ he
      exact Finset.sum_eq_zero fun ρ _ => hF e (fun h => he (Fin.ext h)) ρ
    · simp
  · exact Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ =>
      hF e (by have := e.isLt; omega) ρ

/-- The incidence of the boundary `d` between a cell of degree `a` and one of degree `b`. -/
def incidenceEntry (c : ℕ → ℕ) (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (a b : ℕ) (σ : Fin (c a)) (τ : Fin (c b)) : ZMod 2 :=
  if h : b = a + 1 then d a σ (Fin.cast (congrArg c h) τ) else 0

/-- The entry of a map `s` of degree `+1` between a cell of degree `a` and one of degree `b`. -/
def raiseEntry (c : ℕ → ℕ) (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2))
    (a b : ℕ) (σ : Fin (c a)) (τ : Fin (c b)) : ZMod 2 :=
  if h : a = b + 1 then s b (Fin.cast (congrArg c h) σ) τ else 0

/-- The entry of a map `M` of degree `0` between a cell of degree `a` and one of degree `b`. -/
def blockEntry {r c : ℕ → ℕ} (M : ∀ i, Matrix (Fin (r i)) (Fin (c i)) (ZMod 2))
    (a b : ℕ) (σ : Fin (r a)) (τ : Fin (c b)) : ZMod 2 :=
  if h : b = a then M a σ (Fin.cast (congrArg c h) τ) else 0

/-- The boundary on all the cells of degree below `N`. -/
def allBoundary (c : ℕ → ℕ) (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2)) (N : ℕ) :
    Matrix (AllCells c N) (AllCells c N) (ZMod 2) :=
  Matrix.of fun x y => incidenceEntry c d x.1 y.1 x.2 y.2

/-- A map of degree `+1` on all the cells of degree below `N`. -/
def allRaise (c : ℕ → ℕ) (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)) (N : ℕ) :
    Matrix (AllCells c N) (AllCells c N) (ZMod 2) :=
  Matrix.of fun x y => raiseEntry c s x.1 y.1 x.2 y.2

/-- A map of degree `0` on all the cells of degree below `N`. -/
def allBlock {r c : ℕ → ℕ} (M : ∀ i, Matrix (Fin (r i)) (Fin (c i)) (ZMod 2)) (N : ℕ) :
    Matrix (AllCells r N) (AllCells c N) (ZMod 2) :=
  Matrix.of fun x y => blockEntry M x.1 y.1 x.2 y.2

/-- The boundary has degree `1`: a column has the degree of its row plus one. -/
theorem allBoundary_isGraded (c : ℕ → ℕ) (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (N : ℕ) :
    IsGraded (fun x : AllCells c N => (x.1 : ℕ)) (fun x => (x.1 : ℕ)) 1 (allBoundary c d N) := by
  intro x y h
  simp only [allBoundary, Matrix.of_apply, incidenceEntry] at h
  split_ifs at h with hb
  · dsimp only
    omega
  · exact absurd rfl h

/-- A map of degree `+1` has degree `-1` as a matrix: a column has the degree of its row less
one. -/
theorem allRaise_isGraded (c : ℕ → ℕ) (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2))
    (N : ℕ) :
    IsGraded (fun x : AllCells c N => (x.1 : ℕ)) (fun x => (x.1 : ℕ)) (-1) (allRaise c s N) := by
  intro x y h
  simp only [allRaise, Matrix.of_apply, raiseEntry] at h
  split_ifs at h with ha
  · dsimp only
    omega
  · exact absurd rfl h

/-- A map of degree `0` has degree `0`. -/
theorem allBlock_isGraded {r c : ℕ → ℕ} (M : ∀ i, Matrix (Fin (r i)) (Fin (c i)) (ZMod 2))
    (N : ℕ) : IsGraded (fun x : AllCells r N => (x.1 : ℕ)) (fun x : AllCells c N => (x.1 : ℕ)) 0
      (allBlock M N) := by
  intro x y h
  simp only [allBlock, Matrix.of_apply, blockEntry] at h
  split_ifs at h with hb
  · dsimp only
    omega
  · exact absurd rfl h

/-- Maps of degree `0` compose degree by degree. -/
theorem allBlock_mul_allBlock {r c t : ℕ → ℕ} {N : ℕ}
    (M : ∀ i, Matrix (Fin (r i)) (Fin (c i)) (ZMod 2))
    (M' : ∀ i, Matrix (Fin (c i)) (Fin (t i)) (ZMod 2)) :
    allBlock M N * allBlock M' N = allBlock (fun i => M i * M' i) N := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  rw [Matrix.mul_apply]
  simp only [allBlock, Matrix.of_apply]
  rw [sum_allCells_eq_of_degree (fun e ρ => blockEntry M a e σ ρ * blockEntry M' e b ρ τ) a
    (fun e he ρ => by simp [blockEntry, he]), if_pos ha]
  by_cases hab : b = a
  · subst hab
    simp [blockEntry, Matrix.mul_apply]
  · simp [blockEntry, hab]

/-- Maps of degree `0` add degree by degree. -/
theorem allBlock_add {r c : ℕ → ℕ} {N : ℕ}
    (M M' : ∀ i, Matrix (Fin (r i)) (Fin (c i)) (ZMod 2)) :
    allBlock M N + allBlock M' N = allBlock (fun i => M i + M' i) N := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  simp only [allBlock, Matrix.add_apply, Matrix.of_apply, blockEntry]
  split_ifs <;> simp

/-- The identity is the map of degree `0` with identity blocks. -/
theorem allBlock_one {c : ℕ → ℕ} {N : ℕ} :
    allBlock (fun i => (1 : Matrix (Fin (c i)) (Fin (c i)) (ZMod 2))) N = 1 := by
  ext x y
  rw [one_allCells_apply]
  obtain ⟨⟨a, ha⟩, σ⟩ := x
  obtain ⟨⟨b, hb⟩, τ⟩ := y
  simp only [allBlock, Matrix.of_apply, blockEntry]
  by_cases hab : b = a
  · subst hab
    simp [Matrix.one_apply, Fin.ext_iff]
  · rw [dif_neg hab, if_neg (fun h => hab h.1.symm)]

/-- `∂ g = 0` from `∂_a g_{a+1} = 0` in each degree. -/
theorem allBoundary_mul_allBlock {r c : ℕ → ℕ} {N : ℕ}
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (M : ∀ i, Matrix (Fin (c i)) (Fin (r i)) (ZMod 2)) (h : ∀ a, d a * M (a + 1) = 0) :
    allBoundary c d N * allBlock M N = 0 := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [allBoundary, allBlock, Matrix.of_apply]
  rw [sum_allCells_eq_of_degree (fun e ρ => incidenceEntry c d a e σ ρ * blockEntry M e b ρ τ) b
    (fun e he ρ => by simp [blockEntry, Ne.symm he]), if_pos hb]
  by_cases hab : b = a + 1
  · subst hab
    have := congrFun (congrFun (h a) σ) τ
    simpa [incidenceEntry, blockEntry, Matrix.mul_apply] using this
  · simp [incidenceEntry, hab]

/-- `f ∂ = 0` from `f_a ∂_a = 0` in each degree. -/
theorem allBlock_mul_allBoundary {r c : ℕ → ℕ} {N : ℕ}
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (M : ∀ i, Matrix (Fin (r i)) (Fin (c i)) (ZMod 2)) (h : ∀ a, M a * d a = 0) :
    allBlock M N * allBoundary c d N = 0 := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [allBoundary, allBlock, Matrix.of_apply]
  rw [sum_allCells_eq_of_degree (fun e ρ => blockEntry M a e σ ρ * incidenceEntry c d e b ρ τ) a
    (fun e he ρ => by simp [blockEntry, he]), if_pos ha]
  by_cases hab : b = a + 1
  · subst hab
    have := congrFun (congrFun (h a) σ) τ
    simpa [incidenceEntry, blockEntry, Matrix.mul_apply] using this
  · simp [incidenceEntry, hab]

/-- `∂ ∂ = 0` on all the cells of degree below `N`. -/
theorem allBoundary_mul_allBoundary {c : ℕ → ℕ} {N : ℕ}
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2)) (h : ∀ a, d a * d (a + 1) = 0) :
    allBoundary c d N * allBoundary c d N = 0 := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [allBoundary, Matrix.of_apply]
  rw [sum_allCells_eq_of_degree
    (fun e ρ => incidenceEntry c d a e σ ρ * incidenceEntry c d e b ρ τ) (a + 1)
    (fun e he ρ => by simp [incidenceEntry, he])]
  split_ifs with h1
  · by_cases hab : b = a + 1 + 1
    · subst hab
      have := congrFun (congrFun (h a) σ) τ
      simpa [incidenceEntry, Matrix.mul_apply] using this
    · simp [incidenceEntry, hab]
  · rfl

/-- The map of degree `0` beside `s ∘ d`: `0` in degree `0`, and `s_{j} d_{j}` in degree
`j + 1`. -/
def raiseAfterBoundary (c : ℕ → ℕ) (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)) :
    ∀ i, Matrix (Fin (c i)) (Fin (c i)) (ZMod 2)
  | 0 => 0
  | j + 1 => s j * d j

/-- `∂ s` is `∂_a s_a` in each degree `a`, when no boundary leaves degree `N - 1` or above. -/
theorem allBoundary_mul_allRaise {c : ℕ → ℕ} {N : ℕ}
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)) (hN : ∀ a, N ≤ a + 1 → d a = 0) :
    allBoundary c d N * allRaise c s N = allBlock (fun a => d a * s a) N := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  rw [Matrix.mul_apply]
  simp only [allBoundary, allRaise, allBlock, Matrix.of_apply]
  rw [sum_allCells_eq_of_degree
    (fun e ρ => incidenceEntry c d a e σ ρ * raiseEntry c s e b ρ τ) (a + 1)
    (fun e he ρ => by simp [incidenceEntry, he])]
  split_ifs with h1
  · by_cases hab : b = a
    · subst hab
      simp [incidenceEntry, raiseEntry, blockEntry, Matrix.mul_apply]
    · simp [raiseEntry, blockEntry, hab, show a ≠ b from fun h => hab h.symm]
  · by_cases hab : b = a
    · subst hab
      simp [blockEntry, hN b (by omega)]
    · simp [blockEntry, hab]

/-- `s ∂` is `s_{a-1} ∂_{a-1}` in each degree `a`. -/
theorem allRaise_mul_allBoundary {c : ℕ → ℕ} {N : ℕ}
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)) :
    allRaise c s N * allBoundary c d N = allBlock (raiseAfterBoundary c d s) N := by
  ext ⟨⟨a, ha⟩, σ⟩ ⟨⟨b, hb⟩, τ⟩
  rw [Matrix.mul_apply]
  simp only [allBoundary, allRaise, allBlock, Matrix.of_apply]
  cases a with
  | zero =>
    rw [Finset.sum_eq_zero fun y _ => by simp [raiseEntry]]
    by_cases hab : b = 0
    · subst hab
      simp [blockEntry, raiseAfterBoundary]
    · simp [blockEntry, hab]
  | succ j =>
    rw [sum_allCells_eq_of_degree
      (fun e ρ => raiseEntry c s (j + 1) e σ ρ * incidenceEntry c d e b ρ τ) j
      (fun e he ρ => by simp [raiseEntry, Ne.symm he]), if_pos (by omega)]
    by_cases hab : b = j + 1
    · subst hab
      simp [incidenceEntry, raiseEntry, blockEntry, raiseAfterBoundary, Matrix.mul_apply]
    · simp [incidenceEntry, blockEntry, hab]

/-- **A contraction of a complex over a field**: maps `s` of degree `+1` with `∂ s ∂ = ∂`,
`s ∂ s = s` and `s s = 0`. Each `s_i` is a right inverse of `∂_{i+1}` onto its image after a
projection onto that image, chosen to vanish on the image of `s_{i-1}`. -/
theorem exists_contraction (c : ℕ → ℕ)
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2)) (hdd : ∀ i, d i * d (i + 1) = 0) :
    ∃ s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2),
      (∀ i, d i * s i * d i = d i) ∧ (∀ i, s i * d i * s i = s i) ∧ ∀ i, s (i + 1) * s i = 0 := by
  have hr : ∀ i, ∃ r : LinearMap.range (d i).mulVecLin →ₗ[ZMod 2] (Fin (c (i + 1)) → ZMod 2),
      ∀ b, d i *ᵥ r b = b := by
    intro i
    obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective (d i).mulVecLin.rangeRestrict
      (LinearMap.range_rangeRestrict _)
    exact ⟨r, fun b => congrArg Subtype.val (LinearMap.congr_fun hr b)⟩
  choose r hr using hr
  let R : ∀ i, Submodule (ZMod 2) (Fin (c i) → ZMod 2) := fun i =>
    Nat.casesOn (motive := fun i => Submodule (ZMod 2) (Fin (c i) → ZMod 2)) i ⊥
      fun j => LinearMap.range (r j)
  have hdisj : ∀ i, Disjoint (LinearMap.range (d i).mulVecLin) (R i) := by
    intro i
    cases i with
    | zero => exact disjoint_bot_right
    | succ j =>
      rw [Submodule.disjoint_def]
      rintro x ⟨w, rfl⟩ ⟨b, hb⟩
      have h1 : d j *ᵥ (r j b) = b := hr j b
      rw [hb, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hdd, Matrix.zero_mulVec] at h1
      have hb0 : b = 0 := Subtype.ext h1.symm
      rw [← hb, hb0, map_zero]
  have hπ : ∀ i, ∃ π : (Fin (c i) → ZMod 2) →ₗ[ZMod 2] LinearMap.range (d i).mulVecLin,
      (∀ b : LinearMap.range (d i).mulVecLin, π b = b) ∧ ∀ y ∈ R i, π y = 0 := by
    intro i
    obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective
      ((R i).mkQ ∘ₗ (LinearMap.range (d i).mulVecLin).subtype) (by
        rw [LinearMap.ker_eq_bot']
        intro b hb
        have hbR : (b : Fin (c i) → ZMod 2) ∈ R i := (Submodule.Quotient.mk_eq_zero _).1 hb
        exact Subtype.ext ((Submodule.disjoint_def.1 (hdisj i)) b b.2 hbR))
    refine ⟨l ∘ₗ (R i).mkQ, fun b => LinearMap.congr_fun hl b, fun y hy => ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hy, map_zero]
  choose π hπ1 hπ2 using hπ
  refine ⟨fun i => LinearMap.toMatrix' ((r i).comp (π i)), fun i => ?_, fun i => ?_, fun i => ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
      Matrix.toLin'_apply]
    have hv : π i (d i *ᵥ v) = ⟨d i *ᵥ v, LinearMap.mem_range_self _ v⟩ := hπ1 i ⟨_, _⟩
    rw [hv, hr]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
      Matrix.toLin'_apply]
    rw [hr, hπ1]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, map_zero,
      LinearMap.zero_apply]
    rw [hπ2 (i + 1) _ ⟨π i v, rfl⟩, map_zero]

/-- `1 + X` is idempotent over `ZMod 2` when `X` is. -/
theorem one_add_mul_one_add_of_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n (ZMod 2)} (hX : X * X = X) : (1 + X) * (1 + X) = 1 + X := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hX]
  rw [add_assoc, matrix_add_self_eq_zero, add_zero]

/-- An idempotent factors through its image: `P = g f` with `f g = 1`. -/
theorem exists_factor_of_idempotent {m : ℕ} (P : Matrix (Fin m) (Fin m) (ZMod 2))
    (hP : P * P = P) :
    ∃ (h : ℕ) (f : Matrix (Fin h) (Fin m) (ZMod 2)) (g : Matrix (Fin m) (Fin h) (ZMod 2)),
      f * g = 1 ∧ g * f = P := by
  set L := Matrix.toLin' P with hL
  set b := Module.finBasis (ZMod 2) (LinearMap.range L) with hb
  have hfix : ∀ y : LinearMap.range L, L.rangeRestrict y = y := by
    rintro ⟨_, v, rfl⟩
    apply Subtype.ext
    change L (L v) = L v
    rw [← LinearMap.comp_apply, hL, ← Matrix.toLin'_mul, hP]
  refine ⟨Module.finrank (ZMod 2) (LinearMap.range L),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ L.rangeRestrict),
    LinearMap.toMatrix' ((LinearMap.range L).subtype ∘ₗ b.equivFun.symm.toLinearMap), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, hfix,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← LinearMap.toMatrix'_comp]
    have : (LinearMap.range L).subtype ∘ₗ b.equivFun.symm.toLinearMap ∘ₗ
        (b.equivFun.toLinearMap ∘ₗ L.rangeRestrict) = L := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.subtype_apply]
      rfl
    rw [LinearMap.comp_assoc, this, hL, LinearMap.toMatrix'_toLin']

/-- The projection `1 + ∂ s + s ∂` of a contraction, onto a complement of the boundaries among the
cycles. -/
def contractionProjection (c : ℕ → ℕ) (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)) (i : ℕ) :
    Matrix (Fin (c i)) (Fin (c i)) (ZMod 2) :=
  1 + (d i * s i + raiseAfterBoundary c d s i)

/-- A **splitting** of a complex `d` over `ZMod 2`: maps `f`, `g` of degree `0` to and from cells
`h i` with no boundary, and `s` of degree `+1`, with `f g = 1`, `∂ g = 0`, `f ∂ = 0` and
`∂ s + s ∂ = 1 + g f`. -/
def IsSplitting (c : ℕ → ℕ) (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2))
    (h : ℕ → ℕ) (f : ∀ i, Matrix (Fin (h i)) (Fin (c i)) (ZMod 2))
    (g : ∀ i, Matrix (Fin (c i)) (Fin (h i)) (ZMod 2))
    (s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)) : Prop :=
  (∀ i, f i * g i = 1) ∧ (∀ i, d i * g (i + 1) = 0) ∧ (∀ i, f i * d i = 0) ∧
    ∀ i, d i * s i + raiseAfterBoundary c d s i = 1 + g i * f i

/-- **Every complex over `ZMod 2` has a splitting.** -/
theorem exists_splitting (c : ℕ → ℕ)
    (d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2)) (hdd : ∀ i, d i * d (i + 1) = 0) :
    ∃ h f g s, IsSplitting c d h f g s := by
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_contraction c d hdd
  have hX : ∀ i,
      (d i * s i + raiseAfterBoundary c d s i) * (d i * s i + raiseAfterBoundary c d s i) =
        d i * s i + raiseAfterBoundary c d s i := by
    intro i
    cases i with
    | zero =>
      simp only [raiseAfterBoundary, add_zero]
      rw [← Matrix.mul_assoc, hs1]
    | succ j =>
      have t1 : d (j + 1) * s (j + 1) * (d (j + 1) * s (j + 1)) = d (j + 1) * s (j + 1) := by
        rw [← Matrix.mul_assoc, hs1]
      have t2 : d (j + 1) * s (j + 1) * (s j * d j) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.mul_assoc (d (j + 1)), hs3, Matrix.mul_zero, Matrix.zero_mul]
      have t3 : s j * d j * (d (j + 1) * s (j + 1)) = 0 := by
        rw [← Matrix.mul_assoc, Matrix.mul_assoc (s j), hdd, Matrix.mul_zero, Matrix.zero_mul]
      have t4 : s j * d j * (s j * d j) = s j * d j := by
        rw [← Matrix.mul_assoc, hs2]
      simp only [raiseAfterBoundary, Matrix.add_mul, Matrix.mul_add, t1, t2, t3, t4, add_zero,
        zero_add]
  have hdP : ∀ i, d i * contractionProjection c d s (i + 1) = 0 := by
    intro i
    simp only [contractionProjection, raiseAfterBoundary, Matrix.mul_add, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hdd, Matrix.zero_mul, zero_add, ← Matrix.mul_assoc, hs1,
      matrix_add_self_eq_zero]
  have hPd : ∀ i, contractionProjection c d s i * d i = 0 := by
    intro i
    cases i with
    | zero =>
      simp only [contractionProjection, raiseAfterBoundary, add_zero, Matrix.add_mul,
        Matrix.one_mul, hs1, matrix_add_self_eq_zero]
    | succ j =>
      simp only [contractionProjection, raiseAfterBoundary, Matrix.add_mul, Matrix.one_mul, hs1]
      rw [Matrix.mul_assoc (s j), hdd, Matrix.mul_zero, add_zero, matrix_add_self_eq_zero]
  have hfac : ∀ i, ∃ (h : ℕ) (f : Matrix (Fin h) (Fin (c i)) (ZMod 2))
      (g : Matrix (Fin (c i)) (Fin h) (ZMod 2)),
        f * g = 1 ∧ g * f = contractionProjection c d s i :=
    fun i => exists_factor_of_idempotent _ (one_add_mul_one_add_of_mul_self (hX i))
  choose h f g hfg hgf using hfac
  refine ⟨h, f, g, s, hfg, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have hg : g (i + 1) = contractionProjection c d s (i + 1) * g (i + 1) := by
      rw [← hgf, Matrix.mul_assoc, hfg, Matrix.mul_one]
    rw [hg, ← Matrix.mul_assoc, hdP, Matrix.zero_mul]
  · have hf : f i = f i * contractionProjection c d s i := by
      rw [← hgf, ← Matrix.mul_assoc, hfg, Matrix.one_mul]
    rw [hf, Matrix.mul_assoc, hPd, Matrix.mul_zero]
  · rw [hgf, contractionProjection, ← add_assoc, matrix_add_self_eq_zero, zero_add]

/-- A splitting gives the identities of a deformation retract on the cells of degree below `N`,
when the complex has no boundary out of degree `N - 1` or above. -/
theorem allCells_identities_of_splitting {c : ℕ → ℕ}
    {d : ∀ i, Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2)} {h : ℕ → ℕ}
    {f : ∀ i, Matrix (Fin (h i)) (Fin (c i)) (ZMod 2)}
    {g : ∀ i, Matrix (Fin (c i)) (Fin (h i)) (ZMod 2)}
    {s : ∀ i, Matrix (Fin (c (i + 1))) (Fin (c i)) (ZMod 2)} (hs : IsSplitting c d h f g s) (N : ℕ)
    (hN : ∀ a, N ≤ a + 1 → d a = 0) :
    allBlock f N * allBlock g N = 1 ∧ allBoundary c d N * allBlock g N = 0 ∧
      allBlock f N * allBoundary c d N = 0 ∧
      allBoundary c d N * allRaise c s N + allRaise c s N * allBoundary c d N =
        1 + allBlock g N * allBlock f N := by
  obtain ⟨hfg, hdg, hfd, hds⟩ := hs
  refine ⟨?_, allBoundary_mul_allBlock d g hdg, allBlock_mul_allBoundary d f hfd, ?_⟩
  · rw [allBlock_mul_allBlock, show (fun i => f i * g i) = fun i => 1 from funext hfg, allBlock_one]
  · rw [allBoundary_mul_allRaise d s hN, allRaise_mul_allBoundary, allBlock_add,
      allBlock_mul_allBlock, ← allBlock_one, allBlock_add]
    exact congrArg (allBlock · N) (funext hds)

/-- **The tensor product of two deformation retracts is one**: with `∂ = ∂ ⊗ 1 + 1 ⊗ ∂'`,
`F = f ⊗ f'`, `G = g ⊗ g'` and `S = s ⊗ 1 + g f ⊗ s'`, every sign `1` over `ZMod 2`. -/
theorem kronecker_retract {ι ι' κ κ' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {d S : Matrix ι ι (ZMod 2)} {F : Matrix κ ι (ZMod 2)} {G : Matrix ι κ (ZMod 2)}
    {d' S' : Matrix ι' ι' (ZMod 2)} {F' : Matrix κ' ι' (ZMod 2)} {G' : Matrix ι' κ' (ZMod 2)}
    (hdd : d * d = 0) (hFG : F * G = 1) (hdG : d * G = 0) (hFd : F * d = 0)
    (hdS : d * S + S * d = 1 + G * F) (hdd' : d' * d' = 0) (hFG' : F' * G' = 1)
    (hdG' : d' * G' = 0) (hFd' : F' * d' = 0) (hdS' : d' * S' + S' * d' = 1 + G' * F') :
    (d ⊗ₖ 1 + 1 ⊗ₖ d') * (d ⊗ₖ 1 + 1 ⊗ₖ d') = 0 ∧ (F ⊗ₖ F') * (G ⊗ₖ G') = 1 ∧
      (d ⊗ₖ 1 + 1 ⊗ₖ d') * (G ⊗ₖ G') = 0 ∧ (F ⊗ₖ F') * (d ⊗ₖ 1 + 1 ⊗ₖ d') = 0 ∧
      (d ⊗ₖ 1 + 1 ⊗ₖ d') * (S ⊗ₖ 1 + (G * F) ⊗ₖ S') +
          (S ⊗ₖ 1 + (G * F) ⊗ₖ S') * (d ⊗ₖ 1 + 1 ⊗ₖ d') =
        1 + (G ⊗ₖ G') * (F ⊗ₖ F') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      hdd, hdd', zero_kronecker, kronecker_zero, zero_add, add_zero]
    exact matrix_add_self_eq_zero _
  · rw [← mul_kronecker_mul, hFG, hFG', one_kronecker_one]
  · simp only [Matrix.add_mul, ← mul_kronecker_mul, Matrix.one_mul, hdG, hdG', zero_kronecker,
      kronecker_zero, add_zero]
  · simp only [Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one, hFd, hFd', zero_kronecker,
      kronecker_zero, add_zero]
  · have e1 : d * (G * F) = 0 := by rw [← Matrix.mul_assoc, hdG, Matrix.zero_mul]
    have e2 : G * F * d = 0 := by rw [Matrix.mul_assoc, hFd, Matrix.mul_zero]
    have k1 : (d * S) ⊗ₖ (1 : Matrix ι' ι' (ZMod 2)) + (S * d) ⊗ₖ 1 = (1 + G * F) ⊗ₖ 1 := by
      rw [← add_kronecker, hdS]
    have k2 : (G * F) ⊗ₖ (d' * S') + (G * F) ⊗ₖ (S' * d') = (G * F) ⊗ₖ (1 + G' * F') := by
      rw [← kronecker_add, hdS']
    calc (d ⊗ₖ 1 + 1 ⊗ₖ d') * (S ⊗ₖ 1 + (G * F) ⊗ₖ S') +
          (S ⊗ₖ 1 + (G * F) ⊗ₖ S') * (d ⊗ₖ 1 + 1 ⊗ₖ d')
        = ((d * S) ⊗ₖ 1 + (S * d) ⊗ₖ 1) + ((G * F) ⊗ₖ (d' * S') + (G * F) ⊗ₖ (S' * d')) +
            (S ⊗ₖ d' + S ⊗ₖ d') := by
          simp only [Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one,
            Matrix.one_mul, e1, e2, zero_kronecker, add_zero, zero_add]
          abel
      _ = 1 + (G * F) ⊗ₖ (G' * F') + ((G * F) ⊗ₖ 1 + (G * F) ⊗ₖ 1) := by
          rw [k1, k2, matrix_add_self_eq_zero, add_zero, add_kronecker, kronecker_add,
            one_kronecker_one]
          abel
      _ = 1 + (G ⊗ₖ G') * (F ⊗ₖ F') := by
          rw [matrix_add_self_eq_zero, add_zero, ← mul_kronecker_mul]

/-- The cells of degree `k` among the cells of degree below `N`. -/
def degreeEmbedding (c : ℕ → ℕ) (N k : ℕ) (hk : k < N) (σ : Fin (c k)) : AllCells c N :=
  ⟨⟨k, hk⟩, σ⟩

/-- `degreeEmbedding` is injective. -/
theorem degreeEmbedding_injective (c : ℕ → ℕ) (N k : ℕ) (hk : k < N) :
    Function.Injective (degreeEmbedding c N k hk) := fun _ _ h =>
  Fin.ext (allCells_mk_eq_mk_iff.1 h).2

/-- `degreeEmbedding` is onto the cells of degree `k`. -/
theorem exists_degreeEmbedding_eq_iff (c : ℕ → ℕ) (N k : ℕ) (hk : k < N) (x : AllCells c N) :
    (∃ σ, degreeEmbedding c N k hk σ = x) ↔ (x.1 : ℕ) = k := by
  constructor
  · rintro ⟨σ, rfl⟩
    rfl
  · obtain ⟨⟨i, hi⟩, σ⟩ := x
    rintro (rfl : i = k)
    exact ⟨σ, rfl⟩

/-- The pairs of cells of total degree `k` among the pairs of cells of degree below `N`. -/
def pairEmbedding (c c' : ℕ → ℕ) (N k : ℕ) (hk : k < N)
    (x : Σ p : Fin (k + 1), Fin (c p) × Fin (c' (k - p))) : AllCells c N × AllCells c' N :=
  (⟨⟨x.1, by have := x.1.isLt; omega⟩, x.2.1⟩, ⟨⟨k - x.1, by omega⟩, x.2.2⟩)

/-- `pairEmbedding` is injective. -/
theorem pairEmbedding_injective (c c' : ℕ → ℕ) (N k : ℕ) (hk : k < N) :
    Function.Injective (pairEmbedding c c' N k hk) := by
  rintro ⟨p, σ, τ⟩ ⟨q, σ', τ'⟩ h
  simp only [pairEmbedding, Prod.mk.injEq, allCells_mk_eq_mk_iff] at h
  obtain ⟨⟨hpq, hσ⟩, -, hτ⟩ := h
  obtain rfl : p = q := Fin.ext hpq
  obtain rfl : σ = σ' := Fin.ext hσ
  obtain rfl : τ = τ' := Fin.ext hτ
  rfl

/-- `pairEmbedding` is onto the pairs of total degree `k`. -/
theorem exists_pairEmbedding_eq_iff (c c' : ℕ → ℕ) (N k : ℕ) (hk : k < N)
    (z : AllCells c N × AllCells c' N) :
    (∃ x, pairEmbedding c c' N k hk x = z) ↔ (z.1.1 : ℕ) + z.2.1 = k := by
  constructor
  · rintro ⟨⟨p, σ, τ⟩, rfl⟩
    simp only [pairEmbedding]
    have := p.isLt
    omega
  · obtain ⟨⟨⟨i, hi⟩, σ⟩, ⟨⟨j, hj⟩, τ⟩⟩ := z
    intro hij
    simp only at hij
    refine ⟨⟨⟨i, by omega⟩, σ, Fin.cast (congrArg c' (by omega : j = k - i)) τ⟩, ?_⟩
    simp only [pairEmbedding, Prod.mk.injEq, allCells_mk_eq_mk_iff, Fin.val_cast]
    exact ⟨trivial, by omega, trivial⟩

end FTQCLib.CSS.Kunneth

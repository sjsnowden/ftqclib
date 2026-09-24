/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.SiegelGeneration

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The explicit Weil representation of `Sp(2n, 𝔽_q)`, at every rank

`SiegelGeneration` proved `Sp = ⟨shears, w⟩` for the isometry group of the split form on
`W = (ι→F)×(ι→F)`. This file transports that onto the `Heis` side, where the Weil operators live,
closing the explicit route at every rank:

* `inWeilGroup_of_isSymplectic` — **every symplectic `Heis` map is a word in `Heis.shear` and
  `Heis.fourierMap`**, at every rank;
* `hasWeilOperator_of_isSymplectic_explicit` — hence every symplectic map has a Weil operator; the
  **proof** constructs it as a word in chirps and DFTs rather than extracting it from an existence
  proof. (The statement itself is the bare existential `HasWeilOperator` — proof irrelevance means
  the word structure is a property of this file's route, not of the proposition.)

The transport is the vector part `vecFun g (p,m) = ((g ⟨p,m,0⟩).pos, (g ⟨p,m,0⟩).mom)`. Three facts
make it work:

* a symplectic `g` **ignores the centre coordinate** on positions and momenta (`heis_apply_cen`:
  `g ⟨p,m,c⟩ = central c · g ⟨p,m,0⟩`, because `g` fixes the centre), so `vecFun` is well behaved and
  composes;
* a symplectic `g` **is determined by its vector part** (`eq_of_vecFun_eq`) — it fixes the centre, so
  there is nothing else to know;
* `InWeilGroup` is **closed under inverses** (`InWeilGroup.exists_inv`) — needed because the Siegel
  statement is about a `Subgroup.closure`, whose induction principle has an `inv` case. The
  inductive `InWeilGroup` has no `inv` constructor, but shears invert by `S ↦ −S` and `w` by `w³`.
-/

namespace ECCLib.WeilComplete

open ECCLib.Heisenberg ECCLib.Siegel

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]

/-! ### The vector part -/

/-- The vector part of a `Heis` map: its action on positions and momenta at centre `0`. -/
def vecFun (g : Heis F ι → Heis F ι) (x : W F ι) : W F ι :=
  ((g ⟨x.1, x.2, 0⟩).pos, (g ⟨x.1, x.2, 0⟩).mom)

/-- **A symplectic map only shifts the centre**: `g ⟨p,m,c⟩ = central c · g ⟨p,m,0⟩`. Because `g`
fixes the centre (`map_central`), the position and momentum of `g ⟨p,m,c⟩` do not depend on `c`. -/
theorem heis_apply_cen {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (p m : ι → F) (c : F) :
    g ⟨p, m, c⟩ = Heis.central c * g ⟨p, m, 0⟩ := by
  have hfac : (⟨p, m, c⟩ : Heis F ι) = Heis.central c * ⟨p, m, 0⟩ := by
    rw [Heis.central_mul, add_zero]
  rw [hfac, Heis.isSymplectic_map_mul hg, hg.map_central]

theorem pos_indep {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (p m : ι → F) (c : F) :
    (g ⟨p, m, c⟩).pos = (g ⟨p, m, 0⟩).pos := by
  rw [heis_apply_cen hg, Heis.central_mul]

theorem mom_indep {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (p m : ι → F) (c : F) :
    (g ⟨p, m, c⟩).mom = (g ⟨p, m, 0⟩).mom := by
  rw [heis_apply_cen hg, Heis.central_mul]

/-- **A symplectic map is determined by its vector part** — it fixes the centre, so there is nothing
else to know. -/
theorem eq_of_vecFun_eq {g h : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g)
    (hh : Heis.IsSymplectic h) (hv : ∀ x, vecFun g x = vecFun h x) : g = h := by
  funext z
  have hz : z = (⟨z.pos, z.mom, z.cen⟩ : Heis F ι) := rfl
  rw [hz, heis_apply_cen hg, heis_apply_cen hh]
  have hvz := hv (z.pos, z.mom)
  refine congrArg (fun w => Heis.central z.cen * w) (Heis.ext ?_ ?_ ?_)
  · exact congrArg Prod.fst hvz
  · exact congrArg Prod.snd hvz
  · rw [hg.map_cen, hh.map_cen]

/-! ### `InWeilGroup` is a group -/

theorem isSymplectic_comp {g h : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g)
    (hh : Heis.IsSymplectic h) : Heis.IsSymplectic (g ∘ h) where
  map_pos x y := by
    change (g (h (x * y))).pos = (g (h x)).pos + (g (h y)).pos
    rw [Heis.isSymplectic_map_mul hh, hg.map_pos]
  map_mom x y := by
    change (g (h (x * y))).mom = (g (h x)).mom + (g (h y)).mom
    rw [Heis.isSymplectic_map_mul hh, hg.map_mom]
  map_cen x := by
    change (g (h x)).cen = x.cen
    rw [hg.map_cen, hh.map_cen]
  map_symp x y := by
    change Heis.symp (g (h x)) (g (h y)) = Heis.symp x y
    rw [hg.map_symp, hh.map_symp]

theorem isSymplectic_of_inWeilGroup {g : Heis F ι → Heis F ι} (hg : InWeilGroup g) :
    Heis.IsSymplectic g := by
  induction hg with
  | shear hS => exact Heis.isSymplectic_shear hS
  | fourier => exact Heis.isSymplectic_fourierMap
  | comp _ _ ihg ihh => exact isSymplectic_comp ihg ihh

/-- `w⁴ = id`. -/
theorem fourierMap_four (x : Heis F ι) :
    Heis.fourierMap (Heis.fourierMap (Heis.fourierMap (Heis.fourierMap x))) = x := by
  refine Heis.ext ?_ ?_ rfl <;> simp [Heis.fourierMap]

/-- The negation of a symmetric map is symmetric. -/
theorem isSymmetricMap_neg {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S) :
    IsSymmetricMap (fun z => -(S z)) where
  map_add a b := by rw [hS.map_add]; abel
  symm a b := by
    rw [ECCLib.Heisenberg.pairing_neg_left, ECCLib.Heisenberg.pairing_neg_left,
      hS.symm a b]

/-- **`InWeilGroup` is closed under inverses.** The inductive has no `inv` constructor; shears invert
by `S ↦ −S`, `w` by `w³`, and composites by reversing. Needed for the `Subgroup.closure` induction. -/
theorem InWeilGroup.exists_inv {g : Heis F ι → Heis F ι} (hg : InWeilGroup g) :
    ∃ g' : Heis F ι → Heis F ι, InWeilGroup g' ∧ (∀ x, g' (g x) = x) ∧ (∀ x, g (g' x) = x) := by
  induction hg with
  | @shear S hS =>
    refine ⟨Heis.shear (fun z => -(S z)), InWeilGroup.shear (isSymmetricMap_neg hS), ?_, ?_⟩
    · intro x
      refine Heis.ext rfl ?_ rfl
      change x.mom - S x.pos - -(S x.pos) = x.mom
      abel
    · intro x
      refine Heis.ext rfl ?_ rfl
      change x.mom - -(S x.pos) - S x.pos = x.mom
      abel
  | fourier =>
    refine ⟨Heis.fourierMap ∘ Heis.fourierMap ∘ Heis.fourierMap,
      InWeilGroup.comp InWeilGroup.fourier (InWeilGroup.comp InWeilGroup.fourier
        InWeilGroup.fourier), ?_, ?_⟩
    · intro x
      change Heis.fourierMap (Heis.fourierMap (Heis.fourierMap (Heis.fourierMap x))) = x
      exact fourierMap_four x
    · intro x
      change Heis.fourierMap (Heis.fourierMap (Heis.fourierMap (Heis.fourierMap x))) = x
      exact fourierMap_four x
  | @comp g h _ _ ihg ihh =>
    obtain ⟨g', hg', hgl, hgr⟩ := ihg
    obtain ⟨h', hh', hhl, hhr⟩ := ihh
    refine ⟨h' ∘ g', InWeilGroup.comp hh' hg', ?_, ?_⟩
    · intro x
      change h' (g' (g (h x))) = x
      rw [hgl, hhl]
    · intro x
      change g (h (h' (g' x))) = x
      rw [hhr, hgr]

/-! ### `vecFun` on the generators, and under composition -/

theorem vecFun_shear (S : (ι → F) →ₗ[F] (ι → F)) (x : W F ι) :
    vecFun (Heis.shear ⇑S) x = momShear S x := rfl

theorem vecFun_fourier (x : W F ι) :
    vecFun (Heis.fourierMap (F := F) (ι := ι)) x = weyl x := rfl

theorem vecFun_comp {g h : Heis F ι → Heis F ι} (hh : Heis.IsSymplectic h) (x : W F ι) :
    vecFun (g ∘ h) x = vecFun g (vecFun h x) := by
  have hc : (h ⟨x.1, x.2, 0⟩ : Heis F ι)
      = ⟨(h ⟨x.1, x.2, 0⟩).pos, (h ⟨x.1, x.2, 0⟩).mom, 0⟩ := by
    refine Heis.ext rfl rfl ?_
    rw [hh.map_cen]
  unfold vecFun
  rw [← hc]
  rfl

theorem isSymmetricMap_of_isSymLin {S : (ι → F) →ₗ[F] (ι → F)} (hS : IsSymLin S) :
    IsSymmetricMap ⇑S where
  map_add a b := by rw [map_add]
  symm a b := hS a b

/-- **The missing bridge direction**: a raw `IsSymmetricMap` is automatically `F`-linear —
additivity is a field of the structure, and homogeneity is *forced* by nondegeneracy of the
pairing (`⟨S(c•a) − c·S a, b⟩ = 0` for every `b`, via two applications of symmetry). Together with
`isSymmetricMap_of_isSymLin` this closes the raw ↔ bundled loop: the shear/chirp API's raw
symmetric maps and `SiegelGeneration`'s `IsSymLin` linear maps are the same objects, so a consumer
holding a `LinearMap`/`Matrix` need not unbundle by hand. -/
def symmetricMapToLinear {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S) :
    (ι → F) →ₗ[F] (ι → F) where
  toFun := S
  map_add' := hS.map_add
  map_smul' c a := by
    have hsmul_l : ∀ b y : ι → F, pairing (c • b) y = c * pairing b y := by
      intro b y
      simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hsmul_r : ∀ b y : ι → F, pairing b (c • y) = c * pairing b y := by
      intro b y
      simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
    have key : ∀ b, pairing (S (c • a) - c • S a) b = 0 := by
      intro b
      have h1 : pairing (S (c • a)) b = c * pairing (S a) b := by
        rw [hS.symm, hsmul_r, hS.symm]
      rw [pairing_sub_left, h1, hsmul_l, sub_self]
    have h0 := eq_zero_of_pairing_left _ key
    simpa [sub_eq_zero] using h0

@[simp] theorem symmetricMapToLinear_apply {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S)
    (a : ι → F) : symmetricMapToLinear hS a = S a := rfl

/-- The bundled form of a symmetric map is `IsSymLin` — the round trip closes. -/
theorem isSymLin_symmetricMapToLinear {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S) :
    IsSymLin (symmetricMapToLinear hS) := fun x y => hS.symm x y

/-! ### The vector part of a symplectic map, bundled -/

theorem vecFun_add {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (x y : W F ι) :
    vecFun g (x + y) = vecFun g x + vecFun g y := by
  have hmul : (⟨x.1, x.2, 0⟩ : Heis F ι) * ⟨y.1, y.2, 0⟩
      = ⟨x.1 + y.1, x.2 + y.2, (2 : F)⁻¹ * Heis.symp ⟨x.1, x.2, 0⟩ ⟨y.1, y.2, 0⟩⟩ := by
    refine Heis.ext rfl rfl ?_
    change (0 : F) + 0 + (2 : F)⁻¹ * Heis.symp _ _ = (2 : F)⁻¹ * Heis.symp _ _
    ring
  refine Prod.ext ?_ ?_
  · change (g ⟨x.1 + y.1, x.2 + y.2, 0⟩).pos = (g ⟨x.1, x.2, 0⟩).pos + (g ⟨y.1, y.2, 0⟩).pos
    rw [← pos_indep hg (x.1 + y.1) (x.2 + y.2) ((2 : F)⁻¹ * Heis.symp ⟨x.1, x.2, 0⟩ ⟨y.1, y.2, 0⟩),
      ← hmul, hg.map_pos]
  · change (g ⟨x.1 + y.1, x.2 + y.2, 0⟩).mom = (g ⟨x.1, x.2, 0⟩).mom + (g ⟨y.1, y.2, 0⟩).mom
    rw [← mom_indep hg (x.1 + y.1) (x.2 + y.2) ((2 : F)⁻¹ * Heis.symp ⟨x.1, x.2, 0⟩ ⟨y.1, y.2, 0⟩),
      ← hmul, hg.map_mom]

theorem vecFun_smul {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (c : F) (x : W F ι) :
    vecFun g (c • x) = c • vecFun g x := by
  have hv : (⟨(c • x).1, (c • x).2, 0⟩ : Heis F ι) = Heis.vscale c ⟨x.1, x.2, 0⟩ := rfl
  refine Prod.ext ?_ ?_
  · change (g ⟨(c • x).1, (c • x).2, 0⟩).pos = c • (g ⟨x.1, x.2, 0⟩).pos
    rw [hv, hg.map_vscale, Heis.vscale_pos]
    rfl
  · change (g ⟨(c • x).1, (c • x).2, 0⟩).mom = c • (g ⟨x.1, x.2, 0⟩).mom
    rw [hv, hg.map_vscale, Heis.vscale_mom]
    rfl

/-- The vector part of a symplectic map, as a linear map. -/
def vecLin {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) : W F ι →ₗ[F] W F ι where
  toFun := vecFun g
  map_add' := vecFun_add hg
  map_smul' := vecFun_smul hg

@[simp] theorem vecLin_apply {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (x : W F ι) :
    vecLin hg x = vecFun g x := rfl

theorem vecFun_bijective {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    Function.Bijective (vecFun g) := by
  constructor
  · intro x y hxy
    have hpos : (g ⟨x.1, x.2, 0⟩).pos = (g ⟨y.1, y.2, 0⟩).pos := congrArg Prod.fst hxy
    have hmom : (g ⟨x.1, x.2, 0⟩).mom = (g ⟨y.1, y.2, 0⟩).mom := congrArg Prod.snd hxy
    have hcen : (g ⟨x.1, x.2, 0⟩).cen = (g ⟨y.1, y.2, 0⟩).cen := by rw [hg.map_cen, hg.map_cen]
    have := hg.injective (Heis.ext hpos hmom hcen)
    exact Prod.ext (congrArg Heis.pos this) (congrArg Heis.mom this)
  · intro w
    obtain ⟨z, hz⟩ := hg.bijective.surjective (⟨w.1, w.2, 0⟩ : Heis F ι)
    have hzc : z.cen = 0 := by
      have := hg.map_cen z
      rw [hz] at this
      exact this.symm
    refine ⟨(z.pos, z.mom), ?_⟩
    have hze : (⟨z.pos, z.mom, 0⟩ : Heis F ι) = z := by
      refine Heis.ext rfl rfl ?_
      rw [hzc]
    unfold vecFun
    rw [hze, hz]

/-- The vector part of a symplectic map, as a linear automorphism of `W`. -/
noncomputable def vecEquiv {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    W F ι ≃ₗ[F] W F ι :=
  LinearEquiv.ofBijective (vecLin hg) (vecFun_bijective hg)

@[simp] theorem vecEquiv_apply {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (x : W F ι) :
    vecEquiv hg x = vecFun g x := rfl

/-- The vector part of a symplectic `Heis` map is an isometry of `ω`. -/
theorem vecEquiv_isSymplectic {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    SpGen.IsSymplecticEquiv (omega (F := F) (ι := ι)) (vecEquiv hg) := by
  intro x y
  have h := hg.map_symp ⟨x.1, x.2, 0⟩ ⟨y.1, y.2, 0⟩
  exact h

/-! ### Transporting the Siegel word to `Heis` -/

/-- Every element of `⟨shears, w⟩` on `W` is the vector part of an `InWeilGroup` word on `Heis`. -/
theorem exists_inWeilGroup_of_mem_closure {e : W F ι ≃ₗ[F] W F ι}
    (he : e ∈ Subgroup.closure (gens (F := F) (ι := ι))) :
    ∃ h : Heis F ι → Heis F ι, InWeilGroup h ∧ ∀ x, vecFun h x = e x := by
  induction he using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨S, hS, rfl⟩ | rfl
    · exact ⟨Heis.shear ⇑S, InWeilGroup.shear (isSymmetricMap_of_isSymLin hS), vecFun_shear S⟩
    · exact ⟨Heis.fourierMap, InWeilGroup.fourier, vecFun_fourier⟩
  | one =>
    refine ⟨Heis.shear ⇑(0 : (ι → F) →ₗ[F] (ι → F)),
      InWeilGroup.shear (isSymmetricMap_of_isSymLin (by intro x y; simp)), fun x => ?_⟩
    change ((⟨x.1, x.2 - (0 : (ι → F) →ₗ[F] (ι → F)) x.1, 0⟩ : Heis F ι).pos,
      (⟨x.1, x.2 - (0 : (ι → F) →ₗ[F] (ι → F)) x.1, 0⟩ : Heis F ι).mom) = x
    simp
  | mul a b _ _ iha ihb =>
    obtain ⟨ha, hIna, hva⟩ := iha
    obtain ⟨hb, hInb, hvb⟩ := ihb
    refine ⟨ha ∘ hb, InWeilGroup.comp hIna hInb, fun x => ?_⟩
    rw [vecFun_comp (isSymplectic_of_inWeilGroup hInb), hvb, hva]
    rfl
  | inv a _ iha =>
    obtain ⟨h, hIn, hveq⟩ := iha
    obtain ⟨h', hIn', _, hr⟩ := InWeilGroup.exists_inv hIn
    refine ⟨h', hIn', fun x => ?_⟩
    have hid : vecFun h (vecFun h' x) = x := by
      rw [← vecFun_comp (isSymplectic_of_inWeilGroup hIn')]
      unfold vecFun
      rw [Function.comp_apply, hr]
    have h1 : a (vecFun h' x) = x := by rw [← hveq]; exact hid
    have h2 := congrArg (fun z => (a⁻¹ : W F ι ≃ₗ[F] W F ι) z) h1
    simpa using h2

/-! ### The main theorems -/

/-- **Every symplectic map is a word in the shears and `w`, at every rank.** The explicit route's
generation statement, on the `Heis` side where the Weil operators live. -/
theorem inWeilGroup_of_isSymplectic {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    InWeilGroup g := by
  have hmem : vecEquiv hg ∈ Subgroup.closure (gens (F := F) (ι := ι)) :=
    isSymplectic_iff_mem_closure.mp (vecEquiv_isSymplectic hg)
  obtain ⟨h, hIn, hveq⟩ := exists_inWeilGroup_of_mem_closure hmem
  have hgh : g = h :=
    eq_of_vecFun_eq hg (isSymplectic_of_inWeilGroup hIn) (fun x => (hveq x).symm)
  rw [hgh]
  exact hIn

/-- **The explicit route to the Weil operators, at every rank.** Every symplectic map has a Weil
operator. The statement is the bare existential `HasWeilOperator` — identical to the Stone–von
Neumann route's conclusion (`hasWeilOperator_of_isSymplectic_svn`); what is explicit is the
**proof**: it writes the map as a word in the shears and `w` (`inWeilGroup_of_isSymplectic`) and
assigns each letter its operator (chirps and DFTs), rather than extracting an operator from
Stone–von Neumann. By proof irrelevance the word structure of the witness is not asserted by, or
recoverable from, the proposition; pinning it down would need a predicate on units generated by
`chirpUnit` and `fourierUnit`, which is not defined here. -/
theorem hasWeilOperator_of_isSymplectic_explicit (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) : HasWeilOperator h2 ψ g :=
  hasWeilOperator_of_inWeilGroup h2 hψ (inWeilGroup_of_isSymplectic hg)

end ECCLib.WeilComplete

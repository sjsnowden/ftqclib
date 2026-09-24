/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Heisenberg

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# Classification and generation for the symplectic action

Two results, each in the form in which it is provable here.

**Classification** (`Heis.IsSymplectic.map_vscale`): an `IsSymplectic` map is automatically
`F`-linear on the vector part. The predicate only asks for additivity and preservation of the form,
but the form is nondegenerate and the field is finite, so additive + form-preserving forces
injective, hence bijective, hence scalar-natural. The "refactor `IsSymplectic` into a genuine
`Sp(2n,𝔽_q)`" item dissolves: the predicate already carves out exactly the linear symplectic
automorphisms.

**Generation at rank one** (`hasWeilOperator_of_isSymplectic`): over a one-element index type,
every symplectic map is a `2×2` matrix `mob a b c d` with `ad − bc = 1` (classification), every such
matrix is a word in the shears and the Weyl element (the three-shear Bruhat-cell identity
`[[a,b],[c,d]] = U((a−1)/c)·L(c)·U((d−1)/c)` for `c ≠ 0`, with a `w`-pivot for `c = 0`), and every
word has a Weil operator (`hasWeilOperator_shear`, `hasWeilOperator_fourierMap`,
`HasWeilOperator.comp`). So **the Weil representation of `Sp(2, 𝔽_q)` is complete**: every element
has an explicit intertwiner.

General rank stays open: `Sp(2n, 𝔽_q) = ⟨Siegel unipotents⟩` (`Ep = Sp`) is classical but a
formalization project of its own. `inWeilGroup_mob` holds at every rank — it is the *diagonal*
`SL₂ ≤ Sp(2n)` — but at rank `≥ 2` it is not all of `Sp`.
-/

namespace ECCLib.Heisenberg

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-! ### Nondegeneracy of the pairing and of `symp` -/

section Nondegeneracy

variable [DecidableEq ι]

/-- Nondegeneracy in the first slot: a vector pairing to zero with everything is zero. -/
theorem eq_zero_of_pairing_left (m : ι → F) (h : ∀ p : ι → F, pairing m p = 0) : m = 0 := by
  funext i
  have hi := h (Pi.single i 1)
  unfold pairing at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa using hi
  · intro j _ hj
    simp [hj]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Separation: two vectors with the same pairings agree. -/
theorem pairing_left_cancel {m m' : ι → F} (h : ∀ p : ι → F, pairing m p = pairing m' p) :
    m = m' := by
  have hz : ∀ p : ι → F, pairing (m - m') p = 0 := by
    intro p
    rw [pairing_sub_left, h p, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pairing_left (m - m') hz)

/-- Separation in the second slot (via symmetry). -/
theorem pairing_right_cancel {p p' : ι → F} (h : ∀ b : ι → F, pairing b p = pairing b p') :
    p = p' := by
  refine pairing_left_cancel fun b => ?_
  rw [pairing_symm, h b, pairing_symm]

/-- **`symp` separates**: two elements with the same symplectic pairings against everything have the
same position and momentum. (Not the same centre — `symp` never sees it.) -/
theorem symp_left_cancel {u v : Heis F ι} (h : ∀ z : Heis F ι, Heis.symp u z = Heis.symp v z) :
    u.pos = v.pos ∧ u.mom = v.mom := by
  constructor
  · refine pairing_right_cancel fun b => ?_
    have hb := h ⟨0, b, 0⟩
    simpa only [Heis.symp, pairing_zero_right, sub_zero] using hb
  · refine pairing_left_cancel fun p => ?_
    have hp := h ⟨p, 0, 0⟩
    simpa only [Heis.symp, pairing_zero_left, zero_sub, neg_inj] using hp

end Nondegeneracy

/-! ### Classification: `IsSymplectic` maps are `F`-linear -/

section Classification

variable [DecidableEq ι]

instance [Fintype F] : Finite (Heis F ι) :=
  Finite.of_equiv ((ι → F) × (ι → F) × F)
    ⟨fun p => ⟨p.1, p.2.1, p.2.2⟩, fun x => (x.pos, x.mom, x.cen), fun _ => rfl, fun _ => rfl⟩

/-- An `IsSymplectic` map is injective: the form is nondegenerate and preserved, and the centre
coordinate is carried along untouched. -/
theorem Heis.IsSymplectic.injective {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    Function.Injective g := by
  intro x x' hxx'
  have hsym : ∀ y, Heis.symp x y = Heis.symp x' y := fun y => by
    rw [← hg.map_symp x y, hxx', hg.map_symp x' y]
  obtain ⟨hpos, hmom⟩ := symp_left_cancel hsym
  have hcen : x.cen = x'.cen := by rw [← hg.map_cen x, hxx', hg.map_cen x']
  exact Heis.ext hpos hmom hcen

/-- Over a finite field an `IsSymplectic` map is bijective. -/
theorem Heis.IsSymplectic.bijective [Fintype F] {g : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) : Function.Bijective g :=
  Finite.injective_iff_bijective.mp hg.injective

namespace Heis

/-- Scale the vector part by `c`, centre untouched. -/
def vscale (c : F) (x : Heis F ι) : Heis F ι :=
  ⟨fun i => c * x.pos i, fun i => c * x.mom i, x.cen⟩

@[simp] lemma vscale_pos (c : F) (x : Heis F ι) :
    (vscale c x).pos = fun i => c * x.pos i := rfl
@[simp] lemma vscale_mom (c : F) (x : Heis F ι) :
    (vscale c x).mom = fun i => c * x.mom i := rfl
@[simp] lemma vscale_cen (c : F) (x : Heis F ι) : (vscale c x).cen = x.cen := rfl

end Heis

lemma pairing_mul_left (c : F) (b y : ι → F) :
    pairing (fun i => c * b i) y = c * pairing b y := by
  unfold pairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma pairing_mul_right (c : F) (b y : ι → F) :
    pairing b (fun i => c * y i) = c * pairing b y := by
  unfold pairing
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma Heis.symp_vscale_left (c : F) (x y : Heis F ι) :
    Heis.symp (Heis.vscale c x) y = c * Heis.symp x y := by
  unfold Heis.symp
  rw [Heis.vscale_pos, Heis.vscale_mom, pairing_mul_right, pairing_mul_left]
  ring

/-- **The linearity theorem**: an `IsSymplectic` map is scalar-natural on the vector part. Additivity
is in the definition; this is the multiplicative half of `F`-linearity, and it is *forced*:
`ω(g(c·x), g(y)) = ω(c·x, y) = c·ω(x, y) = c·ω(g(x), g(y)) = ω(c·g(x), g(y))`, the image of `g`
exhausts everything (finiteness), and `ω` separates. So `IsSymplectic` = linear symplectic
automorphism, and no refactor of the predicate is needed. -/
theorem Heis.IsSymplectic.map_vscale [Fintype F] {g : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) (c : F) (x : Heis F ι) :
    g (Heis.vscale c x) = Heis.vscale c (g x) := by
  have hsym : ∀ z, Heis.symp (g (Heis.vscale c x)) z = Heis.symp (Heis.vscale c (g x)) z := by
    intro z
    obtain ⟨y, rfl⟩ := hg.bijective.surjective z
    rw [hg.map_symp, Heis.symp_vscale_left, Heis.symp_vscale_left, ← hg.map_symp x y]
  obtain ⟨hpos, hmom⟩ := symp_left_cancel hsym
  refine Heis.ext hpos hmom ?_
  rw [hg.map_cen, Heis.vscale_cen, Heis.vscale_cen, hg.map_cen]

lemma Heis.vscale_zero (x : Heis F ι) : Heis.vscale (0 : F) x = Heis.central x.cen := by
  refine Heis.ext ?_ ?_ rfl <;> funext i <;> simp

/-- An `IsSymplectic` map fixes the centre pointwise — now a *theorem*, discharging the hypothesis
`symplecticHom_central` had to assume. -/
theorem Heis.IsSymplectic.map_central [Fintype F] {g : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) (s : F) : g (Heis.central s) = Heis.central s := by
  have h := hg.map_vscale 0 (Heis.central s)
  rw [Heis.vscale_zero, Heis.vscale_zero, Heis.central_cen, hg.map_cen, Heis.central_cen] at h
  exact h

end Classification

/-! ### The scalar `2×2` maps and the generation theorem -/

section Mob

/-- The `2×2`-block map `(p, m) ↦ (a·p + b·m, c·p + d·m)` acting diagonally across `ι`, centre
untouched. For `ad − bc = 1` these are the "scalar" symplectic maps — the diagonal `SL₂ ≤ Sp(2n)`;
at `|ι| = 1` they are all of `Sp(2, F)`. -/
def mob (a b c d : F) (x : Heis F ι) : Heis F ι :=
  ⟨fun i => a * x.pos i + b * x.mom i, fun i => c * x.pos i + d * x.mom i, x.cen⟩

@[simp] lemma mob_pos (a b c d : F) (x : Heis F ι) :
    (mob a b c d x).pos = fun i => a * x.pos i + b * x.mom i := rfl
@[simp] lemma mob_mom (a b c d : F) (x : Heis F ι) :
    (mob a b c d x).mom = fun i => c * x.pos i + d * x.mom i := rfl
@[simp] lemma mob_cen (a b c d : F) (x : Heis F ι) : (mob a b c d x).cen = x.cen := rfl

/-- Composition of `mob`s is matrix multiplication. -/
theorem mob_comp (a b c d a' b' c' d' : F) (x : Heis F ι) :
    mob a b c d (mob a' b' c' d' x)
      = mob (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') x := by
  refine Heis.ext ?_ ?_ rfl <;> funext i <;> simp only [mob_pos, mob_mom] <;> ring

/-- `mob a b c d` is symplectic exactly on the determinant-one locus. -/
theorem isSymplectic_mob {a b c d : F} (h : a * d - b * c = 1) :
    Heis.IsSymplectic (mob (F := F) (ι := ι) a b c d) where
  map_pos x y := by
    funext i
    simp only [mob_pos, Heis.mul_pos, Heis.mul_mom, Pi.add_apply]
    ring
  map_mom x y := by
    funext i
    simp only [mob_mom, Heis.mul_pos, Heis.mul_mom, Pi.add_apply]
    ring
  map_cen x := rfl
  map_symp x y := by
    unfold Heis.symp
    simp only [mob_pos, mob_mom]
    unfold pairing
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (y.mom i * x.pos i - x.mom i * y.pos i) * h

/-- The subgroup of maps generated by the shears and the Weyl element — the candidate generating
set for `Sp`. Closure under composition is by construction; every member has a Weil operator
(`hasWeilOperator_of_inWeilGroup`). -/
inductive InWeilGroup : (Heis F ι → Heis F ι) → Prop
  | shear {S : (ι → F) → (ι → F)} (hS : IsSymmetricMap S) : InWeilGroup (Heis.shear S)
  | fourier : InWeilGroup Heis.fourierMap
  | comp {g h : Heis F ι → Heis F ι} : InWeilGroup g → InWeilGroup h → InWeilGroup (g ∘ h)

/-- Scalar multiplication is a symmetric map. -/
theorem isSymmetricMap_smulFun (s : F) :
    IsSymmetricMap (fun z : ι → F => fun i => s * z i) where
  map_add a b := by
    funext i
    simp only [Pi.add_apply]
    ring
  symm a b := by
    unfold pairing
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The scalar shear, as a `mob`. -/
theorem shear_eq_mob (s : F) :
    Heis.shear (fun z : ι → F => fun i => s * z i) = mob (F := F) (ι := ι) 1 0 (-s) 1 := by
  funext x
  refine Heis.ext ?_ ?_ rfl
  · funext i
    change x.pos i = 1 * x.pos i + 0 * x.mom i
    ring
  · funext i
    change x.mom i - s * x.pos i = -s * x.pos i + 1 * x.mom i
    ring

/-- The Weyl element, as a `mob`. -/
theorem fourierMap_eq_mob :
    Heis.fourierMap (F := F) (ι := ι) = mob 0 1 (-1) 0 := by
  funext x
  refine Heis.ext ?_ ?_ rfl
  · funext i
    change x.mom i = 0 * x.pos i + 1 * x.mom i
    ring
  · funext i
    change -x.pos i = -1 * x.pos i + 0 * x.mom i
    ring

theorem inWeilGroup_momShear (t : F) : InWeilGroup (mob (F := F) (ι := ι) 1 0 t 1) := by
  have h := shear_eq_mob (F := F) (ι := ι) (-t)
  rw [neg_neg] at h
  rw [← h]
  exact InWeilGroup.shear (isSymmetricMap_smulFun (-t))

theorem inWeilGroup_wMob : InWeilGroup (mob (F := F) (ι := ι) 0 1 (-1) 0) := by
  rw [← fourierMap_eq_mob]
  exact InWeilGroup.fourier

/-- The opposite (position) shear is the `w`-conjugate of a momentum shear: `U(t) = w·L(−t)·w⁻¹`,
with `w⁻¹ = w³`. -/
theorem inWeilGroup_posShear (t : F) : InWeilGroup (mob (F := F) (ι := ι) 1 t 0 1) := by
  have hsplit : mob (F := F) (ι := ι) 1 t 0 1
      = mob 0 1 (-1) 0 ∘ (mob 1 0 (-t) 1 ∘ (mob 0 1 (-1) 0 ∘ (mob 0 1 (-1) 0 ∘ mob 0 1 (-1) 0))) := by
    funext x
    simp only [Function.comp_apply, mob_comp]
    refine Heis.ext ?_ ?_ rfl <;> funext i <;> simp only [mob_pos, mob_mom] <;> ring
  rw [hsplit]
  exact InWeilGroup.comp inWeilGroup_wMob (InWeilGroup.comp (inWeilGroup_momShear (-t))
    (InWeilGroup.comp inWeilGroup_wMob (InWeilGroup.comp inWeilGroup_wMob inWeilGroup_wMob)))

/-- **The three-shear identity** (the open Bruhat cell): for `c ≠ 0`,
`[[a,b],[c,d]] = U((a−1)/c) · L(c) · U((d−1)/c)`, so the cell is inside `⟨shears, w⟩`. -/
theorem inWeilGroup_mob_of_ne {a b c d : F} (h : a * d - b * c = 1) (hc : c ≠ 0) :
    InWeilGroup (mob (F := F) (ι := ι) a b c d) := by
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hsplit : mob (F := F) (ι := ι) a b c d
      = mob 1 ((a - 1) * c⁻¹) 0 1 ∘ (mob 1 0 c 1 ∘ mob 1 ((d - 1) * c⁻¹) 0 1) := by
    funext x
    simp only [Function.comp_apply, mob_comp]
    refine Heis.ext ?_ ?_ rfl <;> funext i <;> simp only [mob_pos, mob_mom]
    · linear_combination (-(x.pos i * (a - 1))
          - x.mom i * ((a - 1) * (d - 1) * c⁻¹ + b)) * hcc - x.mom i * c⁻¹ * h
    · linear_combination (-(x.mom i * (d - 1))) * hcc
  rw [hsplit]
  exact InWeilGroup.comp (inWeilGroup_posShear _)
    (InWeilGroup.comp (inWeilGroup_momShear c) (inWeilGroup_posShear _))

/-- **Generation**: every determinant-one `mob` is a word in the shears and the Weyl element. The
`c = 0` matrices (the closed cell) reach the open cell after one `w`-pivot on the right. -/
theorem inWeilGroup_mob {a b c d : F} (h : a * d - b * c = 1) :
    InWeilGroup (mob (F := F) (ι := ι) a b c d) := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by linear_combination h
    have hd : d ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at had
      exact zero_ne_one had
    have hsplit : mob (F := F) (ι := ι) a b 0 d
        = mob (-b) a (-d) 0 ∘ (mob 0 1 (-1) 0 ∘ (mob 0 1 (-1) 0 ∘ mob 0 1 (-1) 0)) := by
      funext x
      simp only [Function.comp_apply, mob_comp]
      refine Heis.ext ?_ ?_ rfl <;> funext i <;> simp only [mob_pos, mob_mom] <;> ring
    rw [hsplit]
    refine InWeilGroup.comp ?_ (InWeilGroup.comp inWeilGroup_wMob
      (InWeilGroup.comp inWeilGroup_wMob inWeilGroup_wMob))
    exact inWeilGroup_mob_of_ne (by linear_combination had) (neg_ne_zero.mpr hd)
  · exact inWeilGroup_mob_of_ne h hc

end Mob

/-! ### Every generated element has a Weil operator -/

section WeilOperators

variable [Fintype F] [DecidableEq ι]

/-- Every word in the shears and the Weyl element has a Weil operator — the Bruhat route's closure,
now stated over the whole generated subgroup at once. -/
theorem hasWeilOperator_of_inWeilGroup (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : InWeilGroup g) : HasWeilOperator h2 ψ g := by
  induction hg with
  | shear hS => exact hasWeilOperator_shear h2 ψ hS
  | fourier => exact hasWeilOperator_fourierMap h2 hψ
  | comp _ _ ihg ihh => exact ihg.comp ihh

end WeilOperators

/-! ### Rank one: classification + generation = the Weil representation of `Sp(2, 𝔽_q)` -/

section RankOne

variable [DecidableEq ι] [Fintype F] [Unique ι]

lemma pos_eq_vscale (p : ι → F) :
    (⟨p, 0, 0⟩ : Heis F ι) = Heis.vscale (p default) ⟨fun _ => 1, 0, 0⟩ := by
  refine Heis.ext ?_ ?_ rfl
  · funext i
    change p i = p default * 1
    rw [mul_one, Unique.eq_default i]
  · funext i
    change (0 : ι → F) i = p default * (0 : ι → F) i
    simp

lemma mom_eq_vscale (m : ι → F) :
    (⟨0, m, 0⟩ : Heis F ι) = Heis.vscale (m default) ⟨0, fun _ => 1, 0⟩ := by
  refine Heis.ext ?_ ?_ rfl
  · funext i
    change (0 : ι → F) i = m default * (0 : ι → F) i
    simp
  · funext i
    change m i = m default * 1
    rw [mul_one, Unique.eq_default i]

/-- **Classification at rank one**: over a one-element index type every symplectic map *is* a `2×2`
matrix, its entries read off from the images of the two basis vectors. Linearity (`map_vscale`) plus
the factorization `x = central·position·momentum` reduce everything to those two values. -/
theorem Heis.IsSymplectic.eq_mob {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    g = mob ((g ⟨fun _ => 1, 0, 0⟩).pos default) ((g ⟨0, fun _ => 1, 0⟩).pos default)
        ((g ⟨fun _ => 1, 0, 0⟩).mom default) ((g ⟨0, fun _ => 1, 0⟩).mom default) := by
  funext x
  have hfac : g x = g (Heis.central (x.cen - (2 : F)⁻¹ * pairing x.mom x.pos))
      * g ⟨x.pos, 0, 0⟩ * g ⟨0, x.mom, 0⟩ := by
    conv_lhs => rw [Heis.factor x]
    rw [Heis.isSymplectic_map_mul hg, Heis.isSymplectic_map_mul hg]
  refine Heis.ext ?_ ?_ (by rw [hg.map_cen]; rfl)
  · rw [hfac, hg.map_central, pos_eq_vscale x.pos, mom_eq_vscale x.mom, hg.map_vscale,
      hg.map_vscale]
    funext i
    simp only [Heis.mul_pos, Pi.add_apply, Heis.central_pos, Heis.vscale_pos, mob_pos, zero_add]
    rw [Unique.eq_default i]
    ring
  · rw [hfac, hg.map_central, pos_eq_vscale x.pos, mom_eq_vscale x.mom, hg.map_vscale,
      hg.map_vscale]
    funext i
    simp only [Heis.mul_mom, Pi.add_apply, Heis.central_mom, Heis.vscale_mom, mob_mom, zero_add]
    rw [Unique.eq_default i]
    ring

/-- The extracted matrix has determinant one: `ω(e₁, e₂) = 1` on both sides of `map_symp`. -/
theorem Heis.IsSymplectic.det_eq_one {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    (g ⟨fun _ => 1, 0, 0⟩).pos default * (g ⟨0, fun _ => 1, 0⟩).mom default
      - (g ⟨0, fun _ => 1, 0⟩).pos default * (g ⟨fun _ => 1, 0, 0⟩).mom default = 1 := by
  have hpair : ∀ u v : ι → F, pairing u v = u default * v default := fun u v => by
    unfold pairing
    exact Fintype.sum_unique _
  have h := hg.map_symp ⟨fun _ => 1, 0, 0⟩ ⟨0, fun _ => 1, 0⟩
  unfold Heis.symp at h
  rw [hpair, hpair, hpair, hpair] at h
  simp only [Pi.zero_apply, mul_one, mul_zero, sub_zero] at h
  linear_combination h

/-- **The Weil representation of `Sp(2, 𝔽_q)`, complete**: at rank one, *every* symplectic map has a
Weil operator — classification (`eq_mob`), the determinant (`det_eq_one`), generation
(`inWeilGroup_mob`), and the explicit operators of the Bruhat route, composed. -/
theorem hasWeilOperator_of_isSymplectic (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) : HasWeilOperator h2 ψ g := by
  rw [hg.eq_mob]
  exact hasWeilOperator_of_inWeilGroup h2 hψ (inWeilGroup_mob hg.det_eq_one)

end RankOne

end ECCLib.Heisenberg

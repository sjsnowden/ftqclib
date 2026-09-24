/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.WeilGeneration
import ECCLib.PoissonSummation

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Linear codes in the Schrödinger model

A linear code is a subspace `C ≤ 𝔽_q^ι` — nothing more. Its indicator function is a vector of the
Schrödinger model `(ι → F) → ℂ`, the space the Weil representation acts on, and the first theorem
here is that the DFT sends code indicators to dual-code indicators:

* `dualCode C` — the dual code, membership definitional over the repo's `pairing`
  (`∀ x ∈ C, pairing x y = 0`);
* `mem_dualCode_iff_mem_charAnnih` — the bridge to the Fourier engine: `y ∈ C^⊥` iff the character
  `pairingChar ψ y` is trivial on `C`. The content is that `ψ∘pairing(·,y)` trivial on a *subspace*
  forces `pairing(·,y) = 0` there — the image is a subspace of `F`, so `0` or everything, and the
  latter kills `ψ ≠ 1`;
* `card_dualCode_mul_card` — `|C^⊥|·|C| = q^n`, from **rank–nullity**
  (`finrank_dualCode_add_finrank`), deliberately *not* through `card_annihilator_mul_card`: see the
  section "The size relation, without the Fourier engine" below for why the independence matters;
* `dualCode_dualCode` — double duality, from the trivial inclusion plus the cardinality relation
  (no appeal to `orthogonal_orthogonal`);
* **`fourierOp_indicator`** — `𝓕(𝟙_C) = |C| · 𝟙_{C^⊥}`: the dual code IS the DFT of the code.
  Restricted character orthogonality (`sum_char_over_subgroup`) plus the bridge. MacWilliams will be
  weight statistics of this statement.
-/

namespace ECCLib.Coding

open ECCLib.Heisenberg

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## A nontrivial character exists

`card_dualCode_mul_card` and `dualCode_dualCode` are about dimensions, and `macwilliams` is a
polynomial identity in `z`; no character occurs in any of their conclusions. **Only `macwilliams`'s
proof needs a character** — it runs through `fourierOp_indicator` and the Krawtchouk sums. The other
two are proved by rank–nullity and are deliberately free of the Fourier layer (see "The size
relation, without the Fourier engine" below, and `ECCLib/VerifyIndependence.lean`, which
checks that independence rather than asserting it). Since a character can always be produced, it
need not be a hypothesis anywhere. -/
set_option backward.isDefEq.respectTransparency false in
theorem exists_ne_one_addChar (F : Type*) [Field F] [Fintype F] :
    ∃ ψ : AddChar F ℂ, ψ ≠ 1 := by
  refine ⟨AddChar.FiniteField.primitiveChar_to_Complex F, ?_⟩
  intro h
  have hp := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have h1 := hp (show (1 : F) ≠ 0 from one_ne_zero)
  rw [AddChar.mulShift_one, h] at h1
  exact h1 rfl

/-! ## The dual code -/

lemma pairing_smul_left (c : F) (b y : ι → F) : pairing (c • b) y = c * pairing b y := by
  unfold pairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma pairing_smul_right (c : F) (b y : ι → F) : pairing b (c • y) = c * pairing b y := by
  rw [pairing_symm, pairing_smul_left, pairing_symm]

/-- The **dual code** `C^⊥ = {y | ∀ x ∈ C, ⟨x,y⟩ = 0}`. -/
def dualCode (C : Submodule F (ι → F)) : Submodule F (ι → F) where
  carrier := {y | ∀ x ∈ C, pairing x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [pairing_add_right, ha x hx, hb x hx, add_zero]
  zero_mem' := by
    intro x _
    exact pairing_zero_right x
  smul_mem' := by
    intro c y hy x hx
    rw [pairing_smul_right, hy x hx, mul_zero]

@[simp] theorem mem_dualCode {C : Submodule F (ι → F)} {y : ι → F} :
    y ∈ dualCode C ↔ ∀ x ∈ C, pairing x y = 0 := Iff.rfl

@[simp] theorem dualCode_bot : dualCode (⊥ : Submodule F (ι → F)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, pairing_zero_left]

@[simp] theorem dualCode_top : dualCode (⊤ : Submodule F (ι → F)) = ⊥ := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [Submodule.mem_bot]
    refine eq_zero_of_pairing_left y fun p => ?_
    rw [pairing_symm]
    exact hy p Submodule.mem_top
  · intro y hy
    rw [Submodule.mem_bot] at hy
    subst hy
    intro x _
    exact pairing_zero_right x

/-! ## The bridge to the character annihilator -/

/-- The subspace trick: if `ψ∘pairing(·,y)` is trivial on the subspace `C`, then `pairing(·,y)`
vanishes on `C`. The image of `C` under `pairing(·,y)` is an `F`-subspace of `F`; were some value
nonzero, scaling would produce every value of `F` inside the image, forcing `ψ = 1`. -/
theorem pairing_eq_zero_of_char_trivial {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {C : Submodule F (ι → F)} {y : ι → F}
    (h : ∀ x ∈ C, ψ (pairing x y) = 1) : ∀ x ∈ C, pairing x y = 0 := by
  intro x hx
  by_contra hne
  apply hψ
  refine DFunLike.ext _ _ fun s => ?_
  rw [AddChar.one_apply]
  have hmem : (s * (pairing x y)⁻¹) • x ∈ C := C.smul_mem _ hx
  have hval := h _ hmem
  rwa [pairing_smul_left, mul_assoc, inv_mul_cancel₀ hne, mul_one] at hval

open Classical in
/-- **The bridge**: `y ∈ C^⊥` iff the character `pairingChar ψ y` lies in the annihilator of `C`.
This is what turns every Fourier-engine statement about `charAnnih` into a statement about the dual
code. -/
theorem mem_dualCode_iff_mem_charAnnih {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {C : Submodule F (ι → F)} {y : ι → F} :
    y ∈ dualCode C ↔ pairingChar ψ y ∈ charAnnih C.toAddSubgroup := by
  rw [mem_charAnnih]
  constructor
  · intro hy x hx
    rw [pairingChar_apply, hy x hx, AddChar.map_zero_eq_one]
  · intro h x hx
    refine pairing_eq_zero_of_char_trivial hψ (fun x' hx' => ?_) x hx
    have hx'' := h x' hx'
    rwa [pairingChar_apply] at hx''

open Classical in
/-- The annihilator of a code has the size of its dual code — `pairingChar` restricts to a bijection
between them (self-duality). -/
theorem card_charAnnih_eq {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (C : Submodule F (ι → F)) :
    (charAnnih C.toAddSubgroup).card = Nat.card (dualCode C) := by
  have e : (dualCode C) ≃ {ξ : AddChar (ι → F) ℂ // ξ ∈ charAnnih C.toAddSubgroup} := by
    refine Equiv.ofBijective
      (fun y => ⟨pairingChar ψ y.1, (mem_dualCode_iff_mem_charAnnih hψ).mp y.2⟩) ⟨?_, ?_⟩
    · intro a b hab
      exact Subtype.ext ((pairingChar_bijective hψ).injective (congrArg Subtype.val hab))
    · rintro ⟨ξ, hξ⟩
      obtain ⟨z, hz⟩ := exists_eq_pairingChar hψ ξ
      have hzmem : z ∈ dualCode C := (mem_dualCode_iff_mem_charAnnih hψ).mpr (hz ▸ hξ)
      exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩
  calc (charAnnih C.toAddSubgroup).card
      = Nat.card {ξ : AddChar (ι → F) ℂ // ξ ∈ charAnnih C.toAddSubgroup} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (dualCode C) := Nat.card_congr e.symm

/-! ## The size relation, without the Fourier engine

`|C^⊥|·|C| = q^n` is pure linear algebra. `C^⊥` is the kernel of the map sending `y` to the
functional `⟨·,y⟩` *restricted to* `C`; that map is surjective because `pairing` is nondegenerate,
and rank–nullity gives the relation.

Proving it this way matters beyond hygiene. `macwilliams_one` reaches the same number *from* the
MacWilliams identity, i.e. through the DFT. If this theorem also went through Poisson summation the
two would share the Fourier layer, and a convention error there would break both identically —
which is precisely the failure mode the cross-check exists to catch. Going through rank–nullity
makes the two routes genuinely independent. -/

lemma pairing_single (i : ι) (y : ι → F) : pairing (Pi.single i 1) y = y i := by
  unfold pairing
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_mul]

/-- `pairing` as a map into the dual space: `y ↦ ⟨·, y⟩`. -/
def toDualPairing : (ι → F) →ₗ[F] Module.Dual F (ι → F) where
  toFun y :=
    { toFun := fun x => pairing x y
      map_add' := fun a b => pairing_add_left a b y
      map_smul' := fun c a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact pairing_smul_left c a y }
  map_add' y y' := LinearMap.ext fun x => pairing_add_right x y y'
  map_smul' c y := LinearMap.ext fun x => by simpa using pairing_smul_right c x y

@[simp] lemma toDualPairing_apply (y x : ι → F) : toDualPairing y x = pairing x y := rfl

/-- **Nondegeneracy of `pairing`**, in the form used below: `y ↦ ⟨·,y⟩` is injective. Witnessed by
the standard basis — `⟨e_i, y⟩ = y i`. -/
theorem toDualPairing_injective : Function.Injective (toDualPairing (F := F) (ι := ι)) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
  have h0 : toDualPairing y = 0 := LinearMap.mem_ker.mp hy
  funext i
  have h := congrArg (fun g : Module.Dual F (ι → F) => g (Pi.single i 1)) h0
  simpa [pairing_single] using h

/-- **Rank–nullity for the dual code**: `dim C^⊥ + dim C = n`. No character, no Fourier engine. -/
theorem finrank_dualCode_add_finrank (C : Submodule F (ι → F)) :
    Module.finrank F (dualCode C) + Module.finrank F C = Module.finrank F (ι → F) := by
  classical
  set Φ : (ι → F) →ₗ[F] Module.Dual F ↥C := C.dualRestrict ∘ₗ toDualPairing with hΦ
  have hker : LinearMap.ker Φ = dualCode C := by
    ext y
    simp only [LinearMap.mem_ker, hΦ, LinearMap.comp_apply, mem_dualCode]
    constructor
    · intro h x hx
      have hx' := congrArg (fun g : Module.Dual F ↥C => g ⟨x, hx⟩) h
      simpa [Submodule.dualRestrict_apply] using hx'
    · intro h
      refine LinearMap.ext fun x => ?_
      simpa [Submodule.dualRestrict_apply] using h x.1 x.2
  have hsurjT : Function.Surjective (toDualPairing (F := F) (ι := ι)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := F) (V := ι → F)).symm).mp toDualPairing_injective
  have hsurj : Function.Surjective Φ := by
    intro g
    obtain ⟨f, hf⟩ := Subspace.dualRestrict_surjective (W := C) g
    obtain ⟨y, hy⟩ := hsurjT f
    exact ⟨y, by rw [hΦ, LinearMap.comp_apply, hy, hf]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.mpr hsurj, hker, finrank_top, Subspace.dual_finrank_eq] at hrn
  omega

/-- **The size relation** `|C^⊥| · |C| = q^n`, from rank–nullity. -/
theorem card_dualCode_mul_card (C : Submodule F (ι → F)) :
    Nat.card (dualCode C) * Nat.card C = Fintype.card (ι → F) := by
  classical
  have h := finrank_dualCode_add_finrank C
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F) (V := ↥(dualCode C)),
    Module.card_eq_pow_finrank (K := F) (V := ↥C),
    Module.card_eq_pow_finrank (K := F) (V := ι → F), ← pow_add, h]

theorem le_dualCode_dualCode (C : Submodule F (ι → F)) : C ≤ dualCode (dualCode C) := by
  intro x hx y hy
  rw [pairing_symm]
  exact hy x hx

/-- **Double duality** `C^⊥⊥ = C` — the trivial inclusion plus the size relation (twice), no
orthogonal-complement machinery. -/
theorem dualCode_dualCode (C : Submodule F (ι → F)) :
    dualCode (dualCode C) = C := by
  classical
  have h1 := card_dualCode_mul_card C
  have h2 := card_dualCode_mul_card (dualCode C)
  have hpos : 0 < Nat.card (dualCode C) := Nat.card_pos
  have hcard : Nat.card (dualCode (dualCode C)) = Nat.card C :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans (h1.symm.trans (mul_comm _ _)))
  have hfr : Module.finrank F (dualCode (dualCode C)) = Module.finrank F C := by
    have hd : Fintype.card (dualCode (dualCode C)) = Fintype.card C := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
    rw [Module.card_eq_pow_finrank (K := F) (V := ↥(dualCode (dualCode C))),
      Module.card_eq_pow_finrank (K := F) (V := ↥C)] at hd
    exact Nat.pow_right_injective Fintype.one_lt_card hd
  exact (Submodule.eq_of_le_of_finrank_le (le_dualCode_dualCode C) hfr.le).symm

/-! ## The bridge theorem: the dual code is the DFT of the code -/

open Classical in
/-- The indicator of a code, as a vector of the Schrödinger model. -/
noncomputable def indicator (C : Submodule F (ι → F)) : (ι → F) → ℂ :=
  fun x => if x ∈ C then 1 else 0

open Classical in
/-- **The code–dual-code theorem**: `𝓕(𝟙_C) = |C| · 𝟙_{C^⊥}` — the dual code is the DFT of the code
indicator. Codes live in the Schrödinger model, and the Weil operator of the Weyl element acts on
them by duality. MacWilliams is weight statistics of this identity. -/
theorem fourierOp_indicator {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (C : Submodule F (ι → F)) :
    fourierOp ψ (indicator C) = (Nat.card C : ℂ) • indicator (dualCode C) := by
  funext y
  rw [fourierOp_apply]
  have hstep : ∑ x : ι → F, ψ (pairing y x) * indicator C x
      = ∑ x : C.toAddSubgroup, (pairingChar ψ y) (x : ι → F) := by
    rw [← Finset.sum_subtype (p := fun v => v ∈ C.toAddSubgroup)
      (Finset.univ.filter (fun v : ι → F => v ∈ C))
      (fun x => ⟨fun hx => (Finset.mem_filter.mp hx).2,
        fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩)
      (fun v => (pairingChar ψ y) v), Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold indicator
    split_ifs with hx
    · rw [mul_one, pairingChar_apply, pairing_symm]
    · rw [mul_zero]
  rw [hstep, sum_char_over_subgroup]
  have hcond : (∀ h ∈ C.toAddSubgroup, (pairingChar ψ y) h = 1) ↔ y ∈ dualCode C := by
    rw [mem_dualCode_iff_mem_charAnnih hψ, mem_charAnnih]
  rw [Pi.smul_apply, smul_eq_mul]
  unfold indicator
  split_ifs with hmem hdual hdual
  · rw [mul_one]
    rfl
  · exact absurd (hcond.mp hmem) hdual
  · exact absurd (hcond.mpr hdual) hmem
  · rw [mul_zero]

open Classical in
/-- Sanity at `C = ⊥`: the DFT of `δ₀` is the constant function `1`. -/
theorem fourierOp_indicator_bot {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    fourierOp ψ (indicator (⊥ : Submodule F (ι → F))) = indicator ⊤ := by
  have hone : Nat.card (⊥ : Submodule F (ι → F)) = 1 := Nat.card_unique
  rw [fourierOp_indicator hψ, dualCode_bot, hone]
  simp

open Classical in
/-- Sanity at `C = ⊤`: the DFT of the constant function `1` is `q^n · δ₀`. -/
theorem fourierOp_indicator_top {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    fourierOp ψ (indicator (⊤ : Submodule F (ι → F)))
      = (Fintype.card (ι → F) : ℂ) • indicator (⊥ : Submodule F (ι → F)) := by
  have htop : Nat.card (⊤ : Submodule F (ι → F)) = Fintype.card (ι → F) := by
    rw [Nat.card_congr (Submodule.topEquiv (R := F) (M := ι → F)).toEquiv,
      Nat.card_eq_fintype_card]
  rw [fourierOp_indicator hψ, dualCode_top, htop]

end ECCLib.Coding

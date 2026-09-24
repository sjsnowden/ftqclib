/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.style.longLine false

/-!
# Symplectic transvections generate the symplectic group, over any field

`transvections_generate_sp`: every isometry of a nondegenerate alternating form on a
finite-dimensional space over a field is a product of symplectic transvections. This is the classical
theorem (Artin; Grove, *Classical Groups and Geometric Algebra*), and it is what `Ep(2n) = Sp(2n)`
amounts to once the transvections are known to lie in the group at hand.

The architecture is the codimension induction: measure an isometry `T` by
`finrank V − finrank (fixedSpace T)`; if that is `0` then `T = 1`; otherwise `moveStep` produces a
short transvection word `g` with `g (T e) = e` that fixes everything `T` already fixed, so `g * T`
has a strictly larger fixed space and the induction hypothesis applies.

Over `𝔽₂` this argument is `FTQCLib/Gates/TransvectionAbstract.lean` (the proof that
transvections generate the binary symplectic group). Three things there are genuinely char-2
and are replaced here rather than reused:

* a transvection carries a **scalar** `c` (`t_{v,c} : u ↦ u + c·B(v,u)·v`). Over `𝔽₂` the only
  nonzero scalar is `1`, so it can be omitted; in general it cannot. `t_{v,c} ∘ t_{v,c'} = t_{v,c+c'}`,
  so the inverse is `t_{v,−c}` — the char-2 file instead gets its inverse from involutivity, which
  is false here (`t_{v,c}² = t_{v,2c}`).
* the pairing conditions are `≠ 0`, not `= 1`. This is the *natural* statement; `𝔽₂` conflates them,
  and the three-case `exists_simultaneous_pair` argument goes through verbatim once restated.
* the one-transvection move sends `a ↦ e` by `t_{e−a, 1/B(e,a)}`, not by `τ_{a+e}` (which works over
  `𝔽₂` precisely because `2a = 0`).

This file is Mathlib-only, so it can be lifted with the rest of `ECCLib`.
-/

namespace ECCLib.SpGen

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  (B : V →ₗ[F] V →ₗ[F] F)

/-- A `B`-isometry: a linear automorphism preserving the form. -/
def IsSymplecticEquiv (T : V ≃ₗ[F] V) : Prop := ∀ x y, B (T x) (T y) = B x y

/-- Skew-symmetry, the form in which alternation is actually used below. -/
theorem skew (hA : B.IsAlt) (x y : V) : B x y = - B y x := (LinearMap.IsAlt.neg hA y x).symm

/-! ## The transvection with a scalar -/

/-- The linear part of the transvection `t_{v,c} : u ↦ u + c·B(v,u)·v`. -/
def transvectionLin (v : V) (c : F) : V →ₗ[F] V :=
  LinearMap.id + LinearMap.smulRight (c • B v) v

@[simp] theorem transvectionLin_apply (v : V) (c : F) (u : V) :
    transvectionLin B v c u = u + (c * B v u) • v := by
  simp [transvectionLin, smul_eq_mul]

@[simp] theorem transvectionLin_zero (v : V) : transvectionLin B v 0 = LinearMap.id := by
  refine LinearMap.ext fun u => ?_
  simp

/-- **The composition law**: `t_{v,c} ∘ t_{v,c'} = t_{v,c+c'}`. The scalars simply add, which is
what replaces the char-2 file's involutivity. -/
theorem transvectionLin_comp (hA : B.IsAlt) (v : V) (c c' : F) :
    transvectionLin B v c ∘ₗ transvectionLin B v c' = transvectionLin B v (c + c') := by
  refine LinearMap.ext fun u => ?_
  have hb : B v (u + (c' * B v u) • v) = B v u := by
    rw [map_add, map_smul, hA.self_eq_zero v, smul_zero, add_zero]
  simp only [LinearMap.comp_apply, transvectionLin_apply, hb]
  rw [add_assoc, ← add_smul]
  ring_nf

/-- The transvection `t_{v,c}` as a linear automorphism; its inverse is `t_{v,−c}`. -/
def transvectionEquiv (hA : B.IsAlt) (v : V) (c : F) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinear (transvectionLin B v c) (transvectionLin B v (-c))
    (by rw [transvectionLin_comp B hA, add_neg_cancel, transvectionLin_zero])
    (by rw [transvectionLin_comp B hA, neg_add_cancel, transvectionLin_zero])

@[simp] theorem transvectionEquiv_apply (hA : B.IsAlt) (v : V) (c : F) (u : V) :
    transvectionEquiv B hA v c u = u + (c * B v u) • v := by
  simp only [transvectionEquiv, LinearEquiv.ofLinear_apply, transvectionLin_apply]

/-- **The pivot lemma**: a transvection by `v` fixes everything `B`-orthogonal to `v`. This is what
lets the induction keep its accumulated fixed space intact. -/
theorem transvection_fixes_of_orthogonal (hA : B.IsAlt) {v u : V} (c : F) (h : B v u = 0) :
    transvectionEquiv B hA v c u = u := by
  rw [transvectionEquiv_apply, h, mul_zero, zero_smul, add_zero]

/-- A transvection is an isometry. -/
theorem transvectionEquiv_isSymplectic (hA : B.IsAlt) (v : V) (c : F) :
    IsSymplecticEquiv B (transvectionEquiv B hA v c) := by
  intro x y
  have hvv : B v v = 0 := hA.self_eq_zero v
  have hxv : B x v = - B v x := skew B hA x v
  simp only [transvectionEquiv_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hvv, hxv]
  ring

/-- **Conjugation moves the direction**: a symplectic conjugate of a transvection is the
transvection along the moved vector, `g · t_{v,c} · g⁻¹ = t_{g v, c}`. The engine of "every
transvection is a shear conjugate": conjugating by a shear moves `v` to a pure direction. -/
theorem transvectionEquiv_conj (hA : B.IsAlt) {g : V ≃ₗ[F] V} (hg : IsSymplecticEquiv B g)
    (v : V) (c : F) :
    g * transvectionEquiv B hA v c * g⁻¹ = transvectionEquiv B hA (g v) c := by
  refine LinearEquiv.toLinearMap_injective (LinearMap.ext fun u => ?_)
  have hBvu : B v (g.symm u) = B (g v) u := by
    have h := hg v (g.symm u)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    transvectionEquiv_apply, map_add, map_smul, LinearEquiv.apply_symm_apply, hBvu]

/-! ## The one-transvection move -/

/-- **The move.** When `B e a ≠ 0`, the transvection by `e − a` with scalar `1/B(e,a)` sends `a` to
`e`: `t(a) = a + c·B(e−a, a)·(e−a) = a + c·B(e,a)·(e−a) = a + (e−a) = e`, using `B a a = 0`.

Over `𝔽₂` this is `τ_{a+e}`, which works there only because `2a = 0`. -/
theorem transvection_move (hA : B.IsAlt) {a e : V} (h : B e a ≠ 0) :
    transvectionEquiv B hA (e - a) (B e a)⁻¹ a = e := by
  have hb : B (e - a) a = B e a := by
    rw [map_sub, LinearMap.sub_apply, hA.self_eq_zero a, sub_zero]
  rw [transvectionEquiv_apply, hb, inv_mul_cancel₀ h, one_smul]
  abel

/-! ## Nondegeneracy: pairing partners -/

/-- Nondegeneracy, in the form used: a nonzero vector pairs nontrivially with something. -/
theorem exists_pair_ne_zero (hN : B.Nondegenerate) {e : V} (he : e ≠ 0) :
    ∃ a, B e a ≠ 0 := by
  by_contra hcon
  refine he (hN.1 e fun y => ?_)
  by_contra hy
  exact hcon ⟨y, hy⟩

/-- **Simultaneous pair.** For nonzero `e, x`, a single `u` pairs nontrivially with both. The
three-case argument of the char-2 file, restated with `≠ 0` in place of `= 1`. -/
theorem exists_simultaneous_pair (hN : B.Nondegenerate) {e x : V} (he : e ≠ 0) (hx : x ≠ 0) :
    ∃ u, B e u ≠ 0 ∧ B x u ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_pair_ne_zero B hN he
  obtain ⟨b, hb⟩ := exists_pair_ne_zero B hN hx
  by_cases hxa : B x a ≠ 0
  · exact ⟨a, ha, hxa⟩
  · by_cases heb : B e b ≠ 0
    · exact ⟨b, heb, hb⟩
    · refine ⟨a + b, ?_, ?_⟩
      · rw [map_add, not_not.mp heb, add_zero]; exact ha
      · rw [map_add, not_not.mp hxa, zero_add]; exact hb

/-! ## The fixed space -/

/-- The fixed subspace of `T`. -/
def fixedSpace (T : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.ker (T.toLinearMap - LinearMap.id)

@[simp] theorem mem_fixedSpace {T : V ≃ₗ[F] V} {u : V} : u ∈ fixedSpace T ↔ T u = u := by
  simp only [fixedSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, sub_eq_zero]

/-- If `T e ≠ e` then `T e` is itself not fixed — else injectivity would force `T e = e`. -/
theorem Te_notMem_fixedSpace {T : V ≃ₗ[F] V} {e : V} (he : T e ≠ e) :
    T e ∉ fixedSpace T := by
  rw [mem_fixedSpace]
  intro h
  exact he (T.injective h.symm).symm

/-- For `y ∉ W`, some `s ∈ W^⊥` pairs nontrivially with `y` — via `W^⊥⊥ = W`. -/
theorem exists_pair_ne_zero_of_notMem [FiniteDimensional F V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) {W : Submodule F V} {y : V} (hy : y ∉ W) :
    ∃ s, s ∈ LinearMap.BilinForm.orthogonal B W ∧ B y s ≠ 0 := by
  have hRefl : B.IsRefl := hA.isRefl
  have hyy : y ∉ LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B W) := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal hN hRefl W]; exact hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hyy
  simp only [not_forall, LinearMap.BilinForm.isOrtho_def] at hyy
  obtain ⟨s, hs, hsy⟩ := hyy
  refine ⟨s, hs, ?_⟩
  rw [skew B hA y s]
  simpa using hsy

/-- The `W^⊥`-relative simultaneous pair: for `e, x ∉ W`, one `s ∈ W^⊥` pairs with both. -/
theorem exists_simultaneous_pair_mem [FiniteDimensional F V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) {W : Submodule F V} {e x : V} (he : e ∉ W) (hx : x ∉ W) :
    ∃ s, s ∈ LinearMap.BilinForm.orthogonal B W ∧ B e s ≠ 0 ∧ B x s ≠ 0 := by
  obtain ⟨a, ha, hea⟩ := exists_pair_ne_zero_of_notMem B hN hA he
  obtain ⟨b, hb, hxb⟩ := exists_pair_ne_zero_of_notMem B hN hA hx
  by_cases hxa : B x a ≠ 0
  · exact ⟨a, ha, hea, hxa⟩
  · by_cases heb : B e b ≠ 0
    · exact ⟨b, hb, heb, hxb⟩
    · refine ⟨a + b, Submodule.add_mem _ ha hb, ?_, ?_⟩
      · rw [map_add, not_not.mp heb, add_zero]; exact hea
      · rw [map_add, not_not.mp hxa, zero_add]; exact hxb

/-! ## The generating set and the move step -/

/-- The set of all symplectic transvections. -/
def transvectionGens (hA : B.IsAlt) : Set (V ≃ₗ[F] V) :=
  {h | ∃ (v : V) (c : F), h = transvectionEquiv B hA v c}

theorem mem_transvectionGens (hA : B.IsAlt) (v : V) (c : F) :
    transvectionEquiv B hA v c ∈ transvectionGens B hA :=
  ⟨v, c, rfl⟩

/-- **The move step.** If `T e ≠ e`, a transvection word `g` sends `T e` back to `e` while fixing
everything `T` fixed. Easy case `B e (T e) ≠ 0`: one transvection. Degenerate case
`B e (T e) = 0`: a two-transvection bridge through `(fixedSpace T)^⊥`. -/
theorem moveStep [FiniteDimensional F V] (hN : B.Nondegenerate) (hA : B.IsAlt)
    {T : V ≃ₗ[F] V} (hT : IsSymplecticEquiv B T) {e : V} (he : T e ≠ e) :
    ∃ g : V ≃ₗ[F] V, g ∈ Subgroup.closure (transvectionGens B hA) ∧
      g (T e) = e ∧ ∀ w, T w = w → g w = w := by
  -- `T e − e` is orthogonal to the fixed space, for any `T`-fixed `w`.
  have hfix_orth : ∀ w, T w = w → B (T e) w = B e w := by
    intro w hw
    have h := hT e w
    rwa [hw] at h
  by_cases h1 : B e (T e) ≠ 0
  · -- Easy case: one transvection by `e − T e`.
    refine ⟨transvectionEquiv B hA (e - T e) (B e (T e))⁻¹,
      Subgroup.subset_closure (mem_transvectionGens B hA _ _),
      transvection_move B hA h1, fun w hw => ?_⟩
    refine transvection_fixes_of_orthogonal B hA _ ?_
    rw [map_sub, LinearMap.sub_apply, hfix_orth w hw, sub_self]
  · -- Degenerate case: bridge through `s ∈ (fixedSpace T)^⊥`.
    have h1' : B e (T e) = 0 := not_not.mp h1
    have heW : e ∉ fixedSpace T := fun h => he (mem_fixedSpace.mp h)
    have hTeW : T e ∉ fixedSpace T := Te_notMem_fixedSpace he
    obtain ⟨s, hs, hes, hTes⟩ := exists_simultaneous_pair_mem B hN hA heW hTeW
    have hsw : ∀ w, T w = w → B s w = 0 := by
      intro w hw
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hs) w (mem_fixedSpace.mpr hw)
      rw [LinearMap.BilinForm.isOrtho_def] at h
      rw [skew B hA s w, h, neg_zero]
    set u := e + s with hu
    -- `u` pairs with `T e` and with `e`, so two easy moves chain `T e → u → e`.
    have hTeu : B u (T e) ≠ 0 := by
      rw [hu, map_add, LinearMap.add_apply, h1', zero_add, skew B hA s (T e)]
      simpa using hTes
    have hue : B e u ≠ 0 := by
      rw [hu, map_add, hA.self_eq_zero e, zero_add]
      exact hes
    refine ⟨transvectionEquiv B hA (e - u) (B e u)⁻¹
        * transvectionEquiv B hA (u - T e) (B u (T e))⁻¹,
      mul_mem (Subgroup.subset_closure (mem_transvectionGens B hA _ _))
        (Subgroup.subset_closure (mem_transvectionGens B hA _ _)), ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, transvection_move B hA hTeu, transvection_move B hA hue]
    · intro w hw
      have hv1w : B (u - T e) w = 0 := by
        rw [map_sub, LinearMap.sub_apply, hu, map_add, LinearMap.add_apply, hfix_orth w hw,
          hsw w hw, add_zero, sub_self]
      have hv2w : B (e - u) w = 0 := by
        rw [map_sub, LinearMap.sub_apply, hu, map_add, LinearMap.add_apply, hsw w hw, add_zero,
          sub_self]
      rw [LinearEquiv.mul_apply, transvection_fixes_of_orthogonal B hA _ hv1w,
        transvection_fixes_of_orthogonal B hA _ hv2w]

/-! ## Isometries form a group, and the generation theorem -/

theorem isSymplecticEquiv_one : IsSymplecticEquiv B (1 : V ≃ₗ[F] V) := fun _ _ => rfl

theorem isSymplecticEquiv_mul {a b : V ≃ₗ[F] V} (ha : IsSymplecticEquiv B a)
    (hb : IsSymplecticEquiv B b) : IsSymplecticEquiv B (a * b) := by
  intro x y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]

theorem isSymplecticEquiv_symm {a : V ≃ₗ[F] V} (ha : IsSymplecticEquiv B a) :
    IsSymplecticEquiv B a.symm := by
  intro x y
  have h := ha (a.symm x) (a.symm y)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem isSymplecticEquiv_inv {a : V ≃ₗ[F] V} (ha : IsSymplecticEquiv B a) :
    IsSymplecticEquiv B a⁻¹ := isSymplecticEquiv_symm B ha

/-- Every product of transvections is an isometry — needed to recurse. -/
theorem isSymplecticEquiv_of_mem_closure (hA : B.IsAlt) {g : V ≃ₗ[F] V}
    (hg : g ∈ Subgroup.closure (transvectionGens B hA)) : IsSymplecticEquiv B g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨v, c, rfl⟩ := hx; exact transvectionEquiv_isSymplectic B hA v c
  | one => exact isSymplecticEquiv_one B
  | mul a b _ _ iha ihb => exact isSymplecticEquiv_mul B iha ihb
  | inv a _ iha => exact isSymplecticEquiv_inv B iha

theorem eq_one_of_fixedSpace_top {T : V ≃ₗ[F] V} (htop : fixedSpace T = ⊤) : T = 1 := by
  refine LinearEquiv.ext fun x => ?_
  have hx : T x = x := mem_fixedSpace.mp (htop.ge Submodule.mem_top)
  simpa using hx

/-- The codimension induction. -/
theorem transvections_generate_sp_aux [FiniteDimensional F V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) :
    ∀ (n : ℕ) (T : V ≃ₗ[F] V), IsSymplecticEquiv B T →
      Module.finrank F V - Module.finrank F (fixedSpace T) ≤ n →
      T ∈ Subgroup.closure (transvectionGens B hA) := by
  intro n
  induction n with
  | zero =>
    intro T _ hle
    have hsub : Module.finrank F (fixedSpace T) ≤ Module.finrank F V := Submodule.finrank_le _
    have hfull : Module.finrank F (fixedSpace T) = Module.finrank F V := by omega
    rw [eq_one_of_fixedSpace_top (Submodule.eq_top_of_finrank_eq hfull)]
    exact Subgroup.one_mem _
  | succ n IH =>
    intro T hT hle
    by_cases htop : fixedSpace T = ⊤
    · rw [eq_one_of_fixedSpace_top htop]; exact Subgroup.one_mem _
    · obtain ⟨e, he⟩ : ∃ e, T e ≠ e := by
        by_contra hcon
        apply htop
        rw [Submodule.eq_top_iff']
        intro x
        rw [mem_fixedSpace]
        by_contra hx
        exact hcon ⟨x, hx⟩
      obtain ⟨g, hg, hge, hgfix⟩ := moveStep B hN hA hT he
      set T1 := g * T with hT1def
      have hT1iso : IsSymplecticEquiv B T1 :=
        isSymplecticEquiv_mul B (isSymplecticEquiv_of_mem_closure B hA hg) hT
      have hfix_le : fixedSpace T ≤ fixedSpace T1 := by
        intro w hw
        rw [mem_fixedSpace] at hw ⊢
        rw [hT1def, LinearEquiv.mul_apply, hw]
        exact hgfix w hw
      have he_mem : e ∈ fixedSpace T1 := by
        rw [mem_fixedSpace, hT1def, LinearEquiv.mul_apply]; exact hge
      have he_notmem : e ∉ fixedSpace T := fun h => he (mem_fixedSpace.mp h)
      have hlt : fixedSpace T < fixedSpace T1 :=
        lt_of_le_of_ne hfix_le (fun heq => he_notmem (heq.symm ▸ he_mem))
      have hfrank := Submodule.finrank_lt_finrank_of_lt hlt
      have hsub : Module.finrank F (fixedSpace T1) ≤ Module.finrank F V := Submodule.finrank_le _
      have hle1 : Module.finrank F V - Module.finrank F (fixedSpace T1) ≤ n := by omega
      have hT1mem : T1 ∈ Subgroup.closure (transvectionGens B hA) := IH T1 hT1iso hle1
      have hTeq : T = g⁻¹ * T1 := by rw [hT1def, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hTeq]
      exact mul_mem (inv_mem hg) hT1mem

/-- **Transvections generate the symplectic group** (any field). Every isometry of a nondegenerate
alternating form on a finite-dimensional space is a product of symplectic transvections. -/
theorem transvections_generate_sp [FiniteDimensional F V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) {T : V ≃ₗ[F] V} (hT : IsSymplecticEquiv B T) :
    T ∈ Subgroup.closure (transvectionGens B hA) :=
  transvections_generate_sp_aux B hN hA _ T hT (Nat.le_refl _)

end ECCLib.SpGen

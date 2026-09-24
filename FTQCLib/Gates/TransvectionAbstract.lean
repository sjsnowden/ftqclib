/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Gates.Transvection
import FTQCLib.Stabilizer.Witt
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Transvections over an abstract symplectic space

The transvections of `FTQCLib.Gates.Transvection` are specific to `Pauli n` and `omega`. The
proof that transvections generate the symplectic group descends by induction into subspaces,
so it must run over an **abstract** finite-dimensional `(ZMod 2)`-space `V` with a
non-degenerate alternating bilinear form `B`. This file builds the abstract transvection
`transvectionEquivB B v : V ≃ₗ V` (`u ↦ u + B v u · v`), its structural lemmas, and the
bridge back to the concrete transvection on `Pauli n` (`transvectionEquivB_omega`).

The pivot lemma `transvection_fixes_of_orthogonal` (a transvection by `v` fixes everything
`B`-orthogonal to `v`) lets the generation proof keep its accumulated fixed subspace intact — the
role a restrict-to-complement step would play in a subtype recursion.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)

/-! ## The abstract transvection -/

/-- The linear part of the transvection by `v` for a bilinear form `B`: `u ↦ u + B v u · v`. -/
def transvectionLinB (v : V) : V →ₗ[ZMod 2] V :=
  LinearMap.id + LinearMap.smulRight (B v) v

@[simp] theorem transvectionLinB_apply (v u : V) :
    transvectionLinB B v u = u + B v u • v := rfl

/-- For an alternating `B` (`B v v = 0`), the transvection is an involution. -/
theorem transvectionLinB_involutive (hA : B.IsAlt) (v : V) :
    transvectionLinB B v ∘ₗ transvectionLinB B v = LinearMap.id := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.comp_apply, transvectionLinB_apply, LinearMap.id_coe, id_eq]
  have hb : B v (u + B v u • v) = B v u := by
    rw [map_add, map_smul, hA.self_eq_zero v, smul_zero, add_zero]
  rw [hb, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

/-- The abstract symplectic transvection by `v`, as a linear automorphism of `V`. -/
def transvectionEquivB (hA : B.IsAlt) (v : V) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofLinear (transvectionLinB B v) (transvectionLinB B v)
    (transvectionLinB_involutive B hA v) (transvectionLinB_involutive B hA v)

@[simp] theorem transvectionEquivB_apply (hA : B.IsAlt) (v u : V) :
    transvectionEquivB B hA v u = u + B v u • v := by
  simp only [transvectionEquivB, LinearEquiv.ofLinear_apply, transvectionLinB_apply]

/-- **The pivot lemma.** A transvection by `v` fixes every vector `B`-orthogonal to `v`, keeping the
accumulated fixed subspace intact during the generation induction. -/
theorem transvection_fixes_of_orthogonal (hA : B.IsAlt) {v u : V} (h : B v u = 0) :
    transvectionEquivB B hA v u = u := by
  rw [transvectionEquivB_apply, h, zero_smul, add_zero]

/-! ## Isometry and conjugation -/

/-- A transvection preserves the form `B`, hence is a `B`-symplectic automorphism. -/
theorem transvectionEquivB_isSymplectic (hA : B.IsAlt) (v : V) :
    IsSymplecticEquiv B (transvectionEquivB B hA v) := by
  intro p q
  simp only [transvectionEquivB_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hA.self_eq_zero, mul_zero, add_zero]
  rw [FTQCLib.Stabilizer.BilinForm_alt_symm B hA v p, mul_comm (B v q) (B v p), add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

/-- **Conjugation law.** For a `B`-isometry `T`, conjugating a transvection by `T` gives the
transvection by the transported vector: `T · τ_v · T⁻¹ = τ_{T v}`. -/
theorem transvectionEquivB_conj (hA : B.IsAlt) {T : V ≃ₗ[ZMod 2] V}
    (hT : IsSymplecticEquiv B T) (v : V) :
    transvectionEquivB B hA (T v) = (T.symm.trans (transvectionEquivB B hA v)).trans T := by
  refine LinearEquiv.ext fun u => ?_
  have h : B (T v) u = B v (T.symm u) := by
    have := hT v (T.symm u)
    rwa [LinearEquiv.apply_symm_apply] at this
  simp only [LinearEquiv.trans_apply, transvectionEquivB_apply, map_add, map_smul,
    LinearEquiv.apply_symm_apply]
  rw [h]

/-! ## Bridge to the concrete transvection on `Pauli n` -/

/-- The symplectic form `omegaBilin` on `Pauli n` is alternating. -/
theorem omegaBilin_isAlt {n : ℕ} : (omegaBilin (n := n)).IsAlt := by
  intro p
  rw [omegaBilin_apply]
  exact omega_self p

/-- The abstract transvection for `omegaBilin` is the concrete transvection on `Pauli n`. -/
theorem transvectionEquivB_omega {n : ℕ} (v : Pauli n) :
    transvectionEquivB omegaBilin omegaBilin_isAlt v = transvectionEquiv v := by
  refine LinearEquiv.ext fun u => ?_
  rw [transvectionEquivB_apply, transvectionEquiv_apply, omegaBilin_apply]

/-! ## The char-2 move and the simultaneous-pair existence

The two pieces of the move step, isolated. `transvection_move` is the single-transvection move
`a ↦ e` (when `B a e = 1`); `exists_simultaneous_pair` supplies the bridge vector used when the move
needs two transvections. -/

/-- `w + w = 0` for a vector in a `ZMod 2`-module (char-2 cancellation on vectors, not scalars). -/
private theorem add_self_eq_zero_v (w : V) : w + w = 0 := by
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  calc w + w = (1 : ZMod 2) • w + (1 : ZMod 2) • w := by rw [one_smul]
    _ = ((1 : ZMod 2) + 1) • w := (add_smul 1 1 w).symm
    _ = (0 : ZMod 2) • w := by rw [h2]
    _ = 0 := zero_smul _ _

/-- **The char-2 one-transvection move.** When `B a e = 1`, the transvection by `a + e` sends `a` to
`e`: over `𝔽₂`, `τ_{a+e} a = a + B(a+e, a)·(a+e) = a + (a+e) = e`. -/
theorem transvection_move (hA : B.IsAlt) {a e : V} (h : B a e = 1) :
    transvectionEquivB B hA (a + e) a = e := by
  have hb : B (a + e) a = 1 := by
    rw [map_add, LinearMap.add_apply, hA.self_eq_zero a, zero_add,
      FTQCLib.Stabilizer.BilinForm_alt_symm B hA a e]
    exact h
  rw [transvectionEquivB_apply, hb, one_smul, ← add_assoc, add_self_eq_zero_v a, zero_add]

/-- **Simultaneous pair.** For nonzero `e, x` and a non-degenerate `B`, a single `u` is paired with
both: `B e u = 1` and `B x u = 1`. Elementary: pick `a` with `B e a = 1` and `b` with `B x b = 1`;
then `a`, `b`, or `a + b` works, by cases on `B x a` and `B e b`. -/
theorem exists_simultaneous_pair (hN : B.Nondegenerate) {e x : V} (he : e ≠ 0) (hx : x ≠ 0) :
    ∃ u : V, B e u = 1 ∧ B x u = 1 := by
  obtain ⟨a, ha⟩ := FTQCLib.Stabilizer.exists_pair_eq_one B hN he
  obtain ⟨b, hb⟩ := FTQCLib.Stabilizer.exists_pair_eq_one B hN hx
  have dich : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
  by_cases hxa : B x a = 1
  · exact ⟨a, ha, hxa⟩
  · by_cases heb : B e b = 1
    · exact ⟨b, heb, hb⟩
    · refine ⟨a + b, ?_, ?_⟩
      · rw [map_add, ha, dich _ heb, add_zero]
      · rw [map_add, dich _ hxa, hb, zero_add]

/-! ## Wave C — the move step (easy case)

The inductive step of B1 reduces a `B`-isometry `T` by fixing one more vector with a transvection
word. The **easy case**, when `B (T e) e = 1`, mirrors the one-reflection step of Mathlib's
`reflections_generate_dim_aux`: the transvection by `T e + e` sends `T e` back to `e` and fixes
everything `T` already fixed (since `T e + e` is `B`-orthogonal to the fixed space). The general
(char-2) case, when `B (T e) e = 0`, needs a two-transvection bridge and is handled separately. -/

/-- **Easy-case move.** When `B (T e) e = 1`, the transvection `g := τ_{T e + e}` sends `T e` to `e`
and fixes every `T`-fixed vector, so `g ∘ T` fixes `e` and everything `T` fixed. -/
theorem move_easy (hA : B.IsAlt) {T : V ≃ₗ[ZMod 2] V} (hT : IsSymplecticEquiv B T)
    (e : V) (h1 : B (T e) e = 1) :
    transvectionEquivB B hA (T e + e) (T e) = e ∧
      ∀ u, T u = u → transvectionEquivB B hA (T e + e) u = u := by
  refine ⟨transvection_move B hA h1, fun u hu => ?_⟩
  apply transvection_fixes_of_orthogonal B hA
  have hiso : B (T e) u = B e u := by
    have h := hT e u
    rwa [hu] at h
  rw [map_add, LinearMap.add_apply, hiso, CharTwo.add_self_eq_zero]

/-! ## Wave C — the fixed space and its key properties -/

/-- The fixed subspace of `T`: the kernel of `T - id`. -/
def fixedSpace (T : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  LinearMap.ker (T.toLinearMap - LinearMap.id)

@[simp] theorem mem_fixedSpace {T : V ≃ₗ[ZMod 2] V} {u : V} : u ∈ fixedSpace T ↔ T u = u := by
  simp only [fixedSpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, sub_eq_zero]

/-- **The image of a moved vector is itself unfixed.** If `T e ≠ e` then `T e ∉ fixedSpace T` — else
`T (T e) = T e = T e` would force `T e = e` by injectivity. The linchpin of the hard-case move: it
gives `T e ∉ (fixedSpace T)ᗮᗮ`, so `T e` pairs non-trivially with the orthogonal complement. -/
theorem Te_notMem_fixedSpace {T : V ≃ₗ[ZMod 2] V} {e : V} (he : T e ≠ e) :
    T e ∉ fixedSpace T := by
  rw [mem_fixedSpace]
  intro h
  exact he (T.injective h.symm).symm

/-! ## Wave C — orthogonal-relative existence (for the hard-case bridge)

When `y ∉ W` (`B` non-degenerate), `y ∉ (W^⊥)^⊥ = W`, so `y` pairs non-trivially with some vector
*inside* `W^⊥`. Applied to `e` and `T e` (both outside `fixedSpace`), this yields a bridge vector in
`(fixedSpace)^⊥` — what lets the char-2 move fix `e` while keeping the fixed space fixed. -/

/-- For `y ∉ W`, there is `s ∈ W^⊥` with `B y s = 1` (via the double-orthogonal identity). -/
theorem exists_pair_one_of_notMem [FiniteDimensional (ZMod 2) V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) {W : Submodule (ZMod 2) V} {y : V} (hy : y ∉ W) :
    ∃ s, s ∈ LinearMap.BilinForm.orthogonal B W ∧ B y s = 1 := by
  have hRefl : B.IsRefl := hA.isRefl
  have hyy : y ∉ LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B W) := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal hN hRefl W]; exact hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hyy
  simp only [not_forall, LinearMap.BilinForm.isOrtho_def] at hyy
  obtain ⟨s, hs, hsy⟩ := hyy
  refine ⟨s, hs, ?_⟩
  have dich : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  rw [FTQCLib.Stabilizer.BilinForm_alt_symm B hA s y]
  exact dich _ hsy

/-- For `e, x ∉ W`, a single `s ∈ W^⊥` pairs with both: `B e s = 1 ∧ B x s = 1`. The `W^⊥`-relative
simultaneous pair (same 3-case construction as `exists_simultaneous_pair`, in the subspace). -/
theorem exists_simultaneous_pair_mem [FiniteDimensional (ZMod 2) V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) {W : Submodule (ZMod 2) V} {e x : V} (he : e ∉ W) (hx : x ∉ W) :
    ∃ s, s ∈ LinearMap.BilinForm.orthogonal B W ∧ B e s = 1 ∧ B x s = 1 := by
  obtain ⟨a, ha, hea⟩ := exists_pair_one_of_notMem B hN hA he
  obtain ⟨b, hb, hxb⟩ := exists_pair_one_of_notMem B hN hA hx
  have dich : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
  by_cases hxa : B x a = 1
  · exact ⟨a, ha, hea, hxa⟩
  · by_cases heb : B e b = 1
    · exact ⟨b, hb, heb, hxb⟩
    · refine ⟨a + b, Submodule.add_mem _ ha hb, ?_, ?_⟩
      · rw [map_add, hea, dich _ heb, add_zero]
      · rw [map_add, dich _ hxa, hxb, zero_add]

/-! ## Wave C — the move step -/

/-- The set of all transvections of `B` (the generating set for the symplectic group). -/
def transvectionGens (hA : B.IsAlt) : Set (V ≃ₗ[ZMod 2] V) :=
  {h | ∃ v, h = transvectionEquivB B hA v}

theorem mem_transvectionGens (hA : B.IsAlt) (v : V) :
    transvectionEquivB B hA v ∈ transvectionGens B hA :=
  ⟨v, rfl⟩

/-- **The move step.** If `T e ≠ e`, a transvection word `g` (in the transvection-generated
subgroup) sends `T e` back to `e` and fixes every `T`-fixed vector. Easy case `B (T e) e = 1`: one
transvection. Char-2 case `B (T e) e = 0`: a two-transvection bridge through `(fixedSpace T)^⊥`. -/
theorem moveStep [FiniteDimensional (ZMod 2) V] (hN : B.Nondegenerate) (hA : B.IsAlt)
    {T : V ≃ₗ[ZMod 2] V} (hT : IsSymplecticEquiv B T) {e : V} (he : T e ≠ e) :
    ∃ g : V ≃ₗ[ZMod 2] V, g ∈ Subgroup.closure (transvectionGens B hA) ∧
      g (T e) = e ∧ ∀ w, T w = w → g w = w := by
  have dich : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
  by_cases h1 : B (T e) e = 1
  · obtain ⟨hge, hgfix⟩ := move_easy B hA hT e h1
    exact ⟨transvectionEquivB B hA (T e + e),
      Subgroup.subset_closure (mem_transvectionGens B hA _), hge, hgfix⟩
  · have h0 : B (T e) e = 0 := dich _ h1
    have heW : e ∉ fixedSpace T := fun h => he (mem_fixedSpace.mp h)
    have hTeW : T e ∉ fixedSpace T := Te_notMem_fixedSpace he
    obtain ⟨s, hs, hes, hTes⟩ := exists_simultaneous_pair_mem B hN hA heW hTeW
    have hsw : ∀ w ∈ fixedSpace T, B s w = 0 := by
      intro w hwW
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hs) w hwW
      rw [LinearMap.BilinForm.isOrtho_def] at h
      rw [FTQCLib.Stabilizer.BilinForm_alt_symm B hA w s]; exact h
    set u := e + s with hu
    have hTeu : B (T e) u = 1 := by rw [hu, map_add, h0, hTes, zero_add]
    have hue : B u e = 1 := by
      rw [hu, map_add, LinearMap.add_apply, hA.self_eq_zero e, zero_add,
        FTQCLib.Stabilizer.BilinForm_alt_symm B hA e s, hes]
    refine ⟨transvectionEquivB B hA (u + e) * transvectionEquivB B hA (T e + u),
      mul_mem (Subgroup.subset_closure (mem_transvectionGens B hA _))
        (Subgroup.subset_closure (mem_transvectionGens B hA _)), ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, transvection_move B hA hTeu, transvection_move B hA hue]
    · intro w hw
      have hwW : w ∈ fixedSpace T := mem_fixedSpace.mpr hw
      have hiso : B (T e) w = B e w := by have h := hT e w; rwa [hw] at h
      have hv1w : B (T e + u) w = 0 := by
        rw [hu, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hiso, hsw w hwW,
          add_zero, CharTwo.add_self_eq_zero]
      have hv2w : B (u + e) w = 0 := by
        rw [hu, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hsw w hwW, add_zero,
          CharTwo.add_self_eq_zero]
      rw [LinearEquiv.mul_apply, transvection_fixes_of_orthogonal B hA hv1w,
        transvection_fixes_of_orthogonal B hA hv2w]

/-! ## Wave D — transvections generate the symplectic group

The `B`-isometries form a subgroup of `V ≃ₗ V`; the transvections lie in it, so any product of
transvections is an isometry (needed to recurse). Then strong induction on the codimension of the
fixed space proves every isometry is a product of transvections. -/

theorem isSymplecticEquiv_one : IsSymplecticEquiv B (1 : V ≃ₗ[ZMod 2] V) := fun _ _ => rfl

theorem isSymplecticEquiv_mul {a b : V ≃ₗ[ZMod 2] V} (ha : IsSymplecticEquiv B a)
    (hb : IsSymplecticEquiv B b) : IsSymplecticEquiv B (a * b) := by
  intro x y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]

theorem isSymplecticEquiv_symm {a : V ≃ₗ[ZMod 2] V} (ha : IsSymplecticEquiv B a) :
    IsSymplecticEquiv B a.symm := by
  intro x y
  have h := ha (a.symm x) (a.symm y)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

theorem isSymplecticEquiv_inv {a : V ≃ₗ[ZMod 2] V} (ha : IsSymplecticEquiv B a) :
    IsSymplecticEquiv B a⁻¹ := isSymplecticEquiv_symm B ha

/-- Every element of the transvection-generated subgroup is a `B`-isometry. -/
theorem isSymplecticEquiv_of_mem_closure (hA : B.IsAlt) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Subgroup.closure (transvectionGens B hA)) : IsSymplecticEquiv B g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact transvectionEquivB_isSymplectic B hA v
  | one => exact isSymplecticEquiv_one B
  | mul a b _ _ iha ihb => exact isSymplecticEquiv_mul B iha ihb
  | inv a _ iha => exact isSymplecticEquiv_inv B iha

/-- If the fixed space is everything, the map is the identity. -/
theorem eq_one_of_fixedSpace_top {T : V ≃ₗ[ZMod 2] V} (htop : fixedSpace T = ⊤) :
    T = 1 := by
  refine LinearEquiv.ext fun x => ?_
  have hx : T x = x := mem_fixedSpace.mp (htop.ge Submodule.mem_top)
  simpa using hx

/-- **Generation, abstract form.** Every `B`-isometry is a product of transvections. Strong
induction on the codimension `finrank V − finrank (fixedSpace T)`: at codim 0 the map is `1`; else a
`moveStep` produces a transvection word strictly enlarging the fixed space, and the IH applies. -/
theorem transvections_generate_sp_aux [FiniteDimensional (ZMod 2) V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) :
    ∀ (n : ℕ) (T : V ≃ₗ[ZMod 2] V), IsSymplecticEquiv B T →
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (fixedSpace T) ≤ n →
      T ∈ Subgroup.closure (transvectionGens B hA) := by
  intro n
  induction n with
  | zero =>
    intro T _ hle
    have hsub : Module.finrank (ZMod 2) (fixedSpace T) ≤ Module.finrank (ZMod 2) V :=
      Submodule.finrank_le _
    have hfull : Module.finrank (ZMod 2) (fixedSpace T) = Module.finrank (ZMod 2) V := by omega
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
        rw [hT1def, LinearEquiv.mul_apply, hw]; exact hgfix w hw
      have he_mem : e ∈ fixedSpace T1 := by
        rw [mem_fixedSpace, hT1def, LinearEquiv.mul_apply]; exact hge
      have he_notmem : e ∉ fixedSpace T := fun h => he (mem_fixedSpace.mp h)
      have hlt : fixedSpace T < fixedSpace T1 :=
        lt_of_le_of_ne hfix_le (fun heq => he_notmem (heq.symm ▸ he_mem))
      have hfrank := Submodule.finrank_lt_finrank_of_lt hlt
      have hsub : Module.finrank (ZMod 2) (fixedSpace T1) ≤ Module.finrank (ZMod 2) V :=
        Submodule.finrank_le _
      have hle1 : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (fixedSpace T1) ≤ n := by
        omega
      have hT1mem : T1 ∈ Subgroup.closure (transvectionGens B hA) := IH T1 hT1iso hle1
      have hTeq : T = g⁻¹ * T1 := by rw [hT1def, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hTeq]
      exact mul_mem (inv_mem hg) hT1mem

/-- **Generation.** Every `B`-isometry lies in the subgroup generated by transvections. -/
theorem transvections_generate_sp [FiniteDimensional (ZMod 2) V] (hN : B.Nondegenerate)
    (hA : B.IsAlt) {T : V ≃ₗ[ZMod 2] V} (hT : IsSymplecticEquiv B T) :
    T ∈ Subgroup.closure (transvectionGens B hA) :=
  transvections_generate_sp_aux B hN hA _ T hT (Nat.le_refl _)

end FTQCLib.Gates

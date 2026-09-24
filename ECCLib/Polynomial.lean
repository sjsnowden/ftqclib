/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Instances.AddCircle.Real

set_option linter.style.longLine false

/-!
# Classical and nonclassical polynomials (Hatami–Hatami–Lovett, Ch 6, Def 6.1 / 6.2)

A function `P : V → G` is a **polynomial of degree `≤ d`** (the *local* definition) iff every `(d+1)`-fold
iterated additive derivative — over arbitrary directions — vanishes. Over `G = 𝔽_p` this is the classical
notion; over `G = 𝕋 = ℝ/ℤ` it is the **nonclassical** notion of Tao–Ziegler (HHL Def 6.2): extra `𝕋`-valued
solutions with `p`-power denominators appear because the global↔local equivalence needs division by `d!`,
impossible over the torus.

Reference: Hatami–Hatami–Lovett, Ch 6. Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V] {G : Type*} [AddCommGroup G]

/-- **Def 6.1 / 6.2 (local definition).** `P : V → G` is a **polynomial of degree `≤ d`** iff every
`(d+1)`-fold iterated additive derivative, over arbitrary directions, is the zero function. -/
def IsPolyDegLE (d : ℕ) (P : V → G) : Prop :=
  ∀ ys : Fin (d + 1) → V, iteratedFwdDiff (List.ofFn ys) P = 0

/-- **Monotonicity in the degree:** a polynomial of degree `≤ d` is also of degree `≤ d+1`. -/
theorem IsPolyDegLE.mono_succ {d : ℕ} {P : V → G} (h : IsPolyDegLE d P) :
    IsPolyDegLE (d + 1) P := by
  intro ys
  rw [List.ofFn_succ, iteratedFwdDiff_cons, h fun i => ys i.succ, fwdDiff_zero]

/-- **Monotonicity in the degree** (general): `d ≤ e` and degree `≤ d` give degree `≤ e`. -/
theorem IsPolyDegLE.mono {d : ℕ} {f : V → G} (h : IsPolyDegLE d f) {e : ℕ} (hde : d ≤ e) :
    IsPolyDegLE e f := by
  induction e, hde using Nat.le_induction with
  | base => exact h
  | succ e hde ih => exact ih.mono_succ

/-- **A degree-`≤ d` function is killed by any iterated difference of length `≥ d+1`** (over arbitrary
directions). The trivial/forward complement of the unit-directions reduction. -/
theorem IsPolyDegLE.iteratedFwdDiff_eq_zero {d : ℕ} {f : V → G} (h : IsPolyDegLE d f)
    {l : List V} (hl : d + 1 ≤ l.length) : iteratedFwdDiff l f = 0 := by
  have hlen : (l.length - 1) + 1 = l.length := by omega
  have hkey := (h.mono (by omega : d ≤ l.length - 1))
    (fun j : Fin ((l.length - 1) + 1) => l.get (Fin.cast hlen j))
  rwa [show List.ofFn (fun j : Fin ((l.length - 1) + 1) => l.get (Fin.cast hlen j)) = l from by
    apply List.ext_getElem
    · rw [List.length_ofFn]; omega
    · intro p hp1 hp2
      simp only [List.getElem_ofFn, List.get_eq_getElem, Fin.cast_mk]] at hkey

/-!
## The mother example — a genuine nonclassical polynomial over `ℝ/ℤ`

HHL Ch 6 give `Q(1) = 1/4` over `𝔽₂` as the smallest nonclassical polynomial: degree exactly 2 (not 1), and
genuinely `𝕋`-valued because `1/4 ∉ (1/2)ℤ/ℤ`. We build it in two steps. First the **finite depth-1 model** on
`ZMod 4`, where the degree is decidable. Then we transport it to the **true torus** `ℝ/ℤ` along the injective
homomorphism `ZMod.toAddCircle`, so every statement below (`…T`) is about the genuine `𝕋`-valued object — not a
finite surrogate, and with no unproven bridge.
-/

/-- The mother example on the finite depth-1 model `(𝔽₂)¹ → ZMod 4`, `v ↦ |v₀|`. -/
def motherExample : (Fin 1 → ZMod 2) → ZMod 4 := fun v => ((v 0).val : ZMod 4)

/-- On the finite model, degree `≤ 2` (decidable). -/
theorem motherExample_isPolyDegLE_two : IsPolyDegLE 2 motherExample := by
  unfold IsPolyDegLE; decide

/-- On the finite model, degree *exactly* 2: not `≤ 1` (decidable). -/
theorem motherExample_not_isPolyDegLE_one : ¬ IsPolyDegLE 1 motherExample := by
  unfold IsPolyDegLE; decide

/-! ### Transport to the genuine torus `ℝ/ℤ` -/

/-- **Composing with an injective additive hom preserves *and reflects* the degree.** Together with
`iteratedFwdDiff_comp_addMonoidHom`, this transports a polynomial's degree between coefficient groups — here
along `ZMod 4 ↪ ℝ/ℤ`. -/
lemma isPolyDegLE_comp_iff {G' : Type*} [AddCommGroup G'] {φ : G →+ G'}
    (hφ : Function.Injective φ) {d : ℕ} {P : V → G} :
    IsPolyDegLE d (φ ∘ P) ↔ IsPolyDegLE d P := by
  constructor
  · intro h ys
    have key : (φ : G → G') ∘ iteratedFwdDiff (List.ofFn ys) P = 0 := by
      rw [← iteratedFwdDiff_comp_addMonoidHom]; exact h ys
    funext x
    have hx := congrFun key x
    simp only [Function.comp_apply, Pi.zero_apply] at hx ⊢
    exact hφ (by rw [hx, map_zero])
  · intro h ys
    rw [iteratedFwdDiff_comp_addMonoidHom, h ys]
    funext x; simp

/-- The **genuine torus-valued mother example** `Q : (𝔽₂)¹ → ℝ/ℤ`, `Q(v) = |v₀| / 4` — so `Q(1) = 1/4`. -/
noncomputable def motherExampleT : (Fin 1 → ZMod 2) → UnitAddCircle :=
  (ZMod.toAddCircle : ZMod 4 →+ UnitAddCircle) ∘ motherExample

/-- Its defining value: `Q(1) = 1/4` in `ℝ/ℤ` (the property that makes it *the* mother example). -/
theorem motherExampleT_one : motherExampleT (fun _ => 1) = ((1 / 4 : ℝ) : UnitAddCircle) := by
  have h1 : motherExample (fun _ => 1) = ((1 : ℕ) : ZMod 4) := by decide
  rw [motherExampleT, Function.comp_apply, h1, ZMod.toAddCircle_natCast]
  norm_num

/-- **The mother example over `ℝ/ℤ` is a polynomial of degree `≤ 2`.** -/
theorem motherExampleT_isPolyDegLE_two : IsPolyDegLE 2 motherExampleT :=
  (isPolyDegLE_comp_iff (ZMod.toAddCircle_injective 4)).mpr motherExample_isPolyDegLE_two

/-- **Its degree over `ℝ/ℤ` is exactly 2:** it is not of degree `≤ 1`. -/
theorem motherExampleT_not_isPolyDegLE_one : ¬ IsPolyDegLE 1 motherExampleT := fun h =>
  motherExample_not_isPolyDegLE_one ((isPolyDegLE_comp_iff (ZMod.toAddCircle_injective 4)).mp h)

/-! ### It is genuinely nonclassical -/

/-- **Classical polynomials (HHL Ch 6).** A `𝕋`-valued function is *classical of order `p`* if every value is
killed by `p` — i.e. lies in the order-`p` subgroup `(1/p)ℤ/ℤ ⊂ ℝ/ℤ`. The genuinely nonclassical polynomials
(like the mother example) need finer `p`-power denominators. -/
def IsClassical (p : ℕ) (P : V → UnitAddCircle) : Prop := ∀ x, p • P x = 0

/-- **The mother example is genuinely nonclassical:** its value `1/4` is not `2`-torsion in `ℝ/ℤ`. -/
theorem motherExampleT_not_isClassical : ¬ IsClassical 2 motherExampleT := by
  intro h
  have h2 := h (fun _ => 1)
  simp only [motherExampleT, Function.comp_apply] at h2
  rw [← map_nsmul, ZMod.toAddCircle_eq_zero] at h2
  revert h2; decide

/-! ## The unit-directions reduction (Aichinger–Moosbauer over `𝔽₂`)

Over `V = 𝔽₂ⁿ`, checking a polynomial's degree on *arbitrary* directions reduces to checking it on the `n`
standard-basis directions (with repetition allowed): `f` is degree `≤ d` iff every `(d+1)`-fold iterated
difference over basis directions vanishes (`isPolyDegLE_of_unitDirections`). The seed is the composition law
`D_{a+b} = D_a + D_b + D_a D_b` (`fwdDiff_add'`): over `𝔽₂` every direction is a subset-sum of basis vectors,
so an arbitrary-direction difference expands (`fwdDiff_sumDir_eq`) into a list-sum of *nonempty* basis
differences, and a `(d+1)`-fold product lands entirely in basis differences of length `≥ d+1`
(tracked as membership in an `AddSubgroup.closure`), which the hypothesis kills. This is the reduction the
frame's degree/level accounting meets: the basis-direction differences here are the frame's `funcDerivG`. -/

section UnitDirections

variable {n : ℕ}

/-- Iterated basis difference over a coordinate list `[i₁,…,i_k]`: `D_{e_{i₁}} ⋯ D_{e_{i_k}} g`. -/
def basisDiff (bl : List (Fin n)) (g : (Fin n → ZMod 2) → G) : (Fin n → ZMod 2) → G :=
  iteratedFwdDiff (bl.map (fun i => Pi.single i (1 : ZMod 2))) g

lemma basisDiff_nil (g : (Fin n → ZMod 2) → G) : basisDiff [] g = g := rfl

lemma basisDiff_cons (i : Fin n) (bl : List (Fin n)) (g : (Fin n → ZMod 2) → G) :
    basisDiff (i :: bl) g = fwdDiff (Pi.single i (1 : ZMod 2)) (basisDiff bl g) := by
  simp only [basisDiff, List.map_cons, iteratedFwdDiff_cons]

lemma basisDiff_append (bl₁ bl₂ : List (Fin n)) (g : (Fin n → ZMod 2) → G) :
    basisDiff (bl₁ ++ bl₂) g = basisDiff bl₁ (basisDiff bl₂ g) := by
  simp only [basisDiff, List.map_append, iteratedFwdDiff_append]

/-- **Single-direction subset expansion over `𝔽₂`.** For the direction `∑_{i ∈ is} eᵢ`, the forward
difference `D` decomposes as a list-sum of *nonempty* iterated basis differences. -/
lemma fwdDiff_sumDir_eq (g : (Fin n → ZMod 2) → G) (is : List (Fin n)) :
    ∃ bls : List (List (Fin n)), (∀ bl ∈ bls, 1 ≤ bl.length) ∧
      fwdDiff ((is.map (fun i => Pi.single i (1 : ZMod 2))).sum) g
        = (bls.map (fun bl => basisDiff bl g)).sum := by
  induction is with
  | nil =>
    exact ⟨[], by simp, by simp only [List.map_nil, List.sum_nil]; exact fwdDiff_zero_dir g⟩
  | cons i is ih =>
    obtain ⟨bls, hlen, heq⟩ := ih
    refine ⟨[i] :: bls ++ bls.map (fun bl => i :: bl), ?_, ?_⟩
    · intro bl hbl
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hbl
      rcases hbl with h | h | ⟨bl', _, rfl⟩
      · rw [h]; simp
      · exact hlen bl h
      · simp
    · have hcomp : (bls.map (fun bl => basisDiff bl g)).map (fwdDiff (Pi.single i (1 : ZMod 2)))
            = bls.map (fun bl => basisDiff (i :: bl) g) := by
        rw [List.map_map]; apply List.map_congr_left; intro bl _
        simp only [Function.comp_apply]; rw [basisDiff_cons]
      rw [List.map_cons, List.sum_cons, fwdDiff_add', heq, fwdDiff_list_sum, hcomp]
      have hei : fwdDiff (Pi.single i (1 : ZMod 2)) g = basisDiff [i] g := by
        rw [basisDiff_cons, basisDiff_nil]
      rw [hei, List.cons_append, List.map_cons, List.map_append, List.map_map, List.sum_cons,
        List.sum_append]
      simp only [Function.comp_def]; abel

/-- Every `𝔽₂`-vector is the subset-sum of its support's basis vectors. -/
lemma exists_sumDir (h : Fin n → ZMod 2) :
    ∃ is : List (Fin n), (is.map (fun i => Pi.single i (1 : ZMod 2))).sum = h := by
  refine ⟨(Finset.univ.filter (fun i => h i = 1)).toList, ?_⟩
  rw [Finset.sum_map_toList]
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  generalize h j = a
  revert a; decide

/-- **Arbitrary-direction expansion:** `D_h g` is a list-sum of nonempty basis differences. -/
lemma fwdDiff_arbitrary_expand (h : Fin n → ZMod 2) (g : (Fin n → ZMod 2) → G) :
    ∃ bls : List (List (Fin n)), (∀ bl ∈ bls, 1 ≤ bl.length) ∧
      fwdDiff h g = (bls.map (fun bl => basisDiff bl g)).sum := by
  obtain ⟨is, rfl⟩ := exists_sumDir h
  exact fwdDiff_sumDir_eq g is

/-- Given all length-`m` basis differences vanish, every length-`≥ m` one does (suffix stability). -/
lemma basisDiff_eq_zero_of_len_ge (f : (Fin n → ZMod 2) → G) {m : ℕ}
    (H : ∀ is : List (Fin n), is.length = m → basisDiff is f = 0)
    (bl : List (Fin n)) (hbl : m ≤ bl.length) : basisDiff bl f = 0 := by
  have hlen : (bl.drop (bl.length - m)).length = m := by rw [List.length_drop]; omega
  calc basisDiff bl f
      = basisDiff (bl.take (bl.length - m) ++ bl.drop (bl.length - m)) f := by
        rw [List.take_append_drop]
    _ = basisDiff (bl.take (bl.length - m)) (basisDiff (bl.drop (bl.length - m)) f) :=
        basisDiff_append _ _ _
    _ = basisDiff (bl.take (bl.length - m)) 0 := by rw [H _ hlen]
    _ = 0 := by simp only [basisDiff, iteratedFwdDiff_zero_fun]

/-- Applying `D_h` raises the closure level: it maps the "length `≥ k`" closure into "length `≥ k+1`". -/
lemma fwdDiff_closure_mem (f : (Fin n → ZMod 2) → G) (h : Fin n → ZMod 2) (k : ℕ)
    {F : (Fin n → ZMod 2) → G}
    (hF : F ∈ AddSubgroup.closure
      {G' | ∃ bl : List (Fin n), k ≤ bl.length ∧ G' = basisDiff bl f}) :
    fwdDiff h F ∈ AddSubgroup.closure
      {G' | ∃ bl : List (Fin n), k + 1 ≤ bl.length ∧ G' = basisDiff bl f} := by
  have hle : AddSubgroup.closure {G' | ∃ bl : List (Fin n), k ≤ bl.length ∧ G' = basisDiff bl f}
      ≤ (AddSubgroup.closure
          {G' | ∃ bl : List (Fin n), k + 1 ≤ bl.length ∧ G' = basisDiff bl f}).comap
          (fwdDiffHom h) := by
    rw [AddSubgroup.closure_le]
    rintro F ⟨bl, hbl, rfl⟩
    simp only [AddSubgroup.mem_comap, fwdDiffHom_apply, SetLike.mem_coe]
    obtain ⟨bls, hbls, heq⟩ := fwdDiff_arbitrary_expand h (basisDiff bl f)
    rw [heq]
    apply AddSubgroup.list_sum_mem
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨bl', hbl', rfl⟩ := hx
    rw [← basisDiff_append]
    apply AddSubgroup.subset_closure
    exact ⟨bl' ++ bl, by rw [List.length_append]; have := hbls bl' hbl'; omega, rfl⟩
  exact hle hF

/-- `iteratedFwdDiff hs f` lies in the closure of basis differences of length `≥ hs.length`. -/
lemma iteratedFwdDiff_closure_mem (f : (Fin n → ZMod 2) → G) (hs : List (Fin n → ZMod 2)) :
    iteratedFwdDiff hs f ∈ AddSubgroup.closure
      {G' | ∃ bl : List (Fin n), hs.length ≤ bl.length ∧ G' = basisDiff bl f} := by
  induction hs with
  | nil =>
    apply AddSubgroup.subset_closure
    exact ⟨[], by simp, (basisDiff_nil f).symm⟩
  | cons h hs ih =>
    rw [iteratedFwdDiff_cons]
    exact fwdDiff_closure_mem f h hs.length ih

/-- **The unit-directions reduction (list form).** If every length-`m` iterated basis difference of `f`
vanishes, then so does every length-`m` iterated difference over *arbitrary* directions. -/
theorem iteratedFwdDiff_eq_zero_of_basisDiff (f : (Fin n → ZMod 2) → G) {m : ℕ}
    (H : ∀ is : List (Fin n), is.length = m → basisDiff is f = 0)
    (hs : List (Fin n → ZMod 2)) (hlen : hs.length = m) :
    iteratedFwdDiff hs f = 0 := by
  have hmem := iteratedFwdDiff_closure_mem f hs
  rw [hlen] at hmem
  have hbot : AddSubgroup.closure
      {G' | ∃ bl : List (Fin n), m ≤ bl.length ∧ G' = basisDiff bl f} = ⊥ := by
    rw [eq_bot_iff, AddSubgroup.closure_le]
    rintro F ⟨bl, hbl, rfl⟩
    simp only [AddSubgroup.coe_bot, Set.mem_singleton_iff]
    exact basisDiff_eq_zero_of_len_ge f H bl hbl
  rw [hbot] at hmem
  exact AddSubgroup.mem_bot.mp hmem

/-- **The unit-directions reduction (`Fin` form / Aichinger–Moosbauer over `𝔽₂`).** If every `(d+1)`-fold
iterated difference of `f` over *standard-basis* directions (repetition allowed) vanishes, then `f` is a
polynomial of degree `≤ d`: every arbitrary-direction iterate vanishes. The converse is immediate, so this
is the reduction to basis directions the frame bridge uses. -/
theorem isPolyDegLE_of_unitDirections (f : (Fin n → ZMod 2) → G) (d : ℕ)
    (H : ∀ is : Fin (d + 1) → Fin n,
        iteratedFwdDiff (List.ofFn (fun j => Pi.single (is j) (1 : ZMod 2))) f = 0) :
    IsPolyDegLE d f := by
  have H' : ∀ is : List (Fin n), is.length = d + 1 → basisDiff is f = 0 := by
    intro is hlis
    have hmap : is.map (fun i => Pi.single i (1 : ZMod 2))
        = List.ofFn (fun j : Fin (d + 1) =>
            Pi.single (is.get (Fin.cast hlis.symm j)) (1 : ZMod 2)) := by
      apply List.ext_getElem
      · simp [hlis]
      · intro p h1 h2
        simp only [List.getElem_map, List.getElem_ofFn, List.get_eq_getElem, Fin.cast_mk]
    rw [basisDiff, hmap]
    exact H _
  intro ys
  exact iteratedFwdDiff_eq_zero_of_basisDiff f H' (List.ofFn ys) List.length_ofFn

end UnitDirections

end ECCLib

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GowersNorm

set_option linter.style.longLine false

/-!
# The Gowers–Cauchy–Schwarz inequality

The main result of this file is `gowersCauchySchwarz`:
`‖⟨(f_ω)_{ω∈{0,1}^d}⟩_{U^d}‖ ≤ ∏_ω ‖f_ω‖_{U^d}` (standard; Tao–Vu, *Additive Combinatorics*, Eq. 11.6 — it
is **not** proved in Green–Tao–Ziegler, which states the norm definition and defers the norm property). It
bounds the multilinear **box inner product** of a family of functions indexed by the cube `{0,1}^d` by the
product of their Gowers norms.

The proof assembles in four movements:

1. **Peeling factorization** (`gowersBox_succ`) + **complex Cauchy–Schwarz** (`norm_expect_mul_conj_sq_le`)
   give the single CS step `norm_gowersBox_succ_sq_le`, recast against `collapse0` as
   `norm_gowersBox_succ_sq_le'`: `‖gowersBox (d+1) F‖²` ≤ the product of the two collapsed self-energies.
2. **Explicit product form** (`boxProdE`, `boxFn_eq_boxProdE`) and **cube-coordinate symmetry**
   (`gowersBox_perm`): the box is invariant under permuting the cube axes, so the CS step can peel *any*
   coordinate, not just the first.
3. **Self-box = norm** (`norm_gowersBox_const_eq_pow`): the box of a constant family `F ≡ g` is `‖g‖_{U^d}^{2^d}`.
4. **The leaf induction** (`GLeafGen`): peel each free coordinate in turn (swap to front, diagonalise,
   recurse), reaching the `2^d` fully-diagonalised self-boxes; then take the `2^d`-th root.

The design choice that keeps step 1 tractable: `boxFn` is defined **recursively** by splitting off one
cube-coordinate, so the vertex-product split is *definitional*; it is marked `irreducible` after its unfold
lemma. Everything is **axiom-clean — no `sorry`**. Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V]

/-- The **Gowers box product** `∏_{ω∈{0,1}^d} conj^{|ω|} (F ω)(x + ω·h)`, defined by peeling the first
cube-coordinate. `boxFn (d+1) F h x = boxFn d F₀ (tail h) x · conj(boxFn d F₁ (tail h) (x + h 0))`, where
`F_b ω' = F (cons b ω')`. -/
def boxFn : (d : ℕ) → ((Fin d → Bool) → V → ℂ) → (Fin d → V) → V → ℂ
  | 0,     F, _ => F (fun i => i.elim0)
  | _ + 1, F, h => fun x =>
      boxFn _ (fun ω => F (Fin.cons false ω)) (Fin.tail h) x *
      (starRingEnd ℂ) (boxFn _ (fun ω => F (Fin.cons true ω)) (Fin.tail h) (x + h 0))

/-- The one-step unfold of `boxFn` (the definitional vertex-product split). -/
lemma boxFn_succ (d : ℕ) (F : (Fin (d + 1) → Bool) → V → ℂ) (h : Fin (d + 1) → V) (x : V) :
    boxFn (d + 1) F h x
      = boxFn d (fun ω => F (Fin.cons false ω)) (Fin.tail h) x *
        (starRingEnd ℂ) (boxFn d (fun ω => F (Fin.cons true ω)) (Fin.tail h) (x + h 0)) := rfl

/-- The empty-cube box product is just `F` at the (unique) empty vertex. -/
lemma boxFn_zero (F : (Fin 0 → Bool) → V → ℂ) (h : Fin 0 → V) (x : V) :
    boxFn 0 F h x = F (fun i => i.elim0) x := rfl

attribute [irreducible] boxFn

/-! ## The explicit product form and cube-coordinate symmetry

The recursion `boxFn` peels the *first* cube-coordinate, which makes the peeling factorization
definitional but hides the symmetry of the box under permuting the coordinates. We now give the
**explicit product form** `boxProdE d F h x = ∏_{ω∈{0,1}^d} conj^{|ω|} (F ω)(x + ω·h)`, prove it equals
`boxFn`, and read off **cube-coordinate symmetry** — the ingredient that lets the Gowers–Cauchy–Schwarz
leaf induction peel *any* coordinate, not just the first. -/

/-- The cube vertex offset `∑_{i : ω i = 1} h i`; the vertex is `x + cubePt ω h`. -/
def cubePt (ω : Fin d → Bool) (h : Fin d → V) : V := ∑ i, if ω i then h i else 0

/-- The cube-vertex parity `|ω|` (number of `1`s) — the conjugation exponent at vertex `ω`. -/
def cubePar (ω : Fin d → Bool) : ℕ := ∑ i, if ω i then 1 else 0

/-- **Explicit product form** of the box product over the cube `{0,1}^d`,
`∏_{ω} conj^{|ω|} (F ω)(x + ω·h)`. Equal to the recursive `boxFn` (`boxFn_eq_boxProdE`); the product
form makes the cube-coordinate symmetry `gowersBox_perm` transparent. -/
noncomputable def boxProdE (d : ℕ) (F : (Fin d → Bool) → V → ℂ) (h : Fin d → V) (x : V) : ℂ :=
  ∏ ω : Fin d → Bool, (starRingEnd ℂ)^[cubePar ω] ((F ω) (x + cubePt ω h))

lemma cubePar_cons (b : Bool) (ω' : Fin d → Bool) :
    cubePar (Fin.cons b ω') = (if b then 1 else 0) + cubePar ω' := by
  simp only [cubePar, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma cubePt_cons (b : Bool) (ω' : Fin d → Bool) (h : Fin (d + 1) → V) :
    cubePt (Fin.cons b ω') h = (if b then h 0 else 0) + cubePt ω' (Fin.tail h) := by
  simp only [cubePt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- The product form satisfies the same peeling recursion as `boxFn`. -/
lemma boxProdE_succ (d : ℕ) (F : (Fin (d + 1) → Bool) → V → ℂ) (h : Fin (d + 1) → V) (x : V) :
    boxProdE (d + 1) F h x
      = boxProdE d (fun ω => F (Fin.cons false ω)) (Fin.tail h) x *
        (starRingEnd ℂ) (boxProdE d (fun ω => F (Fin.cons true ω)) (Fin.tail h) (x + h 0)) := by
  have hce : ∀ (b : Bool) (y : Fin d → Bool),
      (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)) (b, y) = Fin.cons b y := fun b y => rfl
  rw [boxProdE, ← (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).prod_comp, Fintype.prod_prod_type,
    Fintype.prod_bool, mul_comm]
  simp only [hce, cubePar_cons, cubePt_cons, if_true, if_false, Bool.false_eq_true,
    zero_add, Function.iterate_add_apply, Function.iterate_one]
  rw [boxProdE, boxProdE, map_prod]
  refine congr_arg₂ (· * ·) (Finset.prod_congr rfl fun ω' _ => ?_)
    (Finset.prod_congr rfl fun ω' _ => ?_)
  · rfl
  · rw [add_assoc]

/-- **The recursive and product forms of the box product agree.** -/
lemma boxFn_eq_boxProdE (d : ℕ) (F : (Fin d → Bool) → V → ℂ) (h : Fin d → V) (x : V) :
    boxFn d F h x = boxProdE d F h x := by
  induction d generalizing x with
  | zero =>
      rw [boxFn_zero, boxProdE, Fintype.prod_unique]
      simp only [cubePar, cubePt, Finset.univ_eq_empty, Finset.sum_empty, Function.iterate_zero,
        id_eq, add_zero]
      rfl
  | succ d ih => rw [boxFn_succ, boxProdE_succ, ih, ih]

lemma cubePar_reindex (e : Equiv.Perm (Fin d)) (ν : Fin d → Bool) :
    cubePar (fun i => ν (e.symm i)) = cubePar ν := by
  simp only [cubePar]; rw [← Equiv.sum_comp e.symm (fun j => if ν j then (1 : ℕ) else 0)]

lemma cubePt_reindex (e : Equiv.Perm (Fin d)) (ν : Fin d → Bool) (h : Fin d → V) :
    cubePt (fun i => ν (e.symm i)) h = cubePt ν (fun j => h (e j)) := by
  simp only [cubePt]; rw [← Equiv.sum_comp e.symm (fun j => if ν j then h (e j) else 0)]
  simp only [Equiv.apply_symm_apply]

/-- **Cube-coordinate reindexing of the product form.** Permuting the cube coordinates by `e` matches
relabelling the directions by `e`. -/
lemma boxProdE_reindex (e : Equiv.Perm (Fin d)) (F : (Fin d → Bool) → V → ℂ) (h : Fin d → V) (x : V) :
    boxProdE d (fun ω => F (fun i => ω (e i))) h x = boxProdE d F (fun j => h (e j)) x := by
  simp only [boxProdE]
  rw [← Equiv.prod_comp (Equiv.arrowCongr e (Equiv.refl Bool))
    (fun ω => (starRingEnd ℂ)^[cubePar ω] ((F (fun i => ω (e i))) (x + cubePt ω h)))]
  refine Finset.prod_congr rfl (fun ν _ => ?_)
  have harr : (Equiv.arrowCongr e (Equiv.refl Bool)) ν = fun i => ν (e.symm i) := by funext i; rfl
  rw [harr]; simp only [Equiv.symm_apply_apply, cubePar_reindex, cubePt_reindex]

variable [Fintype V]

/-- The **Gowers box inner product**: `⟨(F ω)⟩_{U^d} = 𝔼_{x, h} boxFn d F h x`. With `F ≡ f` constant it is
`‖f‖_{U^d}^{2^d}`; the Gowers–Cauchy–Schwarz inequality bounds `‖·‖` by `∏_ω ‖F ω‖_{U^d}`. -/
noncomputable def gowersBox (d : ℕ) (F : (Fin d → Bool) → V → ℂ) : ℂ :=
  Finset.expect Finset.univ (fun p : V × (Fin d → V) => boxFn d F p.2 p.1)

/-- **The U¹ factorization (reusable):** averaging `A(x)·conj(B(x+h))` over `(x, h)` factors as
`(𝔼 A)·conj(𝔼 B)`. -/
lemma expect_mul_conj_shift (A B : V → ℂ) :
    Finset.expect Finset.univ (fun p : V × V => A p.1 * (starRingEnd ℂ) (B (p.1 + p.2)))
      = Finset.expect Finset.univ A * (starRingEnd ℂ) (Finset.expect Finset.univ B) := by
  let e : (V × V) ≃ (V × V) :=
    { toFun := fun p => (p.1, p.1 + p.2), invFun := fun q => (q.1, q.2 - q.1)
      left_inv := by rintro ⟨x, h⟩; simp
      right_inv := by rintro ⟨x, y⟩; simp }
  rw [Fintype.expect_equiv e (fun p => A p.1 * (starRingEnd ℂ) (B (p.1 + p.2)))
        (fun q => A q.1 * (starRingEnd ℂ) (B q.2)) (fun p => rfl),
    ← Finset.univ_product_univ,
    Finset.expect_product' Finset.univ Finset.univ (fun x y => A x * (starRingEnd ℂ) (B y)),
    ← Finset.expect_mul_expect, conj_expect]

/-- The reindex `(x, h) ↦ (tail h, (x, h 0))` peeling the first direction out of the box average. -/
def boxPeelEquiv (d : ℕ) : (V × (Fin (d + 1) → V)) ≃ ((Fin d → V) × (V × V)) where
  toFun p := (Fin.tail p.2, (p.1, p.2 0))
  invFun q := (q.2.1, Fin.cons q.2.2 q.1)
  left_inv := by rintro ⟨x, h⟩; simp [Fin.cons_self_tail]
  right_inv := by rintro ⟨h', x, a⟩; simp [Fin.tail_cons]

-- The reindex + U¹ factorization together need headroom above the default heartbeat ceiling.
set_option maxHeartbeats 4000000 in
set_option linter.style.maxHeartbeats false in
/-- **Peeling factorization of the box inner product:**
`gowersBox (d+1) F = 𝔼_{h'} (𝔼_x boxFn d F₀ h' x) · conj(𝔼_x boxFn d F₁ h' x)`. This is the analytic heart of
the Gowers–Cauchy–Schwarz argument. -/
lemma gowersBox_succ (d : ℕ) (F : (Fin (d + 1) → Bool) → V → ℂ) :
    gowersBox (d + 1) F
      = Finset.expect Finset.univ (fun h' : Fin d → V =>
          Finset.expect Finset.univ (boxFn d (fun ω => F (Fin.cons false ω)) h') *
          (starRingEnd ℂ) (Finset.expect Finset.univ (boxFn d (fun ω => F (Fin.cons true ω)) h'))) := by
  rw [gowersBox]
  simp only [boxFn_succ]
  rw [Fintype.expect_equiv (boxPeelEquiv d)
      (fun p : V × (Fin (d + 1) → V) => boxFn d (fun ω => F (Fin.cons false ω)) (Fin.tail p.2) p.1 *
        (starRingEnd ℂ) (boxFn d (fun ω => F (Fin.cons true ω)) (Fin.tail p.2) (p.1 + p.2 0)))
      (fun q => boxFn d (fun ω => F (Fin.cons false ω)) q.1 q.2.1 *
        (starRingEnd ℂ) (boxFn d (fun ω => F (Fin.cons true ω)) q.1 (q.2.1 + q.2.2)))
      (fun p => rfl),
    ← Finset.univ_product_univ, Finset.expect_product]
  refine Finset.expect_congr rfl (fun h' _ => ?_)
  exact expect_mul_conj_shift (boxFn d (fun ω => F (Fin.cons false ω)) h')
    (boxFn d (fun ω => F (Fin.cons true ω)) h')

/-- **Complex Cauchy–Schwarz for the finite average:** `‖𝔼 A·conj B‖² ≤ (𝔼‖A‖²)(𝔼‖B‖²)`. -/
lemma norm_expect_mul_conj_sq_le {ι : Type*} [Fintype ι] (A B : ι → ℂ) :
    ‖Finset.expect Finset.univ (fun i => A i * (starRingEnd ℂ) (B i))‖ ^ 2
      ≤ Finset.expect Finset.univ (fun i => ‖A i‖ ^ 2) *
        Finset.expect Finset.univ (fun i => ‖B i‖ ^ 2) := by
  have h1 : ‖Finset.expect Finset.univ (fun i => A i * (starRingEnd ℂ) (B i))‖
      ≤ Finset.expect Finset.univ (fun i => ‖A i‖ * ‖B i‖) := by
    refine (RCLike.norm_expect_le (K := ℝ)).trans (le_of_eq ?_)
    refine Finset.expect_congr rfl (fun i _ => ?_)
    rw [norm_mul, Complex.norm_conj]
  calc ‖Finset.expect Finset.univ (fun i => A i * (starRingEnd ℂ) (B i))‖ ^ 2
      ≤ (Finset.expect Finset.univ (fun i => ‖A i‖ * ‖B i‖)) ^ 2 := by gcongr
    _ ≤ _ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖A i‖) (fun i => ‖B i‖)

/-- **The Gowers–Cauchy–Schwarz argument** (the single Cauchy–Schwarz step): applying complex Cauchy–Schwarz to
the peeling factorization bounds `‖gowersBox (d+1) F‖²` by the product of the two "face L²-energies"
`𝔼_{h'} ‖𝔼_x boxFn d F_b h' x‖²`. Iterating this over all cube-coordinates yields the full inequality
`‖⟨(f_ω)⟩‖ ≤ ∏_ω ‖f_ω‖_{U^d}` (the `2^d`-leaf induction — still outstanding). -/
lemma norm_gowersBox_succ_sq_le (d : ℕ) (F : (Fin (d + 1) → Bool) → V → ℂ) :
    ‖gowersBox (d + 1) F‖ ^ 2
      ≤ Finset.expect Finset.univ (fun h' : Fin d → V =>
          ‖Finset.expect Finset.univ (boxFn d (fun ω => F (Fin.cons false ω)) h')‖ ^ 2)
        * Finset.expect Finset.univ (fun h' : Fin d → V =>
          ‖Finset.expect Finset.univ (boxFn d (fun ω => F (Fin.cons true ω)) h')‖ ^ 2) := by
  rw [gowersBox_succ]
  exact norm_expect_mul_conj_sq_le _ _

/-- **Cube-coordinate symmetry of the box inner product.** For any permutation `e` of the cube axes,
`gowersBox d (F ∘ e) = gowersBox d F`. This is what lets the Gowers–Cauchy–Schwarz leaf induction peel
*any* coordinate, not just the first. -/
lemma gowersBox_perm (d : ℕ) (e : Equiv.Perm (Fin d)) (F : (Fin d → Bool) → V → ℂ) :
    gowersBox d (fun ω => F (fun i => ω (e i))) = gowersBox d F := by
  simp only [gowersBox, boxFn_eq_boxProdE]
  refine Fintype.expect_equiv
    (Equiv.prodCongr (Equiv.refl V) (Equiv.arrowCongr e.symm (Equiv.refl V))) _ _ (fun p => ?_)
  obtain ⟨x, h⟩ := p
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq]
  rw [boxProdE_reindex]; rfl

/-! ## The self-box is the Gowers norm

The box inner product of a **constant** family `F ≡ g` is `‖g‖_{U^d}^{2^d}` — the Gowers norm to the
`2^d`. Concretely `boxFn d (const g)` is the (iterated) conjugate of the Gowers product `iterMderiv`, so
after averaging `gowersBox d (const g) = conj^d (gowersInner d g)`, and taking norms gives the norm
identity. This is the base of the Gowers–Cauchy–Schwarz leaf induction: the `2^d` fully-diagonalised
leaves are exactly these self-boxes. -/

lemma iterate_conj_mul (n : ℕ) (a b : ℂ) :
    (starRingEnd ℂ)^[n] (a * b) = (starRingEnd ℂ)^[n] a * (starRingEnd ℂ)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

lemma norm_iterate_conj (n : ℕ) (z : ℂ) : ‖(starRingEnd ℂ)^[n] z‖ = ‖z‖ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Complex.norm_conj, ih]

omit [Fintype V] in
/-- **Pointwise self-box.** The box product of a constant family is the iterated conjugate of the Gowers
product `iterMderiv`: `boxFn d (const g) h x = conj^d (∂_{h} g)(x)`. -/
lemma boxFn_const_eq (d : ℕ) (g : V → ℂ) (h : Fin d → V) (x : V) :
    boxFn d (fun _ => g) h x = (starRingEnd ℂ)^[d] (iterMderiv (List.ofFn h) g x) := by
  induction d generalizing x with
  | zero => rw [boxFn_zero]; simp [iterMderiv]
  | succ d ih =>
      rw [boxFn_succ]
      have hf : ∀ (b : Bool) (k : Fin d → V) (y : V),
          boxFn d (fun ω => (fun _ : Fin (d + 1) → Bool => g) (Fin.cons b ω)) k y
            = (starRingEnd ℂ)^[d] (iterMderiv (List.ofFn k) g y) := fun b k y => ih k y
      rw [hf false, hf true, iterMderiv_ofFn_peel, iterMderiv_ofFn_one, iterate_conj_mul,
        show (Fin.tail h : Fin d → V) = fun i => h i.succ from rfl]
      have h1 : (starRingEnd ℂ) ((starRingEnd ℂ)^[d]
            (iterMderiv (List.ofFn (fun i => h i.succ)) g (x + h 0)))
          = (starRingEnd ℂ)^[d + 1] (iterMderiv (List.ofFn (fun i => h i.succ)) g (x + h 0)) :=
        (Function.iterate_succ_apply' _ d _).symm
      have h2 : (starRingEnd ℂ)^[d + 1] ((starRingEnd ℂ)
            (iterMderiv (List.ofFn (fun i => h i.succ)) g x))
          = (starRingEnd ℂ)^[d] (iterMderiv (List.ofFn (fun i => h i.succ)) g x) := by
        rw [Function.iterate_succ_apply, Complex.conj_conj]
      rw [h1, h2]; ring

/-- Complex conjugation (iterated) commutes with the finite average. -/
lemma iterate_conj_expect {ι : Type*} [Fintype ι] (n : ℕ) (f : ι → ℂ) :
    (starRingEnd ℂ)^[n] (Finset.expect Finset.univ f)
      = Finset.expect Finset.univ (fun i => (starRingEnd ℂ)^[n] (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, conj_expect]
      exact Finset.expect_congr rfl (fun i _ => (Function.iterate_succ_apply' _ n _).symm)

/-- **The self-box is the iterated conjugate of the Gowers inner product.** -/
lemma gowersBox_const (d : ℕ) (g : V → ℂ) :
    gowersBox d (fun _ => g) = (starRingEnd ℂ)^[d] (gowersInner d g) := by
  rw [gowersBox, gowersInner, iterate_conj_expect]
  exact Finset.expect_congr rfl (fun p _ => boxFn_const_eq d g p.2 p.1)

/-- **The self-box has the Gowers-inner-product norm.** -/
lemma norm_gowersBox_const (d : ℕ) (g : V → ℂ) :
    ‖gowersBox d (fun _ => g)‖ = ‖gowersInner d g‖ := by
  rw [gowersBox_const, norm_iterate_conj]

/-- `‖g‖_{U^d}^{2^d} = ‖⟨g,…,g⟩‖`: the Gowers norm to the `2^d` recovers the (norm of the) Gowers inner
product. -/
lemma gowersNorm_pow (d : ℕ) (g : V → ℂ) :
    gowersNorm d g ^ (2 ^ d) = ‖gowersInner d g‖ := by
  rw [gowersNorm_eq, ← Real.rpow_natCast (‖gowersInner d g‖ ^ ((1 : ℝ) / 2 ^ d)) (2 ^ d),
    ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, Nat.cast_ofNat, one_div,
    inv_mul_cancel₀ (by positivity), Real.rpow_one]

/-- **The self-box is the Gowers norm to the `2^d`.** `‖⟨g,…,g⟩_{U^d}‖ = ‖g‖_{U^d}^{2^d}` — the fully
diagonalised leaf value of the Gowers–Cauchy–Schwarz inequality. -/
lemma norm_gowersBox_const_eq_pow (d : ℕ) (g : V → ℂ) :
    ‖gowersBox d (fun _ => g)‖ = gowersNorm d g ^ (2 ^ d) := by
  rw [norm_gowersBox_const, gowersNorm_pow]

/-! ## Diagonalising one coordinate

The Gowers–Cauchy–Schwarz leaf induction peels one cube-coordinate at a time, turning a free coordinate
into a **collapsed** one. `collapse0 G` lifts a `d`-family to a `(d+1)`-family that ignores its first
coordinate; the single Cauchy–Schwarz step bounds `‖gowersBox (d+1) F‖²` by the product of the two
collapsed self-energies `‖gowersBox (d+1) (collapse0 F_b)‖`, each a nonnegative real. -/

/-- Collapse coordinate 0: lift a `d`-family to a `(d+1)`-family ignoring the first coordinate. -/
def collapse0 (G : (Fin d → Bool) → V → ℂ) : (Fin (d + 1) → Bool) → V → ℂ := fun ω => G (Fin.tail ω)

/-- The self-correlation form of the collapsed box: `gowersBox (d+1) (collapse0 G)
= 𝔼_{h'} (𝔼_x boxFn d G h' x)·conj(𝔼_x boxFn d G h' x)`. -/
lemma gowersBox_collapse0 (d : ℕ) (G : (Fin d → Bool) → V → ℂ) :
    gowersBox (d + 1) (collapse0 G)
      = Finset.expect Finset.univ (fun h' : Fin d → V =>
          Finset.expect Finset.univ (boxFn d G h') *
          (starRingEnd ℂ) (Finset.expect Finset.univ (boxFn d G h'))) := by
  rw [gowersBox_succ]
  refine Finset.expect_congr rfl (fun h' _ => ?_)
  rw [show (fun ω => collapse0 G (Fin.cons false ω)) = G from by
        funext ω; simp only [collapse0, Fin.tail_cons],
      show (fun ω => collapse0 G (Fin.cons true ω)) = G from by
        funext ω; simp only [collapse0, Fin.tail_cons]]

/-- The collapsed box is a nonnegative real: the face energy `𝔼_{h'} ‖𝔼_x boxFn d G h' x‖²`. -/
lemma gowersBox_collapse0_ofReal (d : ℕ) (G : (Fin d → Bool) → V → ℂ) :
    gowersBox (d + 1) (collapse0 G)
      = ((Finset.expect Finset.univ (fun h' : Fin d → V =>
          ‖Finset.expect Finset.univ (boxFn d G h')‖ ^ 2) : ℝ) : ℂ) := by
  rw [gowersBox_collapse0, Complex.ofReal_expect]
  refine Finset.expect_congr rfl (fun h' _ => ?_)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- The norm of the collapsed box is the face energy `𝔼_{h'} ‖𝔼_x boxFn d G h' x‖²`. -/
lemma norm_gowersBox_collapse0 (d : ℕ) (G : (Fin d → Bool) → V → ℂ) :
    ‖gowersBox (d + 1) (collapse0 G)‖
      = Finset.expect Finset.univ (fun h' : Fin d → V =>
          ‖Finset.expect Finset.univ (boxFn d G h')‖ ^ 2) := by
  rw [gowersBox_collapse0_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact Finset.expect_nonneg (fun h' _ => sq_nonneg _)

/-- **The Cauchy–Schwarz step, recast with `collapse0`.** `‖gowersBox (d+1) F‖²` is at most the product
of the two collapsed self-energies of its coordinate-0 faces — each `‖gowersBox (d+1) (collapse0 ·)‖`. -/
lemma norm_gowersBox_succ_sq_le' (d : ℕ) (F : (Fin (d + 1) → Bool) → V → ℂ) :
    ‖gowersBox (d + 1) F‖ ^ 2
      ≤ ‖gowersBox (d + 1) (collapse0 (fun ω => F (Fin.cons false ω)))‖
        * ‖gowersBox (d + 1) (collapse0 (fun ω => F (Fin.cons true ω)))‖ := by
  rw [norm_gowersBox_collapse0, norm_gowersBox_collapse0]
  exact norm_gowersBox_succ_sq_le d F

/-! ## The Gowers–Cauchy–Schwarz inequality

The leaf induction. `liftSuffix k m H` lifts a free `m`-family `H` to a `(k+m)`-family whose first `k`
coordinates are collapsed. `GLeafGen` bounds `‖gowersBox (k+m) (liftSuffix k m H)‖^{2^m}` by the product
of the `2^m` self-boxes of `H`, by induction on the free count `m`: each step swaps the first free
coordinate to the front (`gowersBox_perm`), diagonalises it (`norm_gowersBox_succ_sq_le'`), and recurses.
Specialising to `k = 0` and converting self-boxes to Gowers norms (`norm_gowersBox_const_eq_pow`) yields
`gowersCauchySchwarz`: `‖⟨(f_ω)⟩_{U^d}‖ ≤ ∏_ω ‖f_ω‖_{U^d}`. -/

/-- Lift a free `m`-family to a `(k+m)`-family whose first `k` coordinates are collapsed. -/
def liftSuffix (k m : ℕ) (H : (Fin m → Bool) → V → ℂ) : (Fin (k + m) → Bool) → V → ℂ :=
  fun ω => H (fun i => ω (Fin.natAdd k i))

/-- Transport the box inner product along a dimension equality (norm-preserving). -/
lemma norm_gowersBox_cast {n n' : ℕ} (h : n = n') (F : (Fin n' → Bool) → V → ℂ) :
    ‖gowersBox n' F‖ = ‖gowersBox n (fun ω => F (fun i => ω (Fin.cast h.symm i)))‖ := by
  subst h; simp only [Fin.cast_refl, id_eq]

/-- Transport a constant self-box along a dimension equality. -/
lemma norm_gowersBox_cast_const {n n' : ℕ} (h : n = n') (g : V → ℂ) :
    ‖gowersBox n' (fun _ => g)‖ = ‖gowersBox n (fun _ => g)‖ := by subst h; rfl

omit [AddCommGroup V] [Fintype V] in
/-- The `b`-face split of a product over the `(m+1)`-cube. -/
lemma prod_cons_bool {M : Type*} [CommMonoid M] (m : ℕ) (f : (Fin (m + 1) → Bool) → M) :
    ∏ τ : Fin (m + 1) → Bool, f τ
      = (∏ σ : Fin m → Bool, f (Fin.cons false σ)) * (∏ σ : Fin m → Bool, f (Fin.cons true σ)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)).prod_comp, Fintype.prod_prod_type,
    Fintype.prod_bool, mul_comm]; rfl

omit [AddCommGroup V] [Fintype V] in
/-- **Peel-recursion index identity.** Swapping the first free coordinate `k` to the front, fixing it to
`b`, and re-collapsing turns `liftSuffix k (m+1) H` into `liftSuffix (k+1) m` of the `b`-face of `H`
(reindexed across the `(k+m)+1 = (k+1)+m` dimension identity). -/
lemma collapse0_face_liftSuffix (k m : ℕ) (H : (Fin (m + 1) → Bool) → V → ℂ) (b : Bool)
    (hsucc : (k + m) + 1 = (k + 1) + m) :
    collapse0 (fun ω' : Fin (k + m) → Bool => liftSuffix k (m + 1) H
        (fun i => (Fin.cons b ω' : Fin (k + (m + 1)) → Bool)
          (Equiv.swap (0 : Fin (k + (m + 1))) ⟨k, by omega⟩ i)))
      = fun ω => liftSuffix (k + 1) m (fun σ => H (Fin.cons b σ)) (fun i => ω (Fin.cast hsucc.symm i)) := by
  funext ω
  simp only [collapse0, liftSuffix]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [Fin.cons_zero]
    have h0 : Fin.natAdd k (0 : Fin (m + 1)) = (⟨k, by omega⟩ : Fin (k + (m + 1))) := by
      apply Fin.ext; simp [Fin.natAdd]
    rw [h0, Equiv.swap_apply_right, Fin.cons_zero]
  · intro j'
    simp only [Fin.cons_succ]
    have hne0 : Fin.natAdd k (j'.succ) ≠ (0 : Fin (k + (m + 1))) := by
      apply Fin.ne_of_val_ne; simp [Fin.natAdd]
    have hnek : Fin.natAdd k (j'.succ) ≠ (⟨k, by omega⟩ : Fin (k + (m + 1))) := by
      apply Fin.ne_of_val_ne; simp [Fin.natAdd, Fin.succ]
    rw [Equiv.swap_apply_of_ne_of_ne hne0 hnek]
    have hidx : (Fin.natAdd k (j'.succ) : Fin (k + (m + 1)))
        = (⟨k + j', by omega⟩ : Fin (k + m)).succ := by
      apply Fin.ext; simp [Fin.natAdd, Fin.succ]; omega
    rw [hidx, Fin.cons_succ]
    simp only [Fin.tail]
    congr 1
    apply Fin.ext; simp [Fin.natAdd, Fin.succ, Fin.cast]; omega

/-- **The leaf bound.** For a free `m`-family `H` lifted with `k` collapsed coordinates,
`‖gowersBox (k+m) (liftSuffix k m H)‖^{2^m} ≤ ∏_σ ‖gowersBox (k+m) (const (H σ))‖` — the box is at most
the product of its `2^m` fully-diagonalised self-boxes. By induction on the free count `m`. -/
lemma GLeafGen : ∀ (m k : ℕ) (H : (Fin m → Bool) → V → ℂ),
    ‖gowersBox (k + m) (liftSuffix k m H)‖ ^ (2 ^ m)
      ≤ ∏ σ : Fin m → Bool, ‖gowersBox (k + m) (fun _ => H σ)‖ := by
  intro m
  induction m with
  | zero =>
      intro k H
      rw [pow_zero, pow_one, Fintype.prod_unique]
      refine le_of_eq (congrArg (fun G => ‖gowersBox (k + 0) G‖) ?_)
      funext ω; simp only [liftSuffix]; exact congrArg H (Subsingleton.elim _ _)
  | succ m ih =>
      intro k H
      have hsucc : (k + m) + 1 = (k + 1) + m := by omega
      set e := Equiv.swap (0 : Fin (k + (m + 1))) ⟨k, by omega⟩ with he
      have hcs := norm_gowersBox_succ_sq_le' (k + m)
        (fun ω : Fin ((k + m) + 1) → Bool => liftSuffix k (m + 1) H (fun i => ω (e i)))
      have hface : ∀ b : Bool,
          ‖gowersBox ((k + m) + 1) (collapse0 (fun ω' =>
              (fun ω : Fin ((k + m) + 1) → Bool =>
                liftSuffix k (m + 1) H (fun i => ω (e i))) (Fin.cons b ω')))‖
            = ‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons b σ)))‖ := by
        intro b
        rw [show (fun ω' => (fun ω : Fin ((k + m) + 1) → Bool =>
              liftSuffix k (m + 1) H (fun i => ω (e i))) (Fin.cons b ω'))
              = (fun ω' : Fin (k + m) → Bool => liftSuffix k (m + 1) H
                (fun i => (Fin.cons b ω' : Fin (k + (m + 1)) → Bool) (e i))) from rfl,
          he, collapse0_face_liftSuffix k m H b hsucc, ← norm_gowersBox_cast hsucc]
      rw [(gowersBox_perm (k + (m + 1)) e (liftSuffix k (m + 1) H)).symm]
      have hstep : ‖gowersBox ((k + m) + 1) (fun ω => liftSuffix k (m + 1) H (fun i => ω (e i)))‖ ^ 2
          ≤ ‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons false σ)))‖
            * ‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons true σ)))‖ := by
        rw [← hface false, ← hface true]; exact hcs
      calc ‖gowersBox ((k + m) + 1) (fun ω => liftSuffix k (m + 1) H (fun i => ω (e i)))‖ ^ (2 ^ (m + 1))
          = (‖gowersBox ((k + m) + 1) (fun ω => liftSuffix k (m + 1) H (fun i => ω (e i)))‖ ^ 2)
              ^ (2 ^ m) := by rw [← pow_mul]; congr 1; rw [pow_succ]; ring
        _ ≤ (‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons false σ)))‖
              * ‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons true σ)))‖)
              ^ (2 ^ m) := pow_le_pow_left₀ (by positivity) hstep (2 ^ m)
        _ = ‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons false σ)))‖ ^ (2 ^ m)
              * ‖gowersBox ((k + 1) + m) (liftSuffix (k + 1) m (fun σ => H (Fin.cons true σ)))‖
                ^ (2 ^ m) := by rw [mul_pow]
        _ ≤ (∏ σ : Fin m → Bool, ‖gowersBox ((k + 1) + m) (fun _ => H (Fin.cons false σ))‖)
              * (∏ σ : Fin m → Bool, ‖gowersBox ((k + 1) + m) (fun _ => H (Fin.cons true σ))‖) :=
            mul_le_mul (ih (k + 1) _) (ih (k + 1) _) (by positivity) (by positivity)
        _ = ∏ τ : Fin (m + 1) → Bool, ‖gowersBox (k + (m + 1)) (fun _ => H τ)‖ := by
            rw [prod_cons_bool]
            congr 1
            · exact Finset.prod_congr rfl (fun σ _ => norm_gowersBox_cast_const hsucc _)
            · exact Finset.prod_congr rfl (fun σ _ => norm_gowersBox_cast_const hsucc _)

/-- **The Gowers–Cauchy–Schwarz inequality.** `‖⟨(f_ω)_{ω∈{0,1}^d}⟩_{U^d}‖ ≤ ∏_ω ‖f_ω‖_{U^d}`: the box
inner product of a family is bounded by the product of the Gowers norms of its functions. The main
result — Tao–Vu, *Additive Combinatorics*, Eq. 11.6. -/
theorem gowersCauchySchwarz (d : ℕ) (F : (Fin d → Bool) → V → ℂ) :
    ‖gowersBox d F‖ ≤ ∏ ω : Fin d → Bool, gowersNorm d (F ω) := by
  have hcast : ‖gowersBox (0 + d) (liftSuffix 0 d F)‖ = ‖gowersBox d F‖ := by
    rw [norm_gowersBox_cast (Nat.zero_add d).symm]
    refine congrArg (fun G => ‖gowersBox d G‖) ?_
    funext ω; simp only [liftSuffix]
    congr 1; funext j; congr 1
    apply Fin.ext; simp [Fin.natAdd, Fin.cast]
  have key : ‖gowersBox d F‖ ^ (2 ^ d) ≤ ∏ ω : Fin d → Bool, ‖gowersBox d (fun _ => F ω)‖ := by
    have h := GLeafGen d 0 F
    rw [hcast] at h
    refine h.trans (le_of_eq (Finset.prod_congr rfl (fun σ _ => ?_)))
    rw [norm_gowersBox_cast (Nat.zero_add d).symm]
  have hpow : ‖gowersBox d F‖ ^ (2 ^ d) ≤ (∏ ω : Fin d → Bool, gowersNorm d (F ω)) ^ (2 ^ d) := by
    refine key.trans (le_of_eq ?_)
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun ω _ => norm_gowersBox_const_eq_pow d (F ω))
  exact le_of_pow_le_pow_left₀ (by positivity)
    (Finset.prod_nonneg (fun ω _ => gowersNorm_nonneg d (F ω))) hpow

end ECCLib

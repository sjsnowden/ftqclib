/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Group.ForwardDiff

set_option linter.style.longLine false

/-!
# Higher-order Fourier analysis: the additive derivative and its multi-direction iterate

The additive (forward) derivative `D_y f (x) = f (x + y) − f x` and its iterate over several **distinct**
directions `y₁, …, y_k`. Built directly on Mathlib's `fwdDiff` (`Mathlib/Algebra/Group/ForwardDiff.lean`),
which *is* `D_y`. Mathlib supplies the same-direction iterate `fwdDiff_iter`, the Gregory–Newton formula, and
linearity; it has **no** multi-direction iterate — that is supplied here.

Anchored to Hatami–Hatami–Lovett, *Higher-order Fourier Analysis and Applications* (Found. & Trends TCS 13:4),
Ch 6 (the local definition of a degree-`≤ d` polynomial via `D_{y₁}⋯D_{y_{d+1}} P = 0`). This library is
Mathlib-only and FTQCLib-independent, intended to be lifted into a standalone repository.
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V] {G : Type*} [AddCommGroup G]

/-- The **iterated additive derivative** over a list of directions:
`iteratedFwdDiff [y₁, …, y_k] f = D_{y₁} (D_{y₂} (⋯ (D_{y_k} f)))`, where `D_y = fwdDiff y`. -/
def iteratedFwdDiff (ys : List V) (f : V → G) : V → G :=
  ys.foldr fwdDiff f

@[simp] lemma iteratedFwdDiff_nil (f : V → G) : iteratedFwdDiff ([] : List V) f = f := rfl

lemma iteratedFwdDiff_cons (y : V) (ys : List V) (f : V → G) :
    iteratedFwdDiff (y :: ys) f = fwdDiff y (iteratedFwdDiff ys f) := rfl

/-- **Distinct directions commute:** `D_a (D_b f) = D_b (D_a f)`, since translation in `V` is
commutative. -/
theorem fwdDiff_comm (a b : V) (f : V → G) :
    fwdDiff a (fwdDiff b f) = fwdDiff b (fwdDiff a f) := by
  funext x
  simp only [fwdDiff]
  rw [add_right_comm x a b]
  abel

/-- `fwdDiff` of the zero function is zero. -/
@[simp] lemma fwdDiff_zero (y : V) : fwdDiff y (0 : V → G) = 0 := by
  funext x; simp [fwdDiff]

/-- The forward difference in the **zero direction** vanishes: `D_0 f = 0`. -/
@[simp] lemma fwdDiff_zero_dir (f : V → G) : fwdDiff (0 : V) f = 0 := by
  funext x; simp [fwdDiff]

/-- **If any direction is the zero vector, the whole iterated derivative vanishes.** This lets a degree
computation ignore every tuple of directions except those with all entries nonzero. -/
lemma iteratedFwdDiff_eq_zero_of_zero_mem (f : V → G) {ys : List V} (h : (0 : V) ∈ ys) :
    iteratedFwdDiff ys f = 0 := by
  revert h
  induction ys with
  | nil => intro h; simp at h
  | cons y ys ih =>
    intro h
    rcases List.mem_cons.mp h with hy | hy
    · rw [iteratedFwdDiff_cons, ← hy, fwdDiff_zero_dir]
    · rw [iteratedFwdDiff_cons, ih hy, fwdDiff_zero]

/-! ### Iterating a single 2-torsion direction

If a direction `e` is 2-torsion (`e + e = 0`, as in `𝔽₂^n`), the same-direction iterated difference collapses
to a scalar multiple of the first difference: `D_e^{n+1} f = (-2)^n • D_e f`. This is the engine behind the
uniform degree of the depth tower. -/

/-- `fwdDiff` commutes with `ℤ`-scaling of the function. -/
lemma fwdDiff_zsmul (c : ℤ) (y : V) (f : V → G) :
    fwdDiff y (c • f) = c • fwdDiff y f := by
  funext x; simp only [fwdDiff, Pi.smul_apply, smul_sub]

/-- In a **2-torsion direction** (`e + e = 0`), the first difference is anti-periodic:
`(D_e f)(v + e) = -(D_e f) v`. -/
lemma fwdDiff_apply_add_two_torsion {e : V} (he : e + e = 0) (f : V → G) (v : V) :
    fwdDiff e f (v + e) = -fwdDiff e f v := by
  have hv : v + e + e = v := by rw [add_assoc, he, add_zero]
  simp only [fwdDiff]
  rw [hv]; abel

/-- The **second difference** in a 2-torsion direction collapses: `D_e (D_e f) = (-2) • D_e f`. -/
lemma fwdDiff_fwdDiff_two_torsion {e : V} (he : e + e = 0) (f : V → G) :
    fwdDiff e (fwdDiff e f) = (-2 : ℤ) • fwdDiff e f := by
  funext v
  have h : fwdDiff e (fwdDiff e f) v = fwdDiff e f (v + e) - fwdDiff e f v := rfl
  rw [h, fwdDiff_apply_add_two_torsion he, Pi.smul_apply]
  abel

/-- **Iterating one 2-torsion direction:** `D_e^{n+1} f = (-2)^n • D_e f`. -/
lemma iteratedFwdDiff_replicate_two_torsion {e : V} (he : e + e = 0) (f : V → G) (n : ℕ) :
    iteratedFwdDiff (List.replicate (n + 1) e) f = ((-2 : ℤ) ^ n) • fwdDiff e f := by
  induction n with
  | zero =>
    simp only [List.replicate_succ, List.replicate_zero, iteratedFwdDiff_cons, iteratedFwdDiff_nil,
      pow_zero, one_smul]
  | succ n ih =>
    rw [List.replicate_succ, iteratedFwdDiff_cons, ih, fwdDiff_zsmul,
      fwdDiff_fwdDiff_two_torsion he, smul_smul, ← pow_succ]

variable {G' : Type*} [AddCommGroup G']

/-- **`fwdDiff` commutes with an additive homomorphism on the codomain:** `D_y (φ ∘ f) = φ ∘ D_y f`. -/
lemma fwdDiff_comp_addMonoidHom (φ : G →+ G') (y : V) (f : V → G) :
    fwdDiff y (φ ∘ f) = φ ∘ fwdDiff y f := by
  funext x; simp only [fwdDiff, Function.comp_apply, map_sub]

/-- **The iterated derivative commutes with an additive homomorphism:**
`iteratedFwdDiff ys (φ ∘ f) = φ ∘ iteratedFwdDiff ys f`. This is what transports the degree of a polynomial
between coefficient groups. -/
lemma iteratedFwdDiff_comp_addMonoidHom (φ : G →+ G') (ys : List V) (f : V → G) :
    iteratedFwdDiff ys (φ ∘ f) = φ ∘ iteratedFwdDiff ys f := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [iteratedFwdDiff_cons, ih, fwdDiff_comp_addMonoidHom]

/-! ### The composition law and list-structural lemmas

The seed of the Aichinger–Moosbauer reduction (arbitrary directions ⟺ standard-basis directions): the forward
difference in a sum of directions decomposes as `D_{a+b} = D_a + D_b + D_a D_b`, together with the list
lemmas that let a long iterate vanish once any suffix does. -/

/-- **The composition law** `D_{a+b} = D_a + D_b + D_a D_b`: the forward difference in a sum of directions.
The seed identity behind expressing an arbitrary-direction difference through the standard basis. -/
lemma fwdDiff_add_apply (a b : V) (f : V → G) (x : V) :
    fwdDiff (a + b) f x
      = fwdDiff a f x + fwdDiff b f x + fwdDiff a (fwdDiff b f) x := by
  simp only [fwdDiff, add_assoc]
  abel

/-- `iteratedFwdDiff` of the zero function is zero. -/
@[simp] lemma iteratedFwdDiff_zero_fun (l : List V) :
    iteratedFwdDiff l (0 : V → G) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [iteratedFwdDiff_cons, ih, fwdDiff_zero]

/-- **`iteratedFwdDiff` splits over list append:** `D_{l₁ ++ l₂} f = D_{l₁} (D_{l₂} f)`. -/
lemma iteratedFwdDiff_append (l₁ l₂ : List V) (f : V → G) :
    iteratedFwdDiff (l₁ ++ l₂) f = iteratedFwdDiff l₁ (iteratedFwdDiff l₂ f) := by
  simp only [iteratedFwdDiff, List.foldr_append]

/-- **If a suffix already annihilates `f`, so does the whole iterate:** once `D_{l₂} f = 0`, any prefix
`l₁` leaves `D_{l₁ ++ l₂} f = 0`. This is what turns "every length-`(d+1)` basis iterate vanishes" into
"every length-`≥ d+1` basis iterate vanishes." -/
lemma iteratedFwdDiff_eq_zero_of_suffix {l₂ : List V} (f : V → G)
    (h : iteratedFwdDiff l₂ f = 0) (l₁ : List V) :
    iteratedFwdDiff (l₁ ++ l₂) f = 0 := by
  rw [iteratedFwdDiff_append, h, iteratedFwdDiff_zero_fun]

/-- `fwdDiff` is additive in the function argument. -/
lemma fwdDiff_add_fun (y : V) (a b : V → G) :
    fwdDiff y (a + b) = fwdDiff y a + fwdDiff y b := by
  funext x; simp only [fwdDiff, Pi.add_apply]; abel

/-- `fwdDiff` negates through the function argument. -/
lemma fwdDiff_neg_fun (y : V) (a : V → G) : fwdDiff y (-a) = -fwdDiff y a := by
  funext x; simp only [fwdDiff, Pi.neg_apply]; abel

/-- The **function-level composition law** `D_{a+b} = D_a + D_b + D_a D_b` (the pointwise
`fwdDiff_add_apply`, as an equation of functions). -/
lemma fwdDiff_add' (a b : V) (f : V → G) :
    fwdDiff (a + b) f = fwdDiff a f + fwdDiff b f + fwdDiff a (fwdDiff b f) := by
  funext x; simp only [Pi.add_apply]; exact fwdDiff_add_apply a b f x

/-- `fwdDiff` commutes with a finite list-sum of functions. -/
lemma fwdDiff_list_sum (y : V) (L : List (V → G)) :
    fwdDiff y L.sum = (L.map (fwdDiff y)).sum := by
  induction L with
  | nil => simp only [List.sum_nil, List.map_nil]; exact fwdDiff_zero y
  | cons a L ih => rw [List.sum_cons, fwdDiff_add_fun, ih, List.map_cons, List.sum_cons]

/-- **`fwdDiff` as an additive homomorphism** on the function space `V → G`. -/
def fwdDiffHom (y : V) : (V → G) →+ (V → G) where
  toFun := fwdDiff y
  map_zero' := fwdDiff_zero y
  map_add' := fwdDiff_add_fun y

@[simp] lemma fwdDiffHom_apply (y : V) (f : V → G) : fwdDiffHom y f = fwdDiff y f := rfl

end ECCLib

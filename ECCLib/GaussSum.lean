/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

set_option linter.style.longLine false

/-!
# The quadratic-form Gauss sum over a finite field

The odd-characteristic analogue of the frame's char-2 Weil sign: the quadratic Gauss sum
`g(ψ) = ∑_{x ∈ F} ψ(x²)` for an additive character `ψ : AddChar F ℂ` of a finite field `F` of odd
characteristic. Mathlib supplies the *multiplicative-character* Gauss sum `gaussSum χ ψ = ∑ χ(a) ψ(a)`
and its square `gaussSum_sq`, but **not** the quadratic-form sum `∑_x ψ(x²)`. This file builds that
sum and reduces it to `gaussSum` for the quadratic character, so its evaluation is inherited from
Mathlib:

* `quadGaussSum_eq_gaussSum` — `∑_x ψ(x²) = gaussSum χ₂ ψ`, via the fiber count
  `#{x : x² = y} = χ₂(y) + 1` (`quadraticChar_card_sqrts`) and the vanishing of the linear term;
* `quadGaussSum_sq` — `(∑_x ψ(x²))² = χ₂(−1)·|F|`, the "√±q" square-evaluation (from `gaussSum_sq`).

Imports no `FTQCLib.*`; Mathlib-only, intended to sit in the standalone `ECCLib` library.
-/

namespace ECCLib

open scoped BigOperators ComplexConjugate
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character of `F` pushed into `ℂ` via `ℤ ↪ ℂ`: `χ₂ : MulChar F ℂ`. -/
noncomputable def quadCharC (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

/-- The **quadratic-form Gauss sum** `g(ψ) = ∑_{x ∈ F} ψ(x²)`. -/
noncomputable def quadGaussSum (ψ : AddChar F ℂ) : ℂ := ∑ x : F, ψ (x ^ 2)

/-- Reindex a sum over squares by the fiber cardinality:
`∑_x h(x²) = ∑_y #{x : x² = y}·h(y)`. -/
private lemma sum_comp_sq (h : F → ℂ) :
    ∑ x : F, h (x ^ 2) = ∑ y : F, (({x : F | x ^ 2 = y}.toFinset.card : ℂ)) * h y := by
  have key : ∀ x : F, h (x ^ 2) = ∑ y : F, (if x ^ 2 = y then h y else 0) := by
    intro x
    rw [Finset.sum_ite_eq Finset.univ (x ^ 2) h]
    simp
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, Set.toFinset_setOf, nsmul_eq_mul]

/-- `χ₂` pushed into `ℂ` is applied by casting: `quadCharC F a = ((quadraticChar F a : ℤ) : ℂ)`. -/
lemma quadCharC_apply (a : F) : quadCharC F a = ((quadraticChar F a : ℤ) : ℂ) := by
  simp [quadCharC, MulChar.ringHomComp_apply]

/-- `quadCharC F` is nontrivial when the characteristic is odd. -/
lemma quadCharC_ne_one (hF : ringChar F ≠ 2) : quadCharC F ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hF)

/-- `quadCharC F` is a quadratic character. -/
lemma quadCharC_isQuadratic : (quadCharC F).IsQuadratic := by
  intro a
  rcases quadraticChar_isQuadratic F a with h | h | h <;>
    simp [quadCharC_apply, h]

/-- **The quadratic-form Gauss sum equals the multiplicative Gauss sum of `χ₂`.**
`∑_x ψ(x²) = gaussSum χ₂ ψ`, for `ψ` nontrivial and odd characteristic. -/
theorem quadGaussSum_eq_gaussSum (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ1 : ψ ≠ 1) :
    quadGaussSum ψ = gaussSum (quadCharC F) ψ := by
  rw [quadGaussSum, sum_comp_sq]
  have hcard : ∀ y : F, (({x : F | x ^ 2 = y}.toFinset.card : ℂ)) = quadCharC F y + 1 := by
    intro y
    have h := quadraticChar_card_sqrts hF y
    have h2 := congrArg (fun z : ℤ => (z : ℂ)) h
    rw [quadCharC_apply]
    push_cast at h2 ⊢
    linear_combination h2
  simp_rw [hcard, add_mul, one_mul, Finset.sum_add_distrib]
  rw [AddChar.sum_eq_zero_of_ne_one hψ1, add_zero, gaussSum]

/-- **The square-evaluation.** `(∑_x ψ(x²))² = χ₂(−1)·|F|` — the "√±q" (magnitude `√|F|`,
sign of the square governed by `χ₂(−1) = χ₄(|F|)`, i.e. `|F| mod 4`). -/
theorem quadGaussSum_sq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    quadGaussSum ψ ^ 2 = ((quadraticChar F (-1) : ℤ) : ℂ) * (Fintype.card F : ℂ) := by
  rw [quadGaussSum_eq_gaussSum hF hψ,
    gaussSum_sq (quadCharC_ne_one hF) quadCharC_isQuadratic (AddChar.IsPrimitive.of_ne_one hψ),
    quadCharC_apply]

omit [DecidableEq F] in
/-- **The magnitude.** `‖∑_x ψ(x²)‖² = |F|` — the quadratic Gauss sum has modulus `√|F|`.
Immediate from `quadGaussSum_sq` via `‖g²‖ = ‖g‖²` and `‖χ₂(−1)‖ = 1`. -/
theorem quadGaussSum_normSq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ‖quadGaussSum ψ‖ ^ 2 = Fintype.card F := by
  classical
  have hpm : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 := by
    have hne : quadraticChar F (-1) ≠ 0 := by
      rw [Ne, quadraticChar_eq_zero_iff]; exact neg_ne_zero.mpr one_ne_zero
    rcases quadraticChar_isQuadratic F (-1) with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  have hnorm1 : ‖((quadraticChar F (-1) : ℤ) : ℂ)‖ = 1 := by
    rcases hpm with h | h <;> rw [h] <;> norm_num
  have hn : ‖quadGaussSum ψ ^ 2‖ = (Fintype.card F : ℝ) := by
    rw [quadGaussSum_sq hF hψ, norm_mul, hnorm1, one_mul]; simp
  rw [norm_pow] at hn
  exact_mod_cast hn

/-! ## The general quadratic Gauss sum `g(a) = ∑_x ψ(a·x²)`

Reducing to the `a = 1` case for the shifted character `mulShift ψ a` inherits the evaluation.
(Quadratic reciprocity itself is Mathlib's `legendreSym.quadratic_reciprocity`; nothing to re-prove.)
-/

/-- The **general quadratic Gauss sum** `g(a) = ∑_{x ∈ F} ψ(a·x²)`. -/
noncomputable def quadGaussSumGen (ψ : AddChar F ℂ) (a : F) : ℂ := ∑ x : F, ψ (a * x ^ 2)

omit [DecidableEq F] in
/-- `g(a)` is the `a = 1` sum of the shifted character: `∑_x ψ(a·x²) = quadGaussSum (mulShift ψ a)`. -/
lemma quadGaussSumGen_eq (ψ : AddChar F ℂ) (a : F) :
    quadGaussSumGen ψ a = quadGaussSum (AddChar.mulShift ψ a) := by
  simp only [quadGaussSumGen, quadGaussSum, AddChar.mulShift_apply]

omit [Fintype F] [DecidableEq F] in
/-- `mulShift ψ a` is primitive when `ψ` is and `a ≠ 0`. -/
lemma mulShift_isPrimitive {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {a : F} (ha : a ≠ 0) :
    (AddChar.mulShift ψ a).IsPrimitive := by
  intro b hb
  have h : AddChar.mulShift (AddChar.mulShift ψ a) b = AddChar.mulShift ψ (a * b) := by
    ext x; simp [AddChar.mulShift_apply, mul_assoc]
  rw [h]; exact hψ (mul_ne_zero ha hb)

omit [Fintype F] [DecidableEq F] in
/-- `mulShift ψ a` is nontrivial when `ψ` is and `a ≠ 0` — the `ψ ≠ 1` face of
`mulShift_isPrimitive`, so consumers never need `IsPrimitive`. -/
lemma mulShift_ne_one {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) :
    AddChar.mulShift ψ a ≠ 1 :=
  AddChar.IsPrimitive.of_ne_one hψ ha

omit [Fintype F] [DecidableEq F] in
/-- A primitive character is nontrivial — the converse of `AddChar.IsPrimitive.of_ne_one`
(over a field the two are equivalent). For callers holding an `IsPrimitive` witness against the
library's `ψ ≠ 1` API. -/
lemma ne_one_of_isPrimitive {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) : ψ ≠ 1 := by
  have h := hψ (show (1 : F) ≠ 0 from one_ne_zero)
  rwa [AddChar.mulShift_one] at h

omit [DecidableEq F] in
/-- **Magnitude, general `a ≠ 0`:** `‖∑_x ψ(a·x²)‖² = |F|`. -/
theorem quadGaussSumGen_normSq (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {a : F} (ha : a ≠ 0) : ‖quadGaussSumGen ψ a‖ ^ 2 = Fintype.card F := by
  rw [quadGaussSumGen_eq]; exact quadGaussSum_normSq hF (mulShift_ne_one hψ ha)

/-! ## Characteristic 2: the sums vanish

The substantive Gauss theory above lives in odd characteristic — the quadratic character, and with
it the Gauss evaluations, exist because the field's own squaring map supplies a quadratic form
(polarization `(x+y)² − x² − y² = 2xy`, nondegenerate exactly when `2 ≠ 0`). In characteristic 2
that polarization is identically zero: squaring is the Frobenius, and the field supplies no
quadratic datum at all. The sums are still defined there, and they vanish — squaring is a bijection
of a finite field, so `∑_x ψ(a·x²)` reindexes to `∑_y ψ(y) = 0`.

These lemmas are stated on their own because in characteristic 2 nothing is being *computed*:
everything is zero, for a reason unrelated to the Gauss-sign theory. They also supply the
characteristic-2 branch of the unconditional value law below, which there reads `0 = χ₂(a)·0 = 1·0`
(Mathlib's `quadraticChar_eq_one_of_char_two`: in characteristic 2 every nonzero element is a
square) — true, and degenerate. The genuine characteristic-2 content is the vanishing statements
themselves. -/

section CharTwo

omit [Fintype F] [DecidableEq F] in
/-- In characteristic 2 squaring is injective: `x² = y²` forces `(x−y)² = 0`, and a field has no
nilpotents. (This is the Frobenius, spelled out rather than routed through `frobenius` so that no
`ExpChar` instance plumbing is needed.) -/
theorem sq_injective_of_char_two (hF : ringChar F = 2) :
    Function.Injective (fun x : F => x ^ 2) := by
  have h2 : (2 : F) = 0 := by
    have h := (ringChar.spec F 2).mpr (by rw [hF])
    exact_mod_cast h
  intro x y hxy
  simp only at hxy
  have hzero : (x - y) ^ 2 = 0 := by
    have hexp : (x - y) ^ 2 = x ^ 2 - 2 * (x * y) + y ^ 2 := by ring
    rw [hexp, hxy]
    linear_combination (y ^ 2 - x * y) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hzero)

omit [DecidableEq F] in
/-- **Characteristic 2: the quadratic Gauss sum vanishes.** For nontrivial `ψ`, `∑_x ψ(x²) = 0`. -/
theorem quadGaussSum_char_two_eq_zero (hF : ringChar F = 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    quadGaussSum ψ = 0 := by
  have hbij : Function.Bijective (fun x : F => x ^ 2) :=
    Finite.injective_iff_bijective.mp (sq_injective_of_char_two hF)
  unfold quadGaussSum
  rw [show (∑ x : F, ψ (x ^ 2)) = ∑ y : F, ψ y from
    Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun y => ψ y)]
  exact AddChar.sum_eq_zero_of_ne_one hψ

omit [DecidableEq F] in
/-- **Characteristic 2: the twisted sum vanishes too**, for every `a ≠ 0` — `x ↦ a·x²` is injective
as the composite of squaring with multiplication by a unit. This is the form the value law's
characteristic-2 branch would need. -/
theorem quadGaussSumGen_char_two_eq_zero (hF : ringChar F = 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {a : F} (ha : a ≠ 0) : quadGaussSumGen ψ a = 0 := by
  have hinj : Function.Injective (fun x : F => a * x ^ 2) := fun x y hxy =>
    sq_injective_of_char_two hF (mul_left_cancel₀ ha hxy)
  have hbij : Function.Bijective (fun x : F => a * x ^ 2) :=
    Finite.injective_iff_bijective.mp hinj
  unfold quadGaussSumGen
  rw [show (∑ x : F, ψ (a * x ^ 2)) = ∑ y : F, ψ y from
    Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun y => ψ y)]
  exact AddChar.sum_eq_zero_of_ne_one hψ

end CharTwo

/-- **The value law** `g(a) = χ₂(a)·g(1)` for `a ≠ 0` — **unconditional in the characteristic**.
In odd characteristic this is the substantive identity relating the twisted and untwisted Gauss
sums through the quadratic character. In characteristic 2 both sides vanish (`0 = 1·0`, by the
`CharTwo` lemmas above and `quadraticChar_eq_one_of_char_two`), so the identity holds degenerately;
the content-carrying characteristic-2 statements are the vanishing lemmas. -/
theorem quadGaussSumGen_eq_quadraticChar_mul {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) :
    quadGaussSumGen ψ a = quadCharC F a * quadGaussSum ψ := by
  by_cases hF : ringChar F = 2
  · rw [quadGaussSumGen_char_two_eq_zero hF hψ ha,
      quadGaussSum_char_two_eq_zero hF hψ, mul_zero]
  · have hms := gaussSum_mulShift (quadCharC F) ψ (Units.mk0 a ha)
    have hu : ((Units.mk0 a ha : Fˣ) : F) = a := rfl
    rw [hu] at hms
    have hne : quadCharC F a ≠ 0 := by
      simp only [quadCharC_apply, ne_eq, Int.cast_eq_zero, quadraticChar_eq_zero_iff]; exact ha
    have hsq : quadCharC F a * quadCharC F a = 1 := by
      rcases quadCharC_isQuadratic (F := F) a with h | h | h
      · exact absurd h hne
      · rw [h]; ring
      · rw [h]; ring
    rw [quadGaussSumGen_eq, quadGaussSum_eq_gaussSum hF (mulShift_ne_one hψ ha),
      quadGaussSum_eq_gaussSum hF hψ, ← hms, ← mul_assoc, hsq, one_mul]

end ECCLib

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Polynomial

set_option linter.style.longLine false

/-!
# The depth tower of nonclassical polynomials over `ℝ/ℤ`

For every `k`, the single-variable function `Sₖ(v) = |v₀| / 2^k : (𝔽₂)¹ → ℝ/ℤ` is a polynomial of degree
**exactly `k`**, and is **nonclassical** (its values need a `2^k` denominator) once `k ≥ 2`; at `k = 1` it is the
classical floor `|x|/2`. Each rung adds one power of two of precision — the higher-order-Fourier image of the
frame's `ZMod 2^m` precision ladder. The `k = 2` rung is the mother example `|x|/4` of `Polynomial`.

The result is **uniform in `k`** (`towerT_isPolyDegLE`, `towerT_not_isPolyDegLE_pred`), not a family of separate
`decide`s. Two ingredients make this work:

* `isPolyDegLE_univariate_iff` — on `(𝔽₂)¹`, a degree reduces to a *single* same-direction difference (any
  tuple of directions with a zero entry contributes nothing);
* `iteratedFwdDiff_replicate_two_torsion` — in the 2-torsion direction that difference collapses to
  `(-2)^n • D_e f`, which over `ZMod 2^k` vanishes exactly when `n ≥ k`.

The injective transfer `isPolyDegLE_comp_iff` (along `ZMod.toAddCircle`) lifts everything to the genuine torus,
so all `towerT…` statements are about the real `ℝ/ℤ`-valued object. Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

/-! ### Reduction of univariate degree to one same-direction difference -/

/-- On `(𝔽₂)¹`, every vector is either `0` or the all-ones vector. -/
private lemma fin1_dichotomy (v : Fin 1 → ZMod 2) : v = 0 ∨ v = (fun _ => 1) := by
  have h2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h2 (v 0) with h | h
  · left; funext i; fin_cases i; simpa using h
  · right; funext i; fin_cases i; simpa using h

/-- **Univariate degree reduces to a single same-direction difference.** On `(𝔽₂)¹`, any iterated
derivative that uses a zero direction vanishes, so `P` has degree `≤ k` **iff** its `(k+1)`-fold difference
in the one nonzero direction is zero. -/
lemma isPolyDegLE_univariate_iff {G : Type*} [AddCommGroup G] {k : ℕ}
    (P : (Fin 1 → ZMod 2) → G) :
    IsPolyDegLE k P ↔ iteratedFwdDiff (List.replicate (k + 1) (fun _ => 1)) P = 0 := by
  constructor
  · intro h
    have := h (fun _ => (fun _ => 1))
    rwa [List.ofFn_const] at this
  · intro h ys
    by_cases hz : (0 : Fin 1 → ZMod 2) ∈ List.ofFn ys
    · exact iteratedFwdDiff_eq_zero_of_zero_mem P hz
    · have hys : ys = fun _ => (fun _ => 1) := by
        funext i
        rcases fin1_dichotomy (ys i) with h0 | h1
        · exact absurd ((List.mem_ofFn' ys 0).mpr ⟨i, h0⟩) hz
        · exact h1
      rw [hys, List.ofFn_const]; exact h

/-! ### The finite depth-`k` model over `ZMod 2^k` -/

instance instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩

/-- Finite model of rung `k`: `v ↦ |v₀|` in `ZMod 2^k`. -/
def sk (k : ℕ) : (Fin 1 → ZMod 2) → ZMod (2 ^ k) := fun v => ((v 0).val : ZMod (2 ^ k))

/-- `sₖ` sends the generator to `1`. -/
lemma sk_apply_one (k : ℕ) : sk k (fun _ => 1) = 1 := by
  have hv1 : ((1 : ZMod 2)).val = 1 := by decide
  simp only [sk, hv1, Nat.cast_one]

/-- The first difference of `sₖ` at `0` is `1`. -/
lemma sk_fwdDiff_zero (k : ℕ) : fwdDiff (fun _ => (1 : ZMod 2)) (sk k) 0 = 1 := by
  have hv1 : ((1 : ZMod 2)).val = 1 := by decide
  have hv0 : ((0 : ZMod 2)).val = 0 := by decide
  simp only [fwdDiff, sk, zero_add, Pi.zero_apply, hv1, hv0, Nat.cast_one, Nat.cast_zero, sub_zero]

/-- The generator is 2-torsion. -/
lemma he1 : (fun _ => (1 : ZMod 2)) + (fun _ => (1 : ZMod 2)) = (0 : Fin 1 → ZMod 2) := by decide

/-! ### The two `ZMod 2^k` number facts

The `(k+1)`-fold same-direction difference of `sₖ` is `(-2)^k • D_e sₖ`; over `ZMod 2^k` the scalar `(-2)^j`
vanishes exactly when `k ≤ j`, which is what pins the degree at `k`. -/

/-- In `ZMod 2^k` the integer scalar `(-2)^j` is zero iff `k ≤ j`. -/
lemma neg_two_intCast (k j : ℕ) : (((-2 : ℤ) ^ j : ℤ) : ZMod (2 ^ k)) = 0 ↔ k ≤ j := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natAbs_dvd_natAbs]
  simp only [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast]
  change 2 ^ k ∣ 2 ^ j ↔ k ≤ j
  rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)]

/-- The scalar `(-2)^k` annihilates all of `ZMod 2^k`. -/
lemma neg_two_pow_smul_zmod (k : ℕ) (x : ZMod (2 ^ k)) : ((-2 : ℤ) ^ k) • x = 0 := by
  rw [zsmul_eq_mul, (neg_two_intCast k k).mpr le_rfl, zero_mul]

/-! ### Degree exactly `k`, for all `k` -/

/-- On the finite model, `sₖ` has degree `≤ k`. -/
lemma sk_isPolyDegLE (k : ℕ) : IsPolyDegLE k (sk k) := by
  rw [isPolyDegLE_univariate_iff, iteratedFwdDiff_replicate_two_torsion he1]
  funext v
  rw [Pi.smul_apply, Pi.zero_apply, neg_two_pow_smul_zmod]

/-- On the finite model, `sₖ` is not of degree `≤ k-1` (for `k ≥ 1`). -/
lemma sk_not_isPolyDegLE_pred (k : ℕ) (hk : 1 ≤ k) : ¬ IsPolyDegLE (k - 1) (sk k) := by
  rw [isPolyDegLE_univariate_iff, iteratedFwdDiff_replicate_two_torsion he1]
  intro hc
  have hval := congrFun hc 0
  rw [Pi.smul_apply, Pi.zero_apply, sk_fwdDiff_zero, zsmul_eq_mul, mul_one, neg_two_intCast] at hval
  omega

/-- The **genuine torus tower** `Sₖ = |x|/2^k : (𝔽₂)¹ → ℝ/ℤ`. -/
noncomputable def towerT (k : ℕ) : (Fin 1 → ZMod 2) → UnitAddCircle :=
  (ZMod.toAddCircle : ZMod (2 ^ k) →+ UnitAddCircle) ∘ sk k

/-- **`Sₖ` has degree `≤ k` over `ℝ/ℤ`, for every `k`.** -/
theorem towerT_isPolyDegLE (k : ℕ) : IsPolyDegLE k (towerT k) :=
  (isPolyDegLE_comp_iff (ZMod.toAddCircle_injective (2 ^ k))).mpr (sk_isPolyDegLE k)

/-- **…and its degree is exactly `k`: not `≤ k-1`, for every `k ≥ 1`.** This is the uniform statement — the
whole tower, not a family of separate checks. -/
theorem towerT_not_isPolyDegLE_pred (k : ℕ) (hk : 1 ≤ k) : ¬ IsPolyDegLE (k - 1) (towerT k) :=
  fun h => sk_not_isPolyDegLE_pred k hk
    ((isPolyDegLE_comp_iff (ZMod.toAddCircle_injective (2 ^ k))).mp h)

/-! ### The classical → nonclassical boundary -/

/-- Rung `k = 1` (`|x|/2`) is **classical**: every value is `2`-torsion. -/
theorem towerT_isClassical_one : IsClassical 2 (towerT 1) := by
  intro x
  simp only [towerT, Function.comp_apply, ← map_nsmul]
  rw [ZMod.toAddCircle_eq_zero]
  revert x
  decide

/-- Every rung `k ≥ 2` is **nonclassical**: `2 • (1/2^k) = 1/2^{k-1} ≠ 0`, so its values are not `2`-torsion. -/
theorem towerT_not_isClassical (k : ℕ) (hk : 2 ≤ k) : ¬ IsClassical 2 (towerT k) := by
  intro h
  have h2 := h (fun _ => 1)
  simp only [towerT, Function.comp_apply, ← map_nsmul, sk_apply_one] at h2
  rw [ZMod.toAddCircle_eq_zero, nsmul_eq_mul, mul_one,
    CharP.cast_eq_zero_iff (ZMod (2 ^ k)) (2 ^ k) 2] at h2
  have h4 : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2le : 2 ^ k ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

/-! ### The concrete rungs `k = 1, 2, 3`

Instances of the uniform theorems. The `k = 2` rung recovers the mother example `|x|/4` of `Polynomial`. -/

example : IsPolyDegLE 1 (towerT 1) ∧ ¬ IsPolyDegLE 0 (towerT 1) ∧ IsClassical 2 (towerT 1) :=
  ⟨towerT_isPolyDegLE 1, towerT_not_isPolyDegLE_pred 1 (by norm_num), towerT_isClassical_one⟩

example : IsPolyDegLE 2 (towerT 2) ∧ ¬ IsPolyDegLE 1 (towerT 2) ∧ ¬ IsClassical 2 (towerT 2) :=
  ⟨towerT_isPolyDegLE 2, towerT_not_isPolyDegLE_pred 2 (by norm_num),
    towerT_not_isClassical 2 (by norm_num)⟩

example : IsPolyDegLE 3 (towerT 3) ∧ ¬ IsPolyDegLE 2 (towerT 3) ∧ ¬ IsClassical 2 (towerT 3) :=
  ⟨towerT_isPolyDegLE 3, towerT_not_isPolyDegLE_pred 3 (by norm_num),
    towerT_not_isClassical 3 (by norm_num)⟩

end ECCLib

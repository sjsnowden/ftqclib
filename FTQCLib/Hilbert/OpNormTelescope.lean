/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # Telescoping the operator norm over a product of contractions

Infrastructure for an ℓ²-operator-norm SU(2) coverage argument. (The coverage theorem
`su2_coverage` in `FTQCLib/Examples/SU2CoverageLinfty.lean` is the ℓ∞/max-row-sum version; it uses
its own product-difference bound and does not import this file.) The Euler approximant
`R_z(α)·H·R_z(β)·H·R_z(γ)` replaces each of the three rotations by its dyadic tower gate and keeps the two
`H`'s exact; bounding the composite needs: the norm of a difference of two products of contractions
(operators of norm `≤ 1`) is at most the sum of the per-factor differences. Nothing of this shape exists in
Mathlib (only submultiplicativity `norm_mul_le` / `opNorm_comp_le`), so it is assembled here from the
identity `a·P − b·Q = a·(P − Q) + (a − b)·Q` and induction over the factor list.

Stated for an arbitrary normed ring — the operator ring `QState n →L[ℂ] QState n` is the instance used by
the coverage theorem, where the ring product is composition and `‖1‖ = 1`. -/

namespace FTQCLib.Hilbert

variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- A product of contractions (`‖x‖ ≤ 1`) is itself a contraction. -/
theorem norm_list_prod_le_one : ∀ {l : List R}, (∀ x ∈ l, ‖x‖ ≤ 1) → ‖l.prod‖ ≤ 1
  | [], _ => by simpa using (le_of_eq norm_one)
  | a :: t, h => by
    rw [List.prod_cons]
    calc ‖a * t.prod‖
        ≤ ‖a‖ * ‖t.prod‖ := norm_mul_le a t.prod
      _ ≤ 1 * 1 := mul_le_mul (h a (by simp))
          (norm_list_prod_le_one fun x hx => h x (by simp [hx])) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

/-- **Telescoping.** For equal-length lists of contractions, the norm of the difference of the two
products is bounded by the sum of the per-factor norm-differences:
`‖∏ aᵢ − ∏ bᵢ‖ ≤ Σ ‖aᵢ − bᵢ‖`. -/
theorem norm_list_prod_sub_le : ∀ (as bs : List R), as.length = bs.length →
    (∀ x ∈ as, ‖x‖ ≤ 1) → (∀ x ∈ bs, ‖x‖ ≤ 1) →
    ‖as.prod - bs.prod‖ ≤ (List.zipWith (fun a b => ‖a - b‖) as bs).sum
  | [], [], _, _, _ => by simp
  | [], b :: bs, hlen, _, _ => by simp at hlen
  | a :: as, [], hlen, _, _ => by simp at hlen
  | a :: as, b :: bs, hlen, ha, hb => by
    rw [List.prod_cons, List.prod_cons, List.zipWith_cons_cons, List.sum_cons]
    have hkey : a * as.prod - b * bs.prod = a * (as.prod - bs.prod) + (a - b) * bs.prod := by
      noncomm_ring
    rw [hkey]
    have hbtail : ‖bs.prod‖ ≤ 1 := norm_list_prod_le_one fun x hx => hb x (by simp [hx])
    have h1 : ‖a * (as.prod - bs.prod)‖ ≤ ‖as.prod - bs.prod‖ :=
      calc ‖a * (as.prod - bs.prod)‖
          ≤ ‖a‖ * ‖as.prod - bs.prod‖ := norm_mul_le _ _
        _ ≤ 1 * ‖as.prod - bs.prod‖ :=
            mul_le_mul_of_nonneg_right (ha a (by simp)) (norm_nonneg _)
        _ = ‖as.prod - bs.prod‖ := one_mul _
    have h2 : ‖(a - b) * bs.prod‖ ≤ ‖a - b‖ :=
      calc ‖(a - b) * bs.prod‖
          ≤ ‖a - b‖ * ‖bs.prod‖ := norm_mul_le _ _
        _ ≤ ‖a - b‖ * 1 := mul_le_mul_of_nonneg_left hbtail (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _
    have hIH := norm_list_prod_sub_le as bs (by simpa using hlen)
      (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx]))
    calc ‖a * (as.prod - bs.prod) + (a - b) * bs.prod‖
        ≤ ‖a * (as.prod - bs.prod)‖ + ‖(a - b) * bs.prod‖ := norm_add_le _ _
      _ ≤ ‖as.prod - bs.prod‖ + ‖a - b‖ := add_le_add h1 h2
      _ ≤ (List.zipWith (fun a b => ‖a - b‖) as bs).sum + ‖a - b‖ := by linarith
      _ = ‖a - b‖ + (List.zipWith (fun a b => ‖a - b‖) as bs).sum := by ring

end FTQCLib.Hilbert

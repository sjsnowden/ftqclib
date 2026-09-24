/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKTwoSided
import FTQCLib.Hilbert.FrameKernel
import FTQCLib.Hierarchy.FrameExponent

/-! # Kernel frame — the representation theorem (RT)

The representation theorem maps the frame's exponent calculus onto the diagonal Clifford hierarchy:

* `rt_levels` (RT(b)) — levels to levels, verbatim `cgk_exact_level`.
* `rt_classify` (RT(c)) — classification (k ≥ 2, free phase), verbatim
  `cgk_diagonal_dyadic_iff`; `rt_classify_one` the k = 1 dyadic companion.
* `rt_inj` (RT(a)) — the kernel map is injective up to global phase on normal
  forms (the substantive new content of "ker(sem) = R").
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

/-- **RT(b) — levels to levels** (pointed). A constant-free multilinear
exponent's kernel sits at hierarchy level `k` exactly when its frame level is
`≤ k`. Verbatim `cgk_exact_level` in frame vocabulary (`kernel P` for
`diagonalGateEquiv (realPhase P)`, `level P` for `effectiveLevel P`). -/
theorem rt_levels {m : ℕ} {P : DiagPhase n m} {k : ℕ} (hk : 1 ≤ k)
    (h_mul : DiagPhase.IsMultilinear P) (h_const : P.coeff 0 = 0) :
    IsCliffordHierarchyDyadic k (kernel P) ↔ level P ≤ k :=
  cgk_exact_level hk h_mul h_const

/-- **RT(c) — classification** (k ≥ 2, free global phase). Verbatim
`cgk_diagonal_dyadic_iff` in frame vocabulary. -/
theorem rt_classify {k : ℕ} (hk : 2 ≤ k) (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f) :
    IsCliffordHierarchyDyadic k U ↔ ∃ (α : ℂˣ) (P : DiagPhase n k),
      DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧ level P ≤ k ∧ U = scaleEquiv α (kernel P) :=
  cgk_diagonal_dyadic_iff hk U h_diag

/-- **RT(c) — classification, k = 1 companion** (dyadic global phase). Verbatim
`cgk_diagonal_dyadic_iff_one` in frame vocabulary. -/
theorem rt_classify_one (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f) :
    IsCliffordHierarchyDyadic 1 U ↔ ∃ (α : ℂˣ) (P : DiagPhase n 1),
      IsDyadicScalar α ∧ DiagPhase.IsMultilinear P ∧ P.coeff 0 = 0 ∧
        level P ≤ 1 ∧ U = scaleEquiv α (kernel P) :=
  cgk_diagonal_dyadic_iff_one U h_diag

/-! ### RT(a) — `ker(sem) = R`: the kernel map is injective up to global phase

The genuinely-new clause. The "semantics" `sem : P ↦ kernel P` descends, modulo
the global-phase group `U(1)`, to an **injective** map on constant-free
multilinear exponents, with kernel exactly the relation `R` (the precision-lift
identification). The homomorphism law is `kernel_add`; the image is the dyadic
projective diagonals (`rt_classify`). Both clauses below reuse the verified gate
→ values bridge `eval_val_mul_eq_of_eq_scaleEquiv` (which already forces the unit
to `1`, extracts eigenvalues, and pins the phase via the `[0, 2π)` bounds). -/

/-- **RT(a) — `ker(sem) = R`** (the relation is precision-lift). If two
constant-free multilinear exponents at precisions `m₁ ≤ m₂` have kernels equal up
to a global phase, then `Q` is exactly the precision-lift of `P`: `liftTo m₂ P = Q`.
So the only way two presentations share a kernel-mod-`U(1)` is the move `R₂`
(precision lift) — the content of `ker(sem) = R`. -/
theorem rt_inj_cross {m₁ m₂ : ℕ} (h12 : m₁ ≤ m₂)
    {P : DiagPhase n m₁} {Q : DiagPhase n m₂} {α : ℂˣ}
    (hP_mul : DiagPhase.IsMultilinear P) (hP_c0 : P.coeff 0 = 0)
    (hQ_mul : DiagPhase.IsMultilinear Q) (hQ_c0 : Q.coeff 0 = 0)
    (h : kernel Q = scaleEquiv α (kernel P)) :
    liftTo m₂ h12 P = Q := by
  simp only [kernel_def] at h
  apply eq_liftTo_of_val_table h12 hP_mul hQ_mul
  intro v
  have hval := eval_val_mul_eq_of_eq_scaleEquiv hP_c0 hQ_c0 h v
  -- hval : (Q.eval v).val * 2 ^ m₁ = (P.eval v).val * 2 ^ m₂
  -- Detach the `.val`s to opaque ℕ so the `2 ^ m₂` factor can be split without
  -- the rewrite touching the `ZMod (2 ^ m₂)` in the type of `(Q.eval v).val`.
  set a := (Q.eval v).val with ha
  set b := (P.eval v).val with hb
  have hsplit : (2 : ℕ) ^ m₂ = 2 ^ (m₂ - m₁) * 2 ^ m₁ := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← mul_assoc] at hval
  -- hval : a * 2 ^ m₁ = b * 2 ^ (m₂ - m₁) * 2 ^ m₁
  have h2m1 : (0 : ℕ) < 2 ^ m₁ := by positivity
  have hQP := Nat.eq_of_mul_eq_mul_right h2m1 hval
  -- hQP : a = b * 2 ^ (m₂ - m₁)
  rw [Nat.mul_comm] at hQP
  exact hQP.symm

/-- **RT(a) — injectivity** (same precision). The kernel map is injective up to
global phase: at a fixed precision, two constant-free multilinear exponents whose
kernels agree up to a phase are equal. The `m₁ = m₂` case of `rt_inj_cross`,
where the only relation is equality. -/
theorem rt_inj {m : ℕ} {P Q : DiagPhase n m} {α : ℂˣ}
    (hP_mul : DiagPhase.IsMultilinear P) (hP_c0 : P.coeff 0 = 0)
    (hQ_mul : DiagPhase.IsMultilinear Q) (hQ_c0 : Q.coeff 0 = 0)
    (h : kernel Q = scaleEquiv α (kernel P)) :
    P = Q := by
  simp only [kernel_def] at h
  apply multilinear_eval_injective hP_mul hQ_mul
  intro v
  have hval := eval_val_mul_eq_of_eq_scaleEquiv hP_c0 hQ_c0 h v
  have h2m : (0 : ℕ) < 2 ^ m := by positivity
  have hve : (Q.eval v).val = (P.eval v).val := Nat.eq_of_mul_eq_mul_right h2m hval
  exact (ZMod.val_injective _ hve).symm

/-! ### RT(d) — filtration / group form -/

/-- **RT(d) — filtration / group form** (k ≥ 2). The diagonal level-`k` group is
`U(1) × (level-graded exponent components)`: the global-phase circle times the
frame's level-graded exponent filtration `∏_{∅≠S,|S|≤k} ℤ/2^(k−|S|+1)`
(`CGKComponents`). The circle factor is exactly the `U(1)` modded out in `RT(a)`;
the components factor is the frame's exponent calculus, graded by level. Verbatim
`cgkDiagonalParametrization`. -/
noncomputable def rt_filtration {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    (Circle × Multiplicative (CGKComponents n k))
      ≃* ↥(diagonalDyadicSubgroup n k hk1) :=
  cgkDiagonalParametrization hk1 hk2

/-- **RT(d) — generators.** Circle phases together with single-monomial gates
generate the diagonal level-`k` group: the frame's exponents are generated, under
the kernel map, by the gate words. Verbatim `cgk_generating_set`. -/
theorem rt_generators {k : ℕ} (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) :
    Subgroup.closure
      (Set.range (fun ζ : Circle => cgkParamFun hk1 hk2 (ζ, 1))
        ∪ Set.range (fun p : (S : CGKIndex n k)
              × ZMod (2 ^ (k - S.val.card + 1)) =>
            cgkParamFun hk1 hk2 (1, Multiplicative.ofAdd (Pi.single p.1 p.2))))
      = (⊤ : Subgroup ↥(diagonalDyadicSubgroup n k hk1)) :=
  cgk_generating_set hk1 hk2

end FTQCLib.Frame

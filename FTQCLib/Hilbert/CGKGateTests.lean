/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKTwoSided
import FTQCLib.Hierarchy.GatePolynomials

set_option linter.unusedSectionVars false

/-! # Gate sanity suite for the sharp CGK classification

Membership test theorems certifying the standard gates at their SHARP
hierarchy levels — each one level below what `cgk_forward` could
certify. These fail to compile if a sharpness regression slips into the
forward direction:

* `Z` at level 1, `S` at level 2, `T` at level 3 (the `rzGatePoly`
  ladder at precisions 1, 2, 3);
* `CS` at level 3 (precision 2, degree 2 — defined here as `csPoly`);
* `CCZ` at level 3 (precision 1, degree 3).

Strictness lower bounds (e.g. `T ∉ C₂`) are out of scope.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## Helpers -/

lemma X_eq_monomial {m : ℕ} (i : Fin n) :
    (MvPolynomial.X i : DiagPhase n m)
      = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ m)) := by
  rw [← MvPolynomial.X_pow_eq_monomial, pow_one]

lemma twoAdicVal_one_eq_zero {m : ℕ} (h1 : (1 : ZMod (2 ^ m)) ≠ 0)
    (hval : (1 : ZMod (2 ^ m)).val = 1) :
    DiagPhase.twoAdicVal (1 : ZMod (2 ^ m)) = 0 := by
  rw [DiagPhase.twoAdicVal_of_ne_zero h1, hval]
  simp [Nat.factorization_one]

private lemma single_lin (i : Fin n) : ∀ j, (Finsupp.single i (1 : ℕ)) j ≤ 1 := by
  intro j
  rw [Finsupp.single_apply]
  split_ifs <;> omega

private lemma single_sum (i : Fin n) :
    (Finsupp.single i (1 : ℕ)).sum (fun _ e => e) = 1 :=
  Finsupp.sum_single_index rfl

/-! ## The rzGatePoly ladder: Z @ 1, S @ 2, T @ 3 -/

/-- The Z gate sits at dyadic hierarchy level 1 (sharp). -/
theorem zGate_mem_dyadic_one (i : Fin n) :
    IsCliffordHierarchyDyadic 1
      (diagonalGateEquiv (DiagPhase.realPhase (rzGatePoly i 1))) := by
  rw [show rzGatePoly i 1
      = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 1))
    from X_eq_monomial i]
  apply cgk_forward_monomial _ _ (le_refl 1) (single_lin i)
    (Finsupp.single_ne_zero.mpr one_ne_zero)
  rw [twoAdicVal_one_eq_zero (by decide) (by decide), single_sum]

/-- The S gate sits at dyadic hierarchy level 2 (sharp; `cgk_forward`
only certified 3). -/
theorem sGate_mem_dyadic_two (i : Fin n) :
    IsCliffordHierarchyDyadic 2
      (diagonalGateEquiv (DiagPhase.realPhase (rzGatePoly i 2))) := by
  rw [show rzGatePoly i 2
      = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 2))
    from X_eq_monomial i]
  apply cgk_forward_monomial _ _ (by omega) (single_lin i)
    (Finsupp.single_ne_zero.mpr one_ne_zero)
  rw [twoAdicVal_one_eq_zero (by decide) (by decide), single_sum]

/-- The T gate sits at dyadic hierarchy level 3 (sharp; `cgk_forward`
only certified 4). -/
theorem tGate_mem_dyadic_three (i : Fin n) :
    IsCliffordHierarchyDyadic 3
      (diagonalGateEquiv (DiagPhase.realPhase (tGatePoly i))) := by
  rw [show tGatePoly i
      = MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 3))
    from X_eq_monomial i]
  apply cgk_forward_monomial _ _ (by omega) (single_lin i)
    (Finsupp.single_ne_zero.mpr one_ne_zero)
  rw [twoAdicVal_one_eq_zero (by decide) (by decide), single_sum]

/-! ## CS @ 3 -/

/-- The CS gate sits at dyadic hierarchy level 3 (sharp: precision 2,
degree 2). -/
theorem csGate_mem_dyadic_three (i j : Fin n) (hij : i ≠ j) :
    IsCliffordHierarchyDyadic 3
      (diagonalGateEquiv (DiagPhase.realPhase (csPoly i j))) := by
  have hd : csPoly i j = MvPolynomial.monomial
      (Finsupp.single i 1 + Finsupp.single j 1) (1 : ZMod (2 ^ 2)) := by
    unfold csPoly
    rw [X_eq_monomial, X_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  rw [hd]
  apply cgk_forward_monomial _ _ (by omega)
  · intro l
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h1 : i = l <;> by_cases h2 : j = l
    · exact absurd (h1.trans h2.symm) hij
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  · intro h0
    have h := congrArg (fun d : Fin n →₀ ℕ => d i) h0
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h
    rw [Finsupp.single_apply, if_pos rfl, Finsupp.single_apply,
      if_neg (fun hji => hij hji.symm)] at h
    omega
  · have hsum : (Finsupp.single i (1 : ℕ) + Finsupp.single j 1).sum
        (fun _ e => e) = 2 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
    rw [twoAdicVal_one_eq_zero (by decide) (by decide), hsum]

/-! ## CCZ @ 3 -/

/-- The CCZ gate sits at dyadic hierarchy level 3 (sharp: precision 1,
degree 3). -/
theorem cczGate_mem_dyadic_three (i j l : Fin n)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    IsCliffordHierarchyDyadic 3
      (diagonalGateEquiv (DiagPhase.realPhase (cczPoly i j l))) := by
  have hd : cczPoly i j l = MvPolynomial.monomial
      (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single l 1)
      (1 : ZMod (2 ^ 1)) := by
    unfold cczPoly
    rw [X_eq_monomial, X_eq_monomial, X_eq_monomial,
      MvPolynomial.monomial_mul, MvPolynomial.monomial_mul, one_mul, one_mul]
  rw [hd]
  apply cgk_forward_monomial _ _ (by omega)
  · intro w
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply,
      Finsupp.single_apply, Finsupp.single_apply]
    by_cases h1 : i = w <;> by_cases h2 : j = w <;> by_cases h3 : l = w
    · exact absurd (h1.trans h2.symm) hij
    · exact absurd (h1.trans h2.symm) hij
    · exact absurd (h1.trans h3.symm) hil
    · simp [h1, h2, h3]
    · exact absurd (h2.trans h3.symm) hjl
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]
  · intro h0
    have h := congrArg (fun d : Fin n →₀ ℕ => d i) h0
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at h
    rw [Finsupp.single_apply, if_pos rfl, Finsupp.single_apply,
      if_neg (fun hji => hij hji.symm), Finsupp.single_apply,
      if_neg (fun hli => hil hli.symm)] at h
    omega
  · have hsum : (Finsupp.single i (1 : ℕ) + Finsupp.single j 1
        + Finsupp.single l 1).sum (fun _ e => e) = 3 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl,
        Finsupp.sum_single_index rfl]
    rw [twoAdicVal_one_eq_zero (by decide) (by decide), hsum]

end FTQCLib.Hilbert

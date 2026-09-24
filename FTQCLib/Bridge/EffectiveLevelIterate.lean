/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.FuncDeriv

set_option linter.style.longLine false

/-!
# Iterating the `effectiveLevel` strict-drop to a degree bound

Frame-side support for the bridge theorem `IsPolyDegLE (effectiveLevel P) (eval P)` (in
`FTQCLib/Bridge/HOFBridge.lean`). The strict-drop lemma `shiftDeriv_effectiveLevel_lt` requires
its argument to be multilinear, so to *iterate* it we first show `shiftDeriv` **preserves**
multilinearity (`IsMultilinear.shiftDeriv`). Then a strong induction on `effectiveLevel P` gives
that any `(effectiveLevel P + 1)`-fold `shiftDeriv` composition of a multilinear `P` is the zero
polynomial (`shiftDeriv_foldr_eq_zero_of_lt`). This file has no `ECCLib` dependency; the
higher-order Fourier theorem (feeding this into the unit-directions reduction) lives in
`HOFBridge.lean`.
-/

namespace FTQCLib.Bridge

open FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase MvPolynomial

variable {n m : ℕ}

/-- **`shiftDeriv` preserves multilinearity.** Decomposing `P` into monomials, `shiftDeriv i` sends each
multilinear monomial either to `0` (when `d i = 0`) or to `monomial (d.erase i) c − 2·monomial d c` (when
`d i = 1`), both of whose supports (`{d.erase i}`, `{d}`) are multilinear exponent vectors. -/
theorem IsMultilinear.shiftDeriv {P : DiagPhase n m} (hP : DiagPhase.IsMultilinear P) (i : Fin n) :
    DiagPhase.IsMultilinear (DiagPhase.shiftDeriv i P) := by
  classical
  have hdecomp : DiagPhase.shiftDeriv i P
      = ∑ d ∈ P.support, DiagPhase.shiftDeriv i (monomial d (coeff d P)) := by
    simp only [DiagPhase.shiftDeriv]
    conv_lhs => rw [show P = ∑ d ∈ P.support, monomial d (coeff d P) from P.as_sum]
    rw [map_sum, Finset.sum_sub_distrib]
  intro e he k
  rw [hdecomp] at he
  have hex : ∃ d ∈ P.support, e ∈ (DiagPhase.shiftDeriv i (monomial d (coeff d P))).support := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    apply (mem_support_iff.mp he)
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro d hd
    by_contra h
    exact hcon d hd (mem_support_iff.mpr h)
  obtain ⟨d, hd, hde⟩ := hex
  have hdml : ∀ j, d j ≤ 1 := hP d hd
  by_cases hdi : d i = 0
  · rw [shiftDeriv_monomial_of_di_zero i d (coeff d P) hdi] at hde
    simp at hde
  · have hdi1 : d i = 1 := by have := hdml i; omega
    rw [shiftDeriv_monomial_multilinear_di_one i d (coeff d P) hdi1, mem_support_iff,
      coeff_sub, two_mul_monomial, coeff_monomial, coeff_monomial] at hde
    by_cases hde1 : d.erase i = e
    · rw [← hde1, Finsupp.erase_apply]
      split_ifs with hk
      · omega
      · exact hdml k
    · by_cases hde2 : d = e
      · rw [← hde2]; exact hdml k
      · exact absurd (by rw [if_neg hde1, if_neg hde2]; ring) hde

/-- `shiftDeriv` folded over any direction list annihilates the zero polynomial. -/
lemma foldr_shiftDeriv_zero (l : List (Fin n)) :
    l.foldr (DiagPhase.shiftDeriv (m := m)) (0 : DiagPhase n m) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih, DiagPhase.shiftDeriv_zero]

/-- **Iterating the strict-drop.** For multilinear `P`, any `shiftDeriv` composition longer than
`effectiveLevel P` is the zero polynomial. Strong induction on `effectiveLevel P`, peeling the innermost
direction: while `totalDegree P > 0` the strict-drop lowers the level and multilinearity is preserved (so
the IH applies); when `totalDegree P = 0` the whole composition collapses to `0`. -/
theorem shiftDeriv_foldr_eq_zero :
    ∀ (N : ℕ) (P : DiagPhase n m), DiagPhase.IsMultilinear P →
      DiagPhase.effectiveLevel P = N →
      ∀ (dirs : List (Fin n)), N < dirs.length → dirs.foldr DiagPhase.shiftDeriv P = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro P hP hN dirs hlen
    rcases List.eq_nil_or_concat dirs with rfl | ⟨init, last, rfl⟩
    · simp at hlen
    · rw [List.concat_eq_append, List.foldr_append, List.foldr_cons, List.foldr_nil]
      by_cases hdeg : P.totalDegree = 0
      · rw [DiagPhase.shiftDeriv_totalDegree_zero last hdeg]
        exact foldr_shiftDeriv_zero init
      · have hpos : 0 < P.totalDegree := Nat.pos_of_ne_zero hdeg
        have hlt := DiagPhase.shiftDeriv_effectiveLevel_lt last hP hpos
        have hmul' : DiagPhase.IsMultilinear (DiagPhase.shiftDeriv last P) :=
          IsMultilinear.shiftDeriv hP last
        simp only [List.length_concat] at hlen
        exact ih (DiagPhase.effectiveLevel (DiagPhase.shiftDeriv last P)) (by omega)
          _ hmul' rfl init (by omega)

/-- The usable form: `dirs.foldr shiftDeriv P = 0` whenever `effectiveLevel P < dirs.length`. -/
theorem shiftDeriv_foldr_eq_zero_of_lt (P : DiagPhase n m) (hP : DiagPhase.IsMultilinear P)
    (dirs : List (Fin n)) (hlen : DiagPhase.effectiveLevel P < dirs.length) :
    dirs.foldr DiagPhase.shiftDeriv P = 0 :=
  shiftDeriv_foldr_eq_zero _ P hP rfl dirs hlen

end FTQCLib.Bridge

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.AffineDifference
import FTQCLib.Hierarchy.BoolReduceLevel
import FTQCLib.Hierarchy.DyadicValuation
import FTQCLib.Hierarchy.GatePolynomials
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.LinearCombination

/-!
# The polar matrix of a diagonal exponent and the polarization law

A diagonal exponent `D : DiagPhase n m` of effective level at most two is a quadratic function
on `𝔽₂ⁿ` with values in `ZMod (2^m)`, and a quadratic function has a polar form. The **polar
matrix** `polarMatrix D` is the symmetric `𝔽₂`-matrix read from the coefficients: its diagonal
entry at `j` is the bit `[2·coeff(X_j) ≠ 0]` (the quarter turn), its off-diagonal entry at
`(j, k)` the bit `[coeff(X_j X_k) ≠ 0]` (the sign). **The polarization law** is the shift of the
exponent along `v`, with its constant explicit:

`D.eval (w + v) − D.eval w = (D.eval v − D.eval 0) + 2^{m−1} · ⟨polarMatrix D · v, w⟩`

for every `v w`, for every `D` of level at most two, with no multilinearity hypothesis
(`eval_add_sub_eval_eq_of_effectiveLevel_le_two`). The proof is per monomial: at level two an
exponent vector has weight at most two (`exponent_cases_two`), a degree-two coefficient is the
top bit (`eq_two_pow_pred_of_effLevelMonom_le_two`), a degree-one coefficient has `4c = 0` so
`2c` is `0` or the top bit (`four_mul_eq_zero_of_effLevelMonom_single_le_two` with the dichotomy
of `DyadicValuation`), the square `X_j²` contributes to the constant and never to the row, and
the law is additive (`PolarLaw.add`) with the matrix additive over the support
(`polarMatrix_eq_sum_monoMatrix`).

The frame's datum forms are corollaries: the shift datum `IsShiftDatum D.eval (polarMatrix D) V`
at every subspace `V`, with the constant forced (`const_eq_of_shift`); the half-diagonal
identity (`two_mul_eval_sub_eval_zero`: the constant is a `ℤ/4` refinement of the polar form);
the matrix is forced by a datum at `⊤` at positive precision (`eq_of_isShiftDatum_top`); a
datum on `V` makes the pairing symmetric on `V` (`symm_on_of_isShiftDatum`); and the transport
to the Boolean normal form under the extended level
(`isShiftDatum_polarMatrix_boolReduce_of_levelExt_le_two`), which is the reading the class rule
on the carrier uses. The instances `S` and `CZ` have the matrices their one-bit shears carry
(`polarMatrix_sGate` at precision at least two, `polarMatrix_czGate` on distinct bits), the `S`
exponent at precision one and the square `X_i²` have the zero matrix, and the instances' levels
are at most two at every precision.

## Main definitions

* `polarMatrix D` — the polar matrix, read from the coefficients.
* `IsShiftDatum f M V` — along every `v ∈ V` the shift of `f` is a constant plus the top bit
  times the pairing of `M v` with the word.
* `PolarLaw f M`, `topPairing M v w`, `monoMatrix d c` — the proof devices.

## Main results

* `eval_add_sub_eval_eq_of_effectiveLevel_le_two` — the polarization law.
* `two_mul_eval_sub_eval_zero` — the half-diagonal identity.
* `isShiftDatum_polarMatrix_of_effectiveLevel_le_two` — the datum for the class.
* `eq_of_isShiftDatum_top`, `symm_on_of_isShiftDatum` — uniqueness of the matrix; symmetry of
  the pairing from the datum.
* `isShiftDatum_polarMatrix_boolReduce_of_levelExt_le_two` — the datum on the normal form.
* `polarMatrix_sGate`, `polarMatrix_sGate_one`, `polarMatrix_czGate`, `polarMatrix_czGate_self`,
  `effectiveLevel_sGate_le_two`, `effectiveLevel_czGate_le_two`, `levelExt_sGate_le_two`,
  `levelExt_czGate_le_two` — the instances.

## Implementation notes

The coefficient reading is the level-two reading: outside the class the matrix has no meaning
(`X₀ + X₀²` at precision two reads a diagonal bit while its function is `Z₀`), which is why the
class rule reads it on the Boolean normal form and the floor theorem carries the level. The
pairing is written with Mathlib's `Matrix.mulVec` and `dotProduct`; the frame's `dotF2` is
`dotProduct` definitionally. `decide` runs through neither `MvPolynomial.coeff` nor
`DiagPhase.eval`, so every coefficient and evaluation row in the check module is a `rw` row. The
uniqueness theorem needs `1 ≤ m`: at precision zero every matrix carries every datum.
-/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial Matrix

variable {n m : ℕ}

/-! ## Bits -/

/-- A bit is `0` or `1`. -/
theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_two_val_zero : ((0 : ZMod 2).val : ℕ) = 0 := by decide

theorem zmod_two_val_one : ((1 : ZMod 2).val : ℕ) = 1 := by decide

theorem zmod_two_one_add_one : (1 + 1 : ZMod 2) = 0 := by decide

/-- The value of a sum of bits, in `ZMod (2^m)`: `(a ⊕ b) = a + b − 2ab`. -/
theorem val_add_bits (a b : ZMod 2) :
    (((a + b).val : ℕ) : ZMod (2 ^ m)) =
      ((a.val : ℕ) : ZMod (2 ^ m)) + ((b.val : ℕ) : ZMod (2 ^ m))
        - 2 * ((a.val : ℕ) : ZMod (2 ^ m)) * ((b.val : ℕ) : ZMod (2 ^ m)) := by
  rcases zmod_two_cases a with ha | ha <;> rcases zmod_two_cases b with hb | hb <;>
    subst ha <;> subst hb
  · simp
  · simp
  · simp
  · simp only [zmod_two_one_add_one, zmod_two_val_zero, zmod_two_val_one, Nat.cast_zero,
      Nat.cast_one]
    ring

/-- The value of a product of bits is the product of the values. -/
theorem val_mul_bits (a b : ZMod 2) :
    (((a * b).val : ℕ) : ZMod (2 ^ m)) =
      ((a.val : ℕ) : ZMod (2 ^ m)) * ((b.val : ℕ) : ZMod (2 ^ m)) := by
  rcases zmod_two_cases a with ha | ha <;> rcases zmod_two_cases b with hb | hb <;>
    subst ha <;> subst hb <;>
    simp only [mul_zero, mul_one, zmod_two_val_zero, zmod_two_val_one, Nat.cast_zero,
      Nat.cast_one]

/-- A bit squared is itself. -/
theorem val_sq_bit (a : ZMod 2) :
    ((a.val : ℕ) : ZMod (2 ^ m)) ^ 2 = ((a.val : ℕ) : ZMod (2 ^ m)) := by
  rcases zmod_two_cases a with ha | ha <;> subst ha <;>
    simp only [zmod_two_val_zero, zmod_two_val_one, Nat.cast_zero, Nat.cast_one,
      zero_pow two_ne_zero, one_pow]

/-! ## Exponent vectors of weight two -/

/-- Two pairs of distinct variables give the same exponent vector exactly when they are the
same pair. -/
theorem single_add_single_eq_iff {j k a b : Fin n} (hjk : j ≠ k) :
    Finsupp.single j 1 + Finsupp.single k 1 = Finsupp.single a 1 + Finsupp.single b (1 : ℕ) ↔
      (a = j ∧ b = k) ∨ (a = k ∧ b = j) := by
  constructor
  · intro h
    have hj := congrArg (fun d : Fin n →₀ ℕ => d j) h
    have hk := congrArg (fun d : Fin n →₀ ℕ => d k) h
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hj hk
    by_cases haj : a = j
    · subst haj
      left
      refine ⟨rfl, ?_⟩
      by_contra hbk
      simp only [if_true, if_neg hjk, if_neg hbk] at hk
      omega
    · by_cases hbj : b = j
      · subst hbj
        right
        refine ⟨?_, rfl⟩
        by_contra hak
        simp only [if_true, if_neg hjk, if_neg hak] at hk
        omega
      · exfalso
        simp only [if_true, if_neg haj, if_neg hbj, if_neg (Ne.symm hjk)] at hj
        omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

/-- A single variable is not a pair of distinct variables. -/
theorem single_ne_single_add_single {j a b : Fin n} (hab : a ≠ b) :
    Finsupp.single j 1 ≠ Finsupp.single a 1 + Finsupp.single b (1 : ℕ) := by
  intro h
  have ha := congrArg (fun d : Fin n →₀ ℕ => d a) h
  have hb := congrArg (fun d : Fin n →₀ ℕ => d b) h
  simp only [Finsupp.add_apply, Finsupp.single_apply, if_true, if_neg hab, if_neg (Ne.symm hab)]
    at ha hb
  by_cases hja : j = a
  · subst hja
    simp only [if_neg hab] at hb
    omega
  · simp only [if_neg hja] at ha
    omega

/-- A square is not a single variable. -/
theorem single_two_ne_single {j a : Fin n} : Finsupp.single j 2 ≠ Finsupp.single a (1 : ℕ) := by
  intro h
  have := congrArg (fun d : Fin n →₀ ℕ => d j) h
  simp only [Finsupp.single_apply] at this
  split_ifs at this <;> omega

/-- A square is not a pair of distinct variables. -/
theorem single_two_ne_single_add_single {j a b : Fin n} (hab : a ≠ b) :
    Finsupp.single j 2 ≠ Finsupp.single a 1 + Finsupp.single b (1 : ℕ) := by
  intro h
  have := congrArg (fun d : Fin n →₀ ℕ => d j) h
  simp only [Finsupp.add_apply, Finsupp.single_apply, if_true] at this
  by_cases haj : a = j
  · subst haj
    have hba : ¬ b = a := fun h => hab h.symm
    simp only [if_true, if_neg hba] at this
    omega
  · simp only [if_neg haj] at this
    split_ifs at this
    omega

/-- The zero exponent is not a pair of distinct variables. -/
theorem zero_ne_single_add_single {a b : Fin n} (hab : a ≠ b) :
    (0 : Fin n →₀ ℕ) ≠ Finsupp.single a 1 + Finsupp.single b 1 := by
  intro h
  have := congrArg (fun d : Fin n →₀ ℕ => d a) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply, Finsupp.single_apply, if_true,
    if_neg (Ne.symm hab)] at this
  omega

/-- An exponent vector of total weight at most two is zero, a variable, a square, or a pair of
distinct variables. -/
theorem exponent_cases_two {d : Fin n →₀ ℕ} (hd : d.sum (fun _ e => e) ≤ 2) :
    d = 0 ∨ (∃ j, d = Finsupp.single j 1) ∨ (∃ j, d = Finsupp.single j 2) ∨
      ∃ j k, j ≠ k ∧ d = Finsupp.single j 1 + Finsupp.single k 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr h0
  have hsum : d.sum (fun _ e => e) = ∑ l ∈ d.support, d l := rfl
  have hdj1 : 1 ≤ d j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hdjle : d j ≤ ∑ l ∈ d.support, d l :=
    Finset.single_le_sum (f := fun l => d l) (fun _ _ => Nat.zero_le _) hj
  by_cases hrest : ∃ k, k ≠ j ∧ k ∈ d.support
  · obtain ⟨k, hkj, hk⟩ := hrest
    have hdk1 : 1 ≤ d k := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)
    have hsub : ({j, k} : Finset (Fin n)) ⊆ d.support := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl'
      · exact hj
      · rw [Finset.mem_singleton] at hl'; subst hl'; exact hk
    have h2 : d j + d k ≤ ∑ l ∈ d.support, d l := by
      rw [← Finset.sum_pair (Ne.symm hkj)]
      exact Finset.sum_le_sum_of_subset hsub
    have hdj : d j = 1 := by omega
    have hdk : d k = 1 := by omega
    refine Or.inr (Or.inr (Or.inr ⟨j, k, Ne.symm hkj, ?_⟩))
    ext l
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hlj : l = j
    · subst hlj
      simp [hdj, hkj]
    · by_cases hlk : l = k
      · subst hlk
        simp [hdk, Ne.symm hlj]
      · rw [if_neg (fun h : j = l => hlj h.symm), if_neg (fun h : k = l => hlk h.symm)]
        by_contra hl
        have hlmem : l ∈ d.support := Finsupp.mem_support_iff.mpr hl
        have hsub3 : ({j, k, l} : Finset (Fin n)) ⊆ d.support := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hj
          · rcases Finset.mem_insert.mp hx' with rfl | hx''
            · exact hk
            · rw [Finset.mem_singleton] at hx''; subst hx''; exact hlmem
        have hnot : j ∉ ({k, l} : Finset (Fin n)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hkj, fun h : j = l => hlj h.symm⟩
        have h3 : d j + (d k + d l) ≤ ∑ x ∈ d.support, d x := by
          rw [← Finset.sum_pair (Ne.symm hlk), ← Finset.sum_insert hnot]
          exact Finset.sum_le_sum_of_subset hsub3
        omega
  · have hrest' : ∀ k, k ≠ j → k ∉ d.support := fun k hk hmem => hrest ⟨k, hk, hmem⟩
    have hsupp : d.support = {j} := by
      ext l
      constructor
      · intro hl
        by_contra hlj
        rw [Finset.mem_singleton] at hlj
        exact hrest' l hlj hl
      · intro hl; rw [Finset.mem_singleton] at hl; subst hl; exact hj
    have hdj2 : d j ≤ 2 := by
      have : ∑ l ∈ d.support, d l = d j := by rw [hsupp, Finset.sum_singleton]
      omega
    have hd_single : d = Finsupp.single j (d j) := by
      ext l
      rw [Finsupp.single_apply]
      by_cases hlj : l = j
      · subst hlj; rw [if_pos rfl]
      · rw [if_neg (fun h : j = l => hlj h.symm)]
        by_contra hl
        exact hrest' l hlj (Finsupp.mem_support_iff.mpr hl)
    rcases (show d j = 1 ∨ d j = 2 by omega) with h1 | h2
    · exact Or.inr (Or.inl ⟨j, by rw [hd_single, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, by rw [hd_single, h2]⟩))

/-! ## The polar matrix -/

/-- **The polar matrix** of a diagonal exponent, read from the coefficients. -/
noncomputable def polarMatrix (D : DiagPhase n m) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j =>
    if i = j then (if 2 * D.coeff (Finsupp.single i 1) = 0 then 0 else 1)
    else (if D.coeff (Finsupp.single i 1 + Finsupp.single j 1) = 0 then 0 else 1)

theorem polarMatrix_apply_self (D : DiagPhase n m) (i : Fin n) :
    polarMatrix D i i = if 2 * D.coeff (Finsupp.single i 1) = 0 then 0 else 1 := by
  simp [polarMatrix]

theorem polarMatrix_apply_of_ne (D : DiagPhase n m) {i j : Fin n} (h : i ≠ j) :
    polarMatrix D i j =
      if D.coeff (Finsupp.single i 1 + Finsupp.single j 1) = 0 then 0 else 1 := by
  simp [polarMatrix, h]

/-- The polar matrix is symmetric, for every exponent. -/
theorem polarMatrix_isSymm (D : DiagPhase n m) : (polarMatrix D).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  by_cases h : i = j
  · subst h; rfl
  · rw [polarMatrix_apply_of_ne D h, polarMatrix_apply_of_ne D (Ne.symm h), add_comm]

/-- The polar matrix does not read the constant. -/
theorem polarMatrix_sub_C (D : DiagPhase n m) (c : ZMod (2 ^ m)) :
    polarMatrix (D - MvPolynomial.C c) = polarMatrix D := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [polarMatrix_apply_self, polarMatrix_apply_self, coeff_sub, coeff_C,
      if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)), sub_zero]
  · rw [polarMatrix_apply_of_ne _ h, polarMatrix_apply_of_ne _ h, coeff_sub, coeff_C,
      if_neg (zero_ne_single_add_single h), sub_zero]

/-! ## The pairing and the law as a predicate -/

/-- The pairing of the row `M v` with the word, lifted to the top bit. -/
noncomputable def topPairing (M : Matrix (Fin n) (Fin n) (ZMod 2)) (v w : Fin n → ZMod 2) :
    ZMod (2 ^ m) :=
  (2 : ZMod (2 ^ m)) ^ (m - 1) * (((M *ᵥ v ⬝ᵥ w).val : ℕ) : ZMod (2 ^ m))

theorem topPairing_add (M N : Matrix (Fin n) (Fin n) (ZMod 2)) (v w : Fin n → ZMod 2) :
    (topPairing (M + N) v w : ZMod (2 ^ m)) = topPairing M v w + topPairing N v w := by
  unfold topPairing
  rw [Matrix.add_mulVec, add_dotProduct, two_pow_pred_mul_val_add]

theorem topPairing_zero (v w : Fin n → ZMod 2) : (topPairing 0 v w : ZMod (2 ^ m)) = 0 := by
  unfold topPairing
  rw [Matrix.zero_mulVec, zero_dotProduct, ZMod.val_zero, Nat.cast_zero, mul_zero]

/-- The pairing of a diagonal unit: the product of the two bits at `j`. -/
theorem topPairing_single_self (j : Fin n) (v w : Fin n → ZMod 2) :
    (topPairing (Matrix.single j j (1 : ZMod 2)) v w : ZMod (2 ^ m)) =
      (2 : ZMod (2 ^ m)) ^ (m - 1) *
        (((v j).val : ZMod (2 ^ m)) * ((w j).val : ZMod (2 ^ m))) := by
  unfold topPairing
  rw [Matrix.single_mulVec,
    show Function.update (0 : Fin n → ZMod 2) j (1 * v j) = Pi.single j (1 * v j) from rfl,
    single_dotProduct, one_mul, val_mul_bits]

/-- The pairing of an off-diagonal pair of units. -/
theorem topPairing_single_pair {j k : Fin n} (hjk : j ≠ k) (v w : Fin n → ZMod 2) :
    (topPairing (Matrix.single j k (1 : ZMod 2) + Matrix.single k j 1) v w : ZMod (2 ^ m)) =
      (2 : ZMod (2 ^ m)) ^ (m - 1) * (((v k).val : ZMod (2 ^ m)) * ((w j).val : ZMod (2 ^ m)))
        + (2 : ZMod (2 ^ m)) ^ (m - 1) *
          (((v j).val : ZMod (2 ^ m)) * ((w k).val : ZMod (2 ^ m))) := by
  have _ := hjk
  unfold topPairing
  rw [Matrix.add_mulVec, add_dotProduct, Matrix.single_mulVec, Matrix.single_mulVec,
    show Function.update (0 : Fin n → ZMod 2) j (1 * v k) = Pi.single j (1 * v k) from rfl,
    show Function.update (0 : Fin n → ZMod 2) k (1 * v j) = Pi.single k (1 * v j) from rfl,
    single_dotProduct, single_dotProduct, one_mul, one_mul, two_pow_pred_mul_val_add,
    val_mul_bits, val_mul_bits]

/-- **The polarization law** for a function `f` with matrix `M`. -/
def PolarLaw (f : (Fin n → ZMod 2) → ZMod (2 ^ m)) (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ v w, f (w + v) - f w = (f v - f 0) + topPairing M v w

theorem PolarLaw.add {f g : (Fin n → ZMod 2) → ZMod (2 ^ m)}
    {M N : Matrix (Fin n) (Fin n) (ZMod 2)} (hf : PolarLaw f M) (hg : PolarLaw g N) :
    PolarLaw (f + g) (M + N) := by
  intro v w
  simp only [Pi.add_apply]
  rw [topPairing_add]
  have h1 := hf v w
  have h2 := hg v w
  linear_combination h1 + h2

theorem PolarLaw.zero : PolarLaw (0 : (Fin n → ZMod 2) → ZMod (2 ^ m)) 0 := by
  intro v w
  simp [topPairing_zero]

theorem PolarLaw.sum {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ZMod 2) → ZMod (2 ^ m))
    (M : ι → Matrix (Fin n) (Fin n) (ZMod 2)) (h : ∀ i ∈ s, PolarLaw (f i) (M i)) :
    PolarLaw (∑ i ∈ s, f i) (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolarLaw.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The monomial matrices -/

/-- The polar matrix of one monomial `monomial d c`. -/
noncomputable def monoMatrix (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j =>
    if i = j then (if d = Finsupp.single i 1 then (if 2 * c = 0 then 0 else 1) else 0)
    else (if d = Finsupp.single i 1 + Finsupp.single j 1 then (if c = 0 then 0 else 1) else 0)

theorem monoMatrix_zero (c : ZMod (2 ^ m)) : monoMatrix (0 : Fin n →₀ ℕ) c = 0 := by
  ext a b
  simp only [monoMatrix, Matrix.of_apply, Matrix.zero_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero))]
  · rw [if_neg hab, if_neg (zero_ne_single_add_single hab)]

theorem monoMatrix_single_two (c : ZMod (2 ^ m)) (j : Fin n) :
    monoMatrix (Finsupp.single j 2) c = 0 := by
  ext a b
  simp only [monoMatrix, Matrix.of_apply, Matrix.zero_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg single_two_ne_single]
  · rw [if_neg hab, if_neg (single_two_ne_single_add_single hab)]

theorem monoMatrix_single (c : ZMod (2 ^ m)) (j : Fin n) :
    monoMatrix (Finsupp.single j 1) c =
      if 2 * c = 0 then 0 else Matrix.single j j (1 : ZMod 2) := by
  ext a b
  simp only [monoMatrix, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    by_cases hja : j = a
    · subst hja
      rw [if_pos rfl]
      by_cases h2 : 2 * c = 0
      · rw [if_pos h2, if_pos h2, Matrix.zero_apply]
      · rw [if_neg h2, if_neg h2, Matrix.single_apply_same]
    · rw [if_neg (fun h => hja ((Finsupp.single_left_inj one_ne_zero).mp h))]
      by_cases h2 : 2 * c = 0
      · rw [if_pos h2, Matrix.zero_apply]
      · rw [if_neg h2, Matrix.single_apply, if_neg (fun h => hja h.1)]
  · rw [if_neg hab, if_neg (single_ne_single_add_single hab)]
    by_cases h2 : 2 * c = 0
    · rw [if_pos h2, Matrix.zero_apply]
    · rw [if_neg h2, Matrix.single_apply, if_neg (fun h => hab (h.1.symm.trans h.2))]

theorem monoMatrix_pair (c : ZMod (2 ^ m)) {j k : Fin n} (hjk : j ≠ k) :
    monoMatrix (Finsupp.single j 1 + Finsupp.single k 1) c =
      if c = 0 then 0 else Matrix.single j k (1 : ZMod 2) + Matrix.single k j 1 := by
  ext a b
  simp only [monoMatrix, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg (Ne.symm (single_ne_single_add_single hjk))]
    by_cases hc : c = 0
    · rw [if_pos hc, Matrix.zero_apply]
    · rw [if_neg hc, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
        if_neg (fun h => hjk (h.1.trans h.2.symm)), if_neg (fun h => hjk (h.2.trans h.1.symm)),
        add_zero]
  · rw [if_neg hab]
    by_cases hp : Finsupp.single j 1 + Finsupp.single k 1 = Finsupp.single a 1 + Finsupp.single b 1
    · rw [if_pos hp]
      rcases (single_add_single_eq_iff hjk).mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · by_cases hc : c = 0
        · rw [if_pos hc, if_pos hc, Matrix.zero_apply]
        · rw [if_neg hc, if_neg hc, Matrix.add_apply, Matrix.single_apply_same,
            Matrix.single_apply, if_neg (fun h => hab h.2), add_zero]
      · by_cases hc : c = 0
        · rw [if_pos hc, if_pos hc, Matrix.zero_apply]
        · rw [if_neg hc, if_neg hc, Matrix.add_apply, Matrix.single_apply,
            if_neg (fun h => hab h.2), Matrix.single_apply_same, zero_add]
    · rw [if_neg hp]
      have h1 : ¬ (j = a ∧ k = b) := fun h =>
        hp ((single_add_single_eq_iff hjk).mpr (Or.inl ⟨h.1.symm, h.2.symm⟩))
      have h2 : ¬ (k = a ∧ j = b) := fun h =>
        hp ((single_add_single_eq_iff hjk).mpr (Or.inr ⟨h.1.symm, h.2.symm⟩))
      by_cases hc : c = 0
      · rw [if_pos hc, Matrix.zero_apply]
      · rw [if_neg hc, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1,
          if_neg h2, add_zero]

/-- The polar matrix is the sum of the monomial matrices over the support. -/
theorem polarMatrix_eq_sum_monoMatrix (D : DiagPhase n m) :
    polarMatrix D = ∑ d ∈ D.support, monoMatrix d (D.coeff d) := by
  classical
  ext i j
  rw [Matrix.sum_apply]
  by_cases h : i = j
  · subst h
    rw [polarMatrix_apply_self]
    simp only [monoMatrix, Matrix.of_apply, if_true]
    rw [Finset.sum_ite_eq' D.support (Finsupp.single i 1)]
    by_cases hmem : Finsupp.single i 1 ∈ D.support
    · rw [if_pos hmem]
    · rw [if_neg hmem, MvPolynomial.notMem_support_iff.mp hmem, mul_zero, if_pos rfl]
  · rw [polarMatrix_apply_of_ne _ h]
    simp only [monoMatrix, Matrix.of_apply, if_neg h]
    rw [Finset.sum_ite_eq' D.support (Finsupp.single i 1 + Finsupp.single j 1)]
    by_cases hmem : Finsupp.single i 1 + Finsupp.single j 1 ∈ D.support
    · rw [if_pos hmem]
    · rw [if_neg hmem, MvPolynomial.notMem_support_iff.mp hmem, if_pos rfl]

/-! ## The coefficient arithmetic at level two -/

/-- At level two a degree-one coefficient has `4c = 0`. -/
theorem four_mul_eq_zero_of_effLevelMonom_single_le_two {c : ZMod (2 ^ m)} {j : Fin n}
    (hc : c ≠ 0) (h : effLevelMonom m c (Finsupp.single j 1) ≤ 2) : 4 * c = 0 := by
  unfold effLevelMonom at h
  rw [Finsupp.sum_single_index (by rfl)] at h
  have hv : m - 2 ≤ twoAdicVal c := by omega
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · haveI : Subsingleton (ZMod (2 ^ 0)) := by
        rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    · rw [show (4 : ZMod (2 ^ 1)) = 0 by decide, zero_mul]
  · have hdvd : 2 ^ (m - 2) ∣ c.val := (pow_dvd_val_iff hc (m - 2)).mpr hv
    obtain ⟨t, ht⟩ := hdvd
    have hc' : c = ((c.val : ℕ) : ZMod (2 ^ m)) := (ZMod.natCast_zmod_val c).symm
    have h4 : (4 : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) = 0 := by
      have : (4 : ZMod (2 ^ m)) * ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
          = ((2 ^ m : ℕ) : ZMod (2 ^ m)) := by
        rw [show (4 : ZMod (2 ^ m)) = ((2 ^ 2 : ℕ) : ZMod (2 ^ m)) by norm_num, ← Nat.cast_mul,
          ← pow_add, Nat.add_sub_cancel' hm]
      rw [this, ZMod.natCast_self]
    rw [hc', ht, Nat.cast_mul, ← mul_assoc, h4, zero_mul]

/-- At level two a degree-two coefficient is the top bit. -/
theorem eq_two_pow_pred_of_effLevelMonom_le_two {c : ZMod (2 ^ m)} {d : Fin n →₀ ℕ}
    (hc : c ≠ 0) (hd : d.sum (fun _ e => e) = 2) (h : effLevelMonom m c d ≤ 2) :
    c = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
  unfold effLevelMonom at h
  rw [hd] at h
  exact eq_two_pow_pred_of_twoAdicVal hc (by omega)

/-! ## Evaluation of the four shapes -/

theorem eval_monomial_zero (c : ZMod (2 ^ m)) (w : Fin n → ZMod 2) :
    DiagPhase.eval (monomial 0 c : DiagPhase n m) w = c := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_monomial, Finsupp.prod_zero_index, mul_one]

theorem eval_monomial_single (c : ZMod (2 ^ m)) (j : Fin n) (w : Fin n → ZMod 2) :
    DiagPhase.eval (monomial (Finsupp.single j 1) c : DiagPhase n m) w =
      c * ((w j).val : ZMod (2 ^ m)) := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp), pow_one]
  rfl

theorem eval_monomial_single_two (c : ZMod (2 ^ m)) (j : Fin n) (w : Fin n → ZMod 2) :
    DiagPhase.eval (monomial (Finsupp.single j 2) c : DiagPhase n m) w =
      c * ((w j).val : ZMod (2 ^ m)) := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_monomial, Finsupp.prod_single_index (by simp)]
  change c * ((((w j).val : ℕ) : ZMod (2 ^ m)) ^ 2) = _
  rw [val_sq_bit]

theorem eval_monomial_pair (c : ZMod (2 ^ m)) {j k : Fin n} (hjk : j ≠ k) (w : Fin n → ZMod 2) :
    DiagPhase.eval (monomial (Finsupp.single j 1 + Finsupp.single k 1) c : DiagPhase n m) w =
      c * (((w j).val : ZMod (2 ^ m)) * ((w k).val : ZMod (2 ^ m))) := by
  have _ := hjk
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (by simp),
    Finsupp.prod_single_index (by simp), pow_one, pow_one]
  rfl

/-! ## The law for one monomial -/

theorem polarLaw_monomial {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)} (hc : c ≠ 0)
    (h : effLevelMonom m c d ≤ 2) :
    PolarLaw (fun w => DiagPhase.eval (monomial d c : DiagPhase n m) w) (monoMatrix d c) := by
  have hdsum : d.sum (fun _ e => e) ≤ 2 := by
    unfold effLevelMonom at h; omega
  have hz : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := two_pow_pred_mul_two
  rcases exponent_cases_two hdsum with h0 | ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, k, hjk, hjk'⟩
  · subst h0
    intro v w
    simp only [eval_monomial_zero, sub_self, zero_add, monoMatrix_zero, topPairing_zero]
  · subst hj
    have h4 := four_mul_eq_zero_of_effLevelMonom_single_le_two hc h
    intro v w
    simp only [eval_monomial_single, monoMatrix_single, Pi.add_apply, val_add_bits,
      Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero]
    by_cases h20 : 2 * c = 0
    · rw [if_pos h20, topPairing_zero]
      linear_combination (-(((w j).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m)))) * h20
    · rw [if_neg h20, topPairing_single_self]
      rcases two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero h4 with h2 | h2
      · exact absurd h2 h20
      · linear_combination (-(((w j).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m)))) * h2
          + (-(((v j).val : ZMod (2 ^ m)) * ((w j).val : ZMod (2 ^ m)))) * hz
  · subst hj
    intro v w
    simp only [eval_monomial_single_two, monoMatrix_single_two, topPairing_zero, Pi.add_apply,
      val_add_bits, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero]
    have hc2 : c = (2 : ZMod (2 ^ m)) ^ (m - 1) :=
      eq_two_pow_pred_of_effLevelMonom_le_two hc (by rw [Finsupp.sum_single_index (by rfl)]) h
    subst hc2
    linear_combination (-(((w j).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m)))) * hz
  · subst hjk'
    intro v w
    have hc2 : c = (2 : ZMod (2 ^ m)) ^ (m - 1) :=
      eq_two_pow_pred_of_effLevelMonom_le_two hc (by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index (by rfl), Finsupp.sum_single_index (by rfl)]) h
    simp only [eval_monomial_pair _ hjk, monoMatrix_pair _ hjk, if_neg hc,
      topPairing_single_pair hjk, Pi.add_apply, val_add_bits, Pi.zero_apply, ZMod.val_zero,
      Nat.cast_zero, mul_zero, sub_zero]
    subst hc2
    linear_combination
      (-(((w j).val : ZMod (2 ^ m)) * ((w k).val : ZMod (2 ^ m)) * ((v k).val : ZMod (2 ^ m)))
        - ((v j).val : ZMod (2 ^ m)) * ((w k).val : ZMod (2 ^ m)) * ((v k).val : ZMod (2 ^ m))
        - ((w j).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m)) * ((w k).val : ZMod (2 ^ m))
        - ((w j).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m)) * ((v k).val : ZMod (2 ^ m))
        + 2 * ((w j).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m)) * ((w k).val : ZMod (2 ^ m))
          * ((v k).val : ZMod (2 ^ m))) * hz

/-! ## The law -/

/-- The exponent is the sum of its monomials, as functions on words. -/
theorem eval_eq_sum_support (D : DiagPhase n m) :
    (fun w => DiagPhase.eval D w) =
      ∑ d ∈ D.support, fun w => DiagPhase.eval (monomial d (D.coeff d) : DiagPhase n m) w := by
  funext w
  rw [Finset.sum_apply]
  conv_lhs => rw [D.as_sum]
  unfold DiagPhase.eval
  rw [map_sum]

/-- **The polarization law.** -/
theorem eval_add_sub_eval_eq_of_effectiveLevel_le_two (D : DiagPhase n m)
    (hD : effectiveLevel D ≤ 2) (v w : Fin n → ZMod 2) :
    DiagPhase.eval D (w + v) - DiagPhase.eval D w =
      (DiagPhase.eval D v - DiagPhase.eval D 0) +
        (2 : ZMod (2 ^ m)) ^ (m - 1) * (((polarMatrix D *ᵥ v ⬝ᵥ w).val : ℕ) : ZMod (2 ^ m)) := by
  have hlaw : PolarLaw (fun w => DiagPhase.eval D w) (polarMatrix D) := by
    rw [eval_eq_sum_support, polarMatrix_eq_sum_monoMatrix]
    refine PolarLaw.sum _ _ _ fun d hd => ?_
    have hc : D.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hlev : effLevelMonom m (D.coeff d) d ≤ 2 :=
      le_trans (Finset.le_sup (f := fun e => effLevelMonom m (D.coeff e) e) hd) hD
    exact polarLaw_monomial hc hlev
  have := hlaw v w
  unfold topPairing at this
  exact this

/-! ## The datum forms -/

/-- **The shift datum** of a function by a matrix: along every `v ∈ V` the shift is a constant
plus the top bit times the pairing of the row `M v` with the word. The frame's `DiagShiftDatum`
is this predicate with the one-bit shear's row. -/
def IsShiftDatum (f : (Fin n → ZMod 2) → ZMod (2 ^ m)) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  ∀ v ∈ V, ∃ c : ZMod (2 ^ m), ∀ w, f (w + v) - f w =
    c + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((M *ᵥ v ⬝ᵥ w).val : ℕ) : ZMod (2 ^ m))

theorem IsShiftDatum.mono {f : (Fin n → ZMod 2) → ZMod (2 ^ m)}
    {M : Matrix (Fin n) (Fin n) (ZMod 2)} {V V' : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hV : V ≤ V') (h : IsShiftDatum f M V') : IsShiftDatum f M V :=
  fun v hv => h v (hV hv)

/-- **The datum is additive**: functions add, matrices add. -/
theorem IsShiftDatum.add {f g : (Fin n → ZMod 2) → ZMod (2 ^ m)}
    {M N : Matrix (Fin n) (Fin n) (ZMod 2)} {V : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hf : IsShiftDatum f M V) (hg : IsShiftDatum g N V) :
    IsShiftDatum (fun w => f w + g w) (M + N) V := by
  intro v hv
  obtain ⟨c, hc⟩ := hf v hv
  obtain ⟨c', hc'⟩ := hg v hv
  refine ⟨c + c', fun w => ?_⟩
  rw [Matrix.add_mulVec, add_dotProduct, two_pow_pred_mul_val_add]
  linear_combination hc w + hc' w

/-- **The datum for the class**: every level-two exponent carries the shift datum of its polar
matrix, on every subspace. -/
theorem isShiftDatum_polarMatrix_of_effectiveLevel_le_two (D : DiagPhase n m)
    (hD : effectiveLevel D ≤ 2) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    IsShiftDatum (DiagPhase.eval D) (polarMatrix D) V :=
  fun v _ => ⟨DiagPhase.eval D v - DiagPhase.eval D 0,
    fun w => eval_add_sub_eval_eq_of_effectiveLevel_le_two D hD v w⟩

/-- The constant of a datum is forced: it is the shift at the zero word. -/
theorem const_eq_of_shift {f : (Fin n → ZMod 2) → ZMod (2 ^ m)}
    {M : Matrix (Fin n) (Fin n) (ZMod 2)} {v : Fin n → ZMod 2} {c : ZMod (2 ^ m)}
    (h : ∀ w, f (w + v) - f w =
      c + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((M *ᵥ v ⬝ᵥ w).val : ℕ) : ZMod (2 ^ m))) :
    c = f v - f 0 := by
  have h0 := h 0
  rw [zero_add, dotProduct_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at h0
  exact h0.symm

/-- **The half-diagonal identity**: twice the constant is the top bit times the polar form's
diagonal, so the constant is a `ℤ/4` refinement of the polar form. -/
theorem two_mul_eval_sub_eval_zero (D : DiagPhase n m) (hD : effectiveLevel D ≤ 2)
    (v : Fin n → ZMod 2) :
    2 * (DiagPhase.eval D v - DiagPhase.eval D 0) =
      (2 : ZMod (2 ^ m)) ^ (m - 1) * (((polarMatrix D *ᵥ v ⬝ᵥ v).val : ℕ) : ZMod (2 ^ m)) := by
  have h := eval_add_sub_eval_eq_of_effectiveLevel_le_two D hD v v
  have hvv : v + v = 0 := funext fun i => CharTwo.add_self_eq_zero (v i)
  rw [hvv] at h
  have hz : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := two_pow_pred_mul_two
  linear_combination (-1 : ZMod (2 ^ m)) * h
    - (((polarMatrix D *ᵥ v ⬝ᵥ v).val : ℕ) : ZMod (2 ^ m)) * hz

/-! ## Uniqueness and symmetry -/

/-- At positive precision the top bit separates the two bits. -/
theorem bit_eq_of_two_pow_pred_mul_val_eq {m : ℕ} (hm : 1 ≤ m) {s t : ZMod 2}
    (h : (2 : ZMod (2 ^ m)) ^ (m - 1) * ((s.val : ℕ) : ZMod (2 ^ m)) =
      (2 : ZMod (2 ^ m)) ^ (m - 1) * ((t.val : ℕ) : ZMod (2 ^ m))) : s = t := by
  have hne := two_pow_pred_ne_zero hm
  rcases zmod_two_cases s with hs | hs <;> rcases zmod_two_cases t with ht | ht <;>
    subst hs <;> subst ht
  · rfl
  · exfalso
    simp only [zmod_two_val_zero, zmod_two_val_one, Nat.cast_zero, Nat.cast_one, mul_zero,
      mul_one] at h
    exact hne h.symm
  · exfalso
    simp only [zmod_two_val_zero, zmod_two_val_one, Nat.cast_zero, Nat.cast_one, mul_zero,
      mul_one] at h
    exact hne h
  · rfl

/-- A datum on `V` makes the pairing symmetric on `V`: the second difference is symmetric in its
two directions. -/
theorem symm_on_of_isShiftDatum {m : ℕ} (hm : 1 ≤ m) {f : (Fin n → ZMod 2) → ZMod (2 ^ m)}
    {M : Matrix (Fin n) (Fin n) (ZMod 2)} {V : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : IsShiftDatum f M V) : ∀ u ∈ V, ∀ v ∈ V, M *ᵥ u ⬝ᵥ v = M *ᵥ v ⬝ᵥ u := by
  intro u hu v hv
  obtain ⟨cu, hcu⟩ := h u hu
  obtain ⟨cv, hcv⟩ := h v hv
  have hu0 := const_eq_of_shift hcu
  have hv0 := const_eq_of_shift hcv
  have h1 := hcu v
  have h2 := hcv u
  rw [hu0] at h1
  rw [hv0] at h2
  rw [add_comm v u] at h1
  refine bit_eq_of_two_pow_pred_mul_val_eq hm ?_
  linear_combination h2 - h1

/-- **The matrix is forced by a datum at `⊤`** at positive precision. -/
theorem eq_of_isShiftDatum_top {m : ℕ} (hm : 1 ≤ m) {f : (Fin n → ZMod 2) → ZMod (2 ^ m)}
    {M M' : Matrix (Fin n) (Fin n) (ZMod 2)} (h : IsShiftDatum f M ⊤)
    (h' : IsShiftDatum f M' ⊤) : M = M' := by
  ext i j
  obtain ⟨c, hc⟩ := h (Pi.single j 1) Submodule.mem_top
  obtain ⟨c', hc'⟩ := h' (Pi.single j 1) Submodule.mem_top
  have h0 := const_eq_of_shift hc
  have h0' := const_eq_of_shift hc'
  have h1 := hc (Pi.single i 1)
  have h2 := hc' (Pi.single i 1)
  rw [h0] at h1
  rw [h0'] at h2
  have h3 : (2 : ZMod (2 ^ m)) ^ (m - 1) * (((M *ᵥ Pi.single j 1 ⬝ᵥ Pi.single i 1).val : ℕ) :
      ZMod (2 ^ m)) = (2 : ZMod (2 ^ m)) ^ (m - 1) *
        (((M' *ᵥ Pi.single j 1 ⬝ᵥ Pi.single i 1).val : ℕ) : ZMod (2 ^ m)) := by
    linear_combination h2 - h1
  have h4 := bit_eq_of_two_pow_pred_mul_val_eq hm h3
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, dotProduct_single, dotProduct_single,
    mul_one, mul_one] at h4
  exact h4

/-! ## The normal form -/

theorem eval_sub_C (D : DiagPhase n m) (c : ZMod (2 ^ m)) (w : Fin n → ZMod 2) :
    DiagPhase.eval (D - MvPolynomial.C c) w = DiagPhase.eval D w - c := by
  unfold DiagPhase.eval
  rw [map_sub, MvPolynomial.eval_C]

/-- The normal form of the constant-free part has the coefficients of the normal form away
from the constant. -/
theorem coeff_boolReduce_sub_C (D : DiagPhase n m) (c : ZMod (2 ^ m)) {e : Fin n →₀ ℕ}
    (he : e ≠ 0) :
    (boolReduce (D - MvPolynomial.C c)).coeff e = (boolReduce D).coeff e := by
  classical
  rw [coeff_boolReduce, coeff_boolReduce]
  have hset : (D - MvPolynomial.C c).support.filter (fun d => boolShadow d = e) =
      D.support.filter (fun d => boolShadow d = e) := by
    ext d
    simp only [Finset.mem_filter, MvPolynomial.mem_support_iff, coeff_sub, coeff_C]
    constructor
    · rintro ⟨hne, hsh⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [boolShadow_zero] at hsh
        exact he hsh.symm
      rw [if_neg (Ne.symm hd0), sub_zero] at hne
      exact ⟨hne, hsh⟩
    · rintro ⟨hne, hsh⟩
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [boolShadow_zero] at hsh
        exact he hsh.symm
      refine ⟨?_, hsh⟩
      rw [if_neg (Ne.symm hd0), sub_zero]
      exact hne
  rw [hset]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [Finset.mem_filter, boolShadow_zero] at hd
    exact he hd.2.symm
  rw [coeff_sub, coeff_C, if_neg (Ne.symm hd0), sub_zero]

theorem polarMatrix_boolReduce_sub_C (D : DiagPhase n m) (c : ZMod (2 ^ m)) :
    polarMatrix (boolReduce (D - MvPolynomial.C c)) = polarMatrix (boolReduce D) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [polarMatrix_apply_self, polarMatrix_apply_self,
      coeff_boolReduce_sub_C _ _ (Finsupp.single_ne_zero.mpr one_ne_zero)]
  · rw [polarMatrix_apply_of_ne _ h, polarMatrix_apply_of_ne _ h,
      coeff_boolReduce_sub_C _ _ (Ne.symm (zero_ne_single_add_single h))]

/-- **The datum on the normal form.** Under the extended level (the level of the normal form of
the constant-free part) every exponent carries the shift datum of the polar matrix of its normal
form: the reading the class rule on the carrier uses. -/
theorem isShiftDatum_polarMatrix_boolReduce_of_levelExt_le_two (D : DiagPhase n m)
    (hD : FTQCLib.Frame.levelExt D ≤ 2) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    IsShiftDatum (DiagPhase.eval D) (polarMatrix (boolReduce D)) V := by
  intro v hv
  have hD' : effectiveLevel (boolReduce (D - MvPolynomial.C (D.coeff 0))) ≤ 2 := hD
  obtain ⟨c, hc⟩ := isShiftDatum_polarMatrix_of_effectiveLevel_le_two _ hD' V v hv
  refine ⟨c, fun w => ?_⟩
  have h := hc w
  rw [boolReduce_eval_eq, boolReduce_eval_eq, eval_sub_C, eval_sub_C,
    polarMatrix_boolReduce_sub_C] at h
  linear_combination h

/-! ## The instances -/

theorem sGate_eq_monomial (m : ℕ) (i : Fin n) :
    sGate m i = monomial (Finsupp.single i 1) ((2 : ZMod (2 ^ m)) ^ (m - 2)) := by
  unfold sGate
  rw [MvPolynomial.C_mul_X_eq_monomial]

theorem czGate_eq_monomial (m : ℕ) (i j : Fin n) :
    czGate m i j =
      monomial (Finsupp.single i 1 + Finsupp.single j 1) ((2 : ZMod (2 ^ m)) ^ (m - 1)) := by
  unfold czGate
  rw [show (MvPolynomial.X i : DiagPhase n m) = monomial (Finsupp.single i 1) 1 from rfl,
    show (MvPolynomial.X j : DiagPhase n m) = monomial (Finsupp.single j 1) 1 from rfl,
    monomial_mul, mul_one, MvPolynomial.C_mul_monomial, mul_one]

theorem coeff_single_sGate (m : ℕ) (i j : Fin n) :
    (sGate m i).coeff (Finsupp.single j 1) =
      if i = j then (2 : ZMod (2 ^ m)) ^ (m - 2) else 0 := by
  rw [sGate_eq_monomial, coeff_monomial]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (fun h' => h ((Finsupp.single_left_inj one_ne_zero).mp h')), if_neg h]

theorem coeff_pair_sGate (m : ℕ) (i : Fin n) {a b : Fin n} (hab : a ≠ b) :
    (sGate m i).coeff (Finsupp.single a 1 + Finsupp.single b 1) = 0 := by
  rw [sGate_eq_monomial, coeff_monomial, if_neg (single_ne_single_add_single hab)]

/-- The polar matrix of `S` at precision at least two: the diagonal unit at its bit. -/
theorem polarMatrix_sGate {m : ℕ} (hm : 2 ≤ m) (i : Fin n) :
    polarMatrix (sGate m i) = Matrix.single i i (1 : ZMod 2) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [polarMatrix_apply_self, coeff_single_sGate]
    by_cases hia : i = a
    · subst hia
      rw [if_pos rfl, Matrix.single_apply_same, if_neg]
      rw [show (2 : ZMod (2 ^ m)) * 2 ^ (m - 2) = 2 ^ (m - 1) by
        rw [← pow_succ']; congr 1; omega]
      exact two_pow_pred_ne_zero (by omega)
    · rw [if_neg hia, mul_zero, if_pos rfl, Matrix.single_apply, if_neg (fun h => hia h.1)]
  · rw [polarMatrix_apply_of_ne _ hab, coeff_pair_sGate _ _ hab, if_pos rfl, Matrix.single_apply,
      if_neg (fun h => hab (h.1.symm.trans h.2))]

/-- At precision one the `S` exponent is the `Z` exponent and its polar matrix vanishes. -/
theorem polarMatrix_sGate_one (i : Fin n) : polarMatrix (sGate 1 i) = 0 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [polarMatrix_apply_self, coeff_single_sGate, Matrix.zero_apply]
    by_cases hia : i = a
    · rw [if_pos hia, if_pos (by decide)]
    · rw [if_neg hia, mul_zero, if_pos rfl]
  · rw [polarMatrix_apply_of_ne _ hab, coeff_pair_sGate _ _ hab, if_pos rfl, Matrix.zero_apply]

/-- The polar matrix of `CZ` on distinct bits: the two off-diagonal units. -/
theorem polarMatrix_czGate {m : ℕ} (hm : 1 ≤ m) {i j : Fin n} (hij : i ≠ j) :
    polarMatrix (czGate m i j) = Matrix.single i j (1 : ZMod 2) + Matrix.single j i 1 := by
  rw [czGate_eq_monomial]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [polarMatrix_apply_self, coeff_monomial, if_neg (Ne.symm (single_ne_single_add_single hij)),
      mul_zero, if_pos rfl, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
      if_neg (fun h => hij (h.1.trans h.2.symm)), if_neg (fun h => hij (h.2.trans h.1.symm)),
      add_zero]
  · rw [polarMatrix_apply_of_ne _ hab, coeff_monomial]
    by_cases hp : Finsupp.single i 1 + Finsupp.single j 1 = Finsupp.single a 1 + Finsupp.single b 1
    · rw [if_pos hp, if_neg (two_pow_pred_ne_zero hm)]
      rcases (single_add_single_eq_iff hij).mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [Matrix.add_apply, Matrix.single_apply_same, Matrix.single_apply,
          if_neg (fun h => hab h.2), add_zero]
      · rw [Matrix.add_apply, Matrix.single_apply, if_neg (fun h => hab h.2),
          Matrix.single_apply_same, zero_add]
    · rw [if_neg hp, if_pos rfl, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
        if_neg (fun h => hp ((single_add_single_eq_iff hij).mpr (Or.inl ⟨h.1.symm, h.2.symm⟩))),
        if_neg (fun h => hp ((single_add_single_eq_iff hij).mpr (Or.inr ⟨h.1.symm, h.2.symm⟩))),
        add_zero]

/-- The square `X_i²` (the `Z` exponent) has the zero polar matrix. -/
theorem polarMatrix_czGate_self (m : ℕ) (i : Fin n) : polarMatrix (czGate m i i) = 0 := by
  rw [czGate_eq_monomial, ← Finsupp.single_add, show (1 + 1 : ℕ) = 2 from rfl]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [polarMatrix_apply_self, coeff_monomial, if_neg single_two_ne_single, mul_zero, if_pos rfl,
      Matrix.zero_apply]
  · rw [polarMatrix_apply_of_ne _ hab, coeff_monomial, if_neg (single_two_ne_single_add_single hab),
      if_pos rfl, Matrix.zero_apply]

/-! ## The levels of the instances, at every precision -/

theorem effectiveLevel_sGate_le_two (m : ℕ) (i : Fin n) : effectiveLevel (sGate m i) ≤ 2 := by
  rw [sGate_eq_monomial]
  refine (effectiveLevel_monomial_le _ _).trans ?_
  unfold effLevelMonom
  rw [Finsupp.sum_single_index (by rfl), twoAdicVal_pow_two]
  omega

theorem effectiveLevel_czGate_le_two (m : ℕ) (i j : Fin n) :
    effectiveLevel (czGate m i j) ≤ 2 := by
  rw [czGate_eq_monomial]
  refine (effectiveLevel_monomial_le _ _).trans ?_
  unfold effLevelMonom
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index (by rfl),
    Finsupp.sum_single_index (by rfl), twoAdicVal_pow_two]
  omega

theorem coeff_zero_sGate (m : ℕ) (i : Fin n) : (sGate m i).coeff 0 = 0 := by
  rw [sGate_eq_monomial, coeff_monomial, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]

theorem coeff_zero_czGate (m : ℕ) (i j : Fin n) : (czGate m i j).coeff 0 = 0 := by
  rw [czGate_eq_monomial, coeff_monomial, if_neg]
  intro h
  have := congrArg (fun d : Fin n →₀ ℕ => d i) h
  simp only [Finsupp.add_apply, Finsupp.single_apply, if_true, Finsupp.coe_zero, Pi.zero_apply]
    at this
  split_ifs at this

theorem levelExt_sGate_le_two (m : ℕ) (i : Fin n) : FTQCLib.Frame.levelExt (sGate m i) ≤ 2 := by
  refine (FTQCLib.Frame.levelExt_le_effectiveLevel_sub_C _).trans ?_
  rw [coeff_zero_sGate, MvPolynomial.C_0, sub_zero]
  exact effectiveLevel_sGate_le_two m i

theorem levelExt_czGate_le_two (m : ℕ) (i j : Fin n) : FTQCLib.Frame.levelExt (czGate m i j) ≤ 2 := by
  refine (FTQCLib.Frame.levelExt_le_effectiveLevel_sub_C _).trans ?_
  rw [coeff_zero_czGate, MvPolynomial.C_0, sub_zero]
  exact effectiveLevel_czGate_le_two m i j

/-! ## The instances are their own normal forms -/

/-- `S` is multilinear. -/
theorem isMultilinear_sGate (m : ℕ) (i : Fin n) : IsMultilinear (sGate m i) := by
  intro d hd k
  rw [sGate_eq_monomial] at hd
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd), Finsupp.single_apply]
  split_ifs <;> omega

/-- `CZ` is multilinear (`i ≠ j`). -/
theorem isMultilinear_czGate (m : ℕ) {i j : Fin n} (hij : i ≠ j) :
    IsMultilinear (czGate m i j) := by
  intro d hd k
  rw [czGate_eq_monomial] at hd
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd), Finsupp.add_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- `S` is its own Boolean normal form. -/
theorem boolReduce_sGate (m : ℕ) (i : Fin n) : boolReduce (sGate m i) = sGate m i :=
  boolReduce_eq_self_of_isMultilinear (isMultilinear_sGate m i)

/-- `CZ` is its own Boolean normal form (`i ≠ j`). -/
theorem boolReduce_czGate (m : ℕ) {i j : Fin n} (hij : i ≠ j) :
    boolReduce (czGate m i j) = czGate m i j :=
  boolReduce_eq_self_of_isMultilinear (isMultilinear_czGate m hij)

end FTQCLib.Hierarchy.DiagPhase

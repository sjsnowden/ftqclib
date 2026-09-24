/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Bridge.G1Verify
import FTQCLib.Frame.MobiusProductTower

set_option linter.style.longLine false

/-!
# The converse degree bound — `effectiveLevel` is exact

`eval_isPolyDegLE_effectiveLevel` proves the soundness half: every multilinear diagonal phase has
nonclassical degree `≤ effectiveLevel`. This file proves the **witness half** and combines them into
exactness: for multilinear `P` with **no constant term**,

* `exists_iteratedFwdDiff_length_effectiveLevel_ne_zero` — an explicit `effectiveLevel P`-fold iterated
  difference that does **not** vanish. The witness: take the monomial `d₀` achieving the sup, with
  coefficient `c` and variable set `S`; difference `k + 1 = (m − 1 − v(c)) + 1` times in one variable of
  `S` and once in each remaining variable. The repeats each multiply by `−2`
  (`iteratedFwdDiff_replicate_two_torsion`), pumping the 2-adic valuation one rung per repeat (the
  tower's staircase arithmetic); the `S`-part extracts the coefficient (`mobiusCoeff` = the ANF
  coefficient, via the ring-general Möbius expansion). The value at `0` is `(−2)^k • c`, of valuation
  exactly `m − 1 < m` — nonzero.
* `eval_isPolyDegLE_iff` — **exactness**: `IsPolyDegLE d (eval P) ↔ effectiveLevel P ≤ d`. The frame's
  grade IS the coordinate-free difference-depth, not just a ceiling on it.

The `P.coeff 0 = 0` hypothesis is necessary, not cosmetic: the constant monomial contributes
`m − 1 − v(c₀)` to `effectiveLevel` but nothing to any difference (differences kill constants), so
tightness genuinely fails for constant-dominated phases (e.g. `P = 1` over `ℤ/8` has `effectiveLevel 2`
but difference-depth `0`). Dropping the constant term changes no difference of `eval P`.
-/

namespace FTQCLib.Bridge

open FTQCLib.Hierarchy FTQCLib.Hierarchy.BooleanMobius FTQCLib.Hierarchy.DiagPhase ECCLib
open FTQCLib.Frame.MobiusTower

variable {n m : ℕ}

/-- A multilinear polynomial's monomials are determined by their variable sets. -/
lemma multilinear_eq_of_support_eq {P : DiagPhase n m} (hP : DiagPhase.IsMultilinear P)
    {d d' : Fin n →₀ ℕ} (hd : d ∈ P.support) (hd' : d' ∈ P.support)
    (h : d.support = d'.support) : d = d' := by
  ext i
  by_cases hi : i ∈ d.support
  · have hi' : i ∈ d'.support := h ▸ hi
    have h1 : d i = 1 :=
      le_antisymm (hP d hd i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    have h2 : d' i = 1 :=
      le_antisymm (hP d' hd' i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi'))
    rw [h1, h2]
  · have hi' : i ∉ d'.support := h ▸ hi
    have h1 : d i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi
    have h2 : d' i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi'
    rw [h1, h2]

/-- A multilinear monomial's total degree is its variable count. -/
lemma multilinear_sum_eq_card {P : DiagPhase n m} (hP : DiagPhase.IsMultilinear P)
    {d : Fin n →₀ ℕ} (hd : d ∈ P.support) :
    d.sum (fun _ e => e) = d.support.card := by
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact le_antisymm (hP d hd i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- **A multilinear phase's eval is its Möbius expansion** with coefficients the polynomial's own:
`eval P = Σ_{d ∈ supp} c_d · monomChar (d.support)`. -/
lemma eval_eq_sum_monomChar (P : DiagPhase n m) (hP : DiagPhase.IsMultilinear P) :
    P.eval = ∑ d ∈ P.support,
      (fun v => P.coeff d * FTQCLib.Frame.MobiusTower.monomChar d.support v) := by
  funext v
  rw [Finset.sum_apply]
  show MvPolynomial.eval (liftBinary v) P = _
  rw [MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have h1 : d i = 1 :=
    le_antisymm (hP d hd i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  rw [h1, pow_one]
  rfl

/-- **The Möbius coefficient of a multilinear phase is the polynomial coefficient:**
`mobiusCoeff (d₀.support) (eval P) = P.coeff d₀` for `d₀ ∈ supp`. The frame's ANF layer reads off the
polynomial exactly. -/
lemma mobiusCoeff_eval_eq_coeff (P : DiagPhase n m) (hP : DiagPhase.IsMultilinear P)
    {d₀ : Fin n →₀ ℕ} (hd₀ : d₀ ∈ P.support) :
    mobiusCoeff d₀.support P.eval = P.coeff d₀ := by
  rw [eval_eq_sum_monomChar P hP, FTQCLib.Frame.MobiusTower.mobiusCoeff_sum]
  rw [Finset.sum_eq_single_of_mem d₀ hd₀ ?_]
  · rw [FTQCLib.Frame.MobiusTower.mobiusCoeff_const_mul,
      FTQCLib.Frame.MobiusTower.mobiusCoeff_monomChar, if_pos rfl, mul_one]
  · intro d hd hne'
    rw [FTQCLib.Frame.MobiusTower.mobiusCoeff_const_mul,
      FTQCLib.Frame.MobiusTower.mobiusCoeff_monomChar, if_neg, mul_zero]
    exact fun hsupp => hne' (multilinear_eq_of_support_eq hP hd hd₀ hsupp)

/-- **The pumped coefficient is nonzero:** `(−2)^{m−1−v(c)} • c ≠ 0` for `c ≠ 0` in `ZMod (2^m)` — the
repeats raise the valuation to exactly `m − 1 < m`, never to saturation. -/
lemma neg_two_pow_smul_ne_zero {c : ZMod (2 ^ m)} (hc : c ≠ 0) :
    ((-2 : ℤ) ^ (m - 1 - twoAdicVal c)) • c ≠ 0 := by
  intro h0
  have hm : 1 ≤ m := by
    by_contra hm'
    have hm0 : m = 0 := by omega
    subst hm0
    haveI : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact hc (Subsingleton.elim c 0)
  set k := m - 1 - twoAdicVal c with hk_def
  rw [neg_pow, mul_smul] at h0
  have h2 : ((2 : ℤ) ^ k) • c = 0 := by
    rcases Nat.even_or_odd k with he | ho
    · rwa [he.neg_one_pow, one_smul] at h0
    · rw [ho.neg_one_pow, neg_smul, one_smul] at h0
      exact neg_eq_zero.mp h0
  have h3 : (2 : ZMod (2 ^ m)) ^ k * c = 0 := by
    rw [zsmul_eq_mul] at h2
    push_cast at h2
    exact h2
  have hv := congrArg twoAdicVal h3
  rw [twoAdicVal_mul, twoAdicVal_pow_two, twoAdicVal_zero] at hv
  have hvc : twoAdicVal c < m := twoAdicVal_lt_of_ne_zero hc
  omega

/-- **The converse bound (the witness).** For multilinear `P` with no constant term, there is an
explicit `effectiveLevel P`-fold iterated difference of `eval P` that does not vanish: repeat one variable of the
sup-achieving monomial `(m − 1 − v(c)) + 1` times and take each remaining variable once. So the
nonclassical degree of `eval P` is `≥ effectiveLevel P`. -/
theorem exists_iteratedFwdDiff_length_effectiveLevel_ne_zero
    (P : DiagPhase n m) (hP : DiagPhase.IsMultilinear P) (hc0 : P.coeff 0 = 0) (hne : P ≠ 0) :
    ∃ ys : List (Fin n → ZMod 2),
      ys.length = DiagPhase.effectiveLevel P ∧ iteratedFwdDiff ys P.eval ≠ 0 := by
  classical
  have hsupp : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hne (MvPolynomial.support_eq_empty.mp h))
  obtain ⟨d₀, hd₀, hsup⟩ :=
    Finset.exists_mem_eq_sup P.support hsupp
      (fun d => DiagPhase.effLevelMonom m (P.coeff d) d)
  have hc : P.coeff d₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hd₀
  have hSne : d₀.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro hd0eq
    rw [hd0eq] at hc
    exact hc hc0
  obtain ⟨j, hj⟩ := hSne
  set k := m - 1 - twoAdicVal (P.coeff d₀) with hk_def
  have hejtor : (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)
      + (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) = 0 := by
    rw [← Pi.single_add, show (1 : ZMod 2) + 1 = 0 from by decide, Pi.single_zero]
  refine ⟨List.replicate (k + 1) (Pi.single j (1 : ZMod 2))
      ++ (d₀.support.erase j).toList.map (fun i => Pi.single i (1 : ZMod 2)), ?_, ?_⟩
  · rw [List.length_append, List.length_replicate, List.length_map, Finset.length_toList,
      Finset.card_erase_of_mem hj]
    have hsum := multilinear_sum_eq_card hP hd₀
    have hScard : 1 ≤ d₀.support.card := Finset.card_pos.mpr ⟨j, hj⟩
    have heL : DiagPhase.effectiveLevel P
        = DiagPhase.effLevelMonom m (P.coeff d₀) d₀ := hsup
    rw [heL]
    unfold DiagPhase.effLevelMonom
    omega
  · intro hzero
    have hrw : iteratedFwdDiff
        (List.replicate (k + 1) (Pi.single j (1 : ZMod 2))
          ++ (d₀.support.erase j).toList.map (fun i => Pi.single i (1 : ZMod 2))) P.eval
        = ((-2 : ℤ) ^ k) • funcDerivSubset d₀.support P.eval := by
      rw [iteratedFwdDiff_append, ← funcDerivSubset_eq_iteratedFwdDiff,
        iteratedFwdDiff_replicate_two_torsion hejtor, ← funcDerivG_eq_fwdDiff,
        ← funcDerivSubset_insert (Finset.notMem_erase j d₀.support),
        Finset.insert_erase hj]
    rw [hrw] at hzero
    have h0 := congrFun hzero 0
    rw [Pi.smul_apply, Pi.zero_apply] at h0
    have hmob : funcDerivSubset d₀.support P.eval 0 = P.coeff d₀ := by
      have hdef : mobiusCoeff d₀.support P.eval = funcDerivSubset d₀.support P.eval 0 := rfl
      rw [← hdef]
      exact mobiusCoeff_eval_eq_coeff P hP hd₀
    rw [hmob] at h0
    exact neg_two_pow_smul_ne_zero hc h0

/-- **Exactness — the frame's grade IS the difference-depth.** For multilinear `P` with no constant
term: `IsPolyDegLE d (eval P) ↔ effectiveLevel P ≤ d`. The `←` half is
`eval_isPolyDegLE_effectiveLevel` (soundness of the static analysis); the `→` half is the witness
(completeness). The nonclassical degree of `eval P` — the least `d` such that all `(d+1)`-fold
differences vanish — equals `effectiveLevel P` exactly. -/
theorem eval_isPolyDegLE_iff
    (P : DiagPhase n m) (hP : DiagPhase.IsMultilinear P) (hc0 : P.coeff 0 = 0) (hne : P ≠ 0)
    {d : ℕ} :
    IsPolyDegLE d P.eval ↔ DiagPhase.effectiveLevel P ≤ d := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨ys, hlen, hnz⟩ :=
      exists_iteratedFwdDiff_length_effectiveLevel_ne_zero P hP hc0 hne
    exact hnz (h.iteratedFwdDiff_eq_zero (by omega))
  · intro h
    exact (eval_isPolyDegLE_effectiveLevel P hP).mono h

/-- End-to-end check on the `T`-gate polynomial: `PT` has nonclassical degree exactly `3` — the iff
pins both `IsPolyDegLE 3` (the soundness half) and `¬ IsPolyDegLE 2` (the witness), matching the
direct computation `tCubic_thirdDiff = 4 ≠ 0`. -/
example : ¬ IsPolyDegLE 2 (DiagPhase.eval PT) := by
  intro h
  have hc0 : PT.coeff 0 = 0 := by
    rw [PT, MvPolynomial.coeff_monomial, if_neg (by simp)]
  have hne : PT ≠ 0 := by
    intro hcon
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 1)) hcon
    rw [PT, MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
    exact absurd hcoeff (by decide)
  have := (eval_isPolyDegLE_iff PT PT_multilinear hc0 hne).mp h
  rw [PT_effectiveLevel] at this
  omega

end FTQCLib.Bridge

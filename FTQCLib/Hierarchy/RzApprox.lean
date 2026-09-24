/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.RzHardness
import FTQCLib.Hierarchy.GatePolynomials
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.BitIndices

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # Dyadic approximation of `R_z(θ)` — the positive twin of `RzHardness`

The negative twin (`FTQCLib/Hierarchy/RzHardness.lean`, `rz_irrational_not_polyEncodable`) says: for irrational
`θ/π`, no phase polynomial `P : DiagPhase n m` realises `R_z(θ)` *exactly*. This file is its positive
complement: every `R_z(θ)` is *approximated* to any accuracy by a frame gate, and the cost of the
approximation is the frame's own level meter, logarithmically and sharply.

**Design decisions.**

* **The measure is the arc distance on the phase data**, stated frame-purely in `RzHardness`'s
  coordinate (`realPhase`), NOT the operator norm. The operator-norm form is a separate Hilbert-side
  certificate (`FTQCLib/Hilbert/RzApproxOperator.lean`; the exact bridge is `chord = 2·sin(arc/2)`,
  two-sided-linear by `Real.sin_le` / Jordan `Real.mul_le_sin`). The negative and positive results
  then quantify over the same objects and read as one dichotomy.
* **The witness is the anchored linear polynomial** `C c * X i` (constant term 0, so no global-phase
  freedom `φ`; `ProjectiveHierarchy` shows unanchored constants inflate the level meter). Global phase
  enters only as the periodicity integer `k`, exactly as the twin's statement keeps a `2πk` slack.
* **Encoding: explicit `∃ k : ℤ` on ℝ** (twin-consistent), with `abs_sub_round` the achievability engine
  and odd-integer midpoint arithmetic the sharpness engine.
* **Cost is the level, not the T-count** (level ≠ count). The `Θ(log 1/ε)` shape
  coincides with Ross–Selinger's T-count law but is a different currency; no T-count optimality is claimed.

**Results.**

* `rz_dyadic_approx` — achievability: for every `θ` and precision `m` there is a coefficient
  `c : ZMod (2^m)` whose gate `C c * X i` matches the `R_z(θ)` phase pattern to within the half-spacing
  `π/2^m` on every input (arc distance, anchored).
* `rz_approx_level_le` — cost: the witness has `level ≤ m`.
* `rz_dyadic_lower` — sharpness: the grid-midpoint target `θ = π/2^m` is at least the half-spacing `π/2^m`
  from EVERY precision-`m` gate's phase — so `π/2^m` is exactly the best precision-`m` accuracy, and the
  meter cannot be beaten. Two-sided with the achievability bound: precision `m` buys accuracy `π/2^m`, no
  more and no less.

An `FTQCLib/Hierarchy/` result, frame-pure (no `FTQCLib.Hilbert` import), axiom-clean. -/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial Real

variable {n : ℕ}

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- The phase pattern of the linear witness `C c * X i`: `2π·c.val/2^m` on the `v i = 1` branch, `0` on
the `v i = 0` branch — i.e. `(v i).val` times the dyadic angle `2π·c.val/2^m`. -/
theorem realPhase_linear (c : ZMod (2 ^ m)) (i : Fin n) (v : Fin n → ZMod 2) :
    realPhase (C c * X i) v = (v i).val * (2 * π * (c.val : ℝ) / 2 ^ m) := by
  have hev : (C c * X i : DiagPhase n m).eval v = c * ((v i).val : ZMod (2 ^ m)) := by
    unfold DiagPhase.eval
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    rfl
  rw [realPhase, hev]
  rcases zmod2_cases (v i) with h | h
  · rw [h]
    have e0 : ((0 : ZMod 2).val : ZMod (2 ^ m)) = 0 := by
      rw [show (0 : ZMod 2).val = 0 from by decide, Nat.cast_zero]
    rw [e0, mul_zero, ZMod.val_zero]
    simp
  · rw [h]
    have e1 : ((1 : ZMod 2).val : ZMod (2 ^ m)) = 1 := by
      rw [show (1 : ZMod 2).val = 1 from by decide, Nat.cast_one]
    have hv1 : ((1 : ZMod 2).val : ℝ) = 1 := by
      rw [show (1 : ZMod 2).val = 1 from by decide, Nat.cast_one]
    rw [e1, mul_one, hv1]; ring

/-! ## Achievability: the anchored dyadic witness is within the half-spacing -/

/-- **Achievability (arc distance, anchored).** For every angle `θ`, precision `m`, and qubit `i`, there is
a coefficient `c : ZMod (2^m)` such that the gate `C c * X i` matches the `R_z(θ)` phase pattern
`(v i).val · θ` to within `π/2^m` on every input `v`, in arc distance (the `∃ k` absorbs both the `ℤ/2^m`
reduction of `c` and the `2π`-periodicity of `θ`). No global-phase offset: the witness is anchored. -/
theorem rz_dyadic_approx (θ : ℝ) (i : Fin n) (m : ℕ) :
    ∃ c : ZMod (2 ^ m), ∀ v : Fin n → ZMod 2,
      ∃ k : ℤ, |realPhase (C c * X i) v - (v i).val * θ - 2 * π * k| ≤ π / 2 ^ m := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0:ℕ) < 2 ^ m).ne'⟩
  have hpi : (0:ℝ) < π := pi_pos
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hpowR : ((2:ℝ) ^ m) ≠ 0 := by positivity
  set r : ℤ := round (θ * 2 ^ m / (2 * π)) with hr
  set j : ℤ := r / 2 ^ m with hj
  refine ⟨(r : ZMod (2 ^ m)), fun v => ?_⟩
  rw [realPhase_linear]
  -- `c.val` differs from `r` by a multiple of `2^m`: `(c.val : ℝ) = r − 2^m·j`, `j = r/2^m`.
  have hval' : ((r : ZMod (2 ^ m)).val : ℝ) = (r : ℝ) - 2 ^ m * (j : ℝ) := by
    have hZ : ((r : ZMod (2 ^ m)).val : ℤ) = r - 2 ^ m * j := by
      have hv : ((r : ZMod (2 ^ m)).val : ℤ) = r % 2 ^ m := by
        have := ZMod.val_intCast (n := 2 ^ m) r; exact_mod_cast this
      have hd : 2 ^ m * (r / 2 ^ m) + r % 2 ^ m = r := Int.mul_ediv_add_emod r (2 ^ m)
      rw [hv, hj]; linarith
    have := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at this; linarith
  rcases zmod2_cases (v i) with h0 | h1
  · -- `v i = 0`: both sides 0.
    refine ⟨0, ?_⟩
    rw [h0]; simp; positivity
  · -- `v i = 1`: the dyadic angle `2π·c.val/2^m` is within `π/2^m` of `θ` after removing `2π·j`.
    refine ⟨-j, ?_⟩
    rw [h1]
    have hv1 : ((1 : ZMod 2).val : ℝ) = 1 := by
      rw [show (1 : ZMod 2).val = 1 from by decide, Nat.cast_one]
    have hkey : ((1 : ZMod 2).val : ℝ) * (2 * π * ((r : ZMod (2 ^ m)).val : ℝ) / 2 ^ m)
          - ((1 : ZMod 2).val : ℝ) * θ - 2 * π * ((-j : ℤ) : ℝ)
        = (2 * π / 2 ^ m) * ((r : ℝ) - θ * 2 ^ m / (2 * π)) := by
      rw [hv1, hval']; push_cast; field_simp; ring
    rw [hkey, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
    have hb := abs_sub_round (θ * 2 ^ m / (2 * π))
    rw [← hr] at hb
    calc 2 * π / 2 ^ m * |θ * 2 ^ m / (2 * π) - (r : ℝ)|
          ≤ 2 * π / 2 ^ m * (1 / 2) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = π / 2 ^ m := by ring

/-! ## Cost: the witness sits at level ≤ m -/

/-- **Cost.** The anchored witness `C c * X i` has Clifford-hierarchy level `≤ m` (`= m` when `c ≠ 0`,
`= m − 1` when `c = 0` = the identity gate). So accuracy `π/2^m` costs level `≤ m`. -/
theorem rz_approx_level_le (c : ZMod (2 ^ m)) (i : Fin n) (hm : 1 ≤ m) :
    (C c * X i : DiagPhase n m).level ≤ m := by
  haveI : Fact (1 < 2 ^ m) := ⟨Nat.one_lt_two_pow (by omega)⟩
  unfold DiagPhase.level
  have hdeg : (C c * X i : DiagPhase n m).totalDegree ≤ 1 := by
    calc (C c * X i : DiagPhase n m).totalDegree
          ≤ (C c : DiagPhase n m).totalDegree + (X i : DiagPhase n m).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = 0 + 1 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
      _ = 1 := by ring
  omega

/-! ## The composition form: the approximant IS a product of root-of-Z tower gates

Diagonal-gate composition is phase-polynomial addition, so "product of gates" reads as "sum of phase
polynomials". The approximant `C c * X i` decomposes as the sum over the set bits of `c` of the gates
`C (2^k) * X i` — and `C (2^k) * X i : DiagPhase n m` applies angle `2π·2^k/2^m = 2π/2^{m-k}`, i.e. it IS
the depth-`(m−k)` root-of-`Z` tower gate on qubit `i` (`rzGatePoly`'s family). So an arbitrary dyadic
rotation is literally the composition of the frame's discrete phase rotations, one per binary digit of the
angle — the constructive content of "arbitrary rotations by composition of discrete phase rotations". -/

/-- **Composition form.** The anchored approximant `C c * X i` is the sum (= gate composition) of the
tower-gate polynomials `C (2^k) * X i`, one for each set bit `k` of `c` (`Nat.bitIndices c.val` lists
those positions; `twoPowSum_bitIndices` is the binary expansion). One tower gate per binary digit. -/
theorem rz_approx_composition (c : ZMod (2 ^ m)) (i : Fin n) :
    (C c * X i : DiagPhase n m)
      = ∑ k ∈ c.val.bitIndices.toFinset, (C ((2 : ZMod (2 ^ m)) ^ k) * X i) := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0:ℕ) < 2 ^ m).ne'⟩
  have hnodup : c.val.bitIndices.Nodup := Nat.bitIndices_nodup
  have hc : c = ∑ k ∈ c.val.bitIndices.toFinset, (2 : ZMod (2 ^ m)) ^ k := by
    rw [List.sum_toFinset (fun k => (2 : ZMod (2 ^ m)) ^ k) hnodup]
    have hcast : (c.val.bitIndices.map (fun k => (2 : ZMod (2 ^ m)) ^ k)).sum
        = (((c.val.bitIndices.map (fun k => 2 ^ k)).sum : ℕ) : ZMod (2 ^ m)) := by
      rw [Nat.cast_list_sum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast, Nat.twoPowSum_bitIndices, ZMod.natCast_zmod_val]
  conv_lhs => rw [hc]
  rw [map_sum, Finset.sum_mul]

/-! ## Sharpness: the meter cannot be beaten -/

/-- **Sharpness.** The grid-midpoint target `θ = π/2^m` is at least the half-spacing `π/2^m` in arc
distance from EVERY precision-`m` phase value `2π·(P.eval v).val/2^m` on the `v i = 1` branch (the value is
a dyadic multiple of `2π/2^m`; the midpoint is exactly half a step from every one). With `rz_dyadic_approx`,
precision `m` buys accuracy exactly `π/2^m` — no precision-`m` gate does better. The bound is φ-invariant:
it runs on the dyadic value, and no global-phase offset can move a value off its grid. -/
theorem rz_dyadic_lower (m : ℕ) (a : ℤ) (k : ℤ) :
    |(π / 2 ^ m) - 2 * π * (a : ℝ) / 2 ^ m - 2 * π * k| ≥ π / 2 ^ m := by
  have hpowR : ((2:ℝ) ^ m) ≠ 0 := by positivity
  have hpi : (0:ℝ) < π := pi_pos
  have hfac : (π / 2 ^ m) - 2 * π * (a : ℝ) / 2 ^ m - 2 * π * k
      = (π / 2 ^ m) * ((1 : ℝ) - 2 * a - 2 ^ (m + 1) * k) := by
    have h2 : ((2:ℝ) ^ (m + 1)) = 2 * 2 ^ m := by rw [pow_succ]; ring
    rw [h2]; field_simp
  rw [hfac, abs_mul, abs_of_pos (by positivity)]
  have hodd : (1 : ℝ) ≤ |(1 : ℝ) - 2 * (a:ℝ) - 2 ^ (m + 1) * (k:ℝ)| := by
    have hzR : ((1 - 2 * a - 2 ^ (m + 1) * k : ℤ) : ℝ) = 1 - 2 * (a:ℝ) - 2 ^ (m + 1) * (k:ℝ) := by
      push_cast; ring
    have hne : (1 - 2 * a - 2 ^ (m + 1) * k : ℤ) ≠ 0 := by
      have hev : (2 : ℤ) ∣ (2 * a + 2 ^ (m + 1) * k) := by
        refine Dvd.dvd.add (Dvd.intro a rfl) ?_
        exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero m)) k
      omega
    have hint : (1:ℤ) ≤ |1 - 2 * a - 2 ^ (m + 1) * k| := Int.one_le_abs hne
    have hcast := (Int.cast_le (R := ℝ)).2 hint
    rw [Int.cast_abs, hzR] at hcast
    simpa using hcast
  rw [ge_iff_le]
  nlinarith [hodd, (show (0:ℝ) < π / 2 ^ m by positivity)]

end FTQCLib.Hierarchy.DiagPhase

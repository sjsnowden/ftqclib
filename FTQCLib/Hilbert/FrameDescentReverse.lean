/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.FrameDescent

/-! # Kernel frame — the descent characterization, reverse direction

The forward direction
(`level ≤ k ⟹ all (k+1)-fold differences vanish`) is `descent_forward`
(`FrameDescent.lean`). This file builds the **reverse** direction
(`all (k+1)-fold differences vanish ⟹ level ≤ k`) — the Aichinger–Moosbauer /
Clark–Schauz functional-degree *lower bound*:

* The hard content (the functional-degree lower bound: a level-`L`
  exponent admits a length-`L` iterated difference that is still nonzero) is
  **isolated behind the named `Prop` `SurvivingTopCoeffNonzero`**. A `Prop`
  hypothesis is not an axiom, so `descent_reverse` and `descent_characterization`
  land axiom-clean (`propext`/`Classical.choice`/`Quot.sound`) against it; the
  `Prop` is discharged in `FrameDescentReverseDischarge.lean`.
* Everything around the crux is proved unconditionally here: the `iterDiff`
  infrastructure (`iterDiff_append`, `iterDiff_isMultilinear`, `iterDiff_finsetSum`,
  the monomial decomposition), the lower-monomial annihilation
  (`iterDiff_monomial_eq_zero_of_effLevelMonom_lt`, reusing `descent_forward`),
  the top-monomial witness (`exists_top_monomial`), the single-coordinate
  reduction (`iterDiff_map_single`), and the function face (`iterDiff_eval_eq`).

The discharge in `FrameDescentReverseDischarge.lean` uses the `−2Δ` tower on a
monomial, a 2-adic nonzeroness lemma, and the leading-term non-cancellation.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

/-! ### `iterDiff` infrastructure -/

/-- **Append law.** Iterating over `ds₁ ++ ds₂` is iterating over `ds₁` then over
`ds₂` (foldl associativity). -/
lemma iterDiff_append {m : ℕ} (ds₁ ds₂ : List (Fin n → ZMod 2)) (P : DiagPhase n m) :
    iterDiff (ds₁ ++ ds₂) P = iterDiff ds₂ (iterDiff ds₁ P) := by
  unfold iterDiff
  rw [List.foldl_append]

/-- **Multilinearity is preserved by iterated differences.** -/
lemma iterDiff_isMultilinear {m : ℕ} {ds : List (Fin n → ZMod 2)} {P : DiagPhase n m}
    (h : DiagPhase.IsMultilinear P) : DiagPhase.IsMultilinear (iterDiff ds P) := by
  induction ds generalizing P with
  | nil => exact h
  | cons d rest ih =>
    rw [iterDiff_cons]
    exact ih (DiagPhase.shiftBy_isMultilinear d h)

/-- **Additivity over finite sums.** `iterDiff` distributes over a finite sum of
exponents, by folding `shiftBy_finsetSum` along the direction list. -/
lemma iterDiff_finsetSum {m : ℕ} {α : Type*} (ds : List (Fin n → ZMod 2))
    (t : Finset α) (f : α → DiagPhase n m) :
    iterDiff ds (∑ i ∈ t, f i) = ∑ i ∈ t, iterDiff ds (f i) := by
  induction ds generalizing f with
  | nil => simp only [iterDiff_nil]
  | cons d rest ih =>
    rw [iterDiff_cons, DiagPhase.shiftBy_finsetSum, ih]
    simp only [iterDiff_cons]

/-- **Monomial decomposition.** The iterated difference of `P` is the sum, over
`P.support`, of the iterated differences of its monomials. -/
lemma iterDiff_eq_sum_over_support {m : ℕ} (ds : List (Fin n → ZMod 2))
    (P : DiagPhase n m) :
    iterDiff ds P = ∑ d ∈ P.support, iterDiff ds (MvPolynomial.monomial d (P.coeff d)) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [iterDiff_finsetSum]

/-- **Lower monomials die.** A squarefree monomial whose per-monomial effective
level is `< ds.length` is annihilated by the length-`ds.length` iterated
difference. For `c = 0` the monomial is zero; for `c ≠ 0` it is multilinear with
`effectiveLevel = DiagPhase.effLevelMonom m c d`, so `descent_forward` applies. -/
lemma iterDiff_monomial_eq_zero_of_effLevelMonom_lt {m : ℕ}
    {ds : List (Fin n → ZMod 2)} {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)}
    (hsq : ∀ i, d i ≤ 1) (h : DiagPhase.effLevelMonom m c d < ds.length) :
    iterDiff ds (MvPolynomial.monomial d c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, map_zero]; exact iterDiff_zero ds
  · have h_mul : DiagPhase.IsMultilinear (MvPolynomial.monomial d c : DiagPhase n m) :=
      DiagPhase.IsMultilinear.monomial d c hsq
    have h_eff_eq : DiagPhase.effectiveLevel (MvPolynomial.monomial d c : DiagPhase n m)
        = DiagPhase.effLevelMonom m c d := DiagPhase.effectiveLevel_monomial_eq hc
    rw [← h_eff_eq] at h
    exact descent_forward h_mul h

/-- **Single-coordinate reduction.** The iterated difference along single
coordinates `e_i = Pi.single i 1` is the iterated `shiftDeriv`. (Restricting the
difference directions to single coordinates is what makes the lower bound
tractable.) -/
lemma iterDiff_map_single {m : ℕ} (is : List (Fin n)) (P : DiagPhase n m) :
    iterDiff (is.map (fun i => Pi.single i 1)) P
      = is.foldl (fun Q i => DiagPhase.shiftDeriv i Q) P := by
  induction is generalizing P with
  | nil => rfl
  | cons i rest ih =>
    rw [List.map_cons, iterDiff_cons, List.foldl_cons,
      ← DiagPhase.shiftBy_single_eq_shiftDeriv, ih]

/-! ### The function face -/

/-- **Function reading.** The value function of the iterated difference is the
iterated `frameDiff` applied to `P.eval`. -/
lemma iterDiff_eval_eq {m : ℕ} (ds : List (Fin n → ZMod 2)) (P : DiagPhase n m) :
    (iterDiff ds P).eval = ds.foldl (fun g d => frameDiff d g) (P.eval) := by
  induction ds generalizing P with
  | nil => simp only [iterDiff_nil, List.foldl_nil]
  | cons d ds' ih =>
    rw [iterDiff_cons, List.foldl_cons, ih (DiagPhase.shiftBy d P), shiftBy_eval_frameDiff]

/-- A multilinear exponent is zero iff its value function vanishes everywhere. -/
lemma multilinear_eq_zero_iff_eval {m : ℕ} {P : DiagPhase n m}
    (h : DiagPhase.IsMultilinear P) :
    P = 0 ↔ ∀ v, P.eval v = 0 := by
  constructor
  · intro hP v; rw [hP]; simp [DiagPhase.eval]
  · intro h_eval; exact multilinear_eval_injective h isMultilinear_zero h_eval

/-! ### The top-monomial witness -/

/-- **Top monomial.** A nonzero exponent has a support monomial whose
per-monomial effective level attains the polynomial's effective level. -/
lemma exists_top_monomial {m : ℕ} {P : DiagPhase n m} (hP : P ≠ 0) :
    ∃ d ∈ P.support, DiagPhase.effLevelMonom m (P.coeff d) d = DiagPhase.effectiveLevel P := by
  have h_ne : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨d, hd_mem, hd_eq⟩ :=
    Finset.exists_mem_eq_sup P.support h_ne (fun d => DiagPhase.effLevelMonom m (P.coeff d) d)
  exact ⟨d, hd_mem, hd_eq.symm⟩

/-! ### The reverse direction (against the isolated lower-bound `Prop`) -/

/-- **The Aichinger–Moosbauer lower-bound crux** (isolated `Prop`). A multilinear,
**constant-free** (`coeff 0 = 0`) nonzero exponent `P` admits a *surviving*
difference sequence: a direction list `ds` of length exactly `effectiveLevel P`
whose iterated difference `iterDiff ds P` is still nonzero. This is the
functional-degree lower bound; discharging it (`FrameDescentReverseDischarge.lean`) needs the
`−2Δ` tower on a monomial, the 2-adic valuation endgame, and leading-term non-cancellation. A
`Prop` hypothesis is not an axiom, so the consumers below stay axiom-clean against
it.

The constant-free guard is essential: a nonzero *constant* `P = C c` is
multilinear with `effectiveLevel = m − 1 ≥ 1`, yet every nonempty difference
vanishes — so without `coeff 0 = 0` the statement is false (and matches the
`h_const` hypothesis of `cgk_exact_level`). -/
def SurvivingTopCoeffNonzero (n : ℕ) : Prop :=
  ∀ {m : ℕ} (P : DiagPhase n m), DiagPhase.IsMultilinear P → P.coeff 0 = 0 → P ≠ 0 →
    ∃ ds : List (Fin n → ZMod 2),
      ds.length = DiagPhase.effectiveLevel P ∧ iterDiff ds P ≠ 0

/-- **Descent, reverse direction.** If all `(k+1)`-fold iterated differences of a
multilinear exponent vanish, then its effective level is `≤ k`. Proof: contrapose
via `SurvivingTopCoeffNonzero` — a level-`> k` exponent has a surviving sequence
of length `> k`; its length-`(k+1)` prefix is then a nonzero `(k+1)`-fold
difference (truncate via `iterDiff_append` + `iterDiff_zero`), contradicting the
hypothesis. -/
theorem descent_reverse (hsurv : SurvivingTopCoeffNonzero n) {m : ℕ}
    {P : DiagPhase n m} {k : ℕ}
    (h_mul : DiagPhase.IsMultilinear P) (hconst : P.coeff 0 = 0)
    (hvanish : ∀ ds : List (Fin n → ZMod 2), ds.length = k + 1 → iterDiff ds P = 0) :
    DiagPhase.effectiveLevel P ≤ k := by
  by_contra h_contra
  rw [not_le] at h_contra
  by_cases hP_zero : P = 0
  · subst hP_zero
    rw [DiagPhase.effectiveLevel_zero] at h_contra
    exact Nat.not_lt_zero k h_contra
  · obtain ⟨ds, hds_len, hds_nonzero⟩ := hsurv P h_mul hconst hP_zero
    have hds_ge : k + 1 ≤ ds.length := by omega
    have hcat : ds.take (k + 1) ++ ds.drop (k + 1) = ds := List.take_append_drop (k + 1) ds
    have hlen' : (ds.take (k + 1)).length = k + 1 := by
      rw [List.length_take]; exact Nat.min_eq_left hds_ge
    have hzero := hvanish (ds.take (k + 1)) hlen'
    apply hds_nonzero
    calc iterDiff ds P
        = iterDiff (ds.take (k + 1) ++ ds.drop (k + 1)) P := by rw [hcat]
      _ = iterDiff (ds.drop (k + 1)) (iterDiff (ds.take (k + 1)) P) :=
          iterDiff_append _ _ _
      _ = iterDiff (ds.drop (k + 1)) 0 := by rw [hzero]
      _ = 0 := iterDiff_zero _

/-- **Descent characterization.** For a multilinear exponent, `effectiveLevel ≤ k`
iff every `(k+1)`-fold iterated difference vanishes — the frame's form of
"level = functional degree". Forward is `descent_forward`; reverse is
`descent_reverse` (against the isolated `SurvivingTopCoeffNonzero`). -/
theorem descent_characterization (hsurv : SurvivingTopCoeffNonzero n)
    {m : ℕ} {P : DiagPhase n m} (h_mul : DiagPhase.IsMultilinear P)
    (hconst : P.coeff 0 = 0) (k : ℕ) :
    DiagPhase.effectiveLevel P ≤ k ↔
      ∀ ds : List (Fin n → ZMod 2), ds.length = k + 1 → iterDiff ds P = 0 := by
  constructor
  · intro h_le ds h_len
    apply descent_forward h_mul
    rw [h_len]; omega
  · intro hvanish
    exact descent_reverse hsurv h_mul hconst hvanish

end FTQCLib.Frame

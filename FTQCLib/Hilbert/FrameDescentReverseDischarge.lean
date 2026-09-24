/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.FrameDescentReverse

/-! # Discharging `SurvivingTopCoeffNonzero` (descent, reverse direction)

Proves the named `Prop` `SurvivingTopCoeffNonzero` TRUE — the Aichinger–Moosbauer
functional-degree lower bound — making `descent_reverse` / `descent_characterization`
unconditional. The route is the combinatorial 2-adic `−2Δ` monomial tower.

This file builds upward:
* `pow_two_mul_ne_zero` — the surviving-constant nonzeroness (`2^(m-1-v(c))·c ≠ 0`,
  its `val` is exactly `2^(m-1)`).
* the `−2Δ` same-direction tower on a monomial.
* the `S*`-pass constant extraction + ties (the crux).
* the discharge of `SurvivingTopCoeffNonzero` and unconditional consumers.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert MvPolynomial

variable {n : ℕ}

/-! ### Surviving-constant nonzeroness -/

/-- `((2:ZMod (2^m))^o * c).val = (2^o * c.val) % 2^m`. -/
private lemma val_pow_two_mul {m : ℕ} (c : ZMod (2 ^ m)) (o : ℕ) :
    ((2 : ZMod (2 ^ m)) ^ o * c).val = (2 ^ o * c.val) % 2 ^ m := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have hcast : ((2 ^ o * c.val : ℕ) : ZMod (2 ^ m)) = (2 : ZMod (2 ^ m)) ^ o * c := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.val_natCast]

/-- **Surviving-constant nonzeroness.** For `c ≠ 0` with `v = DiagPhase.twoAdicVal c`, the
element `2^(m-1-v) · c` is nonzero in `ZMod (2^m)`: its `val` is exactly `2^(m-1)`
(the odd part wraps away, `2^(m-1)·(odd) ≡ 2^(m-1) mod 2^m`). This is the endgame
of the descent-reverse crux; it needs no exact-valuation lemma. -/
lemma pow_two_mul_ne_zero {m : ℕ} {c : ZMod (2 ^ m)} (hc : c ≠ 0) :
    (2 : ZMod (2 ^ m)) ^ (m - 1 - DiagPhase.twoAdicVal c) * c ≠ 0 := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  have hcval_ne : c.val ≠ 0 := by
    intro h; apply hc
    have hh := ZMod.natCast_zmod_val c
    rw [h, Nat.cast_zero] at hh; exact hh.symm
  have hv_lt : DiagPhase.twoAdicVal c < m := DiagPhase.twoAdicVal_lt_of_ne_zero hc
  have hm : 1 ≤ m := by omega
  have hfact : DiagPhase.twoAdicVal c = c.val.factorization 2 := DiagPhase.twoAdicVal_of_ne_zero hc
  have hsplit : 2 ^ (DiagPhase.twoAdicVal c) * ordCompl[2] c.val = c.val := by
    rw [hfact]; exact Nat.ordProj_mul_ordCompl_eq_self c.val 2
  have hu_odd : ¬ 2 ∣ ordCompl[2] c.val := Nat.not_dvd_ordCompl Nat.prime_two hcval_ne
  -- the value is exactly 2^(m-1)
  have hval : ((2 : ZMod (2 ^ m)) ^ (m - 1 - DiagPhase.twoAdicVal c) * c).val = 2 ^ (m - 1) := by
    rw [val_pow_two_mul, ← hsplit, ← mul_assoc, ← pow_add]
    have hexp : (m - 1 - DiagPhase.twoAdicVal c) + DiagPhase.twoAdicVal c = m - 1 := by omega
    rw [hexp]
    obtain ⟨t, ht⟩ : ∃ t, ordCompl[2] c.val = 2 * t + 1 := by
      rcases Nat.even_or_odd (ordCompl[2] c.val) with he | ho
      · exact absurd he.two_dvd hu_odd
      · exact ho
    rw [ht]
    have h2 : (2 : ℕ) ^ (m - 1) * 2 = 2 ^ m := by rw [← pow_succ]; congr 1; omega
    have hrw : (2 : ℕ) ^ (m - 1) * (2 * t + 1) = 2 ^ (m - 1) + 2 ^ m * t := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, h2]; ring
    rw [hrw, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by
      have : (2 : ℕ) ^ (m - 1) < 2 ^ m := by
        apply Nat.pow_lt_pow_right (by norm_num); omega
      exact this)
  intro h0
  rw [h0, ZMod.val_zero] at hval
  exact absurd hval.symm (by positivity)

/-! ### The `−2Δ` same-direction tower -/

/-- **`−2Δ` same-direction tower** on a monomial. Repeating `shiftDeriv i` (with
`d i = 1`) builds the 2-adic depth:
`(shiftDeriv i)^[k+1] (monomial d c) = monomial (d.erase i) ((-2)^k · c)
+ monomial d ((-2)^(k+1) · c)`. The recursion collapses because `shiftDeriv i`
annihilates `monomial (d.erase i) _` (the erase removed `i`). -/
lemma shiftDeriv_iterate_monomial {m : ℕ} (i : Fin n) (d : Fin n →₀ ℕ)
    (c : ZMod (2 ^ m)) (hdi : d i = 1) (k : ℕ) :
    (DiagPhase.shiftDeriv i)^[k + 1] (monomial d c : DiagPhase n m)
      = monomial (d.erase i) ((-2 : ZMod (2 ^ m)) ^ k * c)
        + monomial d ((-2 : ZMod (2 ^ m)) ^ (k + 1) * c) := by
  induction k with
  | zero =>
    rw [Function.iterate_one,
      DiagPhase.shiftDeriv_monomial_multilinear_di_one i d c hdi,
      pow_zero, one_mul, pow_one, DiagPhase.two_mul_monomial, sub_eq_add_neg, ← map_neg]
    congr 2
    ring
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih, DiagPhase.shiftDeriv_add,
      DiagPhase.shiftDeriv_monomial_of_di_zero i (d.erase i) _ (Finsupp.erase_same),
      DiagPhase.shiftDeriv_monomial_multilinear_di_one i d _ hdi,
      DiagPhase.two_mul_monomial, zero_add, sub_eq_add_neg, ← map_neg]
    congr 2
    ring

/-! ### `S*`-pass: the iterated single-coordinate difference and the kill lemma -/

/-- Iterated single-coordinate difference `is.foldl shiftDeriv`. Equals
`iterDiff (is.map e_·)` via `iterDiff_map_single`. -/
noncomputable def iterShiftDeriv (is : List (Fin n)) {m : ℕ} (Q : DiagPhase n m) :
    DiagPhase n m :=
  is.foldl (fun R i => DiagPhase.shiftDeriv i R) Q

@[simp] lemma iterShiftDeriv_nil {m : ℕ} (Q : DiagPhase n m) : iterShiftDeriv [] Q = Q := rfl

lemma iterShiftDeriv_cons (i : Fin n) (is : List (Fin n)) {m : ℕ} (Q : DiagPhase n m) :
    iterShiftDeriv (i :: is) Q = iterShiftDeriv is (DiagPhase.shiftDeriv i Q) := rfl

lemma shiftDeriv_zero (i : Fin n) {m : ℕ} : DiagPhase.shiftDeriv i (0 : DiagPhase n m) = 0 := by
  have h := DiagPhase.shiftDeriv_add i (0 : DiagPhase n m) 0
  rw [add_zero] at h
  nth_rewrite 1 [← add_zero (DiagPhase.shiftDeriv i (0 : DiagPhase n m))] at h
  exact (add_left_cancel h).symm

lemma iterShiftDeriv_zero {m : ℕ} (is : List (Fin n)) :
    iterShiftDeriv is (0 : DiagPhase n m) = 0 := by
  induction is with
  | nil => rfl
  | cons i rest ih => rw [iterShiftDeriv_cons, shiftDeriv_zero]; exact ih

/-- For a squarefree-supported `Q`, every monomial of `shiftDeriv i Q` is either
`e.erase i` or `e` for some monomial `e` of `Q` (the closed forms touch only the
`i`-slot). -/
lemma support_shiftDeriv_pair (i : Fin n) {m : ℕ} {Q : DiagPhase n m}
    (hQ : ∀ e ∈ Q.support, ∀ k, e k ≤ 1) :
    ∀ e' ∈ (DiagPhase.shiftDeriv i Q).support, ∃ e ∈ Q.support, e' = e.erase i ∨ e' = e := by
  classical
  intro e' he'
  rw [← DiagPhase.shiftBy_single_eq_shiftDeriv, MvPolynomial.as_sum Q,
    DiagPhase.shiftBy_finsetSum] at he'
  obtain ⟨e, he, he'2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he')
  rw [DiagPhase.shiftBy_single_eq_shiftDeriv] at he'2
  refine ⟨e, he, ?_⟩
  by_cases hei : e i = 0
  · rw [DiagPhase.shiftDeriv_monomial_of_di_zero i e _ hei,
      MvPolynomial.support_zero] at he'2
    exact absurd he'2 (Finset.notMem_empty e')
  · have hei1 : e i = 1 := le_antisymm (hQ e he i) (Nat.one_le_iff_ne_zero.mpr hei)
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [MvPolynomial.mem_support_iff,
      DiagPhase.shiftDeriv_monomial_multilinear_di_one i e _ hei1,
      DiagPhase.two_mul_monomial, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
      if_neg (fun h => h1 h.symm), if_neg (fun h => h2 h.symm), sub_zero] at he'2
    exact he'2 rfl

/-- `shiftDeriv i` preserves squarefree support. -/
lemma support_shiftDeriv_squarefree (i : Fin n) {m : ℕ} {Q : DiagPhase n m}
    (hQ : ∀ e ∈ Q.support, ∀ k, e k ≤ 1) :
    ∀ e' ∈ (DiagPhase.shiftDeriv i Q).support, ∀ k, e' k ≤ 1 := by
  intro e' he' k
  obtain ⟨e, he, h⟩ := support_shiftDeriv_pair i hQ e' he'
  rcases h with h | h
  · subst h
    by_cases hk : k = i
    · subst hk; rw [Finsupp.erase_same]; exact Nat.zero_le 1
    · rw [Finsupp.erase_ne hk]; exact hQ e he k
  · rw [h]; exact hQ e he k

/-- `shiftDeriv i` preserves omission of a coordinate `j ≠ i`. -/
lemma support_shiftDeriv_omit (i j : Fin n) (hij : i ≠ j) {m : ℕ} {Q : DiagPhase n m}
    (hQ : ∀ e ∈ Q.support, ∀ k, e k ≤ 1) (homit : ∀ e ∈ Q.support, e j = 0) :
    ∀ e' ∈ (DiagPhase.shiftDeriv i Q).support, e' j = 0 := by
  intro e' he'
  obtain ⟨e, he, h⟩ := support_shiftDeriv_pair i hQ e' he'
  rcases h with h | h
  · subst h; rw [Finsupp.erase_ne (Ne.symm hij)]; exact homit e he
  · rw [h]; exact homit e he

/-- The kill lemma: if some coordinate `j ∈ is` is absent from `Q` (every monomial
omits it), the whole iterated difference vanishes — `shiftDeriv j` annihilates a
`j`-free polynomial and nothing reintroduces `j`. -/
lemma iterShiftDeriv_eq_zero_of_mem_omit {m : ℕ} (is : List (Fin n)) (j : Fin n) :
    ∀ {Q : DiagPhase n m}, (∀ e ∈ Q.support, ∀ k, e k ≤ 1) →
      (∀ e ∈ Q.support, e j = 0) → j ∈ is → iterShiftDeriv is Q = 0 := by
  classical
  induction is with
  | nil => intro Q _ _ hj; simp at hj
  | cons i rest ih =>
    intro Q hsq homit hj
    rw [iterShiftDeriv_cons]
    by_cases hij : i = j
    · subst hij
      have hz : DiagPhase.shiftDeriv i Q = 0 := by
        rw [← DiagPhase.shiftBy_single_eq_shiftDeriv, MvPolynomial.as_sum Q,
          DiagPhase.shiftBy_finsetSum]
        apply Finset.sum_eq_zero
        intro e he
        rw [DiagPhase.shiftBy_single_eq_shiftDeriv]
        exact DiagPhase.shiftDeriv_monomial_of_di_zero i e (Q.coeff e) (homit e he)
      rw [hz, iterShiftDeriv_zero]
    · have hj' : j ∈ rest := (List.mem_cons.mp hj).resolve_left (fun h => hij h.symm)
      exact ih (Q := DiagPhase.shiftDeriv i Q) (support_shiftDeriv_squarefree i hsq)
        (support_shiftDeriv_omit i j hij hsq homit) hj'

/-- A monomial missing a coordinate `j ∈ is` is killed by the iterated
difference. -/
lemma iterShiftDeriv_monomial_eq_zero_of_mem_zero {m : ℕ} {is : List (Fin n)}
    {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)} (hsq : ∀ k, d k ≤ 1) {j : Fin n}
    (hj : j ∈ is) (hdj : d j = 0) :
    iterShiftDeriv is (monomial d c : DiagPhase n m) = 0 := by
  refine iterShiftDeriv_eq_zero_of_mem_omit is j (fun e he k => ?_) (fun e he => ?_) hj
  · rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)]; exact hsq k
  · rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)]; exact hdj

/-- `shiftDeriv i` preserves "every monomial contains coordinate `k`" for `k ≠ i`. -/
lemma support_shiftDeriv_keep (i k : Fin n) (hik : i ≠ k) {m : ℕ} {Q : DiagPhase n m}
    (hQ : ∀ e ∈ Q.support, ∀ l, e l ≤ 1) (hkeep : ∀ e ∈ Q.support, e k ≠ 0) :
    ∀ e' ∈ (DiagPhase.shiftDeriv i Q).support, e' k ≠ 0 := by
  intro e' he'
  obtain ⟨e, he, h⟩ := support_shiftDeriv_pair i hQ e' he'
  rcases h with h | h
  · subst h; rw [Finsupp.erase_ne (Ne.symm hik)]; exact hkeep e he
  · rw [h]; exact hkeep e he

/-- The iterated difference preserves "every monomial contains `k`" when `k ∉ is`. -/
lemma iterShiftDeriv_keep {m : ℕ} (k : Fin n) :
    ∀ (is : List (Fin n)), k ∉ is → ∀ {Q : DiagPhase n m},
      (∀ e ∈ Q.support, ∀ l, e l ≤ 1) → (∀ e ∈ Q.support, e k ≠ 0) →
        ∀ e' ∈ (iterShiftDeriv is Q).support, e' k ≠ 0 := by
  intro is
  induction is with
  | nil => intro _ Q _ hkeep e' he'; rw [iterShiftDeriv_nil] at he'; exact hkeep e' he'
  | cons i rest ih =>
    intro hk Q hsq hkeep e' he'
    rw [iterShiftDeriv_cons] at he'
    have hik : i ≠ k := by
      intro h; subst h; exact hk (List.mem_cons.mpr (Or.inl rfl))
    have hk' : k ∉ rest := fun h => hk (List.mem_cons.mpr (Or.inr h))
    exact ih hk' (Q := DiagPhase.shiftDeriv i Q) (support_shiftDeriv_squarefree i hsq)
      (support_shiftDeriv_keep i k hik hsq hkeep) e' he'

/-- A polynomial whose every monomial contains coordinate `k` has no constant term. -/
lemma coeff_zero_eq_zero_of_keep {m : ℕ} (k : Fin n) {Q : DiagPhase n m}
    (hkeep : ∀ e ∈ Q.support, e k ≠ 0) : MvPolynomial.coeff 0 Q = 0 := by
  by_contra hc
  exact hkeep 0 (MvPolynomial.mem_support_iff.mpr hc) (by simp)

/-- An un-differentiated support coordinate forces the constant term to `0`. -/
lemma iterShiftDeriv_coeff_zero_of_keep {m : ℕ} {is : List (Fin n)}
    {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)} (hsq : ∀ l, d l ≤ 1) {k : Fin n}
    (hk : k ∉ is) (hdk : d k ≠ 0) :
    MvPolynomial.coeff 0 (iterShiftDeriv is (monomial d c : DiagPhase n m)) = 0 := by
  apply coeff_zero_eq_zero_of_keep k
  apply iterShiftDeriv_keep k is hk
  · intro e he l
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)]; exact hsq l
  · intro e he
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)]; exact hdk

/-- `shiftDeriv i` distributes over subtraction. -/
lemma shiftDeriv_sub (i : Fin n) {m : ℕ} (P Q : DiagPhase n m) :
    DiagPhase.shiftDeriv i (P - Q) = DiagPhase.shiftDeriv i P - DiagPhase.shiftDeriv i Q := by
  rw [sub_eq_add_neg, sub_eq_add_neg, DiagPhase.shiftDeriv_add]
  congr 1
  have h := DiagPhase.shiftDeriv_add i Q (-Q)
  rw [add_neg_cancel, shiftDeriv_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The iterated difference distributes over subtraction. -/
lemma iterShiftDeriv_sub {m : ℕ} (is : List (Fin n)) (P Q : DiagPhase n m) :
    iterShiftDeriv is (P - Q) = iterShiftDeriv is P - iterShiftDeriv is Q := by
  induction is generalizing P Q with
  | nil => rfl
  | cons i rest ih =>
    rw [iterShiftDeriv_cons, iterShiftDeriv_cons, iterShiftDeriv_cons, shiftDeriv_sub]
    exact ih (DiagPhase.shiftDeriv i P) (DiagPhase.shiftDeriv i Q)

/-- **Exact-support pass.** Differencing along each coordinate of `d`'s
support exactly once extracts the coefficient as the constant term. -/
lemma iterShiftDeriv_exact_coeff {m : ℕ} :
    ∀ (is : List (Fin n)), is.Nodup → ∀ {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)},
      (∀ i, d i ≤ 1) → is.toFinset = d.support →
        MvPolynomial.coeff 0 (iterShiftDeriv is (monomial d c : DiagPhase n m)) = c := by
  intro is
  induction is with
  | nil =>
    intro _ d c _ hsupp
    rw [List.toFinset_nil] at hsupp
    have hd : d = 0 := Finsupp.support_eq_empty.mp hsupp.symm
    subst hd
    rw [iterShiftDeriv_nil, MvPolynomial.coeff_monomial, if_pos rfl]
  | cons i rest ih =>
    intro hnd d c hsq hsupp
    have hi_mem : i ∈ d.support := by
      rw [← hsupp, List.mem_toFinset]; exact List.mem_cons.mpr (Or.inl rfl)
    have hdi : d i = 1 :=
      le_antisymm (hsq i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi_mem))
    have hi_notin : i ∉ rest := (List.nodup_cons.mp hnd).1
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hi_notin_tf : i ∉ rest.toFinset := by rw [List.mem_toFinset]; exact hi_notin
    have hsupp_erase : rest.toFinset = (d.erase i).support := by
      rw [Finsupp.support_erase, ← hsupp, List.toFinset_cons, Finset.erase_insert hi_notin_tf]
    have hsq_erase : ∀ l, (d.erase i) l ≤ 1 := by
      intro l; by_cases hl : l = i
      · subst hl; rw [Finsupp.erase_same]; omega
      · rw [Finsupp.erase_ne hl]; exact hsq l
    rw [iterShiftDeriv_cons, DiagPhase.shiftDeriv_monomial_multilinear_di_one i d c hdi,
      DiagPhase.two_mul_monomial, iterShiftDeriv_sub, MvPolynomial.coeff_sub,
      ih hnd' hsq_erase hsupp_erase,
      iterShiftDeriv_coeff_zero_of_keep hsq hi_notin (by rw [hdi]; exact one_ne_zero), sub_zero]

/-! ### Assembly helpers -/

lemma iterShiftDeriv_append {m : ℕ} (a b : List (Fin n)) (Q : DiagPhase n m) :
    iterShiftDeriv (a ++ b) Q = iterShiftDeriv b (iterShiftDeriv a Q) := by
  unfold iterShiftDeriv; rw [List.foldl_append]

lemma iterShiftDeriv_replicate {m : ℕ} (o : ℕ) (i : Fin n) (Q : DiagPhase n m) :
    iterShiftDeriv (List.replicate o i) Q = (DiagPhase.shiftDeriv i)^[o] Q := by
  induction o generalizing Q with
  | zero => rfl
  | succ o ih =>
    rw [List.replicate_succ, iterShiftDeriv_cons, ih, Function.iterate_succ]; rfl

lemma iterShiftDeriv_add {m : ℕ} (is : List (Fin n)) (P Q : DiagPhase n m) :
    iterShiftDeriv is (P + Q) = iterShiftDeriv is P + iterShiftDeriv is Q := by
  induction is generalizing P Q with
  | nil => rfl
  | cons i rest ih =>
    rw [iterShiftDeriv_cons, iterShiftDeriv_cons, iterShiftDeriv_cons, DiagPhase.shiftDeriv_add]
    exact ih _ _

/-- For a squarefree exponent, the degree sum equals the support cardinality. -/
lemma sum_eq_card_of_squarefree {d : Fin n →₀ ℕ} (hsq : ∀ k, d k ≤ 1) :
    d.sum (fun _ e => e) = d.support.card := by
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro i hi
  exact le_antisymm (hsq i) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-! ### Discharging the lower-bound `Prop` -/

/-- **The Aichinger–Moosbauer lower bound** (`SurvivingTopCoeffNonzero` proven).
Every multilinear, constant-free, nonzero exponent admits a length-`effectiveLevel`
iterated difference that is still nonzero — the witness being `o` repeats of a
top-monomial coordinate `i*` followed by one pass over the rest of its support. -/
theorem survivingTopCoeffNonzero {n : ℕ} : SurvivingTopCoeffNonzero n := by
  intro m P h_mul hconst hP_ne
  classical
  obtain ⟨d, hd_mem, hlevel⟩ := exists_top_monomial hP_ne
  have hc_ne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd_mem
  haveI : Nontrivial (ZMod (2 ^ m)) := nontrivial_of_ne _ _ hc_ne
  have hsq : ∀ k, d k ≤ 1 := h_mul d hd_mem
  have hd_ne : d ≠ 0 := fun h0 => hc_ne (by rw [h0]; exact hconst)
  obtain ⟨istar, histar⟩ := Finsupp.support_nonempty_iff.mpr hd_ne
  have hdistar : d istar = 1 :=
    le_antisymm (hsq istar) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp histar))
  obtain ⟨o, ho⟩ : ∃ o, m - 1 - DiagPhase.twoAdicVal (P.coeff d) = o := ⟨_, rfl⟩
  set isW := List.replicate o istar ++ d.support.toList with hisW
  have htf : d.support.toList.toFinset = d.support := Finset.toList_toFinset _
  have hnd_list : d.support.toList.Nodup := Finset.nodup_toList _
  have histar_list : istar ∈ d.support.toList := Finset.mem_toList.mpr histar
  have hsq_erase : ∀ l, (d.erase istar) l ≤ 1 := by
    intro l; by_cases hl : l = istar
    · subst hl; rw [Finsupp.erase_same]; omega
    · rw [Finsupp.erase_ne hl]; exact hsq l
  have hisW_tf : isW.toFinset = d.support := by
    rw [hisW, List.toFinset_append, htf, Finset.union_eq_right]
    intro x hx
    rw [List.mem_toFinset, List.mem_replicate] at hx
    rw [hx.2]; exact histar
  -- other monomials contribute nothing to the constant term
  have h0 : ∀ d' ∈ P.support, d' ≠ d →
      MvPolynomial.coeff 0 (iterDiff (isW.map (fun i => Pi.single i 1))
        (monomial d' (P.coeff d'))) = 0 := by
    intro d' hd'_mem hd'_ne
    rw [iterDiff_map_single]
    show MvPolynomial.coeff 0 (iterShiftDeriv isW (monomial d' (P.coeff d'))) = 0
    have hsq' : ∀ k, d' k ≤ 1 := h_mul d' hd'_mem
    have hne_supp : d'.support ≠ d.support := by
      intro h; apply hd'_ne; ext k
      have hd1 : d k = (if k ∈ d.support then 1 else 0) := by
        by_cases hk : k ∈ d.support
        · rw [if_pos hk]
          exact le_antisymm (hsq k) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk))
        · rw [if_neg hk]; by_contra hh; exact hk (Finsupp.mem_support_iff.mpr hh)
      have hd2 : d' k = (if k ∈ d.support then 1 else 0) := by
        by_cases hk : k ∈ d.support
        · rw [if_pos hk]
          rw [← h] at hk
          exact le_antisymm (hsq' k) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk))
        · rw [if_neg hk]
          rw [← h] at hk
          by_contra hh; exact hk (Finsupp.mem_support_iff.mpr hh)
      rw [hd2, hd1]
    rw [Ne, Finset.ext_iff, not_forall] at hne_supp
    obtain ⟨k, hk⟩ := hne_supp
    by_cases hkd' : k ∈ d'.support
    · have hkd : k ∉ d.support := fun h => hk ⟨fun _ => h, fun _ => hkd'⟩
      have hk_isW : k ∉ isW := fun h => hkd (hisW_tf ▸ List.mem_toFinset.mpr h)
      exact iterShiftDeriv_coeff_zero_of_keep hsq' hk_isW (Finsupp.mem_support_iff.mp hkd')
    · have hkd : k ∈ d.support := by
        by_contra h; exact hk ⟨fun hh => absurd hh hkd', fun hh => absurd hh h⟩
      have hk_isW : k ∈ isW := List.mem_toFinset.mp (hisW_tf ▸ hkd)
      rw [iterShiftDeriv_monomial_eq_zero_of_mem_zero hsq' hk_isW
        (by by_contra hh; exact hkd' (Finsupp.mem_support_iff.mpr hh)), MvPolynomial.coeff_zero]
  refine ⟨isW.map (fun i => Pi.single i 1), ?_, ?_⟩
  · rw [List.length_map, hisW, List.length_append, List.length_replicate,
      Finset.length_toList, ← hlevel, DiagPhase.effLevelMonom,
      sum_eq_card_of_squarefree hsq, ho]
  · have hcoeff : MvPolynomial.coeff 0
        (iterDiff (isW.map (fun i => Pi.single i 1)) P)
        = (-2 : ZMod (2 ^ m)) ^ o * P.coeff d := by
      rw [iterDiff_eq_sum_over_support, MvPolynomial.coeff_sum,
        Finset.sum_eq_single_of_mem d hd_mem h0, iterDiff_map_single]
      show MvPolynomial.coeff 0 (iterShiftDeriv isW (monomial d (P.coeff d)))
        = (-2 : ZMod (2 ^ m)) ^ o * P.coeff d
      rw [hisW, iterShiftDeriv_append, iterShiftDeriv_replicate]
      cases o with
      | zero =>
        rw [Function.iterate_zero_apply,
          iterShiftDeriv_exact_coeff d.support.toList hnd_list hsq htf, pow_zero, one_mul]
      | succ k =>
        rw [shiftDeriv_iterate_monomial istar d (P.coeff d) hdistar k,
          iterShiftDeriv_add, MvPolynomial.coeff_add,
          iterShiftDeriv_monomial_eq_zero_of_mem_zero hsq_erase histar_list Finsupp.erase_same,
          MvPolynomial.coeff_zero,
          iterShiftDeriv_exact_coeff d.support.toList hnd_list hsq htf, zero_add]
    intro hzero
    rw [hzero, MvPolynomial.coeff_zero] at hcoeff
    have h2c : (2 : ZMod (2 ^ m)) ^ o * P.coeff d ≠ 0 := by
      rw [← ho]; exact pow_two_mul_ne_zero hc_ne
    refine (?_ : (-2 : ZMod (2 ^ m)) ^ o * P.coeff d ≠ 0) hcoeff.symm
    rcases Nat.even_or_odd o with he | hodd
    · rw [he.neg_pow]; exact h2c
    · rw [hodd.neg_pow, neg_mul]; exact neg_ne_zero.mpr h2c

/-- **Descent, reverse direction (unconditional).** -/
theorem descent_reverse' {m : ℕ} {P : DiagPhase n m} {k : ℕ}
    (h_mul : DiagPhase.IsMultilinear P) (hconst : P.coeff 0 = 0)
    (hvanish : ∀ ds : List (Fin n → ZMod 2), ds.length = k + 1 → iterDiff ds P = 0) :
    DiagPhase.effectiveLevel P ≤ k :=
  descent_reverse survivingTopCoeffNonzero h_mul hconst hvanish

/-- **Descent characterization (unconditional).** For a multilinear, constant-free
exponent, `effectiveLevel ≤ k` iff every `(k+1)`-fold iterated difference vanishes —
the frame's "level = functional degree", with the lower bound discharged. -/
theorem descent_characterization' {m : ℕ} {P : DiagPhase n m}
    (h_mul : DiagPhase.IsMultilinear P) (hconst : P.coeff 0 = 0) (k : ℕ) :
    DiagPhase.effectiveLevel P ≤ k ↔
      ∀ ds : List (Fin n → ZMod 2), ds.length = k + 1 → iterDiff ds P = 0 :=
  descent_characterization survivingTopCoeffNonzero h_mul hconst k

end FTQCLib.Frame

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.BoolReduceLevel

/-!
# The difference of a level-two exponent is dyadic-affine

A function `f : (𝔽₂)^N → ZMod (2^m)` is *dyadic-affine* (`IsF2Affine`) when it is a constant plus
the top bit `2^{m−1}` times an `𝔽₂`-linear form: `f w = a + 2^{m−1}·(Σ_j e_j·w_j)`. The theorem of
this module is that the functional difference of an exponent of effective level `≤ 2` along any
variable has this shape (`funcDerivEval_isF2Affine`). The level bound is the hypothesis the
frame's carrier meets on its Clifford fragment: every quadratic coefficient a multiple of
`2^{m−1}`, every linear coefficient a multiple of `2^{m−2}`, every constant of valuation at least
`m − 3`, no cubic terms; the square `c·X_j²` has `c = 2^{m−1}` and evaluates as `2^{m−1}·X_j`.

The route, for a multilinear exponent: `shiftDeriv` drops the effective level by one
(`shiftDeriv_effectiveLevel_lt`), so the difference polynomial has level `≤ 1`; an exponent of
level `≤ 1` is a constant plus top-bit linear monomials, because the only nonzero multiple of
`2^{m−1}` in `ZMod (2^m)` is `2^{m−1}` itself (`eq_two_pow_pred_of_twoAdicVal`); and
`shiftDeriv` evaluates to the functional difference on binary inputs. Every affine function has
vanishing second difference (`IsF2Affine.second_diff`), which `AffineDifferenceCheck` uses to
show the level hypothesis is necessary. An arbitrary
exponent is handled through its Boolean normal form, which evaluates the same, is multilinear and
does not raise the level (`FTQCLib/Hierarchy/BoolReduceLevel.lean`).

## Main definitions

* `IsF2Affine f` — `f` is a constant plus the top bit times an `𝔽₂`-linear form.

## Main results

* `funcDerivEval_isF2Affine` — the difference of a level-`≤ 2` exponent is dyadic-affine.
* `funcDerivEval_isF2Affine_of_isMultilinear` — the same on a multilinear exponent, by the
  polynomial-side strict drop.
* `isF2Affine_eval_of_effectiveLevel_le_one` — a level-`≤ 1` exponent evaluates dyadic-affinely.
* `IsF2Affine.second_diff` — the second difference of a dyadic-affine function vanishes.

## Implementation notes

The linear form is carried as a coefficient vector `e` with the sum `Σ_j e_j·w_j` written out; the
frame layer's `dotF2` is that sum definitionally, and this module sits below it. The top-bit
identity `2^{m−1}·2 = 0` is re-derived here (`two_pow_pred_mul_val_add`) rather than imported from
the frame layer, for the same reason. The polynomial-side strict-drop lemma requires
multilinearity (`shiftDeriv` of `X_j²` is outside its scope); the functional statement is stated
for every exponent by passing to the Boolean normal form.
-/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial

variable {N m : ℕ}

/-! ## The top bit against a sum of bits -/

/-- `t ↦ 2^{m−1}·t.val` is additive on `ZMod 2`. -/
theorem two_pow_pred_mul_val_add (s t : ZMod 2) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * (((s + t).val : ℕ) : ZMod (2 ^ m))
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * ((s.val : ℕ) : ZMod (2 ^ m))
        + (2 : ZMod (2 ^ m)) ^ (m - 1) * ((t.val : ℕ) : ZMod (2 ^ m)) := by
  have hz : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      haveI : Subsingleton (ZMod (2 ^ 0)) := by
        rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    · have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 2 ^ m := by
        rw [← pow_succ]; congr 1; omega
      have h0 : ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_pow, Nat.cast_ofNat] at h0
      rw [h2, h0]
  have v0 : ((0 : ZMod 2).val) = 0 := by decide
  have v1 : ((1 : ZMod 2).val) = 1 := by decide
  have v11 : (((1 : ZMod 2) + 1).val) = 0 := by decide
  rcases (show s = 0 ∨ s = 1 by revert s; decide) with rfl | rfl <;>
    rcases (show t = 0 ∨ t = 1 by revert t; decide) with rfl | rfl
  · rw [add_zero, v0]; push_cast; ring
  · rw [zero_add, v0, v1]; push_cast; ring
  · rw [add_zero, v0, v1]; push_cast; ring
  · rw [v11, v1]; push_cast
    rw [mul_zero, mul_one, show (2 : ZMod (2 ^ m)) ^ (m - 1) + 2 ^ (m - 1) = 2 ^ (m - 1) * 2 from by
      ring]
    exact hz.symm

/-! ## Dyadic-affine functions -/

/-- `f` is **dyadic-affine** at precision `m`: a constant plus `2^{m−1}` times an `𝔽₂`-linear form
given by a coefficient vector. -/
def IsF2Affine (f : (Fin N → ZMod 2) → ZMod (2 ^ m)) : Prop :=
  ∃ (a : ZMod (2 ^ m)) (e : Fin N → ZMod 2), ∀ w : Fin N → ZMod 2,
    f w = a + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((∑ j, e j * w j).val : ℕ) : ZMod (2 ^ m))

/-- A constant is dyadic-affine. -/
theorem isF2Affine_const (c : ZMod (2 ^ m)) :
    IsF2Affine (fun _ : Fin N → ZMod 2 => c) := by
  refine ⟨c, 0, fun w => ?_⟩
  simp [show ((0 : ZMod 2).val) = 0 from by decide]

/-- Dyadic-affine functions are closed under addition. -/
theorem IsF2Affine.add {f g : (Fin N → ZMod 2) → ZMod (2 ^ m)}
    (hf : IsF2Affine f) (hg : IsF2Affine g) : IsF2Affine (fun w => f w + g w) := by
  obtain ⟨a, e, ha⟩ := hf
  obtain ⟨b, d, hb⟩ := hg
  refine ⟨a + b, e + d, fun w => ?_⟩
  have hsum : (∑ j, (e + d) j * w j) = (∑ j, e j * w j) + (∑ j, d j * w j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [Pi.add_apply]; ring)
  change f w + g w = _
  rw [ha, hb, hsum, two_pow_pred_mul_val_add]
  ring

/-- The top bit times one coordinate is dyadic-affine. -/
theorem isF2Affine_lin (j : Fin N) :
    IsF2Affine (fun w : Fin N → ZMod 2 =>
      (2 : ZMod (2 ^ m)) ^ (m - 1) * (((w j).val : ℕ) : ZMod (2 ^ m))) := by
  refine ⟨0, Pi.single j 1, fun w => ?_⟩
  have hs : (∑ l, (Pi.single j 1 : Fin N → ZMod 2) l * w l) = w j := by
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_mul]
  rw [zero_add, hs]

/-- A finite sum of dyadic-affine functions is dyadic-affine. -/
theorem isF2Affine_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin N → ZMod 2) → ZMod (2 ^ m))
    (hg : ∀ d ∈ s, IsF2Affine (g d)) : IsF2Affine (fun w => ∑ d ∈ s, g d w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isF2Affine_const (N := N) (m := m) 0
  | insert a s ha ih =>
      have h1 : IsF2Affine (g a) := hg a (Finset.mem_insert_self a s)
      have h2 : IsF2Affine (fun w => ∑ d ∈ s, g d w) :=
        ih (fun d hd => hg d (Finset.mem_insert_of_mem hd))
      have h3 := h1.add h2
      simpa [Finset.sum_insert ha] using h3

/-- Every dyadic-affine function has vanishing second difference. -/
theorem IsF2Affine.second_diff {f : (Fin N → ZMod 2) → ZMod (2 ^ m)} (hf : IsF2Affine f)
    (u v : Fin N → ZMod 2) : f 0 + f (u + v) = f u + f v := by
  obtain ⟨a, e, hae⟩ := hf
  have hz : (∑ j, e j * (0 : Fin N → ZMod 2) j) = 0 := by simp
  have hsplit : (∑ j, e j * (u + v) j) = (∑ j, e j * u j) + (∑ j, e j * v j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [Pi.add_apply]; ring)
  rw [hae 0, hae (u + v), hae u, hae v, hz, hsplit, two_pow_pred_mul_val_add,
    show ((0 : ZMod 2).val) = 0 from by decide]
  push_cast
  ring

/-! ## The shape of an exponent of effective level at most one -/

/-- An exponent vector of total weight at most one is zero or a single variable. -/
theorem exponent_cases {d : Fin N →₀ ℕ} (hd : d.sum (fun _ e => e) ≤ 1) :
    d = 0 ∨ ∃ j, d = Finsupp.single j 1 := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  refine Or.inr ?_
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr h0
  have hsum : d.sum (fun _ e => e) = ∑ l ∈ d.support, d l := rfl
  have hdj1 : 1 ≤ d j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hdjle : d j ≤ ∑ l ∈ d.support, d l :=
    Finset.single_le_sum (f := fun l => d l) (fun _ _ => Nat.zero_le _) hj
  have hdj : d j = 1 := by omega
  refine ⟨j, ?_⟩
  ext k
  by_cases hkj : k = j
  · subst hkj; rw [hdj, Finsupp.single_eq_same]
  · rw [Finsupp.single_apply, if_neg (fun h : j = k => hkj h.symm)]
    by_contra hk
    have hkmem : k ∈ d.support := Finsupp.mem_support_iff.mpr hk
    have hsub : ({j, k} : Finset (Fin N)) ⊆ d.support := by
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl'
      · exact hj
      · rw [Finset.mem_singleton] at hl'; subst hl'; exact hkmem
    have h2 : d j + d k ≤ ∑ l ∈ d.support, d l := by
      rw [← Finset.sum_pair (Ne.symm hkj)]
      exact Finset.sum_le_sum_of_subset hsub
    omega

/-- In `ZMod (2^m)` the only nonzero element divisible by `2^{m−1}` is `2^{m−1}` itself. -/
theorem eq_two_pow_pred_of_twoAdicVal {c : ZMod (2 ^ m)} (hc : c ≠ 0)
    (hv : m - 1 ≤ twoAdicVal c) : c = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
  have hm : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    subst hm0
    haveI : Subsingleton (ZMod (2 ^ 0)) := by
      rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
    exact hc (Subsingleton.elim _ _)
  have hdvd : 2 ^ (m - 1) ∣ c.val := (pow_dvd_val_iff hc (m - 1)).mpr hv
  obtain ⟨k, hk⟩ := hdvd
  have hlt : c.val < 2 ^ m := ZMod.val_lt c
  have hne : c.val ≠ 0 := by
    intro h
    exact hc (by rw [← ZMod.natCast_zmod_val c, h, Nat.cast_zero])
  have hpow : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hpos : 0 < 2 ^ (m - 1) := Nat.two_pow_pos _
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · omega
      · rfl
    · exfalso
      have : 2 ^ (m - 1) * 2 ≤ 2 ^ (m - 1) * k := Nat.mul_le_mul_left _ h
      omega
  have hval : c.val = 2 ^ (m - 1) := by rw [hk, hk1, mul_one]
  rw [← ZMod.natCast_zmod_val c, hval]
  push_cast
  ring

/-- **A level-`≤ 1` exponent evaluates dyadic-affinely.** -/
theorem isF2Affine_eval_of_effectiveLevel_le_one (R : DiagPhase N m)
    (h : effectiveLevel R ≤ 1) : IsF2Affine (fun w => R.eval w) := by
  classical
  have heval : ∀ w : Fin N → ZMod 2,
      R.eval w = ∑ d ∈ R.support, DiagPhase.eval (monomial d (R.coeff d)) w := by
    intro w
    unfold DiagPhase.eval
    conv_lhs => rw [show R = ∑ d ∈ R.support, monomial d (R.coeff d) from R.as_sum]
    rw [map_sum]
  have hkey : IsF2Affine (fun w : Fin N → ZMod 2 =>
      ∑ d ∈ R.support, DiagPhase.eval (monomial d (R.coeff d)) w) := by
    refine isF2Affine_sum _ _ (fun d hd => ?_)
    have hle : effLevelMonom m (R.coeff d) d ≤ 1 := by
      refine le_trans ?_ h
      unfold effectiveLevel
      exact Finset.le_sup (f := fun e => effLevelMonom m (R.coeff e) e) hd
    have hsumle : d.sum (fun _ e => e) ≤ 1 := by unfold effLevelMonom at hle; omega
    rcases exponent_cases hsumle with rfl | ⟨j, rfl⟩
    · have hfun : DiagPhase.eval (monomial 0 (R.coeff 0))
          = (fun _ : Fin N → ZMod 2 => R.coeff 0) := by
        funext w
        unfold DiagPhase.eval
        rw [MvPolynomial.monomial_zero', MvPolynomial.eval_C]
      rw [hfun]
      exact isF2Affine_const _
    · have hc : R.coeff (Finsupp.single j 1) ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hsum1 : (Finsupp.single j 1 : Fin N →₀ ℕ).sum (fun _ e => e) = 1 := by
        rw [Finsupp.sum_single_index rfl]
      have hv : m - 1 ≤ twoAdicVal (R.coeff (Finsupp.single j 1)) := by
        unfold effLevelMonom at hle
        rw [hsum1] at hle
        omega
      have hcoeff : R.coeff (Finsupp.single j 1) = (2 : ZMod (2 ^ m)) ^ (m - 1) :=
        eq_two_pow_pred_of_twoAdicVal hc hv
      have hfun : DiagPhase.eval (monomial (Finsupp.single j 1) (R.coeff (Finsupp.single j 1)))
          = fun w : Fin N → ZMod 2 =>
            (2 : ZMod (2 ^ m)) ^ (m - 1) * (((w j).val : ℕ) : ZMod (2 ^ m)) := by
        funext w
        unfold DiagPhase.eval
        rw [MvPolynomial.eval_monomial, hcoeff, Finsupp.prod_single_index (by rw [pow_zero]),
          pow_one]
        rfl
      rw [hfun]
      exact isF2Affine_lin j
  obtain ⟨a, e, hae⟩ := hkey
  exact ⟨a, e, fun w => by change R.eval w = _; rw [heval w]; exact hae w⟩

/-! ## The theorem -/

/-- A multilinear level-two exponent has a difference polynomial of level at most one. -/
theorem shiftDeriv_effectiveLevel_le_one {Q : DiagPhase N m} (hml : IsMultilinear Q)
    (hlev : effectiveLevel Q ≤ 2) (i : Fin N) : effectiveLevel (shiftDeriv i Q) ≤ 1 := by
  rcases Nat.eq_zero_or_pos Q.totalDegree with h0 | hpos
  · rw [shiftDeriv_totalDegree_zero i h0, effectiveLevel_zero]; omega
  · have := shiftDeriv_effectiveLevel_lt (P := Q) i hml hpos
    omega

/-- The difference of a multilinear level-two exponent is dyadic-affine: the polynomial-side
route through the strict drop of `shiftDeriv`. -/
theorem funcDerivEval_isF2Affine_of_isMultilinear {Q : DiagPhase N m} (hml : IsMultilinear Q)
    (hlev : effectiveLevel Q ≤ 2) (i : Fin N) :
    IsF2Affine (funcDerivEval i Q) := by
  obtain ⟨a, e, hae⟩ :=
    isF2Affine_eval_of_effectiveLevel_le_one (shiftDeriv i Q)
      (shiftDeriv_effectiveLevel_le_one hml hlev i)
  exact ⟨a, e, fun w => by rw [← shiftDeriv_eval_eq_funcDerivEval i Q w]; exact hae w⟩

/-- **The difference of a level-two exponent is dyadic-affine.** For every exponent of effective
level `≤ 2` the functional difference along any variable is `a + 2^{m−1}·ℓ(w)` with `ℓ`
`𝔽₂`-linear. The exponent is replaced by its Boolean normal form, which evaluates the same, is
multilinear and has level at most `2`. -/
theorem funcDerivEval_isF2Affine {Q : DiagPhase N m} (hlev : effectiveLevel Q ≤ 2) (i : Fin N) :
    IsF2Affine (funcDerivEval i Q) := by
  obtain ⟨a, e, hae⟩ := funcDerivEval_isF2Affine_of_isMultilinear (boolReduce_isMultilinear Q)
    ((effectiveLevel_boolReduce_le Q).trans hlev) i
  refine ⟨a, e, fun w => ?_⟩
  have h := hae w
  rw [funcDerivEval_apply, boolReduce_eval_eq, boolReduce_eval_eq] at h
  exact h

end FTQCLib.Hierarchy.DiagPhase

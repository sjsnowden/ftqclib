/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Eberlein numbers — the Johnson analogue of the Krawtchouk numbers

`eberlein n k l t` is the **Eberlein number** `E_l(t)` for the Johnson scheme on `k`-subsets of an
`n`-set: the value, at eigenspace index `t`, of the degree-`l` member of the family. It is defined
by the closed alternating sum, exactly as `ECCLib/Delsarte/Krawtchouk.lean` defines `kraw`.

Eberlein is to the Johnson scheme what Krawtchouk is to the Hamming scheme, and the two sit as
siblings in the Askey hierarchy — Krawtchouk is the Hamming member, Eberlein (a dual Hahn family)
the Johnson one.

## Main definitions

* `eberlein` — the Eberlein number, as a closed alternating sum over `ℤ`.

## Main results

* `eberlein_zero_degree` — degree `0` is constant `1`.
* `eberlein_at_zero` — **`E_l(0)` is the Johnson valence** `C(k,l)·C(n−k,l)`, which is the bridge
  between this file and `Scheme/Johnson.lean`'s `card_filter_interCard_eq`.
* `eberlein_degree_one` — **degree `1` is the classical Johnson graph spectrum**
  `(k−t)(n−k−t) − t`.

## Why the closed form is the definition, and not the recurrence

Delsarte gives a three-term recurrence (4.35) and calls it "very useful for computation", which
makes it look like the natural definition. **It is not available as one.** Its leading coefficient
is `(k+1)²` and it *divides*:

`(k+1)² E_{k+1}(u) = (…) E_k(u) − (…) E_{k−1}(u)`.

Over `ℤ` that determines `E_{k+1}` only as a quotient, so taking it as the definition would need
either `ℚ` or a proof of the divisibility first — the very obligation a recursive definition is
usually chosen to avoid. The closed form is `ℤ`-valued by construction and needs neither.

The divisibility does hold; it was checked numerically over `J(6,3)` before this file was written.
Deriving the recurrence *from* the closed form is therefore a real theorem; it is not proved
here, and not assumed.

## Why there is no generating-polynomial route here

`Krawtchouk.lean` recovers `kraw` as a coefficient of `(1 − X)^i (1 + (q−1)X)^(n−i)`, which works
because Krawtchouk's summand is a Vandermonde-type convolution: the two inner binomials carry
*complementary* indices. Eberlein's two inner binomials carry the *same* index `l − j`, so the
inner sum is a `₂F₁` rather than a product, and no analogue of `kraw_eq_coeff` is available. This
is the one place where the sibling files genuinely differ.

## Convention hazards

The Johnson indexing is stated three different ways across the standard sources — Delsarte
reverses the letters, Martin–Tanaka reverse the order, Burcroff and Godsil agree with this
repository. Rather than argue from conventions, the alignment here was **pinned by computation**:
the definition below reproduces the classical adjacency spectra of `J(4,2)`, `J(6,3)` and — the
only one of the three that can distinguish the alignment, its valences being asymmetric —
`J(5,2)`. Those identifications are kept as rows in `EberleinCheck.lean`.

The outcome is that **`l` is the Johnson *distance*, `k − t`, and not the intersection size `t`.**

As in `Krawtchouk.lean`, `k − t`, `n − k − t` and `l − j` are ℕ-truncated, so values outside
`t ≤ k` and `t ≤ n − k` are junk; consumers bound their quantifiers.

## References

Delsarte, Philips Res. Rep. Suppl. **10** (1973), §4.2.1, equations (4.33) and (4.34);
Burcroff, *Johnson schemes and certain matrices with integral eigenvalues* (2017), Definition 7.6,
equation (73) — the dual-Hahn form, which is the one taken here. The two agree character for
character across reversed conventions.
-/

namespace ECCLib.Delsarte

/-- The **Eberlein number** `E_l(t)` for the Johnson scheme on `k`-subsets of an `n`-set, as the
closed alternating sum (Burcroff (73), Delsarte's second form). Computable; values outside
`t ≤ k` and `t ≤ n − k` are ℕ-truncation junk. -/
def eberlein (n k l t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (l + 1),
    (-1 : ℤ) ^ j * (t.choose j : ℤ) * ((k - t).choose (l - j) : ℤ)
      * ((n - k - t).choose (l - j) : ℤ)

/-! ## Fingerprints -/

@[simp] theorem eberlein_zero_degree (n k t : ℕ) : eberlein n k 0 t = 1 := by
  simp [eberlein]

/-- **`E_l(0)` is the Johnson valence.** Only the `j = 0` term survives, because `C(0,j) = 0` for
`j > 0`. This is the identity `P_l(0) = v_l` — the eigenvalue of relation `l` on the trivial
eigenspace is that relation's valence — and it is the bridge to
`Scheme/Johnson.lean`'s `card_filter_interCard_eq`, whose count `C(k,t)·C(n−k,k−t)` is this same
number under `l = k − t`. -/
theorem eberlein_at_zero (n k l : ℕ) :
    eberlein n k l 0 = (k.choose l : ℤ) * ((n - k).choose l : ℤ) := by
  unfold eberlein
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj0
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos l)) h

/-- **Degree one is the classical Johnson graph spectrum**, `(k−t)(n−k−t) − t`. The `j = 0` term
contributes `(k−t)(n−k−t)` and the `j = 1` term contributes `−t`; there are no others. -/
theorem eberlein_degree_one (n k t : ℕ) :
    eberlein n k 1 t = ((k - t : ℕ) : ℤ) * ((n - k - t : ℕ) : ℤ) - (t : ℤ) := by
  unfold eberlein
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.choose_one_right]
  ring

/-- **One step of the degree-one strict decrease**: the successive difference is `n − 2t ≥ 2`
on the admissible range. This is what makes the degree-one values a separating family. -/
theorem eberlein_degree_one_succ_lt {n k t : ℕ} (h1 : t + 1 ≤ k) (h2 : t + 1 ≤ n - k) :
    eberlein n k 1 (t + 1) < eberlein n k 1 t := by
  rw [eberlein_degree_one, eberlein_degree_one]
  have hkn : k ≤ n := by omega
  have hc1 : ((k - t : ℕ) : ℤ) = (k : ℤ) - t := by
    push_cast [Nat.cast_sub (by omega : t ≤ k)]
    ring
  have hc2 : ((k - (t + 1) : ℕ) : ℤ) = (k : ℤ) - t - 1 := by
    push_cast [Nat.cast_sub h1]
    ring
  have hc3 : ((n - k - t : ℕ) : ℤ) = (n : ℤ) - k - t := by
    have : t ≤ n - k := by omega
    push_cast [Nat.cast_sub (by omega : k ≤ n), Nat.cast_sub this]
    ring
  have hc4 : ((n - k - (t + 1) : ℕ) : ℤ) = (n : ℤ) - k - t - 1 := by
    push_cast [Nat.cast_sub (by omega : k ≤ n), Nat.cast_sub h2]
    ring
  rw [hc1, hc2, hc3, hc4]
  have hA : (1 : ℤ) ≤ (k : ℤ) - t := by
    have := h1
    omega
  have hB : (1 : ℤ) ≤ (n : ℤ) - k - t := by
    have h2' : t + 1 + k ≤ n := by omega
    omega
  have hexp : ((k : ℤ) - t - 1) * ((n : ℤ) - k - t - 1)
      = ((k : ℤ) - t) * ((n : ℤ) - k - t) - ((k : ℤ) - t) - ((n : ℤ) - k - t) + 1 := by
    ring
  push_cast
  linarith [hexp, hA, hB]

/-- **The degree-one values separate the admissible range**: larger `t` gives a strictly
smaller value. -/
theorem eberlein_degree_one_lt_of_lt {n k : ℕ} {t t' : ℕ} (h : t < t') (h1 : t' ≤ k)
    (h2 : t' ≤ n - k) : eberlein n k 1 t' < eberlein n k 1 t := by
  induction t' with
  | zero => omega
  | succ s ih =>
    rcases Nat.lt_or_ge t s with hts | hts
    · exact lt_trans (eberlein_degree_one_succ_lt h1 h2) (ih hts (by omega) (by omega))
    · have hts' : t = s := by omega
      subst hts'
      exact eberlein_degree_one_succ_lt h1 h2

/-- **The top-degree row collapses to a single signed binomial**: at `l = k` the two lower
binomials force `j = t`, so `E_k(t) = (−1)^t C(n−k−t, k−t)` — the eigenvalue row of the
disjointness (Kneser) relation. Holds for every `t ≤ k`, with the usual `ℕ`-truncation
reading outside `t ≤ n − k`. -/
theorem eberlein_top_degree {n k t : ℕ} (ht : t ≤ k) :
    eberlein n k k t = (-1) ^ t * ((n - k - t).choose (k - t) : ℤ) := by
  rw [eberlein]
  rw [Finset.sum_eq_single t
    (fun j _ hjt => ?_) (fun ht' => absurd (Finset.mem_range.mpr (by omega)) ht')]
  · rw [Nat.choose_self, Nat.choose_self]
    push_cast
    ring
  · rcases Nat.lt_or_ge j t with hlt | hge
    · rw [show (k - t).choose (k - j) = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      ring
    · rw [show t.choose j = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      ring

end ECCLib.Delsarte

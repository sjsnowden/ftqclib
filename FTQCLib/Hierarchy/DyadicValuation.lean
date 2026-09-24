/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.EffectiveLevel

/-!
# The top bit and the dyadic valuation of `ZMod (2^m)`

The arithmetic of the top bit `2^{m−1}` of the ring `ZMod (2^m)`, and the 2-adic valuation of a
power of two, stated once at the layer of the level function. Every fact here is about the ring
alone. The frame modules that first proved them (`HadamardRaise`, `HadamardElimination`) and the
Möbius tower (`MobiusProductTower`) import this module; the polar form of a diagonal exponent
(`PolarForm`) reads its coefficient arithmetic from here.

## Main results

* `two_pow_pred_mul_two` — `2^{m−1} · 2 = 0` (at `m = 0` the ring is trivial).
* `two_pow_pred_ne_zero` — `2^{m−1} ≠ 0` at positive precision.
* `exists_bit_of_two_mul_eq_zero` — a residue killed by `2` is the top bit times a bit.
* `two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero` — `4c = 0` puts `2c` on the top-bit lattice.
* `DiagPhase.twoAdicVal_pow_two` — the valuation of `2^a` is `min m a`.

## Implementation notes

The statements are the ones the frame layer proved; the proofs are carried over unchanged. The
`4c = 0` dichotomy is the coefficient arithmetic of a degree-one monomial at level two: its
coefficient is a multiple of `2^{m−2}`, so twice it is `0` or the top bit.
-/

namespace FTQCLib.Hierarchy

/-- The dyadic key: `2^{m−1} · 2 = 0` in `ZMod (2^m)` (at `m = 0` the ring is trivial). -/
theorem two_pow_pred_mul_two {m : ℕ} : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : Subsingleton (ZMod (2 ^ 0)) := by
      rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  · have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 2 ^ m := by
      rw [← pow_succ]
      congr 1
      omega
    have h0 : ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_pow, Nat.cast_ofNat] at h0
    rw [h2, h0]

/-- `2^{m−1}` is not `0` at positive precision. -/
theorem two_pow_pred_ne_zero {m : ℕ} (hm : 1 ≤ m) : (2 : ZMod (2 ^ m)) ^ (m - 1) ≠ 0 := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  intro h
  have h1 : ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = 0 := by exact_mod_cast h
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 ^ (m - 1) : ℕ) : ℤ) (2 ^ m)).mp
    (by rw [Int.cast_natCast]; exact h1)
  have h3 : 2 ^ m ∣ 2 ^ (m - 1) := by exact_mod_cast h2
  have h4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h3
  omega

/-- A residue killed by `2` is `2^{m−1}` times a bit. -/
theorem exists_bit_of_two_mul_eq_zero {m : ℕ} (hm : 1 ≤ m) {κ : ZMod (2 ^ m)}
    (hκ : 2 * κ = 0) :
    ∃ ε : ZMod 2, κ = (2 : ZMod (2 ^ m)) ^ (m - 1) * ((ε.val : ℕ) : ZMod (2 ^ m)) := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  have h1 : ((2 * κ.val : ℕ) : ZMod (2 ^ m)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact_mod_cast hκ
  have h2 : 2 ^ m ∣ 2 * κ.val := by
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 * κ.val : ℕ) : ℤ) (2 ^ m)).mp
      (by rw [Int.cast_natCast]; exact h1)
    exact_mod_cast h3
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  have h2' : 2 * 2 ^ (m - 1) ∣ 2 * κ.val := by rwa [← hpow]
  obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left two_pos h2'
  have hlt : κ.val < 2 * 2 ^ (m - 1) := by
    rw [← hpow]
    exact ZMod.val_lt κ
  rw [hj, mul_comm (2 : ℕ)] at hlt
  have hj2 : j < 2 := Nat.lt_of_mul_lt_mul_left hlt
  have hκv : κ = ((κ.val : ℕ) : ZMod (2 ^ m)) := (ZMod.natCast_zmod_val κ).symm
  interval_cases j
  · exact ⟨0, by rw [hκv, hj]; simp⟩
  · refine ⟨1, ?_⟩
    rw [hκv, hj, show ((1 : ZMod 2).val : ℕ) = 1 by decide]
    push_cast
    ring

/-- `4c = 0` puts `2c` on the top-bit lattice: `2c = 0` or `2c = 2^{m−1}`. This is the coefficient
arithmetic of a degree-one monomial at level two. -/
theorem two_mul_eq_zero_or_two_pow_pred_of_four_mul_eq_zero {m : ℕ} {c : ZMod (2 ^ m)}
    (hc : 4 * c = 0) : 2 * c = 0 ∨ 2 * c = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : Subsingleton (ZMod (2 ^ 0)) := by
      rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
    exact Or.inl (Subsingleton.elim _ _)
  · have h2 : 2 * (2 * c) = 0 := by
      rw [← mul_assoc, show (2 : ZMod (2 ^ m)) * 2 = 4 by norm_num]
      exact hc
    obtain ⟨ε, hε⟩ := exists_bit_of_two_mul_eq_zero hm h2
    have hv : ε.val = 0 ∨ ε.val = 1 := by
      have := ZMod.val_lt ε
      omega
    rcases hv with h | h
    · left
      rw [hε, h]
      simp
    · right
      rw [hε, h]
      simp

namespace DiagPhase

/-- `2^a = 0` in `ZMod (2^m)` once `a ≥ m`. -/
lemma pow_two_eq_zero_of_ge {m a : ℕ} (h : m ≤ a) : (2 : ZMod (2 ^ m)) ^ a = 0 := by
  have hcast : (2 : ZMod (2 ^ m)) ^ a = ((2 ^ a : ℕ) : ZMod (2 ^ m)) := by push_cast; ring
  rw [hcast, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow 2 h

/-- **The valuation of a power of two:** `twoAdicVal (2^a) = min m a` in `ZMod (2^m)`. -/
lemma twoAdicVal_pow_two {m : ℕ} (a : ℕ) :
    twoAdicVal ((2 : ZMod (2 ^ m)) ^ a) = min m a := by
  rcases Nat.lt_or_ge a m with hlt | hge
  · haveI : NeZero (2 ^ m) := ⟨(pow_pos (by norm_num : (0 : ℕ) < 2) m).ne'⟩
    have hcast : (2 : ZMod (2 ^ m)) ^ a = ((2 ^ a : ℕ) : ZMod (2 ^ m)) := by push_cast; ring
    have hval : ((2 ^ a : ℕ) : ZMod (2 ^ m)).val = 2 ^ a := by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hlt)
    have hne : (2 : ZMod (2 ^ m)) ^ a ≠ 0 := by
      rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hle := Nat.le_of_dvd (pow_pos (by norm_num) a) hdvd
      have hlt2 : (2 : ℕ) ^ a < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hlt
      omega
    have hdvd1 : 2 ^ a ∣ ((2 : ZMod (2 ^ m)) ^ a).val := by
      rw [hcast, hval]
    have h1 : a ≤ twoAdicVal ((2 : ZMod (2 ^ m)) ^ a) := (pow_dvd_val_iff hne a).mp hdvd1
    have h2 : ¬ (a + 1 ≤ twoAdicVal ((2 : ZMod (2 ^ m)) ^ a)) := by
      intro hle
      have hdvd2 := (pow_dvd_val_iff hne (a + 1)).mpr hle
      rw [hcast, hval] at hdvd2
      have hle2 := Nat.le_of_dvd (pow_pos (by norm_num) a) hdvd2
      have hlt2 : (2 : ℕ) ^ a < 2 ^ (a + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    omega
  · rw [pow_two_eq_zero_of_ge hge, twoAdicVal_zero]
    omega

end DiagPhase

end FTQCLib.Hierarchy

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle
import FTQCLib.Examples.HadamardCharSumFrame
import FTQCLib.Examples.HadamardRaise
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The dyadic character of the frame's exponent

The frame's exponent takes values in `ZMod (2^m)` and reaches `ℂ` through one character,
`charOf m z = exp(i·2π·z.val/2^m)`; `exp(i·realPhase P v)` is `charOf m (eval P v)` by definition
(`exp_realPhase_eq_charOf`). The tree so far used the character only as an inline expression
(`expChar_add`, `exp_realPhase_add`). Two facts about it carry the floor stratum's theorems:

* **injectivity** (`charOf_injective`) — the character is a power of the primitive `2^m`-th root of
  unity `zeta m`, and distinct residues give distinct powers; this is how an equation between
  amplitudes in `ℂ` becomes an equation between exponents in `ZMod (2^m)`;
* **the sign** (`charOf_two_pow_mul`) — at `1 ≤ m` the residue `2^{m−1}·t` is sent to `(−1)^t`,
  which is how the Pauli action's sign `(−1)^{Z·w}` reads as an exponent shift.

The arithmetic of the top bit `2^{m−1}` in `ZMod (2^m)` is collected here too: multiplying by it
reads only the parity of a natural number (`two_pow_pred_mul_natCast_mod`,
`two_pow_pred_mul_eq_of_cast_eq`), and `zDot` is additive in the word modulo two
(`zDot_cast_two_add_right`).

Everything here is frame-pure. No `FTQCLib.Hilbert`.

## Main definitions

* `charOf` — the dyadic character at precision `m`.
* `zeta` — the primitive `2^m`-th root of unity it is a power of.

## Main results

* `charOf_injective`, `charOf_add`, `charOf_two_pow_mul`, `exp_realPhase_eq_charOf`.
* `charOf_two_pow_sub_two_mul` — the quarter turn: `2^{m−2}·t ↦ i^t` at `2 ≤ m`.
* `one_add_charOf_two_pow_pred`, `one_add_charOf_rotate`, `one_add_charOf_ne_zero` — the two
  branch pairs of bound-bit elimination, collapse and rotate, as identities of the character.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy

/-! ## The character -/

/-- The dyadic character at precision `m`: `z ↦ exp(i·2π·z.val/2^m)`. -/
noncomputable def charOf (m : ℕ) (z : ZMod (2 ^ m)) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * (z.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ))

/-- `exp(i·realPhase P v)` is the character at the exponent's value. -/
theorem exp_realPhase_eq_charOf {N m : ℕ} (P : DiagPhase N m) (v : Fin N → ZMod 2) :
    Complex.exp (Complex.I * (DiagPhase.realPhase P v : ℂ)) = charOf m (DiagPhase.eval P v) := rfl

/-- The character is multiplicative. -/
theorem charOf_add (m : ℕ) (z₁ z₂ : ZMod (2 ^ m)) :
    charOf m (z₁ + z₂) = charOf m z₁ * charOf m z₂ :=
  expChar_add z₁ z₂

/-- The character of `0` is `1`. -/
theorem charOf_zero (m : ℕ) : charOf m 0 = 1 := by
  unfold charOf
  simp

/-- The character never vanishes. -/
theorem charOf_ne_zero (m : ℕ) (z : ZMod (2 ^ m)) : charOf m z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The character of a difference, multiplied back. -/
theorem charOf_sub_mul (m : ℕ) (a b : ZMod (2 ^ m)) :
    charOf m (a - b) * charOf m b = charOf m a := by
  rw [← charOf_add, sub_add_cancel]

/-! ## The primitive root -/

/-- The primitive `2^m`-th root of unity `exp(i·2π/2^m)`. -/
noncomputable def zeta (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi / (2 : ℝ) ^ m : ℝ) : ℂ))

/-- The character is a power of `zeta`. -/
theorem charOf_eq_zeta_pow (m : ℕ) (z : ZMod (2 ^ m)) : charOf m z = zeta m ^ z.val := by
  unfold charOf zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `zeta` in Mathlib's normal form. -/
theorem zeta_eq_exp (m : ℕ) :
    zeta m = Complex.exp (2 * Real.pi * Complex.I / ((2 ^ m : ℕ) : ℂ)) := by
  unfold zeta
  congr 1
  push_cast
  ring

/-- `zeta m` is a primitive `2^m`-th root of unity. -/
theorem isPrimitiveRoot_zeta (m : ℕ) : IsPrimitiveRoot (zeta m) (2 ^ m) := by
  rw [zeta_eq_exp]
  exact Complex.isPrimitiveRoot_exp (2 ^ m) (by positivity)

/-- Powers of `zeta` are read modulo `2^m`. -/
theorem zeta_pow_mod (m : ℕ) (a : ℕ) : zeta m ^ (a % 2 ^ m) = zeta m ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a (2 ^ m), pow_add, pow_mul,
    (isPrimitiveRoot_zeta m).pow_eq_one, one_pow, one_mul]

/-- **Injectivity.** Distinct exponents have distinct characters. -/
theorem charOf_injective (m : ℕ) : Function.Injective (charOf m) := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0 : ℕ) < 2 ^ m).ne'⟩
  intro z₁ z₂ h
  rw [charOf_eq_zeta_pow, charOf_eq_zeta_pow] at h
  exact ZMod.val_injective _
    ((isPrimitiveRoot_zeta m).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)

/-- Equal characters, equal exponents. -/
theorem charOf_eq_iff (m : ℕ) (z₁ z₂ : ZMod (2 ^ m)) : charOf m z₁ = charOf m z₂ ↔ z₁ = z₂ :=
  (charOf_injective m).eq_iff

/-! ## The top bit is the sign -/

/-- `zeta` to the power `2^{m−1}` is `−1`. -/
theorem zeta_pow_two_pow_pred {m : ℕ} (hm : 1 ≤ m) : zeta m ^ (2 ^ (m - 1)) = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  unfold zeta
  rw [← Complex.exp_nat_mul]
  rw [show ((2 ^ (k + 1 - 1) : ℕ) : ℂ) * (Complex.I * ((2 * Real.pi / (2 : ℝ) ^ (k + 1) : ℝ) : ℂ))
      = Real.pi * Complex.I from ?_]
  · exact Complex.exp_pi_mul_I
  · rw [Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    field_simp

/-- **The sign.** At `1 ≤ m` the residue `2^{m−1}·t` has character `(−1)^t`. -/
theorem charOf_two_pow_mul {m : ℕ} (hm : 1 ≤ m) (t : ℕ) :
    charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1) * (t : ZMod (2 ^ m))) = (-1) ^ t := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0 : ℕ) < 2 ^ m).ne'⟩
  have hcast : (2 : ZMod (2 ^ m)) ^ (m - 1) * (t : ZMod (2 ^ m))
      = ((2 ^ (m - 1) * t : ℕ) : ZMod (2 ^ m)) := by
    push_cast
    ring
  rw [hcast, charOf_eq_zeta_pow, ZMod.val_natCast, zeta_pow_mod, pow_mul,
    zeta_pow_two_pow_pred hm]

/-! ## The top bit reads parity

`two_pow_pred_mul_two` (`HadamardRaise.lean`): `2^{m−1} · 2 = 0` in `ZMod (2^m)`, at every `m`
(the ring is trivial at `m = 0`). The two lemmas below need no hypothesis for the same reason. -/

/-- Multiplying by the top bit reads only the parity of a natural number. -/
theorem two_pow_pred_mul_natCast_mod {m : ℕ} (a : ℕ) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * (a : ZMod (2 ^ m))
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * ((a % 2 : ℕ) : ZMod (2 ^ m)) := by
  conv_lhs => rw [← Nat.div_add_mod a 2]
  push_cast
  rw [mul_add, ← mul_assoc, two_pow_pred_mul_two, zero_mul, zero_add]

/-- Equal parities, equal top-bit multiples. -/
theorem two_pow_pred_mul_eq_of_cast_eq {m : ℕ} {a b : ℕ} (h : (a : ZMod 2) = (b : ZMod 2)) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * (a : ZMod (2 ^ m))
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * (b : ZMod (2 ^ m)) := by
  rw [two_pow_pred_mul_natCast_mod a, two_pow_pred_mul_natCast_mod b,
    (ZMod.natCast_eq_natCast_iff' a b 2).mp h]

/-- Equal parities, equal signs. -/
theorem neg_one_pow_eq_of_cast_eq {a b : ℕ} (h : (a : ZMod 2) = (b : ZMod 2)) :
    (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    (ZMod.natCast_eq_natCast_iff' a b 2).mp h]
  simp

/-- `zDot` is additive in the word, modulo two. -/
theorem zDot_cast_two_add_right (g : Pauli n) (v w : Fin n → ZMod 2) :
    ((zDot g (v + w) : ℕ) : ZMod 2) = ((zDot g v : ℕ) : ZMod 2) + ((zDot g w : ℕ) : ZMod 2) := by
  rw [zDot_cast_two, zDot_cast_two, zDot_cast_two]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## The quarter turn

One level below the top bit: at `2 ≤ m` the residue `2^{m−2}` has character `i`. This is the scalar
of the rotate branch of bound-bit elimination, where a difference `a` with `2a = 2^{m−1}` splits a
branch pair into one scale `1 + charOf a` times one linear phase (`one_add_charOf_rotate`); the
collapse branch's pair adds to `2` or `0` (`one_add_charOf_two_pow_pred`). -/

/-- `zeta` to the power `2^{m−2}` is `i`. -/
theorem zeta_pow_two_pow_sub_two {m : ℕ} (hm : 2 ≤ m) : zeta m ^ (2 ^ (m - 2)) = Complex.I := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have h2 : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 2) * 4 := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_add]
    norm_num
  have hpow : ((2 ^ (m - 2) : ℕ) : ℂ) * (Complex.I * ((2 * Real.pi / (2 : ℝ) ^ m : ℝ) : ℂ))
      = Complex.I * ((Real.pi / 2 : ℂ)) := by
    rw [h2]
    push_cast
    have hne' : ((2 : ℂ) ^ (m - 2)) ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    ring
  rw [hpow, mul_comm, Complex.exp_mul_I]
  simp

/-- **The quarter turn.** At `2 ≤ m` the residue `2^{m−2}·t` has character `i^t`. -/
theorem charOf_two_pow_sub_two_mul {m : ℕ} (hm : 2 ≤ m) (t : ℕ) :
    charOf m ((2 : ZMod (2 ^ m)) ^ (m - 2) * (t : ZMod (2 ^ m))) = Complex.I ^ t := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0 : ℕ) < 2 ^ m).ne'⟩
  have hcast : (2 : ZMod (2 ^ m)) ^ (m - 2) * (t : ZMod (2 ^ m))
      = ((2 ^ (m - 2) * t : ℕ) : ZMod (2 ^ m)) := by
    push_cast
    ring
  rw [hcast, charOf_eq_zeta_pow, ZMod.val_natCast, zeta_pow_mod, pow_mul,
    zeta_pow_two_pow_sub_two hm]

/-- **The collapse pair.** The two branches of a bit whose difference is `2^{m−1}·b` add to `2`
when `b = 0` and to `0` when `b = 1`. -/
theorem one_add_charOf_two_pow_pred {m : ℕ} (hm : 1 ≤ m) (b : ZMod 2) :
    1 + charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1) * ((b.val : ℕ) : ZMod (2 ^ m)))
      = if b = 0 then 2 else 0 := by
  rw [charOf_two_pow_mul hm]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · rw [if_pos rfl, ZMod.val_zero, pow_zero]
    norm_num
  · rw [if_neg (by decide), show ((1 : ZMod 2)).val = 1 from by decide, pow_one]
    ring

/-- A rotate constant is odd against the top bit: `charOf (−a) = −charOf a` when
`2a = 2^{m−1}`. -/
theorem charOf_neg_of_two_mul_eq {m : ℕ} (hm : 1 ≤ m) {a : ZMod (2 ^ m)}
    (ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1)) :
    charOf m (-a) = - charOf m a := by
  have hsplit : (-a) = a + (-(2 * a)) := by ring
  have htop : (-(2 * a)) = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
    rw [ha]
    have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) + (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
      have := two_pow_pred_mul_two (m := m)
      linear_combination this
    linear_combination -h2
  have hchi : charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
    have h := charOf_two_pow_mul (m := m) hm 1
    simpa using h
  rw [hsplit, charOf_add, htop, hchi]
  ring

/-- **The rotate pair.** With `2a = 2^{m−1}`, the two branches of a bit whose difference is
`a + 2^{m−1}·b` recombine into one scale times one linear phase. -/
theorem one_add_charOf_rotate {m : ℕ} (hm : 1 ≤ m) {a : ZMod (2 ^ m)}
    (ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1)) (b : ZMod 2) :
    1 + charOf m (a + (2 : ZMod (2 ^ m)) ^ (m - 1) * ((b.val : ℕ) : ZMod (2 ^ m)))
      = (1 + charOf m a) * charOf m (-a * ((b.val : ℕ) : ZMod (2 ^ m))) := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · rw [ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero, mul_zero, charOf_zero, mul_one]
  · rw [show ((1 : ZMod 2)).val = 1 from by decide, Nat.cast_one, mul_one, mul_one,
      charOf_add, charOf_neg_of_two_mul_eq hm ha]
    have h1 : charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
      have h := charOf_two_pow_mul (m := m) hm 1
      simpa using h
    have hsq : charOf m a * charOf m a = -1 := by
      rw [← charOf_add, show a + a = 2 * a from by ring, ha, h1]
    rw [h1]
    linear_combination hsq

/-- The rotate scale is nonzero: `1 + charOf a = 0` forces `a = 2^{m−1}`, which `2a = 2^{m−1}`
excludes at `1 ≤ m`. -/
theorem one_add_charOf_ne_zero {m : ℕ} (hm : 1 ≤ m) {a : ZMod (2 ^ m)}
    (ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1)) : 1 + charOf m a ≠ 0 := by
  intro hc
  have hchi : charOf m a = charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) := by
    have h := charOf_two_pow_mul (m := m) hm 1
    rw [show ((1 : ℕ) : ZMod (2 ^ m)) = 1 from by push_cast; ring, mul_one] at h
    rw [h]
    linear_combination hc
  have ha' : a = (2 : ZMod (2 ^ m)) ^ (m - 1) := charOf_injective m hchi
  rw [ha'] at ha
  have hz : (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
    have h2 := two_pow_pred_mul_two (m := m)
    calc (2 : ZMod (2 ^ m)) ^ (m - 1) = 2 * (2 : ZMod (2 ^ m)) ^ (m - 1) := ha.symm
      _ = (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 := by ring
      _ = 0 := h2
  have hne : charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
    have h := charOf_two_pow_mul (m := m) hm 1
    simpa using h
  rw [hz, charOf_zero] at hne
  exact absurd hne (by norm_num)

end FTQCLib.Frame.Walkthrough

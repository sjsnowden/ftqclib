/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardElimination

/-!
# The residual class has no height-zero presentation

The eliminating H returns a Hadamard to height zero when the adjoined bit's difference is
collapse- or rotate-shaped on the support. This module names the third cell of the value-set
trichotomy: there the adjoined bit is a value at height one whose modulus varies over its support,
so **no height-zero record presents such an output**: a fact about the state, which the record at
height one reports exactly. Two obstructions are stated, each general:

* **modulus** — a height-zero record has constant modulus on its support
  (`normSq_amp_ofKernelState`), so a function with two nonzero values of different modulus is no
  height-zero record (`not_exists_kernelState_of_two_moduli`);
* **support** — a height-zero record's support is a coset, closed under `w + w' + w''`
  (`support_ofKernelState_add_add`), so a function with three nonzero words whose sum is a zero word
  is no height-zero record (`not_exists_kernelState_of_not_affine`).

The **`e_k` pairing** (`walsh_ofKernelState_pair`) computes the Walsh transform of a height-zero
record at a pair `u, u + e_k` on the support: the scale times the character at `u` times
`1 ± charOf Δ`, where `Δ` is the exponent's difference along `e_k`. A residual value — `2Δ ≠ 0`
(not collapse) and `2Δ ≠ 2^{m−1}` (not rotate) — makes the two moduli nonzero and different
(`normSq_pair_ne_of_residual`), and the theorem follows
(`not_exists_kernelState_walsh_of_residual`).

## Main results

* `not_exists_kernelState_of_two_moduli`, `not_exists_kernelState_of_not_affine` — the two general
  obstructions to a height-zero presentation.
* `walsh_ofKernelState_pair` — the `e_k` pairing.
* `charOf_residual`, `normSq_pair_ne_of_residual` — a residual value separates the pair's moduli.
* `not_exists_kernelState_walsh_of_residual`, `not_exists_kernelState_applyHFiner_of_residual` — the
  residual theorem, for the Walsh transform and for the free rule's output.

Everything here is frame-pure. No `FTQCLib.Hilbert`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The modulus obstruction -/

/-- The character has modulus one. -/
theorem normSq_charOf (m : ℕ) (z : ZMod (2 ^ m)) : Complex.normSq (charOf m z) = 1 :=
  normSq_exp_I_real _

/-- A height-zero record has constant modulus on its support. -/
theorem normSq_amp_ofKernelState (K : KernelState n) {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ K.L, w = K.x₀ + p.X) :
    Complex.normSq (amp (ofKernelState K) w) = Complex.normSq K.c := by
  rw [amp_ofKernelState_pos K hw, Complex.normSq_mul, normSq_charOf, mul_one]

/-- A nonzero value of a height-zero record is on its support. -/
theorem support_of_amp_ne_zero (K : KernelState n) {w : Fin n → ZMod 2}
    (hw : amp (ofKernelState K) w ≠ 0) : ∃ p ∈ K.L, w = K.x₀ + p.X := by
  by_contra h
  exact hw (amp_ofKernelState_neg K h)

/-- **The modulus obstruction.** A function with two nonzero values of different modulus is the
amplitude of no height-zero record. -/
theorem not_exists_kernelState_of_two_moduli {f : (Fin n → ZMod 2) → ℂ} {w w' : Fin n → ZMod 2}
    (hw : f w ≠ 0) (hw' : f w' ≠ 0) (hne : Complex.normSq (f w) ≠ Complex.normSq (f w')) :
    ¬ ∃ T : KernelState n, amp (ofKernelState T) = f := by
  rintro ⟨T, rfl⟩
  rw [normSq_amp_ofKernelState T (support_of_amp_ne_zero T hw),
    normSq_amp_ofKernelState T (support_of_amp_ne_zero T hw')] at hne
  exact hne rfl

/-! ## The support obstruction -/

/-- A height-zero record's support is a coset: three support words sum to a support word. -/
theorem support_ofKernelState_add_add (K : KernelState n) {w w' w'' : Fin n → ZMod 2}
    (h : ∃ p ∈ K.L, w = K.x₀ + p.X) (h' : ∃ p ∈ K.L, w' = K.x₀ + p.X)
    (h'' : ∃ p ∈ K.L, w'' = K.x₀ + p.X) : ∃ p ∈ K.L, w + w' + w'' = K.x₀ + p.X := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨p', hp', rfl⟩ := h'
  obtain ⟨p'', hp'', rfl⟩ := h''
  refine ⟨p + p' + p'', Submodule.add_mem _ (Submodule.add_mem _ hp hp') hp'', ?_⟩
  rw [X_add, X_add]
  have hre : K.x₀ + p.X + (K.x₀ + p'.X) + (K.x₀ + p''.X) =
      (K.x₀ + K.x₀) + (K.x₀ + (p.X + p'.X + p''.X)) := by abel
  rw [hre, add_self_word, zero_add]

/-- **The support obstruction.** A function with three nonzero words whose sum is a zero word is
the amplitude of no height-zero record. -/
theorem not_exists_kernelState_of_not_affine {f : (Fin n → ZMod 2) → ℂ}
    {w w' w'' : Fin n → ZMod 2} (hw : f w ≠ 0) (hw' : f w' ≠ 0) (hw'' : f w'' ≠ 0)
    (hsum : f (w + w' + w'') = 0) : ¬ ∃ T : KernelState n, amp (ofKernelState T) = f := by
  rintro ⟨T, rfl⟩
  have hc : T.c ≠ 0 := by
    rw [amp_ofKernelState_pos T (support_of_amp_ne_zero T hw)] at hw
    exact left_ne_zero_of_mul hw
  rw [amp_ofKernelState_pos T (support_ofKernelState_add_add T (support_of_amp_ne_zero T hw)
    (support_of_amp_ne_zero T hw') (support_of_amp_ne_zero T hw''))] at hsum
  exact mul_ne_zero hc (charOf_ne_zero _ _) hsum

/-! ## The `e_k` pairing -/

/-- Updating a word at a bit where it is `0`. -/
theorem update_zero_of_apply_zero {u : Fin n → ZMod 2} {k : Fin n} (huk : u k = 0) :
    Function.update u k 0 = u := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self, huk]
  · rw [Function.update_of_ne hj]

/-- Updating a word at a bit where it is `0` to `1` adds the unit word. -/
theorem update_one_of_apply_zero {u : Fin n → ZMod 2} {k : Fin n} (huk : u k = 0) :
    Function.update u k 1 = u + Pi.single k 1 := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self, Pi.add_apply, huk, Pi.single_eq_same, zero_add]
  · rw [Function.update_of_ne hj, Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]

/-- The pair's second word reads `1` at the bit. -/
theorem add_single_apply_self {u : Fin n → ZMod 2} {k : Fin n} (huk : u k = 0) :
    (u + Pi.single k 1 : Fin n → ZMod 2) k = 1 := by
  rw [Pi.add_apply, huk, Pi.single_eq_same, zero_add]

/-- Updating the pair's second word at the bit. -/
theorem update_add_single_zero {u : Fin n → ZMod 2} {k : Fin n} (huk : u k = 0) :
    Function.update (u + Pi.single k 1) k 0 = u := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self, huk]
  · rw [Function.update_of_ne hj, Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]

theorem update_add_single_one {u : Fin n → ZMod 2} {k : Fin n} (huk : u k = 0) :
    Function.update (u + Pi.single k 1) k 1 = u + Pi.single k 1 := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self, add_single_apply_self huk]
  · rw [Function.update_of_ne hj]

/-- `signOf 0 = 1`. -/
theorem signOf_zero : signOf 0 = 1 := if_pos rfl

/-- `signOf 1 = −1`. -/
theorem signOf_one : signOf 1 = -1 := if_neg one_ne_zero

/-- **The `e_k` pairing.** At a pair `u, u + e_k` on the support (`u k = 0`), the Walsh transform of
a height-zero record is the scale times the character at `u` times `1 ± charOf Δ`, where `Δ` is the
exponent's difference along `e_k`. -/
theorem walsh_ofKernelState_pair (K : KernelState n) (k : Fin n) {u : Fin n → ZMod 2}
    (huk : u k = 0) (hu : ∃ p ∈ K.L, u = K.x₀ + p.X)
    (hu' : ∃ p ∈ K.L, u + Pi.single k 1 = K.x₀ + p.X) :
    walshTransform k (amp (ofKernelState K)) u =
        (1 / (Real.sqrt 2 : ℂ)) * (K.c * charOf K.m (DiagPhase.eval K.q u)) *
          (1 + charOf K.m (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u)) ∧
      walshTransform k (amp (ofKernelState K)) (u + Pi.single k 1) =
        (1 / (Real.sqrt 2 : ℂ)) * (K.c * charOf K.m (DiagPhase.eval K.q u)) *
          (1 - charOf K.m (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u)) := by
  constructor
  · unfold walshTransform
    rw [update_zero_of_apply_zero huk, update_one_of_apply_zero huk, huk, signOf_zero,
      amp_ofKernelState_pos K hu, amp_ofKernelState_pos K hu',
      ← charOf_sub_mul K.m (DiagPhase.eval K.q (u + Pi.single k 1)) (DiagPhase.eval K.q u)]
    ring
  · unfold walshTransform
    rw [update_add_single_zero huk, update_add_single_one huk, add_single_apply_self huk,
      signOf_one, amp_ofKernelState_pos K hu, amp_ofKernelState_pos K hu',
      ← charOf_sub_mul K.m (DiagPhase.eval K.q (u + Pi.single k 1)) (DiagPhase.eval K.q u)]
    ring

/-! ## The residual value -/

/-- The moduli of `1 + z` and `1 − z` for a unit `z`. -/
theorem normSq_one_add_of_normSq_one {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.normSq (1 + z) = 2 + 2 * z.re := by
  rw [Complex.normSq_add, Complex.normSq_one, hz, one_mul, Complex.conj_re]
  ring

theorem normSq_one_sub_of_normSq_one {z : ℂ} (hz : Complex.normSq z = 1) :
    Complex.normSq (1 - z) = 2 - 2 * z.re := by
  rw [Complex.normSq_sub, Complex.normSq_one, hz, one_mul, Complex.conj_re]
  ring

/-- A unit `z` with `z.re = 0` squares to `−1`. -/
theorem mul_self_eq_neg_one_of_re_zero {z : ℂ} (hz : Complex.normSq z = 1) (hre : z.re = 0) :
    z * z = -1 := by
  rw [Complex.normSq_apply, hre, mul_zero, zero_add] at hz
  apply Complex.ext
  · simp only [Complex.mul_re, hre, mul_zero, zero_sub, Complex.neg_re, Complex.one_re]
    linear_combination -hz
  · simp only [Complex.mul_im, hre, mul_zero, zero_mul, add_zero, Complex.neg_im, Complex.one_im,
      neg_zero]

/-- **A residual value separates the pair's moduli.** For `2Δ ≠ 0` and `2Δ ≠ 2^{m−1}`, the
character `z = charOf Δ` has `1 + z ≠ 0`, `1 − z ≠ 0` and `z.re ≠ 0`. -/
theorem charOf_residual {m : ℕ} (hm : 1 ≤ m) {Δ : ZMod (2 ^ m)} (h0 : 2 * Δ ≠ 0)
    (h1 : 2 * Δ ≠ (2 : ZMod (2 ^ m)) ^ (m - 1)) :
    1 + charOf m Δ ≠ 0 ∧ 1 - charOf m Δ ≠ 0 ∧ (charOf m Δ).re ≠ 0 := by
  have hsq : charOf m Δ * charOf m Δ = charOf m (2 * Δ) := by
    rw [two_mul, charOf_add]
  have hnorm : Complex.normSq (charOf m Δ) = 1 := normSq_charOf m Δ
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hz : charOf m Δ = -1 := by linear_combination h
    apply h0
    apply charOf_injective m
    rw [← hsq, hz, charOf_zero]
    ring
  · intro h
    have hz : charOf m Δ = 1 := by linear_combination -h
    apply h0
    apply charOf_injective m
    rw [← hsq, hz, charOf_zero, one_mul]
  · intro hre
    apply h1
    apply charOf_injective m
    rw [← hsq, mul_self_eq_neg_one_of_re_zero hnorm hre]
    have := charOf_two_pow_mul hm 1
    rw [Nat.cast_one, mul_one, pow_one] at this
    exact this.symm

/-- The two moduli at a residual pair are nonzero and different. -/
theorem normSq_pair_ne_of_residual (K : KernelState n) (hm : 1 ≤ K.m) (hc : K.c ≠ 0) (k : Fin n)
    {u : Fin n → ZMod 2} (huk : u k = 0) (hu : ∃ p ∈ K.L, u = K.x₀ + p.X)
    (hu' : ∃ p ∈ K.L, u + Pi.single k 1 = K.x₀ + p.X)
    (h0 : 2 * (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u) ≠ 0)
    (h1 : 2 * (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u) ≠
      (2 : ZMod (2 ^ K.m)) ^ (K.m - 1)) :
    walshTransform k (amp (ofKernelState K)) u ≠ 0 ∧
      walshTransform k (amp (ofKernelState K)) (u + Pi.single k 1) ≠ 0 ∧
      Complex.normSq (walshTransform k (amp (ofKernelState K)) u) ≠
        Complex.normSq (walshTransform k (amp (ofKernelState K)) (u + Pi.single k 1)) := by
  obtain ⟨e0, e1⟩ := walsh_ofKernelState_pair K k huk hu hu'
  obtain ⟨hz1, hz1', hzre⟩ := charOf_residual hm h0 h1
  set A : ℂ := (1 / (Real.sqrt 2 : ℂ)) * (K.c * charOf K.m (DiagPhase.eval K.q u)) with hAdef
  have hA : A ≠ 0 := by
    refine mul_ne_zero ?_ (mul_ne_zero hc (charOf_ne_zero _ _))
    exact one_div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos))
  refine ⟨by rw [e0]; exact mul_ne_zero hA hz1, by rw [e1]; exact mul_ne_zero hA hz1', ?_⟩
  rw [e0, e1, Complex.normSq_mul A, Complex.normSq_mul A]
  intro h
  have hA' : Complex.normSq A ≠ 0 := (Complex.normSq_pos.mpr hA).ne'
  have h' := mul_left_cancel₀ hA' h
  rw [normSq_one_add_of_normSq_one (normSq_charOf _ _),
    normSq_one_sub_of_normSq_one (normSq_charOf _ _)] at h'
  exact hzre (by linarith)

/-- **The residual theorem.** At a residual pair `u, u + e_k` of a height-zero record — the
exponent's difference along `e_k` has `2Δ ≠ 0` (not collapse) and `2Δ ≠ 2^{m−1}` (not rotate) —
the Walsh transform of its amplitude is the amplitude of no height-zero record. -/
theorem not_exists_kernelState_walsh_of_residual (K : KernelState n) (hm : 1 ≤ K.m) (hc : K.c ≠ 0)
    (k : Fin n) {u : Fin n → ZMod 2} (huk : u k = 0) (hu : ∃ p ∈ K.L, u = K.x₀ + p.X)
    (hu' : ∃ p ∈ K.L, u + Pi.single k 1 = K.x₀ + p.X)
    (h0 : 2 * (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u) ≠ 0)
    (h1 : 2 * (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u) ≠
      (2 : ZMod (2 ^ K.m)) ^ (K.m - 1)) :
    ¬ ∃ T : KernelState n, amp (ofKernelState T) = walshTransform k (amp (ofKernelState K)) := by
  obtain ⟨hne0, hne1, hne⟩ := normSq_pair_ne_of_residual K hm hc k huk hu hu' h0 h1
  exact not_exists_kernelState_of_two_moduli hne0 hne1 hne

/-- The same, for the free rule's output: at a residual pair, `applyHFiner` has no height-zero
presentation. -/
theorem not_exists_kernelState_applyHFiner_of_residual (K : KernelState n) (hm : 1 ≤ K.m)
    (hc : K.c ≠ 0) (k : Fin n) (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj K.L)
    {u : Fin n → ZMod 2} (huk : u k = 0) (hu : ∃ p ∈ K.L, u = K.x₀ + p.X)
    (hu' : ∃ p ∈ K.L, u + Pi.single k 1 = K.x₀ + p.X)
    (h0 : 2 * (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u) ≠ 0)
    (h1 : 2 * (DiagPhase.eval K.q (u + Pi.single k 1) - DiagPhase.eval K.q u) ≠
      (2 : ZMod (2 ^ K.m)) ^ (K.m - 1)) :
    ¬ ∃ T : KernelState n, amp (ofKernelState T) = amp (applyHFiner k (ofKernelState K)) := by
  rw [amp_applyHFiner k (ofKernelState K) hm hk]
  exact not_exists_kernelState_walsh_of_residual K hm hc k huk hu hu' h0 h1

end FTQCLib.Frame.Walkthrough

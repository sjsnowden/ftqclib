/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardPhase

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # Frame-pure character-sum branch algebra

The `2^m`-th-root character multiplicativity (`expChar_add`, `exp_realPhase_add`), the freeze / append /
coupling evaluation lemmas, and the **branch-evaluation identity** `hBranch_eval`
(`ampCore (hBranch k p Q) w = (-1)^{p·w_k}·ampCore Q (w[k←p])`) — all frame-pure (`DiagPhase` / `realPhase` /
`ℂ` only, importing no `FTQCLib.Hilbert`). Relocated here from `FTQCLib/Hilbert/HadamardCharSumBridge.lean` so both
the Hilbert bridge and the frame-native Gauss-sum pairing (`FTQCLib/Examples/CharSumPairing.lean`) share them
without either importing the other. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Hierarchy Complex

/-! ## The `2^m`-th-root character is multiplicative

`exp(i·2π·(z₁+z₂).val / 2^m) = exp(i·2π·z₁.val/2^m) · exp(i·2π·z₂.val/2^m)`. This is the phase-additivity
`HadamardPhase` avoids everywhere (it keeps single `realPhase`s); the branch-evaluation below needs it. -/
theorem expChar_add {m : ℕ} (z₁ z₂ : ZMod (2 ^ m)) :
    Complex.exp (Complex.I * ((2 * Real.pi * ((z₁ + z₂).val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((2 * Real.pi * (z₁.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((2 * Real.pi * (z₂.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)) := by
  set ζ : ℂ := Complex.exp (Complex.I * ((2 * Real.pi / (2 : ℝ) ^ m : ℝ) : ℂ)) with hζ
  have expA : ∀ N : ℕ,
      Complex.exp (Complex.I * ((2 * Real.pi * (N : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)) = ζ ^ N := by
    intro N
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hζpow : ζ ^ (2 ^ m) = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    rw [show ((2 ^ m : ℕ) : ℂ) * (Complex.I * ((2 * Real.pi / (2 : ℝ) ^ m : ℝ) : ℂ))
          = 2 * (Real.pi : ℂ) * Complex.I from by push_cast; field_simp]
    exact Complex.exp_two_pi_mul_I
  have hred : ∀ a : ℕ, ζ ^ a = ζ ^ (a % 2 ^ m) := by
    intro a
    conv_lhs => rw [← Nat.div_add_mod a (2 ^ m), pow_add, pow_mul, hζpow, one_pow, one_mul]
  rw [expA, expA, expA, ← pow_add, ZMod.val_add]
  exact (hred (z₁.val + z₂.val)).symm

/-- `exp∘realPhase` is multiplicative over `+` of exponents (the character corollary of `expChar_add`). -/
theorem exp_realPhase_add {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    Complex.exp (Complex.I * (DiagPhase.realPhase (A + B) v : ℂ))
      = Complex.exp (Complex.I * (DiagPhase.realPhase A v : ℂ))
        * Complex.exp (Complex.I * (DiagPhase.realPhase B v : ℂ)) := by
  have hadd : (A + B).eval v = A.eval v + B.eval v := by
    unfold DiagPhase.eval; rw [map_add]
  unfold DiagPhase.realPhase
  rw [hadd]
  exact expChar_add (A.eval v) (B.eval v)

/-- Updating `append w y` at the output index `castAdd h k` = appending the updated `w`. -/
theorem update_append_castAdd {n h : ℕ} (k : Fin n) (p : ZMod 2)
    (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) :
    Function.update (Fin.append w y) (Fin.castAdd h k) p = Fin.append (Function.update w k p) y := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun l => ?_) j
  · rw [Fin.append_left]
    by_cases hik : i = k
    · subst hik; rw [Function.update_self, Function.update_self]
    · have hne : (Fin.castAdd h i : Fin (n + h)) ≠ Fin.castAdd h k := by
        intro hc; exact hik (Fin.ext (by simpa [Fin.val_castAdd] using Fin.ext_iff.mp hc))
      rw [Function.update_of_ne hne, Function.update_of_ne hik, Fin.append_left]
  · have hne : (Fin.natAdd n l : Fin (n + h)) ≠ Fin.castAdd h k := by
      intro hc
      have hval := Fin.ext_iff.mp hc
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
      have := k.isLt; omega
    rw [Fin.append_right, Function.update_of_ne hne, Fin.append_right]

/-- `realPhase` of a freeze = `realPhase` at the updated point (from `freezeAt_eval`). -/
theorem realPhase_freezeAt {N m : ℕ} (j : Fin N) (p : ZMod 2) (Q : DiagPhase N m) (z : Fin N → ZMod 2) :
    DiagPhase.realPhase (freezeAt j p Q) z = DiagPhase.realPhase Q (Function.update z j p) := by
  unfold DiagPhase.realPhase; rw [freezeAt_eval]

/-- The `2^{m-1}` coupling monomial contributes exactly the Walsh sign `(-1)^{p·w_k}`. -/
theorem exp_coupling {n h m : ℕ} (hm : 1 ≤ m) (k : Fin n) (p : ZMod 2)
    (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) :
    Complex.exp (Complex.I * (DiagPhase.realPhase
        (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1) * (p.val : ZMod (2 ^ m)))
          * MvPolynomial.X (Fin.castAdd h k)) (Fin.append w y) : ℂ))
      = (-1 : ℂ) ^ (p.val * (w k).val) := by
  have heval : ((MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1) * (p.val : ZMod (2 ^ m)))
        * MvPolynomial.X (Fin.castAdd h k) : DiagPhase (n + h) m)).eval (Fin.append w y)
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * ((p.val * (w k).val : ℕ) : ZMod (2 ^ m)) := by
    unfold DiagPhase.eval
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp only [DiagPhase.liftBinary]
    rw [Fin.append_left]
    push_cast
    ring
  unfold DiagPhase.realPhase
  rw [heval]
  have hN1 : p.val * (w k).val ≤ 1 :=
    (Nat.mul_le_mul (Nat.lt_succ_iff.mp (ZMod.val_lt p)) (Nat.lt_succ_iff.mp (ZMod.val_lt (w k)))).trans
      (by norm_num)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hN1 with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    have hval : ((2 : ZMod (2 ^ m)) ^ (m - 1) * ((1 : ℕ) : ZMod (2 ^ m))).val = 2 ^ (m - 1) := by
      rw [Nat.cast_one, mul_one,
        show (2 : ZMod (2 ^ m)) ^ (m - 1) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) from by push_cast; ring,
        ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
    rw [hval,
      show 2 * Real.pi * ((2 ^ (m - 1) : ℕ) : ℝ) / (2 : ℝ) ^ m = Real.pi from by
        rw [show (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) from by
          rw [← pow_succ']; congr 1; omega]
        push_cast; field_simp,
      show Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I from by push_cast; ring,
      Complex.exp_pi_mul_I]
    norm_num

/-- **The branch-evaluation identity** — freezing the summation variable to `p` and reading off the Walsh
sign: `ampCore (hBranch k p Q) w = (-1)^{p·w_k} · ampCore Q (w with bit k → p)`. -/
theorem hBranch_eval {n h m : ℕ} (hm : 1 ≤ m) (k : Fin n) (p : ZMod 2) (Q : DiagPhase (n + h) m)
    (c : ℂ) (w : Fin n → ZMod 2) :
    ampCore m h (hBranch k p Q) c w
      = (-1 : ℂ) ^ (p.val * (w k).val) * ampCore m h Q c (Function.update w k p) := by
  unfold ampCore
  have hsum : (∑ y : Fin h → ZMod 2,
        Complex.exp (Complex.I * (DiagPhase.realPhase (hBranch k p Q) (Fin.append w y) : ℂ)))
      = (-1 : ℂ) ^ (p.val * (w k).val) * ∑ y : Fin h → ZMod 2,
          Complex.exp (Complex.I *
            (DiagPhase.realPhase Q (Fin.append (Function.update w k p) y) : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold hBranch
    rw [exp_realPhase_add, realPhase_freezeAt, update_append_castAdd, exp_coupling hm]
    ring
  rw [hsum]
  ring

end FTQCLib.Frame.Walkthrough

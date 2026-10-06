/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.GateWord
import FTQCLib.Carrier.PrecisionGauge
import FTQCLib.Hierarchy.GatePolynomials

/-!
# Controlled-H on carrier registers at any height

Controlled-H with control `c` and target `t` acts on an amplitude function by
`(C H_t f)(w) = f w` where `w c = 0` and `(C H_t f)(w) = (W_t f)(w)` where `w c = 1`, with `W_t` the
Walsh transform at the target (`docs/GLOSSARY.md`, "controlled-`U`"). This is its referee
(`controlledHAmp`), in the sense of decision D5: it is defined from the matrix, not from any
circuit.

The **controlled-H word** (`controlledHWord`) is the gate word, head letter first,

  `S†_t, H_t, T_t, H_t, S_t, CNOT(c, t), S†_t, H_t, T†_t, H_t, S_t`.

As matrices the first five letters are `V = S H T H S†` on the target and the last five are
`V† = S H T† H S†`, and `V† X V = H` exactly, with no global phase; so the word is
`(I ⊗ V†) · CNOT · (I ⊗ V)`, which is controlled-`(V† X V)`. That matrix identity was checked by
computation on 2×2 and 4×4 matrices, and on amplitude functions over three free bits for every
ordered pair of distinct bits, before the statement was written (measured 2026-09-30). It is not
stated here as an identity of matrices; its consequence on amplitude functions is proved here
(`runAmp_controlledHWord`). It is the one-CNOT case of the controlled-`U` networks of Barenco et
al.: H is conjugate to `σ_x`, so one CNOT suffices; the particular conjugator is this module's own.

The proof reads the word as two five-letter sandwiches `S†, H, D, H, S` (`sandwichWord`) around
the CNOT (`controlledHWord_eq_append`). Each sandwich, read at the target's two values, is a
linear combination of its input at those two points (`runAmp_sandwichWord_update_zero`,
`runAmp_sandwichWord_update_one`); the CNOT swaps the two points where the control bit is `1`;
the rest is arithmetic in `ℂ` with the T phase `(1 + i)/√2` (`charOf_three_one`).

T needs precision at least three, and a carrier state may be at precision one or two. The input
is therefore first lifted by the gauge rewrite R7 (`liftPrecision`, `PrecisionGauge.lean`) to a
precision `k` at least three and at least its own; the canonical choice is `k = max S.m 3`, and
the statement holds at every such `k`.

**The statement** (`docs/TARGETS.md`, T08): for every carrier state `S`, at any height and any
precision, and every pair of distinct free bits `c ≠ t`, the word run on the lifted state gives a
carrier state whose amplitude is controlled-H applied to `amp S` (`amp_controlledHWord`). An
equation of amplitudes is exactly `StateEq` (D8), so the output is stated up to `StateEq`, not
as a record.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported; `liftTo` keeps its full
name `FTQCLib.Hilbert.liftTo` from before its move.

## Main definitions

* `controlledHAmp` — the referee: controlled-H on an amplitude function.
* `sandwichWord` — the five letters `S†, H, D, H, S` on the target, for a diagonal `D`.
* `controlledHWord` — the controlled-H word at a precision of at least three.

## Main results

* `runAmp_sandwichWord_update_zero`, `runAmp_sandwichWord_update_one` — the sandwich's referee
  at the target's two values.
* `controlledHWord_eq_append` — the word is a sandwich, the CNOT, and a sandwich.
* `runAmp_controlledHWord` — the word's referee is controlled-H, on every amplitude function.
* `amp_controlledHWord` — the word keeps the carrier property and computes the referee.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The referee -/

/-- **Controlled-H on an amplitude function**, control `c` and target `t`: the identity where the
control bit is `0`, the Walsh transform at the target where it is `1`. -/
noncomputable def controlledHAmp (c t : Fin n) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  fun w => if w c = 0 then f w else walshTransform t f w

/-! ## The word -/

/-- **The controlled-H word** at precision `k ≥ 3`, control `c`, target `t`, head letter first:
`S†, H, T, H, S` on the target, `CNOT(c, t)`, then `S†, H, T†, H, S` on the target. `S` is
`sGate k t`, and `T` is `tGatePoly t` lifted to precision `k`; `S†` and `T†` are their negations. -/
noncomputable def controlledHWord (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t) :
    GateWord n k :=
  [.diagonal (-(sGate k t)), .hadamard t, .diagonal (FTQCLib.Hilbert.liftTo k hk (tGatePoly t)),
    .hadamard t, .diagonal (sGate k t),
    .cnot c t hct,
    .diagonal (-(sGate k t)), .hadamard t, .diagonal (-(FTQCLib.Hilbert.liftTo k hk (tGatePoly t))),
    .hadamard t, .diagonal (sGate k t)]

/-- **The sandwich** `S†, H, D, H, S` on the target `t`, head letter first, for a diagonal `D` at
precision `k`: the conjugate of `D` by `H S†`. -/
noncomputable def sandwichWord (k : ℕ) (t : Fin n) (D : DiagPhase n k) : GateWord n k :=
  [.diagonal (-(sGate k t)), .hadamard t, .diagonal D, .hadamard t, .diagonal (sGate k t)]

/-- The controlled-H word is the sandwich with `T`, the CNOT, and the sandwich with `T†`. -/
theorem controlledHWord_eq_append (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t) :
    controlledHWord k hk hct
      = sandwichWord k t (FTQCLib.Hilbert.liftTo k hk (tGatePoly t))
        ++ GateLetter.cnot c t hct
          :: sandwichWord k t (-FTQCLib.Hilbert.liftTo k hk (tGatePoly t)) :=
  rfl

/-! ## The phases at the target's two values -/

/-- The `S` and `S†` phases where the target bit is `0` and where it is `1`: `1`, `i`, `1`, `−i`. -/
private theorem charOf_sGate_update {k : ℕ} (hk : 2 ≤ k) (t : Fin n) (w : Fin n → ZMod 2) :
    charOf k ((sGate k t).eval (Function.update w t 0)) = 1
      ∧ charOf k ((sGate k t).eval (Function.update w t 1)) = Complex.I
      ∧ charOf k ((-sGate k t).eval (Function.update w t 0)) = 1
      ∧ charOf k ((-sGate k t).eval (Function.update w t 1)) = -Complex.I := by
  have h0 : charOf k ((sGate k t).eval (Function.update w t 0)) = 1 := by
    rw [sGate_eval, Function.update_self, ZMod.val_zero, Nat.cast_zero, mul_zero, charOf_zero]
  have h1 : charOf k ((sGate k t).eval (Function.update w t 1)) = Complex.I := by
    rw [sGate_eval, Function.update_self, show (1 : ZMod 2).val = 1 from rfl,
      charOf_two_pow_sub_two_mul hk 1, pow_one]
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [DiagPhase.eval_neg, charOf_neg, h0, inv_one]
  · rw [DiagPhase.eval_neg, charOf_neg, h1, Complex.inv_I]

/-- The `T` and `T†` phases, lifted to precision `k`, where the target bit is `0` and where it is
`1`: `1`, `charOf 3 1`, `1`, `charOf 3 (−1)`. -/
private theorem charOf_tGate_update {k : ℕ} (hk : 3 ≤ k) (t : Fin n) (w : Fin n → ZMod 2) :
    charOf k ((FTQCLib.Hilbert.liftTo k hk (tGatePoly t)).eval (Function.update w t 0)) = 1
      ∧ charOf k ((FTQCLib.Hilbert.liftTo k hk (tGatePoly t)).eval (Function.update w t 1))
          = charOf 3 1
      ∧ charOf k ((-FTQCLib.Hilbert.liftTo k hk (tGatePoly t)).eval (Function.update w t 0)) = 1
      ∧ charOf k ((-FTQCLib.Hilbert.liftTo k hk (tGatePoly t)).eval (Function.update w t 1))
          = charOf 3 (-1) := by
  have h0 : charOf k ((FTQCLib.Hilbert.liftTo k hk (tGatePoly t)).eval (Function.update w t 0))
      = 1 := by
    rw [charOf_eval_liftTo, tGatePoly, DiagPhase.eval_X, Function.update_self, ZMod.val_zero,
      Nat.cast_zero, charOf_zero]
  have h1 : charOf k ((FTQCLib.Hilbert.liftTo k hk (tGatePoly t)).eval (Function.update w t 1))
      = charOf 3 1 := by
    rw [charOf_eval_liftTo, tGatePoly, DiagPhase.eval_X, Function.update_self,
      show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one]
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [DiagPhase.eval_neg, charOf_neg, h0, inv_one]
  · rw [DiagPhase.eval_neg, charOf_neg, h1, ← charOf_neg]

/-! ## The sandwich at the target's two values -/

/-- **The sandwich, read where the target bit is `0`.** For a diagonal `D` whose phase is `1` where
the target bit is `0` and `ξ` where it is `1`, the sandwich's referee is a linear combination of
its input at the two points that differ from `w` at most in the target bit. -/
theorem runAmp_sandwichWord_update_zero {k : ℕ} (hk : 2 ≤ k) (t : Fin n) (D : DiagPhase n k)
    (w : Fin n → ZMod 2) {ξ : ℂ} (hD0 : charOf k (D.eval (Function.update w t 0)) = 1)
    (hD1 : charOf k (D.eval (Function.update w t 1)) = ξ) (g : (Fin n → ZMod 2) → ℂ) :
    runAmp (sandwichWord k t D) g (Function.update w t 0)
      = (1 / 2 : ℂ) * ((g (Function.update w t 0) - Complex.I * g (Function.update w t 1))
          + ξ * (g (Function.update w t 0) + Complex.I * g (Function.update w t 1))) := by
  obtain ⟨hS0, -, hnS0, hnS1⟩ := charOf_sGate_update hk t w
  simp only [sandwichWord, runAmp_cons, runAmp_nil, letterAmp, walshTransform,
    Function.update_idem, Function.update_self]
  rw [hnS0, hnS1, hD0, hD1, hS0, signOf_zero, signOf_one]
  ring_nf
  rw [inv_sqrt_two_sq]
  ring

/-- **The sandwich, read where the target bit is `1`.** The companion of
`runAmp_sandwichWord_update_zero`, under the same hypotheses on `D`. -/
theorem runAmp_sandwichWord_update_one {k : ℕ} (hk : 2 ≤ k) (t : Fin n) (D : DiagPhase n k)
    (w : Fin n → ZMod 2) {ξ : ℂ} (hD0 : charOf k (D.eval (Function.update w t 0)) = 1)
    (hD1 : charOf k (D.eval (Function.update w t 1)) = ξ) (g : (Fin n → ZMod 2) → ℂ) :
    runAmp (sandwichWord k t D) g (Function.update w t 1)
      = Complex.I * ((1 / 2 : ℂ) *
          ((g (Function.update w t 0) - Complex.I * g (Function.update w t 1))
          - ξ * (g (Function.update w t 0) + Complex.I * g (Function.update w t 1)))) := by
  obtain ⟨-, hS1, hnS0, hnS1⟩ := charOf_sGate_update hk t w
  simp only [sandwichWord, runAmp_cons, runAmp_nil, letterAmp, walshTransform,
    Function.update_idem, Function.update_self]
  rw [hnS0, hnS1, hD0, hD1, hS1, signOf_zero, signOf_one]
  ring_nf
  rw [inv_sqrt_two_sq]
  ring

/-! ## The CNOT and the finish -/

/-- The CNOT's referee at a point `w` with its target bit set to `B`: the input at the point with
the target bit set to `B + w c`. -/
private theorem letterAmp_cnot_update {m : ℕ} {c t : Fin n} (hct : c ≠ t)
    (g : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) (B : ZMod 2) :
    letterAmp (GateLetter.cnot c t hct : GateLetter n m) g (Function.update w t B)
      = g (Function.update w t (B + w c)) := by
  change g (cnotBitMap c t (Function.update w t B)) = _
  unfold cnotBitMap
  rw [Function.update_idem, Function.update_self, Function.update_of_ne hct]

/-- **The arithmetic of the finish.** With `ζ = (1 + i)/√2` and `ζ' = (1 − i)/√2`, and `u₀`, `u₁`
the first sandwich's values at the target's two values, the second sandwich returns `a` and `b`
when it reads `(u₀, u₁)` (control bit `0`), and the Walsh transform of `(a, b)` when it reads
`(u₁, u₀)` (control bit `1`). The coefficients are the quotients of each difference by
`i² + 1` and `(1/√2)² − 1/2`, computed with SymPy's `reduced` (2026-09-30). -/
private theorem controlledH_finish {a b ζ ζ' u₀ u₁ : ℂ}
    (hζ : ζ = (1 + Complex.I) / (Real.sqrt 2 : ℂ)) (hζ' : ζ' = (1 - Complex.I) / (Real.sqrt 2 : ℂ))
    (hu₀ : u₀ = (1 / 2 : ℂ) * ((a - Complex.I * b) + ζ * (a + Complex.I * b)))
    (hu₁ : u₁ = Complex.I * ((1 / 2 : ℂ) * ((a - Complex.I * b) - ζ * (a + Complex.I * b)))) :
    (1 / 2 : ℂ) * ((u₀ - Complex.I * u₁) + ζ' * (u₀ + Complex.I * u₁)) = a
      ∧ Complex.I * ((1 / 2 : ℂ) * ((u₀ - Complex.I * u₁) - ζ' * (u₀ + Complex.I * u₁))) = b
      ∧ (1 / 2 : ℂ) * ((u₁ - Complex.I * u₀) + ζ' * (u₁ + Complex.I * u₀))
          = 1 / (Real.sqrt 2 : ℂ) * (a + signOf 0 * b)
      ∧ Complex.I * ((1 / 2 : ℂ) * ((u₁ - Complex.I * u₀) - ζ' * (u₁ + Complex.I * u₀)))
          = 1 / (Real.sqrt 2 : ℂ) * (a + signOf 1 * b) := by
  subst hζ hζ' hu₀ hu₁
  rw [signOf_zero, signOf_one]
  set r := (Real.sqrt 2 : ℂ)⁻¹ with hr_def
  have hr : r ^ 2 = 1 / 2 := inv_sqrt_two_sq
  simp only [div_eq_mul_inv, one_mul, ← hr_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (Complex.I ^ 3 * b * r ^ 2 + Complex.I ^ 2 * a * r ^ 2
      + 2 * Complex.I ^ 2 * b * r - 3 * Complex.I * b * r ^ 2 + Complex.I * b - 3 * a * r ^ 2
      + 2 * a * r - a) / 4 * Complex.I_sq + (Complex.I * b + a) * hr
  · linear_combination -(Complex.I ^ 4 * b * r ^ 2 + Complex.I ^ 3 * a * r ^ 2
      - 2 * Complex.I ^ 2 * a * r - 3 * Complex.I ^ 2 * b * r ^ 2 - 2 * Complex.I ^ 2 * b * r
      - Complex.I ^ 2 * b - 3 * Complex.I * a * r ^ 2 + Complex.I * a + 4 * b * r ^ 2 + 2 * b) / 4
      * Complex.I_sq + (-Complex.I * a + b) * hr
  · linear_combination -r * (a + b) * Complex.I_sq
  · linear_combination -r * (Complex.I ^ 2 * b + a - b) * Complex.I_sq

/-- The controlled-H word's referee at `w` with its target bit set to `B`: the four cases of the
control bit and `B`, each the finish's arithmetic on the two sandwiches around the CNOT. -/
private theorem runAmp_controlledHWord_update (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t)
    (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) (B : ZMod 2) :
    runAmp (controlledHWord k hk hct) f (Function.update w t B)
      = controlledHAmp c t f (Function.update w t B) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨hT0, hT1, hnT0, hnT1⟩ := charOf_tGate_update hk t w
  have hF0 := runAmp_sandwichWord_update_zero hk2 t _ w hT0 hT1 f
  have hF1 := runAmp_sandwichWord_update_one hk2 t _ w hT0 hT1 f
  have hG0 := runAmp_sandwichWord_update_zero hk2 t _ w hnT0 hnT1
    (letterAmp (m := k) (GateLetter.cnot c t hct)
      (runAmp (sandwichWord k t (FTQCLib.Hilbert.liftTo k hk (tGatePoly t))) f))
  have hG1 := runAmp_sandwichWord_update_one hk2 t _ w hnT0 hnT1
    (letterAmp (m := k) (GateLetter.cnot c t hct)
      (runAmp (sandwichWord k t (FTQCLib.Hilbert.liftTo k hk (tGatePoly t))) f))
  rw [letterAmp_cnot_update, letterAmp_cnot_update] at hG0 hG1
  have hfin := controlledH_finish charOf_three_one charOf_three_neg_one hF0 hF1
  rw [controlledHWord_eq_append, runAmp_append, runAmp_cons]
  unfold controlledHAmp walshTransform
  rw [Function.update_of_ne hct, Function.update_idem, Function.update_idem,
    Function.update_self]
  rcases zmod_two_eq_zero_or_one (w c) with hc | hc <;>
    rcases zmod_two_eq_zero_or_one B with rfl | rfl
  · rw [if_pos hc, hG0, hc, add_zero, add_zero]
    exact hfin.1
  · rw [if_pos hc, hG1, hc, add_zero, add_zero]
    exact hfin.2.1
  · rw [if_neg (by rw [hc]; decide), hG0, hc, zero_add, show (1 + 1 : ZMod 2) = 0 from rfl]
    exact hfin.2.2.1
  · rw [if_neg (by rw [hc]; decide), hG1, hc, zero_add, show (1 + 1 : ZMod 2) = 0 from rfl]
    exact hfin.2.2.2

/-- **The word's referee is controlled-H**, on every amplitude function: the controlled-H word at
any precision `k ≥ 3`, with control `c` and target `t` distinct, composes to `controlledHAmp`. -/
theorem runAmp_controlledHWord (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t)
    (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (controlledHWord k hk hct) f = controlledHAmp c t f := by
  funext w
  simpa only [Function.update_eq_self] using runAmp_controlledHWord_update k hk hct f w (w t)

/-- Controlled-H keeps `Σ_w |·|²`: it is the referee of T08's word (`runAmp_controlledHWord`), and
every word keeps it (`sum_normSq_runAmp`). -/
theorem sum_normSq_controlledHAmp (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t)
    (f : (Fin n → ZMod 2) → ℂ) :
    ∑ w : Fin n → ZMod 2, Complex.normSq (controlledHAmp c t f w)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w) := by
  rw [← runAmp_controlledHWord k hk hct]
  exact sum_normSq_runAmp _ f

/-! ## The statement -/

-- source: papers/clifford_hierarchy/Barenco_1995_elementary_gates_quant-ph_9503016 lemma:5.1
/-- **Controlled-H on a carrier register.** For a carrier state `S` at any height and any precision,
distinct free bits `c ≠ t`, and any precision `k` at least three and at least `S.m`, the
controlled-H word run on `S` lifted to precision `k` gives a carrier state whose amplitude is
controlled-H applied to `amp S`. -/
theorem amp_controlledHWord {S : KernelSumState n} (hS : IsCarrier S) {c t : Fin n}
    (hct : c ≠ t) (k : ℕ) (hmk : S.m ≤ k) (hk : 3 ≤ k) :
    IsCarrier (run (controlledHWord k hk hct) (liftPrecision S k hmk))
      ∧ amp (run (controlledHWord k hk hct) (liftPrecision S k hmk))
          = controlledHAmp c t (amp S) := by
  have hSk := isCarrier_liftPrecision hS k hmk
  refine ⟨isCarrier_run (controlledHWord k hk hct) hSk rfl, ?_⟩
  rw [amp_run (controlledHWord k hk hct) hSk rfl, amp_liftPrecision, runAmp_controlledHWord]

end FTQCLib.Frame.Walkthrough

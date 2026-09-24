/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardAmplitude

/-!
# Reduction: the pinned constructor is the raising rule at `u = 0`

`applyHPinned` (`FTQCLib/Examples/HadamardGate.lean`) is the pinned Hadamard: it frees a bit
whose value is definite, emitting the dyadic sign `2^{m−1}·x₀ᵢ·Xᵢ` and rotating the support.
`hRaise` (`FTQCLib/Examples/HadamardRaise.lean`) at the representer `u = 0` does the same and one thing
more: it **freezes** the Hadamarded coordinate to `x₀ᵢ` in the exponent before emitting the sign.
This file makes the relation exact, at the level of denotation.

The two constructors live on different carriers (`KernelState` and `KernelSumState` at `h = 0`),
so the comparison goes through the embedding `ofKernelState` and the frame-side amplitude `amp`.
On the output support the two exponents differ only by the freeze, so the amplitudes agree exactly
when the exponent does not read the pinned bit — the hypothesis `hqfree` that `cert_pinned`
(`FTQCLib/Examples/HadamardGateCertificate.lean`) already carries. Under it the pinned constructor
inherits the referee certificate of `amp_hRaise`: `amp (ofKernelState (applyHPinned i K)) =
walshTransform i (amp (ofKernelState K))`. Without it, `hRaise` at `u = 0` is still correct
(`amp_hRaise_zero_ofKernelState` needs only pinning) and `applyHPinned` is not, as the check module
exhibits. The pinned constructor is therefore a special case of the raising rule, not a sibling.

Everything here is frame-pure: no `FTQCLib.Hilbert`.

## Main definitions

None.

## Main results

* `applyHPinned_q_eval`, `hRaise_zero_ofKernelState_eval` — the two output exponents, evaluated:
  the same sign term, with and without the freeze.
* `amp_ofKernelState_applyHPinned_eq_hRaise` — under `hqfree`, the two constructors have the same
  amplitude.
* `amp_hRaise_zero_ofKernelState` — `hRaise` at `u = 0` is the Walsh transform under pinning alone.
* `amp_ofKernelState_applyHPinned` — **the transported certificate**: `applyHPinned` is the Walsh
  transform under pinning and `hqfree`, at every `1 ≤ m`.
* `amp_ofKernelState_applyHPinned_classical` — the classical register, certified against the
  referee.

## Implementation notes

* The evaluation lemmas are stated with the implicit index `n + 0` on the left, which is what the
  `h = 0` character sum (`ampCore_zero`) produces; stating them at `n` would make the rewrites in
  the amplitude proof miss. The right-hand sides are at `n`, so that `hqfree`, stated by consumers
  at `n`, rewrites them.
* `cert_pinned` is at `m = 1` and stated on the floor chart; this file's statements are at every
  `1 ≤ m` and against the referee, so they are not a restatement of it but the amplitude-level fact
  its content transports to. Its `hqfree` is inherited verbatim.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The `u = 0` slot of the branch data -/

/-- The zero representer pairs to nothing. -/
theorem dotF2_zero_left (v : Fin n → ZMod 2) : dotF2 (0 : Fin n → ZMod 2) v = 0 := by
  unfold dotF2
  simp

/-- At `u = 0` the branch constant is the pinned bit's value. -/
theorem raiseConst_zero (i : Fin n) (x₀ : Fin n → ZMod 2) :
    raiseConst i (0 : Fin n → ZMod 2) x₀ = x₀ i := by
  unfold raiseConst
  rw [dotF2_zero_left, add_zero]

/-! ## Evaluating the two exponents -/

/-- The dyadic sign polynomial evaluates to `ε·2^{m−1}·wᵢ`. -/
theorem hSignPoly_eval (i : Fin n) (ε : ZMod 2) (m : ℕ) (w : Fin n → ZMod 2) :
    DiagPhase.eval (hSignPoly i ε m) w
      = (ε.val : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1) * ((w i).val : ZMod (2 ^ m)) := by
  unfold hSignPoly
  rw [MvPolynomial.smul_eq_C_mul, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]

/-- **`applyHPinned`'s exponent, evaluated:** the input exponent unchanged, plus the sign. -/
theorem applyHPinned_q_eval (i : Fin n) (K : KernelState n) (w : Fin n → ZMod 2) :
    @DiagPhase.eval (n + 0) K.m (applyHPinned i K).q w
      = DiagPhase.eval K.q w
        + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((K.x₀ i).val : ZMod (2 ^ K.m))
            * ((w i).val : ZMod (2 ^ K.m)) := by
  change DiagPhase.eval (K.q + hSignPoly i (K.x₀ i) K.m) w = _
  rw [DiagPhase.eval_add, hSignPoly_eval]
  ring

/-- **`hRaise`'s exponent at `u = 0`, evaluated:** the input exponent *frozen* at the pinned bit,
plus the same sign. The freeze is the one difference between the constructors. -/
theorem hRaise_zero_ofKernelState_eval (i : Fin n) (K : KernelState n) (w : Fin n → ZMod 2) :
    @DiagPhase.eval (n + 0) K.m (hRaise i 0 (ofKernelState K)).Q w
      = DiagPhase.eval K.q (Function.update w i (K.x₀ i))
        + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((K.x₀ i).val : ZMod (2 ^ K.m))
            * ((w i).val : ZMod (2 ^ K.m)) := by
  refine (hRaise_eval i 0 (ofKernelState K) w).trans ?_
  rw [dotF2_zero_left, add_zero, raiseConst_zero]
  rfl

/-! ## The amplitude identity between the constructors -/

/-- **The reduction.** When the exponent does not read the pinned bit, `applyHPinned` and `hRaise`
at `u = 0` have the same amplitude on the carrier: same support, same scale, and exponents that
differ only by a freeze the hypothesis makes invisible. -/
theorem amp_ofKernelState_applyHPinned_eq_hRaise (i : Fin n) (K : KernelState n)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval K.q (Function.update w i b) = DiagPhase.eval K.q w) :
    amp (ofKernelState (applyHPinned i K)) = amp (hRaise i 0 (ofKernelState K)) := by
  funext w
  have hr : @DiagPhase.realPhase (n + 0) K.m (applyHPinned i K).q w
      = @DiagPhase.realPhase (n + 0) K.m (hRaise i 0 (ofKernelState K)).Q w := by
    unfold DiagPhase.realPhase
    rw [applyHPinned_q_eval, hRaise_zero_ofKernelState_eval, hqfree]
  have hcore : ampCore (ofKernelState (applyHPinned i K)).m (ofKernelState (applyHPinned i K)).h
      (ofKernelState (applyHPinned i K)).Q (ofKernelState (applyHPinned i K)).c w
      = ampCore (hRaise i 0 (ofKernelState K)).m (hRaise i 0 (ofKernelState K)).h
          (hRaise i 0 (ofKernelState K)).Q (hRaise i 0 (ofKernelState K)).c w := by
    change ampCore K.m 0 (applyHPinned i K).q (K.c / (Real.sqrt 2 : ℂ)) w
      = ampCore K.m 0 (hRaise i 0 (ofKernelState K)).Q (K.c / (Real.sqrt 2 : ℂ)) w
    rw [ampCore_zero, ampCore_zero, hr]
  by_cases hw : ∃ p ∈ (hRaise i 0 (ofKernelState K)).L,
      w = (hRaise i 0 (ofKernelState K)).x₀ + p.X
  · have hw' : ∃ p ∈ (ofKernelState (applyHPinned i K)).L,
        w = (ofKernelState (applyHPinned i K)).x₀ + p.X := hw
    rw [amp_pos hw', amp_pos hw]
    exact hcore
  · have hw' : ¬ ∃ p ∈ (ofKernelState (applyHPinned i K)).L,
        w = (ofKernelState (applyHPinned i K)).x₀ + p.X := hw
    rw [amp_neg hw', amp_neg hw]

/-! ## The pinned constructor against the referee -/

/-- **`hRaise` at `u = 0` under pinning alone.** On a co-isotropic `L` with bit `i` pinned, `u = 0`
is a representer, so `amp_hRaise` applies with no hypothesis on the exponent. -/
theorem amp_hRaise_zero_ofKernelState (i : Fin n) (K : KernelState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin K.L ≤ K.L)
    (hpin : ∀ p ∈ K.L, p.X i = 0) (hm : 1 ≤ K.m) :
    amp (hRaise i 0 (ofKernelState K)) = walshTransform i (amp (ofKernelState K)) :=
  amp_hRaise i 0 (ofKernelState K) horth rfl (pinned_representer_zero hpin) hm

/-- **The transported certificate.** `applyHPinned` is the Walsh transform on the support-restricted
amplitude, under pinning, `hqfree`, and `1 ≤ m` — `cert_pinned`'s content at amplitude level, for
every precision, obtained from `amp_hRaise` rather than reproved. The extra hypothesis relative to
`amp_hRaise_zero_ofKernelState` is exactly `hqfree`, and it is not decorative (check module). -/
theorem amp_ofKernelState_applyHPinned (i : Fin n) (K : KernelState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin K.L ≤ K.L)
    (hpin : ∀ p ∈ K.L, p.X i = 0)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval K.q (Function.update w i b) = DiagPhase.eval K.q w)
    (hm : 1 ≤ K.m) :
    amp (ofKernelState (applyHPinned i K)) = walshTransform i (amp (ofKernelState K)) := by
  rw [amp_ofKernelState_applyHPinned_eq_hRaise i K hqfree]
  exact amp_hRaise_zero_ofKernelState i K horth hpin hm

/-! ## The classical register: runs A and B, certified -/

/-- Every bit of the classical register is pinned. -/
theorem classical_pinned (i : Fin n) (v : Fin n → ZMod 2) :
    ∀ p ∈ (classical v).L, p.X i = 0 := by
  intro p hp
  have h : p.X = 0 := mem_Lz.mp hp
  rw [h]
  rfl

/-- The classical register's exponent is zero, so it reads no bit. -/
theorem classical_qfree (i : Fin n) (v : Fin n → ZMod 2) :
    ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval (classical v).q (Function.update w i b)
        = DiagPhase.eval (classical v).q w := by
  intro w b
  change DiagPhase.eval (0 : DiagPhase n 1) _ = DiagPhase.eval (0 : DiagPhase n 1) w
  simp [DiagPhase.eval]

/-- **The classical register against the referee.** `H` on any bit of the classical register
`v` — the `applyHPinned_classical_*` examples — computes the Walsh transform of the register's
amplitude. Every hypothesis discharged on `Lz`. -/
theorem amp_ofKernelState_applyHPinned_classical (i : Fin n) (v : Fin n → ZMod 2) :
    amp (ofKernelState (applyHPinned i (classical v)))
      = walshTransform i (amp (ofKernelState (classical v))) :=
  amp_ofKernelState_applyHPinned i (classical v) orthogonal_omegaBilin_Lz.le
    (classical_pinned i v) (classical_qfree i v) le_rfl

end FTQCLib.Frame.Walkthrough

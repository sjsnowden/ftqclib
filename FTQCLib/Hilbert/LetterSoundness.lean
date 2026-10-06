/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ProtocolSemantics

/-!
# Soundness of the unitary moves: the frame's referees are the Hilbert gates

T18 (`docs/TARGETS.md`): for every carrier move, the Hilbert image of the output is the unitary
applied to the image of the input. The carrier moves are the three letters of `GateLetter n m`
(`Carrier/GateWord.lean`) as `applyLetter` runs them on a carrier state, and a word is these moves
in sequence, head letter first (`run`); the steps of `CarrierRule` are rewrites of one state, not
moves (`docs/fidelity/T18.md`, Claim 2).

**The image.** The Hilbert image of a carrier state `S` is its amplitude `amp S`
(`Carrier/CarrierAmplitude.lean`: `ampCore` on the support coset, zero off it) read in
`QubitSpace n`, which is the abbreviation `(Fin n → ZMod 2) → ℂ`, so no transport is needed. It is
the Hilbert side's `F` of `Hilbert/CharSumCorrespondence.lean`, which has the same defining
formula; it is not `ampVec` of `HadamardCharSumBridge.lean` or `ampFun`, `embed` of
`CharSumPairingBridge.lean`, the raw amplitude unrestricted to the support.

**What this module states.** The frame already proves that a move computes its referee:
`amp (applyLetter g S) = letterAmp g (amp S)` on a carrier state at the letter's precision
(`amp_applyLetter`), and `amp (run gs S) = runAmp gs (amp S)` (`amp_run`), both at T05. What is
left is that each referee is the Hilbert gate. `letterAmp_eq_gate` says it for every letter, as
functions on `QubitSpace n`, with no hypothesis: `letterAmp (hadamard k)` is `hadamardGate k`,
`letterAmp (diagonal D)` is `diagonalGate` of the letter's radian phase `DiagPhase.realPhase D`
(`exp(i · realPhase D w) = charOf m (D.eval w)`, `exp_realPhase_eq_charOf`), and
`letterAmp (cnot i j hij)` is `cnotGate i j hij`. These are T17's `letterGate`
(`Hilbert/ProtocolSemantics.lean`), the operators the Hilbert semantics `⟦p⟧` is built from, so the
gates are not restated here. `runAmp_eq_wordGate` says it for a word: `runAmp gs` is T17's
`wordGate gs`, the letters' gates composed head letter first. Composed with `amp_applyLetter` and
`amp_run`, these give T18's Statement for each move and each word; the hypotheses `IsCarrier S`
(the H move needs the dichotomy of `hadamard_cover`) and `S.m = m` (a diagonal letter at another
precision is left unchanged by `applyLetter`) are those two theorems' own.

**Which existing modules already state a case.** Read for this module, declaration by
declaration:

* `Hilbert/CharSumCorrespondence.lean` states the three moves on `F`, against these same Hilbert
  gates: `F_applyHFiner` the H move by the free rule `applyHFiner` only, under an X-supported bit
  and `1 ≤ S.m`; `F_applyDiagSum` the diagonal move at `diagonalGate (DiagPhase.realPhase D)`;
  `F_applyCnotSum` the CNOT move. Its words are its own alphabet `Gate` with `gateHilbert`, run
  tail first by `foldr` (`F_applyGate`, `F_runFrame`), whose H is the free rule alone. It states
  no case of `letterAmp` or `runAmp`, and none of the representer rule `hRaise`.
* `Hilbert/HadamardCharSumBridge.lean` states the free-rule H move on the raw amplitude `ampVec`
  (`ampVec_applyHFiner`) and a word of free-rule Hadamards (`ampVec_hadamardWord`); no diagonal
  or CNOT case, and no case of `letterAmp`.
* `Hilbert/CharSumPairingBridge.lean` states no move: it carries norms, inner products and
  distances to `QState`.
* The `FrameBridge` modules (`FrameBridge.lean`, `FrameBridgeAmplitude.lean`,
  `FrameBridgeAmplitudeCore.lean`, `FrameBridgeAmplitudeQuad.lean`, `FrameSignedBridge.lean`)
  state no move: they concern stabilizer states and the signed chart.

So the diagonal and CNOT letters have a stated counterpart on `F` and the H letter one for the
free rule only; the referee identities themselves, the representer rule's image, and the
head-first word are stated here first.

## Main results

* `letterAmp_eq_gate` — a letter's referee is its Hilbert gate `letterGate g` (proved at T18.3).
* `runAmp_eq_wordGate` — a word's referee is its Hilbert gate `wordGate gs` (proved at T18.3).

## Implementation notes

* The equalities are of functions `QubitSpace n → QubitSpace n`, the coercion of the linear maps
  `letterGate g` and `wordGate gs`; the pointwise form at `f` and `w` follows by `congrFun`.
* The H identity is a two-term sum: `walshTransform k f w = (1/√2)(f(w[k←0]) + signOf(w_k)
  f(w[k←1]))` against `invSqrt2 · Σ_b (−1)^{w_k.val · b.val} f(w[k←b])`. The diagonal identity
  holds by `exp_realPhase_eq_charOf`, which is `rfl`; the CNOT identity by `cnotBitMap` and
  `cnotPerm` being the same map (`docs/fidelity/T18.md`, Claim 4).
* The precision `m` is the letter's index; no hypothesis on it is needed here, since `letterAmp`
  and `letterGate` both read the exponent at the letter's own precision.

## References

* M. Amy, *Towards large-scale functional verification of universal quantum circuits*,
  arXiv:1805.06908: the matrices of `H`, `R_k` and CNOT, and their path-sum interpretations
  (`docs/fidelity/T18.md`, Claim 3).
-/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Frame.Walkthrough

variable {n m : ℕ}

/-- A sum over `ZMod 2` is the two-term sum. -/
private theorem sum_zmod2 (f : ZMod 2 → ℂ) : ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := by
  decide

private theorem zmod2_val_one : (1 : ZMod 2).val = 1 := by
  decide

private theorem one_div_sqrt_two : 1 / (Real.sqrt 2 : ℂ) = invSqrt2 := by
  rw [invSqrt2, Complex.ofReal_inv, one_div]

/-- The frame's Walsh transform at bit `k` is the Hilbert `hadamardGate k`, pointwise: the two
terms `b = 0` and `b = 1` of the gate's sum carry the signs `1` and `signOf (w k)`. -/
private theorem walshTransform_eq_hadamardGate (k : Fin n) (f : QubitSpace n)
    (w : Fin n → ZMod 2) : walshTransform k f w = hadamardGate k f w := by
  rw [walshTransform, hadamardGate_apply, sum_zmod2, one_div_sqrt_two]
  rcases zmod2_cases (w k) with hwk | hwk
  · rw [hwk, signOf_zero, zmod2_val_zero, zero_mul, zero_mul, pow_zero]
    ring
  · rw [hwk, signOf_one, zmod2_val_zero, zmod2_val_one, mul_zero, mul_one, pow_zero, pow_one]
    ring

/-- **A letter's referee is its Hilbert gate.** For every gate letter `g`, the frame's referee
`letterAmp g` is the Hilbert gate `letterGate g` on `QubitSpace n`: `hadamardGate k` for
`hadamard k`, `diagonalGate (DiagPhase.realPhase D)` for `diagonal D`, and `cnotGate i j hij` for
`cnot i j hij`. -/
theorem letterAmp_eq_gate (g : GateLetter n m) : letterAmp g = ⇑(letterGate g) := by
  funext f w
  cases g with
  | hadamard k => exact walshTransform_eq_hadamardGate k f w
  | diagonal D => rfl
  | cnot i j hij => rfl

/-- **A word's referee is its Hilbert gate.** For every gate word `gs`, the frame's referee
`runAmp gs` is `wordGate gs`, the letters' Hilbert gates composed head letter first. -/
theorem runAmp_eq_wordGate (gs : GateWord n m) : runAmp gs = ⇑(wordGate gs) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    funext f
    rw [runAmp_cons, ih, letterAmp_eq_gate]
    rfl

end FTQCLib.Hilbert

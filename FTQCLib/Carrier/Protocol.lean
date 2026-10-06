/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FeedForward
import FTQCLib.Carrier.OutcomeWeight
import FTQCLib.Carrier.RewriteCompleteness

/-!
# The protocol syntax, its frame interpretation, and completeness of protocol equality

A **protocol** (`docs/TARGETS.md`, T14) on `n` data bits at precision `m` with `k` conditioning
letters is a sequence, in a fixed order, of gate words (T05, `GateWord.lean`) and conditioning
letters (T10, `Conditioning.lean`). Each conditioning letter creates one **outcome bit**, a new
last free bit, so the protocol ends on `n + k` free bits: the data bits first, then the outcome
bits in the order their letters occur. Feed-forward is a gate word on the data and outcome free
bits (T13, `FeedForward.lean`): a gate chosen by outcomes is that gate controlled by the outcome
bits, such as `controlledPauliWord` or `controlledDiagonal`.

**Outcomes are free bits throughout** (decision D2 as revised, signed 2026-09-30). No definition
here takes an outcome as a parameter. The conditioning letter is interpreted by
`conditionOutcome`, the one carrier state `Σ_b ∣b⟩ ⊗ Π_b f`, never by `condition S P b`. A
protocol's **interpretation** (`Protocol.interpret`) is one carrier state on `n + k` free bits.
A **branch** (`Protocol.branch`) is the evaluation of the outcome bits of that one state at an
outcome string `o : Fin k → ZMod 2`: the amplitude function `w ↦ amp (interpret p S) (w ++ o)` on
the data bits. Its weight (`Protocol.branchWeight`) is T11's: the squared norm `Σ_w |·|²` that
`ampNormSq` takes of a conditioned state, here taken of the branch's amplitude. For one
conditioning letter the branch is `amp (condition S P b)` (`conditionOutcome_eval`), so the
parameter outcome of T10 is recovered as an evaluation and the weight is `outcomeWeight`
(`branchWeight_condition_nil`).

**A feed-forward word reads only outcome bits already created.** The type is indexed by the number
`k` of conditioning letters so far, and a word appended after them is a `GateWord (n + k) m`: its
letters name bits of `Fin (n + k)`, the data bits and the `k` outcome bits that earlier
conditioning letters created. An outcome bit that a later letter will create is not yet a bit of
the register, so no letter can name it; no well-formedness predicate is needed, as none is for
T05's words. Run 8's check (`docs/STEPS.md`, entry 2026-10-01d) is met: the `k` conditioning
letters occur in a fixed order and a feed-forward word may read any earlier outcome bit.

**Precision.** The protocol's letters live at one precision `m`, as a word's do. Conditioning on a
Pauli with an odd number of Y raises a precision-one state to two (`conditionPrecision`), after
which a diagonal letter at `m = 1` would meet a state at another precision, the case outside every
theorem of T05. So the conditioning letter carries `yWeight P % 2 = 1 → 2 ≤ m`; on a carrier
state at precision `m` the whole run then stays at `m` (`interpret_m`).

**The referee** (decision D5) is `Protocol.interpretAmp`, on amplitude functions: a word's
`runAmp`, and for a conditioning letter the map `f ↦ ((w, b) ↦ Π_b f (w))` of
`amp_conditionOutcome`, with `Π_b` the projection `pauliProjection`. The statement
`amp_interpret` is that the interpretation of a protocol on a carrier state at its precision is a
carrier state whose amplitude is the referee's. The carrier property is part of its conclusion
because the induction over the protocol needs it at every letter (an H letter after a conditioning
letter needs the conditioned state's Lagrangian), and because `protocol_complete` takes it of the
interpretations. The outcome-bit form never vanishes on a nonzero input, since `Π_0 f + Π_1 f = f`;
a branch of weight zero is a zero evaluation of a nonzero state, not a zero state (decision D10
concerns `condition`, not this form).

**Completeness of protocol equality** (`protocol_complete`). Two protocols on the same data bits
with the same number of outcome bits, at any precisions and on any inputs, whose interpretations
are carrier states (so nonzero) with a dyadic ratio of scales (`IsDyadicRatio`, decision D9),
have equal branches at every outcome string exactly when T07's rules relate their interpretations
(`Relation.EqvGen CarrierRule`). It is a corollary of `rewrite_complete`: the branches are the
evaluations of one carrier state, and the words `w ++ o` are every word of `Fin (n + k)`. The
hypotheses are T07's, read of the interpretations.

Everything here is frame-pure (decision D5). No `FTQCLib.Hilbert` module is imported. The paper's
patterns are defined on Hilbert spaces; here the interpretation is a carrier state and the referee
acts on amplitude functions on `𝔽₂^{n+k}`, which is the frame form of the paper's computation
state `q, Γ` with the outcome map `Γ` read as the outcome bits.

## Main definitions

* `Protocol` — a protocol at precision `m` on `n` data bits with `k` conditioning letters:
  `nil`, `word` (a gate word on the `n + k` bits, feed-forward included) and `condition` (a
  conditioning letter creating the next outcome bit).
* `Protocol.interpret` — the interpretation, one carrier state on `n + k` free bits.
* `Protocol.interpretAmp` — the referee of a protocol on amplitude functions.
* `Protocol.branch`, `Protocol.branchWeight` — the evaluation of the outcome bits at an outcome
  string, and its squared norm.

## Main results

* `amp_interpret` — on a carrier state at the protocol's precision, the interpretation is a
  carrier state with the referee's amplitude (proved at T14.3.1).
* `branch_weights_sum` — the branch weights over every outcome string sum to the input's
  `ampNormSq` (proved at T14.3.2).
* `protocol_complete` — for interpretations that are carrier states with a dyadic ratio of scales,
  equal branches exactly when T07's rules relate the interpretations (proved at T14.3.3).
* `interpret_m`, `branchWeight_condition_nil` — the precision along the run, and the weight of a
  one-letter protocol's branch is T11's `outcomeWeight`.

## Implementation notes

* The type is built by appending (`word p w` is `p` then `w`; `condition p P hP` is `p` then the
  conditioning letter), so the last constructor is the last thing done, `k` counts the letters so
  far, and the final register is `Fin (n + k)` with no cast: `n + (k + 1)` and `n + k + 1` are
  the same number by definition.
* The `j`-th conditioning letter, counted from `0`, creates free bit `n + j` (`Fin.natAdd n j`):
  it is the last bit when it is created, and nothing later moves a bit. So an outcome string `o`
  is read at `Fin.append w o`.
* A word constructor rather than a letter constructor: T13's corrections (`controlledPauliWord`)
  are words, and a letter is a one-letter word. The representation is not unique (a word may be
  split, or empty); a split word has the same run (`run_append`), and nothing here depends on
  the split.
* The diagonal letter's precision and the conditioning letter's are the protocol's `m`. A
  conditioning letter on a Pauli with an odd number of Y at `m = 1` is not a term; a protocol
  needing it is written at `m = 2`, its input lifted by R7 (`PrecisionGauge.lean`).
* `protocol_complete` is not a result of the source: the measurement calculus's rewriting is
  sound, and completeness for protocol equality is this repository's extension through T07.

## References

* V. Danos, E. Kashefi and P. Panangaden, *The measurement calculus*, arXiv:quant-ph/0412135. The
  shape of the syntax (a command sequence with outcomes, conditions on dependencies), the branches
  and their probabilities; cited unit by unit above the declarations below.
* Chareton et al., *Hybrid Path-Sums*, arXiv:2604.24578 (cross-check, not cited): measurement
  and feed-forward on sums over paths with a separate classical layer, sound and not complete.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## The syntax -/

-- source: papers/measurement_calculus/
-- danos_kashefi_panangaden_quant-ph_0412135_measurement_calculus paragraph:h0a0cab23c3c0
-- source: papers/measurement_calculus/
-- danos_kashefi_panangaden_quant-ph_0412135_measurement_calculus paragraph:h059d1d394dec
/-- **A protocol** at precision `m` on `n` data bits with `k` conditioning letters so far, built by
appending. `word p w` runs the gate word `w` on the `n + k` free bits after `p`: unitary gates and
feed-forward alike, since a letter on an outcome bit is a gate controlled by that outcome.
`condition p P hP` conditions on the Pauli `P` with its sign after `p`, creating the next outcome
bit as the new last free bit; `hP` keeps the run at precision `m`. A word's letters name only bits
of `Fin (n + k)`, so feed-forward reads only outcome bits that earlier conditioning letters
created. -/
inductive Protocol (m n : ℕ) : ℕ → Type where
  /-- The empty protocol: no letter, no outcome bit. -/
  | nil : Protocol m n 0
  /-- `p`, then the gate word `w` on the data and outcome free bits. -/
  | word {k : ℕ} (p : Protocol m n k) (w : GateWord (n + k) m) : Protocol m n k
  /-- `p`, then conditioning on `P` with its sign, the outcome a new last free bit. -/
  | condition {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
      (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) : Protocol m n (k + 1)

namespace Protocol

variable {m n : ℕ}

/-! ## The interpretation and its referee -/

-- source: papers/measurement_calculus/
-- danos_kashefi_panangaden_quant-ph_0412135_measurement_calculus paragraph:h9bafbb4c7fae
/-- **The interpretation**: one carrier state on `n + k` free bits. A word runs (`run`); a
conditioning letter is `conditionOutcome`, the outcome a new last free bit and never a
parameter. -/
noncomputable def interpret : {k : ℕ} → Protocol m n k → KernelSumState n → KernelSumState (n + k)
  | _, nil, S => S
  | _, word p w, S => run w (p.interpret S)
  | _, condition p P _, S => conditionOutcome (p.interpret S) P

/-- **The referee of a protocol** (decision D5), on amplitude functions: a word's `runAmp`, and for
a conditioning letter `f ↦ ((w, b) ↦ Π_b f (w))`, the projection at the new last bit's value. -/
noncomputable def interpretAmp : {k : ℕ} → Protocol m n k →
    ((Fin n → ZMod 2) → ℂ) → (Fin (n + k) → ZMod 2) → ℂ
  | _, nil, f => f
  | _, word p w, f => runAmp w (p.interpretAmp f)
  | k + 1, condition p P _, f => fun v : Fin (n + k + 1) → ZMod 2 =>
      pauliProjection P (v (Fin.last (n + k))) (p.interpretAmp f) (Fin.init v)

@[simp] theorem interpret_nil (S : KernelSumState n) : (nil : Protocol m n 0).interpret S = S :=
  rfl

@[simp] theorem interpret_word {k : ℕ} (p : Protocol m n k) (w : GateWord (n + k) m)
    (S : KernelSumState n) : (p.word w).interpret S = run w (p.interpret S) :=
  rfl

@[simp] theorem interpret_condition {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) (S : KernelSumState n) :
    (p.condition P hP).interpret S = conditionOutcome (p.interpret S) P :=
  rfl

@[simp] theorem interpretAmp_nil (f : (Fin n → ZMod 2) → ℂ) :
    (nil : Protocol m n 0).interpretAmp f = f :=
  rfl

@[simp] theorem interpretAmp_word {k : ℕ} (p : Protocol m n k) (w : GateWord (n + k) m)
    (f : (Fin n → ZMod 2) → ℂ) : (p.word w).interpretAmp f = runAmp w (p.interpretAmp f) :=
  rfl

@[simp] theorem interpretAmp_condition {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) (f : (Fin n → ZMod 2) → ℂ) :
    (p.condition P hP).interpretAmp f = fun v : Fin (n + k + 1) → ZMod 2 =>
      pauliProjection P (v (Fin.last (n + k))) (p.interpretAmp f) (Fin.init v) :=
  rfl

/-! ## Branches -/

-- source: papers/measurement_calculus/
-- danos_kashefi_panangaden_quant-ph_0412135_measurement_calculus paragraph:hde3702006de9
/-- **A branch**: the evaluation of the outcome bits of the interpretation at the outcome string
`o`, an amplitude function on the data bits. The `j`-th conditioning letter's outcome is `o j`, at
free bit `n + j`. -/
noncomputable def branch {k : ℕ} (p : Protocol m n k) (S : KernelSumState n)
    (o : Fin k → ZMod 2) : (Fin n → ZMod 2) → ℂ :=
  fun w => amp (p.interpret S) (Fin.append w o)

/-- **The weight of a branch**: T11's squared norm `Σ_w |·|²`, of the branch's amplitude. It is
not divided by the input's norm (decision D3). -/
noncomputable def branchWeight {k : ℕ} (p : Protocol m n k) (S : KernelSumState n)
    (o : Fin k → ZMod 2) : ℝ :=
  ∑ w : Fin n → ZMod 2, Complex.normSq (p.branch S o w)

end Protocol

open Protocol

/-! ## The precision along the run -/

/-- **The run stays at the protocol's precision** on a state at that positive precision. -/
theorem interpret_m {m n k : ℕ} (p : Protocol m n k) {S : KernelSumState n} (hm1 : 1 ≤ m)
    (hm : S.m = m) : (p.interpret S).m = m := by
  induction p with
  | nil => exact hm
  | word p w ih => rw [interpret_word, run_m, ih]
  | condition p P hP ih =>
    rw [interpret_condition, conditionOutcome_m]
    rw [ih]
    refine conditionPrecision_eq P.appendZ hm1 ?_
    rw [yWeight_appendZ]
    exact hP

/-! ## The statement -/

/-- **The interpretation's amplitude.** On a carrier state `S` at the protocol's precision, the
interpretation is a carrier state, and its amplitude is the referee's: each word's `runAmp`
(T05's `amp_run`) and, at each conditioning letter, the projection `Π_b` at the new outcome bit's
value `b` (T10's `amp_conditionOutcome`). The carrier property is in the conclusion since the
induction needs it at each letter and `protocol_complete` takes it of the interpretations.
Proved at T14.3.1. -/
theorem amp_interpret {m n k : ℕ} (p : Protocol m n k) {S : KernelSumState n} (hS : IsCarrier S)
    (hm : S.m = m) :
    IsCarrier (p.interpret S) ∧ amp (p.interpret S) = p.interpretAmp (amp S) := by
  have hm1 : 1 ≤ m := hm ▸ hS.1
  induction p with
  | nil => exact ⟨hS, rfl⟩
  | word p w ih =>
    obtain ⟨hc, ha⟩ := ih
    have hpm : (p.interpret S).m = m := interpret_m p hm1 hm
    rw [interpret_word, interpretAmp_word, amp_run w hc hpm, ha]
    exact ⟨isCarrier_run w hc hpm, rfl⟩
  | condition p P hP ih =>
    obtain ⟨hc, ha⟩ := ih
    rw [interpret_condition, interpretAmp_condition, amp_conditionOutcome _ hc.2.2.1 P, ha]
    exact ⟨isCarrier_conditionOutcome hc P, rfl⟩

/-! ## The norm along the run -/

/-- The referee keeps `Σ_w |·|²` along the whole protocol. -/
private theorem sum_normSq_interpretAmp {m n k : ℕ} (p : Protocol m n k)
    (f : (Fin n → ZMod 2) → ℂ) :
    ∑ v : Fin (n + k) → ZMod 2, Complex.normSq (p.interpretAmp f v)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w) := by
  induction p with
  | nil => rfl
  | word p w ih => rw [interpretAmp_word, sum_normSq_runAmp, ih]
  | condition p P hP ih =>
    rw [interpretAmp_condition]
    exact (sum_normSq_projection P _).trans ih

/-- A sum over outcome strings and data words is a sum over the words of `Fin (N + k)`. -/
theorem sum_sum_append {N k : ℕ} (g : (Fin (N + k) → ZMod 2) → ℝ) :
    ∑ o : Fin k → ZMod 2, ∑ w : Fin N → ZMod 2, g (Fin.append w o)
      = ∑ v : Fin (N + k) → ZMod 2, g v := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Fin.appendEquiv N k) _ _ (fun _ => rfl)

/-- The outcome string `![s, u]` appended to the data bits is two snocs. -/
theorem append_pair {N : ℕ} (w : Fin N → ZMod 2) (s u : ZMod 2) :
    Fin.append w ![s, u] = Fin.snoc (Fin.snoc w s) u := by
  have h : (![s, u] : Fin 2 → ZMod 2) = Fin.snoc (fun _ : Fin 1 => s) u := by
    funext i
    fin_cases i <;> rfl
  rw [h, Fin.append_snoc, Fin.append_right_eq_snoc]

-- source: papers/measurement_calculus/
-- danos_kashefi_panangaden_quant-ph_0412135_measurement_calculus paragraph:likeli
/-- **The branch weights sum to the input's norm.** On a carrier state at the protocol's precision,
the weights of the `2^k` branches add up to `ampNormSq S`: each word keeps the norm, and each
conditioning letter splits it between the two values of its outcome bit (T11's
`outcomeWeight_add`). Proved at T14.3.2. -/
theorem branch_weights_sum {m n k : ℕ} (p : Protocol m n k) {S : KernelSumState n}
    (hS : IsCarrier S) (hm : S.m = m) :
    ∑ o : Fin k → ZMod 2, p.branchWeight S o = ampNormSq S := by
  unfold branchWeight branch ampNormSq
  rw [(amp_interpret p hS hm).2,
    sum_sum_append (fun v => Complex.normSq (p.interpretAmp (amp S) v))]
  exact sum_normSq_interpretAmp p (amp S)

/-- **Completeness of protocol equality.** Two protocols on the same data bits with the same number
of outcome bits, at any precisions and on any inputs, whose interpretations are nonzero carrier
states with a dyadic ratio of scales (decision D9), have equal branches at every outcome string
exactly when T07's rules relate their interpretations. The branches are the evaluations of one
carrier state, so this is `rewrite_complete` read through them. Proved at T14.3.3. -/
theorem protocol_complete {m m' n k : ℕ} (p : Protocol m n k) (q : Protocol m' n k)
    {S T : KernelSumState n} (hp : IsCarrier (p.interpret S)) (hq : IsCarrier (q.interpret T))
    (hc : IsDyadicRatio ((q.interpret T).c / (p.interpret S).c)) :
    (∀ o : Fin k → ZMod 2, p.branch S o = q.branch T o)
      ↔ Relation.EqvGen CarrierRule (p.interpret S) (q.interpret T) := by
  rw [rewrite_complete hp hq]
  constructor
  · intro h
    exact ⟨amp_eq_of_append_eq (fun o w => congrFun (h o) w), hc⟩
  · rintro ⟨hs, _⟩ o
    funext w
    exact congrFun hs (Fin.append w o)

/-! ## One conditioning letter -/

/-- **A one-letter protocol's branch weight is T11's weight.** Conditioning on `P` with the outcome
as a free bit, then evaluating it at `b`, has the weight `outcomeWeight S P b` of conditioning at
the parameter outcome `b`: the parameter form is an evaluation (D2 as revised). -/
theorem branchWeight_condition_nil {m n : ℕ} (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) (b : ZMod 2) :
    ((nil : Protocol m n 0).condition P hP).branchWeight S (fun _ => b) = outcomeWeight S P b := by
  unfold branchWeight branch outcomeWeight ampNormSq
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [interpret_condition, interpret_nil, Fin.append_right_eq_snoc]
  exact congrArg Complex.normSq (congrFun (conditionOutcome_eval S horth P b) w)

end FTQCLib.Frame.Walkthrough

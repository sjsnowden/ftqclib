/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.EliminationOrder
import FTQCLib.Hierarchy.PolarForm

/-!
# A degree-two carrier state that the two elimination shapes cannot move

**Question** (`explore/degree-rank/REPORT.html`, section 1). Does every carrier state whose exponent
has degree at most two reach height zero by the two elimination shapes of `BoundElimination.lean`,
collapse (`SignAffine`) and rotate (`RotateData`)? The quadratic Gauss sums of Dickson's
classification can all be evaluated, so the question is whether the two shapes are enough to
evaluate them.

**Outcome: no.** The witness has no free bits, two bound bits and precision two, with exponent
`2·y₀·y₁` over `ZMod 4` (`czGate 2 0 1`, the `CZ` exponent on the bound register) and scale
one:

* its exponent has effective level at most two (`effectiveLevel_pairExponent_le_two`);
* it is a carrier state (`isCarrier_pairState`);
* no elimination step is available at either bound bit (`eliminationStuck_pairState`): the
  difference along either bit is `0` or `2` according to the other bound bit, so it is not uniform
  in the remaining bound word, as collapse asks, and it is even, where rotate needs it odd;
* yet it presents the same state as a height-zero record (`stateEq_pairState_floor`): the four terms
  `1, 1, 1, −1` sum to `2`, and `2 / √2² = 1`.

**How to read it.** The two bound bits form a hyperbolic pair in Dickson's sense. Summing either one
against its difference forces the other to zero, a constraint on a *bound* bit, which neither shape
can express: collapse cuts the support by a condition on free bits alone. The step that removes such
a pair is the pair shape of `explore/degree-rank/elimination.py`. The exhaustive search there finds
that with it added every carrier state of degree at most two, in every cell searched, reaches height
zero in every order. This file checks only the witness.

The witness is the first carrier state of its cell, in that search's order, with no sequence
reaching height zero (`explore/degree-rank/outputs/elimination.json`, cell `n = 0, h = 2`,
`first_stuck_two_shapes`).
-/

namespace FTQCLib.Explore.DegreeRank

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer
open FTQCLib.Frame.Walkthrough

/-- The witness exponent `2·y₀·y₁` over `ZMod 4`, on two bound bits and no free bits. -/
noncomputable def pairExponent : DiagPhase (0 + 2) 2 :=
  czGate 2 0 1

/-- The witness: no free bits, two bound bits, precision two, scale one, the empty support data. -/
noncomputable def pairState : KernelSumState 0 :=
  ⟨2, 2, pairExponent, 1, ⊥, 0⟩

/-- The height-zero record presenting the same state: exponent zero, scale one. -/
noncomputable def floorState : KernelSumState 0 :=
  ⟨2, 0, 0, 1, ⊥, 0⟩

/-- The witness exponent has effective level at most two: it is a degree-two phase. -/
theorem effectiveLevel_pairExponent_le_two : effectiveLevel pairExponent ≤ 2 :=
  effectiveLevel_czGate_le_two 2 0 1

/-! ## Evaluation on the words -/

/-- The moved exponent evaluates as the original at the word read through the transposition (the
same fact as the private `eval_boundToLast` of `EliminationOrder.lean`). -/
theorem eval_boundToLast' {m h : ℕ} (j : Fin (h + 1)) (Q : DiagPhase (0 + (h + 1)) m)
    (v : Fin (0 + h + 1) → ZMod 2) :
    DiagPhase.eval (boundToLast j Q) v
      = DiagPhase.eval Q (v ∘ Equiv.swap (Fin.natAdd 0 j) (Fin.last (0 + h))) := by
  unfold boundToLast DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  rfl

/-- With no free bits and `L = ⊥`, the one (empty) word is on the support. -/
theorem mem_support_bot' :
    ∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 0)), (0 : Fin 0 → ZMod 2) = 0 + p.X :=
  ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩

/-- The difference along either bound bit, moved last, is `0` where the other bound bit is `0` and
`2` where it is `1`. -/
theorem lastDiff_pairExponent (j : Fin (1 + 1)) :
    (lastDiff (boundToLast j pairExponent)).eval (Fin.append (0 : Fin 0 → ZMod 2) ![0]) = 0
      ∧ (lastDiff (boundToLast j pairExponent)).eval (Fin.append (0 : Fin 0 → ZMod 2) ![1])
        = 2 := by
  fin_cases j <;>
  · simp only [lastDiff_eval, eval_boundToLast', pairExponent, czGate, DiagPhase.eval_mul,
      DiagPhase.eval_C, DiagPhase.eval_X]
    decide

/-! ## Stuck -/

/-- At `n = 0`, `h = 1`, `m = 2`, `L = ⊥`: a difference that is `0` at one remaining bound word
and `2` at the other admits no step. Collapse would make it one value for both words; rotate would
make it odd. -/
theorem not_stepAvailable_of_zero_two {Q : DiagPhase (0 + (1 + 1)) 2} {j : Fin (1 + 1)}
    (hZero : (lastDiff (boundToLast j Q)).eval (Fin.append (0 : Fin 0 → ZMod 2) ![0]) = 0)
    (hTwo : (lastDiff (boundToLast j Q)).eval (Fin.append (0 : Fin 0 → ZMod 2) ![1]) = 2) :
    ¬ StepAvailable Q ⊥ 0 j := by
  have twoNeZero : (2 : ZMod (2 ^ 2)) ≠ 0 := by decide
  have evenNotRotate : ∀ (a : ZMod (2 ^ 2)) (b : ZMod 2), 2 * a = 2 ^ (2 - 1) →
      (0 : ZMod (2 ^ 2)) ≠ a + 2 ^ (2 - 1) * ((b.val : ℕ) : ZMod (2 ^ 2)) := by
    decide
  rintro (⟨σ, ε, hs⟩ | ⟨a, Λ, ha, hr⟩)
  · have atZero := hs 0 mem_support_bot' ![0]
    have atOne := hs 0 mem_support_bot' ![1]
    rw [hZero] at atZero
    rw [hTwo] at atOne
    exact twoNeZero (atOne.trans atZero.symm)
  · obtain ⟨b, -, hb⟩ := hr 0 mem_support_bot' ![0]
    rw [hZero] at hb
    exact evenNotRotate a b ha hb

/-- **Stuck.** No elimination step is available at either bound bit of the witness. -/
theorem eliminationStuck_pairState :
    EliminationStuck (h := 1) pairState.Q pairState.L pairState.x₀ := by
  intro j
  exact not_stepAvailable_of_zero_two (lastDiff_pairExponent j).1 (lastDiff_pairExponent j).2

/-! ## The same state at height zero -/

/-- A sum over one bit. -/
theorem sum_bit {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ p, f p = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton]

/-- A sum over the four words of two bits. -/
theorem sum_two_bits {M : Type*} [AddCommMonoid M] (F : (Fin 2 → ZMod 2) → M) :
    ∑ y, F y = F ![0, 0] + F ![0, 1] + (F ![1, 0] + F ![1, 1]) := by
  rw [← (piFinTwoEquiv fun _ => ZMod 2).symm.sum_comp F, Fintype.sum_prod_type, sum_bit, sum_bit,
    sum_bit]
  rfl

/-- The witness exponent at the four bound words: `0, 0, 0, 2`. -/
theorem eval_pairExponent_words :
    DiagPhase.eval pairExponent (Fin.append (0 : Fin 0 → ZMod 2) ![0, 0]) = 0
      ∧ DiagPhase.eval pairExponent (Fin.append (0 : Fin 0 → ZMod 2) ![0, 1]) = 0
      ∧ DiagPhase.eval pairExponent (Fin.append (0 : Fin 0 → ZMod 2) ![1, 0]) = 0
      ∧ DiagPhase.eval pairExponent (Fin.append (0 : Fin 0 → ZMod 2) ![1, 1]) = 2 := by
  simp only [pairExponent, czGate, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
  decide

/-- `charOf 2 2 = −1`. -/
theorem charOf_two_two' : charOf 2 2 = -1 := by
  rw [show (2 : ZMod (2 ^ 2)) = 2 ^ (2 - 1) * ((1 : ℕ) : ZMod (2 ^ 2)) from by decide,
    charOf_two_pow_mul (by norm_num), pow_one]

/-- The witness's amplitude at the empty word is `1`. -/
theorem amp_pairState_zero : amp pairState (0 : Fin 0 → ZMod 2) = 1 := by
  rw [amp_pos (S := pairState) mem_support_bot']
  change ampCore 2 2 pairExponent 1 0 = 1
  obtain ⟨e00, e01, e10, e11⟩ := eval_pairExponent_words
  rw [ampCore_eq_sum_charOf, sum_two_bits, e00, e01, e10, e11, charOf_zero, charOf_two_two']
  have hsqrt : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hsqrt]
  norm_num

/-- The height-zero record's amplitude at the empty word is `1`. -/
theorem amp_floorState_zero : amp floorState (0 : Fin 0 → ZMod 2) = 1 := by
  rw [amp_pos (S := floorState) mem_support_bot']
  change ampCore 2 0 (0 : DiagPhase (0 + 0) 2) 1 0 = 1
  rw [ampCore_eq_sum_charOf, Fintype.sum_unique]
  simp [DiagPhase.eval, charOf_zero]

/-- **The same state at height zero.** The witness and the height-zero record denote one
amplitude. -/
theorem stateEq_pairState_floor : StateEq pairState floorState := by
  funext w
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [amp_pairState_zero, amp_floorState_zero]

/-- The witness is a carrier state. -/
theorem isCarrier_pairState : IsCarrier pairState := by
  have hzero : ∀ p : Pauli 0, p = 0 := fun p =>
    Pauli.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  refine ⟨(by norm_num : (1 : ℕ) ≤ 2), fun p _ q _ => ?_, fun p _ => ?_, fun h => ?_⟩
  · rw [hzero p]
    exact omega_zero_left q
  · rw [hzero p]
    exact Submodule.zero_mem _
  · have h0 := congrFun h 0
    rw [amp_pairState_zero] at h0
    exact one_ne_zero h0

end FTQCLib.Explore.DegreeRank

/-! ## Axioms -/

/-- info: 'FTQCLib.Explore.DegreeRank.eliminationStuck_pairState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Explore.DegreeRank.eliminationStuck_pairState

/-- info: 'FTQCLib.Explore.DegreeRank.stateEq_pairState_floor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Explore.DegreeRank.stateEq_pairState_floor

/-- info: 'FTQCLib.Explore.DegreeRank.isCarrier_pairState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Explore.DegreeRank.isCarrier_pairState

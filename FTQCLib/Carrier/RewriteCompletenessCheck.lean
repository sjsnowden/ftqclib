/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.RewriteCompleteness
import FTQCLib.Carrier.EliminationOrder
import FTQCLib.Carrier.CarrierRulesCheck

/-!
# Check: `rewrite_complete` on T04's two outcomes and a non-dyadic pair

T07's witness (`docs/STEPS.md`, "The unit", phase 2): rows that test the frozen statement of
`FTQCLib/Carrier/RewriteCompleteness.lean` on small cases.

* **Agreement.** T04's two stuck outcomes (`FTQCLib/Carrier/EliminationOrder.lean`,
  `EliminationOrder.outcomeA`, `EliminationOrder.outcomeB`) are both reached from
  `EliminationOrder.input` by one gauge relabelling (R5, moving the rotated bit last) followed by
  one `CarrierRule.rotate` step; `Relation.EqvGen CarrierRule` is symmetric and transitive, so the
  two outcomes are related through the input, matching decision D8's closing sentence
  (`docs/decisions/T04.md`): "the two stuck outcomes of T04 are related, through the input."
* **Discriminating.** `CarrierRulesCheck.lean`'s non-dyadic pair (`onePair`, scale `1`, and
  `triplePair`, scale `3/√2`) is not joined by a single `CarrierRule` step there; here the same
  pair is shown not joined by any chain: every step of `Relation.EqvGen CarrierRule` multiplies
  the scale by a dyadic ratio (`exists_isDyadicRatio_of_carrierRule`), and the dyadic ratios are
  closed under the group operations, so the whole chain does too
  (`exists_isDyadicRatio_of_eqvGen`); `3/√2` is not dyadic (`nine_div_two_ne_zpow`,
  `sq_norm_eq_zpow_of_isDyadicRatio`, exactly as in the single-step
  row), so no chain, of any length, joins the pair. This discriminates `rewrite_complete`'s
  conjunction from a weaker statement that dropped the dyadic-ratio condition: it is not enough to
  test the frozen statement at the single-step level, since the theorem is about the whole
  equivalence closure.

## Implementation notes

The gauge relabelling in the agreement row reuses `EliminationOrder.inputExponent`'s own bit-swap
identity, proved the same way `EliminationOrder.lean` proves `stateEq_outcomeB_input`: fix the one
(trivial) free word, name the three bound bits, rewrite `DiagPhase.eval` down to `ZMod 4` arithmetic
with `eval_add`, `eval_mul`, `eval_C`, `eval_X`, and close the finite check with `decide`. The
public twin `FTQCLib.Explore.CyclotomicKernelB.eval_boundToLast` is used in place of
`EliminationOrder.lean`'s private copy.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer
open FTQCLib.Frame.Walkthrough.EliminationOrder

/-! ## Agreement: T04's two outcomes, related through the input -/

section Agreement

/-- The input with bound bit `0` moved last: the state `CarrierRule.rotate` eliminates to reach
`outcomeA`. -/
noncomputable def intermediateA : KernelSumState 0 :=
  ⟨2, 3, boundToLast (h := 2) 0 inputExponent, 1, ⊥, 0⟩

/-- The input with bound bit `1` moved last: the state `CarrierRule.rotate` eliminates to reach
`outcomeB`. -/
noncomputable def intermediateB : KernelSumState 0 :=
  ⟨2, 3, boundToLast (h := 2) 1 inputExponent, 1, ⊥, 0⟩

/-- **The relabelling to `intermediateA`.** R5, moving bound bit `0` last: `inputExponent` at a
word agrees with its `boundToLast 0` image at the word with bound bits `0` and `2` swapped back —
table-checked, the same way `stateEq_outcomeB_input` checks the `j = 1` case. -/
theorem gaugeStep_input_intermediateA : GaugeStep input intermediateA :=
  GaugeStep.renameBound (n := 0) (h := 3) (boundToLast (n := 0) (h := 2) 0 inputExponent)
    inputExponent 1 ⊥ 0
    ((Equiv.swap (0 : Fin 3) 2).arrowCongr (Equiv.refl (ZMod 2)))
    (by
      intro w y
      rw [FTQCLib.Explore.CyclotomicKernelB.eval_boundToLast]
      obtain rfl : w = 0 := Subsingleton.elim _ _
      obtain ⟨a, b, d, rfl⟩ : ∃ a b d : ZMod 2, y = ![a, b, d] :=
        ⟨y 0, y 1, y 2, by funext i; fin_cases i <;> rfl⟩
      simp only [inputExponent, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
        DiagPhase.eval_X]
      revert a b d
      decide)

/-- **The relabelling to `intermediateB`.** R5, moving bound bit `1` last: symmetric to
`gaugeStep_input_intermediateA`, swapping bound bits `1` and `2`. -/
theorem gaugeStep_input_intermediateB : GaugeStep input intermediateB :=
  GaugeStep.renameBound (n := 0) (h := 3) (boundToLast (n := 0) (h := 2) 1 inputExponent)
    inputExponent 1 ⊥ 0
    ((Equiv.swap (1 : Fin 3) 2).arrowCongr (Equiv.refl (ZMod 2)))
    (by
      intro w y
      rw [FTQCLib.Explore.CyclotomicKernelB.eval_boundToLast]
      obtain rfl : w = 0 := Subsingleton.elim _ _
      obtain ⟨a, b, d, rfl⟩ : ∃ a b d : ZMod 2, y = ![a, b, d] :=
        ⟨y 0, y 1, y 2, by funext i; fin_cases i <;> rfl⟩
      simp only [inputExponent, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
        DiagPhase.eval_X]
      revert a b d
      decide)

/-- **One step, `input` to `intermediateA`.** -/
theorem step_input_intermediateA : CarrierRule input intermediateA :=
  CarrierRule.gauge gaugeStep_input_intermediateA

/-- **One step, `input` to `intermediateB`.** -/
theorem step_input_intermediateB : CarrierRule input intermediateB :=
  CarrierRule.gauge gaugeStep_input_intermediateB

/-- **One rotate step, `intermediateA` to `outcomeA`.** -/
theorem step_intermediateA_outcomeA : CarrierRule intermediateA outcomeA :=
  CarrierRule.rotate (by norm_num) (boundToLast (h := 2) 0 inputExponent) 1 ⊥ 0 1 lambdaA
    rotateData_stepA ⊥ 0 (fun _ => Iff.rfl)

/-- **One rotate step, `intermediateB` to `outcomeB`.** -/
theorem step_intermediateB_outcomeB : CarrierRule intermediateB outcomeB :=
  CarrierRule.rotate (by norm_num) (boundToLast (h := 2) 1 inputExponent) 1 ⊥ 0 1 lambdaB
    rotateData_stepB ⊥ 0 (fun _ => Iff.rfl)

/-- **`input` reaches `outcomeA`.** -/
theorem eqvGen_input_outcomeA : Relation.EqvGen CarrierRule input outcomeA :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ step_input_intermediateA)
    (Relation.EqvGen.rel _ _ step_intermediateA_outcomeA)

/-- **`input` reaches `outcomeB`.** -/
theorem eqvGen_input_outcomeB : Relation.EqvGen CarrierRule input outcomeB :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ step_input_intermediateB)
    (Relation.EqvGen.rel _ _ step_intermediateB_outcomeB)

/-- **Agreement.** T04's two outcomes, both reached from `input` by one relabelling and one
rotation, are related by `Relation.EqvGen CarrierRule`: through `input`, by symmetry and
transitivity, matching decision D8's "the two stuck outcomes of T04 are related, through the
input" (`docs/decisions/T04.md`). -/
-- row: agreement
theorem outcomeA_outcomeB_agreement :
    Relation.EqvGen CarrierRule input outcomeA ∧ Relation.EqvGen CarrierRule input outcomeB
      ∧ Relation.EqvGen CarrierRule outcomeA outcomeB :=
  ⟨eqvGen_input_outcomeA, eqvGen_input_outcomeB,
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ eqvGen_input_outcomeA)
      eqvGen_input_outcomeB⟩

end Agreement

/-! ## Discriminating: no chain joins a non-dyadic scale ratio -/

section Discriminating

/-- **Discriminating.** `onePair` (scale `1`) and `triplePair` (scale `3/√2`) are not joined by
any chain of `CarrierRule` steps: the chain's scale ratio would be dyadic
(`exists_isDyadicRatio_of_eqvGen`), but `‖3/√2‖² = 9/2` is not an integer power of two
(`nine_div_two_ne_zpow`, `sq_norm_eq_zpow_of_isDyadicRatio`), exactly the single-step obstruction of
`no_step_joins_scale_ratio`, now shown to hold at every length. This discriminates
`rewrite_complete`'s dyadic-ratio conjunct: a version of the statement testing only single steps
would miss that the whole closure is obstructed, not just one step of it. -/
-- row: discriminating
theorem no_chain_joins_scale_ratio :
    ¬ Relation.EqvGen CarrierRule onePair triplePair := by
  intro hchain
  obtain ⟨r, hr, hc⟩ := exists_isDyadicRatio_of_eqvGen hchain
  obtain ⟨e, he⟩ := sq_norm_eq_zpow_of_isDyadicRatio hr
  apply nine_div_two_ne_zpow e
  rw [← he]
  have hcr : r = (3 : ℂ) / (Real.sqrt 2 : ℂ) := by
    have heq : triplePair.c = r * onePair.c := hc
    simp only [onePair, triplePair, mul_one] at heq
    exact heq.symm
  rw [hcr, norm_div, show ‖(3 : ℂ)‖ = 3 from by norm_num,
    show ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)],
    div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end Discriminating

/-! ## Inhabitation: `rewrite_complete`'s hypotheses, held together by a concrete pair -/

section Inhabitation

/-- `outcomeA` is a carrier state: same free variables, submodule `⊥` and precision `2` as
`input` (`isCarrier_input`), and the same nonzero denotation, since `StateEq outcomeA input`
(`stateEq_outcomeA_input`) is amplitude equality. -/
theorem isCarrier_outcomeA : IsCarrier outcomeA := by
  have hzero : ∀ p : Pauli 0, p = 0 := fun p => Pauli.ext (Subsingleton.elim _ _)
    (Subsingleton.elim _ _)
  refine ⟨(by norm_num : (1 : ℕ) ≤ 2), fun p _ q _ => ?_, fun p _ => ?_, ?_⟩
  · rw [hzero p]
    exact omega_zero_left q
  · rw [hzero p]
    exact Submodule.zero_mem _
  · rw [stateEq_outcomeA_input]
    exact isCarrier_input.2.2.2

/-- **Inhabitation.** `input` and `outcomeA` are both carrier states, so `rewrite_complete`'s
hypotheses `hS`, `hT` hold together on a concrete pair; the theorem then reduces to the earlier
agreement fact (`eqvGen_input_outcomeA`) and the dyadic-ratio witness `1` (both states have scale
`1`, `EliminationOrder.input`, `EliminationOrder.elimRotate`). -/
-- row: inhabitation
theorem rewrite_complete_inhabited :
    Relation.EqvGen CarrierRule input outcomeA ↔
      StateEq input outcomeA ∧ IsDyadicRatio (outcomeA.c / input.c) :=
  rewrite_complete isCarrier_input isCarrier_outcomeA

end Inhabitation

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.rewrite_complete' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rewrite_complete

/-- info: 'FTQCLib.Frame.Walkthrough.rewrite_conservative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rewrite_conservative

end FTQCLib.Frame.Walkthrough

-- mutant: complete_ratio | FTQCLib/Carrier/RewriteCompleteness.lean | StateEq S T ∧ IsDyadicRatio (T.c / S.c) := by | StateEq S T ∧ IsDyadicRatio (S.c / T.c) := by

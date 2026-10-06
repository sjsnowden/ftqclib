/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Doubling
import FTQCLib.Carrier.UnreadBitsCheck

/-!
# Check: T49, the doubling

T49's check (`docs/STEPS.md`, T49.4), completing T49.2's witness rows on the frozen statement of
`Doubling.lean` with the axiom sweep and an aimed mutant. Every headline `Doubling.lean` names (`choi_eq_iff`, `choi_measured_eq_iff`,
`choi_mem_dyadic`, `isCarrier_choi`, `amp_choi`, `choi_gram_eq_iff`, `isDilation_dilation`,
`channel_ne_of_forall_dilation`, `rotation_not_realised`) is proved, at T49.3, T49.3.1 and
T49.3.2 (`docs/STEPS.md`, entries 2026-10-02h and 2026-10-02i); none is `sorry`'d, and the axiom
sweep below checks each builds on no axiom beyond the standard three. The witness rows below are
about the objects the headlines name (`choi`, `choiRead`, `measured`, `readBranch`) and are
computed without any of them: a Choi amplitude is T14's `amp_interpret` on T46's identity lifted by
R7 (`amp_choi_route`, private), and each letter's referee is evaluated word by word.

* **H and CNOT (agreement).** The Choi state of H on one bit is, as a carrier state, T46's
  presentation `wordState 1 1 [H]`, and its amplitude at `(r, y)` is H's matrix entry
  `(−1)^{ry}/√2`; likewise CNOT on two bits, `wordState 2 1 [CNOT₀₁]`, with the permutation
  matrix's entry `[y = (r₀, r₁ + r₀)]`.
* **`P1` against `P2` (discriminating).** `P1` conditions on `Z` of the one data bit, the outcome
  read; `P2` is `P1` followed by `Z` on the outcome bit. Their branches have the same Gram data on
  every input at every outcome (the right side of `choi_measured_eq_iff`), their measured Choi
  states are `UnreadEq` over the copy bit, and their coherent Choi states are not `UnreadEq`: the
  Gram entries at `((0,0,0), (1,1,1))` are `1` and `−1` (fidelity note, Claim 4).
* **Read against unread (discriminating).** `P1`'s Choi state with its outcome bit read keeps the
  coherence between the reference words `0` and `1` (Gram entry `1` at `((0,0,0), (1,1,1))`); with
  the outcome bit unread it is lost (Gram entry `0` at `((0,0), (1,1))`).
* **The `3/5` rotation (inhabitation).** `rotState (2/5)` (T27's check module, `r = 6, 8, −8, 6`
  at scale `2/5`, height four) is a carrier state at precision `1` whose amplitude at `(r, y)` is
  `rotationThreeFifths y r`, the rotation's Choi amplitude, reference bit first: carrier-ness holds
  for a channel outside the tower (fidelity note, Claim 10). That no protocol realises it is
  `rotation_not_realised`, T49.3.2's, not a row here.

Scope (standard 7.3): the witness rows are about one and two data bits at precision `1` and prove
nothing about other cells.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## The protocols and the readings -/

/-- H on the one data bit, at precision `1`. -/
noncomputable def doublingHadamard : Protocol 1 1 0 :=
  Protocol.nil.word [GateLetter.hadamard 0]

/-- CNOT from data bit `0` onto data bit `1`, at precision `1`. -/
noncomputable def doublingCnot : Protocol 1 2 0 :=
  Protocol.nil.word [GateLetter.cnot 0 1 (by decide)]

/-- `P1`: conditioning on `Z` of the one data bit, at precision `1`. -/
noncomputable def doublingZCondition : Protocol 1 1 1 :=
  Protocol.nil.condition ⟨0, zPauli (Pi.single 0 1)⟩ (zPauli_precision 1 _)

/-- `P2`: `P1`, then `Z` on the outcome bit (free bit `1`). -/
noncomputable def doublingZConditionZ : Protocol 1 1 1 :=
  doublingZCondition.word [GateLetter.diagonal (MvPolynomial.X 1)]

/-- The one outcome bit read. -/
def doublingRead : Fin 1 ≃ Fin (1 + 0) := Equiv.refl _

/-- The one outcome bit unread. -/
def doublingUnread : Fin 1 ≃ Fin (0 + 1) := Equiv.refl _

/-! ## Evaluation -/

/-- The Choi amplitude by T14 and T46: `amp_interpret` on the identity lifted by R7. -/
private theorem amp_choi_route {m n k : ℕ} (p : Protocol m n k) (hm : 1 ≤ m) :
    amp (choi p) = p.onSecondHalf.interpretAmp (amp (idState n)) := by
  unfold choi idAt
  rw [(amp_interpret _ (isCarrier_liftPrecision (isCarrier_idState n) _ _)
    (max_eq_right hm)).2, amp_liftPrecision]

private theorem append_zero_zero {a b : ℕ} :
    Fin.append (0 : Fin a → ZMod 2) (0 : Fin b → ZMod 2) = 0 := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

private theorem signOf_mul_conj (b : ZMod 2) : signOf b * starRingEnd ℂ (signOf b) = 1 := by
  rcases zmod_two_dichotomy b with h | h <;> rw [h] <;> simp [signOf_zero, signOf_one]

/-- Evaluate a referee at a concrete word: projections, phases and the identity's amplitude. -/
local macro "doubling_eval" : tactic =>
  `(tactic| (
    simp (config := {decide := true}) [doublingZCondition, doublingZConditionZ, measured,
      copyReadBits, Protocol.onSecondHalf, secondHalfLetter, secondHalfBit, letterAmp,
      runAmp_cons, runAmp_nil, pauliProjection_apply, shiftFactor, secondHalfPauli, zPauli,
      amp_idState, zDot, yWeight, Fin.sum_univ_succ, Fin.init, Function.comp_def,
      append_zero_zero, DiagPhase.eval, MvPolynomial.eval_rename, MvPolynomial.eval_X,
      DiagPhase.liftBinary, signOf_zero, signOf_one, charOf_zero, charOf_one_one]
    all_goals (first | norm_num | decide)))

/-- Split a bit into its two values, as literals. -/
local macro "bit_cases " a:ident : tactic =>
  `(tactic| (rcases zmod_two_dichotomy $a with h | h <;> subst h))

/-- `P1`'s Choi amplitude: `[r = d]·[o = d]` at reference `r`, data `d` and outcome `o`. -/
private theorem zCondition_amp (a b c : ZMod 2) :
    doublingZCondition.onSecondHalf.interpretAmp (amp (idState 1)) ![a, b, c]
      = if a = b ∧ c = b then 1 else 0 := by
  bit_cases a <;> bit_cases b <;> bit_cases c <;> doubling_eval

/-- `P2`'s Choi amplitude: `P1`'s times `(−1)^o`. -/
private theorem zConditionZ_amp (a b c : ZMod 2) :
    doublingZConditionZ.onSecondHalf.interpretAmp (amp (idState 1)) ![a, b, c]
      = if a = b ∧ c = b then signOf c else 0 := by
  bit_cases a <;> bit_cases b <;> bit_cases c <;> doubling_eval

/-- The measured `P1`'s Choi amplitude. -/
private theorem measured_zCondition_amp (a b c d : ZMod 2) :
    (measured doublingZCondition doublingRead).onSecondHalf.interpretAmp (amp (idState 1))
      ![a, b, c, d] = if a = b ∧ c = b ∧ d = c then 1 else 0 := by
  bit_cases a <;> bit_cases b <;> bit_cases c <;> bit_cases d <;> doubling_eval

/-- The measured `P2`'s Choi amplitude. -/
private theorem measured_zConditionZ_amp (a b c d : ZMod 2) :
    (measured doublingZConditionZ doublingRead).onSecondHalf.interpretAmp (amp (idState 1))
      ![a, b, c, d] = if a = b ∧ c = b ∧ d = c then signOf d else 0 := by
  bit_cases a <;> bit_cases b <;> bit_cases c <;> bit_cases d <;> doubling_eval

/-- `P2`'s measured Choi amplitude is `P1`'s times the sign of the copy bit, the last bit. -/
private theorem measured_sign (v : Fin ((1 + 1) + (1 + 1)) → ZMod 2) :
    (measured doublingZConditionZ doublingRead).onSecondHalf.interpretAmp (amp (idState 1)) v
      = signOf (v 3) *
        (measured doublingZCondition doublingRead).onSecondHalf.interpretAmp
          (amp (idState 1)) v := by
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, measured_zConditionZ_amp, measured_zCondition_amp]
  by_cases h : v 0 = v 1 ∧ v 2 = v 1 ∧ v 3 = v 2
  · simp [h]
  · simp [h]

/-- The Gram data with no unread bit: one product. -/
private theorem gram_no_unread {N : ℕ} (f : (Fin (N + 0) → ZMod 2) → ℂ)
    (x y : Fin N → ZMod 2) :
    gram (k := 0) f x y
      = f (Fin.append x Fin.elim0) * starRingEnd ℂ (f (Fin.append y Fin.elim0)) := by
  unfold gram
  rw [Fintype.sum_unique]
  congr 3

/-- The sign `charOf 1 b` of a bit has modulus one. -/
private theorem charOf_bit_mul_conj (b : ZMod 2) :
    charOf 1 ((b.val : ℕ) : ZMod (2 ^ 1))
      * starRingEnd ℂ (charOf 1 ((b.val : ℕ) : ZMod (2 ^ 1)))
      = 1 := by
  rcases zmod_two_dichotomy b with h | h <;> rw [h]
  · simp [charOf_zero]
  · simp [charOf_one_one]

/-! ## Gram entries of `P1` and `P2` -/

/-- Reading the one outcome bit keeps the word. -/
private theorem read_word (w : Fin ((1 + 1) + 1) → ZMod 2) :
    (Fin.append w Fin.elim0 : Fin (((1 + 1) + 1) + 0) → ZMod 2)
      ∘ readingEquiv (1 + 1) doublingRead = w := by
  funext i
  fin_cases i <;> rfl

/-- `P1` read: the Gram entry at `((0,0,0), (1,1,1))` is `1`. -/
private theorem gram_zCondition_read :
    gram (k := 0) (amp (choiRead doublingZCondition doublingRead)) ![0, 0, 0] ![1, 1, 1] = 1 := by
  rw [gram_no_unread]
  unfold choiRead
  rw [amp_reindexFreeBits, amp_choi_route _ le_rfl]
  beta_reduce
  rw [read_word, read_word, zCondition_amp, zCondition_amp]
  simp

/-- `P2` read: the Gram entry at `((0,0,0), (1,1,1))` is `−1`. -/
private theorem gram_zConditionZ_read :
    gram (k := 0) (amp (choiRead doublingZConditionZ doublingRead)) ![0, 0, 0] ![1, 1, 1]
      = -1 := by
  rw [gram_no_unread]
  unfold choiRead
  rw [amp_reindexFreeBits, amp_choi_route _ le_rfl]
  beta_reduce
  rw [read_word, read_word, zConditionZ_amp, zConditionZ_amp]
  simp [signOf_zero, signOf_one]

/-- Leaving the one outcome bit unread keeps the word. -/
private theorem unread_word (w : Fin (1 + 1) → ZMod 2) (u : Fin 1 → ZMod 2) :
    (Fin.append w u : Fin (((1 + 1) + 0) + 1) → ZMod 2)
      ∘ readingEquiv (1 + 1) doublingUnread = ![w 0, w 1, u 0] := by
  funext i
  fin_cases i <;> rfl

/-- `P1` unread: the Gram entry at `((0,0), (1,1))` is `0`. -/
private theorem gram_zCondition_unread :
    gram (k := 1) (amp (choiRead doublingZCondition doublingUnread)) ![0, 0] ![1, 1] = 0 := by
  unfold gram choiRead
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [amp_reindexFreeBits, amp_choi_route _ le_rfl]
  beta_reduce
  rw [unread_word, unread_word, zCondition_amp, zCondition_amp]
  rcases zmod_two_dichotomy (u 0) with h | h <;> simp [h]

/-! ## `P1` and `P2` branch by branch and measured -/

/-- `P2`'s branch is `P1`'s times the sign of the outcome. -/
private theorem readBranch_zConditionZ (f : (Fin 1 → ZMod 2) → ℂ) (o : Fin 1 → ZMod 2) :
    readBranch doublingZConditionZ doublingRead f o
      = fun v => charOf 1 (((o 0).val : ℕ) : ZMod (2 ^ 1))
          * readBranch doublingZCondition doublingRead f o v := by
  funext v
  unfold readBranch doublingZConditionZ
  rw [Protocol.interpretAmp_word, runAmp_cons, runAmp_nil]
  simp only [letterAmp, DiagPhase.eval, MvPolynomial.eval_X, DiagPhase.liftBinary]
  rfl

/-- `P1` against `P2` branch by branch: the same Gram data on every input at every outcome. -/
private theorem zCondition_branches (f : (Fin 1 → ZMod 2) → ℂ) (o : Fin 1 → ZMod 2)
    (x y : Fin 1 → ZMod 2) :
    gram (readBranch doublingZCondition doublingRead f o) x y
      = gram (readBranch doublingZConditionZ doublingRead f o) x y := by
  rw [readBranch_zConditionZ]
  unfold gram
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_mul]
  linear_combination (-(readBranch doublingZCondition doublingRead f o (Fin.append x u)
    * starRingEnd ℂ (readBranch doublingZCondition doublingRead f o (Fin.append y u))))
    * charOf_bit_mul_conj (o 0)

/-- The measured reading's reindexing sends the copy bit to the last position. -/
private theorem measured_word_three (w : Fin ((1 + 1) + 1) → ZMod 2)
    (u : Fin (0 + 1) → ZMod 2) :
    (Fin.append w u ∘ readingEquiv (1 + 1) (measuredReading doublingRead)) 3 = u 0 := rfl

/-- `P1` against `P2` measured: `UnreadEq` over the copy bit. -/
private theorem zCondition_measured :
    UnreadEq (0 + 1) (choiRead (measured doublingZCondition doublingRead)
        (measuredReading doublingRead))
      (choiRead (measured doublingZConditionZ doublingRead) (measuredReading doublingRead)) := by
  intro x y
  unfold gram choiRead
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [amp_reindexFreeBits, amp_reindexFreeBits, amp_choi_route _ le_rfl,
    amp_choi_route _ le_rfl]
  beta_reduce
  rw [measured_sign, measured_sign, measured_word_three, measured_word_three, map_mul]
  linear_combination (-((measured doublingZCondition doublingRead).onSecondHalf.interpretAmp
      (amp (idState 1)) (Fin.append x u ∘ readingEquiv (1 + 1) (measuredReading doublingRead))
    * starRingEnd ℂ ((measured doublingZCondition doublingRead).onSecondHalf.interpretAmp
      (amp (idState 1)) (Fin.append y u ∘ readingEquiv (1 + 1) (measuredReading doublingRead)))))
    * signOf_mul_conj (u 0)

/-! ## The `3/5` rotation -/

/-- `rotState (2/5)` is a carrier state: its amplitude at `(0, 0)` is `3/5`. -/
private theorem isCarrier_rotState_twoFifths : IsCarrier (rotState (2 / 5)) := by
  refine ⟨le_rfl, isStabilizer_lagNoZ _, orthogonal_lagNoZ _, fun h => ?_⟩
  have h0 := congrFun h ![0, 0]
  rw [amp_rotState_00] at h0
  norm_num at h0

/-! ## The rows -/

-- source: papers/categorical_qm/
-- Backens_2014_zx_calculus_complete_stabilizer_1307.7025 theorem:thm:Choi-Jamiolkowski
-- row: agreement
/-- **H.** The Choi state of H on one bit is T46's presentation of the word `[H]`, and its
amplitude at `(r, y)` is H's matrix entry `(−1)^{ry}/√2`, by T14 on the identity. -/
theorem row_choi_hadamard :
    choi doublingHadamard = wordState 1 1 [GateLetter.hadamard 0]
      ∧ ∀ r y : ZMod 2,
          amp (choi doublingHadamard) ![r, y] = signOf (r * y) / (Real.sqrt 2 : ℂ) := by
  refine ⟨rfl, fun r y => ?_⟩
  rw [amp_choi_route _ le_rfl]
  bit_cases r <;> bit_cases y <;>
    simp (config := {decide := true}) [doublingHadamard, Protocol.onSecondHalf, secondHalfLetter,
      secondHalfBit, runAmp_cons, runAmp_nil, letterAmp, walshTransform, amp_idState,
      Function.comp_def, signOf_zero, signOf_one, neg_div]

-- source: papers/categorical_qm/
-- Backens_2014_zx_calculus_complete_stabilizer_1307.7025 theorem:thm:Choi-Jamiolkowski
-- row: agreement
/-- **CNOT.** The Choi state of CNOT from bit `0` onto bit `1` is T46's presentation of the word
`[CNOT₀₁]`, and its amplitude at `(r, y)` is the permutation matrix's entry
`[y = (r₀, r₁ + r₀)]`, by T14 on the identity. -/
theorem row_choi_cnot :
    choi doublingCnot = wordState 2 1 [GateLetter.cnot 0 1 (by decide)]
      ∧ ∀ r₀ r₁ y₀ y₁ : ZMod 2, amp (choi doublingCnot) ![r₀, r₁, y₀, y₁]
          = if y₀ = r₀ ∧ y₁ = r₁ + r₀ then 1 else 0 := by
  refine ⟨rfl, fun r₀ r₁ y₀ y₁ => ?_⟩
  rw [amp_choi_route _ le_rfl]
  bit_cases r₀ <;> bit_cases r₁ <;> bit_cases y₀ <;> bit_cases y₁ <;>
    simp (config := {decide := true}) [doublingCnot, Protocol.onSecondHalf, secondHalfLetter,
      secondHalfBit, runAmp_cons, runAmp_nil, letterAmp, DiagPhase.cnotBitMap, amp_idState,
      Function.comp_def]

-- row: discriminating
/-- **`P1` against `P2`.** Conditioning on `Z` with the outcome read, against the same followed by
`Z` on the outcome bit: equal branch by branch (the same Gram data on every input at every
outcome) and as measured channels (`UnreadEq` over the copy bit), and not `UnreadEq` as coherent
Choi states, the Gram entries at `((0,0,0), (1,1,1))` being `1` and `−1`. -/
theorem row_zCondition_coherent_measured :
    (∀ (f : (Fin 1 → ZMod 2) → ℂ) (o : Fin 1 → ZMod 2) (x y : Fin 1 → ZMod 2),
        gram (readBranch doublingZCondition doublingRead f o) x y
          = gram (readBranch doublingZConditionZ doublingRead f o) x y)
      ∧ UnreadEq (0 + 1)
          (choiRead (measured doublingZCondition doublingRead) (measuredReading doublingRead))
          (choiRead (measured doublingZConditionZ doublingRead) (measuredReading doublingRead))
      ∧ ¬ UnreadEq 0 (choiRead doublingZCondition doublingRead)
          (choiRead doublingZConditionZ doublingRead) := by
  refine ⟨zCondition_branches, zCondition_measured, fun h => ?_⟩
  have h01 := h ![0, 0, 0] ![1, 1, 1]
  rw [gram_zCondition_read, gram_zConditionZ_read] at h01
  norm_num at h01

-- row: discriminating
/-- **Read against unread.** `P1`'s Choi state with its outcome bit read keeps the coherence
between the reference words `0` and `1` (Gram entry `1` at `((0,0,0), (1,1,1))`); with the outcome
bit unread it is lost (Gram entry `0` at `((0,0), (1,1))`). -/
theorem row_zCondition_read_unread :
    gram (k := 0) (amp (choiRead doublingZCondition doublingRead)) ![0, 0, 0] ![1, 1, 1] = 1
      ∧ gram (k := 1) (amp (choiRead doublingZCondition doublingUnread)) ![0, 0] ![1, 1] = 0
      ∧ gram (k := 0) (amp (choiRead doublingZCondition doublingRead)) ![0, 0, 0] ![1, 1, 1]
          ≠ gram (k := 1) (amp (choiRead doublingZCondition doublingUnread)) ![0, 0] ![1, 1] := by
  refine ⟨gram_zCondition_read, gram_zCondition_unread, ?_⟩
  rw [gram_zCondition_read, gram_zCondition_unread]
  exact one_ne_zero

-- row: inhabitation
/-- **The `3/5` rotation.** `rotState (2/5)` is a carrier state at precision `1` whose amplitude
at `(r, y)` is `rotationThreeFifths y r`, the rotation's Choi amplitude, reference bit first. -/
theorem row_rotation_carrier :
    IsCarrier (rotState (2 / 5)) ∧ (rotState (2 / 5)).m = 1
      ∧ ∀ r y : ZMod 2, amp (rotState (2 / 5)) ![r, y] = rotationThreeFifths ![y] ![r] := by
  refine ⟨isCarrier_rotState_twoFifths, rfl, fun r y => ?_⟩
  bit_cases r <;> bit_cases y
  · rw [amp_rotState_00]
    unfold rotationThreeFifths
    norm_num
  · rw [amp_rotState_01]
    unfold rotationThreeFifths
    simp (config := {decide := true})
    norm_num
  · rw [amp_rotState_10]
    unfold rotationThreeFifths
    simp (config := {decide := true})
    norm_num
  · rw [amp_rotState_11]
    unfold rotationThreeFifths
    norm_num

/-! ## The aimed mutant -/

-- mutant: rotation_cosine | FTQCLib/Carrier/Doubling.lean | then 3 / 5 else | then 2 / 5 else

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_secondHalfPauli' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms yWeight_secondHalfPauli

/-- info: 'FTQCLib.Frame.Walkthrough.interpretAmp_add_smul' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interpretAmp_add_smul

/-- info: 'FTQCLib.Frame.Walkthrough.innerSum_interpretAmp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms innerSum_interpretAmp

/-- info: 'FTQCLib.Frame.Walkthrough.zPauli_precision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zPauli_precision

/-- info: 'FTQCLib.Frame.Walkthrough.choi_eq_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choi_eq_iff

/-- info: 'FTQCLib.Frame.Walkthrough.choi_measured_eq_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choi_measured_eq_iff

/-- info: 'FTQCLib.Frame.Walkthrough.choi_mem_dyadic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choi_mem_dyadic

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_choi' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isCarrier_choi

/-- info: 'FTQCLib.Frame.Walkthrough.amp_choi' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_choi

/-- info: 'FTQCLib.Frame.Walkthrough.choi_gram_eq_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choi_gram_eq_iff

/-- info: 'FTQCLib.Frame.Walkthrough.isDilation_dilation' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isDilation_dilation

/-- info: 'FTQCLib.Frame.Walkthrough.channel_ne_of_forall_dilation' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms channel_ne_of_forall_dilation

/-- info: 'FTQCLib.Frame.Walkthrough.rotation_not_realised' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rotation_not_realised

end FTQCLib.Frame.Walkthrough

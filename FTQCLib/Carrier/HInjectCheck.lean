/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.HInject
import FTQCLib.Carrier.GateWordCheck
import FTQCLib.Carrier.CarrierStateHadamardCheck

/-!
# Check: witness for T15, H inject on one qubit

T15's witness (`docs/STEPS.md`, T15.2): rows on the frozen statement of `HInject.lean`, on
one-qubit registers, input qubit `0`, at the register's precision.

* **The processing steps keep the carrier property** (`isCarrier_appendFreeBit`,
  `isCarrier_permuteFreeBits` in `Conditioning.lean`, `isCarrier_restrictZ` where the amplitude
  is nonzero in `ConditionFloor.lean`), so the
  amplitude of a processed branch is computed by the referees already proved: `amp_interpret`
  (T14), `amp_restrictZ` (T12), `amp_run` (T05) and `amp_permuteFreeBits` (T10). This is
  `amp_processBranch`, for any protocol on the register and its ancilla with one outcome bit,
  given that the branch read as a state is nonzero.
* **On one qubit** the referees are evaluated word by word: with its correction the processed
  branch is the Walsh transform of the register's amplitude at each outcome
  (`injectOuter_hInjectProtocol`); without it (`hInjectBare`: CZ and the X-measurement, no X on
  the ancilla) it is the Walsh transform of `Z^b` applied to the register
  (`injectOuter_hInjectBare`). Hence `amp_hInjectBranch_one`: on every one-qubit carrier register
  the processed branch has the amplitude of T05's run of `H_0`.
* **Rows (agreement).** The processed branch is `StateEq` to the unitary H's output on `∣0⟩`
  (`KZ`, `CarrierStateHadamardCheck.lean`), on `∣1⟩` (`K1` below) and on the height-one register
  `heightOneState` (`GateWordCheck.lean`), at both outcomes; on `∣0⟩` its value is `1/√2`
  everywhere, `walsh_delta0`'s value for H on `δ₀`.
* **Rows (discriminating).** On `∣1⟩` the protocol without its correction has processed
  branches that differ at the word `0` between the outcomes `0` and `1`, and its branch at
  outcome `1` is not `StateEq` to H's output. `∣0⟩` would not discriminate: `Z∣0⟩ = ∣0⟩`.
* **Row (inhabitation).** The height-one register meets `hInject_correct`'s hypothesis.

No row uses `hInject_correct` (proved at T15.3). The weight clauses and the clause on T07's rules
are not tested here.

Frame form (D5): the rows compare amplitude functions on the free bits; the unitary H is T05's H
letter, whose referee is the Walsh transform. `HInject.lean` imports no `FTQCLib.Hilbert`
module.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer
open Protocol

variable {n : ℕ}

/-! ## The processing of a branch, for any protocol -/

/-- **The processing of a branch of any protocol** on the register with its ancilla, as
`hInjectBranch` does it: the outcome bit evaluated at `b` and dropped, H on the measured qubit,
the ancilla moved into its place, and the measured qubit dropped at `b`. -/
noncomputable def processBranch (m : ℕ) (j : Fin n) (p : Protocol m (n + 1) 1)
    (S : KernelSumState n) (b : ZMod 2) : KernelSumState n :=
  restrictZ (Fin.last n) b
    (permuteFreeBits (Equiv.swap j.castSucc (Fin.last n))
      (run ([GateLetter.hadamard j.castSucc] : GateWord (n + 1) m)
        (restrictZ (Fin.last (n + 1)) b (p.interpret (appendFreeBit S)))))

/-- `hInjectBranch` is the processing of `hInjectProtocol`'s branch. -/
theorem hInjectBranch_eq_processBranch (m : ℕ) (j : Fin n) (S : KernelSumState n) (b : ZMod 2) :
    hInjectBranch m j S b = processBranch m j (hInjectProtocol m j) S b :=
  rfl

/-- **The amplitude of a processed branch**: the referee of the protocol, evaluated at the
outcome `b`, then the Walsh transform at the measured qubit, the swap, and the evaluation of the
measured qubit at `b`. The hypothesis is that the branch read as a state is nonzero. -/
theorem amp_processBranch {m : ℕ} (j : Fin n) (p : Protocol m (n + 1) 1) {S : KernelSumState n}
    (hS : IsCarrier S) (hm : S.m = m) (b : ZMod 2)
    (hne : (fun v => p.interpretAmp (amp (appendFreeBit S))
      (Fin.insertNth (Fin.last (n + 1)) b v)) ≠ 0) :
    amp (processBranch m j p S b) = fun w =>
      walshTransform j.castSucc
        (fun v => p.interpretAmp (amp (appendFreeBit S)) (Fin.insertNth (Fin.last (n + 1)) b v))
        (Fin.insertNth (Fin.last n) b w ∘ Equiv.swap j.castSucc (Fin.last n)) := by
  have hm1 : 1 ≤ m := hm ▸ hS.1
  have hA : IsCarrier (appendFreeBit S) := isCarrier_appendFreeBit hS
  have hI := amp_interpret p hA hm
  set R := restrictZ (Fin.last (n + 1)) b (p.interpret (appendFreeBit S)) with hR
  have hRamp : amp R = fun v => p.interpretAmp (amp (appendFreeBit S))
      (Fin.insertNth (Fin.last (n + 1)) b v) := by
    funext v
    rw [hR, amp_restrictZ hI.1, hI.2]
  have hRc : IsCarrier R := isCarrier_restrictZ hI.1 _ _ (hRamp ▸ hne)
  have hRm : R.m = m := by
    rw [hR, restrictZ_m hI.1.1]
    exact interpret_m p hm1 hm
  have hH := isCarrier_run ([GateLetter.hadamard j.castSucc] : GateWord (n + 1) m) hRc hRm
  have hP := isCarrier_permuteFreeBits (Equiv.swap j.castSucc (Fin.last n)) hH
  funext w
  change amp (restrictZ (Fin.last n) b (permuteFreeBits _ (run _ R))) w = _
  rw [amp_restrictZ hP, amp_permuteFreeBits, amp_run _ hRc hRm, hRamp]
  rfl

/-! ## The protocol without its correction -/

/-- **H inject without its correction**: CZ between bit `j` and the ancilla, then the
X-measurement of bit `j`, its outcome the new free bit `n + 1`; no X on the ancilla. -/
noncomputable def hInjectBare (m : ℕ) (j : Fin n) : Protocol m (n + 1) 1 :=
  let cz : GateWord (n + 1 + 0) m :=
    [GateLetter.diagonal (DiagPhase.czGate m j.castSucc (Fin.last n))]
  (Protocol.nil.word cz).condition ⟨0, paulix j.castSucc⟩
    (fun h => by rw [yWeight_paulix] at h; exact absurd h (by decide))

/-- H inject is its bare protocol followed by the correction. -/
theorem hInjectProtocol_eq (m : ℕ) (j : Fin n) :
    hInjectProtocol m j = (hInjectBare m j).word
      [GateLetter.cnot (Fin.last (n + 1)) (Fin.last n).castSucc (Fin.castSucc_lt_last _).ne'] :=
  rfl

/-- A one-bit amplitude function is its two values. -/
theorem fun_one_eq (f : (Fin 1 → ZMod 2) → ℂ) :
    f = fun u => if u 0 = 0 then f ![0] else f ![1] := by
  funext u
  rcases word_cases u with rfl | rfl
  · simp
  · simp

/-! ## One qubit: the referees -/

/-- The branch of H inject at outcome `b`, read as an amplitude on the input qubit and the
ancilla, on a one-qubit register of amplitude `f`. -/
noncomputable def injectInner (m : ℕ) (p : Protocol m (1 + 1) 1) (f : (Fin 1 → ZMod 2) → ℂ)
    (b : ZMod 2) : (Fin (1 + 1) → ZMod 2) → ℂ :=
  fun v => p.interpretAmp (fun u => f (Fin.init u)) (Fin.insertNth (Fin.last (1 + 1)) b v)

/-- The processed branch's referee on a one-qubit register of amplitude `f`. -/
noncomputable def injectOuter (m : ℕ) (p : Protocol m (1 + 1) 1) (f : (Fin 1 → ZMod 2) → ℂ)
    (b : ZMod 2) : (Fin 1 → ZMod 2) → ℂ :=
  fun w => walshTransform (Fin.castSucc (0 : Fin 1)) (injectInner m p f b)
    (Fin.insertNth (Fin.last 1) b w ∘ Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1))

/-- **With its correction, the processed branch is the Walsh transform**, at each outcome. -/
theorem injectOuter_hInjectProtocol {m : ℕ} (hm : 1 ≤ m) (f : (Fin 1 → ZMod 2) → ℂ)
    (b : ZMod 2) : injectOuter m (hInjectProtocol m 0) f b = walshTransform 0 f := by
  funext w
  rw [fun_one_eq f]
  simp only [injectOuter, injectInner, hInjectProtocol_eq, hInjectBare, interpretAmp_condition,
    interpretAmp_word, interpretAmp_nil, runAmp_cons, runAmp_nil, letterAmp, pauliProjection,
    SignedPauli.act, pauliAct, charOf_czGate_eval hm, yWeight_paulix, zDot_paulix, walshTransform]
  rcases word_cases w with rfl | rfl <;> fin_cases b <;>
    simp (config := { decide := true }) [DiagPhase.cnotBitMap, Fin.init, paulix, signOf] <;> ring

/-- **Without its correction, the processed branch carries `Z^b`**: at outcome `b` it is the
Walsh transform with the sign `(−1)^b` on the input's value at `1`. -/
theorem injectOuter_hInjectBare {m : ℕ} (hm : 1 ≤ m) (f : (Fin 1 → ZMod 2) → ℂ)
    (b : ZMod 2) : injectOuter m (hInjectBare m 0) f b
      = walshTransform 0 (fun u => (-1 : ℂ) ^ (b * u 0).val * f u) := by
  funext w
  rw [fun_one_eq f]
  simp only [injectOuter, injectInner, hInjectBare, interpretAmp_condition,
    interpretAmp_word, interpretAmp_nil, runAmp_cons, runAmp_nil, letterAmp, pauliProjection,
    SignedPauli.act, pauliAct, charOf_czGate_eval hm, yWeight_paulix, zDot_paulix, walshTransform]
  rcases word_cases w with rfl | rfl <;> fin_cases b <;>
    simp (config := { decide := true }) [Fin.init, paulix, signOf] <;> ring

/-- The branch read as a state is nonzero on a nonzero register, with the correction. -/
theorem injectInner_hInjectProtocol_ne_zero {m : ℕ} (hm : 1 ≤ m) {f : (Fin 1 → ZMod 2) → ℂ}
    (hf : f ≠ 0) (b : ZMod 2) : injectInner m (hInjectProtocol m 0) f b ≠ 0 := by
  intro h
  apply hf
  have h0 := congrFun h ![0, b]
  have h1 := congrFun h ![0, b + 1]
  rw [fun_one_eq f] at h0 h1 ⊢
  simp only [injectInner, hInjectProtocol_eq, hInjectBare, interpretAmp_condition,
    interpretAmp_word, interpretAmp_nil, runAmp_cons, runAmp_nil, letterAmp, pauliProjection,
    SignedPauli.act, pauliAct, charOf_czGate_eval hm, yWeight_paulix, zDot_paulix,
    Pi.zero_apply] at h0 h1
  funext u
  fin_cases b
  · simp (config := { decide := true }) only [one_div, Fin.init, DiagPhase.cnotBitMap,
      Nat.reduceAdd, Fin.reduceLast, Fin.zero_eta, Fin.isValue, Fin.castSucc_one,
      Fin.insertNth_apply_same, Nat.add_zero, Fin.castSucc_zero, ne_eq, Function.update_of_ne,
      Function.update_self, Even.neg_pow, one_pow, ↓reduceIte, one_mul, ZMod.val_zero, pow_zero,
      mul_one, paulix, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne, add_zero, mul_eq_zero,
      inv_eq_zero, OfNat.ofNat_ne_zero, false_or, Odd.neg_one_pow, neg_mul, mul_neg] at h0 h1
    have e0 : f ![0] = 0 := by linear_combination (h0 + h1) / 2
    have e1 : f ![1] = 0 := by linear_combination (h0 - h1) / 2
    rcases word_cases u with rfl | rfl <;> simp [e0, e1]
  · simp (config := { decide := true }) only [one_div, Fin.init, DiagPhase.cnotBitMap,
      Nat.reduceAdd, Fin.reduceLast, Fin.mk_one, Fin.isValue, Fin.castSucc_one,
      Fin.insertNth_apply_same, Nat.add_zero, Fin.castSucc_zero, ne_eq, Function.update_of_ne,
      Function.update_self, Even.neg_pow, one_pow, ↓reduceIte, one_mul, Odd.neg_one_pow,
      ZMod.val_zero, pow_zero, mul_one, paulix, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne,
      add_zero, neg_mul, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, mul_neg,
      neg_neg] at h0 h1
    have e0 : f ![0] = 0 := by linear_combination (h0 + h1) / 2
    have e1 : f ![1] = 0 := by linear_combination (h1 - h0) / 2
    rcases word_cases u with rfl | rfl <;> simp [e0, e1]

/-- The branch read as a state is nonzero on a nonzero register, without the correction. -/
theorem injectInner_hInjectBare_ne_zero {m : ℕ} (hm : 1 ≤ m) {f : (Fin 1 → ZMod 2) → ℂ}
    (hf : f ≠ 0) (b : ZMod 2) : injectInner m (hInjectBare m 0) f b ≠ 0 := by
  intro h
  apply hf
  have h0 := congrFun h ![0, 0]
  have h1 := congrFun h ![0, 1]
  rw [fun_one_eq f] at h0 h1 ⊢
  simp only [injectInner, hInjectBare, interpretAmp_condition, interpretAmp_word,
    interpretAmp_nil, runAmp_cons, runAmp_nil, letterAmp, pauliProjection, SignedPauli.act,
    pauliAct, charOf_czGate_eval hm, yWeight_paulix, zDot_paulix, Pi.zero_apply] at h0 h1
  funext u
  fin_cases b
  · simp (config := { decide := true }) only [one_div, Fin.init, Nat.reduceAdd, Fin.reduceLast,
      Fin.zero_eta, Fin.isValue, Nat.add_zero, Fin.castSucc_zero, Fin.castSucc_one, Even.neg_pow,
      one_pow, ↓reduceIte, one_mul, Fin.insertNth_apply_same, ZMod.val_zero, pow_zero, mul_one,
      paulix, Pi.add_apply, Pi.single_eq_same, ne_eq, Pi.single_eq_of_ne, add_zero, mul_eq_zero,
      inv_eq_zero, OfNat.ofNat_ne_zero, false_or, Odd.neg_one_pow, neg_mul, mul_neg] at h0 h1
    have e0 : f ![0] = 0 := by linear_combination (h0 + h1) / 2
    have e1 : f ![1] = 0 := by linear_combination (h0 - h1) / 2
    rcases word_cases u with rfl | rfl <;> simp [e0, e1]
  · simp (config := { decide := true }) only [one_div, Fin.init, Nat.reduceAdd, Fin.reduceLast,
      Fin.mk_one, Fin.isValue, Nat.add_zero, Fin.castSucc_zero, Fin.castSucc_one, Even.neg_pow,
      one_pow, ↓reduceIte, one_mul, Fin.insertNth_apply_same, Odd.neg_one_pow, ZMod.val_zero,
      pow_zero, mul_one, paulix, Pi.add_apply, Pi.single_eq_same, ne_eq, Pi.single_eq_of_ne,
      add_zero, neg_mul, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, mul_neg,
      neg_neg] at h0 h1
    have e0 : f ![0] = 0 := by linear_combination (h0 + h1) / 2
    have e1 : f ![1] = 0 := by linear_combination (h1 - h0) / 2
    rcases word_cases u with rfl | rfl <;> simp [e0, e1]

/-! ## One qubit: the processed branches -/

/-- **H inject on one qubit**: on every one-qubit carrier register, at its precision and at each
outcome, the processed branch has the amplitude of H's output, the Walsh transform. -/
theorem amp_hInjectBranch_one {S : KernelSumState 1} (hS : IsCarrier S) (b : ZMod 2) :
    amp (hInjectBranch S.m 0 S b) = walshTransform 0 (amp S) := by
  rw [hInjectBranch_eq_processBranch, amp_processBranch 0 _ hS rfl b ?_]
  · rw [amp_appendFreeBit]
    exact injectOuter_hInjectProtocol hS.1 (amp S) b
  · rw [amp_appendFreeBit]
    exact injectInner_hInjectProtocol_ne_zero hS.1 hS.2.2.2 b

/-- **Without its correction**, on every one-qubit carrier register, the processed branch at
outcome `b` is H's output of `Z^b` applied to the register. -/
theorem amp_processBranch_hInjectBare_one {S : KernelSumState 1} (hS : IsCarrier S)
    (b : ZMod 2) :
    amp (processBranch S.m 0 (hInjectBare S.m 0) S b)
      = walshTransform 0 (fun u => (-1 : ℂ) ^ (b * u 0).val * amp S u) := by
  rw [amp_processBranch 0 _ hS rfl b ?_]
  · rw [amp_appendFreeBit]
    exact injectOuter_hInjectBare hS.1 (amp S) b
  · rw [amp_appendFreeBit]
    exact injectInner_hInjectBare_ne_zero hS.1 hS.2.2.2 b

/-- H's output on a carrier register at its precision is the Walsh transform. -/
theorem amp_run_hadamard_one {S : KernelSumState 1} (hS : IsCarrier S) :
    amp (run ([GateLetter.hadamard 0] : GateWord 1 S.m) S) = walshTransform 0 (amp S) :=
  amp_run _ hS rfl

/-! ## The register `∣1⟩` -/

/-- The point state `∣1⟩`: `L = ⟨Z⟩`, flat exponent, scale `1`, offset `1`. -/
noncomputable def K1 : KernelState 1 := ⟨1, 0, 1, lagZ, ![1]⟩

/-- The word `1` is on `K1`'s support. -/
theorem K1_support_one : ∃ p ∈ K1.L, (![1] : Fin 1 → ZMod 2) = K1.x₀ + p.X :=
  ⟨0, Submodule.zero_mem _, by simp [K1]⟩

/-- `K1`'s amplitude at the word `1` is `1`. -/
theorem amp_K1_one : amp (ofKernelState K1) ![1] = 1 := by
  rw [amp_ofKernelState_pos K1 K1_support_one]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 1 1) ![1]) = 1
  rw [eval_zero_poly, charOf_zero, one_mul]

/-- **`∣1⟩` is a carrier state.** -/
theorem isCarrier_K1 : IsCarrier (ofKernelState K1) := by
  refine ⟨le_rfl, isStabilizer_span_singleton' (pauliz (0 : Fin 1)), ?_, ?_⟩
  · exact orthogonal_le_of_lagrangian (isStabilizer_span_singleton' (pauliz (0 : Fin 1)))
      (finrank_span_singleton (by decide))
  · intro h
    have h1 := congrFun h ![1]
    rw [amp_K1_one] at h1
    exact one_ne_zero h1

/-! ## Rows -/

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:generalonebit
/-- **Agreement, on `∣0⟩`.** At each outcome the processed branch of H inject on `∣0⟩` is
`StateEq` to the unitary H's output, T05's run of `H_0`. -/
-- row: agreement
theorem stateEq_hInjectBranch_KZ (b : ZMod 2) :
    StateEq (hInjectBranch 1 0 (ofKernelState KZ) b)
      (run ([GateLetter.hadamard 0] : GateWord 1 1) (ofKernelState KZ)) :=
  (amp_hInjectBranch_one isCarrier_KZ b).trans (amp_run_hadamard_one isCarrier_KZ).symm

/-- **Agreement, on `∣0⟩`, by value.** The processed branch of H inject on `∣0⟩` is
`(1/√2)·(∣0⟩ + ∣1⟩)` at each outcome: the value `walsh_delta0` computes for H on `δ₀`. -/
-- row: agreement
theorem amp_hInjectBranch_KZ (b : ZMod 2) :
    amp (hInjectBranch 1 0 (ofKernelState KZ) b) = fun _ => 1 / (Real.sqrt 2 : ℂ) := by
  have e : amp (hInjectBranch 1 0 (ofKernelState KZ) b)
      = walshTransform 0 (amp (ofKernelState KZ)) := amp_hInjectBranch_one isCarrier_KZ b
  rw [e, amp_KZ, walsh_delta0]

/-- **Agreement, on `∣1⟩`.** At each outcome the processed branch of H inject on `∣1⟩` is
`StateEq` to the unitary H's output. -/
-- row: agreement
theorem stateEq_hInjectBranch_K1 (b : ZMod 2) :
    StateEq (hInjectBranch 1 0 (ofKernelState K1) b)
      (run ([GateLetter.hadamard 0] : GateWord 1 1) (ofKernelState K1)) :=
  (amp_hInjectBranch_one isCarrier_K1 b).trans (amp_run_hadamard_one isCarrier_K1).symm

/-- **Agreement, on a height-one register.** At each outcome the processed branch of H inject
on `heightOneState` (`GateWordCheck.lean`, `h = 1`) is `StateEq` to the unitary H's output. -/
-- row: agreement
theorem stateEq_hInjectBranch_heightOneState (b : ZMod 2) :
    StateEq (hInjectBranch 1 0 heightOneState b)
      (run ([GateLetter.hadamard 0] : GateWord 1 1) heightOneState) :=
  (amp_hInjectBranch_one isCarrier_heightOneState b).trans
    (amp_run_hadamard_one isCarrier_heightOneState).symm

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:zteleport
/-- **Discriminating: without its correction the branches differ.** On `∣1⟩`, the processed
branches of the protocol without its correction (`hInjectBare`) at outcomes `0` and `1` differ
at the word `0`: they are H's outputs of `∣1⟩` and of `Z∣1⟩ = −∣1⟩`. -/
-- row: discriminating
theorem processBranch_hInjectBare_K1_branches_ne :
    amp (processBranch 1 0 (hInjectBare 1 0) (ofKernelState K1) 0)
      ≠ amp (processBranch 1 0 (hInjectBare 1 0) (ofKernelState K1) 1) := by
  intro h
  have h0 := congrFun h ![0]
  have e0 : amp (processBranch 1 0 (hInjectBare 1 0) (ofKernelState K1) 0)
      = walshTransform 0
          (fun u => (-1 : ℂ) ^ ((0 : ZMod 2) * u 0).val * amp (ofKernelState K1) u) :=
    amp_processBranch_hInjectBare_one isCarrier_K1 0
  have e1 : amp (processBranch 1 0 (hInjectBare 1 0) (ofKernelState K1) 1)
      = walshTransform 0
          (fun u => (-1 : ℂ) ^ ((1 : ZMod 2) * u 0).val * amp (ofKernelState K1) u) :=
    amp_processBranch_hInjectBare_one isCarrier_K1 1
  rw [e0, e1] at h0
  simp only [walshTransform] at h0
  have hu0 : Function.update (![0] : Fin 1 → ZMod 2) 0 0 = ![0] := by decide
  have hu1 : Function.update (![0] : Fin 1 → ZMod 2) 0 1 = ![1] := by decide
  rw [hu0, hu1, amp_K1_one] at h0
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp [signOf] at h0
  field_simp at h0
  norm_num at h0

/-- **Discriminating: without its correction the branch at outcome `1` is not H's output.** On
`∣1⟩`, the processed branch of `hInjectBare` at outcome `1` is not `StateEq` to the unitary H's
output, which the corrected protocol's branch is (`stateEq_hInjectBranch_K1`). -/
-- row: discriminating
theorem not_stateEq_processBranch_hInjectBare_K1 :
    ¬ StateEq (processBranch 1 0 (hInjectBare 1 0) (ofKernelState K1) 1)
      (run ([GateLetter.hadamard 0] : GateWord 1 1) (ofKernelState K1)) := by
  intro h
  have h0 := congrFun h ![0]
  have e1 : amp (processBranch 1 0 (hInjectBare 1 0) (ofKernelState K1) 1)
      = walshTransform 0
          (fun u => (-1 : ℂ) ^ ((1 : ZMod 2) * u 0).val * amp (ofKernelState K1) u) :=
    amp_processBranch_hInjectBare_one isCarrier_K1 1
  have eH : amp (run ([GateLetter.hadamard 0] : GateWord 1 1) (ofKernelState K1))
      = walshTransform 0 (amp (ofKernelState K1)) := amp_run_hadamard_one isCarrier_K1
  rw [e1, eH] at h0
  simp only [walshTransform] at h0
  have hu0 : Function.update (![0] : Fin 1 → ZMod 2) 0 0 = ![0] := by decide
  have hu1 : Function.update (![0] : Fin 1 → ZMod 2) 0 1 = ![1] := by decide
  rw [hu0, hu1, amp_K1_one] at h0
  simp [signOf] at h0
  field_simp at h0
  norm_num at h0

/-- **Inhabitation.** The hypothesis of `hInject_correct` holds for the height-one register: it
is a carrier state, at precision `1`. -/
-- row: inhabitation
theorem hInject_correct_hypotheses_heightOneState :
    IsCarrier heightOneState ∧ heightOneState.m = 1 :=
  ⟨isCarrier_heightOneState, rfl⟩

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.hInject_correct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.hInject_correct

/-! ## Mutants -/

-- mutant: hInject_correct_weight_conclusion | FTQCLib/Carrier/HInject.lean
--   | ampNormSq (hInjectBranch S.m j S b) = ampNormSq (appendFreeBit S) / 2 ∧
--   | ampNormSq (hInjectBranch S.m j S b) = ampNormSq (appendFreeBit S) / 3 ∧

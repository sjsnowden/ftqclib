/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.RemoteCH
import FTQCLib.Carrier.HInjectCheck
import FTQCLib.Carrier.ControlledHadamardCheck
import FTQCLib.Carrier.CarrierCliffordCheck

/-!
# Check: witness for T16, remote controlled-H

T16's witness (`docs/STEPS.md`, T16.2): rows on the statement of `RemoteCH.lean`, at precision
`3`, at every outcome string `(s, u)`: on two-qubit registers, Alice's input qubit `0` and Bob's
`1`; and on a three-qubit register, Alice's input qubit `0`, Bob's `2` and a spectator bit `1`
between them.

* **The processing keeps the carrier property.** `processRemote` (`RemoteCH.lean`) is
  `remoteCHBranch`'s processing for any protocol on the register and the two ancillas with two
  outcome bits. Its amplitude is computed by referees already proved: `amp_interpret` (T14),
  `amp_restrictZ` (T12), `amp_appendFreeBit` and `amp_liftPrecision`. This is
  `processRemote_spec`: if the protocol's referee, read at the outcome bits and at the bits the
  measurements left the ancillas at, is a nonzero function `G`, the processed branch is a carrier
  state of amplitude `G`.
* **On two qubits** the referee of `remoteCHProtocol` is evaluated letter by letter, with T08's
  word replaced by its referee (`runAmp_controlledHWord`): at every outcome string it is
  `controlledHAmp 0 1` of the register's amplitude (`interpretAmp_remoteCH_two`). Hence
  `amp_remoteCHBranch_two`, on every two-qubit carrier register at precision at most `3`.
* **On three qubits** the same evaluation, with control `0`, target `2` and spectator `1`, gives
  `controlledHAmp 0 2` of the register's amplitude at every outcome string
  (`interpretAmp_remoteCH_three`); the amplitude is written as a function of its three bits, not as
  its eight values, to stay within the default heartbeat budget.
* **Rows (agreement).** The processed branch is `StateEq` to T08's word run on the register, on
  the basis inputs `∣00⟩` (`K00`, `CarrierCliffordCheck.lean`) and `∣10⟩` (`K10` below) and on
  the height-one register `heightOneState2` (`ControlledHadamardCheck.lean`), at each outcome
  string; on `∣10⟩` its value at `∣11⟩` is `1/√2`, the value
  `controlledHAmp_basis_control_one_eleven` computes.
* **Row (agreement, a spectator bit).** On `KSpectator`, a three-qubit register with every
  amplitude nonzero (`∣+−+⟩`, amplitude `(−1)^{w₁}`, a sign on the spectator), the processed
  branch with `c = 0`, `t = 2` is `StateEq` to T08's word run on the register, at each outcome
  string. The bit indexing of the protocol's letters past a register whose inputs are not its
  first two bits is exercised.
* **Rows (discriminating).** With CZ in place of T08's word (`remoteCZProtocol`), the processed
  branch on `∣10⟩` is `0` at `∣11⟩` at every outcome string, so it is not `StateEq` to T08's
  word's output. `∣00⟩` would not discriminate: controlled-H and CZ both fix it.
* **Row (inhabitation).** `heightOneState2` meets `remoteCH_correct`'s hypotheses with `c = 0`,
  `t = 1` and `k = 3`.

No row uses `remoteCH_correct` (proved at T16.3) or `interpretAmp_remoteCHProtocol`, its closed
form of the referee: every referee here is evaluated word by word at literal words. The rows test
the `StateEq` clause; the weight clauses and the clause on T07's rules have no row of their own.

Frame form (D5): the rows compare amplitude functions on the free bits; controlled-H is T08's
word, whose referee is `controlledHAmp`, and CZ is its diagonal letter, whose referee is the
phase `(−1)^{w₀w₁}`. `RemoteCH.lean` imports no `FTQCLib.Hilbert` module.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer
open Protocol

variable {n : ℕ}

/-! ## Remote CZ: CZ in place of T08's word -/

/-- **Remote CZ**: `remoteCHProtocol` with T08's controlled-H word replaced by one CZ letter
between `B₁` and Bob's input qubit `t`; every other letter is the same. -/
noncomputable def remoteCZProtocol (k : ℕ) (c t : Fin n) : Protocol k (n + 2) 2 :=
  let a₁ : Fin (n + 2) := (Fin.last n).castSucc
  let b₁ : Fin (n + 2) := Fin.last (n + 1)
  let alice : GateWord (n + 2 + 0) k :=
    [GateLetter.hadamard b₁, GateLetter.cnot a₁ b₁ (Fin.castSucc_lt_last _).ne,
      GateLetter.cnot c.castSucc.castSucc a₁ (castSucc_castSucc_ne_last_castSucc c)]
  let bob : GateWord (n + 2 + 1) k :=
    [GateLetter.cnot (Fin.last (n + 2)) b₁.castSucc (Fin.castSucc_lt_last _).ne',
      GateLetter.diagonal (DiagPhase.czGate k b₁.castSucc t.castSucc.castSucc.castSucc),
      GateLetter.hadamard b₁.castSucc]
  let correction : GateWord (n + 2 + 2) k :=
    [GateLetter.diagonal
      (DiagPhase.czGate k (Fin.last (n + 3)) c.castSucc.castSucc.castSucc.castSucc)]
  let first : Protocol k (n + 2) 1 :=
    (Protocol.nil.word alice).condition (signedZ a₁) (signedZ_side a₁)
  ((first.word bob).condition (signedZ b₁.castSucc) (signedZ_side b₁.castSucc)).word correction

/-! ## Two qubits: the referees -/

/-- `Z_j` acts by the sign `(−1)^{w_j}`. -/
theorem pauliAct_pauliz {N : ℕ} (j : Fin N) (f : (Fin N → ZMod 2) → ℂ) (w : Fin N → ZMod 2) :
    pauliAct (pauliz j) f w = (-1 : ℂ) ^ (w j).val * f w := by
  have hz : zDot (pauliz j) w = (w j).val := by
    unfold zDot pauliz
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simp
  have hy : yWeight (pauliz j) = 0 := by simp [yWeight, zDot]
  rw [pauliAct, hy, pauliz_X, add_zero, hz, pow_zero, one_mul]

/-- A two-bit amplitude function is its four values. -/
theorem fun_two_eq (f : (Fin 2 → ZMod 2) → ℂ) :
    f = fun v => if v 0 = 0 then (if v 1 = 0 then f ![0, 0] else f ![0, 1])
      else (if v 1 = 0 then f ![1, 0] else f ![1, 1]) := by
  funext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rcases zmod_two_eq_zero_or_one (v 0) with h0 | h0 <;>
    rcases zmod_two_eq_zero_or_one (v 1) with h1 | h1 <;>
    · rw [hv]
      simp [h0, h1]

/-- `1/√2` as a number `r` with the powers the referees produce: `r² = ½`, `r³ = r/2`,
`r⁴ = ¼`. -/
theorem sqrt_two_inv_powers : ∃ r : ℂ, (Real.sqrt 2 : ℂ)⁻¹ = r ∧ r ^ 2 = 2⁻¹ ∧
    r ^ 3 = 2⁻¹ * r ∧ r ^ 4 = 2⁻¹ * 2⁻¹ := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hr2 : (Real.sqrt 2 : ℂ)⁻¹ ^ 2 = 2⁻¹ := by rw [sq, ← mul_inv, h2]
  refine ⟨_, rfl, hr2, by rw [pow_succ, hr2], ?_⟩
  rw [show 4 = 2 + 2 from rfl, pow_add, hr2]

/- The evaluation of a two-qubit referee at a literal word, the outcome bit `u` split: the
protocol unfolded letter by letter, T08's word replaced by its referee, the amplitude written as
its four values, and the result normalised in `r = 1/√2`. One macro so that each of the sixteen
literal cases is one short declaration: one declaration over the four outcome strings at a word
with control bit `1` exceeded the default heartbeat budget (measured at this step), and the
budget is not raised (LN.4). -/
set_option hygiene false in
macro "remote_eval" : tactic => `(tactic| (
  rw [fun_two_eq F]
  simp only [RefereeCH, RefereeCZ, remoteCHProtocol, remoteCZProtocol, interpretAmp_word,
    interpretAmp_condition, interpretAmp_nil, runAmp_append, runAmp_controlledHWord, runAmp_cons,
    runAmp_nil, letterAmp, pauliProjection, SignedPauli.act, signedZ, pauliAct_pauliz,
    controlledHAmp, walshTransform, charOf_czGate_eval (show 1 ≤ 3 by norm_num),
    DiagPhase.cnotBitMap]
  obtain ⟨r, hr, hr2, hr3, hr4⟩ := sqrt_two_inv_powers
  rcases zmod_two_eq_zero_or_one u with rfl | rfl <;>
    simp (config := { decide := true }) [Fin.init, signOf] <;>
    rw [hr] <;> ring_nf <;> simp only [hr2, hr3, hr4] <;> ring))

/-- The referee of remote CH on two qubits, read at the literal word `![a, b, s, u, s, u]`. -/
abbrev RefereeCH (F : (Fin 2 → ZMod 2) → ℂ) (a b s u : ZMod 2) : Prop :=
  (remoteCHProtocol 3 le_rfl (0 : Fin 2) 1).interpretAmp (fun x => F (Fin.init (Fin.init x)))
    ![a, b, s, u, s, u] = controlledHAmp 0 1 F ![a, b]

/-- The referee of remote CZ on two qubits, read at the literal word `![a, b, s, u, s, u]`. -/
abbrev RefereeCZ (F : (Fin 2 → ZMod 2) → ℂ) (a b s u : ZMod 2) : Prop :=
  (remoteCZProtocol 3 (0 : Fin 2) 1).interpretAmp (fun x => F (Fin.init (Fin.init x)))
    ![a, b, s, u, s, u]
    = letterAmp (m := 3) (.diagonal (DiagPhase.czGate 3 (0 : Fin 2) 1)) F ![a, b]

/-- Remote CH's referee at `∣00⟩`, `s = 0`. -/
theorem refereeCH_000 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 0 0 0 u := by
  remote_eval
/-- Remote CH's referee at `∣00⟩`, `s = 1`. -/
theorem refereeCH_001 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 0 0 1 u := by
  remote_eval
/-- Remote CH's referee at `∣01⟩`, `s = 0`. -/
theorem refereeCH_010 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 0 1 0 u := by
  remote_eval
/-- Remote CH's referee at `∣01⟩`, `s = 1`. -/
theorem refereeCH_011 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 0 1 1 u := by
  remote_eval
/-- Remote CH's referee at `∣10⟩`, `s = 0`. -/
theorem refereeCH_100 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 1 0 0 u := by
  remote_eval
/-- Remote CH's referee at `∣10⟩`, `s = 1`. -/
theorem refereeCH_101 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 1 0 1 u := by
  remote_eval
/-- Remote CH's referee at `∣11⟩`, `s = 0`. -/
theorem refereeCH_110 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 1 1 0 u := by
  remote_eval
/-- Remote CH's referee at `∣11⟩`, `s = 1`. -/
theorem refereeCH_111 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCH F 1 1 1 u := by
  remote_eval

/-- Remote CZ's referee at `∣00⟩`, `s = 0`. -/
theorem refereeCZ_000 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 0 0 0 u := by
  remote_eval
/-- Remote CZ's referee at `∣00⟩`, `s = 1`. -/
theorem refereeCZ_001 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 0 0 1 u := by
  remote_eval
/-- Remote CZ's referee at `∣01⟩`, `s = 0`. -/
theorem refereeCZ_010 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 0 1 0 u := by
  remote_eval
/-- Remote CZ's referee at `∣01⟩`, `s = 1`. -/
theorem refereeCZ_011 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 0 1 1 u := by
  remote_eval
/-- Remote CZ's referee at `∣10⟩`, `s = 0`. -/
theorem refereeCZ_100 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 1 0 0 u := by
  remote_eval
/-- Remote CZ's referee at `∣10⟩`, `s = 1`. -/
theorem refereeCZ_101 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 1 0 1 u := by
  remote_eval
/-- Remote CZ's referee at `∣11⟩`, `s = 0`. -/
theorem refereeCZ_110 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 1 1 0 u := by
  remote_eval
/-- Remote CZ's referee at `∣11⟩`, `s = 1`. -/
theorem refereeCZ_111 (F : (Fin 2 → ZMod 2) → ℂ) (u : ZMod 2) : RefereeCZ F 1 1 1 u := by
  remote_eval

/-- The four snocs of a two-bit word are the literal word. -/
theorem snoc_four_eq (w : Fin 2 → ZMod 2) (s u : ZMod 2) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u : Fin (2 + 2 + 2) → ZMod 2)
      = ![w 0, w 1, s, u, s, u] := by
  funext i
  fin_cases i <;> rfl

/-- A two-bit word is its literal. -/
theorem word_two_eq (w : Fin 2 → ZMod 2) : w = ![w 0, w 1] := by
  funext i
  fin_cases i <;> rfl

/-- **Remote CH's referee on two qubits** is controlled-H, at every outcome string. -/
theorem interpretAmp_remoteCH_two (F : (Fin 2 → ZMod 2) → ℂ) (s u : ZMod 2)
    (w : Fin 2 → ZMod 2) :
    (remoteCHProtocol 3 le_rfl (0 : Fin 2) 1).interpretAmp (fun x => F (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u) = controlledHAmp 0 1 F w := by
  rw [snoc_four_eq]
  conv_rhs => rw [word_two_eq w]
  generalize w 0 = a
  generalize w 1 = b
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one s with rfl | rfl
  exacts [refereeCH_000 F u, refereeCH_001 F u, refereeCH_010 F u, refereeCH_011 F u,
    refereeCH_100 F u, refereeCH_101 F u, refereeCH_110 F u, refereeCH_111 F u]

/-- **Remote CZ's referee on two qubits** is CZ, at every outcome string. -/
theorem interpretAmp_remoteCZ_two (F : (Fin 2 → ZMod 2) → ℂ) (s u : ZMod 2)
    (w : Fin 2 → ZMod 2) :
    (remoteCZProtocol 3 (0 : Fin 2) 1).interpretAmp (fun x => F (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u)
      = letterAmp (m := 3) (.diagonal (DiagPhase.czGate 3 (0 : Fin 2) 1)) F w := by
  rw [snoc_four_eq]
  conv_rhs => rw [word_two_eq w]
  generalize w 0 = a
  generalize w 1 = b
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one s with rfl | rfl
  exacts [refereeCZ_000 F u, refereeCZ_001 F u, refereeCZ_010 F u, refereeCZ_011 F u,
    refereeCZ_100 F u, refereeCZ_101 F u, refereeCZ_110 F u, refereeCZ_111 F u]

/-- Controlled-H on two qubits sends only zero to zero. -/
theorem controlledHAmp_ne_zero {F : (Fin 2 → ZMod 2) → ℂ} (hF : F ≠ 0) :
    controlledHAmp 0 1 F ≠ 0 := by
  intro h
  apply hF
  have h00 := congrFun h ![0, 0]
  have h01 := congrFun h ![0, 1]
  have h10 := congrFun h ![1, 0]
  have h11 := congrFun h ![1, 1]
  rw [fun_two_eq F] at h00 h01 h10 h11 ⊢
  simp (config := { decide := true }) only [controlledHAmp, ↓reduceIte, Pi.zero_apply,
    walshTransform, one_div, signOf, one_mul, mul_eq_zero, inv_eq_zero, Complex.ofReal_eq_zero,
    Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, false_or, neg_mul]
    at h00 h01 h10 h11
  have e10 : F ![1, 0] = 0 := by linear_combination (h10 + h11) / 2
  have e11 : F ![1, 1] = 0 := by linear_combination (h10 - h11) / 2
  funext v
  simp [h00, h01, e10, e11]

/-- CZ on two qubits sends only zero to zero. -/
theorem czAmp_ne_zero {F : (Fin 2 → ZMod 2) → ℂ} (hF : F ≠ 0) :
    letterAmp (m := 3) (.diagonal (DiagPhase.czGate 3 (0 : Fin 2) 1)) F ≠ 0 := by
  intro h
  apply hF
  funext v
  have hv := congrFun h v
  simp only [letterAmp, charOf_czGate_eval (show 1 ≤ 3 by norm_num), Pi.zero_apply] at hv
  rcases mul_eq_zero.mp hv with h1 | h1
  · exact absurd h1 (pow_ne_zero _ (by norm_num))
  · exact h1

/-! ## Two qubits: the processed branches -/

/-- **Remote CH on two qubits**: on every two-qubit carrier register at precision at most `3`,
at each outcome string, the processed branch has amplitude controlled-H of the register's. -/
theorem amp_remoteCHBranch_two {S : KernelSumState 2} (hS : IsCarrier S) (hmk : S.m ≤ 3)
    (s u : ZMod 2) :
    amp (remoteCHBranch 3 le_rfl 0 1 S hmk s u) = controlledHAmp 0 1 (amp S) :=
  (processRemote_spec hS 3 hmk _ s u (controlledHAmp_ne_zero hS.2.2.2)
    (interpretAmp_remoteCH_two (amp S) s u)).2

/-- **Remote CZ on two qubits**: the processed branch has amplitude CZ of the register's. -/
theorem amp_processRemote_remoteCZ_two {S : KernelSumState 2} (hS : IsCarrier S)
    (hmk : S.m ≤ 3) (s u : ZMod 2) :
    amp (processRemote 3 (remoteCZProtocol 3 0 1) S hmk s u)
      = letterAmp (m := 3) (.diagonal (DiagPhase.czGate 3 (0 : Fin 2) 1)) (amp S) :=
  (processRemote_spec hS 3 hmk _ s u (czAmp_ne_zero hS.2.2.2)
    (interpretAmp_remoteCZ_two (amp S) s u)).2

/-- T08's word on a two-qubit carrier register at precision at most `3` is controlled-H. -/
theorem amp_run_controlledHWord_two {S : KernelSumState 2} (hS : IsCarrier S) (hmk : S.m ≤ 3) :
    amp (run (controlledHWord 3 le_rfl (show (0 : Fin 2) ≠ 1 by decide))
      (liftPrecision S 3 hmk)) = controlledHAmp 0 1 (amp S) :=
  (amp_controlledHWord hS (show (0 : Fin 2) ≠ 1 by decide) 3 hmk le_rfl).2

/-! ## The register `∣10⟩` -/

/-- The point state `∣10⟩`: `L = ⟨Z₀, Z₁⟩`, flat exponent, scale `1`, offset `![1, 0]`. -/
noncomputable def K10 : KernelState 2 := ⟨1, 0, 1, lagZZ, ![1, 0]⟩

/-- Its support is the word `![1, 0]`. -/
theorem support_K10 (w : Fin 2 → ZMod 2) :
    (∃ p ∈ K10.L, w = K10.x₀ + p.X) ↔ w = ![1, 0] := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p.X = 0 at hp
    change ![1, 0] + p.X = ![1, 0]
    rw [hp, add_zero]
  · rintro rfl
    exact ⟨0, lagZZ.zero_mem, by change (![1, 0] : Fin 2 → ZMod 2) = ![1, 0] + 0; rw [add_zero]⟩

/-- `K10`'s amplitude is the delta at `![1, 0]`. -/
theorem amp_K10 : amp (ofKernelState K10) = deltaAmp ![1, 0] := by
  funext w
  by_cases hw : w = ![1, 0]
  · rw [amp_ofKernelState_pos K10 ((support_K10 w).mpr hw), hw, deltaAmp_self]
    change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase 2 1) ![1, 0]) = 1
    rw [eval_zero_poly, charOf_zero, one_mul]
  · rw [amp_ofKernelState_neg K10 (fun h => hw ((support_K10 w).mp h)), deltaAmp_of_ne hw]

/-- **`∣10⟩` is a carrier state.** -/
theorem isCarrier_K10 : IsCarrier (ofKernelState K10) := by
  refine ⟨le_rfl, isStabilizer_lagZZ, orthogonal_lagZZ, ?_⟩
  intro h
  have h0 := congrFun h ![1, 0]
  rw [amp_K10, deltaAmp_self] at h0
  exact one_ne_zero h0

/-! ## Three qubits: a spectator between the inputs

Alice's input qubit is bit `0`, Bob's is bit `2`, and bit `1` is a spectator: no letter of the
protocol names it, and controlled-H leaves it unchanged. The bits of the ancillas and the outcomes
are then `3` to `6`, so the indexing of the protocol's letters past the register is exercised at
a register whose inputs are not its first two bits. -/

/-- A three-bit word is its literal. -/
theorem word_three_eq (w : Fin 3 → ZMod 2) : w = ![w 0, w 1, w 2] := by
  funext i
  fin_cases i <;> rfl

/- The evaluation of a three-qubit referee at a literal word, the outcome bit `u` split, as
`remote_eval` does on two qubits, except that the amplitude is written as a function of its three
bits (`word_three_eq`) rather than as its eight values: the eight-way case split of `remote_eval`'s
form exceeded the default heartbeat budget at one literal word (measured at this step), and the
budget is not raised (LN.4). -/
set_option hygiene false in
macro "remote_eval3" : tactic => `(tactic| (
  rw [show F = fun v => F ![v 0, v 1, v 2] from funext fun v => congrArg F (word_three_eq v)]
  simp only [RefereeCH3, remoteCHProtocol, interpretAmp_word, interpretAmp_condition,
    interpretAmp_nil, runAmp_append, runAmp_controlledHWord, runAmp_cons, runAmp_nil, letterAmp,
    pauliProjection, SignedPauli.act, signedZ, pauliAct_pauliz, controlledHAmp, walshTransform,
    charOf_czGate_eval (show 1 ≤ 3 by norm_num), DiagPhase.cnotBitMap]
  obtain ⟨r, hr, hr2, hr3, hr4⟩ := sqrt_two_inv_powers
  rcases zmod_two_eq_zero_or_one u with rfl | rfl <;>
    simp (config := { decide := true }) [Fin.init, signOf] <;>
    rw [hr] <;> ring_nf <;> simp only [hr2, hr3, hr4] <;> ring))

/-- The referee of remote CH on three qubits, control `0` and target `2`, read at the literal
word `![a, b, d, s, u, s, u]`. -/
abbrev RefereeCH3 (F : (Fin 3 → ZMod 2) → ℂ) (a b d s u : ZMod 2) : Prop :=
  (remoteCHProtocol 3 le_rfl (0 : Fin 3) 2).interpretAmp (fun x => F (Fin.init (Fin.init x)))
    ![a, b, d, s, u, s, u] = controlledHAmp 0 2 F ![a, b, d]

/-- Remote CH's referee at `∣000⟩`, `s = 0`. -/
theorem refereeCH3_0000 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 0 0 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣000⟩`, `s = 1`. -/
theorem refereeCH3_0001 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 0 0 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣001⟩`, `s = 0`. -/
theorem refereeCH3_0010 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 0 1 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣001⟩`, `s = 1`. -/
theorem refereeCH3_0011 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 0 1 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣010⟩`, `s = 0`. -/
theorem refereeCH3_0100 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 1 0 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣010⟩`, `s = 1`. -/
theorem refereeCH3_0101 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 1 0 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣011⟩`, `s = 0`. -/
theorem refereeCH3_0110 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 1 1 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣011⟩`, `s = 1`. -/
theorem refereeCH3_0111 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 0 1 1 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣100⟩`, `s = 0`. -/
theorem refereeCH3_1000 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 0 0 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣100⟩`, `s = 1`. -/
theorem refereeCH3_1001 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 0 0 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣101⟩`, `s = 0`. -/
theorem refereeCH3_1010 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 0 1 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣101⟩`, `s = 1`. -/
theorem refereeCH3_1011 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 0 1 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣110⟩`, `s = 0`. -/
theorem refereeCH3_1100 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 1 0 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣110⟩`, `s = 1`. -/
theorem refereeCH3_1101 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 1 0 1 u := by
  remote_eval3
/-- Remote CH's referee at `∣111⟩`, `s = 0`. -/
theorem refereeCH3_1110 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 1 1 0 u := by
  remote_eval3
/-- Remote CH's referee at `∣111⟩`, `s = 1`. -/
theorem refereeCH3_1111 (F : (Fin 3 → ZMod 2) → ℂ) (u : ZMod 2) :
    RefereeCH3 F 1 1 1 1 u := by
  remote_eval3

/-- The four snocs of a three-bit word are the literal word. -/
theorem snoc_four_eq_three (w : Fin 3 → ZMod 2) (s u : ZMod 2) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u : Fin (3 + 2 + 2) → ZMod 2)
      = ![w 0, w 1, w 2, s, u, s, u] := by
  funext i
  fin_cases i <;> rfl

/-- **Remote CH's referee on three qubits**, control `0`, target `2`, spectator `1`, is
controlled-H, at every outcome string. -/
theorem interpretAmp_remoteCH_three (F : (Fin 3 → ZMod 2) → ℂ) (s u : ZMod 2)
    (w : Fin 3 → ZMod 2) :
    (remoteCHProtocol 3 le_rfl (0 : Fin 3) 2).interpretAmp (fun x => F (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u) = controlledHAmp 0 2 F w := by
  rw [snoc_four_eq_three]
  conv_rhs => rw [word_three_eq w]
  generalize w 0 = a
  generalize w 1 = b
  generalize w 2 = d
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one d with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one s with rfl | rfl
  exacts [refereeCH3_0000 F u, refereeCH3_0001 F u, refereeCH3_0010 F u, refereeCH3_0011 F u,
    refereeCH3_0100 F u, refereeCH3_0101 F u, refereeCH3_0110 F u, refereeCH3_0111 F u,
    refereeCH3_1000 F u, refereeCH3_1001 F u, refereeCH3_1010 F u, refereeCH3_1011 F u,
    refereeCH3_1100 F u, refereeCH3_1101 F u, refereeCH3_1110 F u, refereeCH3_1111 F u]

/-! ## The register `∣+−+⟩` on three qubits -/

/-- The three-qubit record with every amplitude nonzero: `L` the all-`X` Lagrangian (support every
word), offset `0`, scale `1`, precision `1`, exponent `x₁`, so the amplitude is `(−1)^{w₁}`, a
sign on the spectator bit: `∣+−+⟩` with the scale kept (D3). -/
noncomputable def KSpectator : KernelState 3 := ⟨1, MvPolynomial.X 1, 1, lagXXX, 0⟩

/-- `KSpectator`'s amplitude is `1` at the origin. -/
theorem amp_KSpectator_zero : amp (ofKernelState KSpectator) 0 = 1 := by
  rw [amp_ofKernelState_pos KSpectator ⟨0, lagXXX.zero_mem,
    by change (0 : Fin 3 → ZMod 2) = 0 + 0; rw [add_zero]⟩]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (MvPolynomial.X 1 : DiagPhase 3 1) 0) = 1
  rw [eval_X_diag, Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, charOf_zero, one_mul]

/-- **`KSpectator` is a carrier state.** -/
theorem isCarrier_KSpectator : IsCarrier (ofKernelState KSpectator) := by
  refine ⟨le_rfl, isStabilizer_lagXXX, orthogonal_lagXXX, ?_⟩
  intro h
  have h0 := congrFun h 0
  rw [amp_KSpectator_zero] at h0
  exact one_ne_zero h0

/-- Controlled-H of `KSpectator`'s amplitude is nonzero: at the origin the control is `0`, so it
is `KSpectator`'s own value `1` there. -/
theorem controlledHAmp_KSpectator_ne_zero :
    controlledHAmp 0 2 (amp (ofKernelState KSpectator)) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [controlledHAmp, Pi.zero_apply, if_true, amp_KSpectator_zero] at h0
  exact one_ne_zero h0

/-! ## Rows -/

-- source: papers/clifford_hierarchy/
-- Eisert_Jacobs_Papadopoulos_Plenio_2000_optimal_local_nonlocal_gates_quant-ph_0005101
--   theorem:theorem2
/-- **Agreement, on `∣00⟩`.** At each outcome string the processed branch of remote CH on `∣00⟩`
is `StateEq` to T08's word run on `∣00⟩`. -/
-- row: agreement
theorem stateEq_remoteCHBranch_K00 (s u : ZMod 2) :
    StateEq (remoteCHBranch 3 le_rfl 0 1 (ofKernelState K00) (by decide) s u)
      (run (controlledHWord 3 le_rfl (show (0 : Fin 2) ≠ 1 by decide))
        (liftPrecision (ofKernelState K00) 3 (by decide))) :=
  (amp_remoteCHBranch_two isCarrier_K00 _ s u).trans
    (amp_run_controlledHWord_two isCarrier_K00 _).symm

/-- **Agreement, on `∣10⟩`.** At each outcome string the processed branch of remote CH on `∣10⟩`
is `StateEq` to T08's word run on `∣10⟩`. -/
-- row: agreement
theorem stateEq_remoteCHBranch_K10 (s u : ZMod 2) :
    StateEq (remoteCHBranch 3 le_rfl 0 1 (ofKernelState K10) (by decide) s u)
      (run (controlledHWord 3 le_rfl (show (0 : Fin 2) ≠ 1 by decide))
        (liftPrecision (ofKernelState K10) 3 (by decide))) :=
  (amp_remoteCHBranch_two isCarrier_K10 _ s u).trans
    (amp_run_controlledHWord_two isCarrier_K10 _).symm

/-- **Agreement, on `∣10⟩`, by value.** At each outcome string the processed branch of remote CH
on `∣10⟩` is `1/√2` at `∣11⟩`: the value `controlledHAmp_basis_control_one_eleven` computes from
controlled-H's matrix. -/
-- row: agreement
theorem amp_remoteCHBranch_K10_eleven (s u : ZMod 2) :
    amp (remoteCHBranch 3 le_rfl 0 1 (ofKernelState K10) (by decide) s u) ![1, 1]
      = 1 / (Real.sqrt 2 : ℂ) := by
  rw [amp_remoteCHBranch_two isCarrier_K10 _ s u, amp_K10]
  exact controlledHAmp_basis_control_one_eleven

/-- **Agreement, on a height-one register.** At each outcome string the processed branch of
remote CH on `heightOneState2` (`ControlledHadamardCheck.lean`, `h = 1`) is `StateEq` to T08's
word run on it. -/
-- row: agreement
theorem stateEq_remoteCHBranch_heightOneState2 (s u : ZMod 2) :
    StateEq (remoteCHBranch 3 le_rfl 0 1 heightOneState2 (by rw [heightOneState2_m]; norm_num) s u)
      (run (controlledHWord 3 le_rfl (show (0 : Fin 2) ≠ 1 by decide))
        (liftPrecision heightOneState2 3 (by rw [heightOneState2_m]; norm_num))) :=
  (amp_remoteCHBranch_two isCarrier_heightOneState2 _ s u).trans
    (amp_run_controlledHWord_two isCarrier_heightOneState2 _).symm

/-- **Agreement, on three qubits with a spectator between the inputs.** On `KSpectator`, a
three-qubit register with every amplitude nonzero, with Alice's input qubit `0`, Bob's `2` and the
spectator bit `1`, at each outcome string the processed branch of remote CH is `StateEq` to T08's
word run on `KSpectator`. The branch's amplitude is computed by `processRemote_spec` from the
referee evaluated word by word (`interpretAmp_remoteCH_three`), the word's by
`amp_controlledHWord`. -/
-- row: agreement
theorem stateEq_remoteCHBranch_KSpectator (s u : ZMod 2) :
    StateEq (remoteCHBranch 3 le_rfl 0 2 (ofKernelState KSpectator) (by decide) s u)
      (run (controlledHWord 3 le_rfl (show (0 : Fin 3) ≠ 2 by decide))
        (liftPrecision (ofKernelState KSpectator) 3 (by decide))) :=
  (processRemote_spec isCarrier_KSpectator 3 _ _ s u controlledHAmp_KSpectator_ne_zero
    (interpretAmp_remoteCH_three _ s u)).2.trans
    (amp_controlledHWord isCarrier_KSpectator (show (0 : Fin 3) ≠ 2 by decide) 3 _ le_rfl).2.symm

-- source: papers/clifford_hierarchy/
-- Eisert_Jacobs_Papadopoulos_Plenio_2000_optimal_local_nonlocal_gates_quant-ph_0005101 figure:fig1
/-- **Discriminating: CZ in place of controlled-H.** On `∣10⟩`, at each outcome string, the
processed branch of remote CZ is `0` at `∣11⟩`, where T08's word's output is `1/√2`
(`controlledHAmp_basis_control_one_eleven`): it is not `StateEq` to T08's word's output, which
remote CH's branch is (`stateEq_remoteCHBranch_K10`). -/
-- row: discriminating
theorem not_stateEq_processRemote_remoteCZ_K10 (s u : ZMod 2) :
    ¬ StateEq (processRemote 3 (remoteCZProtocol 3 0 1) (ofKernelState K10) (by decide) s u)
      (run (controlledHWord 3 le_rfl (show (0 : Fin 2) ≠ 1 by decide))
        (liftPrecision (ofKernelState K10) 3 (by decide))) := by
  intro h
  have h11 := congrFun h ![1, 1]
  rw [amp_processRemote_remoteCZ_two isCarrier_K10 _ s u,
    amp_run_controlledHWord_two isCarrier_K10 _, amp_K10,
    controlledHAmp_basis_control_one_eleven] at h11
  have hd : deltaAmp (![1, 0] : Fin 2 → ZMod 2) ![1, 1] = 0 := deltaAmp_of_ne (by decide)
  simp only [letterAmp, hd, mul_zero] at h11
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  exact one_div_ne_zero hs h11.symm

/-- **Inhabitation.** The hypotheses of `remoteCH_correct` hold together on the height-one
register: a carrier state, distinct bits `0 ≠ 1`, and precision `3` at least the state's own and
at least three. -/
-- row: inhabitation
theorem remoteCH_correct_hypotheses_heightOneState2 :
    IsCarrier heightOneState2 ∧ (0 : Fin 2) ≠ 1 ∧ heightOneState2.m ≤ 3 ∧ 3 ≤ 3 :=
  ⟨isCarrier_heightOneState2, by decide, by rw [heightOneState2_m]; norm_num, le_rfl⟩

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module

`RemoteCH.lean`'s public declarations are `remoteCHProtocol`, `remoteCHInput`, `processRemote` and
`remoteCHBranch` (definitions) and seven theorems: `castSucc_castSucc_ne_last_castSucc`,
`isCarrier_remoteCHInput`, `remoteCHInput_m`, `amp_remoteCHInput`, `processRemote_spec`,
`interpretAmp_remoteCHProtocol` and `remoteCH_correct`; its other theorems are private. No
inductive type or nested-namespace theorem is declared there, and it generates no `congr_simp`
lemma. -/

/-- info: 'FTQCLib.Frame.Walkthrough.castSucc_castSucc_ne_last_castSucc' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms castSucc_castSucc_ne_last_castSucc

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_remoteCHInput' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_remoteCHInput

/-- info: 'FTQCLib.Frame.Walkthrough.remoteCHInput_m' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms remoteCHInput_m

/-- info: 'FTQCLib.Frame.Walkthrough.amp_remoteCHInput' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_remoteCHInput

/-- info: 'FTQCLib.Frame.Walkthrough.processRemote_spec' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms processRemote_spec

/-- info: 'FTQCLib.Frame.Walkthrough.interpretAmp_remoteCHProtocol' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms interpretAmp_remoteCHProtocol

/-- info: 'FTQCLib.Frame.Walkthrough.remoteCH_correct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms remoteCH_correct

end FTQCLib.Frame.Walkthrough

-- mutant: swap_outcome_bits | FTQCLib/Carrier/RemoteCH.lean | hmk s u) (run | hmk u s) (run
-- mutant: processed_weight_quarter | FTQCLib/Carrier/RemoteCH.lean
--   | ampNormSq (remoteCHBranch k hk c t S hmk s u) = ampNormSq (remoteCHInput S k hmk) / 4
--   | ampNormSq (remoteCHBranch k hk c t S hmk s u) = ampNormSq (remoteCHInput S k hmk) / 3

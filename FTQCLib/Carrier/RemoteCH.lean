/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierScale
import FTQCLib.Carrier.ControlledHadamard

/-!
# Remote controlled-H as a protocol

Remote CH (`docs/TARGETS.md`, T16) is the circuit of `RemoteCNOT` (`Examples/ConditionalAction`)
with the local CNOT on Bob's side replaced by T08's controlled-H word (`controlledHWord`,
`ControlledHadamard.lean`), written as a protocol of T14 (`Protocol.lean`). The input is an
arbitrary carrier register `S` on `n` free bits, at any height and any precision, with any two
distinct free bits `c ≠ t`: `c` is Alice's input qubit (the control) and `t` is Bob's (the target).

**Both inputs are arbitrary.** Alice's and Bob's inputs are the bits `c` and `t` of one arbitrary
carrier register. A product of an arbitrary register of Alice's and an arbitrary register of Bob's
is one such register, and so is every entangled input; stating the protocol on the joint register
is the weaker hypothesis (LN.2). No input is fixed, unlike `RemoteCNOT`'s `∣+0⟩`.

**The shared ebit.** Two `∣+⟩` ancillas are appended (`appendFreeBit`, twice): Alice's half `A₁`,
free bit `n`, and Bob's half `B₁`, free bit `n + 1`. `appendFreeBit` keeps the scale (decision D3),
so each is `∣0⟩ + ∣1⟩`; the protocol's first letters, H on `B₁` and a CNOT from `A₁` to `B₁`, make
the pair `√2·(∣00⟩ + ∣11⟩)`. The protocol's input is the register lifted by R7 to a precision
`k ≥ 3` (T needs it, as in T08) with the two ancillas.

**The protocol** (`remoteCHProtocol`, a `Protocol k (n + 2) 2`), the steps of the source's circuit:

1. H on `B₁` and CNOT from `A₁` to `B₁`: the ebit;
2. Alice's CNOT from `c` to `A₁`;
3. the Z-measurement of `A₁`, a conditioning letter on `Z_{A₁}` with sign `+`; its outcome `s` is a
   new free bit, bit `n + 2` (decision D2 as revised);
4. Bob's X on `B₁` controlled by `s`, one CNOT letter (T13's feed-forward); then T08's
   controlled-H word with control `B₁` and target `t`, unchanged; then H on `B₁`;
5. the Z-measurement of `B₁`, its outcome `u` the new free bit `n + 3`;
6. Alice's Z on `c` controlled by `u`, one CZ letter (T13's feed-forward).

**A branch, processed** (`remoteCHBranch`). In the branch of the outcome string `(s, u)`, the two
outcome bits are evaluated at `u` and `s` and dropped (`restrictZ`, T12, whose amplitude is the
evaluation: `amp_restrictZ`); this reads the protocol's branch (T14's `branch`) as a carrier state.
Then the two ancillas, which the measurements left at the fixed bits `B₁ = u` and `A₁ = s`, are
dropped at those bits by `restrictZ`. The result is a carrier state on the register's `n` bits.

**The statement** (`remoteCH_correct`). For every carrier state `S`, at any height and precision,
every pair of distinct free bits `c ≠ t`, every precision `k ≥ 3` at least `S.m`, and each outcome
string `(s, u)`, read as T14's outcome string `![s, u]`:

* the protocol's branch weight (T14's `branchWeight`) is `¼` of the protocol input's `ampNormSq`;
* the processed branch has the same weight, `¼` of the input's;
* the processed branch is a carrier state;
* it is `StateEq` (decision D8) to T08's controlled-H word run on `S` lifted to `k`: the same
  word, `controlledHWord k hk hct`, and the same lifted input as `amp_controlledHWord`, whose
  amplitude is controlled-H applied to `amp S` (`controlledHAmp`);
* it is related to that output by T07's rules (`Relation.EqvGen CarrierRule`).

**Reading of "the input's weight".** The protocol's input is the lifted register with its two
ancillas, `remoteCHInput`, and the weights are compared with its `ampNormSq`. `appendFreeBit` keeps
the scale (D3), so each ancilla is `∣0⟩ + ∣1⟩ = √2·∣+⟩` and the input's weight is four times the
register's (`ampNormSq_appendFreeBit`, `amp_liftPrecision`). Each of the four branches is exactly
controlled-H's output, and controlled-H keeps `Σ_w |·|²` (`sum_normSq_runAmp` with
`runAmp_controlledHWord`), so each branch has the register's weight, `¼` of the input's. As in
H inject (`HInject.lean`), the clauses weight `¼` of the input's and `StateEq` to controlled-H's
output hold together only so: with normalised `∣+⟩` ancillas each branch would be `½` times
controlled-H's output.

**Frame form** (decision D5). Controlled-H is T08's word, whose referee is `controlledHAmp`; the
Z-measurements are T10's projections `½(1 + (−1)^b Z)` with the outcomes as free bits. No
`FTQCLib.Hilbert` module is imported (`liftTo` keeps its full name from before its move, as in
`ControlledHadamard.lean`).

## Main definitions

* `remoteCHProtocol` — the protocol: the ebit, Alice's CNOT and Z-measurement, Bob's correction,
  T08's controlled-H word, H and Z-measurement, and Alice's correction.
* `remoteCHInput` — the register lifted to precision `k`, with the two ancillas.
* `remoteCHBranch` — the branch of an outcome string as a carrier state on the register's bits:
  the outcome bits evaluated and dropped, then the ancillas dropped at the bits they were left at.

## Main results

* `processRemote_spec` — a processed branch of any protocol on the register and the two ancillas
  is a carrier state of the amplitude its referee gives at the outcome bits.
* `interpretAmp_remoteCHProtocol` — remote CH's referee, read with the ancillas at the outcome
  bits, is controlled-H.
* `remoteCH_correct` — each branch has weight `¼` of the input's, and each processed branch has
  the same weight, is a carrier state, is `StateEq` to T08's controlled-H word's output on the
  register, and is related to it by T07's rules (proved at T16.3).

## Implementation notes

* The H on `B₁` before its Z-measurement is the source's: it turns `B₁`, which carries a copy of
  `c` after the controlled-H, into a bit that can be measured without disturbing the inputs. After
  it, the Z-measurement leaves `B₁` at its outcome `u`, so the processing needs no H of its own,
  unlike H inject's (`HInject.lean`).
* The corrections are single letters, a CNOT from `s` to `B₁` and a CZ between `u` and `c`, the
  gates T13 names for X and Z controlled by one outcome bit; `controlledPauliWord` is not used.
* Bob's X comes before the controlled-H, as in the source: the controlled-H reads `B₁` as its
  control, so `B₁` must hold the value of `c` when it runs. So feed-forward from `s` is placed
  between the first conditioning letter and the word, which T14's syntax allows: the word is a
  `GateWord (n + 2 + 1) k`, and its letters may name the outcome bit `s`.
* The protocol does not need `c ≠ t`; the statement does, since T08's word on the register needs
  it.
* The branch weight sums the referee over every value of the two ancillas' bits. Off `A₁ = s`,
  `B₁ = u` it is zero: each Z-measurement projects its bit onto its outcome, and no letter after a
  measurement changes the measured bit (Bob's letters act on `B₁` and `t`, the H on `B₁` comes
  before `B₁`'s measurement, and the correction is diagonal). The clause on T07's rules follows
  from `rewrite_complete`: the ancillas keep the scale, and the run and every restriction multiply
  it by a power of `√2` (`ScaledBy`, `CarrierScale.lean`).

## References

* J. Eisert, K. Jacobs, P. Papadopoulos and M. B. Plenio, *Optimal local implementation of
  non-local quantum gates*, arXiv:quant-ph/0005101: the non-local CNOT circuit and the control-U
  gate by the same circuit; cited unit by unit above the declarations.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-- Bob's half of the ebit is not Bob's input qubit. -/
private theorem last_castSucc_ne_remoteCH (t : Fin n) :
    (Fin.last (n + 1)).castSucc ≠ t.castSucc.castSucc.castSucc := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

/-- Alice's input qubit is not her half of the ebit. -/
theorem castSucc_castSucc_ne_last_castSucc (c : Fin n) :
    c.castSucc.castSucc ≠ (Fin.last n).castSucc := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

/-! ## The protocol -/

-- source: papers/clifford_hierarchy/
-- Eisert_Jacobs_Papadopoulos_Plenio_2000_optimal_local_nonlocal_gates_quant-ph_0005101 figure:fig1
-- source: papers/clifford_hierarchy/
-- Eisert_Jacobs_Papadopoulos_Plenio_2000_optimal_local_nonlocal_gates_quant-ph_0005101
--   theorem:theorem2
/-- **Remote CH** at precision `k ≥ 3`, Alice's input qubit `c` and Bob's `t`, on the register's
`n` bits and the two halves of the ebit, `A₁` (bit `n`) and `B₁` (bit `n + 1`): H on `B₁` and CNOT
from `A₁` to `B₁` (the ebit); CNOT from `c` to `A₁`; the Z-measurement of `A₁`, its outcome `s` the
new free bit `n + 2`; X on `B₁` controlled by `s`, T08's controlled-H word from `B₁` to `t`, and H
on `B₁`; the Z-measurement of `B₁`, its outcome `u` the new free bit `n + 3`; Z on `c` controlled by
`u`. -/
noncomputable def remoteCHProtocol (k : ℕ) (hk : 3 ≤ k) (c t : Fin n) : Protocol k (n + 2) 2 :=
  let a₁ : Fin (n + 2) := (Fin.last n).castSucc
  let b₁ : Fin (n + 2) := Fin.last (n + 1)
  let alice : GateWord (n + 2 + 0) k :=
    [GateLetter.hadamard b₁, GateLetter.cnot a₁ b₁ (Fin.castSucc_lt_last _).ne,
      GateLetter.cnot c.castSucc.castSucc a₁ (castSucc_castSucc_ne_last_castSucc c)]
  let bob : GateWord (n + 2 + 1) k :=
    [GateLetter.cnot (Fin.last (n + 2)) b₁.castSucc (Fin.castSucc_lt_last _).ne']
      ++ controlledHWord k hk (last_castSucc_ne_remoteCH t)
      ++ [GateLetter.hadamard b₁.castSucc]
  let correction : GateWord (n + 2 + 2) k :=
    [GateLetter.diagonal
      (DiagPhase.czGate k (Fin.last (n + 3)) c.castSucc.castSucc.castSucc.castSucc)]
  let first : Protocol k (n + 2) 1 :=
    (Protocol.nil.word alice).condition (signedZ a₁) (signedZ_side a₁)
  ((first.word bob).condition (signedZ b₁.castSucc) (signedZ_side b₁.castSucc)).word
    correction

/-- **The protocol's input**: the register lifted by R7 to precision `k`, with the two halves of
the ebit appended as `∣0⟩ + ∣1⟩` each, bits `n` and `n + 1`; the protocol's first letters entangle
them. -/
noncomputable def remoteCHInput (S : KernelSumState n) (k : ℕ) (hmk : S.m ≤ k) :
    KernelSumState (n + 2) :=
  appendFreeBit (appendFreeBit (liftPrecision S k hmk))

/-! ## A branch, processed -/

/-- **The processing of a branch of any protocol** on the register and the two ancillas with two
outcome bits, on the register's `n` bits: the protocol run on its input; the outcome bits `u`
(bit `n + 3`) and `s` (bit `n + 2`) evaluated and dropped (`restrictZ`), which reads the protocol's
branch as a carrier state; then `B₁` (bit `n + 1`) dropped at `u` and `A₁` (bit `n`) dropped at
`s`, the bits the measurements left them at. -/
noncomputable def processRemote (k : ℕ) (p : Protocol k (n + 2) 2) (S : KernelSumState n)
    (hmk : S.m ≤ k) (s u : ZMod 2) : KernelSumState n :=
  restrictZ (Fin.last n) s
    (restrictZ (Fin.last (n + 1)) u
      (restrictZ (Fin.last (n + 2)) s
        (restrictZ (Fin.last (n + 3)) u (p.interpret (remoteCHInput S k hmk)))))

/-- **The branch of the outcome string `(s, u)`, processed**: `processRemote` of
`remoteCHProtocol`. -/
noncomputable def remoteCHBranch (k : ℕ) (hk : 3 ≤ k) (c t : Fin n) (S : KernelSumState n)
    (hmk : S.m ≤ k) (s u : ZMod 2) : KernelSumState n :=
  processRemote k (remoteCHProtocol k hk c t) S hmk s u

/-- The protocol's input is a carrier state. -/
theorem isCarrier_remoteCHInput {S : KernelSumState n} (hS : IsCarrier S) (k : ℕ)
    (hmk : S.m ≤ k) : IsCarrier (remoteCHInput S k hmk) :=
  isCarrier_appendFreeBit (isCarrier_appendFreeBit (isCarrier_liftPrecision hS k hmk))

/-- The protocol's input is at precision `k`. -/
theorem remoteCHInput_m (S : KernelSumState n) (k : ℕ) (hmk : S.m ≤ k) :
    (remoteCHInput S k hmk).m = k :=
  rfl

/-- The protocol's input has the register's amplitude, the two ancillas ignored. -/
theorem amp_remoteCHInput (S : KernelSumState n) (k : ℕ) (hmk : S.m ≤ k) :
    amp (remoteCHInput S k hmk) = fun x => amp S (Fin.init (Fin.init x)) := by
  unfold remoteCHInput
  rw [amp_appendFreeBit, amp_appendFreeBit, amp_liftPrecision]

/-- A function that agrees with a nonzero `G` along a map is nonzero. -/
private theorem ne_zero_of_comp_eq {N : ℕ} {A : (Fin N → ZMod 2) → ℂ}
    {G : (Fin n → ZMod 2) → ℂ} (hG : G ≠ 0) (e : (Fin n → ZMod 2) → (Fin N → ZMod 2))
    (h : ∀ w, A (e w) = G w) : A ≠ 0 := by
  intro hA
  apply hG
  funext w
  rw [← h w, hA]
  rfl

/-- **A processed branch, from its referee.** If a protocol's referee on the input's amplitude,
read with the ancillas and the outcome bits at `(s, u)`, is a nonzero function `G` of the
register's bits, the processed branch is a carrier state of amplitude `G`. Each restriction needs
the carrier property of its input, which holds since its amplitude agrees with `G` along an
embedding. -/
theorem processRemote_spec {S : KernelSumState n} (hS : IsCarrier S) (k : ℕ) (hmk : S.m ≤ k)
    (p : Protocol k (n + 2) 2) (s u : ZMod 2) {G : (Fin n → ZMod 2) → ℂ} (hG : G ≠ 0)
    (hp : ∀ w, p.interpretAmp (fun x => amp S (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u) = G w) :
    IsCarrier (processRemote k p S hmk s u) ∧ amp (processRemote k p S hmk s u) = G := by
  obtain ⟨h0c, h0a⟩ := amp_interpret p (isCarrier_remoteCHInput hS k hmk) rfl
  rw [amp_remoteCHInput] at h0a
  set X0 := p.interpret (remoteCHInput S k hmk) with hX0
  set X1 := restrictZ (Fin.last (n + 3)) u X0 with hX1
  have e1 : ∀ w, amp X1 (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) = G w := by
    intro w
    rw [hX1, amp_restrictZ h0c, Fin.insertNth_last', h0a]
    exact hp w
  have h1c : IsCarrier X1 := isCarrier_restrictZ h0c _ _ (ne_zero_of_comp_eq hG _ e1)
  set X2 := restrictZ (Fin.last (n + 2)) s X1 with hX2
  have e2 : ∀ w, amp X2 (Fin.snoc (Fin.snoc w s) u) = G w := by
    intro w
    rw [hX2, amp_restrictZ h1c, Fin.insertNth_last']
    exact e1 w
  have h2c : IsCarrier X2 := isCarrier_restrictZ h1c _ _ (ne_zero_of_comp_eq hG _ e2)
  set X3 := restrictZ (Fin.last (n + 1)) u X2 with hX3
  have e3 : ∀ w, amp X3 (Fin.snoc w s) = G w := by
    intro w
    rw [hX3, amp_restrictZ h2c, Fin.insertNth_last']
    exact e2 w
  have h3c : IsCarrier X3 := isCarrier_restrictZ h2c _ _ (ne_zero_of_comp_eq hG _ e3)
  have e4 : amp (restrictZ (Fin.last n) s X3) = G := by
    funext w
    rw [amp_restrictZ h3c, Fin.insertNth_last']
    exact e3 w
  refine ⟨isCarrier_restrictZ h3c _ _ ?_, e4⟩
  rw [e4]
  exact hG

/-! ## The proof: the referee in closed form -/

/-- **The protocol's referee is controlled-H.** On the register's amplitude `f` with the two
ancillas ignored, read with the ebit's halves and the outcome bits at the outcome string `(s, u)`
(`A₁ = s`, `B₁ = u`), the referee is controlled-H applied to `f`. The protocol is unfolded letter
by letter, T08's word replaced by its referee (`runAmp_controlledHWord`); the evaluation points
are snocs of the register's word, so each update of a free bit is pushed through them. The last
step splits on the control bit and the two outcomes, with `r = 1/√2` and `r² = ½`. -/
theorem interpretAmp_remoteCHProtocol (k : ℕ) (hk : 3 ≤ k) {c t : Fin n} (hct : c ≠ t)
    (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) (s u : ZMod 2) :
    (remoteCHProtocol k hk c t).interpretAmp (fun x => f (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w s) u) s) u) = controlledHAmp c t f w := by
  unfold remoteCHProtocol
  dsimp only
  rw [Protocol.interpretAmp_word, Protocol.interpretAmp_condition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_condition, Protocol.interpretAmp_word, Protocol.interpretAmp_nil]
  simp only [runAmp_append, runAmp_cons, runAmp_nil, runAmp_controlledHWord]
  simp only [letterAmp, pauliProjection_signedZ, walshTransform, controlledHAmp,
    DiagPhase.cnotBitMap, Fin.snoc_last, Fin.snoc_castSucc, Fin.init_snoc, ← Fin.snoc_update,
    Fin.update_snoc_last, charOf_czGate_eval (by omega : 1 ≤ k)]
  simp only [if_true, Function.update_of_ne hct, if_neg (one_ne_zero : (1 : ZMod 2) ≠ 0)]
  have h2 : (1 / (Real.sqrt 2 : ℂ)) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  generalize 1 / (Real.sqrt 2 : ℂ) = r at h2 ⊢
  have h3 : r ^ 3 = r * (1 / 2) := by rw [pow_succ, h2, mul_comm]
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  generalize f w = A
  generalize f (Function.update w t 0) = B
  generalize f (Function.update w t 1) = C
  generalize signOf (w t) = D
  generalize w c = a
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one u with rfl | rfl <;>
    simp (config := { decide := true }) only [signOf, if_true, if_false, ZMod.val_zero, hv1,
      mul_zero, mul_one, pow_zero, pow_one] <;>
    ring_nf <;> (try simp only [h2, h3]) <;> ring

/-- **The referee off the measured bits.** Read with `A₁ ≠ s` or `B₁ ≠ u`, the referee is zero:
the Z-measurement of `A₁` projects onto `A₁ = s` and no later letter changes `A₁` (Bob's letters
act on `B₁` and `t`, the correction is diagonal); the Z-measurement of `B₁` projects onto `B₁ = u`
after the H on `B₁`, and the correction is diagonal. -/
private theorem interpretAmp_remoteCHProtocol_of_ne (k : ℕ) (hk : 3 ≤ k) (c t : Fin n)
    (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) {a b s u : ZMod 2} (h : a ≠ s ∨ b ≠ u) :
    (remoteCHProtocol k hk c t).interpretAmp (fun x => f (Fin.init (Fin.init x)))
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc w a) b) s) u) = 0 := by
  unfold remoteCHProtocol
  dsimp only
  rw [Protocol.interpretAmp_word, Protocol.interpretAmp_condition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_condition, Protocol.interpretAmp_word, Protocol.interpretAmp_nil]
  simp only [runAmp_append, runAmp_cons, runAmp_nil, runAmp_controlledHWord]
  simp only [letterAmp, pauliProjection_signedZ, walshTransform, controlledHAmp,
    DiagPhase.cnotBitMap, Fin.snoc_last, Fin.snoc_castSucc, Fin.init_snoc, ← Fin.snoc_update,
    Fin.update_snoc_last, charOf_czGate_eval (by omega : 1 ≤ k)]
  rcases h with h | h
  · simp only [if_neg h, mul_zero, add_zero, ite_self]
  · simp only [if_neg h, mul_zero]

/-! ## The weights -/

/-- **The branch weight** of the outcome string `(s, u)` is the weight of controlled-H's output:
the sum over the ancillas' bits keeps only `A₁ = s`, `B₁ = u`, where the referee is controlled-H
(`interpretAmp_remoteCHProtocol`); off them it is zero (`interpretAmp_remoteCHProtocol_of_ne`). -/
private theorem branchWeight_remoteCH {S : KernelSumState n} (hS : IsCarrier S) {c t : Fin n}
    (hct : c ≠ t) (k : ℕ) (hmk : S.m ≤ k) (hk : 3 ≤ k) (s u : ZMod 2) :
    (remoteCHProtocol k hk c t).branchWeight (remoteCHInput S k hmk) ![s, u]
      = ∑ w : Fin n → ZMod 2, Complex.normSq (controlledHAmp c t (amp S) w) := by
  unfold Protocol.branchWeight Protocol.branch
  rw [(amp_interpret (remoteCHProtocol k hk c t) (isCarrier_remoteCHInput hS k hmk)
    (remoteCHInput_m S k hmk)).2, amp_remoteCHInput]
  refine (Finset.sum_congr rfl fun w _ => by rw [append_pair w s u]).trans ?_
  rw [sum_words_snoc]
  refine (Finset.sum_congr rfl fun b _ => sum_words_snoc _).trans ?_
  rw [Finset.sum_eq_single u, Finset.sum_eq_single s]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [interpretAmp_remoteCHProtocol k hk hct]
  · intro a _ ha
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [interpretAmp_remoteCHProtocol_of_ne k hk c t _ _ (Or.inl ha), map_zero]
  · intro h
    exact absurd (Finset.mem_univ s) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun w _ => ?_
    rw [interpretAmp_remoteCHProtocol_of_ne k hk c t _ _ (Or.inr hb), map_zero]
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- **The input's weight** is four times the register's: each `∣0⟩ + ∣1⟩` ancilla doubles it
(`ampNormSq_appendFreeBit`, D3), and R7 keeps the amplitude (`amp_liftPrecision`). -/
private theorem ampNormSq_remoteCHInput (S : KernelSumState n) (k : ℕ) (hmk : S.m ≤ k) :
    ampNormSq (remoteCHInput S k hmk) = 4 * ampNormSq S := by
  unfold remoteCHInput
  rw [ampNormSq_appendFreeBit, ampNormSq_appendFreeBit]
  unfold ampNormSq
  rw [amp_liftPrecision]
  ring

/-! ## The scale along the processing -/

/-- The processed branch's scale is the lifted register's times a power of `√2`, or zero: the
ancillas keep the scale (D3), and the run and each restriction scale by a power of `√2`. -/
private theorem scaledBy_processRemote (k : ℕ) (p : Protocol k (n + 2) 2) (S : KernelSumState n)
    (hmk : S.m ≤ k) (s u : ZMod 2) :
    ScaledBy (liftPrecision S k hmk).c (processRemote k p S hmk s u).c :=
  ((((scaledBy_interpret p (remoteCHInput S k hmk)).trans (scaledBy_restrictZ _ _ _)).trans
    (scaledBy_restrictZ _ _ _)).trans (scaledBy_restrictZ _ _ _)).trans (scaledBy_restrictZ _ _ _)

/-! ## The statement -/

-- source: papers/clifford_hierarchy/
-- Eisert_Jacobs_Papadopoulos_Plenio_2000_optimal_local_nonlocal_gates_quant-ph_0005101
--   theorem:theorem2
/-- **Remote CH is correct.** For every carrier state `S`, at any height and any precision, every
pair of distinct free bits `c ≠ t` (Alice's input qubit and Bob's), every precision `k ≥ 3` at
least `S.m`, and each outcome string `(s, u)`, on the protocol's input (the register lifted to `k`
with its two `∣0⟩ + ∣1⟩` ancillas): the protocol's branch at `![s, u]` has weight `¼` of that
input's (T14's `branchWeight`, D3); the branch processed (the outcome bits evaluated and dropped,
the ebit's halves dropped at the bits the measurements left them at) has weight `¼` of the
input's, is a carrier state, is `StateEq` (D8) to T08's controlled-H word run on `S` lifted to
`k`, whose amplitude is controlled-H applied to `amp S` (`amp_controlledHWord`), and is related to
it by T07's rules. The two ancillas multiply the register's weight by four, so `¼` of the input's
is the register's own. Proved at T16.3. -/
theorem remoteCH_correct {S : KernelSumState n} (hS : IsCarrier S) {c t : Fin n} (hct : c ≠ t)
    (k : ℕ) (hmk : S.m ≤ k) (hk : 3 ≤ k) (s u : ZMod 2) :
    (remoteCHProtocol k hk c t).branchWeight (remoteCHInput S k hmk) ![s, u]
        = ampNormSq (remoteCHInput S k hmk) / 4 ∧
      ampNormSq (remoteCHBranch k hk c t S hmk s u) = ampNormSq (remoteCHInput S k hmk) / 4 ∧
      IsCarrier (remoteCHBranch k hk c t S hmk s u) ∧
      StateEq (remoteCHBranch k hk c t S hmk s u) (run (controlledHWord k hk hct)
        (liftPrecision S k hmk)) ∧
      Relation.EqvGen CarrierRule (remoteCHBranch k hk c t S hmk s u)
        (run (controlledHWord k hk hct) (liftPrecision S k hmk)) := by
  obtain ⟨hHc, hHamp⟩ := amp_controlledHWord hS hct k hmk hk
  have hG : controlledHAmp c t (amp S) ≠ 0 := by
    rw [← hHamp]
    exact hHc.2.2.2
  obtain ⟨hBc, hBamp⟩ := processRemote_spec hS k hmk (remoteCHProtocol k hk c t) s u hG
    (fun w => interpretAmp_remoteCHProtocol k hk hct (amp S) w s u)
  have hquarter : ampNormSq (remoteCHInput S k hmk) / 4 = ampNormSq S := by
    rw [ampNormSq_remoteCHInput]
    ring
  refine ⟨?_, ?_, hBc, hBamp.trans hHamp.symm, ?_⟩
  · rw [hquarter, branchWeight_remoteCH hS hct k hmk hk]
    exact sum_normSq_controlledHAmp k hk hct (amp S)
  · rw [hquarter]
    unfold ampNormSq remoteCHBranch
    rw [hBamp]
    exact sum_normSq_controlledHAmp k hk hct (amp S)
  · exact eqvGen_carrierRule_of_scaledBy hBc hHc (hBamp.trans hHamp.symm)
      (scaledBy_processRemote k _ S hmk s u) (scaledBy_run _ (liftPrecision S k hmk))

end FTQCLib.Frame.Walkthrough

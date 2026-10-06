/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierScale

/-!
# H inject: one-bit teleportation of H as a protocol

One-bit teleportation of H (`docs/TARGETS.md`, T15) is a protocol of T14 (`Protocol.lean`) on an
arbitrary carrier register `S` with `n` free bits, at any height and any precision, and any free
bit `j` of it, the **input qubit**:

1. a `∣+⟩` ancilla, appended as the new last free bit, bit `n` (`appendFreeBit`);
2. CZ between the input qubit and the ancilla, one diagonal letter (`czGate`);
3. the X-measurement of the input qubit, a conditioning letter on `X_j` with sign `+`, whose
   outcome is a new free bit, bit `n + 1` (decision D2 as revised);
4. X on the ancilla controlled by the outcome bit, one CNOT letter: T13's feed-forward, a word on
   the data and outcome free bits.

This is `hInjectProtocol`, a `Protocol m (n + 1) 1`: its data bits are the register's `n` bits and
the ancilla, and its one outcome bit is the X-measurement's.

**A branch, processed** (`hInjectBranch`). In the branch of outcome `b`, the protocol's branch is
read as a carrier state by evaluating the outcome bit at `b` and dropping it (`restrictZ`, T12,
whose amplitude is the evaluation: `amp_restrictZ`). On that state the measured qubit is turned to
a fixed bit by an H letter: it is `∣±⟩` after the X-measurement, so after H it is `∣b⟩`. Then the
ancilla is moved into its place, by the relabelling of free bits that swaps bit `j` and bit `n`
(`permuteFreeBits`, T10), and the measured qubit, now the last bit and fixed at `b`, is dropped by
`restrictZ` at `b`. The result is a carrier state on the register's `n` bits, with the ancilla in
the input qubit's place.

**The statement** (`hInject_correct`). For every carrier state `S`, at any height and precision,
every free bit `j` and each outcome `b`:

* the protocol's branch weight (T14's `branchWeight`) is `½` of the protocol input's `ampNormSq`;
* the processed branch has the same weight, `½` of the input's;
* the processed branch is a carrier state;
* it is `StateEq` to the unitary H's output, T05's run of the one-letter word `H_j` on `S`
  (decision D8);
* it is related to that output by T07's rules (`Relation.EqvGen CarrierRule`).

**Reading of "the input's weight".** The protocol's input is the register with its ancilla,
`appendFreeBit S`, and the weights are compared with its `ampNormSq`. `appendFreeBit` keeps the
scale (D3), so its ancilla is `∣0⟩ + ∣1⟩ = √2·∣+⟩` and the input's weight is twice the register's:
each branch then has the register's weight, as an H output must, since H keeps `Σ_w |·|²`. The
target's two clauses, weight `½` of the input's and `StateEq` to H's output, hold together only so:
with a normalised `∣+⟩` the branch is `1/√2` times H's output, of weight `½` of the register's,
and not `StateEq` to H's output.

**Frame form** (decision D5). The unitary H is T05's H letter, whose referee is the Walsh
transform (`walshTransform`); the X-measurement is T10's projection `½(1 + (−1)^b X_j)` with the
outcome as a free bit. No `FTQCLib.Hilbert` module is imported.

## Main definitions

* `hInjectProtocol` — the protocol: CZ, the X-measurement of the input qubit into an outcome bit,
  and X on the ancilla controlled by it.
* `hInjectBranch` — the branch of an outcome as a carrier state on the register's bits: the
  outcome bit evaluated and dropped, H on the measured qubit, the ancilla moved into its place,
  and the measured qubit dropped.

## Main results

* `hInject_correct` — each branch has weight `½` of the input's, is a carrier state, is `StateEq`
  to the unitary H's output, and is related to it by T07's rules (proved at T15.3).

## Implementation notes

* The protocol runs at the register's own precision `S.m`, which is at least `1` on a carrier
  state: CZ is `2^{m−1}·x_j·x_n` at every precision `m ≥ 1`, and `X_j` has no Y, so no lift (R7) is
  needed and the conditioning letter's side condition holds at every `m` (`yWeight_paulix`).
* The ancilla's correction is one CNOT letter from the outcome bit to the ancilla: X controlled by
  the outcome bit, the gate T13 names for a Pauli whose X-part is one bit and whose Z-part is
  zero. `controlledPauliWord` is not used, so the word is exactly the one letter.
* `restrictZ` is used twice: once to read the protocol's branch, an evaluation of the outcome bit,
  as a carrier state; once to drop the measured qubit at the bit H fixed it to. Both are cuts to a
  slice followed by dropping a free bit, so neither depends on how the run's support is recorded
  (`dropFreeBit` alone needs the support to determine the bit).
* The proof computes the branch in closed form on amplitude functions (`injectRead_eq`): after H
  on the measured qubit the amplitude vanishes off the slice where that qubit is `b`, and on it
  is the Walsh transform of the register's amplitude with the ancilla as the input qubit
  (`walsh_injectRead`). The weights follow from the Walsh transform being an isometry, and the
  clause on T07's rules from `rewrite_complete`: every step of the processing, and H's run,
  multiplies the scale by a power of `√2` (`ScaledBy`, `CarrierScale.lean`), so the two scales
  have a dyadic ratio.
* The general facts the proof uses (the carrier property kept by `appendFreeBit`, `restrictZ` and
  `permuteFreeBits`, `yWeight_paulix`, the CZ phase, the scale) are public in their own modules
  (docs/STEPS.md, entry 2026-10-01g).

## References

* X. Zhou, D. W. Leung and I. L. Chuang, *Methodology for quantum logic gate construction*,
  arXiv:quant-ph/0002039: one-bit teleportation; cited unit by unit above the declarations.
* D. Gottesman and I. L. Chuang, *Quantum teleportation is a universal computational primitive*,
  arXiv:quant-ph/9908010: gates performed by teleportation; cited above `hInject_correct`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The protocol -/

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:zteleport
-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:xztel
/-- **H inject** at precision `m` on input qubit `j`, on the register's `n` bits and the ancilla,
bit `n`: CZ between bit `j` and the ancilla; the X-measurement of bit `j` with sign `+`, its
outcome the new free bit `n + 1`; then X on the ancilla controlled by the outcome bit, a CNOT. -/
noncomputable def hInjectProtocol (m : ℕ) (j : Fin n) : Protocol m (n + 1) 1 :=
  let cz : GateWord (n + 1 + 0) m :=
    [GateLetter.diagonal (DiagPhase.czGate m j.castSucc (Fin.last n))]
  let correction : GateWord (n + 1 + 1) m :=
    [GateLetter.cnot (Fin.last (n + 1)) (Fin.last n).castSucc (Fin.castSucc_lt_last _).ne']
  ((Protocol.nil.word cz).condition ⟨0, paulix j.castSucc⟩
      (fun h => by rw [yWeight_paulix] at h; exact absurd h (by decide))).word correction

/-! ## A branch, processed -/

/-- **The branch of outcome `b`, processed**, on the register's `n` bits: the protocol run on the
register with its `∣+⟩` ancilla (`appendFreeBit`); the outcome bit evaluated at `b` and dropped
(`restrictZ`), which reads the protocol's branch as a carrier state; H on the measured qubit `j`,
which turns it to the fixed bit `b`; the ancilla moved into its place by swapping bits `j` and `n`;
and the measured qubit, now bit `n`, dropped at `b`. -/
noncomputable def hInjectBranch (m : ℕ) (j : Fin n) (S : KernelSumState n) (b : ZMod 2) :
    KernelSumState n :=
  restrictZ (Fin.last n) b
    (permuteFreeBits (Equiv.swap j.castSucc (Fin.last n))
      (run ([GateLetter.hadamard j.castSucc] : GateWord (n + 1) m)
        (restrictZ (Fin.last (n + 1)) b ((hInjectProtocol m j).interpret (appendFreeBit S)))))

/-! ## The proof: the branch in closed form -/

/-- The branch of outcome `b` read on the register and its ancilla, on amplitude functions: the
protocol's referee on the register's amplitude `f` with its ancilla, the outcome bit at `b`. -/
private noncomputable def injectRead (m : ℕ) (j : Fin n) (f : (Fin n → ZMod 2) → ℂ) (b : ZMod 2) :
    (Fin (n + 1) → ZMod 2) → ℂ :=
  fun u => (hInjectProtocol m j).interpretAmp (fun x => f (Fin.init x))
    (Fin.insertNth (Fin.last (n + 1)) b u)

/-- The correction leaves the outcome bit unchanged. -/
private theorem cnotBitMap_snoc_last (u : Fin (n + 1) → ZMod 2) (b : ZMod 2) :
    DiagPhase.cnotBitMap (Fin.last (n + 1)) (Fin.last n).castSucc (Fin.snoc u b)
      (Fin.last (n + 1)) = b := by
  unfold DiagPhase.cnotBitMap
  rw [Function.update_of_ne (Fin.castSucc_lt_last _).ne', Fin.snoc_last]

/-- The correction adds the outcome bit to the ancilla. -/
private theorem init_cnotBitMap_snoc (u : Fin (n + 1) → ZMod 2) (b : ZMod 2) :
    Fin.init (DiagPhase.cnotBitMap (Fin.last (n + 1)) (Fin.last n).castSucc (Fin.snoc u b))
      = Function.update u (Fin.last n) (u (Fin.last n) + b) := by
  unfold DiagPhase.cnotBitMap
  rw [Fin.init_update_castSucc, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Flipping a bit other than the last commutes with dropping the last. -/
private theorem init_add_single (y : Fin (n + 1) → ZMod 2) (j : Fin n) :
    Fin.init (y + Pi.single j.castSucc 1) = Fin.init y + Pi.single j 1 := by
  funext i
  simp only [Fin.init, Pi.add_apply]
  congr 1
  by_cases h : i = j
  · rw [h, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (fun e => h (Fin.castSucc_injective _ e)), Pi.single_eq_of_ne h]

/-- The branch read on the register and its ancilla, in closed form. -/
private theorem injectRead_eq {m : ℕ} (hm : 1 ≤ m) (j : Fin n) (f : (Fin n → ZMod 2) → ℂ)
    (b : ZMod 2) (u : Fin (n + 1) → ZMod 2) :
    injectRead m j f b u = (1 / 2) *
      ((-1 : ℂ) ^ ((u j.castSucc).val * (u (Fin.last n) + b).val) * f (Fin.init u)
        + (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ ((u j.castSucc + 1).val * (u (Fin.last n) + b).val)
          * f (Fin.init u + Pi.single j 1))) := by
  have hjL : j.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
  unfold injectRead hInjectProtocol
  dsimp only
  rw [Protocol.interpretAmp_word, Protocol.interpretAmp_condition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_nil]
  simp only [runAmp_cons, runAmp_nil, letterAmp, pauliProjection, SignedPauli.act, pauliAct,
    Fin.insertNth_last']
  rw [cnotBitMap_snoc_last, init_cnotBitMap_snoc, yWeight_paulix, zDot_paulix,
    paulix_X, charOf_czGate_eval hm, charOf_czGate_eval hm, init_add_single,
    Fin.init_update_last]
  simp only [Pi.add_apply, Function.update_of_ne hjL, Function.update_self,
    Pi.single_eq_same, Pi.single_eq_of_ne hjL.symm, add_zero, ZMod.val_zero, pow_zero, one_mul]

/-- Flipping a bit set to `x` sets it to `x + 1`. -/
private theorem update_add_single (w : Fin n → ZMod 2) (j : Fin n) (x : ZMod 2) :
    Function.update w j x + Pi.single j 1 = Function.update w j (x + 1) := by
  funext i
  by_cases h : i = j
  · subst h
    rw [Pi.add_apply, Function.update_self, Function.update_self, Pi.single_eq_same]
  · rw [Pi.add_apply, Function.update_of_ne h, Function.update_of_ne h, Pi.single_eq_of_ne h,
      add_zero]

/-- The four values of the Walsh combination of the closed form. -/
private theorem walsh_combination (c a b : ZMod 2) (F0 F1 : ℂ) :
    (1 / (Real.sqrt 2 : ℂ)) *
      ((1 / 2) * ((-1 : ℂ) ^ ((0 : ZMod 2).val * (a + b).val) * F0
          + (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ ((1 : ZMod 2).val * (a + b).val) * F1))
        + signOf c * ((1 / 2) * ((-1 : ℂ) ^ ((1 : ZMod 2).val * (a + b).val) * F1
          + (-1 : ℂ) ^ b.val * ((-1 : ℂ) ^ ((0 : ZMod 2).val * (a + b).val) * F0))))
      = if c = b then (1 / (Real.sqrt 2 : ℂ)) * (F0 + signOf a * F1) else 0 := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp (config := { decide := true }) [signOf] <;> ring

private theorem walsh_injectRead {m : ℕ} (hm : 1 ≤ m) (j : Fin n) (f : (Fin n → ZMod 2) → ℂ)
    (b : ZMod 2) (v : Fin (n + 1) → ZMod 2) :
    walshTransform j.castSucc (injectRead m j f b) v
      = if v j.castSucc = b then (1 / (Real.sqrt 2 : ℂ)) *
          (f (Function.update (Fin.init v) j 0)
            + signOf (v (Fin.last n)) * f (Function.update (Fin.init v) j 1))
        else 0 := by
  have hjL : j.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
  unfold walshTransform
  rw [injectRead_eq hm, injectRead_eq hm]
  simp only [Function.update_self, Function.update_of_ne hjL.symm, Fin.init_update_castSucc,
    update_add_single]
  rw [zero_add, show (1 + 1 : ZMod 2) = 0 from rfl]
  exact walsh_combination (v j.castSucc) (v (Fin.last n)) b _ _

/-- With the ancilla moved into the input qubit's place and the measured qubit at `b`, the
closed form is the Walsh transform of the register at the input qubit. -/
private theorem walsh_injectRead_swap {m : ℕ} (hm : 1 ≤ m) (j : Fin n)
    (f : (Fin n → ZMod 2) → ℂ) (b : ZMod 2) (w : Fin n → ZMod 2) :
    walshTransform j.castSucc (injectRead m j f b)
        (Fin.insertNth (Fin.last n) b w ∘ Equiv.swap j.castSucc (Fin.last n))
      = walshTransform j f w := by
  have h1 : (Fin.insertNth (Fin.last n) b w ∘ Equiv.swap j.castSucc (Fin.last n)) j.castSucc
      = b := by
    rw [Function.comp_apply, Equiv.swap_apply_left, Fin.insertNth_last', Fin.snoc_last]
  have h2 : (Fin.insertNth (Fin.last n) b w ∘ Equiv.swap j.castSucc (Fin.last n)) (Fin.last n)
      = w j := by
    rw [Function.comp_apply, Equiv.swap_apply_right, Fin.insertNth_last', Fin.snoc_castSucc]
  have h3 : Fin.init (Fin.insertNth (Fin.last n) b w ∘ Equiv.swap j.castSucc (Fin.last n))
      = Function.update w j b := by
    funext i
    rw [Fin.init, Function.comp_apply]
    by_cases h : i = j
    · subst h
      rw [Equiv.swap_apply_left, Fin.insertNth_last', Fin.snoc_last, Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun e => h (Fin.castSucc_injective _ e))
        (Fin.castSucc_lt_last i).ne, Fin.insertNth_last', Fin.snoc_castSucc,
        Function.update_of_ne h]
  rw [walsh_injectRead hm, if_pos h1, h2, h3, Function.update_idem, Function.update_idem]
  rfl

/-- **The branch's weight**, on amplitude functions: the branch read on the register and its
ancilla has the register's `Σ_w |·|²`. -/
private theorem sum_normSq_injectRead {m : ℕ} (hm : 1 ≤ m) (j : Fin n)
    (f : (Fin n → ZMod 2) → ℂ) (b : ZMod 2) :
    ∑ u : Fin (n + 1) → ZMod 2, Complex.normSq (injectRead m j f b u)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w) := by
  set σ := Equiv.swap j.castSucc (Fin.last n) with hσ
  have hinv : Function.Involutive (fun u : Fin (n + 1) → ZMod 2 => u ∘ σ) := by
    intro u
    funext i
    simp only [Function.comp_apply, hσ, Equiv.swap_apply_self]
  rw [← walsh_normSq_isometry j.castSucc,
    ← Fintype.sum_equiv (Function.Involutive.toPerm _ hinv)
      (fun u => Complex.normSq (walshTransform j.castSucc (injectRead m j f b) (u ∘ σ))) _
      (fun _ => rfl),
    sum_words_snoc, Finset.sum_eq_single b]
  · refine (Finset.sum_congr rfl fun w _ => ?_).trans (walsh_normSq_isometry j f)
    rw [← Fin.insertNth_last', walsh_injectRead_swap hm]
  · intro c _ hc
    refine Finset.sum_eq_zero fun w _ => ?_
    have hj : (Fin.snoc w c ∘ σ : Fin (n + 1) → ZMod 2) j.castSucc = c := by
      rw [Function.comp_apply, hσ, Equiv.swap_apply_left, Fin.snoc_last]
    rw [walsh_injectRead hm, if_neg (by rw [hj]; exact hc), map_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-! ## The scale along the processing -/

/-- The processed branch's scale is the register's times a power of `√2`, or zero. -/
private theorem scaledBy_hInjectBranch (m : ℕ) (j : Fin n) (S : KernelSumState n) (b : ZMod 2) :
    ScaledBy S.c (hInjectBranch m j S b).c := by
  unfold hInjectBranch
  set I := (hInjectProtocol m j).interpret (appendFreeBit S)
  set R := restrictZ (Fin.last (n + 1)) b I
  set H := run ([GateLetter.hadamard j.castSucc] : GateWord (n + 1) m) R
  set P := permuteFreeBits (Equiv.swap j.castSucc (Fin.last n)) H
  have hI : ScaledBy S.c I.c := scaledBy_interpret (hInjectProtocol m j) (appendFreeBit S)
  have hR : ScaledBy I.c R.c := scaledBy_restrictZ (Fin.last (n + 1)) b I
  have hH : ScaledBy R.c H.c := scaledBy_run _ R
  have hP : ScaledBy H.c P.c := ScaledBy.refl H.c
  exact (((hI.trans hR).trans hH).trans hP).trans (scaledBy_restrictZ (Fin.last n) b P)

/-! ## The processed branch -/

/-- The branch read as a carrier state has the closed form's amplitude. -/
private theorem amp_restrictZ_interpret_hInject {S : KernelSumState n} (hS : IsCarrier S)
    (j : Fin n) (b : ZMod 2) :
    amp (restrictZ (Fin.last (n + 1)) b ((hInjectProtocol S.m j).interpret (appendFreeBit S)))
      = injectRead S.m j (amp S) b := by
  have hI := amp_interpret (hInjectProtocol S.m j) (isCarrier_appendFreeBit hS) rfl
  funext v
  rw [amp_restrictZ hI.1, hI.2, amp_appendFreeBit]
  rfl

/-- **The processed branch**: a carrier state whose amplitude is the Walsh transform of the
register's at the input qubit. -/
private theorem hInjectBranch_spec {S : KernelSumState n} (hS : IsCarrier S) (j : Fin n)
    (b : ZMod 2) :
    IsCarrier (hInjectBranch S.m j S b) ∧
      amp (hInjectBranch S.m j S b) = walshTransform j (amp S) := by
  have hm1 : 1 ≤ S.m := hS.1
  have hI := amp_interpret (hInjectProtocol S.m j) (isCarrier_appendFreeBit hS) rfl
  set R := restrictZ (Fin.last (n + 1)) b ((hInjectProtocol S.m j).interpret (appendFreeBit S))
    with hR
  have hRamp : amp R = injectRead S.m j (amp S) b := amp_restrictZ_interpret_hInject hS j b
  have hW : walshTransform j (amp S) ≠ 0 := fun h =>
    hS.2.2.2 (eq_zero_of_walshTransform_eq_zero j h)
  have hRne : amp R ≠ 0 := by
    intro h0
    apply hW
    funext w
    rw [← walsh_injectRead_swap hm1, ← hRamp, h0]
    simp only [walshTransform, Pi.zero_apply, mul_zero, add_zero]
  have hRc : IsCarrier R := isCarrier_restrictZ hI.1 _ _ hRne
  have hRm : R.m = S.m := by
    rw [hR, restrictZ_m hI.1.1]
    exact interpret_m _ hm1 rfl
  set H := run ([GateLetter.hadamard j.castSucc] : GateWord (n + 1) S.m) R with hH
  have hHc : IsCarrier H := isCarrier_run _ hRc hRm
  have hHamp : amp H = walshTransform j.castSucc (amp R) := amp_run _ hRc hRm
  set P := permuteFreeBits (Equiv.swap j.castSucc (Fin.last n)) H with hP
  have hPc : IsCarrier P := isCarrier_permuteFreeBits _ hHc
  have hamp : amp (restrictZ (Fin.last n) b P) = walshTransform j (amp S) := by
    funext w
    rw [amp_restrictZ hPc, hP, amp_permuteFreeBits, hHamp, hRamp]
    exact walsh_injectRead_swap hm1 j (amp S) b w
  have hB : hInjectBranch S.m j S b = restrictZ (Fin.last n) b P := rfl
  rw [hB]
  exact ⟨isCarrier_restrictZ hPc _ _ (by rw [hamp]; exact hW), hamp⟩

/-! ## The statement -/

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:generalonebit
-- source: papers/clifford_hierarchy/
-- Gottesman_Chuang_1999_universal_via_teleportation_quant-ph_9908010 figure:fig:ftqc-ck
/-- **H inject is correct.** For every carrier state `S`, at any height and any precision, every
input qubit `j` and each outcome `b`, run at the register's precision on the register with its
`∣+⟩` ancilla: the protocol's branch has weight `½` of that input's (T14's `branchWeight`, D3);
the branch processed (the measured qubit turned to the fixed bit `b` by H and dropped, the ancilla
moved into its place) has weight `½` of the input's, is a carrier state, is `StateEq` to the
unitary H's output, T05's run of `H_j` on `S` (D8), and is related to it by T07's rules. The
ancilla `∣0⟩ + ∣1⟩` doubles the register's weight, so `½` of the input's is the register's own.
Proved at T15.3. -/
theorem hInject_correct {S : KernelSumState n} (hS : IsCarrier S) (j : Fin n) (b : ZMod 2) :
    (hInjectProtocol S.m j).branchWeight (appendFreeBit S) (fun _ => b)
        = ampNormSq (appendFreeBit S) / 2 ∧
      ampNormSq (hInjectBranch S.m j S b) = ampNormSq (appendFreeBit S) / 2 ∧
      IsCarrier (hInjectBranch S.m j S b) ∧
      StateEq (hInjectBranch S.m j S b) (run ([GateLetter.hadamard j] : GateWord n S.m) S) ∧
      Relation.EqvGen CarrierRule (hInjectBranch S.m j S b)
        (run ([GateLetter.hadamard j] : GateWord n S.m) S) := by
  obtain ⟨hBc, hBamp⟩ := hInjectBranch_spec hS j b
  have hHamp : amp (run ([GateLetter.hadamard j] : GateWord n S.m) S) = walshTransform j (amp S) :=
    amp_run _ hS rfl
  have hHc : IsCarrier (run ([GateLetter.hadamard j] : GateWord n S.m) S) := isCarrier_run _ hS rfl
  have hhalf : ampNormSq (appendFreeBit S) / 2 = ampNormSq S := by
    rw [ampNormSq_appendFreeBit]
    ring
  have hst : StateEq (hInjectBranch S.m j S b) (run ([GateLetter.hadamard j] : GateWord n S.m) S) :=
    hBamp.trans hHamp.symm
  refine ⟨?_, ?_, hBc, hst, ?_⟩
  · rw [hhalf]
    unfold Protocol.branchWeight Protocol.branch
    have hI := amp_interpret (hInjectProtocol S.m j) (isCarrier_appendFreeBit hS) rfl
    rw [hI.2, amp_appendFreeBit]
    refine (Finset.sum_congr rfl fun u _ => ?_).trans (sum_normSq_injectRead hS.1 j (amp S) b)
    rw [Fin.append_right_eq_snoc, ← Fin.insertNth_last']
    rfl
  · rw [hhalf]
    unfold ampNormSq
    rw [hBamp]
    exact walsh_normSq_isometry j (amp S)
  · exact eqvGen_carrierRule_of_scaledBy hBc hHc hst (scaledBy_hInjectBranch S.m j S b)
      (scaledBy_run ([GateLetter.hadamard j] : GateWord n S.m) S)

end FTQCLib.Frame.Walkthrough

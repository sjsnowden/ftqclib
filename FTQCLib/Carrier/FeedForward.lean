/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.GateWord
import FTQCLib.Carrier.Conditioning

/-!
# Feed-forward and reconvergence on carrier states

**Feed-forward is a word** (`docs/TARGETS.md`, T13; decision D2 as revised). With the outcome of
conditioning carried as a free bit (`conditionOutcome`), a gate chosen by the outcome is that gate
controlled by the outcome bit, a gate on the data and outcome free bits. For the two kinds of gate
a capstone's correction is made of, the controlled gate is a word of T05's letters
(`GateWord.lean`):

* **a Pauli** `M` with its sign, controlled by bit `c` (`controlledPauliWord`): one CNOT from `c`
  to each bit of `M`'s X-part (`controlledShiftWord`), then one diagonal letter, `X_c` times the
  exponent of the factor `(−1)^{sign}·i^{yWeight}·(−1)^{Z·(w + X)}` that `M` puts on its shifted
  branch (`branchPhase`, from `Conditioning.lean`). That letter is the CZs from `c` to the bits of
  `M`'s Z-part, together with the phase `(−1)^{sign + Z·X}·i^{yWeight}` on `c`;
* **a diagonal gate** given by a phase polynomial `D`, controlled by bit `c`
  (`controlledDiagonal`): the one diagonal letter `X_c · D`.

The referees (decision D5) are the controlled actions: the word's referee is `M`'s action where
bit `c` is one and the identity where it is zero (`runAmp_controlledPauliWord`), and the letter's
is multiplication by the phase where bit `c` is one (`letterAmp_controlledDiagonal`). Neither
word has an H letter, so its run has the referee's amplitude on every state at the word's
precision, carrier or not (`amp_run_of_forall_ne_hadamard`, `amp_run_controlledPauliWord`); the
conditioned state needs nothing of the carrier property for it.

**Reconvergence** (`reconverge`). Condition on a Pauli `P` with the outcome as a new last free bit,
then apply, controlled by that bit, a Pauli `M` that stabilizes the input's amplitude with its
sign (`M f = f`) and anticommutes with `P` (`ω(M, P) = 1`): the anticommuting witness as
correction (`correctOutcome`). The corrected state's evaluations at both outcomes are equal, and
both are the outcome-`0` projection `Π_0 f`. On amplitudes, `M Π_1 f = Π_0 (M f) = Π_0 f`.

**Frame form of the guide.** The guide is `branch_reconverges`
(`FTQCLib/Examples/ConditionalAction/Reset.lean`), stated on pure signed stabilizer states through
Hilbert definitions (`injStepWith`, `cliffordActionPure`). Here it is stated frame-pure, as D5
requires: the witness's membership of the signed Lagrangian is its stabilizing of the amplitude,
`M.act (amp S) = amp S`, and the two branches are evaluations of the outcome free bit. The guide
compares states up to a global phase; this statement compares amplitudes, so the witness carries
its sign.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported.

## Main definitions

* `controlledShiftWord` — the CNOTs from bit `c` to the bits of an X-part.
* `controlledDiagonal` — a diagonal gate controlled by bit `c`, one diagonal letter.
* `controlledPauliWord` — a Pauli with its sign controlled by bit `c`, a word of CNOTs and one
  diagonal letter.
* `SignedPauli.appendId` — a Pauli on the data bits, acting as the identity on a new last bit.
* `correctOutcome` — conditioning with the outcome bit, then the Pauli controlled by that bit.

## Main results

* `letterAmp_controlledDiagonal`, `runAmp_controlledPauliWord` — the referees are the controlled
  gates.
* `amp_run_of_forall_ne_hadamard`, `amp_run_controlledPauliWord` — an H-free word's run has the
  referee's amplitude on every state at its precision.
* `reconverge` — with the anticommuting witness as correction, the corrected state's evaluations
  at both outcomes are the outcome-`0` projection (proved at T13.3).

## Implementation notes

* `reconverge` takes co-isotropy of `L`, which is what `amp_conditionOutcome` needs, and nothing
  else of the carrier property: the correction has no H letter.
* The diagonal letter lives at the word's precision, so a witness with an odd number of Y needs
  precision at least two at the conditioned state, for `i`; `reconverge` carries that hypothesis.
  Conditioning raises the precision to two only for a `P` with an odd number of Y.
* A Pauli whose X-part has bit `c` cannot be controlled by `c` with a CNOT; the referee theorem
  carries `M.pauli.X c = 0`, which `SignedPauli.appendId` meets at the last bit.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The controlled gates as words -/

/-- The CNOT from bit `c` to bit `j`, when `j ≠ c` and `a j = 1`; nothing otherwise. -/
def shiftLetter {m : ℕ} (c : Fin n) (a : Fin n → ZMod 2) (j : Fin n) : Option (GateLetter n m) :=
  if h : c ≠ j ∧ a j = 1 then some (GateLetter.cnot c j h.1) else none

/-- The CNOTs from bit `c` to every bit `j ≠ c` of the X-part `a`: the shift `w ↦ w + w_c·a`. -/
def controlledShiftWord {m : ℕ} (c : Fin n) (a : Fin n → ZMod 2) : GateWord n m :=
  (List.finRange n).filterMap (shiftLetter c a)

/-- **A diagonal gate controlled by bit `c`**: the one diagonal letter `X_c · D`, whose phase is
`D`'s where bit `c` is one and trivial where it is zero. -/
noncomputable def controlledDiagonal {m : ℕ} (c : Fin n) (D : DiagPhase n m) : GateLetter n m :=
  GateLetter.diagonal (MvPolynomial.X c * D)

/-- **A Pauli with its sign controlled by bit `c`**: the CNOTs from `c` to `M`'s X-part, then the
diagonal letter `X_c` times the exponent of `M`'s factor on its shifted branch, which is the CZs
from `c` to `M`'s Z-part and `M`'s constant phase on `c`. -/
noncomputable def controlledPauliWord {m : ℕ} (c : Fin n) (M : SignedPauli n) : GateWord n m :=
  controlledShiftWord c M.pauli.X ++ [controlledDiagonal c (branchPhase m id M 0)]

/-! ## The referees -/

/-- The CNOT letters over a list without repeats shift the word by `w_c` at the listed bits of the
X-part other than `c`. -/
private theorem runAmp_filterMap_shiftLetter {m : ℕ} (c : Fin n) (a : Fin n → ZMod 2)
    (l : List (Fin n)) (hl : l.Nodup) (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (l.filterMap (shiftLetter c a) : GateWord n m) f
      = fun w => f (fun k => w k + if k ∈ l ∧ (c ≠ k ∧ a k = 1) then w c else 0) := by
  induction l generalizing f with
  | nil =>
    funext w
    simp only [List.filterMap_nil, runAmp_nil, List.not_mem_nil, false_and, if_false, add_zero]
  | cons j l ih =>
    obtain ⟨hjl, hl'⟩ := List.nodup_cons.1 hl
    by_cases hj : c ≠ j ∧ a j = 1
    · have hcons : (j :: l).filterMap (shiftLetter c a)
          = (GateLetter.cnot c j hj.1 : GateLetter n m) :: l.filterMap (shiftLetter c a) := by
        simp only [List.filterMap_cons, shiftLetter, dif_pos hj]
      rw [hcons, runAmp_cons, ih hl']
      funext w
      simp only [letterAmp, cnotBitMap]
      congr 1
      funext k
      have hcc : ¬ (c ∈ l ∧ (c ≠ c ∧ a c = 1)) := fun h => h.2.1 rfl
      rw [Function.update_apply]
      by_cases hk : k = j
      · subst hk
        simp only [if_true, hjl, false_and, if_false, add_zero, hcc, List.mem_cons_self, true_and,
          hj]
        rw [if_pos ⟨hj.1, trivial⟩]
      · rw [if_neg hk]
        simp only [List.mem_cons, hk, false_or]
    · have hcons : (j :: l).filterMap (shiftLetter c a)
          = (l.filterMap (shiftLetter c a) : GateWord n m) := by
        simp only [List.filterMap_cons, shiftLetter, dif_neg hj]
      rw [hcons, ih hl']
      funext w
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk
        simp only [hjl, if_false, hj, and_false]
      · simp only [List.mem_cons, hk, false_or]

/-- **The referee of the controlled shift**: the input at `w + w_c·a`, for an X-part `a` with
`a c = 0`. -/
theorem runAmp_controlledShiftWord {m : ℕ} (c : Fin n) (a : Fin n → ZMod 2) (hc : a c = 0)
    (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (controlledShiftWord c a : GateWord n m) f
      = fun w => if w c = 1 then f (w + a) else f w := by
  unfold controlledShiftWord
  rw [runAmp_filterMap_shiftLetter c a _ (List.nodup_finRange n)]
  funext w
  have hbit : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  split_ifs with hw
  · congr 1
    funext k
    simp only [List.mem_finRange, true_and, hw, Pi.add_apply]
    by_cases hk : k = c
    · subst hk
      simp only [ne_eq, not_true_eq_false, false_and, if_false, hc]
    · have hck : c ≠ k := fun h => hk h.symm
      rcases hbit (a k) with ha | ha <;> simp [hck, ha]
  · have hw0 : w c = 0 := (hbit (w c)).resolve_right hw
    congr 1
    funext k
    simp only [hw0, ite_self, add_zero]

/-- **The referee of a controlled diagonal gate**: multiplication by `D`'s phase where bit `c` is
one, and the identity where it is zero. -/
theorem letterAmp_controlledDiagonal {m : ℕ} (c : Fin n) (D : DiagPhase n m)
    (f : (Fin n → ZMod 2) → ℂ) :
    letterAmp (controlledDiagonal c D) f
      = fun w => if w c = 1 then charOf m (D.eval w) * f w else f w := by
  funext w
  have hbit : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  simp only [controlledDiagonal, letterAmp, DiagPhase.eval, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, DiagPhase.liftBinary]
  rcases hbit (w c) with hw | hw
  · rw [hw, if_neg (by decide), ZMod.val_zero, Nat.cast_zero, zero_mul, charOf_zero, one_mul]
  · rw [hw, if_pos rfl, ZMod.val_one, Nat.cast_one, one_mul]

/-- **The referee of a controlled Pauli**: `M`'s action, with its sign, where bit `c` is one, and
the identity where it is zero. It needs `M`'s X-part off `c`, and the precision `i^{yWeight}`
needs. -/
theorem runAmp_controlledPauliWord {m : ℕ} (c : Fin n) (M : SignedPauli n)
    (hc : M.pauli.X c = 0) (hm : 1 ≤ m) (hodd : yWeight M.pauli % 2 = 1 → 2 ≤ m)
    (f : (Fin n → ZMod 2) → ℂ) :
    runAmp (controlledPauliWord c M : GateWord n m) f
      = fun w => if w c = 1 then M.act f w else f w := by
  unfold controlledPauliWord
  rw [runAmp_append, runAmp_cons, runAmp_nil, runAmp_controlledShiftWord c _ hc,
    letterAmp_controlledDiagonal]
  funext w
  split_ifs with hw
  · rw [charOf_branchPhase_eval id M 0 hm hodd w]
    simp only [SignedPauli.act, pauliAct, ZMod.val_zero, pow_zero, one_mul, id]
    ring
  · rfl

/-! ## Runs of H-free words -/

/-- **An H-free word has the referee's amplitude on every state** at its precision: CNOT and
diagonal letters need no carrier property (`amp_applyCnotSum`, `amp_applyDiagSum`). -/
theorem amp_run_of_forall_ne_hadamard {m : ℕ} (gs : GateWord n m)
    (hH : ∀ g ∈ gs, ∀ k : Fin n, g ≠ GateLetter.hadamard k) (S : KernelSumState n)
    (hm : S.m = m) : amp (run gs S) = runAmp gs (amp S) := by
  induction gs generalizing S with
  | nil => rw [run_nil, runAmp_nil]
  | cons g gs ih =>
    have hletter : amp (applyLetter g S) = letterAmp g (amp S) := by
      cases g with
      | hadamard k => exact absurd rfl (hH _ (List.mem_cons.2 (Or.inl rfl)) k)
      | diagonal D =>
        subst hm
        rw [applyLetter_diagonal]
        exact amp_applyDiagSum S D
      | cnot i j hij =>
        rw [applyLetter_cnot]
        exact amp_applyCnotSum hij S
    rw [run_cons, runAmp_cons, ← hletter]
    exact ih (fun g' hg' => hH g' (List.mem_cons_of_mem _ hg')) _ ((applyLetter_m g S).trans hm)

/-- The controlled Pauli word has no H letter. -/
theorem controlledPauliWord_ne_hadamard {m : ℕ} (c : Fin n) (M : SignedPauli n) :
    ∀ g ∈ (controlledPauliWord c M : GateWord n m), ∀ k : Fin n, g ≠ GateLetter.hadamard k := by
  intro g hg k hgk
  subst hgk
  rcases List.mem_append.1 hg with hA | hd
  · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 hA
    unfold shiftLetter at hj
    split_ifs at hj with h
    cases hj
  · cases List.mem_singleton.1 hd

/-- **The run of a controlled Pauli** on any state at the word's precision: `M`'s action where bit
`c` is one, the identity where it is zero. -/
theorem amp_run_controlledPauliWord {m : ℕ} (c : Fin n) (M : SignedPauli n)
    (hc : M.pauli.X c = 0) (hm1 : 1 ≤ m) (hodd : yWeight M.pauli % 2 = 1 → 2 ≤ m)
    (S : KernelSumState n) (hm : S.m = m) :
    amp (run (controlledPauliWord c M : GateWord n m) S)
      = fun w => if w c = 1 then M.act (amp S) w else amp S w := by
  rw [amp_run_of_forall_ne_hadamard _ (controlledPauliWord_ne_hadamard c M) S hm,
    runAmp_controlledPauliWord c M hc hm1 hodd]

/-! ## Reconvergence -/

/-- A Pauli with its sign on the data bits, acting as the identity on a new last bit. -/
def SignedPauli.appendId (M : SignedPauli n) : SignedPauli (n + 1) :=
  ⟨M.sign, pauliSnoc M.pauli 0⟩

/-- **The corrected state.** Condition on `P` with the outcome as a new last free bit
(`conditionOutcome`), then apply `M`, controlled by that bit (`controlledPauliWord`), at the
conditioned state's precision: feed-forward as one word on the data and outcome free bits. -/
noncomputable def correctOutcome (S : KernelSumState n) (P M : SignedPauli n) :
    KernelSumState (n + 1) :=
  run (controlledPauliWord (m := (conditionOutcome S P).m) (Fin.last n) M.appendId)
    (conditionOutcome S P)

/-- The Z-sign exponent of a Pauli extended by the identity, at a word extended by any bit, is the
Pauli's at the word: the last qubit has no Z-part. -/
private theorem zDot_pauliSnoc_snoc (p : Pauli n) (v : Fin n → ZMod 2) (b : ZMod 2) :
    zDot (pauliSnoc p 0) (Fin.snoc v b : Fin (n + 1) → ZMod 2) = zDot p v := by
  unfold zDot
  rw [Fin.sum_univ_castSucc]
  change ∑ i : Fin n, ((Fin.snoc p.Z 0 : Fin (n + 1) → ZMod 2) i.castSucc).val
        * ((Fin.snoc v b : Fin (n + 1) → ZMod 2) i.castSucc).val
      + ((Fin.snoc p.Z 0 : Fin (n + 1) → ZMod 2) (Fin.last n)).val
        * ((Fin.snoc v b : Fin (n + 1) → ZMod 2) (Fin.last n)).val = _
  simp only [Fin.snoc_castSucc, Fin.snoc_last, ZMod.val_zero, zero_mul, add_zero]

/-- Extending by the identity keeps the number of Y. -/
private theorem yWeight_appendId (M : SignedPauli n) :
    yWeight M.appendId.pauli = yWeight M.pauli :=
  zDot_pauliSnoc_snoc M.pauli M.pauli.X 0

/-- The shift of a Pauli extended by the identity keeps the last bit. -/
private theorem snoc_add_appendId (M : SignedPauli n) (w : Fin n → ZMod 2) (b : ZMod 2) :
    (Fin.snoc w b : Fin (n + 1) → ZMod 2) + M.appendId.pauli.X = Fin.snoc (w + M.pauli.X) b := by
  change (Fin.snoc w b : Fin (n + 1) → ZMod 2) + Fin.snoc M.pauli.X 0 = _
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Pi.add_apply, Fin.snoc_last, add_zero]
  · simp only [Pi.add_apply, Fin.snoc_castSucc]

/-- **A Pauli extended by the identity acts on each fibre of the last bit** as the Pauli does. -/
private theorem act_appendId_snoc (M : SignedPauli n) (g : (Fin (n + 1) → ZMod 2) → ℂ)
    (w : Fin n → ZMod 2) (b : ZMod 2) :
    M.appendId.act g (Fin.snoc w b : Fin (n + 1) → ZMod 2)
      = M.act (fun u => g (Fin.snoc u b : Fin (n + 1) → ZMod 2)) w := by
  have hz : zDot M.appendId.pauli (Fin.snoc (w + M.pauli.X) b : Fin (n + 1) → ZMod 2)
      = zDot M.pauli (w + M.pauli.X) :=
    zDot_pauliSnoc_snoc M.pauli (w + M.pauli.X) b
  simp only [SignedPauli.act, pauliAct]
  rw [snoc_add_appendId, hz, yWeight_appendId]
  rfl

/-- **Anticommuting signed Paulis.** When `ω(M, P) = 1`, `M P f = −P M f`, signs included. -/
private theorem act_act_of_omega_eq_one {M P : SignedPauli n} (hanti : omega M.pauli P.pauli = 1)
    (f : (Fin n → ZMod 2) → ℂ) : M.act (P.act f) = fun w => -P.act (M.act f) w := by
  funext w
  have h := pauliAct_anticomm hanti f w
  unfold SignedPauli.act
  rw [pauliAct_mul_left, pauliAct_mul_left]
  linear_combination ((-1 : ℂ) ^ M.sign.val * (-1 : ℂ) ^ P.sign.val) * h

/-- **The witness exchanges the projections.** A signed Pauli that fixes `f` and anticommutes with
`P` sends the outcome-`1` projection of `f` to its outcome-`0` projection. -/
private theorem act_pauliProjection_one {M P : SignedPauli n} (f : (Fin n → ZMod 2) → ℂ)
    (hstab : M.act f = f) (hanti : omega M.pauli P.pauli = 1) :
    M.act (pauliProjection P 1 f) = pauliProjection P 0 f := by
  have hone : (1 : ZMod 2).val = 1 := rfl
  have hlin : M.act (pauliProjection P 1 f)
      = fun w => (1 / 2 : ℂ) * (M.act f w - M.act (P.act f) w) := by
    funext w
    simp only [SignedPauli.act, pauliAct, pauliProjection, hone]
    ring
  rw [hlin, act_act_of_omega_eq_one hanti, hstab]
  funext w
  simp only [pauliProjection, ZMod.val_zero, pow_zero]
  ring

/-- The conditioned state's precision is positive: both constructors take the conditioning
precision. -/
private theorem one_le_conditionOutcome_m (S : KernelSumState n) (P : SignedPauli n) :
    1 ≤ (conditionOutcome S P).m := by
  unfold conditionOutcome condition
  split_ifs
  · exact one_le_conditionPrecision (appendFreeBit S).m P.appendZ
  · exact one_le_conditionPrecision (appendFreeBit S).m P.appendZ

/-- **Reconvergence.** With the anticommuting witness as correction (a Pauli `M` with its sign
that stabilizes the input's amplitude and anticommutes with `P`), the corrected state's
evaluations at both outcomes are equal: each is the outcome-`0` projection `½(f + P f)` of the
input's amplitude `f`. The frame form, on amplitudes, of `branch_reconverges`. Proved at T13.3. -/
theorem reconverge (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P M : SignedPauli n)
    (hstab : M.act (amp S) = amp S) (hanti : omega M.pauli P.pauli = 1)
    (hodd : yWeight M.pauli % 2 = 1 → 2 ≤ (conditionOutcome S P).m) (b : ZMod 2) :
    (fun w : Fin n → ZMod 2 => amp (correctOutcome S P M) (Fin.snoc w b : Fin (n + 1) → ZMod 2))
      = pauliProjection P 0 (amp S) := by
  have hc : M.appendId.pauli.X (Fin.last n) = 0 := by
    change (Fin.snoc M.pauli.X 0 : Fin (n + 1) → ZMod 2) (Fin.last n) = 0
    rw [Fin.snoc_last]
  have hodd' : yWeight M.appendId.pauli % 2 = 1 → 2 ≤ (conditionOutcome S P).m := by
    rw [yWeight_appendId]
    exact hodd
  have hrun := amp_run_controlledPauliWord (Fin.last n) M.appendId hc
    (one_le_conditionOutcome_m S P) hodd' (conditionOutcome S P) rfl
  unfold correctOutcome
  rw [hrun]
  funext w
  rcases zmod_two_eq_zero_or_one b with hb | hb <;> subst hb
  · have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp only [Fin.snoc_last, h01, if_false]
    rw [amp_conditionOutcome S horth P]
    simp only [Fin.init_snoc, Fin.snoc_last]
  · simp only [Fin.snoc_last, if_true]
    rw [act_appendId_snoc, amp_conditionOutcome S horth P]
    simp only [Fin.init_snoc, Fin.snoc_last]
    rw [act_pauliProjection_one (amp S) hstab hanti]

end FTQCLib.Frame.Walkthrough

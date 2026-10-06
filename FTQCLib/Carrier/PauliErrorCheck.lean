/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PauliError

/-!
# Check: Pauli errors on carrier states

T64's witness (`docs/STEPS.md`, T64.2): rows on the frozen statement of `PauliError.lean`, on small
instances. No row uses a headline theorem of `PauliError.lean` (`amp_applyPauli`,
`applyPauli_stateEq_pauliWord`, `PauliGroup.act_act`, `interpret_append`, `interpret_insertAt`,
`runAmp_outcomePauliWord`): the move's amplitude is computed from its record by `amp_pos`,
`amp_neg` and the exponent's value; a run's amplitude from the letters' referees (`letterAmp`),
through the private `runAmp_hadamard_sandwich` (H, a sign controlled by a bit function, H is the
controlled X), and a protocol's interpretation by `amp_interpret` (`Protocol.lean`).

The input is the one-bit basis state `∣0⟩` on the carrier (`ketZero`: Lagrangian `⟨Z⟩`, offset
`0`, exponent `0`, scale `1`, precision `1`); `ketOne` is the same record with offset `1`.

* **Row 1 (agreement).** X on `ketZero` has `ketOne`'s amplitude.
* **Row 2 (agreement).** Y on `ketZero` runs at precision `2` and has `i` times `ketOne`'s
  amplitude.
* **Row 3, `O1` (discriminating).** X then Z, against Z then X, on `ketZero`: at the word `1` the
  first is `−1` and the second `1`, so the order of application matters.
* **Row 4 (agreement).** Two Z-conditionings, the second appended to the first by
  `Protocol.append`, are the two-letter protocol, as interpretations.
* **Row 5 (agreement).** A measurement error after a Z-conditioning of `ketZero`: the faulty
  protocol's amplitude at `(w, b)` is the conditioned state's at `(w, b + 1)`, so the state moves to
  the other branch.
* **Row 6 (agreement).** `outcomePauliWord` with `d(s) = X^s` on one data bit and one outcome bit
  has the referee of T13's `controlledPauliWord` controlled by the outcome bit.
* **Row 7 (agreement).** `outcomePauliWord` with `d ≡ ⟨0, Y⟩` on one outcome bit, at precision `2`,
  is `i` times X after Z on the data bit (`Y = iXZ` as matrices): the factor `i^{yWeight}`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Cohomology

/-! ## Helpers on exponents and Walsh transforms -/

/-- `0 ≠ 1` in `ZMod 2`. -/
private theorem zero_ne_one_pauliError : (0 : ZMod 2) ≠ 1 := by decide

/-- `1 + 1 = 0` in `ZMod 2`. -/
private theorem one_add_one_pauliError : (1 : ZMod 2) + 1 = 0 := by decide

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem bit_cases_pauliError (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- An amplitude of a height-zero record is its scale times the character of its exponent. -/
private theorem ampCore_of_h_eq_zero {n : ℕ} (S : KernelSumState n) (hh : S.h = 0)
    (w : Fin n → ZMod 2) :
    ampCore S.m S.h S.Q S.c w
      = S.c * charOf S.m (S.Q.eval (Fin.append w (fun _ => 0))) := by
  obtain ⟨m, h, Q, c, L, x₀⟩ := S
  subst hh
  rw [ampCore_zero, exp_realPhase_eq_charOf, append_fin0]

/-- The character of the move's exponent: the input's exponent at the translated word, times the
character of `pauliErrorPhase`. -/
private theorem charOf_eval_applyPauli {n : ℕ} (P : PauliGroup n) (S : KernelSumState n)
    (v : Fin (n + S.h) → ZMod 2) :
    charOf (applyPauli P S).m ((applyPauli P S).Q.eval v)
      = charOf S.m (S.Q.eval (fun l => v l + Fin.append P.base.X (0 : Fin S.h → ZMod 2) l))
        * charOf (pauliPrecision S.m P)
          ((pauliErrorPhase (pauliPrecision S.m P) (Fin.castAdd S.h) P P.base.X).eval v) := by
  have hT : (1 : DiagPhase (n + S.h) (pauliPrecision S.m P)).eval v
      = (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ pauliPrecision S.m P)) := by
    simp [DiagPhase.eval]
  change charOf (pauliPrecision S.m P)
      ((shiftSubst id P.base.X 1
          (FTQCLib.Hilbert.liftTo (pauliPrecision S.m P) (le_pauliPrecision S.m P) S.Q)
        + pauliErrorPhase (pauliPrecision S.m P) (Fin.castAdd S.h) P P.base.X).eval v) = _
  rw [DiagPhase.eval_add, charOf_add, shiftSubst_eval id P.base.X 1 _ v 1 hT, charOf_eval_liftTo]
  simp only [id, one_mul]

/-- The character of `pauliErrorPhase` at a positive precision, `2` or more where `e + yWeight` is
odd: the sign `(−1)^{Σ_j z_j·(v_j + t_j)}` times `i^{e + yWeight}`. -/
private theorem charOf_eval_pauliErrorPhase {n N k : ℕ} (hk : 1 ≤ k) (ι : Fin n → Fin N)
    (P : PauliGroup n) (t : Fin n → ZMod 2)
    (hodd : (P.phase.val + yWeight P.base) % 2 = 1 → 2 ≤ k) (v : Fin N → ZMod 2) :
    charOf k ((pauliErrorPhase k ι P t).eval v)
      = (-1) ^ (∑ j : Fin n, (P.base.Z j).val * ((v (ι j)).val + (t j).val))
        * Complex.I ^ (P.phase.val + yWeight P.base) := by
  unfold pauliErrorPhase
  rw [DiagPhase.eval_add, charOf_add, DiagPhase.eval_C, charOf_iPowExp _ hk hodd,
    DiagPhase.eval_mul, DiagPhase.eval_C]
  congr 1
  have hsum : DiagPhase.eval
      (∑ j : Fin n, MvPolynomial.C (((P.base.Z j).val : ZMod (2 ^ k)))
        * (MvPolynomial.X (ι j) + MvPolynomial.C (((t j).val : ZMod (2 ^ k))))) v
      = ((∑ j : Fin n, (P.base.Z j).val * ((v (ι j)).val + (t j).val) : ℕ) : ZMod (2 ^ k)) := by
    simp only [DiagPhase.eval, map_sum, map_mul, map_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X, DiagPhase.liftBinary]
    push_cast
    rfl
  rw [hsum, charOf_two_pow_mul hk]

/-- The translation by `e_j` is the update of bit `j` to its flip. -/
private theorem update_flip_eq_add_single {N : ℕ} (w : Fin N → ZMod 2) (j : Fin N) :
    Function.update w j (w j + 1) = w + Pi.single j 1 := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp
  · simp [hl]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- **H, a controlled sign, H is the controlled X**: on bit `j`, with a diagonal letter whose
character is `(−1)^{c(w)·w_j}` for a bit function `c` that does not read bit `j`, the three
letters translate by `e_j` where `c` is `1` and do nothing where it is `0`. -/
private theorem runAmp_hadamard_sandwich {N m : ℕ} (j : Fin N) (D : DiagPhase N m)
    (c : (Fin N → ZMod 2) → ZMod 2)
    (hD : ∀ w, charOf m (D.eval w) = (-1) ^ ((c w).val * (w j).val))
    (hc : ∀ w b, c (Function.update w j b) = c w) (f : (Fin N → ZMod 2) → ℂ) :
    runAmp ([GateLetter.hadamard j, GateLetter.diagonal D, GateLetter.hadamard j] :
        GateWord N m) f
      = fun w => if c w = 1 then f (w + Pi.single j 1) else f w := by
  funext w
  have h2 : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs0 : signOf (0 : ZMod 2) = 1 := by unfold signOf; rw [if_pos rfl]
  have hs1 : signOf (1 : ZMod 2) = -1 := by unfold signOf; rw [if_neg (by decide)]
  simp only [runAmp_cons, runAmp_nil, letterAmp, walshTransform, Function.update_idem,
    Function.update_self, hD, hc, hs0, hs1, ZMod.val_zero, ZMod.val_one, mul_zero, mul_one,
    pow_zero, one_mul]
  rcases bit_cases_pauliError (c w) with hcw | hcw <;>
    rcases bit_cases_pauliError (w j) with hwj | hwj
  · have hw : Function.update w j 0 = w := by rw [← hwj]; exact Function.update_eq_self j w
    rw [hcw, hwj, hs0, hw, if_neg zero_ne_one_pauliError]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    linear_combination (2 * f w) * h2
  · have hw : Function.update w j 1 = w := by rw [← hwj]; exact Function.update_eq_self j w
    rw [hcw, hwj, hs1, hw, if_neg zero_ne_one_pauliError]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    linear_combination (2 * f w) * h2
  · have hflip : w + Pi.single j 1 = Function.update w j 1 := by
      rw [← update_flip_eq_add_single, hwj, zero_add]
    rw [hcw, hwj, hs0, if_pos rfl, hflip]
    simp only [ZMod.val_one, pow_one]
    linear_combination (2 * f (Function.update w j 1)) * h2
  · have hflip : w + Pi.single j 1 = Function.update w j 0 := by
      rw [← update_flip_eq_add_single, hwj]
      rfl
    rw [hcw, hwj, hs1, if_pos rfl, hflip]
    simp only [ZMod.val_one, pow_one]
    linear_combination (2 * f (Function.update w j 0)) * h2

/-! ## The instance: one bit -/

/-- Z on one bit, as a register element. -/
private def zGenOne : Pauli 1 := ⟨0, fun _ => 1⟩

/-- The Lagrangian `⟨Z⟩` of a one-bit basis state. -/
private noncomputable def zLine : Submodule (ZMod 2) (Pauli 1) :=
  Submodule.span (ZMod 2) {zGenOne}

/-- The support of a record with Lagrangian `⟨Z⟩` is its offset alone. -/
private theorem support_zLine (x₀ w : Fin 1 → ZMod 2) :
    (∃ p ∈ zLine, w = x₀ + p.X) ↔ w = x₀ := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
    change x₀ + a • zGenOne.X = x₀
    change x₀ + a • (0 : Fin 1 → ZMod 2) = x₀
    rw [smul_zero, add_zero]
  · intro hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    change w = x₀ + 0
    rw [add_zero, hw]

/-- The amplitude of a record with Lagrangian `⟨Z⟩`: its on-support amplitude at its offset, zero
elsewhere. -/
private theorem amp_of_L_eq_zLine (S : KernelSumState 1) (hL : S.L = zLine)
    (w : Fin 1 → ZMod 2) :
    amp S w = if w = S.x₀ then ampCore S.m S.h S.Q S.c w else 0 := by
  by_cases hw : w = S.x₀
  · rw [if_pos hw, amp_pos ((hL ▸ support_zLine S.x₀ w).mpr hw)]
  · rw [if_neg hw, amp_neg (fun h => hw ((hL ▸ support_zLine S.x₀ w).mp h))]

/-- `∣0⟩` on the carrier: Lagrangian `⟨Z⟩`, offset `0`, exponent `0`, scale `1`, precision `1`. -/
noncomputable def ketZero : KernelSumState 1 := ⟨1, 0, 0, 1, zLine, 0⟩

/-- `∣1⟩` on the carrier: `ketZero` with offset `1`. -/
noncomputable def ketOne : KernelSumState 1 := ⟨1, 0, 0, 1, zLine, fun _ => 1⟩

/-- X on one bit, phase `0`. -/
def pauliXOne : PauliGroup 1 := ⟨0, ⟨fun _ => 1, 0⟩⟩

/-- Z on one bit, phase `0`. -/
def pauliZOne : PauliGroup 1 := ⟨0, ⟨0, fun _ => 1⟩⟩

/-- Y on one bit, phase `0`: the register element with both parts `1`. -/
def pauliYOne : PauliGroup 1 := ⟨0, ⟨fun _ => 1, fun _ => 1⟩⟩

/-- The two one-bit words. -/
private theorem fin_one_word_cases (w : Fin 1 → ZMod 2) : w = 0 ∨ w = fun _ => 1 := by
  rcases bit_cases_pauliError (w 0) with h | h
  · left
    funext i
    fin_cases i
    exact h
  · right
    funext i
    fin_cases i
    exact h

/-- The basis state `∣1⟩`'s amplitude: `1` at the word `1`, `0` at the word `0`. -/
theorem amp_ketOne (w : Fin 1 → ZMod 2) :
    amp ketOne w = if w = (fun _ => 1) then 1 else 0 := by
  rw [amp_of_L_eq_zLine ketOne rfl]
  change (if w = (fun _ => 1) then ampCore ketOne.m ketOne.h ketOne.Q ketOne.c w else 0) = _
  split_ifs with hw
  · rw [ampCore_of_h_eq_zero ketOne rfl]
    change (1 : ℂ) * charOf 1 ((0 : DiagPhase (1 + 0) 1).eval _) = 1
    rw [eval_zero_poly, charOf_zero, one_mul]
  · rfl

/-- The basis state `∣0⟩`'s exponent has character `1` at every word. -/
private theorem charOf_eval_ketZero (v : Fin (1 + 0) → ZMod 2) :
    charOf ketZero.m (ketZero.Q.eval v) = 1 := by
  change charOf 1 ((0 : DiagPhase (1 + 0) 1).eval v) = 1
  rw [eval_zero_poly, charOf_zero]

/-- X has no Y. -/
private theorem yWeight_pauliXOne : yWeight pauliXOne.base = 0 := by
  simp [yWeight, zDot, pauliXOne]

/-- Z has no Y. -/
private theorem yWeight_pauliZOne : yWeight pauliZOne.base = 0 := by
  simp [yWeight, zDot, pauliZOne]

/-- Y has one Y. -/
private theorem yWeight_pauliYOne : yWeight pauliYOne.base = 1 := by
  simp [yWeight, zDot, pauliYOne]

/-- A Pauli without Y and with phase `0` meets the odd-phase precision condition vacuously. -/
private theorem hodd_of_yWeight_zero {n k : ℕ} (P : PauliGroup n) (he : P.phase = 0)
    (hy : yWeight P.base = 0) : (P.phase.val + yWeight P.base) % 2 = 1 → 2 ≤ k := by
  rw [he, hy, ZMod.val_zero]
  intro h
  exact absurd h (by decide)

/-- The move's offset on `ketZero` is the X-part. -/
private theorem x₀_applyPauli_ketZero (P : PauliGroup 1) :
    (applyPauli P ketZero).x₀ = P.base.X := by
  change (0 : Fin 1 → ZMod 2) + P.base.X = P.base.X
  rw [zero_add]

/-- X on `ketZero`, at the word `1`: the amplitude `1`. -/
private theorem ampCore_applyPauli_X_ketZero (w : Fin 1 → ZMod 2) :
    ampCore (applyPauli pauliXOne ketZero).m (applyPauli pauliXOne ketZero).h
      (applyPauli pauliXOne ketZero).Q (applyPauli pauliXOne ketZero).c w = 1 := by
  rw [ampCore_of_h_eq_zero _ rfl, charOf_eval_applyPauli, charOf_eval_ketZero,
    charOf_eval_pauliErrorPhase (one_le_pauliPrecision _ _) _ _ _
      (hodd_of_yWeight_zero _ rfl yWeight_pauliXOne)]
  change (1 : ℂ) * (1 * _) = 1
  simp only [yWeight_pauliXOne]
  simp [pauliXOne]

/-- Y on `ketZero`, at the word `1`: the amplitude `i`. -/
private theorem ampCore_applyPauli_Y_ketZero (w : Fin 1 → ZMod 2) (hw : w = fun _ => 1) :
    ampCore (applyPauli pauliYOne ketZero).m (applyPauli pauliYOne ketZero).h
      (applyPauli pauliYOne ketZero).Q (applyPauli pauliYOne ketZero).c w = Complex.I := by
  have hm : 2 ≤ pauliPrecision ketZero.m pauliYOne := by
    unfold pauliPrecision
    rw [yWeight_pauliYOne]
    exact le_max_right _ _
  rw [ampCore_of_h_eq_zero _ rfl, charOf_eval_applyPauli, charOf_eval_ketZero,
    charOf_eval_pauliErrorPhase (one_le_pauliPrecision _ _) _ _ _ (fun _ => hm)]
  change (1 : ℂ) * (1 * _) = Complex.I
  subst hw
  simp only [yWeight_pauliYOne]
  simp [pauliYOne]

/-! ## Rows on the move -/

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he14e60db3a64
/-- **Agreement.** X on the basis state `∣0⟩` has the basis state `∣1⟩`'s amplitude: the move's
record, read by `amp`, without `amp_applyPauli`. -/
-- row: agreement
theorem amp_applyPauli_X_ketZero : amp (applyPauli pauliXOne ketZero) = amp ketOne := by
  funext w
  rw [amp_ketOne, amp_of_L_eq_zLine _ rfl, x₀_applyPauli_ketZero,
    show pauliXOne.base.X = fun _ => 1 from rfl]
  split_ifs
  · exact ampCore_applyPauli_X_ketZero w
  · rfl

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:h89f913675a15
/-- **Agreement.** Y on the basis state `∣0⟩` runs at precision `2` and has `i` times the basis
state `∣1⟩`'s amplitude (`Y = iXZ`, and `XZ∣0⟩ = ∣1⟩`). -/
-- row: agreement
theorem amp_applyPauli_Y_ketZero :
    (applyPauli pauliYOne ketZero).m = 2
      ∧ amp (applyPauli pauliYOne ketZero) = fun w => Complex.I * amp ketOne w := by
  refine ⟨?_, ?_⟩
  · change pauliPrecision 1 pauliYOne = 2
    unfold pauliPrecision
    rw [yWeight_pauliYOne]
    rfl
  · funext w
    rw [amp_ketOne, amp_of_L_eq_zLine _ rfl, x₀_applyPauli_ketZero,
      show pauliYOne.base.X = fun _ => 1 from rfl]
    split_ifs with hw
    · rw [ampCore_applyPauli_Y_ketZero w hw, mul_one]
    · rw [mul_zero]

/-- X, then Z, on `ketZero`: `−1` at the word `1`. -/
private theorem amp_applyPauli_ZX_ketZero (w : Fin 1 → ZMod 2) :
    amp (applyPauli pauliZOne (applyPauli pauliXOne ketZero)) w
      = if w = (fun _ => 1) then -1 else 0 := by
  rw [amp_of_L_eq_zLine _ rfl]
  change (if w = (0 + (fun _ => 1)) + 0 then _ else 0) = _
  rw [zero_add, add_zero]
  split_ifs with hw
  · rw [ampCore_of_h_eq_zero _ rfl, charOf_eval_applyPauli, charOf_eval_applyPauli,
      charOf_eval_ketZero,
      charOf_eval_pauliErrorPhase (one_le_pauliPrecision _ _) _ _ _
        (hodd_of_yWeight_zero _ rfl yWeight_pauliXOne),
      charOf_eval_pauliErrorPhase (one_le_pauliPrecision _ _) _ _ _
        (hodd_of_yWeight_zero _ rfl yWeight_pauliZOne)]
    change (1 : ℂ) * ((1 * _) * _) = -1
    subst hw
    simp only [yWeight_pauliXOne, yWeight_pauliZOne]
    simp [pauliXOne, pauliZOne]
  · rfl

/-- Z, then X, on `ketZero`: `1` at the word `1`. -/
private theorem amp_applyPauli_XZ_ketZero (w : Fin 1 → ZMod 2) :
    amp (applyPauli pauliXOne (applyPauli pauliZOne ketZero)) w
      = if w = (fun _ => 1) then 1 else 0 := by
  rw [amp_of_L_eq_zLine _ rfl]
  change (if w = (0 + 0) + (fun _ => 1) then _ else 0) = _
  rw [zero_add, zero_add]
  split_ifs with hw
  · rw [ampCore_of_h_eq_zero _ rfl, charOf_eval_applyPauli, charOf_eval_applyPauli,
      charOf_eval_ketZero,
      charOf_eval_pauliErrorPhase (one_le_pauliPrecision _ _) _ _ _
        (hodd_of_yWeight_zero _ rfl yWeight_pauliZOne),
      charOf_eval_pauliErrorPhase (one_le_pauliPrecision _ _) _ _ _
        (hodd_of_yWeight_zero _ rfl yWeight_pauliXOne)]
    change (1 : ℂ) * ((1 * _) * _) = 1
    subst hw
    simp only [yWeight_pauliXOne, yWeight_pauliZOne]
    simp [pauliXOne, pauliZOne, one_add_one_pauliError]
  · rfl

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h3a1c2baec0fa
/-- **Discriminating (`O1`).** X then Z, against Z then X, on the basis state `∣0⟩`: the two moves
differ by a sign, `−1` against `1` at the word `1`, so the order of application matters and the
composite is not the same element whichever way it is multiplied. -/
-- row: discriminating O1
theorem applyPauli_order_matters_ketZero :
    amp (applyPauli pauliZOne (applyPauli pauliXOne ketZero))
        = (fun w => -amp (applyPauli pauliXOne (applyPauli pauliZOne ketZero)) w)
      ∧ amp (applyPauli pauliZOne (applyPauli pauliXOne ketZero))
        ≠ amp (applyPauli pauliXOne (applyPauli pauliZOne ketZero)) := by
  refine ⟨?_, ?_⟩
  · funext w
    rw [amp_applyPauli_ZX_ketZero, amp_applyPauli_XZ_ketZero]
    split_ifs <;> simp
  · intro h
    have h1 := congrFun h (fun _ => 1)
    rw [amp_applyPauli_ZX_ketZero, amp_applyPauli_XZ_ketZero, if_pos rfl, if_pos rfl] at h1
    norm_num at h1

/-! ## Rows on protocols -/

/-- A Pauli without X-part has no Y. -/
private theorem yWeight_of_X_eq_zero {n : ℕ} (p : Pauli n) (h : p.X = 0) : yWeight p = 0 := by
  simp [yWeight, zDot, h]

/-- Z on the data bit, sign `+`, before any outcome bit. -/
def zCondFirst : SignedPauli (1 + 0) := ⟨0, ⟨0, fun _ => 1⟩⟩

/-- Z on the data bit, sign `+`, after one outcome bit. -/
def zCondSecond : SignedPauli 2 := ⟨0, ⟨0, Pi.single (Fin.castAdd 1 0) 1⟩⟩

/-- Neither conditioning has Y, so precision `1` suffices for each. -/
private theorem hP_zCondFirst : yWeight zCondFirst.pauli % 2 = 1 → 2 ≤ 1 := by
  rw [yWeight_of_X_eq_zero _ rfl]
  intro h
  exact absurd h (by decide)

private theorem hP_zCondSecond : yWeight zCondSecond.pauli % 2 = 1 → 2 ≤ 1 := by
  rw [yWeight_of_X_eq_zero _ rfl]
  intro h
  exact absurd h (by decide)

/-- The first Z-conditioning, as a protocol. -/
noncomputable def zFirstProtocol : Protocol 1 1 1 := Protocol.nil.condition zCondFirst hP_zCondFirst

/-- The second Z-conditioning, as a protocol on the two free bits the first ends on. -/
noncomputable def zSecondProtocol : Protocol 1 (1 + 1) 1 :=
  Protocol.nil.condition zCondSecond hP_zCondSecond

/-- The two-letter protocol: the two Z-conditionings, one after the other. -/
noncomputable def zTwoLetterProtocol : Protocol 1 1 2 :=
  (Protocol.nil.condition zCondFirst hP_zCondFirst).condition zCondSecond hP_zCondSecond

/-- **Agreement.** The second Z-conditioning appended to the first is the two-letter protocol: the
two interpretations are the same state, on every input, without `interpret_append`. -/
-- row: agreement
theorem interpret_append_zConditionings (S : KernelSumState 1) :
    (zFirstProtocol.append zSecondProtocol).interpret S = zTwoLetterProtocol.interpret S :=
  rfl

/-- `⟨Z⟩` is isotropic. -/
private theorem isStabilizer_zLine : IsStabilizer zLine := by
  intro p hp q hq
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
  rw [omega_smul_left, omega_smul_right, omega_self]
  simp

/-- `⟨Z⟩` is co-isotropic: a Pauli orthogonal to Z has no X-part, so it is a multiple of Z. -/
private theorem zLine_coisotropic : LinearMap.BilinForm.orthogonal omegaBilin zLine ≤ zLine := by
  intro q hq
  have h : omega zGenOne q = 0 := hq zGenOne (Submodule.mem_span_singleton_self _)
  have hcalc : omega zGenOne q = q.X 0 := by
    unfold omega zGenOne
    simp
  rw [hcalc] at h
  have hqX : q.X = 0 := by funext i; fin_cases i; exact h
  change q ∈ Submodule.span (ZMod 2) ({zGenOne} : Set (Pauli 1))
  rw [Submodule.mem_span_singleton]
  refine ⟨q.Z 0, Pauli.ext ?_ ?_⟩
  · rw [hqX]
    funext i
    fin_cases i
    change q.Z 0 • (0 : ZMod 2) = 0
    rw [smul_zero]
  · funext i
    fin_cases i
    change q.Z 0 • (1 : ZMod 2) = q.Z 0
    rw [smul_eq_mul, mul_one]

/-- `ketZero` is a carrier state. -/
private theorem isCarrier_ketZero : IsCarrier ketZero := by
  refine ⟨le_rfl, isStabilizer_zLine, zLine_coisotropic, ?_⟩
  intro h
  have h0 := congrFun h 0
  have hx : (0 : Fin 1 → ZMod 2) = ketZero.x₀ := rfl
  rw [amp_of_L_eq_zLine ketZero rfl, if_pos hx,
    ampCore_of_h_eq_zero ketZero rfl, charOf_eval_ketZero, mul_one] at h0
  exact one_ne_zero h0

/-- X on the last of two bits, as a Pauli group element. -/
private noncomputable def xLastTwo : PauliGroup (1 + (0 + 1)) := ⟨0, paulix (Fin.last (1 + 0))⟩

/-- The gate word of X on the last bit: the diagonal letter of the trivial Z-part and phase, then
H, the sign, H on the last bit. -/
private theorem pauliWord_xLastTwo :
    (pauliWord xLastTwo : GateWord (1 + (0 + 1)) 1)
      = [GateLetter.diagonal (pauliErrorPhase 1 id xLastTwo 0),
        GateLetter.hadamard (Fin.last 1),
        GateLetter.diagonal (MvPolynomial.C ((2 : ZMod (2 ^ 1)) ^ (1 - 1))
          * MvPolynomial.X (Fin.last 1)),
        GateLetter.hadamard (Fin.last 1)] :=
  rfl

/-- A Pauli without Z-part has no Y. -/
private theorem yWeight_of_Z_eq_zero {n : ℕ} (p : Pauli n) (h : p.Z = 0) : yWeight p = 0 := by
  simp [yWeight, zDot, h]

/-- The run of X's word on the last bit translates the last bit, on every amplitude function. -/
private theorem runAmp_pauliWord_xLastTwo (f : (Fin (1 + (0 + 1)) → ZMod 2) → ℂ) :
    runAmp (pauliWord xLastTwo : GateWord (1 + (0 + 1)) 1) f
      = fun v => f (v + Pi.single (Fin.last 1) 1) := by
  rw [pauliWord_xLastTwo, runAmp_cons]
  have hfirst : letterAmp (GateLetter.diagonal (pauliErrorPhase 1 id xLastTwo 0)) f = f := by
    funext v
    change charOf 1 ((pauliErrorPhase 1 id xLastTwo 0).eval v) * f v = f v
    rw [charOf_eval_pauliErrorPhase le_rfl id xLastTwo 0
      (hodd_of_yWeight_zero _ rfl (yWeight_of_Z_eq_zero _ rfl)) v,
      yWeight_of_Z_eq_zero _ rfl]
    simp [xLastTwo, paulix]
  rw [hfirst, runAmp_hadamard_sandwich (Fin.last 1) _ (fun _ => 1) ?_ (fun _ _ => rfl) f]
  · rfl
  · intro v
    rw [DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, ZMod.val_one, one_mul,
      charOf_two_pow_mul le_rfl]

/-- The Z-conditioning of `ketZero` keeps the state on outcome `0`: amplitude `1` at `(0, 0)` and
`0` at `(0, 1)`. -/
private theorem amp_zCondition_ketZero :
    amp ((Protocol.nil.condition zCondFirst hP_zCondFirst).interpret ketZero) ![0, 0] = 1
      ∧ amp ((Protocol.nil.condition zCondFirst hP_zCondFirst).interpret ketZero) ![0, 1] = 0 := by
  rw [(amp_interpret (Protocol.nil.condition zCondFirst hP_zCondFirst) isCarrier_ketZero
    rfl).2]
  have hz : ∀ b : ZMod 2, Protocol.interpretAmp (Protocol.nil.condition zCondFirst hP_zCondFirst)
      (amp ketZero) (Fin.snoc (0 : Fin 1 → ZMod 2) b : Fin 2 → ZMod 2)
      = (1 / 2 : ℂ) * (1 + (-1) ^ b.val) := by
    intro b
    have h0 : amp ketZero 0 = 1 := by
      have hx : (0 : Fin 1 → ZMod 2) = ketZero.x₀ := rfl
      rw [amp_of_L_eq_zLine ketZero rfl, if_pos hx, ampCore_of_h_eq_zero ketZero rfl,
        charOf_eval_ketZero, mul_one]
      rfl
    change (1 / 2 : ℂ)
        * (amp ketZero (Fin.init (Fin.snoc (0 : Fin 1 → ZMod 2) b : Fin 2 → ZMod 2))
          + (-1) ^ ((Fin.snoc (0 : Fin 1 → ZMod 2) b : Fin 2 → ZMod 2) (Fin.last 1)).val
            * zCondFirst.act (amp ketZero)
              (Fin.init (Fin.snoc (0 : Fin 1 → ZMod 2) b : Fin 2 → ZMod 2))) = _
    rw [Fin.init_snoc, Fin.snoc_last]
    unfold SignedPauli.act pauliAct
    rw [yWeight_of_X_eq_zero _ rfl]
    simp [zCondFirst, zDot, h0]
  refine ⟨?_, ?_⟩
  · have hv : (![0, 0] : Fin (1 + (0 + 1)) → ZMod 2) = Fin.snoc (0 : Fin 1 → ZMod 2) 0 := by
      funext i
      fin_cases i <;> rfl
    rw [hv, hz]
    norm_num
  · have hv : (![0, 1] : Fin (1 + (0 + 1)) → ZMod 2) = Fin.snoc (0 : Fin 1 → ZMod 2) 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hv, hz]
    norm_num

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- **Agreement.** A measurement error after a Z-conditioning of `∣0⟩`: the faulty protocol's
amplitude at `(w, b)` is the conditioned state's at `(w, b + 1)`, computed from the word's letters
without `interpret_insertAt`; so the state, on outcome `0` without the error (`1` at `(0, 0)`, `0`
at `(0, 1)`), is on outcome `1` with it. -/
-- row: agreement
theorem amp_measurementError_ketZero :
    (∀ v : Fin (1 + (0 + 1)) → ZMod 2,
      amp ((Protocol.measurementError Protocol.nil zCondFirst hP_zCondFirst).interpret ketZero) v
        = amp ((Protocol.nil.condition zCondFirst hP_zCondFirst).interpret ketZero)
            (v + Pi.single (Fin.last 1) 1))
      ∧ amp ((Protocol.measurementError Protocol.nil zCondFirst hP_zCondFirst).interpret ketZero)
          ![0, 0] = 0
      ∧ amp ((Protocol.measurementError Protocol.nil zCondFirst hP_zCondFirst).interpret ketZero)
          ![0, 1] = 1 := by
  have hrow : ∀ v : Fin (1 + (0 + 1)) → ZMod 2,
      amp ((Protocol.measurementError Protocol.nil zCondFirst hP_zCondFirst).interpret ketZero) v
        = amp ((Protocol.nil.condition zCondFirst hP_zCondFirst).interpret ketZero)
            (v + Pi.single (Fin.last 1) 1) := by
    intro v
    rw [(amp_interpret (Protocol.measurementError Protocol.nil zCondFirst hP_zCondFirst)
        isCarrier_ketZero rfl).2,
      (amp_interpret (Protocol.nil.condition zCondFirst hP_zCondFirst) isCarrier_ketZero rfl).2]
    change runAmp (pauliWord xLastTwo : GateWord (1 + (0 + 1)) 1)
      ((Protocol.nil.condition zCondFirst hP_zCondFirst).interpretAmp (amp ketZero)) v = _
    rw [runAmp_pauliWord_xLastTwo]
  refine ⟨hrow, ?_, ?_⟩
  · rw [hrow]
    have hv : (![0, 0] : Fin (1 + (0 + 1)) → ZMod 2) + Pi.single (Fin.last 1) 1 = ![0, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, amp_zCondition_ketZero.2]
  · rw [hrow]
    have hv : (![0, 1] : Fin (1 + (0 + 1)) → ZMod 2) + Pi.single (Fin.last 1) 1 = ![0, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, amp_zCondition_ketZero.1]

/-! ## Rows on the outcome-controlled word -/

/-- **The indicator expansion evaluates to the function**: at every word, `outcomePoly ι g` is `g`
of the bits read through `ι`. -/
private theorem eval_outcomePoly {N r k : ℕ} (ι : Fin r → Fin N)
    (g : (Fin r → ZMod 2) → ZMod (2 ^ k)) (v : Fin N → ZMod 2) :
    (outcomePoly ι g).eval v = g (fun i => v (ι i)) := by
  unfold outcomePoly
  simp only [DiagPhase.eval, map_sum, map_mul, map_prod, MvPolynomial.eval_C]
  rw [Finset.sum_eq_single (fun i => v (ι i))]
  · rw [Finset.prod_eq_one, mul_one]
    intro i _
    beta_reduce
    rcases bit_cases_pauliError (v (ι i)) with h | h
    · rw [if_neg (by rw [h]; exact zero_ne_one_pauliError)]
      simp [DiagPhase.liftBinary, h]
    · rw [if_pos h]
      simp [DiagPhase.liftBinary, h]
  · intro s _ hs
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    rcases bit_cases_pauliError (s i) with h | h <;>
      rcases bit_cases_pauliError (v (ι i)) with h' | h'
    · exact absurd (h.trans h'.symm) hi
    · rw [if_neg (by rw [h]; exact zero_ne_one_pauliError)]
      simp [DiagPhase.liftBinary, h']
    · rw [if_pos h]
      simp [DiagPhase.liftBinary, h']
    · exact absurd (h.trans h'.symm) hi
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A sum's value is the sum of the values. -/
private theorem eval_sum_pauliError {N m : ℕ} {α : Type*} (s : Finset α) (F : α → DiagPhase N m)
    (v : Fin N → ZMod 2) : (∑ a ∈ s, F a).eval v = ∑ a ∈ s, (F a).eval v :=
  map_sum (MvPolynomial.eval (DiagPhase.liftBinary v)) F s

/-- `d(s) = X^s`: X on the data bit where the outcome bit is `1`, the identity where it is `0`. -/
def outcomeX : (Fin 1 → ZMod 2) → PauliGroup 1 := fun s => ⟨0, ⟨fun _ => s 0, 0⟩⟩

/-- X on the data bit of a data bit and an outcome bit, sign `+`. -/
def xDataTwo : SignedPauli 2 := ⟨0, ⟨Pi.single (Fin.castAdd 1 0) 1, 0⟩⟩

/-- The run of `outcomePauliWord outcomeX`: translate the data bit where the outcome bit is `1`. -/
private theorem runAmp_outcomePauliWord_outcomeX (f : (Fin (1 + 1) → ZMod 2) → ℂ) :
    runAmp (outcomePauliWord outcomeX : GateWord (1 + 1) 1) f
      = fun w => if w (Fin.natAdd 1 0) = 1 then f (w + Pi.single (Fin.castAdd 1 0) 1)
          else f w := by
  unfold outcomePauliWord
  rw [runAmp_cons]
  change runAmp [GateLetter.hadamard (Fin.castAdd 1 0),
    GateLetter.diagonal (MvPolynomial.C ((2 : ZMod (2 ^ 1)) ^ (1 - 1))
      * outcomePoly (Fin.natAdd 1) (fun s => (((outcomeX s).base.X 0).val : ZMod (2 ^ 1)))
      * MvPolynomial.X (Fin.castAdd 1 0)),
    GateLetter.hadamard (Fin.castAdd 1 0)] _ = _
  have hfirst : ∀ g : (Fin (1 + 1) → ZMod 2) → ℂ, letterAmp (GateLetter.diagonal
      (MvPolynomial.C ((2 : ZMod (2 ^ 1)) ^ (1 - 1))
          * ∑ j : Fin 1, outcomePoly (Fin.natAdd 1)
              (fun s => (((outcomeX s).base.Z j).val : ZMod (2 ^ 1)))
              * MvPolynomial.X (Fin.castAdd 1 j)
        + outcomePoly (Fin.natAdd 1)
            (fun s => iPowExp 1 ((outcomeX s).phase.val + yWeight (outcomeX s).base)))) g = g := by
    intro g
    funext w
    change charOf 1 (DiagPhase.eval _ w) * g w = g w
    simp only [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, eval_sum_pauliError,
      eval_outcomePoly, DiagPhase.eval_X]
    simp [outcomeX, yWeight, zDot, iPowExp, charOf_zero]
  rw [hfirst, runAmp_hadamard_sandwich (Fin.castAdd 1 0) _ (fun w => w (Fin.natAdd 1 0)) ?_ ?_ f]
  · intro w
    rw [DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_C, eval_outcomePoly,
      DiagPhase.eval_X]
    simp only [outcomeX]
    rw [mul_assoc, ← Nat.cast_mul, charOf_two_pow_mul le_rfl]
  · intro w b
    show Function.update w (Fin.castAdd 1 0) b (Fin.natAdd 1 0) = w (Fin.natAdd 1 0)
    rw [Function.update_of_ne (show Fin.natAdd 1 (0 : Fin 1) ≠ Fin.castAdd 1 0 by decide)]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- **Agreement.** `outcomePauliWord` with `d(s) = X^s`, on one data bit and one outcome bit, has
the referee of T13's `controlledPauliWord`, X on the data bit controlled by the outcome bit, on
every amplitude function: computed from the letters, without `runAmp_outcomePauliWord`. -/
-- row: agreement
theorem runAmp_outcomePauliWord_outcomeX_eq_controlled (f : (Fin (1 + 1) → ZMod 2) → ℂ) :
    runAmp (outcomePauliWord outcomeX : GateWord (1 + 1) 1) f
      = runAmp (controlledPauliWord (Fin.natAdd 1 0) xDataTwo : GateWord (1 + 1) 1) f := by
  rw [runAmp_outcomePauliWord_outcomeX,
    runAmp_controlledPauliWord (Fin.natAdd 1 0) xDataTwo rfl le_rfl
      (by rw [yWeight_of_Z_eq_zero _ rfl]; intro h; exact absurd h (by decide)) f]
  funext w
  split_ifs
  · unfold SignedPauli.act pauliAct
    rw [yWeight_of_Z_eq_zero _ rfl]
    simp [xDataTwo, zDot]
  · rfl

/-- X on the data bit of a data bit and an outcome bit, as a register element. -/
def xDataReg : Pauli 2 := ⟨Pi.single (Fin.castAdd 1 0) 1, 0⟩

/-- Z on the data bit of a data bit and an outcome bit, as a register element. -/
def zDataReg : Pauli 2 := ⟨0, Pi.single (Fin.castAdd 1 0) 1⟩

/-- The Z-dot of `zDataReg` reads the data bit. -/
private theorem zDot_zDataReg (u : Fin 2 → ZMod 2) :
    zDot zDataReg u = (u (Fin.castAdd 1 0)).val := by
  simp [zDot, zDataReg, Fin.sum_univ_two, Pi.single_apply]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:h89f913675a15
/-- **Agreement.** `outcomePauliWord` with `d ≡ ⟨0, Y⟩` on one outcome bit runs at precision `2`
and is `i` times X after Z on the data bit, `Y = iXZ` as matrices: the phase letter carries the
factor `i^{yWeight}`, with `e = 0`. Computed from the letters, without
`runAmp_outcomePauliWord`; X after Z is `pauliAct` of X on `pauliAct` of Z. -/
-- row: agreement
theorem runAmp_outcomePauliWord_constY (f : (Fin (1 + 1) → ZMod 2) → ℂ) :
    runAmp (outcomePauliWord (fun _ => pauliYOne) : GateWord (1 + 1) 2) f
      = fun w => Complex.I * pauliAct xDataReg (pauliAct zDataReg f) w := by
  unfold outcomePauliWord
  rw [runAmp_cons]
  change runAmp [GateLetter.hadamard (Fin.castAdd 1 0),
    GateLetter.diagonal (MvPolynomial.C ((2 : ZMod (2 ^ 2)) ^ (2 - 1))
      * outcomePoly (Fin.natAdd 1) (fun _ => ((pauliYOne.base.X 0).val : ZMod (2 ^ 2)))
      * MvPolynomial.X (Fin.castAdd 1 0)),
    GateLetter.hadamard (Fin.castAdd 1 0)] _ = _
  rw [runAmp_hadamard_sandwich (Fin.castAdd 1 0) _ (fun _ => 1) ?_ (fun _ _ => rfl) _]
  · funext w
    rw [if_pos rfl]
    change charOf 2 (DiagPhase.eval _ _) * f _ = _
    simp only [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, eval_outcomePoly,
      DiagPhase.eval_X, Fin.sum_univ_one]
    rw [charOf_add, charOf_iPowExp _ (by norm_num) (fun _ => le_rfl), ← Nat.cast_mul,
      charOf_two_pow_mul (by norm_num), yWeight_pauliYOne]
    unfold pauliAct
    have hzx : zDot xDataReg (w + xDataReg.X) = 0 := by simp [zDot, xDataReg]
    rw [yWeight_of_Z_eq_zero xDataReg rfl, yWeight_of_X_eq_zero zDataReg rfl, zDot_zDataReg, hzx]
    have hX : xDataReg.X = Pi.single (Fin.castAdd 1 0) 1 := rfl
    have hZ : zDataReg.X = 0 := rfl
    rw [hX, hZ, add_zero]
    simp only [pauliYOne, ZMod.val_zero, ZMod.val_one, one_mul, zero_add, pow_zero, pow_one]
    ring
  · intro w
    rw [DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_C, eval_outcomePoly,
      DiagPhase.eval_X]
    simp only [pauliYOne, ZMod.val_one, Nat.cast_one, mul_one, one_mul]
    rw [← charOf_two_pow_mul (m := 2) (by norm_num)]

/-! ## Inhabitation -/

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h638c779e61d3
/-- **Inhabitation.** The hypotheses of `isCarrier_applyPauli` (a Pauli group element and a carrier
state) hold together on `pauliXOne` and `ketZero`: `ketZero` is a carrier state
(`isCarrier_ketZero`), so the move keeps the carrier property and the height. -/
-- row: inhabitation
example : IsCarrier (applyPauli pauliXOne ketZero) ∧ (applyPauli pauliXOne ketZero).h = ketZero.h :=
  isCarrier_applyPauli pauliXOne isCarrier_ketZero

/-! ## Axiom sweep -/

/-- info: 'FTQCLib.Cohomology.PauliGroup.act_act' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Cohomology.PauliGroup.act_act

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.bits_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.bits_eq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.brecOn.eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.brecOn.eq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.condition.inj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.condition.inj

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.condition.injEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.condition.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.condition.sizeOf_spec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.condition.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.letter.inj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.letter.inj

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.letter.injEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.letter.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.letter.sizeOf_spec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.letter.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.nil.sizeOf_spec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.nil.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.outcome.sizeOf_spec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.outcome.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.outcomes.eq_def' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.outcomes.eq_def

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.outcomes_add_rest' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.outcomes_add_rest

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.rest.eq_def' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.rest.eq_def

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.word.inj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.word.inj

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.word.injEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.word.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.Location.word.sizeOf_spec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.Location.word.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpret_append' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpret_append

/-- info: 'FTQCLib.Frame.Walkthrough.Protocol.interpret_insertAt' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Protocol.interpret_insertAt

/-- info: 'FTQCLib.Frame.Walkthrough.act_toPauliGroup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.act_toPauliGroup

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyPauli' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_applyPauli

/-- info: 'FTQCLib.Frame.Walkthrough.applyPauli_h' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.applyPauli_h

/-- info: 'FTQCLib.Frame.Walkthrough.applyPauli_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.applyPauli_m

/-- info: 'FTQCLib.Frame.Walkthrough.applyPauli_stateEq_pauliWord' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.applyPauli_stateEq_pauliWord

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_applyPauli' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_applyPauli

/-- info: 'FTQCLib.Frame.Walkthrough.le_pauliPrecision' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.le_pauliPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.one_le_pauliPrecision' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.one_le_pauliPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.runAmp_outcomePauliWord' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.runAmp_outcomePauliWord

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_castBits' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.yWeight_castBits

end FTQCLib.Frame.Walkthrough

-- mutant: pauliPrecision_odd_bound | FTQCLib/Carrier/PauliError.lean
--   | if (P.phase.val + yWeight P.base) % 2 = 0 then max m 1 else max m 2
--   | if (P.phase.val + yWeight P.base) % 2 = 0 then max m 1 else max m 3

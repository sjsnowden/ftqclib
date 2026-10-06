/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.Encoding

/-!
# Check: encoding into a signed stabilizer code

T29's witness (`docs/STEPS.md`, T29.2): rows on the frozen statement of `Codes/Encoding.lean`, on
small codes. No row uses a headline theorem of `Encoding.lean` (`encoder_exists`,
`isCarrier_encode`, `encode_isCodeState`, `encode_floor`, `encode_logical`,
`blockEncode_appendState`). An encoding's amplitude is computed from T05's amplitude theorem
(`amp_run`), the referees of the letters (`letterAmp`), `amp_castBits` and T12's `amp_pinZero`; a
Pauli move's from T64's `amp_applyPauli`; the encoder property from the letters' referees, letter by
letter.

The named small carrier states are `ketZeroEnc`, T46's unit `idState 0` on no bits with one bit
appended and held at zero by `pinZero` (the basis state `∣0⟩`, precision `1`), and `ketOneEnc`, X
applied to it by `applyPauli` (`∣1⟩`).

* **The repetition code (agreement).** On the code of `Z₀Z₁` and `Z₀Z₂` (`repCode`; the source's
  `Z₁Z₂` and `Z₁Z₃`, counting from one), the word `CNOT₀₁ CNOT₀₂` (`repWord`) is an encoder at
  every precision, and it encodes `∣0⟩` and `∣1⟩` to `∣000⟩` and `∣111⟩`.
* **The generators, not only their group (discriminating).** On the code of `Z₀Z₁` and `Z₁Z₂`,
  which has the same stabilizer group, the same word is not an encoder: it carries the second
  ancilla's `Z` to `Z₀Z₂`, which is not the second generator. `IsEncoder` reads the generators
  one by one, in order.
* **`S1`: the sign of a logical representative (discriminating).** On the code of `−Z₀Z₁`
  (`negCode`), with the encoder `CNOT₀₁` then `X₁` (`negWord`), both `Z₀` and `Z₁` represent the
  bare `Z` on the input; applied by `applyPauli`, `Z₀` acts on every encoding as `Z` on the input
  and `Z₁` as `−Z`, and the two differ on every carrier input.
* **A dependent generating set (discriminating).** `Z₀Z₁`, `Z₁Z₂`, `Z₀Z₂` commute pairwise but sum
  to zero, so no `StabCode 3 3` has them as its generators' Pauli parts.
* **Two blocks (agreement).** On a register of two blocks of the repetition code
  (`repRegister`), the blockwise encoding of two carrier inputs appended by `appendStates` has the
  amplitude of the two blocks' encodings appended, both computed without `blockEncode_appendState`.
* **The repetition code is inhabited (T29.4, inhabitation).** `repWord` is an encoder of `repCode`
  and `ketZeroEnc` is a carrier state at its precision: `encode_isCodeState`'s hypotheses hold
  together on this concrete object.

Scope (standard 7.3): every row is about the codes named above alone. The plan's row on the code of
`Z₁Z₂` and `Z₂Z₃` with the word `CNOT₁₂ CNOT₁₃` (counting from one) is stated here on the code of
`Z₁Z₂` and `Z₁Z₃`, the source's (`paragraph:table-9qubit`): with the plan's generators the word
carries `Z₃` to `Z₁Z₃`, not to `Z₂Z₃`, and the second row shows that this is not an encoder in the
sense `IsEncoder` states. The two-block row is stated for carrier inputs at a positive precision
`m`, where `appendStates`' unit `idState 0` (precision `1`) does not raise the precision.

General facts a later step may need, stated privately here: `pinZero_m_encoding` (the precision of
`pinZero` on a carrier state is the input's) belongs in `FTQCLib.Carrier.ConditionFloor`;
`isCarrier_pinZeros` (`pinZeros` keeps the carrier property and the precision) belongs in
`FTQCLib.Codes.Encoding`.
-/

namespace FTQCLib.Frame.Walkthrough

-- mutant: logicalCount_add_ancillaCount_conclusion | FTQCLib/Codes/Encoding.lean
--   | R.logicalCount + R.ancillaCount = R.totalBits | R.logicalCount = R.totalBits

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Cohomology

/-! ## Axiom sweep — every theorem of `FTQCLib.Codes.Encoding` -/

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.isStabilizer_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.isStabilizer_L

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.r_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.r_le

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.frameChi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.frameChi_zero

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.frameChi_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.frameChi_valid

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.frame_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.frame_L

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.frame_chi_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.frame_chi_gen

/-- info: 'FTQCLib.Frame.Walkthrough.encoder_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.encoder_exists

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_encode

/-- info: 'FTQCLib.Frame.Walkthrough.encode_isCodeState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.encode_isCodeState

/-- info: 'FTQCLib.Frame.Walkthrough.encode_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.encode_floor

/-- info: 'FTQCLib.Frame.Walkthrough.encode_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.encode_logical

/-- info: 'FTQCLib.Frame.Walkthrough.secondHalfBit_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.secondHalfBit_injective

/-- info: 'FTQCLib.Frame.Walkthrough.secondHalfLetter_eq_renameBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.secondHalfLetter_eq_renameBits

/-- info: 'FTQCLib.Frame.Walkthrough.Register.logicalCount_add_ancillaCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Register.logicalCount_add_ancillaCount

/-- info: 'FTQCLib.Frame.Walkthrough.Register.bit_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Register.bit_injective

/-- info: 'FTQCLib.Frame.Walkthrough.blockEncode_appendState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.blockEncode_appendState

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.commute

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.independent

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.mk.inj

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.mk.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.mk.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.clifford' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.clifford

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.ancilla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.ancilla

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.logicalX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.logicalX

/-- info: 'FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.logicalZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.StabCode.IsEncoder.logicalZ

/-- info: 'FTQCLib.Frame.Walkthrough.Register.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Register.mk.inj

/-- info: 'FTQCLib.Frame.Walkthrough.Register.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Register.mk.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.Register.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.Register.mk.sizeOf_spec

/-! ## Helpers -/

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem bit_cases_encoding (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- In `ZMod 2` a sum is zero exactly when the summands agree. -/
private theorem add_eq_zero_iff_eq_encoding (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  revert a b
  decide

/-- Two Z-type Paulis commute. -/
private theorem omega_zType_zType {n : ℕ} (a b : Fin n → ZMod 2) :
    omega (⟨0, a⟩ : Pauli n) ⟨0, b⟩ = 0 := by
  simp [omega]

/-- A Pauli with no Z-part acts by translation. -/
private theorem pauliAct_xType_encoding {n : ℕ} (x : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → ℂ)
    (w : Fin n → ZMod 2) : pauliAct (⟨x, 0⟩ : Pauli n) f w = f (w + x) := by
  simp [pauliAct, yWeight, zDot]

/-- A Pauli that commutes with every generator is in the normalizer of the span. -/
private theorem mem_normalizer_L {n r : ℕ} (C : StabCode n r) (p : Pauli n)
    (h : ∀ j, omega p (C.gen j).pauli = 0) : p ∈ normalizer C.L := by
  intro q hq
  induction hq using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact h j
  | zero => exact omega_zero_right _
  | add y z _ _ ihy ihz => rw [omega_add_right, ihy, ihz, add_zero]
  | smul a y _ ihy => rw [omega_smul_right, ihy, mul_zero]

/-- A word whose referee is a bit map `c` carries the Z-type Pauli `a` to the Z-type Pauli `b` with
the sign `s` when the two sign exponents agree at every word. -/
private theorem carriesPauli_zType {N m : ℕ} (w : GateWord N m)
    (c : (Fin N → ZMod 2) → (Fin N → ZMod 2))
    (hw : ∀ f v, runAmp w f v = f (c v)) (a b : Fin N → ZMod 2) (s : ZMod 2)
    (hs : ∀ v, dotF2 a (c v) = s + dotF2 b v) :
    CarriesPauli w ⟨0, a⟩ ⟨s, ⟨0, b⟩⟩ := by
  intro f
  funext v
  change runAmp w _ v = (-1 : ℂ) ^ s.val * pauliAct ⟨0, b⟩ _ v
  rw [hw, pauliAct_zType, pauliAct_zType, hw, ← mul_assoc, ← pow_add]
  congr 1
  apply neg_one_pow_eq_of_cast_eq
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id, hs]

/-- A word whose referee is a bit map `c` carries the X-type Pauli `a` to the X-type Pauli `b`,
sign `+`, when `c` turns a translation by `b` into a translation by `a`. -/
private theorem carriesPauli_xType {N m : ℕ} (w : GateWord N m)
    (c : (Fin N → ZMod 2) → (Fin N → ZMod 2))
    (hw : ∀ f v, runAmp w f v = f (c v)) (a b : Fin N → ZMod 2)
    (hs : ∀ v, c v + a = c (v + b)) :
    CarriesPauli w ⟨a, 0⟩ ⟨0, ⟨b, 0⟩⟩ := by
  intro f
  funext v
  change runAmp w _ v = (-1 : ℂ) ^ (0 : ZMod 2).val * pauliAct ⟨b, 0⟩ _ v
  rw [hw, pauliAct_xType_encoding, pauliAct_xType_encoding, hw, ZMod.val_zero, pow_zero,
    one_mul, hs]

/-- **`pinZero` keeps the precision of a carrier state**: the conditioning on `Z` raises it to at
least `1`, which a carrier state already has, and the slice keeps it. -/
private theorem pinZero_m_encoding {N : ℕ} {S : KernelSumState N} (hS : IsCarrier S) :
    (pinZero S).m = S.m := by
  have hslice : ∀ T : KernelSumState (N + 1), (sliceZ (Fin.last N) 0 T).m = T.m := by
    intro T
    unfold sliceZ
    split <;> rfl
  have hcond : ∀ T : KernelSumState (N + 1),
      (condition T (signedZ (Fin.last N)) 0).m = conditionPrecision T.m (signedZ (Fin.last N)) := by
    intro T
    unfold condition
    split <;> rfl
  have h : (pinZero S).m = conditionPrecision (appendFreeBit S).m (signedZ (Fin.last N)) := by
    unfold pinZero
    rw [hslice, hcond]
  rw [h]
  unfold conditionPrecision
  rw [if_pos (by rw [yWeight_signedZ])]
  exact max_eq_left hS.1

/-- The cast keeps the precision. -/
private theorem castBits_m_encoding {N N' : ℕ} (h : N = N') (S : KernelSumState N) :
    (castBits h S).m = S.m := by
  subst h
  rfl

/-! ## The named carrier states -/

/-- `∣0⟩`: T46's unit `idState 0` on no bits, with one bit appended and held at zero. -/
private noncomputable def ketZeroEnc : KernelSumState 1 := pinZero (idState 0)

/-- `∣1⟩`: X applied to `∣0⟩` by `applyPauli`. -/
private noncomputable def ketOneEnc : KernelSumState 1 :=
  applyPauli ⟨0, ⟨fun _ => 1, 0⟩⟩ ketZeroEnc

private theorem isCarrier_ketZeroEnc : IsCarrier ketZeroEnc :=
  isCarrier_pinZero (isCarrier_idState 0)

private theorem ketZeroEnc_m : ketZeroEnc.m = 1 := pinZero_m_encoding (isCarrier_idState 0)

/-- `∣0⟩`'s amplitude: `1` at the word `0`, `0` at the word `1`. -/
private theorem amp_ketZeroEnc (u : Fin 1 → ZMod 2) :
    amp ketZeroEnc u = if u = (fun _ => 0) then 1 else 0 := by
  rw [ketZeroEnc, amp_pinZero (isCarrier_idState 0), amp_idState]
  have hsub : ∀ w : Fin (0 + 0) → ZMod 2, w ∘ Fin.castAdd 0 = w ∘ Fin.natAdd 0 := by
    intro w
    funext i
    exact i.elim0
  simp only [hsub, if_true]
  have hiff : u (Fin.last 0) = 0 ↔ u = fun _ => 0 := by
    constructor
    · intro h
      funext i
      fin_cases i
      exact h
    · intro h
      rw [h]
  simp only [hiff]

private theorem isCarrier_ketOneEnc : IsCarrier ketOneEnc :=
  (isCarrier_applyPauli _ isCarrier_ketZeroEnc).1

private theorem ketOneEnc_m : ketOneEnc.m = 1 := by
  unfold ketOneEnc applyPauli
  dsimp only
  rw [ketZeroEnc_m]
  unfold pauliPrecision
  rw [if_pos (by simp [yWeight, zDot])]
  rfl

/-- `∣1⟩`'s amplitude: `1` at the word `1`, `0` at the word `0`. -/
private theorem amp_ketOneEnc (u : Fin 1 → ZMod 2) :
    amp ketOneEnc u = if u = (fun _ => 1) then 1 else 0 := by
  rw [ketOneEnc, amp_applyPauli]
  change Complex.I ^ (0 : ZMod 4).val * pauliAct ⟨fun _ => 1, 0⟩ (amp ketZeroEnc) u = _
  rw [ZMod.val_zero, pow_zero, one_mul, pauliAct_xType_encoding, amp_ketZeroEnc]
  have hiff : u + (fun _ => 1) = (fun _ => 0) ↔ u = fun _ => 1 := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      simp only [Pi.add_apply] at hi
      exact (add_eq_zero_iff_eq_encoding _ _).mp hi
    · intro h
      rw [h]
      funext i
      rfl
  simp only [hiff]

/-! ## The repetition code -/

/-- The Pauli parts of the repetition code's generators, `Z₀Z₁` and `Z₀Z₂`. -/
private def repZ : Fin 2 → Pauli 3 := ![⟨0, ![1, 1, 0]⟩, ⟨0, ![1, 0, 1]⟩]

private theorem repZ_independent : LinearIndependent (ZMod 2) repZ := by
  refine LinearIndependent.pair_iff.mpr ?_
  intro s t h
  have h1 := congrArg (fun p : Pauli 3 => p.Z 1) h
  have h2 := congrArg (fun p : Pauli 3 => p.Z 2) h
  change s * 1 + t * 0 = 0 at h1
  change s * 0 + t * 1 = 0 at h2
  simp only [mul_one, mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:table-9qubit
/-- **The repetition code** on three bits: the generators `Z₀Z₁` and `Z₀Z₂`, sign `+`, the
source's `M₁` and `M₂` restricted to the first block of three. -/
private noncomputable def repCode : StabCode 3 2 where
  gen j := ⟨0, repZ j⟩
  commute i j := by
    fin_cases i <;> fin_cases j <;> exact omega_zType_zType _ _
  independent := repZ_independent

/-- `CNOT₀₁` then `CNOT₀₂`. -/
private def repWord {m : ℕ} : GateWord 3 m :=
  [GateLetter.cnot 0 1 (by decide), GateLetter.cnot 0 2 (by decide)]

/-- The referee of `repWord`: read the word at `(v₀, v₁ + v₀, v₂ + v₀)`. -/
private theorem runAmp_repWord {m : ℕ} (f : (Fin 3 → ZMod 2) → ℂ) (v : Fin 3 → ZMod 2) :
    runAmp (repWord : GateWord 3 m) f v = f ![v 0, v 1 + v 0, v 2 + v 0] := by
  simp only [repWord, runAmp_cons, runAmp_nil, letterAmp, DiagPhase.cnotBitMap]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem repWord_clifford {m : ℕ} : ∀ g ∈ (repWord : GateWord 3 m), g.IsClifford := by
  intro g hg
  simp only [repWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> trivial

private theorem repWord_ancilla {m : ℕ} (j : Fin 2) :
    CarriesPauli (repWord : GateWord 3 m) (pauliz (repCode.ancillaBit j)) (repCode.gen j) := by
  fin_cases j
  · refine carriesPauli_zType _ _ runAmp_repWord _ _ _ fun v => ?_
    simp [dotF2, Fin.sum_univ_three, Pi.single_apply, repCode, StabCode.ancillaBit]
    exact add_comm _ _
  · refine carriesPauli_zType _ _ runAmp_repWord _ _ _ fun v => ?_
    simp [dotF2, Fin.sum_univ_three, Pi.single_apply, repCode, StabCode.ancillaBit]
    exact add_comm _ _

/-- `repWord` is an encoder of `repCode`: `Z₁ ↦ Z₀Z₁`, `Z₂ ↦ Z₀Z₂`, `X₀ ↦ X₀X₁X₂`, `Z₀ ↦ Z₀`. -/
private theorem repWord_isEncoder {m : ℕ} : repCode.IsEncoder (repWord : GateWord 3 m) := by
  refine ⟨repWord_clifford, repWord_ancilla, fun i => ⟨⟨0, ⟨![1, 1, 1], 0⟩⟩, ?_, ?_⟩,
    fun i => ⟨⟨0, ⟨0, ![1, 0, 0]⟩⟩, ?_, ?_⟩⟩
  · refine mem_normalizer_L _ _ fun j => ?_
    fin_cases j <;> simp [omega, Fin.sum_univ_three, repCode, repZ] <;> decide
  · refine carriesPauli_xType _ _ runAmp_repWord _ _ fun v => ?_
    fin_cases i
    funext k
    fin_cases k <;> simp [StabCode.logicalBit] <;> ring_nf <;>
      simp [show (2 : ZMod 2) = 0 from rfl]
  · refine mem_normalizer_L _ _ fun j => ?_
    fin_cases j <;> simp [omega, repCode, repZ]
  · refine carriesPauli_zType _ _ runAmp_repWord _ _ _ fun v => ?_
    fin_cases i
    simp [dotF2, Fin.sum_univ_three, Pi.single_apply, StabCode.logicalBit]

/-- The repetition code's encoding, from T05's amplitude theorem and T12's `amp_pinZero`: the
input's amplitude at `v₀` where the three bits agree, zero elsewhere. -/
private theorem amp_repEncode {m : ℕ} {S : KernelSumState 1} (hS : IsCarrier S) (hm : S.m = m)
    (v : Fin 3 → ZMod 2) :
    amp (repCode.encode (repWord : GateWord 3 m) S) v
      = if v 1 = v 0 ∧ v 2 = v 0 then amp S (fun _ => v 0) else 0 := by
  have h1 := isCarrier_pinZero hS
  have h2 := isCarrier_pinZero h1
  have hIn : IsCarrier (repCode.encodeInput S) := isCarrier_castBits _ h2
  have hmIn : (repCode.encodeInput S).m = m := by
    rw [StabCode.encodeInput, castBits_m_encoding]
    change (pinZero (pinZero S)).m = m
    rw [pinZero_m_encoding h1, pinZero_m_encoding hS, hm]
  rw [StabCode.encode, amp_run _ hIn hmIn, runAmp_repWord, StabCode.encodeInput, amp_castBits]
  change amp (pinZero (pinZero S)) _ = _
  rw [amp_pinZero h1, amp_pinZero hS]
  have hinit : Fin.init (Fin.init ![v 0, v 1 + v 0, v 2 + v 0]) = fun _ => v 0 := by
    funext i
    fin_cases i
    rfl
  have hone : Fin.init ![v 0, v 1 + v 0, v 2 + v 0] 1 = v 1 + v 0 := rfl
  simp
  rw [hinit, hone]
  simp only [add_eq_zero_iff_eq_encoding]
  by_cases ha : v 1 = v 0 <;> by_cases hb : v 2 = v 0 <;> simp [ha, hb]

/-- A word on three bits is constant `b` exactly when its bits agree with the first, which is
`b`. -/
private theorem rep_basis_iff (v : Fin 3 → ZMod 2) (b : ZMod 2) :
    ((v 1 = v 0 ∧ v 2 = v 0) ∧ (fun _ : Fin 1 => v 0) = (fun _ => b)) ↔ v = fun _ => b := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h0⟩
    have hb : v 0 = b := congrFun h0 0
    funext i
    fin_cases i
    · exact hb
    · exact h1.trans hb
    · exact h2.trans hb
  · intro h
    subst h
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The repetition code's encoding of a basis state `∣b⟩` is `∣bbb⟩`. -/
private theorem amp_repEncode_basis {S : KernelSumState 1} (hS : IsCarrier S) (hm : S.m = 1)
    (b : ZMod 2) (hb : ∀ u, amp S u = if u = (fun _ => b) then 1 else 0) :
    amp (repCode.encode (repWord : GateWord 3 1) S)
      = fun v => if v = (fun _ => b) then 1 else 0 := by
  funext v
  rw [amp_repEncode hS hm, hb]
  by_cases h1 : v 1 = v 0 ∧ v 2 = v 0
  · by_cases h2 : (fun _ : Fin 1 => v 0) = (fun _ => b)
    · rw [if_pos h1, if_pos h2, if_pos ((rep_basis_iff v b).mp ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 ((rep_basis_iff v b).mpr h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 ((rep_basis_iff v b).mpr h).1)]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h04196e6bf560
-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:hba0d3b4e9157
/-- **Agreement.** On the code of `Z₀Z₁` and `Z₀Z₂`, the word `CNOT₀₁ CNOT₀₂` is an encoder at every
precision (`Z` of each ancilla to its generator, `X₀` to `X₀X₁X₂` and `Z₀` to `Z₀`, logical
Paulis), and it encodes the basis states `∣0⟩` and `∣1⟩` to `∣000⟩` and `∣111⟩`, as the source's
blocks of three: the encodings' amplitudes, computed by T05's run, are the indicators of `000` and
`111`. -/
-- row: agreement
theorem repCode_encoder_encodes_basis {m : ℕ} :
    repCode.IsEncoder (repWord : GateWord 3 m)
      ∧ amp (repCode.encode (repWord : GateWord 3 1) ketZeroEnc)
          = (fun v => if v = (fun _ => 0) then 1 else 0)
      ∧ amp (repCode.encode (repWord : GateWord 3 1) ketOneEnc)
          = (fun v => if v = (fun _ => 1) then 1 else 0) :=
  ⟨repWord_isEncoder, amp_repEncode_basis isCarrier_ketZeroEnc ketZeroEnc_m 0 amp_ketZeroEnc,
    amp_repEncode_basis isCarrier_ketOneEnc ketOneEnc_m 1 amp_ketOneEnc⟩

/-- **Inhabitation (T29.4).** `encode_isCodeState`'s hypotheses hold together on a concrete
object: `repWord` is an encoder of `repCode`, and `ketZeroEnc` is a carrier state at `repWord`'s
precision `1`. -/
-- row: inhabitation
theorem repCode_encode_isCodeState_hypotheses_hold :
    repCode.IsEncoder (repWord : GateWord 3 1) ∧ IsCarrier ketZeroEnc ∧ ketZeroEnc.m = 1 :=
  ⟨repWord_isEncoder, isCarrier_ketZeroEnc, ketZeroEnc_m⟩

/-! ## The same group, other generators -/

/-- The Pauli parts `Z₀Z₁` and `Z₁Z₂`: the same span as `repZ`, other generators. -/
private def otherZ : Fin 2 → Pauli 3 := ![⟨0, ![1, 1, 0]⟩, ⟨0, ![0, 1, 1]⟩]

private theorem otherZ_independent : LinearIndependent (ZMod 2) otherZ := by
  refine LinearIndependent.pair_iff.mpr ?_
  intro s t h
  have h0 := congrArg (fun p : Pauli 3 => p.Z 0) h
  have h2 := congrArg (fun p : Pauli 3 => p.Z 2) h
  change s * 1 + t * 0 = 0 at h0
  change s * 0 + t * 1 = 0 at h2
  simp only [mul_one, mul_zero, add_zero, zero_add] at h0 h2
  exact ⟨h0, h2⟩

/-- The code of `Z₀Z₁` and `Z₁Z₂`, sign `+`. -/
private noncomputable def otherCode : StabCode 3 2 where
  gen j := ⟨0, otherZ j⟩
  commute i j := by
    fin_cases i <;> fin_cases j <;> exact omega_zType_zType _ _
  independent := otherZ_independent

/-- **Discriminating.** On the code of `Z₀Z₁` and `Z₁Z₂`, which has the stabilizer group of
`repCode`, the word `CNOT₀₁ CNOT₀₂` is not an encoder: it carries `Z₂` to `Z₀Z₂`, and on the
constant amplitude `1` at the word `100` the two sides are `−1` and `1`. -/
-- row: discriminating
theorem otherCode_not_isEncoder_repWord {m : ℕ} :
    ¬ otherCode.IsEncoder (repWord : GateWord 3 m) := by
  intro h
  have hc := congrFun (h.ancilla 1 (fun _ => 1)) ![1, 0, 0]
  change runAmp repWord (pauliAct ⟨0, _⟩ _) _
      = (-1 : ℂ) ^ (0 : ZMod 2).val * pauliAct ⟨0, ![0, 1, 1]⟩ _ _ at hc
  rw [runAmp_repWord, pauliAct_zType, pauliAct_zType, runAmp_repWord] at hc
  simp [dotF2, Fin.sum_univ_three, StabCode.ancillaBit, Pi.single_apply] at hc
  norm_num at hc

/-! ## `S1`: the code of `−Z₀Z₁` -/

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 equation:he6e827075ed8
/-- **H, a controlled sign, H is the controlled X**: on bit `j`, with a diagonal letter whose
character is `(−1)^{c(w)·w_j}` for a bit function `c` that does not read bit `j`, the three
letters translate by `e_j` where `c` is `1` and do nothing where it is `0`. -/
private theorem runAmp_hadamard_sandwich_encoding {N m : ℕ} (j : Fin N) (D : DiagPhase N m)
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
  have hne : (0 : ZMod 2) ≠ 1 := by decide
  have hflipOf : ∀ b : ZMod 2, w j = b → w + Pi.single j 1 = Function.update w j (b + 1) := by
    intro b hb
    funext l
    by_cases hl : l = j
    · subst hl
      simp [hb]
    · simp [hl]
  simp only [runAmp_cons, runAmp_nil, letterAmp, walshTransform, Function.update_idem,
    Function.update_self, hD, hc, hs0, hs1, ZMod.val_zero, ZMod.val_one, mul_zero, mul_one,
    pow_zero, one_mul]
  rcases bit_cases_encoding (c w) with hcw | hcw <;>
    rcases bit_cases_encoding (w j) with hwj | hwj
  · have hw : Function.update w j 0 = w := by rw [← hwj]; exact Function.update_eq_self j w
    rw [hcw, hwj, hs0, hw, if_neg hne]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    linear_combination (2 * f w) * h2
  · have hw : Function.update w j 1 = w := by rw [← hwj]; exact Function.update_eq_self j w
    rw [hcw, hwj, hs1, hw, if_neg hne]
    simp only [ZMod.val_zero, pow_zero, one_mul]
    linear_combination (2 * f w) * h2
  · have hflip : w + Pi.single j 1 = Function.update w j 1 := by
      rw [hflipOf 0 hwj, zero_add]
    rw [hcw, hwj, hs0, if_pos rfl, hflip]
    simp only [ZMod.val_one, pow_one]
    linear_combination (2 * f (Function.update w j 1)) * h2
  · have hflip : w + Pi.single j 1 = Function.update w j 0 := by
      rw [hflipOf 1 hwj]
      rfl
    rw [hcw, hwj, hs1, if_pos rfl, hflip]
    simp only [ZMod.val_one, pow_one]
    linear_combination (2 * f (Function.update w j 0)) * h2

/-- X on bit `j`: H, the Z exponent `czGate m j j`, H. -/
private theorem runAmp_xWord {N m : ℕ} (hm : 1 ≤ m) (j : Fin N) (f : (Fin N → ZMod 2) → ℂ) :
    runAmp ([GateLetter.hadamard j, GateLetter.diagonal (DiagPhase.czGate m j j),
        GateLetter.hadamard j] : GateWord N m) f = fun w => f (w + Pi.single j 1) := by
  rw [runAmp_hadamard_sandwich_encoding j _ (fun _ => 1) ?_ (fun _ _ => rfl) f]
  · rfl
  · intro w
    rw [charOf_czGate_eval hm, ZMod.val_one, one_mul]
    rcases bit_cases_encoding (w j) with h | h <;> rw [h] <;> simp

/-- The Pauli part of `−Z₀Z₁`. -/
private def negZ : Pauli 2 := ⟨0, ![1, 1]⟩

/-- **The code of `−Z₀Z₁`**: one generator, sign `−`. -/
private noncomputable def negCode : StabCode 2 1 where
  gen _ := ⟨1, negZ⟩
  commute _ _ := omega_zType_zType _ _
  independent := by
    rw [linearIndependent_unique_iff]
    intro h
    have h0 := congrArg (fun p : Pauli 2 => p.Z 0) h
    exact absurd h0 (by decide)

/-- `CNOT₀₁` then `X₁`, X written as H, the Z exponent, H. -/
private noncomputable def negWord {m : ℕ} : GateWord 2 m :=
  [GateLetter.cnot 0 1 (by decide), GateLetter.hadamard 1,
    GateLetter.diagonal (DiagPhase.czGate m 1 1), GateLetter.hadamard 1]

/-- The referee of `negWord`: read the word at `(v₀, v₁ + 1 + v₀)`. -/
private theorem runAmp_negWord {m : ℕ} (hm : 1 ≤ m) (f : (Fin 2 → ZMod 2) → ℂ)
    (v : Fin 2 → ZMod 2) : runAmp (negWord : GateWord 2 m) f v = f ![v 0, v 1 + 1 + v 0] := by
  rw [negWord, runAmp_cons, runAmp_xWord hm]
  simp only [letterAmp, DiagPhase.cnotBitMap]
  congr 1
  funext i
  fin_cases i <;> simp

/-- `negWord` is an encoder of `negCode`: `Z₁ ↦ −Z₀Z₁`, `X₀ ↦ X₀X₁`, `Z₀ ↦ Z₀`. -/
private theorem negWord_isEncoder {m : ℕ} (hm : 1 ≤ m) :
    negCode.IsEncoder (negWord : GateWord 2 m) := by
  refine ⟨?_, fun j => ?_, fun i => ⟨⟨0, ⟨![1, 1], 0⟩⟩, ?_, ?_⟩,
    fun i => ⟨⟨0, ⟨0, ![1, 0]⟩⟩, ?_, ?_⟩⟩
  · intro g hg
    simp only [negWord, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · exact DiagPhase.levelExt_czGate_le_two m 1 1
    · trivial
  · fin_cases j
    refine carriesPauli_zType _ _ (runAmp_negWord hm) _ _ _ fun v => ?_
    simp [dotF2, Pi.single_apply, StabCode.ancillaBit]
    ring
  · refine mem_normalizer_L _ _ fun j => ?_
    simp [omega, negCode, negZ]
    decide
  · refine carriesPauli_xType _ _ (runAmp_negWord hm) _ _ fun v => ?_
    fin_cases i
    funext k
    fin_cases k
    · simp [StabCode.logicalBit]
    · simp only [StabCode.logicalBit]
      simp
      ring_nf
      simp [show (3 : ZMod 2) = 1 from rfl]
  · refine mem_normalizer_L _ _ fun j => ?_
    simp [omega, negCode, negZ]
  · refine carriesPauli_zType _ _ (runAmp_negWord hm) _ _ _ fun v => ?_
    fin_cases i
    simp [dotF2, Pi.single_apply, StabCode.logicalBit]

/-- The code of `−Z₀Z₁`'s encoding, from T05's amplitude theorem and T12's `amp_pinZero`: the
input's amplitude at `v₀` where `v₁ = v₀ + 1`, zero elsewhere. -/
private theorem amp_negEncode {m : ℕ} (hm : 1 ≤ m) {S : KernelSumState 1} (hS : IsCarrier S)
    (hSm : S.m = m) (v : Fin 2 → ZMod 2) :
    amp (negCode.encode (negWord : GateWord 2 m) S) v
      = if v 1 = v 0 + 1 then amp S (fun _ => v 0) else 0 := by
  have h1 := isCarrier_pinZero hS
  have hIn : IsCarrier (negCode.encodeInput S) := isCarrier_castBits _ h1
  have hmIn : (negCode.encodeInput S).m = m := by
    rw [StabCode.encodeInput, castBits_m_encoding]
    change (pinZero S).m = m
    rw [pinZero_m_encoding hS, hSm]
  rw [StabCode.encode, amp_run _ hIn hmIn, runAmp_negWord hm, StabCode.encodeInput,
    amp_castBits]
  change amp (pinZero S) _ = _
  rw [amp_pinZero hS]
  have hinit : Fin.init ![v 0, v 1 + 1 + v 0] = fun _ => v 0 := by
    funext i
    fin_cases i
    rfl
  have hiff : v 1 + 1 + v 0 = 0 ↔ v 1 = v 0 + 1 := by
    generalize v 1 = a
    generalize v 0 = b
    revert a b
    decide
  simp
  rw [hinit]
  simp only [hiff]

/-- Z on bit `0` of two. -/
private def zFirst : Pauli 2 := ⟨0, ![1, 0]⟩

/-- Z on bit `1` of two. -/
private def zSecond : Pauli 2 := ⟨0, ![0, 1]⟩

/-- Z on the one logical bit. -/
private def zOne : Pauli (2 - 1) := ⟨0, ![1]⟩

/-- The code of `−Z₀Z₁`'s encoding map on amplitudes: `φ` at `v₀` where `v₁ = v₀ + 1`. -/
private noncomputable def negEncodeAmp (φ : (Fin (2 - 1) → ZMod 2) → ℂ) (v : Fin 2 → ZMod 2) :
    ℂ :=
  if v 1 = v 0 + 1 then φ (fun _ => v 0) else 0

/-- A Z-type Pauli applied by `applyPauli` to an encoding: its sign times the encoding. -/
private theorem amp_applyPauli_zType_negEncode {m : ℕ} (S : KernelSumState 1)
    (z v : Fin 2 → ZMod 2) :
    amp (applyPauli (PauliGroup.sec ⟨0, z⟩) (negCode.encode (negWord : GateWord 2 m) S)) v
      = (-1 : ℂ) ^ (dotF2 z v).val * amp (negCode.encode (negWord : GateWord 2 m) S) v := by
  rw [amp_applyPauli]
  change Complex.I ^ (0 : ZMod 4).val * pauliAct ⟨0, z⟩ _ v = _
  rw [ZMod.val_zero, pow_zero, one_mul, pauliAct_zType]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h4fd9476e182c
/-- **Discriminating (`S1`).** On the code of `−Z₀Z₁`, with the encoder `CNOT₀₁` then `X₁`: `Z₀`
and `Z₁` both represent the bare `Z` on the input (the encoder carries `Z ⊗ I` to `Z₀`, and
`Z₀ + Z₀ = 0` and `Z₁ + Z₀ = Z₀Z₁` are in `L`); applied by `applyPauli`, `Z₀` acts on the encoding
of every carrier input as `Z` on the input and `Z₁` as `−Z`, and the two differ. A representative
fixes its action only up to a sign. -/
-- row: discriminating S1
theorem negCode_logical_signs {m : ℕ} (hm : 1 ≤ m) {S : KernelSumState 1} (hS : IsCarrier S)
    (hSm : S.m = m) :
    negCode.IsEncoder (negWord : GateWord 2 m)
      ∧ negCode.IsLogicalRep (negWord : GateWord 2 m) zOne zFirst
      ∧ negCode.IsLogicalRep (negWord : GateWord 2 m) zOne zSecond
      ∧ amp (applyPauli (PauliGroup.sec zFirst) (negCode.encode (negWord : GateWord 2 m) S))
          = negEncodeAmp (pauliAct zOne (amp S))
      ∧ amp (applyPauli (PauliGroup.sec zSecond) (negCode.encode (negWord : GateWord 2 m) S))
          = (fun v => -negEncodeAmp (pauliAct zOne (amp S)) v)
      ∧ amp (applyPauli (PauliGroup.sec zFirst) (negCode.encode (negWord : GateWord 2 m) S))
          ≠ amp (applyPauli (PauliGroup.sec zSecond)
              (negCode.encode (negWord : GateWord 2 m) S)) := by
  have hpad : padPauli 2 zOne = zFirst := by
    refine Pauli.ext ?_ ?_ <;> funext b <;> fin_cases b <;> rfl
  have hQ : CarriesPauli (negWord : GateWord 2 m) (padPauli 2 zOne) ⟨0, zFirst⟩ := by
    rw [hpad]
    refine carriesPauli_zType _ _ (runAmp_negWord hm) _ _ _ fun v => ?_
    simp [dotF2]
  have hfirst :
      amp (applyPauli (PauliGroup.sec zFirst) (negCode.encode (negWord : GateWord 2 m) S))
        = negEncodeAmp (pauliAct zOne (amp S)) := by
    funext v
    refine (amp_applyPauli_zType_negEncode S ![1, 0] v).trans ?_
    rw [amp_negEncode hm hS hSm, negEncodeAmp]
    split_ifs
    · rw [zOne, pauliAct_zType]
      simp [dotF2]
    · rw [mul_zero]
  have hsecond :
      amp (applyPauli (PauliGroup.sec zSecond) (negCode.encode (negWord : GateWord 2 m) S))
        = (fun v => -negEncodeAmp (pauliAct zOne (amp S)) v) := by
    funext v
    refine (amp_applyPauli_zType_negEncode S ![0, 1] v).trans ?_
    rw [amp_negEncode hm hS hSm, negEncodeAmp]
    split_ifs with hv
    · rw [zOne, pauliAct_zType]
      simp [dotF2, hv]
      rcases bit_cases_encoding (v 0) with h | h <;> rw [h] <;>
        norm_num [show ZMod.val (2 : ZMod 2) = 0 from rfl]
    · rw [mul_zero, neg_zero]
  refine ⟨negWord_isEncoder hm, ⟨⟨0, zFirst⟩, hQ, ?_⟩, ⟨⟨0, zFirst⟩, hQ, ?_⟩, hfirst, hsecond,
    ?_⟩
  · have h0 : zFirst + zFirst = 0 := by
      refine Pauli.ext ?_ ?_ <;> funext b <;> fin_cases b <;> rfl
    change zFirst + zFirst ∈ negCode.L
    rw [h0]
    exact negCode.L.zero_mem
  · have h0 : zSecond + zFirst = negZ := by
      refine Pauli.ext ?_ ?_ <;> funext b <;> fin_cases b <;> rfl
    change zSecond + zFirst ∈ negCode.L
    rw [h0]
    exact Submodule.subset_span ⟨0, rfl⟩
  · obtain ⟨u, hu⟩ := Function.ne_iff.mp hS.2.2.2
    intro h
    have hv := congrFun h ![u 0, u 0 + 1]
    rw [hsecond, hfirst] at hv
    have hu' : (fun _ : Fin 1 => u 0) = u := by
      funext i
      fin_cases i
      rfl
    simp only [negEncodeAmp, zOne] at hv
    have hc : ![u 0, u 0 + 1] 1 = ![u 0, u 0 + 1] 0 + 1 := rfl
    simp only [if_pos hc] at hv
    change pauliAct ⟨0, ![1]⟩ (amp S) (fun _ => u 0)
        = -pauliAct ⟨0, ![1]⟩ (amp S) (fun _ => u 0) at hv
    rw [hu', pauliAct_zType] at hv
    have hsign : (-1 : ℂ) ^ (dotF2 ![1] u).val ≠ 0 := pow_ne_zero _ (by norm_num)
    have hzero : (-1 : ℂ) ^ (dotF2 ![1] u).val * amp S u = 0 := by linear_combination hv / 2
    exact hu ((mul_eq_zero.mp hzero).resolve_left hsign)

/-! ## A dependent generating set -/

/-- `Z₀Z₁`, `Z₁Z₂`, `Z₀Z₂`: pairwise commuting, summing to zero. -/
private def dependentZ : Fin 3 → Pauli 3 :=
  ![⟨0, ![1, 1, 0]⟩, ⟨0, ![0, 1, 1]⟩, ⟨0, ![1, 0, 1]⟩]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:he4985923b04d
/-- **Discriminating.** `Z₀Z₁`, `Z₁Z₂` and `Z₀Z₂` commute pairwise, so they generate an Abelian
group without `−1`, but they sum to zero: no `StabCode 3 3` has them as its generators' Pauli
parts, whatever the signs. A dependent generating set is refused, not read as a code with
`k = 0`. -/
-- row: discriminating
theorem dependent_not_stabCode :
    (∀ i j, omega (dependentZ i) (dependentZ j) = 0)
      ∧ ¬ ∃ C : StabCode 3 3, ∀ j, (C.gen j).pauli = dependentZ j := by
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> exact omega_zType_zType _ _
  · rintro ⟨C, hC⟩
    have hsum : ∑ j, (1 : ZMod 2) • (C.gen j).pauli = 0 := by
      simp only [hC, one_smul, Fin.sum_univ_three]
      refine Pauli.ext ?_ ?_ <;> funext k <;> fin_cases k <;> rfl
    exact one_ne_zero (Fintype.linearIndependent_iff.mp C.independent (fun _ => 1) hsum 0)

/-! ## Two blocks of the repetition code -/

/-- Two blocks, each holding the repetition code. -/
private noncomputable def repRegister : Register 2 := ⟨fun _ => 3, fun _ => 2, fun _ => repCode⟩

/-- The blockwise word of `repWord` in both blocks: each block's two CNOTs at its own bits. -/
private theorem repRegister_word_eq {m : ℕ} :
    repRegister.word (fun _ => (repWord : GateWord 3 m))
      = ([GateLetter.cnot (repRegister.bit 0 ⟨0, by decide⟩) (repRegister.bit 0 ⟨1, by decide⟩)
            (by decide),
          GateLetter.cnot (repRegister.bit 0 ⟨0, by decide⟩) (repRegister.bit 0 ⟨2, by decide⟩)
            (by decide),
          GateLetter.cnot (repRegister.bit 1 ⟨0, by decide⟩) (repRegister.bit 1 ⟨1, by decide⟩)
            (by decide),
          GateLetter.cnot (repRegister.bit 1 ⟨0, by decide⟩) (repRegister.bit 1 ⟨2, by decide⟩)
            (by decide)] : GateWord repRegister.totalBits m) :=
  rfl

/-- The referee of the blockwise word: `repWord`'s map in each block of three. -/
private theorem runAmp_repRegister {m : ℕ} (f : (Fin 6 → ZMod 2) → ℂ) (v : Fin 6 → ZMod 2) :
    runAmp (repRegister.word (fun _ => (repWord : GateWord 3 m))) f v
      = f ![v 0, v 1 + v 0, v 2 + v 0, v 3, v 4 + v 3, v 5 + v 3] := by
  rw [repRegister_word_eq]
  simp only [runAmp_cons, runAmp_nil, letterAmp, DiagPhase.cnotBitMap]
  congr 1
  funext i
  have hb : ∀ (t : Fin 2) (j : Fin 3), ((repRegister.bit t j : Fin 6) : ℕ) = 3 * t + j := by
    decide
  have h00 : @Eq (Fin 6) (repRegister.bit 0 ⟨0, by decide⟩) 0 := by decide
  have h01 : @Eq (Fin 6) (repRegister.bit 0 ⟨1, by decide⟩) 1 := by decide
  have h02 : @Eq (Fin 6) (repRegister.bit 0 ⟨2, by decide⟩) 2 := by decide
  have h10 : @Eq (Fin 6) (repRegister.bit 1 ⟨0, by decide⟩) 3 := by decide
  have h11 : @Eq (Fin 6) (repRegister.bit 1 ⟨1, by decide⟩) 4 := by decide
  have h12 : @Eq (Fin 6) (repRegister.bit 1 ⟨2, by decide⟩) 5 := by decide
  fin_cases i <;> simp [Function.update, Fin.ext_iff, hb] <;>
    (try simp only [h00, h01, h02, h10, h11, h12]) <;> rfl

/-- Two states appended by `appendStates`: the first's amplitude on the first `K` bits times the
second's on the last `K`. -/
private theorem amp_appendStates_two {K : ℕ} (F : Fin 2 → KernelSumState K)
    (w : Fin (∑ _t : Fin 2, K) → ZMod 2) :
    amp (appendStates F) w
      = amp (F 0) (fun j => w ⟨j, by simp; omega⟩)
        * amp (F 1) (fun j => w ⟨K + j, by simp; omega⟩) := by
  simp only [appendStates, amp_castBits, amp_appendState, amp_idState]
  rw [if_pos (funext fun i => Fin.elim0 i), one_mul]
  congr 1
  change amp (F 0) _ = _
  congr 1
  funext j
  apply congrArg w
  ext
  simp

private theorem isCarrier_appendStates_two {K : ℕ} {F : Fin 2 → KernelSumState K}
    (hF : ∀ t, IsCarrier (F t)) : IsCarrier (appendStates F) :=
  isCarrier_castBits _ (isCarrier_appendState (isCarrier_castBits _ (isCarrier_appendState
    (isCarrier_castBits _ (isCarrier_idState 0)) (hF _))) (hF _))

private theorem appendStates_two_m {K m : ℕ} {F : Fin 2 → KernelSumState K} (hm1 : 1 ≤ m)
    (hm : ∀ t, (F t).m = m) : (appendStates F).m = m := by
  have happ : ∀ {N N' : ℕ} (A : KernelSumState N) (B : KernelSumState N'),
      (appendState A B).m = max A.m B.m := fun _ _ => rfl
  simp only [appendStates, castBits_m_encoding, happ]
  change max (max 1 (F 0).m) (F 1).m = m
  rw [hm 0, hm 1, max_eq_right hm1, max_self]

/-- `pinZeros` keeps the carrier property and the precision. -/
private theorem isCarrier_pinZeros {N : ℕ} {S : KernelSumState N} (hS : IsCarrier S) :
    ∀ r, IsCarrier (pinZeros r S) ∧ (pinZeros r S).m = S.m
  | 0 => ⟨hS, rfl⟩
  | r + 1 => by
    obtain ⟨hc, hm⟩ := isCarrier_pinZeros hS r
    exact ⟨isCarrier_pinZero hc, (pinZero_m_encoding hc).trans hm⟩

/-- Two blocks of the repetition code, each encoding its own input: block `t`'s input amplitude
at its first bit where the block's three bits agree. -/
private noncomputable def twoBlockAmp (S : Fin 2 → KernelSumState 1) (v : Fin 6 → ZMod 2) : ℂ :=
  (if v 1 = v 0 ∧ v 2 = v 0 then amp (S 0) (fun _ => v 0) else 0)
    * (if v 4 = v 3 ∧ v 5 = v 3 then amp (S 1) (fun _ => v 3) else 0)

/-- The blocks' encodings appended, computed from each block's encoding. -/
private theorem amp_appendStates_repEncode {m : ℕ} (S : Fin 2 → KernelSumState 1)
    (hS : ∀ t, IsCarrier (S t)) (hm : ∀ t, (S t).m = m) (v : Fin 6 → ZMod 2) :
    amp (appendStates fun t => repCode.encode (repWord : GateWord 3 m) (S t)) v
      = twoBlockAmp S v := by
  rw [amp_appendStates_two, amp_repEncode (hS 0) (hm 0), amp_repEncode (hS 1) (hm 1)]
  rfl

/-- The blockwise encoding on the appended inputs, computed by T05's run of the blockwise word on
the register's input: the ancillas held at zero by `pinZero`, moved into their blocks by
`layout`. -/
private theorem amp_blockEncode_rep {m : ℕ} (S : Fin 2 → KernelSumState 1)
    (hS : ∀ t, IsCarrier (S t)) (hm1 : 1 ≤ m) (hm : ∀ t, (S t).m = m) (v : Fin 6 → ZMod 2) :
    amp (repRegister.blockEncode (fun _ => (repWord : GateWord 3 m)) (appendStates S)) v
      = twoBlockAmp S v := by
  have hX := isCarrier_appendStates_two hS
  have hXm := appendStates_two_m hm1 hm
  have hP := isCarrier_pinZeros hX repRegister.ancillaCount
  have hIn : IsCarrier (repRegister.input (appendStates S)) :=
    isCarrier_reindexFreeBits _ _ hP.1
  have hre : ∀ {N N' : ℕ} (h : N = N') (e : Fin N ≃ Fin N') (T : KernelSumState N),
      (reindexFreeBits h e T).m = T.m := by
    intro N N' h e T
    subst h
    rfl
  have hInm : (repRegister.input (appendStates S)).m = m := by
    rw [Register.input, hre]
    exact hP.2.trans hXm
  rw [Register.blockEncode, amp_run _ hIn hInm, runAmp_repRegister, Register.input,
    amp_reindexFreeBits]
  have c1 := isCarrier_pinZero hX
  have c2 := isCarrier_pinZero c1
  have c3 := isCarrier_pinZero c2
  change amp (pinZero (pinZero (pinZero (pinZero (appendStates S)))))
    (![v 0, v 1 + v 0, v 2 + v 0, v 3, v 4 + v 3, v 5 + v 3] ∘ ⇑repRegister.layout) = _
  rw [amp_pinZero c3, amp_pinZero c2, amp_pinZero c1, amp_pinZero hX]
  have hvec : ∀ x : Fin (repRegister.logicalCount + repRegister.ancillaCount),
      (![v 0, v 1 + v 0, v 2 + v 0, v 3, v 4 + v 3, v 5 + v 3] : Fin 6 → ZMod 2)
          (repRegister.layout x)
        = [v 0, v 3, v 1 + v 0, v 2 + v 0, v 4 + v 3, v 5 + v 3].getD x.val 0 := by
    intro x
    fin_cases x <;> rfl
  simp only [Fin.init, Function.comp_apply]
  rw [amp_appendStates_two]
  simp only [Fin.init, Function.comp_apply, hvec]
  simp
  simp only [add_eq_zero_iff_eq_encoding, twoBlockAmp]
  by_cases h1 : v 1 = v 0 <;> by_cases h2 : v 2 = v 0 <;> by_cases h4 : v 4 = v 3 <;>
    by_cases h5 : v 5 = v 3 <;> simp [h1, h2, h4, h5]

-- source: papers/foundations/
-- Gottesman_1997_stabilizer_codes_qec_quant-ph_9705052 paragraph:h91b92ec7d0c6
/-- **Agreement.** Two blocks of the repetition code on a product input: the blockwise encoding
of the two inputs appended by `appendStates` (its input the logical bits with the four ancillas
held at zero and moved into their blocks, its word each block's `repWord` renamed into the block)
has the amplitude of the two blocks' encodings appended, for any carrier inputs at a positive
precision. Both sides are computed, from T05's run and T46's `amp_appendState`, as the same
function. -/
-- row: agreement
theorem repRegister_blockEncode_appendStates {m : ℕ} (hm1 : 1 ≤ m)
    (S : Fin 2 → KernelSumState 1) (hS : ∀ t, IsCarrier (S t)) (hm : ∀ t, (S t).m = m) :
    StateEq (repRegister.blockEncode (fun _ => (repWord : GateWord 3 m)) (appendStates S))
      (appendStates fun t => repCode.encode (repWord : GateWord 3 m) (S t)) := by
  funext v
  exact (amp_blockEncode_rep S hS hm1 hm v).trans (amp_appendStates_repEncode S hS hm v).symm

end FTQCLib.Frame.Walkthrough

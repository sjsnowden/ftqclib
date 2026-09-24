/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.BoundElimination
import FTQCLib.Examples.CharSumGates

/-!
# Check: the elimination of the last bound bit

One qubit, one bound bit (`n = 1`, `h = 0`), on the full-shadow Lagrangian `⟨X₀⟩`.

* **Collapse** (`m = 1`): the exponent `x₀·y` — the free rule's output for the uniform state — has
  difference `x₀` along `y`, the collapse shape with `σ = e₀`, `ε = 0`. The certificate applies with
  the output Lagrangian `⟨Z₀⟩` (support `{0}`), and the two sides evaluate to `√2` at the word `0`
  and `0` at the word `1` by direct computation — the agreement rows.
* **Rotate** (`m = 2`): the exponent `y + 2·x₀·y` — the free rule's output for the `S` state — has
  difference `1 + 2·x₀`, the rotate shape with `a = 1` and `Λ = xorForm e₀ 0`. The certificate
  applies with the Lagrangian unchanged; the eliminated record's exponent is `3·x₀` and its scale
  `(1 + i)/√2`, and it evaluates to `(1 + i)/√2` at `0` and `(1 − i)/√2` at `1` — the values
  of the `KS` example in `HadamardEliminationCheck`.
* **The residual cell** (`m = 3`): the exponent `y + 4·x₀·y` — the free rule's output for the `T`
  state — has difference `1 + 4·x₀`, values `1, 5`: no `σ, ε` gives the collapse shape and no
  `a, Λ` the rotate shape, each by evaluation at the word `0` (`rw` rows, not `decide`, since
    `DiagPhase.eval` is noncomputable); the record is a value at height one, neither eliminator
  applies.

The Lagrangians are presented by constraints; the `ZMod` arithmetic is decided by the kernel after
the evaluations are rewritten. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## The one-qubit Lagrangians -/

/-- `⟨X₀⟩`: no Z-part. Its shadow is every word. -/
def lx1 : Submodule (ZMod 2) (Pauli 1) where
  carrier := {p | p.Z 0 = 0}
  zero_mem' := rfl
  add_mem' := fun hp hq => by
    simp only [Set.mem_setOf_eq, Z_add, Pi.add_apply] at *
    rw [hp, hq, add_zero]
  smul_mem' := fun c _ hp => by
    simp only [Set.mem_setOf_eq, Z_smul, Pi.smul_apply] at *
    rw [hp, smul_zero]

@[simp] theorem mem_lx1 {p : Pauli 1} : p ∈ lx1 ↔ p.Z 0 = 0 := Iff.rfl

/-- `⟨Z₀⟩`: no X-part. Its shadow is the word `0`. -/
def lz1 : Submodule (ZMod 2) (Pauli 1) where
  carrier := {p | p.X 0 = 0}
  zero_mem' := rfl
  add_mem' := fun hp hq => by
    simp only [Set.mem_setOf_eq, X_add, Pi.add_apply] at *
    rw [hp, hq, add_zero]
  smul_mem' := fun c _ hp => by
    simp only [Set.mem_setOf_eq, X_smul, Pi.smul_apply] at *
    rw [hp, smul_zero]

@[simp] theorem mem_lz1 {p : Pauli 1} : p ∈ lz1 ↔ p.X 0 = 0 := Iff.rfl

/-- Every word on one qubit is `![0]` or `![1]`. -/
theorem word_cases₁ (w : Fin 1 → ZMod 2) : w = ![0] ∨ w = ![1] := by
  rcases zmod_two_eq_zero_or_one (w 0) with h | h
  · left; funext i; fin_cases i; exact h
  · right; funext i; fin_cases i; exact h

/-- Every word is on the coset of `⟨X₀⟩` at offset `0`. -/
theorem mem_coset_lx1 (w : Fin 1 → ZMod 2) : ∃ p ∈ lx1, w = 0 + p.X :=
  ⟨⟨w, 0⟩, mem_lx1.mpr rfl, by simp⟩

/-- The coset of `⟨Z₀⟩` at offset `0` is the word `0`. -/
theorem mem_coset_lz1_iff (w : Fin 1 → ZMod 2) : (∃ p ∈ lz1, w = 0 + p.X) ↔ w = ![0] := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_lz1] at hp
    funext i
    fin_cases i
    simp [hp]
  · rintro rfl
    exact ⟨0, Submodule.zero_mem _, by simp⟩

/-! ## The bit index bookkeeping on `Fin (1 + 0 + 1)` -/

/-- The free bit of the two-variable exponent. -/
abbrev freeBit : Fin (1 + 0 + 1) := Fin.castSucc (Fin.castAdd 0 (0 : Fin 1))

/-- The bound bit of the two-variable exponent. -/
abbrev boundBit : Fin (1 + 0 + 1) := Fin.last (1 + 0)

/-- Reading the free bit of an extended word. -/
theorem snoc_append_freeBit (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) (b : ZMod 2) :
    (Fin.snoc (Fin.append w y) b : Fin (1 + 0 + 1) → ZMod 2) freeBit = w 0 := by
  rw [freeBit, Fin.snoc_castSucc, Fin.append_left]

/-- Reading the bound bit of an extended word. -/
theorem snoc_append_boundBit (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) (b : ZMod 2) :
    (Fin.snoc (Fin.append w y) b : Fin (1 + 0 + 1) → ZMod 2) boundBit = b := by
  rw [boundBit, Fin.snoc_last]

/-! ## Collapse: the uniform state's free-rule output at `m = 1` -/

/-- The exponent `x₀·y`. -/
noncomputable def qCollapse : DiagPhase (1 + 0 + 1) 1 :=
  MvPolynomial.X freeBit * MvPolynomial.X boundBit

/-- Its difference along `y` is `x₀`. -/
theorem lastDiff_qCollapse (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) :
    (lastDiff qCollapse).eval (Fin.append w y) = ((w 0).val : ZMod (2 ^ 1)) := by
  rw [lastDiff_eval]
  unfold qCollapse
  rw [eval_mul, eval_mul, eval_X, eval_X, eval_X, eval_X, snoc_append_freeBit, snoc_append_freeBit,
    snoc_append_boundBit, snoc_append_boundBit, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    show ((0 : ZMod 2).val : ℕ) = 0 by decide]
  push_cast
  ring

/-- The collapse shape holds with `σ = e₀`, `ε = 0`. -/
theorem signAffine_qCollapse : SignAffine (h := 0) qCollapse lx1 0 (Pi.single 0 1) 0 := by
  intro w _ y
  rw [lastDiff_qCollapse, dotF2_single_left, zero_add]
  simp

/-- The output support: the coset of `⟨Z₀⟩` is the input coset cut by `w₀ = 0`. -/
theorem hsupp_collapse (w : Fin 1 → ZMod 2) :
    (∃ p ∈ lz1, w = 0 + p.X) ↔ (∃ p ∈ lx1, w = 0 + p.X) ∧ 0 + dotF2 (Pi.single 0 1) w = 0 := by
  rw [mem_coset_lz1_iff, dotF2_single_left, zero_add]
  constructor
  · rintro rfl
    exact ⟨mem_coset_lx1 _, rfl⟩
  · rintro ⟨-, h0⟩
    funext i
    fin_cases i
    exact h0

/-- **The collapse certificate on the witness**: the eliminated record denotes the input's state. -/
theorem amp_elimCollapse_witness :
    amp (elimCollapse (h := 0) qCollapse 1 lz1 0)
      = amp (⟨1, 0 + 1, qCollapse, 1, lx1, 0⟩ : KernelSumState 1) :=
  amp_elimCollapse le_rfl 1 signAffine_qCollapse hsupp_collapse

/-- The frozen exponent of the collapse witness vanishes at every word. -/
theorem eval_snocFreeze_qCollapse (b : ZMod 2) (z : Fin (1 + 0) → ZMod 2) :
    (snocFreeze b qCollapse).eval z
      = ((z 0).val : ZMod (2 ^ 1)) * ((b.val : ℕ) : ZMod (2 ^ 1)) := by
  rw [snocFreeze_eval]
  unfold qCollapse
  rw [eval_mul, eval_X, eval_X, boundBit, Fin.snoc_last, freeBit, Fin.snoc_castSucc]
  rfl

/-- **Agreement, the eliminated side**: `√2` at the word `0`. -/
theorem amp_elimCollapse_witness_zero :
    amp (elimCollapse (h := 0) qCollapse 1 lz1 0) ![0] = Real.sqrt 2 := by
  rw [amp_pos ((mem_coset_lz1_iff _).mpr rfl)]
  change ampCore 1 0 (snocFreeze 0 qCollapse) ((Real.sqrt 2 : ℂ) * 1) ![0] = _
  rw [ampCore_zero, exp_realPhase_eq_charOf, eval_snocFreeze_qCollapse]
  simp [charOf_zero]

/-- **Agreement, the input side**: `√2` at the word `0`, by the peel. -/
theorem amp_input_collapse_zero :
    amp (⟨1, 0 + 1, qCollapse, 1, lx1, 0⟩ : KernelSumState 1) ![0] = Real.sqrt 2 := by
  rw [amp_pos (mem_coset_lx1 _)]
  change ampCore 1 (0 + 1) qCollapse 1 ![0] = _
  rw [ampCore_peel_last, ampCore_zero, ampCore_zero, exp_realPhase_eq_charOf,
    exp_realPhase_eq_charOf, eval_snocFreeze_qCollapse, eval_snocFreeze_qCollapse]
  simp only [Matrix.cons_val_zero, ZMod.val_zero, Nat.cast_zero, zero_mul, charOf_zero, one_mul]
  rw [show (1 : ℂ) + 1 = 2 by norm_num, one_div_sqrt_two_mul_two]

/-- **The eliminated side vanishes at the word `1`** (off the cut support). -/
theorem amp_elimCollapse_witness_one : amp (elimCollapse (h := 0) qCollapse 1 lz1 0) ![1] = 0 :=
  amp_neg (fun h => by
    have := (mem_coset_lz1_iff _).mp h
    exact absurd (congrFun this 0) (by decide))

/-! ## Rotate: the `S` state's free-rule output at `m = 2` -/

/-- The exponent `y + 2·x₀·y`. -/
noncomputable def qRotate : DiagPhase (1 + 0 + 1) 2 :=
  MvPolynomial.X boundBit + MvPolynomial.C 2 * MvPolynomial.X freeBit * MvPolynomial.X boundBit

/-- Its difference along `y` is `1 + 2·x₀`. -/
theorem lastDiff_qRotate (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) :
    (lastDiff qRotate).eval (Fin.append w y) = 1 + 2 * ((w 0).val : ZMod (2 ^ 2)) := by
  rw [lastDiff_eval]
  unfold qRotate
  rw [eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_mul, eval_C, eval_C, eval_X, eval_X,
    eval_X, eval_X, snoc_append_freeBit, snoc_append_freeBit, snoc_append_boundBit,
    snoc_append_boundBit, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    show ((0 : ZMod 2).val : ℕ) = 0 by decide]
  push_cast
  ring

/-- The rotate shape holds with `a = 1` and `Λ = xorForm e₀ 0`. -/
theorem rotateData_qRotate :
    RotateData (h := 0) qRotate lx1 0 1 (xorForm (h := 0) (m := 2) (Pi.single 0 1) 0) := by
  refine ⟨by decide, fun w _ y => ⟨w 0, ?_, ?_⟩⟩
  · rw [xorForm_eval, zero_add]
    congr 2
    unfold dotF2
    rw [Fin.sum_univ_one, Pi.single_eq_same, one_mul]
    exact Fin.append_left w y 0
  · rw [lastDiff_qRotate]
    rcases zmod_two_eq_zero_or_one (w 0) with h | h <;> rw [h] <;> decide

/-- **The rotate certificate on the witness**: the Lagrangian unchanged, the eliminated record
denotes the input's state. -/
theorem amp_elimRotate_witness :
    amp (elimRotate (h := 0) qRotate 1 (xorForm (h := 0) (m := 2) (Pi.single 0 1) 0) 1 lx1
        0)
      = amp (⟨2, 0 + 1, qRotate, 1, lx1, 0⟩ : KernelSumState 1) :=
  amp_elimRotate (by norm_num) 1 rotateData_qRotate (fun w => Iff.rfl)

/-- The eliminated exponent is `3·x₀` in value: `0 − 1·(x₀ ⊕ 0) = 3·x₀` in `ZMod 4`. -/
theorem eval_elimRotate_exponent (z : Fin (1 + 0) → ZMod 2) :
    (snocFreeze 0 qRotate
        + MvPolynomial.C (-1) * xorForm (h := 0) (m := 2) (Pi.single 0 1) 0).eval z
      = 3 * ((z 0).val : ZMod (2 ^ 2)) := by
  rw [eval_add, eval_mul, eval_C, snocFreeze_eval, xorForm_eval]
  unfold qRotate
  rw [eval_add, eval_mul, eval_mul, eval_C, eval_X, eval_X, boundBit, Fin.snoc_last, freeBit,
    Fin.snoc_castSucc]
  have hd : dotF2 (Pi.single 0 1 : Fin 1 → ZMod 2) (fun j => z (Fin.castAdd 0 j)) = z 0 := by
    unfold dotF2
    rw [Fin.sum_univ_one, Pi.single_eq_same, one_mul]
    rfl
  have hz : z (Fin.castAdd 0 0) = z 0 := rfl
  rw [hd, hz, zero_add]
  rcases zmod_two_eq_zero_or_one (z 0) with h | h <;> rw [h] <;> decide

/-- **The rotate example's value**: the eliminated record's scale times the character of `3·w₀` is
`(1 + i)/√2` at `0` and `(1 − i)/√2` at `1`, at both words. -/
theorem charOf_two_one' : charOf 2 1 = Complex.I := by
  have h := charOf_two_pow_sub_two_mul (m := 2) le_rfl 1
  simpa using h

theorem charOf_two_three' : charOf 2 3 = -Complex.I := by
  have h2 : charOf 2 2 = -1 := by
    have h := charOf_two_pow_mul (m := 2) (by norm_num) 1
    simpa using h
  rw [show (3 : ZMod (2 ^ 2)) = 1 + 2 by decide, charOf_add, charOf_two_one', h2]
  ring

theorem amp_elimRotate_witness_values :
    amp (elimRotate (h := 0) qRotate 1 (xorForm (h := 0) (m := 2) (Pi.single 0 1) 0) 1 lx1 0) ![0]
        = (1 + Complex.I) / Real.sqrt 2
      ∧ amp (elimRotate (h := 0) qRotate 1 (xorForm (h := 0) (m := 2) (Pi.single 0 1) 0) 1 lx1 0)
          ![1] = (1 - Complex.I) / Real.sqrt 2 := by
  have h0 := charOf_zero 2
  have h1 := charOf_two_one'
  have h3 := charOf_two_three'
  refine ⟨?_, ?_⟩
  · rw [amp_pos (mem_coset_lx1 _)]
    change ampCore 2 0 (snocFreeze 0 qRotate
        + MvPolynomial.C (-1) * xorForm (h := 0) (m := 2) (Pi.single 0 1) 0)
      (1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)) ![0] = _
    rw [ampCore_zero, exp_realPhase_eq_charOf, eval_elimRotate_exponent]
    simp only [Matrix.cons_val_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, h0, h1, mul_one]
    ring
  · rw [amp_pos (mem_coset_lx1 _)]
    change ampCore 2 0 (snocFreeze 0 qRotate
        + MvPolynomial.C (-1) * xorForm (h := 0) (m := 2) (Pi.single 0 1) 0)
      (1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)) ![1] = _
    rw [ampCore_zero, exp_realPhase_eq_charOf, eval_elimRotate_exponent]
    have hv : (3 : ZMod (2 ^ 2)) * (((![1] : Fin 1 → ZMod 2) 0).val : ZMod (2 ^ 2)) = 3 := by decide
    rw [hv, h3, h1]
    ring_nf
    rw [Complex.I_sq]
    ring

/-! ## The residual cell: the `T` state's free-rule output at `m = 3`, a value at height one -/

/-- The exponent `y + 4·x₀·y`. -/
noncomputable def qResidual : DiagPhase (1 + 0 + 1) 3 :=
  MvPolynomial.X boundBit + MvPolynomial.C 4 * MvPolynomial.X freeBit * MvPolynomial.X boundBit

/-- Its difference along `y` is `1 + 4·x₀`. -/
theorem lastDiff_qResidual (w : Fin 1 → ZMod 2) (y : Fin 0 → ZMod 2) :
    (lastDiff qResidual).eval (Fin.append w y) = 1 + 4 * ((w 0).val : ZMod (2 ^ 3)) := by
  rw [lastDiff_eval]
  unfold qResidual
  rw [eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_mul, eval_C, eval_C, eval_X, eval_X,
    eval_X, eval_X, snoc_append_freeBit, snoc_append_freeBit, snoc_append_boundBit,
    snoc_append_boundBit, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    show ((0 : ZMod 2).val : ℕ) = 0 by decide]
  push_cast
  ring

/-- **No collapse shape**: at the word `0` the difference is `1`, not a multiple of `4`. -/
theorem not_signAffine_qResidual : ¬ ∃ σ ε, SignAffine (h := 0) qResidual lx1 0 σ ε := by
  rintro ⟨σ, ε, h⟩
  have h0 := h ![0] (mem_coset_lx1 _) (fun i => i.elim0)
  rw [lastDiff_qResidual] at h0
  simp only [Matrix.cons_val_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at h0
  rcases zmod_two_eq_zero_or_one (ε + dotF2 σ ![0]) with hb | hb <;> rw [hb] at h0 <;>
    exact absurd h0 (by decide)

/-- **No rotate shape**: `2a = 4` and `1 = a + 4b` have no common solution in `ZMod 8`. -/
theorem not_rotateData_qResidual : ¬ ∃ a Λ, RotateData (h := 0) qResidual lx1 0 a Λ := by
  rintro ⟨a, Λ, ha, h⟩
  obtain ⟨b, -, hb⟩ := h ![0] (mem_coset_lx1 _) (fun i => i.elim0)
  rw [lastDiff_qResidual] at hb
  simp only [Matrix.cons_val_zero, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero] at hb
  have h2 : (2 : ZMod (2 ^ 3)) * 1 = 2 * a + 2 * (4 * ((b.val : ℕ) : ZMod (2 ^ 3))) := by
    rw [hb]; ring
  rw [ha] at h2
  rcases zmod_two_eq_zero_or_one b with hb0 | hb0 <;> rw [hb0] at h2 <;>
    exact absurd h2 (by decide)

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_eq_sum_charOf' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_eq_sum_charOf

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_mul_left' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_mul_left

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_peel_last' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_peel_last

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_snocFreeze_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_snocFreeze_one

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_snocFreeze_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_snocFreeze_zero

/-- info: 'FTQCLib.Frame.Walkthrough.SignAffine' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignAffine

/-- info: 'FTQCLib.Frame.Walkthrough.RotateData' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RotateData

/-- info: 'FTQCLib.Frame.Walkthrough.elimCollapse' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.elimRotate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.elimCollapse_h' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimCollapse_h

/-- info: 'FTQCLib.Frame.Walkthrough.elimRotate_h' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimRotate_h

/-- info: 'FTQCLib.Frame.Walkthrough.elimCollapse_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimCollapse_L

/-- info: 'FTQCLib.Frame.Walkthrough.elimRotate_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimRotate_L

/-- info: 'FTQCLib.Frame.Walkthrough.one_div_sqrt_two_mul_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_div_sqrt_two_mul_two

/-- info: 'FTQCLib.Frame.Walkthrough.mul_mul_sum_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_mul_sum_eq

/-- info: 'FTQCLib.Frame.Walkthrough.freeBit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms freeBit

/-- info: 'FTQCLib.Frame.Walkthrough.boundBit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms boundBit

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_snocFreeze_one_of_signAffine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_snocFreeze_one_of_signAffine

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimCollapse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_branches_of_rotateData' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_branches_of_rotateData

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimRotate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimRotate

/-- info: 'FTQCLib.Frame.Walkthrough.amp_map_zShearBy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_map_zShearBy

/-- info: 'FTQCLib.Frame.Walkthrough.amp_map_zShear' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_map_zShear

/-- info: 'FTQCLib.Frame.Walkthrough.lx1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lx1

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lx1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lx1

/-- info: 'FTQCLib.Frame.Walkthrough.lz1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lz1

/-- info: 'FTQCLib.Frame.Walkthrough.mem_lz1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_lz1

/-- info: 'FTQCLib.Frame.Walkthrough.word_cases₁' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms word_cases₁

/-- info: 'FTQCLib.Frame.Walkthrough.mem_coset_lx1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_coset_lx1

/-- info: 'FTQCLib.Frame.Walkthrough.mem_coset_lz1_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_coset_lz1_iff

/-- info: 'FTQCLib.Frame.Walkthrough.snoc_append_freeBit' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms snoc_append_freeBit

/-- info: 'FTQCLib.Frame.Walkthrough.snoc_append_boundBit' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms snoc_append_boundBit

/-- info: 'FTQCLib.Frame.Walkthrough.qCollapse' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_qCollapse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_qCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.signAffine_qCollapse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signAffine_qCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.hsupp_collapse' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hsupp_collapse

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimCollapse_witness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimCollapse_witness

/-- info: 'FTQCLib.Frame.Walkthrough.eval_snocFreeze_qCollapse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_snocFreeze_qCollapse

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimCollapse_witness_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimCollapse_witness_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_input_collapse_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_input_collapse_zero

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimCollapse_witness_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimCollapse_witness_one

/-- info: 'FTQCLib.Frame.Walkthrough.qRotate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qRotate

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_qRotate' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_qRotate

/-- info: 'FTQCLib.Frame.Walkthrough.rotateData_qRotate' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotateData_qRotate

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimRotate_witness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimRotate_witness

/-- info: 'FTQCLib.Frame.Walkthrough.eval_elimRotate_exponent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_elimRotate_exponent

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_one'' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charOf_two_one'

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_two_three'' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charOf_two_three'

/-- info: 'FTQCLib.Frame.Walkthrough.amp_elimRotate_witness_values' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimRotate_witness_values

/-- info: 'FTQCLib.Frame.Walkthrough.qResidual' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms qResidual

/-- info: 'FTQCLib.Frame.Walkthrough.lastDiff_qResidual' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lastDiff_qResidual

/-- info: 'FTQCLib.Frame.Walkthrough.not_signAffine_qResidual' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_signAffine_qResidual

/-- info: 'FTQCLib.Frame.Walkthrough.not_rotateData_qResidual' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_rotateData_qResidual

end FTQCLib.Frame.Walkthrough

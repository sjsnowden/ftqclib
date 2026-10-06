/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ProtocolSemantics

/-!
# Check: the Hilbert semantics of protocols on one data bit

T17's witness (`docs/STEPS.md`, T17.2): rows on the frozen statement of `ProtocolSemantics.lean`,
computed from the definitions of `hilbertSem` and `kraus` (through `bornProjection`,
`conditionIsometry`, `cnotGate`, `hadamardGate`) and never through `hilbertSem_isometry`,
`kraus_sum_eq_one` or `kraus_eq_prod_of_controlsOnly`, which are not yet proved.

The instance: one data bit at precision `1`, conditioned on `+Z₀` (`zPlus`), the outcome a new
free bit `1` (`zCondition`); then either a CNOT from the outcome bit to bit `0`
(`cnotFromOutcome`, row `R1`) or an H on the outcome bit (`hadamardOnOutcome`, row `H1`).

* **Empty protocol (agreement).** `⟦nil⟧` is the inclusion `φ ↦ φ ⊗ e_∅` (`appendOutcome` at the
  empty string), and its one Kraus operator is the identity matrix.
* **Z-conditioning (agreement).** `K_o` is the matrix unit `|o⟩⟨o|`, the projector onto `o`.
* **`R1` (discriminating).** Z-conditioning, then CNOT from the outcome bit to bit `0`: `K_o` is
  `|0⟩⟨o|`, so `K_0 = P₀` and `K_1 = E₀₁`, which squares to zero: not a pair of projectors.
* **`H1` (agreement).** Z-conditioning, then H on the outcome bit: `K_o = Z^o/√2`, against
  `pauliOperator (pauliz 0)`, the Hilbert side's Z.
* **`H1` (discriminating).** `OutcomeControlsOnly` fails for it, and its `K_1` differs from the
  product form `krausProduct` at the entry `(0, 0)`: `1/√2` against `0`.
* **Z-conditioning satisfies `OutcomeControlsOnly` (inhabitation).** `zCondition` conditions `nil`,
  which has no outcome bit yet, so `kraus_eq_prod_of_controlsOnly`'s hypotheses hold together for
  it, and `kraus` there is `krausProduct`.

Every row is about `hilbertSem` or `kraus` on a concrete term; the matrix units and `pauliOperator` are the existing objects the
witness rows compare `kraus` with.

T17.3 proved `hilbertSem_isometry`, `kraus_sum_eq_one` and `kraus_eq_prod_of_controlsOnly`; none is
`sorry`'d or left unproved here, and the witness rows above use only `hilbertSem`'s and `kraus`'s
own definitions, never these three theorems.
-/

namespace FTQCLib.Hilbert.ProtocolSemanticsCheck

open FTQCLib FTQCLib.Pauli FTQCLib.Hilbert FTQCLib.Frame.Walkthrough

/-! ## The instance -/

/-- `+Z₀` on one bit: sign exponent `0`, the Pauli `Z` on bit `0`. -/
def zPlus : SignedPauli 1 := ⟨0, pauliz 0⟩

/-- `+Z₀` has no Y, so it needs no precision above `1`. -/
theorem zPlus_precision : yWeight zPlus.pauli % 2 = 1 → 2 ≤ 1 := by
  intro h
  simp [zPlus, yWeight, zDot, pauliz] at h

/-- **Z-conditioning on one data bit**: condition on `+Z₀`, the outcome a new free bit `1`. -/
def zCondition : Protocol 1 1 1 :=
  (Protocol.nil : Protocol 1 1 0).condition zPlus zPlus_precision

/-- **Row `R1`'s term**: Z-conditioning, then CNOT with control the outcome bit `1` and target
the data bit `0`. -/
def cnotFromOutcome : Protocol 1 1 1 :=
  zCondition.word [.cnot (Fin.last 1) 0 (by decide)]

/-- **Row `H1`'s term**: Z-conditioning, then H on the outcome bit `1`. -/
def hadamardOnOutcome : Protocol 1 1 1 :=
  zCondition.word [.hadamard (Fin.last 1)]

/-- The one-bit word with value `b`. -/
def bit (b : ZMod 2) : Fin 1 → ZMod 2 := fun _ => b

/-! ## Private computations -/

private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

private theorem word_one_eq_bit (y : Fin 1 → ZMod 2) : y = bit (y 0) := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

private theorem bit_inj {a b : ZMod 2} : bit a = bit b ↔ a = b :=
  ⟨fun h => congrFun h 0, fun h => h ▸ rfl⟩

private theorem appendOutcome_apply (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) (φ : QubitSpace N)
    (v : Fin (N + k) → ZMod 2) :
    appendOutcome N o φ v = if v ∘ Fin.natAdd N = o then φ (v ∘ Fin.castAdd k) else 0 :=
  rfl

/-- The Born projector of `+Z₀` at `b` keeps the words whose bit is `b`. -/
private theorem bornProjection_zPlus_apply (b : ZMod 2) (ψ : QubitSpace 1)
    (v : Fin 1 → ZMod 2) :
    bornProjection (N := 1 + 0) zPlus b ψ v = if v 0 = b then ψ v else 0 := by
  simp only [bornProjection, LinearMap.comp_apply, LinearEquiv.coe_coe, toQState_symm_apply,
    bornProjector, LinearMap.smul_apply, PiLp.smul_apply, LinearMap.add_apply, PiLp.add_apply,
    LinearMap.id_apply, pauliHermitian_apply_fun, toQState_apply, smul_eq_mul]
  have hX : zPlus.pauli.X = 0 := rfl
  have hw : xzWeight zPlus.pauli = 0 := by
    simp [xzWeight, zDotVal, zPlus, pauliz]
  rw [hX, sub_zero, hw, show zPlus.pauli = pauliz 0 from rfl, zDotVal_pauliz,
    show zPlus.sign = 0 from rfl]
  rcases zmod2_cases b with rfl | rfl <;> rcases zmod2_cases (v 0) with h | h <;>
    simp [h] <;> ring

/-- `⟦zCondition⟧` at a two-bit word `w`: the input at bit `0` when the outcome bit agrees. -/
private theorem hilbertSem_zCondition_apply (ψ : QubitSpace 1) (w : Fin (1 + 1) → ZMod 2) :
    hilbertSem zCondition ψ w = if w 1 = w 0 then ψ (bit (w 0)) else 0 := by
  simp only [zCondition, hilbertSem_condition, hilbertSem_nil, LinearMap.comp_id,
    conditionIsometry, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  rw [sum_zmod2]
  simp only [appendOutcome_apply, bornProjection_zPlus_apply]
  have hc : w ∘ Fin.castAdd 1 = bit (w 0) := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  have hn : ∀ b : ZMod 2, (w ∘ Fin.natAdd 1 = fun _ : Fin 1 => b) ↔ w 1 = b := by
    intro b
    constructor
    · intro h
      exact congrFun h 0
    · intro h
      funext i
      rw [Subsingleton.elim i 0]
      exact h
  rw [hc]
  simp only [hn]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    simp [h0, h1, bit]

/-- A Kraus entry is `⟦p⟧` on a basis vector, evaluated at the data word and the outcome string. -/
private theorem kraus_apply {m n k : ℕ} (p : Protocol m n k) (o : Fin k → ZMod 2)
    (y x : Fin n → ZMod 2) :
    kraus p o y x = hilbertSem p (Pi.single x 1) (Fin.append y o) := by
  rw [kraus, LinearMap.toMatrix'_apply]
  rfl

private theorem append_bit_zero (a c : ZMod 2) : Fin.append (bit a) (bit c) (0 : Fin (1 + 1)) = a :=
  Fin.append_left (bit a) (bit c) 0

private theorem append_bit_one (a c : ZMod 2) : Fin.append (bit a) (bit c) (1 : Fin (1 + 1)) = c :=
  Fin.append_right (bit a) (bit c) 0

private theorem single_bit_apply (a b : ZMod 2) :
    (Pi.single (bit b) (1 : ℂ) : QubitSpace 1) (bit a) = if a = b then 1 else 0 := by
  rw [Pi.single_apply]
  simp only [bit_inj]

private theorem matrix_single_bit_apply (a b c d : ZMod 2) :
    Matrix.single (bit a) (bit b) (1 : ℂ) (bit c) (bit d) = if a = c ∧ b = d then 1 else 0 := by
  simp only [Matrix.single, Matrix.of_apply, bit_inj]

private theorem invSqrt2_ne_zero : invSqrt2 ≠ 0 := by
  rw [invSqrt2, Complex.ofReal_ne_zero]
  exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))

/-! ## Rows -/

-- row: agreement
/-- **The empty protocol is the inclusion.** `⟦nil⟧` is `φ ↦ φ ⊗ e_∅`, the existing
`appendOutcome` at the empty outcome string, on any number of data bits at any precision. -/
theorem hilbertSem_nil_eq_appendOutcome (m n : ℕ) :
    hilbertSem (.nil : Protocol m n 0) = appendOutcome n (Fin.elim0 : Fin 0 → ZMod 2) := by
  refine LinearMap.ext fun ψ => funext fun v => ?_
  rw [appendOutcome_apply, if_pos (funext fun i => Fin.elim0 i)]
  rfl

-- row: agreement
/-- **The empty protocol's one Kraus operator is the identity matrix.** -/
theorem kraus_nil_eq_one (m n : ℕ) :
    kraus (.nil : Protocol m n 0) Fin.elim0 = 1 := by
  ext y x
  have hy : Fin.append y (Fin.elim0 : Fin 0 → ZMod 2) = y := by
    funext i
    exact Fin.append_left y Fin.elim0 i
  rw [kraus_apply, Matrix.one_apply, hilbertSem_nil, LinearMap.id_apply, hy, Pi.single_apply]

-- row: agreement
/-- **Z-conditioning on one bit has Kraus `P₀`, `P₁`.** At the outcome `o`, `K_o` is the matrix
unit `|o⟩⟨o|`, the projector onto the basis word `o`. -/
theorem kraus_zCondition (o : Fin 1 → ZMod 2) : kraus zCondition o = Matrix.single o o 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, o = bit c := ⟨o 0, word_one_eq_bit o⟩
  ext y x
  obtain ⟨a, rfl⟩ : ∃ a, y = bit a := ⟨y 0, word_one_eq_bit y⟩
  obtain ⟨b, rfl⟩ : ∃ b, x = bit b := ⟨x 0, word_one_eq_bit x⟩
  rw [kraus_apply, hilbertSem_zCondition_apply, append_bit_zero, append_bit_one,
    single_bit_apply, matrix_single_bit_apply]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;> simp

/-- `⟦cnotFromOutcome⟧` at `w` is `⟦zCondition⟧` at the CNOT-permuted word. -/
private theorem hilbertSem_cnotFromOutcome_apply (ψ : QubitSpace 1) (w : Fin (1 + 1) → ZMod 2) :
    hilbertSem cnotFromOutcome ψ w = if w 0 = 0 then ψ (bit (w 0 + w 1)) else 0 := by
  simp only [cnotFromOutcome, hilbertSem_word, LinearMap.comp_apply, wordGate, letterGate,
    LinearMap.id_comp, LinearEquiv.coe_coe, cnotGate_apply]
  rw [hilbertSem_zCondition_apply]
  have hl : (Fin.last 1 : Fin (1 + 1)) = 1 := rfl
  have h10 : (1 : Fin (1 + 1)) ≠ 0 := by decide
  simp only [cnotPerm, Function.update_apply, hl, h10, if_false, if_true]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    simp [h0, h1]

/-- `⟦hadamardOnOutcome⟧` at `w`: `(1/√2)(−1)^{w₁ w₀}` times the input at bit `0`. -/
private theorem hilbertSem_hadamardOnOutcome_apply (ψ : QubitSpace 1)
    (w : Fin (1 + 1) → ZMod 2) :
    hilbertSem hadamardOnOutcome ψ w =
      invSqrt2 * ((-1 : ℂ) ^ ((w 1).val * (w 0).val) * ψ (bit (w 0))) := by
  simp only [hadamardOnOutcome, hilbertSem_word, LinearMap.comp_apply, wordGate, letterGate,
    LinearMap.id_comp, hadamardGate_apply]
  rw [sum_zmod2]
  have hl : (Fin.last 1 : Fin (1 + 1)) = 1 := rfl
  have h01 : (0 : Fin (1 + 1)) ≠ 1 := by decide
  simp only [hilbertSem_zCondition_apply, Function.update_apply, hl, h01, if_false, if_true]
  rcases zmod2_cases (w 0) with h0 | h0 <;> rcases zmod2_cases (w 1) with h1 | h1 <;>
    simp [h0, h1]

/-- `R1`'s Kraus operators: `K_o = |0⟩⟨o|`. -/
private theorem kraus_cnotFromOutcome (o : Fin 1 → ZMod 2) :
    kraus cnotFromOutcome o = Matrix.single (bit 0) o 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, o = bit c := ⟨o 0, word_one_eq_bit o⟩
  ext y x
  obtain ⟨a, rfl⟩ : ∃ a, y = bit a := ⟨y 0, word_one_eq_bit y⟩
  obtain ⟨b, rfl⟩ : ∃ b, x = bit b := ⟨x 0, word_one_eq_bit x⟩
  rw [kraus_apply, hilbertSem_cnotFromOutcome_apply, append_bit_zero, append_bit_one,
    matrix_single_bit_apply]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;> simp [single_bit_apply]

-- row: discriminating R1
/-- **`R1`.** Z-conditioning, then CNOT from the outcome bit to bit `0`: `K_0 = P₀` and
`K_1 = E₀₁`, the matrix unit sending `1` to `0`, which squares to zero. So `K_1` is not a
projector, and it differs from the Z-conditioning's `K_1 = P₁`: the feed-forward word acts on
the Kraus family, which is not a pair of projectors. -/
theorem kraus_cnotFromOutcome_not_projectors :
    kraus cnotFromOutcome (bit 0) = Matrix.single (bit 0) (bit 0) 1 ∧
      kraus cnotFromOutcome (bit 1) = Matrix.single (bit 0) (bit 1) 1 ∧
      kraus cnotFromOutcome (bit 1) * kraus cnotFromOutcome (bit 1) ≠
        kraus cnotFromOutcome (bit 1) ∧
      kraus cnotFromOutcome (bit 1) ≠ kraus zCondition (bit 1) := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  refine ⟨kraus_cnotFromOutcome _, kraus_cnotFromOutcome _, ?_, ?_⟩
  · rw [kraus_cnotFromOutcome]
    intro h
    have h' := congrFun (congrFun h (bit 0)) (bit 1)
    rw [Matrix.mul_apply, Matrix.single_apply_same, Finset.sum_eq_zero] at h'
    · exact zero_ne_one h'
    · intro z _
      obtain ⟨d, rfl⟩ : ∃ d, z = bit d := ⟨z 0, word_one_eq_bit z⟩
      rw [matrix_single_bit_apply, matrix_single_bit_apply]
      rcases zmod2_cases d with rfl | rfl <;> simp
  · rw [kraus_cnotFromOutcome, kraus_zCondition]
    intro h
    have := congrFun (congrFun h (bit 0)) (bit 1)
    rw [Matrix.single_apply_same, matrix_single_bit_apply, if_neg (fun h' => h01.symm h'.1)] at this
    exact one_ne_zero this

-- row: agreement H1
/-- **`H1`.** Z-conditioning, then H on the outcome bit: `K_o = Z^o/√2`, the Hilbert side's Z
(`pauliOperator (pauliz 0)`) to the power of the outcome, over `√2`. -/
theorem kraus_hadamardOnOutcome (o : Fin 1 → ZMod 2) :
    kraus hadamardOnOutcome o =
      invSqrt2 • LinearMap.toMatrix' (pauliOperator (pauliz (0 : Fin 1))) ^ (o 0).val := by
  obtain ⟨c, rfl⟩ : ∃ c, o = bit c := ⟨o 0, word_one_eq_bit o⟩
  ext y x
  obtain ⟨a, rfl⟩ : ∃ a, y = bit a := ⟨y 0, word_one_eq_bit y⟩
  obtain ⟨b, rfl⟩ : ∃ b, x = bit b := ⟨x 0, word_one_eq_bit x⟩
  rw [kraus_apply, hilbertSem_hadamardOnOutcome_apply, append_bit_zero, append_bit_one,
    single_bit_apply, Matrix.smul_apply]
  rcases zmod2_cases c with rfl | rfl
  · rw [show (bit 0 0).val = 0 from rfl, pow_zero, Matrix.one_apply]
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp [bit_inj]
  · rw [show (bit 1 0).val = 1 from rfl, pow_one, LinearMap.toMatrix'_apply,
      pauliOperator_apply_fun, pauliz_X, sub_zero, zDotVal_pauliz, single_bit_apply]
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp [bit]

-- row: discriminating
/-- **`H1` is not controls-only.** H acts on the outcome bit, so `OutcomeControlsOnly` fails. -/
theorem not_outcomeControlsOnly_hadamardOnOutcome :
    ¬ OutcomeControlsOnly hadamardOnOutcome := by
  simp [OutcomeControlsOnly, hadamardOnOutcome, LetterControlsOnly]

/-- `H1`'s entries at the outcome `1` and the entry `(0, 0)`: `1/√2` in `K_1`, `0` in the product
form. -/
private theorem kraus_krausProduct_hadamardOnOutcome_entry :
    kraus hadamardOnOutcome (bit 1) (bit 0) (bit 0) = invSqrt2 ∧
      krausProduct hadamardOnOutcome (bit 1) (bit 0) (bit 0) = 0 := by
  constructor
  · rw [kraus_apply, hilbertSem_hadamardOnOutcome_apply, append_bit_zero, append_bit_one,
      single_bit_apply]
    simp
  · simp only [hadamardOnOutcome, zCondition, krausProduct, Matrix.mul_one, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    obtain ⟨d, rfl⟩ : ∃ d, z = bit d := ⟨z 0, word_one_eq_bit z⟩
    refine mul_eq_zero_of_right _ ?_
    rw [LinearMap.toMatrix'_apply]
    erw [bornProjection_zPlus_apply]
    rw [single_bit_apply]
    change (if d = 1 then (if d = 0 then (1 : ℂ) else 0) else 0) = 0
    rcases zmod2_cases d with rfl | rfl <;> simp

-- row: discriminating
/-- **`H1`'s `K_1` is not the product form.** At the outcome `1`, `K_1` has `1/√2` at the entry
`(0, 0)`, and `krausProduct`, the H's matrix at `1` after the Born projector `P₁`, has `0`: where
a word acts on an outcome bit, the Kraus operator is no product of a projector and a unitary. -/
theorem kraus_hadamardOnOutcome_ne_krausProduct :
    kraus hadamardOnOutcome (bit 1) ≠ krausProduct hadamardOnOutcome (bit 1) := by
  intro h
  obtain ⟨hk, hp⟩ := kraus_krausProduct_hadamardOnOutcome_entry
  have h' := congrFun (congrFun h (bit 0)) (bit 0)
  rw [hk, hp] at h'
  exact invSqrt2_ne_zero h'

-- row: inhabitation
/-- **Z-conditioning satisfies `OutcomeControlsOnly`.** Its conditioning Pauli `+Z₀` touches no
outcome bit, there being none yet (`zCondition` conditions `nil`, which has none): the two
hypotheses of `kraus_eq_prod_of_controlsOnly` hold together for a concrete object, `zCondition`,
and there `kraus` equals the product form `krausProduct`. -/
theorem outcomeControlsOnly_zCondition :
    OutcomeControlsOnly zCondition
      ∧ ∀ o : Fin 1 → ZMod 2, kraus zCondition o = krausProduct zCondition o := by
  have hp : OutcomeControlsOnly zCondition := ⟨trivial, fun j => j.elim0⟩
  exact ⟨hp, kraus_eq_prod_of_controlsOnly zCondition hp⟩

/-! ## The aimed mutant -/

-- mutant: kraus_scale | FTQCLib/Hilbert/ProtocolSemantics.lean
--   | LinearMap.toMatrix' (evalOutcome n o ∘ₗ hilbertSem p)
--   | (2 : ℂ) • LinearMap.toMatrix' (evalOutcome n o ∘ₗ hilbertSem p)

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Hilbert.hilbertSem_nil' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.hilbertSem_nil

/-- info: 'FTQCLib.Hilbert.hilbertSem_word' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.hilbertSem_word

/-- info: 'FTQCLib.Hilbert.hilbertSem_condition' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.hilbertSem_condition

/-- info: 'FTQCLib.Hilbert.hilbertSem_isometry' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.hilbertSem_isometry

/-- info: 'FTQCLib.Hilbert.kraus_mulVec' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.kraus_mulVec

/-- info: 'FTQCLib.Hilbert.kraus_sum_eq_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.kraus_sum_eq_one

/-- info: 'FTQCLib.Hilbert.kraus_eq_prod_of_controlsOnly' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.kraus_eq_prod_of_controlsOnly

/-- info: 'FTQCLib.Hilbert.homMatrix_toHom' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.homMatrix_toHom

/-- info: 'FTQCLib.Hilbert.homMatrix_comp' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.homMatrix_comp

/-- info: 'FTQCLib.Hilbert.homMatrix_id' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.homMatrix_id

/-- info: 'FTQCLib.Hilbert.homMatrix_tensor' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.homMatrix_tensor

/-- info: 'FTQCLib.Hilbert.wordGate_append' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.wordGate_append

/-- info: 'FTQCLib.Hilbert.wordAt_unitary' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.wordAt_unitary

end FTQCLib.Hilbert.ProtocolSemanticsCheck

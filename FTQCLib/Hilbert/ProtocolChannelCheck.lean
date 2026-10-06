/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ProtocolChannel
import FTQCLib.Hilbert.ProtocolSemanticsCheck

/-!
# Check: the non-selective channel and H inject, on one data bit

T21's witness (`docs/STEPS.md`, T21.2): rows on the frozen statement of `ProtocolChannel.lean`,
computed from the definitions of `nonselective`, `krausChannel` and `hInjectKraus` (through
`kraus`, `hilbertSem`, `bornProjection`, `conditionIsometry`, `cnotGate`, `diagonalGate`,
`hadamardGate` and `plusAncilla`), never through `kraus_weights_sum`,
`nonselective_tracePreserving`, `nonselective_condition_eq_luders` or `hInject_channel_eq`, which
are not yet proved, nor through T17's `kraus_sum_eq_one`. The one-bit protocols are T17's witness's
(`ProtocolSemanticsCheck`): `zCondition`, conditioning on `+Z₀`, and `cnotFromOutcome`, the same
then CNOT from the outcome bit to bit `0`, whose Kraus operators that module computes
(`kraus_zCondition`, `kraus_cnotFromOutcome_not_projectors`).

* **The reset (agreement).** `cnotFromOutcome`'s non-selective channel is the reset
  `ρ ↦ tr(ρ)|0⟩⟨0|`, and it keeps the trace of every `ρ`: computed from `K₀ = |0⟩⟨0|`,
  `K₁ = |0⟩⟨1|` by `Kᵢ ρ Kᵢ† = ρᵢᵢ |0⟩⟨0|`.
* **`R2` (discriminating).** The reset takes `I/2` to `P₀ = |0⟩⟨0|`: the channel is not unital,
  while every Lüders channel is (the corrected claim of T21, entry 2026-10-02l). The nearest
  wrong object is a Lüders channel, which fixes `I/2`; the input is `I/2`, and the output differs
  from `I/2` at the entry `(1, 1)`, `0` against `1/2`.
* **Z-conditioning is Lüders (agreement).** The object `nonselective_condition_eq_luders` names,
  at `P = +Z₀`, `w₁ = w₂ = []`: its channel is `Σ_b Π_b ρ Π_b` with `Π_b` the Born projectors of
  `+Z₀`, computed as `Π_b = |b⟩⟨b| = K_b`.
* **H inject (agreement).** At precision `1`, one register bit, input qubit `0`: on each matrix
  unit `|a⟩⟨c|`, a basis of the matrices, `krausChannel (hInjectKraus 1 0)` is `H |a⟩⟨c| H†`.
  Computed from the Kraus family letter by letter: `⟦hInjectProtocol 1 0⟧` at a word (the CZ
  phase `(−1)^{x₀x₁}`, the Born projector of `+X₀`, the CNOT), then each `hInjectKraus 1 0 (o, d)`
  entry by entry, which is `[d = o] / √2` times H's entry.

A general fact a later step will need is stated privately here: `bornProjection_paulix_apply`,
the Born projector of `+X_j` at a word `w` is `½(h w + (−1)^b h (w − e_j))`. It belongs in
`Hilbert/ProtocolSemantics.lean`, beside `bornProjection`.

**At T21.4 (this step):**

* **Z-conditioning's hypotheses hold together (inhabitation).** `nonselective_condition_eq_luders`
  applies at the concrete object `P = +Z₀`, `w₁ = w₂ = []`: its side condition `hP` is discharged
  by `zPlus_precision`, a concrete witness that the two hold together.

The axiom sweep below covers every theorem of `ProtocolChannel.lean`, including those this step's
rows do not use (`kraus_weights_sum`, `nonselective_condition_eq_luders`,
`hInject_channel_eq`, `remoteCH_channel_eq`): none is `sorry`'d, all proved at T21.3.1 and T21.3.2
as the topic module's docstring says, and none is used by the inhabitation row above.
-/

namespace FTQCLib.Hilbert.ProtocolChannelCheck

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hilbert FTQCLib.Frame.Walkthrough
open FTQCLib.Hilbert.ProtocolSemanticsCheck (zPlus zPlus_precision zCondition cnotFromOutcome bit
  kraus_zCondition kraus_cnotFromOutcome_not_projectors)
open scoped Matrix

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

/-- A sum over the one-bit outcome strings is the two-term sum over `bit 0`, `bit 1`. -/
private theorem sum_outcome_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → ZMod 2) → M) :
    ∑ o : Fin 1 → ZMod 2, f o = f (bit 0) + f (bit 1) := by
  rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp, sum_zmod2]
  rfl

/-- `Kᵢ ρ Kᵢ†` for a matrix unit `Kᵢ = |a⟩⟨c|`: the entry `ρ c c` at `|a⟩⟨a|`. -/
private theorem single_conj {α : Type*} [Fintype α] [DecidableEq α] (a c : α)
    (ρ : Matrix α α ℂ) :
    Matrix.single a c (1 : ℂ) * ρ * (Matrix.single a c (1 : ℂ))ᴴ
      = Matrix.single a a (ρ c c) := by
  rw [Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, one_mul, mul_one]

/-! ## The reset: `R2` -/

/-- `cnotFromOutcome`'s channel, from its Kraus operators: `Σ_o ρ o o |0⟩⟨0|`. -/
private theorem nonselective_cnotFromOutcome_eq (ρ : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ) :
    nonselective cnotFromOutcome ρ = Matrix.single (bit 0) (bit 0) (ρ.trace) := by
  obtain ⟨h0, h1, -, -⟩ := kraus_cnotFromOutcome_not_projectors
  rw [nonselective_apply, sum_outcome_one, h0, h1, single_conj, single_conj, ← Matrix.single_add,
    Matrix.trace, sum_outcome_one]
  rfl

-- row: agreement
/-- **The reset keeps the trace.** Conditioning on `+Z₀`, then CNOT from the outcome bit to bit
`0`, has the non-selective channel `ρ ↦ tr(ρ)|0⟩⟨0|`, the reset; so the trace of every `ρ` is
kept. Computed from its Kraus operators `|0⟩⟨0|`, `|0⟩⟨1|`. -/
theorem nonselective_cnotFromOutcome_reset (ρ : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ) :
    nonselective cnotFromOutcome ρ = ρ.trace • Matrix.single (bit 0) (bit 0) 1 ∧
      (nonselective cnotFromOutcome ρ).trace = ρ.trace := by
  rw [nonselective_cnotFromOutcome_eq, Matrix.smul_single, smul_eq_mul, mul_one]
  exact ⟨rfl, Matrix.trace_single_eq_same _ _⟩

-- row: discriminating R2
/-- **`R2`: the reset is not unital.** It takes `I/2` to `P₀ = |0⟩⟨0|`, which differs from `I/2`
at the entry `(1, 1)`: `0` against `1/2`. Every Lüders channel fixes `I/2`, so this channel,
trace preserving, is no Lüders channel. -/
theorem nonselective_cnotFromOutcome_not_unital :
    nonselective cnotFromOutcome ((2⁻¹ : ℂ) • 1) = Matrix.single (bit 0) (bit 0) 1 ∧
      nonselective cnotFromOutcome ((2⁻¹ : ℂ) • 1) (bit 1) (bit 1) = 0 ∧
      ((2⁻¹ : ℂ) • (1 : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ)) (bit 1) (bit 1) = 2⁻¹ := by
  have htr : ((2⁻¹ : ℂ) • (1 : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ)).trace = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have hne : bit 0 ≠ bit 1 := fun h => absurd (congrFun h 0) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [nonselective_cnotFromOutcome_eq, htr]
  · rw [nonselective_cnotFromOutcome_eq, htr, Matrix.single_apply_of_ne]
    exact fun h => hne h.1
  · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]

/-! ## Z-conditioning is Lüders -/

/-- The Born projector of `+Z₀` at `b` keeps the words whose bit is `b`. -/
private theorem bornProjection_zPlus_apply (b : ZMod 2) (ψ : QubitSpace 1)
    (v : Fin 1 → ZMod 2) :
    bornProjection zPlus b ψ v = if v 0 = b then ψ v else 0 := by
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

/-- The Born projector of `+Z₀` at `b`, as a matrix, is the matrix unit `|b⟩⟨b|`. -/
private theorem toMatrix_bornProjection_zPlus (b : ZMod 2) :
    LinearMap.toMatrix' (bornProjection zPlus b) = Matrix.single (bit b) (bit b) 1 := by
  ext y x
  obtain ⟨a, rfl⟩ : ∃ a, y = bit a := ⟨y 0, word_one_eq_bit y⟩
  obtain ⟨c, rfl⟩ : ∃ c, x = bit c := ⟨x 0, word_one_eq_bit x⟩
  rw [LinearMap.toMatrix'_apply, bornProjection_zPlus_apply, Pi.single_apply, Matrix.single_apply]
  simp only [bit_inj, show ∀ e : ZMod 2, bit e 0 = e from fun _ => rfl]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases c with rfl | rfl <;> simp

/-- The empty word leaves the Kraus family unchanged. -/
private theorem kraus_word_nil {k : ℕ} (p : Protocol 1 1 k) (o : Fin k → ZMod 2) :
    kraus (p.word []) o = kraus p o := by
  rw [kraus, kraus, hilbertSem_word]
  rfl

-- row: agreement
/-- **Z-conditioning's channel is the Lüders channel.** The object
`nonselective_condition_eq_luders` names, at one data bit, `P = +Z₀`, `w₁ = w₂ = []`: its
non-selective channel is `Σ_b Π_b ρ Π_b`, the Born projectors of `+Z₀` on either side, after the
empty word's unitary, the identity. Computed from `K_b = |b⟩⟨b| = Π_b`. -/
theorem nonselective_zCondition_eq_luders (ρ : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ) :
    nonselective (((Protocol.nil : Protocol 1 1 0).condition zPlus zPlus_precision).word
        (liftData 1 ([] : GateWord 1 1) ++ liftUnread 1 ([] : GateWord 1 1))) ρ
      = LinearMap.toMatrix' (wordGate ([] : GateWord 1 1)) *
          (∑ b : ZMod 2, LinearMap.toMatrix' (bornProjection zPlus b) * ρ *
            LinearMap.toMatrix' (bornProjection zPlus b)) *
          (LinearMap.toMatrix' (wordGate ([] : GateWord 1 1)))ᴴ := by
  have hw : wordGate ([] : GateWord 1 1) = LinearMap.id := rfl
  have hword : liftData 1 ([] : GateWord 1 1) ++ liftUnread 1 ([] : GateWord 1 1) = [] := rfl
  rw [hw, LinearMap.toMatrix'_id, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    hword, nonselective_apply, sum_outcome_one, sum_zmod2]
  simp only [kraus_word_nil, toMatrix_bornProjection_zPlus]
  change kraus zCondition (bit 0) * ρ * (kraus zCondition (bit 0))ᴴ
      + kraus zCondition (bit 1) * ρ * (kraus zCondition (bit 1))ᴴ = _
  simp only [kraus_zCondition, Matrix.conjTranspose_single, star_one]

/-! ## H inject -/

/-- **The Born projector of `+X_j` at a word**: `½(h w + (−1)^b h (w − e_j))`. -/
private theorem bornProjection_paulix_apply {N : ℕ} (j : Fin N) (b : ZMod 2) (h : QubitSpace N)
    (w : Fin N → ZMod 2) :
    bornProjection (⟨0, paulix j⟩ : SignedPauli N) b h w
      = 2⁻¹ * (h w + (-1 : ℂ) ^ b.val * h (w - Pi.single j 1)) := by
  simp only [bornProjection, LinearMap.comp_apply, LinearEquiv.coe_coe, toQState_symm_apply,
    bornProjector, LinearMap.smul_apply, PiLp.smul_apply, LinearMap.add_apply, PiLp.add_apply,
    LinearMap.id_apply, pauliHermitian_apply_fun, toQState_apply, smul_eq_mul]
  have hw : xzWeight (paulix j) = 0 := by
    simp only [xzWeight, zDotVal, paulix_Z, Pi.zero_apply, ZMod.val_zero, zero_mul,
      Finset.sum_const_zero]
  have hz : ∀ v, zDotVal (paulix j) v = 0 := by
    intro v
    simp only [zDotVal, paulix_Z, Pi.zero_apply, ZMod.val_zero, zero_mul, Finset.sum_const_zero]
  rw [hw, hz, ZMod.val_zero]
  simp [paulix]

/-- **The conditioning letter's isometry at a word**: the Born projector at the word's last bit,
applied at `Fin.init u`. -/
private theorem conditionIsometry_apply {N : ℕ} (P : SignedPauli N) (χ : QubitSpace N)
    (u : Fin (N + 1) → ZMod 2) :
    conditionIsometry P χ u = bornProjection P (u (Fin.last N)) χ (Fin.init u) := by
  simp only [conditionIsometry, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  rw [Finset.sum_eq_single (u (Fin.last N))]
  · change (if u ∘ Fin.natAdd N = fun _ => u (Fin.last N) then _ else 0) = _
    rw [if_pos (funext fun i => by rw [Subsingleton.elim i 0]; rfl)]
    rfl
  · intro b _ hb
    change (if u ∘ Fin.natAdd N = fun _ => b then _ else 0) = 0
    rw [if_neg]
    intro h
    exact hb (congrFun h 0).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The CZ letter's phase at precision `1`: `(−1)^{v₀v₁}`. -/
private theorem exp_realPhase_czGate (v : Fin (1 + 1) → ZMod 2) :
    Complex.exp (Complex.I *
        (DiagPhase.realPhase (DiagPhase.czGate 1 (Fin.castSucc (0 : Fin 1)) (Fin.last 1)) v : ℂ))
      = (-1 : ℂ) ^ ((v 0).val * (v 1).val) := by
  rw [exp_realPhase_eq_charOf, charOf_czGate_eval le_rfl]
  rfl

/-- **`⟦hInjectProtocol 1 0⟧` at a word** `w = (x₀, x₁, o)`: the CNOT reads the ancilla at
`x₁ + o`, the Born projector of `+X₀` at `o` averages the data bit's two values, and the CZ phase
is `(−1)^{x₀x₁}`. -/
private theorem hilbertSem_hInject_apply (φ : QubitSpace (1 + 1)) (w : Fin (1 + 1 + 1) → ZMod 2) :
    hilbertSem (hInjectProtocol 1 (0 : Fin 1)) φ w
      = 2⁻¹ * ((-1 : ℂ) ^ ((w 0).val * (w 1 + w 2).val) * φ ![w 0, w 1 + w 2]
        + (-1 : ℂ) ^ (w 2).val *
          ((-1 : ℂ) ^ ((w 0 + 1).val * (w 1 + w 2).val) * φ ![w 0 + 1, w 1 + w 2])) := by
  simp only [hInjectProtocol, hilbertSem_word, hilbertSem_condition, hilbertSem_nil,
    LinearMap.comp_apply, LinearMap.id_apply, wordGate, letterGate, LinearEquiv.coe_coe,
    cnotGate_apply, LinearMap.id_comp]
  rw [conditionIsometry_apply, bornProjection_paulix_apply, diagonalGate_apply, diagonalGate_apply,
    exp_realPhase_czGate, exp_realPhase_czGate]
  have hlast : cnotPerm (Fin.last (1 + 1)) (Fin.last 1).castSucc w (Fin.last (1 + 1)) = w 2 := rfl
  have hinit :
      Fin.init (cnotPerm (Fin.last (1 + 1)) (Fin.last 1).castSucc w) = ![w 0, w 1 + w 2] := by
    funext i
    fin_cases i <;> rfl
  have hflip : (![w 0, w 1 + w 2] - Pi.single (Fin.castSucc (0 : Fin 1)) 1 : Fin (1 + 1) → ZMod 2)
      = ![w 0 + 1, w 1 + w 2] := by
    funext i
    fin_cases i
    · change w 0 - 1 = w 0 + 1
      rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    · change w 1 + w 2 - 0 = w 1 + w 2
      rw [sub_zero]
  rw [hlast, hinit, hflip]
  rfl

/-- The register word `(a, d)` read through the swap of bit `0` and the ancilla: `(d, a)`. -/
private theorem append_comp_swap (a d : ZMod 2) :
    ((Fin.append (bit a) fun _ : Fin 1 => d) ∘
        ⇑(Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1)) : Fin (1 + 1) → ZMod 2)
      = Fin.append (bit d) (bit a) := by
  funext i
  fin_cases i <;> rfl

private theorem update_pair_zero (a b d : ZMod 2) :
    Function.update (Fin.append (bit d) (bit a) : Fin (1 + 1) → ZMod 2) (Fin.castSucc (0 : Fin 1)) b
      = Fin.append (bit b) (bit a) := by
  funext i
  fin_cases i <;> rfl

private theorem append_pair_bit_zero (a b e : ZMod 2) :
    (Fin.append (Fin.append (bit b) (bit a)) (bit e) : Fin (1 + 1 + 1) → ZMod 2) 0 = b :=
  rfl

private theorem append_pair_bit_one (a b e : ZMod 2) :
    (Fin.append (Fin.append (bit b) (bit a)) (bit e) : Fin (1 + 1 + 1) → ZMod 2) 1 = a :=
  rfl

private theorem append_pair_bit_two (a b e : ZMod 2) :
    (Fin.append (Fin.append (bit b) (bit a)) (bit e) : Fin (1 + 1 + 1) → ZMod 2) 2 = e :=
  rfl

private theorem append_pair_zero (a d : ZMod 2) :
    (Fin.append (bit d) (bit a) : Fin (1 + 1) → ZMod 2) (Fin.castSucc 0) = d :=
  rfl

private theorem one_add_one_eq_zero_zmod2 : (1 + 1 : ZMod 2) = 0 := by
  decide

private theorem init_eq_bit (v : Fin (1 + 1) → ZMod 2) : Fin.init v = bit (v 0) := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

private theorem single_bit_apply (a b : ZMod 2) :
    (Pi.single (bit b) (1 : ℂ) : QubitSpace 1) (bit a) = if a = b then 1 else 0 := by
  rw [Pi.single_apply]
  simp only [bit_inj]

/-- **H inject's Kraus entries**, from the protocol's semantics at a word
(`hilbertSem_hInject_apply`): at `(o, d) = (e, d)`, the entry `(a, c)` is `[d = e]/√2` times
`(−1)^{ac}/√2`. -/
private theorem hInjectKraus_apply (e d a c : ZMod 2) :
    hInjectKraus 1 (0 : Fin 1) (bit e, d) (bit a) (bit c)
      = (if d = e then invSqrt2 else 0) * (invSqrt2 * (-1 : ℂ) ^ (a.val * c.val)) := by
  rw [hInjectKraus, kraus, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_apply]
  simp only [LinearMap.comp_apply, evalOutcome, LinearMap.funLeft_apply, hadamardGate_apply,
    sum_zmod2, hilbertSem_hInject_apply, plusAncilla, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, append_comp_swap, update_pair_zero, append_pair_bit_zero, append_pair_bit_one,
    append_pair_bit_two, append_pair_zero, init_eq_bit, Matrix.cons_val_zero, single_bit_apply]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    rcases zmod2_cases d with rfl | rfl <;> rcases zmod2_cases e with rfl | rfl <;>
    simp only [one_add_one_eq_zero_zmod2, ZMod.val_zero, ZMod.val_one, zero_add, add_zero, mul_zero,
      zero_mul, mul_one, pow_zero, pow_one, one_mul, if_true, if_false, one_ne_zero, zero_ne_one,
      ] <;> ring

/-- H's matrix entry `(a, c)` on one bit: `(−1)^{ac}/√2`. -/
private theorem toMatrix_hadamardGate_apply (a c : ZMod 2) :
    LinearMap.toMatrix' (hadamardGate (0 : Fin 1)) (bit a) (bit c)
      = invSqrt2 * (-1 : ℂ) ^ (a.val * c.val) := by
  have hupd : ∀ b : ZMod 2, Function.update (bit a) 0 b = bit b := by
    intro b
    funext i
    rw [Subsingleton.elim i 0, Function.update_self]
    rfl
  rw [LinearMap.toMatrix'_apply, hadamardGate_apply, sum_zmod2, hupd, hupd, single_bit_apply,
    single_bit_apply, show bit a 0 = a from rfl]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    simp only [ZMod.val_zero, ZMod.val_one, mul_zero, mul_one, pow_zero, pow_one, if_true,
      if_false, one_ne_zero, zero_ne_one] <;> ring

/-- Each Kraus operator of H inject, at precision `1` on one register bit, is its scalar times
H's matrix: computed entry by entry, without `hInject_channel_eq`. -/
private theorem hInjectKraus_eq_smul (i : (Fin 1 → ZMod 2) × ZMod 2) :
    hInjectKraus 1 (0 : Fin 1) i
      = (if i.2 = i.1 0 then invSqrt2 else 0) • LinearMap.toMatrix' (hadamardGate (0 : Fin 1)) := by
  obtain ⟨o, d⟩ := i
  obtain ⟨e, rfl⟩ : ∃ e, o = bit e := ⟨o 0, word_one_eq_bit o⟩
  ext y x
  obtain ⟨a, rfl⟩ : ∃ a, y = bit a := ⟨y 0, word_one_eq_bit y⟩
  obtain ⟨c, rfl⟩ : ∃ c, x = bit c := ⟨x 0, word_one_eq_bit x⟩
  rw [hInjectKraus_apply, Matrix.smul_apply, toMatrix_hadamardGate_apply, smul_eq_mul]
  rfl

private theorem star_invSqrt2 : star invSqrt2 = invSqrt2 := by
  rw [invSqrt2, Complex.star_def, Complex.conj_ofReal]

/-! ## An inhabitation row -/

-- row: inhabitation
/-- **Z-conditioning's hypotheses hold together.** `nonselective_condition_eq_luders` applies at
the concrete object `P = +Z₀`, `w₁ = w₂ = []`: its side condition `hP` is discharged by
`zPlus_precision`, a concrete witness that the hypotheses hold together, and the conclusion
below is that theorem's instance there. -/
theorem nonselective_condition_eq_luders_inhabited
    (ρ : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ) :
    nonselective (((Protocol.nil : Protocol 1 1 0).condition zPlus zPlus_precision).word
        (liftData 1 ([] : GateWord 1 1) ++ liftUnread 1 ([] : GateWord 1 1))) ρ
      = LinearMap.toMatrix' (wordGate ([] : GateWord 1 1)) *
          (∑ b : ZMod 2, LinearMap.toMatrix' (bornProjection zPlus b) * ρ *
            LinearMap.toMatrix' (bornProjection zPlus b)) *
          (LinearMap.toMatrix' (wordGate ([] : GateWord 1 1)))ᴴ :=
  nonselective_condition_eq_luders zPlus zPlus_precision [] [] ρ

-- row: agreement
/-- **H inject's channel is conjugation by H, on a basis of matrices.** At precision `1`, one
register bit, input qubit `0`: on every matrix unit `|a⟩⟨c|`, the Kraus sum of `hInjectKraus`
is `H |a⟩⟨c| H†`. Computed from the Kraus operators entry by entry, each `[d = o]/√2` times H,
the four scalars' squared moduli `½, 0, 0, ½` summing to one. -/
theorem krausChannel_hInjectKraus_single (a c : Fin 1 → ZMod 2) :
    krausChannel (hInjectKraus 1 (0 : Fin 1)) (Matrix.single a c 1)
      = LinearMap.toMatrix' (hadamardGate (0 : Fin 1)) * Matrix.single a c 1 *
          (LinearMap.toMatrix' (hadamardGate (0 : Fin 1)))ᴴ := by
  rw [krausChannel]
  simp only [hInjectKraus_eq_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_smul,
    smul_smul]
  rw [← Finset.sum_smul, Fintype.sum_prod_type, sum_outcome_one, sum_zmod2, sum_zmod2]
  have hb : ∀ e : ZMod 2, bit e 0 = e := fun _ => rfl
  simp only [hb, if_true, if_false, one_ne_zero, zero_ne_one, star_zero, star_invSqrt2, mul_zero,
    add_zero, zero_add, invSqrt2_mul_self]
  norm_num

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Hilbert.nonselective_apply' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.nonselective_apply

/-- info: 'FTQCLib.Hilbert.kraus_weights_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.kraus_weights_sum

/-- info: 'FTQCLib.Hilbert.nonselective_tracePreserving' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.nonselective_tracePreserving

/-- info: 'FTQCLib.Hilbert.nonselective_condition_eq_luders' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.nonselective_condition_eq_luders

/-- info: 'FTQCLib.Hilbert.hInject_channel_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.hInject_channel_eq

/-- info: 'FTQCLib.Hilbert.remoteCH_channel_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.remoteCH_channel_eq

end FTQCLib.Hilbert.ProtocolChannelCheck

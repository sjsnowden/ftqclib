/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.BranchSoundness
import FTQCLib.Hilbert.ProtocolSemanticsCheck
import FTQCLib.Carrier.HInject
import FTQCLib.Carrier.CarrierStateHadamardCheck

/-!
# Check: soundness of every branch, on small protocols

T20's witness (`docs/STEPS.md`, T20.2): rows on the frozen statement of `BranchSoundness.lean`,
now proved at T20.3 (`interpretAmp_eq_hilbertSem`, `branch_eq_kraus`, `branch_eq_krausProduct`;
T17's `kraus_mulVec`, T18's `runAmp_eq_wordGate` and T19's `pauliProjection_eq_bornProjection`
likewise proved). The witness's own rows are about a protocol's branch (`Protocol.branch`, the
interpretation evaluated at an outcome string), computed from the definitions of `interpretAmp`
and `hilbertSem` letter by letter, through T14's `amp_interpret` and T17's `kraus_mulVec`, and
never through `interpretAmp_eq_hilbertSem`, `branch_eq_kraus` or `branch_eq_krausProduct`, nor
through T18's `runAmp_eq_wordGate` or T19's `pauliProjection_eq_bornProjection`.

* **T15's H inject (agreement).** On a register of one bit with its ancilla, input qubit `0`, at
  any precision `m`: on every carrier state at precision `m` and at each outcome, the branch of
  `hInjectProtocol m 0` is `kraus` applied to the input's amplitude. The two sides are computed
  letter by letter on this protocol: the CZ letter's phase `charOf m (D w)` is the diagonal
  gate's `exp (i·realPhase D w)` by definition, the CNOT bit-map is `cnotPerm`, and the
  X-measurement's projection `½(f + (−1)^b X₀ f)` is the Born projector of `+X₀`, computed here
  for `X_j` from `pauliAct` and `pauliHermitian`.
* **`H1` (agreement).** Conditioning on `+Z₀`, then H on its outcome bit
  (`ProtocolSemanticsCheck.hadamardOnOutcome`): on every one-bit carrier state at precision `1`,
  the branch at `o` is `Z^o ψ/√2`, against the Hilbert side's Z, `pauliOperator (pauliz 0)`. The
  branch is computed on the frame side, the Walsh transform of the projections.
* **Two letters swapped (discriminating).** H on the data bit then conditioning on `+Z₀`
  (`hadamardThenCondition`), against conditioning on `+Z₀` then H on the data bit
  (`conditionThenHadamard`): on `∣0⟩` (`KZ`), at the outcome `1` and the data word `1`, the
  first branch is `1/√2` (`H∣0⟩` read at `1`) and the second `0` (the projection onto `1` kills
  `∣0⟩`). So the branch depends on the order of the letters.
* **`branch_eq_kraus`'s hypotheses (inhabitation).** `∣0⟩` is a carrier state at precision `1`,
  the precision of `hadamardOnOutcome`, `hadamardThenCondition` and `conditionThenHadamard`.

A general fact the proof step will need is stated privately here: `conditionIsometry_apply`, the
conditioning letter's isometry at a word `u` is the Born projector at `u`'s last bit, applied at
`Fin.init u`. It belongs in `Hilbert/ProtocolSemantics.lean`.
-/

namespace FTQCLib.Hilbert.BranchSoundnessCheck

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Hilbert
  FTQCLib.Frame.Walkthrough
open FTQCLib.Hilbert.ProtocolSemanticsCheck (zPlus zPlus_precision zCondition hadamardOnOutcome bit)
open scoped Matrix

/-! ## Private computations -/

private theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

/-- Over `ZMod 2`, subtracting a word is adding it. -/
private theorem sub_eq_add_word {N : ℕ} (w v : Fin N → ZMod 2) : w - v = w + v := by
  funext i
  rw [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

private theorem xzWeight_paulix {N : ℕ} (j : Fin N) : xzWeight (paulix j) = 0 := by
  simp only [xzWeight, zDotVal, paulix_Z, Pi.zero_apply, ZMod.val_zero, zero_mul,
    Finset.sum_const_zero]

private theorem zDotVal_paulix {N : ℕ} (j : Fin N) (v : Fin N → ZMod 2) :
    zDotVal (paulix j) v = 0 := by
  simp only [zDotVal, paulix_Z, Pi.zero_apply, ZMod.val_zero, zero_mul, Finset.sum_const_zero]

/-- The frame's projection for `+X_j` is the Born projector of `+X_j`: `X_j` has no Y and no Z,
so both are `½(h w + (−1)^b h (w + e_j))`. -/
private theorem pauliProjection_paulix_eq {N : ℕ} (j : Fin N) (b : ZMod 2) (h : QubitSpace N) :
    pauliProjection ⟨0, paulix j⟩ b h = bornProjection ⟨0, paulix j⟩ b h := by
  funext w
  simp only [pauliProjection, SignedPauli.act, pauliAct, bornProjection, LinearMap.comp_apply,
    LinearEquiv.coe_coe, toQState_symm_apply, bornProjector, LinearMap.smul_apply,
    PiLp.smul_apply, LinearMap.add_apply, PiLp.add_apply, LinearMap.id_apply,
    pauliHermitian_apply_fun, toQState_apply, smul_eq_mul]
  rw [yWeight_paulix, zDot_paulix, xzWeight_paulix, zDotVal_paulix, sub_eq_add_word,
    ZMod.val_zero]
  norm_num

/-- **The conditioning letter's isometry at a word.** `conditionIsometry P χ` at `u` is the Born
projector at `u`'s last bit, applied to `χ` at `Fin.init u`: the sum over `b` keeps one term. -/
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

/-- On T15's H inject with one register bit, the frame's referee and T17's semantics agree, letter
by letter: CNOT's bit-map is `cnotPerm`, the X-measurement's projection is the Born projector
(`pauliProjection_paulix_eq`) read at the last bit (`conditionIsometry_apply`), and CZ's phase is
the diagonal gate's. -/
private theorem interpretAmp_hInjectProtocol (m : ℕ) (f : QubitSpace (1 + 1)) :
    (hInjectProtocol m (0 : Fin 1)).interpretAmp f
      = hilbertSem (hInjectProtocol m (0 : Fin 1)) f := by
  simp only [hInjectProtocol, Protocol.interpretAmp_word, Protocol.interpretAmp_condition,
    Protocol.interpretAmp_nil, hilbertSem_word, hilbertSem_condition, hilbertSem_nil,
    LinearMap.comp_apply, LinearMap.id_apply]
  funext v
  simp only [runAmp, List.foldl, letterAmp, wordGate, letterGate, LinearMap.comp_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, cnotGate_apply]
  rw [conditionIsometry_apply, ← pauliProjection_paulix_eq]
  rfl

/-! ## T15's H inject -/

-- row: agreement
/-- **H inject: the branch is `K_o` applied to the input.** On T15's H inject with one register
bit and its ancilla, input qubit `0`, at any precision `m`: on every carrier state at precision
`m` and at each outcome `o`, the branch is `kraus` applied to the input's amplitude. -/
theorem hInjectProtocol_branch_eq_kraus {m : ℕ} {S : KernelSumState (1 + 1)} (hS : IsCarrier S)
    (hm : S.m = m) (o : Fin 1 → ZMod 2) :
    (hInjectProtocol m (0 : Fin 1)).branch S o
      = kraus (hInjectProtocol m (0 : Fin 1)) o *ᵥ amp S := by
  funext w
  rw [kraus_mulVec]
  change amp ((hInjectProtocol m (0 : Fin 1)).interpret S) (Fin.append w o) = _
  rw [(amp_interpret _ hS hm).2, interpretAmp_hInjectProtocol]

/-! ## One data bit -/

/-- A one-bit word is the bit word of its value. -/
private theorem word_one_eq_bit (y : Fin 1 → ZMod 2) : y = bit (y 0) := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

/-- `Z₀`'s `zDot` with a one-bit word is the word's value. -/
private theorem zDot_pauliz_one (u : Fin 1 → ZMod 2) : zDot (pauliz (0 : Fin 1)) u = (u 0).val := by
  simp [zDot, pauliz]

/-- The projection of `+Z₀` at `d` keeps the words whose bit is `d`. -/
private theorem pauliProjection_zPlus_apply (d : ZMod 2) (f : QubitSpace 1) (u : Fin 1 → ZMod 2) :
    pauliProjection zPlus d f u = if u 0 = d then f u else 0 := by
  have hy : yWeight (pauliz (0 : Fin 1)) = 0 := by simp [yWeight, zDot, pauliz]
  simp only [pauliProjection, SignedPauli.act, pauliAct, 
    show zPlus.pauli = pauliz 0 from rfl, hy, zDot_pauliz_one, show zPlus.sign = 0 from rfl,
    ZMod.val_zero, pow_zero, one_mul]
  rcases zmod2_cases d with rfl | rfl <;> rcases zmod2_cases (u 0) with h | h <;>
    simp [h] <;> ring

/-- Setting the outcome bit of `(a, c)` to `d` gives `(a, d)`. -/
private theorem update_append_last (a c d : ZMod 2) :
    Function.update (Fin.append (bit a) (bit c) : Fin (1 + 1) → ZMod 2) (Fin.last 1) d
      = Fin.append (bit a) (bit d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Function.update_self]
    exact (Fin.append_right (bit a) (bit d) 0).symm
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    rw [show (Fin.castSucc j : Fin (1 + 1)) = Fin.castAdd 1 j from rfl, Fin.append_left,
      Fin.append_left]

/-- Setting the data bit of `(a, c)` to `d` gives `(d, c)`. -/
private theorem update_append_zero (a c d : ZMod 2) :
    Function.update (Fin.append (bit a) (bit c) : Fin (1 + 1) → ZMod 2) 0 d
      = Fin.append (bit d) (bit c) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Function.update_of_ne (by decide)]
    exact (Fin.append_right (bit a) (bit c) 0).trans (Fin.append_right (bit d) (bit c) 0).symm
  · rw [Subsingleton.elim j 0, show (Fin.castSucc (0 : Fin 1) : Fin (1 + 1)) = 0 from rfl,
      Function.update_self]
    exact (Fin.append_left (bit d) (bit c) 0).symm

/-- The last bit of `(a, d)` is `d`. -/
private theorem append_last (a d : ZMod 2) :
    (Fin.append (bit a) (bit d) : Fin (1 + 1) → ZMod 2) (Fin.last 1) = d :=
  Fin.append_right (bit a) (bit d) 0

/-- Bit `0` of `(a, d)` is `a`. -/
private theorem append_zero (a d : ZMod 2) :
    (Fin.append (bit a) (bit d) : Fin (1 + 1) → ZMod 2) 0 = a :=
  Fin.append_left (bit a) (bit d) 0

/-- The data bits of `(a, d)` are `a`. -/
private theorem init_append (a d : ZMod 2) :
    Fin.init (Fin.append (bit a) (bit d) : Fin (1 + 1) → ZMod 2) = bit a := by
  funext i
  rw [Subsingleton.elim i 0]
  exact Fin.append_left (bit a) (bit d) 0

/-- The Walsh transform's factor is `invSqrt2`. -/
private theorem one_div_sqrt_two : 1 / (Real.sqrt 2 : ℂ) = invSqrt2 := by
  rw [invSqrt2, Complex.ofReal_inv, one_div]

/-- `H1`'s referee at `(a, c)`: `(1/√2)(−1)^{c a}` times the input at `a`. -/
private theorem interpretAmp_hadamardOnOutcome (f : QubitSpace 1) (a c : ZMod 2) :
    hadamardOnOutcome.interpretAmp f (Fin.append (bit a) (bit c))
      = invSqrt2 * ((-1 : ℂ) ^ (c.val * a.val) * f (bit a)) := by
  simp only [hadamardOnOutcome, zCondition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_condition, Protocol.interpretAmp_nil, runAmp, List.foldl, letterAmp,
    walshTransform]
  rw [update_append_last, update_append_last, init_append, init_append, append_last]
  erw [append_last, append_last]
  rw [pauliProjection_zPlus_apply, pauliProjection_zPlus_apply, one_div_sqrt_two]
  change invSqrt2 * ((if a = 0 then f (bit a) else 0) + signOf c * (if a = 1 then f (bit a) else 0))
    = _
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    simp [signOf_zero, signOf_one]

-- row: agreement
/-- **`H1`: the branch is `Z^o ψ/√2`.** Conditioning on `+Z₀`, then H on its outcome bit: on every
one-bit carrier state at precision `1`, the branch at `o` is `1/√2` times the Hilbert side's Z,
`pauliOperator (pauliz 0)`, to the power of the outcome, applied to the input's amplitude. -/
theorem hadamardOnOutcome_branch {S : KernelSumState 1} (hS : IsCarrier S) (hm : S.m = 1)
    (o : Fin 1 → ZMod 2) :
    hadamardOnOutcome.branch S o
      = invSqrt2 • ((pauliOperator (pauliz (0 : Fin 1))) ^ (o 0).val) (amp S) := by
  funext w
  obtain ⟨c, rfl⟩ : ∃ c, o = bit c := ⟨o 0, word_one_eq_bit o⟩
  obtain ⟨a, rfl⟩ : ∃ a, w = bit a := ⟨w 0, word_one_eq_bit w⟩
  change amp (hadamardOnOutcome.interpret S) (Fin.append (bit a) (bit c)) = _
  rw [(amp_interpret hadamardOnOutcome hS hm).2, interpretAmp_hadamardOnOutcome, Pi.smul_apply,
    smul_eq_mul]
  rcases zmod2_cases c with rfl | rfl
  · rw [show (bit 0 0).val = 0 from rfl, pow_zero, Module.End.one_apply]
    simp
  · rw [show (bit 1 0).val = 1 from rfl, pow_one, pauliOperator_apply_fun, pauliz_X, sub_zero,
      zDotVal_pauliz]
    simp [bit]

/-! ## Two letters swapped -/

/-- H on the data bit, then conditioning on `+Z₀`. -/
def hadamardThenCondition : Protocol 1 1 1 :=
  ((Protocol.nil : Protocol 1 1 0).word [.hadamard 0]).condition zPlus zPlus_precision

/-- Conditioning on `+Z₀`, then H on the data bit: `hadamardThenCondition` with its two letters
swapped. -/
def conditionThenHadamard : Protocol 1 1 1 :=
  zCondition.word [.hadamard 0]

/-- Setting the bit of a one-bit word to `d` gives `d`. -/
private theorem update_bit (a d : ZMod 2) : Function.update (bit a) 0 d = bit d := by
  funext i
  rw [Subsingleton.elim i 0, Function.update_self]
  rfl

/-- `δ₀` at the one-bit word `d`. -/
private theorem d0_bit (d : ZMod 2) : d0 (bit d) = if d = 0 then 1 else 0 := rfl

/-- `hadamardThenCondition`'s referee at `(a, c)`: the Walsh transform at `a` when `a = c`. -/
private theorem interpretAmp_hadamardThenCondition (f : QubitSpace 1) (a c : ZMod 2) :
    hadamardThenCondition.interpretAmp f (Fin.append (bit a) (bit c))
      = if a = c then walshTransform 0 f (bit a) else 0 := by
  simp only [hadamardThenCondition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_condition, Protocol.interpretAmp_nil, runAmp, List.foldl, letterAmp]
  rw [init_append]
  erw [append_last]
  rw [pauliProjection_zPlus_apply]
  rfl

/-- `conditionThenHadamard`'s referee at `(a, c)`: the Walsh transform, at `a`, of the input
projected onto the word `c`. -/
private theorem interpretAmp_conditionThenHadamard (f : QubitSpace 1) (a c : ZMod 2) :
    conditionThenHadamard.interpretAmp f (Fin.append (bit a) (bit c))
      = invSqrt2 * ((if 0 = c then f (bit 0) else 0)
          + signOf a * (if 1 = c then f (bit 1) else 0)) := by
  simp only [conditionThenHadamard, zCondition, Protocol.interpretAmp_word,
    Protocol.interpretAmp_condition, Protocol.interpretAmp_nil, runAmp, List.foldl, letterAmp,
    walshTransform]
  rw [update_append_zero, update_append_zero, init_append, init_append, append_zero]
  erw [append_last]
  rw [pauliProjection_zPlus_apply, pauliProjection_zPlus_apply, one_div_sqrt_two]
  rfl

/-- `1/√2 ≠ 0`. -/
private theorem invSqrt2_ne_zero : invSqrt2 ≠ 0 := by
  rw [invSqrt2, Complex.ofReal_ne_zero]
  exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))

-- row: discriminating
/-- **Swapping two letters changes a branch.** On `∣0⟩`, at the outcome `1` and the data word `1`,
H then conditioning on `+Z₀` gives `1/√2`, `H∣0⟩` read at `1`; conditioning on `+Z₀` then H gives
`0`, since the projection onto `1` kills `∣0⟩`. So the two branches at the outcome `1` differ. -/
theorem branch_hadamardThenCondition_ne_conditionThenHadamard :
    hadamardThenCondition.branch (ofKernelState KZ) (bit 1) (bit 1) = invSqrt2 ∧
      conditionThenHadamard.branch (ofKernelState KZ) (bit 1) (bit 1) = 0 ∧
      hadamardThenCondition.branch (ofKernelState KZ) (bit 1)
        ≠ conditionThenHadamard.branch (ofKernelState KZ) (bit 1) := by
  have h1 : hadamardThenCondition.branch (ofKernelState KZ) (bit 1) (bit 1) = invSqrt2 := by
    change amp (hadamardThenCondition.interpret _) (Fin.append (bit 1) (bit 1)) = _
    rw [(amp_interpret hadamardThenCondition isCarrier_KZ rfl).2, amp_KZ,
      interpretAmp_hadamardThenCondition, if_pos rfl, walshTransform, update_bit, update_bit,
      d0_bit, d0_bit, one_div_sqrt_two]
    simp
  have h2 : conditionThenHadamard.branch (ofKernelState KZ) (bit 1) (bit 1) = 0 := by
    change amp (conditionThenHadamard.interpret _) (Fin.append (bit 1) (bit 1)) = _
    rw [(amp_interpret conditionThenHadamard isCarrier_KZ rfl).2, amp_KZ,
      interpretAmp_conditionThenHadamard, d0_bit, d0_bit]
    simp
  refine ⟨h1, h2, fun h => invSqrt2_ne_zero ?_⟩
  rw [← h1, ← h2, h]

-- row: inhabitation
/-- **`branch_eq_kraus`'s hypotheses hold together.** `∣0⟩` is a carrier state at precision `1`,
the precision of the one-bit protocols above. -/
theorem branch_eq_kraus_hypotheses_KZ :
    IsCarrier (ofKernelState KZ) ∧ (ofKernelState KZ).m = 1 :=
  ⟨isCarrier_KZ, rfl⟩

/-! ## The aimed mutant -/

-- mutant: branch_eq_kraus_scale | FTQCLib/Hilbert/BranchSoundness.lean
--   | kraus p o *ᵥ amp S
--   | (2 : ℂ) • (kraus p o *ᵥ amp S)

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Hilbert.interpretAmp_eq_hilbertSem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.interpretAmp_eq_hilbertSem

/-- info: 'FTQCLib.Hilbert.branch_eq_kraus' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.branch_eq_kraus

/-- info: 'FTQCLib.Hilbert.branch_eq_krausProduct' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hilbert.branch_eq_krausProduct

end FTQCLib.Hilbert.BranchSoundnessCheck

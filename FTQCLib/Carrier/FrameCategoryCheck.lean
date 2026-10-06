/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FrameCategory
import FTQCLib.Carrier.GateWordCheck

/-!
# Check: T46, the frame as a monoidal category

Rows on the frozen statement of `FrameCategory.lean` (`docs/STEPS.md`, T46.2 and T46.4).

* **Row 1 (agreement).** CZ as a morphism `2 → 2` (`czHom`, the word `[CZ₀₁]` at precision `1`)
  composed with itself is the identity on `2`: `δ_{x = z}` at scale `1`.
* **Row 2 (agreement).** The two-letter protocol `twoLetterProtocol` (H on bit `0`, then the
  conditioning on `Z₀`, at precision `1`, on one data bit): on every carrier state `S` at the
  protocol's precision, the class of T14's interpretation, as a morphism from `0`, is `S`
  composed with the letters' morphisms in order, `[H]` then `[Z₀]`. An inhabitation row gives it
  on `heightOneState` (`GateWordCheck.lean`).
* **Row 3 (discriminating).** The identity on `1 + 1` composed with the swapped identity
  (`FrameCategory.swap ⟨1⟩ ⟨1⟩`) is not the identity: at the input `(0, 1)` and the output
  `(0, 1)` the composite has amplitude `0` and the identity `1`.

Every composite of rows 1–3 is computed from `amp_comp` (the referee of composition, proved at
T46.3.1, no longer `sorry`) and the referees of the pieces (`amp_idState`, `amp_swapState`,
`amp_wordState`, `amp_conditionState`, `amp_castBits`); the interpretation from T14's
`amp_interpret`. No row uses the laws (`comp_assoc`, `id_comp`, `comp_id`, `swap_swap`, ...) or
`interpret_eq_comp`. Every theorem of the
topic module is now proved (T46.3.1 through T46.3.4; no `sorry` in any value or proof since commit
`40a4d2c`/entry 2026-10-02b), so this step's axiom sweep below is unconditional, not merely modulo
a placeholder.

No row of 1–3 reproduces an example of the corpus paper; the cases are the framing note's
(`docs/framing/T46.md`, "The cases").

Frame form (D5): the rows compare amplitude functions on the free bits; no `FTQCLib.Hilbert`
object is named.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer
open Protocol

/-! ## Words appended and read back -/

/-- A word appended to the empty word, read through the cast `k = 0 + k`, is itself. -/
private theorem append_nil_comp_cast {α : Type*} {k : ℕ} (e : Fin 0 → α) (v : Fin k → α)
    (h : k = 0 + k) : Fin.append e v ∘ Fin.cast h = v := by
  funext i
  have hi : Fin.cast h i = Fin.natAdd 0 i := Fin.ext (by simp)
  rw [Function.comp_apply, hi, Fin.append_right]

/-- Reading a word through `Fin.natAdd 0` is reading it through the cast `0 + k = k`. -/
private theorem comp_natAdd_zero {α : Type*} {k : ℕ} (w : Fin (0 + k) → α) (h : k = 0 + k) :
    w ∘ Fin.natAdd 0 = w ∘ Fin.cast h := by
  funext i
  simp only [Function.comp_apply]
  congr 1
  exact Fin.ext (by simp)

/-! ## Row 1: CZ composed with itself -/

/-- The CZ word on two bits, at precision `1`. -/
noncomputable def czWord : GateWord 2 1 := [.diagonal (czGate 1 0 1)]

/-- **CZ as a morphism** `2 → 2`. -/
noncomputable def czHom : FrameCategory.Hom ⟨2⟩ ⟨2⟩ := FrameCategory.wordHom 2 1 czWord

/-- CZ's presentation at `(x, y)` is `(−1)^{y₀y₁}·δ_{y = x}`, by the word's referee. -/
theorem amp_czWordState (x y : Fin 2 → ZMod 2) :
    amp (wordState 2 1 czWord) (Fin.append x y)
      = (-1 : ℂ) ^ ((y 0).val * (y 1).val) * delta x y := by
  rw [amp_wordState 2 1 czWord le_rfl]
  show charOf 1 ((czGate 1 0 1).eval y) * delta x y = _
  rw [charOf_czGate_eval le_rfl]

-- row: agreement
/-- **CZ composed with itself is the identity on `2`.** The contraction
`Σ_y (−1)^{y₀y₁}δ_{y=x}·(−1)^{z₀z₁}δ_{z=y}` is `δ_{x=z}`, since `((−1)^k)² = 1`. -/
theorem czHom_comp_czHom : FrameCategory.comp czHom czHom = FrameCategory.id ⟨2⟩ := by
  unfold czHom FrameCategory.wordHom FrameCategory.id
  rw [FrameCategory.comp_toHom, FrameCategory.toHom_eq_toHom_iff]
  unfold StateEq
  rw [amp_comp, amp_idState]
  funext w
  dsimp only
  unfold contractAmp
  simp only [amp_czWordState]
  rw [Finset.sum_eq_single (w ∘ Fin.castAdd 2)]
  · simp only [delta]
    by_cases h : w ∘ Fin.castAdd 2 = w ∘ Fin.natAdd 2
    · rw [if_pos h.symm, if_pos h, ← h]
      simp only [↓reduceIte, mul_one]
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero, mul_zero]
  · intro b _ hb
    simp only [delta, if_neg hb, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Row 2: a two-letter protocol as the composite of its letters -/

/-- H on the one data bit, at precision `1`. -/
noncomputable def hWord : GateWord 1 1 := [.hadamard 0]

/-- `Z₀` on one bit. -/
def zZero : SignedPauli 1 := signedZ 0

/-- `Z₀` needs no precision above `1`. -/
theorem zZero_precision : yWeight zZero.pauli % 2 = 1 → 2 ≤ 1 := by
  rw [zZero, yWeight_signedZ]
  intro h
  exact absurd h (by decide)

/-- **The two-letter protocol**: H on bit `0`, then the conditioning on `Z₀`, at precision `1`. -/
noncomputable def twoLetterProtocol : Protocol 1 1 1 :=
  ((nil : Protocol 1 1 0).word hWord).condition zZero zZero_precision

/-- The H presentation at `(x, y)` is the Walsh transform at bit `0` of the point mass at `x`. -/
private theorem amp_hWordState (x y : Fin 1 → ZMod 2) :
    amp (wordState 1 1 hWord) (Fin.append x y) = walshTransform 0 (delta x) y :=
  amp_wordState 1 1 hWord le_rfl x y

/-- The `Z₀` presentation at `(x, v)` is `δ_{x = init v}` on the slice `(init v)₀ = v_last`. -/
private theorem amp_zZeroState (x : Fin 1 → ZMod 2) (v : Fin (1 + 1) → ZMod 2) :
    amp (conditionState 1 1 zZero) (Fin.append x v)
      = if Fin.init v 0 = v (Fin.last 1) then delta x (Fin.init v) else 0 := by
  have h := amp_conditionState 1 1 zZero x (Fin.init v) (v (Fin.last 1))
  rw [Fin.snoc_init_self] at h
  rw [h, zZero, pauliProjection_signedZ]

/-- The Walsh transform is linear: summed against the point masses it is the transform. -/
private theorem sum_mul_walshTransform_delta {N : ℕ} (k : Fin N) (s : (Fin N → ZMod 2) → ℂ)
    (u : Fin N → ZMod 2) :
    ∑ x : Fin N → ZMod 2, s x * walshTransform k (delta x) u = walshTransform k s u := by
  simp only [walshTransform, delta, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

-- row: agreement
/-- **A two-letter protocol is the composite of its letters.** On a carrier state `S` at the
protocol's precision, the class of `interpret twoLetterProtocol S` from `0` is `S` composed with
`[H]` and then `[Z₀]`. The left side is T14's `amp_interpret`; the right two contractions, each
summing a point mass against a linear referee. -/
theorem twoLetterProtocol_eq_comp {S : KernelSumState 1} (hS : IsCarrier S) (hm : S.m = 1) :
    FrameCategory.ofState (twoLetterProtocol.interpret S)
      = FrameCategory.comp
          (FrameCategory.comp (FrameCategory.ofState S) (FrameCategory.wordHom 1 1 hWord))
          (FrameCategory.conditionHom 1 1 zZero) := by
  unfold FrameCategory.ofState FrameCategory.wordHom FrameCategory.conditionHom
  rw [FrameCategory.comp_toHom, FrameCategory.comp_toHom, FrameCategory.toHom_eq_toHom_iff]
  unfold StateEq
  rw [amp_comp, amp_comp, amp_castBits, amp_castBits, (amp_interpret twoLetterProtocol hS hm).2]
  funext w
  dsimp only
  unfold contractAmp
  simp only [append_comp_natAdd, append_nil_comp_cast, amp_hWordState, amp_zZeroState,
    sum_mul_walshTransform_delta]
  rw [comp_natAdd_zero w (Nat.zero_add (1 + 1)).symm]
  show pauliProjection zZero _ (runAmp hWord (amp S)) _ = _
  rw [zZero, pauliProjection_signedZ]
  by_cases hc : Fin.init (w ∘ Fin.cast (Nat.zero_add (1 + 1)).symm) 0
      = (w ∘ Fin.cast (Nat.zero_add (1 + 1)).symm) (Fin.last 1)
  · simp only [hc, if_true, delta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ]
    rfl
  · simp only [hc, if_false, mul_zero, Finset.sum_const_zero]

-- row: inhabitation
/-- The hypotheses of row 2 hold together on `heightOneState`, a carrier state at precision `1`. -/
theorem twoLetterProtocol_eq_comp_heightOneState :
    FrameCategory.ofState (twoLetterProtocol.interpret heightOneState)
      = FrameCategory.comp
          (FrameCategory.comp (FrameCategory.ofState heightOneState)
            (FrameCategory.wordHom 1 1 hWord))
          (FrameCategory.conditionHom 1 1 zZero) :=
  twoLetterProtocol_eq_comp isCarrier_heightOneState heightOneState_m

/-! ## Row 3: the swapped identity -/

/-- The word `(0, 1)` on two bits. -/
def zeroOne : Fin (1 + 1) → ZMod 2 := ![0, 1]

/-- `(0, 1)` is not its own halves swapped. -/
private theorem zeroOne_ne_swap :
    zeroOne ≠ Fin.append (zeroOne ∘ Fin.natAdd 1) (zeroOne ∘ Fin.castAdd 1) := by
  intro h
  have h0 := congrFun h 0
  revert h0
  decide

-- row: discriminating
/-- **Composing with the swapped identity is not the identity**: at the input `(0, 1)` and the
output `(0, 1)` the identity on `1 + 1` composed with `swap ⟨1⟩ ⟨1⟩` has amplitude `0`, the
identity `1`. -/
theorem comp_swap_ne_id :
    FrameCategory.comp (FrameCategory.id (FrameCategory.tensorObj ⟨1⟩ ⟨1⟩))
        (FrameCategory.swap ⟨1⟩ ⟨1⟩)
      ≠ FrameCategory.id (FrameCategory.tensorObj ⟨1⟩ ⟨1⟩) := by
  unfold FrameCategory.id FrameCategory.swap
  rw [FrameCategory.comp_toHom, Ne, FrameCategory.toHom_eq_toHom_iff]
  intro h
  have hw := congrFun h (Fin.append zeroOne zeroOne)
  rw [amp_comp, amp_idState] at hw
  dsimp only [FrameCategory.tensorObj] at hw
  unfold contractAmp at hw
  simp only [append_comp_castAdd, append_comp_natAdd, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hw
  rw [amp_swapState] at hw
  simp only [← Function.comp_assoc, append_comp_castAdd, append_comp_natAdd,
    if_neg zeroOne_ne_swap] at hw
  exact zero_ne_one hw

/-! ## The mutant: the scale of a contracted pair -/

-- mutant: contractPair_scale | FTQCLib/Carrier/FrameCategory.lean
--   | scaleBy (Real.sqrt 2 : ℂ)
--   | scaleBy (Real.sqrt 3 : ℂ)

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.Obj.mk.inj' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.Obj.mk.inj

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.Obj.mk.injEq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.Obj.mk.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.Obj.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.Obj.mk.sizeOf_spec

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.associator_hom_inv_id' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.associator_hom_inv_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.associator_inv_hom_id' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.associator_inv_hom_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.associator_naturality' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.associator_naturality

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.braiding_naturality_left' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.braiding_naturality_left

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.braiding_naturality_right' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.braiding_naturality_right

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.comp_assoc' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.comp_assoc

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.comp_id' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.comp_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.comp_toHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.comp_toHom

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.hexagon_forward' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.hexagon_forward

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.hexagon_reverse' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.hexagon_reverse

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.id_comp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.id_comp

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.id_whiskerRight' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.id_whiskerRight

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.interpret_eq_comp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.interpret_eq_comp

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.leftUnitor_hom_inv_id' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.leftUnitor_hom_inv_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.leftUnitor_inv_hom_id' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.leftUnitor_inv_hom_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.leftUnitor_naturality' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.leftUnitor_naturality

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.ofState_inj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.ofState_inj

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.pentagon' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.pentagon

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.protocolHom_condition' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.protocolHom_condition

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.protocolHom_nil' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.protocolHom_nil

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.protocolHom_word' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.protocolHom_word

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.rightUnitor_hom_inv_id' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.rightUnitor_hom_inv_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.rightUnitor_inv_hom_id' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.rightUnitor_inv_hom_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.rightUnitor_naturality' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.rightUnitor_naturality

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.swap_hexagon' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.swap_hexagon

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.swap_natural' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.swap_natural

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.swap_swap' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.swap_swap

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensorHom_comp_tensorHom' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensorHom_comp_tensorHom

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensorHom_def' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensorHom_def

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensor_assoc' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensor_assoc

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensor_comp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensor_comp

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensor_id' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensor_id

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensor_id_left' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensor_id_left

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensor_id_right' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensor_id_right

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.tensor_toHom' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.tensor_toHom

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.toHom_eq_toHom_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.toHom_eq_toHom_iff

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.triangle' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.triangle

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.whiskerLeft_id' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.whiskerLeft_id

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_mul_scale' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ampCore_mul_scale

/-- info: 'FTQCLib.Frame.Walkthrough.amp_appendState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_appendState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_carrierRep' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_carrierRep

/-- info: 'FTQCLib.Frame.Walkthrough.amp_castBits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_castBits

/-- info: 'FTQCLib.Frame.Walkthrough.amp_comp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_comp

/-- info: 'FTQCLib.Frame.Walkthrough.amp_conditionState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_conditionState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_contractPair' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_contractPair

/-- info: 'FTQCLib.Frame.Walkthrough.amp_contractShared' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_contractShared

/-- info: 'FTQCLib.Frame.Walkthrough.amp_idState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_idState

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_idState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_idState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_reindexFreeBits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_reindexFreeBits

/-- info: 'FTQCLib.Frame.Walkthrough.amp_scaleBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_scaleBy

/-- info: 'FTQCLib.Frame.Walkthrough.amp_swapState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_swapState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_tensorState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_tensorState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_wordState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_wordState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_zeroState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_zeroState

/-- info: 'FTQCLib.Frame.Walkthrough.castBits_stateEq_congr' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.castBits_stateEq_congr

/-- info: 'FTQCLib.Frame.Walkthrough.comp_stateEq_congr' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.comp_stateEq_congr

/-- info: 'FTQCLib.Frame.Walkthrough.exists_carrier_of_amp_ne_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_carrier_of_amp_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_appendState' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_appendState

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_carrierRep' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_carrierRep

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_castBits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_castBits

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_comp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_comp

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_reindexFreeBits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_reindexFreeBits

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_scaleBy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_scaleBy

/-- info: 'FTQCLib.Frame.Walkthrough.reindexFreeBits_stateEq_congr' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.reindexFreeBits_stateEq_congr

/-- info: 'FTQCLib.Frame.Walkthrough.tensor_stateEq_congr' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.tensor_stateEq_congr

/-- info: 'FTQCLib.Frame.Walkthrough.map_xProj_shadowLagrangian' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.map_xProj_shadowLagrangian

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_shadowLagrangian' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isStabilizer_shadowLagrangian

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_shadowLagrangian_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_shadowLagrangian_le

end FTQCLib.Frame.Walkthrough

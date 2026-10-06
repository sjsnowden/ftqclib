/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierRules
import FTQCLib.Explore.CyclotomicKernelB

/-!
# Check: `CarrierRule` on the (HH) witness, a non-dyadic pair, and one instance per constructor

T06's witness (`docs/STEPS.md`, "The unit", phase 2): rows that test the frozen statement of
`FTQCLib/Carrier/CarrierRules.lean` on small cases.

* **Agreement.** `HHWitness.hhState` (`FTQCLib/Explore/CyclotomicKernelB.lean`) is related to
  `HHWitness.tState` by a chain of `CarrierRule` steps: one flip (`flip_derivable`, on the last
  bound bit, by a bit that reads only the free word), one halving (antipodal on the two words with
  that bit `0`), one collapse (the remaining bit's difference is identically zero). The chain's
  scale returns to `1`: the flip keeps it, the halving divides by `√2`, the collapse multiplies by
  `√2` back.
* **Discriminating.** Two `m = 1` records whose scale ratio is `3`, so a nonzero multiple of the
  amplitude `1/√2` — not a dyadic ratio (`IsDyadicRatio`), since its modulus squared is `9/2`, never
  an integer power of two, so no `CarrierRule` step (`exists_isDyadicRatio_of_carrierRule`) joins
  them.
* **Inhabitation.** One instance of each constructor of `CarrierRule` (`gauge`, `collapse`,
  `rotate`, `rephase`, `halve`, `copy`), drawn from the agreement row's witness and from
  `EliminationOrderCheck.lean`'s and `PrecisionGaugeCheck.lean`'s own small cases where a fresh one
  is simpler to build than a citation.

## Implementation notes

`DiagPhase.eval` is noncomputable (`MvPolynomial.eval`); every finite side condition is closed by
rewriting it away with `eval_add`, `eval_mul`, `eval_C`, `eval_X` (and the local `eval_sub'` for
subtraction) and then `decide` over the finitely many words, following
`FTQCLib/Explore/CyclotomicKernelB.lean`'s `HHWitness` proofs.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer
open FTQCLib.Explore.CyclotomicKernelB.HHWitness (qHH hhState tState lagX lagX_support amp_tState)

/-- `DiagPhase.eval` on a difference (not stated in `Defs.lean`, only additivity). -/
theorem eval_sub' {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    DiagPhase.eval (A - B) v = DiagPhase.eval A v - DiagPhase.eval B v := by
  simp [DiagPhase.eval]

/-! ## Agreement: one flip, one halving, one collapse from the (HH) witness to the T state -/

section Agreement

/-- The bit `1 ⊕ w₀`, read off the free word alone, in the shape a copy-gadget flip needs (a
function of the free word and the bound bits other than the one flipped — here it uses none of
them). -/
def flipBit : (Fin 1 → ZMod 2) → (Fin 2 → ZMod 2) → ZMod 2 := fun w _ => 1 + w 0

/-- `flipBit` does not read the bound bit it flips (bit `1`): it reads no bound bit at all. -/
theorem flipBit_indep (w : Fin 1 → ZMod 2) (y : Fin 2 → ZMod 2) (b : ZMod 2) :
    flipBit w (Function.update y 1 b) = flipBit w y := rfl

/-- The value bit `1` is flipped to, as a `ZMod 8` polynomial in `w₀` and the old bit `y₁`: the
XOR `y₁ ⊕ (1 ⊕ w₀)` written as `y₁ + (1 ⊕ w₀) − 2·y₁·(1 ⊕ w₀)` over `{0, 1}`, with `1 ⊕ w₀` itself
written `1 − w₀`. -/
noncomputable def flipTarget : DiagPhase (1 + 2) 3 :=
  MvPolynomial.C 1 - MvPolynomial.X 0 - MvPolynomial.X 2
    + MvPolynomial.C 2 * MvPolynomial.X 2 * MvPolynomial.X 0

/-- `qHH` with bit `1` (`y₁`) flipped by `flipBit`: `qHH`'s own shape with `y₁` read through
`flipTarget`. -/
noncomputable def qHH1 : DiagPhase (1 + 2) 3 :=
  MvPolynomial.C 4 * MvPolynomial.X 1 * (flipTarget + MvPolynomial.X 0) + flipTarget

/-- **The flip's defining equation.** `qHH1` at `(w, y)` is `qHH` at `(w, y)` with `y₁` moved by
`flipBit w y`, for every `w` and `y` — the hypothesis `flip_derivable` needs, checked over all
`8` free-word/bound-word pairs. -/
theorem qHH1_eq_flip (w : Fin 1 → ZMod 2) (y : Fin 2 → ZMod 2) :
    qHH1.eval (Fin.append w y)
      = qHH.eval (Fin.append w (Function.update y 1 (y 1 + flipBit w y))) := by
  simp only [qHH1, flipTarget, qHH, flipBit, DiagPhase.eval_add, eval_sub', DiagPhase.eval_mul,
    DiagPhase.eval_C, DiagPhase.eval_X]
  revert w y
  decide

/-- **One flip.** `qHH1`'s state is related to `hhState` by a chain of `CarrierRule` steps that
never leaves precision `3`, Lagrangian `lagX`, and `hhState`'s denotation. -/
theorem step_flip :
    Relation.EqvGen
      (CarrierRuleWithin fun A => A.m = 3 ∧ A.L = lagX ∧ StateEq A hhState)
      (⟨3, 2, qHH1, 1, lagX, 0⟩ : KernelSumState 1) hhState :=
  flip_derivable qHH qHH1 1 lagX 0 1 flipBit
    (fun w _ y b => flipBit_indep w y b) (fun w _ y => qHH1_eq_flip w y)

/-- The reduct after the flip, on the one bound bit `y₀` kept (`y₁` fixed to `1`): the constant
`X 0` — table-checked, `qHH1` at `y₁ = 1` reads off `w₀` alone. -/
noncomputable def qHalved : DiagPhase (1 + 1) 3 := MvPolynomial.X 0

/-- The embedding of the one-bit words into the two-bit words, fixing `y₁ = 1`: the kept half of
the halving. -/
noncomputable def keepEmbed : (Fin 1 → ZMod 2) ↪ (Fin 2 → ZMod 2) where
  toFun y := Fin.snoc y 1
  inj' y y' h := by
    have h0 := congrFun h 0
    funext i
    fin_cases i
    simpa using h0

/-- The pair `y₁ = 0` removes: the complement of `keepEmbed`'s image. -/
noncomputable def keepComplement : Finset (Fin 2 → ZMod 2) := {![0, 0], ![1, 0]}

/-- The pairing of `keepComplement`, swapping the free bit `y₀` and fixing `y₁ = 0`. -/
noncomputable def keepSwap : Equiv.Perm (Fin 2 → ZMod 2) := Equiv.swap ![0, 0] ![1, 0]

/-- **`keepComplement` is exactly what `keepEmbed` misses.** -/
theorem hP_keep : ∀ y' : Fin 2 → ZMod 2, y' ∈ keepComplement ↔ ∀ y, keepEmbed y ≠ y' := by
  decide

/-- **The halved reduct agrees with `qHH1` read through `keepEmbed`.** Table-checked: `qHH1` at
`y₁ = 1` is `w₀`, independent of `y₀`. -/
theorem hQ'_keep (w : Fin 1 → ZMod 2) (y : Fin 1 → ZMod 2) :
    qHalved.eval (Fin.append w y) = qHH1.eval (Fin.append w (keepEmbed y)) := by
  simp only [qHalved, qHH1, flipTarget, DiagPhase.eval_add, eval_sub', DiagPhase.eval_mul,
    DiagPhase.eval_C, DiagPhase.eval_X, keepEmbed]
  revert w y
  decide

/-- **`keepComplement`'s pairing is antipodal for `qHH1`, at both free words.** Table-checked. -/
theorem hpair_keep (w : Fin 1 → ZMod 2) : AntipodalOn qHH1 w keepComplement keepSwap := by
  refine ⟨by decide, fun y hy => ?_⟩
  fin_cases hy <;>
    · simp only [qHH1, flipTarget, keepSwap, DiagPhase.eval_add, eval_sub', DiagPhase.eval_mul,
        DiagPhase.eval_C, DiagPhase.eval_X]
      revert w
      decide

/-- **One halving.** `qHH1`'s state, height two, steps to `qHalved`'s state, height one, scale
divided by `√2`. -/
theorem step_halve :
    CarrierRule (⟨3, 2, qHH1, 1, lagX, 0⟩ : KernelSumState 1)
      (⟨3, 1, qHalved, 1 / (Real.sqrt 2 : ℂ), lagX, 0⟩ : KernelSumState 1) :=
  CarrierRule.halve (by norm_num) qHH1 qHalved 1 lagX 0 keepEmbed keepComplement keepSwap
    hP_keep (fun w _ y => hQ'_keep w y) (fun w _ => hpair_keep w)

/-- The dot product with the zero vector is zero. -/
theorem dotF2_zero_left_one (w : Fin 1 → ZMod 2) : dotF2 (0 : Fin 1 → ZMod 2) w = 0 := by
  simp [dotF2]

/-- **`qHalved`'s last bit has no difference.** It does not read the bound bit at all. -/
theorem hsign_keep :
    SignAffine (n := 1) (h := 0) (m := 3) qHalved lagX (0 : Fin 1 → ZMod 2)
      (0 : Fin 1 → ZMod 2) 0 := by
  intro w hw y
  clear hw
  simp only [qHalved, lastDiff_eval, DiagPhase.eval_X, dotF2_zero_left_one]
  revert w y
  decide

/-- **The collapse's support is unchanged**: `ε + ⟨σ, w⟩ = 0` always holds at `σ = 0`, `ε = 0`. -/
theorem hsupp_keep : ∀ w : Fin 1 → ZMod 2,
    (∃ p ∈ lagX, w = (0 : Fin 1 → ZMod 2) + p.X)
      ↔ (∃ p ∈ lagX, w = (0 : Fin 1 → ZMod 2) + p.X) ∧ (0 : ZMod 2) + dotF2 0 w = 0 := by
  intro w
  rw [dotF2_zero_left_one]
  simp

/-- The reduct after the collapse: height zero, `snocFreeze 0 qHalved`. -/
noncomputable def finalState : KernelSumState 1 :=
  elimCollapse (h := 0) qHalved (1 / (Real.sqrt 2 : ℂ)) lagX 0

/-- **One collapse.** `qHalved`'s state, height one, steps to `finalState`, height zero, scale
times `√2`. -/
theorem step_collapse :
    CarrierRule (⟨3, 1, qHalved, 1 / (Real.sqrt 2 : ℂ), lagX, 0⟩ : KernelSumState 1) finalState :=
  CarrierRule.collapse (n := 1) (h := 0) (m := 3) (by norm_num) qHalved
    (1 / (Real.sqrt 2 : ℂ)) lagX 0 0 0 hsign_keep lagX 0 hsupp_keep

/-- `√2 · (1/√2) = 1`. -/
theorem sqrt_two_mul_inv : (Real.sqrt 2 : ℂ) * (1 / (Real.sqrt 2 : ℂ)) = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
  field_simp

/-- The frozen last bit of `Fin.snoc w 0` at index `0` is `w 0`: the frozen bit does not move the
kept coordinate. -/
theorem snoc_zero_apply_zero (w : Fin 1 → ZMod 2) : (Fin.snoc w (0 : ZMod 2) : Fin 2 → ZMod 2) 0
    = w 0 := by
  simp [Fin.snoc]

/-- **The chain's endpoint agrees with the T state.** `finalState`'s amplitude is exactly
`tState`'s: `charOf 3` of the free bit. -/
theorem amp_finalState (w : Fin 1 → ZMod 2) :
    amp finalState w = charOf 3 ((w 0).val : ZMod (2 ^ 3)) := by
  rw [amp_pos (lagX_support w)]
  change ampCore 3 0 (snocFreeze 0 qHalved) ((Real.sqrt 2 : ℂ) * (1 / (Real.sqrt 2 : ℂ))) w = _
  rw [ampCore_eq_sum_charOf, Fintype.sum_unique, pow_zero, div_one, append_fin0, snocFreeze_eval]
  rw [show qHalved.eval (Fin.snoc w (0 : ZMod 2)) = ((w 0).val : ZMod (2 ^ 3)) from by
    rw [qHalved, DiagPhase.eval_X, snoc_zero_apply_zero], sqrt_two_mul_inv, one_mul]

/-- **Agreement.** `hhState` (`HHWitness`'s `(HH)` witness) is related to `tState` by a chain of
`CarrierRule` steps: one flip, one halving, one collapse — and the chain's endpoint denotes exactly
`tState`'s state. -/
-- row: agreement
theorem hh_to_t_agreement :
    Relation.EqvGen
        (CarrierRuleWithin fun A => A.m = 3 ∧ A.L = lagX ∧ StateEq A hhState)
        (⟨3, 2, qHH1, 1, lagX, 0⟩ : KernelSumState 1) hhState
      ∧ CarrierRule (⟨3, 2, qHH1, 1, lagX, 0⟩ : KernelSumState 1)
          (⟨3, 1, qHalved, 1 / (Real.sqrt 2 : ℂ), lagX, 0⟩ : KernelSumState 1)
      ∧ CarrierRule (⟨3, 1, qHalved, 1 / (Real.sqrt 2 : ℂ), lagX, 0⟩ : KernelSumState 1) finalState
      ∧ StateEq finalState tState :=
  ⟨step_flip, step_halve, step_collapse,
    funext fun w => (amp_finalState w).trans (amp_tState w).symm⟩

end Agreement

/-! ## Discriminating: a scale ratio that is not dyadic joins no step -/

section Discriminating

/-- One free bit, height zero, precision one, scale `1`: amplitude `1`. -/
noncomputable def onePair : KernelSumState 0 := ⟨1, 0, 0, 1, ⊤, 0⟩

/-- The same shape, scale `1 · 3`: amplitude `3` — read as `3/√2` if height one, `√2 · 3/√2` the
same ratio; the ratio tested is the scale, `3`, not folded into a particular presentation. -/
noncomputable def triplePair : KernelSumState 0 := ⟨1, 0, 0, (3 : ℂ) / (Real.sqrt 2 : ℂ), ⊤, 0⟩

/-- Every word on zero free bits is on the support of `⊤`. -/
theorem mem_support_top_zero (w : Fin 0 → ZMod 2) :
    ∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 0)), w = (0 : Fin 0 → ZMod 2) + p.X :=
  ⟨0, Submodule.mem_top, Subsingleton.elim _ _⟩

/-- **Discriminating.** `triplePair`'s scale is `3` times `onePair`'s; `3` is not a dyadic ratio
(`‖3‖² = 9`, not `‖3/√2‖`'s own `9/2` — the ratio is `triplePair.c / onePair.c = 3/√2`, and
`‖3/√2‖² = 9/2` is not an integer power of two), so no `CarrierRule` step joins them: the theorem
`exists_isDyadicRatio_of_carrierRule` would hand back a dyadic ratio equal to `3/√2`. -/
-- row: discriminating
theorem no_step_joins_scale_ratio : ¬ CarrierRule onePair triplePair := by
  intro hstep
  obtain ⟨r, hr, hc⟩ := exists_isDyadicRatio_of_carrierRule hstep
  obtain ⟨e, he⟩ := sq_norm_eq_zpow_of_isDyadicRatio hr
  apply nine_div_two_ne_zpow e
  rw [← he]
  have hcr : r = (3 : ℂ) / (Real.sqrt 2 : ℂ) := by
    have heq : triplePair.c = r * onePair.c := hc
    simp only [onePair, triplePair, mul_one] at heq
    exact heq.symm
  rw [hcr, norm_div, show ‖(3 : ℂ)‖ = 3 from by norm_num,
    show ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)],
    div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end Discriminating

/-! ## Inhabitation: one instance of each constructor -/

section Inhabitation

/-- The trivial gauge rewrite R4 (`congrSupport`) at the zero state on no free bits: its own
exponent equal to itself, the hypothesis `rfl`. -/
theorem gaugeStep_trivial :
    GaugeStep (n := 0) (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0)
      (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) :=
  GaugeStep.congrSupport 0 0 1 ⊤ 0 (fun _ _ _ => rfl)

/-- **Gauge.** One instance of `CarrierRule.gauge`. -/
theorem carrierRule_gauge :
    CarrierRule (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) :=
  CarrierRule.gauge gaugeStep_trivial

/-- **Rephase.** One instance of `CarrierRule.rephase`, at the trivial pairing set `P = ∅` (both
conjuncts of `AntipodalOn` hold vacuously, and the "off `P`" condition is everywhere). -/
theorem carrierRule_rephase :
    CarrierRule (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) :=
  CarrierRule.rephase (n := 0) (h := 0) (m := 1) (by norm_num) 0 0 1 ⊤ 0 ∅ (Equiv.refl _)
    (Equiv.refl _) (fun _ _ _ _ => rfl)
    (fun _ _ => ⟨by simp, fun y hy => absurd hy (by simp)⟩)
    (fun _ _ => ⟨by simp, fun y hy => absurd hy (by simp)⟩)

/-- The rotate shape's exponent: the single bound bit itself, at precision `2`. -/
noncomputable def qRotateShape : DiagPhase (0 + 0 + 1) 2 := MvPolynomial.X 0

/-- The rotate shape's affine bit: the constant `0`. -/
noncomputable def lamRotate : DiagPhase (0 + 0) 2 := 0

/-- **`qRotateShape`'s data satisfies the rotate shape** at `a = 1` (`2 · 1 = 2 = 2^{2-1}` in
`ZMod 4`): the difference along the sole bound bit is the constant `1`, and `lamRotate` is the
constant bit `0`. -/
theorem rotateData_trivial :
    RotateData (n := 0) (h := 0) qRotateShape (⊤ : Submodule (ZMod 2) (Pauli 0)) 0 (1 : ZMod (2 ^ 2))
      lamRotate := by
  refine ⟨by decide, fun w hw y => ⟨0, ?_, ?_⟩⟩
  · simp [lamRotate, DiagPhase.eval]
  · clear hw
    simp only [qRotateShape, lastDiff_eval, DiagPhase.eval_X]
    revert w y
    decide

/-- **Rotate.** One instance of `CarrierRule.rotate`. -/
theorem carrierRule_rotate :
    CarrierRule (n := 0) (⟨2, 0 + 1, qRotateShape, 1, ⊤, 0⟩ : KernelSumState 0)
      (elimRotate qRotateShape (1 : ZMod (2 ^ 2)) lamRotate 1 ⊤ 0) :=
  CarrierRule.rotate (n := 0) (h := 0) (m := 2) (by norm_num) qRotateShape 1
    (⊤ : Submodule (ZMod 2) (Pauli 0)) 0 1 lamRotate rotateData_trivial ⊤ 0 (fun _ => Iff.rfl)

/-- The copy shape's exponent: `t · z` at precision `1` (`2^{1-1} = 1`), the two fresh bound bits
`z = X 0`, `t = X 1`, no free bits and no other bound bits. -/
noncomputable def qCopy : DiagPhase (0 + (0 + 1 + 1)) 1 := MvPolynomial.X 1 * MvPolynomial.X 0

/-- The copy's `P`, constantly `0`. -/
def pCopy : (Fin 0 → ZMod 2) → (Fin 0 → ZMod 2) → ZMod 2 := fun _ _ => 0

/-- **The copy shape holds for `qCopy`.** Table-checked over the four bit values. -/
theorem copy_hQ : ∀ w : Fin 0 → ZMod 2, (∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 0)), w = 0 + p.X) →
    ∀ (y : Fin 0 → ZMod 2) (z t : ZMod 2),
      qCopy.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t))
        = qCopy.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0))
          + (2 : ZMod (2 ^ 1)) ^ (1 - 1) * (((t * (z + pCopy w y)).val : ℕ) : ZMod (2 ^ 1)) := by
  intro w hw y z t
  clear hw
  simp only [qCopy, pCopy, DiagPhase.eval_mul, DiagPhase.eval_X]
  revert w y z t
  decide

/-- **The copy's reduct is the zero polynomial** (no bound bits left, no free bits). -/
theorem copy_hQ' : ∀ w : Fin 0 → ZMod 2, (∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli 0)), w = 0 + p.X) →
    ∀ y : Fin 0 → ZMod 2, (0 : DiagPhase (0 + 0) 1).eval (Fin.append w y)
      = qCopy.eval (Fin.append w (Fin.snoc (Fin.snoc y (pCopy w y)) 0)) := by
  intro w hw y
  clear hw
  simp only [qCopy, pCopy, eval_zero_poly, DiagPhase.eval_mul, DiagPhase.eval_X]
  revert w y
  decide

/-- **Copy.** One instance of `CarrierRule.copy`. -/
theorem carrierRule_copy :
    CarrierRule (n := 0) (⟨1, 0 + 1 + 1, qCopy, 1, ⊤, 0⟩ : KernelSumState 0)
      (⟨1, 0, (0 : DiagPhase (0 + 0) 1), 1, ⊤, 0⟩ : KernelSumState 0) :=
  CarrierRule.copy (n := 0) (h := 0) (m := 1) (by norm_num) qCopy 0 1
    (⊤ : Submodule (ZMod 2) (Pauli 0)) 0 pCopy copy_hQ copy_hQ'

/-- **Inhabitation.** One instance of each of `CarrierRule`'s six constructors: `gauge`,
`collapse` and `halve` (from the agreement row above), `rephase`, `rotate`, `copy`. -/
-- source: papers/tensor_network_simulation/
-- Vilmart_2023_sop_toffoli_hadamard_dyadic_complete_2205.02600 equation:h939465430480
-- row: inhabitation
theorem carrierRule_constructors_inhabited :
    CarrierRule (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0)
      ∧ CarrierRule (⟨3, 2, qHH1, 1, lagX, 0⟩ : KernelSumState 1)
          (⟨3, 1, qHalved, 1 / (Real.sqrt 2 : ℂ), lagX, 0⟩ : KernelSumState 1)
      ∧ CarrierRule (⟨3, 1, qHalved, 1 / (Real.sqrt 2 : ℂ), lagX, 0⟩ : KernelSumState 1) finalState
      ∧ CarrierRule (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0) (⟨1, 0, 0, 1, ⊤, 0⟩ : KernelSumState 0)
      ∧ CarrierRule (n := 0) (⟨2, 0 + 1, qRotateShape, 1, ⊤, 0⟩ : KernelSumState 0)
          (elimRotate qRotateShape (1 : ZMod (2 ^ 2)) lamRotate 1 ⊤ 0)
      ∧ CarrierRule (n := 0) (⟨1, 0 + 1 + 1, qCopy, 1, ⊤, 0⟩ : KernelSumState 0)
          (⟨1, 0, (0 : DiagPhase (0 + 0) 1), 1, ⊤, 0⟩ : KernelSumState 0) :=
  ⟨carrierRule_gauge, step_halve, step_collapse, carrierRule_rephase, carrierRule_rotate,
    carrierRule_copy⟩

end Inhabitation

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.stateEq_of_carrierRule' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_carrierRule

/-- info: 'FTQCLib.Frame.Walkthrough.exists_isDyadicRatio_of_carrierRule' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_isDyadicRatio_of_carrierRule

/-- info: 'FTQCLib.Frame.Walkthrough.flip_derivable' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flip_derivable

/-- info: 'FTQCLib.Frame.Walkthrough.relabel_derivable' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relabel_derivable

/-- info: 'FTQCLib.Frame.Walkthrough.isDyadicRatio_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isDyadicRatio_one

/-- info: 'FTQCLib.Frame.Walkthrough.isDyadicRatio_sqrt_two_zpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isDyadicRatio_sqrt_two_zpow

/-- info: 'FTQCLib.Frame.Walkthrough.IsDyadicRatio.ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.IsDyadicRatio.ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.IsDyadicRatio.mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.IsDyadicRatio.mul

/-- info: 'FTQCLib.Frame.Walkthrough.IsDyadicRatio.inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.IsDyadicRatio.inv

/-- info: 'FTQCLib.Frame.Walkthrough.not_isDyadicRatio_two_fifths' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.not_isDyadicRatio_two_fifths

/-- info: 'FTQCLib.Frame.Walkthrough.sq_norm_eq_zpow_of_isDyadicRatio' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sq_norm_eq_zpow_of_isDyadicRatio

/-- info: 'FTQCLib.Frame.Walkthrough.nine_div_two_ne_zpow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.nine_div_two_ne_zpow

/-- info: 'FTQCLib.Frame.Walkthrough.exists_isDyadicRatio_of_eqvGen' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_isDyadicRatio_of_eqvGen

end FTQCLib.Frame.Walkthrough

-- mutant: dyadic_ratio_order | FTQCLib/Carrier/CarrierRules.lean | ζ ^ 2 ^ k = 1 | ζ ^ 2 ^ k = 0

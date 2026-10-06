/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PropCompleteness
import FTQCLib.Carrier.FrameCategoryCheck

/-!
# Check: T47, completeness of the frame's equational theory as a PROP

Rows on the frozen statement of `PropCompleteness.lean` (`docs/STEPS.md`, T47.2). Every row is
about morphisms of T46's PROP (`FrameCategory.toHom`, `FrameCategory.Hom`), the object
`prop_complete` names, and is computed from the amplitude referees (`amp_idState`, `amp_wordState`,
`ampCore_eq_sum_charOf`) and from explicit `CarrierRule` steps. No row uses `prop_complete`,
`prop_conservative`, `rewrite_complete` or `rewrite_conservative`.

* **Agreement.** Two presentations of CZ as a morphism `2 → 2`, at precision `1`, height `0`, on
  the identity's Lagrangian: `czIn`, the phase `(−1)^{x₀x₁}` read on the input bits, and `czOut`,
  the phase `(−1)^{y₀y₁}` read on the output bits. Each is computed to be T46's own CZ
  morphism (`czHom`, the word `[CZ₀₁]`, `FrameCategoryCheck.lean`), and one R4 step
  (`GaugeStep.congrSupport`: on the support `x = y` the two exponents agree) relates them. Both
  sides of `prop_complete`'s equivalence hold on this pair, each found without the other.
* **Discriminating.** Decision D9's pair as morphisms `⟨0⟩ → ⟨0⟩`: `d9Cubic`, the exponent
  `y₀y₁y₂` at height `3`, scale `1`, precision `1`, and `d9Flat`, height `0`, scale `3/√2`. They
  are one morphism (amplitude `6/√2³ = 3/√2` on both), and no chain of `CarrierRule` steps relates
  them: every chain multiplies the scale by a dyadic ratio (`exists_isDyadicRatio_of_eqvGen`,
  `CarrierRules.lean`) and `‖3/√2‖² = 9/2` is not a power of two (`nine_div_two_ne_zpow`).
  This tells `prop_complete` from the nearest wrong statement, the one without
  `IsDyadicRatio (G.c / F.c)`.
* **Inhabitation.** `prop_complete`'s hypotheses hold together on `czIn` and `czOut`: `czIn`'s
  amplitude is nonzero (it is `1` at the zero word) and the ratio of scales is `1`.

No row reproduces an example of the corpus papers; the pair of the discriminating row is D9's
(`docs/TARGETS.md`, decisions).

Frame form (D5): the rows compare amplitude functions on the free bits; no `FTQCLib.Hilbert`
object is named.
-/

namespace FTQCLib.Frame.Walkthrough

namespace PropCompletenessCheck

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## CZ on two bits, read on either half -/

/-- CZ's phase on the free bits `i` and `j` of a morphism `2 → 2`, at precision `1` and height `0`,
on the identity's Lagrangian: the identity times `(−1)^{w_i w_j}`. -/
noncomputable def czAt (i j : Fin (2 + 2)) : KernelSumState (2 + 2) :=
  ⟨1, 0, DiagPhase.czGate 1 (Fin.castAdd 0 i) (Fin.castAdd 0 j), 1, idL 2, 0⟩

/-- CZ read on the input bits `x₀`, `x₁`. -/
noncomputable def czIn : KernelSumState (2 + 2) := czAt 0 1

/-- CZ read on the output bits `y₀`, `y₁`. -/
noncomputable def czOut : KernelSumState (2 + 2) := czAt 2 3

/-- On the identity's support, `czAt i j` has the identity's raw amplitude times the phase. -/
private theorem ampCore_czAt (i j : Fin (2 + 2)) (w : Fin (2 + 2) → ZMod 2) :
    ampCore (czAt i j).m (czAt i j).h (czAt i j).Q (czAt i j).c w
      = (-1 : ℂ) ^ ((w i).val * (w j).val) := by
  rw [ampCore_eq_sum_charOf]
  change ((1 : ℂ) / (Real.sqrt 2 : ℂ) ^ 0)
      * ∑ y : Fin 0 → ZMod 2,
          charOf 1 ((DiagPhase.czGate 1 (Fin.castAdd 0 i) (Fin.castAdd 0 j)).eval
            (Fin.append w y)) = _
  rw [Finset.univ_unique, Finset.sum_singleton, charOf_czGate_eval le_rfl, Fin.append_left,
    Fin.append_left, pow_zero, div_one, one_mul]

/-- **The amplitude of `czAt i j`**: the identity's amplitude times `(−1)^{w_i w_j}`. -/
private theorem amp_czAt (i j : Fin (2 + 2)) (w : Fin (2 + 2) → ZMod 2) :
    amp (czAt i j) w = amp (idState 2) w * (-1 : ℂ) ^ ((w i).val * (w j).val) := by
  by_cases hw : ∃ p ∈ idL 2, w = 0 + p.X
  · rw [amp_pos (S := czAt i j) hw, amp_pos (S := idState 2) hw, ampCore_czAt]
    have h1 : ampCore (idState 2).m (idState 2).h (idState 2).Q (idState 2).c w = 1 := by
      have h := amp_pos (S := idState 2) hw
      have hs : w ∘ Fin.castAdd 2 = w ∘ Fin.natAdd 2 := by
        obtain ⟨p, hp, rfl⟩ := hw
        funext k
        simp only [Function.comp_apply, zero_add]
        exact (hp k).1
      simp only [amp_idState, if_pos hs] at h
      exact h.symm
    rw [h1, one_mul]
  · rw [amp_neg (S := czAt i j) hw, amp_neg (S := idState 2) hw, zero_mul]

/-- The identity's amplitude at `(x, y)` is `δ_{y = x}`. -/
private theorem amp_idState_two (x y : Fin 2 → ZMod 2) :
    amp (idState 2) (Fin.append x y) = delta x y := by
  rw [amp_idState]
  simp only [append_comp_castAdd, append_comp_natAdd]
  unfold delta
  by_cases h : y = x
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

/-- `czOut` is T46's CZ morphism. -/
theorem toHom_czOut : FrameCategory.toHom (a := ⟨2⟩) (b := ⟨2⟩) czOut = czHom := by
  unfold czHom FrameCategory.wordHom
  rw [FrameCategory.toHom_eq_toHom_iff]
  funext w
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin 2 → ZMod 2, w = Fin.append x y :=
    ⟨_, _, (Fin.append_castAdd_natAdd (f := w)).symm⟩
  change amp czOut (Fin.append x y) = amp (wordState 2 1 czWord) (Fin.append x y)
  rw [czOut, amp_czAt, amp_czWordState, amp_idState_two]
  have h2 : (Fin.append x y : Fin (2 + 2) → ZMod 2) 2 = y 0 := Fin.append_right x y 0
  have h3 : (Fin.append x y : Fin (2 + 2) → ZMod 2) 3 = y 1 := Fin.append_right x y 1
  rw [h2, h3, mul_comm]

/-- `czIn` is T46's CZ morphism: on the support `y = x` its phase `(−1)^{x₀x₁}` is `(−1)^{y₀y₁}`. -/
theorem toHom_czIn : FrameCategory.toHom (a := ⟨2⟩) (b := ⟨2⟩) czIn = czHom := by
  unfold czHom FrameCategory.wordHom
  rw [FrameCategory.toHom_eq_toHom_iff]
  funext w
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin 2 → ZMod 2, w = Fin.append x y :=
    ⟨_, _, (Fin.append_castAdd_natAdd (f := w)).symm⟩
  change amp czIn (Fin.append x y) = amp (wordState 2 1 czWord) (Fin.append x y)
  rw [czIn, amp_czAt, amp_czWordState, amp_idState_two]
  have h0 : (Fin.append x y : Fin (2 + 2) → ZMod 2) 0 = x 0 := Fin.append_left x y 0
  have h1 : (Fin.append x y : Fin (2 + 2) → ZMod 2) 1 = x 1 := Fin.append_left x y 1
  rw [h0, h1, mul_comm]
  unfold delta
  by_cases h : y = x
  · rw [if_pos h, h]
  · rw [if_neg h, mul_zero, mul_zero]

/-- **One R4 step from `czIn` to `czOut`.** On the identity's support `x = y`, so the exponents
`x₀x₁` and `y₀y₁` agree there. -/
theorem carrierRule_czIn_czOut : CarrierRule czIn czOut := by
  refine CarrierRule.gauge (GaugeStep.congrSupport _ _ 1 (idL 2) 0 ?_)
  rintro w ⟨p, hp, rfl⟩ y
  rw [DiagPhase.czGate_eval, DiagPhase.czGate_eval, Fin.append_left, Fin.append_left,
    Fin.append_left, Fin.append_left]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add]
  rw [show (0 : Fin (2 + 2)) = Fin.castAdd 2 0 from rfl, show (1 : Fin (2 + 2)) = Fin.castAdd 2 1
    from rfl, show (2 : Fin (2 + 2)) = Fin.natAdd 2 0 from rfl,
    show (3 : Fin (2 + 2)) = Fin.natAdd 2 1 from rfl, (hp 0).1, (hp 1).1]

/-- **Agreement.** Two presentations of CZ, its phase read on the input bits and on the output
bits, are each T46's CZ morphism, computed on amplitudes, and one `CarrierRule` step relates them:
both sides of `prop_complete`'s equivalence hold, found independently. -/
-- row: agreement
theorem cz_presentations_agreement :
    FrameCategory.toHom (a := ⟨2⟩) (b := ⟨2⟩) czIn = czHom
      ∧ FrameCategory.toHom (a := ⟨2⟩) (b := ⟨2⟩) czOut = czHom
      ∧ Relation.EqvGen CarrierRule czIn czOut :=
  ⟨toHom_czIn, toHom_czOut, Relation.EqvGen.rel _ _ carrierRule_czIn_czOut⟩

/-! ## D9's pair: one morphism, no chain -/

/-- The exponent `y₀y₁y₂` on three bound bits and no free bits. -/
noncomputable def cubicExponent : DiagPhase (0 + 0 + 3) 1 :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2

/-- **D9's height-three state**, a morphism `⟨0⟩ → ⟨0⟩`: exponent `y₀y₁y₂`, scale `1`,
precision `1`. -/
noncomputable def d9Cubic : KernelSumState (0 + 0) := ⟨1, 3, cubicExponent, 1, ⊤, 0⟩

/-- **D9's height-zero state**, a morphism `⟨0⟩ → ⟨0⟩`: scale `3/√2`, no bound bits. -/
noncomputable def d9Flat : KernelSumState (0 + 0) :=
  ⟨1, 0, 0, (3 : ℂ) / (Real.sqrt 2 : ℂ), ⊤, 0⟩

/-- Every word is on the support of `⊤`. -/
private theorem mem_support_top (w : Fin (0 + 0) → ZMod 2) :
    ∃ p ∈ (⊤ : Submodule (ZMod 2) (Pauli (0 + 0))), w = (0 : Fin (0 + 0) → ZMod 2) + p.X :=
  ⟨0, Submodule.mem_top, funext fun i => (Nat.not_lt_zero _ i.isLt).elim⟩

/-- The character of `y₀y₁y₂` at precision `1` is `(−1)^{y₀y₁y₂}`. -/
private theorem charOf_cubicExponent (v : Fin (0 + 0 + 3) → ZMod 2) :
    charOf 1 (cubicExponent.eval v) = (-1 : ℂ) ^ ((v 0).val * (v 1).val * (v 2).val) := by
  have h := charOf_two_pow_mul (m := 1) le_rfl ((v 0).val * (v 1).val * (v 2).val)
  rw [pow_zero, one_mul] at h
  rw [← h, cubicExponent, eval_mul, eval_mul, eval_X, eval_X, eval_X]
  push_cast
  rfl

/-- The character sum of `y₀y₁y₂` over its eight bound words is `6`: seven `1`s and one `−1`. -/
private theorem sum_charOf_cubicExponent (w : Fin (0 + 0) → ZMod 2) :
    ∑ y : Fin 3 → ZMod 2, charOf 1 (cubicExponent.eval (Fin.append w y)) = 6 := by
  have hw : ∀ y : Fin 3 → ZMod 2, (Fin.append w y : Fin (0 + 0 + 3) → ZMod 2) = y := by
    intro y
    funext k
    have hk := Fin.append_right w y (k : Fin 3)
    convert hk using 2
    exact Fin.ext (by simp)
  simp only [hw, charOf_cubicExponent, sum_fin_cons (N := 2), sum_fin_cons (N := 1), sum_fin_cons (N := 0),
    Fintype.sum_unique, sum_zmod_two]
  simp only [Fin.cons_zero, Fin.cons_one]
  have e : ∀ (a b c : ZMod 2) (d : Fin 0 → ZMod 2), (Fin.cons a (Fin.cons b
      (Fin.cons c d : Fin 1 → ZMod 2)) : Fin 3 → ZMod 2) 2 = c := fun _ _ _ _ => rfl
  simp only [e, ZMod.val_zero, ZMod.val_one]
  norm_num

/-- **D9's pair is one morphism.** `d9Cubic`'s amplitude is `6/√2³ = 3/√2`, `d9Flat`'s is `3/√2`. -/
theorem toHom_d9Cubic_eq_toHom_d9Flat :
    FrameCategory.toHom (a := ⟨0⟩) (b := ⟨0⟩) d9Cubic = FrameCategory.toHom d9Flat := by
  rw [FrameCategory.toHom_eq_toHom_iff]
  funext w
  rw [amp_pos (S := d9Cubic) (mem_support_top w), amp_pos (S := d9Flat) (mem_support_top w),
    ampCore_eq_sum_charOf, ampCore_eq_sum_charOf]
  change ((1 : ℂ) / (Real.sqrt 2 : ℂ) ^ 3)
      * ∑ y : Fin 3 → ZMod 2, charOf 1 (cubicExponent.eval (Fin.append w y))
    = ((3 : ℂ) / (Real.sqrt 2 : ℂ) / (Real.sqrt 2 : ℂ) ^ 0)
      * ∑ y : Fin 0 → ZMod 2, charOf 1 ((0 : DiagPhase (0 + 0 + 0) 1).eval (Fin.append w y))
  rw [sum_charOf_cubicExponent, Finset.univ_unique, Finset.sum_singleton]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  simp only [DiagPhase.eval, map_zero, charOf_zero, pow_zero, div_one, mul_one]
  field_simp
  linear_combination (-3 : ℂ) * hs

/-! ## The dyadic invariant of a chain

The facts this row uses are public in `CarrierRules.lean` (`exists_isDyadicRatio_of_eqvGen`,
`sq_norm_eq_zpow_of_isDyadicRatio`, `nine_div_two_ne_zpow`; entry 2026-10-02c). -/

/-- **Discriminating.** D9's pair is one morphism `⟨0⟩ → ⟨0⟩`, `d9Cubic` has a nonzero amplitude,
and yet no chain of `CarrierRule` steps relates the two presentations: the chain's scale ratio
would be dyadic (`exists_isDyadicRatio_of_eqvGen`), and `‖3/√2‖² = 9/2` is not an integer power of
two. A statement of `prop_complete` without its dyadic-ratio hypothesis is false here. -/
-- row: discriminating
theorem d9_pair_discriminating :
    FrameCategory.toHom (a := ⟨0⟩) (b := ⟨0⟩) d9Cubic = FrameCategory.toHom d9Flat
      ∧ ¬ Relation.EqvGen CarrierRule d9Cubic d9Flat := by
  refine ⟨toHom_d9Cubic_eq_toHom_d9Flat, fun hchain => ?_⟩
  obtain ⟨r, hr, hc⟩ := exists_isDyadicRatio_of_eqvGen hchain
  obtain ⟨e, he⟩ := sq_norm_eq_zpow_of_isDyadicRatio hr
  apply nine_div_two_ne_zpow e
  rw [← he]
  have hcr : r = (3 : ℂ) / (Real.sqrt 2 : ℂ) := by
    have heq : d9Flat.c = r * d9Cubic.c := hc
    simp only [d9Flat, d9Cubic, mul_one] at heq
    exact heq.symm
  rw [hcr, norm_div, show ‖(3 : ℂ)‖ = 3 from by norm_num,
    show ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 from by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)],
    div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ## Inhabitation -/

/-- **Inhabitation.** `prop_complete`'s hypotheses hold together on `czIn` and `czOut`: `czIn`'s
amplitude is `1` at the zero word, so nonzero, and the ratio of the scales is `1`. -/
-- row: inhabitation
theorem prop_complete_hypotheses_czIn_czOut :
    amp czIn ≠ 0 ∧ IsDyadicRatio (czOut.c / czIn.c) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h0 := congrFun h 0
    simp [czIn, amp_czAt, amp_idState] at h0
  · change IsDyadicRatio ((1 : ℂ) / 1)
    rw [div_one]
    exact isDyadicRatio_one

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.prop_complete' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.prop_complete

/-- info: 'FTQCLib.Frame.Walkthrough.FrameCategory.prop_conservative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.FrameCategory.prop_conservative

end PropCompletenessCheck

end FTQCLib.Frame.Walkthrough

-- mutant: prop_conservative_precision | FTQCLib/Carrier/PropCompleteness.lean
--   | CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m
--   | CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m + 1

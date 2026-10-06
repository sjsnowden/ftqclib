/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.OutcomeWeight

/-!
# Check: the outcome weight, on four small instances

T11's witness (`docs/STEPS.md`, T11.2): `outcomeWeight`'s frozen statement (`OutcomeWeight.lean`)
computed by hand on four small cases, through the public `amp_condition` (proved at T10.3.1) and
the raw `pauliProjection`/`pauliAct` formulas — `outcomeWeight_add`, `outcomeWeight_floor` and
`ampNormSq_eq_carrierNormSq` (proved at T11.3.1 and T11.3.2, after these rows were written) are
not used here.

Two states carry all four rows. `pointZ` is the one-qubit point state `∣0⟩`, with the genuinely
co-isotropic Lagrangian `⟨Z₀⟩` (not `⊥`, which is rank-deficient and not co-isotropic at `n = 1`),
so `amp_condition` applies to it directly:

* **Row 1 (agreement).** `X` on `pointZ`: weight `½` at both outcomes — `∣0⟩` measured in the `X`
  basis is an even coin flip.
* **Row 2 (discriminating).** `Z` on `pointZ`: weight `1` at outcome `0`, `0` at outcome `1` — the
  two outcomes are discriminated, `Z` being `pointZ`'s own stabilizer.
* **Row 4 (discriminating).** `pointZ` itself is a state without full support
  (`π_X(⟨Z₀⟩) = ⊥ ≠ ⊤`) whose `carrierNormSq` (`2`, since `ampCore` does not vanish at the
  off-support word) differs from its `ampNormSq` (`1`).

`magicT` is `T∣+⟩` as a one-qubit, height-zero carrier (`L = ⊤`, exponent `X₀` at precision `3`,
scale `1/√2`): the magic resource of `Examples/Teleport/TGadget.lean`, built directly on
`KernelSumState` rather than through `ofKernelState`, so no extra import is needed.

* **Row 3 (agreement).** `X` on `magicT`: weight `cos²(π/8)` at outcome `0`, `sin²(π/8)` at
  outcome `1` — `T∣+⟩` measured in the `X` basis, the standard magic-state statistics, read off
  `charOf_three_one` (`DyadicCharacter.lean`) and `Real.cos_sq`/`Real.cos_pi_div_four` (Mathlib).
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Hierarchy

/-! ## A helper: summing over the one-qubit free word -/

/-- The sum over `Fin 1 → ZMod 2` is the two terms at `0` and at the other point. -/
theorem sum_fin1 {M : Type*} [AddCommMonoid M] (F : (Fin 1 → ZMod 2) → M) :
    ∑ w : Fin 1 → ZMod 2, F w = F 0 + F (fun _ => 1) := by
  rw [show (Finset.univ : Finset (Fin 1 → ZMod 2)) = {0, fun _ => (1 : ZMod 2)} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ## `pointZ`: `∣0⟩`, with the co-isotropic Lagrangian `⟨Z₀⟩` -/

/-- `Z₀` on one qubit, as a bare Pauli. -/
noncomputable def z0Gen : Pauli 1 := zPauli (Pi.single (0 : Fin 1) 1)

/-- `∣0⟩`'s Lagrangian: `⟨Z₀⟩`, of the correct rank `1 = n`, unlike `⊥`. -/
noncomputable def pointL : Submodule (ZMod 2) (Pauli 1) := Submodule.span (ZMod 2) {z0Gen}

/-- **`pointL` is co-isotropic.** `z0Gen` pairs with `q` to `q.X 0`, so the orthogonal complement
forces `q.X = 0`, and such a `q` is `q.Z 0 • z0Gen`. -/
theorem pointL_coisotropic : LinearMap.BilinForm.orthogonal omegaBilin pointL ≤ pointL := by
  intro q hq
  have h : omega z0Gen q = 0 := hq z0Gen (Submodule.mem_span_singleton_self _)
  have hcalc : omega z0Gen q = q.X 0 := by
    unfold omega z0Gen zPauli
    simp
  rw [hcalc] at h
  have hqX : q.X = 0 := by funext i; fin_cases i; exact h
  change q ∈ Submodule.span (ZMod 2) ({z0Gen} : Set (Pauli 1))
  rw [Submodule.mem_span_singleton]
  refine ⟨q.Z 0, Pauli.ext ?_ ?_⟩
  · rw [hqX]
    funext i; fin_cases i
    change (0 : ZMod 2) = q.Z 0 • (z0Gen.X 0)
    simp [z0Gen, zPauli]
  · funext i; fin_cases i
    simp [z0Gen, zPauli, Pi.single_eq_same]

/-- `∣0⟩` on the carrier: the point state at `0`, with the co-isotropic Lagrangian `⟨Z₀⟩`. -/
noncomputable def pointZ : KernelSumState 1 := ⟨1, 0, 0, 1, pointL, 0⟩

/-- `pointZ`'s support is exactly `{0}`: `π_X(⟨Z₀⟩) = ⊥`, since `Z₀`'s X-part is `0`. -/
theorem support_pointZ (w : Fin 1 → ZMod 2) :
    (∃ p ∈ pointZ.L, w = pointZ.x₀ + p.X) ↔ w = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
    change (0 : Fin 1 → ZMod 2) + (a • z0Gen).X = 0
    simp [z0Gen, zPauli]
  · rintro rfl
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    change (0 : Fin 1 → ZMod 2) = pointZ.x₀ + (0 : Pauli 1).X
    simp [pointZ]

/-- `pointZ`'s `ampCore` is the constant `1` (the exponent `Q = 0`), at every word. -/
theorem ampCore_pointZ_const (w : Fin 1 → ZMod 2) :
    ampCore pointZ.m pointZ.h pointZ.Q pointZ.c w = 1 := by
  change ampCore 1 0 (0 : DiagPhase (1 + 0) 1) 1 w = 1
  rw [ampCore_zero, exp_realPhase_eq_charOf]
  have heval : DiagPhase.eval (0 : DiagPhase (1 + 0) 1) w = 0 := by simp [DiagPhase.eval]
  rw [heval, charOf_zero, mul_one]

/-- `pointZ`'s amplitude at `0` is `1`. -/
theorem amp_pointZ_zero : amp pointZ (0 : Fin 1 → ZMod 2) = 1 := by
  rw [amp_pos ((support_pointZ 0).mpr rfl), ampCore_pointZ_const]

/-- `pointZ`'s amplitude off `0` is `0`. -/
theorem amp_pointZ_ne {w : Fin 1 → ZMod 2} (hw : w ≠ 0) : amp pointZ w = 0 :=
  amp_neg (fun h => hw ((support_pointZ w).mp h))

/-! ## Row 1: `X` on `pointZ`, weight `½` at both outcomes (agreement) -/

/-- `X` on one qubit: sign `+`, X-part `e₀`. -/
noncomputable def xPoint : SignedPauli 1 := ⟨0, ⟨Pi.single (0 : Fin 1) 1, 0⟩⟩

/-- `X`'s action swaps the two one-qubit words: `yWeight` and the `Z`-dot are both `0`. -/
theorem xPoint_act (f : (Fin 1 → ZMod 2) → ℂ) (w : Fin 1 → ZMod 2) :
    xPoint.act f w = f (w + (fun _ => 1)) := by
  have hX : xPoint.pauli.X = (fun _ => (1 : ZMod 2)) := by funext i; fin_cases i; rfl
  have hyw : yWeight xPoint.pauli = 0 := by simp [yWeight, zDot, xPoint]
  have hzd : zDot xPoint.pauli (w + xPoint.pauli.X) = 0 := by simp [zDot, xPoint]
  unfold SignedPauli.act pauliAct
  rw [hyw, hzd, hX]
  simp [xPoint]

/-- The two one-qubit words differ by `e₀`. -/
theorem fin1_zero_add_one : (0 : Fin 1 → ZMod 2) + (fun _ => (1 : ZMod 2)) = fun _ => 1 := by
  funext i; fin_cases i; rfl

theorem fin1_one_add_one : (fun _ => (1 : ZMod 2) : Fin 1 → ZMod 2) + (fun _ => 1) = 0 := by
  funext i; fin_cases i; decide

/-- **Row 1 (agreement).** `X` conditioning `pointZ`, at both outcomes: weight `½` — `∣0⟩`
measured in the `X` basis is an even coin flip, read off `pauliProjection` on the two-point
support. -/
-- row: agreement
theorem outcomeWeight_pointZ_X :
    outcomeWeight pointZ xPoint 0 = 1 / 2 ∧ outcomeWeight pointZ xPoint 1 = 1 / 2 := by
  have hamp := amp_condition pointZ pointL_coisotropic xPoint
  have hval : ∀ b : ZMod 2, outcomeWeight pointZ xPoint b
      = Complex.normSq (pauliProjection xPoint b (amp pointZ) 0)
        + Complex.normSq (pauliProjection xPoint b (amp pointZ) (fun _ => 1)) := by
    intro b
    unfold outcomeWeight ampNormSq
    rw [sum_fin1, hamp]
  have hp0 : pauliProjection xPoint 0 (amp pointZ) 0 = 1 / 2 := by
    unfold pauliProjection
    rw [xPoint_act, fin1_zero_add_one, amp_pointZ_zero, amp_pointZ_ne
      (show (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 by intro h; simpa using congrFun h 0)]
    simp
  have hp0' : pauliProjection xPoint 0 (amp pointZ) (fun _ => 1) = 1 / 2 := by
    unfold pauliProjection
    rw [xPoint_act, fin1_one_add_one, amp_pointZ_zero, amp_pointZ_ne
      (show (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 by intro h; simpa using congrFun h 0)]
    simp
  have hp1 : pauliProjection xPoint 1 (amp pointZ) 0 = 1 / 2 := by
    unfold pauliProjection
    rw [xPoint_act, fin1_zero_add_one, amp_pointZ_zero, amp_pointZ_ne
      (show (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 by intro h; simpa using congrFun h 0)]
    norm_num
  have hp1' : pauliProjection xPoint 1 (amp pointZ) (fun _ => 1) = -(1 / 2) := by
    unfold pauliProjection
    rw [xPoint_act, fin1_one_add_one, amp_pointZ_zero, amp_pointZ_ne
      (show (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 by intro h; simpa using congrFun h 0)]
    norm_num
  constructor
  · rw [hval 0, hp0, hp0']
    norm_num [Complex.normSq]
  · rw [hval 1, hp1, hp1']
    norm_num [Complex.normSq]

/-! ## Row 2: `Z` on `pointZ`, weight `1` at outcome `0`, `0` at outcome `1` (discriminating) -/

/-- `Z` on one qubit: sign `+`, `Z`-part `e₀` — `pointZ`'s own stabilizer generator. -/
noncomputable def zPoint : SignedPauli 1 := ⟨0, z0Gen⟩

/-- `Z`'s action keeps the word and multiplies by `(-1)^{w₀}`. -/
theorem zPoint_act (f : (Fin 1 → ZMod 2) → ℂ) (w : Fin 1 → ZMod 2) :
    zPoint.act f w = (-1 : ℂ) ^ (w 0).val * f w := by
  have hX : zPoint.pauli.X = 0 := by funext i; fin_cases i; rfl
  have hyw : yWeight zPoint.pauli = 0 := by simp [yWeight, zDot, zPoint, z0Gen, zPauli]
  have hzd : zDot zPoint.pauli (w + zPoint.pauli.X) = (w 0).val := by
    unfold zDot
    rw [hX, add_zero]
    show (∑ i : Fin 1, (zPoint.pauli.Z i).val * (w i).val) = (w 0).val
    simp [zPoint, z0Gen, zPauli]
  unfold SignedPauli.act pauliAct
  rw [hyw, hzd, hX]
  simp [zPoint]

/-- **Row 2 (discriminating).** `Z` conditioning `pointZ`: weight `1` at outcome `0` and `0` at
outcome `1` — the certain and the impossible outcome of `pointZ`'s own stabilizer, discriminated
by their values. -/
-- row: discriminating
theorem outcomeWeight_pointZ_Z :
    outcomeWeight pointZ zPoint 0 = 1 ∧ outcomeWeight pointZ zPoint 1 = 0
      ∧ outcomeWeight pointZ zPoint 0 ≠ outcomeWeight pointZ zPoint 1 := by
  have hamp := amp_condition pointZ pointL_coisotropic zPoint
  have hval : ∀ b : ZMod 2, outcomeWeight pointZ zPoint b
      = Complex.normSq (pauliProjection zPoint b (amp pointZ) 0)
        + Complex.normSq (pauliProjection zPoint b (amp pointZ) (fun _ => 1)) := by
    intro b
    unfold outcomeWeight ampNormSq
    rw [sum_fin1, hamp]
  have hne1 : (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 := by
    intro h; simpa using congrFun h 0
  have hp00 : pauliProjection zPoint 0 (amp pointZ) 0 = 1 := by
    unfold pauliProjection
    rw [zPoint_act, amp_pointZ_zero]
    norm_num
  have hp01 : pauliProjection zPoint 0 (amp pointZ) (fun _ => 1) = 0 := by
    unfold pauliProjection
    rw [zPoint_act, amp_pointZ_ne hne1]
    simp
  have hp10 : pauliProjection zPoint 1 (amp pointZ) 0 = 0 := by
    unfold pauliProjection
    rw [zPoint_act, amp_pointZ_zero]
    norm_num
  have hp11 : pauliProjection zPoint 1 (amp pointZ) (fun _ => 1) = 0 := by
    unfold pauliProjection
    rw [zPoint_act, amp_pointZ_ne hne1]
    simp
  refine ⟨by rw [hval 0, hp00, hp01]; norm_num [Complex.normSq],
    by rw [hval 1, hp10, hp11]; norm_num [Complex.normSq], ?_⟩
  rw [hval 0, hval 1, hp00, hp01, hp10, hp11]
  norm_num [Complex.normSq]

/-! ## Row 4: `pointZ` itself, `carrierNormSq ≠ ampNormSq` (discriminating) -/

/-- **Row 4 (discriminating).** `pointZ` is a state without full support
(`π_X(pointL) = ⊥ ≠ ⊤`), and its `ampCore` does not vanish at the one word off its support: its
`carrierNormSq` (`2`) differs from its `ampNormSq` (`1`). -/
-- row: discriminating
theorem carrierNormSq_ne_ampNormSq_pointZ :
    (Submodule.map xProj pointZ.L ≠ (⊤ : Submodule (ZMod 2) (Fin 1 → ZMod 2)))
      ∧ carrierNormSq pointZ = 2 ∧ ampNormSq pointZ = 1
      ∧ carrierNormSq pointZ ≠ ampNormSq pointZ := by
  have hne1 : (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 := by
    intro h; simpa using congrFun h 0
  have hnotfull : Submodule.map xProj pointZ.L ≠ (⊤ : Submodule (ZMod 2) (Fin 1 → ZMod 2)) := by
    intro htop
    have hmem : (fun _ : Fin 1 => (1 : ZMod 2)) ∈ Submodule.map xProj pointZ.L := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp hmem
    have hpz : p.X = 0 := by
      change p ∈ pointL at hp
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
      simp [z0Gen, zPauli]
    rw [xProj_apply, hpz] at hpx
    exact hne1 hpx.symm
  have hcarrier : carrierNormSq pointZ = 2 := by
    unfold carrierNormSq
    rw [sum_fin1, ampCore_pointZ_const, ampCore_pointZ_const]
    norm_num [Complex.normSq]
  have hampNorm : ampNormSq pointZ = 1 := by
    unfold ampNormSq
    rw [sum_fin1, amp_pointZ_zero, amp_pointZ_ne hne1]
    norm_num [Complex.normSq]
  exact ⟨hnotfull, hcarrier, hampNorm, by rw [hcarrier, hampNorm]; norm_num⟩

/-! ## `magicT`: `T∣+⟩`, the magic resource, as a height-zero carrier -/

/-- `T∣+⟩` as a one-qubit carrier: full support (`L = ⊤`), exponent `X₀` at precision `3` (the `T`
phase, `charOf_three_one`), scale `1/√2` so the state is unit-norm. The same resource as
`Examples/Teleport/TGadget.lean`'s `magicA`, built directly on `KernelSumState` rather than through
`ofKernelState`. -/
noncomputable def magicT : KernelSumState 1 :=
  ⟨3, 0, MvPolynomial.X (0 : Fin 1), (Real.sqrt 2 : ℂ)⁻¹, ⊤, 0⟩

/-- `magicT`'s support is everything: `L = ⊤`. -/
theorem support_magicT (w : Fin 1 → ZMod 2) : ∃ p ∈ magicT.L, w = magicT.x₀ + p.X := by
  refine ⟨⟨w, 0⟩, Submodule.mem_top, ?_⟩
  change w = magicT.x₀ + w
  unfold magicT
  simp

/-- `magicT`'s amplitude at `0` is `1/√2`. -/
theorem amp_magicT_zero : amp magicT (0 : Fin 1 → ZMod 2) = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [amp_pos (support_magicT 0)]
  change ampCore 3 0 (MvPolynomial.X (0 : Fin 1)) (Real.sqrt 2 : ℂ)⁻¹ 0 = _
  rw [ampCore_zero, exp_realPhase_eq_charOf]
  have heval : DiagPhase.eval (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3)
      (0 : Fin 1 → ZMod 2) = 0 := by
    rw [DiagPhase.eval_X]; rfl
  rw [heval, charOf_zero, mul_one]

/-- `magicT`'s amplitude at the other word is `(1/√2) · (1+i)/√2 = (1+i)/2`. -/
theorem amp_magicT_one : amp magicT (fun _ => (1 : ZMod 2)) = (1 + Complex.I) / 2 := by
  rw [amp_pos (support_magicT (fun _ => 1))]
  change ampCore 3 0 (MvPolynomial.X (0 : Fin 1)) (Real.sqrt 2 : ℂ)⁻¹ (fun _ => 1) = _
  rw [ampCore_zero, exp_realPhase_eq_charOf]
  have heval : DiagPhase.eval (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3)
      (fun _ : Fin 1 => (1 : ZMod 2)) = 1 := by
    rw [DiagPhase.eval_X]; rfl
  rw [heval, charOf_three_one, inv_mul_eq_div, div_div,
    sqrt_two_mul_self]

/-- The real and imaginary parts of `magicT`'s two amplitudes. -/
theorem amp_magicT_zero_re : (amp magicT (0 : Fin 1 → ZMod 2)).re = Real.sqrt 2 / 2 := by
  rw [amp_magicT_zero, Complex.inv_re, Complex.normSq_ofReal, Complex.ofReal_re,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem amp_magicT_zero_im : (amp magicT (0 : Fin 1 → ZMod 2)).im = 0 := by
  rw [amp_magicT_zero, Complex.inv_im, Complex.ofReal_im]
  simp

theorem amp_magicT_one_re : (amp magicT (fun _ => (1 : ZMod 2))).re = 1 / 2 := by
  rw [amp_magicT_one]; simp

theorem amp_magicT_one_im : (amp magicT (fun _ => (1 : ZMod 2))).im = 1 / 2 := by
  rw [amp_magicT_one]; simp

/-- `magicT`'s own norm is `1`. -/
theorem ampNormSq_magicT : ampNormSq magicT = 1 := by
  unfold ampNormSq
  rw [sum_fin1, Complex.normSq_apply, Complex.normSq_apply, amp_magicT_zero_re,
    amp_magicT_zero_im, amp_magicT_one_re, amp_magicT_one_im]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h2]

/-! ## Row 3: `X` on `magicT`, `cos²(π/8)` and `sin²(π/8)` (agreement) -/

/-- **Row 3 (agreement).** `X` conditioning `magicT`: weight `cos²(π/8)` at outcome `0` and
`sin²(π/8)` at outcome `1` — the standard magic-state statistics of measuring `T∣+⟩` in the `X`
basis, read off the amplitudes' real and imaginary parts and the half-angle identity
`Real.cos_sq`. -/
-- row: agreement
theorem outcomeWeight_magicT_X :
    outcomeWeight magicT xPoint 0 = Real.cos (Real.pi / 8) ^ 2
      ∧ outcomeWeight magicT xPoint 1 = Real.sin (Real.pi / 8) ^ 2 := by
  have hamp := amp_condition magicT (le_top) xPoint
  have hval : ∀ b : ZMod 2, outcomeWeight magicT xPoint b
      = Complex.normSq (pauliProjection xPoint b (amp magicT) 0)
        + Complex.normSq (pauliProjection xPoint b (amp magicT) (fun _ => 1)) := by
    intro b
    unfold outcomeWeight ampNormSq
    rw [sum_fin1, hamp]
  have hp00 : pauliProjection xPoint 0 (amp magicT) 0
      = (1 / 2 : ℂ) * (amp magicT 0 + amp magicT (fun _ => 1)) := by
    unfold pauliProjection
    rw [xPoint_act, fin1_zero_add_one, show ((0 : ZMod 2).val) = 0 from rfl, pow_zero, one_mul]
  have hp01 : pauliProjection xPoint 0 (amp magicT) (fun _ => 1)
      = (1 / 2 : ℂ) * (amp magicT (fun _ => 1) + amp magicT 0) := by
    unfold pauliProjection
    rw [xPoint_act, fin1_one_add_one, show ((0 : ZMod 2).val) = 0 from rfl, pow_zero, one_mul]
  have hp10 : pauliProjection xPoint 1 (amp magicT) 0
      = (1 / 2 : ℂ) * (amp magicT 0 - amp magicT (fun _ => 1)) := by
    unfold pauliProjection
    rw [xPoint_act, fin1_zero_add_one, show ((1 : ZMod 2).val) = 1 from rfl, pow_one]
    ring
  have hp11 : pauliProjection xPoint 1 (amp magicT) (fun _ => 1)
      = (1 / 2 : ℂ) * (amp magicT (fun _ => 1) - amp magicT 0) := by
    unfold pauliProjection
    rw [xPoint_act, fin1_one_add_one, show ((1 : ZMod 2).val) = 1 from rfl, pow_one]
    ring
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnormsq_sum : Complex.normSq (amp magicT 0 + amp magicT (fun _ => 1))
      = 1 + Real.sqrt 2 / 2 := by
    rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, amp_magicT_zero_re,
      amp_magicT_zero_im, amp_magicT_one_re, amp_magicT_one_im]
    nlinarith [hsq2]
  have hnormsq_diff : Complex.normSq (amp magicT 0 - amp magicT (fun _ => 1))
      = 1 - Real.sqrt 2 / 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, amp_magicT_zero_re,
      amp_magicT_zero_im, amp_magicT_one_re, amp_magicT_one_im]
    nlinarith [hsq2]
  have hhalf : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by norm_num [Complex.normSq]
  have hw0 : outcomeWeight magicT xPoint 0 = 1 / 2 + Real.sqrt 2 / 4 := by
    rw [hval 0, hp00, hp01, Complex.normSq_mul, Complex.normSq_mul, hhalf,
      add_comm (amp magicT (fun _ => 1)) (amp magicT 0), hnormsq_sum]
    ring
  have hw1 : outcomeWeight magicT xPoint 1 = 1 / 2 - Real.sqrt 2 / 4 := by
    have hswap : Complex.normSq (amp magicT (fun _ => 1) - amp magicT 0)
        = Complex.normSq (amp magicT 0 - amp magicT (fun _ => 1)) := by
      rw [← Complex.normSq_neg (amp magicT 0 - amp magicT (fun _ => 1))]
      congr 1
      ring
    rw [hval 1, hp10, hp11, Complex.normSq_mul, Complex.normSq_mul, hhalf, hswap, hnormsq_diff]
    ring
  have hcos : Real.cos (Real.pi / 8) ^ 2 = 1 / 2 + Real.sqrt 2 / 4 := by
    rw [Real.cos_sq, show (2 : ℝ) * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
    ring
  have hsin : Real.sin (Real.pi / 8) ^ 2 = 1 / 2 - Real.sqrt 2 / 4 := by
    have hpyth := Real.sin_sq_add_cos_sq (Real.pi / 8)
    rw [hcos] at hpyth
    linarith
  exact ⟨hw0.trans hcos.symm, hw1.trans hsin.symm⟩

/-! ## Row 5: `outcomeWeight_floor`'s hypotheses, together, on `pointZ` (inhabitation) -/

/-- **`pointZ` is stabilized by `pointL`.** `z0Gen`'s `X`-part is `0`, so it acts on the amplitude
by the sign `(-1)^{w 0}`; `pointZ`'s amplitude is already zero off `w = 0`, where that sign is
`+1`, so `z0Gen` fixes `amp pointZ` outright. Every element of `pointL` is `0` or `z0Gen`. -/
theorem stabilizedBy_pointL : StabilizedBy pointL (amp pointZ) := by
  intro g hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  have hgX : (a • z0Gen).X = 0 := by
    funext i; fin_cases i; simp [z0Gen, zPauli]
  have hgy : yWeight (a • z0Gen) = 0 := by
    unfold yWeight; rw [hgX]; simp
  refine ⟨0, ?_⟩
  funext w
  rcases eq_or_ne w 0 with rfl | hw
  · simp [pauliAct_apply, hgX, hgy, amp_pointZ_zero]
  · rw [amp_pointZ_ne hw]
    simp [pauliAct_apply, hgX, hgy, amp_pointZ_ne hw]

/-- **Row 5 (inhabitation).** `outcomeWeight_floor`'s two hypotheses — a co-isotropic Lagrangian
(`pointL_coisotropic`) and one that stabilizes the amplitude (`stabilizedBy_pointL`) — hold
together on the concrete object `pointZ`, so the floor theorem applies to it. -/
-- row: inhabitation
theorem outcomeWeight_floor_pointZ (P : SignedPauli 1) (b : ZMod 2) :
    outcomeWeight pointZ P b = 0 ∨ outcomeWeight pointZ P b = ampNormSq pointZ / 2
      ∨ outcomeWeight pointZ P b = ampNormSq pointZ :=
  outcomeWeight_floor pointZ pointL_coisotropic stabilizedBy_pointL P b

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, one guard per row and the two outcome-weight facts -/

/-- info: 'FTQCLib.Frame.Walkthrough.sum_fin1' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_fin1

/-- info: 'FTQCLib.Frame.Walkthrough.pointL_coisotropic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pointL_coisotropic

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_pointZ_X' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_pointZ_X

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_pointZ_Z' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_pointZ_Z

/-- info: 'FTQCLib.Frame.Walkthrough.carrierNormSq_ne_ampNormSq_pointZ' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.carrierNormSq_ne_ampNormSq_pointZ

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_magicT_X' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_magicT_X

/-- info: 'FTQCLib.Frame.Walkthrough.stabilizedBy_pointL' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.stabilizedBy_pointL

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_floor_pointZ' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_floor_pointZ

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_eq

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_add' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_add

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeWeight_floor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeWeight_floor

/-- info: 'FTQCLib.Frame.Walkthrough.ampNormSq_eq_carrierNormSq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ampNormSq_eq_carrierNormSq

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_half_add_add_normSq_half_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.normSq_half_add_add_normSq_half_sub

/-- info: 'FTQCLib.Frame.Walkthrough.sum_normSq_projection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_normSq_projection

/-- info: 'FTQCLib.Frame.Walkthrough.sum_words_snoc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_words_snoc

/-- info: 'FTQCLib.Frame.Walkthrough.ampNormSq_appendFreeBit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ampNormSq_appendFreeBit

/-- info: 'FTQCLib.Frame.Walkthrough.eq_zero_of_walshTransform_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.eq_zero_of_walshTransform_eq_zero

/-! ## Declared mutants, aimed at a conclusion and at a constant a proof uses -/

-- mutant: outcomeWeight_add_conclusion | FTQCLib/Carrier/OutcomeWeight.lean
--   | outcomeWeight S P 0 + outcomeWeight S P 1 = ampNormSq S
--   | outcomeWeight S P 0 + outcomeWeight S P 1 = ampNormSq S + 1
-- mutant: parallelogram_scale | FTQCLib/Carrier/OutcomeWeight.lean
--   | (Complex.normSq a + Complex.normSq c) / 2
--   | (Complex.normSq a + Complex.normSq c) / 3

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierState
import FTQCLib.Hierarchy.FloorEquivalence

/-!
# The floor chart of a floor record, read at the offset

The floor chart (`FTQCLib/Hierarchy/FloorEquivalence.lean`) presents a stabilizer state as a
`FloorKernel`: a Lagrangian, an offset, and a `ZMod 4`-valued exponent `e` on the support space with
`e 0 = 0` and the shift recurrence `ShiftConsistent`. Reading that exponent off the record at the
origin (`eOf K w = 2·q(w)`) is wrong at a nonzero offset: two records with the same denotation
then decode to different characters. The decode used here reads the exponent **at the offset**:

`eAt K u := 2^{2−m} · (q(x₀ + u) − q(x₀))`,

the exponent's difference from its value at the offset, scaled from `ZMod (2^m)` into `ZMod 4`
(`toFour`; the chart lives at precision `m ≤ 2`). Then:

* `eAt K 0 = 0` by construction;
* `shiftConsistent_eAt_iff` — at `1 ≤ m ≤ 2`, `eAt` is shift-consistent exactly when the record
  satisfies the basepoint-free exponent law `ShiftLaw` — which is the floor, by
  `isFloor_iff_shiftLaw`;
* `chiAt K g := chiOfE (eAt K) g − 2·(g.Z·x₀)` is the decoded character, `decodeAt` the
  `FloorKernel`, `chiAt_eq_fullChi` and `chiAt_valid` its bundling;
* **`chiAt_eq_character`** — on a floor record the decoded character is the eigenphase of the
  Pauli action: `pauliAct g amp = i^{chiAt K g} · amp` for `g ∈ L`. This is the statement that the
  chart reads the state, not the record.

Everything here is frame-pure. No `FTQCLib.Hilbert`.

## Main definitions

* `toFour`, `eAt`, `chiAt`, `decodeAt`.

## Main results

* `shiftConsistent_eAt_iff`, `chiAt_valid`, `chiAt_eq_character`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## The scaling into `ZMod 4` -/

/-- The chart's scaling of a precision-`m` exponent value into `ZMod 4`: `z ↦ 2^{2−m}·z.val`
(the identity at `m = 2`, doubling at `m = 1`). -/
def toFour (m : ℕ) (z : ZMod (2 ^ m)) : ZMod 4 :=
  (2 : ZMod 4) ^ (2 - m) * (z.val : ZMod 4)

/-- `toFour` sends `0` to `0`. -/
theorem toFour_zero (m : ℕ) : toFour m 0 = 0 := by
  simp [toFour]

/-- `toFour` is additive at `m ≤ 2`. -/
theorem toFour_add {m : ℕ} (hm : m ≤ 2) (a b : ZMod (2 ^ m)) :
    toFour m (a + b) = toFour m a + toFour m b := by
  interval_cases m <;> revert a b <;> decide

/-- `toFour` respects subtraction at `m ≤ 2`. -/
theorem toFour_sub {m : ℕ} (hm : m ≤ 2) (a b : ZMod (2 ^ m)) :
    toFour m (a - b) = toFour m a - toFour m b := by
  have h := toFour_add hm (a - b) b
  rw [sub_add_cancel] at h
  linear_combination -h

/-- `toFour` is injective at `1 ≤ m ≤ 2`. -/
theorem toFour_injective {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2) (a b : ZMod (2 ^ m))
    (h : toFour m a = toFour m b) : a = b := by
  interval_cases m <;> revert a b <;> decide

/-- `toFour` sends the top-bit multiple of a residue to twice that residue, at `1 ≤ m ≤ 2`. -/
theorem toFour_two_pow_pred_mul {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2) (z : ZMod (2 ^ m)) :
    toFour m ((2 : ZMod (2 ^ m)) ^ (m - 1) * z) = 2 * (z.val : ZMod 4) := by
  interval_cases m <;> revert z <;> decide

/-- The top-bit multiple of a natural number, through `toFour`, is twice its cast. -/
theorem toFour_two_pow_pred_mul_natCast {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2) (t : ℕ) :
    toFour m ((2 : ZMod (2 ^ m)) ^ (m - 1) * (t : ZMod (2 ^ m))) = 2 * (t : ZMod 4) := by
  rw [toFour_two_pow_pred_mul hm1 hm, two_mul_natCast_four t, two_mul_natCast_four
    ((t : ZMod (2 ^ m)).val)]
  congr 2
  interval_cases m <;> rw [ZMod.natCast_val, ZMod.cast_natCast (by norm_num)]

/-! ## The exponent at the offset -/

/-- The chart exponent of an `h = 0` record, read at the offset: `2^{2−m}·(q(x₀ + u) − q(x₀))`. -/
noncomputable def eAt (K : KernelState n) (u : Fin n → ZMod 2) : ZMod 4 :=
  toFour K.m (DiagPhase.eval K.q (K.x₀ + u) - DiagPhase.eval K.q K.x₀)

/-- The chart exponent vanishes at `0`. -/
theorem eAt_zero (K : KernelState n) : eAt K 0 = 0 := by
  unfold eAt
  rw [add_zero, sub_self, toFour_zero]

/-- The floor chart's support space is the X-shadow. -/
theorem supportSpace_eq_map_xProj (L : Submodule (ZMod 2) (Pauli n)) :
    supportSpace L = Submodule.map xProj L := by
  unfold supportSpace
  congr 1

/-- Membership in the shadow is support membership of the translate. -/
theorem mem_shadow_iff_support (K : KernelState n) (u : Fin n → ZMod 2) :
    u ∈ Submodule.map xProj K.L ↔ ∃ p ∈ K.L, K.x₀ + u = K.x₀ + p.X := by
  constructor
  · intro hu
    obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hu
    refine ⟨p, hp, ?_⟩
    rw [xProj_apply] at hpX
    rw [hpX]
  · rintro ⟨p, hp, h⟩
    rw [add_left_cancel h]
    exact Submodule.mem_map_of_mem hp

/-- **The chart exponent is shift-consistent exactly when the record obeys the exponent law**, at
`1 ≤ m ≤ 2`. -/
theorem shiftConsistent_eAt_iff (K : KernelState n) (hm1 : 1 ≤ K.m) (hm : K.m ≤ 2) :
    ShiftConsistent K.L (eAt K) ↔ ShiftLaw K := by
  have h2 : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * 2 = 0 := two_pow_pred_mul_two
  constructor
  · intro hsc g hg
    refine ⟨DiagPhase.eval K.q (K.x₀ + g.X) - DiagPhase.eval K.q K.x₀
      - (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m)), ?_⟩
    intro w hw
    obtain ⟨p, hp, rfl⟩ := hw
    have hu : p.X ∈ supportSpace K.L := by
      rw [supportSpace_eq_map_xProj]
      exact Submodule.mem_map_of_mem hp
    have hrec := hsc g hg p.X hu
    unfold eAt at hrec
    rw [← toFour_two_pow_pred_mul_natCast hm1 hm (zDot g p.X), ← toFour_add hm,
      ← toFour_add hm] at hrec
    have heq := toFour_injective hm1 hm _ _ hrec
    have hpar := two_pow_pred_mul_zDot_add_X (m := K.m) g (K.x₀ + p.X)
    have hpar2 : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g (K.x₀ + p.X) : ℕ) : ZMod (2 ^ K.m))
        = (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m))
          + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g p.X : ℕ) : ZMod (2 ^ K.m)) := by
      rw [← mul_add, ← Nat.cast_add]
      apply two_pow_pred_mul_eq_of_cast_eq
      rw [zDot_cast_two_add_right, Nat.cast_add]
    rw [show K.x₀ + (p.X + g.X) = K.x₀ + p.X + g.X from (add_assoc _ _ _).symm] at heq
    linear_combination heq - hpar2
  · intro hlaw g hg u hu
    obtain ⟨k, hk⟩ := hlaw g hg
    rw [supportSpace_eq_map_xProj, mem_shadow_iff_support] at hu
    have h1 := hk (K.x₀ + u) hu
    have h0 := hk K.x₀ (x₀_mem_support K)
    have hpar2 : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g (K.x₀ + u) : ℕ) : ZMod (2 ^ K.m))
        = (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m))
          + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g u : ℕ) : ZMod (2 ^ K.m)) := by
      rw [← mul_add, ← Nat.cast_add]
      apply two_pow_pred_mul_eq_of_cast_eq
      rw [zDot_cast_two_add_right, Nat.cast_add]
    unfold eAt
    rw [← toFour_two_pow_pred_mul_natCast hm1 hm (zDot g u), ← toFour_add hm, ← toFour_add hm]
    congr 1
    rw [show K.x₀ + (u + g.X) = K.x₀ + u + g.X from (add_assoc _ _ _).symm]
    linear_combination h1 - h0 + hpar2

/-! ## The decoded character -/

/-- The decoded character of an `h = 0` record: `chiOfE (eAt K) g − 2·(g.Z·x₀)`. -/
noncomputable def chiAt (K : KernelState n) (g : Pauli n) : ZMod 4 :=
  chiOfE (eAt K) g - 2 * ((zDot g K.x₀ : ℕ) : ZMod 4)

/-- The floor chart of a lawful record at `1 ≤ m ≤ 2`. -/
noncomputable def decodeAt (K : KernelState n) (hStab : IsStabilizer K.L)
    (hFull : finrank (ZMod 2) K.L = n) (hlaw : ShiftLaw K) (hm1 : 1 ≤ K.m) (hm : K.m ≤ 2) :
    FloorKernel n :=
  ⟨K.L, hStab, hFull, K.x₀, eAt K, eAt_zero K, (shiftConsistent_eAt_iff K hm1 hm).mpr hlaw⟩

/-- On `L`, the chart's full character is `chiAt`. -/
theorem chiAt_eq_fullChi (K : KernelState n) (hStab : IsStabilizer K.L)
    (hFull : finrank (ZMod 2) K.L = n) (hlaw : ShiftLaw K) (hm1 : 1 ≤ K.m) (hm : K.m ≤ 2)
    {g : Pauli n} (hg : g ∈ K.L) :
    fullChi (decodeAt K hStab hFull hlaw hm1 hm) g = chiAt K g := by
  unfold fullChi
  rw [if_pos (show g ∈ (decodeAt K hStab hFull hlaw hm1 hm).L from hg)]
  rfl

/-- The decoded character obeys the `betaFrame`-twisted law on `L`. -/
theorem chiAt_valid (K : KernelState n) (hStab : IsStabilizer K.L)
    (hFull : finrank (ZMod 2) K.L = n) (hlaw : ShiftLaw K) (hm1 : 1 ≤ K.m) (hm : K.m ≤ 2)
    {p q : Pauli n} (hp : p ∈ K.L) (hq : q ∈ K.L) :
    chiAt K (p + q) = chiAt K p + chiAt K q + betaFrame p q := by
  rw [← chiAt_eq_fullChi K hStab hFull hlaw hm1 hm (K.L.add_mem hp hq),
    ← chiAt_eq_fullChi K hStab hFull hlaw hm1 hm hp,
    ← chiAt_eq_fullChi K hStab hFull hlaw hm1 hm hq]
  exact fullChi_valid _ hp hq

/-! ## The character is the eigenphase -/

/-- `zeta 1 = −1`. -/
theorem zeta_one : zeta 1 = -1 := by
  have h := zeta_pow_two_pow_pred (m := 1) le_rfl
  simpa using h

/-- `zeta 2 = i`. -/
theorem zeta_two : zeta 2 = Complex.I := by
  unfold zeta
  have hπ : ((2 * Real.pi / (2 : ℝ) ^ 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hπ, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- At `1 ≤ m ≤ 2` the character is `i` to the scaled value. -/
theorem charOf_eq_I_pow_toFour {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2) (z : ZMod (2 ^ m)) :
    charOf m z = Complex.I ^ (toFour m z).val := by
  rw [charOf_eq_zeta_pow]
  interval_cases m
  · rw [zeta_one]
    have hz : z = 0 ∨ z = 1 := by revert z; decide
    rcases hz with rfl | rfl
    · simp [toFour]
    · have hv : (toFour 1 1).val = 2 := by decide
      have hv1 : (1 : ZMod (2 ^ 1)).val = 1 := by decide
      rw [hv, hv1, pow_one, Complex.I_sq]
  · rw [zeta_two]
    have hv : (toFour 2 z).val = z.val := by
      revert z
      decide
    rw [hv]

/-- **The decoded character is the eigenphase.** On a floor record at `1 ≤ m ≤ 2`, every `g ∈ L`
acts on the denotation by `i^{chiAt K g}`. -/
theorem chiAt_eq_character (K : KernelState n) (hF : IsFloor (ofKernelState K)) (hm : K.m ≤ 2)
    {g : Pauli n} (hg : g ∈ K.L) :
    pauliAct g (amp (ofKernelState K))
      = fun w => Complex.I ^ (chiAt K g).val * amp (ofKernelState K) w := by
  have hm1 : 1 ≤ K.m := hF.1.1
  have hlaw : ShiftLaw K := (isFloor_iff_shiftLaw K hF.1).mp hF
  obtain ⟨k, hk⟩ := hlaw g hg
  rw [pauliAct_amp_ofKernelState_of_defect K hm1 hg hk]
  funext w
  congr 1
  -- the scalar `i^{yw}·(−1)^{yw}·charOf k` is `i^{chiAt g}`
  have hk0 := hk K.x₀ (x₀_mem_support K)
  have hchi : chiAt K g = toFour K.m k - (yWeight g : ZMod 4) := by
    unfold chiAt chiOfE eAt
    rw [add_zero, sub_self, toFour_zero, sub_zero]
    have hkk : DiagPhase.eval K.q (K.x₀ + g.X) - DiagPhase.eval K.q K.x₀
        = k + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m)) := by
      linear_combination hk0
    rw [hkk, toFour_add hm, toFour_two_pow_pred_mul_natCast hm1 hm]
    ring
  rw [hchi, charOf_eq_I_pow_toFour hm1 hm, neg_one_pow_eq_I_pow, ← pow_add, ← pow_add]
  apply I_pow_eq_of_natCast_eq
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hfour : ∀ y : ZMod 4, 4 * y = 0 := by decide
  linear_combination hfour (yWeight g : ZMod 4)

end FTQCLib.Frame.Walkthrough

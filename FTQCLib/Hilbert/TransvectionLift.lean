/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.SignedCharacterSelection

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The transvection lift family — every `τ_v` gets a selected lift with a frame cochain

For every Pauli label `v`, the **rotation lift** `rotGate v = (1 − i·I^{xz v}·P_v)/√2` realizes
the transvection `τ_v` (entangling `v` included), with an **explicit frame-native sign cochain**:

* `cliffordFun_rotGate` — the symplectic part is `transvectionEquiv v`;
* `cliffordSign_rotGate` — `cliffordSign (rotGate v) = iZ4 ∘ rotSign v`, where `rotSign` is an
  explicit ℤ/4 expression in `ω`, `xzWeight`, `zDotVal` (frame objects);
* `rotSign_validity` — the cochain satisfies the frame's `tvSign_validity` identity for EVERY
  `v`, transported from `cliffordSign_cocycle` through `iZ4`/`clog` — so the frame's
  signed-stabilizer action extends to every transvection;
* `rotSign_pauliz` + `rotGate_pauliz_eq_phaseGate` — on basis directions the cochain IS
  `tvSignZ`, so by the selection theorem **`rotGate (Z_k)` equals the S gate mod phase** — the
  phase gate re-derived from sign data alone, no matrix comparison.

**The global quadratic does not extend.** The naive global statement — "the
supp-restricted global quadratic `2·xzWeight` is the sign cochain of a lift for every
transvection" — is **false** for entangling directions: `no_lift_with_global_quadratic_sign`
shows no lift of `τ_{Z₀Z₁}` on two qubits has sign character `iZ4 ∘ (2·xzWeight)`, because that
restriction fails to be a group character on the fixed subgroup (violating
`cliffordSign_char_on_fix`; witness labels `Y₀X₁` and `Z₀`). The uniform-quadratic phenomenon is
strictly per-plane; for entangling `v` the selected cochain is the genuinely `v`-dependent
`rotSign v`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame Complex

variable {n : ℕ}

/-! ## Parity and cochain helpers -/

private lemma zmod2_cases' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-- `zDot` is additive mod 2 in its vector argument. -/
lemma zDotVal_cast_add_right (p : Pauli n) (a b : Fin n → ZMod 2) :
    ((zDotVal p (a + b) : ℕ) : ZMod 2)
      = ((zDotVal p a : ℕ) : ZMod 2) + ((zDotVal p b : ℕ) : ZMod 2) := by
  unfold zDotVal
  push_cast
  simp only [ZMod.natCast_zmod_val, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => mul_add _ _ _

/-- The symplectic form as the mod-2 sum of the two `zDot` pairings. -/
lemma omega_cast_zDotVal (p q : Pauli n) :
    ((zDotVal p q.X + zDotVal q p.X : ℕ) : ZMod 2) = omega p q := by
  unfold zDotVal omega
  push_cast
  simp only [ZMod.natCast_zmod_val]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `(−1)`-powers agree across a mod-2 equality of exponents. -/
lemma neg_one_pow_congr {a b : ℕ} (h : ((a : ℕ) : ZMod 2) = (b : ZMod 2)) :
    ((-1 : ℂ)) ^ a = (-1 : ℂ) ^ b := by
  have hm : a % 2 = b % 2 := (ZMod.natCast_eq_natCast_iff a b 2).mp h
  rcases Nat.even_or_odd a with ha | ha
  · have hb : Even b := by
      rw [Nat.even_iff] at ha ⊢
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]
  · have hb : Odd b := by
      rw [Nat.odd_iff] at ha ⊢
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]

/-- `(−1)`-powers flip across a mod-2 offset of exponents. -/
lemma neg_one_pow_flip {a b : ℕ} (h : ((a : ℕ) : ZMod 2) = (b : ZMod 2) + 1) :
    ((-1 : ℂ)) ^ a = -((-1 : ℂ) ^ b) := by
  have hm : a % 2 = (b + 1) % 2 := (ZMod.natCast_eq_natCast_iff a (b + 1) 2).mp (by push_cast; exact h)
  rcases Nat.even_or_odd b with hb | hb
  · have ha : Odd a := by
      rw [Nat.even_iff] at hb
      rw [Nat.odd_iff]
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]
  · have ha : Even a := by
      rw [Nat.odd_iff] at hb
      rw [Nat.even_iff]
      omega
    rw [ha.neg_one_pow, hb.neg_one_pow]
    norm_num

/-- `iZ4` of a difference. -/
lemma iZ4_sub (a b : ZMod 4) : iZ4 (a - b) = iZ4 a * (iZ4 b)⁻¹ := by
  have hne : iZ4 b ≠ 0 := by
    unfold iZ4
    exact pow_ne_zero _ Complex.I_ne_zero
  have h := iZ4_add (a - b) b
  rw [sub_add_cancel] at h
  rw [eq_mul_inv_iff_mul_eq₀ hne]
  exact h.symm

/-- A bare Pauli squares to `(−1)^{xz}`. -/
lemma pauliOperator_comp_self (v : Pauli n) :
    pauliOperator v ∘ₗ pauliOperator v = ((-1 : ℂ) ^ xzWeight v) • LinearMap.id := by
  rw [pauliOperator_mul v v, pauli_add_self, pauliOperator_zero]
  rfl

/-- Transvections are involutions (apply level). -/
lemma transvectionEquiv_invol (v p : Pauli n) :
    transvectionEquiv v (transvectionEquiv v p) = p := by
  rw [transvectionEquiv_apply, transvectionEquiv_apply, omega_add_right, omega_smul_right,
    omega_self, mul_zero, add_zero, add_assoc, ← add_smul]
  rw [show omega v p + omega v p = 0 from CharTwo.add_self_eq_zero _, zero_smul, add_zero]

/-! ## The rotation lift -/

/-- The Hermitianizing coefficient: `−i·I^{xz v}`, so that `(c·P_v)² = −1`. -/
noncomputable def rotCoeff (v : Pauli n) : ℂ := -Complex.I * Complex.I ^ xzWeight v

lemma rotCoeff_sq (v : Pauli n) : rotCoeff v ^ 2 = -((-1 : ℂ) ^ xzWeight v) := by
  unfold rotCoeff
  rw [mul_pow, show (-Complex.I) ^ 2 = -1 from by
      rw [neg_pow]
      norm_num [Complex.I_sq],
    ← pow_mul, mul_comm (xzWeight v) 2, pow_mul, Complex.I_sq]
  ring

lemma rotCoeff_ne_zero (v : Pauli n) : rotCoeff v ≠ 0 := by
  unfold rotCoeff
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (pow_ne_zero _ Complex.I_ne_zero)

noncomputable def rotLin (v : Pauli n) : QubitSpace n →ₗ[ℂ] QubitSpace n :=
  (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (LinearMap.id + rotCoeff v • pauliOperator v)

noncomputable def rotInvLin (v : Pauli n) : QubitSpace n →ₗ[ℂ] QubitSpace n :=
  (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (LinearMap.id + (-rotCoeff v) • pauliOperator v)

lemma sqrt_two_inv_sq :
    ((((Real.sqrt 2 : ℝ) : ℂ)))⁻¹ * ((((Real.sqrt 2 : ℝ) : ℂ)))⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The general two-factor product in the rotation algebra. -/
lemma rot_mul_aux (v : Pauli n) (a b : ℂ) :
    (LinearMap.id + a • pauliOperator v) ∘ₗ (LinearMap.id + b • pauliOperator v)
      = (1 + a * b * (-1 : ℂ) ^ xzWeight v) • LinearMap.id + (a + b) • pauliOperator v := by
  rw [LinearMap.add_comp, LinearMap.id_comp, LinearMap.smul_comp, LinearMap.comp_add,
    LinearMap.comp_id, LinearMap.comp_smul, pauliOperator_comp_self]
  module

lemma rotLin_comp_rotInvLin (v : Pauli n) : rotLin v ∘ₗ rotInvLin v = LinearMap.id := by
  unfold rotLin rotInvLin
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, sqrt_two_inv_sq, rot_mul_aux]
  rw [show rotCoeff v * -rotCoeff v * (-1 : ℂ) ^ xzWeight v = 1 from by
      have h := rotCoeff_sq v
      have h2 : rotCoeff v * -rotCoeff v = (-1 : ℂ) ^ xzWeight v := by
        rw [mul_neg, ← sq, h]
        ring
      rw [h2, ← pow_add, ← two_mul, pow_mul]
      norm_num,
    show rotCoeff v + -rotCoeff v = 0 from by ring, zero_smul, add_zero]
  rw [show (1 : ℂ) + 1 = 2 from by norm_num, smul_smul]
  norm_num

lemma rotInvLin_comp_rotLin (v : Pauli n) : rotInvLin v ∘ₗ rotLin v = LinearMap.id := by
  unfold rotLin rotInvLin
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, sqrt_two_inv_sq, rot_mul_aux]
  rw [show -rotCoeff v * rotCoeff v * (-1 : ℂ) ^ xzWeight v = 1 from by
      have h := rotCoeff_sq v
      have h2 : -rotCoeff v * rotCoeff v = (-1 : ℂ) ^ xzWeight v := by
        rw [neg_mul, ← sq, h]
        ring
      rw [h2, ← pow_add, ← two_mul, pow_mul]
      norm_num,
    show -rotCoeff v + rotCoeff v = 0 from by ring, zero_smul, add_zero]
  rw [show (1 : ℂ) + 1 = 2 from by norm_num, smul_smul]
  norm_num

/-- **The transvection lift**: `rotGate v = (1 − i·I^{xz v}·P_v)/√2`, normalized so that
`rotGate (Z_k)` is the S gate mod phase (`rotGate_pauliz_eq_phaseGate` below). -/
noncomputable def rotGate (v : Pauli n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  LinearEquiv.ofLinear (rotLin v) (rotInvLin v) (rotLin_comp_rotInvLin v)
    (rotInvLin_comp_rotLin v)

/-! ## The conjugation law -/

/-- **The rotation conjugation law**: `rotGate v` conjugates `P_r` to `P_{τ_v r}`, with phase `1`
on the commuting set and `rotCoeff v · (−1)^{zDot v r.X}` on the anticommuting set. -/
theorem rotGate_conj (v r : Pauli n) :
    (conjEquiv (rotGate v) (pauliEquiv r)).toLinearMap
      = (if omega v r = 0 then (1 : ℂ)
          else rotCoeff v * (-1 : ℂ) ^ zDotVal v r.X) • pauliOperator (transvectionEquiv v r) := by
  have hcomp : (conjEquiv (rotGate v) (pauliEquiv r)).toLinearMap
      = rotLin v ∘ₗ pauliOperator r ∘ₗ rotInvLin v :=
    LinearMap.ext fun _ => rfl
  -- expand the sandwich
  have hexp : rotLin v ∘ₗ pauliOperator r ∘ₗ rotInvLin v
      = (2 : ℂ)⁻¹ • ((1 - rotCoeff v * rotCoeff v
              * (-1 : ℂ) ^ (zDotVal r v.X + zDotVal v (v + r).X)) • pauliOperator r
          + (rotCoeff v * ((-1 : ℂ) ^ zDotVal v r.X - (-1 : ℂ) ^ zDotVal r v.X))
              • pauliOperator (v + r)) := by
    unfold rotLin rotInvLin
    rw [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, sqrt_two_inv_sq]
    congr 1
    rw [LinearMap.comp_add, LinearMap.comp_id, LinearMap.comp_smul, pauliOperator_mul v r,
      LinearMap.add_comp, LinearMap.id_comp, LinearMap.smul_comp, LinearMap.comp_add,
      LinearMap.comp_smul, pauliOperator_mul r v,
      show pauliOperator v ∘ₗ ((-1 : ℂ) ^ zDotVal r v.X • pauliOperator (v + r))
          = ((-1 : ℂ) ^ zDotVal r v.X * (-1 : ℂ) ^ zDotVal v (v + r).X)
              • pauliOperator r from by
        rw [LinearMap.comp_smul, pauliOperator_mul (v + r) v,
          show v + r + v = r from by rw [add_comm v r, add_assoc, pauli_add_self, add_zero],
          smul_smul],
      show r + v = v + r from add_comm r v]
    module
  rw [hcomp, hexp]
  -- case split on the commutator
  rcases zmod2_cases' (omega v r) with h | h
  · rw [if_pos h]
    -- parities: zDot v rX ≡ zDot r vX, and the double exponent ≡ xz v
    have hΩ := omega_cast_zDotVal v r
    rw [h] at hΩ
    push_cast at hΩ
    have hpar : ((zDotVal v r.X : ℕ) : ZMod 2) = ((zDotVal r v.X : ℕ) : ZMod 2) := by
      have := hΩ
      rw [add_eq_zero_iff_eq_neg] at this
      rw [this, CharTwo.neg_eq]
    have hcancel : ((-1 : ℂ)) ^ zDotVal v r.X - (-1 : ℂ) ^ zDotVal r v.X = 0 := by
      rw [neg_one_pow_congr hpar, sub_self]
    have hdouble : ((-1 : ℂ)) ^ (zDotVal r v.X + zDotVal v (v + r).X)
        = (-1 : ℂ) ^ xzWeight v := by
      apply neg_one_pow_congr
      push_cast
      rw [show (v + r).X = v.X + r.X from rfl, zDotVal_cast_add_right]
      have hxz : ((zDotVal v v.X : ℕ) : ZMod 2) = ((xzWeight v : ℕ) : ZMod 2) := by
        rfl
      rw [← hxz]
      -- zd r vX + (zd v vX + zd v rX) = zd v vX  given zd v rX = zd r vX (char 2)
      rw [← hpar]
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero, zero_add]
    have hτ : transvectionEquiv v r = r := by
      rw [transvectionEquiv_apply, h, zero_smul, add_zero]
    rw [hcancel, mul_zero, zero_smul, add_zero, hdouble, hτ]
    rw [show rotCoeff v * rotCoeff v = -((-1 : ℂ) ^ xzWeight v) from by
        rw [← sq]
        exact rotCoeff_sq v]
    rw [show (1 : ℂ) - -(-1 : ℂ) ^ xzWeight v * (-1 : ℂ) ^ xzWeight v = 2 from by
        rw [neg_mul, sub_neg_eq_add, ← pow_add, ← two_mul, pow_mul]
        norm_num]
    rw [smul_smul]
    norm_num
  · rw [if_neg (by rw [h]; exact one_ne_zero)]
    -- parities: zDot r vX ≡ zDot v rX + 1, and the double exponent ≡ xz v + 1
    have hΩ := omega_cast_zDotVal v r
    rw [h] at hΩ
    push_cast at hΩ
    have hflip : ((zDotVal r v.X : ℕ) : ZMod 2) = ((zDotVal v r.X : ℕ) : ZMod 2) + 1 := by
      have : ((zDotVal r v.X : ℕ) : ZMod 2)
          = 1 - ((zDotVal v r.X : ℕ) : ZMod 2) := by
        rw [← hΩ]
        ring
      rw [this, CharTwo.sub_eq_add, add_comm]
    have hdiff : ((-1 : ℂ)) ^ zDotVal v r.X - (-1 : ℂ) ^ zDotVal r v.X
        = 2 * (-1 : ℂ) ^ zDotVal v r.X := by
      rw [neg_one_pow_flip hflip]
      ring
    have hdouble : ((-1 : ℂ)) ^ (zDotVal r v.X + zDotVal v (v + r).X)
        = -((-1 : ℂ) ^ xzWeight v) := by
      apply neg_one_pow_flip
      push_cast
      rw [show (v + r).X = v.X + r.X from rfl, zDotVal_cast_add_right]
      have hxz : ((zDotVal v v.X : ℕ) : ZMod 2) = ((xzWeight v : ℕ) : ZMod 2) := by
        rfl
      rw [← hxz, hflip]
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
    have hτ : transvectionEquiv v r = v + r := by
      rw [transvectionEquiv_apply, h, one_smul, add_comm]
    rw [hdiff, hdouble, hτ]
    rw [show rotCoeff v * rotCoeff v = -((-1 : ℂ) ^ xzWeight v) from by
        rw [← sq]
        exact rotCoeff_sq v]
    rw [show (1 : ℂ) - -(-1 : ℂ) ^ xzWeight v * -(-1 : ℂ) ^ xzWeight v = 0 from by
        rw [neg_mul_neg, ← pow_add, ← two_mul, pow_mul]
        norm_num]
    rw [zero_smul, zero_add, smul_smul]
    congr 1
    ring

/-! ## Clifford structure and the frame cochain -/

theorem isCliffordOperator_rotGate (v : Pauli n) : IsCliffordOperator (rotGate v) := by
  intro r
  rcases zmod2_cases' (omega v r) with h | h
  · refine ⟨1, transvectionEquiv v r, ?_⟩
    rw [rotGate_conj, if_pos h, Units.val_one]
  · refine ⟨Units.mk0 (rotCoeff v * (-1 : ℂ) ^ zDotVal v r.X)
      (mul_ne_zero (rotCoeff_ne_zero v) (pow_ne_zero _ (by norm_num))),
      transvectionEquiv v r, ?_⟩
    rw [rotGate_conj, if_neg (by rw [h]; exact one_ne_zero)]
    rfl

/-- The rotation lift's symplectic part is the transvection — for EVERY label `v`. -/
theorem cliffordFun_rotGate (v r : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_rotGate v) r = transvectionEquiv v r := by
  rcases zmod2_cases' (omega v r) with h | h
  · exact cliffordFun_eq_of_conj _ (α := 1) (by rw [rotGate_conj, if_pos h, Units.val_one])
  · exact cliffordFun_eq_of_conj _
      (α := Units.mk0 (rotCoeff v * (-1 : ℂ) ^ zDotVal v r.X)
        (mul_ne_zero (rotCoeff_ne_zero v) (pow_ne_zero _ (by norm_num))))
      (by rw [rotGate_conj, if_neg (by rw [h]; exact one_ne_zero)]; rfl)

/-- **The general transvection sign cochain**, frame-native: supported on the anticommuting set,
where it is the explicit ℤ/4 expression `3 + xz v + 2·zDot v r.X + xz r − xz(v+r)`. On basis
directions it collapses to `tvSignZ` (`rotSign_pauliz`). -/
noncomputable def rotSign (v r : Pauli n) : ZMod 4 :=
  if omega v r = 0 then 0
  else ((3 + xzWeight v + 2 * zDotVal v r.X + xzWeight r : ℕ) : ZMod 4)
    - ((xzWeight (v + r) : ℕ) : ZMod 4)

/-- **Every transvection's lift carries the frame cochain** —
`cliffordSign (rotGate v) r = iZ4 (rotSign v r)`, globally in `v` and `r`. -/
theorem cliffordSign_rotGate (v r : Pauli n) :
    cliffordSign (isCliffordOperator_rotGate v) r = iZ4 (rotSign v r) := by
  rcases zmod2_cases' (omega v r) with h | h
  · have hconj : (conjEquiv (rotGate v) (pauliEquiv r)).toLinearMap
        = ((1 : ℂˣ) : ℂ) • pauliOperator (transvectionEquiv v r) := by
      rw [rotGate_conj, if_pos h, Units.val_one]
    have hs := cliffordSign_eq_of_conj (isCliffordOperator_rotGate v) hconj
    have hτ : transvectionEquiv v r = r := by
      rw [transvectionEquiv_apply, h, zero_smul, add_zero]
    rw [hs, hτ, Units.val_one, mul_one,
      mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero)]
    rw [rotSign, if_pos h]
    unfold iZ4
    norm_num
  · have hconj : (conjEquiv (rotGate v) (pauliEquiv r)).toLinearMap
        = ((Units.mk0 (rotCoeff v * (-1 : ℂ) ^ zDotVal v r.X)
            (mul_ne_zero (rotCoeff_ne_zero v) (pow_ne_zero _ (by norm_num))) : ℂˣ) : ℂ)
          • pauliOperator (transvectionEquiv v r) := by
      rw [rotGate_conj, if_neg (by rw [h]; exact one_ne_zero)]
      rfl
    have hs := cliffordSign_eq_of_conj (isCliffordOperator_rotGate v) hconj
    have hτ : transvectionEquiv v r = v + r := by
      rw [transvectionEquiv_apply, h, one_smul, add_comm]
    rw [hs, hτ]
    rw [rotSign, if_neg (by rw [h]; exact one_ne_zero), iZ4_sub, iZ4_natCast, iZ4_natCast]
    show Complex.I ^ xzWeight r
        * (rotCoeff v * (-1 : ℂ) ^ zDotVal v r.X)
        * (Complex.I ^ xzWeight (v + r))⁻¹
      = Complex.I ^ (3 + xzWeight v + 2 * zDotVal v r.X + xzWeight r)
        * (Complex.I ^ xzWeight (v + r))⁻¹
    congr 1
    unfold rotCoeff
    rw [show (-Complex.I : ℂ) = Complex.I ^ 3 from by
        rw [pow_succ, Complex.I_sq]
        ring,
      show ((-1 : ℂ)) ^ zDotVal v r.X = Complex.I ^ (2 * zDotVal v r.X) from by
        rw [pow_mul, Complex.I_sq]]
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring

/-- **The validity identity for EVERY transvection** — the frame-side consistency law
(`tvSign_validity`'s shape) for `rotSign v`, any `v`. Transported from `cliffordSign_cocycle`
through `iZ4`/`clog`: the frame's signed-stabilizer action extends to all transvections. -/
theorem rotSign_validity (v p q : Pauli n) :
    rotSign v (transvectionEquiv v p) + rotSign v (transvectionEquiv v q)
      - rotSign v (transvectionEquiv v (p + q))
      = betaFrame (transvectionEquiv v p) (transvectionEquiv v q) - betaFrame p q := by
  have hc := cliffordSign_cocycle (isCliffordOperator_rotGate v)
    (transvectionEquiv v p) (transvectionEquiv v q)
  rw [cliffordFun_rotGate, cliffordFun_rotGate, transvectionEquiv_invol, transvectionEquiv_invol,
    cliffordSign_rotGate, cliffordSign_rotGate,
    show transvectionEquiv v p + transvectionEquiv v q = transvectionEquiv v (p + q) from
      (map_add (transvectionEquiv v) p q).symm,
    cliffordSign_rotGate, pauliPhase_eq_iZ4_betaFrame, pauliPhase_eq_iZ4_betaFrame,
    ← iZ4_add, ← iZ4_add, ← iZ4_add] at hc
  have h4 := congrArg clog hc
  rw [clog_iZ4, clog_iZ4] at h4
  linear_combination h4

/-! ## Specialization: the basis directions recover the S gate -/

/-- `τ_{Z_k}` is the frame's `phaseAt` shear. -/
lemma transvection_pauliz_eq_phaseAt (k : Fin n) (p : Pauli n) :
    transvectionEquiv (pauliz k) p = phaseAt k p := by
  rw [transvectionEquiv_apply, omega_pauliz_apply]
  rcases zmod2_cases' (p.X k) with hx | hx <;> rw [hx]
  · rw [zero_smul, add_zero]
    exact ((phaseAt_fixed_iff k p).mpr hx).symm
  · rw [one_smul]
    refine Pauli.ext ?_ ?_
    · rw [X_add, pauliz_X, add_zero, phaseAt_X]
    · funext i
      rw [Z_add, pauliz_Z, phaseAt_Z, Pi.add_apply]
      by_cases hik : i = k
      · subst hik
        rw [Function.update_self, Pi.single_eq_same, hx]
      · rw [Function.update_of_ne hik, Pi.single_eq_of_ne hik, add_zero]

/-- The k-split of the `xz`-weight. -/
lemma xzWeight_split (k : Fin n) (p : Pauli n) :
    xzWeight p
      = (p.Z k).val * (p.X k).val + ∑ i ∈ Finset.univ.erase k, (p.Z i).val * (p.X i).val := by
  unfold xzWeight zDotVal
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]

/-- **On basis directions the general cochain IS the frame's `tvSignZ`.** -/
theorem rotSign_pauliz (k : Fin n) (r : Pauli n) : rotSign (pauliz k) r = tvSignZ k r := by
  unfold rotSign
  rcases zmod2_cases' (omega (pauliz k) r) with h | h
  · rw [if_pos h]
    rw [omega_pauliz_apply] at h
    unfold tvSignZ
    rw [h]
    simp
  · rw [if_neg (by rw [h]; exact one_ne_zero)]
    rw [omega_pauliz_apply] at h
    -- the off-k parts of `xz r` and `xz (Z_k + r)` agree
    have hoff : (∑ i ∈ Finset.univ.erase k, (((pauliz k + r).Z i).val * ((pauliz k + r).X i).val))
        = ∑ i ∈ Finset.univ.erase k, ((r.Z i).val * (r.X i).val) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≠ k := (Finset.mem_erase.mp hi).1
      rw [X_add, Z_add, pauliz_X, pauliz_Z, Pi.add_apply, Pi.add_apply, Pi.zero_apply,
        Pi.single_eq_of_ne hik, zero_add, zero_add]
    have hxzv : xzWeight (pauliz k) = 0 := xzWeight_pauliz k
    have hzd : zDotVal (pauliz k) r.X = 1 := by
      rw [show zDotVal (pauliz k) r.X = ((r.X k).val) from zDotVal_pauliz k r.X, h]
      decide
    have hk1 : ((pauliz k + r).Z k).val * ((pauliz k + r).X k).val
        = (1 + r.Z k).val * (r.X k).val := by
      rw [X_add, Z_add, pauliz_X, pauliz_Z, Pi.add_apply, Pi.add_apply, Pi.zero_apply,
        Pi.single_eq_same, zero_add]
    unfold tvSignZ
    rcases zmod2_cases' (r.Z k) with hz | hz
    · have h1 : xzWeight (pauliz k + r) = xzWeight r + 1 := by
        rw [xzWeight_split k (pauliz k + r), xzWeight_split k r, hoff, hk1, h, hz]
        norm_num [show ((0 : ZMod 2)).val = 0 from rfl,
          show ((1 : ZMod 2)).val = 1 from by decide,
          show ((1 : ZMod 2) + 0) = 1 from rfl]
        omega
      rw [h1, hxzv, hzd, h, hz]
      push_cast
      ring_nf
      decide
    · have h1 : xzWeight r = xzWeight (pauliz k + r) + 1 := by
        rw [xzWeight_split k (pauliz k + r), xzWeight_split k r, hoff, hk1, h, hz]
        norm_num [show ((0 : ZMod 2)).val = 0 from rfl,
          show ((1 : ZMod 2)).val = 1 from by decide,
          show ((2 : ZMod 2)).val = 0 from by decide]
        omega
      rw [h1, hxzv, hzd, h, hz]
      push_cast
      ring_nf
      decide

/-- **The S gate, re-derived from sign data alone**: `rotGate (Z_k)` has the shear's symplectic
part and the frame cochain as sign character, so by the selection theorem it IS the phase gate
mod global phase — no matrix comparison anywhere. -/
theorem rotGate_pauliz_eq_phaseGate (k : Fin n) :
    ∃ α : ℂˣ, (rotGate (pauliz k)).toLinearMap = (α : ℂ) • (phaseGate k).toLinearMap := by
  refine frame_selects_phaseGate k (isCliffordOperator_rotGate (pauliz k)) ?_ ?_
  · refine LinearEquiv.ext fun p => ?_
    rw [cliffordToSymplectic_apply, cliffordToSymplectic_apply, cliffordFun_rotGate,
      cliffordFun_phase, transvection_pauliz_eq_phaseAt]
  · intro r
    rw [cliffordSign_rotGate, rotSign_pauliz]

/-! ## The negative theorem: the global quadratic does NOT extend -/

/-- **The global-quadratic sign is false for entangling directions**: no Clifford lift of
`τ_{Z₀Z₁}` on two qubits has sign character `iZ4 ∘ (2·xzWeight)`. The would-be cochain fails to
be a group character on the fixed subgroup — `Y₀X₁` and `Z₀` are both fixed with values `−1` and
`+1`, but their sum `X₀X₁` gets `+1` — contradicting `cliffordSign_char_on_fix`. Uniform
quadratic sign data is a strictly per-plane phenomenon. -/
theorem no_lift_with_global_quadratic_sign :
    ¬ ∃ (U : QubitSpace 2 ≃ₗ[ℂ] QubitSpace 2) (hU : IsCliffordOperator U),
      (∀ p, cliffordToSymplecticFun hU p = transvectionEquiv (pauliz 0 + pauliz 1) p) ∧
      (∀ r, cliffordSign hU r = iZ4 ((2 * xzWeight r : ℕ) : ZMod 4)) := by
  rintro ⟨U, hU, hFun, hSign⟩
  set a : Pauli 2 := yLabel 0 + paulix 1 with ha_def
  set b : Pauli 2 := pauliz 0 with hb_def
  have hΩa : omega (pauliz 0 + pauliz 1) a = 0 := by
    rw [ha_def]
    unfold yLabel
    decide +kernel
  have hΩb : omega (pauliz 0 + pauliz 1) b = 0 := by
    rw [hb_def]
    decide +kernel
  have ha : cliffordToSymplecticFun hU a = a := by
    rw [hFun, transvectionEquiv_apply, hΩa, zero_smul, add_zero]
  have hb : cliffordToSymplecticFun hU b = b := by
    rw [hFun, transvectionEquiv_apply, hΩb, zero_smul, add_zero]
  have hchar := cliffordSign_char_on_fix hU ha hb
  rw [hSign, hSign, hSign] at hchar
  have hwa : xzWeight a = 1 := by
    rw [ha_def]
    unfold yLabel
    decide +kernel
  have hwb : xzWeight b = 0 := by
    rw [hb_def]
    decide +kernel
  have hwab : xzWeight (a + b) = 0 := by
    rw [ha_def, hb_def]
    unfold yLabel
    decide +kernel
  rw [hwa, hwb, hwab] at hchar
  rw [show ((2 * 1 : ℕ) : ZMod 4) = 2 from by decide,
    show ((2 * 0 : ℕ) : ZMod 4) = 0 from by decide] at hchar
  rw [show iZ4 (2 : ZMod 4) = -1 from by
      unfold iZ4
      rw [show ((2 : ZMod 4)).val = 2 from rfl]
      rw [sq]
      norm_num [Complex.I_mul_I],
    show iZ4 (0 : ZMod 4) = 1 from by
      unfold iZ4
      norm_num] at hchar
  norm_num at hchar

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.FrameBridgeAmplitudeCore

/-! # Discharging the Dehaene–De Moor core `CosetAmplitudeQuadForm`

This file proves `cosetAmplitudeQuadForm_holds : ∀ n, CosetAmplitudeQuadForm n`, the hypothesis
to which `FrameBridgeAmplitude.lean` / `FrameBridgeAmplitudeCore.lean` reduce the bridge theorem.

`CosetAmplitudeQuadForm n` asks, for a full Lagrangian `S`, a nonzero joint eigenvector `ψ`, and
a base point `x₀` with `ψ x₀ ≠ 0`, for a `BooleanQuadForm e` (a `ZMod 4`-valued Boolean-degree-≤2
phase) whose `μ₄` reading reproduces the amplitude factor on the support coset:

  `iZ4 (e (x₀ + p.X)) = amplitudeFactor S x₀ p = S.sign p · I^{xzWeight p} · (-1)^{p.Z·x₀}`.

## The construction

The amplitude factor `F p = amplitudeFactor S x₀ p` satisfies a clean **cocycle law** on the
Lagrangian `L` (`amplitudeFactor_cocycle`):

  `F (p + q) = F p · F q · (-1)^{zDotVal q p.X}`,    `p, q ∈ L`,

with bilinear "defect" `(-1)^{q.Z · p.X}`. This is `Dehaene–De Moor`: `F` is a `μ₄`-valued
quadratic form on `L` whose associated bilinear form is `(-1)^{q.Z · p.X}`.

Rather than picking a basis and writing the explicit double-sum, we realise `e` directly:

* a `ZMod 2`-linear lift `Λ : (Fin n → ZMod 2) →ₗ Pauli n` landing in `L` (`exists_piX_lift` of
  the X-projection `π_X(L)`, precomposed with the projection onto `π_X(L)`), so that `Λ v ∈ L`
  always and `Λ (p.X) = p` "up to X-part" for `p ∈ L`;
* a `μ₄`-logarithm `clog : ℂ → ZMod 4` inverting `iZ4` on `μ₄`;
* `e w := clog (F (Λ (w - x₀)))`.

The **match** is then almost definitional: `Λ (x₀ + p.X - x₀) = Λ p.X` has the same X-part as
`p`, so `F (Λ p.X) = F p` (`amplitudeFactor_eq_of_X_eq`), and `iZ4 (clog (F p)) = F p` since
`F p ∈ μ₄`.

The **`BooleanQuadForm`** is the differential criterion `booleanQuadForm_of_differential`. The
cocycle makes the first difference of `e` split off a constant plus `clog ((-1)^{·})`; the second
difference is therefore the *constant* `clog ((-1)^{zDotVal δ_k δ_j.X})` (bilinear defect,
independent of `w`); the third difference of a constant vanishes, and the pair coefficient is
`clog` of a sign, so it lies in `{0,2}` and is even.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hilbert FTQCLib.Hierarchy FTQCLib.Pauli FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ}

/-! ### `μ₄` membership of the basic phase factors -/

/-- Every power of `i` is one of the four fourth roots of unity. -/
theorem iPow_mem_mu4 (k : ℕ) :
    Complex.I ^ k = 1 ∨ Complex.I ^ k = Complex.I ∨ Complex.I ^ k = -1 ∨
      Complex.I ^ k = -Complex.I := by
  rw [Complex.I_pow_eq_pow_mod]
  have hlt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 4
  · left; rw [pow_zero]
  · right; left; rw [pow_one]
  · right; right; left; rw [pow_two, Complex.I_mul_I]
  · right; right; right
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two, Complex.I_mul_I, pow_one, neg_one_mul]

/-- A sign `(-1)^m` is `±1`. -/
theorem neg_one_pow_mem (m : ℕ) : (-1 : ℂ) ^ m = 1 ∨ (-1 : ℂ) ^ m = -1 := by
  rcases Nat.even_or_odd m with he | ho
  · left; exact he.neg_one_pow
  · right; exact ho.neg_one_pow

/-- Membership in `μ₄ = {1, I, -1, -I}`. -/
def IsMu4 (z : ℂ) : Prop := z = 1 ∨ z = Complex.I ∨ z = -1 ∨ z = -Complex.I

theorem isMu4_one : IsMu4 1 := Or.inl rfl
theorem isMu4_I : IsMu4 Complex.I := Or.inr (Or.inl rfl)
theorem isMu4_neg_one : IsMu4 (-1) := Or.inr (Or.inr (Or.inl rfl))
theorem isMu4_iPow (k : ℕ) : IsMu4 (Complex.I ^ k) := iPow_mem_mu4 k

theorem isMu4_neg_one_pow (m : ℕ) : IsMu4 ((-1 : ℂ) ^ m) := by
  rcases neg_one_pow_mem m with h | h
  · rw [h]; exact isMu4_one
  · rw [h]; exact isMu4_neg_one

theorem isMu4_neg_I : IsMu4 (-Complex.I) := Or.inr (Or.inr (Or.inr rfl))

/-- `μ₄` is closed under multiplication. -/
theorem isMu4_mul {a b : ℂ} (ha : IsMu4 a) (hb : IsMu4 b) : IsMu4 (a * b) := by
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have e1 : (-1 : ℂ) * Complex.I = -Complex.I := by ring
  have e2 : Complex.I * (-1 : ℂ) = -Complex.I := by ring
  have e3 : (-1 : ℂ) * (-1) = 1 := by ring
  have e4 : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, hI2, neg_neg]
  have e5 : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, hI2, neg_neg]
  have e6 : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, hI2]
  have e7 : (-Complex.I) * (-1 : ℂ) = Complex.I := by ring
  have e8 : (-1 : ℂ) * (-Complex.I) = Complex.I := by ring
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, hI2, e1, e2, e3, e4, e5, e6, e7, e8] <;>
    first
      | exact isMu4_one | exact isMu4_I | exact isMu4_neg_one | exact isMu4_neg_I

/-! ### The `μ₄`-logarithm `clog`

`clog z = 0,1,2,3` for `z = 1, I, -1, -I`. It inverts `iZ4` on `μ₄` (`iZ4_clog`) and is additive
there (`clog_mul`), so `e := clog ∘ (amplitude factor) ∘ lift` reads the `μ₄` factor back. -/

/-- The `μ₄`-logarithm: a section `ℂ → ZMod 4` of `iZ4` on the fourth roots of unity. -/
noncomputable def clog (z : ℂ) : ZMod 4 :=
  if z = 1 then 0 else if z = Complex.I then 1 else if z = -1 then 2 else 3

theorem clog_one : clog 1 = 0 := if_pos rfl
theorem clog_I : clog Complex.I = 1 := by
  have h1 : Complex.I ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this
  unfold clog; rw [if_neg h1, if_pos rfl]
theorem clog_neg_one : clog (-1 : ℂ) = 2 := by
  have h1 : (-1 : ℂ) ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num at this
  have h2 : (-1 : ℂ) ≠ Complex.I := by intro h; have := congrArg Complex.im h; simp at this
  unfold clog; rw [if_neg h1, if_neg h2, if_pos rfl]
theorem clog_neg_I : clog (-Complex.I) = 3 := by
  unfold clog
  have h1 : (-Complex.I) ≠ 1 := by
    intro h; have := congrArg Complex.im h; norm_num at this
  have h2 : (-Complex.I) ≠ Complex.I := by
    intro h; have := congrArg Complex.im h; norm_num at this
  have h3 : (-Complex.I) ≠ -1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- `clog` inverts `iZ4` on `μ₄`. -/
theorem iZ4_clog {z : ℂ} (hz : IsMu4 z) : iZ4 (clog z) = z := by
  rcases hz with rfl | rfl | rfl | rfl
  · rw [clog_one]; unfold iZ4; rw [show (0 : ZMod 4).val = 0 from rfl, pow_zero]
  · rw [clog_I]; unfold iZ4; rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]
  · rw [clog_neg_one]; unfold iZ4
    rw [show (2 : ZMod 4).val = 2 from rfl, pow_two, Complex.I_mul_I]
  · rw [clog_neg_I]; unfold iZ4
    rw [show (3 : ZMod 4).val = 3 from rfl, show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two,
      Complex.I_mul_I, pow_one, neg_one_mul]

/-- `clog` is additive on `μ₄`: `clog (a * b) = clog a + clog b`. Checked over the `4 × 4` table of
fourth roots of unity. -/
theorem clog_mul {a b : ℂ} (ha : IsMu4 a) (hb : IsMu4 b) :
    clog (a * b) = clog a + clog b := by
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hnegI : (-1 : ℂ) * Complex.I = -Complex.I := by ring
  have hII : Complex.I * (-1 : ℂ) = -Complex.I := by ring
  have hnn : (-1 : ℂ) * (-1) = 1 := by ring
  have hInI : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, hI2, neg_neg]
  have hnII : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, hI2, neg_neg]
  have hnInI : (-Complex.I) * (-Complex.I) = -1 := by rw [neg_mul_neg, hI2]
  have hnIn1 : (-Complex.I) * (-1 : ℂ) = Complex.I := by ring
  have hn1nI : (-1 : ℂ) * (-Complex.I) = Complex.I := by ring
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, hI2, hnegI, hII, hnn, hInI, hnII, hnInI, hnIn1, hn1nI,
      clog_one, clog_I, clog_neg_one, clog_neg_I] <;> decide

/-! ### `μ₄` membership of the amplitude factor -/

/-- For `p ∈ L` the amplitude factor is a fourth root of unity: `S.sign p = ±1`,
`I^{xzWeight p} ∈ μ₄`, and `(-1)^{·} = ±1`. -/
theorem isMu4_amplitudeFactor (S : SignedStab n) (x₀ : Fin n → ZMod 2)
    {p : Pauli n} (hp : p ∈ S.L) : IsMu4 (amplitudeFactor S x₀ p) := by
  unfold amplitudeFactor
  have hsign : IsMu4 (S.sign p) := by
    rcases mul_self_eq_one_iff.mp (sign_mul_self S hp) with h | h
    · rw [h]; exact isMu4_one
    · rw [h]; exact isMu4_neg_one
  exact isMu4_mul (isMu4_mul hsign (isMu4_iPow _)) (isMu4_neg_one_pow _)

/-! ### The amplitude-factor cocycle (Dehaene–De Moor)

The amplitude factor is a `μ₄`-valued quadratic form on `L`:
`F (p + q) = F p · F q · (-1)^{q.Z·p.X}`
with bilinear defect `(-1)^{q.Z·p.X}`. This is the engine of both the differential criterion and the
match. The proof expands `S.sign (p + q)` by `S.valid`, `pauliPhase` by its definition, collects the
`I^{xzWeight (p+q)}` square into `(-1)^{xzWeight (p+q)}`, cancels it against `(-1)^{zDotVal (p+q)
(p+q).X} = (-1)^{xzWeight (p+q)}`, and reconciles the `x₀` sign by `zDotVal` left-additivity. -/

/-- **The amplitude-factor cocycle.** For `p, q ∈ L`, the amplitude factor of `p + q` is the product
of the factors times the bilinear defect `(-1)^{zDotVal q p.X}`. -/
theorem amplitudeFactor_cocycle (S : SignedStab n) (x₀ : Fin n → ZMod 2)
    {p q : Pauli n} (hp : p ∈ S.L) (hq : q ∈ S.L) :
    amplitudeFactor S x₀ (p + q)
      = amplitudeFactor S x₀ p * amplitudeFactor S x₀ q * (-1 : ℂ) ^ zDotVal q p.X := by
  unfold amplitudeFactor
  have hval : S.sign (p + q) = S.sign q * S.sign p * pauliPhase p q := (S.valid p hp q hq).symm
  rw [hval]
  unfold pauliPhase
  have hxzdef : xzWeight (p + q) = zDotVal (p + q) (p + q).X := rfl
  have hIsq : Complex.I ^ xzWeight (p + q) * Complex.I ^ xzWeight (p + q)
      = (-1 : ℂ) ^ xzWeight (p + q) := by
    rw [← pow_add, ← two_mul, pow_mul, Complex.I_sq]
  have hcancel : (-1 : ℂ) ^ xzWeight (p + q)
      * (-1 : ℂ) ^ zDotVal (p + q) (p + q).X = 1 := by
    rw [hxzdef, ← pow_add, ← two_mul, pow_mul]; norm_num
  have hx0 : (-1 : ℂ) ^ zDotVal (p + q) x₀
      = (-1 : ℂ) ^ zDotVal p x₀ * (-1 : ℂ) ^ zDotVal q x₀ := by
    rw [← pow_add]
    exact neg_one_pow_eq_of_mod_two_eq (zDotVal_add_left_mod_two p q x₀)
  rw [hx0, pow_add]
  -- Group the `I^{xzWeight (p+q)}` square and the `(p+q).X` overlap sign into the defect.
  have hgroup : (-1 : ℂ) ^ zDotVal q p.X * (-1 : ℂ) ^ zDotVal (p + q) (p + q).X
      * (Complex.I ^ xzWeight (p + q) * Complex.I ^ xzWeight (p + q))
      = (-1 : ℂ) ^ zDotVal q p.X := by
    rw [hIsq]
    rw [show (-1 : ℂ) ^ zDotVal q p.X * (-1 : ℂ) ^ zDotVal (p + q) (p + q).X
          * (-1 : ℂ) ^ xzWeight (p + q)
        = (-1 : ℂ) ^ zDotVal q p.X
          * ((-1 : ℂ) ^ xzWeight (p + q) * (-1 : ℂ) ^ zDotVal (p + q) (p + q).X) from by ring]
    rw [hcancel, mul_one]
  linear_combination (S.sign p * S.sign q * Complex.I ^ xzWeight p * Complex.I ^ xzWeight q
    * (-1 : ℂ) ^ zDotVal p x₀ * (-1 : ℂ) ^ zDotVal q x₀) * hgroup

/-! ### The phase function `e` and its differences

`e w := clog (amplitudeFactor S x₀ (Λ (w - x₀)))`, where `Λ : (Fin n → ZMod 2) →ₗ Pauli n` is a
linear lift landing in `L` (`hΛmem`). The cocycle controls its discrete derivatives. -/

section Eform

variable (S : SignedStab n) (x₀ : Fin n → ZMod 2)
  (Λ : (Fin n → ZMod 2) →ₗ[ZMod 2] Pauli n) (hΛmem : ∀ w, Λ w ∈ S.L)

/-- The candidate phase function: `clog` of the amplitude factor of the lift of `w - x₀`. -/
noncomputable def eOf (w : Fin n → ZMod 2) : ZMod 4 :=
  clog (amplitudeFactor S x₀ (Λ (w - x₀)))

/-- The lift shifts by `Λ (Pi.single k 1) ∈ L` under the single derivative direction. -/
theorem Λ_shift (w : Fin n → ZMod 2) (k : Fin n) :
    Λ ((w + Pi.single k 1) - x₀) = Λ (w - x₀) + Λ (Pi.single k 1) := by
  rw [show (w + Pi.single k 1) - x₀ = (w - x₀) + Pi.single k 1 from by abel, map_add]

include hΛmem

/-- The `μ₄` value of `eOf` is the amplitude factor of the lift (since the latter is in `μ₄`). -/
theorem iZ4_eOf (w : Fin n → ZMod 2) :
    iZ4 (eOf S x₀ Λ w) = amplitudeFactor S x₀ (Λ (w - x₀)) :=
  iZ4_clog (isMu4_amplitudeFactor S x₀ (hΛmem _))

/-- **First difference of `eOf`.** Splits into the constant `clog (F δ_k)` and the `clog` of the
sign `(-1)^{zDotVal δ_k (Λ (w - x₀)).X}`, by the cocycle and `clog` additivity on `μ₄`. -/
theorem funcDerivG_eOf (k : Fin n) (w : Fin n → ZMod 2) :
    funcDerivG k (eOf S x₀ Λ) w
      = clog (amplitudeFactor S x₀ (Λ (Pi.single k 1)))
        + clog ((-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (w - x₀)).X) := by
  rw [funcDerivG_apply]
  unfold eOf
  rw [Λ_shift (x₀ := x₀) (Λ := Λ) (w := w) (k := k)]
  -- Cocycle for the sum at `Λ (w - x₀)` and `δ_k := Λ (Pi.single k 1)`.
  rw [amplitudeFactor_cocycle S x₀ (hΛmem (w - x₀)) (hΛmem (Pi.single k 1))]
  -- `clog (a * b * c) = clog a + clog b + clog c` for `a, b, c ∈ μ₄`.
  have ha : IsMu4 (amplitudeFactor S x₀ (Λ (w - x₀))) :=
    isMu4_amplitudeFactor S x₀ (hΛmem _)
  have hb : IsMu4 (amplitudeFactor S x₀ (Λ (Pi.single k 1))) :=
    isMu4_amplitudeFactor S x₀ (hΛmem _)
  have hc : IsMu4 ((-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (w - x₀)).X) := isMu4_neg_one_pow _
  rw [clog_mul (isMu4_mul ha hb) hc, clog_mul ha hb]
  abel

/-- **Second difference of `eOf` is constant.** It equals `clog ((-1)^{zDotVal δ_k δ_j.X})`, the
bilinear defect of the cocycle — independent of `w`. The variable part of the first difference is
`clog ((-1)^{zDotVal δ_k (Λ (w - x₀)).X})`, whose `j`-shift multiplies the sign by the constant
`(-1)^{zDotVal δ_k δ_j.X}`. -/
theorem funcDerivG_funcDerivG_eOf (j k : Fin n) (w : Fin n → ZMod 2) :
    funcDerivG j (funcDerivG k (eOf S x₀ Λ)) w
      = clog ((-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (Pi.single j 1)).X) := by
  rw [funcDerivG_apply, funcDerivG_eOf S x₀ Λ hΛmem k, funcDerivG_eOf S x₀ Λ hΛmem k]
  -- the constants `clog (F δ_k)` cancel; reduce the two signs.
  rw [Λ_shift (x₀ := x₀) (Λ := Λ) (w := w) (k := j)]
  -- `(Λ (w - x₀) + Λ δ_j).X = (Λ (w - x₀)).X + (Λ δ_j).X`
  rw [show (Λ (w - x₀) + Λ (Pi.single j 1)).X
        = (Λ (w - x₀)).X + (Λ (Pi.single j 1)).X from rfl]
  -- the sign over the sum splits (mod 2) into the product of the two signs.
  have hsplit : (-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1))
        ((Λ (w - x₀)).X + (Λ (Pi.single j 1)).X)
      = (-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (w - x₀)).X
        * (-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (Pi.single j 1)).X := by
    rw [← pow_add]
    exact neg_one_pow_eq_of_mod_two_eq
      (zDotVal_add_right_mod_two _ (Λ (w - x₀)).X (Λ (Pi.single j 1)).X)
  rw [hsplit]
  have hA : IsMu4 ((-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (w - x₀)).X) := isMu4_neg_one_pow _
  have hB : IsMu4 ((-1 : ℂ) ^ zDotVal (Λ (Pi.single k 1)) (Λ (Pi.single j 1)).X) :=
    isMu4_neg_one_pow _
  rw [clog_mul hA hB]
  abel

/-- **Third difference of `eOf` vanishes.** The second difference is constant
(`funcDerivG_funcDerivG_eOf`), so any further difference is zero. -/
theorem funcDerivG_third_eOf (i j k : Fin n) :
    funcDerivG i (funcDerivG j (funcDerivG k (eOf S x₀ Λ))) = 0 := by
  funext w
  rw [funcDerivG_apply, funcDerivG_funcDerivG_eOf S x₀ Λ hΛmem j k,
    funcDerivG_funcDerivG_eOf S x₀ Λ hΛmem j k, sub_self]
  rfl

/-- The pair Möbius coefficient of `eOf` is `clog` of a sign, hence in `{0, 2}` — even. -/
theorem two_dvd_mobiusCoeff_pair_eOf (T : Finset (Fin n)) (hT : T.card = 2) :
    2 ∣ (mobiusCoeff T (eOf S x₀ Λ)).val := by
  -- pick the two distinct elements
  obtain ⟨a, haT⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hbT⟩ : (T.erase a).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_erase_of_mem haT]; omega)
  have hbT' : b ∈ T := Finset.mem_of_mem_erase hbT
  -- T = {a, b}, so funcDerivSubset T = funcDerivG a (funcDerivG b ·) up to the empty tail.
  rw [mobiusCoeff_apply, funcDerivSubset_factor haT, funcDerivSubset_factor hbT]
  have heq : (T.erase a).erase b = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_erase_of_mem hbT, Finset.card_erase_of_mem haT, hT]
  rw [heq, funcDerivSubset_empty]
  -- now the value is `funcDerivG b (funcDerivG a (eOf …)) 0 = clog ((-1)^…)`.
  rw [funcDerivG_funcDerivG_eOf S x₀ Λ hΛmem b a]
  rcases neg_one_pow_mem (zDotVal (Λ (Pi.single a 1)) (Λ (Pi.single b 1)).X) with h | h
  · rw [h, clog_one]; exact ⟨0, by rw [ZMod.val_zero]⟩
  · rw [h, clog_neg_one]; exact ⟨1, by rw [show ((2 : ZMod 4)).val = 2 from rfl]⟩

/-- `eOf` is a `BooleanQuadForm`: third differences vanish (`funcDerivG_third_eOf`) and pair
coefficients are even (`two_dvd_mobiusCoeff_pair_eOf`). -/
theorem booleanQuadForm_eOf : BooleanQuadForm (eOf S x₀ Λ) :=
  booleanQuadForm_of_differential
    (fun i j k => funcDerivG_third_eOf S x₀ Λ hΛmem i j k)
    (fun T hT => two_dvd_mobiusCoeff_pair_eOf S x₀ Λ hΛmem T hT)

end Eform

/-! ### The lift `Λ` and `CosetAmplitudeQuadForm`

`Λ := τ ∘ (subtype) ∘ (projection onto π_X(L))`, where `τ` lifts `π_X(L)` into `L` linearly
(`exists_piX_lift`). It lands in `L` everywhere, and inverts the X-projection on `π_X(L)`. -/

/-- **The Dehaene–De Moor core, discharged.** For every `n`, `CosetAmplitudeQuadForm n` holds:
the amplitude factor on the support coset is realised by a global Boolean quadratic form `eOf`.
The match is `iZ4 ∘ clog = id` on `μ₄` plus `amplitudeFactor_eq_of_X_eq` (the lift `Λ p.X ∈ L`
has the same X-part as `p`); the `BooleanQuadForm` is the differential criterion
`booleanQuadForm_eOf`. -/
theorem cosetAmplitudeQuadForm_holds (n : ℕ) : CosetAmplitudeQuadForm n := by
  intro S ψ _hL _hψne _hψfix x₀ _hx₀ne
  -- The X-projection of `L`.
  set M : Submodule (ZMod 2) (Fin n → ZMod 2) := Submodule.map xProj S.L with hM
  -- A complement and the projection onto `M`.
  obtain ⟨N, hcompl⟩ := M.exists_isCompl
  set proj : (Fin n → ZMod 2) →ₗ[ZMod 2] ↥M := M.linearProjOfIsCompl N hcompl with hproj
  -- The linear lift of `M` into `L`.
  obtain ⟨τ, hτ⟩ := exists_piX_lift S.L
  -- The composite lift `Λ : (Fin n → ZMod 2) →ₗ Pauli n`.
  set Λ : (Fin n → ZMod 2) →ₗ[ZMod 2] Pauli n := τ ∘ₗ M.subtype ∘ₗ proj with hΛ
  -- `Λ w = τ ((proj w).val)`, and `(proj w).val ∈ M`, so `Λ w ∈ L`.
  have hΛapp : ∀ w, Λ w = τ ((proj w : Fin n → ZMod 2)) := fun w => rfl
  have hΛmem : ∀ w, Λ w ∈ S.L := by
    intro w
    rw [hΛapp]
    exact (hτ _ (proj w).2).1
  -- On `M`, `Λ` inverts the X-projection: `(Λ v).X = v` for `v ∈ M`.
  have hΛX : ∀ v ∈ M, (Λ v).X = v := by
    intro v hv
    have hpv : (proj v : Fin n → ZMod 2) = v := by
      have := M.linearProjOfIsCompl_apply_left hcompl ⟨v, hv⟩
      rw [hproj]
      exact congrArg Subtype.val this
    rw [hΛapp, hpv]
    exact (hτ v hv).2
  refine ⟨eOf S x₀ Λ, booleanQuadForm_eOf S x₀ Λ hΛmem, ?_⟩
  intro p hp
  -- `p.X ∈ M` and `Λ p.X` has the same X-part as `p`.
  have hpXM : p.X ∈ M := by
    rw [hM]; exact ⟨p, hp, rfl⟩
  have hΛpX_mem : Λ p.X ∈ S.L := hΛmem p.X
  have hΛpX_X : (Λ p.X).X = p.X := hΛX p.X hpXM
  -- Evaluate `eOf` at `x₀ + p.X`.
  rw [iZ4_eOf S x₀ Λ hΛmem]
  rw [show (x₀ + p.X) - x₀ = p.X from by abel]
  -- The factor of the lift equals the factor of `p` (same X-part).
  exact amplitudeFactor_eq_of_X_eq S ψ _hψfix _hx₀ne hΛpX_mem hp hΛpX_X

/-! ### The bridge theorem, unconditional -/

/-- **Bridge theorem, unconditional.** Every full-rank sector has a **unit** stabilizer state `ψ`
which is the kernel frame's own **level-≤2** object on its support coset: its support is the affine
coset `x₀ + π_X(L)`, and on it `ψ w = c · exp(i · realPhase q w)` for a frame exponent `q` of level
≤ 2. This is **Dehaene–De Moor Thm 5(ii)** (qubit, Z-type/diagonal scope), the stabilizer fragment
realized as objects *of* the kernel frame, with no hypothesis: the DDM quadratic-form core
`CosetAmplitudeQuadForm` is discharged by `cosetAmplitudeQuadForm_holds`, completing the chain
`stabilizerState_isLevel2Kernel ⟸ StabStateAmplitudeForm ⟸ AmplitudePhaseForm ⟸
CosetAmplitudeQuadForm`. -/
theorem stabilizerState_isLevel2Kernel_unconditional (S : SignedStab n)
    (hL : Module.finrank (ZMod 2) S.L = n) :
    ∃ (ψ : QState n) (m : ℕ) (q : DiagPhase n m) (c : ℂ) (x₀ : Fin n → ZMod 2),
      ‖ψ‖ = 1 ∧ (∀ g ∈ S.L, (S.sign g • pauliHermitian g) ψ = ψ) ∧
        DiagPhase.effectiveLevel q ≤ 2 ∧
          (∀ w, ψ w ≠ 0 ↔ ∃ p ∈ S.L, w = x₀ + p.X) ∧
          (∀ w, ψ w ≠ 0 → ψ w = c * Complex.exp (Complex.I * (DiagPhase.realPhase q w : ℂ))) :=
  stabilizerState_isLevel2Kernel_of_amplitudePhaseForm
    (amplitudePhaseForm_holds (cosetAmplitudeQuadForm_holds n)) S hL

end FTQCLib.Frame

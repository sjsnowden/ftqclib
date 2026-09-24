/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierAmplitude
import FTQCLib.Examples.DyadicCharacter
import FTQCLib.Examples.SwapShadow
import FTQCLib.Hierarchy.LastVariable

/-!
# Eliminating the last bound bit of a carrier

A carrier record with a bound register of `h + 1` bits sums over its last bit. Peeling that bit
(`ampCore_peel_last`) writes the amplitude as `(1/√2)·(c/√2^h)·Σ_y ω^{Q(w,y,0)}·(1 + ω^{Δ(w,y)})`,
with `Δ` the difference of the exponent along the last bit (`lastDiff`). The factor `1 + ω^Δ` is
absorbable into a record with one bound bit fewer in exactly two shapes, and each shape has its
constructor and its certificate:

* **collapse** (`SignAffine`): on the support coset, uniformly in the remaining bound word, `Δ` is
  the top bit `2^{m−1}` times the `𝔽₂`-affine value `ε + ⟨σ, w⟩` of the free word. The factor is `2`
  where that value is `0` and vanishes where it is `1`: the support is cut by one linear equation,
  the exponent is the zero branch, the scale gains `√2` (`elimCollapse`, `amp_elimCollapse`).
* **rotate** (`RotateData`): `Δ` takes the two values `a`, `a + 2^{m−1}` with `2a = 2^{m−1}`, the
  choice made by a `{0,1}`-valued polynomial `Λ` of the free and remaining bound variables — affine
  or not. The factor is `(1 + ω^a)·ω^{−a·Λ}`: the support is unchanged, the exponent gains `−a·Λ`,
  the scale gains `(1 + ω^a)/√2` (`elimRotate`, `amp_elimRotate`). At `m = 1` no `a` satisfies
  `2a = 2^{m−1}`, so the rotate shape is empty there by its own hypothesis.

Both certificates are equalities of the amplitude *function*: the eliminated record denotes the same
state as the input (`StateEq`). Their hypotheses are the shape on the coset and a description of the
output record's support; nothing about the Lagrangian beyond its shadow enters. The eliminating
Hadamard — the free rule followed by this elimination, with the swapped Lagrangian and the alignment
that makes its shadow the right support — is built on top of these in `HadamardElimination.lean`.
On the residual class (neither shape) no certificate exists and the record keeps its bit.

## Main definitions

* `SignAffine Q L x₀ σ ε`, `RotateData Q L x₀ a Λ` — the two shapes of the last bit's difference.
* `elimCollapse Q c L'' x₀''`, `elimRotate Q a Λ c L'' x₀''` — the two eliminated records, with the
  output Lagrangian and offset as data.

## Main results

* `ampCore_peel_last` — the last bound bit peeled.
* `amp_elimCollapse`, `amp_elimRotate` — the eliminated record denotes the input's state.
* `amp_map_zShear` — a Z-shear of the Lagrangian is a gauge move on the denotation.

## Implementation notes

The records are stated on explicit fields `⟨m, h + 1, Q, c, L, x₀⟩` with
`Q : DiagPhase (n + h + 1) m`, the convention of the gauge rewrites in `CarrierAmplitude.lean`;
`n + h + 1` and `n + (h + 1)` are the same type by definitional unfolding, so no transport appears
in any statement. The rotate scale is
`c·(1 + charOf a)/√2` rather than an eighth root of unity: it is uniform over the two rotate
constants and the certificate never needs the quarter turn — that appears only in check rows. The
exponent gain is `C (−a) * Λ` for a polynomial `Λ` evaluating to a bit; for an `𝔽₂`-affine bit the
XOR form (`xorForm`) is the polynomial to use, never the ordinary sum, since `−a` is not a multiple
of the top bit.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The amplitude in character form, and the peel -/

/-- The raw amplitude as a character sum over the bound register. -/
theorem ampCore_eq_sum_charOf (m h : ℕ) (Q : DiagPhase (n + h) m) (c : ℂ) (w : Fin n → ZMod 2) :
    ampCore m h Q c w
      = (c / (Real.sqrt 2 : ℂ) ^ h) * ∑ y : Fin h → ZMod 2, charOf m (Q.eval (Fin.append w y)) := by
  unfold ampCore
  rfl

/-- The raw amplitude is linear in the scale. -/
theorem ampCore_mul_left (m h : ℕ) (Q : DiagPhase (n + h) m) (a c : ℂ) (w : Fin n → ZMod 2) :
    ampCore m h Q (a * c) w = a * ampCore m h Q c w := by
  unfold ampCore
  ring

/-- **The peel.** The amplitude over `h + 1` bound bits is `1/√2` times the sum of the two
amplitudes with the last bit frozen. -/
theorem ampCore_peel_last {h m : ℕ} (Q : DiagPhase (n + h + 1) m) (c : ℂ) (w : Fin n → ZMod 2) :
    ampCore m (h + 1) Q c w
      = (1 / (Real.sqrt 2 : ℂ))
          * (ampCore m h (snocFreeze 0 Q) c w + ampCore m h (snocFreeze 1 Q) c w) := by
  unfold ampCore
  have hterm :
      (∑ y' : Fin (h + 1) → ZMod 2,
          Complex.exp (Complex.I *
            (DiagPhase.realPhase Q (@Fin.append n (h + 1) (ZMod 2) w y') : ℂ)))
        = ∑ y' : Fin (h + 1) → ZMod 2,
            Complex.exp (Complex.I *
              (DiagPhase.realPhase (snocFreeze (y' (Fin.last h)) Q)
                (Fin.append w (Fin.init y')) : ℂ)) := by
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    congr 2
    unfold DiagPhase.realPhase
    rw [snocFreeze_eval, ← Fin.append_snoc, Fin.snoc_init_self]
  rw [hterm, sum_snoc_peel]
  simp only [Fin.snoc_last, Fin.init_snoc]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, pow_succ]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  field_simp

/-- The one-branch amplitude is the zero-branch character sum weighted by the character of the
difference along the last bit. -/
theorem ampCore_snocFreeze_one {h m : ℕ} (Q : DiagPhase (n + h + 1) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m h (snocFreeze 1 Q) c w
      = (c / (Real.sqrt 2 : ℂ) ^ h)
          * ∑ y : Fin h → ZMod 2,
              charOf m (Q.eval (Fin.snoc (Fin.append w y) 0))
                * charOf m ((lastDiff Q).eval (Fin.append w y)) := by
  rw [ampCore_eq_sum_charOf]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [snocFreeze_eval, lastDiff_eval, mul_comm, charOf_sub_mul]

/-- The zero-branch amplitude as a character sum. -/
theorem ampCore_snocFreeze_zero {h m : ℕ} (Q : DiagPhase (n + h + 1) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m h (snocFreeze 0 Q) c w
      = (c / (Real.sqrt 2 : ℂ) ^ h)
          * ∑ y : Fin h → ZMod 2, charOf m (Q.eval (Fin.snoc (Fin.append w y) 0)) := by
  rw [ampCore_eq_sum_charOf]
  congr 1
  exact Finset.sum_congr rfl (fun y _ => by rw [snocFreeze_eval])

/-! ## The two shapes of the difference -/

/-- **The collapse shape.** On the support coset, uniformly in the remaining bound word, the
difference along the last bit is the top bit times the affine value `ε + ⟨σ, w⟩` of the free
word. -/
def SignAffine {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ σ : Fin n → ZMod 2) (ε : ZMod 2) : Prop :=
  ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
    (lastDiff Q).eval (Fin.append w y)
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * (((ε + dotF2 σ w).val : ℕ) : ZMod (2 ^ m))

/-- **The rotate shape.** `2a = 2^{m−1}`, and on the support coset, uniformly in the remaining bound
word, the difference along the last bit is `a + 2^{m−1}·b` for the bit `b` that `Λ` evaluates to. -/
def RotateData {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2) (a : ZMod (2 ^ m)) (Λ : DiagPhase (n + h) m) : Prop :=
  2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1) ∧
    ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2, ∃ b : ZMod 2,
      Λ.eval (Fin.append w y) = ((b.val : ℕ) : ZMod (2 ^ m)) ∧
      (lastDiff Q).eval (Fin.append w y)
        = a + (2 : ZMod (2 ^ m)) ^ (m - 1) * ((b.val : ℕ) : ZMod (2 ^ m))

/-! ## The two eliminated records -/

/-- **Collapse.** The last bound bit dropped, the exponent frozen at its zero branch, the scale
times `√2`, the Lagrangian and offset supplied as data. -/
noncomputable def elimCollapse {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (c : ℂ)
    (L'' : Submodule (ZMod 2) (Pauli n)) (x₀'' : Fin n → ZMod 2) : KernelSumState n :=
  ⟨m, h, snocFreeze 0 Q, (Real.sqrt 2 : ℂ) * c, L'', x₀''⟩

/-- **Rotate.** The last bound bit dropped, the exponent frozen at its zero branch plus `−a·Λ`, the
scale times `(1 + charOf a)/√2`, the Lagrangian and offset supplied as data. -/
noncomputable def elimRotate {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (a : ZMod (2 ^ m))
    (Λ : DiagPhase (n + h) m) (c : ℂ) (L'' : Submodule (ZMod 2) (Pauli n))
    (x₀'' : Fin n → ZMod 2) : KernelSumState n :=
  ⟨m, h, snocFreeze 0 Q + MvPolynomial.C (-a) * Λ, c * (1 + charOf m a) / (Real.sqrt 2 : ℂ),
    L'', x₀''⟩

@[simp] theorem elimCollapse_h {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (c : ℂ)
    (L'' : Submodule (ZMod 2) (Pauli n)) (x₀'' : Fin n → ZMod 2) :
    (elimCollapse Q c L'' x₀'').h = h := rfl

@[simp] theorem elimRotate_h {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (a : ZMod (2 ^ m))
    (Λ : DiagPhase (n + h) m) (c : ℂ) (L'' : Submodule (ZMod 2) (Pauli n))
    (x₀'' : Fin n → ZMod 2) : (elimRotate Q a Λ c L'' x₀'').h = h := rfl

@[simp] theorem elimCollapse_L {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (c : ℂ)
    (L'' : Submodule (ZMod 2) (Pauli n)) (x₀'' : Fin n → ZMod 2) :
    (elimCollapse Q c L'' x₀'').L = L'' := rfl

@[simp] theorem elimRotate_L {m h : ℕ} (Q : DiagPhase (n + h + 1) m) (a : ZMod (2 ^ m))
    (Λ : DiagPhase (n + h) m) (c : ℂ) (L'' : Submodule (ZMod 2) (Pauli n))
    (x₀'' : Fin n → ZMod 2) : (elimRotate Q a Λ c L'' x₀'').L = L'' := rfl

/-! ## The certificates -/

/-- `(1/√2)·2 = √2` in `ℂ`. -/
theorem one_div_sqrt_two_mul_two : (1 / (Real.sqrt 2 : ℂ)) * 2 = Real.sqrt 2 := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  field_simp
  exact h2.symm

/-- Under the collapse shape, the one-branch amplitude is the sign of the affine value times the
zero-branch amplitude. -/
theorem ampCore_snocFreeze_one_of_signAffine {m h : ℕ} (hm : 1 ≤ m)
    {Q : DiagPhase (n + h + 1) m} {L : Submodule (ZMod 2) (Pauli n)} {x₀ σ : Fin n → ZMod 2}
    {ε : ZMod 2} (hsign : SignAffine Q L x₀ σ ε) (c : ℂ) {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ L, w = x₀ + p.X) :
    ampCore m h (snocFreeze 1 Q) c w
      = (-1 : ℂ) ^ (ε + dotF2 σ w).val * ampCore m h (snocFreeze 0 Q) c w := by
  rw [ampCore_snocFreeze_one, ampCore_snocFreeze_zero, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [hsign w hw y, charOf_two_pow_mul hm]
  ring

/-- **The collapse certificate.** With the collapse shape on the coset and the output support the
input coset cut by `ε + ⟨σ, w⟩ = 0`, the eliminated record denotes the input's state. -/
theorem amp_elimCollapse {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h + 1) m} (c : ℂ)
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ σ : Fin n → ZMod 2} {ε : ZMod 2}
    (hsign : SignAffine Q L x₀ σ ε) {L'' : Submodule (ZMod 2) (Pauli n)} {x₀'' : Fin n → ZMod 2}
    (hsupp : ∀ w : Fin n → ZMod 2,
      (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X) ∧ ε + dotF2 σ w = 0) :
    amp (elimCollapse Q c L'' x₀'') = amp (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · have hpeel : amp (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n) w
        = (1 / (Real.sqrt 2 : ℂ))
            * ((1 + (-1 : ℂ) ^ (ε + dotF2 σ w).val) * ampCore m h (snocFreeze 0 Q) c w) := by
      rw [amp_pos hw]
      change ampCore m (h + 1) Q c w = _
      rw [ampCore_peel_last, ampCore_snocFreeze_one_of_signAffine hm hsign c hw]
      ring
    rcases zmod_two_eq_zero_or_one (ε + dotF2 σ w) with hb | hb
    · have hmem : ∃ p ∈ L'', w = x₀'' + p.X := (hsupp w).mpr ⟨hw, hb⟩
      rw [hpeel, hb, amp_pos hmem]
      change ampCore m h (snocFreeze 0 Q) ((Real.sqrt 2 : ℂ) * c) w = _
      rw [ampCore_mul_left, ZMod.val_zero, pow_zero]
      linear_combination (-(ampCore m h (snocFreeze 0 Q) c w)) * one_div_sqrt_two_mul_two
    · have hmem : ¬ ∃ p ∈ L'', w = x₀'' + p.X := by
        intro hmem
        have := ((hsupp w).mp hmem).2
        rw [hb] at this
        exact absurd this (by decide)
      rw [hpeel, hb, amp_neg hmem, show ((1 : ZMod 2)).val = 1 from by decide, pow_one]
      ring
  · have hmem : ¬ ∃ p ∈ L'', w = x₀'' + p.X := fun hmem => hw ((hsupp w).mp hmem).1
    rw [amp_neg hmem, amp_neg hw]

/-- Pulling a scalar into a scaled sum. -/
theorem mul_mul_sum_eq {ι : Type*} (s : Finset ι) (a b : ℂ) (f : ι → ℂ) :
    a * (b * ∑ i ∈ s, f i) = b * ∑ i ∈ s, a * f i := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Under the rotate shape, the two branch amplitudes recombine into the scale `1 + charOf a` times
the amplitude of the shifted exponent. -/
theorem ampCore_branches_of_rotateData {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h + 1) m}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2} {a : ZMod (2 ^ m)}
    {Λ : DiagPhase (n + h) m} (hrot : RotateData Q L x₀ a Λ) (c : ℂ) {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ L, w = x₀ + p.X) :
    ampCore m h (snocFreeze 0 Q) c w + ampCore m h (snocFreeze 1 Q) c w
      = (1 + charOf m a) * ampCore m h (snocFreeze 0 Q + MvPolynomial.C (-a) * Λ) c w := by
  have hsum : (∑ y : Fin h → ZMod 2, charOf m (Q.eval (Fin.snoc (Fin.append w y) 0)))
      + ∑ y : Fin h → ZMod 2, charOf m (Q.eval (Fin.snoc (Fin.append w y) 0))
          * charOf m ((lastDiff Q).eval (Fin.append w y))
      = ∑ y : Fin h → ZMod 2, (charOf m (Q.eval (Fin.snoc (Fin.append w y) 0))
          + charOf m (Q.eval (Fin.snoc (Fin.append w y) 0))
              * charOf m ((lastDiff Q).eval (Fin.append w y))) := by
    rw [Finset.sum_add_distrib]
  rw [ampCore_snocFreeze_zero, ampCore_snocFreeze_one, ampCore_eq_sum_charOf, ← mul_add, hsum,
    mul_mul_sum_eq]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  obtain ⟨b, hΛ, hΔ⟩ := hrot.2 w hw y
  rw [hΔ, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, snocFreeze_eval, hΛ,
    charOf_add m (Q.eval (Fin.snoc (Fin.append w y) 0)) (-a * ((b.val : ℕ) : ZMod (2 ^ m)))]
  have hr := one_add_charOf_rotate hm hrot.1 b
  linear_combination (charOf m (Q.eval (Fin.snoc (Fin.append w y) 0))) * hr

/-- **The rotate certificate.** With the rotate shape on the coset and the output support the input
coset, the eliminated record denotes the input's state. -/
theorem amp_elimRotate {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h + 1) m} (c : ℂ)
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2} {a : ZMod (2 ^ m)}
    {Λ : DiagPhase (n + h) m} (hrot : RotateData Q L x₀ a Λ) {L'' : Submodule (ZMod 2) (Pauli n)}
    {x₀'' : Fin n → ZMod 2}
    (hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X)) :
    amp (elimRotate Q a Λ c L'' x₀'') = amp (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := elimRotate Q a Λ c L'' x₀'') ((hsupp w).mpr hw)]
    change ampCore m h (snocFreeze 0 Q + MvPolynomial.C (-a) * Λ)
        (c * (1 + charOf m a) / (Real.sqrt 2 : ℂ)) w = ampCore m (h + 1) Q c w
    rw [ampCore_peel_last, ampCore_branches_of_rotateData hm hrot c hw,
      show c * (1 + charOf m a) / (Real.sqrt 2 : ℂ)
        = ((1 / (Real.sqrt 2 : ℂ)) * (1 + charOf m a)) * c from by ring,
      ampCore_mul_left]
    ring
  · rw [amp_neg (S := (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := elimRotate Q a Λ c L'' x₀'') (fun hmem => hw ((hsupp w).mp hmem))]

/-! ## The shear is a gauge move -/

/-- A Z-shear of the Lagrangian by any linear map does not change the denotation (the shadow is
fixed). -/
theorem amp_map_zShearBy {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2) :
    amp (⟨m, h, Q, c, Submodule.map (zShearBy M) L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) :=
  amp_congr_xProj Q c _ _ x₀ (map_xProj_map_zShearBy M L)

/-- A Z-shear of the Lagrangian at a bit does not change the denotation. -/
theorem amp_map_zShear {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ) (k : Fin n)
    (d : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    amp (⟨m, h, Q, c, Submodule.map (zShear k d) L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) :=
  amp_map_zShearBy Q c (shearLin k d) L x₀

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.Matrix.Normed
import FTQCLib.Hierarchy.RzApprox

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # Frame-native SU(2) coverage in the max-row-sum (ℓ∞ operator) measure

Covering a general single-qubit unitary frame-natively. The measure is the
**max-row-sum induced operator norm** `‖A‖_∞ = max_i Σ_j |A_ij|` on the `2×2` ℂ amplitude matrix — a
frame-pure ℂ-formula (Mathlib `Matrix.linftyOpNorm`, imports no `FTQCLib.Hilbert`), submultiplicative
(`linfty_opNorm_mul`), with `‖1‖ = 1`. It is genuinely non-ℓ² (no inner product); the price is that Hadamard
has `‖H‖_∞ = √2` rather than 1, so the composite carries a `(√2)^{#H}` constant. Relation to the ℓ²
operator norm, stated exactly: the Schur bound `‖A‖_op ≤ √(‖A‖₁‖A‖_∞)` needs the
max-**column**-sum `‖A‖₁` as well, which this file does **not** bound — so the ℓ∞ result here does
*not* by itself imply an operator-norm (Ross–Selinger-style) bound. (For the `2×2` matrices in
play an ℓ1 bound would be symmetric work; this file does not treat it.)

This file: the measure infrastructure — the general product-difference bound (no contraction hypothesis, so it
absorbs `‖H‖ = √2`) and the diagonal rotation matrix with its norm. The Hadamard, per-factor frame
approximation, and the Euler-word composite follow. -/

namespace FTQCLib.Frame.SU2

open Matrix Complex FTQCLib.Hierarchy.DiagPhase
open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormSMulClass

/-! ## The general two-factor product-difference bound (no contraction hypothesis) -/

/-- `‖a·c − b·d‖ ≤ ‖a‖·‖c−d‖ + ‖a−b‖·‖d‖` in any normed ring, from `a·c − b·d = a·(c−d) + (a−b)·d`. No
`‖·‖ ≤ 1` assumption — the factors may have norm `> 1` (here Hadamard has norm `√2`). -/
theorem norm_mul_sub_mul_le {R : Type*} [NormedRing R] (a b c d : R) :
    ‖a * c - b * d‖ ≤ ‖a‖ * ‖c - d‖ + ‖a - b‖ * ‖d‖ := by
  have hkey : a * c - b * d = a * (c - d) + (a - b) * d := by noncomm_ring
  calc ‖a * c - b * d‖
      = ‖a * (c - d) + (a - b) * d‖ := by rw [hkey]
    _ ≤ ‖a * (c - d)‖ + ‖(a - b) * d‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖c - d‖ + ‖a - b‖ * ‖d‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)

/-! ## The diagonal rotation matrix `R_z(θ) = diag(1, e^{iθ})` -/

/-- The anchored `R_z(θ)` as a `2×2` ℂ matrix `diag(1, e^{iθ})`. -/
noncomputable def Rz (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![1, Complex.exp (Complex.I * θ)]

/-- The entrywise norm of the rotation's diagonal vector is `1` (both entries are unit-modulus). -/
private theorem norm_rzVec (θ : ℝ) : ‖(![1, Complex.exp (Complex.I * θ)] : Fin 2 → ℂ)‖ = 1 := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro i
    fin_cases i
    · simp
    · simp [Complex.norm_exp]
  · calc (1:ℝ) = ‖(![1, Complex.exp (Complex.I * θ)] : Fin 2 → ℂ) 0‖ := by simp
      _ ≤ ‖(![1, Complex.exp (Complex.I * θ)] : Fin 2 → ℂ)‖ := norm_le_pi_norm _ 0

/-- **`‖R_z(θ)‖_∞ = 1`.** The rotation is a contraction in the measure. -/
theorem norm_Rz (θ : ℝ) : ‖Rz θ‖ = 1 := by
  rw [Rz, Matrix.linfty_opNorm_diagonal, norm_rzVec]

/-- The difference of two rotations is diagonal, so its measure is the chord between the phasors:
`‖R_z(θ) − R_z(θ')‖_∞ = |e^{iθ} − e^{iθ'}|`. -/
theorem norm_Rz_sub (θ θ' : ℝ) :
    ‖Rz θ - Rz θ'‖ = ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * θ')‖ := by
  have hdiag : Rz θ - Rz θ' =
      Matrix.diagonal ![0, Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * θ')] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz, Matrix.sub_apply, Matrix.diagonal_apply]
  rw [hdiag, Matrix.linfty_opNorm_diagonal]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i; fin_cases i
    · simp
    · simp
  · calc ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * θ')‖
        = ‖(![0, Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * θ')] : Fin 2 → ℂ) 1‖ := by simp
      _ ≤ _ := norm_le_pi_norm _ 1

/-! ## The Hadamard matrix `H = (1/√2)·[[1,1],[1,-1]]` -/

/-- The Hadamard as a `2×2` ℂ matrix. -/
noncomputable def Had : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.ofReal (Real.sqrt 2))⁻¹ • !![1, 1; 1, -1]

/-- The unnormalised Walsh matrix has measure `≤ 2` (each row sums to `2`). -/
private theorem norm_walsh_le : ‖(!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : (Finset.univ.sup fun i : Fin 2 =>
      ∑ j : Fin 2, ‖(!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) i j‖₊) ≤ (2 : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num
  exact_mod_cast hsup

/-- **`‖H‖_∞ ≤ √2`.** Hadamard is not a contraction — the price of the non-ℓ² measure. -/
theorem norm_Had_le : ‖Had‖ ≤ Real.sqrt 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Had, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc (Real.sqrt 2)⁻¹ * ‖(!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)‖
      ≤ (Real.sqrt 2)⁻¹ * 2 := mul_le_mul_of_nonneg_left norm_walsh_le (by positivity)
    _ = Real.sqrt 2 := by
        rw [inv_mul_eq_div, div_eq_iff (by positivity : (0:ℝ) < Real.sqrt 2).ne', h2]

/-! ## The per-factor frame approximation: chord ≤ arc, fed by `rz_dyadic_approx` -/

/-- The elementary chord bound `‖e^{ia} − e^{ib}‖ ≤ |a − b − 2πk|`, restated frame-pure (the `2πk`
periodicity absorbed by `exp`). -/
theorem chord_le_arc {a b δ : ℝ} (k : ℤ) (hk : |a - b - 2 * Real.pi * k| ≤ δ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ δ := by
  have hfac : Complex.exp (Complex.I * (b : ℂ))
        * (Complex.exp (Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)) - 1)
      = Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    rw [show Complex.I * (b : ℂ) + Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)
          = Complex.I * (a : ℂ) + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hnorm1 : ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [← hfac, norm_mul, hnorm1, one_mul]
  calc ‖Complex.exp (Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)) - 1‖
      ≤ ‖(a - b - 2 * Real.pi * k : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a - b - 2 * Real.pi * k| := Real.norm_eq_abs _
    _ ≤ δ := hk

/-! ## The frame's per-factor approximation, and the Euler-word composite -/

/-- **The frame's dyadic approximant for `R_z(θ)`.** A tower coefficient `c` whose rotation matrix is
within `π/2^m` of the target in the measure — `rz_dyadic_approx` (the frame's diagonal theorem) read on the
active branch, plus `chord ≤ arc`. This is the frame-native content: `c` and its accuracy come from the
frame's own proven approximation, unchanged. -/
theorem Rz_frame_approx (θ : ℝ) (m : ℕ) :
    ∃ c : ZMod (2 ^ m),
      ‖Rz (2 * Real.pi * (c.val : ℝ) / 2 ^ m) - Rz θ‖ ≤ Real.pi / 2 ^ m := by
  obtain ⟨c, hc⟩ := rz_dyadic_approx θ (0 : Fin 1) m
  refine ⟨c, ?_⟩
  obtain ⟨k, hk⟩ := hc (fun _ => 1)
  rw [realPhase_linear, show (((fun _ => 1 : Fin 1 → ZMod 2) 0).val : ℝ) = 1 from by
    rw [show ((fun _ => 1 : Fin 1 → ZMod 2) 0) = 1 from rfl,
      show ((1 : ZMod 2)).val = 1 from by decide, Nat.cast_one]] at hk
  rw [norm_Rz_sub]
  refine chord_le_arc k ?_
  simpa using hk

/-- `‖H · A − H · B‖ ≤ √2 · ‖A − B‖` — H shared exactly, so only its `√2` norm enters. -/
private theorem norm_Had_mul_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖Had * A - Had * B‖ ≤ Real.sqrt 2 * ‖A - B‖ := by
  calc ‖Had * A - Had * B‖
      ≤ ‖Had‖ * ‖A - B‖ + ‖Had - Had‖ * ‖B‖ := norm_mul_sub_mul_le _ _ _ _
    _ = ‖Had‖ * ‖A - B‖ := by rw [sub_self, norm_zero, zero_mul, add_zero]
    _ ≤ Real.sqrt 2 * ‖A - B‖ := mul_le_mul_of_nonneg_right norm_Had_le (norm_nonneg _)

/-- `‖H · A‖ ≤ √2 · ‖A‖`. -/
private theorem norm_Had_mul (A : Matrix (Fin 2) (Fin 2) ℂ) : ‖Had * A‖ ≤ Real.sqrt 2 * ‖A‖ :=
  le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right norm_Had_le (norm_nonneg _))

/-- **Frame-native SU(2) coverage in the max-row-sum measure.** For Euler angles `α, β, γ` and precision
`m`, the frame's Euler word `R_z·H·R_z·H·R_z` — each rotation replaced by its dyadic tower approximant
(`Rz_frame_approx`), the two H's exact — is within `6·π/2^m` of the target in `‖·‖_∞`, i.e. `O(π/2^m)`,
`Θ(log 1/ε)`. Frame-pure (imports no `FTQCLib.Hilbert`). This does **not** imply an operator-norm bound: the
Schur inequality `‖·‖_op ≤ √(‖·‖₁‖·‖_∞)` also needs the max-**column**-sum `‖·‖₁`, which is not bounded
here — see the file header. -/
theorem su2_coverage (α β γ : ℝ) (m : ℕ) :
    ∃ a b c : ZMod (2 ^ m),
      ‖Rz α * (Had * (Rz β * (Had * Rz γ)))
        - Rz (2 * Real.pi * (a.val : ℝ) / 2 ^ m)
            * (Had * (Rz (2 * Real.pi * (b.val : ℝ) / 2 ^ m)
                * (Had * Rz (2 * Real.pi * (c.val : ℝ) / 2 ^ m))))‖
        ≤ 6 * Real.pi / 2 ^ m := by
  obtain ⟨a, ha⟩ := Rz_frame_approx α m
  obtain ⟨b, hb⟩ := Rz_frame_approx β m
  obtain ⟨c, hc⟩ := Rz_frame_approx γ m
  refine ⟨a, b, c, ?_⟩
  set A' := Rz (2 * Real.pi * (a.val : ℝ) / 2 ^ m)
  set B' := Rz (2 * Real.pi * (b.val : ℝ) / 2 ^ m)
  set G' := Rz (2 * Real.pi * (c.val : ℝ) / 2 ^ m)
  have hs2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- per-factor errors (target − approx), each ≤ π/2^m
  have eA : ‖Rz α - A'‖ ≤ Real.pi / 2 ^ m := by rw [norm_sub_rev]; exact ha
  have eB : ‖Rz β - B'‖ ≤ Real.pi / 2 ^ m := by rw [norm_sub_rev]; exact hb
  have eG : ‖Rz γ - G'‖ ≤ Real.pi / 2 ^ m := by rw [norm_sub_rev]; exact hc
  -- norm bounds on the approximant factors
  have nB' : ‖B'‖ = 1 := norm_Rz _
  have nG' : ‖G'‖ = 1 := norm_Rz _
  -- inner: ‖B*(H*G) − B'*(H*G')‖ ≤ 2√2·(π/2^m)
  have hHG : ‖Had * Rz γ - Had * G'‖ ≤ Real.sqrt 2 * (Real.pi / 2 ^ m) :=
    le_trans (norm_Had_mul_sub _ _) (mul_le_mul_of_nonneg_left eG hs2)
  have hHG' : ‖Had * G'‖ ≤ Real.sqrt 2 := by
    have := norm_Had_mul G'; rw [nG', mul_one] at this; exact this
  have hInner : ‖Rz β * (Had * Rz γ) - B' * (Had * G')‖
      ≤ 2 * Real.sqrt 2 * (Real.pi / 2 ^ m) := by
    calc ‖Rz β * (Had * Rz γ) - B' * (Had * G')‖
        ≤ ‖Rz β‖ * ‖Had * Rz γ - Had * G'‖ + ‖Rz β - B'‖ * ‖Had * G'‖ :=
          norm_mul_sub_mul_le _ _ _ _
      _ ≤ 1 * (Real.sqrt 2 * (Real.pi / 2 ^ m)) + (Real.pi / 2 ^ m) * Real.sqrt 2 := by
          rw [norm_Rz]
          exact add_le_add (mul_le_mul_of_nonneg_left hHG (by norm_num))
            (mul_le_mul eB hHG' (norm_nonneg _) (by positivity))
      _ = 2 * Real.sqrt 2 * (Real.pi / 2 ^ m) := by ring
  -- middle: ‖H*(B*(H*G)) − H*(B'*(H*G'))‖ ≤ √2·2√2·(π/2^m) = 4·(π/2^m)
  have hMid : ‖Had * (Rz β * (Had * Rz γ)) - Had * (B' * (Had * G'))‖
      ≤ 4 * (Real.pi / 2 ^ m) := by
    calc ‖Had * (Rz β * (Had * Rz γ)) - Had * (B' * (Had * G'))‖
        ≤ Real.sqrt 2 * ‖Rz β * (Had * Rz γ) - B' * (Had * G')‖ := norm_Had_mul_sub _ _
      _ ≤ Real.sqrt 2 * (2 * Real.sqrt 2 * (Real.pi / 2 ^ m)) :=
          mul_le_mul_of_nonneg_left hInner hs2
      _ = 4 * (Real.pi / 2 ^ m) := by rw [show Real.sqrt 2 * (2 * Real.sqrt 2 * (Real.pi / 2 ^ m))
            = 2 * (Real.sqrt 2 * Real.sqrt 2) * (Real.pi / 2 ^ m) by ring, h22]; ring
  -- ‖H*(B'*(H*G'))‖ ≤ 2
  have hY : ‖Had * (B' * (Had * G'))‖ ≤ 2 := by
    calc ‖Had * (B' * (Had * G'))‖
        ≤ Real.sqrt 2 * ‖B' * (Had * G')‖ := norm_Had_mul _
      _ ≤ Real.sqrt 2 * (‖B'‖ * ‖Had * G'‖) := by
          exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) hs2
      _ ≤ Real.sqrt 2 * (1 * Real.sqrt 2) := by
          rw [nB']; exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hHG' (by norm_num)) hs2
      _ = 2 := by rw [one_mul, h22]
  -- outer
  calc ‖Rz α * (Had * (Rz β * (Had * Rz γ))) - A' * (Had * (B' * (Had * G')))‖
      ≤ ‖Rz α‖ * ‖Had * (Rz β * (Had * Rz γ)) - Had * (B' * (Had * G'))‖
          + ‖Rz α - A'‖ * ‖Had * (B' * (Had * G'))‖ := norm_mul_sub_mul_le _ _ _ _
    _ ≤ 1 * (4 * (Real.pi / 2 ^ m)) + (Real.pi / 2 ^ m) * 2 := by
        rw [norm_Rz]
        exact add_le_add (mul_le_mul_of_nonneg_left hMid (by norm_num))
          (mul_le_mul eA hY (norm_nonneg _) (by positivity))
    _ = 6 * Real.pi / 2 ^ m := by ring

end FTQCLib.Frame.SU2

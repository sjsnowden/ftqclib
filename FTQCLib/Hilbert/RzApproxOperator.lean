/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.RzApprox
import FTQCLib.Hilbert.Inner
import FTQCLib.Hilbert.Diagonal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # The operator-norm certificate for the Rz approximation theorem

The frame-pure result `FTQCLib/Hierarchy/RzApprox.lean` prices dyadic approximation of `R_z(θ)`
in the ARC distance on the phase data. This file is the separable Hilbert-side **adequacy
certificate**: it shows the same result in the QC literature's measure — the operator norm — so
the theorem is an instance of Ross–Selinger (1403.2975, Def 9.1: `∃` unit `λ`,
`‖R_z(θ) − λ·U‖ ≤ ε`) and Dawson–Nielsen (the operator norm `sup_{‖ψ‖=1} ‖(U−S)ψ‖`).

**Design.** The operator norm needs only the `≤` direction here — `ContinuousLinearMap.opNorm_le_bound` — and because `rz_dyadic_approx` gives a
UNIFORM per-input bound, the ℓ² estimate is termwise, needing no spectral "op-norm = sup of diagonal
entries" theorem. So we get a genuine operator norm (matching the literature) at low cost. The bridge is the
per-entry chord `|e^{iα} − e^{iβ}| = ‖e^{i(α−β)} − 1‖ ≤ |α−β|` (`Real.norm_exp_I_mul_ofReal_sub_one_le`),
with the `2πk` arc-periodicity carried by `Complex.exp_int_mul_two_pi_mul_I`. Global phase is a
statement-level `∃λ`, never a quotiented measure. Frame-purity preserved: `RzApprox` imports no
`FTQCLib.Hilbert`; the dependency is one-way (this file → `RzApprox`), reusing its `∃ c` witness verbatim.

* `qDiagCLM` — a phase pattern's diagonal gate, transported to the ℓ² space `QState` as a bundled
  continuous linear map.
* `qDiag_sub_opNorm_le` — the reusable engine: a uniform per-entry chord bound gives an operator-norm bound.
* `rz_approx_opNorm` / `rz_approx_opNorm_upToPhase` — the certificate: the frame's approximant is within
  `π/2^m` of `R_z(θ)` in operator norm (up to a unit global phase, Def 9.1 form).
* `rz_dyadic_lower_opNorm` — operator-side sharpness: the grid-midpoint adversary of `rz_dyadic_lower`
  transported to the operator norm, with the exact chord constant `2·sin(π/2^{m+1})` (the arc constant
  `π/2^m` shrunk by exactly the arc-versus-chord gap). One application of `le_opNorm` at the basis vector
  on the `v i = 1` branch — no spectral input, mirroring the `≤` engine. -/

namespace FTQCLib.Hilbert

open FTQCLib.Hierarchy.DiagPhase MvPolynomial

variable {n : ℕ}

/-! ## The diagonal gate on the ℓ² space, bundled -/

/-- A phase pattern's diagonal gate transported to `QState n` (the ℓ² space), as a linear map. -/
noncomputable def qDiagonalGate (f : (Fin n → ZMod 2) → ℝ) : QState n →ₗ[ℂ] QState n :=
  toQState.toLinearMap ∘ₗ diagonalGate f ∘ₗ toQState.symm.toLinearMap

@[simp] theorem qDiagonalGate_apply (f : (Fin n → ZMod 2) → ℝ) (ψ : QState n) (v : Fin n → ZMod 2) :
    qDiagonalGate f ψ v = Complex.exp (Complex.I * f v) * ψ v := by
  simp only [qDiagonalGate, LinearMap.comp_apply, LinearEquiv.coe_coe, toQState_apply,
    diagonalGate_apply, toQState_symm_apply]

/-- The bundled continuous linear map (`QState n` is finite-dimensional). -/
noncomputable def qDiagCLM (f : (Fin n → ZMod 2) → ℝ) : QState n →L[ℂ] QState n :=
  LinearMap.toContinuousLinearMap (qDiagonalGate f)

@[simp] theorem qDiagCLM_apply (f : (Fin n → ZMod 2) → ℝ) (ψ : QState n) (v : Fin n → ZMod 2) :
    qDiagCLM f ψ v = Complex.exp (Complex.I * f v) * ψ v := by
  simp only [qDiagCLM, LinearMap.coe_toContinuousLinearMap', qDiagonalGate_apply]

/-! ## The reusable engine: a uniform per-entry chord bound bounds the operator norm -/

/-- **The engine.** If the two phase patterns' diagonal entries are within `ε` at every basis label, the
transported gates are within `ε` in operator norm. Diagonal structure reduces the ℓ² estimate to a termwise
sum; only the `≤` direction of the operator norm is used (no spectral theorem). -/
theorem qDiag_sub_opNorm_le {f g : (Fin n → ZMod 2) → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ v, ‖Complex.exp (Complex.I * f v) - Complex.exp (Complex.I * g v)‖ ≤ ε) :
    ‖qDiagCLM f - qDiagCLM g‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro ψ
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  have hpt : ∀ v, ‖(qDiagCLM f - qDiagCLM g) ψ v‖ ^ 2 ≤ ε ^ 2 * ‖ψ v‖ ^ 2 := by
    intro v
    rw [ContinuousLinearMap.sub_apply, PiLp.sub_apply, qDiagCLM_apply, qDiagCLM_apply,
      ← sub_mul, norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (h v) 2
  calc Real.sqrt (∑ v, ‖(qDiagCLM f - qDiagCLM g) ψ v‖ ^ 2)
      ≤ Real.sqrt (∑ v, ε ^ 2 * ‖ψ v‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum (fun v _ => hpt v))
    _ = Real.sqrt (ε ^ 2 * ∑ v, ‖ψ v‖ ^ 2) := by rw [Finset.mul_sum]
    _ = ε * Real.sqrt (∑ v, ‖ψ v‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

/-! ## The chord bound from the arc bound (carrying the `2πk` periodicity) -/

/-- The chord between two unit phasors is bounded by the arc distance: if `|a − b − 2πk| ≤ δ` then
`‖e^{ia} − e^{ib}‖ ≤ δ`. The `2πk` slack is absorbed by periodicity of `exp`. -/
theorem chord_le_of_arc {a b δ : ℝ} (k : ℤ) (hk : |a - b - 2 * Real.pi * k| ≤ δ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ δ := by
  have hnorm1 : ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hfac : Complex.exp (Complex.I * (b : ℂ))
        * (Complex.exp (Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)) - 1)
      = Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    rw [show Complex.I * (b : ℂ) + Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)
          = Complex.I * (a : ℂ) + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [← hfac, norm_mul, hnorm1, one_mul]
  calc ‖Complex.exp (Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)) - 1‖
      ≤ ‖(a - b - 2 * Real.pi * k : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a - b - 2 * Real.pi * k| := Real.norm_eq_abs _
    _ ≤ δ := hk

/-! ## The certificate -/

open Real in
/-- **The operator-norm certificate (phase-gate form).** For every angle `θ`, precision `m`, and qubit `i`,
there is a frame gate `C c * X i` whose transported operator is within `π/2^m` in operator norm of the
anchored `R_z(θ)` phase gate `diag(1, e^{iθ})`. The frame's arc-distance achievability, transported to the
QC literature's measure. -/
theorem rz_approx_opNorm (θ : ℝ) (i : Fin n) (m : ℕ) :
    ∃ c : ZMod (2 ^ m),
      ‖qDiagCLM (fun v => ((v i).val : ℝ) * θ) - qDiagCLM (realPhase (C c * X i))‖ ≤ π / 2 ^ m := by
  obtain ⟨c, hc⟩ := rz_dyadic_approx θ i m
  refine ⟨c, ?_⟩
  apply qDiag_sub_opNorm_le (by positivity)
  intro v
  obtain ⟨k, hk⟩ := hc v
  apply chord_le_of_arc (-k)
  have hrw : ((v i).val : ℝ) * θ - realPhase (C c * X i) v - 2 * π * ((-k : ℤ) : ℝ)
      = -(realPhase (C c * X i) v - ((v i).val : ℝ) * θ - 2 * π * (k : ℝ)) := by
    push_cast; ring
  rw [hrw, abs_neg]
  exact hk

/-- A constant phase shift factors out as a global scalar: `qDiagCLM (f + c₀) = e^{ic₀}·qDiagCLM f`. This is
why the anchored gate `diag(1, e^{iθ})` and the literal `R_z(θ) = diag(e^{−iθ/2}, e^{iθ/2})` differ only by
the unit global phase `e^{−iθ/2}`. -/
theorem qDiagCLM_const_shift (f : (Fin n → ZMod 2) → ℝ) (c₀ : ℝ) :
    qDiagCLM (fun v => f v + c₀) = Complex.exp (Complex.I * (c₀ : ℂ)) • qDiagCLM f := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [ContinuousLinearMap.smul_apply]
  ext v
  rw [qDiagCLM_apply, PiLp.smul_apply, qDiagCLM_apply, smul_eq_mul, Complex.ofReal_add,
    mul_add, Complex.exp_add]
  ring

open Real in
/-- **The operator-norm certificate, Ross–Selinger Def 9.1 form.** For every `θ`, precision `m`, qubit `i`,
there is a frame gate and a UNIT global phase `λ` with `‖R_z(θ) − λ·U‖ ≤ π/2^m` in operator norm, where
`R_z(θ) = diag(e^{−iθ/2}, e^{iθ/2})` is the literal rotation (phase pattern `(v i).val·θ − θ/2`). This is a
verbatim instance of the known approximation theorem; the frame's dyadic approximant realises it, priced by
the level meter (`rz_approx_level_le`). -/
theorem rz_approx_opNorm_upToPhase (θ : ℝ) (i : Fin n) (m : ℕ) :
    ∃ (c : ZMod (2 ^ m)) (lam : ℂ), ‖lam‖ = 1 ∧
      ‖qDiagCLM (fun v => ((v i).val : ℝ) * θ - θ / 2)
        - lam • qDiagCLM (realPhase (C c * X i))‖ ≤ π / 2 ^ m := by
  obtain ⟨c, hc⟩ := rz_approx_opNorm θ i m
  refine ⟨c, Complex.exp (Complex.I * ((-(θ / 2)) : ℂ)), by rw [Complex.norm_exp]; simp, ?_⟩
  have hshift : qDiagCLM (fun v => ((v i).val : ℝ) * θ - θ / 2)
      = Complex.exp (Complex.I * ((-(θ / 2)) : ℂ)) • qDiagCLM (fun v => ((v i).val : ℝ) * θ) := by
    have h := qDiagCLM_const_shift (fun v => ((v i).val : ℝ) * θ) (-(θ / 2))
    simpa [sub_eq_add_neg] using h
  rw [hshift]
  have hfactor :
      (Complex.exp (Complex.I * ((-(θ / 2)) : ℂ)) • qDiagCLM (fun v => ((v i).val : ℝ) * θ))
        - Complex.exp (Complex.I * ((-(θ / 2)) : ℂ)) • qDiagCLM (realPhase (C c * X i))
      = Complex.exp (Complex.I * ((-(θ / 2)) : ℂ))
        • (qDiagCLM (fun v => ((v i).val : ℝ) * θ) - qDiagCLM (realPhase (C c * X i))) := by
    rw [smul_sub]
  rw [hfactor, norm_smul, Complex.norm_exp]
  simpa using hc

/-! ## Operator-side sharpness: the transported grid-midpoint adversary

The `≤` certificate above carries the arc constant `π/2^m`. The sharp OPERATOR-side constant at the
grid-midpoint target `θ = π/2^m` is the chord subtending that arc, `2·sin(π/2^{m+1})`: the lower bound
below transports `rz_dyadic_lower`'s adversary to the operator norm by evaluating the difference gate at
the basis vector on the `v i = 1` branch — a single application of `le_opNorm`, no spectral input. -/

/-- The exact chord between two unit phasors: `‖e^{ia} − e^{ib}‖ = 2·|sin((a−b)/2)|`. -/
theorem norm_exp_I_sub_exp_I (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖
      = 2 * |Real.sin ((a - b) / 2)| := by
  have hfac : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * (((a + b) / 2 : ℝ) : ℂ))
        * (Complex.exp (Complex.I * (((a - b) / 2 : ℝ) : ℂ))
            - Complex.exp (-(Complex.I * (((a - b) / 2 : ℝ) : ℂ)))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring
  have hsin : Complex.exp (Complex.I * (((a - b) / 2 : ℝ) : ℂ))
        - Complex.exp (-(Complex.I * (((a - b) / 2 : ℝ) : ℂ)))
      = 2 * Complex.I * Complex.sin (((a - b) / 2 : ℝ) : ℂ) := by
    rw [Complex.sin,
      show (-((((a - b) / 2 : ℝ)) : ℂ) * Complex.I) = -(Complex.I * (((a - b) / 2 : ℝ) : ℂ)) by ring,
      show (((((a - b) / 2 : ℝ)) : ℂ) * Complex.I) = Complex.I * (((a - b) / 2 : ℝ) : ℂ) by ring]
    field_simp
    linear_combination (Complex.exp (Complex.I * (((a - b) / 2 : ℝ) : ℂ))
      - Complex.exp (-(Complex.I * (((a - b) / 2 : ℝ) : ℂ)))) * Complex.I_mul_I
  have h1 : ‖Complex.exp (Complex.I * (((a + b) / 2 : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have h2I : ‖(2 * Complex.I : ℂ)‖ = 2 := by
    rw [norm_mul, Complex.norm_I, mul_one]; norm_num
  have hs : ‖(((Real.sin ((a - b) / 2) : ℝ)) : ℂ)‖ = |Real.sin ((a - b) / 2)| :=
    RCLike.norm_ofReal _
  rw [hfac, hsin, norm_mul, h1, one_mul, norm_mul, h2I,
    show Complex.sin (((a - b) / 2 : ℝ) : ℂ) = ((Real.sin ((a - b) / 2) : ℝ) : ℂ) from
      (Complex.ofReal_sin _).symm, hs]

/-- The lower-bound engine: the operator norm of a difference of diagonal gates dominates every per-entry
chord (evaluate at the basis vector of the entry). The `≥` counterpart of `qDiag_sub_opNorm_le`. -/
theorem le_opNorm_qDiag_sub (f g : (Fin n → ZMod 2) → ℝ) (v : Fin n → ZMod 2) :
    ‖Complex.exp (Complex.I * f v) - Complex.exp (Complex.I * g v)‖
      ≤ ‖qDiagCLM f - qDiagCLM g‖ := by
  have happ : (qDiagCLM f - qDiagCLM g) (EuclideanSpace.single v (1 : ℂ))
      = EuclideanSpace.single v
          (Complex.exp (Complex.I * f v) - Complex.exp (Complex.I * g v)) := by
    ext w
    rw [ContinuousLinearMap.sub_apply, PiLp.sub_apply, qDiagCLM_apply, qDiagCLM_apply,
      EuclideanSpace.single_apply, EuclideanSpace.single_apply]
    by_cases hw : w = v
    · subst hw; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg hw, if_neg hw]; ring
  have h := (qDiagCLM f - qDiagCLM g).le_opNorm (EuclideanSpace.single v (1 : ℂ))
  rw [happ, EuclideanSpace.norm_single, EuclideanSpace.norm_single] at h
  simpa using h

private lemma sin_le_sin_of_le_of_le_pi_sub {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ Real.pi - x) : Real.sin x ≤ Real.sin y := by
  have hpi := Real.pi_pos
  rcases le_or_gt y (Real.pi / 2) with h | h
  · exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, h⟩ hxy
  · rw [← Real.sin_pi_sub y]
    exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

open Real in
/-- **Exact operator distance for anchored single-qubit patterns.** For two anchored linear phase
patterns on the same carrier bit, the transported gates' operator-norm distance is EXACTLY the
active-branch chord `2·|sin((α−β)/2)|`: the `≤` engine (`qDiag_sub_opNorm_le`, the inactive branch
contributes chord 0) and the `≥` engine (`le_opNorm_qDiag_sub` at the active basis vector) meet. -/
theorem qDiag_sub_opNorm_eq_anchored (α β : ℝ) (i : Fin n) :
    ‖qDiagCLM (fun v => ((v i).val : ℝ) * α) - qDiagCLM (fun v => ((v i).val : ℝ) * β)‖
      = 2 * |Real.sin ((α - β) / 2)| := by
  apply le_antisymm
  · apply qDiag_sub_opNorm_le (by positivity)
    intro v
    rcases zmod2_cases (v i) with h | h
    · rw [h, show (0 : ZMod 2).val = 0 from by decide, Nat.cast_zero, zero_mul, zero_mul]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, norm_zero]
      positivity
    · rw [h, show (1 : ZMod 2).val = 1 from by decide, Nat.cast_one, one_mul, one_mul,
        norm_exp_I_sub_exp_I]
  · set v₁ : Fin n → ZMod 2 := fun j => if j = i then 1 else 0 with hv₁
    have hvi : v₁ i = 1 := by simp [hv₁]
    refine le_trans ?_ (le_opNorm_qDiag_sub (fun v => ((v i).val : ℝ) * α)
      (fun v => ((v i).val : ℝ) * β) v₁)
    rw [hvi, show (1 : ZMod 2).val = 1 from by decide, Nat.cast_one, one_mul, one_mul,
      norm_exp_I_sub_exp_I]

open Real in
/-- **Operator-side sharpness.** The grid-midpoint adversary of `rz_dyadic_lower`, transported to the
operator norm: EVERY precision-`m` gate `C c * X i` is at least `2·sin(π/2^{m+1})` from the anchored
midpoint target `θ = π/2^m` in operator norm — the exact chord constant, the arc constant `π/2^m` shrunk
by exactly the arc-versus-chord gap. Together with `rz_approx_opNorm` (the `≤ π/2^m` side, same target),
the operator-side worst case at precision `m` is pinned between the chord and the arc of the half-spacing.
The `≤` certificate does not depend on this lemma. -/
theorem rz_dyadic_lower_opNorm (i : Fin n) (m : ℕ) (c : ZMod (2 ^ m)) :
    2 * Real.sin (π / 2 ^ (m + 1))
      ≤ ‖qDiagCLM (fun v => ((v i).val : ℝ) * (π / 2 ^ m)) - qDiagCLM (realPhase (C c * X i))‖ := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0:ℕ) < 2 ^ m).ne'⟩
  have hpi : (0:ℝ) < π := pi_pos
  set x : ℝ := π / 2 ^ (m + 1) with hxdef
  have hx0 : (0:ℝ) < x := by rw [hxdef]; positivity
  have hpix : (2:ℝ) ^ (m + 1) * x = π := by rw [hxdef]; field_simp
  -- the active-branch basis label
  set v₁ : Fin n → ZMod 2 := fun j => if j = i then 1 else 0 with hv₁
  have hvi : v₁ i = 1 := by simp [hv₁]
  refine le_trans ?_
    (le_opNorm_qDiag_sub (fun v => ((v i).val : ℝ) * (π / 2 ^ m)) (realPhase (C c * X i)) v₁)
  rw [norm_exp_I_sub_exp_I, realPhase_linear, hvi,
    show (1 : ZMod 2).val = 1 from by decide, Nat.cast_one]
  -- the chord argument is `(1 − 2·c.val)·x`
  have harg : ((1:ℝ) * (π / 2 ^ m) - 1 * (2 * π * (c.val : ℝ) / 2 ^ m)) / 2
      = (1 - 2 * (c.val : ℝ)) * x := by
    rw [hxdef, pow_succ]; field_simp
  rw [harg]
  -- bound the coefficient: `c.val < 2^m`
  have hlt : (c.val : ℝ) < 2 ^ m := by
    have := ZMod.val_lt c
    calc (c.val : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 ^ m := by push_cast; ring
  rcases Nat.eq_zero_or_pos c.val with h0 | hpos
  · -- `c = 0`: the argument is exactly `x`; equality
    have h2le : (2:ℝ) ≤ 2 ^ (m + 1) := by
      calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ one_le_two (by omega)
    have hxpi : x ≤ π := by nlinarith [hpix, hx0, h2le]
    rw [h0, show ((0:ℕ):ℝ) = 0 from Nat.cast_zero,
      show (1 - 2 * (0:ℝ)) * x = x by ring,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx0.le hxpi)]
  · -- `c.val ≥ 1`: the argument is `−(2a−1)x` with `1 ≤ 2a−1 ≤ 2^{m+1}−1`
    have hA1 : (1:ℝ) ≤ (c.val : ℝ) := by exact_mod_cast hpos
    have hflip : (1 - 2 * (c.val : ℝ)) * x = -((2 * (c.val : ℝ) - 1) * x) := by ring
    rw [hflip, Real.sin_neg, abs_neg]
    have hyx : x ≤ (2 * (c.val : ℝ) - 1) * x := by nlinarith
    have hylt : (2 * (c.val : ℝ) - 1) * x ≤ π - x := by
      have h2 : (2:ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      nlinarith [hpix]
    have hy0 : 0 ≤ (2 * (c.val : ℝ) - 1) * x := le_trans hx0.le hyx
    have hypi : (2 * (c.val : ℝ) - 1) * x ≤ π := by linarith
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy0 hypi)]
    have := sin_le_sin_of_le_of_le_pi_sub hx0.le hyx hylt
    linarith

end FTQCLib.Hilbert

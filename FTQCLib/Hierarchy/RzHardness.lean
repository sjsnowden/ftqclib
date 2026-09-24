/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.HierarchyLevel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational

set_option linter.unusedSectionVars false

/-! # No polynomial-phase encoding of an irrational `R_z(θ)`

In the Cui–Gottesman–Krishna framework (`FTQCLib/Hierarchy/Defs.lean`),
the diagonal unitary attached to a phase polynomial
`P : DiagPhase n m = MvPolynomial (Fin n) (ZMod (2^m))` is

  U_P = diag(ξ^{P(v)} : v ∈ (F₂)ⁿ),  ξ = exp(2π·i / 2^m),

so the phase angle (in radians) applied to basis state `v` is the
dyadic rational `2π · (P.eval v).val / 2^m`. The Clifford-hierarchy
level of `U_P` is `(m − 1) + totalDegree(P)`; in particular T, S, Z, CCZ
all fit the framework with appropriate `m` and total degree.

The single-qubit rotation `R_z(θ) = diag(e^{−iθ/2}, e^{iθ/2})` applies
a *real-valued* phase angle `θ` (modulo a global phase) between the
two computational-basis states. If `θ/π` is irrational, this phase is
incommensurable with the dyadic-rational grid `(2π/2^m)·ℤ`, so `R_z(θ)`
cannot be `U_P` for any precision `m` or polynomial `P`.

This file makes that argument precise:

* `DiagPhase.realPhase P v` is the actual real-number phase angle
  produced by `U_P` at basis state `v`.
* `realPhase_sub_isRat_mul_two_pi` records the structural fact that
  any difference of `realPhase` values is a rational multiple of `2π`.
* `rz_irrational_not_polyEncodable` packages the contradiction: no
  polynomial `P` (any precision `m`, any global-phase offset `φ`) can
  realise the `R_z(θ)` pattern modulo `2π` when `θ/π` is irrational.

The argument is purely number-theoretic — it does not need any
operator-side machinery beyond the `realPhase` bridge. -/

namespace FTQCLib.Hierarchy.DiagPhase

variable {n m : ℕ}

/-- The actual real-number phase angle (in radians) applied by `U_P`
to the computational-basis state indexed by `v : (F₂)ⁿ`. By definition
of the polynomial-phase framework `U_P` has diagonal entry
`ξ^{P(v)}` with `ξ = exp(2π·i / 2^m)`, so the radian phase is
`2π · (P.eval v).val / 2^m` — always a dyadic-rational multiple of
`2π`. -/
noncomputable def realPhase (P : DiagPhase n m) (v : Fin n → ZMod 2) : ℝ :=
  2 * Real.pi * (P.eval v).val / (2 : ℝ)^m

/-- **Bridge lemma**: the difference of two `realPhase` values is a
rational multiple of `2π`. Concretely the rational is
`((P.eval v).val − (P.eval w).val) / 2^m`. This captures the discrete
constraint imposed by the polynomial-phase framework: phase
differences live on the dyadic-rational subgroup of `ℝ/2πℤ`. -/
theorem realPhase_sub_isRat_mul_two_pi (P : DiagPhase n m)
    (v w : Fin n → ZMod 2) :
    ∃ (q : ℚ), realPhase P v - realPhase P w = 2 * Real.pi * (q : ℝ) := by
  refine ⟨((P.eval v).val : ℚ) / (2 : ℚ)^m
            - ((P.eval w).val : ℚ) / (2 : ℚ)^m, ?_⟩
  unfold realPhase
  have htwo_ne : ((2 : ℝ)^m) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  field_simp

/-- **Hardness theorem**: no diagonal phase polynomial `P` can encode
the `R_z(θ)` rotation on qubit `i` when `θ/π` is irrational.

The encoding condition asks: there exist `m : ℕ`, a phase polynomial
`P : DiagPhase n m`, and a global-phase offset `φ : ℝ`, such that for
every binary input `v` the polynomial-framework phase angle
`realPhase P v` agrees with `(v i).val · θ + φ` modulo `2π`. The
modular freedom is captured by the integer `k`.

The proof contradicts irrationality of `θ/π`: evaluating the encoding
at the all-zeros vector `v₀` and at `v₁ = update v₀ i 1` and
subtracting, the LHS is forced to be a rational multiple of `2π`
(`realPhase_sub_isRat_mul_two_pi`), while the RHS is `θ` plus an
integer multiple of `2π`. Combining yields `θ/π ∈ ℚ`. -/
theorem rz_irrational_not_polyEncodable {n : ℕ}
    (θ : ℝ) (hθ : Irrational (θ / Real.pi)) (i : Fin n) :
    ¬ ∃ (m : ℕ) (P : DiagPhase n m) (φ : ℝ),
      ∀ (v : Fin n → ZMod 2),
        ∃ (k : ℤ),
          realPhase P v = (v i).val * θ + φ + 2 * Real.pi * k := by
  rintro ⟨m, P, φ, hEnc⟩
  -- Set up the two test vectors `v₀ = 0` and `v₁ = update v₀ i 1`.
  let v₀ : Fin n → ZMod 2 := fun _ => 0
  let v₁ : Fin n → ZMod 2 := Function.update v₀ i 1
  -- Apply the encoding hypothesis at `v₀` and `v₁`.
  obtain ⟨k₀, hEnc₀⟩ := hEnc v₀
  obtain ⟨k₁, hEnc₁⟩ := hEnc v₁
  -- Compute `(v₀ i).val = 0`.
  have hv₀i : (v₀ i).val = 0 := by
    change ((0 : ZMod 2)).val = 0
    exact ZMod.val_zero
  -- Compute `(v₁ i).val = 1`. We use `Fact (1 < 2)` so `(1 : ZMod 2).val = 1`.
  have hv₁i : (v₁ i).val = 1 := by
    have h_eq : v₁ i = (1 : ZMod 2) := by
      change Function.update v₀ i 1 i = 1
      exact Function.update_self i 1 v₀
    rw [h_eq]
    haveI : Fact (1 < 2) := ⟨by norm_num⟩
    exact ZMod.val_one 2
  -- Substitute the val values into `hEnc₀` and `hEnc₁`.
  rw [hv₀i] at hEnc₀
  rw [hv₁i] at hEnc₁
  -- Subtract: realPhase P v₁ − realPhase P v₀ = θ + 2π·(k₁ − k₀).
  have hdiff_rhs :
      realPhase P v₁ - realPhase P v₀
        = θ + 2 * Real.pi * ((k₁ : ℝ) - (k₀ : ℝ)) := by
    rw [hEnc₁, hEnc₀]
    push_cast
    ring
  -- The bridge lemma gives a rational `q` with the LHS = 2π·q.
  obtain ⟨q, hq⟩ := realPhase_sub_isRat_mul_two_pi P v₁ v₀
  -- Combine: 2π·q = θ + 2π·(k₁ − k₀), so θ = 2π·(q − (k₁ − k₀)).
  have hθ_eq : θ = 2 * Real.pi * ((q : ℝ) - ((k₁ : ℝ) - (k₀ : ℝ))) := by
    have hcombined : 2 * Real.pi * (q : ℝ)
        = θ + 2 * Real.pi * ((k₁ : ℝ) - (k₀ : ℝ)) := by
      rw [← hq]; exact hdiff_rhs
    linarith
  -- Therefore θ / π = 2 · (q − (k₁ − k₀)), a rational.
  have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hθ_over_pi :
      θ / Real.pi = 2 * ((q : ℝ) - ((k₁ : ℝ) - (k₀ : ℝ))) := by
    rw [hθ_eq]
    field_simp
  -- Build the witness rational `q' = 2 · (q − (k₁ − k₀))` and conclude.
  set q' : ℚ := 2 * (q - ((k₁ : ℚ) - (k₀ : ℚ))) with hq'_def
  have hθ_eq_q' : θ / Real.pi = (q' : ℝ) := by
    rw [hθ_over_pi, hq'_def]
    push_cast
    ring
  -- This contradicts `Irrational (θ / Real.pi)`.
  exact hθ ⟨q', hθ_eq_q'.symm⟩

end FTQCLib.Hierarchy.DiagPhase

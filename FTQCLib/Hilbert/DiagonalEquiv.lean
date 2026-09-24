/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Diagonal

set_option linter.unusedSectionVars false

/-! # Diagonal gates as linear equivalences

`Diagonal.lean` defines `diagonalGate f` as a `LinearMap` on the qubit
Hilbert space. For applications that need invertibility — composing
diagonal gates as a group, identifying the codespace setwise rather
than as a containment, or treating the gate as a unitary change of
basis — it is more convenient to package `diagonalGate f` as a
`LinearEquiv`. This file does the packaging.

A diagonal phase gate with pattern `f : (Fin n → ZMod 2) → ℝ` has
inverse equal to the diagonal phase gate with pattern `-f`, because
the pointwise product `e^{i·f(v)} · e^{-i·f(v)} = 1`. So
`diagonalGateEquiv f` is the linear equivalence whose forward map is
`diagonalGate f` and whose inverse is `diagonalGate (-f)`.

The file records the basic identities:

* `diagonalGateEquiv_apply` / `diagonalGateEquiv_symm_apply` — the
  forward and inverse maps agree with the underlying `diagonalGate`s.
* `diagonalGateEquiv_zero` — the equivalence for the zero phase
  pattern is the identity.
* `diagonalGateEquiv_add` — composing two diagonal-gate equivalences
  gives the diagonal-gate equivalence for the sum of phase patterns
  (the phase-multiplication identity `e^{i·f} · e^{i·g} = e^{i·(f+g)}`).
-/

namespace FTQCLib.Hilbert

variable {n : ℕ}

/-- Pointwise verification that the diagonal gate with phase pattern
`-f` is a left inverse of the diagonal gate with phase pattern `f`. -/
private lemma diagonalGate_neg_comp_self
    (f : (Fin n → ZMod 2) → ℝ) (ψ : QubitSpace n) :
    diagonalGate (fun v => -f v) (diagonalGate f ψ) = ψ := by
  funext v
  simp only [diagonalGate_apply]
  have h₁ : Complex.exp (Complex.I * ((-f v : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * (f v : ℂ)))⁻¹ := by
    rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  rw [h₁]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]

/-- Pointwise verification that the diagonal gate with phase pattern
`-f` is a right inverse of the diagonal gate with phase pattern `f`. -/
private lemma diagonalGate_self_comp_neg
    (f : (Fin n → ZMod 2) → ℝ) (ψ : QubitSpace n) :
    diagonalGate f (diagonalGate (fun v => -f v) ψ) = ψ := by
  funext v
  simp only [diagonalGate_apply]
  have h₁ : Complex.exp (Complex.I * ((-f v : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * (f v : ℂ)))⁻¹ := by
    rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg]
  rw [h₁]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]

/-- The diagonal phase gate packaged as a linear equivalence on
`QubitSpace n`. Forward map is `diagonalGate f`; inverse is the
diagonal phase gate with the negated phase pattern. -/
noncomputable def diagonalGateEquiv (f : (Fin n → ZMod 2) → ℝ) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n where
  toFun := diagonalGate f
  map_add' := (diagonalGate f).map_add'
  map_smul' := (diagonalGate f).map_smul'
  invFun := diagonalGate (fun v => -f v)
  left_inv := diagonalGate_neg_comp_self f
  right_inv := diagonalGate_self_comp_neg f

@[simp] theorem diagonalGateEquiv_apply
    (f : (Fin n → ZMod 2) → ℝ) (ψ : QubitSpace n) :
    diagonalGateEquiv f ψ = diagonalGate f ψ := rfl

@[simp] theorem diagonalGateEquiv_symm_apply
    (f : (Fin n → ZMod 2) → ℝ) (ψ : QubitSpace n) :
    (diagonalGateEquiv f).symm ψ = diagonalGate (fun v => -f v) ψ := rfl

@[simp] theorem diagonalGateEquiv_toLinearMap
    (f : (Fin n → ZMod 2) → ℝ) :
    (diagonalGateEquiv f).toLinearMap = diagonalGate f := rfl

/-- The zero phase pattern gives the identity equivalence: every
computational basis vector picks up a phase factor of `e^{i·0} = 1`. -/
@[simp] theorem diagonalGateEquiv_zero :
    diagonalGateEquiv (0 : (Fin n → ZMod 2) → ℝ) = LinearEquiv.refl ℂ (QubitSpace n) := by
  refine LinearEquiv.toLinearMap_injective ?_
  refine LinearMap.ext (fun ψ => ?_)
  funext v
  change diagonalGate 0 ψ v = ψ v
  rw [diagonalGate_apply]
  change Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) * ψ v = ψ v
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]

/-- Composing two diagonal-gate equivalences in either order gives the
diagonal-gate equivalence for the sum of phase patterns. The phase
multiplication identity `e^{i·f(v)} · e^{i·g(v)} = e^{i·(f(v)+g(v))}`
makes the composition pointwise equal to a single diagonal gate. -/
theorem diagonalGateEquiv_add (f g : (Fin n → ZMod 2) → ℝ) :
    diagonalGateEquiv (f + g) =
      (diagonalGateEquiv f).trans (diagonalGateEquiv g) := by
  refine LinearEquiv.toLinearMap_injective ?_
  refine LinearMap.ext (fun ψ => ?_)
  funext v
  change diagonalGate (f + g) ψ v = diagonalGate g (diagonalGate f ψ) v
  rw [diagonalGate_apply, diagonalGate_apply, diagonalGate_apply]
  rw [Pi.add_apply, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

end FTQCLib.Hilbert

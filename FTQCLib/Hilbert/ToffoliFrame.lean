/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.GateLifts
import FTQCLib.Hilbert.Hierarchy
import FTQCLib.Hierarchy.GatePolynomials

/-! # The frame in use — Toffoli = H·CCZ·H, as operators

A "frame in use" demonstration. The frame names and prices the **diagonal** level-3 gate CCZ; the
universal reversible gate **Toffoli (CCX)** is its Hadamard-conjugate. Here we *prove* that at the
operator level, against an **independently defined** Toffoli permutation — so the identity is a
theorem (the diagonal core *equals* the universal gate, one Hadamard away), not a definition.

* `toffoliPerm` / `toffoliGate` — the standard CCNOT permutation `|v⟩ ↦ |v with k ↦ v_k ⊕ v_i·v_j⟩`
  and its Hilbert unitary (precomposition with the involutive permutation), with no reference to
  H or CCZ.
* `cczOperator` — the diagonal level-3 kernel `diagonalGateEquiv (realPhase cczPoly)`, acting as the
  sign `(-1)^{v_i v_j v_k}`.
* `toffoliGate_eq_hadamard_conj_ccz` — the identity `CCX = H_k · CCZ · H_k`, via the nested
  Walsh-transform collapse `∑_c (-1)^{c·s} = 2·[s=0]`.
-/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Hierarchy FTQCLib.Pauli

variable {n : ℕ}

/-! ### The standard Toffoli permutation and its unitary -/

/-- The Toffoli (CCNOT) basis permutation: flip qubit `k` controlled by `i ∧ j`,
`v ↦ v` with `v_k ↦ v_k + v_i·v_j` (over `ZMod 2`). Defined with no reference to H or CCZ. -/
def toffoliPerm (i j k : Fin n) (v : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  Function.update v k (v k + v i * v j)

/-- The Toffoli permutation is an involution (when `k ∉ {i, j}`): the control `v_i·v_j` is unchanged
by flipping `k`, so flipping twice returns. -/
theorem toffoliPerm_involutive (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Fin n → ZMod 2) : toffoliPerm i j k (toffoliPerm i j k v) = v := by
  funext l
  unfold toffoliPerm
  rcases eq_or_ne l k with rfl | hl
  · rw [Function.update_self, Function.update_self,
      Function.update_of_ne hik, Function.update_of_ne hjk,
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [Function.update_of_ne hl, Function.update_of_ne hl]

/-- The Toffoli gate as a Hilbert unitary: precomposition with the (involutive) permutation. -/
noncomputable def toffoliGate (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n where
  toFun ψ := fun w => ψ (toffoliPerm i j k w)
  map_add' ψ φ := by funext w; simp [Pi.add_apply]
  map_smul' c ψ := by funext w; simp
  invFun ψ := fun w => ψ (toffoliPerm i j k w)
  left_inv ψ := by funext w; simp [toffoliPerm_involutive i j k hik hjk]
  right_inv ψ := by funext w; simp [toffoliPerm_involutive i j k hik hjk]

@[simp] theorem toffoliGate_apply (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    toffoliGate i j k hik hjk ψ w = ψ (toffoliPerm i j k w) := rfl

/-! ### The CCZ operator (the frame's diagonal level-3 kernel) -/

/-- The CCZ gate as a Hilbert unitary: the frame's diagonal kernel for the exponent
`cczPoly i j k = j_i·j_j·j_k`. Acts as `ψ v ↦ (-1)^{v_i v_j v_k} ψ v`. -/
noncomputable def cczOperator (i j k : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (DiagPhase.realPhase (DiagPhase.cczPoly i j k))

/-- **CCZ acts as the diagonal sign** `(-1)^{v_i v_j v_k}`. The exponent `cczPoly = j_i·j_j·j_k`
evaluates to `v_i·v_j·v_k` over `𝔽₂`, and at precision `m = 1` the real phase `π·(eval).val` gives
the `(-1)`-power. -/
theorem cczOperator_apply (i j k : Fin n) (g : QubitSpace n) (w : Fin n → ZMod 2) :
    cczOperator i j k g w = (-1 : ℂ) ^ (w i * w j * w k).val * g w := by
  unfold cczOperator
  rw [diagonalGateEquiv_apply, diagonalGate_apply]
  have heval : DiagPhase.eval (DiagPhase.cczPoly i j k) w = w i * w j * w k := by
    unfold DiagPhase.eval DiagPhase.cczPoly
    rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_X]
    simp [DiagPhase.liftBinary]
  -- pass to a `ℕ`-level `.val` equality (sidesteps the `ZMod (2^1)` vs `ZMod 2` motive issue)
  have hval : (DiagPhase.eval (DiagPhase.cczPoly i j k) w).val = (w i * w j * w k).val :=
    congrArg ZMod.val heval
  have hexp : Complex.exp (Complex.I * (DiagPhase.realPhase (DiagPhase.cczPoly i j k) w : ℂ))
      = (-1 : ℂ) ^ (w i * w j * w k).val := by
    have hrp : DiagPhase.realPhase (DiagPhase.cczPoly i j k) w
        = Real.pi * ((w i * w j * w k).val : ℝ) := by
      unfold DiagPhase.realPhase; rw [hval, pow_one]; ring
    have harg : Complex.I * (DiagPhase.realPhase (DiagPhase.cczPoly i j k) w : ℂ)
        = ((w i * w j * w k).val : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      rw [hrp]; push_cast; ring
    rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [hexp]

/-! ### The frame in use — `Toffoli = H·CCZ·H`

The main identity. `toffoliGate` is defined independently (a basis permutation), `cczOperator`
is the frame's diagonal level-3 kernel, and `hadamardEquiv` is the Walsh transform. The proof is the
nested Walsh-sum collapse `∑_c (-1)^{c·s} = 2·[s=0]`: conjugating the diagonal CCZ by `H_k` rotates
the target qubit from the Z-basis (phase) to the X-basis (flip), producing the controlled-controlled
flip. -/

/-- **`Toffoli = H_k · CCZ_{ijk} · H_k`** as operators on `QubitSpace n` (for `i ≠ k`, `j ≠ k`). The
universal reversible gate is the Hadamard-conjugate of the frame's diagonal level-3 core — the frame
in use, proved against an independently-defined Toffoli rather than assumed. -/
theorem toffoliGate_eq_hadamard_conj_ccz (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    toffoliGate i j k hik hjk = conjEquiv (hadamardEquiv k) (cczOperator i j k) := by
  apply LinearEquiv.ext
  intro ψ
  funext w
  rw [conjEquiv_apply, hadamardEquiv_symm_apply, hadamardEquiv_apply]
  have hsum2 : ∀ f : ZMod 2 → ℂ, ∑ b : ZMod 2, f b = f 0 + f 1 := fun f => Fin.sum_univ_two f
  simp only [toffoliGate_apply, toffoliPerm, hadamardGate_apply, cczOperator_apply,
    Function.update_self, Function.update_idem, Function.update_of_ne hik,
    Function.update_of_ne hjk, hsum2]
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (w k) with hwk | hwk <;> rcases dich (w i * w j) with ha | ha <;>
    simp only [hwk, ha, e0, e1, mul_zero, mul_one, one_mul, pow_zero, pow_one,
      add_zero, zero_add, CharTwo.add_self_eq_zero]
  · linear_combination (-2 * ψ (Function.update w k 0)) * invSqrt2_mul_self
  · linear_combination (-2 * ψ (Function.update w k 1)) * invSqrt2_mul_self
  · linear_combination (-2 * ψ (Function.update w k 1)) * invSqrt2_mul_self
  · linear_combination (-2 * ψ (Function.update w k 0)) * invSqrt2_mul_self

/-! ### Pricing Toffoli through its diagonal core -/

/-- **Price-by-the-core.** The operator Toffoli is the Hadamard-conjugate of its diagonal core
`cczOperator i j k`, and that core carries frame level `3` (the exponent `cczPoly` has functional
degree `3` at precision `1`). The frame can't see the non-diagonal Toffoli directly, but prices it
by pricing the diagonal heart and noting the Hadamard is a Clifford — the demonstration that the
calculus reaches the universal reversible gate. -/
theorem toffoliGate_priced_via_ccz_core (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    toffoliGate i j k hik hjk = conjEquiv (hadamardEquiv k) (cczOperator i j k)
      ∧ (DiagPhase.cczPoly i j k).level = 3 :=
  ⟨toffoliGate_eq_hadamard_conj_ccz i j k hik hjk, DiagPhase.cczPoly_level i j k⟩

end FTQCLib.Hilbert

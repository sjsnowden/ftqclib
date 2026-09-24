/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.PauliProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.CharP.Two

set_option linter.unusedSectionVars false

/-! # The qubit inner product and Hermitian Pauli operators

`FTQCLib.Hilbert.QubitSpace n` carries only the bare function-space module
structure; measurement statements need an inner product. We work on the
type synonym

  `QState n := EuclideanSpace ℂ (Fin n → ZMod 2)`,

the ℓ² space on the `2ⁿ` computational labels, and transport the Pauli
operators across the canonical linear equivalence `toQState`.

`FTQCLib.Hilbert.pauliOperator` drops the global `i^{X·Z}` phase, so it is
self-adjoint and an involution only for X- and Z-type Paulis. The
**Hermitian Pauli**

  `pauliHermitian p := (Complex.I)^(xzWeight p) • qPauli p`,

restores that phase (`xzWeight p = ∑ᵢ (p.X i)(p.Z i)` qubits carry a `Y`),
and is self-adjoint with `pauliHermitian p ∘ pauliHermitian p = id` for
every `p`. This file establishes the involution property; self-adjointness,
the expectation value, and the Born probability follow.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-- The `n`-qubit state space with its ℓ² inner product. -/
abbrev QState (n : ℕ) : Type := EuclideanSpace ℂ (Fin n → ZMod 2)

/-- Identify the bare function space `QubitSpace n` with the ℓ² space
`QState n`. The map is the identity on functions; only the norm/inner
product structure changes. -/
noncomputable def toQState : QubitSpace n ≃ₗ[ℂ] QState n :=
  (WithLp.linearEquiv 2 ℂ (QubitSpace n)).symm

/-- The X·Z overlap weight of a Pauli: the number of qubits carrying a
`Y` (both an X- and a Z-support bit). -/
noncomputable def xzWeight (p : Pauli n) : ℕ := zDotVal p p.X

/-- `pauliOperator p` transported to `QState n`. -/
noncomputable def qPauli (p : Pauli n) : QState n →ₗ[ℂ] QState n :=
  toQState.toLinearMap ∘ₗ pauliOperator p ∘ₗ toQState.symm.toLinearMap

theorem qPauli_apply (p : Pauli n) (ψ : QState n) :
    qPauli p ψ = toQState (pauliOperator p (toQState.symm ψ)) := rfl

/-- The Hermitian Pauli operator on `QState n`. -/
noncomputable def pauliHermitian (p : Pauli n) : QState n →ₗ[ℂ] QState n :=
  (Complex.I) ^ (xzWeight p) • qPauli p

theorem pauliHermitian_apply (p : Pauli n) (ψ : QState n) :
    pauliHermitian p ψ = (Complex.I) ^ (xzWeight p) • qPauli p ψ := rfl

/-- Squaring the (phaseless) transported Pauli yields the sign `(-1)^{xzWeight}`. -/
theorem qPauli_sq_apply (p : Pauli n) (ψ : QState n) :
    qPauli p (qPauli p ψ) = ((-1 : ℂ) ^ (xzWeight p)) • ψ := by
  simp only [qPauli_apply, LinearEquiv.symm_apply_apply]
  rw [pauliOperator_apply_pauliOperator_apply]
  have hpp : p + p = 0 := by ext i <;> exact CharTwo.add_self_eq_zero _
  rw [hpp, pauliOperator_zero]
  simp only [LinearMap.id_coe, id_eq, map_smul, LinearEquiv.apply_symm_apply]
  rfl

/-- The Hermitian Pauli is an involution: `H(p) ∘ H(p) = id`. -/
theorem pauliHermitian_sq (p : Pauli n) :
    pauliHermitian p ∘ₗ pauliHermitian p = LinearMap.id := by
  ext ψ
  simp only [LinearMap.comp_apply, LinearMap.id_apply, pauliHermitian_apply,
    map_smul, smul_smul]
  rw [qPauli_sq_apply, smul_smul]
  have hscalar :
      (Complex.I) ^ (xzWeight p) * (Complex.I) ^ (xzWeight p) * (-1 : ℂ) ^ (xzWeight p) = 1 := by
    have hI : (Complex.I) ^ (xzWeight p) * (Complex.I) ^ (xzWeight p)
        = (-1 : ℂ) ^ (xzWeight p) := by
      rw [← pow_add, ← two_mul, pow_mul, Complex.I_sq]
    rw [hI, ← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hscalar, one_smul]

/-- The transported computational basis vector `|v⟩` in `QState n`. -/
noncomputable def qComputational (v : Fin n → ZMod 2) : QState n :=
  toQState (computational v)

/-- The transported Pauli sends `|v⟩` to `(-1)^{p.Z·v} |v + p.X⟩`. -/
theorem qPauli_qComputational (p : Pauli n) (v : Fin n → ZMod 2) :
    qPauli p (qComputational v) = ((-1 : ℂ) ^ (zDotVal p v)) • qComputational (v + p.X) := by
  simp only [qComputational, qPauli_apply, LinearEquiv.symm_apply_apply,
    pauliOperator_computational, map_smul]

/-- The Hermitian Pauli sends `|v⟩` to `iˣᶻ (-1)^{p.Z·v} |v + p.X⟩`. -/
theorem pauliHermitian_qComputational (p : Pauli n) (v : Fin n → ZMod 2) :
    pauliHermitian p (qComputational v)
      = ((Complex.I) ^ (xzWeight p) * (-1 : ℂ) ^ (zDotVal p v)) • qComputational (v + p.X) := by
  rw [pauliHermitian_apply, qPauli_qComputational, smul_smul]

/-- Composition of transported Paulis carries the phaseless Pauli-product cocycle
`(-1)^{q.Z·p.X}` (transport of `pauliOperator_mul`). -/
theorem qPauli_mul_apply (p q : Pauli n) (ψ : QState n) :
    qPauli q (qPauli p ψ) = ((-1 : ℂ) ^ (zDotVal q p.X)) • qPauli (p + q) ψ := by
  simp only [qPauli_apply, LinearEquiv.symm_apply_apply]
  rw [pauliOperator_apply_pauliOperator_apply, map_smul]

theorem qPauli_mul (p q : Pauli n) :
    qPauli q ∘ₗ qPauli p = ((-1 : ℂ) ^ (zDotVal q p.X)) • qPauli (p + q) := by
  ext ψ
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, qPauli_mul_apply]

/-- The transported identity Pauli is the identity map. -/
theorem qPauli_zero : qPauli (0 : Pauli n) = LinearMap.id := by
  ext ψ
  simp [qPauli_apply, pauliOperator_zero]

/-- A triple of transported Paulis whose symplectic vectors sum to zero composes to a sign times
the identity (the cocycle phases accumulate; the support shift returns to the origin). -/
theorem qPauli_triple_of_sum_zero (a b c : Pauli n) (h : a + b + c = 0) :
    qPauli c ∘ₗ qPauli b ∘ₗ qPauli a
      = ((-1 : ℂ) ^ (zDotVal b a.X + zDotVal c (a + b).X)) • LinearMap.id := by
  rw [qPauli_mul a b, LinearMap.comp_smul, qPauli_mul (a + b) c, smul_smul, ← pow_add, h,
    qPauli_zero]

/-- A triple of **Hermitian** Paulis whose symplectic vectors sum to zero composes to a scalar
(a fourth root of unity) times the identity. For a commuting triple the scalar is `±1`; this is
the operator content behind the Mermin–Peres / Kochen–Specker witness. -/
theorem pauliHermitian_triple_of_sum_zero (a b c : Pauli n) (h : a + b + c = 0) :
    pauliHermitian c ∘ₗ pauliHermitian b ∘ₗ pauliHermitian a
      = (Complex.I ^ xzWeight a * Complex.I ^ xzWeight b * Complex.I ^ xzWeight c
          * (-1 : ℂ) ^ (zDotVal b a.X + zDotVal c (a + b).X)) • LinearMap.id := by
  simp only [pauliHermitian, LinearMap.smul_comp, LinearMap.comp_smul]
  rw [qPauli_triple_of_sum_zero a b c h]
  simp only [smul_smul]
  congr 1
  ring

/-- `computational v` is the standard basis function `Pi.single v 1`. -/
theorem computational_eq_pi_single (v : Fin n → ZMod 2) :
    computational v = Pi.single v (1 : ℂ) := by
  funext w
  simp [computational, Pi.single_apply]

/-- The transported basis vector is the Euclidean standard basis vector. -/
theorem qComputational_eq_single (v : Fin n → ZMod 2) :
    qComputational v = EuclideanSpace.single v (1 : ℂ) := by
  rw [qComputational, computational_eq_pi_single]
  rfl

/-- The transported computational basis is orthonormal. -/
theorem inner_qComputational (v w : Fin n → ZMod 2) :
    inner ℂ (qComputational v) (qComputational w) = if v = w then 1 else 0 := by
  rw [qComputational_eq_single, qComputational_eq_single,
    EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply, map_one]

/-- `toQState` is the identity on the underlying functions. -/
@[simp] theorem toQState_apply (x : QubitSpace n) (w : Fin n → ZMod 2) :
    toQState x w = x w := rfl

/-- `toQState.symm` is the identity on the underlying functions. -/
@[simp] theorem toQState_symm_apply (x : QState n) (w : Fin n → ZMod 2) :
    toQState.symm x w = x w := rfl

/-- Pointwise action of `pauliOperator`. -/
theorem pauliOperator_apply_fun (p : Pauli n) (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    pauliOperator p ψ w = (-1 : ℂ) ^ (zDotVal p (w - p.X)) * ψ (w - p.X) := rfl

/-- Pointwise action of the transported Pauli. -/
theorem qPauli_apply_fun (p : Pauli n) (x : QState n) (w : Fin n → ZMod 2) :
    qPauli p x w = (-1 : ℂ) ^ (zDotVal p (w - p.X)) * x (w - p.X) := by
  simp only [qPauli_apply, toQState_apply, pauliOperator_apply_fun, toQState_symm_apply]

/-- Pointwise action of the Hermitian Pauli. -/
theorem pauliHermitian_apply_fun (p : Pauli n) (x : QState n) (w : Fin n → ZMod 2) :
    pauliHermitian p x w
      = (Complex.I) ^ (xzWeight p) * ((-1 : ℂ) ^ (zDotVal p (w - p.X)) * x (w - p.X)) := by
  rw [pauliHermitian_apply, PiLp.smul_apply, qPauli_apply_fun, smul_eq_mul]

/-- The Hermitian Pauli is a (linear) isometry: it preserves the inner product. The unit-modulus
phase `iˣᶻ` and the signs `(-1)^{p.Z·(w-p.X)}` each cancel against their conjugates, and the
shift `w ↦ w - p.X` is a bijection. -/
theorem pauliHermitian_inner (p : Pauli n) (x y : QState n) :
    inner ℂ (pauliHermitian p x) (pauliHermitian p y) = inner ℂ x y := by
  have hterm : ∀ w : Fin n → ZMod 2,
      (inner ℂ (pauliHermitian p x w) (pauliHermitian p y w) : ℂ)
        = inner ℂ (x (w - p.X)) (y (w - p.X)) := by
    intro w
    rw [pauliHermitian_apply_fun, pauliHermitian_apply_fun, RCLike.inner_apply, RCLike.inner_apply]
    simp only [map_mul, map_pow, Complex.conj_I, map_neg, map_one]
    have hI : (Complex.I) ^ xzWeight p * (-Complex.I) ^ xzWeight p = 1 := by
      rw [← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow]
    have hs : ((-1 : ℂ) ^ zDotVal p (w - p.X)) * ((-1 : ℂ) ^ zDotVal p (w - p.X)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination
      (((-1 : ℂ) ^ zDotVal p (w - p.X)) * ((-1 : ℂ) ^ zDotVal p (w - p.X))
          * y (w - p.X) * (starRingEnd ℂ) (x (w - p.X))) * hI
        + (y (w - p.X) * (starRingEnd ℂ) (x (w - p.X))) * hs
  rw [PiLp.inner_apply, PiLp.inner_apply, Finset.sum_congr rfl (fun w _ => hterm w)]
  exact Fintype.sum_equiv (Equiv.subRight p.X)
    (fun w => inner ℂ (x (w - p.X)) (y (w - p.X)))
    (fun w => inner ℂ (x w) (y w))
    (fun w => rfl)

/-- The Hermitian Pauli is symmetric: `⟪H(p) x, y⟫ = ⟪x, H(p) y⟫`. Immediate from the isometry
`pauliHermitian_inner` and the involution `pauliHermitian_sq`: rewrite `y` as `H(p) (H(p) y)`. -/
theorem pauliHermitian_isSymmetric (p : Pauli n) :
    (pauliHermitian p).IsSymmetric := by
  intro x y
  have hinv : pauliHermitian p (pauliHermitian p y) = y := by
    have h2 := LinearMap.congr_fun (pauliHermitian_sq p) y
    simpa [LinearMap.comp_apply] using h2
  calc inner ℂ (pauliHermitian p x) y
      = inner ℂ (pauliHermitian p x) (pauliHermitian p (pauliHermitian p y)) := by rw [hinv]
    _ = inner ℂ x (pauliHermitian p y) := pauliHermitian_inner p x (pauliHermitian p y)

/-- The Hermitian Pauli is self-adjoint. -/
theorem pauliHermitian_isSelfAdjoint (p : Pauli n) :
    IsSelfAdjoint (pauliHermitian p) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp (pauliHermitian_isSymmetric p)

/-- The expectation value `⟪ψ, H(p) ψ⟫` of the Hermitian Pauli `H(p)` in the state `ψ`. -/
noncomputable def expectation (ψ : QState n) (p : Pauli n) : ℂ :=
  inner ℂ ψ (pauliHermitian p ψ)

/-- The expectation value of a Hermitian Pauli is real (it is a self-adjoint observable). -/
theorem expectation_real (ψ : QState n) (p : Pauli n) :
    (starRingEnd ℂ) (expectation ψ p) = expectation ψ p := by
  rw [expectation, inner_conj_symm]
  exact pauliHermitian_isSymmetric p ψ ψ

/-- Accuracy anchor and Prop-2 eigenvalue case: a `Z`-type Pauli (`p.X = 0`) acts diagonally on the
computational basis, so its expectation in `|v⟩` is exactly the eigenvalue `(-1)^{p.Z·v}`. In
particular `Z` on `|0⟩` gives `+1`. -/
theorem expectation_qComputational_of_X_eq_zero
    (p : Pauli n) (hp : p.X = 0) (v : Fin n → ZMod 2) :
    expectation (qComputational v) p = (-1 : ℂ) ^ (zDotVal p v) := by
  have hxz : xzWeight p = 0 := by
    unfold xzWeight; rw [hp]; unfold zDotVal; simp
  rw [expectation, pauliHermitian_qComputational, hp, add_zero, hxz, pow_zero, one_mul,
    inner_smul_right, inner_qComputational]
  simp

end FTQCLib.Hilbert


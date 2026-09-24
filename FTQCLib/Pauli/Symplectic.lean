/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

/-! # Symplectic structure on the Pauli group

The symplectic form on the binary symplectic representation of the Pauli
group on `n` qubits:

    ω(p, q) = ∑ᵢ p.Z i · q.X i + ∑ᵢ p.X i · q.Z i   (sum in `ZMod 2`).

Two original Paulis commute (in the full Pauli group with phases) iff their
effective representatives have `ω` between them equal to `0`. The form is
bilinear, alternating, and (in characteristic 2) symmetric, and
non-degenerate.

This file proves:

* **P3** `omega`, `omega_add_left`, `omega_add_right`, `omega_smul_left`,
  `omega_smul_right` — symplectic form, bilinear.
* **P4** `omega_self`, `omega_comm` — alternating in characteristic 2,
  hence symmetric.
* `omega_zero_left`, `omega_zero_right` — vanishing on zero.
* `omega_nondegenerate` — non-degenerate.
* `omegaBilin` — same form packaged as a `LinearMap.BilinForm` for use with
  Mathlib's bilinear-form machinery.
-/

namespace FTQCLib.Pauli

open Finset

variable {n : ℕ}

/-- The symplectic form on `Pauli n`:
`ω(p, q) = ⟨p.Z, q.X⟩ + ⟨p.X, q.Z⟩` (mod 2), where `⟨·,·⟩` is the
standard dot product on `(ZMod 2)^n`. Two original Paulis commute iff their
effective representatives have `ω` between them equal to `0`. -/
def omega (p q : Pauli n) : ZMod 2 :=
  (∑ i, p.Z i * q.X i) + (∑ i, p.X i * q.Z i)

/-- The symplectic form is additive in the first argument. -/
theorem omega_add_left (p₁ p₂ q : Pauli n) :
    omega (p₁ + p₂) q = omega p₁ q + omega p₂ q := by
  simp only [omega, X_add, Z_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  abel

/-- The symplectic form is additive in the second argument. -/
theorem omega_add_right (p q₁ q₂ : Pauli n) :
    omega p (q₁ + q₂) = omega p q₁ + omega p q₂ := by
  simp only [omega, X_add, Z_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  abel

/-- The symplectic form is `ZMod 2`-linear in the first argument:
`ω(a · p, q) = a · ω(p, q)`. -/
theorem omega_smul_left (a : ZMod 2) (p q : Pauli n) :
    omega (a • p) q = a * omega p q := by
  simp only [omega, X_smul, Z_smul, Pi.smul_apply, smul_eq_mul, mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The symplectic form is `ZMod 2`-linear in the second argument:
`ω(p, a · q) = a · ω(p, q)`. -/
theorem omega_smul_right (a : ZMod 2) (p q : Pauli n) :
    omega p (a • q) = a * omega p q := by
  simp only [omega, X_smul, Z_smul, Pi.smul_apply, smul_eq_mul, mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The symplectic form is alternating: `ω(p, p) = 0` for every `p`.
In characteristic 2 this is equivalent to symmetry. -/
theorem omega_self (p : Pauli n) : omega p p = 0 := by
  have h : (∑ i, p.X i * p.Z i) = (∑ i, p.Z i * p.X i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact mul_comm _ _
  change (∑ i, p.Z i * p.X i) + (∑ i, p.X i * p.Z i) = 0
  rw [h]
  exact CharTwo.add_self_eq_zero _

/-- In characteristic 2, the symplectic form is symmetric:
`ω(p, q) = ω(q, p)`. -/
theorem omega_comm (p q : Pauli n) : omega p q = omega q p := by
  have h1 : (∑ i, p.Z i * q.X i) = (∑ i, q.X i * p.Z i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact mul_comm _ _
  have h2 : (∑ i, p.X i * q.Z i) = (∑ i, q.Z i * p.X i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact mul_comm _ _
  change (∑ i, p.Z i * q.X i) + (∑ i, p.X i * q.Z i) =
         (∑ i, q.Z i * p.X i) + (∑ i, q.X i * p.Z i)
  rw [h1, h2, add_comm]

/-- `ω(0, q) = 0` for every `q`. -/
@[simp]
theorem omega_zero_left (q : Pauli n) : omega 0 q = 0 := by
  simp [omega]

/-- `ω(p, 0) = 0` for every `p`. -/
@[simp]
theorem omega_zero_right (p : Pauli n) : omega p 0 = 0 := by
  simp [omega]

/-- Helper: a dot product of `f` with `Pi.single i 1` picks out `f i`. -/
private lemma sum_mul_single (f : Fin n → ZMod 2) (i : Fin n) :
    (∑ j, f j * (Pi.single i 1 : Fin n → ZMod 2) j) = f i := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intros j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The symplectic form on `Pauli n` is non-degenerate: if `ω(p, q) = 0` for
every `q`, then `p = 0`. -/
theorem omega_nondegenerate (p : Pauli n)
    (hp : ∀ q : Pauli n, omega p q = 0) : p = 0 := by
  ext i
  · have h := hp ⟨0, (Pi.single i 1 : Fin n → ZMod 2)⟩
    simp only [omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_add] at h
    rw [sum_mul_single p.X i] at h
    exact h
  · have h := hp ⟨(Pi.single i 1 : Fin n → ZMod 2), 0⟩
    simp only [omega, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero] at h
    rw [sum_mul_single p.Z i] at h
    exact h

/-- The symplectic form `ω` packaged as a `LinearMap.BilinForm`. Same
underlying data as `omega`; this version is the one to feed into Mathlib's
bilinear-form machinery (orthogonal complements, finite-dim non-degeneracy
results, etc.). -/
def omegaBilin : FTQCLib.Pauli n →ₗ[ZMod 2] FTQCLib.Pauli n →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) omega
    omega_add_left
    omega_smul_left
    omega_add_right
    omega_smul_right

@[simp]
theorem omegaBilin_apply (p q : FTQCLib.Pauli n) : omegaBilin p q = omega p q := rfl

/-- `omegaBilin` is non-degenerate (both left- and right-separating).
For symmetric forms the two directions coincide; the proof of the right-side
separation uses `omega_comm`. -/
theorem omegaBilin_nondegenerate :
    LinearMap.BilinForm.Nondegenerate (omegaBilin (n := n)) :=
  ⟨fun x hx => omega_nondegenerate x (fun y => by simpa using hx y),
   fun y hy => omega_nondegenerate y (fun x => by
     rw [omega_comm]
     simpa using hy x)⟩

/-- `omegaBilin` is reflexive: `ω(x, y) = 0 → ω(y, x) = 0`. Trivial from
`omega_comm`. -/
theorem omegaBilin_isRefl : LinearMap.BilinForm.IsRefl (omegaBilin (n := n)) :=
  fun x y h => by
    rw [omegaBilin_apply] at h ⊢
    rw [omega_comm]
    exact h

end FTQCLib.Pauli

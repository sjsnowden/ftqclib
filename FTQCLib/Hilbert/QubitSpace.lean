/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Complex.Basic

set_option linter.unusedSectionVars false

/-! # The qubit Hilbert space and computational basis

For chapter 3's equivalence work, we need the actual Hilbert space
`(ℂ²)^⊗n` paired with the F_2-symplectic representation of Paulis on
`Pauli n` from chapter 1. This file sets up the qubit space and its
computational basis.

We use the function-space presentation: `QubitSpace n` is the type of
functions `(Fin n → ZMod 2) → ℂ`. A standard basis vector
`computational v` for `v : Fin n → ZMod 2` is the indicator function
of `{v}`. The Hilbert space structure (inner product, norm) is the
standard `ℓ²` structure on a finite-dim function space; Mathlib's
`Pi` instances give us module/algebra structure automatically.

Reasoning here is at the level of finite-dim complex vector spaces.
For the chapter 3 equivalence work we don't need unitarity arguments
or normalisation — we work with the codespace as a vector subspace
and gate actions as linear maps. Inner product / unitarity machinery
can be added later for chapters that need them.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli

/-- The `n`-qubit Hilbert space: complex-valued functions on binary
labels. Each function `ψ : (Fin n → ZMod 2) → ℂ` represents the
quantum state `∑_v ψ(v) |v⟩` in computational-basis notation.

We use the function space `(Fin n → ZMod 2) → ℂ` rather than
`Fin (2^n) → ℂ` so that computational-basis indices match the F_2
representation of Paulis from chapter 1 directly. -/
abbrev QubitSpace (n : ℕ) : Type := (Fin n → ZMod 2) → ℂ

variable {n : ℕ}

/-- The computational basis vector `|v⟩` for a binary label
`v : Fin n → ZMod 2`. As a function, it is `1` at `v` and `0`
elsewhere — the indicator function of the singleton `{v}`. -/
noncomputable def computational (v : Fin n → ZMod 2) : QubitSpace n :=
  fun w => if w = v then 1 else 0

@[simp] theorem computational_self (v : Fin n → ZMod 2) :
    computational v v = 1 := by
  unfold computational
  simp

theorem computational_of_ne {v w : Fin n → ZMod 2} (h : w ≠ v) :
    computational v w = 0 := by
  unfold computational
  simp [h]

end FTQCLib.Hilbert

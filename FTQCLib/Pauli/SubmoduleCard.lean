/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

set_option linter.unusedSectionVars false

/-! # Finiteness and cardinality of `Pauli n` submodule subtypes

`Pauli n` is module-finite over the finite ring `ZMod 2`, hence finite
(`Module.finite_of_finite`), so every submodule subtype `↥L` is finite;
`Fintype.ofFinite` then upgrades this to a (noncomputable) `Fintype`. We also
record that a rank-`n` subspace has `2 ^ n` elements.

Downstream character-orthogonality steps (`FTQCLib/Hilbert/LemSpan.lean`) sum
over `AddChar ↥L ℂ`, which needs a `Fintype ↥L` instance; these three
declarations rest only on `Pauli n` itself, so they moved here out of the
Hilbert layer.
-/

namespace FTQCLib.Hilbert

open Module

variable {n : ℕ}

/-- `Pauli n` is a finite type. It is module-finite over the finite ring `ZMod 2`
(`Module.Finite (ZMod 2) (Pauli n)`), so `Module.finite_of_finite` yields finiteness.
Supplies the `Finite ↥L` needed by `fintypeSubmodule` via `Subtype.finite`. -/
instance finitePauli : Finite (FTQCLib.Pauli n) := Module.finite_of_finite (ZMod 2)

/-- A `Fintype` instance for submodule subtypes of `Pauli n`. Since `Pauli n` is a
finite type (`finitePauli`), every submodule subtype `↥L` is finite, and
`Fintype.ofFinite` upgrades this to a (noncomputable) `Fintype`. Needed because
summing over `AddChar ↥L ℂ` requires `Fintype ↥L`, which typeclass search does not
otherwise provide (only `Finite ↥L` is automatic). -/
noncomputable instance fintypeSubmodule
    (L : Submodule (ZMod 2) (FTQCLib.Pauli n)) : Fintype ↥L :=
  Fintype.ofFinite _

/-- A rank-`n` subspace of `Pauli n` has `2 ^ n` elements. Over the field
`ZMod 2`, `Module.card_eq_pow_finrank` gives `Fintype.card ↥L = 2 ^ finrank ↥L`
(using `ZMod.card 2 : Fintype.card (ZMod 2) = 2`); rewriting by the rank
hypothesis `h` yields `2 ^ n`. -/
theorem card_submodule_eq_pow_finrank {L : Submodule (ZMod 2) (FTQCLib.Pauli n)}
    (h : Module.finrank (ZMod 2) L = n) : Fintype.card ↥L = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, h]

end FTQCLib.Hilbert

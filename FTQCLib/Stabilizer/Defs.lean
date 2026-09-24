/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Symplectic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option linter.unusedSectionVars false

/-! # Stabilizer subgroups as isotropic subspaces

In the modulo-phase Pauli group `FTQCLib.Pauli n = (ZMod 2)^{2n}`, a stabilizer
subgroup corresponds to a `ZMod 2`-subspace `S` of `Pauli n` on which the
symplectic form `omega` vanishes identically: every pair of elements in `S`
commute (as Pauli operators). Such a subspace is called \emph{isotropic}.

The translation between full Pauli-group stabilizers and isotropic
subspaces:

* A stabilizer subgroup of the full Pauli group is abelian (commuting set).
  In the modulo-phase quotient, "abelian" becomes "isotropic under omega."
* The "no -I" condition (a true stabilizer subgroup does not contain `-I`)
  is automatic in the modulo-phase picture, since `-I` is identified with `I`
  in the quotient. The condition does have a phase-level meaning that we
  do not need here: every isotropic subspace of `Pauli n` lifts to a
  consistent phase choice (a stabilizer code in the strict sense exists).

This file defines:

* `IsStabilizer` — an ω-isotropic subspace.

The stabilizer rank is `Module.finrank (ZMod 2) S` from Mathlib; the
logical-qubit count lives in `FTQCLib.Stabilizer.Codespace`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-- A submodule `S` of `Pauli n` is a \emph{stabilizer subspace} iff every
pair of elements in `S` has `omega = 0`, i.e., the represented Paulis all
mutually commute. -/
def IsStabilizer (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, omega p q = 0

end FTQCLib.Stabilizer

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Defs

set_option linter.unusedSectionVars false

/-! # Logical qubit count

The number of logical qubits of a stabilizer code with stabilizer subspace
`S ⊂ Pauli n` is

    k = n - r,

where `r = dim_{ZMod 2}(S)` is the stabilizer rank.

Two notes on what this file does and doesn't do:

* The classical justification for the formula is that the codespace (the
  joint `+1` eigenspace of all stabilizer operators acting on the `2^n`-dim
  Hilbert space) has dimension `2^{n - r}`. That Hilbert-space statement
  is not formalized here; downstream algebraic reasoning about logical
  operators only requires the count `k = n - r`.

* The bound `r ≤ n` (which guarantees `k ≥ 0`) follows from `S` being
  ω-isotropic in a non-degenerate symplectic space of dimension `2n`; it
  is proved in `FTQCLib.Stabilizer.Dimension` (`finrank_le_of_isStabilizer`).
  `logicalCount` uses natural-number subtraction, which gives `0` if
  `r > n`.

This file defines:

* `logicalCount` — the number of logical qubits as `n - rank(S)`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-- The number of logical qubits of a stabilizer code with stabilizer
subspace `S`. Equals `n - dim_{ZMod 2}(S)` when `S` is isotropic; for
non-isotropic subspaces this is still defined formally but is not a code
parameter. -/
noncomputable def logicalCount (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) : ℕ :=
  n - Module.finrank (ZMod 2) S

end FTQCLib.Stabilizer

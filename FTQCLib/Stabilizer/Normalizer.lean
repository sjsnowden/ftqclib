/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Defs

set_option linter.unusedSectionVars false

/-! # Normalizer of a stabilizer subspace

The \emph{normalizer} of a stabilizer subspace `S ⊆ Pauli n` is the
ω-orthogonal complement:

    N(S) = { p ∈ Pauli n | ∀ q ∈ S, ω(p, q) = 0 }.

For abelian (i.e., ω-isotropic) `S`, this equals the centralizer of `S` in
`Pauli n` — every Pauli that commutes with all stabilizer generators. We
have `S ⊆ N(S)` (`S` is isotropic, so its elements all commute with each
other).

The quotient `N(S) / S` is the \emph{logical Pauli group}, isomorphic to
`Pauli k` where `k = n - rank(S)`. The isomorphism depends on a choice of
symplectic basis (`FTQCLib.Stabilizer.Logical`); two basis choices differ by a
symplectic transformation of `Pauli k`, which is the algebraic core of F9
in the SIMD-C plan (logical-qubit relabel and virtual SWAP).

This file proves:

* **N1** `normalizer` — definition of `N(S)` as a submodule of `Pauli n`.

`N2` (centralizer = normalizer for isotropic `S`) and `N3`–`N5` (quotient
structure and basis choice) live in `FTQCLib.Stabilizer.Logical`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-- The normalizer `N(S)` of a stabilizer subspace `S ⊆ Pauli n`:
the `ZMod 2`-submodule of `Pauli n` consisting of all elements that
ω-commute with every element of `S`. -/
def normalizer (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) :
    Submodule (ZMod 2) (FTQCLib.Pauli n) where
  carrier := { p | ∀ q ∈ S, omega p q = 0 }
  zero_mem' := fun q _ => omega_zero_left q
  add_mem' := fun {p₁ p₂} hp₁ hp₂ q hq => by
    rw [omega_add_left, hp₁ q hq, hp₂ q hq, add_zero]
  smul_mem' := fun a p hp q hq => by
    rw [omega_smul_left, hp q hq, mul_zero]

end FTQCLib.Stabilizer

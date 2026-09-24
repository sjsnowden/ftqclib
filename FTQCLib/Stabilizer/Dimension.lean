/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Codespace
import FTQCLib.Stabilizer.Logical
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity

set_option linter.unusedSectionVars false

/-! # Dimensions of `Pauli n`, the normalizer, and the logical quotient

This file establishes the dimension count that justifies the
"`k` logical qubits" formula for a stabilizer code:

* `finrank (Pauli n) = 2n`.
* `finrank (N(S)) = 2n − dim S`.
* `finrank (N(S)/S) = 2n − 2 · dim S = 2k` (when `S` is isotropic, so
  `dim S ≤ n`).

The proof of the last identity reduces, by Mathlib's
`Submodule.finrank_quotient_add_finrank`, to the assertion
`finrank (S.comap N(S).subtype) = finrank S`. For a stabilizer
(isotropic) subspace `S ⊆ N(S)`, the comap is linearly isomorphic to
`S` itself via `Submodule.comapSubtypeEquivOfLe`. The middle identity is
`LinearMap.BilinForm.finrank_orthogonal` applied to the non-degenerate
`omegaBilin`, combined with `normalizer_eq_orthogonal`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli Module

variable {n : ℕ}

/-- The Pauli space `Pauli n` has `(ZMod 2)`-dimension `2n`. -/
theorem finrank_Pauli : finrank (ZMod 2) (Pauli n) = 2 * n := by
  rw [linearEquivProd.finrank_eq, Module.finrank_prod,
    Module.finrank_pi, Fintype.card_fin, two_mul]

/-- The normalizer of `S ⊆ Pauli n` has dimension `2n − dim S`. -/
theorem finrank_normalizer (S : Submodule (ZMod 2) (Pauli n)) :
    finrank (ZMod 2) (normalizer S) = 2 * n - finrank (ZMod 2) S := by
  rw [normalizer_eq_orthogonal,
    LinearMap.BilinForm.finrank_orthogonal omegaBilin_nondegenerate,
    finrank_Pauli]

/-- For an isotropic subspace `S ⊆ Pauli n` (so `S ⊆ N(S)`), the comap of
`S` along the inclusion `N(S) → Pauli n` has the same dimension as `S`. -/
theorem finrank_comap_subtype_normalizer
    {S : Submodule (ZMod 2) (Pauli n)} (h : IsStabilizer S) :
    finrank (ZMod 2) (S.comap (normalizer S).subtype) = finrank (ZMod 2) S :=
  (Submodule.comapSubtypeEquivOfLe (subset_normalizer h)).finrank_eq

/-- The logical Pauli group `N(S)/S` has dimension `2n − 2 · dim S`.
When `S` is a stabilizer subspace, this equals `2k`, the standard
"twice the logical-qubit count" formula. -/
theorem finrank_logicalQuotient {S : Submodule (ZMod 2) (Pauli n)}
    (h : IsStabilizer S) :
    finrank (ZMod 2) (logicalQuotient S) =
      2 * n - 2 * finrank (ZMod 2) S := by
  have hSum :
      finrank (ZMod 2) (logicalQuotient S) +
        finrank (ZMod 2) (S.comap (normalizer S).subtype) =
      finrank (ZMod 2) (normalizer S) :=
    Submodule.finrank_quotient_add_finrank _
  rw [finrank_comap_subtype_normalizer h, finrank_normalizer] at hSum
  omega

/-- A stabilizer (isotropic) subspace of `Pauli n` has dimension at most
`n`. The bound follows from `S ⊆ N(S)` and the dimension formula
`finrank N(S) = 2n − finrank S`. -/
theorem finrank_le_of_isStabilizer {S : Submodule (ZMod 2) (Pauli n)}
    (h : IsStabilizer S) :
    finrank (ZMod 2) S ≤ n := by
  have h_le : finrank (ZMod 2) (S.comap (normalizer S).subtype) ≤
      finrank (ZMod 2) (normalizer S) := Submodule.finrank_le _
  rw [finrank_comap_subtype_normalizer h, finrank_normalizer] at h_le
  omega

/-- For a stabilizer subspace, the logical-quotient dimension is twice
the logical-qubit count: `finrank (N(S)/S) = 2 · logicalCount S`. -/
theorem finrank_logicalQuotient_eq_two_logicalCount
    {S : Submodule (ZMod 2) (Pauli n)} (h : IsStabilizer S) :
    finrank (ZMod 2) (logicalQuotient S) = 2 * logicalCount S := by
  have hle := finrank_le_of_isStabilizer h
  rw [finrank_logicalQuotient h, logicalCount]
  omega

end FTQCLib.Stabilizer

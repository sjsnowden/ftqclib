/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Wrapper
import FTQCLib.Gates.Hadamard

set_option linter.unusedSectionVars false

/-! # The Toffoli (CCNOT) gate as a level-3 hierarchy element

The Toffoli gate `CCNOT_{ijk}` flips qubit `k` if and only if both
qubits `i` and `j` are in state `|1⟩`. It is the prototypical
non-diagonal level-3 element of the Clifford hierarchy.

Unlike `CCZ_{ijk}` (a diagonal level-3 element), `CCNOT_{ijk}` does
not act diagonally on the computational basis. The standard
decomposition expresses it as the Hadamard-conjugate of CCZ:

  CCNOT_{ijk} = H_k · CCZ_{ijk} · H_k.

In our framework `CCNOT` is therefore a `ClifConjOfDiag`: its diagonal
piece is `cczPoly i j k` (over `ZMod 2`, level 3) and its pre/post
Cliffords are both `hadamardAt k`. Hierarchy-level membership follows
from `cczPoly_isDiagonalHierarchyLevel_three` and
`cliffordConjugate_isHierarchyLevel`.
-/

namespace FTQCLib.Gates

open FTQCLib.Hierarchy FTQCLib.Pauli

variable {n : ℕ}

/-- The Toffoli gate on three qubits `i, j, k`, factored as the
Hadamard-conjugate of CCZ:

  CCNOT_{ijk} = H_k · CCZ_{ijk} · H_k.

The diagonal piece is the CCZ phase polynomial `j_i · j_j · j_k`
over `ZMod 2` (level 3). The pre- and post-conjugating Cliffords are
both Hadamard on qubit `k`. -/
noncomputable def ccnotGate (i j k : Fin n) : ClifConjOfDiag n :=
  { diagPrecision := 1
    diagPoly := DiagPhase.cczPoly i j k
    pre := hadamardAt k
    pre_isClifford := hadamardAt_isClifford k
    post := hadamardAt k
    post_isClifford := hadamardAt_isClifford k }

/-- The Toffoli gate sits at level 3 of the Clifford hierarchy. -/
theorem ccnotGate_isHierarchyLevel_three (i j k : Fin n) :
    ClifConjOfDiag.IsHierarchyLevel 3 (ccnotGate i j k) := by
  unfold ccnotGate ClifConjOfDiag.IsHierarchyLevel
  exact DiagPhase.cczPoly_isDiagonalHierarchyLevel_three i j k

end FTQCLib.Gates

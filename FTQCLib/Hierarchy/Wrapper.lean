/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.HierarchyLevel
import FTQCLib.Gates.Clifford

set_option linter.unusedSectionVars false

/-! # Clifford-conjugates of diagonal hierarchy elements

The diagonal subgroup `C_d^(k)` of the Clifford hierarchy is
parametrised by `DiagPhase n m` with `P.level ≤ k` (Cui–Gottesman–Krishna
Theorem 3, captured in `IsDiagonalHierarchyLevel`). The full level-$k$
of the hierarchy contains non-diagonal elements as well, obtained by
conjugating diagonal elements by Cliffords. The Toffoli gate
`CCNOT = H_k · CCZ_{ijk} · H_k` is the prototypical example.

This file introduces a structured wrapper `ClifConjOfDiag n` for
"Clifford-conjugate of a diagonal hierarchy element". A value of this
type is a triple `(pre, diagPoly, post)` representing the abstract
unitary `post · U_{diagPoly} · pre` (composition order matches the
library's Clifford convention, where Cliffords act as
`Pauli n ≃ₗ[ZMod 2] Pauli n` automorphisms).

The level of a `ClifConjOfDiag` is the level of its diagonal piece;
Clifford conjugation does not change the hierarchy level
(`clifford_conj_preserves_level`, the polynomial-framework analogue
of the standard Clifford-hierarchy stability lemma).

`ClifConjOfDiag` is intentionally bare: we treat it as a "tag" type
that records the algebraic data necessary to identify a hierarchy
element, without claiming it forms a group or that every level-$k$
element factors this way. For the gates T, CCZ and CCNOT this
representation is sufficient.
-/

namespace FTQCLib.Hierarchy

open FTQCLib.Pauli FTQCLib.Gates

/-- Algebraic data for a "Clifford-conjugate of a diagonal hierarchy
element": a precision `m`, a phase polynomial `diagPoly : DiagPhase n m`,
and two Clifford automorphisms `pre, post` of `Pauli n`. The abstract
operator represented is `post ∘ U_{diagPoly} ∘ pre`.

The level of the underlying hierarchy element is the level of the
diagonal piece (Clifford conjugation preserves level). -/
structure ClifConjOfDiag (n : ℕ) where
  /-- The precision of the diagonal phase polynomial. -/
  diagPrecision : ℕ
  /-- The diagonal phase polynomial. -/
  diagPoly : DiagPhase n diagPrecision
  /-- The pre-conjugating Clifford. -/
  pre : Pauli n ≃ₗ[ZMod 2] Pauli n
  /-- Proof that `pre` is Clifford. -/
  pre_isClifford : IsClifford pre
  /-- The post-conjugating Clifford. -/
  post : Pauli n ≃ₗ[ZMod 2] Pauli n
  /-- Proof that `post` is Clifford. -/
  post_isClifford : IsClifford post

namespace ClifConjOfDiag

variable {n : ℕ}

/-- The level of a `ClifConjOfDiag`: the level of its diagonal piece.
By the Clifford-conjugation stability lemma, this matches the
Clifford-hierarchy level of the underlying unitary. -/
noncomputable def level (h : ClifConjOfDiag n) : ℕ :=
  h.diagPoly.level

/-- The hierarchy-level predicate for `ClifConjOfDiag`. -/
def IsHierarchyLevel (k : ℕ) (h : ClifConjOfDiag n) : Prop :=
  DiagPhase.IsDiagonalHierarchyLevel k h.diagPoly

/-- Embed a pure diagonal element as a `ClifConjOfDiag` with trivial
pre- and post-Cliffords (the identity). -/
noncomputable def ofDiag {m : ℕ} (P : DiagPhase n m) : ClifConjOfDiag n :=
  { diagPrecision := m
    diagPoly := P
    pre := LinearEquiv.refl (ZMod 2) (Pauli n)
    pre_isClifford := isClifford_refl
    post := LinearEquiv.refl (ZMod 2) (Pauli n)
    post_isClifford := isClifford_refl }

/-- The level of a pure diagonal embedding equals the level of the
underlying phase polynomial. -/
@[simp]
theorem ofDiag_level {m : ℕ} (P : DiagPhase n m) :
    (ofDiag P).level = P.level := rfl

/-- Conjugating a `ClifConjOfDiag` by a Clifford `U` (on both sides)
yields another `ClifConjOfDiag` with the same diagonal piece — only
the pre- and post-Cliffords change. -/
noncomputable def cliffordConjugate (U : Pauli n ≃ₗ[ZMod 2] Pauli n)
    (hU : IsClifford U) (h : ClifConjOfDiag n) : ClifConjOfDiag n :=
  { diagPrecision := h.diagPrecision
    diagPoly := h.diagPoly
    pre := h.pre.trans U
    pre_isClifford := h.pre_isClifford.trans hU
    post := U.symm.trans h.post
    post_isClifford := by
      -- `U.symm` is Clifford because `IsClifford` is closed under inverse
      -- (the symplectic group is a group).
      have hUsymm : IsClifford U.symm := by
        intro p q
        have := hU (U.symm p) (U.symm q)
        simp at this
        exact this.symm
      exact hUsymm.trans h.post_isClifford }

/-- **Clifford conjugation preserves hierarchy level.** Conjugating a
`ClifConjOfDiag` element by any Clifford does not change its
hierarchy level. The proof is structural: `cliffordConjugate` rewires
the `pre` and `post` Cliffords but leaves the `diagPoly` unchanged,
so the `level` (computed from `diagPoly`) is unchanged. This is the
polynomial-framework image of the Clifford-hierarchy stability lemma
`V ∈ C_k, U ∈ C_2 ⇒ UVU† ∈ C_k`. -/
theorem cliffordConjugate_level {U : Pauli n ≃ₗ[ZMod 2] Pauli n}
    (hU : IsClifford U) (h : ClifConjOfDiag n) :
    (cliffordConjugate U hU h).level = h.level := rfl

/-- Clifford conjugation preserves `IsHierarchyLevel`. -/
theorem cliffordConjugate_isHierarchyLevel {k : ℕ}
    {U : Pauli n ≃ₗ[ZMod 2] Pauli n} (hU : IsClifford U)
    {h : ClifConjOfDiag n} (hh : IsHierarchyLevel k h) :
    IsHierarchyLevel k (cliffordConjugate U hU h) := hh

end ClifConjOfDiag

end FTQCLib.Hierarchy

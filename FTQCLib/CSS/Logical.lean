/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Defs

set_option linter.unusedSectionVars false

/-! # Logical operators for CSS codes

For a CSS code given by parity-check matrices `(H_X, H_Z)`, the logical
Pauli space splits as

    L(S_CSS) ≅ L_X ⊕ L_Z,

where

    L_X = ker(H_Z) / im(H_Xᵀ)   (X-logical operators, mod stabilizer)
    L_Z = ker(H_X) / im(H_Zᵀ)   (Z-logical operators, mod stabilizer).

The X-logical space is the quotient of the "Z-syndrome-trivial" X-strings
(those commuting with every Z-stabilizer) by the X-stabilizer image.
Concretely, a binary vector `v ∈ (ZMod 2)^n` represents a logical X
operator iff `H_Z v = 0` (commutation with all Z-stabilizers), and two
such vectors represent the same logical operator iff they differ by a
row-combination of `H_X` (a product of X-stabilizers).

This file defines:

* **X-logical** `cssXLogicalCarrier`, `cssXLogicalSubspace`
  — the kernel `ker(H_Z) ⊂ (ZMod 2)^n` and the image-span
  `im(H_Xᵀ) ⊂ ker(H_Z)`, plus the quotient `L_X`.
* **Z-logical** `cssZLogicalCarrier`, `cssZLogicalSubspace`,
  `cssZLogical` — symmetric definitions for `Z`-logical operators.

The dimension result `dim L_X = dim L_Z = k` is `finrank_cssXLogical` /
`finrank_cssZLogical` in `FTQCLib/CSS/Rank.lean`. This file does not
treat the identification `L_X ⊕ L_Z ≅ L(S_CSS)`; it reduces to the
direct-sum structure inherited from the X/Z block decomposition of
`Pauli n`.
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli Matrix

variable {n r_X r_Z : ℕ}

/-- The kernel of `H_Z` viewed as a linear map `(ZMod 2)^n → (ZMod 2)^r_Z`
(multiplying on the right): the X-supports that commute with every
Z-stabilizer. -/
def cssXLogicalCarrier (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (Matrix.mulVecLin H_Z)

/-- The image of `H_Xᵀ` in `(ZMod 2)^n`: the X-supports of products of
X-stabilizers. -/
def cssXLogicalSubspace (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin H_Xᵀ)

/-- Under the CSS commutativity condition `H_X · H_Zᵀ = 0`, the image of
`H_Xᵀ` is contained in the kernel of `H_Z`: every X-stabilizer commutes
with every Z-stabilizer. -/
theorem cssXLogicalSubspace_le_cssXLogicalCarrier
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} (h : IsCSSPair H_X H_Z) :
    cssXLogicalSubspace H_X ≤ cssXLogicalCarrier H_Z := by
  rintro v ⟨u, rfl⟩
  change H_Z *ᵥ (H_Xᵀ *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec]
  rw [show H_Z * H_Xᵀ = 0 from by
        have := congrArg Matrix.transpose h
        rwa [Matrix.transpose_zero, Matrix.transpose_mul,
          Matrix.transpose_transpose] at this]
  simp

/-- **X-logical space.** The X-logical Pauli space: the quotient
`ker(H_Z) / im(H_Xᵀ)` as an `(ZMod 2)`-vector space. -/
abbrev cssXLogical
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) : Type :=
  (cssXLogicalCarrier H_Z) ⧸
    (cssXLogicalSubspace H_X).comap (cssXLogicalCarrier H_Z).subtype

/-- The kernel of `H_X`: the Z-supports that commute with every
X-stabilizer. -/
def cssZLogicalCarrier (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (Matrix.mulVecLin H_X)

/-- The image of `H_Zᵀ` in `(ZMod 2)^n`: the Z-supports of products of
Z-stabilizers. -/
def cssZLogicalSubspace (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin H_Zᵀ)

/-- Under the CSS commutativity condition, the image of `H_Zᵀ` is
contained in the kernel of `H_X`. -/
theorem cssZLogicalSubspace_le_cssZLogicalCarrier
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} (h : IsCSSPair H_X H_Z) :
    cssZLogicalSubspace H_Z ≤ cssZLogicalCarrier H_X := by
  rintro v ⟨u, rfl⟩
  change H_X *ᵥ (H_Zᵀ *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec, h]
  simp

/-- **Z-logical space.** The Z-logical Pauli space: the quotient
`ker(H_X) / im(H_Zᵀ)` as an `(ZMod 2)`-vector space. -/
abbrev cssZLogical
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) : Type :=
  (cssZLogicalCarrier H_X) ⧸
    (cssZLogicalSubspace H_Z).comap (cssZLogicalCarrier H_X).subtype

end FTQCLib.CSS

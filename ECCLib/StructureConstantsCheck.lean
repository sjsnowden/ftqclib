/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.StructureConstants
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Checks for `ECCLib/StructureConstants.lean`

Axiom sweeps, plus rows pinning the generality — which is the whole point of the module and the
reason it was worth separating from its original home.

The extraction is itself checkable: this file imports **only** the new module and Mathlib. If the
coordinate theory had a hidden dependency on circuit synthesis, this file would not compile.
-/

namespace ECCLib

open Module

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.strConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.strConst

/-- info: 'ECCLib.repr_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.repr_mul

/-- info: 'ECCLib.constMulMat' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.constMulMat

/-- info: 'ECCLib.repr_const_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.repr_const_mul

/-- info: 'ECCLib.mul_basis_eq_repr_smul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.mul_basis_eq_repr_smul

/-! ## Generality rows

The coordinate theorem is stated at `[CommRing R] [CommRing A] [Algebra R A]`. These rows
exercise it where a field-based or characteristic-zero statement could not go. -/

section Generic

variable {m : ℕ}

/-- Over `ZMod 4`, which is not a field, not an integral domain — it has nilpotents — and has
positive non-prime characteristic. Named rather than anonymous so the module owns a declaration:
the ontology extractor requires every module to emit at least one node. -/
theorem repr_mul_zmod4 {A : Type*} [CommRing A] [Algebra (ZMod 4) A]
    (B : Basis (Fin m) (ZMod 4) A) (x y : A) (k : Fin m) :
    B.repr (x * y) k = ∑ i, ∑ j, strConst B i j k * (B.repr x i * B.repr y j) :=
  repr_mul B x y k

/-- Over a polynomial ring: not a field, characteristic zero, and infinite — the opposite corner
from `ZMod 4`.

(A `ℤ` row is deliberately absent. It hits Mathlib's `ℤ`-module diamond —
`AddCommGroup.toIntModule` against `Algebra.toModule` — which is a fact about Mathlib's instance
graph and says nothing about this module's generality.) -/
example {A : Type*} [CommRing A] [Algebra (Polynomial ℚ) A]
    (B : Basis (Fin m) (Polynomial ℚ) A) (x y : A) (k : Fin m) :
    B.repr (x * y) k = ∑ i, ∑ j, strConst B i j k * (B.repr x i * B.repr y j) :=
  repr_mul B x y k

/-- The fixed-factor form over the same ring. -/
example {A : Type*} [CommRing A] [Algebra (ZMod 4) A]
    (B : Basis (Fin m) (ZMod 4) A) (a x : A) (k : Fin m) :
    B.repr (a * x) k = ∑ i, constMulMat B a k i * B.repr x i :=
  repr_const_mul B a x k

end Generic

/-! ## No finiteness of the algebra beyond the basis

The statements carry no `FiniteDimensional`, no `Module.Finite`, no `Fintype A`. A basis indexed
by `Fin m` is the only finiteness in sight, and it is what makes the sums well-formed rather than
an assumption about `A` itself. -/

example {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {m : ℕ}
    (B : Basis (Fin m) R A) (i j k : Fin m) :
    strConst B i j k = B.repr (B i * B j) k := rfl

end ECCLib

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Commutativity as a class on a subalgebra

`Subalgebra.IsCommutative`, and the `CommRing` instance it entails. Verified absent from
Mathlib v4.29.1, where the only occurrences of the name are a section heading.
`Subalgebra.toCommRing` does not apply in the intended use: it needs a commutative *ambient*
algebra, and a matrix algebra is not one.

## Main definitions

* `Subalgebra.IsCommutative` — commutativity as a class on a subalgebra.
* `Subalgebra.instCommRingOfIsCommutative` — the `CommRing` structure it entails.

## Implementation notes

**Originally declared in `ECCLib/Scheme/SelfPaired.lean`.** The class mentions no orbit, no
matrix and no scheme, but consuming it from `SelfPaired.lean` meant importing the orbital
layer. A second consumer (`ECCLib/Matrix/SpectralDetermination.lean`, which must not import
`Scheme/`) needs it, so the class lives in the lowest layer that can state it.

The namespace stays `ECCLib.Scheme`, where the class was first declared, so the move
changed no consumer — the same precedent `Matrix/PermCommutant.lean` set and
`StructureConstants.lean` followed.
-/

namespace ECCLib.Scheme

/-- Commutativity carried as a class on a subalgebra, so that the `CommRing` it entails is a
genuine instance rather than a `letI` at each use site. `Subalgebra.toCommRing` does not apply
here: it needs a commutative *ambient* algebra, and a matrix algebra is not one. -/
class Subalgebra.IsCommutative {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R A) : Prop where
  mul_comm' : ∀ a b : S, a * b = b * a

instance Subalgebra.instCommRingOfIsCommutative {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (S : Subalgebra R A) [Subalgebra.IsCommutative S] : CommRing S :=
  { (inferInstance : Ring S) with mul_comm := Subalgebra.IsCommutative.mul_comm' }

end ECCLib.Scheme

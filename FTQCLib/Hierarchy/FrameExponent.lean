/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BoolReduce
import FTQCLib.Hierarchy.EffectiveLevel

/-! # Kernel frame — exponents and the level

The frame's **exponent at precision `m`** is `DiagPhase n m` itself: the
syntax is the verified `MvPolynomial (Fin n) (ZMod (2^m))`, the reading `e^` is
`DiagPhase.realPhase`, and the precision identification is `liftTo` with its five
exact transport lemmas. By design the dyadic value group
`ℤ[1/2]/ℤ` stays *implicit* behind this per-precision substrate — no colimit
object is built; precision is a property.

This file fixes the frame's **level**.
-/

namespace FTQCLib.Frame

open FTQCLib.Hierarchy

variable {n : ℕ}

/-- The frame's **level** (per-precision representation):
`ℓ := effectiveLevel`, the max over the support of the per-monomial
`(o(c) − 1) + |S|` (equivalently `(m − 1 − v₂(c)) + |S|`). On the constant-free
multilinear normal forms the frame works with, this is exact. -/
noncomputable abbrev level {m : ℕ} (P : DiagPhase n m) : ℕ := DiagPhase.effectiveLevel P

/-- The frame's level **extended to arbitrary exponents** by constant-stripping
and multilinear reduction: `ℓ(f) := ℓ(nf(f − f(0)))`, where `f − f(0)` removes the
constant term (`P − C(P.coeff 0)`) and `boolReduce` is the multilinear normalizer.
Agrees with `level` on constant-free multilinear representatives (where the strip
and the reduction are identities). -/
noncomputable def levelExt {m : ℕ} (P : DiagPhase n m) : ℕ :=
  DiagPhase.effectiveLevel (DiagPhase.boolReduce (P - MvPolynomial.C (P.coeff 0)))

end FTQCLib.Frame

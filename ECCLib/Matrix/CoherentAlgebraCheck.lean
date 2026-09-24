/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.CoherentAlgebra

/-!
# Checks for `ECCLib/Matrix/CoherentAlgebra.lean`

Axiom sweeps, plus rows that pin the parts of the statement most easily got wrong: that the
theorem needs no hypothesis on the generating set, that it is ring-generic, and that the
all-ones matrix is not the identity matrix.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.hadamard_mem_permCommutant' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.hadamard_mem_permCommutant

/-- info: 'ECCLib.Scheme.of_one_mem_permCommutant' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.of_one_mem_permCommutant

/-- info: 'ECCLib.Scheme.isCoherentAlgebra_permCommutant' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCoherentAlgebra_permCommutant

/-- info: 'ECCLib.Scheme.IsCoherentAlgebra' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.IsCoherentAlgebra

/-- info: 'ECCLib.Scheme.IsCoherentAlgebra.one_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.IsCoherentAlgebra.one_mem

/-- info: 'ECCLib.Scheme.of_one_apply' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.of_one_apply

/-- info: 'ECCLib.Scheme.hadamard_of_one_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.hadamard_of_one_self

/-! ## `J` is not `1`, and the distinction is load-bearing

The two coherent-algebra axioms name *two different matrices*. A reader who reads `of 1` as the
identity gets a statement that is true for the wrong reason, so the difference is compiled. -/

/-- The identity and the all-ones matrix differ as soon as there are two indices to tell apart. -/
theorem of_one_ne_one_bool : (Matrix.of 1 : Matrix Bool Bool ℤ) ≠ 1 := by
  intro h
  have := congrFun (congrFun h false) true
  simp at this

/-! ## The theorem takes no hypothesis on the generating set

`isCoherentAlgebra_permCommutant` quantifies over an arbitrary `Set (Equiv.Perm X)`. These rows
exercise the cases a group-shaped statement could not reach. -/

section NoHypothesis

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The empty set of permutations: the commutant is everything, and is still coherent. -/
example : IsCoherentAlgebra (permCommutant ℤ (∅ : Set (Equiv.Perm X))) :=
  isCoherentAlgebra_permCommutant _

/-- A single permutation, which generates a group only incidentally. -/
example (σ : Equiv.Perm X) : IsCoherentAlgebra (permCommutant ℤ ({σ} : Set (Equiv.Perm X))) :=
  isCoherentAlgebra_permCommutant _

end NoHypothesis

/-! ## Ring-genericity, at the two rings that matter

Schur closure is stated at `[CommSemiring R]` — weaker than the `[CommRing R]` the orbital basis
needs, and weaker than the `ℂ` the spectral tier needs. These rows exercise it where neither is
available. Named rather than anonymous so the module owns a declaration: the ontology extractor
requires every module to emit at least one node. -/

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Over `ZMod 2`, where the qLDPC-facing consumer lives. -/
theorem hadamard_mem_permCommutant_zmod2 {S : Set (Equiv.Perm X)} {M N : Matrix X X (ZMod 2)}
    (hM : M ∈ permCommutant (ZMod 2) S) (hN : N ∈ permCommutant (ZMod 2) S) :
    M ⊙ N ∈ permCommutant (ZMod 2) S :=
  hadamard_mem_permCommutant hM hN

/-- Over `ℕ`, a semiring with no negation at all — which pins that `CommSemiring` is the real
hypothesis and not shorthand for something stronger. -/
example {S : Set (Equiv.Perm X)} {M N : Matrix X X ℕ}
    (hM : M ∈ permCommutant ℕ S) (hN : N ∈ permCommutant ℕ S) :
    M ⊙ N ∈ permCommutant ℕ S :=
  hadamard_mem_permCommutant hM hN

/-- The whole package over `ℕ`. -/
example (S : Set (Equiv.Perm X)) : IsCoherentAlgebra (permCommutant ℕ S) :=
  isCoherentAlgebra_permCommutant _

end Generic

/-! ## The `⋆` axiom is available but deliberately not a field

Godsil §1.3 includes conjugation-closure; §16.10 does not, and this file follows §16.10 so the
statement stays ring-generic. The stronger closure is still there for anyone who wants it, and
composes with the coherent package rather than replacing it. -/

example {X : Type*} [Fintype X] [DecidableEq X] {S : Set (Equiv.Perm X)}
    {M : Matrix X X ℂ} (hM : M ∈ permCommutant ℂ S) :
    Mᴴ ∈ permCommutant ℂ S ∧ IsCoherentAlgebra (permCommutant ℂ S) :=
  ⟨conjTranspose_mem_permCommutant hM, isCoherentAlgebra_permCommutant _⟩

end ECCLib.Scheme

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Orbital

/-!
# Checks for the orbital algebra

Axiom sweeps, a discriminating row, an agreement row, and kernel rows for
`ECCLib/Scheme/Orbital.lean`.

The discriminating row is the one that justifies a design choice. The orbital layer is stated
over an arbitrary `CommRing` rather than over `ℂ`, and the row that shows this is not idle
generality is the **left regular action of a group on itself over `ZMod 2`**: a group acting on
itself by left multiplication is a permutation action, so `finrank_orbitalAlgebra` says the
commutant of the left regular representation has dimension exactly `|G|`. That *reduces* the
classical identification — that the **right** regular representation is the whole commutant — to
two elementary steps not taken here: the containment `span {R[g]} ⊆ commutant`, and the linear
independence of the `R[g]`. The dimension is what this layer supplies; the identification is one
short step beyond it. That is the shape a binary group-algebra layer needs, and a `ℂ`-only
statement could not express it at all.

## What is deliberately not here

The other natural agreement row — the orbital count at a translation carrier against
`finrank_schemeAlgebra` — is not stated here. The translation-scheme dimension theorem counts
`H`-orbits on `V`, while the general one counts orbitals on `V × V`; they agree only through the
difference map `(x, y) ↦ y - x`. That bridge, and the agreement row, are in
`Scheme/TranslationOrbital.lean` (`card_orbits_prod_eq_card_orbits`).
-/

namespace ECCLib.Scheme

open Matrix

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.mem_orbitalAlgebra_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_orbitalAlgebra_iff

/-- info: 'ECCLib.Scheme.mem_orbitalAlgebra_iff_orb' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_orbitalAlgebra_iff_orb

/-- info: 'ECCLib.Scheme.finrank_orbitalAlgebra' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.finrank_orbitalAlgebra

/-- info: 'ECCLib.Scheme.orbitalBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbitalBasis

/-- info: 'ECCLib.Scheme.conjTranspose_mem_permCommutant' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.conjTranspose_mem_permCommutant

/-- info: 'ECCLib.Scheme.mem_permCommutant_closure_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_permCommutant_closure_iff

/-! ## The discriminating row: the layer is ring-generic, and that is load-bearing

A group acting on itself by left multiplication. Over `ZMod 2` — a ring a `ℂ`-only statement
could not accept. -/

section Binary

/-- A small group, written multiplicatively so that it acts on itself by left multiplication. -/
abbrev G2 : Type := Multiplicative (ZMod 2)

/-- A slightly larger one. -/
abbrev G3 : Type := Multiplicative (ZMod 3)

/-- The orbital algebra exists over `ZMod 2`. This is the row that fails to typecheck against a
`ℂ`-only statement. -/
example : Subalgebra (ZMod 2) (Matrix G2 G2 (ZMod 2)) := orbitalAlgebra (ZMod 2) G2 G2

/-- Membership is entrywise invariance, over `ZMod 2`. -/
example (M : Matrix G2 G2 (ZMod 2)) :
    M ∈ orbitalAlgebra (ZMod 2) G2 G2 ↔ ∀ (g x y : G2), M (g • x) (g • y) = M x y :=
  mem_orbitalAlgebra_iff M

/-- ...and over `ZMod 3`, to show `2` is not special. -/
example (M : Matrix G3 G3 (ZMod 3)) :
    M ∈ orbitalAlgebra (ZMod 3) G3 G3 ↔ ∀ (g x y : G3), M (g • x) (g • y) = M x y :=
  mem_orbitalAlgebra_iff M

/-- Transpose-closure holds over `ZMod 2` with no hypothesis on the action. This is the
ring-generic half of the closure story, and it is the half a binary layer can use: **Mathlib
puts no `StarRing` instance on `ZMod n`**, so `conjTranspose_mem_permCommutant` is simply not
available here. That is not a defect — it is why the two closure lemmas are stated separately,
one at `CommSemiring` and one at `StarRing`, instead of being merged. -/
example {M : Matrix G2 G2 (ZMod 2)} (hM : M ∈ permCommutant (ZMod 2) (actPerms G2 G2)) :
    Mᵀ ∈ permCommutant (ZMod 2) (actPerms G2 G2) :=
  transpose_mem_permCommutant hM

/-- Conjugate-transpose closure, where a star does exist. -/
example {X : Type} [Fintype X] [DecidableEq X] {G : Type} [Group G] [MulAction G X]
    {M : Matrix X X ℂ} (hM : M ∈ permCommutant ℂ (actPerms G X)) :
    Mᴴ ∈ permCommutant ℂ (actPerms G X) :=
  conjTranspose_mem_permCommutant hM

end Binary

/-! ## Agreement rows: the dimension theorem against the kernel

`finrank_orbitalAlgebra` is proved abstractly. These rows compute the same number by kernel
reduction on `orbits`, at the left regular action, where the answer should be `|G|` — the
commutant of the left regular representation is the right regular representation. -/

/-- info: 2 -/
#guard_msgs in
#eval (orbits G2 (G2 × G2)).card

/-- info: 3 -/
#guard_msgs in
#eval (orbits G3 (G3 × G3)).card

/-- The kernel confirms the orbital count for the left regular action of a group of order 2. -/
theorem card_orbits_G2 : (orbits G2 (G2 × G2)).card = 2 := by decide

/-- The same at order 3. -/
theorem card_orbits_G3 : (orbits G3 (G3 × G3)).card = 3 := by decide

/-! ### A reduction wall

The natural composite row — `Module.finrank (ZMod 2) (orbitalAlgebra (ZMod 2) G2 G2) = 2`,
obtained as `finrank_orbitalAlgebra.trans card_orbits_G2` — **does not elaborate**. It times out
at `whnf` at the default 200,000 heartbeats and still times out at 1,000,000, so this is a
reduction wall rather than a tuning question. Unfolding `orbitalAlgebra` at a concrete carrier
means unfolding `permCommutant` into `Subalgebra.centralizer` over a concrete matrix type and
reducing the `Field`-to-`CommRing` instance path on `ZMod n`; the elaborator does not get
through it.

Two things this does NOT mean. It is not a gap in the mathematics: `finrank_orbitalAlgebra` is
proved for every field and swept above, and `card_orbits_G2`/`card_orbits_G3` are proved by the
kernel. The agreement between them is a composition of two facts each independently checked —
what fails is only forcing that composition through definitional unfolding at a concrete
carrier. And it is not a reason to reach for `decide` harder: the standalone kernel rows above
reduce in seconds, so the cost is in the instance path, not in the orbit computation. -/


/-- info: 'ECCLib.Scheme.orbitalAdj_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbitalAdj_apply

/-- info: 'ECCLib.Scheme.coe_orbitalBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.coe_orbitalBasis

/-- info: 'ECCLib.Scheme.val_orbitalBasis' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.val_orbitalBasis

end ECCLib.Scheme

/-- info: 'ECCLib.Scheme.trace_orbitalAdj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.trace_orbitalAdj

/-- info: 'ECCLib.Scheme.transposePairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transposePairs

/-- info: 'ECCLib.Scheme.mem_transposePairs' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_transposePairs

/-- info: 'ECCLib.Scheme.card_transposePairs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_transposePairs

/-- info: 'ECCLib.Scheme.transposePairs_transposePairs' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transposePairs_transposePairs

/-- info: 'ECCLib.Scheme.orb_swap' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orb_swap

/-- info: 'ECCLib.Scheme.transposePairs_mem_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transposePairs_mem_orbits

/-- info: 'ECCLib.Scheme.trace_orbitalAdj_mul_orbitalAdj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.trace_orbitalAdj_mul_orbitalAdj

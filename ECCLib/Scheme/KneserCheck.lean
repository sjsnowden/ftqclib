/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Kneser

/-!
# Checks for the Kneser spectrum

The Petersen graph is `K(5,2)`. Kernel rows recompute its eigenvalue row `3, −2, 1`
against the literal `eberlein`, its multiplicities `1, 4, 5` as the closed-form
differences, the zero-trace handshake `1·3 + 4·(−2) + 5·1 = 0`, and the edge count
`#(kneserSet 5 2) = 30`; a **control** kernelises the guard `2k ≤ n` — at `K(3,2)` the
disjointness relation is empty, and an empty set is no orbital. The independence number
rows are a supplement: an explicit `4`-star is pairwise-intersecting, and every
five-element vertex set contains a disjoint pair — `α(Petersen) = 4`, both halves by
`decide`. The noncomputable main theorem instantiates live at `K(5,2)`.
-/

namespace ECCLib.Scheme.Johnson

open Finset ECCLib.Delsarte

/-! ## The Petersen spectrum, kernel-checked -/

/-- The Petersen eigenvalue row is the top-degree Eberlein row at `J(5,2)`: `3, −2, 1`. -/
example : eberlein 5 2 2 0 = 3 ∧ eberlein 5 2 2 1 = -2 ∧ eberlein 5 2 2 2 = 1 := by
  decide

/-- The Petersen multiplicities are the Johnson closed forms at `n = 5`:
`m₀ = 1`, `m₁ = C(5,1) − C(5,0) = 4`, `m₂ = C(5,2) − C(5,1) = 5`. -/
example : ((5).choose 1 : ℤ) - (5).choose 0 = 4 ∧ ((5).choose 2 : ℤ) - (5).choose 1 = 5 := by
  decide

/-- The zero-trace handshake: the multiplicity-weighted eigenvalue row sums to the trace
of the adjacency matrix, which is `0`. -/
example : 1 * eberlein 5 2 2 0 + 4 * eberlein 5 2 2 1 + 5 * eberlein 5 2 2 2 = 0 := by
  decide

/-! ## The dictionary, kernel-checked -/

/-- A disjoint pair is a Kneser edge. -/
example : ((⟨{0, 1}, by decide⟩ : KSub 5 2), (⟨{2, 3}, by decide⟩ : KSub 5 2))
    ∈ kneserSet 5 2 := by decide

/-- A meeting pair is not. -/
example : ((⟨{0, 1}, by decide⟩ : KSub 5 2), (⟨{1, 2}, by decide⟩ : KSub 5 2))
    ∉ kneserSet 5 2 := by decide

/-- The Petersen edge count (ordered): `#(kneserSet 5 2) = 30 = C(5,2) · C(3,2)` — ten
vertices, valency three. -/
example : #(kneserSet 5 2) = 30 := by decide

/-- **Control — the guard `2k ≤ n` is load-bearing**: at `K(3,2)` two `2`-subsets of a
`3`-set always meet, the disjointness relation is empty, and an empty set is no orbital
(orbits are nonempty). -/
example : kneserSet 3 2 = ∅ := by decide

/-! ## The independence number: `α(Petersen) = 4`

Independent sets of the Kneser graph are pairwise-intersecting families. Both halves run
through the same decidable predicate, so each is the other's control: the instrument
answers `true` at `4` and `false` at `5`. The five-subsets are enumerated as length-`5`
sublists of an explicit vertex list — a completeness row certifies the list is the whole
carrier without repetition, so every five-element vertex set is one of them up to order.
(The `Finset.powersetCard` form of the same statement is a kernel wall: `Multiset`
quotient reduction did not finish; the list enumeration is immediate.) -/

/-- The star at `0` is an explicit pairwise-intersecting `4`-family. -/
example :
    ({⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩,
        ⟨{0, 4}, by decide⟩} : Finset (KSub 5 2)).card = 4 ∧
      ∀ x ∈ ({⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩,
          ⟨{0, 4}, by decide⟩} : Finset (KSub 5 2)),
        ∀ y ∈ ({⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩,
            ⟨{0, 4}, by decide⟩} : Finset (KSub 5 2)),
          (x.1 ∩ y.1).Nonempty := by decide

/-- The ten Petersen vertices: the `2`-subsets of a `5`-set, listed. -/
def petersenVerts : List (KSub 5 2) :=
  [⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩, ⟨{0, 4}, by decide⟩,
    ⟨{1, 2}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{1, 4}, by decide⟩,
    ⟨{2, 3}, by decide⟩, ⟨{2, 4}, by decide⟩, ⟨{3, 4}, by decide⟩]

/-- **Completeness of the vertex list**: ten entries, no repetition, every vertex. -/
example : petersenVerts.length = 10 ∧ petersenVerts.Nodup ∧
    ∀ v : KSub 5 2, v ∈ petersenVerts := by decide

set_option maxRecDepth 4096 in
/-- Every five vertices contain a Kneser edge, over all `C(10,5) = 252` five-element
sublists: no `5`-element independent set exists. A subset of an independent set is
independent, so refuting size exactly `5` refutes every larger size — with the star row
as the matching lower bound, `α(Petersen) = 4`. -/
example : ∀ S ∈ petersenVerts.sublistsLen 5,
    ∃ x ∈ S, ∃ y ∈ S, x.1 ∩ y.1 = ∅ := by decide

/-! ## Non-vacuity: the main theorem instantiates at the Petersen carrier -/

section Live

local instance kSub52Nonempty : Nonempty (KSub 5 2) := KSub.nonempty (by norm_num)

/-- **The Kneser spectrum, live at `K(5,2)`**: the main theorem hands over the Petersen
eigenvalue in closed form on every eigenspace. -/
example (j : Fin (min 2 (5 - 2) + 1)) :
    eigenmatrixP (johnsonSpectrumEquiv j)
        (⟨kneserSet 5 2, kneserSet_mem_orbits (by norm_num)⟩
          : ↥(orbits (Equiv.Perm (Fin 5)) (KSub 5 2 × KSub 5 2)))
      = (((-1) ^ (j : ℕ) * ((5 - 2 - (j : ℕ)).choose (2 - (j : ℕ)) : ℤ) : ℤ) : ℂ) :=
  eigenmatrixP_kneser (by norm_num) j

/-- The edge count, through `card_kneserSet` rather than by evaluation. -/
example : #(kneserSet 5 2) = (5).choose 2 * (5 - 2).choose 2 :=
  card_kneserSet (by norm_num)

/-- The disjointness orbital has width zero, live. -/
example : orbWidth (⟨kneserSet 5 2, kneserSet_mem_orbits (by norm_num)⟩
    : ↥(orbits (Equiv.Perm (Fin 5)) (KSub 5 2 × KSub 5 2))) = 0 :=
  orbWidth_kneserSet (by norm_num)

end Live

end ECCLib.Scheme.Johnson

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.Johnson.kneserSet' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.kneserSet

/-- info: 'ECCLib.Scheme.Johnson.mem_kneserSet' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.mem_kneserSet

/-- info: 'ECCLib.Scheme.Johnson.kneserSet_mem_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.kneserSet_mem_orbits

/-- info: 'ECCLib.Scheme.Johnson.orbWidth_kneserSet' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.orbWidth_kneserSet

/-- info: 'ECCLib.Scheme.Johnson.eigenmatrixP_kneser' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.eigenmatrixP_kneser

/-- info: 'ECCLib.Scheme.Johnson.card_kneserSet' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_kneserSet

/-- info: 'ECCLib.Scheme.Johnson.petersenVerts' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.petersenVerts

/-- info: 'ECCLib.Scheme.Johnson.kSub52Nonempty' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.kSub52Nonempty

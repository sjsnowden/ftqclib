/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Eberlein

/-!
# Checks for `ECCLib/Delsarte/Eberlein.lean`

Axiom sweeps, and the **numeric identifications that pinned the index convention**.

The identification rows are the reason this file matters more than a usual check module. The
Johnson indexing is stated three different ways across the standard sources, and rather than
argue from conventions the alignment was settled by evaluating the definition against spectra
that are known independently. Those evaluations are kept here so the convention cannot drift
without a row going red.

**These rows are numeric evidence, not theorems.** They pin the convention and they check the
closed form at particular points. They do *not* prove that the Johnson eigenmatrix has Eberlein
entries — that is a separate statement about the Johnson scheme.

**Orientation.** The naive form `eigenmatrixP i j = eberlein n k i j` is **false**: it attaches
the `P`/`Q` names the wrong way around. Under `Scheme/OrbitalSpectrum.lean`'s orientation —
`eigenmatrixP` indexed spectrum × orbital, entries pinned as eigenvalues by
`orbitalAdj_mul_orbitalIdem` — the identification reads
`eigenmatrixP I (interCard-orbital (k − l)) = eberlein n k l t` with `I` the spectral index
identified by the separation argument.
-/

namespace ECCLib.Delsarte

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Delsarte.eberlein_zero_degree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_zero_degree

/-- info: 'ECCLib.Delsarte.eberlein_at_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_at_zero

/-- info: 'ECCLib.Delsarte.eberlein_degree_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_degree_one

/-- info: 'ECCLib.Delsarte.eberlein' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein

/-! ## The identification: degree one is the classical Johnson spectrum

The Johnson graph `J(n,k)` has adjacency eigenvalues `(k−j)(n−k−j) − j` for `j = 0, …, k`. Three
schemes are checked, and the third is the one that does the work. -/

/-! `J(4,2)`: spectrum `{4, 0, −2}`. -/
/-- info: [4, 0, -2] -/
#guard_msgs in
#eval (List.range 3).map (fun t => eberlein 4 2 1 t)

/-! `J(6,3)`: spectrum `{9, 3, −1, −3}`. -/
/-- info: [9, 3, -1, -3] -/
#guard_msgs in
#eval (List.range 4).map (fun t => eberlein 6 3 1 t)

/-! ## The row that actually pins the alignment

`J(4,2)` and `J(6,3)` have **palindromic** valences — `[1,4,1]` and `[1,9,9,1]` — so neither can
distinguish which relation the degree index `l` names. `J(5,2)` has valences `[3,6,1]` and can.

Reading `P_l(0)` against those valences gives `l = k − t`: the degree index is the Johnson
**distance**, not the intersection size. If that alignment were ever flipped, the third row below
would go red while the first two stayed green. -/

/-! `J(5,2)`: spectrum `{6, 1, −2}`. -/
/-- info: [6, 1, -2] -/
#guard_msgs in
#eval (List.range 3).map (fun t => eberlein 5 2 1 t)

/-! The valences of `J(5,2)`, asymmetric: `C(k,l)·C(n−k,l)` for `l = 0,1,2`. -/
/-- info: [1, 6, 3] -/
#guard_msgs in
#eval (List.range 3).map (fun l => Nat.choose 2 l * Nat.choose 3 l)

/-! `P_l(0)` on `J(5,2)`, which must equal the valence of relation `l`. -/
/-- info: [1, 6, 3] -/
#guard_msgs in
#eval (List.range 3).map (fun l => eberlein 5 2 l 0)

/-! ## An independent check of the whole family

`Σ_l P_l(t)` is `|X|` at `t = 0` and zero elsewhere — the all-ones vector is the trivial
eigenvector. This tests every column at once rather than one at a time. -/

/-- info: [10, 0, 0] -/
#guard_msgs in
#eval (List.range 3).map (fun t => ((List.range 3).map (fun l => eberlein 5 2 l t)).sum)

/-- info: [6, 0, 0] -/
#guard_msgs in
#eval (List.range 3).map (fun t => ((List.range 3).map (fun l => eberlein 4 2 l t)).sum)

/-! ## `P_l(0)` is the valence, as a theorem rather than a table -/

/-- The valence identity at a concrete scheme, through `eberlein_at_zero` rather than by
evaluation. -/
theorem eberlein_at_zero_five_two (l : ℕ) :
    eberlein 5 2 l 0 = (Nat.choose 2 l : ℤ) * (Nat.choose 3 l : ℤ) :=
  eberlein_at_zero 5 2 l

/-- Degree one, through `eberlein_degree_one` rather than by evaluation. -/
example (t : ℕ) : eberlein 5 2 1 t = ((2 - t : ℕ) : ℤ) * ((3 - t : ℕ) : ℤ) - (t : ℤ) :=
  eberlein_degree_one 5 2 t

/-- info: 'ECCLib.Delsarte.eberlein_at_zero_five_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_at_zero_five_two

/-- info: 'ECCLib.Delsarte.eberlein_degree_one_succ_lt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_degree_one_succ_lt

/-- info: 'ECCLib.Delsarte.eberlein_degree_one_lt_of_lt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_degree_one_lt_of_lt

/-! ## The top-degree collapse -/

/-- Top degree at `J(5,2)` — the Petersen eigenvalue row `3, −2, 1`: the closed form
against the literal sum, every column. -/
example : ∀ t < 3, eberlein 5 2 2 t = (-1) ^ t * ((3 - t).choose (2 - t) : ℤ) := by decide

/-- Top degree at the balanced `J(6,3)`: the surviving binomial is `C(3−t, 3−t) = 1`, so
the row is the alternating `±1` — the Kneser relation there is the disjoint-complement
matching. -/
example : ∀ t < 4, eberlein 6 3 3 t = (-1) ^ t * ((6 - 3 - t).choose (3 - t) : ℤ) := by
  decide

/-- Through `eberlein_top_degree` rather than by evaluation. -/
example (t : ℕ) (ht : t ≤ 2) :
    eberlein 5 2 2 t = (-1) ^ t * ((5 - 2 - t).choose (2 - t) : ℤ) :=
  eberlein_top_degree ht

/-- info: 'ECCLib.Delsarte.eberlein_top_degree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.eberlein_top_degree

end ECCLib.Delsarte

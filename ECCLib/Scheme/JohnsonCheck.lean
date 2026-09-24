/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Johnson
import ECCLib.Delsarte.Eberlein
import Mathlib.Combinatorics.SetFamily.KruskalKatona

/-!
# Checks for the Johnson scheme

Axiom sweeps, kernel rows, and the discriminating row that pins the count's guard.

## Why the kernel rows decide the invariant's image and not `orbits`

Deciding `(orbits _ _).card` directly is measured infeasible past the smallest cases: `J(4,2)`
costs about eighty seconds and `J(5,2)` did not return in five minutes. By the classification the
number of orbitals *is* the number of distinct values of `interCard`, and that image decides in
seconds — `J(6,3)` in about eleven. So the rows below compute the image.

The ceiling on that route is `(7,3)`, which fails with an **elaboration stack overflow** rather
than a heartbeat timeout, so raising `maxHeartbeats` would not help; only a larger interpreter
stack would.
-/

namespace ECCLib.Scheme.Johnson

open Finset

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.Johnson.mem_orbit_iff_interCard_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.mem_orbit_iff_interCard_eq

/-- info: 'ECCLib.Scheme.Johnson.swap_mem_orbit' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.swap_mem_orbit

/-- info: 'ECCLib.Scheme.Johnson.isSelfPaired_kSub' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.isSelfPaired_kSub

/-- info: 'ECCLib.Scheme.Johnson.card_orbits_kSub' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_orbits_kSub

/-- info: 'ECCLib.Scheme.Johnson.card_orbits_finset_kSub' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_orbits_finset_kSub

/-- info: 'ECCLib.Scheme.Johnson.isCommutative_johnsonAlgebra' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.isCommutative_johnsonAlgebra

/-! ## Carrier sizes -/

/-- info: 6 -/
#guard_msgs in
#eval Fintype.card (KSub 4 2)

/-- info: 4 -/
#guard_msgs in
#eval Fintype.card (KSub 4 3)

/-- info: 0 -/
#guard_msgs in
#eval Fintype.card (KSub 2 3)

/-! ## Kernel rows: the number of distinct invariant values is the orbital count -/

/-- `J(4,2)`: three orbitals. -/
example : (univ.image (interCard (n := 4) (k := 2))).card = 3 := by decide

/-- `J(4,3)`: two orbitals — and the row that refutes the unguarded `k + 1`, on a **nonempty**
carrier, so it cannot be waved away as degenerate. -/
example : (univ.image (interCard (n := 4) (k := 3))).card = 2 := by decide

set_option maxRecDepth 8000 in
/-- `J(5,3)`: three orbitals. Also `min`-form only. Needs a raised recursion depth, scoped to
this declaration — an unscoped `set_option` trips the standard linter. -/
example : (univ.image (interCard (n := 5) (k := 3))).card = 3 := by decide

/-- `J(2,3)`: the carrier is empty, so there are no orbitals at all. This is the row that shows
the `k ≤ n` guard is doing work — without it the formula would claim one. -/
example : (univ.image (interCard (n := 2) (k := 3))).card = 0 := by decide

/-- The degenerate edges. -/
example : (univ.image (interCard (n := 0) (k := 0))).card = 1 := by decide

example : (univ.image (interCard (n := 3) (k := 3))).card = 1 := by decide

/-! ## The formula against those rows

The theorem is abstract; these check that the arithmetic it produces matches the kernel counts
above. `(4,3)` and `(5,3)` are the discriminating pair: the classical `k + 1` gives 4 at both and
is wrong, while the guarded `min` form gives 2 and 3 and is right. -/

example : min 2 (4 - 2) + 1 = 3 := by norm_num

example : min 3 (4 - 3) + 1 = 2 := by norm_num

example : min 3 (5 - 3) + 1 = 3 := by norm_num

/-- The unguarded classical formula is **wrong** at `(4,3)`: it would give four orbitals where the
kernel counts two. -/
example : (3 : ℕ) + 1 ≠ (univ.image (interCard (n := 4) (k := 3))).card := by decide

set_option maxRecDepth 8000 in
/-- ...and wrong at `(5,3)` too. -/
example : (3 : ℕ) + 1 ≠ (univ.image (interCard (n := 5) (k := 3))).card := by decide

/-- Where `2 * k ≤ n` does hold, the two formulas agree, as the corollary says. -/
example : min 2 (4 - 2) + 1 = 2 + 1 := by norm_num

/-! ## The Erdős–Ko–Rado agreement row

EKR bounds an intersecting family of `k`-subsets — **the same objects this scheme is built on**.
Mathlib proves it by compression (`Combinatorics/SetFamily/KruskalKatona.lean`), a method with
nothing in common with orbital combinatorics, so it is worth far more here as an independent
witness than it would have been as a target. It is not re-proved here.

The row that connects the two is that **the scheme's own invariant being positive is exactly
EKR's intersecting condition** — so a family that is pairwise intersecting in `interCard` is
bounded by a theorem this layer had no hand in. -/

theorem interCard_pos_iff_not_disjoint {n k : ℕ} (x y : KSub n k) :
    0 < interCard (x, y) ↔ ¬ Disjoint x.1 y.1 := by
  change 0 < (x.1 ∩ y.1).card ↔ _
  rw [Finset.card_pos, Finset.not_disjoint_iff_nonempty_inter]

/-- **The agreement row.** A family of `k`-subsets pairwise intersecting in the scheme's
invariant obeys the Erdős–Ko–Rado bound. -/
theorem card_le_of_interCard_pos {n k : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (hsize : ∀ S ∈ 𝒜, S.card = k)
    (hint : ∀ S ∈ 𝒜, ∀ T ∈ 𝒜, ¬ Disjoint S T)
    (hk : k ≤ n / 2) :
    𝒜.card ≤ (n - 1).choose (k - 1) :=
  Finset.erdos_ko_rado (fun _ hS _ hT => hint _ hS _ hT) (fun _ hS => hsize _ hS) hk

/-! ## Valences (Delsarte 4.21)

Axiom sweeps, then a **kernel row**: the valence at a concrete small scheme, verified by
`decide` without reference to the theorem. That is an independent check of the closed form rather
than a re-derivation of it. -/

/-- info: 'ECCLib.Scheme.Johnson.card_filter_inter_card_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_filter_inter_card_eq

/-- info: 'ECCLib.Scheme.Johnson.card_filter_interCard_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_filter_interCard_eq

/-- info: 'ECCLib.Scheme.Johnson.card_filter_interCard_eq_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_filter_interCard_eq_self

/-- info: 'ECCLib.Scheme.Johnson.card_filter_interCard_eq_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_filter_interCard_eq_zero

/-- **Kernel row.** `J(4,2)`: every point has exactly 4 neighbours at intersection 1, checked by
the kernel over all 6 carriers rather than through the closed form. -/
theorem valence_four_two_kernel :
    ∀ x : KSub 4 2, (Finset.univ.filter (fun y : KSub 4 2 => interCard (x, y) = 1)).card = 4 := by
  decide

/-- ...and the closed form agrees: `C(2,1) * C(2,1) = 4`. -/
example (x : KSub 4 2) :
    (Finset.univ.filter (fun y : KSub 4 2 => interCard (x, y) = 1)).card = 4 := by
  simpa using card_filter_interCard_eq (n := 4) (k := 2) (t := 1) x (by norm_num)

/-- **The valences partition the carrier.** Summing over all intersection sizes recovers
`|KSub n k|`, which is the identity `Σ_t C(k,t)·C(n−k,k−t) = C(n,k)` in disguise — Vandermonde. -/
theorem sum_valence_four_two :
    ∑ t ∈ Finset.range 3, (2 : ℕ).choose t * (4 - 2).choose (2 - t) = Nat.choose 4 2 := by
  decide

/-! ## The agreement row between the two computations of the valence

`Scheme/Johnson.lean` counts the valence combinatorially, by a bijection onto a product of
`powersetCard`s. `Delsarte/Eberlein.lean` computes `E_l(0)` as an alternating sum that collapses
to a single term. **They are the same number**, under `l = k − t` — which is the identity
`P_l(0) = v_l`, and which is also the numeric fact that pinned the index convention.

Neither side knows about the other: `Delsarte/` does not import `Scheme/`, and the counting proof
mentions no polynomial. So this is a genuine two-route agreement, not a restatement. -/

theorem valence_eq_eberlein_at_zero {n k t : ℕ} (x : KSub n k) (ht : t ≤ k) :
    ((Finset.univ.filter (fun y : KSub n k => interCard (x, y) = t)).card : ℤ)
      = ECCLib.Delsarte.eberlein n k (k - t) 0 := by
  rw [card_filter_interCard_eq x ht, ECCLib.Delsarte.eberlein_at_zero, Nat.choose_symm ht]
  push_cast
  ring

/-- info: 'ECCLib.Scheme.Johnson.valence_four_two_kernel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.valence_four_two_kernel

/-- info: 'ECCLib.Scheme.Johnson.sum_valence_four_two' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.sum_valence_four_two

/-- info: 'ECCLib.Scheme.Johnson.valence_eq_eberlein_at_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.valence_eq_eberlein_at_zero

/-- info: 'ECCLib.Scheme.Johnson.KSub.nonempty' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.KSub.nonempty

/-- info: 'ECCLib.Scheme.Johnson.KSub.k_le_of_nonempty' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.KSub.k_le_of_nonempty

end ECCLib.Scheme.Johnson

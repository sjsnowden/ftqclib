/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonOrthogonality

/-!
# Acceptance rows for the Eberlein full orthogonality

`eberlein_full_orthogonality` is decidable arithmetic: kernel rows check the diagonal and
off-diagonal at `J(4,2)` and `J(5,2)` against the literal `eberlein`, and the **control**
drops the `j = 0` guard and watches the diagonal fail — the same load-bearing-guard pattern
as `JohnsonMultiplicityCheck.lean`. Live rows instantiate the theorem through its own
hypotheses.
-/

namespace ECCLib.Scheme.Johnson

open Finset ECCLib.Delsarte

/-- `J(4,2)`, diagonal `d = d' = 1`: the orbital size `C(4,2)·C(2,1)·C(2,1) = 24`. -/
example : ∑ t ∈ Finset.range (min 2 (4 - 2) + 1),
    (if t = 0 then 1 else ((4).choose t : ℤ) - (4).choose (t - 1))
      * (eberlein 4 2 1 t * eberlein 4 2 1 t) = 24 := by decide

/-- `J(4,2)`, off-diagonal `d = 1, d' = 2`: orthogonality. -/
example : ∑ t ∈ Finset.range (min 2 (4 - 2) + 1),
    (if t = 0 then 1 else ((4).choose t : ℤ) - (4).choose (t - 1))
      * (eberlein 4 2 1 t * eberlein 4 2 2 t) = 0 := by decide

/-- `J(4,2)`, diagonal `d = d' = 2`: `C(4,2)·C(2,2)·C(2,2) = 6`. -/
example : ∑ t ∈ Finset.range (min 2 (4 - 2) + 1),
    (if t = 0 then 1 else ((4).choose t : ℤ) - (4).choose (t - 1))
      * (eberlein 4 2 2 t * eberlein 4 2 2 t) = 6 := by decide

/-- `J(5,2)`, diagonal `d = d' = 1`: `C(5,2)·C(2,1)·C(3,1) = 60`. -/
example : ∑ t ∈ Finset.range (min 2 (5 - 2) + 1),
    (if t = 0 then 1 else ((5).choose t : ℤ) - (5).choose (t - 1))
      * (eberlein 5 2 1 t * eberlein 5 2 1 t) = 60 := by decide

/-- `J(5,2)`, off-diagonal `d = 0, d' = 2`: orthogonality against the constant. -/
example : ∑ t ∈ Finset.range (min 2 (5 - 2) + 1),
    (if t = 0 then 1 else ((5).choose t : ℤ) - (5).choose (t - 1))
      * (eberlein 5 2 0 t * eberlein 5 2 2 t) = 0 := by decide

/-- **Control — the `t = 0` guard is load-bearing**: with the raw weight at `t = 0` the
`J(4,2)` diagonal `d = d' = 0` row is off by one. -/
example : ¬(∑ t ∈ Finset.range (min 2 (4 - 2) + 1),
    (((4).choose t : ℤ) - (4).choose (t - 1))
      * (eberlein 4 2 0 t * eberlein 4 2 0 t) = 6) := by decide

/-- The theorem instantiates through its own hypotheses. -/
example : ∑ t ∈ Finset.range (min 2 (4 - 2) + 1),
    (if t = 0 then 1 else ((4).choose t : ℤ) - (4).choose (t - 1))
      * (eberlein 4 2 1 t * eberlein 4 2 2 t)
    = if 1 = 2 then ((4).choose 2 * ((2).choose 1 * (4 - 2).choose 1) : ℤ) else 0 :=
  eberlein_full_orthogonality (by norm_num) (by norm_num) (by norm_num)

end ECCLib.Scheme.Johnson

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.Johnson.card_orbital_johnson' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.card_orbital_johnson

/-- info: 'ECCLib.Scheme.Johnson.eberlein_full_orthogonality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.eberlein_full_orthogonality

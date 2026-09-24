/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonMultiplicity

/-!
# Checks for the Johnson multiplicities

The orthogonality identity `eberlein_orthogonality` is decidable arithmetic: kernel rows check
it at `J(4,2)`, `J(5,2)` and `J(6,3)` against the literal `eberlein`, and a **control**
kernelises the truncation pitfall — the same sum with the `j = 0` guard dropped (the raw
`ℕ`-truncated weight `C(n,0) − C(n,0−1) = 0`) is refuted, so the guard is load-bearing, not
decoration. The closed forms are noncomputable (`spectralMult` is a `finrank`), so their rows
are live instantiations at `J(4,2)`.
-/

namespace ECCLib.Scheme.Johnson

open Finset ECCLib.Delsarte

/-- `J(4,2)`, `d = 0`: the multiplicity row sums to `C(4,2) = 6` against the constant. -/
example : ∑ j ∈ Finset.range (min 2 (4 - 2) + 1),
    (if j = 0 then 1 else ((4).choose j : ℤ) - (4).choose (j - 1)) * eberlein 4 2 0 j
      = 6 := by decide

/-- `J(4,2)`, `d = 1`: orthogonality. -/
example : ∑ j ∈ Finset.range (min 2 (4 - 2) + 1),
    (if j = 0 then 1 else ((4).choose j : ℤ) - (4).choose (j - 1)) * eberlein 4 2 1 j
      = 0 := by decide

/-- `J(4,2)`, `d = 2`: orthogonality. -/
example : ∑ j ∈ Finset.range (min 2 (4 - 2) + 1),
    (if j = 0 then 1 else ((4).choose j : ℤ) - (4).choose (j - 1)) * eberlein 4 2 2 j
      = 0 := by decide

/-- `J(5,2)`, `d = 0`. -/
example : ∑ j ∈ Finset.range (min 2 (5 - 2) + 1),
    (if j = 0 then 1 else ((5).choose j : ℤ) - (5).choose (j - 1)) * eberlein 5 2 0 j
      = 10 := by decide

/-- `J(5,2)`, `d = 2`. -/
example : ∑ j ∈ Finset.range (min 2 (5 - 2) + 1),
    (if j = 0 then 1 else ((5).choose j : ℤ) - (5).choose (j - 1)) * eberlein 5 2 2 j
      = 0 := by decide

/-- `J(6,3)`, `d = 3`: the deepest shell at the balanced carrier. -/
example : ∑ j ∈ Finset.range (min 3 (6 - 3) + 1),
    (if j = 0 then 1 else ((6).choose j : ℤ) - (6).choose (j - 1)) * eberlein 6 3 3 j
      = 0 := by decide

/-- **Control — the `j = 0` guard is load-bearing** (the truncation pitfall,
kernelised): with the raw weight `C(n,0) − C(n,0−1) = 0` at `j = 0`, the `d = 0` row is
off by exactly `1` and the identity fails. -/
example : ¬(∑ j ∈ Finset.range (min 2 (4 - 2) + 1),
    (((4).choose j : ℤ) - (4).choose (j - 1)) * eberlein 4 2 0 j = 6) := by decide

/-! ## Live rows at `J(4,2)` -/

section Live

local instance : Nonempty (KSub 4 2) := KSub.nonempty (by norm_num)

/-- The orthogonality identity instantiates through its own hypotheses. -/
example : ∑ j ∈ Finset.range (min 2 (4 - 2) + 1),
    (if j = 0 then 1 else ((4).choose j : ℤ) - (4).choose (j - 1)) * eberlein 4 2 1 j
      = if 1 = 0 then ((4).choose 2 : ℤ) else 0 :=
  eberlein_orthogonality (by norm_num) (by norm_num)

/-- Gottlieb's rank theorem instantiates at a live carrier. -/
example : Matrix.rank (inclMatrix ℂ 4 1 2) = 4 :=
  rank_inclMatrix (by norm_num) (by norm_num)

/-- The trivial multiplicity at a live carrier. -/
example : spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin 4)) (KSub 4 2))
    (johnsonSpectrumEquiv (0 : Fin (min 2 (4 - 2) + 1))) = 1 :=
  spectralMult_johnson_zero

/-- The subtraction-free closed form at a live carrier. -/
example (j : Fin (min 2 (4 - 2) + 1)) (hj : 0 < (j : ℕ)) :
    spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin 4)) (KSub 4 2))
        (johnsonSpectrumEquiv j) + (4).choose ((j : ℕ) - 1)
      = (4).choose (j : ℕ) :=
  spectralMult_johnson_add_choose hj

end Live

end ECCLib.Scheme.Johnson

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.Johnson.inclGramK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.inclGramK

/-- info: 'ECCLib.Scheme.Johnson.inclGramT' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.inclGramT

/-- info: 'ECCLib.Scheme.Johnson.splitChar_johnsonSpectrumEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.splitChar_johnsonSpectrumEquiv

/-- info: 'ECCLib.Scheme.Johnson.splitChar_inclGramK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.splitChar_inclGramK

/-- info: 'ECCLib.Scheme.Johnson.splitChar_inclGramT' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.splitChar_inclGramT

/-- info: 'ECCLib.Scheme.Johnson.sum_spectralMult_filter_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.sum_spectralMult_filter_le

/-- info: 'ECCLib.Scheme.Johnson.spectralMult_johnson_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.spectralMult_johnson_zero

/-- info: 'ECCLib.Scheme.Johnson.spectralMult_johnson_add_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.spectralMult_johnson_add_choose

/-- info: 'ECCLib.Scheme.Johnson.spectralMult_johnson_eq_sub' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.spectralMult_johnson_eq_sub

/-- info: 'ECCLib.Scheme.Johnson.trace_orbitalAdj_johnson' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.trace_orbitalAdj_johnson

/-- info: 'ECCLib.Scheme.Johnson.eberlein_orthogonality' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.eberlein_orthogonality

/-- info: 'ECCLib.Scheme.Johnson.rank_inclMatrix' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.rank_inclMatrix

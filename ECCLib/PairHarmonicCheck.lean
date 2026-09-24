/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.PairHarmonic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Checks for `ECCLib/PairHarmonic.lean`

Axiom sweeps, kernel rows for the three value regimes (`1`, `-1`, `0`) at a concrete pair
system over `ℤ`, and a generality row at `ZMod 6` — a commutative ring with zero divisors,
which the statements' `[CommRing R]` claims to allow and a `[NoZeroDivisors]` phrasing would
not.
-/

namespace ECCLib

/-- info: 'ECCLib.pairDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff

/-- info: 'ECCLib.pairDiff_eq_zero_of_mem_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff_eq_zero_of_mem_iff

/-- info: 'ECCLib.pairDiff_eq_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff_eq_one

/-- info: 'ECCLib.pairDiff_map_swap' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff_map_swap

/-- info: 'ECCLib.exists_card_eq_and_pairDiff_eq_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.exists_card_eq_and_pairDiff_eq_one

/-! ## Kernel rows — the three value regimes at one pair over `ℤ`

Pair system `a = ![0]`, `b = ![1]` in `Fin 3`. A transversal (`{0}`, also `{0,2}`) gives `1`;
the reversed transversal (`{1}`) gives `-1`; a non-separating subset (`{0,1}` contains both,
`{2}` contains neither) gives `0`. -/

example : pairDiff ℤ ![(0 : Fin 3)] ![1] {0} = 1 := by decide
example : pairDiff ℤ ![(0 : Fin 3)] ![1] {0, 2} = 1 := by decide
example : pairDiff ℤ ![(0 : Fin 3)] ![1] {1} = -1 := by decide
example : pairDiff ℤ ![(0 : Fin 3)] ![1] {0, 1} = 0 := by decide
example : pairDiff ℤ ![(0 : Fin 3)] ![1] {2} = 0 := by decide

/-- Two pairs: `K = {0, 2}` separates both positively → `1`; flipping one pair's membership
(`K = {0, 3}` hits `b 1 = 3`) flips the sign. -/
example : pairDiff ℤ ![(0 : Fin 4), 2] ![1, 3] {0, 2} = 1 := by decide
example : pairDiff ℤ ![(0 : Fin 4), 2] ![1, 3] {0, 3} = -1 := by decide

/-! ## Generality row — a ring with zero divisors

`ZMod 6` has zero divisors; the definition and the transversal value are indifferent. -/

example : pairDiff (ZMod 6) ![(0 : Fin 3)] ![1] {0} = 1 := by decide

end ECCLib

/-- info: 'ECCLib.exists_transversal' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.exists_transversal

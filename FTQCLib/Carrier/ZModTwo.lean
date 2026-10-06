/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Two facts about `ZMod 2`

A bit is `0` or `1`, and a sum over the two bits is their two terms. Mathlib has the second for
`Fin 2` (`Fin.sum_univ_two`), and `ZMod 2` unfolds to `Fin 2`, so it is Mathlib's read at `ZMod 2`,
stated here so that `rw` finds it, which it does not through the unfolding; Mathlib has no lemma for
the first (checked at the pinned revision, 2026-10-02). They lived in eight private copies in the carrier modules and five more in the older
layers (docs/STEPS.md, entries 2026-10-02d and 2026-10-02e); this is their one home, importing
Mathlib alone. The older layers' copies are reported, not moved.

## Main results

* `zmod_two_dichotomy` — a bit is `0` or `1`.
* `sum_zmod_two` — `∑ t : ZMod 2, f t = f 0 + f 1`.
-/

namespace FTQCLib.Frame.Walkthrough

/-- A bit is `0` or `1`, decided over the two bits. -/
theorem zmod_two_dichotomy (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- A sum over the two bits is their two terms: `Fin.sum_univ_two` at `ZMod 2`. -/
theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ t, f t = f 0 + f 1 :=
  Fin.sum_univ_two f

end FTQCLib.Frame.Walkthrough

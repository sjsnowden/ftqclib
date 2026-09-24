/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BooleanMobius

set_option linter.style.longLine false

/-! # The Lie framing: no Lie cocycle, and integration is just translation

This file treats the **Lie / infinitesimal framing** of the frame's difference data: does that data
carry an alternating 3-cocycle — the seed a Lie/L∞ bracket would need? The answer is no, and for a
structural reason, not an accident of examples:

* `tripleDeriv_perm_invariant` — the iterated triple difference is **fully symmetric** in its three
  directions, for ANY phase `f` and any codomain (from `funcDerivG_comm` alone — mixed differences
  commute). This generalizes the per-gate check `thirdDiff_symm`
  (`FTQCLib/Explore/CubicPolarization.lean`) to a law.
* `alternating_triple_eq_zero` — hence the **signed S₃-sum of triple differences vanishes
  identically**: the built data carries no alternating trilinear cocycle. The Lie framing's bracket
  seed does not exist — by commutativity, not by symmetry of a particular gate.
* `funcDerivG_bracket_eq_zero` — the operator bracket `[D_i, D_j] = 0`: the difference calculus's
  Lie algebra is abelian; all its content is in the *associative* relation `D(D+2) = 0`
  (`FTQCLib/Frame/CurvatureObstruction.lean`), which is the object of
  `FTQCLib/Explore/FactorizationHomology.lean`.
* `shiftOp` + `shiftOp_eq_add_funcDerivG` + `shiftOp_involutive` + `shiftOp_comm` — the
  **integration answer**: the discrete exponential of `D_i` is exactly `1 + D_i` = the shift
  operator, it is an involution (`(1+D)² = 1`, the operator face of `D(D+2) = 0`), and the shifts
  commute. So integrating the frame's "infinitesimal" data yields precisely the translation action
  of `(𝔽₂)ⁿ` already present — no higher-symplectic direction exists infinitesimally, and no
  `exp`-divergence subtlety arises (the exponential series is exact at first order; there are no
  higher divided powers to divide by).

**Relation to the literature.** Rogers's higher-symplectic L∞ tower is built on *skew* contraction
and is inert to the frame's *symmetric* trilinear data; Nekovář's char-0 higher-Heisenberg
construction divides by 2 throughout; a curved-L∞ variant is the cohomological framing in different
clothes, with absorption of the `−2` closed off. Together with these observations, this file
formalizes the statement that the Lie framing reduces to the cohomological one: the Lie-specific
content of the frame's difference data is (i) an abelian bracket, (ii) no alternating cocycle, (iii)
integration = translations. What survives of the framing is exactly its associative/factorization
face, treated in `FactorizationHomology.lean`. An exploratory file, not part of the `FTQCLib`
target. -/

namespace FTQCLib.Explore.LieClosure

open FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ} {A : Type*} [AddCommGroup A]

/-! ## The triple difference is symmetric — hence no alternating cocycle -/

/-- **Full symmetry of the triple difference in its directions** (any phase, any codomain): the six
orderings of `D_i D_j D_k` coincide. Pure `funcDerivG_comm`. Stated as invariance under the two generating
transpositions; the other orderings follow by composition (see `alternating_triple_eq_zero`, which uses all
six). -/
theorem tripleDeriv_swap₁₂ (i j k : Fin n) (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG j (funcDerivG k f))
      = funcDerivG j (funcDerivG i (funcDerivG k f)) :=
  funcDerivG_comm i j (funcDerivG k f)

theorem tripleDeriv_swap₂₃ (i j k : Fin n) (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG j (funcDerivG k f))
      = funcDerivG i (funcDerivG k (funcDerivG j f)) :=
  congrArg (funcDerivG i) (funcDerivG_comm j k f)

/-- The two 3-cycles equal the identity ordering (with the transposition lemmas above, all six orderings
coincide — the full S₃-invariance). -/
theorem tripleDeriv_perm_invariant (i j k : Fin n) (f : (Fin n → ZMod 2) → A) :
    funcDerivG j (funcDerivG k (funcDerivG i f))
        = funcDerivG i (funcDerivG j (funcDerivG k f))
      ∧ funcDerivG k (funcDerivG i (funcDerivG j f))
        = funcDerivG i (funcDerivG j (funcDerivG k f)) := by
  constructor
  · rw [congrArg (funcDerivG j) (funcDerivG_comm k i f),
      funcDerivG_comm j i (funcDerivG k f)]
  · rw [funcDerivG_comm k i (funcDerivG j f),
      congrArg (funcDerivG i) (funcDerivG_comm k j f)]

/-- **The alternating trilinear part vanishes identically.** The signed sum over all six orderings
of the triple difference is `0` for every phase — the frame's difference data carries **no
alternating 3-cocycle**, so there is no Lie/L∞ bracket seed. The mechanism is `funcDerivG_comm`
(commutativity), not the symmetry of any particular gate. -/
theorem alternating_triple_eq_zero (i j k : Fin n) (f : (Fin n → ZMod 2) → A) :
    (funcDerivG i (funcDerivG j (funcDerivG k f))
      + funcDerivG j (funcDerivG k (funcDerivG i f))
      + funcDerivG k (funcDerivG i (funcDerivG j f)))
      - (funcDerivG j (funcDerivG i (funcDerivG k f))
      + funcDerivG i (funcDerivG k (funcDerivG j f))
      + funcDerivG k (funcDerivG j (funcDerivG i f))) = 0 := by
  obtain ⟨h1, h2⟩ := tripleDeriv_perm_invariant i j k f
  have h3 : funcDerivG k (funcDerivG j (funcDerivG i f))
      = funcDerivG i (funcDerivG j (funcDerivG k f)) := by
    rw [congrArg (funcDerivG k) (funcDerivG_comm j i f),
      funcDerivG_comm k i (funcDerivG j f),
      congrArg (funcDerivG i) (funcDerivG_comm k j f)]
  rw [h1, h2, h3, ← tripleDeriv_swap₁₂ i j k f, ← tripleDeriv_swap₂₃ i j k f]
  abel

/-- **The bracket is abelian:** `[D_i, D_j] = 0` as operators. The difference calculus's Lie algebra
is the abelian one; all structure lives in the associative relation `D(D+2) = 0` (see
`FactorizationHomology.lean`). -/
theorem funcDerivG_bracket_eq_zero (i j : Fin n) (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG j f) - funcDerivG j (funcDerivG i f) = 0 := by
  rw [funcDerivG_comm]
  abel

/-! ## Integration: the discrete exponential is `1 + D`, exactly -/

/-- The shift operator `T_i f = f(· + e_i)` — the group element the difference operator differentiates. -/
def shiftOp (i : Fin n) (f : (Fin n → ZMod 2) → A) : (Fin n → ZMod 2) → A :=
  fun v => f (v + Pi.single i 1)

/-- **`exp(D) = 1 + D`, exactly:** the shift is the identity plus the difference — the discrete exponential
series terminates at first order (no `1/k!` is ever needed, so the char-2 "no exp" obstruction is moot for
this data). -/
theorem shiftOp_eq_add_funcDerivG (i : Fin n) (f : (Fin n → ZMod 2) → A) :
    shiftOp i f = f + funcDerivG i f := by
  funext v
  simp only [shiftOp, Pi.add_apply, funcDerivG_apply]
  abel

/-- **The integrated object is an involution:** `T_i² = 1` — the operator face of `D(D+2) = 0` (expand
`(1+D)² = 1 + 2D + D² = 1 + 2D − 2D`). Integration of the frame's infinitesimal data produces exactly the
translation action of `(𝔽₂)ⁿ`, nothing more. -/
theorem shiftOp_involutive (i : Fin n) (f : (Fin n → ZMod 2) → A) :
    shiftOp i (shiftOp i f) = f := by
  funext v
  simp only [shiftOp]
  congr 1
  rw [add_assoc, ← Pi.single_add, show (1 : ZMod 2) + 1 = 0 from by decide, Pi.single_zero,
    add_zero]

/-- The shifts commute — the integrated group is the abelian translation group. -/
theorem shiftOp_comm (i j : Fin n) (f : (Fin n → ZMod 2) → A) :
    shiftOp i (shiftOp j f) = shiftOp j (shiftOp i f) := by
  funext v
  simp only [shiftOp]
  congr 1
  abel

end FTQCLib.Explore.LieClosure

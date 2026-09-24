/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.BooleanMobius

set_option linter.style.longLine false

/-!
# Is interaction × precision a coherent bigrading? (a structured negative)

The frame grades a diagonal phase by two axes: **interaction** (`totalDegree`) and **precision**
(`m − 1 − twoAdicVal(coeff)`). The question is whether these compose into a
coherent *bigraded* structure (a graded ring). They do not, and this file says exactly why.

The precision axis is governed by `twoAdicVal`, and its behavior under the ring product is the
**saturating-valuation law** `twoAdicVal_mul`:
```
    twoAdicVal (c · c') = min m (twoAdicVal c + twoAdicVal c')
```
So `twoAdicVal` is additive **below** the saturation threshold `m` (`twoAdicVal_mul_of_le`) and **saturates** at
it — it is *not* additive in general (`twoAdicVal_not_additive`: in ℤ/8, `v(4·4) = 3 ≠ 4 = v(4)+v(4)`, because
`4·4 = 0`). A graded-ring grading must be additive under the product; the precision grade is not. Hence:

**The structured negative.** Interaction × precision is *not* a coherent graded-ring bigrading — the precision
axis is a valuation that saturates at `m`. It *is* coherent on the unsaturated regime (`twoAdicVal c + twoAdicVal
c' ≤ m`), so the two axes are **irreducibly coupled** through the saturating valuation, not a product lattice.
This is why `effectiveLevel` (which folds precision in as `m−1−twoAdicVal`) cannot be split into two independent
graded axes.
-/

namespace FTQCLib.Hierarchy.DiagPhase

variable {m : ℕ}

private lemma val_ne_zero_of_ne {c : ZMod (2 ^ m)} (hc : c ≠ 0) : c.val ≠ 0 :=
  fun h => hc (by rw [← ZMod.natCast_zmod_val c, h, Nat.cast_zero])

/-- **The saturating 2-adic valuation law.** `twoAdicVal (c·c') = min m (v c + v c')`: the precision
valuation is additive below the saturation threshold `m` and saturates at it. The exact obstruction to an
interaction × precision graded-ring bigrading. -/
theorem twoAdicVal_mul (c c' : ZMod (2 ^ m)) :
    twoAdicVal (c * c') = min m (twoAdicVal c + twoAdicVal c') := by
  haveI : NeZero (2 ^ m) := ⟨(Nat.two_pow_pos m).ne'⟩
  by_cases hc : c = 0
  · rw [hc, zero_mul, twoAdicVal_zero]; omega
  by_cases hc' : c' = 0
  · rw [hc', mul_zero, twoAdicVal_zero]; omega
  have hx : c.val ≠ 0 := val_ne_zero_of_ne hc
  have hy : c'.val ≠ 0 := val_ne_zero_of_ne hc'
  have hxy : c.val * c'.val ≠ 0 := Nat.mul_ne_zero hx hy
  have hvalmul : (c * c').val = (c.val * c'.val) % 2 ^ m := ZMod.val_mul c c'
  have hsum : Nat.factorization (c.val * c'.val) 2 = twoAdicVal c + twoAdicVal c' := by
    rw [Nat.factorization_mul hx hy, Finsupp.add_apply,
      ← twoAdicVal_of_ne_zero hc, ← twoAdicVal_of_ne_zero hc']
  refine le_antisymm (le_min (twoAdicVal_le _) ?_) ?_
  · -- twoAdicVal (c*c') ≤ v c + v c'
    by_cases hcc : c * c' = 0
    · rw [hcc, twoAdicVal_zero]
      have hdvd : 2 ^ m ∣ c.val * c'.val :=
        Nat.dvd_of_mod_eq_zero (by rw [← hvalmul, hcc, ZMod.val_zero])
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hxy).mp hdvd
      omega
    · have h1 : 2 ^ (twoAdicVal (c * c')) ∣ c.val * c'.val := by
        have := pow_twoAdicVal_dvd_val hcc
        rw [hvalmul] at this
        exact (Nat.dvd_mod_iff (pow_dvd_pow 2 (twoAdicVal_le _))).mp this
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hxy).mp h1
      omega
  · -- min m (v c + v c') ≤ twoAdicVal (c*c')
    set k := min m (twoAdicVal c + twoAdicVal c') with hk
    have hk1 : 2 ^ k ∣ c.val * c'.val := by
      refine (pow_dvd_pow 2 (min_le_right _ _)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul (pow_twoAdicVal_dvd_val hc) (pow_twoAdicVal_dvd_val hc')
    have hk2 : 2 ^ k ∣ (c * c').val := by
      rw [hvalmul]; exact (Nat.dvd_mod_iff (pow_dvd_pow 2 (min_le_left _ _))).mpr hk1
    by_cases hcc : c * c' = 0
    · rw [hcc, twoAdicVal_zero]; exact min_le_left _ _
    · exact (pow_dvd_val_iff hcc k).mp hk2

/-- **Precision adds below saturation.** When `v c + v c' ≤ m`, the precision valuation is additive — the
bigrading is coherent on the unsaturated regime. -/
theorem twoAdicVal_mul_of_le (c c' : ZMod (2 ^ m))
    (h : twoAdicVal c + twoAdicVal c' ≤ m) :
    twoAdicVal (c * c') = twoAdicVal c + twoAdicVal c' := by
  rw [twoAdicVal_mul]; omega

/-- **The obstruction, concretely** (ℤ/8 = `ZMod (2^3)`): `twoAdicVal` is not additive at saturation, because
`4·4 = 0` — `v(4·4) = v(0) = 3 ≠ 4 = v(4) + v(4)`. A graded-ring grading would require additivity; the precision
axis fails it, so interaction × precision is not a coherent graded-ring bigrading. -/
theorem twoAdicVal_not_additive :
    twoAdicVal ((4 : ZMod (2 ^ 3)) * 4)
      ≠ twoAdicVal (4 : ZMod (2 ^ 3)) + twoAdicVal (4 : ZMod (2 ^ 3)) := by
  rw [twoAdicVal_mul]
  have hne : (4 : ZMod (2 ^ 3)) ≠ 0 := by decide
  have hval : (4 : ZMod (2 ^ 3)).val = 4 := by decide
  have h4 : twoAdicVal (4 : ZMod (2 ^ 3)) = 2 := by
    have hle : 2 ≤ twoAdicVal (4 : ZMod (2 ^ 3)) := by rw [← pow_dvd_val_iff hne, hval]; decide
    have hlt : ¬ 3 ≤ twoAdicVal (4 : ZMod (2 ^ 3)) := by rw [← pow_dvd_val_iff hne, hval]; decide
    omega
  rw [h4]; decide

/-! ## Beyond the negative: the level filtration (holds) and a strict DGA (blocked)

The graded-*ring* bigrading fails. Two candidate replacements, both pinned to the same 2-adic
obstruction:

* **The filtration holds.** `level` is subadditive under the product (`level_mul_le`), so the
  layers `F_d = {level ≤ d}` form a filtration `F_a·F_b ⊆ F_{a+b}` — an *upper bound*, which
  saturation obeys (products land lower). (The interaction filtration is separately
  `FTQCLib.Frame.mobiusDegLE_mul`.) The associated graded recovers a graded ring, but is
  degenerate wherever `level` drops.
* **The strict DGA is blocked.** The natural differential `funcDerivG` squares to `−2·(itself)`
  (`funcDerivG_funcDerivG`), and `−2 = 0` only over `ℤ/2` (`m = 1`). Over `ℤ/2^m` with `m ≥ 2` it
  is nonzero (`funcDerivG_sq_ne_zero`), so `d² ≠ 0` — no strict DGA. The obstruction is the same
  `2`-adic effect as the failure of the graded-ring bigrading. -/

section Structures
variable {n : ℕ}
open FTQCLib.Hierarchy.BooleanMobius

/-- **The level filtration.** `level (P·Q) ≤ level P + level Q`: `level` is subadditive under
the product, so `F_d = {level ≤ d}` is a filtration with `F_a·F_b ⊆ F_{a+b}`. (The single `m−1`
in `level = (m−1)+totalDegree` against the *two* on the right gives the slack; `totalDegree` is
itself subadditive.) -/
theorem level_mul_le (P Q : DiagPhase n m) :
    DiagPhase.level (P * Q) ≤ DiagPhase.level P + DiagPhase.level Q := by
  simp only [DiagPhase.level]
  have h := MvPolynomial.totalDegree_mul P Q
  omega

/-- **The differential squares to `−2·(itself)`.**
`funcDerivG i (funcDerivG i f) = (−2)·funcDerivG i f`, because the coordinate direction is
2-torsion (`e + e = 0` over `𝔽₂`). This is the obstruction to a strict DGA: `d² = 0` needs
`−2 = 0`. -/
theorem funcDerivG_funcDerivG {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG i f) = (-2 : ℤ) • funcDerivG i f := by
  funext v
  have he : v + Pi.single i (1 : ZMod 2) + Pi.single i (1 : ZMod 2) = v := by
    rw [add_assoc, ← Pi.single_add, show (1 : ZMod 2) + 1 = 0 from by decide, Pi.single_zero,
      add_zero]
  show funcDerivG i f (v + Pi.single i 1) - funcDerivG i f v = (-2 : ℤ) • funcDerivG i f v
  simp only [funcDerivG_apply]
  rw [he]
  abel

/-- **The strict DGA is blocked over `ℤ/2^m` for `m ≥ 2`** (`−2 ≠ 0`). Over `ℤ/4` the second
difference of `|v₀|` is `2 ≠ 0`, so `funcDerivG` is not a differential and no strict DGA exists there. -/
theorem funcDerivG_sq_ne_zero :
    ∃ (f : (Fin 1 → ZMod 2) → ZMod 4) (i : Fin 1), funcDerivG i (funcDerivG i f) ≠ 0 := by
  refine ⟨fun v => ((v 0).val : ZMod 4), 0, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [funcDerivG_funcDerivG, Pi.smul_apply, Pi.zero_apply] at h0
  have hd : funcDerivG (0 : Fin 1) (fun v => ((v 0).val : ZMod 4)) 0 = 1 := by
    rw [funcDerivG_apply]; decide
  rw [hd] at h0
  revert h0; decide

end Structures

end FTQCLib.Hierarchy.DiagPhase

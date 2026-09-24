/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BoolReduce
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.FrameExponent

/-!
# The Boolean normal form: multilinearity and level

`boolReduce P` is the Boolean normal form of a diagonal exponent: every exponent vector of the
support is replaced by its `0/1` shadow and coefficients of merged monomials are summed
(`FTQCLib/Hierarchy/BoolReduce.lean`). This module states what the normal form does to the two
readings of the exponent the frame uses: it is multilinear (`boolReduce_isMultilinear`), its
effective level is at most the exponent's (`effectiveLevel_boolReduce_le`), it is the identity on
multilinear input (`boolReduce_eq_self_of_isMultilinear`) and hence idempotent, and its
coefficients are the merged sums (`coeff_boolReduce`). The frame's extended level
`FTQCLib.Frame.levelExt` is the level of the normal form of the constant-free part; the two facts
its docstring states — bounded by the stripped exponent's level, equal to the level on constant-free
multilinear input — are theorems here.

## Main results

* `boolReduce_isMultilinear` — the normal form is multilinear.
* `effectiveLevel_boolReduce_le` — the normal form does not raise the effective level.
* `boolReduce_eq_self_of_isMultilinear`, `boolReduce_idem` — identity on multilinear input.
* `coeff_boolReduce` — the coefficient of the normal form is the sum over the merged monomials.
* `FTQCLib.Frame.levelExt_le_effectiveLevel_sub_C`, `FTQCLib.Frame.levelExt_eq_effectiveLevel` — the
  extended level against the level.

## Implementation notes

The first two results were first proved in `FTQCLib/Hilbert/CGKForward.lean`, above this layer; they
are stated here, at the layer that can state them, and the Hilbert module imports this one. The
proofs are the shorter ones: the support of a sum of monomials is inside the union of the
monomials' supports (`MvPolynomial.support_sum`), and the level of a sum is bounded by the
supremum of the summands' levels (`effectiveLevel_finsetSum_le`), which absorbs the merged
coefficients — no valuation of a sum of coefficients is ever computed here.
-/

namespace FTQCLib.Hierarchy.DiagPhase

open MvPolynomial

variable {n m : ℕ}

/-- Every entry of the Boolean shadow is `0` or `1`. -/
lemma boolShadow_apply_le_one (d : Fin n →₀ ℕ) (k : Fin n) : boolShadow d k ≤ 1 := by
  rw [boolShadow_apply]
  split_ifs <;> omega

/-- **The normal form is multilinear.** -/
theorem boolReduce_isMultilinear (P : DiagPhase n m) : IsMultilinear (boolReduce P) := by
  classical
  intro e he k
  have hsub : (boolReduce P).support ⊆ P.support.biUnion
      fun d => (monomial (boolShadow d) (P.coeff d) : DiagPhase n m).support := by
    unfold boolReduce
    exact MvPolynomial.support_sum
  obtain ⟨d, _, hd⟩ := Finset.mem_biUnion.mp (hsub he)
  by_cases hc : P.coeff d = 0
  · rw [hc, show (monomial (boolShadow d) (0 : ZMod (2 ^ m)) : DiagPhase n m) = 0 from
      LinearMap.map_zero _, MvPolynomial.support_zero] at hd
    exact absurd hd (Finset.notMem_empty _)
  · rw [MvPolynomial.support_monomial, if_neg hc, Finset.mem_singleton] at hd
    rw [hd]
    exact boolShadow_apply_le_one d k

/-- **The normal form does not raise the effective level.** -/
theorem effectiveLevel_boolReduce_le (P : DiagPhase n m) :
    effectiveLevel (boolReduce P) ≤ effectiveLevel P := by
  classical
  unfold boolReduce
  refine (effectiveLevel_finsetSum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro d hd
  refine (effectiveLevel_monomial_le _ _).trans ?_
  have hmono : effLevelMonom m (P.coeff d) (boolShadow d) ≤ effLevelMonom m (P.coeff d) d := by
    unfold effLevelMonom
    exact Nat.add_le_add_left (boolShadow_sum_le d) _
  refine hmono.trans ?_
  unfold effectiveLevel
  exact Finset.le_sup (f := fun e => effLevelMonom m (P.coeff e) e) hd

/-- The coefficient of the normal form at `e` is the sum of the coefficients of the monomials
whose shadow is `e`: the merge, as a formula. -/
theorem coeff_boolReduce (P : DiagPhase n m) (e : Fin n →₀ ℕ) :
    (boolReduce P).coeff e =
      ∑ d ∈ P.support.filter (fun d => boolShadow d = e), P.coeff d := by
  classical
  unfold boolReduce
  rw [MvPolynomial.coeff_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun d _ => by rw [MvPolynomial.coeff_monomial]

/-- The normal form of a nonzero monomial is the monomial at the shadow. -/
lemma boolReduce_monomial {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)} (hc : c ≠ 0) :
    boolReduce (monomial d c : DiagPhase n m) = monomial (boolShadow d) c := by
  classical
  unfold boolReduce
  rw [MvPolynomial.support_monomial, if_neg hc, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

/-- The shadow of a multilinear exponent vector is itself. -/
lemma boolShadow_eq_self_of_le_one {d : Fin n →₀ ℕ} (hd : ∀ k, d k ≤ 1) : boolShadow d = d := by
  classical
  ext k
  rw [boolShadow_apply]
  by_cases hk : k ∈ d.support
  · rw [if_pos hk]
    have h1 := Finsupp.mem_support_iff.mp hk
    have h2 := hd k
    omega
  · rw [if_neg hk]
    exact (Finsupp.notMem_support_iff.mp hk).symm

/-- **The normal form is the identity on multilinear input.** -/
theorem boolReduce_eq_self_of_isMultilinear {P : DiagPhase n m} (hP : IsMultilinear P) :
    boolReduce P = P := by
  classical
  unfold boolReduce
  have h : ∀ d ∈ P.support, (monomial (boolShadow d) (P.coeff d) : DiagPhase n m)
      = monomial d (P.coeff d) := by
    intro d hd
    rw [boolShadow_eq_self_of_le_one (hP d hd)]
  rw [Finset.sum_congr rfl h]
  exact MvPolynomial.support_sum_monomial_coeff P

/-- The normal form is idempotent. -/
theorem boolReduce_idem (P : DiagPhase n m) : boolReduce (boolReduce P) = boolReduce P :=
  boolReduce_eq_self_of_isMultilinear (boolReduce_isMultilinear P)

end FTQCLib.Hierarchy.DiagPhase

namespace FTQCLib.Frame

open FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase

variable {n m : ℕ}

/-- The extended level is bounded by the level of the constant-free part. -/
theorem levelExt_le_effectiveLevel_sub_C (P : DiagPhase n m) :
    levelExt P ≤ effectiveLevel (P - MvPolynomial.C (P.coeff 0)) :=
  effectiveLevel_boolReduce_le _

/-- On a constant-free multilinear exponent the extended level is the level: the strip and the
normal form are identities there. -/
theorem levelExt_eq_effectiveLevel {P : DiagPhase n m} (hP : IsMultilinear P)
    (h0 : P.coeff 0 = 0) : levelExt P = effectiveLevel P := by
  unfold levelExt
  rw [h0, MvPolynomial.C_0, sub_zero, boolReduce_eq_self_of_isMultilinear hP]

/-- **The extended level of a sum** is at most the larger level: constant-stripping and the
Boolean normal form are additive, and `effectiveLevel_add_le` bounds the sum. -/
theorem levelExt_add_le {m : ℕ} (P Q : DiagPhase n m) :
    levelExt (P + Q) ≤ max (levelExt P) (levelExt Q) := by
  unfold levelExt
  have h : (P + Q) - MvPolynomial.C ((P + Q).coeff 0) =
      (P - MvPolynomial.C (P.coeff 0)) + (Q - MvPolynomial.C (Q.coeff 0)) := by
    rw [MvPolynomial.coeff_add, MvPolynomial.C_add]
    ring
  rw [h, DiagPhase.boolReduce_add]
  exact DiagPhase.effectiveLevel_add_le _ _

/-- **A global phase is invisible to the extended level**: the constant is stripped before the
level is read. -/
@[simp] theorem levelExt_add_C {m : ℕ} (P : DiagPhase n m) (c : ZMod (2 ^ m)) :
    levelExt (P + MvPolynomial.C c) = levelExt P := by
  unfold levelExt
  congr 2
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_pos rfl, MvPolynomial.C_add]
  ring

end FTQCLib.Frame

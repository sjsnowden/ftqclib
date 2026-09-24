/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.AJO
import FTQCLib.Codes.AJOOverlap
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi

set_option linter.unusedSectionVars false

/-! # AJO Theorem 1 (uniform-angle case): lattice of trans-logical constraints

This file builds the lattice-constraint extraction infrastructure used in
the proof of `ajo_uniform_dyadic` (the AJO Theorem 1 target stated in
`FTQCLib/Codes/AJOMain.lean`).

## Setup

Fix a CSS code with check matrices `(H_X, H_Z)`. Suppose `θ ∈ ℝ` makes
`f(v) := θ · wt(v)` (the uniform linear-bit phase) trans-logical. By
definition, for every `v ∈ ker(H_Z)` and every `h ∈ row(H_X)`,

  `f(v + h) − f(v) ∈ 2π·ℤ`.

Computing in real arithmetic, with `(v + h)` being F₂ addition (XOR
componentwise),

  `wt(v + h) − wt(v) = wt(h) − 2·wt(v ∧ h)`

where `∧` is bitwise AND (pointwise multiplication in `ZMod 2`). So
the trans-logical constraint is

  `θ · (wt(h) − 2·wt(v ∧ h)) ∈ 2π·ℤ`,

a (linear-in-θ) integer constraint parametrised by `(v, h)`. The full
set of constraints over `v ∈ ker(H_Z), h ∈ row(H_X)` forms a lattice;
this file extracts and organises the basic constraint and its
instantiations.

## What this file proves

* `twoWtAnd v h` — convenience: `2 · wt(v ∧ h)`.
* `transShift h v` — the integer coefficient `wt(h) − 2·wt(v ∧ h)`.
* `wt_add_eq_transShift` — the F₂ identity `(wt(v + h) − wt(v) : ℤ)
  = transShift h v`.
* `isTransversalLogical_uniform_constraint` — for `θ` uniform-linear-
  phase trans-logical, the integer constraint
  `θ · (transShift h v : ℝ) ∈ 2π·ℤ` for all `v ∈ ker(H_Z), h ∈ row(H_X)`.
* `transShift_unit_vec` — instantiation at a unit vector `v = e_j`.
* `transShift_eq_iff_dvd` — equivalent reformulation of
  `θ · (m : ℝ) ∈ 2π·ℤ` for `m ≠ 0` (vacuous when `m = 0`).
* `zero_mem_cssXLogicalCarrier`, `unitVec_mem_cssXLogicalCarrier_of_col_zero`
  — basic membership facts for `ker(H_Z)`.
-/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Hierarchy Matrix Finset

variable {n r_X r_Z : ℕ}

/-! ## Convenience: `2·wt(v ∧ h)` and the shift coefficient `transShift` -/

/-- `2 · wt(v ∧ h)` — the integer coefficient subtracted in the
trans-logical constraint. Bitwise AND is pointwise multiplication in
`ZMod 2`. -/
def twoWtAnd (v h : Fin n → ZMod 2) : ℕ :=
  2 * hammingWeight (fun j => v j * h j)

/-- The integer coefficient `wt(h) − 2·wt(v ∧ h)` appearing in the
uniform-angle trans-logical constraint `θ · (wt(h) − 2·wt(v ∧ h)) ∈
2π·ℤ`. Since the difference can be negative we land in `ℤ`. -/
def transShift (h v : Fin n → ZMod 2) : ℤ :=
  (hammingWeight h : ℤ) - (twoWtAnd v h : ℤ)

/-! ## F₂ bit-by-bit identity for `wt(v + h) − wt(v)`

The core identity:

  `(wt(v + h) − wt(v) : ℤ) = wt(h) − 2·wt(v ∧ h)`.

Per-bit cases (each contribution is `(v + h)_i .val − v_i .val`):

* `(0, 0)`: `0 − 0 = 0`
* `(0, 1)`: `1 − 0 = 1`
* `(1, 0)`: `1 − 1 = 0`
* `(1, 1)`: `0 − 1 = −1`

The contribution depends only on `(v_i, h_i)`. Summing gives the claim.
-/

/-- Per-bit difference between `(a + b).val` and `a.val`, as an
integer: matches `(b).val − 2·(a * b).val`. The right-hand side
collapses to `0` if `b = 0` and to `1 − 2·a.val` (so `±1`) if
`b = 1`. -/
private lemma bit_diff_eq (a b : ZMod 2) :
    ((a + b).val : ℤ) - (a.val : ℤ) =
      (b.val : ℤ) - 2 * ((a * b).val : ℤ) := by
  -- Enumerate the four cases of `(a, b) ∈ (ZMod 2)²`. Rewrite both
  -- `a` and `b` as `((a.val : ℕ) : ZMod 2)`, `((b.val : ℕ) : ZMod 2)`
  -- and let `interval_cases` do the rest.
  have ea : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  have eb : b = ((b.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val b).symm
  have ha : a.val < 2 := ZMod.val_lt a
  have hb : b.val < 2 := ZMod.val_lt b
  rw [ea, eb]
  interval_cases a.val <;> interval_cases b.val <;> decide

/-- The F₂ identity:
`(wt(v + h) − wt(v) : ℤ) = (wt(h) − 2·wt(v ∧ h) : ℤ) = transShift h v`. -/
theorem wt_add_sub_wt_eq_transShift (v h : Fin n → ZMod 2) :
    ((hammingWeight (v + h) : ℤ) - (hammingWeight v : ℤ)) =
      transShift h v := by
  -- Pointwise identity at each bit, lifted to a sum identity.
  have hpt : ∀ i : Fin n,
      (((v + h) i).val : ℤ) - ((v i).val : ℤ) =
        ((h i).val : ℤ) - 2 * (((v i) * (h i)).val : ℤ) := by
    intro i
    have hpt' : (v + h) i = v i + h i := rfl
    rw [hpt']
    exact bit_diff_eq (v i) (h i)
  -- Sum the pointwise identity and unfold both sides.
  have hsum :
      ∑ i, ((((v + h) i).val : ℤ) - ((v i).val : ℤ)) =
        ∑ i, (((h i).val : ℤ) - 2 * (((v i) * (h i)).val : ℤ)) :=
    Finset.sum_congr rfl (fun i _ => hpt i)
  -- Expand the LHS difference of sums.
  rw [Finset.sum_sub_distrib] at hsum
  -- Expand the RHS difference of sums; extract the factor `2` from the
  -- second one.
  have hRHS :
      ∑ i, (((h i).val : ℤ) - 2 * (((v i) * (h i)).val : ℤ)) =
        (∑ i, ((h i).val : ℤ)) -
          2 * (∑ i, (((v i) * (h i)).val : ℤ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hRHS] at hsum
  unfold transShift twoWtAnd hammingWeight
  push_cast
  -- The goal now matches `hsum` up to associativity / commutativity.
  linarith [hsum]

/-! ## Trans-logical constraint, in `transShift` form

The substantive content: under `IsTransversalLogical (linearPhase
(uniform θ))`, the trans-logical condition at `(v, h)` is the integer
constraint `θ · (transShift h v : ℝ) ∈ 2π·ℤ`. -/

/-- The uniform linear-phase pattern `f(v) = θ · wt(v)`:
`linearPhase (fun _ => θ) v = θ · ∑ᵢ (v i).val = θ · wt(v)`. -/
private lemma linearPhase_uniform_apply (θ : ℝ) (v : Fin n → ZMod 2) :
    linearPhase (fun _ : Fin n => θ) v = θ * (hammingWeight v : ℝ) := by
  unfold linearPhase hammingWeight
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Trans-logical constraint, uniform-angle case.** If `θ` makes the
uniform linear phase `f(v) = θ · wt(v)` trans-logical on `(H_X, H_Z)`,
then for every `v ∈ ker(H_Z)` and every `h ∈ row(H_X)`, the integer
shift `transShift h v` is a `2π/θ`-multiple of `1`:

  `θ · (transShift h v : ℝ) ∈ 2π·ℤ`. -/
theorem isTransversalLogical_uniform_constraint
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                  (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ, θ * (transShift h v : ℝ) = 2 * Real.pi * (k : ℝ) := by
  obtain ⟨k, hk⟩ := h_trans v hv h hh
  refine ⟨k, ?_⟩
  -- Rewrite the LHS of `hk` using `linearPhase_uniform_apply`.
  rw [linearPhase_uniform_apply, linearPhase_uniform_apply] at hk
  -- `hk : θ * wt(v + h) − θ * wt(v) = 2π · k`. Convert to
  -- `θ * (wt(v + h) − wt(v)) = 2π · k`.
  have hfact : θ * ((hammingWeight (v + h) : ℝ) - (hammingWeight v : ℝ)) =
      2 * Real.pi * (k : ℝ) := by linarith [hk]
  -- Rewrite the difference using `wt_add_sub_wt_eq_transShift`.
  have hshift := wt_add_sub_wt_eq_transShift v h
  -- `hshift : (wt(v + h) : ℤ) − (wt(v) : ℤ) = transShift h v`.
  have hcast : ((hammingWeight (v + h) : ℝ) - (hammingWeight v : ℝ)) =
      ((transShift h v : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hshift
    push_cast at this
    linarith [this]
  rw [hcast] at hfact
  exact hfact

/-! ## Equivalent formulation: `θ` lies in the lattice `(2π / m)·ℤ`

For `m ≠ 0`, the integer constraint `θ · m ∈ 2π·ℤ` is equivalent to
`θ ∈ (2π / m)·ℤ`. For `m = 0` the constraint is vacuous. -/

/-- **Lattice equivalence (non-zero `m`).** When `m ≠ 0`,
`(∃ k : ℤ, θ · m = 2π·k) ↔ θ ∈ {2π · (k / m) | k : ℤ}`. -/
theorem transShift_eq_iff_dvd {θ : ℝ} {m : ℝ} (hm : m ≠ 0) :
    (∃ k : ℤ, θ * m = 2 * Real.pi * (k : ℝ)) ↔
      ∃ k : ℤ, θ = 2 * Real.pi * (k : ℝ) / m := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp
    linarith [hk]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    field_simp

/-- **Vacuous case (`m = 0`).** When `m = 0`, the constraint `θ · m =
2π · k` collapses to `k = 0` regardless of `θ`. So the only information
extracted is that `0 = 2π·0`, which is trivially true. -/
theorem transShift_eq_zero_vacuous (θ : ℝ) :
    ∃ k : ℤ, θ * (0 : ℝ) = 2 * Real.pi * (k : ℝ) :=
  ⟨0, by ring⟩

/-! ## Unit-vector instantiation

For `j : Fin n` such that the `j`-th column of `H_Z` is zero, the unit
vector `e_j = Pi.single j 1` lies in `ker(H_Z)`. Trans-logical at this
`v` gives a clean constraint. -/

/-- The zero vector is in `ker(H_Z)`. -/
theorem zero_mem_cssXLogicalCarrier
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    (0 : Fin n → ZMod 2) ∈ cssXLogicalCarrier H_Z :=
  Submodule.zero_mem _

/-- If column `j` of `H_Z` is zero (i.e., `H_Z i j = 0` for all `i`),
then the unit vector `Pi.single j 1` lies in `ker(H_Z)`. -/
theorem unitVec_mem_cssXLogicalCarrier_of_col_zero
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (j : Fin n)
    (hcol : ∀ i : Fin r_Z, H_Z i j = 0) :
    (Pi.single j 1 : Fin n → ZMod 2) ∈ cssXLogicalCarrier H_Z := by
  -- Unfold `cssXLogicalCarrier` to `LinearMap.ker (mulVecLin H_Z)` and
  -- check that `H_Z *ᵥ Pi.single j 1 = 0`.
  change Matrix.mulVecLin H_Z (Pi.single j 1) = 0
  rw [Matrix.mulVecLin_apply]
  -- `H_Z *ᵥ Pi.single j 1 = column_j(H_Z)`. We show this column is zero.
  funext i
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_def, Matrix.transpose_apply, Pi.zero_apply]
  exact hcol i

/-! ### `transShift` on a unit vector

For `v = Pi.single j 1`, `(v ∧ h) = h_j · Pi.single j 1`, so
`wt(v ∧ h) = (h j).val`. Hence
`transShift h (Pi.single j 1) = wt(h) − 2·(h j).val`. -/

/-- Pointwise: `(Pi.single j 1) i * h i = (if i = j then h j else 0)`. -/
private lemma pi_single_mul_apply (j : Fin n) (h : Fin n → ZMod 2)
    (i : Fin n) :
    (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i * h i =
      (if i = j then h j else (0 : ZMod 2)) := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Pi.single_eq_same, one_mul]
  · rw [if_neg hij, Pi.single_eq_of_ne hij, zero_mul]

/-- The Hamming weight of `(Pi.single j 1) ∧ h` equals `(h j).val`. -/
private lemma hammingWeight_single_and (j : Fin n) (h : Fin n → ZMod 2) :
    hammingWeight
        (fun i => (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i * h i) =
      (h j).val := by
  unfold hammingWeight
  rw [Finset.sum_eq_single j]
  · -- Main case: `i = j`. The summand is `((Pi.single j 1) j * h j).val =
    -- (1 * h j).val = (h j).val`.
    change ((Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) j * h j).val = (h j).val
    rw [pi_single_mul_apply j h j, if_pos rfl]
  · -- Off-diagonal: `i ≠ j`. The summand is `0`.
    intros i _ hij
    change ((Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) i * h i).val = 0
    rw [pi_single_mul_apply j h i, if_neg hij, ZMod.val_zero]
  · -- `j ∈ univ`.
    intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **Unit-vector specialisation of `transShift`.** With `v = e_j`,
`transShift h (Pi.single j 1) = wt(h) − 2·(h j).val`. -/
theorem transShift_unit_vec (j : Fin n) (h : Fin n → ZMod 2) :
    transShift h (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) =
      (hammingWeight h : ℤ) - 2 * ((h j).val : ℤ) := by
  unfold transShift twoWtAnd
  rw [hammingWeight_single_and]
  push_cast
  ring

/-- **Trans-logical constraint, unit-vector specialisation.** For `j`
with column `j` of `H_Z` zero and `h ∈ row(H_X)`,
`θ · (wt(h) − 2·(h j).val) ∈ 2π·ℤ`. -/
theorem isTransversalLogical_uniform_unit_vec_constraint
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                  (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (j : Fin n) (hcol : ∀ i : Fin r_Z, H_Z i j = 0)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ,
      θ * (((hammingWeight h : ℤ) - 2 * ((h j).val : ℤ)) : ℝ) =
        2 * Real.pi * (k : ℝ) := by
  have hmem := unitVec_mem_cssXLogicalCarrier_of_col_zero H_Z j hcol
  obtain ⟨k, hk⟩ :=
    isTransversalLogical_uniform_constraint h_trans hmem hh
  refine ⟨k, ?_⟩
  rw [transShift_unit_vec] at hk
  push_cast at hk ⊢
  linarith [hk]

/-! ## Zero-vector instantiation

At `v = 0`, the constraint reduces to `θ · wt(h) ∈ 2π·ℤ` for all
`h ∈ row(H_X)`. -/

/-- `transShift h 0 = wt(h)`: `0 ∧ h = 0`, so `2·wt(0 ∧ h) = 0`. -/
theorem transShift_zero (h : Fin n → ZMod 2) :
    transShift h (0 : Fin n → ZMod 2) = (hammingWeight h : ℤ) := by
  unfold transShift twoWtAnd
  have : (fun j : Fin n => (0 : Fin n → ZMod 2) j * h j) = 0 := by
    funext j
    simp
  rw [this, hammingWeight_zero]
  push_cast
  ring

/-- **Trans-logical constraint at `v = 0`.** For every `h ∈ row(H_X)`,
`θ · wt(h) ∈ 2π·ℤ`. -/
theorem isTransversalLogical_uniform_zero_constraint
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                  (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ, θ * (hammingWeight h : ℝ) = 2 * Real.pi * (k : ℝ) := by
  have h0 : (0 : Fin n → ZMod 2) ∈ cssXLogicalCarrier H_Z :=
    zero_mem_cssXLogicalCarrier H_Z
  obtain ⟨k, hk⟩ :=
    isTransversalLogical_uniform_constraint h_trans h0 hh
  refine ⟨k, ?_⟩
  rw [transShift_zero] at hk
  push_cast at hk
  exact hk

/-! ## Generator-pair and logical instantiations

The two further specialisations: `v = g_i` (an X-stabilizer generator,
in `row(H_X) ⊆ ker(H_Z)` by CSS commutativity) and `v = g_L` (a
non-trivial logical X). -/

/-- For any `v, h : Fin n → ZMod 2`,
`transShift h v = wt(h) − 2·wt(v ∧ h)`. Tautological unfolding. -/
theorem transShift_eq (h v : Fin n → ZMod 2) :
    transShift h v =
      (hammingWeight h : ℤ) -
        2 * (hammingWeight (fun j => v j * h j) : ℤ) := by
  unfold transShift twoWtAnd
  push_cast
  ring

/-- **Trans-logical constraint at a generator pair.** If `v ∈ row(H_X)`
(hence in `ker(H_Z)` by CSS commutativity), then for every
`h ∈ row(H_X)`, `θ · (wt(h) − 2·wt(v ∧ h)) ∈ 2π·ℤ`. -/
theorem isTransversalLogical_uniform_generator_constraint
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hCSS : IsCSSPair H_X H_Z)
    (h_trans : IsTransversalLogical
                  (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalSubspace H_X)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ,
      θ * (((hammingWeight h : ℤ) -
              2 * (hammingWeight (fun j => v j * h j) : ℤ)) : ℝ) =
        2 * Real.pi * (k : ℝ) := by
  -- `cssXLogicalSubspace ≤ cssXLogicalCarrier` under CSS commutativity.
  have hv' : v ∈ cssXLogicalCarrier H_Z :=
    cssXLogicalSubspace_le_cssXLogicalCarrier hCSS hv
  obtain ⟨k, hk⟩ :=
    isTransversalLogical_uniform_constraint h_trans hv' hh
  refine ⟨k, ?_⟩
  rw [transShift_eq] at hk
  push_cast at hk ⊢
  linarith [hk]

/-- **Trans-logical constraint at a logical vector.** For `v ∈
ker(H_Z)` (e.g., a non-trivial logical `g_L`) and `h ∈ row(H_X)`,
`θ · (wt(h) − 2·wt(v ∧ h)) ∈ 2π·ℤ`. -/
theorem isTransversalLogical_uniform_logical_constraint
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                  (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ,
      θ * (((hammingWeight h : ℤ) -
              2 * (hammingWeight (fun j => v j * h j) : ℤ)) : ℝ) =
        2 * Real.pi * (k : ℝ) := by
  obtain ⟨k, hk⟩ :=
    isTransversalLogical_uniform_constraint h_trans hv hh
  refine ⟨k, ?_⟩
  rw [transShift_eq] at hk
  push_cast at hk ⊢
  linarith [hk]

/-! ## Status

This file extracts the basic integer-linear constraint
`θ · (wt(h) − 2·wt(v ∧ h)) ∈ 2π·ℤ` produced by
`IsTransversalLogical` at the uniform-linear phase, together with the
zero-vector, unit-vector, generator-pair, and logical specialisations.

The full lattice (intersections of these constraints over all valid
`(v, h)`) determines `θ` up to integer multiples of `2π / d` for some
denominator `d` depending on the code. The dyadic conclusion follows
from showing `d` is a power of two; this is the substantive content of
`ajo_uniform_dyadic`. The lemmas above supply the elementary constraint
extraction step. -/

end FTQCLib.Codes

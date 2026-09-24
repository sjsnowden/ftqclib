/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Defs
import FTQCLib.CSS.Logical
import FTQCLib.Codes.AJO
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi

set_option linter.unusedSectionVars false

/-! # AJO binary-matrix overlap lemma: definitions and structure

The substantive combinatorial content of
`FTQCLib.Codes.AJO.transversalLogical_polyEncodable` is a binary-matrix
"overlap" lemma extracted from pp. 7--8 of arXiv:1408.5547 (Anderson--
Jochym-O'Connor 2014). This file sets up the algebraic vocabulary
needed to state the lemma and proves a handful of structural
properties of the overlap construction. The main lemma is
recorded as a documented target (`AJOOverlapHypothesis`,
`AJOOverlapConclusion`) rather than as a theorem; as stated it has a
residual counterexample at `r = 1`, recorded as `ajo_target_false`.

## Hypothesis: AJO-shape overlap conditions

The hypothesis predicates encode the conditions an iterated application
of `IsTransversalLogical` produces when `f` is the linear-in-bits
phase pattern `f(v) = ∑ᵢ θ · (vᵢ).val` (the uniform case
`θᵢ = θ`).

A direct computation gives, for `v ∈ ker(H_Z)` and `h ∈ row(H_X)`,

    f(v + h) - f(v) = θ · wt(h) - 2θ · wt(v ∧ h).

Iterating trans-logical down the chain `v = 0`, `v = g_1`, `v =
g_1 + g_2`, ..., expanding `wt((g_1 + ... + g_k) ∧ g_{k+1})` by the
inclusion-exclusion identity for the F₂-sum, and inducting on subset
size, gives:

* **Condition (1).** For every non-empty `I ⊆ Fin r`,
  `2^(|I|-1) · θ · wt(overlap g I) ∈ 2π · ℤ`.

  Concretely: at `|I| = 1` (factor `2^0 = 1`),
  `θ · wt(g_i) ∈ 2π · ℤ` for every generator `g_i`; at `|I| = 2`
  (factor `2^1 = 2`), `2θ · wt(g_i ∧ g_j) ∈ 2π · ℤ` for every
  pair; etc.

* **Condition (2).** For every non-empty `J ⊆ Fin r`,
  `2^|J| · θ · wt(g_L ∧ overlap g J) ∈ 2π · ℤ`.

  Concretely: at `|J| = 1` (factor `2^1 = 2`),
  `2θ · wt(g_L ∧ g_i) ∈ 2π · ℤ` for every generator; etc.

  We do **not** impose the `J = ∅` clause `θ · wt(g_L) ∈ 2π · ℤ`.
  That condition does not follow from `IsTransversalLogical` applied
  to a linear-in-bits phase: the trans-logical predicate requires
  `h ∈ row(H_X)`, while `g_L ∉ row(H_X)` by non-triviality, so
  the trans-logical step from `v = 0` with `h = g_L` is not
  available. If we *did* impose `θ · wt(g_L) ∈ 2π · ℤ` we would
  force `wt(g_L) ≡ 0 mod q_o` (with `q_o` the odd part of the
  rotation denominator), neutralising the AJO contradiction that
  uses `wt(g_L) ≢ 0 mod q_o`.

## Non-triviality

The non-triviality of the X-logical sector is encoded by
`g_L ∈ cssXLogicalCarrier H_Z` and `g_L ∉ cssXLogicalSubspace H_X`,
i.e., `g_L ∈ ker(H_Z) \ row(H_X)`. The additional AJO-style
non-triviality `wt(g_L) ≢ 0 mod q_o` is **not** assumed here; it is
content of the conclusion's derivation, where the inductive argument
extracts a residue-nonzero weight from the binary structure of
`g_L` against `H_X`.

## Residual counterexample for `r = 1`

The explicit `r = 1`, `n = 9`, `H_X` = all-ones,
`g_L` weight 3, `θ = 2π/3` configuration **still** satisfies
condition (1) (`θ · 9 = 6π = 2π · 3`) and condition (2) at the
only non-empty `J = {0}` (`2θ · wt(g_L ∧ g_0) = 2θ · 3 = 4π`),
along with the non-triviality, yet `θ / (2π) = 1/3` is non-dyadic.
This reflects a genuine feature of the underlying structure: for the
all-ones X-stabilizer alone, trans-logical at `v = g_L` gives only
`3θ ∈ 2π · ℤ`, which has the non-dyadic solution `θ = 2π/3`. The
corresponding logical action of `Z(2π/3)^⊗9` on the encoded qubit
spanned by `g_L = (1, 1, 1, 0, ...)` is the identity (since
`wt(g_L) · θ = 3 · 2π/3 = 2π ≡ 0 mod 2π`), so AJO Theorem 1
*does* hold operationally — the logical gate is trivially in the
hierarchy — but the *angle* `θ` itself is not dyadic. The
counterexample `ajo_target_false` records this. To force `θ`
dyadic (as opposed to "θ_L dyadic"), one needs either richer
structure than a single all-ones X-stabilizer can supply, or to
weaken the conclusion to "θ · wt(overlap I)" being a dyadic
multiple of `2π` for some non-empty `I`.

## The setup

Fix a CSS code `(H_X, H_Z)` on `n` qubits with `H_X` of shape
`r × n`. Write `g_i = (H_X i) : Fin n → ZMod 2` for the binary
support of the `i`-th X-stabilizer generator (`i : Fin r`). Fix a
non-trivial logical-X vector `g_L : Fin n → ZMod 2` with
`g_L ∈ ker(H_Z)` and `g_L ∉ row(H_X)` (so the code is non-trivial
on the X-logical side).

For a subset `I : Finset (Fin r)`, the *overlap* of the generators
in `I` is the pointwise product

    overlap g I  : Fin n → ZMod 2
    overlap g I  =  fun j => ∏ i ∈ I, g i j

interpreted bitwise: a position `j` lies in `overlap g I` iff every
`g i` with `i ∈ I` contains `j`. By convention the empty product is
`1`, so `overlap g ∅ = (fun _ => 1)` is the all-ones vector. The
*Hamming weight* of a binary vector is the number of positions where
it is non-zero, equivalently the sum of `(v j).val` over `j`.

## Target lemma

> **AJO overlap lemma (target).** Suppose a real angle
> `θ : ℝ` and a row system `g : Fin r → (Fin n → ZMod 2)` together
> with a non-trivial logical `g_L : Fin n → ZMod 2` satisfy the
> *AJO overlap divisibility* conditions:
>
> 1. For every non-empty subset `I ⊆ Fin r`:
>    `2^(|I|-1) · θ · hammingWeight (overlap g I) ∈ 2π · ℤ`.
>
> 2. For every non-empty subset `J ⊆ Fin r`:
>    `2^|J| · θ · hammingWeight (g_L ∧ overlap g J) ∈ 2π · ℤ`.
>
> Together with `g_L ∈ ker(H_Z) \ row(H_X)` and `1 ≤ r`.
>
> Then either `θ` is a dyadic multiple of `2π`, or the logical
> angle `θ_L := θ · wt(g_L) mod 2π` is, equivalently the diagonal
> logical action of the gate is in the Clifford hierarchy.

The intended proof argues by contradiction: assume
`θ / (2π) = p / q` with `q` having an odd prime factor `q_o`.
Iterate the overlap relations along the chain of generators, using
inclusion-exclusion to expand `wt(F₂-sum ∧ g_m)` in terms of overlap
weights, and extract a power-of-two-weight witness that contradicts
non-triviality. The structural lemmas in this file isolate the
elementary steps; the inductive Möbius argument is the next file.

## What this file proves

Structural vocabulary:

* `hammingWeight v` — sum of `(v j).val` over `j : Fin n`.
* `overlap g I` — pointwise product of the binary vectors `g i` for
  `i ∈ I`. Empty product is the all-ones vector.
* `logicalOverlap g_L g I` — pointwise product `g_L · overlap g I`.
* `AJOOverlapHypothesis`, `AJOOverlapConclusion` — the predicates
  for the lemma.

Basic bounds and identities:

* `hammingWeight_zero`, `hammingWeight_one`, `hammingWeight_le_n`.
* `overlap_empty`, `overlap_singleton`, `overlap_insert`.
* `logicalOverlap_empty`, `logicalOverlap_singleton`,
  `logicalOverlap_insert`.
* `hammingWeight_overlap_empty`, `hammingWeight_overlap_singleton`,
  `hammingWeight_logicalOverlap_empty`,
  `hammingWeight_logicalOverlap_singleton`.

`ZMod 2`-specific arithmetic:

* `zmod_two_val_one`, `zmod_two_val_mul`, `zmod_two_val_mul_le_right`.

Pointwise and Hamming-weight monotonicity in the index set:

* `overlap_val_le_of_insert`, `overlap_val_le_of_subset`.
* `hammingWeight_overlap_insert_le`, `hammingWeight_overlap_antitone`.
* `logicalOverlap_val_le_of_insert`, `logicalOverlap_val_le_overlap`.
* `hammingWeight_logicalOverlap_insert_le`,
  `hammingWeight_logicalOverlap_antitone`,
  `hammingWeight_logicalOverlap_le_overlap`,
  `hammingWeight_logicalOverlap_le_gL`.

Conclusion-side reductions (turning a power-of-two weight witness into
the dyadic conclusion):

* `ajoOverlapConclusion_of_theta_zero`,
  `ajoOverlapConclusion_of_intMul_2pi`,
  `ajoOverlapConclusion_of_pi_dyadic`.
* `ajoOverlapConclusion_of_pow_two`,
  `ajoOverlapConclusion_of_pow_two_half`,
  `ajoOverlapConclusion_of_pow_two_general`.

Hypothesis-side extractions and lucky-generator reductions:

* `AJOOverlapHypothesis.singleton_pi_int`,
  `AJOOverlapHypothesis.singleton_logical_pi_int`.
* `AJOOverlapHypothesis.r_pos`,
  `AJOOverlapHypothesis.gL_mem_carrier`,
  `AJOOverlapHypothesis.gL_not_mem_subspace`,
  `AJOOverlapHypothesis.gL_ne_zero`.
* `AJOOverlapHypothesis.dyadic_of_overlap_pow_two`,
  `AJOOverlapHypothesis.dyadic_of_logicalOverlap_singleton_pow_two`,
  `AJOOverlapHypothesis.dyadic_of_singleton_weight_one`,
  `AJOOverlapHypothesis.dyadic_of_some_singleton_pow_two`.
* `AJOOverlapHypothesis.dyadic_of_n_zero` — vacuous case.

Integer-coefficient combinations of the divisibility conditions:

* `AJOOverlapHypothesis.singleton_minus_logical`.

## What is *not* proved

The main theorem `ajo_binary_matrix_lemma` itself is not proved here.
The proof requires an inclusion-exclusion-style argument over all
`2^r` subsets of `Fin r`, peeling off bits of `g_L` against the row
support, to derive a contradiction with non-triviality. The reductions
above turn that argument's final extracted power-of-two weight witness
into the dyadic conclusion, but extracting that witness is the
substantive open piece. See AJO 2014 pp. 7--8 for the original
combinatorial argument.

The corner case `r = 0` is explicitly excluded by the `1 ≤ r` clause
of `AJOOverlapHypothesis` (extracted as
`AJOOverlapHypothesis.r_pos`). Without this clause the hypothesis is
too weak to force the conclusion: e.g., `n = 3`, `r = 0`,
`g_L = (1, 1, 1)`, `θ = π/3`. Condition (1) is vacuous (no non-empty
`I ⊆ Fin 0`), condition (2) at `J = ∅` is satisfied because
`2 · (π/3) · 3 = 2π`, and `g_L ≠ 0` so `g_L ∉ row(H_X) = {0}`. But
`θ / (2π) = 1/6` is not dyadic. The standard AJO setting implicitly
assumes `r ≥ 1`. The separate `n = 0` vacuous case is handled by
`dyadic_of_n_zero`.
-/

namespace FTQCLib.Codes

open FTQCLib.CSS Matrix Finset

variable {n r : ℕ}

/-! ## Hamming weight on binary vectors -/

/-- The *Hamming weight* of a binary vector `v : Fin n → ZMod 2`:
the number of coordinates at which `v` is non-zero, computed as the
sum of `(v j).val` over `j`. Since `(v j).val ∈ {0, 1}` this is the
count of non-zero coordinates. -/
def hammingWeight (v : Fin n → ZMod 2) : ℕ := ∑ i, (v i).val

/-- The Hamming weight of the zero vector is zero. -/
@[simp]
theorem hammingWeight_zero :
    hammingWeight (0 : Fin n → ZMod 2) = 0 := by
  unfold hammingWeight
  simp

/-- Each binary coordinate contributes at most `1` to the Hamming
weight, so the total is at most `n`. -/
theorem hammingWeight_le_n (v : Fin n → ZMod 2) :
    hammingWeight v ≤ n := by
  unfold hammingWeight
  -- Each `(v i).val` is a `ZMod 2`-residue, hence `< 2`, hence `≤ 1`.
  have hbound : ∀ i : Fin n, (v i).val ≤ 1 := by
    intro i
    have h : (v i).val < 2 := ZMod.val_lt (v i)
    omega
  calc ∑ i, (v i).val
      ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => hbound i)
    _ = n := by simp

/-! ## The overlap construction

The `m`-fold overlap of a family of binary vectors is the bitwise AND
of the family, equivalently the pointwise product in `ZMod 2`. Empty
product is the all-ones vector. -/

/-- The *overlap* of a family of binary vectors `g : Fin r →
(Fin n → ZMod 2)` indexed by a subset `I : Finset (Fin r)`: the
pointwise product `j ↦ ∏ i ∈ I, g i j`. By the convention
`∏ i ∈ ∅, _ = 1` this is the all-ones vector on `I = ∅`. -/
def overlap (g : Fin r → (Fin n → ZMod 2)) (I : Finset (Fin r)) :
    Fin n → ZMod 2 :=
  fun j => ∏ i ∈ I, g i j

/-- The overlap over the empty index set is the all-ones vector. -/
@[simp]
theorem overlap_empty (g : Fin r → (Fin n → ZMod 2)) :
    overlap g (∅ : Finset (Fin r)) = (fun _ : Fin n => 1) := by
  funext j
  unfold overlap
  exact Finset.prod_empty

/-- The overlap over a singleton index set `{i}` is the single
generator `g i`. -/
@[simp]
theorem overlap_singleton (g : Fin r → (Fin n → ZMod 2)) (i : Fin r) :
    overlap g ({i} : Finset (Fin r)) = g i := by
  funext j
  unfold overlap
  rw [Finset.prod_singleton]

/-- Inserting a new index into an overlap multiplies pointwise by the
new generator: `overlap g (insert i I) = g i * overlap g I` when
`i ∉ I`. -/
theorem overlap_insert (g : Fin r → (Fin n → ZMod 2))
    {i : Fin r} {I : Finset (Fin r)} (hi : i ∉ I) :
    overlap g (insert i I) = fun j => g i j * overlap g I j := by
  funext j
  unfold overlap
  exact Finset.prod_insert hi

/-- The Hamming weight of any overlap is bounded by `n`. This is the
trivial bound; the substantive content of the AJO lemma exploits the
finer structure of how `hammingWeight (overlap g I)` varies with `I`. -/
theorem hammingWeight_overlap_le_n
    (g : Fin r → (Fin n → ZMod 2)) (I : Finset (Fin r)) :
    hammingWeight (overlap g I) ≤ n :=
  hammingWeight_le_n _

/-- Pointwise product of `g_L` with an overlap, written as a binary
vector. This is the binary AND of `g_L` with the overlap of `g` over
`I`, appearing in condition (2) of the AJO overlap lemma. -/
def logicalOverlap (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    (I : Finset (Fin r)) : Fin n → ZMod 2 :=
  fun j => g_L j * overlap g I j

/-- The logical overlap on the empty index set reduces to `g_L`
itself, since the empty overlap is the all-ones vector. -/
@[simp]
theorem logicalOverlap_empty
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2)) :
    logicalOverlap g_L g (∅ : Finset (Fin r)) = g_L := by
  funext j
  unfold logicalOverlap
  rw [overlap_empty]
  ring

/-- The logical overlap on a singleton `{i}` is the bitwise product
of `g_L` with `g i`. -/
@[simp]
theorem logicalOverlap_singleton
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2)) (i : Fin r) :
    logicalOverlap g_L g ({i} : Finset (Fin r)) =
      fun j => g_L j * g i j := by
  funext j
  unfold logicalOverlap
  rw [overlap_singleton]

/-- The Hamming weight of a logical overlap is bounded by `n`. -/
theorem hammingWeight_logicalOverlap_le_n
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    (I : Finset (Fin r)) :
    hammingWeight (logicalOverlap g_L g I) ≤ n :=
  hammingWeight_le_n _

/-- Inserting a new index into a logical overlap multiplies pointwise
by the new generator. -/
theorem logicalOverlap_insert
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    {i : Fin r} {I : Finset (Fin r)} (hi : i ∉ I) :
    logicalOverlap g_L g (insert i I) =
      fun j => g i j * logicalOverlap g_L g I j := by
  funext j
  unfold logicalOverlap
  rw [overlap_insert g hi]
  ring

/-! ## Hamming weight of distinguished overlaps

The Hamming weight of the all-ones vector is `n`, of the zero vector is
`0`, and the Hamming weight of `logicalOverlap g_L g ∅` is just the
weight of `g_L` itself. -/

/-- A `ZMod 2` element with `val = 0` is `0`. -/
theorem zmod_two_eq_zero_of_val_zero {a : ZMod 2} (h : a.val = 0) : a = 0 :=
  (ZMod.val_eq_zero a).mp h

/-- Every `ZMod 2` element has `val` equal to either `0` or `1`. -/
theorem zmod_two_val_lt_two (a : ZMod 2) : a.val < 2 := ZMod.val_lt a

/-- `(1 : ZMod 2).val = 1`. -/
@[simp]
theorem zmod_two_val_one : ((1 : ZMod 2).val : ℕ) = 1 := by
  haveI : Fact (1 < 2) := ⟨one_lt_two⟩
  exact ZMod.val_one 2

/-- In `ZMod 2`, the `val` of a product is the product of the `val`s,
without the `% n` correction, because both factors have `val ∈ {0, 1}`
so the product is also at most `1`. -/
theorem zmod_two_val_mul (a b : ZMod 2) : (a * b).val = a.val * b.val := by
  rw [ZMod.val_mul]
  -- Each `val` is `< 2`, hence `≤ 1`, so their product is `≤ 1 < 2`.
  have ha : a.val < 2 := ZMod.val_lt a
  have hb : b.val < 2 := ZMod.val_lt b
  have : a.val * b.val < 2 := by
    interval_cases a.val <;> interval_cases b.val <;> decide
  exact Nat.mod_eq_of_lt this

/-- In `ZMod 2`, multiplication is monotone in the `val`: `(a * b).val
≤ b.val`. This is the binary AND-monotone bound. -/
theorem zmod_two_val_mul_le_right (a b : ZMod 2) : (a * b).val ≤ b.val := by
  rw [zmod_two_val_mul]
  have ha : a.val < 2 := ZMod.val_lt a
  interval_cases a.val <;> simp

/-- The Hamming weight of the all-ones vector is `n`. -/
@[simp]
theorem hammingWeight_one :
    hammingWeight (fun _ : Fin n => (1 : ZMod 2)) = n := by
  unfold hammingWeight
  simp [zmod_two_val_one]

/-- The Hamming weight of `overlap g ∅` is `n` (the all-ones vector). -/
@[simp]
theorem hammingWeight_overlap_empty (g : Fin r → (Fin n → ZMod 2)) :
    hammingWeight (overlap g (∅ : Finset (Fin r))) = n := by
  rw [overlap_empty]
  exact hammingWeight_one

/-- The Hamming weight of `logicalOverlap g_L g ∅` equals the Hamming
weight of `g_L`. -/
@[simp]
theorem hammingWeight_logicalOverlap_empty
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2)) :
    hammingWeight (logicalOverlap g_L g (∅ : Finset (Fin r))) =
      hammingWeight g_L := by
  rw [logicalOverlap_empty]

/-- The Hamming weight of `logicalOverlap g_L g {i}` equals the Hamming
weight of the pointwise product `g_L * g i`. -/
@[simp]
theorem hammingWeight_logicalOverlap_singleton
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2)) (i : Fin r) :
    hammingWeight (logicalOverlap g_L g ({i} : Finset (Fin r))) =
      hammingWeight (fun j => g_L j * g i j) := by
  rw [logicalOverlap_singleton]

/-- The Hamming weight of `overlap g {i}` equals the Hamming weight of
generator `g i`. -/
@[simp]
theorem hammingWeight_overlap_singleton
    (g : Fin r → (Fin n → ZMod 2)) (i : Fin r) :
    hammingWeight (overlap g ({i} : Finset (Fin r))) = hammingWeight (g i) := by
  rw [overlap_singleton]

/-- Inserting an extra generator into the overlap (when `i ∉ I`) can
only decrease the Hamming weight pointwise:
`(overlap g (insert i I) j).val ≤ (overlap g I j).val`. -/
theorem overlap_val_le_of_insert
    (g : Fin r → (Fin n → ZMod 2))
    {i : Fin r} {I : Finset (Fin r)} (hi : i ∉ I) (j : Fin n) :
    (overlap g (insert i I) j).val ≤ (overlap g I j).val := by
  rw [overlap_insert g hi]
  exact zmod_two_val_mul_le_right (g i j) (overlap g I j)

/-- Inserting an extra generator into the overlap (when `i ∉ I`) can
only decrease the Hamming weight:
`hammingWeight (overlap g (insert i I)) ≤ hammingWeight (overlap g I)`. -/
theorem hammingWeight_overlap_insert_le
    (g : Fin r → (Fin n → ZMod 2))
    {i : Fin r} {I : Finset (Fin r)} (hi : i ∉ I) :
    hammingWeight (overlap g (insert i I)) ≤ hammingWeight (overlap g I) := by
  unfold hammingWeight
  exact Finset.sum_le_sum (fun j _ => overlap_val_le_of_insert g hi j)

/-- Inserting an extra generator into the logical overlap (when `i ∉ I`)
can only decrease the Hamming weight pointwise. -/
theorem logicalOverlap_val_le_of_insert
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    {i : Fin r} {I : Finset (Fin r)} (hi : i ∉ I) (j : Fin n) :
    (logicalOverlap g_L g (insert i I) j).val ≤ (logicalOverlap g_L g I j).val := by
  rw [logicalOverlap_insert g_L g hi]
  -- Goal: `(g i j * logicalOverlap g_L g I j).val ≤ (logicalOverlap g_L g I j).val`.
  exact zmod_two_val_mul_le_right (g i j) (logicalOverlap g_L g I j)

/-- Inserting an extra generator into the logical overlap can only
decrease the Hamming weight. -/
theorem hammingWeight_logicalOverlap_insert_le
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    {i : Fin r} {I : Finset (Fin r)} (hi : i ∉ I) :
    hammingWeight (logicalOverlap g_L g (insert i I)) ≤
      hammingWeight (logicalOverlap g_L g I) := by
  unfold hammingWeight
  exact Finset.sum_le_sum (fun j _ => logicalOverlap_val_le_of_insert g_L g hi j)

/-- The logical overlap is dominated pointwise by the overlap itself:
`(logicalOverlap g_L g I j).val ≤ (overlap g I j).val`. -/
theorem logicalOverlap_val_le_overlap
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    (I : Finset (Fin r)) (j : Fin n) :
    (logicalOverlap g_L g I j).val ≤ (overlap g I j).val := by
  unfold logicalOverlap
  -- Goal: `(g_L j * overlap g I j).val ≤ (overlap g I j).val`.
  exact zmod_two_val_mul_le_right (g_L j) (overlap g I j)

/-- The Hamming weight of the logical overlap is bounded by the Hamming
weight of the plain overlap. -/
theorem hammingWeight_logicalOverlap_le_overlap
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    (I : Finset (Fin r)) :
    hammingWeight (logicalOverlap g_L g I) ≤ hammingWeight (overlap g I) := by
  unfold hammingWeight
  exact Finset.sum_le_sum (fun j _ => logicalOverlap_val_le_overlap g_L g I j)

/-- The Hamming weight of the logical overlap is bounded by the Hamming
weight of `g_L`. By symmetry of multiplication, both pointwise factors
of `logicalOverlap g_L g I = g_L * overlap g I` bound the product. -/
theorem hammingWeight_logicalOverlap_le_gL
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    (I : Finset (Fin r)) :
    hammingWeight (logicalOverlap g_L g I) ≤ hammingWeight g_L := by
  unfold hammingWeight
  refine Finset.sum_le_sum (fun j _ => ?_)
  -- `(g_L j * overlap g I j).val ≤ (g_L j).val`.
  unfold logicalOverlap
  rw [mul_comm]
  exact zmod_two_val_mul_le_right (overlap g I j) (g_L j)

/-- Pointwise monotonicity of `overlap`: if `J ⊆ I` then
`(overlap g I j).val ≤ (overlap g J j).val`. This generalises
`overlap_val_le_of_insert`. -/
theorem overlap_val_le_of_subset
    (g : Fin r → (Fin n → ZMod 2))
    {J I : Finset (Fin r)} (hJI : J ⊆ I) (j : Fin n) :
    (overlap g I j).val ≤ (overlap g J j).val := by
  classical
  -- Reduce to the case `I = D ∪ J` with `D` arbitrary disjoint from `J`,
  -- then induct on `D`.
  suffices h : ∀ D : Finset (Fin r), (overlap g (D ∪ J) j).val ≤ (overlap g J j).val by
    have hI : I = (I \ J) ∪ J := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hi; by_cases hij : i ∈ J <;> tauto
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact hJI h
    rw [hI]
    exact h (I \ J)
  intro D
  induction D using Finset.induction_on with
  | empty => simp [Finset.empty_union]
  | insert i D' hi ih =>
    by_cases hiJ : i ∈ J
    · -- `insert i D' ∪ J = D' ∪ J`.
      have hunion : (insert i D') ∪ J = D' ∪ J := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ((rfl | h) | h)
          · exact Or.inr hiJ
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      rw [hunion]
      exact ih
    · -- `i ∉ D' ∪ J`, so `(insert i D') ∪ J = insert i (D' ∪ J)`.
      have hi' : i ∉ D' ∪ J := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hi, hiJ⟩
      have hunion : (insert i D') ∪ J = insert i (D' ∪ J) := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      rw [hunion]
      calc (overlap g (insert i (D' ∪ J)) j).val
          ≤ (overlap g (D' ∪ J) j).val := overlap_val_le_of_insert g hi' j
        _ ≤ (overlap g J j).val := ih

/-- Hamming-weight version of overlap monotonicity:
`J ⊆ I → wt(overlap g I) ≤ wt(overlap g J)`. -/
theorem hammingWeight_overlap_antitone
    (g : Fin r → (Fin n → ZMod 2))
    {J I : Finset (Fin r)} (hJI : J ⊆ I) :
    hammingWeight (overlap g I) ≤ hammingWeight (overlap g J) := by
  unfold hammingWeight
  exact Finset.sum_le_sum (fun j _ => overlap_val_le_of_subset g hJI j)

/-- Hamming-weight version of logical-overlap monotonicity:
`J ⊆ I → wt(logicalOverlap g_L g I) ≤ wt(logicalOverlap g_L g J)`. -/
theorem hammingWeight_logicalOverlap_antitone
    (g_L : Fin n → ZMod 2) (g : Fin r → (Fin n → ZMod 2))
    {J I : Finset (Fin r)} (hJI : J ⊆ I) :
    hammingWeight (logicalOverlap g_L g I) ≤
      hammingWeight (logicalOverlap g_L g J) := by
  unfold hammingWeight
  refine Finset.sum_le_sum (fun j _ => ?_)
  unfold logicalOverlap
  rw [zmod_two_val_mul, zmod_two_val_mul]
  exact Nat.mul_le_mul_left _ (overlap_val_le_of_subset g hJI j)

/-! ## Target statement: AJO binary-matrix overlap lemma

The lemma below is documented as the target. Its hypothesis and
conclusion are recorded as `def`s of `Prop` type rather than as a
theorem; as stated the target is refuted by `ajo_target_false` below.

The target asserts: if `θ ∈ ℝ` and a generator system `g` together
with a non-trivial logical `g_L` satisfy

  (1) for every non-empty `I ⊆ Fin r`:
      `2^(|I|-1) · θ · hammingWeight (overlap g I)`
        is an integer multiple of `2π`;
  (2) for every non-empty `J ⊆ Fin r`:
      `2^|J| · θ · hammingWeight (logicalOverlap g_L g J)`
        is an integer multiple of `2π`;

then `θ / (2π)` is dyadic, i.e., `θ = 2π · a / 2^N` for some `a : ℤ`,
`N : ℕ`. This is the substantive combinatorial content of
`transversalLogical_polyEncodable` in the CSS case (AJO 2014
Theorem 1, pp. 7--8).
-/

/-- The hypothesis of the AJO overlap lemma, packaged as a `Prop`.
This bundles conditions (1) and (2) above, the non-triviality of `g_L`
modulo `row(H_X)`, and the existence of at least one X-stabilizer
generator (`r ≥ 1`).

The `1 ≤ r` clause rules out the `r = 0` corner case in which `H_X` is
the empty `0 × n` matrix and `row(H_X) = {0}`. Without it both
conditions are vacuous (no non-empty subsets of `Fin 0`), and the
hypothesis collapses to `g_L ≠ 0`, which carries no information about
`θ`. Explicit counterexample for `r = 0`: `n = 3`, `g_L = (1, 1, 1)`,
any non-dyadic `θ`; the hypothesis holds trivially while the
conclusion fails. AJO 2014 Section III.A implicitly assumes the code
has at least one X-stabilizer generator; we encode that explicitly
here.

The factor `2^(|I|-1)` on condition (1) and `2^|J|` on condition (2)
matches AJO 2014 Eq (6). Both conditions are restricted to *non-empty*
subsets — the `J = ∅` case would amount to `θ · wt(g_L) ∈ 2π · ℤ`,
which is not derivable from `IsTransversalLogical` since `g_L ∉
row(H_X)`. -/
def AJOOverlapHypothesis
    (H_X : Matrix (Fin r) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r) (Fin n) (ZMod 2))
    (g_L : Fin n → ZMod 2) (θ : ℝ) : Prop :=
  -- The code has at least one X-stabilizer generator.
  1 ≤ r ∧
  -- The logical is non-trivial: in `ker(H_Z) \ row(H_X)`.
  g_L ∈ cssXLogicalCarrier H_Z ∧
  g_L ∉ cssXLogicalSubspace H_X ∧
  -- (1) Overlap divisibility for non-empty subsets of generators,
  --     with the AJO factor `2^(|I|-1)`.
  (∀ I : Finset (Fin r), I.Nonempty →
    ∃ k : ℤ,
      (2 ^ (I.card - 1) : ℝ) * θ *
          (hammingWeight (overlap (fun i => H_X i) I) : ℝ) =
        2 * Real.pi * k) ∧
  -- (2) Logical-overlap divisibility through `g_L`, with the AJO
  --     factor `2^|J|`, for non-empty `J`.
  (∀ J : Finset (Fin r), J.Nonempty →
    ∃ k : ℤ,
      (2 ^ J.card : ℝ) * θ *
          (hammingWeight (logicalOverlap g_L (fun i => H_X i) J) : ℝ) =
        2 * Real.pi * k)

/-- The conclusion of the AJO overlap lemma: `θ / (2π)` is a dyadic
rational, i.e., `θ = 2π · a / 2^N` for some `a : ℤ` and `N : ℕ`. -/
def AJOOverlapConclusion (θ : ℝ) : Prop :=
  ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / (2 ^ N : ℝ)

/-! ## Boundary cases for the AJO conclusion

These supply the dyadic conclusion in concrete easy cases that the full
combinatorial argument reduces to. -/

/-- If `θ = 0` then `θ / (2π)` is trivially dyadic with `a = 0`, `N = 0`. -/
theorem ajoOverlapConclusion_of_theta_zero :
    AJOOverlapConclusion (0 : ℝ) :=
  ⟨0, 0, by norm_num⟩

/-- If `θ = 2π · k` for some integer `k` then the conclusion holds with
`N = 0`. -/
theorem ajoOverlapConclusion_of_intMul_2pi (k : ℤ) :
    AJOOverlapConclusion (2 * Real.pi * (k : ℝ)) :=
  ⟨k, 0, by simp⟩

/-- If `θ = 2π · k / 2^N` for some integer `k` and natural `N` then the
conclusion holds. This is the conclusion's definitional unfolding. -/
theorem ajoOverlapConclusion_of_pi_dyadic (k : ℤ) (N : ℕ) :
    AJOOverlapConclusion (2 * Real.pi * (k : ℝ) / (2 ^ N : ℝ)) :=
  ⟨k, N, rfl⟩

/-! ## Extracting individual relations from `AJOOverlapHypothesis`

These project out specialisations of the hypothesis that are repeatedly
used in the inductive step of the AJO argument. -/

/-- Specialisation of condition (1) to the singleton subset `{i}`: the
angle times the Hamming weight of generator `g_i` is an integer multiple
of `2π`. The factor `2^(|{i}|-1) = 2^0 = 1` is trivial. -/
theorem AJOOverlapHypothesis.singleton_pi_int
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) (i : Fin r) :
    ∃ k : ℤ, θ * (hammingWeight (fun j => H_X i j) : ℝ) = 2 * Real.pi * k := by
  obtain ⟨_, _, _, h1, _⟩ := hyp
  have hres := h1 ({i} : Finset (Fin r)) (Finset.singleton_nonempty i)
  -- `overlap (fun i => H_X i) {i} = H_X i`, so the Hamming weight is `hammingWeight (H_X i)`.
  rw [hammingWeight_overlap_singleton] at hres
  -- The card of `{i}` is `1`, so `2^(1 - 1) = 2^0 = 1`.
  obtain ⟨k, hk⟩ := hres
  refine ⟨k, ?_⟩
  have hcard : ({i} : Finset (Fin r)).card = 1 := Finset.card_singleton i
  rw [hcard] at hk
  simpa using hk

/-- Specialisation of condition (2) to the singleton subset `{i}`:
`2θ · wt(g_L ∧ H_X i)` is an integer multiple of `2π`. The factor
`2^|{i}| = 2^1 = 2`. -/
theorem AJOOverlapHypothesis.singleton_logical_pi_int
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) (i : Fin r) :
    ∃ k : ℤ,
      2 * θ * (hammingWeight (fun j => g_L j * H_X i j) : ℝ) =
        2 * Real.pi * k := by
  obtain ⟨_, _, _, _, h2⟩ := hyp
  have hres := h2 ({i} : Finset (Fin r)) (Finset.singleton_nonempty i)
  rw [hammingWeight_logicalOverlap_singleton] at hres
  -- `2^|{i}| = 2^1 = 2`.
  obtain ⟨k, hk⟩ := hres
  refine ⟨k, ?_⟩
  have hcard : ({i} : Finset (Fin r)).card = 1 := Finset.card_singleton i
  rw [hcard] at hk
  simpa [pow_one] using hk

/-- The generator-count clause: the code has at least one X-stabilizer
generator. -/
theorem AJOOverlapHypothesis.r_pos
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) :
    1 ≤ r := hyp.1

/-- The non-triviality clause: `g_L` is in `ker(H_Z)`. -/
theorem AJOOverlapHypothesis.gL_mem_carrier
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) :
    g_L ∈ cssXLogicalCarrier H_Z := hyp.2.1

/-- The non-triviality clause: `g_L` is *not* in `row(H_X)`. -/
theorem AJOOverlapHypothesis.gL_not_mem_subspace
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) :
    g_L ∉ cssXLogicalSubspace H_X := hyp.2.2.1

/-- The non-triviality of `g_L` in `ker(H_Z) \ row(H_X)` forces `g_L ≠ 0`
because `0 ∈ row(H_X)`. -/
theorem AJOOverlapHypothesis.gL_ne_zero
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) : g_L ≠ 0 := by
  intro h
  exact hyp.gL_not_mem_subspace (h ▸ Submodule.zero_mem _)

/-! ## Dyadic-weight reductions

These lemmas give the AJO conclusion in the case where one of the
hypothesis-supplied integer multiples is over a power-of-two weight.
The full AJO argument extracts a power-of-two weight from the combined
overlap conditions; the proofs below absorb the easier arithmetic step
of taking that weight to the dyadic conclusion. -/

/-- **Dyadic-weight reduction (condition (1) shape).** If
`θ · m = 2π · k` with `m = 2^N` a power of `2`, then `θ` is dyadic. -/
theorem ajoOverlapConclusion_of_pow_two
    {θ : ℝ} {N : ℕ} {k : ℤ}
    (h : θ * ((2 ^ N : ℕ) : ℝ) = 2 * Real.pi * k) :
    AJOOverlapConclusion θ := by
  refine ⟨k, N, ?_⟩
  have hpow : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; ring
  rw [hpow] at h
  have hne' : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp
  linarith [h]

/-- **Dyadic-weight reduction (condition (2) shape).** If
`2 · θ · m = 2π · k` with `m = 2^N` a power of `2`, then `θ` is
dyadic with denominator `2^(N+1)`. -/
theorem ajoOverlapConclusion_of_pow_two_half
    {θ : ℝ} {N : ℕ} {k : ℤ}
    (h : 2 * θ * ((2 ^ N : ℕ) : ℝ) = 2 * Real.pi * k) :
    AJOOverlapConclusion θ := by
  refine ⟨k, N + 1, ?_⟩
  have hpow : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; ring
  rw [hpow] at h
  have hne' : (2 : ℝ) ^ N ≠ 0 := by positivity
  have hne2 : ((2 : ℝ) ^ (N + 1)) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  linarith [h]

/-! ## Vacuous cases and `θ`-fixed conclusions

When the hypothesis-supplied integer is provably zero — for example,
when the overlap or logical-overlap weight already vanishes — the
condition `θ · w ∈ 2π · ℤ` reduces to the trivial `0 ∈ 2π · ℤ`. In that
case it carries no information about `θ`. The AJO argument extracts a
non-vacuous weight from the full set of generators; in this file we
record the structural building block: a non-zero weight that is a power
of `2` suffices. -/

/-- If `θ · m = 2π · k` and `m` is positive, then `θ = 2π · k / m`.
This is the basic plumbing lemma used in dyadic reduction. -/
theorem theta_eq_div_of_mul_eq
    {θ : ℝ} {m : ℝ} {k : ℤ} (hm : m ≠ 0)
    (h : θ * m = 2 * Real.pi * k) :
    θ = 2 * Real.pi * k / m := by
  field_simp
  linarith [h]

/-! ## Power-of-two overlap-weight reductions

If any non-empty subset `I` of generators has an overlap of weight
exactly `2^N`, condition (1) gives the dyadic conclusion (with
`I`-card-dependent denominator). Similarly for non-empty `J` and
condition (2). These are the basic reductions the AJO argument leans
on. -/

/-- **Dyadic-weight reduction (general shape).** If
`c · θ · m = 2π · k` with `c = 2^M` and `m = 2^N` both powers of two,
then `θ` is dyadic with denominator `2^(M + N)`. -/
theorem ajoOverlapConclusion_of_pow_two_general
    {θ : ℝ} {M N : ℕ} {k : ℤ}
    (h : (2 ^ M : ℝ) * θ * ((2 ^ N : ℕ) : ℝ) = 2 * Real.pi * k) :
    AJOOverlapConclusion θ := by
  refine ⟨k, M + N, ?_⟩
  have hpowN : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; ring
  rw [hpowN] at h
  have hneM : (2 : ℝ) ^ M ≠ 0 := by positivity
  have hneN : (2 : ℝ) ^ N ≠ 0 := by positivity
  have hneMN : (2 : ℝ) ^ (M + N) ≠ 0 := by positivity
  rw [pow_add]
  field_simp
  linarith [h]

/-- If condition (1) of `AJOOverlapHypothesis` holds and there exists a
non-empty `I` with `hammingWeight (overlap (fun i => H_X i) I) = 2^N`,
then `θ` is dyadic. Denominator is `2^(|I| - 1 + N)`. -/
theorem AJOOverlapHypothesis.dyadic_of_overlap_pow_two
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ)
    {I : Finset (Fin r)} (hI : I.Nonempty)
    {N : ℕ}
    (hwN : hammingWeight (overlap (fun i => H_X i) I) = 2 ^ N) :
    AJOOverlapConclusion θ := by
  obtain ⟨_, _, _, h1, _⟩ := hyp
  obtain ⟨k, hk⟩ := h1 I hI
  rw [hwN] at hk
  -- `(2 ^ (I.card - 1) : ℝ) * θ * (2^N : ℕ : ℝ) = 2π · k`.
  exact ajoOverlapConclusion_of_pow_two_general hk

/-- If condition (2) of `AJOOverlapHypothesis` holds at `{i}` and
`hammingWeight (g_L ∧ H_X i) = 2^N`, then `θ` is dyadic with
denominator `2^(N + 1)`. -/
theorem AJOOverlapHypothesis.dyadic_of_logicalOverlap_singleton_pow_two
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) (i : Fin r)
    {N : ℕ}
    (hwN : hammingWeight (fun j => g_L j * H_X i j) = 2 ^ N) :
    AJOOverlapConclusion θ := by
  obtain ⟨k, hk⟩ := hyp.singleton_logical_pi_int i
  rw [hwN] at hk
  -- `2 * θ * (2^N : ℕ : ℝ) = 2π · k`, i.e., the half-shape reduction.
  exact ajoOverlapConclusion_of_pow_two_half hk

/-- If some generator `H_X i` has Hamming weight `1`, then `θ` is dyadic
with denominator `1` (i.e., `θ ∈ 2π·ℤ`). This is the simplest "lucky
generator" case. -/
theorem AJOOverlapHypothesis.dyadic_of_singleton_weight_one
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) {i : Fin r}
    (hwt : hammingWeight (fun j => H_X i j) = 1) :
    AJOOverlapConclusion θ := by
  apply hyp.dyadic_of_overlap_pow_two
    (I := ({i} : Finset (Fin r))) (Finset.singleton_nonempty i)
    (N := 0)
  rw [hammingWeight_overlap_singleton]
  simpa using hwt

/-- If both `H_X i` and `g_L` have weight a power of two, the conclusion
follows from cond (1) alone (not needing the cond (2) clauses). -/
theorem AJOOverlapHypothesis.dyadic_of_some_singleton_pow_two
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) {i : Fin r} {N : ℕ}
    (hwN : hammingWeight (fun j => H_X i j) = 2 ^ N) :
    AJOOverlapConclusion θ := by
  apply hyp.dyadic_of_overlap_pow_two
    (I := ({i} : Finset (Fin r))) (Finset.singleton_nonempty i)
    (N := N)
  rw [hammingWeight_overlap_singleton]
  exact hwN

/-- **Vacuous case `n = 0`.** On a zero-qubit code there is no non-trivial
logical: the only `Fin 0 → ZMod 2` is the zero function, but the
hypothesis demands `g_L ∉ {0}`. So the hypothesis is inconsistent and
the conclusion follows vacuously. -/
theorem AJOOverlapHypothesis.dyadic_of_n_zero
    {H_X H_Z : Matrix (Fin r) (Fin 0) (ZMod 2)}
    {g_L : Fin 0 → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) :
    AJOOverlapConclusion θ := by
  -- Show `g_L = 0`, contradicting `gL_ne_zero`.
  exact absurd (funext (fun i => Fin.elim0 i)) hyp.gL_ne_zero

/-! ## Subtracting hypothesis conditions

The conditions are closed under integer linear combinations of the
underlying real equations. Combining at different `I` produces new
divisibility constraints. -/

/-- Subtracting cond (1) at `{i}` doubled from cond (2) at `{i}` gives:
`2θ · (wt(H_X i) - wt(g_L · H_X i)) ∈ 2π·ℤ` as an integer-valued
relation. Geometrically, this is the bits of `H_X i` that are NOT in
the support of `g_L`. (Using the new factors: cond (1) at `{i}` is
`θ · wt(H_X i) ∈ 2π·ℤ`, cond (2) at `{i}` is `2θ · wt(g_L·H_X i)
∈ 2π·ℤ`. Multiplying the first by 2 and subtracting gives the claim.) -/
theorem AJOOverlapHypothesis.singleton_minus_logical
    {H_X H_Z : Matrix (Fin r) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2} {θ : ℝ}
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) (i : Fin r) :
    ∃ k : ℤ,
      2 * θ * ((hammingWeight (fun j => H_X i j) : ℤ) -
          (hammingWeight (fun j => g_L j * H_X i j) : ℤ) : ℝ) =
        2 * Real.pi * k := by
  obtain ⟨k₀, hk₀⟩ := hyp.singleton_pi_int i
  obtain ⟨k₁, hk₁⟩ := hyp.singleton_logical_pi_int i
  refine ⟨2 * k₀ - k₁, ?_⟩
  push_cast
  linarith [hk₀, hk₁]

/-! **Target — and residual counterexample.** The intended AJO
binary-matrix overlap lemma is:

```
theorem ajo_binary_matrix_lemma
    {n r : ℕ}
    (H_X : Matrix (Fin r) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r) (Fin n) (ZMod 2))
    (g_L : Fin n → ZMod 2) (θ : ℝ)
    (hyp : AJOOverlapHypothesis H_X H_Z g_L θ) :
    AJOOverlapConclusion θ
```

With `AJOOverlapHypothesis` as encoded here (factor `2^(|I|-1)` on
condition (1), `2^|J|` on condition (2) for non-empty `J`), the
statement is the actual AJO Theorem 1 target. However, the
hypothesis as encoded here is *still* technically insufficient in the
degenerate `r = 1` regime: an explicit residual counterexample
(`ajo_target_false`) sits at `r = 1`, `n = 9`, `H_X` = all-ones,
`g_L` of weight 3, `θ = 2π/3`. Here:

* Cond (1) at `I = {0}` (factor `2^0 = 1`): `θ · 9 = 6π ∈ 2π·ℤ` ✓.
* Cond (2) at `J = {0}` (factor `2^1 = 2`): `2θ · 3 = 4π ∈ 2π·ℤ` ✓.
* Non-triviality: `g_L ∉ row(H_X)` (only `0` and the all-ones vector
  are in the rowspan, while `g_L` has weight 3) ✓.

But `θ / (2π) = 1/3` is non-dyadic. The structural reason is that
for a single all-ones stabilizer, trans-logical at `v = g_L` gives
only `3θ ∈ 2π·ℤ` (combining cond (1) and cond (2)), which has the
non-dyadic solution `θ = 2π/3`. Operationally `Z(2π/3)^⊗9` acts on
the encoded qubit as the identity (since `wt(g_L) · θ = 2π`), so
AJO Theorem 1 *does* hold — but the logical action is trivial. The
"binary-matrix lemma" conclusion `AJOOverlapConclusion θ` (θ
dyadic) is therefore a *stronger* claim than the AJO theorem
proper, which only requires the logical angle `θ_L = θ · wt(g_L)`
to be dyadic.

The structural results in this file (Hamming-weight identities,
overlap-monotonicity lemmas, dyadic-weight reductions, and the
integer-combination relation `singleton_minus_logical`) remain
valid and usable. What this file reduces the
target to, in regimes where the conclusion does hold:

* If any non-empty `I ⊆ Fin r` has `wt(overlap H_X I) = 2^N`, the
  conclusion holds (`dyadic_of_overlap_pow_two`).
* If `wt(g_L · H_X i) = 2^N` for some `i`, the conclusion holds
  (`dyadic_of_logicalOverlap_singleton_pow_two`).
* If `n = 0`, the hypothesis is inconsistent and the conclusion is
  vacuous (`dyadic_of_n_zero`).
* The integer-combination condition
  `2θ · (wt(H_X i) - wt(g_L · H_X i)) ∈ 2π·ℤ` is recorded as
  `singleton_minus_logical`.

This file does not contain the inductive Möbius-inversion argument
over all `2^r` subsets, nor a reformulation of the conclusion
(restricting to `r ≥ 2` plus some richness, replacing the
conclusion with "θ_L dyadic", or assuming the AJO operator-side
hypothesis explicitly). `ajo_target_false` documents the gap.

The case `r = 0` is excluded by the `1 ≤ r` clause; the `n = 0` case
is handled by `dyadic_of_n_zero`. -/

/-! ## Explicit residual counterexample to the stated target

We construct concrete data `(n, r, H_X, H_Z, g_L, θ)` for which the
*corrected* `AJOOverlapHypothesis H_X H_Z g_L θ` holds but
`AJOOverlapConclusion θ` does not. This documents that the
`r = 1` regime requires either a stronger conclusion or a stronger
hypothesis than the F₂-side encoding can supply on its own.

Setup: `r = 1`, `n = 9`, with `H_X` the single all-ones row,
`H_Z = 0` (a single zero row, so `ker(H_Z) = (ZMod 2)^9`), and
`g_L = (1, 1, 1, 0, …, 0)` of weight 3. The angle `θ = 2π/3` is
non-dyadic. The corrected hypothesis has only two non-trivial
conditions (since the only non-empty subset of `Fin 1` is `{0}`):
`θ · 9 = 6π = 2π · 3` and `2θ · 3 = 4π = 2π · 2`. Both check.
Operationally `Z(2π/3)^⊗9` acts as logical-identity on the
encoded qubit defined by `g_L`, so AJO Theorem 1's operator-side
conclusion ("logical action is in the hierarchy") holds —
trivially — but the *angle* `θ = 2π/3` is not dyadic. -/

/-- The `H_X` for the counterexample: a single all-ones row of length 9. -/
def ajoCounterHX : Matrix (Fin 1) (Fin 9) (ZMod 2) :=
  fun _ _ => 1

/-- The `H_Z` for the counterexample: a single zero row of length 9. The
kernel of this matrix is all of `(ZMod 2)^9`. -/
def ajoCounterHZ : Matrix (Fin 1) (Fin 9) (ZMod 2) :=
  fun _ _ => 0

/-- The non-trivial logical for the counterexample: weight 3, supported on
the first three positions. -/
def ajoCounterGL : Fin 9 → ZMod 2 :=
  fun j => if j.val < 3 then 1 else 0

/-- The non-dyadic angle for the counterexample: `θ = 2π/3`. -/
noncomputable def ajoCounterTheta : ℝ := 2 * Real.pi / 3

/-- The Hamming weight of the counterexample `g_L` is 3. -/
theorem ajoCounter_hammingWeight_gL : hammingWeight ajoCounterGL = 3 := by
  unfold hammingWeight ajoCounterGL
  rfl

/-- The Hamming weight of the all-ones row in the counterexample is 9. -/
theorem ajoCounter_hammingWeight_HX_row :
    hammingWeight (fun j => ajoCounterHX 0 j) = 9 := by
  unfold hammingWeight ajoCounterHX
  rfl

/-- The product of `g_L` with the all-ones row equals `g_L`. -/
theorem ajoCounter_gL_mul_HX :
    (fun j => ajoCounterGL j * ajoCounterHX 0 j) = ajoCounterGL := by
  funext j
  simp [ajoCounterHX]

/-- The kernel of the counterexample `H_Z` is the full space, so any
`g_L : Fin 9 → ZMod 2` lies in it. -/
theorem ajoCounter_gL_mem_carrier :
    ajoCounterGL ∈ cssXLogicalCarrier ajoCounterHZ := by
  unfold cssXLogicalCarrier
  rw [LinearMap.mem_ker]
  ext i
  -- `(ajoCounterHZ *ᵥ ajoCounterGL) i = ∑ j, 0 * ajoCounterGL j = 0`.
  simp [ajoCounterHZ, Matrix.mulVec, dotProduct]

/-- The row span of the counterexample `H_X` consists of just `0` and the
all-ones vector. The counterexample `g_L`, which has weight 3, lies in
neither, hence is outside the row span. -/
theorem ajoCounter_gL_not_mem_subspace :
    ajoCounterGL ∉ cssXLogicalSubspace ajoCounterHX := by
  unfold cssXLogicalSubspace
  rw [LinearMap.mem_range]
  rintro ⟨u, hu⟩
  -- `Matrix.mulVecLin ajoCounterHXᵀ u = ajoCounterGL` means
  -- `(ajoCounterHX)ᵀ *ᵥ u = ajoCounterGL`.
  -- Each entry of `(ajoCounterHX)ᵀ *ᵥ u` equals `∑ i, ajoCounterHX i j * u i`,
  -- and `ajoCounterHX i j = 1` for all `i, j`, so this equals `u 0`
  -- (since `r = 1`). Hence `ajoCounterGL j = u 0` is constant in `j`.
  have hconst : ∀ j : Fin 9, ajoCounterGL j = u 0 := by
    intro j
    have hj := congrFun hu j
    -- `(mulVecLin ajoCounterHXᵀ u) j = ajoCounterGL j`.
    -- Unfold the dot product: `∑ i : Fin 1, ajoCounterHX i j * u i = u 0`.
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, ajoCounterHX, one_mul,
      Finset.sum_singleton, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue] at hj
    exact hj.symm
  -- But `ajoCounterGL 0 = 1` and `ajoCounterGL 3 = 0`, contradicting
  -- the constancy.
  have h0 : ajoCounterGL 0 = u 0 := hconst 0
  have h3 : ajoCounterGL 3 = u 0 := hconst 3
  have hne : ajoCounterGL 0 ≠ ajoCounterGL 3 := by
    decide
  exact hne (h0.trans h3.symm)

/-- Helper: a non-empty subset `S` of `Fin 1` equals `{0}`. -/
private theorem ajoCounter_finset_fin_one_eq
    {S : Finset (Fin 1)} (hS : S.Nonempty) : S = ({0} : Finset (Fin 1)) := by
  ext x
  refine ⟨fun _ => ?_, fun hx => ?_⟩
  · -- `x : Fin 1`, so `x = 0`, hence `x ∈ {0}`.
    rw [Finset.mem_singleton]
    exact Fin.fin_one_eq_zero x
  · rw [Finset.mem_singleton] at hx
    rw [hx]
    obtain ⟨y, hy⟩ := hS
    -- `y : Fin 1`, so `y = 0` and `0 = y ∈ S`.
    have : y = 0 := Fin.fin_one_eq_zero y
    rw [this] at hy
    exact hy

/-- Condition (1) of the corrected `AJOOverlapHypothesis` holds for the
counterexample. For the only non-empty subset `I = {0}` of `Fin 1`,
we have `2^(|I|-1) · θ · wt(overlap H_X {0}) = 2^0 · (2π/3) · 9 =
6π = 2π · 3`. -/
theorem ajoCounter_condition_one
    (I : Finset (Fin 1)) (hI : I.Nonempty) :
    ∃ k : ℤ, (2 ^ (I.card - 1) : ℝ) * ajoCounterTheta *
        (hammingWeight (overlap (fun i => ajoCounterHX i) I) : ℝ) =
      2 * Real.pi * k := by
  refine ⟨3, ?_⟩
  have hI_eq : I = ({0} : Finset (Fin 1)) := ajoCounter_finset_fin_one_eq hI
  have hwt : hammingWeight (overlap (fun i => ajoCounterHX i) I) = 9 := by
    have hov : overlap (fun i => ajoCounterHX i) I =
        (fun _ : Fin 9 => (1 : ZMod 2)) := by
      funext j
      unfold overlap ajoCounterHX
      exact Finset.prod_const_one
    rw [hov, hammingWeight_one]
  have hcard : I.card = 1 := by rw [hI_eq]; exact Finset.card_singleton 0
  rw [hwt, hcard]
  unfold ajoCounterTheta
  push_cast
  ring

/-- Condition (2) of the corrected `AJOOverlapHypothesis` holds for the
counterexample. For the only non-empty subset `J = {0}` of `Fin 1`, we
have `2^|J| · θ · wt(g_L ∧ overlap H_X {0}) = 2 · (2π/3) · 3 = 4π = 2π · 2`. -/
theorem ajoCounter_condition_two
    (J : Finset (Fin 1)) (hJ : J.Nonempty) :
    ∃ k : ℤ, (2 ^ J.card : ℝ) * ajoCounterTheta *
        (hammingWeight (logicalOverlap ajoCounterGL
          (fun i => ajoCounterHX i) J) : ℝ) = 2 * Real.pi * k := by
  refine ⟨2, ?_⟩
  have hJ_eq : J = ({0} : Finset (Fin 1)) := ajoCounter_finset_fin_one_eq hJ
  have hwt :
      hammingWeight (logicalOverlap ajoCounterGL
          (fun i => ajoCounterHX i) J) = 3 := by
    have hlo : logicalOverlap ajoCounterGL (fun i => ajoCounterHX i) J =
        ajoCounterGL := by
      funext j
      unfold logicalOverlap overlap ajoCounterHX
      simp
    rw [hlo, ajoCounter_hammingWeight_gL]
  have hcard : J.card = 1 := by rw [hJ_eq]; exact Finset.card_singleton 0
  rw [hwt, hcard]
  unfold ajoCounterTheta
  push_cast
  ring

/-- The counterexample satisfies `AJOOverlapHypothesis`. -/
theorem ajoCounter_hypothesis :
    AJOOverlapHypothesis ajoCounterHX ajoCounterHZ ajoCounterGL
      ajoCounterTheta := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_refl 1
  · exact ajoCounter_gL_mem_carrier
  · exact ajoCounter_gL_not_mem_subspace
  · exact ajoCounter_condition_one
  · exact ajoCounter_condition_two

/-- The counterexample angle `θ = 2π/3` does *not* satisfy
`AJOOverlapConclusion`: it is not a dyadic multiple of `2π`. -/
theorem ajoCounter_not_conclusion :
    ¬ AJOOverlapConclusion ajoCounterTheta := by
  unfold AJOOverlapConclusion ajoCounterTheta
  rintro ⟨a, N, h⟩
  -- From `2π/3 = 2π · a / 2^N`, derive `2^N = 3 · a`, contradicting
  -- the fact that `3` never divides `2^N` (in `ℕ`).
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h2N_ne : ((2 : ℝ) ^ N) ≠ 0 := ne_of_gt h2N_pos
  -- Multiply both sides by `3 · 2^N`.
  have hkey : ((2 : ℝ) ^ N) = 3 * (a : ℝ) := by
    have h' := h
    field_simp at h'
    have hpi2 : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi
    nlinarith [h', hpi2]
  -- Cast to integers: `2^N = 3 * a`. Then `3 ∣ 2^N`, hence (since
  -- `3` is prime and `2 < 3`) we get `3 ∣ 2` by `Nat.Prime.dvd_of_dvd_pow`,
  -- which is impossible.
  have hint : (2 : ℤ) ^ N = 3 * a := by
    have hcast : ((2 ^ N : ℤ) : ℝ) = ((3 * a : ℤ) : ℝ) := by
      push_cast
      exact hkey
    exact_mod_cast hcast
  -- Get the natural-number version: `3 ∣ 2^N` in ℕ.
  have h3div_nat : (3 : ℕ) ∣ 2 ^ N := by
    have h3div_int : (3 : ℤ) ∣ 2 ^ N := ⟨a, hint⟩
    have h3div_int' : (3 : ℤ) ∣ ((2 ^ N : ℕ) : ℤ) := by
      simpa using h3div_int
    exact_mod_cast h3div_int'
  -- `3 ∣ 2^N` with `3` prime implies `3 ∣ 2`, contradiction.
  have h3p : Nat.Prime 3 := by decide
  have h3dvd2 : (3 : ℕ) ∣ 2 := h3p.dvd_of_dvd_pow h3div_nat
  exact absurd h3dvd2 (by decide)

/-- **Formal refutation of the docstring target.** There exists data
satisfying `AJOOverlapHypothesis` but not `AJOOverlapConclusion`. -/
theorem ajo_target_false :
    ∃ (n r : ℕ)
      (H_X : Matrix (Fin r) (Fin n) (ZMod 2))
      (H_Z : Matrix (Fin r) (Fin n) (ZMod 2))
      (g_L : Fin n → ZMod 2) (θ : ℝ),
      AJOOverlapHypothesis H_X H_Z g_L θ ∧ ¬ AJOOverlapConclusion θ :=
  ⟨9, 1, ajoCounterHX, ajoCounterHZ, ajoCounterGL, ajoCounterTheta,
    ajoCounter_hypothesis, ajoCounter_not_conclusion⟩

end FTQCLib.Codes

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.AJO
import FTQCLib.Codes.AJOOverlap
import FTQCLib.Codes.AJOLattice
import FTQCLib.Codes.AJOMain
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.RingTheory.Int.Basic

set_option linter.unusedSectionVars false

/-! # AJO Theorem 1 (uniform-angle case): general theorem under non-degeneracy

This file targets the general uniform-angle dyadic theorem from AJO 2014
(Anderson--Jochym-O'Connor 2014, arXiv:1408.5547, Section III.A) under
the non-degeneracy hypothesis

  `∃ h ∈ cssXLogicalSubspace H_X, h ≠ 0`

(equivalently: `row(H_X)` contains a non-zero vector).

The three concrete routes are in `AJOMain.lean`:

* `ajo_uniform_dyadic_of_unit_vec_route` — qubit-free-on-Z-side route
* `ajo_uniform_dyadic_of_h_pow_two` — power-of-two X-stabilizer-weight
  route
* `ajo_uniform_dyadic_of_gL_overlap_pow_two` — power-of-two
  `g_L`-overlap-weight route

Each is a "lucky witness" reduction. What remains, and what AJO 2014
actually carries out in Section III.A, is the Möbius / inclusion-
exclusion argument over the `2^{r_X}` subsets of generators that
discharges the general case.

## What this file proves

### Substantive results

* **`ajo_uniform_rational_of_nondegen`** — under non-degeneracy and
  trans-logical, `θ` is a rational multiple of `2π`. This is the
  first qualitative step of AJO Section III.A: it reduces the problem
  from "is `θ/2π` arbitrary?" to "is the denominator a power of two?".
  Proof: the `v = 0` constraint at the non-zero `h_0` gives
  `θ · wt(h_0) ∈ 2π · ℤ`, and `wt(h_0) > 0`.

* **`ajo_uniform_dyadic_of_nondegen_unit_vec`** — non-degeneracy + a
  free-on-Z-side qubit hit by *some* X-stabilizer (not necessarily the
  non-degenerate witness) → dyadic. This packages
  `ajo_uniform_dyadic_of_unit_vec_route` with the non-degeneracy
  hypothesis for uniformity of statement.

* **`ajo_uniform_dyadic_of_nondegen_pow_two_witness`** — non-degeneracy
  + any X-stabilizer of power-of-two weight → dyadic. Packages
  `ajo_uniform_dyadic_of_h_pow_two`.

* **`hammingWeight_add_eq_sub`** — inclusion-exclusion for two binary
  vectors at the Hamming-weight level:
  `wt(g_1 + g_2) = wt(g_1) + wt(g_2) − 2 · wt(g_1 ∧ g_2)`.
  This is the F₂-arithmetic core of any Möbius identity, and follows
  from the per-bit identity already proved in `AJOLattice.lean`.

* **`hammingWeight_bitOr_two`** — at the integer level,
  `wt(g_1 ∨ g_2) = wt(g_1) + wt(g_2) − wt(g_1 ∧ g_2)`, where `∨` is
  bitwise OR (encoded as `a + b + a*b` in `ZMod 2`). This is the
  classical inclusion-exclusion for two sets.

* **`hammingWeight_biUnion_supp_eq_inclusion_exclusion`** — the **full
  Möbius identity** at the F₂ side: for any system of binary vectors
  `g : Fin r_X → (Fin n → ZMod 2)`,
  `|⋃ supp(g_i)| = ∑_{I non-empty} (-1)^{|I|+1} · wt(overlap g I)`.
  Proved by reducing to `Finset.inclusion_exclusion_card_biUnion` from
  Mathlib, with `supp_overlap_nonempty` establishing
  `supp(overlap g I) = ⋂_{i ∈ I} supp(g_i)` for non-empty `I`.

* **`supp` / `mem_supp_overlap_iff` / `supp_overlap_nonempty`** —
  support set of a binary vector, with the characterisation that
  `j ∈ supp(overlap g I)` iff every contributing generator hits `j`.

### What is *not* proved here: the AJO odd-prime contradiction

The substantive missing piece is the AJO Section III.A argument: under
the assumption `θ/(2π) = a/q` with `p` an odd prime dividing `q`, derive
a contradiction with `h_nontriv` via a Möbius-inversion walk over the
`2^{r_X}` subsets of generators.

The argument has the following structure (documented but not formalised):

1. From `θ · wt(h) ∈ 2π · ℤ` and `θ/(2π) = a/q` with `gcd(a, q) = 1`:
   `q | wt(h) · a`, hence `q | wt(h)`, hence `p | wt(h)` for each
   `h ∈ row(H_X)`.

2. From `θ · (wt(h) − 2·wt(v ∧ h)) ∈ 2π · ℤ` at `v ∈ row(H_X)` and
   `h ∈ row(H_X)`: `q | wt(h) − 2·wt(v ∧ h)`, hence
   `p | 2·wt(v ∧ h)`, hence `p | wt(v ∧ h)` (as `p` is odd).

3. By induction on subset size with inclusion-exclusion:
   `p | wt(overlap_S)` for every non-empty `S ⊆ Fin r_X`.

4. From `θ · (wt(h) − 2·wt(g_L ∧ h)) ∈ 2π · ℤ` at `v = g_L`:
   `p | wt(g_L ∧ h)`. Iterating with compound `v = g_L + (sum over I)`
   and `h = ⋀_{j ∈ J} g_j`, conclude `p | wt(g_L ∧ overlap_J)` for all
   non-empty `J`. By Möbius: `p | wt(g_L ∧ union)`.

5. `wt(g_L) = wt(g_L ∧ union) + wt(g_L \\ union)`. From
   `h_nontriv`: `q ∤ wt(g_L) · a`, hence `q ∤ wt(g_L)`, hence
   `p ∤ wt(g_L)`. Combined with step 4: `p ∤ wt(g_L \\ union)`.

6. The "extra-territorial" portion `g_L \\ union` contributes a
   power-of-two-only divisor of `q`, contradicting `p | q`.

Step 6 is the deepest. It requires either:

* The "lifting" trick of AJO: build the chain `v = g_L`, `v = g_L + g_i`,
  ... ; each step is itself a trans-logical constraint, so each step
  enforces `q | (\text{some integer})`. After Möbius reduction the chain
  collapses to a constraint on `wt(g_L \\ union)` modulo a power of 2.
* Or a direct enumeration of the lattice structure of `row(H_X)`,
  which is not formalised here.

The Möbius / inclusion-exclusion identity at the F₂ side is proved in
this file (`hammingWeight_biUnion_supp_eq_inclusion_exclusion`) via
mathlib's `Finset.inclusion_exclusion_card_biUnion`. The remaining
obstacle is the inductive walk that produces the divisibility
hypotheses for each non-empty subset.

## What this file does *not* contain

* The inductive walk over `2^{r_X}` subsets that produces the
  divisibility hypotheses `p | wt(overlap_S)` for non-empty `S`.
* The odd-prime contradiction via `padicValNat`-style reasoning.
* A proof that closes the gap to `ajo_uniform_dyadic_general`.
-/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Hierarchy Matrix

variable {n r_X r_Z : ℕ}

/-! ## Bit-arithmetic and inclusion-exclusion at the Hamming-weight level

`ZMod 2` addition is bitwise XOR; pointwise multiplication is bitwise
AND. There is no native bitwise OR in `ZMod 2`, but we can encode it
as `a ∨ b = a + b − a*b` (cast to `ℤ` per bit) since
`(a ∨ b)_i = a_i + b_i − a_i · b_i` numerically when `a_i, b_i ∈
{0, 1}`.
-/

/-- Per-bit identity in `ZMod 2`: `(a + b).val = a.val + b.val −
2·(a*b).val` as integers. This is the source of inclusion-exclusion. -/
theorem zmod_two_add_val_eq (a b : ZMod 2) :
    ((a + b).val : ℤ) =
      (a.val : ℤ) + (b.val : ℤ) - 2 * ((a * b).val : ℤ) := by
  have ea : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  have eb : b = ((b.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val b).symm
  have ha : a.val < 2 := ZMod.val_lt a
  have hb : b.val < 2 := ZMod.val_lt b
  rw [ea, eb]
  interval_cases a.val <;> interval_cases b.val <;> decide

/-- **F₂ inclusion-exclusion for two vectors at the integer level.**
For `v, h : Fin n → ZMod 2`, the F₂-sum `v + h` has Hamming weight

  `wt(v + h) = wt(v) + wt(h) − 2 · wt(v ∧ h)`

where `v ∧ h` is pointwise multiplication. This is the per-bit identity
summed across coordinates.

(Note: this is implicit in `wt_add_sub_wt_eq_transShift` in
`AJOLattice.lean`, which states `wt(v + h) − wt(v) = wt(h) − 2·wt(v ∧
h)` after rearrangement. We restate it as a free-standing identity for
documentation.) -/
theorem hammingWeight_add_eq_sub (v h : Fin n → ZMod 2) :
    ((hammingWeight (v + h) : ℤ)) =
      (hammingWeight v : ℤ) + (hammingWeight h : ℤ)
        - 2 * (hammingWeight (fun j => v j * h j) : ℤ) := by
  -- Use the integer identity `wt(v + h) − wt(v) = transShift h v`
  -- already proved in `AJOLattice.lean`.
  have hshift := wt_add_sub_wt_eq_transShift v h
  -- Unfold `transShift` to `wt(h) − 2·wt(v ∧ h)`.
  have hexp := transShift_eq h v
  -- Combine.
  linarith [hshift, hexp]

/-! ## Inclusion-exclusion for the bitwise OR of two vectors

The bitwise OR of two binary vectors `g_1, g_2` is `g_1 ∨ g_2 = g_1 +
g_2 + g_1·g_2` in `ZMod 2`: at each bit `(a ∨ b) = a + b + a·b` (a
direct check on the four cases). At the integer level
`(a ∨ b).val = a.val + b.val − a.val · b.val`, hence

  `wt(g_1 ∨ g_2) = wt(g_1) + wt(g_2) − wt(g_1 ∧ g_2)`. -/

/-- Per-bit identity for bitwise OR encoded as `a + b + a*b` in `ZMod 2`:
`((a + b + a*b).val : ℤ) = a.val + b.val − a.val · b.val`. The
encoding `a + b + a*b` is checked case-by-case on the four pairs. -/
theorem zmod_two_or_val_eq (a b : ZMod 2) :
    (((a + b + a * b).val : ℕ) : ℤ) =
      (a.val : ℤ) + (b.val : ℤ) - (a.val : ℤ) * (b.val : ℤ) := by
  have ea : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  have eb : b = ((b.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val b).symm
  have ha : a.val < 2 := ZMod.val_lt a
  have hb : b.val < 2 := ZMod.val_lt b
  rw [ea, eb]
  interval_cases a.val <;> interval_cases b.val <;> decide

/-- The bitwise OR of two binary vectors, encoded as `g_1 + g_2 +
g_1·g_2` in `ZMod 2`. -/
def bitOr (g₁ g₂ : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun j => g₁ j + g₂ j + g₁ j * g₂ j

/-- **Two-set inclusion-exclusion at the Hamming-weight level.**
`wt(g_1 ∨ g_2) = wt(g_1) + wt(g_2) − wt(g_1 ∧ g_2)`. -/
theorem hammingWeight_bitOr_two (g₁ g₂ : Fin n → ZMod 2) :
    (hammingWeight (bitOr g₁ g₂) : ℤ) =
      (hammingWeight g₁ : ℤ) + (hammingWeight g₂ : ℤ)
        - (hammingWeight (fun j => g₁ j * g₂ j) : ℤ) := by
  -- Pointwise: `(bitOr g₁ g₂ j).val = (g₁ j).val + (g₂ j).val − (g₁ j).val · (g₂ j).val`.
  have hpt : ∀ i : Fin n,
      (((bitOr g₁ g₂) i).val : ℤ) =
        ((g₁ i).val : ℤ) + ((g₂ i).val : ℤ) -
          ((g₁ i).val : ℤ) * ((g₂ i).val : ℤ) := by
    intro i
    unfold bitOr
    exact zmod_two_or_val_eq (g₁ i) (g₂ i)
  -- Sum the pointwise identity.
  have hsum :
      ∑ i, (((bitOr g₁ g₂) i).val : ℤ) =
        ∑ i, (((g₁ i).val : ℤ) + ((g₂ i).val : ℤ) -
                ((g₁ i).val : ℤ) * ((g₂ i).val : ℤ)) :=
    Finset.sum_congr rfl (fun i _ => hpt i)
  -- Expand the RHS using `sum_sub_distrib`, `sum_add_distrib`.
  have hRHS_expand :
      ∑ i, (((g₁ i).val : ℤ) + ((g₂ i).val : ℤ) -
              ((g₁ i).val : ℤ) * ((g₂ i).val : ℤ)) =
        (∑ i, ((g₁ i).val : ℤ)) + (∑ i, ((g₂ i).val : ℤ)) -
          (∑ i, ((g₁ i).val : ℤ) * ((g₂ i).val : ℤ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hRHS_expand] at hsum
  -- Unfold the Hamming weights on both sides.
  unfold hammingWeight
  push_cast
  -- The pointwise product term: `((g₁ j * g₂ j).val : ℤ) = ((g₁ j).val * (g₂ j).val : ℤ)`
  -- by `zmod_two_val_mul`.
  have hmul_pt : ∀ i : Fin n,
      (((g₁ i) * (g₂ i)).val : ℤ) = ((g₁ i).val : ℤ) * ((g₂ i).val : ℤ) := by
    intro i
    rw [zmod_two_val_mul]
    push_cast
    ring
  have hmul_sum :
      ∑ i, (((g₁ i) * (g₂ i)).val : ℤ) =
        ∑ i, (((g₁ i).val : ℤ) * ((g₂ i).val : ℤ)) :=
    Finset.sum_congr rfl (fun i _ => hmul_pt i)
  linarith [hsum, hmul_sum]

/-! ## Support sets, intersection / union, and Möbius identity

For binary vectors, the *support* is the set of positions where the
vector is `1`. The Hamming weight equals the support's cardinality.
Multiplication of binary vectors corresponds to set intersection of
supports; bitwise OR (encoded `+ + *` in `ZMod 2`) corresponds to
union.

This lets us push the inclusion-exclusion identity through Mathlib's
`Finset.inclusion_exclusion_card_biUnion`. -/

/-- The *support* of a binary vector `v : Fin n → ZMod 2`: the set of
positions at which `v` is non-zero. -/
def supp (v : Fin n → ZMod 2) : Finset (Fin n) :=
  Finset.univ.filter (fun j => v j = 1)

/-- The Hamming weight of `v` equals the cardinality of its support. -/
theorem hammingWeight_eq_card_supp (v : Fin n → ZMod 2) :
    hammingWeight v = (supp v).card := by
  unfold hammingWeight supp
  -- `∑ j, (v j).val = #{j : v j = 1}`.
  -- Each `(v j).val` is `0` or `1`, equal to `1` iff `v j = 1`.
  -- Use `Finset.card_filter` then convert sums.
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Goal: `(v j).val = if v j = 1 then 1 else 0`.
  by_cases hvj : v j = 1
  · rw [hvj]
    simp
  · have hvj0 : v j = 0 := by
      have h2 : v j ∈ ({0, 1} : Set (ZMod 2)) := by
        have hl : (v j).val < 2 := ZMod.val_lt (v j)
        have hv_recover : v j = ((v j).val : ZMod 2) := (ZMod.natCast_zmod_val (v j)).symm
        rcases (Nat.lt_succ_iff_lt_or_eq.mp hl) with hl1 | hl1
        · -- (v j).val < 1, so = 0
          have : (v j).val = 0 := by omega
          left
          rw [hv_recover, this]
          push_cast
          rfl
        · -- (v j).val = 1
          right
          rw [hv_recover, hl1]
          push_cast
          rfl
      rcases h2 with h0 | h1
      · exact h0
      · exact absurd h1 hvj
    rw [hvj0]
    simp

/-- Pointwise: in `ZMod 2`, `(v j).val = 1 ↔ v j = 1`. -/
private lemma zmod_two_val_eq_one_iff (a : ZMod 2) : a.val = 1 ↔ a = 1 := by
  constructor
  · intro h
    have ha : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
    rw [ha, h]
    push_cast
    rfl
  · intro h
    rw [h]
    haveI : Fact (1 < 2) := ⟨by norm_num⟩
    exact ZMod.val_one 2

/-- The product (bitwise AND) of two binary vectors is `1` at position
`j` iff both are. -/
theorem supp_mul (g₁ g₂ : Fin n → ZMod 2) :
    supp (fun j => g₁ j * g₂ j) = supp g₁ ∩ supp g₂ := by
  ext j
  unfold supp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  -- Need: `g₁ j * g₂ j = 1 ↔ g₁ j = 1 ∧ g₂ j = 1`.
  -- In `ZMod 2`, the only way the product is `1` is both factors are `1`.
  rw [← zmod_two_val_eq_one_iff, ← zmod_two_val_eq_one_iff, ← zmod_two_val_eq_one_iff]
  rw [zmod_two_val_mul]
  have h1 : (g₁ j).val < 2 := ZMod.val_lt (g₁ j)
  have h2 : (g₂ j).val < 2 := ZMod.val_lt (g₂ j)
  constructor
  · intro h
    interval_cases (g₁ j).val <;> interval_cases (g₂ j).val <;> simp_all
  · rintro ⟨h1', h2'⟩
    rw [h1', h2']

/-- The support of an overlap is the intersection of the supports of the
contributing generators. For non-empty `I`.

We prove the stronger pointwise statement: for any `j : Fin n`,
`j ∈ supp (overlap g I) ↔ ∀ i ∈ I, j ∈ supp (g i)`. The `inf'`
characterisation then follows from `Finset.mem_inf'`. -/
theorem mem_supp_overlap_iff
    (g : Fin r_X → (Fin n → ZMod 2))
    (I : Finset (Fin r_X)) (j : Fin n) :
    j ∈ supp (overlap g I) ↔ ∀ i ∈ I, j ∈ supp (g i) := by
  classical
  unfold supp overlap
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Need: `∏ i ∈ I, g i j = 1 ↔ ∀ i ∈ I, g i j = 1`.
  -- In ZMod 2, this follows from: a product is 1 iff every factor is 1.
  constructor
  · intro hprod i hi
    -- `g i j` is a factor of the product; if any factor is 0 the product is 0.
    by_contra hne
    -- `g i j ≠ 1`. Since `g i j ∈ ZMod 2`, `g i j = 0`.
    have hzero : g i j = 0 := by
      have h := (g i j).val_lt
      have : (g i j).val = 0 ∨ (g i j).val = 1 := by omega
      rcases this with h0 | h1
      · exact (ZMod.val_eq_zero (g i j)).mp h0
      · exact absurd ((zmod_two_val_eq_one_iff (g i j)).mp h1) hne
    -- Then the product is 0 (contains a zero factor).
    have : ∏ i ∈ I, g i j = 0 :=
      Finset.prod_eq_zero hi hzero
    rw [this] at hprod
    exact absurd hprod (by decide)
  · intro hall
    -- Every factor is 1, so the product is 1.
    rw [Finset.prod_eq_one]
    intros i hi
    exact hall i hi

/-- The support of an overlap is the intersection of the supports of the
contributing generators. -/
theorem supp_overlap_nonempty
    (g : Fin r_X → (Fin n → ZMod 2))
    {I : Finset (Fin r_X)} (hI : I.Nonempty) :
    supp (overlap g I) = I.inf' hI (fun i => supp (g i)) := by
  ext j
  rw [mem_supp_overlap_iff g I, Finset.mem_inf']

/-- **Möbius / inclusion-exclusion identity for the Hamming weight of a
bitwise union.** Let `g : Fin r_X → (Fin n → ZMod 2)` be binary
vectors. The cardinality of the union of their supports equals the
alternating sum of intersection cardinalities (i.e., overlap weights)
over non-empty subsets:

  `|⋃ supp(g_i)| = ∑_{I non-empty} (-1)^{|I|+1} · wt(overlap g I)`.

This is the AJO Möbius identity at the F₂ side, with the `(-1)^{|I|+1}`
signs in `ℤ`. -/
theorem hammingWeight_biUnion_supp_eq_inclusion_exclusion
    (g : Fin r_X → (Fin n → ZMod 2)) :
    ((Finset.univ.biUnion (fun i : Fin r_X => supp (g i))).card : ℤ) =
      ∑ t : (Finset.univ : Finset (Fin r_X)).powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (t.1.card + 1) *
          (hammingWeight (overlap g t.1) : ℤ) := by
  -- Apply `Finset.inclusion_exclusion_card_biUnion`.
  rw [Finset.inclusion_exclusion_card_biUnion (Finset.univ : Finset (Fin r_X))
        (fun i => supp (g i))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨t, ht⟩ _
  -- `ht : t ∈ (univ.powerset).filter (·.Nonempty)`.
  -- We need `#(t.inf' _ (fun i => supp (g i))) = wt(overlap g t)` (with cast).
  have ht_ne : t.Nonempty := (Finset.mem_filter.mp ht).2
  have hsupp_overlap := supp_overlap_nonempty g ht_ne
  rw [hammingWeight_eq_card_supp, hsupp_overlap]

/-! ## Non-degeneracy → rational `θ`

The substantive first step of AJO 2014 Section III.A:

> If `row(H_X)` contains a non-zero vector, then `θ` is a rational
> multiple of `2π`.

Proof: pick `h_0 ∈ row(H_X)` with `h_0 ≠ 0`. Its Hamming weight is
positive (a binary vector is non-zero iff some bit is one, iff its
Hamming weight is positive). The `v = 0` constraint gives
`θ · wt(h_0) ∈ 2π · ℤ`, so `θ = 2π · k / wt(h_0)` for some `k : ℤ`. -/

/-- A non-zero binary vector has positive Hamming weight. -/
theorem hammingWeight_pos_of_ne_zero {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    0 < hammingWeight v := by
  -- If `wt(v) = 0` then every coordinate of `v` is `0`, contradicting `v ≠ 0`.
  by_contra hle
  have hzero : hammingWeight v = 0 := by omega
  apply hv
  funext j
  -- From `hzero : ∑ i, (v i).val = 0` and each summand is in `ℕ`, every summand is `0`.
  unfold hammingWeight at hzero
  have hsum_zero : ∀ i ∈ (Finset.univ : Finset (Fin n)), (v i).val = 0 := by
    intro i _hi
    exact (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
  exact (ZMod.val_eq_zero (v j)).mp (hsum_zero j (Finset.mem_univ j))

/-- **Rational under non-degeneracy.** If `IsTransversalLogical` holds
at the uniform-angle phase and there exists a non-zero
`h ∈ row(H_X)`, then `θ` is a rational multiple of `2π`:
`θ = 2π · k / m` for some `k : ℤ` and positive `m : ℕ` (concretely,
`m = wt(h)`).

This is the first qualitative reduction of AJO Section III.A. It does
**not** require the non-triviality hypothesis on `g_L`. -/
theorem ajo_uniform_rational_of_nondegen
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_nondegen : ∃ h ∈ cssXLogicalSubspace H_X, h ≠ 0) :
    ∃ (k : ℤ) (m : ℕ), 0 < m ∧ θ * (m : ℝ) = 2 * Real.pi * (k : ℝ) := by
  obtain ⟨h, hh_mem, hh_ne⟩ := h_nondegen
  obtain ⟨k, hk⟩ := isTransversalLogical_uniform_zero_constraint h_trans hh_mem
  refine ⟨k, hammingWeight h, hammingWeight_pos_of_ne_zero hh_ne, hk⟩

/-- **Rational denominator from non-degeneracy.** Under the same
hypotheses as `ajo_uniform_rational_of_nondegen`, `θ = 2π · k / wt(h_0)`
for some non-zero `h_0 ∈ row(H_X)`. -/
theorem ajo_uniform_theta_eq_of_nondegen
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_nondegen : ∃ h ∈ cssXLogicalSubspace H_X, h ≠ 0) :
    ∃ (k : ℤ) (m : ℕ), 0 < m ∧ θ = 2 * Real.pi * (k : ℝ) / (m : ℝ) := by
  obtain ⟨k, m, hm_pos, hθ⟩ := ajo_uniform_rational_of_nondegen h_trans h_nondegen
  refine ⟨k, m, hm_pos, ?_⟩
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hm_pos
  field_simp
  linarith [hθ]

/-! ## Combined witness routes under non-degeneracy

Restatements of the AJOMain.lean witness routes, packaged with the
non-degeneracy hypothesis. The non-degeneracy hypothesis is consumed
to populate the witness's existence; the dyadic conclusion follows from
the underlying route. -/

/-- **Combined route 1 (non-degen + unit-vec).** Under non-degeneracy
and the existence of a free-on-Z-side qubit hit by *any*
`h ∈ row(H_X)`, the angle `θ` is dyadic.

This is a packaging convenience: the non-degeneracy hypothesis
(`∃ h ∈ row(H_X), h ≠ 0`) is not directly used in the conclusion, but
guarantees there is at least one X-stabilizer to work with. The
substantive route is `ajo_uniform_dyadic_of_unit_vec_route`. -/
theorem ajo_uniform_dyadic_of_nondegen_unit_vec
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (_h_nondegen : ∃ h ∈ cssXLogicalSubspace H_X, h ≠ 0)
    {j : Fin n} (hcol : ∀ i : Fin r_Z, H_Z i j = 0)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) (hhj : h j = 1) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) :=
  ajo_uniform_dyadic_of_unit_vec_route h_trans hcol hh hhj

/-- **Combined route 2 (non-degen + power-of-two weight).** If some
X-stabilizer has weight a power of two, `θ` is dyadic. The
non-degeneracy hypothesis is encoded by the power-of-two `h`: any
power-of-two-weight binary vector has positive Hamming weight, hence
is non-zero. -/
theorem ajo_uniform_dyadic_of_nondegen_pow_two_witness
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    {N : ℕ} (hwt : hammingWeight h = 2 ^ N) :
    ∃ (a : ℤ) (N' : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N') :=
  ajo_uniform_dyadic_of_h_pow_two h_trans hh hwt

/-- **The power-of-two witness in Route 2 supplies the non-degeneracy
hypothesis.** If `hammingWeight h = 2^N` then `h ≠ 0`. -/
theorem nondegen_of_pow_two_weight
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    {N : ℕ} (hwt : hammingWeight h = 2 ^ N) :
    ∃ h' ∈ cssXLogicalSubspace H_X, h' ≠ 0 := by
  refine ⟨h, hh, ?_⟩
  intro hzero
  rw [hzero] at hwt
  rw [hammingWeight_zero] at hwt
  -- `0 = 2^N` is false for any `N`.
  have h2N_pos : 0 < (2 : ℕ) ^ N := by positivity
  omega

/-- **Combined route 3 packaged (g_L-overlap power-of-two).** Under
non-degeneracy and a power-of-two `g_L ∧ h`-weight, the angle `θ` is
dyadic. -/
theorem ajo_uniform_dyadic_of_nondegen_gL_overlap_pow_two
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {g_L : Fin n → ZMod 2}
    (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    {N : ℕ} (hwt : hammingWeight (fun j => g_L j * h j) = 2 ^ N) :
    ∃ (a : ℤ) (N' : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N') :=
  ajo_uniform_dyadic_of_gL_overlap_pow_two h_carrier h_trans hh hwt

/-! ## Refined non-triviality consequences

The non-triviality hypothesis `∀ k, wt(g_L) · θ ≠ 2π · k` interacts
with the rational form `θ = 2π · k_0 / m`. In particular `m ∤ wt(g_L) ·
k_0` for the `k_0, m` from non-degeneracy. -/

/-- **Non-triviality forces an irrational quotient.** Under
non-degeneracy with `θ = 2π · k_0 / m`, the non-triviality
`wt(g_L) · θ ∉ 2π · ℤ` is equivalent to `m ∤ wt(g_L) · k_0`. -/
theorem nontriv_iff_not_dvd_of_rational
    {θ : ℝ} {g_L : Fin n → ZMod 2}
    {k_0 : ℤ} {m : ℕ} (hm : 0 < m)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m : ℝ)) :
    (∀ k : ℤ, (hammingWeight g_L : ℝ) * θ ≠ 2 * Real.pi * (k : ℝ)) ↔
      ¬ (m : ℤ) ∣ ((hammingWeight g_L : ℤ) * k_0) := by
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hm
  have htwopi : (2 : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  constructor
  · -- Suppose non-triviality. Show `m ∤ wt(g_L) · k_0`.
    intro hnt hdvd
    obtain ⟨q, hq⟩ := hdvd
    apply hnt q
    rw [hθ]
    have : (hammingWeight g_L : ℝ) * (2 * Real.pi * (k_0 : ℝ) / (m : ℝ)) =
        2 * Real.pi * ((hammingWeight g_L : ℝ) * (k_0 : ℝ) / (m : ℝ)) := by
      ring
    rw [this]
    -- Want `2π · ((wt(g_L) · k_0 : ℝ) / m) = 2π · (q : ℝ)`.
    have hqcast : ((hammingWeight g_L : ℤ) * k_0 : ℤ) = m * q := hq
    have hqcast_real : ((hammingWeight g_L : ℝ) * (k_0 : ℝ)) = (m : ℝ) * (q : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hqcast
      push_cast at this
      exact this
    rw [hqcast_real]
    field_simp
  · -- Suppose `m ∤ wt(g_L) · k_0`. Show non-triviality.
    intro hndvd k hk
    apply hndvd
    rw [hθ] at hk
    -- `hk : wt(g_L) · (2π · k_0 / m) = 2π · k`.
    -- Manipulate: `wt(g_L) · k_0 = m · k`.
    have : (hammingWeight g_L : ℝ) * (k_0 : ℝ) = (m : ℝ) * (k : ℝ) := by
      have h1 := hk
      field_simp at h1
      -- h1: wt(g_L) · 2π · k_0 = 2π · k · m
      nlinarith [h1, htwopi]
    refine ⟨k, ?_⟩
    -- Want `wt(g_L) · k_0 = m · k` over ℤ. We have it over ℝ.
    have hcast :
        ((hammingWeight g_L : ℤ) * k_0 : ℝ) = ((m : ℤ) * k : ℝ) := by
      push_cast
      exact this
    exact_mod_cast hcast

/-! ## What remains: the AJO odd-prime Möbius contradiction

Under non-degeneracy:

  * `θ = 2π · a / q` in lowest terms with `gcd(a, q) = 1`.
  * From non-triviality, `q ∤ wt(g_L) · a`, hence `q ∤ wt(g_L)`.
  * For every `h ∈ row(H_X)` and `v ∈ ker(H_Z)`,
    `q | wt(h) − 2·wt(v ∧ h)`.

The goal: show `q` is a power of two.

Equivalently: every odd prime `p` divides `q` only if it divides
`wt(g_L)`, contradicting `q ∤ wt(g_L)`.

The argument fixes an odd prime `p | q` and walks the chain:

  v = 0:           p | wt(h)              ∀ h ∈ row(H_X).
  v = g_i:         p | 2·wt(g_i ∧ h)      → p | wt(g_i ∧ h)
                                            (`p` odd) ∀ i, h.
  v = g_i + g_j:   By inclusion-exclusion (h_w_add_eq_sub) on `(g_i + g_j) ∧ h`:
                   `(g_i + g_j) ∧ h = g_i ∧ h + g_j ∧ h − 2·(g_i ∧ g_j ∧ h)`
                   ... wait, this is in `ZMod 2`, the `2·` collapses. So
                   `(g_i + g_j) ∧ h = (g_i ∧ h) + (g_j ∧ h)` in `ZMod 2`.
                   Apply `hammingWeight_add_eq_sub` to the *result*:
                   `wt((g_i + g_j) ∧ h) = wt(g_i ∧ h) + wt(g_j ∧ h)
                     − 2·wt(g_i ∧ g_j ∧ h)`.
                   `p | wt((g_i + g_j) ∧ h)`, `p | wt(g_i ∧ h)`,
                   `p | wt(g_j ∧ h)` give `p | 2·wt(g_i ∧ g_j ∧ h)`,
                   hence `p | wt(g_i ∧ g_j ∧ h)`.

By induction on `|S|`: `p | wt(overlap_S ∧ h)` for every non-empty
`S ⊆ Fin r_X` and every `h ∈ row(H_X)`. Specialising `h = ∏_{i ∈ T}
g_i` (which is itself in `row(H_X)` only when `T = {single i}`, so we
need a refinement) — actually, the cleaner statement is
`p | wt(overlap_S)` directly, derived from `v = (sum over I) ∈ row(H_X)`
and `h = g_j`.

For the logical: replace `v = (sum over I)` with `v = g_L + (sum over
I)`. The `v` is still in `ker(H_Z)` because `g_L ∈ ker(H_Z)` and
`row(H_X) ⊆ ker(H_Z)`. The trans-logical constraint then reads

  `p | wt(h) − 2·wt((g_L + sum_I) ∧ h)`
       = wt(h) − 2·(wt(g_L ∧ h) + wt(sum_I ∧ h) − 2·wt(g_L ∧ sum_I ∧ h))
                   (by inclusion-exclusion on `g_L + sum_I`)
       = wt(h) − 2·wt(g_L ∧ h) − 2·wt(sum_I ∧ h) + 4·wt(g_L ∧ sum_I ∧ h).

`p | wt(h)`, `p | wt(g_L ∧ h)` (from `v = g_L`), `p | wt(sum_I ∧ h)`
(after summing the inclusion-exclusion), so `p | 4·wt(g_L ∧ sum_I ∧
h)`. As `p` is odd, `p | wt(g_L ∧ sum_I ∧ h)`. Specialising
`h = g_j` etc and inducting gives `p | wt(g_L ∧ overlap_J)` for every
non-empty `J`.

The Möbius identity

  `∑_{J ⊆ Fin r_X, J ≠ ∅} (-1)^{|J| + 1} · wt(overlap_J) = wt(union)`,

  `∑_{J ⊆ Fin r_X, J ≠ ∅} (-1)^{|J| + 1} · wt(g_L ∧ overlap_J)
    = wt(g_L ∧ union)`,

then transfer `p | each summand` to `p | wt(union)` and `p |
wt(g_L ∧ union)`.

Finally, `wt(g_L) = wt(g_L ∧ union) + wt(g_L outside union)`. Since
`p | wt(g_L ∧ union)` but `p ∤ wt(g_L)`, we get `p ∤ wt(g_L outside
union)`. The "outside union" portion is the part of `g_L` not in the
support of *any* X-stabilizer generator. But this portion is a binary
vector whose support is disjoint from every X-stabilizer; equivalently
its support lies in the *complement* of `row(H_X)`'s union of
supports.

The AJO argument at this point invokes a "weight balance" that is
not formalised in this development.

**What this file provides** toward the argument:

* `supp : (Fin n → ZMod 2) → Finset (Fin n)` — support set of a binary
  vector.
* `hammingWeight_eq_card_supp` — `wt(v) = #(supp v)`.
* `supp_mul` — `supp(g₁ · g₂) = supp(g₁) ∩ supp(g₂)`.
* `supp_overlap_nonempty` — `supp(overlap g I) = ⋂_{i ∈ I} supp(g i)`
  for non-empty `I`.
* `hammingWeight_biUnion_supp_eq_inclusion_exclusion` — the Möbius
  formula at the F₂ side.

**What is not formalised here:**

* The `ZMod p` lift of the divisibility relations
  `q | wt(h) − 2·wt(v ∧ h)`, ranged over `v ∈ ker(H_Z)`.
* The inductive walk over compound `v` showing
  `p | wt(g_L ∧ overlap_I)` for all non-empty `I`, then summing the
  Möbius identity (with signs cancelling correctly modulo `p`) to get
  `p | wt(g_L ∧ ⋃ supp(g_i))`.
* The "extra-territorial" argument: `g_L` restricted to coordinates
  outside `⋃ supp(g_i)` must have weight divisible by `p` (since it
  contributes to the `v = g_L` constraint independently of any
  X-stabilizer overlap), and combined with `p ∤ wt(g_L)` we get the
  contradiction.
-/

/-! ### Documentation: inductive step required for the general proof

The statement of the divisibility walk required by the AJO Möbius
argument (recorded as documentation, not as a typed declaration):

```
ajo_inductive_step_target H_X H_Z g_L θ p :
  IsTransversalLogical (linearPhase (fun _ => θ)) H_X H_Z →
  g_L ∈ cssXLogicalCarrier H_Z →
  (∃ a q : ℤ, q ≠ 0 ∧ Int.gcd a q = 1 ∧ (p : ℤ) ∣ q ∧
    θ = 2π · a / q) →
  (∀ I : Finset (Fin r_X), I.Nonempty →
    (p : ℤ) ∣ wt(overlap H_X I)) ∧
  (∀ I : Finset (Fin r_X), I.Nonempty →
    (p : ℤ) ∣ wt(g_L ∧ overlap H_X I))
```

where `p` is an odd prime dividing the denominator `q` of `θ/(2π)`
in lowest terms.

This is the divisibility-walk conclusion of the Möbius induction:
every overlap (non-logical and logical) has weight divisible by every
odd prime `p` dividing the denominator `q`. From it, the AJO theorem
follows by inclusion-exclusion plus the non-triviality contradiction.

The proof of this step is **not** in this file; it is the
substantive content of AJO 2014 Section III.A. -/

/-! ## The general statement

The general theorem

```lean
theorem ajo_uniform_dyadic_general
    {n r_X r_Z : ℕ}
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    (h_nondegen : ∃ h ∈ cssXLogicalSubspace H_X, h ≠ 0)
    (g_L : Fin n → ZMod 2)
    (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_notInStab : g_L ∉ cssXLogicalSubspace H_X)
    (θ : ℝ)
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ)) :
    ∃ (a : ℤ) (N : ℕ), θ = 2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N)
```

is **NOT** proved in this file.

What this file *does* establish:

1. **`ajo_uniform_rational_of_nondegen`** — under non-degeneracy, `θ`
   is a rational multiple of `2π`. (Substantive first step.)

2. **`ajo_uniform_theta_eq_of_nondegen`** — explicit form
   `θ = 2π · k / m` for some `m > 0`.

3. **`nontriv_iff_not_dvd_of_rational`** — the non-triviality
   hypothesis in the rational regime is equivalent to a non-divisibility
   relation `m ∤ wt(g_L) · k_0`.

4. **Two-vector inclusion-exclusion identities** at the Hamming-weight
   level for the F₂-sum (`hammingWeight_add_eq_sub`) and the bitwise
   OR (`hammingWeight_bitOr_two`).

5. **Möbius / inclusion-exclusion identity for `r_X` generators**
   (`hammingWeight_biUnion_supp_eq_inclusion_exclusion`):

     `|⋃ supp(g_i)| = ∑_{I non-empty} (-1)^{|I|+1} · wt(overlap g I)`.

   Supporting infrastructure: `supp`, `hammingWeight_eq_card_supp`,
   `supp_mul`, `supp_overlap_nonempty`, `mem_supp_overlap_iff`.

6. **Packaging** of the three witness routes from `AJOMain.lean` to
   absorb the non-degeneracy hypothesis when it is supplied implicitly
   by the witness (`ajo_uniform_dyadic_of_nondegen_unit_vec`,
   `ajo_uniform_dyadic_of_nondegen_pow_two_witness`,
   `nondegen_of_pow_two_weight`).

What remains open: the inductive walk through `2^{r_X}` subsets of
generators using `ZMod p` divisibility, and the proof that
`p | wt(overlap_S)` and `p | wt(g_L ∧ overlap_S)` for all non-empty
`S ⊆ Fin r_X` under the odd-prime divisibility hypothesis. With
the Möbius identity now in place, the structure of the remaining
argument is:

* Derive `p | wt(overlap_I)` for all non-empty `I` by induction on
  `|I|`, using the trans-logical constraint at
  `v = ∑_{i ∈ J} g_i ∈ row(H_X) ⊆ ker(H_Z)` for `J ⊆ I`,
  `h = g_{i_0}` for `i_0 ∈ I \ J`, plus the F₂ identity
  `(∑_{i ∈ J} g_i) ∧ h = ∑_{i ∈ J} (g_i ∧ h)` and inductive elimination
  of lower-order overlap weights.

* Derive `p | wt(g_L ∧ overlap_I)` analogously, replacing
  `v = ∑_{i ∈ J} g_i` with `v = g_L + ∑_{i ∈ J} g_i ∈ ker(H_Z)`.

* Apply `hammingWeight_biUnion_supp_eq_inclusion_exclusion` to
  conclude `p | |⋃ supp(g_i)|` and `p | |supp(g_L) ∩ ⋃ supp(g_i)|`.

* The remaining "extra-territorial" reasoning (`g_L` outside
  `⋃ supp(g_i)`) reaches the AJO contradiction with non-triviality. -/

/-! ## Step 1: Lifting the trans-logical divisibility to ZMod p

Under the rational form `θ = 2π · k_0 / m_0` with `p` an odd prime
dividing `m_0` but not dividing `k_0`, the integer constraint
`θ · (transShift h v : ℝ) ∈ 2π · ℤ` lifts to the divisibility relation
`(p : ℤ) ∣ wt(h) - 2 · wt(v ∧ h)`. -/

/-- **Lifting the trans-logical constraint to integer divisibility by
`m_0`.** Given `θ = 2π · k_0 / m_0` with `m_0 > 0`, every trans-logical
constraint `θ · (wt(h) - 2·wt(v ∧ h) : ℝ) = 2π · k` rewrites as the
integer divisibility `(m_0 : ℤ) ∣ k_0 · (wt(h) - 2·wt(v ∧ h))`. -/
theorem dvd_of_trans_constraint
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {v h : Fin n → ZMod 2}
    {k : ℤ}
    (hk : θ * (((hammingWeight h : ℤ) -
              2 * (hammingWeight (fun j => v j * h j) : ℤ)) : ℝ) =
            2 * Real.pi * (k : ℝ)) :
    (m_0 : ℤ) ∣ k_0 *
      ((hammingWeight h : ℤ) -
        2 * (hammingWeight (fun j => v j * h j) : ℤ)) := by
  rw [hθ] at hk
  have hm_ne : (m_0 : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hm_0
  have h2π_ne : (2 : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  -- From `hk`, derive `k_0 · Δ = m_0 · k` where Δ is the integer combination.
  have hkey : (k_0 : ℝ) *
      ((hammingWeight h : ℝ) -
        2 * (hammingWeight (fun j => v j * h j) : ℝ)) =
      (m_0 : ℝ) * (k : ℝ) := by
    have h1 := hk
    push_cast at h1
    field_simp at h1
    nlinarith [h1, h2π_ne, Real.pi_pos]
  -- Cast `hkey` back to ℤ.
  have hcast :
      (k_0 * ((hammingWeight h : ℤ) -
              2 * (hammingWeight (fun j => v j * h j) : ℤ)) : ℤ) =
      ((m_0 : ℤ) * k : ℤ) := by
    have h2 : ((k_0 * ((hammingWeight h : ℤ) -
                  2 * (hammingWeight (fun j => v j * h j) : ℤ)) : ℤ) : ℝ) =
              (((m_0 : ℤ) * k : ℤ) : ℝ) := by
      push_cast
      linarith [hkey]
    exact_mod_cast h2
  exact ⟨k, hcast⟩

/-- **Step 1: ZMod p lift.** Suppose `θ = 2π · k_0 / m_0`, `p` is a prime
dividing `m_0` but not dividing `k_0`. Under the uniform-angle
trans-logical hypothesis, for every `v ∈ ker(H_Z)` and `h ∈ row(H_X)`,
`(p : ℤ) ∣ wt(h) - 2·wt(v ∧ h)`. -/
theorem ajo_dvd_of_trans
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    (p : ℤ) ∣
      (hammingWeight h : ℤ) -
        2 * (hammingWeight (fun j => v j * h j) : ℤ) := by
  obtain ⟨k, hk⟩ :=
    isTransversalLogical_uniform_logical_constraint h_trans hv hh
  have hdvd_m0 := dvd_of_trans_constraint hm_0 hθ hk
  have hp_dvd_prod : (p : ℤ) ∣ k_0 *
      ((hammingWeight h : ℤ) -
        2 * (hammingWeight (fun j => v j * h j) : ℤ)) :=
    dvd_trans hp_dvd_m0 hdvd_m0
  rcases Int.Prime.dvd_mul' hp_prime hp_dvd_prod with hk0 | hΔ
  · exact absurd hk0 hp_ndvd_k0
  · exact hΔ

/-- **Specialisation: p divides wt(h) for h in row(H_X).** Applies
`ajo_dvd_of_trans` at `v = 0`. -/
theorem ajo_dvd_wt_h
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    (p : ℤ) ∣ (hammingWeight h : ℤ) := by
  have hzero : (0 : Fin n → ZMod 2) ∈ cssXLogicalCarrier H_Z :=
    zero_mem_cssXLogicalCarrier H_Z
  have hres := ajo_dvd_of_trans hm_0 hθ h_trans hp_prime hp_dvd_m0
                hp_ndvd_k0 hzero hh
  -- `v = 0`: `v j * h j = 0` for all j, so wt(0 ∧ h) = 0.
  have h_and_zero : (fun j : Fin n => (0 : Fin n → ZMod 2) j * h j) = 0 := by
    funext j; simp
  rw [h_and_zero, hammingWeight_zero] at hres
  push_cast at hres
  simpa using hres

/-- **Specialisation: p odd ⟹ p | wt(v ∧ h) for v ∈ ker(H_Z), h ∈
row(H_X).** Combines `ajo_dvd_of_trans` (giving `p | wt(h) - 2·wt(v∧h)`)
with `ajo_dvd_wt_h` (giving `p | wt(h)`) and oddness of p. -/
theorem ajo_dvd_wt_and
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    (p : ℤ) ∣ (hammingWeight (fun j => v j * h j) : ℤ) := by
  have h1 := ajo_dvd_of_trans hm_0 hθ h_trans hp_prime hp_dvd_m0 hp_ndvd_k0 hv hh
  have h2 := ajo_dvd_wt_h hm_0 hθ h_trans hp_prime hp_dvd_m0 hp_ndvd_k0 hh
  -- From `p | wt(h) - 2·wt(v∧h)` and `p | wt(h)`: `p | 2·wt(v∧h)`.
  have h3 : (p : ℤ) ∣ 2 * (hammingWeight (fun j => v j * h j) : ℤ) := by
    have h4 := dvd_sub h2 h1
    -- `p | wt(h) - (wt(h) - 2·wt(v∧h)) = 2·wt(v∧h)`.
    have heq : (hammingWeight h : ℤ) -
        ((hammingWeight h : ℤ) -
          2 * (hammingWeight (fun j => v j * h j) : ℤ)) =
        2 * (hammingWeight (fun j => v j * h j) : ℤ) := by ring
    rwa [heq] at h4
  -- `p` odd ⟹ `p` and `2` are coprime ⟹ `p | wt(v∧h)`.
  rcases Int.Prime.dvd_mul' hp_prime h3 with h2div | hΔ
  · -- `p | 2`. Combined with `p` odd: contradiction.
    exfalso
    have hpdvd2 : p ∣ 2 := by
      have : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by exact_mod_cast h2div
      exact_mod_cast this
    have hp_eq : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd2 with heq | heq
      · exact absurd heq hp_prime.one_lt.ne'
      · exact heq
    rw [hp_eq] at hp_odd
    exact (Nat.not_odd_iff_even.mpr (by decide : Even 2)) hp_odd
  · exact hΔ

/-- **Each generator row `H_X i` lies in `cssXLogicalSubspace H_X`.**
This is the F₂-side statement that each X-stabilizer is itself in the
row space of `H_X` (equivalently, in the image of `H_Xᵀ`). The witness is
the unit vector `Pi.single i 1`. -/
theorem hx_row_mem_cssXLogicalSubspace
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) (i : Fin r_X) :
    (fun j : Fin n => H_X i j) ∈ cssXLogicalSubspace H_X := by
  refine ⟨Pi.single i 1, ?_⟩
  funext j
  -- mulVecLin H_Xᵀ (Pi.single i 1) = H_Xᵀ.col i (matrix transpose with single).
  -- (H_Xᵀ.col i) j = H_Xᵀ j i = H_X i j.
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  simp [Matrix.transpose_apply]

/-- **The F₂-sum of generators of `H_X` over a finset is in
`cssXLogicalSubspace H_X`.** This follows from the submodule structure
of `cssXLogicalSubspace H_X` and `hx_row_mem_cssXLogicalSubspace`. -/
theorem hx_sum_mem_cssXLogicalSubspace
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) (S : Finset (Fin r_X)) :
    (∑ i ∈ S, (fun j : Fin n => H_X i j)) ∈ cssXLogicalSubspace H_X :=
  Submodule.sum_mem _ (fun i _ => hx_row_mem_cssXLogicalSubspace H_X i)

/-! ## Step 2a: F₂-sum Möbius identity for Hamming weights

For binary vectors `x : Fin r_X → (Fin n → ZMod 2)` indexed by a finset
`S`, the Hamming weight of the F₂-sum `∑_{i ∈ S} x i` admits the
Möbius-type expansion

  `wt(∑_{i ∈ S} x i) = ∑_{∅ ≠ J ⊆ S} (-2)^{|J|-1} · wt(overlap x J)`

in `ℤ`. The proof is by induction on `|S|` using
`hammingWeight_add_eq_sub` (the two-vector inclusion-exclusion identity).
-/

/-- Pointwise distributivity of bitwise AND over `ZMod 2`-sum: for any
finset `T` and binary vectors `y : ι → (Fin n → ZMod 2)`, the AND with
a fixed vector `x` distributes:
`(∑_{i ∈ T} y i) ∧ x = ∑_{i ∈ T} (y i ∧ x)` pointwise in `ZMod 2`. -/
private lemma sum_mul_left (x : Fin n → ZMod 2)
    {ι : Type*} (T : Finset ι) (y : ι → Fin n → ZMod 2) :
    (fun j => (∑ i ∈ T, y i) j * x j) =
      ∑ i ∈ T, (fun j => y i j * x j) := by
  funext j
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_mul]

/-- The overlap of `(g_i ∧ h)` over a non-empty finset `J` equals
`overlap g J ∧ h`. Since `h * h = h` in `ZMod 2` and `J` is non-empty,
the repeated `h` factor collapses to a single `h`. -/
theorem overlap_mul_eq
    (g : Fin r_X → (Fin n → ZMod 2)) (h : Fin n → ZMod 2)
    {J : Finset (Fin r_X)} (hJ : J.Nonempty) :
    overlap (fun i => fun j => g i j * h j) J =
      (fun j => overlap g J j * h j) := by
  funext j
  unfold overlap
  -- LHS: ∏ i ∈ J, (g i j * h j) = (∏ i ∈ J, g i j) * h j ^ |J|.
  -- In ZMod 2, h j ^ |J| = h j (when J nonempty, since h j ∈ {0, 1}).
  rw [Finset.prod_mul_distrib]
  -- ∏ i ∈ J, h j = h j ^ J.card.
  rw [Finset.prod_const]
  -- Need: (∏ i, g i j) * (h j) ^ J.card = (∏ i, g i j) * h j.
  congr 1
  -- `(h j) ^ J.card = h j` in `ZMod 2` for `J.card ≥ 1`.
  obtain ⟨k, hk⟩ : ∃ k, J.card = k + 1 := ⟨J.card - 1, by
    have := hJ.card_pos
    omega⟩
  rw [hk]
  -- `(h j) ^ (k + 1) = (h j) ^ k * h j`.
  rw [pow_succ]
  -- Need `(h j) ^ k * h j = h j`, i.e., `(h j) ^ k * h j = h j`.
  -- In `ZMod 2`, every element satisfies `x ^ k * x = x` for `k ≥ 0` because:
  -- `x * x = x` (since `0^2 = 0` and `1^2 = 1`), so `x^k = x` for `k ≥ 1` and
  -- `x^0 = 1` so `x^0 * x = x`. Both cases give `x^k * x = x` either way:
  -- specifically `x * x = x`, so by induction `x^k = x` for `k ≥ 1`.
  -- Easier: case-analyse on `h j`.
  have hval : h j = 0 ∨ h j = 1 := by
    have hlt : (h j).val < 2 := ZMod.val_lt (h j)
    have hr : h j = ((h j).val : ZMod 2) := (ZMod.natCast_zmod_val (h j)).symm
    interval_cases (h j).val
    · left; rw [hr]; push_cast; rfl
    · right; rw [hr]; push_cast; rfl
  rcases hval with h0 | h1
  · rw [h0]; ring
  · rw [h1]; ring

/- An auxiliary "extended" Möbius sum that includes the `J = ∅` term:
`∑_{J ⊆ S} c_J · wt(overlap x J)` with the convention that the
contribution at `J = ∅` adds `(-1) · wt(overlap x ∅) = (-1) · n` (or
whatever pattern matches). Concretely we sum
`(-2)^{|J|-1} · wt(overlap x J)` over all `J`, with the natural-number
subtraction giving `(-2)^{0 - 1} = (-2)^0 = 1` at `J = ∅` because Lean's
`Nat` subtraction truncates: `(0 - 1) = 0`. So the `J = ∅` term in this
"loose" sum is `1 * wt(overlap x ∅) = n`, which is not what we want.

To avoid that, we explicitly subtract the `J = ∅` term, OR formulate the
sum over the filter to non-empty subsets. We take the latter approach. -/

/-- **F₂-sum Möbius identity (integer form, weak version).** For binary
vectors `x : Fin r_X → (Fin n → ZMod 2)`, the integer Hamming weight of
the F₂-sum admits the Möbius-type expansion over non-empty subsets:

`wt(∑_{i ∈ S} x i) = ∑_{∅ ≠ J ⊆ S} (-2)^{|J|-1} · wt(overlap x J)`.

Proof by induction on `|S|` using `hammingWeight_add_eq_sub`. -/
theorem hammingWeight_sum_mobius
    (x : Fin r_X → (Fin n → ZMod 2)) (S : Finset (Fin r_X)) :
    (hammingWeight (∑ i ∈ S, x i) : ℤ) =
      ∑ J ∈ S.powerset.filter (·.Nonempty),
        (-2 : ℤ) ^ (J.card - 1) * (hammingWeight (overlap x J) : ℤ) := by
  classical
  -- Induct on the cardinality of `S`, generalising over `x` and `S`.
  suffices h : ∀ N : ℕ, ∀ (x : Fin r_X → (Fin n → ZMod 2))
      (S : Finset (Fin r_X)), S.card = N →
      (hammingWeight (∑ i ∈ S, x i) : ℤ) =
        ∑ J ∈ S.powerset.filter (·.Nonempty),
          (-2 : ℤ) ^ (J.card - 1) * (hammingWeight (overlap x J) : ℤ) from
    h S.card x S rfl
  intro N
  induction N with
  | zero =>
    intro x S hS
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hS
    subst hS_empty
    -- LHS: wt(∑_{i ∈ ∅} x i) = wt(0) = 0.
    rw [Finset.sum_empty, hammingWeight_zero]
    push_cast
    -- RHS: sum over filter `(∅.powerset).filter (·.Nonempty)`.
    -- (∅.powerset) = {∅}; filtering for non-empty gives ∅; sum is 0.
    have h_filter_empty :
        (∅ : Finset (Fin r_X)).powerset.filter (·.Nonempty) = ∅ := by
      ext J
      simp [Finset.mem_filter]
    rw [h_filter_empty]
    simp
  | succ k ih =>
    intro x S hS
    -- pick an element of S
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀_mem⟩ := hSne
    set T := S.erase i₀ with hT_def
    have hi₀_T : i₀ ∉ T := Finset.notMem_erase i₀ S
    have hS_eq : S = insert i₀ T := (Finset.insert_erase hi₀_mem).symm
    have hT_card : T.card = k := by
      have hce := Finset.card_erase_of_mem hi₀_mem
      rw [← hT_def] at hce
      omega
    rw [hS_eq]
    -- LHS: wt(x i₀ + ∑_T x i).
    rw [Finset.sum_insert hi₀_T, hammingWeight_add_eq_sub]
    -- Apply IH at T.
    rw [ih (fun i => x i) T hT_card]
    -- The term wt(x i₀ ∧ ∑_T x i): rewrite the AND as a sum of ANDs.
    have h_distrib : (fun j => x i₀ j * (∑ i ∈ T, x i) j) =
        ∑ i ∈ T, (fun j => x i₀ j * x i j) := by
      funext j
      simp only [Finset.sum_apply, Finset.mul_sum]
    rw [h_distrib]
    -- Apply IH at family `fun i => (fun j => x i₀ j * x i j)` and finset T.
    rw [ih (fun i => fun j => x i₀ j * x i j) T hT_card]
    -- Now decompose the RHS sum over `insert i₀ T` into the two parts.
    have hsplit :
        (insert i₀ T).powerset.filter (·.Nonempty) =
          T.powerset.filter (·.Nonempty) ∪
          (T.powerset).image (insert i₀) := by
      ext J
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
        Finset.mem_image]
      constructor
      · rintro ⟨hJsub, hJne⟩
        by_cases hJi : i₀ ∈ J
        · right
          refine ⟨J.erase i₀, ?_, ?_⟩
          · intro a ha
            have ha' : a ∈ J := Finset.mem_of_mem_erase ha
            have hane : a ≠ i₀ := Finset.ne_of_mem_erase ha
            rcases Finset.mem_insert.mp (hJsub ha') with ha1 | ha2
            · exact absurd ha1 hane
            · exact ha2
          · rw [Finset.insert_erase hJi]
        · left
          refine ⟨?_, hJne⟩
          intro a ha
          rcases Finset.mem_insert.mp (hJsub ha) with ha1 | ha2
          · rw [ha1] at ha; exact absurd ha hJi
          · exact ha2
      · rintro (⟨hJT, hJne⟩ | ⟨J', hJ'T, rfl⟩)
        · refine ⟨?_, hJne⟩
          intro a ha
          exact Finset.mem_insert.mpr (Or.inr (hJT ha))
        · refine ⟨?_, ⟨i₀, Finset.mem_insert_self i₀ J'⟩⟩
          intro k' hk'
          rcases Finset.mem_insert.mp hk' with hk1 | hk2
          · rw [hk1]; exact Finset.mem_insert_self i₀ T
          · exact Finset.mem_insert.mpr (Or.inr (hJ'T hk2))
    rw [hsplit]
    -- The union is disjoint.
    have hdisj :
        Disjoint (T.powerset.filter (·.Nonempty)) (T.powerset.image (insert i₀)) := by
      rw [Finset.disjoint_left]
      intro J hJ1 hJ2
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ1
      simp only [Finset.mem_image, Finset.mem_powerset] at hJ2
      obtain ⟨J', hJ'T, hJeq⟩ := hJ2
      have hJi : i₀ ∈ J := hJeq ▸ Finset.mem_insert_self i₀ J'
      have : i₀ ∈ T := hJ1.1 hJi
      exact hi₀_T this
    rw [Finset.sum_union hdisj]
    -- The image sum: reparametrise via `Finset.sum_image`.
    have hinjOn : Set.InjOn (insert i₀ : Finset (Fin r_X) → Finset (Fin r_X))
        (T.powerset : Set (Finset (Fin r_X))) := by
      intro J' hJ' K' hK' hJK
      simp only [Finset.coe_powerset] at hJ' hK'
      have hJ'sub : J' ⊆ T := hJ'
      have hK'sub : K' ⊆ T := hK'
      have hi_notin_J' : i₀ ∉ J' := fun h => hi₀_T (hJ'sub h)
      have hi_notin_K' : i₀ ∉ K' := fun h => hi₀_T (hK'sub h)
      have heq : (insert i₀ J').erase i₀ = (insert i₀ K').erase i₀ := by
        rw [hJK]
      rwa [Finset.erase_insert hi_notin_J', Finset.erase_insert hi_notin_K'] at heq
    rw [Finset.sum_image hinjOn]
    -- Simplify each `(insert i₀ J').card = J'.card + 1` and `overlap x (insert i₀ J')`.
    -- LHS goal: wt(x i₀) + RHS_T - 2 * RHS_T_logical
    --   where RHS_T = ∑_{∅≠J⊆T} (-2)^{|J|-1} · wt(overlap x J)
    --   and   RHS_T_logical = ∑_{∅≠J⊆T} (-2)^{|J|-1} · wt(overlap (x_i₀ ∧ x) J)
    -- RHS goal: RHS_T + ∑_{J'⊆T} (-2)^{|insert i₀ J'|-1} · wt(overlap x (insert i₀ J')).
    -- We want to match `-2 · RHS_T_logical = ∑_{J'⊆T} (-2)^{|J'|} · wt(overlap (x_i₀ ∧ x) J')`
    -- with the second image sum.
    -- Identity: wt(overlap x (insert i₀ J')) = wt(overlap x J' ∧ x i₀) for i₀ ∉ J'.
    -- Identity: overlap (x_i₀ ∧ x) J = overlap x J ∧ x_i₀ for non-empty J.
    -- For J' = ∅: term is wt(x i₀).
    -- For ∅ ≠ J' ⊆ T: term is (-2)^{|J'|} · wt(overlap x J' ∧ x i₀).
    -- And -2 · ∑_{∅≠J⊆T}(-2)^{|J|-1} · wt(overlap x J ∧ x i₀)
    --     = ∑_{∅≠J⊆T} (-2)^{|J|} · wt(overlap x J ∧ x i₀).
    -- So the J=∅ image term (= wt(x i₀)) plus the J≠∅ image terms
    -- (matching -2·RHS_T_logical) combine to give the full image sum.
    -- We now do the algebraic manipulation.
    -- Split the image sum by whether J' = ∅ or J' ≠ ∅.
    have himg_split :
        ∑ J' ∈ T.powerset,
          ((-2 : ℤ) ^ ((insert i₀ J').card - 1) *
            (hammingWeight (overlap x (insert i₀ J')) : ℤ)) =
        ((-2 : ℤ) ^ ((insert i₀ (∅ : Finset (Fin r_X))).card - 1) *
            (hammingWeight (overlap x (insert i₀ ∅)) : ℤ)) +
        ∑ J' ∈ T.powerset.filter (·.Nonempty),
          ((-2 : ℤ) ^ ((insert i₀ J').card - 1) *
            (hammingWeight (overlap x (insert i₀ J')) : ℤ)) := by
      have hpset :
          T.powerset = insert (∅ : Finset (Fin r_X)) (T.powerset.filter (·.Nonempty)) := by
        ext J'
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · intro hJ'
          by_cases hne : J' = ∅
          · left; exact hne
          · right
            refine ⟨hJ', Finset.nonempty_iff_ne_empty.mpr hne⟩
        · rintro (rfl | ⟨hsub, _⟩)
          · exact Finset.empty_subset T
          · exact hsub
      conv_lhs => rw [hpset]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_filter, Finset.empty_subset, Finset.mem_powerset,
          true_and]
        exact Finset.not_nonempty_empty)]
    rw [himg_split]
    -- Simplify the J'=∅ term: `insert i₀ ∅ = {i₀}`, so |{i₀}| - 1 = 0, (-2)^0 = 1,
    -- overlap x {i₀} = x i₀, wt(x i₀).
    have h_empty_simp :
        ((-2 : ℤ) ^ ((insert i₀ (∅ : Finset (Fin r_X))).card - 1) *
          (hammingWeight (overlap x (insert i₀ ∅)) : ℤ)) =
        (hammingWeight (x i₀) : ℤ) := by
      have hsng : (insert i₀ (∅ : Finset (Fin r_X))) =
          ({i₀} : Finset (Fin r_X)) := rfl
      rw [hsng, Finset.card_singleton, overlap_singleton]
      simp
    rw [h_empty_simp]
    -- For the second part of the image sum (J' nonempty), use `overlap_mul_eq`
    -- and `overlap` of insert.
    have h_nonempty_simp :
        ∀ J' ∈ T.powerset.filter (·.Nonempty),
          ((-2 : ℤ) ^ ((insert i₀ J').card - 1) *
            (hammingWeight (overlap x (insert i₀ J')) : ℤ)) =
          (-2 : ℤ) ^ J'.card *
            (hammingWeight (overlap (fun i => fun j => x i₀ j * x i j) J') : ℤ) := by
      intro J' hJ'_mem
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ'_mem
      obtain ⟨hJ'sub, hJ'ne⟩ := hJ'_mem
      have hi_notin : i₀ ∉ J' := fun h => hi₀_T (hJ'sub h)
      have hcard : (insert i₀ J').card = J'.card + 1 := Finset.card_insert_of_notMem hi_notin
      rw [hcard]
      -- overlap x (insert i₀ J') = fun j => x i₀ j * overlap x J' j.
      have hov : overlap x (insert i₀ J') = fun j => x i₀ j * overlap x J' j := by
        funext j
        unfold overlap
        rw [Finset.prod_insert hi_notin]
      rw [hov]
      -- overlap (fun i => x i₀ * x i) J' = fun j => overlap x J' j * x i₀ j (for J' nonempty).
      have hov2 := overlap_mul_eq x (x i₀) hJ'ne
      -- We have: overlap (fun i j => x i j * x i₀ j) J' = fun j => overlap x J' j * x i₀ j.
      -- We need: overlap (fun i j => x i₀ j * x i j) J' = fun j => x i₀ j * overlap x J' j.
      -- These are equal (factors commute).
      have hov3 : overlap (fun i => fun j => x i₀ j * x i j) J' =
          fun j => x i₀ j * overlap x J' j := by
        funext j
        unfold overlap
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        ring_nf
        congr 1
        -- `(x i₀ j) ^ J'.card * (x i₀ j) collapses` — same lemma as overlap_mul_eq.
        obtain ⟨k, hk⟩ : ∃ k, J'.card = k + 1 := ⟨J'.card - 1, by
          have := hJ'ne.card_pos
          omega⟩
        rw [hk]
        have hval : x i₀ j = 0 ∨ x i₀ j = 1 := by
          have hlt : (x i₀ j).val < 2 := ZMod.val_lt _
          have hr : x i₀ j = ((x i₀ j).val : ZMod 2) := (ZMod.natCast_zmod_val _).symm
          interval_cases (x i₀ j).val
          · left; rw [hr]; push_cast; rfl
          · right; rw [hr]; push_cast; rfl
        rcases hval with h0 | h1
        · rw [h0]; ring
        · rw [h1]; ring
      rw [hov3]
      -- Now match `(-2)^(J'.card + 1 - 1) = (-2)^J'.card`.
      have hcard_simp : J'.card + 1 - 1 = J'.card := by omega
      rw [hcard_simp]
    -- Rewrite each summand in the second image sum using h_nonempty_simp.
    rw [Finset.sum_congr rfl h_nonempty_simp]
    -- The second image sum is `∑_{∅≠J⊆T} (-2)^{|J|} · wt(overlap (x i₀ ∧ x) J)`.
    -- This equals `-2 · ∑_{∅≠J⊆T} (-2)^{|J|-1} · wt(overlap (x i₀ ∧ x) J)`,
    -- which equals `-2 · wt(∑_T (x i₀ ∧ x))` by the (already-applied) IH at family
    -- `i ↦ x i₀ ∧ x i` and finset T.
    -- After the rw with `ih'`, the goal already has the substituted form. We finish
    -- by ring manipulation.
    -- Setup: rename for clarity.
    set A : ℤ := ∑ J ∈ T.powerset.filter (·.Nonempty),
      (-2 : ℤ) ^ (J.card - 1) * (hammingWeight (overlap x J) : ℤ) with hA
    set B : ℤ := ∑ J ∈ T.powerset.filter (·.Nonempty),
      (-2 : ℤ) ^ (J.card - 1) *
        (hammingWeight (overlap (fun i => fun j => x i₀ j * x i j) J) : ℤ) with hB
    -- The goal at this point is:
    -- (wt(x i₀) + A) - 2 * B = A + (wt(x i₀) + ∑_{∅≠J⊆T} (-2)^|J| · ...)
    -- We need: -2 · B = ∑_{∅≠J⊆T} (-2)^|J| · (...).
    have hB_rewrite :
        ∑ J ∈ T.powerset.filter (·.Nonempty),
          (-2 : ℤ) ^ J.card *
            (hammingWeight (overlap (fun i => fun j => x i₀ j * x i j) J) : ℤ) =
        -2 * B := by
      rw [hB, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJmem
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
      have hJne : J.Nonempty := hJmem.2
      obtain ⟨k', hk'⟩ : ∃ k, J.card = k + 1 := ⟨J.card - 1, by have := hJne.card_pos; omega⟩
      have h1 : (k' + 1) - 1 = k' := by omega
      have h2 : (1 + k') - 1 = k' := by omega
      rw [hk']
      rw [h1]
      ring
    rw [hB_rewrite]
    ring

/-! ## Step 2b: Subset induction for `p | wt(overlap g S ∧ h)`

Using the F₂-sum Möbius identity and Step 1's `ajo_dvd_wt_and`, we prove
by induction on `|S|` that for every `h ∈ row(H_X)` and every (possibly
empty) `S ⊆ Fin r_X`, the odd prime `p` divides
`wt(overlap (fun i => H_X i) S ∧ h)`. -/

/-- **A power of an odd prime is coprime to a power of 2.** This is the
arithmetic fact used to conclude `p | x` from `p | (-2)^k * x` when
`p` is odd. -/
private lemma odd_prime_ndvd_two_pow {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (k : ℕ) : ¬ (p : ℤ) ∣ ((-2 : ℤ) ^ k) := by
  intro hdvd
  -- `(-2)^k = (-1)^k * 2^k`, so `p | 2^k` (since `p ∤ (-1)^k`).
  -- p prime and p | 2^k implies p | 2.
  have habs : (p : ℤ).natAbs = p := Int.natAbs_natCast p
  have hp2k : p ∣ (2 ^ k : ℕ) := by
    have h1 : ((-2 : ℤ) ^ k).natAbs = 2 ^ k := by
      rw [Int.natAbs_pow]
      norm_num
    have h2 : (p : ℤ).natAbs ∣ ((-2 : ℤ) ^ k).natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
    rw [habs, h1] at h2
    exact h2
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2k
  -- p prime divides 2, so p = 2.
  have hp_eq : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with heq | heq
    · exact absurd heq hp.one_lt.ne'
    · exact heq
  -- But p is odd, contradiction.
  rw [hp_eq] at hodd
  exact (Nat.not_odd_iff_even.mpr (by decide : Even 2)) hodd

/-- **Step 2b (with-h inductive lemma).** For every odd prime `p`
dividing the denominator `m_0` of `θ/(2π) = k_0 / m_0` (with `p ∤ k_0`),
every `h ∈ row(H_X)`, and every `S ⊆ Fin r_X`,
`p ∣ wt(overlap (fun i => H_X i) S ∧ h)` (where `overlap g ∅ = 1`, so the
`S = ∅` case reduces to `p ∣ wt(h)`).

Proof by strong induction on `|S|`, using the F₂-sum Möbius identity
applied to the family `i ↦ (H_X i ∧ h)` and Step 1's `ajo_dvd_wt_and`
applied to `v = ∑_{i ∈ S} H_X i ∈ row(H_X) ⊆ ker(H_Z)`. The CSS pairing
hypothesis `hCSS : IsCSSPair H_X H_Z` ensures `row(H_X) ⊆ ker(H_Z)`. -/
theorem ajo_dvd_wt_overlap_and
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hCSS : IsCSSPair H_X H_Z)
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X)
    (S : Finset (Fin r_X)) :
    (p : ℤ) ∣
      (hammingWeight (fun j => overlap (fun i => fun j' => H_X i j') S j * h j) : ℤ) := by
  classical
  -- Strong induction on |S|.
  suffices hgoal : ∀ N : ℕ, ∀ S : Finset (Fin r_X), S.card = N →
      (p : ℤ) ∣
        (hammingWeight (fun j => overlap (fun i => fun j' => H_X i j') S j * h j) : ℤ) from
    hgoal S.card S rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hS
    by_cases hSne : S.Nonempty
    case neg =>
      -- S = ∅: overlap g ∅ = 1, so wt(overlap g ∅ ∧ h) = wt(h).
      rw [Finset.not_nonempty_iff_eq_empty] at hSne
      subst hSne
      have h_overlap_one :
          (fun j : Fin n => overlap (fun i => fun j' : Fin n => H_X i j')
            (∅ : Finset (Fin r_X)) j * h j) = h := by
        funext j
        rw [overlap_empty]
        ring
      rw [h_overlap_one]
      exact ajo_dvd_wt_h hm_0 hθ h_trans hp_prime hp_dvd_m0 hp_ndvd_k0 hh
    case pos =>
      -- S non-empty.
      -- Step A: Set v_S = ∑_{i ∈ S} H_X i ∈ row(H_X) ⊆ ker(H_Z).
      set vS := (∑ i ∈ S, (fun j : Fin n => H_X i j)) with hvS_def
      have hvS_subspace : vS ∈ cssXLogicalSubspace H_X :=
        hx_sum_mem_cssXLogicalSubspace H_X S
      have hvS_carrier : vS ∈ cssXLogicalCarrier H_Z :=
        cssXLogicalSubspace_le_cssXLogicalCarrier hCSS hvS_subspace
      -- Step B: Apply trans-logical at (v_S, h) to get p | wt(v_S ∧ h).
      have hp_dvd_vS_and_h :=
        ajo_dvd_wt_and hm_0 hθ h_trans hp_prime hp_odd hp_dvd_m0 hp_ndvd_k0
          hvS_carrier hh
      -- Step C: Rewrite wt(v_S ∧ h) using F₂-sum Möbius.
      have hvS_and_h_eq :
          (fun j : Fin n => vS j * h j) =
            ∑ i ∈ S, (fun j : Fin n => H_X i j * h j) := by
        funext j
        simp only [hvS_def, Finset.sum_apply, Finset.sum_mul]
      rw [hvS_and_h_eq] at hp_dvd_vS_and_h
      -- Apply hammingWeight_sum_mobius at family `fun i j => H_X i j * h j` and S.
      rw [hammingWeight_sum_mobius (fun i => fun j => H_X i j * h j) S]
        at hp_dvd_vS_and_h
      -- Step D: Rewrite each `overlap (fun i j => H_X i j * h j) J` for non-empty J
      -- as `fun j => overlap (fun i => H_X i) J j * h j` using `overlap_mul_eq`.
      have hov_rewrite :
          ∀ J ∈ S.powerset.filter (·.Nonempty),
            (-2 : ℤ) ^ (J.card - 1) *
              (hammingWeight (overlap (fun i => fun j => H_X i j * h j) J) : ℤ) =
            (-2 : ℤ) ^ (J.card - 1) *
              (hammingWeight
                (fun j => overlap (fun i => fun j' : Fin n => H_X i j') J j * h j) : ℤ) := by
        intro J hJmem
        simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
        obtain ⟨_, hJne⟩ := hJmem
        congr 1
        rw [overlap_mul_eq (fun i => fun j' : Fin n => H_X i j') h hJne]
      rw [Finset.sum_congr rfl hov_rewrite] at hp_dvd_vS_and_h
      -- Step E: Isolate the J = S term.
      have hS_mem_filter : S ∈ S.powerset.filter (·.Nonempty) := by
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.Subset.refl S, hSne⟩
      rw [← Finset.add_sum_erase _ _ hS_mem_filter] at hp_dvd_vS_and_h
      -- All "other" terms are divisible by p by induction.
      have hp_dvd_others :
          (p : ℤ) ∣
            ∑ J ∈ (S.powerset.filter (·.Nonempty)).erase S,
              (-2 : ℤ) ^ (J.card - 1) *
                (hammingWeight
                  (fun j => overlap (fun i => fun j' : Fin n => H_X i j') J j *
                    h j) : ℤ) := by
        refine Finset.dvd_sum ?_
        intro J hJmem
        rw [Finset.mem_erase] at hJmem
        obtain ⟨hJne_S, hJmem_filter⟩ := hJmem
        simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem_filter
        obtain ⟨hJsubS, _⟩ := hJmem_filter
        -- |J| < |S| since J ⊆ S and J ≠ S.
        have hJcard_lt : J.card < S.card :=
          Finset.card_lt_card
            ⟨hJsubS, fun hSJ => hJne_S (Finset.Subset.antisymm hJsubS hSJ)⟩
        -- Apply IH at J. Card constraint: rewrite via hS.
        have ih_J := ih J.card (by rw [← hS]; exact hJcard_lt) J rfl
        exact dvd_mul_of_dvd_right ih_J _
      -- From `p | (lead_term) + (others)` and `p | (others)`, get `p | (lead_term)`.
      have hp_dvd_lead :
          (p : ℤ) ∣
            (-2 : ℤ) ^ (S.card - 1) *
              (hammingWeight
                (fun j => overlap (fun i => fun j' : Fin n => H_X i j') S j *
                  h j) : ℤ) := by
        have := dvd_sub hp_dvd_vS_and_h hp_dvd_others
        simpa using this
      -- Step F: Since p odd, p coprime to (-2)^(|S|-1); conclude p | wt.
      rcases Int.Prime.dvd_mul' hp_prime hp_dvd_lead with hp_dvd_pow | hp_dvd_wt
      · exact absurd hp_dvd_pow (odd_prime_ndvd_two_pow hp_prime hp_odd _)
      · exact hp_dvd_wt

/-! ## Step 3: Divisibility of `wt(g_L ∧ overlap g I)` and Möbius

By Step 1 applied at `v = g_L` and `h = ∑_{i ∈ S} g_i ∈ row(H_X)`,
combined with F₂-sum Möbius, we obtain the parallel divisibility result
`p ∣ wt(g_L ∧ overlap g I)` for every non-empty `I ⊆ Fin r_X`.

The Möbius identity `wt(g_L ∧ ⋃ supp(g_i)) = ∑ (-1)^{|I|+1} ·
wt(g_L ∧ overlap g I)` then gives `p ∣ wt(g_L ∧ ⋃ supp(g_i))`. -/

/-- **The F₂-sum of a non-empty subset of generators lies in
`row(H_X)`.** Same as `hx_sum_mem_cssXLogicalSubspace` but specialised
to the form used downstream. -/
private lemma sum_gen_mem_subspace
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) (S : Finset (Fin r_X)) :
    (∑ i ∈ S, (fun j : Fin n => H_X i j)) ∈ cssXLogicalSubspace H_X :=
  hx_sum_mem_cssXLogicalSubspace H_X S

/-- **Step 3 (logical-overlap divisibility).** Under the same hypotheses
as `ajo_dvd_wt_overlap_and`, for every `g_L ∈ ker(H_Z)` and every
non-empty `I ⊆ Fin r_X`:
`p ∣ wt(g_L ∧ overlap (fun i => H_X i) I)`.

Proof by strong induction on `|I|`, using `ajo_dvd_of_trans` at
`(v = g_L, h = ∑_{i ∈ I} H_X i)` and F₂-sum Möbius. -/
theorem ajo_dvd_wt_gL_overlap
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    {I : Finset (Fin r_X)} (hI : I.Nonempty) :
    (p : ℤ) ∣
      (hammingWeight
        (fun j => g_L j * overlap (fun i => fun j' : Fin n => H_X i j') I j) : ℤ) := by
  classical
  -- Strong induction on |I|.
  suffices hgoal : ∀ N : ℕ, ∀ I : Finset (Fin r_X), I.card = N → I.Nonempty →
      (p : ℤ) ∣
        (hammingWeight
          (fun j => g_L j * overlap (fun i => fun j' : Fin n => H_X i j') I j) : ℤ) from
    hgoal I.card I rfl hI
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro I hI_card hI_ne
    -- Apply trans-logical at v = g_L, h = ∑_{i ∈ I} H_X i ∈ row(H_X).
    set hI_sum := (∑ i ∈ I, (fun j : Fin n => H_X i j)) with hI_sum_def
    have hI_sum_mem : hI_sum ∈ cssXLogicalSubspace H_X :=
      sum_gen_mem_subspace H_X I
    -- Step A: get p | wt(h_I_sum).
    have hp_dvd_wt_hI :=
      ajo_dvd_wt_h hm_0 hθ h_trans hp_prime hp_dvd_m0 hp_ndvd_k0 hI_sum_mem
    -- Step B: get p | wt(g_L ∧ h_I_sum) via trans-logical and oddness.
    have hp_dvd_gL_and_hI :=
      ajo_dvd_wt_and hm_0 hθ h_trans hp_prime hp_odd hp_dvd_m0 hp_ndvd_k0
        h_carrier hI_sum_mem
    -- Step C: Rewrite g_L ∧ h_I_sum as ∑_{i ∈ I} (g_L ∧ H_X i).
    have hgL_and_sum_eq :
        (fun j : Fin n => g_L j * hI_sum j) =
          ∑ i ∈ I, (fun j : Fin n => g_L j * H_X i j) := by
      funext j
      simp only [hI_sum_def, Finset.sum_apply, Finset.mul_sum]
    rw [hgL_and_sum_eq] at hp_dvd_gL_and_hI
    -- Apply Möbius at family `i ↦ g_L ∧ H_X i` and I.
    rw [hammingWeight_sum_mobius (fun i => fun j => g_L j * H_X i j) I]
      at hp_dvd_gL_and_hI
    -- Step D: For non-empty J, rewrite
    -- overlap (fun i j => g_L j * H_X i j) J = fun j => overlap H_X J j * g_L j.
    have hov_rewrite :
        ∀ J ∈ I.powerset.filter (·.Nonempty),
          (-2 : ℤ) ^ (J.card - 1) *
            (hammingWeight (overlap (fun i => fun j => g_L j * H_X i j) J) : ℤ) =
          (-2 : ℤ) ^ (J.card - 1) *
            (hammingWeight
              (fun j => g_L j *
                overlap (fun i => fun j' : Fin n => H_X i j') J j) : ℤ) := by
      intro J hJmem
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
      obtain ⟨_, hJne⟩ := hJmem
      have hcom : (fun i => fun j : Fin n => g_L j * H_X i j) =
          (fun i => fun j : Fin n => H_X i j * g_L j) := by
        funext i j; ring
      have hov_step : overlap (fun i => fun j : Fin n => g_L j * H_X i j) J =
          fun j => g_L j *
            overlap (fun i => fun j' : Fin n => H_X i j') J j := by
        rw [hcom, overlap_mul_eq (fun i => fun j' : Fin n => H_X i j') g_L hJne]
        funext j; ring
      rw [hov_step]
    rw [Finset.sum_congr rfl hov_rewrite] at hp_dvd_gL_and_hI
    -- Step E: Isolate J = I.
    have hI_mem_filter : I ∈ I.powerset.filter (·.Nonempty) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.refl I, hI_ne⟩
    rw [← Finset.add_sum_erase _ _ hI_mem_filter] at hp_dvd_gL_and_hI
    -- All "other" terms divisible by p by induction.
    have hp_dvd_others :
        (p : ℤ) ∣
          ∑ J ∈ (I.powerset.filter (·.Nonempty)).erase I,
            (-2 : ℤ) ^ (J.card - 1) *
              (hammingWeight
                (fun j => g_L j *
                  overlap (fun i => fun j' : Fin n => H_X i j') J j) : ℤ) := by
      refine Finset.dvd_sum ?_
      intro J hJmem
      rw [Finset.mem_erase] at hJmem
      obtain ⟨hJne_I, hJmem_filter⟩ := hJmem
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem_filter
      obtain ⟨hJsubI, hJne⟩ := hJmem_filter
      have hJcard_lt : J.card < I.card :=
        Finset.card_lt_card
          ⟨hJsubI, fun hIJ => hJne_I (Finset.Subset.antisymm hJsubI hIJ)⟩
      have ih_J := ih J.card (by rw [← hI_card]; exact hJcard_lt) J rfl hJne
      exact dvd_mul_of_dvd_right ih_J _
    -- Combine to get p | (-2)^(|I|-1) · wt(g_L ∧ overlap H_X I).
    have hp_dvd_lead :
        (p : ℤ) ∣
          (-2 : ℤ) ^ (I.card - 1) *
            (hammingWeight
              (fun j => g_L j *
                overlap (fun i => fun j' : Fin n => H_X i j') I j) : ℤ) := by
      have := dvd_sub hp_dvd_gL_and_hI hp_dvd_others
      simpa using this
    rcases Int.Prime.dvd_mul' hp_prime hp_dvd_lead with hp_dvd_pow | hp_dvd_wt
    · exact absurd hp_dvd_pow (odd_prime_ndvd_two_pow hp_prime hp_odd _)
    · exact hp_dvd_wt

/-- **Step 3 (Möbius for `g_L ∧ ⋃ supp(g_i)`).** From Step 3's
`ajo_dvd_wt_gL_overlap`, applied to every non-empty subset and combined
with the integer Möbius identity, we obtain
`p ∣ |supp(g_L) ∩ ⋃ supp(g_i)|`.

The integer-side Möbius identity comes from
`hammingWeight_biUnion_supp_eq_inclusion_exclusion` applied to the
family `i ↦ g_L ∧ H_X i` (i.e., `g_L · H_X i`). -/
theorem ajo_dvd_card_gL_biUnion
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z) :
    (p : ℤ) ∣
      ((Finset.univ.biUnion
        (fun i : Fin r_X =>
          supp (fun j => g_L j * H_X i j))).card : ℤ) := by
  classical
  -- The bi-union Möbius identity gives the cardinality as an alternating sum
  -- of `wt(overlap (fun i => g_L ∧ H_X i) I)` over non-empty subsets.
  -- The family `fun i => g_L ∧ H_X i` has overlaps that equal
  -- `g_L ∧ overlap H_X I` for non-empty I, by `overlap_mul_eq`.
  rw [hammingWeight_biUnion_supp_eq_inclusion_exclusion
      (fun i => fun j => g_L j * H_X i j)]
  refine Finset.dvd_sum ?_
  rintro ⟨t, ht⟩ _
  have ht_ne : t.Nonempty := (Finset.mem_filter.mp ht).2
  have hcom : (fun i => fun j : Fin n => g_L j * H_X i j) =
      (fun i => fun j : Fin n => H_X i j * g_L j) := by
    funext i j; ring
  have hov : overlap (fun i => fun j => g_L j * H_X i j) t =
      fun j => g_L j * overlap (fun i => fun j' : Fin n => H_X i j') t j := by
    rw [hcom, overlap_mul_eq (fun i => fun j' : Fin n => H_X i j') g_L ht_ne]
    funext j; ring
  rw [hov]
  have hp_dvd_wt :=
    ajo_dvd_wt_gL_overlap hm_0 hθ h_trans hp_prime hp_odd hp_dvd_m0 hp_ndvd_k0
      h_carrier ht_ne
  exact dvd_mul_of_dvd_right hp_dvd_wt _

/-! ## Step 4: Closing the contradiction

The Möbius result from Step 3 gives `p ∣ |supp(g_L) ∩ ⋃ supp(g_i)|`.
Combined with non-triviality `p ∤ wt(g_L)`, the integer identity

  `wt(g_L) = |supp(g_L) ∩ ⋃ supp(g_i)| + |supp(g_L) ∖ ⋃ supp(g_i)|`

forces `p ∤ |supp(g_L) ∖ ⋃ supp(g_i)|`. So if `g_L` has no "extra-
territorial" coordinates (every qubit in `supp(g_L)` is hit by some
X-stabilizer), then `supp(g_L) ∖ ⋃ supp(g_i) = ∅`, hence
`p ∣ |supp(g_L) ∖ ⋃ supp(g_i)|` (trivially), contradiction.

We formulate the closing theorem with the **well-supported logical
hypothesis** `h_wellSupp : ∀ j ∈ supp g_L, ∃ i, g_i j = 1`. -/

/-- **Step 4 closure (well-supported case).** Under all the AJO
hypotheses (non-degeneracy yielding `θ = 2π · k_0 / m_0`,
non-triviality yielding `p ∤ k_0` for some odd prime `p ∣ m_0`),
plus the well-supported assumption that every qubit in `supp(g_L)` is
hit by some X-stabilizer, derive a contradiction. -/
theorem ajo_step4_wellSupp_contradiction
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_ndvd_gL : ¬ (p : ℤ) ∣ (hammingWeight g_L : ℤ))
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    False := by
  classical
  -- From Step 3, `p ∣ |supp(g_L) ∩ ⋃ supp(g_L * H_X i)|`.
  have hp_dvd_bU := ajo_dvd_card_gL_biUnion hm_0 hθ h_trans hp_prime hp_odd
    hp_dvd_m0 hp_ndvd_k0 h_carrier
  -- Under well-support, `supp(g_L) ⊆ ⋃_i supp(g_L * H_X i)`. So
  -- `supp(g_L) ∩ ⋃ supp(g_L * H_X i) = supp(g_L)`, with cardinality = wt(g_L).
  have h_eq : Finset.univ.biUnion
      (fun i : Fin r_X => supp (fun j => g_L j * H_X i j)) = supp g_L := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hij⟩
      -- j ∈ supp(g_L * H_X i): g_L j * H_X i j = 1.
      unfold supp at hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
      -- In ZMod 2: product = 1 iff both = 1.
      have hgL_one : g_L j = 1 := by
        have hvm := zmod_two_val_mul (g_L j) (H_X i j)
        have h1 : (g_L j * H_X i j).val = 1 := by
          rw [hij]
          haveI : Fact (1 < 2) := ⟨one_lt_two⟩
          exact ZMod.val_one 2
        rw [hvm] at h1
        have hg_lt : (g_L j).val < 2 := ZMod.val_lt _
        have hH_lt : (H_X i j).val < 2 := ZMod.val_lt _
        have : (g_L j).val = 1 := by
          interval_cases (g_L j).val <;> interval_cases (H_X i j).val <;> simp_all
        rw [(ZMod.natCast_zmod_val (g_L j)).symm, this]
        push_cast
        rfl
      unfold supp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hgL_one
    · intro hj
      -- j ∈ supp(g_L): g_L j = 1. Find an i with H_X i j = 1.
      unfold supp at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨i, hH⟩ := h_wellSupp j hj
      refine ⟨i, ?_⟩
      unfold supp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hj, hH]; ring
  rw [h_eq] at hp_dvd_bU
  rw [← hammingWeight_eq_card_supp] at hp_dvd_bU
  exact h_ndvd_gL hp_dvd_bU

/-! ## AJO general theorem (well-supported case)

Combining all four steps with appropriate factorisation arguments
yields the **AJO uniform-angle dyadic theorem** under the hypotheses:

* Non-degeneracy: `cssXLogicalSubspace H_X` contains a non-zero element.
* Trans-logical: `IsTransversalLogical` for the uniform-angle phase.
* Non-triviality: `wt(g_L) · θ ∉ 2π · ℤ`.
* CSS pairing: `IsCSSPair H_X H_Z`.
* Well-supported logical: every qubit in `supp(g_L)` is hit by some
  X-stabilizer.

The conclusion is that `θ` is a dyadic multiple of `2π`.

The argument proceeds by contradiction: assume `θ` is not dyadic, so the
denominator `q` of `θ/(2π)` in lowest terms has an odd prime factor `p`.
Steps 1–4 then derive `p ∣ wt(g_L)`, contradicting `p ∤ wt(g_L)` (which
follows from non-triviality and `gcd(k_0, q) = 1`). -/

/-- **AJO closure: odd-prime divisor of `m_0` divides `wt(g_L)`.**
This packages Steps 1–4 into a single statement: for every odd prime
`p` dividing the denominator `m_0` of `θ/(2π) = k_0 / m_0` (with
`p ∤ k_0`), under non-degeneracy, well-supported logical, and CSS
pairing, `p ∣ wt(g_L)`.

This is the substantive logical content of the AJO Möbius walk. -/
theorem ajo_odd_prime_dvd_wt_gL
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p)
    (hp_dvd_m0 : (p : ℤ) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    (p : ℤ) ∣ (hammingWeight g_L : ℤ) := by
  by_contra h_ndvd
  exact ajo_step4_wellSupp_contradiction hm_0 hθ h_trans hp_prime hp_odd
    hp_dvd_m0 hp_ndvd_k0 h_carrier h_ndvd h_wellSupp

end FTQCLib.Codes

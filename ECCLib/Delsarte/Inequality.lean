/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Shell
import ECCLib.Delsarte.Distribution

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The Delsarte inequalities (the analytic half of the LP bound)

`delsarte_nonneg`: for ANY code (a bare `Finset` of words over a finite abelian
alphabet) and every degree `k`, the Krawtchouk transform of the distance distribution
is nonnegative — `0 ≤ Σᵢ Nᵢ·K_k(i)` in ℤ. Reference: the Delsarte inequalities,
Cohn–Zhao arXiv:1212.1913 §II / McKinley 2003 Thm 4.2.1, whose `0 ≤ ‖yE_k‖²` proof
shape is exactly the route here.

Proof architecture (cast discipline: one type per lemma, never regroup and cast in the
same step): the ℤ-valued regroup `sum_pairCount_mul` turns
the transform into a sum over ordered codeword pairs; the ℂ-valued spectral identity
`delsarte_spectral` evaluates it — through the shell identity — as a sum of
squared magnitudes of code character sums over the dual shell; nonnegativity descends
ℂ → ℝ → ℤ.

`IsInnerDistribution` packages the four facts every code's distance distribution
satisfies (`delsarte_feasible`); the LP bound (`Delsarte/LP.lean`) consumes ONLY this
abstract, character-free data.
-/

namespace ECCLib.Delsarte

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Regroup

variable {β : Type*} [DecidableEq β]

omit [DecidableEq ι] in
/-- The ℤ-valued regroup: the transform of the distance distribution is the pair sum. -/
theorem sum_pairCount_mul (C : Finset (ι → β)) (g : ℕ → ℤ) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1), (pairCount C i : ℤ) * g i
      = ∑ p ∈ C ×ˢ C, g (hammingDist p.1 p.2) := by
  rw [← Finset.sum_fiberwise_of_maps_to'
    (g := fun p : (ι → β) × (ι → β) => hammingDist p.1 p.2)
    (t := Finset.range (Fintype.card ι + 1))
    (fun p _ => Finset.mem_range.mpr (Nat.lt_succ_of_le hammingDist_le_card_fintype)) g]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

end Regroup

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The code character sum `S(χ) = Σ_{x∈C} tupleChar χ x` — the object whose squared
magnitude carries the positivity. -/
noncomputable def codeChar (C : Finset (ι → A)) (χ : ι → AddChar A ℂ) : ℂ :=
  ∑ x ∈ C, tupleChar χ x

omit [DecidableEq ι] [Fintype A] [DecidableEq A] in
theorem tupleChar_add (χ : ι → AddChar A ℂ) (u v : ι → A) :
    tupleChar χ (u + v) = tupleChar χ u * tupleChar χ v := by
  unfold tupleChar
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    simpa using AddChar.map_add_eq_mul (χ i) (u i) (v i)

omit [DecidableEq ι] [DecidableEq A] in
theorem tupleChar_neg (χ : ι → AddChar A ℂ) (u : ι → A) :
    tupleChar χ (-u) = (starRingEnd ℂ) (tupleChar χ u) := by
  unfold tupleChar
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by
    simpa using AddChar.map_neg_eq_conj (χ i) (u i)

/-- **The spectral identity**: the (ℂ-cast) Krawtchouk transform of the distance
distribution equals the sum of squared magnitudes of the code character sums over the
dual weight-`k` shell. -/
theorem delsarte_spectral (C : Finset (ι → A)) (k : ℕ) :
    ((∑ i ∈ Finset.range (Fintype.card ι + 1),
        (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i : ℤ) : ℂ)
      = ∑ χ ∈ Finset.univ.filter (fun χ : ι → AddChar A ℂ => hammingNorm χ = k),
          ((Complex.normSq (codeChar C χ) : ℝ) : ℂ) := by
  have h1 : ((∑ i ∈ Finset.range (Fintype.card ι + 1),
      (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i : ℤ) : ℂ)
      = ∑ p ∈ C ×ˢ C,
          ((kraw (Fintype.card A) (Fintype.card ι) k (hammingDist p.1 p.2) : ℤ) : ℂ) := by
    rw [sum_pairCount_mul]
    push_cast
    rfl
  have h2 : ∀ p ∈ C ×ˢ C,
      ((kraw (Fintype.card A) (Fintype.card ι) k (hammingDist p.1 p.2) : ℤ) : ℂ)
        = ∑ χ ∈ Finset.univ.filter (fun χ : ι → AddChar A ℂ => hammingNorm χ = k),
            tupleChar χ (-p.1 + p.2) := by
    intro p _
    rw [hammingDist_eq_hammingNorm, ← charShellSum]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hsplit : ∀ p : (ι → A) × (ι → A), tupleChar χ (-p.1 + p.2)
      = (starRingEnd ℂ) (tupleChar χ p.1) * tupleChar χ p.2 := by
    intro p
    rw [tupleChar_add, tupleChar_neg]
  rw [Finset.sum_congr rfl fun p _ => hsplit p,
    Finset.sum_product' (s := C) (t := C)
      (f := fun x y => (starRingEnd ℂ) (tupleChar χ x) * tupleChar χ y),
    ← Finset.sum_mul_sum, ← map_sum]
  rw [show (∑ x ∈ C, tupleChar χ x) = codeChar C χ from rfl]
  rw [mul_comm, Complex.mul_conj]

omit [DecidableEq ι] in
/-- **The Delsarte inequalities** (ℤ-valued, arbitrary code, arbitrary finite abelian
alphabet): the Krawtchouk transform of the distance distribution is nonnegative. -/
theorem delsarte_nonneg (C : Finset (ι → A)) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (Fintype.card ι + 1),
          (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i := by
  classical
  have h := delsarte_spectral C k
  rw [← Complex.ofReal_sum] at h
  have hr : ((∑ i ∈ Finset.range (Fintype.card ι + 1),
      (pairCount C i : ℤ) * kraw (Fintype.card A) (Fintype.card ι) k i : ℤ) : ℝ)
      = ∑ χ ∈ Finset.univ.filter (fun χ : ι → AddChar A ℂ => hammingNorm χ = k),
          Complex.normSq (codeChar C χ) := by
    exact_mod_cast h
  have hnn : (0 : ℝ) ≤ ∑ χ ∈ Finset.univ.filter
      (fun χ : ι → AddChar A ℂ => hammingNorm χ = k), Complex.normSq (codeChar C χ) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [← hr] at hnn
  exact_mod_cast hnn

/-- The abstract feasibility data of a distance distribution — everything the LP bound
consumes, character-free (Cohn–Zhao's quasicode constraints, unnormalised). -/
structure IsInnerDistribution (q n d : ℕ) (N : ℕ → ℕ) (m : ℕ) : Prop where
  zero : N 0 = m
  total : ∑ i ∈ Finset.range (n + 1), N i = m ^ 2
  gap : ∀ i, 0 < i → i < d → N i = 0
  psd : ∀ k, 0 ≤ ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n k i

omit [DecidableEq ι] in
/-- Every code's distance distribution is feasible. -/
theorem delsarte_feasible {d : ℕ} (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    IsInnerDistribution (Fintype.card A) (Fintype.card ι) d (pairCount C) C.card where
  zero := pairCount_zero C
  total := sum_pairCount C
  gap := fun _ h0 hi => pairCount_eq_zero_of_lt hd (Nat.pos_iff_ne_zero.mp h0) hi
  psd := fun k => delsarte_nonneg C k

end ECCLib.Delsarte

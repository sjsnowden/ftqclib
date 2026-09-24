/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonSpectrum
import ECCLib.Scheme.InclusionMatrix
import Mathlib.Analysis.Complex.Order

/-!
# The multiplicities of the Johnson scheme

**`m_0 = 1` and `m_j = C(n,j) − C(n,j−1)`**, in the canonical `MaximalSpectrum` index, for
every `k ≤ n` — and, falling out of the trace system once the multiplicities are known, the
**orthogonality of the Eberlein family against the multiplicity vector**
(`eberlein_orthogonality`).

## The route: inclusion Grams, not binomial arithmetic

One could take the orthogonality identity as an input and derive the multiplicities from it
by finite-difference arithmetic (`fwdDiff_iter_eq_sum_shift`). Instead, with common
eigenvectors, `rank = trace`, and the star/subset sums available, the route through the
Gram matrices of the inclusion matrix is *elementary* — and it delivers the identity as a
**corollary** instead of consuming it. The mechanism:

* both Grams of the inclusion matrix `N = inclMatrix` lie in Johnson orbital algebras
  (`Scheme/InclusionMatrix.lean`), so each is a linear combination of the primitive
  idempotents with coefficients its split-character values;
* those values are **computed by evaluating the eigen-equation at a transversal**: the star
  and subset sums of `Delsarte/PairShellSum.lean` reduce them to two binomial counts —
  `χ_s(NᵀN) = C(k−s, t−s)·C(n−t−s, k−t)`, zero exactly when `s > t` — with no Eberlein
  number appearing anywhere;
* `rank(NᵀN) = rank N = rank(NNᵀ)` (Gram ranks over `ℂ`), the left side is the partial
  multiplicity sum `∑_{s ≤ t} m_s` by `rank_coe_eq_sum_spectralMult`, and the right side is
  the **full** multiplicity sum of the `t`-subset Johnson scheme, which is `C(n,t)`;
* consecutive differences give the closed form, and feeding it back through the trace system
  yields the orthogonality identity.

## Main results

* `sum_spectralMult_filter_le` — `∑_{s ≤ t} m_s = C(n,t)` for every `t ≤ min k (n−k)`.
* `spectralMult_johnson_zero`, `spectralMult_johnson_add_choose` — the closed form,
  subtraction-free: `m_0 = 1` and `m_j + C(n, j−1) = C(n, j)`.
* `eberlein_orthogonality` — **the orthogonality identity**, in the guarded `ℤ` form that
  `ℕ`-truncation forces (the unguarded `ℕ` form is false at `j = 0`).
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix ECCLib.Delsarte

variable {n k : ℕ}

/-- The `k`-side Gram of the inclusion matrix, as an element of the Johnson orbital algebra
on `k`-subsets. -/
noncomputable def inclGramK (n t k : ℕ) :
    ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) :=
  ⟨(inclMatrix ℂ n t k)ᵀ * inclMatrix ℂ n t k, transpose_mul_inclMatrix_mem⟩

/-- The `t`-side Gram, as an element of the Johnson orbital algebra on `t`-subsets. -/
noncomputable def inclGramT (n t k : ℕ) :
    ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t)) :=
  ⟨inclMatrix ℂ n t k * (inclMatrix ℂ n t k)ᵀ, inclMatrix_mul_transpose_mem⟩

/-- **The split characters under the spectrum equivalence are the Johnson functionals**:
`splitChar` at `johnsonSpectrumEquiv jj` is the linear form in the Eberlein data, on the whole
algebra. -/
theorem splitChar_johnsonSpectrumEquiv [Nonempty (KSub n k)]
    (jj : Fin (min k (n - k) + 1))
    (M : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) :
    ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
        (johnsonSpectrumEquiv jj) M
      = ∑ Ω, (orbitalBasis (R := ℂ)).repr M Ω * johnsonMu (k := k) (jj : ℕ) Ω := by
  rw [← idemBasis_repr_eq_splitChar]
  conv_lhs => rw [← (orbitalBasis (R := ℂ)).sum_repr M]
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun Ω _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  congr 1
  rw [show orbitalBasis (R := ℂ) Ω
      = ⟨orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)),
          orbitalAdj_mem_orbitalAlgebra Ω.2⟩ from congrFun coe_orbitalBasis Ω]
  rw [← eigenmatrixP_apply, eigenmatrixP_johnson]
  rfl

/-- **The `k`-side Gram eigenvalues, computed at a transversal**: the split-character value of
`NᵀN` at spectral index `s` is `C(k−s, t−s) · C(n−t−s, k−t)` for `s ≤ t` and `0` above `t`.
No Eberlein number appears: the star sums collapse the evaluation to two counts. -/
theorem splitChar_inclGramK [Nonempty (KSub n k)] {t : ℕ} (htk : t ≤ k) (htn : k + t ≤ n)
    (s : Fin (min k (n - k) + 1)) :
    ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
        (johnsonSpectrumEquiv s) (inclGramK n t k)
      = if (s : ℕ) ≤ t
          then (((k - (s : ℕ)).choose (t - (s : ℕ))
            * (n - t - (s : ℕ)).choose (k - t) : ℕ) : ℂ)
          else 0 := by
  classical
  have hk : k ≤ n := KSub.k_le_of_nonempty
  have hs : (s : ℕ) ≤ min k (n - k) := Nat.lt_succ_iff.mp s.isLt
  have h2 : 2 * (s : ℕ) ≤ n := by omega
  have hjk : (s : ℕ) ≤ k := by omega
  have hkj : k + (s : ℕ) ≤ n := by omega
  -- the transversal carrier point
  obtain ⟨Kst, hKcard, hKa, hKb⟩ := ECCLib.exists_transversal
    (injective_sumElim_pair (n := n) h2) hjk (by rw [Fintype.card_fin]; omega)
  set x : KSub n k := ⟨Kst, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hKcard⟩⟩
    with hx
  have hvx : johnsonVec (k := k) (s : ℕ) h2 x = 1 := by
    rw [johnsonVec]
    rw [show pairDiff ℤ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) x.1 = 1 from
      pairDiff_eq_one hKa hKb]
    norm_num
  -- the eigen-equation at the Gram, evaluated at the transversal
  have hce := isCommonEigenvector_johnsonVec (n := n) (k := k) h2 hjk hkj
  have heig := congrFun (hce.mulVec_eq (inclGramK n t k)) x
  rw [Pi.smul_apply, hvx, smul_eq_mul, mul_one] at heig
  rw [splitChar_johnsonSpectrumEquiv, ← heig]
  -- compute the matrix-vector entry
  rw [show (((inclGramK n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)))
        : Matrix (KSub n k) (KSub n k) ℂ) *ᵥ johnsonVec (k := k) (s : ℕ) h2) x
      = ∑ y : KSub n k,
          (∑ A : KSub n t, (if A.1 ⊆ x.1 then (1 : ℂ) else 0) * if A.1 ⊆ y.1 then 1 else 0)
            * johnsonVec (k := k) (s : ℕ) h2 y from by
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun y _ => by
      rw [show ((inclGramK n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)))
          : Matrix (KSub n k) (KSub n k) ℂ) x y
          = ((inclMatrix ℂ n t k)ᵀ * inclMatrix ℂ n t k) x y from rfl,
        transpose_mul_inclMatrix_apply]]
  rw [show ∑ y : KSub n k,
        (∑ A : KSub n t, (if A.1 ⊆ x.1 then (1 : ℂ) else 0) * if A.1 ⊆ y.1 then 1 else 0)
          * johnsonVec (k := k) (s : ℕ) h2 y
      = ∑ A : KSub n t, (if A.1 ⊆ x.1 then (1 : ℂ) else 0)
          * ∑ y : KSub n k,
              (if A.1 ⊆ y.1 then (1 : ℂ) else 0) * johnsonVec (k := k) (s : ℕ) h2 y from by
    rw [show ∑ y : KSub n k,
          (∑ A : KSub n t, (if A.1 ⊆ x.1 then (1 : ℂ) else 0) * if A.1 ⊆ y.1 then 1 else 0)
            * johnsonVec (k := k) (s : ℕ) h2 y
        = ∑ y : KSub n k, ∑ A : KSub n t,
            ((if A.1 ⊆ x.1 then (1 : ℂ) else 0) * if A.1 ⊆ y.1 then 1 else 0)
              * johnsonVec (k := k) (s : ℕ) h2 y from
      Finset.sum_congr rfl fun y _ => Finset.sum_mul _ _ _]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring]
  -- the pair-difference over `ℂ`, and the inner star sum
  have hinner : ∀ A : KSub n t,
      (∑ y : KSub n k, (if A.1 ⊆ y.1 then (1 : ℂ) else 0)
          * johnsonVec (k := k) (s : ℕ) h2 y)
        = ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A.1 ⊆ K),
            pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K := by
    intro A
    have hjv : ∀ y : KSub n k, johnsonVec (k := k) (s : ℕ) h2 y
        = pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) y.1 := by
      intro y
      rw [johnsonVec, pairDiff, pairDiff, Int.cast_prod]
      exact Finset.prod_congr rfl fun i _ => by
        rw [Int.cast_sub]
        congr 1 <;> split_ifs <;> simp
    rw [Finset.sum_congr rfl fun y _ => by rw [hjv y]]
    rw [show ∑ y : KSub n k, (if A.1 ⊆ y.1 then (1 : ℂ) else 0)
          * pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) y.1
        = ∑ y : KSub n k, (if A.1 ⊆ y.1
            then pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) y.1 else 0) from
      Finset.sum_congr rfl fun y _ => by split_ifs <;> simp]
    rw [Finset.sum_coe_sort (Finset.univ.powersetCard k)
      (fun K => if A.1 ⊆ K
        then pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K else 0)]
    rw [Finset.sum_filter]
  rw [Finset.sum_congr rfl fun A _ => by rw [hinner A]]
  -- collapse the outer indicator to a sum over the `t`-subsets of the transversal
  rw [show ∑ A : KSub n t, (if A.1 ⊆ x.1 then (1 : ℂ) else 0)
        * ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A.1 ⊆ K),
            pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K
      = ∑ A ∈ (x.1).powersetCard t,
          ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K),
            pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K from by
    rw [show ∑ A : KSub n t, (if A.1 ⊆ x.1 then (1 : ℂ) else 0)
          * ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A.1 ⊆ K),
              pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K
        = ∑ A : KSub n t, (if A.1 ⊆ x.1
            then ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A.1 ⊆ K),
              pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K else 0) from
      Finset.sum_congr rfl fun A _ => by split_ifs <;> simp]
    rw [Finset.sum_coe_sort (Finset.univ.powersetCard t)
      (fun Aset => if Aset ⊆ x.1
        then ∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => Aset ⊆ K),
          pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext Aset
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨Finset.subset_univ _, h.2⟩, h.1⟩⟩]
  -- classify the bases: star-zero off the `a`-points, star evaluation on them
  set aSet : Finset (Fin n) := Finset.image (pairA n (s : ℕ) h2) Finset.univ with haSet
  have hbA : ∀ (A : Finset (Fin n)), A ⊆ x.1 → ∀ i, pairB n (s : ℕ) h2 i ∉ A :=
    fun A hAx i hi => hKb i (hAx hi)
  have haInj : Function.Injective (pairA n (s : ℕ) h2) := fun i j h =>
    Sum.inl_injective (@injective_sumElim_pair n (s : ℕ) h2 (Sum.inl i) (Sum.inl j) h)
  have hcardA : #aSet = (s : ℕ) := by
    rw [haSet, Finset.card_image_of_injective _ haInj, Finset.card_univ, Fintype.card_fin]
  have hSA : ∀ A ∈ (x.1).powersetCard t,
      (∑ K ∈ (Finset.univ.powersetCard k).filter (fun K => A ⊆ K),
          pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) K)
        = if aSet ⊆ A then ((n - (s : ℕ) - t).choose (k - t) : ℂ) else 0 := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    by_cases hall : aSet ⊆ A
    · rw [if_pos hall]
      have ha : ∀ i, pairA n (s : ℕ) h2 i ∈ A := fun i =>
        hall (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      rw [sum_star_pairDiff_transversal (injective_sumElim_pair h2) ha
        (hbA A hA.1) (by rw [hA.2]; exact htk)]
      rw [Fintype.card_fin, hA.2]
    · rw [if_neg hall]
      obtain ⟨y, hyA, hyNA⟩ := Finset.not_subset.mp hall
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hyA
      exact sum_star_pairDiff_eq_zero (injective_sumElim_pair h2) hyNA
        (hbA A hA.1 i)
  rw [Finset.sum_congr rfl hSA]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hst : (s : ℕ) ≤ t
  · rw [if_pos hst]
    have hsub : aSet ⊆ x.1 := fun y hy => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hKa i
    rw [show ((x.1).powersetCard t).filter (fun A => aSet ⊆ A)
        = ((x.1).powersetCard t).filter (fun A => aSet ⊆ A) from rfl,
      ECCLib.card_powersetCard_filter_superset hsub (by rw [hcardA]; exact hst)]
    rw [show #(x.1) = k from hKcard, hcardA]
    push_cast
    rw [show n - (s : ℕ) - t = n - t - (s : ℕ) by omega]
  · rw [if_neg hst]
    rw [show ((x.1).powersetCard t).filter (fun A => aSet ⊆ A) = ∅ from
      Finset.filter_false_of_mem fun A hA hsubA => by
        have hle : #aSet ≤ #A := Finset.card_le_card hsubA
        rw [hcardA, (Finset.mem_powersetCard.mp hA).2] at hle
        omega]
    simp

/-- **The `t`-side Gram eigenvalues**: on the `t`-subset Johnson scheme every eigenvalue of
`NNᵀ` is `C(k−s, t−s) · C(n−t−s, k−t)` — nonzero on the whole spectrum, which is what makes
the Gram invertible-in-effect and its rank the full carrier. -/
theorem splitChar_inclGramT {t : ℕ} [Nonempty (KSub n t)] (htk : t ≤ k) (htn : k + t ≤ n)
    (s : Fin (min t (n - t) + 1)) :
    ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t))
        (johnsonSpectrumEquiv s) (inclGramT n t k)
      = (((k - (s : ℕ)).choose (t - (s : ℕ))
          * (n - t - (s : ℕ)).choose (k - t) : ℕ) : ℂ) := by
  classical
  have hs : (s : ℕ) ≤ min t (n - t) := Nat.lt_succ_iff.mp s.isLt
  have h2 : 2 * (s : ℕ) ≤ n := by omega
  have hjt : (s : ℕ) ≤ t := by omega
  have htj : t + (s : ℕ) ≤ n := by omega
  obtain ⟨Ast, hAcard, hAa, hAb⟩ := ECCLib.exists_transversal
    (injective_sumElim_pair (n := n) h2) hjt (by rw [Fintype.card_fin]; omega)
  set x : KSub n t := ⟨Ast, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAcard⟩⟩
    with hx
  have hvx : johnsonVec (k := t) (s : ℕ) h2 x = 1 := by
    rw [johnsonVec]
    rw [show pairDiff ℤ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) x.1 = 1 from
      pairDiff_eq_one hAa hAb]
    norm_num
  have hce := isCommonEigenvector_johnsonVec (n := n) (k := t) h2 hjt htj
  have heig := congrFun (hce.mulVec_eq (inclGramT n t k)) x
  rw [Pi.smul_apply, hvx, smul_eq_mul, mul_one] at heig
  rw [splitChar_johnsonSpectrumEquiv, ← heig]
  -- expand the matrix-vector entry and swap the sums
  rw [show (((inclGramT n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t)))
        : Matrix (KSub n t) (KSub n t) ℂ) *ᵥ johnsonVec (k := t) (s : ℕ) h2) x
      = ∑ B : KSub n t,
          (∑ K : KSub n k, (if x.1 ⊆ K.1 then (1 : ℂ) else 0) * if B.1 ⊆ K.1 then 1 else 0)
            * johnsonVec (k := t) (s : ℕ) h2 B from by
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun B _ => by
      rw [show ((inclGramT n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t)))
          : Matrix (KSub n t) (KSub n t) ℂ) x B
          = (inclMatrix ℂ n t k * (inclMatrix ℂ n t k)ᵀ) x B from rfl,
        inclMatrix_mul_transpose_apply]]
  rw [show ∑ B : KSub n t,
        (∑ K : KSub n k, (if x.1 ⊆ K.1 then (1 : ℂ) else 0) * if B.1 ⊆ K.1 then 1 else 0)
          * johnsonVec (k := t) (s : ℕ) h2 B
      = ∑ K : KSub n k, (if x.1 ⊆ K.1 then (1 : ℂ) else 0)
          * ∑ B : KSub n t,
              (if B.1 ⊆ K.1 then (1 : ℂ) else 0) * johnsonVec (k := t) (s : ℕ) h2 B from by
    rw [show ∑ B : KSub n t,
          (∑ K : KSub n k, (if x.1 ⊆ K.1 then (1 : ℂ) else 0) * if B.1 ⊆ K.1 then 1 else 0)
            * johnsonVec (k := t) (s : ℕ) h2 B
        = ∑ B : KSub n t, ∑ K : KSub n k,
            ((if x.1 ⊆ K.1 then (1 : ℂ) else 0) * if B.1 ⊆ K.1 then 1 else 0)
              * johnsonVec (k := t) (s : ℕ) h2 B from
      Finset.sum_congr rfl fun B _ => Finset.sum_mul _ _ _]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun B _ => by ring]
  -- the inner subset sum, per `K`
  have hjv : ∀ B : KSub n t, johnsonVec (k := t) (s : ℕ) h2 B
      = pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B.1 := by
    intro B
    rw [johnsonVec, pairDiff, pairDiff, Int.cast_prod]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Int.cast_sub]
      congr 1 <;> split_ifs <;> simp
  have hinner : ∀ K : KSub n k,
      (∑ B : KSub n t, (if B.1 ⊆ K.1 then (1 : ℂ) else 0)
          * johnsonVec (k := t) (s : ℕ) h2 B)
        = ∑ B ∈ (K.1).powersetCard t,
            pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B := by
    intro K
    rw [Finset.sum_congr rfl fun B _ => by rw [hjv B]]
    rw [show ∑ B : KSub n t, (if B.1 ⊆ K.1 then (1 : ℂ) else 0)
          * pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B.1
        = ∑ B : KSub n t, (if B.1 ⊆ K.1
            then pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B.1 else 0) from
      Finset.sum_congr rfl fun B _ => by split_ifs <;> simp]
    rw [Finset.sum_coe_sort (Finset.univ.powersetCard t)
      (fun B => if B ⊆ K.1
        then pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext B
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨Finset.subset_univ _, h.2⟩, h.1⟩⟩
  rw [Finset.sum_congr rfl fun K _ => by rw [hinner K]]
  -- evaluate the subset sum on each star member
  have hTK : ∀ K : KSub n k, x.1 ⊆ K.1 →
      (∑ B ∈ (K.1).powersetCard t,
          pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B)
        = if ∀ i, pairB n (s : ℕ) h2 i ∉ K.1
            then ((k - (s : ℕ)).choose (t - (s : ℕ)) : ℂ) else 0 := by
    intro K hxK
    have haK : ∀ i, pairA n (s : ℕ) h2 i ∈ K.1 := fun i => hxK (hAa i)
    by_cases hbK : ∀ i, pairB n (s : ℕ) h2 i ∉ K.1
    · rw [if_pos hbK]
      rw [sum_powersetCard_pairDiff_transversal (injective_sumElim_pair h2) haK hbK hjt]
      rw [KSub.card_val]
    · rw [if_neg hbK]
      simp only [not_forall, not_not] at hbK
      obtain ⟨i, hbi⟩ := hbK
      exact sum_powersetCard_pairDiff_eq_zero (injective_sumElim_pair h2)
        (iff_of_true (haK i) hbi)
  rw [show ∑ K : KSub n k, (if x.1 ⊆ K.1 then (1 : ℂ) else 0)
        * ∑ B ∈ (K.1).powersetCard t,
            pairDiff ℂ (pairA n (s : ℕ) h2) (pairB n (s : ℕ) h2) B
      = ∑ K : KSub n k, (if x.1 ⊆ K.1 ∧ ∀ i, pairB n (s : ℕ) h2 i ∉ K.1
          then ((k - (s : ℕ)).choose (t - (s : ℕ)) : ℂ) else 0) from
    Finset.sum_congr rfl fun K _ => by
      by_cases hxK : x.1 ⊆ K.1
      · rw [hTK K hxK]
        by_cases hbK : ∀ i, pairB n (s : ℕ) h2 i ∉ K.1
        · rw [if_pos hxK, one_mul, if_pos hbK, if_pos ⟨hxK, hbK⟩]
        · rw [if_pos hxK, one_mul, if_neg hbK, if_neg (fun h => hbK h.2)]
      · rw [if_neg hxK, zero_mul, if_neg (fun h => hxK h.1)]]
  rw [show ∑ K : KSub n k, (if x.1 ⊆ K.1 ∧ ∀ i, pairB n (s : ℕ) h2 i ∉ K.1
        then ((k - (s : ℕ)).choose (t - (s : ℕ)) : ℂ) else 0)
      = ∑ K ∈ (Finset.univ.powersetCard k).filter
          (fun K => x.1 ⊆ K ∧ ∀ i, pairB n (s : ℕ) h2 i ∉ K),
          ((k - (s : ℕ)).choose (t - (s : ℕ)) : ℂ) from by
    rw [Finset.sum_coe_sort (Finset.univ.powersetCard k)
      (fun K => if x.1 ⊆ K ∧ ∀ i, pairB n (s : ℕ) h2 i ∉ K
        then ((k - (s : ℕ)).choose (t - (s : ℕ)) : ℂ) else 0)]
    rw [← Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul,
    card_star_avoid (injective_sumElim_pair h2) hAb (by rw [hAcard]; omega)]
  rw [Fintype.card_fin, hAcard]
  push_cast
  rw [show n - (s : ℕ) - t = n - t - (s : ℕ) by omega]
  ring

/-! ## The rank chain and the partial multiplicity sums -/

open scoped ComplexOrder in
/-- **Gottlieb's theorem** (the rank of the inclusion matrix): for `t ≤ min k (n−k)` the
inclusion matrix of the `t`-subsets against the `k`-subsets has full row rank `C(n,t)`.
The fact sits inside the rank chain of `sum_spectralMult_filter_le`; the proof here is
spectral: `rank N = rank NNᵀ`, and on
the `t`-subset Johnson scheme every eigenvalue of `NNᵀ` is a positive binomial product, so
the Gram has full rank `C(n,t)` by the multiplicity total. -/
theorem rank_inclMatrix {t : ℕ} (hk : k ≤ n) (ht : t ≤ min k (n - k)) :
    Matrix.rank (inclMatrix ℂ n t k) = n.choose t := by
  classical
  have htk : t ≤ k := by omega
  have htn : k + t ≤ n := by omega
  haveI : Nonempty (KSub n t) := KSub.nonempty (by omega)
  have h3 : Matrix.rank
        ((inclGramT n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t)))
          : Matrix (KSub n t) (KSub n t) ℂ)
      = Matrix.rank (inclMatrix ℂ n t k) := by
    rw [show ((inclGramT n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t)))
        : Matrix (KSub n t) (KSub n t) ℂ)
        = inclMatrix ℂ n t k * (inclMatrix ℂ n t k)ᵀ from rfl, ← conjTranspose_inclMatrix]
    exact Matrix.rank_self_mul_conjTranspose _
  have h4 : Matrix.rank
        ((inclGramT n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n t)))
          : Matrix (KSub n t) (KSub n t) ℂ)
      = n.choose t := by
    rw [rank_coe_eq_sum_spectralMult]
    rw [Finset.filter_true_of_mem (fun I _ => ?_)]
    · rw [sum_spectralMult_eq_card, card_kSub]
    · rw [show I = johnsonSpectrumEquiv ((johnsonSpectrumEquiv (n := n) (k := t)).symm I)
        from (Equiv.apply_symm_apply _ _).symm, splitChar_inclGramT htk htn]
      set s' : ℕ := (((johnsonSpectrumEquiv (n := n) (k := t)).symm I : Fin _) : ℕ) with hs'
      have hle : s' ≤ min t (n - t) :=
        Nat.lt_succ_iff.mp ((johnsonSpectrumEquiv (n := n) (k := t)).symm I).isLt
      have hc1 : 0 < (k - s').choose (t - s') := Nat.choose_pos (by omega)
      have hc2 : 0 < (n - t - s').choose (k - t) := Nat.choose_pos (by omega)
      exact_mod_cast Nat.mul_ne_zero hc1.ne' hc2.ne'
  omega

open scoped ComplexOrder in
/-- **The partial multiplicity sums are the binomials**: for every `t ≤ min k (n−k)`,
`∑_{s ≤ t} m_s = C(n,t)`. Left side: the rank of `NᵀN` through
`rank_coe_eq_sum_spectralMult` and the `k`-side eigenvalues. Right side: Gottlieb's rank
(`rank_inclMatrix`). -/
theorem sum_spectralMult_filter_le [Nonempty (KSub n k)] {t : ℕ} (ht : t ≤ min k (n - k)) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin (min k (n - k) + 1) => (s : ℕ) ≤ t),
        spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
          (johnsonSpectrumEquiv s)
      = n.choose t := by
  classical
  have hk : k ≤ n := KSub.k_le_of_nonempty
  have htk : t ≤ k := by omega
  have htn : k + t ≤ n := by omega
  haveI : Nonempty (KSub n t) := KSub.nonempty (by omega)
  have hvalK : ∀ s : Fin (min k (n - k) + 1), (s : ℕ) ≤ t →
      ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
        (johnsonSpectrumEquiv s) (inclGramK n t k) ≠ 0 := by
    intro s hst
    rw [splitChar_inclGramK htk htn, if_pos hst]
    have h1 : 0 < (k - (s : ℕ)).choose (t - (s : ℕ)) := Nat.choose_pos (by omega)
    have h2 : 0 < (n - t - (s : ℕ)).choose (k - t) := Nat.choose_pos (by omega)
    exact_mod_cast Nat.mul_ne_zero h1.ne' h2.ne'
  have h1 : Matrix.rank
        ((inclGramK n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)))
          : Matrix (KSub n k) (KSub n k) ℂ)
      = ∑ s ∈ Finset.univ.filter (fun s : Fin (min k (n - k) + 1) => (s : ℕ) ≤ t),
          spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
            (johnsonSpectrumEquiv s) := by
    rw [rank_coe_eq_sum_spectralMult]
    refine (Finset.sum_equiv (johnsonSpectrumEquiv (n := n) (k := k)) (fun s => ?_)
      (fun s _ => rfl)).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hst
      exact hvalK s hst
    · intro hne
      by_contra hst
      rw [splitChar_inclGramK htk htn, if_neg hst] at hne
      exact hne rfl
  have h2 : Matrix.rank
        ((inclGramK n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)))
          : Matrix (KSub n k) (KSub n k) ℂ)
      = Matrix.rank (inclMatrix ℂ n t k) := by
    rw [show ((inclGramK n t k : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)))
        : Matrix (KSub n k) (KSub n k) ℂ)
        = (inclMatrix ℂ n t k)ᵀ * inclMatrix ℂ n t k from rfl, ← conjTranspose_inclMatrix]
    exact Matrix.rank_conjTranspose_mul_self _
  have h34 : Matrix.rank (inclMatrix ℂ n t k) = n.choose t := rank_inclMatrix hk ht
  omega

/-! ## The closed form, subtraction-free -/

/-- **The trivial eigenspace is a line**: `m_0 = 1`. -/
theorem spectralMult_johnson_zero [Nonempty (KSub n k)] :
    spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
      (johnsonSpectrumEquiv (0 : Fin (min k (n - k) + 1))) = 1 := by
  have h := sum_spectralMult_filter_le (n := n) (k := k) (t := 0) (Nat.zero_le _)
  rw [Nat.choose_zero_right] at h
  rw [show Finset.univ.filter (fun s : Fin (min k (n - k) + 1) => (s : ℕ) ≤ 0)
      = {0} from by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Nat.le_zero, Fin.ext_iff, Fin.val_zero]] at h
  simpa using h

/-- **The multiplicity closed form, subtraction-free**: `m_j + C(n, j−1) = C(n, j)` for
`1 ≤ j` — the subtraction-free form, since the `ℕ`-truncated subtraction is false at `j = 0`. -/
theorem spectralMult_johnson_add_choose [Nonempty (KSub n k)]
    {j : Fin (min k (n - k) + 1)} (hj : 0 < (j : ℕ)) :
    spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) (johnsonSpectrumEquiv j)
        + n.choose ((j : ℕ) - 1)
      = n.choose (j : ℕ) := by
  have hjle : (j : ℕ) ≤ min k (n - k) := Nat.lt_succ_iff.mp j.isLt
  have h1 := sum_spectralMult_filter_le (n := n) (k := k) (t := (j : ℕ)) hjle
  have h2 := sum_spectralMult_filter_le (n := n) (k := k) (t := (j : ℕ) - 1) (by omega)
  have hsplit : Finset.univ.filter (fun s : Fin (min k (n - k) + 1) => (s : ℕ) ≤ (j : ℕ))
      = insert j
          (Finset.univ.filter (fun s : Fin (min k (n - k) + 1) => (s : ℕ) ≤ (j : ℕ) - 1)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hs
      rcases eq_or_ne s j with rfl | hne
      · exact Or.inl rfl
      · have : (s : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
        exact Or.inr (by omega)
    · rintro (rfl | hs)
      · exact le_rfl
      · omega
  rw [hsplit, Finset.sum_insert (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    omega)] at h1
  omega

/-- The `ℤ` reading of the closed form. -/
theorem spectralMult_johnson_eq_sub [Nonempty (KSub n k)]
    {j : Fin (min k (n - k) + 1)} (hj : 0 < (j : ℕ)) :
    (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
        (johnsonSpectrumEquiv j) : ℤ)
      = (n.choose (j : ℕ) : ℤ) - n.choose ((j : ℕ) - 1) := by
  have := spectralMult_johnson_add_choose (n := n) (k := k) hj
  omega

/-! ## The trace of a Johnson adjacency, and the orthogonality identity -/

/-- The trace of a Johnson orbital adjacency: `C(n,k)` on the diagonal orbital
(width `k`), zero elsewhere. -/
theorem trace_orbitalAdj_johnson
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) :
    (orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k))).trace
      = if orbWidth Ω = k then (n.choose k : ℂ) else 0 := by
  classical
  rw [trace_orbitalAdj]
  by_cases hw : orbWidth Ω = k
  · rw [if_pos hw]
    rw [show (Ω : Finset (KSub n k × KSub n k)).filter (fun p => p.1 = p.2)
        = Finset.univ.image (fun K : KSub n k => (K, K)) from by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hpd⟩
        exact ⟨p.1, Prod.ext rfl hpd⟩
      · rintro ⟨K, rfl⟩
        refine ⟨(mem_orbital_iff_interCard_eq _).mpr ?_, rfl⟩
        rw [hw, interCard, Finset.inter_self, KSub.card_val]]
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).1),
      Finset.card_univ, card_kSub]
  · rw [if_neg hw]
    rw [show (Ω : Finset (KSub n k × KSub n k)).filter (fun p => p.1 = p.2) = ∅ from
      Finset.filter_false_of_mem fun p hp hpd => hw (by
        rw [← interCard_eq_orbWidth hp, interCard, ← hpd, Finset.inter_self, KSub.card_val])]
    simp

/-- **The orthogonality of the Eberlein family against the multiplicity vector**, in the
guarded `ℤ` form that `ℕ`-truncation forces — a **corollary** of the closed form through the
trace system rather than an input to it. -/
theorem eberlein_orthogonality {n k d : ℕ} (hk : k ≤ n) (hd : d ≤ min k (n - k)) :
    ∑ j ∈ Finset.range (min k (n - k) + 1),
        (if j = 0 then 1 else (n.choose j : ℤ) - n.choose (j - 1)) * eberlein n k d j
      = if d = 0 then (n.choose k : ℤ) else 0 := by
  classical
  haveI : Nonempty (KSub n k) := KSub.nonempty hk
  obtain ⟨Ω, hΩ⟩ := exists_orbWidth_eq (n := n) (k := k) (w := k - d)
    (by omega) (by omega)
  have hΩd : k - orbWidth Ω = d := by omega
  have htrace := sum_spectralMult_mul_eigenmatrixP
    (G := Equiv.Perm (Fin n)) (X := KSub n k) Ω
  rw [show ∑ I, (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) I : ℂ)
        * eigenmatrixP I Ω
      = ∑ s : Fin (min k (n - k) + 1),
          (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
              (johnsonSpectrumEquiv s) : ℂ)
            * eigenmatrixP (johnsonSpectrumEquiv s) Ω from
    (Fintype.sum_equiv (johnsonSpectrumEquiv (n := n) (k := k)) _ _ fun s => rfl).symm]
    at htrace
  rw [trace_orbitalAdj_johnson] at htrace
  have hmult : ∀ s : Fin (min k (n - k) + 1),
      (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
          (johnsonSpectrumEquiv s) : ℂ)
        = (((if (s : ℕ) = 0 then 1
            else (n.choose (s : ℕ) : ℤ) - n.choose ((s : ℕ) - 1)) : ℤ) : ℂ) := by
    intro s
    by_cases hs : (s : ℕ) = 0
    · rw [if_pos hs]
      rw [show s = (0 : Fin (min k (n - k) + 1)) from Fin.ext (by rw [hs, Fin.val_zero]),
        spectralMult_johnson_zero]
      norm_num
    · rw [if_neg hs, ← spectralMult_johnson_eq_sub (Nat.pos_of_ne_zero hs)]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun s _ => by
    rw [hmult s, eigenmatrixP_johnson, hΩd]] at htrace
  have hcond : (orbWidth Ω = k) = (d = 0) := by
    apply propext
    constructor
    · intro h
      omega
    · intro h
      omega
  simp only [hcond] at htrace
  have hZ : ((∑ j ∈ Finset.range (min k (n - k) + 1),
        (if j = 0 then 1 else (n.choose j : ℤ) - n.choose (j - 1)) * eberlein n k d j : ℤ) : ℂ)
      = ((if d = 0 then (n.choose k : ℤ) else 0 : ℤ) : ℂ) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => (if j = 0 then 1 else (n.choose j : ℤ) - n.choose (j - 1))
        * eberlein n k d j) (min k (n - k) + 1)]
    push_cast
    rw [← htrace]
    by_cases hd0 : d = 0 <;> simp [hd0]
  exact_mod_cast hZ

end ECCLib.Scheme.Johnson

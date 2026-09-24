/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Johnson

/-!
# The inclusion matrix of subsets

The 0/1 matrix pairing the `t`-subsets against the `k`-subsets by inclusion. Its two Gram
products live in the two Johnson orbital algebras — the entries of `NᵀN` and `NNᵀ` depend
only on the intersection pattern, so both commute with the permutation action — and that
membership is all this module claims. The **eigenvalues** of the Grams, computed on the
pair-difference eigenvectors by the star and subset sums of `Delsarte/PairShellSum.lean`,
belong to `Scheme/JohnsonMultiplicity.lean`, where they deliver the multiplicities of the
Johnson scheme.

## Main definitions

* `inclMatrix R n t k` — the inclusion matrix.

## Main results

* `transpose_mul_inclMatrix_mem` — `NᵀN` lies in the Johnson orbital algebra on `k`-subsets.
* `inclMatrix_mul_transpose_mem` — `NNᵀ` lies in the Johnson orbital algebra on `t`-subsets.

## Implementation notes

Membership is proved from `mem_orbitalAlgebra_iff` (invariance under the diagonal action)
by reindexing the inner sum along `g • ·` — no orbital decomposition of the Gram and no
binomial entry formula is needed anywhere, so none is stated. The module supplies the
multiplicity computation of `Scheme/JohnsonMultiplicity.lean`, and is kept separate so the
matrix and its algebra membership are reusable independently of the Johnson spectrum.
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix

variable (R : Type*) [CommRing R] {n t k : ℕ}

variable (n t k) in
/-- The **inclusion matrix**: rows the `t`-subsets, columns the `k`-subsets, entry `1` exactly
on inclusion. -/
def inclMatrix : Matrix (KSub n t) (KSub n k) R :=
  fun A K => if A.1 ⊆ K.1 then 1 else 0

theorem inclMatrix_apply (A : KSub n t) (K : KSub n k) :
    inclMatrix R n t k A K = if A.1 ⊆ K.1 then (1 : R) else 0 := rfl

variable {R}

theorem transpose_mul_inclMatrix_apply (K K' : KSub n k) :
    ((inclMatrix R n t k)ᵀ * inclMatrix R n t k) K K'
      = ∑ A : KSub n t,
          (if A.1 ⊆ K.1 then (1 : R) else 0) * if A.1 ⊆ K'.1 then 1 else 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun A _ => by rw [Matrix.transpose_apply]; rfl

theorem inclMatrix_mul_transpose_apply (A B : KSub n t) :
    (inclMatrix R n t k * (inclMatrix R n t k)ᵀ) A B
      = ∑ K : KSub n k,
          (if A.1 ⊆ K.1 then (1 : R) else 0) * if B.1 ⊆ K.1 then 1 else 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun K _ => by rw [Matrix.transpose_apply]; rfl

/-- Inclusion transports along the action: `g • A ⊆ g • K` iff `A ⊆ K`. -/
theorem smul_subset_smul_iff (g : Equiv.Perm (Fin n)) (A : KSub n t) (K : KSub n k) :
    (g • A).1 ⊆ (g • K).1 ↔ A.1 ⊆ K.1 := by
  rw [KSub.val_smul, KSub.val_smul, Finset.map_subset_map]

/-- **`NᵀN` lies in the Johnson orbital algebra on `k`-subsets**: its entries are invariant
under the diagonal action, by reindexing the inner sum along the action. -/
theorem transpose_mul_inclMatrix_mem :
    (inclMatrix R n t k)ᵀ * inclMatrix R n t k
      ∈ orbitalAlgebra R (Equiv.Perm (Fin n)) (KSub n k) := by
  rw [mem_orbitalAlgebra_iff]
  intro g K K'
  rw [transpose_mul_inclMatrix_apply, transpose_mul_inclMatrix_apply]
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun A => ?_).symm
  rw [show MulAction.toPerm g A = g • A from rfl]
  simp only [smul_subset_smul_iff]

/-- **`NNᵀ` lies in the Johnson orbital algebra on `t`-subsets.** -/
theorem inclMatrix_mul_transpose_mem :
    inclMatrix R n t k * (inclMatrix R n t k)ᵀ
      ∈ orbitalAlgebra R (Equiv.Perm (Fin n)) (KSub n t) := by
  rw [mem_orbitalAlgebra_iff]
  intro g A B
  rw [inclMatrix_mul_transpose_apply, inclMatrix_mul_transpose_apply]
  refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun K => ?_).symm
  rw [show MulAction.toPerm g K = g • K from rfl]
  simp only [smul_subset_smul_iff]

/-- Over `ℂ` the inclusion matrix is real, so its conjugate transpose is its transpose. -/
theorem conjTranspose_inclMatrix :
    (inclMatrix ℂ n t k)ᴴ = (inclMatrix ℂ n t k)ᵀ := by
  ext K A
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, inclMatrix_apply]
  by_cases h : A.1 ⊆ K.1 <;> simp [h]

end ECCLib.Scheme.Johnson

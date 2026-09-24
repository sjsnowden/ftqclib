/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitalPositivity
import ECCLib.Scheme.JohnsonOrthogonality

/-!
# Delsarte's inequalities for constant-weight codes

The Johnson instantiation of `Scheme/OrbitalPositivity.lean`: for any family `C` of
`k`-subsets — any **constant-weight code** — the inner distribution pairs nonnegatively against
every column of the Johnson scheme's second eigenmatrix (`delsarte_nonneg_johnson`), and the
`Q`-entries are exhibited division-free against the Eberlein family and the multiplicities
(`choose_mul_eigenmatrixQ_johnson`):

  `C(k,d)·C(n−k,d) · Q(Ω_d, I_j) = m_j · E_d(j)`,   `d = k − width`.

Together these are the linear-programming inequalities behind every bound on `A(n,δ,w)`
— Delsarte's (3.8)/Theorem 3.3 read on the Johnson scheme — with the general layer
carried by `Scheme/OrbitalPositivity.lean` and every Johnson ingredient by the Johnson
spectrum and multiplicities: self-pairedness kills the transpose, the orbital sizes and the
eigenmatrix row are closed forms, and `C(n,k)` cancels between the size and the carrier.

## Main results

* `choose_mul_eigenmatrixQ_johnson` — the second eigenmatrix, division-free.
* `delsarte_nonneg_johnson` — **the constant-weight Delsarte inequality**.
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix ECCLib.Delsarte
open scoped ComplexOrder

variable {n k : ℕ}

/-- **The Johnson second eigenmatrix, division-free**: at the orbital of
Johnson distance `d = k − width` and the canonical spectral index `j`,
`C(k,d)·C(n−k,d) · Q = m_j · E_d(j)` — the `C(n,k)` of the orbital size cancels against
the carrier. -/
theorem choose_mul_eigenmatrixQ_johnson [Nonempty (KSub n k)]
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)))
    (j : Fin (min k (n - k) + 1)) :
    ((k.choose (k - orbWidth Ω) * (n - k).choose (k - orbWidth Ω) : ℕ) : ℂ)
        * eigenmatrixQ Ω (johnsonSpectrumEquiv j)
      = (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
            (johnsonSpectrumEquiv j) : ℂ)
          * ((eberlein n k (k - orbWidth Ω) (j : ℕ) : ℤ) : ℂ) := by
  have hC1 := card_mul_eigenmatrixQ_transposePairs Ω (johnsonSpectrumEquiv j)
  rw [show (⟨transposePairs (Ω : Finset (KSub n k × KSub n k)),
      transposePairs_mem_orbits Ω.2⟩ :
      ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) = Ω from
    Subtype.ext (transposePairs_eq_self_of_isSelfPaired isSelfPaired_kSub Ω.2)] at hC1
  rw [card_orbital_johnson Ω, eigenmatrixP_johnson j Ω, card_kSub,
    ← Nat.choose_symm (orbWidth_le Ω)] at hC1
  have hnk : ((n.choose k : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos KSub.k_le_of_nonempty).ne'
  push_cast at hC1 ⊢
  apply mul_left_cancel₀ hnk
  linear_combination hC1

/-- **The constant-weight Delsarte inequality**: the inner distribution of
any family of `k`-subsets pairs nonnegatively against every `Q`-column, in the canonical
index. -/
theorem delsarte_nonneg_johnson [Nonempty (KSub n k)] (C : Finset (KSub n k))
    (j : Fin (min k (n - k) + 1)) :
    0 ≤ ∑ Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)),
        (orbCount C (Ω : Finset (KSub n k × KSub n k)) : ℂ)
          * eigenmatrixQ Ω (johnsonSpectrumEquiv j) :=
  delsarte_nonneg_orbital C (johnsonSpectrumEquiv j)

end ECCLib.Scheme.Johnson

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonOrthogonality

/-!
# The Kneser graph and its spectrum

The **Kneser graph** `K(n,k)` — vertices the `k`-subsets of an `n`-set, edges the disjoint
pairs — is the width-`0` orbital of the Johnson scheme, so `eigenmatrixP_johnson` hands over
its complete spectrum through one evaluation of the Eberlein family
(`eberlein_top_degree`): eigenvalues `(−1)^j · C(n−k−j, k−j)` on eigenspaces of
dimensions `C(n,j) − C(n,j−1)`. The bridge is a dictionary
(`kneserSet_mem_orbits`, `orbWidth_kneserSet`) plus that one binomial collapse; nothing
else is new. The Petersen graph is `K(5,2)`: eigenvalues `3, −2, 1` with multiplicities
`1, 4, 5`, kernel-checked in the companion check module together with its independence
number `α = 4`, a first instance of the Erdős–Ko–Rado bound (which is not proved
here).

## Main definitions

* `kneserSet n k` — the disjointness relation, as a set of ordered pairs.

## Main results

* `eigenmatrixP_kneser` — **the Kneser spectrum**: the `P`-column of the disjointness
  orbital is `(−1)^j · C(n−k−j, k−j)`, in the canonical index.
* `card_kneserSet` — the edge count (twice): `C(n,k) · C(n−k,k)`.
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix ECCLib.Delsarte

variable {n k : ℕ}

variable (n k) in
/-- The **disjointness relation** of the `k`-subsets: the ordered pairs meeting in the
empty set — the edge set of the Kneser graph, as a set of ordered pairs. -/
def kneserSet : Finset (KSub n k × KSub n k) :=
  Finset.univ.filter (fun p => interCard p = 0)

theorem mem_kneserSet {p : KSub n k × KSub n k} :
    p ∈ kneserSet n k ↔ p.1.1 ∩ p.2.1 = ∅ := by
  rw [kneserSet, Finset.mem_filter, interCard]
  simp [Finset.card_eq_zero]

/-- Under `2k ≤ n` the disjointness relation is an orbital of the Johnson scheme. -/
theorem kneserSet_mem_orbits (h2k : 2 * k ≤ n) :
    kneserSet n k ∈ orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k) := by
  obtain ⟨Ω, hΩ⟩ := exists_orbWidth_eq (n := n) (k := k) (w := 0)
    (Nat.zero_le k) (by omega)
  rw [show kneserSet n k = (Ω : Finset (KSub n k × KSub n k)) from by
    ext p
    rw [kneserSet, Finset.mem_filter, mem_orbital_iff_interCard_eq, hΩ]
    simp]
  exact Ω.2

/-- The disjointness orbital has width zero. -/
theorem orbWidth_kneserSet (h2k : 2 * k ≤ n) :
    orbWidth (⟨kneserSet n k, kneserSet_mem_orbits h2k⟩
      : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) = 0 := by
  obtain ⟨p, hp⟩ := exists_interCard_eq (n := n) (k := k) (t := 0)
    (Nat.zero_le k) (by omega)
  have hmem : p ∈ kneserSet n k := by
    rw [kneserSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp⟩
  rw [← interCard_eq_orbWidth (Ω := ⟨kneserSet n k, kneserSet_mem_orbits h2k⟩) hmem, hp]

/-- **The Kneser spectrum**: the eigenvalue of the disjointness relation on
the `j`-th eigenspace is `(−1)^j · C(n−k−j, k−j)`, in the canonical `MaximalSpectrum`
index; the eigenspace dimensions are the Johnson multiplicities
`spectralMult_johnson_zero` / `spectralMult_johnson_add_choose`. -/
theorem eigenmatrixP_kneser [Nonempty (KSub n k)] (h2k : 2 * k ≤ n)
    (j : Fin (min k (n - k) + 1)) :
    eigenmatrixP (johnsonSpectrumEquiv j)
        (⟨kneserSet n k, kneserSet_mem_orbits h2k⟩
          : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)))
      = (((-1) ^ (j : ℕ) * ((n - k - (j : ℕ)).choose (k - (j : ℕ)) : ℤ) : ℤ) : ℂ) := by
  have hj : (j : ℕ) ≤ k := by
    have := Nat.lt_succ_iff.mp j.isLt
    omega
  rw [eigenmatrixP_johnson, orbWidth_kneserSet h2k, Nat.sub_zero,
    eberlein_top_degree hj]

/-- The disjointness orbital counts ordered disjoint pairs: `C(n,k) · C(n−k,k)` — the
Kneser graph is `C(n−k,k)`-regular. -/
theorem card_kneserSet (h2k : 2 * k ≤ n) :
    #(kneserSet n k) = n.choose k * (n - k).choose k := by
  have h := card_orbital_johnson
    (⟨kneserSet n k, kneserSet_mem_orbits h2k⟩
      : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)))
  rw [orbWidth_kneserSet h2k] at h
  simpa using h

end ECCLib.Scheme.Johnson

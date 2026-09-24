/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonMultiplicity
import ECCLib.Scheme.OrbitalOrthogonality

/-!
# The full orthogonality of the Eberlein family

The Johnson instantiation of `Scheme/OrbitalOrthogonality.lean`: **the Eberlein family is an
orthogonal family for the multiplicity weights**, in the guarded `ℤ` form —

`∑_t m_t · E_d(t) · E_{d'}(t) = δ_{dd'} · C(n,k) · C(k,d) · C(n−k,d)`,

with `m_0 = 1`, `m_t = C(n,t) − C(n,t−1)`. The scheme is self-paired, so the general
theorem's transpose-diagonal is the literal diagonal; the right side is the size of the
distance-`d` orbital, counted here by the profile interface
(`card_orbital_johnson`). The `d = d' = 0` row recovers `eberlein_orthogonality`'s `d = 0`
case with both guards live; all other rows are new.

## Main results

* `card_orbital_johnson` — the orbital sizes: `#Ω = C(n,k) · C(k,w) · C(n−k, k−w)` at
  width `w`.
* `eberlein_full_orthogonality` — **the full orthogonality identity**, guarded `ℤ` form.
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix ECCLib.Delsarte

variable {n k : ℕ}

/-- **The orbital sizes of the Johnson scheme**: the width-`w` orbital holds
`C(n,k) · C(k,w) · C(n−k, k−w)` pairs — one factor chooses the first subset, the profile
count chooses the second. -/
theorem card_orbital_johnson (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) :
    #(Ω : Finset (KSub n k × KSub n k))
      = n.choose k * (k.choose (orbWidth Ω) * (n - k).choose (k - orbWidth Ω)) := by
  classical
  rw [show (Ω : Finset (KSub n k × KSub n k))
      = Finset.univ.filter (fun p => interCard p = orbWidth Ω) from by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_orbital_iff_interCard_eq p]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : KSub n k × KSub n k => p.1) (t := Finset.univ)
    (fun p _ => Finset.mem_univ _)]
  rw [show ∑ K : KSub n k, #((Finset.univ.filter
        (fun p : KSub n k × KSub n k => interCard p = orbWidth Ω)).filter
        (fun p => p.1 = K))
      = ∑ _K : KSub n k, k.choose (orbWidth Ω) * (n - k).choose (k - orbWidth Ω) from
    Finset.sum_congr rfl fun K _ => ?_]
  · rw [Finset.sum_const, Finset.card_univ, card_kSub, smul_eq_mul]
  · have hbij : #((Finset.univ.filter
          (fun p : KSub n k × KSub n k => interCard p = orbWidth Ω)).filter
          (fun p => p.1 = K))
        = #(Finset.univ.filter (fun L : KSub n k => #(K.1 ∩ L.1) = orbWidth Ω)) := by
      apply Finset.card_nbij' (i := fun p => p.2) (j := fun L => (K, L))
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rw [← hp.2]
        exact hp.1
      · intro L hL
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
        exact ⟨hL, trivial⟩
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter] at hp
        exact Prod.ext hp.2.symm rfl
      · intro L _
        rfl
    rw [hbij]
    rw [show #(Finset.univ.filter (fun L : KSub n k => #(K.1 ∩ L.1) = orbWidth Ω))
        = #((Finset.univ.powersetCard k).filter
            (fun y => #(K.1 ∩ y) = orbWidth Ω)) from
      Finset.card_bij' (fun L _ => L.1)
        (fun y hy => ⟨y, (Finset.mem_filter.mp hy).1⟩)
        (fun L hL => by
          rw [Finset.mem_filter] at hL ⊢
          exact ⟨L.2, hL.2⟩)
        (fun y hy => by
          rw [Finset.mem_filter] at hy ⊢
          exact ⟨Finset.mem_univ _, hy.2⟩)
        (fun L _ => rfl) (fun y _ => rfl)]
    rw [card_filter_inter_card_eq K.1 (KSub.card_val K) (orbWidth_le Ω),
      Fintype.card_fin]

/-- **The full orthogonality of the Eberlein family**: against the
multiplicity weights, distinct rows are orthogonal and the diagonal is the orbital size —
the guarded `ℤ` form, every `k ≤ n`. -/
theorem eberlein_full_orthogonality {n k d d' : ℕ} (hk : k ≤ n)
    (hd : d ≤ min k (n - k)) (hd' : d' ≤ min k (n - k)) :
    ∑ t ∈ Finset.range (min k (n - k) + 1),
        (if t = 0 then 1 else (n.choose t : ℤ) - n.choose (t - 1))
          * (eberlein n k d t * eberlein n k d' t)
      = if d = d' then (n.choose k * (k.choose d * (n - k).choose d) : ℤ) else 0 := by
  classical
  haveI : Nonempty (KSub n k) := KSub.nonempty hk
  obtain ⟨Ω, hΩ⟩ := exists_orbWidth_eq (n := n) (k := k) (w := k - d)
    (by omega) (by omega)
  obtain ⟨Ω', hΩ'⟩ := exists_orbWidth_eq (n := n) (k := k) (w := k - d')
    (by omega) (by omega)
  have hΩd : k - orbWidth Ω = d := by omega
  have hΩd' : k - orbWidth Ω' = d' := by omega
  have h := sum_spectralMult_mul_eigenmatrixP_mul_eigenmatrixP
    (G := Equiv.Perm (Fin n)) (X := KSub n k) Ω Ω'
  rw [show ∑ I, (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) I : ℂ)
        * (eigenmatrixP I Ω * eigenmatrixP I Ω')
      = ∑ s : Fin (min k (n - k) + 1),
          (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
              (johnsonSpectrumEquiv s) : ℂ)
            * (eigenmatrixP (johnsonSpectrumEquiv s) Ω
                * eigenmatrixP (johnsonSpectrumEquiv s) Ω') from
    (Fintype.sum_equiv (johnsonSpectrumEquiv (n := n) (k := k)) _ _ fun s => rfl).symm]
    at h
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
    rw [hmult s, eigenmatrixP_johnson, eigenmatrixP_johnson, hΩd, hΩd']] at h
  have hsame : ∀ w w' : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)),
      orbWidth w = orbWidth w' → w = w' := by
    intro w w' hww
    obtain ⟨p, hp⟩ := nonempty_of_mem_orbits w.2
    have hp' : p ∈ (w' : Finset (KSub n k × KSub n k)) := by
      rw [mem_orbital_iff_interCard_eq, ← hww]
      exact interCard_eq_orbWidth hp
    exact Subtype.ext (eq_of_mem_orbits_of_mem w.2 w'.2 hp hp')
  have hcond : ((Ω' : Finset (KSub n k × KSub n k))
        = transposePairs (Ω : Finset (KSub n k × KSub n k))) = (d = d') := by
    apply propext
    rw [transposePairs_eq_self_of_isSelfPaired isSelfPaired_kSub Ω.2]
    constructor
    · intro hset
      have heq : Ω' = Ω := Subtype.ext hset
      have hw : orbWidth Ω' = orbWidth Ω := by rw [heq]
      omega
    · intro hdd
      have : Ω' = Ω := hsame Ω' Ω (by omega)
      rw [this]
  simp only [hcond] at h
  have hsize : #(Ω : Finset (KSub n k × KSub n k))
      = n.choose k * (k.choose d * (n - k).choose d) := by
    rw [card_orbital_johnson, hΩ, show k - (k - d) = d from by omega,
      Nat.choose_symm (show d ≤ k from by omega)]
  rw [hsize] at h
  have hZ : ((∑ t ∈ Finset.range (min k (n - k) + 1),
        (if t = 0 then 1 else (n.choose t : ℤ) - n.choose (t - 1))
          * (eberlein n k d t * eberlein n k d' t) : ℤ) : ℂ)
      = ((if d = d' then (n.choose k * (k.choose d * (n - k).choose d) : ℤ) else 0 : ℤ)
          : ℂ) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun t => (if t = 0 then 1 else (n.choose t : ℤ) - n.choose (t - 1))
        * (eberlein n k d t * eberlein n k d' t)) (min k (n - k) + 1)]
    push_cast
    push_cast at h
    rw [← h]
  exact_mod_cast hZ

end ECCLib.Scheme.Johnson

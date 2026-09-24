/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Johnson
import ECCLib.Matrix.SpectralDetermination
import ECCLib.Delsarte.PairShellSum

/-!
# The spectrum of the Johnson scheme

**The eigenmatrix of the Johnson scheme is the Eberlein family.** The pair-difference
functions are common eigenvectors of the whole Johnson orbital algebra with Eberlein
eigenvalues (`orbitalAdj_mulVec_johnsonVec` — the shell-sum identity of
`Delsarte/PairShellSum.lean` read as a matrix statement); their degree-one values separate
(`Delsarte/Eberlein.lean`'s strict decrease), and there are as many of them as the algebra
has dimensions, so the determination theorem of `Matrix/SpectralDetermination.lean` pins the
whole spectrum: an equivalence `Fin (min k (n−k) + 1) ≃ MaximalSpectrum` under which every
`P`-entry is an Eberlein number (`eigenmatrixP_johnson`).

The carrier is a set of subsets — no group structure, no characters. This is the spectrum the
character-theoretic route of `Scheme/HammingScheme.lean` cannot reach, delivered through the
same shared spine that reuses that route's carrier as its other instance.

## Main definitions

* `orbWidth` — the intersection size an orbital carries.
* `johnsonVec` — the pair-difference eigenvectors.
* `johnsonSpectrumEquiv` — the spectrum equivalence.

## Main results

* `orbitalAdj_mulVec_johnsonVec` — the eigen-equation, for every orbital at once.
* `eigenmatrixP_johnson` — **the main theorem**: `P (σ j) Ω = E_{k − orbWidth Ω}(j)`.

## Implementation notes

The instances declared here (`johnsonCommutative`, `johnsonSpecFintype`, `johnsonSpecDecEq`)
also appear as `local instance`s in `Scheme/OrbitalSpectrumCheck.lean`; the main statement
does not elaborate without them.

The degenerate carrier (`min k (n − k) = 0`) needs no separate branch: zero pairs give the
all-ones vector, the shell sums are the valences, and `eberlein_at_zero` is the `t = 0` row
of the same identity — the machinery is uniform in `j`.
-/

namespace ECCLib.Scheme.Johnson

open Finset Matrix ECCLib.Delsarte

variable {n k : ℕ}

/-- The carrier counts `k`-subsets. Mathlib does not provide this count for the subtype
carrier. -/
theorem card_kSub : Fintype.card (KSub n k) = n.choose k := by
  rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

instance johnsonCommutative :
    Subalgebra.IsCommutative (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) :=
  isCommutative_johnsonAlgebra ℂ

noncomputable instance johnsonSpecFintype :
    Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) := by
  haveI : IsArtinianRing ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) :=
    IsArtinianRing.of_finite ℂ _
  exact Fintype.ofFinite _

noncomputable instance johnsonSpecDecEq :
    DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))) :=
  Classical.decEq _

/-! ## The orbit dictionary: orbitals are intersection shells -/

/-- The intersection size an orbital carries, read off any representative. -/
noncomputable def orbWidth
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) : ℕ :=
  interCard (nonempty_of_mem_orbits Ω.2).choose

theorem interCard_eq_orbWidth {Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))}
    {p : KSub n k × KSub n k} (hp : p ∈ (Ω : Finset (KSub n k × KSub n k))) :
    interCard p = orbWidth Ω := by
  have hrep := (nonempty_of_mem_orbits Ω.2).choose_spec
  have h1 := (mem_iff_orb_eq Ω.2).mp hp
  have h2 := (mem_iff_orb_eq Ω.2).mp hrep
  have hmem : p ∈ orb (Equiv.Perm (Fin n)) (nonempty_of_mem_orbits Ω.2).choose := by
    rw [h2, ← h1]
    exact self_mem_orb p
  obtain ⟨σ, hσ⟩ := mem_orb.mp hmem
  rw [orbWidth, ← hσ, interCard_smul]

/-- **The row of an orbital is an intersection shell**: membership in `Ω` is having its
width. -/
theorem mem_orbital_iff_interCard_eq
    {Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))}
    (p : KSub n k × KSub n k) :
    p ∈ (Ω : Finset (KSub n k × KSub n k)) ↔ interCard p = orbWidth Ω := by
  constructor
  · exact interCard_eq_orbWidth
  · intro hw
    have hrep := (nonempty_of_mem_orbits Ω.2).choose_spec
    have h2 := (mem_iff_orb_eq Ω.2).mp hrep
    have hp : p ∈ MulAction.orbit (Equiv.Perm (Fin n))
        (nonempty_of_mem_orbits Ω.2).choose :=
      (mem_orbit_iff_interCard_eq _ _).mpr (by rw [hw, orbWidth])
    obtain ⟨σ, hσ⟩ := hp
    rw [← h2]
    exact mem_orb.mpr ⟨σ, hσ⟩

theorem orbWidth_le (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) :
    orbWidth Ω ≤ k := by
  rw [orbWidth, interCard]
  calc #((nonempty_of_mem_orbits Ω.2).choose.1.1 ∩ (nonempty_of_mem_orbits Ω.2).choose.2.1)
      ≤ #(nonempty_of_mem_orbits Ω.2).choose.1.1 :=
        Finset.card_le_card Finset.inter_subset_left
    _ = k := KSub.card_val _

/-! ## The pair-difference eigenvectors -/

/-- The standard pair system: the `i`-th pair is `(2i, 2i+1)`. -/
def pairA (n j : ℕ) (h : 2 * j ≤ n) (i : Fin j) : Fin n :=
  ⟨2 * i.val, by omega⟩

def pairB (n j : ℕ) (h : 2 * j ≤ n) (i : Fin j) : Fin n :=
  ⟨2 * i.val + 1, by omega⟩

theorem injective_sumElim_pair {j : ℕ} (h : 2 * j ≤ n) :
    Function.Injective (Sum.elim (pairA n j h) (pairB n j h)) := by
  intro s s' hss
  rcases s with i | i <;> rcases s' with i' | i' <;>
    simp only [Sum.elim_inl, Sum.elim_inr, pairA, pairB, Fin.mk.injEq] at hss <;>
    first
      | (congr 1; exact Fin.ext (by omega))
      | omega

/-- The eigenvector attached to `j` pairs: the pair-difference function, read on the
carrier over `ℂ`. -/
noncomputable def johnsonVec (j : ℕ) (h : 2 * j ≤ n) : KSub n k → ℂ :=
  fun x => ((pairDiff ℤ (pairA n j h) (pairB n j h) x.1 : ℤ) : ℂ)

theorem johnsonVec_ne_zero {j : ℕ} (h : 2 * j ≤ n) (hjk : j ≤ k) (hkj : k + j ≤ n) :
    johnsonVec (k := k) j h ≠ 0 := by
  obtain ⟨K, hKcard, hKone⟩ := exists_card_eq_and_pairDiff_eq_one (R := ℤ)
    (injective_sumElim_pair h) hjk (by rw [Fintype.card_fin]; omega)
  intro hzero
  have hx : (⟨K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, hKcard⟩⟩ : KSub n k)
      ∈ (Finset.univ : Finset (KSub n k)) := Finset.mem_univ _
  have := congrFun hzero ⟨K, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, hKcard⟩⟩
  rw [johnsonVec] at this
  simp only [hKone, Pi.zero_apply] at this
  norm_num at this

/-! ## The eigen-equation -/

/-- **The pair-difference functions are common eigenvectors of every orbital adjacency, with
Eberlein eigenvalues** — the shell-sum identity read as a matrix statement. -/
theorem orbitalAdj_mulVec_johnsonVec {j : ℕ} (h2 : 2 * j ≤ n)
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) :
    orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)) *ᵥ johnsonVec j h2
      = ((eberlein n k (k - orbWidth Ω) j : ℤ) : ℂ) • johnsonVec j h2 := by
  funext x
  have hlhs : (orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)) *ᵥ johnsonVec j h2) x
      = orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)) x ⬝ᵥ johnsonVec j h2 := rfl
  rw [hlhs, Pi.smul_apply]
  have hrow : ∀ y : KSub n k,
      orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)) x y
        = if #(x.1 ∩ y.1) = orbWidth Ω then (1 : ℂ) else 0 := by
    intro y
    rw [orbitalAdj_apply]
    congr 1
    rw [mem_orbital_iff_interCard_eq]
    rfl
  have hdot : (orbitalAdj ℂ (Ω : Finset (KSub n k × KSub n k)) x ⬝ᵥ johnsonVec j h2)
      = ∑ y : KSub n k,
          (if #(x.1 ∩ y.1) = orbWidth Ω then (1 : ℂ) else 0) * johnsonVec j h2 y := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun y _ => by rw [hrow y]
  rw [hdot]
  have hcast : ∀ y : KSub n k,
      (if #(x.1 ∩ y.1) = orbWidth Ω then (1 : ℂ) else 0) * johnsonVec j h2 y
        = ((if #(x.1 ∩ y.1) = orbWidth Ω then (1 : ℤ) else 0)
            * pairDiff ℤ (pairA n j h2) (pairB n j h2) y.1 : ℤ) := by
    intro y
    rw [johnsonVec]
    push_cast
    by_cases hy : #(x.1 ∩ y.1) = orbWidth Ω <;> simp [hy]
  rw [Finset.sum_congr rfl fun y _ => hcast y, ← Int.cast_sum]
  have hshell : (∑ y : KSub n k,
      (if #(x.1 ∩ y.1) = orbWidth Ω then (1 : ℤ) else 0)
        * pairDiff ℤ (pairA n j h2) (pairB n j h2) y.1)
      = ∑ L ∈ (Finset.univ.powersetCard k).filter (fun L => #(x.1 ∩ L) = orbWidth Ω),
          pairDiff ℤ (pairA n j h2) (pairB n j h2) L := by
    rw [show (∑ y : KSub n k, (if #(x.1 ∩ y.1) = orbWidth Ω then (1 : ℤ) else 0)
        * pairDiff ℤ (pairA n j h2) (pairB n j h2) y.1)
        = ∑ y : KSub n k, (if #(x.1 ∩ y.1) = orbWidth Ω
            then pairDiff ℤ (pairA n j h2) (pairB n j h2) y.1 else 0) from
      Finset.sum_congr rfl fun y _ => by
        by_cases hy : #(x.1 ∩ y.1) = orbWidth Ω <;> simp [hy]]
    rw [Finset.sum_coe_sort (Finset.univ.powersetCard k)
      (fun L => if #(x.1 ∩ L) = orbWidth Ω
        then pairDiff ℤ (pairA n j h2) (pairB n j h2) L else 0)]
    rw [Finset.sum_filter]
  rw [hshell, sum_shell_pairDiff (injective_sumElim_pair h2) (KSub.card_val x)
    (orbWidth_le Ω)]
  rw [johnsonVec, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-! ## The determination: the spectrum equivalence and the main theorem -/

/-- The eigenvalue functional data attached to `j` pairs. -/
noncomputable def johnsonMu (j : ℕ)
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) : ℂ :=
  ((eberlein n k (k - orbWidth Ω) j : ℤ) : ℂ)

/-- Every admissible width is realised by an orbital. -/
theorem exists_orbWidth_eq {w : ℕ} (hw1 : w ≤ k) (hw2 : 2 * k ≤ n + w) :
    ∃ Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k)), orbWidth Ω = w := by
  obtain ⟨p, hp⟩ := exists_interCard_eq hw1 hw2
  exact ⟨⟨orb (Equiv.Perm (Fin n)) p, orb_mem_orbits p⟩,
    (interCard_eq_orbWidth (self_mem_orb p)).symm.trans hp⟩

/-- The pair-difference vector is a common eigenvector of the whole Johnson orbital algebra,
through the basis constructor: the functional is the explicit linear form in the Eberlein
data. -/
theorem isCommonEigenvector_johnsonVec {j : ℕ} (h2 : 2 * j ≤ n) (hjk : j ≤ k)
    (hkj : k + j ≤ n) :
    IsCommonEigenvector (orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
      (johnsonVec j h2)
      (fun M => ∑ Ω, (orbitalBasis (R := ℂ)).repr M Ω * johnsonMu (k := k) j Ω) :=
  isCommonEigenvector_basis (orbitalBasis (R := ℂ)) (johnsonMu j)
    (johnsonVec_ne_zero h2 hjk hkj)
    (fun Ω => by
      rw [val_orbitalBasis]
      exact orbitalAdj_mulVec_johnsonVec h2 Ω)

/-- The functional collapses on the orbital basis to the Eberlein datum. -/
theorem johnsonChi_apply_orbitalBasis (j : ℕ)
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) :
    (∑ Ω', (orbitalBasis (R := ℂ)).repr (orbitalBasis (R := ℂ) Ω) Ω'
        * johnsonMu (k := k) j Ω')
      = johnsonMu j Ω := by
  rw [Finset.sum_congr rfl fun Ω' _ => by rw [Module.Basis.repr_self]]
  simp [Finsupp.single_apply]

/-- **The spectrum equivalence, with the main theorem attached**: an equivalence of the index
`Fin (min k (n−k) + 1)` with the maximal spectrum under which every `P`-entry is an Eberlein
number. -/
theorem exists_equiv_eigenmatrixP_eq_eberlein [Nonempty (KSub n k)] :
    ∃ e : Fin (min k (n - k) + 1)
        ≃ MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)),
      ∀ (jj : Fin (min k (n - k) + 1))
        (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))),
        eigenmatrixP (e jj) Ω = ((eberlein n k (k - orbWidth Ω) (jj : ℕ) : ℤ) : ℂ) := by
  classical
  have hk : k ≤ n := KSub.k_le_of_nonempty
  have hbound : ∀ jj : Fin (min k (n - k) + 1),
      2 * (jj : ℕ) ≤ n ∧ (jj : ℕ) ≤ k ∧ k + (jj : ℕ) ≤ n := by
    intro jj
    have := jj.isLt
    omega
  have hsep : Function.Injective (fun jj : Fin (min k (n - k) + 1) =>
      fun M : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) =>
      ∑ Ω, (orbitalBasis (R := ℂ)).repr M Ω * johnsonMu (n := n) (k := k) (jj : ℕ) Ω) := by
    intro jj jj' hchi
    rcases Nat.eq_zero_or_pos (min k (n - k)) with hmin | hmin
    · have h1 := jj.isLt
      have h2 := jj'.isLt
      exact Fin.ext (by omega)
    · have hkn1 : k + 1 ≤ n := by omega
      have hw1 : k - 1 ≤ k := by omega
      have hw2 : 2 * k ≤ n + (k - 1) := by omega
      obtain ⟨Ω₁, hΩ₁⟩ := exists_orbWidth_eq hw1 hw2
      have happ := congrFun hchi (orbitalBasis (R := ℂ) Ω₁)
      simp only [johnsonChi_apply_orbitalBasis] at happ
      rw [johnsonMu, johnsonMu, hΩ₁] at happ
      have hkk1 : k - (k - 1) = 1 := by omega
      rw [hkk1] at happ
      have hint : eberlein n k 1 (jj : ℕ) = eberlein n k 1 (jj' : ℕ) := by
        exact_mod_cast happ
      by_contra hne
      have hjj := jj.isLt
      have hjj' := jj'.isLt
      rcases Nat.lt_or_ge (jj : ℕ) (jj' : ℕ) with hlt | hge
      · exact absurd hint (ne_of_gt (eberlein_degree_one_lt_of_lt hlt
          (by omega) (by omega)))
      · have hlt : (jj' : ℕ) < (jj : ℕ) := by
          rcases Nat.lt_or_ge (jj' : ℕ) (jj : ℕ) with h | h
          · exact h
          · exact absurd (Fin.ext (by omega)) hne
        exact absurd hint.symm (ne_of_gt (eberlein_degree_one_lt_of_lt hlt
          (by omega) (by omega)))
  have hcard : Fintype.card (Fin (min k (n - k) + 1))
      = Module.finrank ℂ ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) := by
    rw [Fintype.card_fin, finrank_orbitalAlgebra, card_orbits_finset_kSub hk]
  obtain ⟨e, he⟩ := exists_equiv_splitChar_of_isCommonEigenvector
    (S := orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k))
    (v := fun jj : Fin (min k (n - k) + 1) => johnsonVec (jj : ℕ) (hbound jj).1)
    (χ := fun jj : Fin (min k (n - k) + 1) =>
      fun M : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) =>
      ∑ Ω, (orbitalBasis (R := ℂ)).repr M Ω * johnsonMu (n := n) (k := k) (jj : ℕ) Ω)
    (fun jj => isCommonEigenvector_johnsonVec (hbound jj).1 (hbound jj).2.1
      (hbound jj).2.2)
    hsep hcard
  refine ⟨e, fun jj Ω => ?_⟩
  have h1 : eigenmatrixP (e jj) Ω
      = idemBasis.repr (orbitalBasis (R := ℂ) Ω) (e jj) := by
    rw [eigenmatrixP, Module.Basis.toMatrix_apply]
  have h2 : idemBasis.repr (orbitalBasis (R := ℂ) Ω) (e jj)
      = ECCLib.splitChar ℂ _ (e jj) (orbitalBasis (R := ℂ) Ω) :=
    idemBasis_repr_eq_splitChar _ _
  have h3 := congrFun (he jj).symm (orbitalBasis (R := ℂ) Ω)
  rw [h1, h2, h3, johnsonChi_apply_orbitalBasis, johnsonMu]

/-- The spectrum equivalence, as data. -/
noncomputable def johnsonSpectrumEquiv [Nonempty (KSub n k)] :
    Fin (min k (n - k) + 1)
      ≃ MaximalSpectrum ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin n)) (KSub n k)) :=
  (exists_equiv_eigenmatrixP_eq_eberlein (n := n) (k := k)).choose

/-- **Main theorem: the eigenmatrix of the Johnson scheme is the Eberlein family.** Under the
spectrum equivalence, the `P`-entry at spectral index `j` and orbital `Ω` is
`E_{k − orbWidth Ω}(j)` — for every `k ≤ n` (the carrier's nonemptiness IS that guard), with
no `2k ≤ n` restriction. -/
theorem eigenmatrixP_johnson [Nonempty (KSub n k)] (jj : Fin (min k (n - k) + 1))
    (Ω : ↥(orbits (Equiv.Perm (Fin n)) (KSub n k × KSub n k))) :
    eigenmatrixP (johnsonSpectrumEquiv jj) Ω
      = ((eberlein n k (k - orbWidth Ω) (jj : ℕ) : ℤ) : ℂ) :=
  (exists_equiv_eigenmatrixP_eq_eberlein (n := n) (k := k)).choose_spec jj Ω

end ECCLib.Scheme.Johnson

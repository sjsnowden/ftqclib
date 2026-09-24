/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitalSpectrum

/-!
# The orthogonality relations of an orbital scheme

**One trace computed two ways.** Spectrally, the trace of a product of orbital adjacencies
is the multiplicity-weighted product of their character values (`splitChar` is an algebra
map, so the trace system reads at products); combinatorially it is a pair count that the
orbit partition collapses to a diagonal against the **transpose** orbital. Equating the two
gives the full orthogonality of the eigenmatrix rows
(`sum_spectralMult_mul_eigenmatrixP_mul_eigenmatrixP`). Running the same two-ways trace at
a primitive idempotent against an adjacency gives the **second eigenmatrix explicitly**,
division-free (`card_mul_eigenmatrixQ_transposePairs`), as a corollary.

The Johnson and Hamming instantiations are `Scheme/JohnsonOrthogonality.lean` and
`Scheme/HammingOrthogonality.lean`.

## Main results

* `sum_spectralMult_mul_eigenmatrixP_mul_eigenmatrixP` — **the full orthogonality**, with
  the transpose orbital on the diagonal; no symmetry hypothesis.
* `card_mul_eigenmatrixQ_transposePairs` — **`Q`, explicitly**:
  `#Ω · Q(Ωᵗ, I) = |X| · m_I · P(I, Ω)`.
-/

namespace ECCLib.Scheme

open Finset Matrix

section Orthogonality

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]
variable [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
variable [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
variable [Nonempty X]

/-- The split character of a basis adjacency is the `P`-entry — the bridge both results
below run through. -/
theorem splitChar_orbitalBasis (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X))
    (Ω : ↥(orbits G (X × X))) :
    ECCLib.splitChar ℂ ↥(orbitalAlgebra ℂ G X) I (orbitalBasis (R := ℂ) Ω)
      = eigenmatrixP (G := G) (X := X) I Ω := by
  rw [← idemBasis_repr_eq_splitChar]
  rw [show orbitalBasis (R := ℂ) Ω
      = ⟨orbitalAdj ℂ (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩ from
    congrFun coe_orbitalBasis Ω]
  rw [← eigenmatrixP_apply]

/-- **The full orthogonality relations**: the multiplicity-weighted product of two rows of
`P` is the size of the orbital on the transpose-diagonal, and zero elsewhere. No symmetry
hypothesis — for a self-paired action `Ωᵗ = Ω`
(`transposePairs_eq_self_of_isSelfPaired`) and the diagonal is literal. -/
theorem sum_spectralMult_mul_eigenmatrixP_mul_eigenmatrixP (Ω Ω' : ↥(orbits G (X × X))) :
    ∑ I, (spectralMult (orbitalAlgebra ℂ G X) I : ℂ)
        * (eigenmatrixP (G := G) (X := X) I Ω * eigenmatrixP (G := G) (X := X) I Ω')
      = if (Ω' : Finset (X × X)) = transposePairs (Ω : Finset (X × X))
          then (#(Ω : Finset (X × X)) : ℂ) else 0 := by
  have h := sum_spectralMult_mul_splitChar_mul_splitChar (S := orbitalAlgebra ℂ G X)
    (orbitalBasis (R := ℂ) Ω) (orbitalBasis (R := ℂ) Ω')
  rw [Finset.sum_congr rfl fun I _ => by
    rw [splitChar_orbitalBasis, splitChar_orbitalBasis]] at h
  rw [h]
  rw [show (((orbitalBasis (R := ℂ) Ω * orbitalBasis (R := ℂ) Ω'
        : ↥(orbitalAlgebra ℂ G X))) : Matrix X X ℂ)
      = orbitalAdj ℂ (Ω : Finset (X × X)) * orbitalAdj ℂ (Ω' : Finset (X × X)) from by
    rw [show orbitalBasis (R := ℂ) (G := G) (X := X)
        = fun Ω : ↥(orbits G (X × X)) =>
          (⟨orbitalAdj ℂ (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩
            : ↥(orbitalAlgebra ℂ G X)) from coe_orbitalBasis]
    rfl]
  exact trace_orbitalAdj_mul_orbitalAdj Ω.2 Ω'.2

/-- **The second eigenmatrix, explicitly and division-free**:
`#Ω · Q(Ωᵗ, I) = |X| · m_I · P(I, Ω)` — the trace of a primitive idempotent against an
adjacency computed two ways: spectrally it is `m_I · P(I, Ω)`; entrywise the idempotent is
constant on the transpose orbital, where its entry is `Q(Ωᵗ, I)/|X|`. -/
theorem card_mul_eigenmatrixQ_transposePairs (Ω : ↥(orbits G (X × X)))
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    (#(Ω : Finset (X × X)) : ℂ)
        * eigenmatrixQ (G := G) (X := X)
            ⟨transposePairs (Ω : Finset (X × X)), transposePairs_mem_orbits Ω.2⟩ I
      = (Fintype.card X : ℂ)
          * ((spectralMult (orbitalAlgebra ℂ G X) I : ℂ)
              * eigenmatrixP (G := G) (X := X) I Ω) := by
  classical
  set E : Matrix X X ℂ :=
    ((ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I
      : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) with hE
  -- way A: the spectral trace
  have hA : (E * orbitalAdj ℂ (Ω : Finset (X × X))).trace
      = (spectralMult (orbitalAlgebra ℂ G X) I : ℂ)
          * eigenmatrixP (G := G) (X := X) I Ω := by
    have h := sum_spectralMult_mul_splitChar_mul_splitChar (S := orbitalAlgebra ℂ G X)
      (ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I)
      (orbitalBasis (R := ℂ) Ω)
    rw [Finset.sum_congr rfl fun J _ => by
      rw [ECCLib.splitChar_primitiveIdempotent, splitChar_orbitalBasis]] at h
    rw [Finset.sum_eq_single I
      (fun J _ hJI => by rw [if_neg hJI, zero_mul, mul_zero])
      (fun hI => absurd (Finset.mem_univ I) hI)] at h
    rw [if_pos rfl, one_mul] at h
    rw [show ((ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I
          * orbitalBasis (R := ℂ) Ω : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
        = E * orbitalAdj ℂ (Ω : Finset (X × X)) from by
      rw [show orbitalBasis (R := ℂ) (G := G) (X := X)
          = fun Ω : ↥(orbits G (X × X)) =>
            (⟨orbitalAdj ℂ (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩
              : ↥(orbitalAlgebra ℂ G X)) from coe_orbitalBasis]
      rfl] at h
    exact h.symm
  -- way B: the entrywise trace, through constancy on the transpose orbital
  set p₀ : X × X :=
    (nonempty_of_mem_orbits (transposePairs_mem_orbits (G := G) Ω.2)).choose with hp₀def
  have hp₀ : p₀ ∈ transposePairs (Ω : Finset (X × X)) :=
    (nonempty_of_mem_orbits (transposePairs_mem_orbits (G := G) Ω.2)).choose_spec
  have hB : (E * orbitalAdj ℂ (Ω : Finset (X × X))).trace
      = (#(Ω : Finset (X × X)) : ℂ) * E p₀.1 p₀.2 := by
    have hexp : (E * orbitalAdj ℂ (Ω : Finset (X × X))).trace
        = ∑ p : X × X,
            if p ∈ transposePairs (Ω : Finset (X × X)) then E p.1 p.2 else 0 := by
      rw [Matrix.trace]
      rw [show ∑ x, (E * orbitalAdj ℂ (Ω : Finset (X × X))).diag x
          = ∑ x, ∑ y, E x y * if (y, x) ∈ (Ω : Finset (X × X)) then (1 : ℂ) else 0 from
        Finset.sum_congr rfl fun x _ => by
          rw [Matrix.diag_apply, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun y _ => by rw [orbitalAdj_apply]]
      rw [show (∑ x, ∑ y, E x y * if (y, x) ∈ (Ω : Finset (X × X)) then (1 : ℂ) else 0)
          = ∑ p : X × X,
              E p.1 p.2 * if p.swap ∈ (Ω : Finset (X × X)) then (1 : ℂ) else 0 from
        (Fintype.sum_prod_type (f := fun p : X × X =>
          E p.1 p.2 * if p.swap ∈ (Ω : Finset (X × X)) then (1 : ℂ) else 0)).symm]
      exact Finset.sum_congr rfl fun p _ => by
        by_cases hp : p.swap ∈ (Ω : Finset (X × X)) <;>
          simp [hp, mem_transposePairs]
    rw [hexp, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hconst : ∀ p ∈ transposePairs (Ω : Finset (X × X)), E p.1 p.2 = E p₀.1 p₀.2 := by
      intro p hp
      have hmem := (ECCLib.primitiveIdempotent ℂ ↥(orbitalAlgebra ℂ G X) I
        : ↥(orbitalAlgebra ℂ G X)).2
      rw [mem_orbitalAlgebra_iff_orb] at hmem
      refine hmem p p₀ ?_
      rw [(mem_iff_orb_eq (transposePairs_mem_orbits Ω.2)).mp hp,
        (mem_iff_orb_eq (transposePairs_mem_orbits Ω.2)).mp hp₀]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, card_transposePairs]
  -- the Q entry is |X| times the idempotent's entry on the transpose orbital
  have hQ : eigenmatrixQ (G := G) (X := X)
        ⟨transposePairs (Ω : Finset (X × X)), transposePairs_mem_orbits Ω.2⟩ I
      = (Fintype.card X : ℂ) * E p₀.1 p₀.2 := by
    rw [eigenmatrixQ_eq_card_mul_entry (Ω := ⟨transposePairs (Ω : Finset (X × X)),
      transposePairs_mem_orbits Ω.2⟩) hp₀]
    rfl
  rw [hQ]
  linear_combination (Fintype.card X : ℂ) * (hB.symm.trans hA)

end Orthogonality

end ECCLib.Scheme

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingScheme

/-!
# The Krawtchouk orthogonality, spectrally

The Hamming instantiation of the two-ways trace (`Scheme/OrbitalOrthogonality.lean`): **the
textbook Krawtchouk orthogonality**

`∑_w C(n,w)(q−1)^w · K_i(w) · K_j(w) = δ_ij · qⁿ · C(n,i)(q−1)^i`

(Cohn–Zhao, eq. (2)) — derived from
the scheme, not from generating functions: the multiplicities are the dual shell sizes
(`spectralMult_translationSpectrumEquiv` + `card_shellSet`), the character values are
Krawtchouk numbers (`splitChar_adj_eq_kraw`), and the trace of a product of shell
adjacencies is a diagonal count (`trace_adj_mul_adj`; a weight shell is its own negation by
`hammingNorm_neg`). Stated at every alphabet carrying the scheme (`TransOnNonzero`,
`1 < q`), which covers the elementary-abelian and Klein/Pauli cases.
**The all-`q` arithmetic form is a different genre** (generating-function coefficient
algebra) and is not proved here.

## Main results

* `shellSet_mem_orbits` / `exists_dualWeight_eq` — under transitivity every dual weight
  shell `w ≤ n` is a dual orbit, and every weight is realised.
* `kraw_orthogonality` — **the orthogonality identity**, guarded `ℤ` form.
-/

namespace ECCLib.Scheme

open Finset MulAction ECCLib.Delsarte
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {G : Type*} [Group G] [Finite G] [DistribMulAction G A]

omit [DecidableEq A] in
/-- Under transitivity every dual weight `w ≤ n` is realised by a character: place a
nonzero coordinate character at `w` positions. -/
theorem exists_dualWeight_eq (hA : 1 < Fintype.card A) {w : ℕ}
    (hw : w ≤ Fintype.card ι) :
    ∃ ξ : AddChar (ι → A) ℂ, dualWeight ξ = w := by
  classical
  have hA' : 1 < Fintype.card (AddChar A ℂ) := by
    rwa [AddChar.card_eq]
  obtain ⟨χt, hχt⟩ := ECCLib.Delsarte.exists_word_of_weight
    (ι := ι) (A := AddChar A ℂ) hA' hw
  exact ⟨piChar χt, by rw [dualWeight, coordChar_piChar, hχt]⟩

omit [Fintype A] [DecidableEq A] in
/-- The dual weight is at most the coordinate count. -/
theorem dualWeight_le (ξ : AddChar (ι → A) ℂ) : dualWeight ξ ≤ Fintype.card ι := by
  rw [dualWeight, hammingNorm]
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_univ))

/-- Under transitivity the dual weight shells are dual orbits. -/
theorem shellSet_mem_orbits (htrans : TransOnNonzero G A) (hA : 1 < Fintype.card A)
    {w : ℕ} (hw : w ≤ Fintype.card ι) :
    shellSet ι A w ∈ orbits (↥(monomialSubgroup ι A G)) (AddChar (ι → A) ℂ) := by
  obtain ⟨ξ, hξ⟩ := exists_dualWeight_eq (ι := ι) hA hw
  rw [show shellSet ι A w = orb (↥(monomialSubgroup ι A G)) ξ from by
    rw [orb_eq_shellSet htrans, hξ]]
  exact orb_mem_orbits _

omit [DecidableEq ι] [DecidableEq A] in
/-- **The Krawtchouk orthogonality**: against the shell-size weights,
distinct Krawtchouk rows are orthogonal and the diagonal is `qⁿ` times the shell size —
the guarded `ℤ` form, at every alphabet carrying the scheme. -/
theorem kraw_orthogonality (htrans : TransOnNonzero G A) (hA : 1 < Fintype.card A)
    {i j : ℕ} (hi : i ≤ Fintype.card ι) (hj : j ≤ Fintype.card ι) :
    ∑ w ∈ Finset.range (Fintype.card ι + 1),
        (((Fintype.card ι).choose w * (Fintype.card A - 1) ^ w : ℕ) : ℤ)
          * (kraw (Fintype.card A) (Fintype.card ι) i w
              * kraw (Fintype.card A) (Fintype.card ι) j w)
      = if i = j
          then ((Fintype.card A ^ Fintype.card ι
              * ((Fintype.card ι).choose i * (Fintype.card A - 1) ^ i) : ℕ) : ℤ)
          else 0 := by
  classical
  obtain ⟨x, hx⟩ := ECCLib.Delsarte.exists_word_of_weight (ι := ι) (A := A) hA hi
  obtain ⟨y, hy⟩ := ECCLib.Delsarte.exists_word_of_weight (ι := ι) (A := A) hA hj
  set H := ↥(monomialSubgroup ι A G) with hH
  have hRx : orb H x = Finset.univ.filter (fun v : ι → A => hammingNorm v = i) := by
    rw [orb_eq_shell htrans]
    simp only [hx]
  have hRy : orb H y = Finset.univ.filter (fun v : ι → A => hammingNorm v = j) := by
    rw [orb_eq_shell htrans]
    simp only [hy]
  have h := sum_spectralMult_mul_splitChar_mul_splitChar
    (S := schemeAlgebra H (ι → A))
    ⟨adj (orb H x), adj_mem_schemeAlgebra (orb_mem_orbits x)⟩
    ⟨adj (orb H y), adj_mem_schemeAlgebra (orb_mem_orbits y)⟩
  -- the trace side: the transpose count at self-negating shells
  rw [show (((⟨adj (orb H x), adj_mem_schemeAlgebra (orb_mem_orbits x)⟩
        * ⟨adj (orb H y), adj_mem_schemeAlgebra (orb_mem_orbits y)⟩
        : ↥(schemeAlgebra H (ι → A)))) : Matrix (ι → A) (ι → A) ℂ)
      = adj (orb H x) * adj (orb H y) from rfl] at h
  rw [trace_adj_mul_adj (orb_mem_orbits x) (orb_mem_orbits y)] at h
  have hnegshell : (orb H x).image (fun w => -w) = orb H x := by
    ext u
    rw [mem_image_neg, hRx]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hnu
      rw [← ECCLib.Delsarte.hammingNorm_neg u]
      exact hnu
    · intro hu
      rw [ECCLib.Delsarte.hammingNorm_neg u]
      exact hu
  have hcond : (orb H y = (orb H x).image (fun w => -w)) = (i = j) := by
    apply propext
    rw [hnegshell]
    constructor
    · intro heq
      have hyy : y ∈ orb H x := heq ▸ self_mem_orb y
      rw [hRx, Finset.mem_filter] at hyy
      omega
    · intro hij
      rw [hRx, hRy, hij]
  simp only [hcond] at h
  have hcardR : #(orb H x) = (Fintype.card ι).choose i * (Fintype.card A - 1) ^ i := by
    rw [hRx, card_shell]
  rw [hcardR] at h
  -- the spectral side: reindex the maximal spectrum by the dual orbits, then by weights
  rw [show ∑ I, (spectralMult (schemeAlgebra H (ι → A)) I : ℂ)
        * (ECCLib.splitChar ℂ ↥(schemeAlgebra H (ι → A)) I
              ⟨adj (orb H x), adj_mem_schemeAlgebra (orb_mem_orbits x)⟩
            * ECCLib.splitChar ℂ ↥(schemeAlgebra H (ι → A)) I
              ⟨adj (orb H y), adj_mem_schemeAlgebra (orb_mem_orbits y)⟩)
      = ∑ S : ↥(orbits H (AddChar (ι → A) ℂ)),
          (spectralMult (schemeAlgebra H (ι → A)) (translationSpectrumEquiv S) : ℂ)
            * (ECCLib.splitChar ℂ ↥(schemeAlgebra H (ι → A))
                  (translationSpectrumEquiv S)
                  ⟨adj (orb H x), adj_mem_schemeAlgebra (orb_mem_orbits x)⟩
                * ECCLib.splitChar ℂ ↥(schemeAlgebra H (ι → A))
                  (translationSpectrumEquiv S)
                  ⟨adj (orb H y), adj_mem_schemeAlgebra (orb_mem_orbits y)⟩) from
    (Fintype.sum_equiv (translationSpectrumEquiv (H := H) (V := ι → A)) _ _
      fun S => rfl).symm] at h
  rw [show ∑ S : ↥(orbits H (AddChar (ι → A) ℂ)),
        (spectralMult (schemeAlgebra H (ι → A)) (translationSpectrumEquiv S) : ℂ)
          * (ECCLib.splitChar ℂ ↥(schemeAlgebra H (ι → A))
                (translationSpectrumEquiv S)
                ⟨adj (orb H x), adj_mem_schemeAlgebra (orb_mem_orbits x)⟩
              * ECCLib.splitChar ℂ ↥(schemeAlgebra H (ι → A))
                (translationSpectrumEquiv S)
                ⟨adj (orb H y), adj_mem_schemeAlgebra (orb_mem_orbits y)⟩)
      = ∑ w ∈ Finset.range (Fintype.card ι + 1),
          (((Fintype.card ι).choose w * (Fintype.card A - 1) ^ w : ℕ) : ℂ)
            * (((kraw (Fintype.card A) (Fintype.card ι) i w : ℤ) : ℂ)
                * ((kraw (Fintype.card A) (Fintype.card ι) j w : ℤ) : ℂ)) from ?_] at h
  · -- assemble the ℤ statement from the ℂ identity
    have hZ : ((∑ w ∈ Finset.range (Fintype.card ι + 1),
          (((Fintype.card ι).choose w * (Fintype.card A - 1) ^ w : ℕ) : ℤ)
            * (kraw (Fintype.card A) (Fintype.card ι) i w
                * kraw (Fintype.card A) (Fintype.card ι) j w) : ℤ) : ℂ)
        = ((if i = j
            then ((Fintype.card A ^ Fintype.card ι
                * ((Fintype.card ι).choose i * (Fintype.card A - 1) ^ i) : ℕ) : ℤ)
            else 0 : ℤ) : ℂ) := by
      push_cast
      push_cast at h
      rw [h]
      rw [show ((Fintype.card (ι → A)) : ℂ) = (Fintype.card A : ℂ) ^ Fintype.card ι from by
        rw [Fintype.card_fun]
        push_cast
        rfl]
    exact_mod_cast hZ
  · -- the weight reindex
    refine Finset.sum_bij'
      (i := fun S _ => dualWeight (nonempty_of_mem_orbits S.2).choose)
      (j := fun w hw => ⟨shellSet ι A w, shellSet_mem_orbits htrans hA
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hw))⟩)
      (fun S _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (dualWeight_le _)))
      (fun w _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro S _
      apply Subtype.ext
      have hrep := (nonempty_of_mem_orbits S.2).choose_spec
      calc shellSet ι A (dualWeight (nonempty_of_mem_orbits S.2).choose)
          = orb H (nonempty_of_mem_orbits S.2).choose := (orb_eq_shellSet htrans _).symm
        _ = (S : Finset (AddChar (ι → A) ℂ)) := (mem_iff_orb_eq S.2).mp hrep
    · intro w hw
      have hmem := (nonempty_of_mem_orbits (shellSet_mem_orbits (G := G) htrans hA
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)))).choose_spec
      rw [mem_shellSet_iff] at hmem
      exact hmem
    · intro S _
      have hrep := (nonempty_of_mem_orbits S.2).choose_spec
      have hSeq : (S : Finset (AddChar (ι → A) ℂ))
          = shellSet ι A (dualWeight (nonempty_of_mem_orbits S.2).choose) := by
        rw [← orb_eq_shellSet htrans]
        exact ((mem_iff_orb_eq S.2).mp hrep).symm
      have hcard : (S : Finset (AddChar (ι → A) ℂ)).card
          = (Fintype.card ι).choose (dualWeight (nonempty_of_mem_orbits S.2).choose)
            * (Fintype.card A - 1) ^ (dualWeight (nonempty_of_mem_orbits S.2).choose) :=
        (congrArg Finset.card hSeq).trans (card_shellSet _)
      rw [spectralMult_translationSpectrumEquiv, hcard]
      rw [splitChar_adj_eq_kraw htrans (orb_mem_orbits x) (self_mem_orb x) S hrep,
        splitChar_adj_eq_kraw htrans (orb_mem_orbits y) (self_mem_orb y) S hrep]
      rw [hx, hy]

end ECCLib.Scheme

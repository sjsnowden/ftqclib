/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.SpectralPositivity
import ECCLib.Scheme.OrbitalSpectrum

/-!
# Delsarte's inequality at the orbital layer

For any finite group action and any subset `C` of the carrier, the **inner distribution** of `C`
— its ordered pairs counted per orbital (`orbCount`) — pairs nonnegatively against every
column of the second eigenmatrix:

  `0 ≤ Σ_Ω orbCount(C,Ω) · Q(Ω, I)`.

This is Delsarte's linear-programming inequality with no commutativity of the *carrier*
anywhere — the mirror, for orbital schemes, of the translation-side
`Scheme/LP.lean`/`Delsarte.delsarte_nonneg`, whose character route needs an abelian
group. The proof is the quadratic form of the positive-semidefinite primitive idempotent
(`posSemidef_coe_orbitalIdem`, the `⋆`-closure bridge of
`Matrix/SpectralPositivity.lean`) at the indicator vector of `C`, with the pair sum
regrouped by the orbital partition and the idempotent entries read off as `Q`-entries
(`eigenmatrixQ_eq_card_mul_entry`).

## Main definitions

* `orbCount` — the (unnormalised) inner distribution: ordered pairs of `C` in an orbital.

## Main results

* `posSemidef_coe_orbitalIdem` — the orbital idempotents are positive semidefinite.
* `sum_orbCount_mul_eigenmatrixQ` — the regrouping identity.
* `delsarte_nonneg_orbital` — **the inequality**.
-/

namespace ECCLib.Scheme

open Finset Matrix MulAction
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]
variable [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
variable [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]

/-! ## The idempotents are projections -/

omit [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] in
/-- The orbital idempotents are Hermitian: the `⋆`-closure bridge, with the closure
discharged by `conjTranspose_mem_orbitalAlgebra`. -/
theorem conjTranspose_coe_orbitalIdem (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)ᴴ
      = ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ) :=
  conjTranspose_coe_primitiveIdempotent
    (fun _ hM => conjTranspose_mem_orbitalAlgebra hM) I

omit [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] in
/-- **The orbital idempotents are positive semidefinite** — they are the orthogonal
projections onto the common eigenspaces. -/
theorem posSemidef_coe_orbitalIdem (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ).PosSemidef :=
  posSemidef_coe_primitiveIdempotent
    (fun _ hM => conjTranspose_mem_orbitalAlgebra hM) I

/-! ## The inner distribution -/

/-- The (unnormalised) **inner distribution**: ordered pairs of `C` lying in a given set
of pairs — at an orbital, the count Delsarte calls `|C|·B_i`. -/
def orbCount (C : Finset X) (Ω : Finset (X × X)) : ℕ :=
  #((C ×ˢ C).filter (fun p => p ∈ Ω))

omit [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]
  [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
  [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] in
/-- Membership in an orbital is the fiber condition of the orbit map. -/
theorem filter_mem_orbital_eq (C : Finset X) (Ω : ↥(orbits G (X × X))) :
    (C ×ˢ C).filter (fun p => p ∈ (Ω : Finset (X × X)))
      = (C ×ˢ C).filter (fun p =>
          (⟨orb G p, orb_mem_orbits p⟩ : ↥(orbits G (X × X))) = Ω) := by
  refine Finset.filter_congr fun p _ => ?_
  constructor
  · intro hp
    exact Subtype.ext ((mem_iff_orb_eq Ω.2).mp hp)
  · intro hp
    exact (mem_iff_orb_eq Ω.2).mpr (congrArg Subtype.val hp)

omit [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]
  [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
  [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] in
/-- **The inner distribution fills the square**: the orbitals partition the pairs. -/
theorem sum_orbCount (C : Finset X) :
    ∑ Ω : ↥(orbits G (X × X)), orbCount C (Ω : Finset (X × X)) = #C ^ 2 := by
  rw [show ∑ Ω : ↥(orbits G (X × X)), orbCount C (Ω : Finset (X × X))
      = ∑ Ω : ↥(orbits G (X × X)), ∑ _p ∈ (C ×ˢ C).filter (fun p =>
          (⟨orb G p, orb_mem_orbits p⟩ : ↥(orbits G (X × X))) = Ω), 1 from
    Finset.sum_congr rfl fun Ω _ => by
      rw [Finset.sum_const, smul_eq_mul, mul_one, orbCount, filter_mem_orbital_eq]]
  rw [Finset.sum_fiberwise (C ×ˢ C)
    (fun p => (⟨orb G p, orb_mem_orbits p⟩ : ↥(orbits G (X × X)))) (fun _ => 1)]
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_product, sq]

variable [Nonempty X]

/-- **The regrouping identity**: the inner distribution against a `Q`-column is `|X|`
times the pair sum of the idempotent's entries over `C × C` — the quadratic form of the
idempotent at the indicator of `C`, before it is named as one. -/
theorem sum_orbCount_mul_eigenmatrixQ (C : Finset X)
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    ∑ Ω : ↥(orbits G (X × X)), (orbCount C (Ω : Finset (X × X)) : ℂ)
        * eigenmatrixQ (G := G) (X := X) Ω I
      = (Fintype.card X : ℂ) * ∑ p ∈ C ×ˢ C,
          ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
            p.1 p.2 := by
  rw [show ∑ p ∈ C ×ˢ C,
      ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
        p.1 p.2
      = ∑ Ω : ↥(orbits G (X × X)), ∑ p ∈ (C ×ˢ C).filter (fun p =>
          (⟨orb G p, orb_mem_orbits p⟩ : ↥(orbits G (X × X))) = Ω),
          ((orbitalIdem (G := G) (X := X) I : ↥(orbitalAlgebra ℂ G X)) : Matrix X X ℂ)
            p.1 p.2 from
    (Finset.sum_fiberwise (C ×ˢ C)
      (fun p => (⟨orb G p, orb_mem_orbits p⟩ : ↥(orbits G (X × X)))) _).symm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Ω _ => ?_
  rw [← filter_mem_orbital_eq, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun p hp =>
    (eigenmatrixQ_eq_card_mul_entry (Finset.mem_filter.mp hp).2 I).symm]
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

omit [Subalgebra.IsCommutative (orbitalAlgebra ℂ G X)]
  [Fintype (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))]
  [DecidableEq (MaximalSpectrum ↥(orbitalAlgebra ℂ G X))] [Nonempty X] in
/-- The pair sum over `C × C` is the quadratic form at the indicator vector of `C`. -/
theorem sum_pair_eq_dotProduct (M : Matrix X X ℂ) (C : Finset X) :
    ∑ p ∈ C ×ˢ C, M p.1 p.2
      = star (fun x => if x ∈ C then (1 : ℂ) else 0) ⬝ᵥ
          (M *ᵥ fun x => if x ∈ C then (1 : ℂ) else 0) := by
  have hstar : (star (fun x => if x ∈ C then (1 : ℂ) else 0) : X → ℂ)
      = fun x => if x ∈ C then (1 : ℂ) else 0 := by
    funext u
    by_cases h : u ∈ C <;> simp [h]
  have hvec : ∀ u, (M *ᵥ fun x => if x ∈ C then (1 : ℂ) else 0) u = ∑ v ∈ C, M u v := by
    intro u
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hstar]
  have h1 : (fun x => if x ∈ C then (1 : ℂ) else 0) ⬝ᵥ
      (M *ᵥ fun x => if x ∈ C then (1 : ℂ) else 0)
      = ∑ u : X, (if u ∈ C then (1 : ℂ) else 0) * ∑ v ∈ C, M u v := by
    rw [show (fun x => if x ∈ C then (1 : ℂ) else 0) ⬝ᵥ
        (M *ᵥ fun x => if x ∈ C then (1 : ℂ) else 0)
        = ∑ u : X, (if u ∈ C then (1 : ℂ) else 0)
            * (M *ᵥ fun x => if x ∈ C then (1 : ℂ) else 0) u from rfl]
    exact Finset.sum_congr rfl fun u _ => by rw [hvec u]
  have h2 : (∑ u : X, (if u ∈ C then (1 : ℂ) else 0) * ∑ v ∈ C, M u v)
      = ∑ u ∈ C, ∑ v ∈ C, M u v := by
    rw [show (∑ u : X, (if u ∈ C then (1 : ℂ) else 0) * ∑ v ∈ C, M u v)
        = ∑ u : X, (if u ∈ C then (∑ v ∈ C, M u v) else 0) from
      Finset.sum_congr rfl fun u _ => by rw [ite_mul, one_mul, zero_mul]]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, h2, Finset.sum_product]

/-- **Delsarte's inequality at the orbital layer**: the inner distribution
of any subset pairs nonnegatively against every column of the second eigenmatrix. -/
theorem delsarte_nonneg_orbital (C : Finset X)
    (I : MaximalSpectrum ↥(orbitalAlgebra ℂ G X)) :
    0 ≤ ∑ Ω : ↥(orbits G (X × X)), (orbCount C (Ω : Finset (X × X)) : ℂ)
        * eigenmatrixQ (G := G) (X := X) Ω I := by
  rw [sum_orbCount_mul_eigenmatrixQ C I, sum_pair_eq_dotProduct]
  have hcard : (0 : ℂ) ≤ (Fintype.card X : ℂ) := by
    exact_mod_cast Complex.zero_le_real.mpr (Nat.cast_nonneg _)
  exact mul_nonneg hcard
    ((posSemidef_coe_orbitalIdem I).dotProduct_mulVec_nonneg _)

end ECCLib.Scheme

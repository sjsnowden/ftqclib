/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.PermCommutant
import ECCLib.Scheme.Orbits
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The orbital algebra of a group action on a finite type

Let a finite group `G` act on a finite type `X` carrying **no algebraic structure at all**.
The matrices commuting with every permutation matrix of the action form a subalgebra, and it
has an obvious basis: let `G` act diagonally on `X × X`, take the orbits of that action — the
*orbitals* — and take the indicator matrix of each. The dimension of the algebra is therefore
the number of orbitals.

Classical combinatorics calls this the Bose–Mesner algebra of an association scheme. Obtaining
it as a commutant rather than axiomatizing it means nothing is postulated: closure under
multiplication is free, because a centralizer is a subalgebra by construction.

## Main definitions

* `actPerms` — the action of `G` on `X`, as a set of permutations.
* `orbitalAlgebra` — the commutant of that set.
* `orbitalAdj` — the indicator matrix of an orbital.
* `orbitalBasis` — the orbital indicators, as a basis.

## Main results

* `mem_orbitalAlgebra_iff` — membership is invariance under the diagonal action.
* `mem_orbitalAlgebra_iff_orb` — equivalently, constancy on orbitals.
* `finrank_orbitalAlgebra` — **the dimension is the number of orbitals.**

## Implementation notes

Everything below the dimension theorem is stated over an arbitrary `CommRing`, and only
`finrank_orbitalAlgebra` asks for a field. This is not generality for its own sake. The left
regular action of a group on itself is a permutation action, so at `R = ZMod 2` this layer
gives the matrix form of left/right commutation together with the fact that the right regular
representation is the *entire* commutant — which is what a binary group-algebra layer needs.
Pinning the lower layers to `ℂ` would be a strictly weaker theorem written for no reason.

The orbital index is literally `orbits G (X × X)` from `Scheme/Orbits.lean`: no new orbit
notion is introduced, so every lemma there applies with no transfer layer. The diagonal action
on `X × X` is Mathlib's `Prod` instance, and `g • p = (g • p.1, g • p.2)` holds by `rfl`.

`orbitalAlgebra` is *defined* as a `permCommutant` of a set rather than restated, so that the
translation scheme — which centralizes translations together with a symmetry action — can be
recognised as an instance without constructing the group they generate.
-/

namespace ECCLib.Scheme

open Finset Matrix

section Orbital

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable (R : Type*) [CommRing R]

/-- The action of `G` on `X`, as a set of permutations of `X`. -/
def actPerms (G : Type*) [Group G] (X : Type*) [MulAction G X] : Set (Equiv.Perm X) :=
  Set.range (fun g : G => (MulAction.toPerm g : Equiv.Perm X))

/-- The commutant of a group action on a bare finite type: the Bose–Mesner algebra of the
scheme the action defines, obtained rather than axiomatized. -/
def orbitalAlgebra (G : Type*) [Group G] [Fintype G] (X : Type*) [Fintype X] [DecidableEq X]
    [MulAction G X] : Subalgebra R (Matrix X X R) :=
  permCommutant R (actPerms G X)

variable {R}

/-- Membership is invariance under the diagonal action. -/
theorem mem_orbitalAlgebra_iff (M : Matrix X X R) :
    M ∈ orbitalAlgebra R G X ↔ ∀ (g : G) (x y : X), M (g • x) (g • y) = M x y := by
  rw [orbitalAlgebra, mem_permCommutant_iff]
  constructor
  · intro h g x y
    exact h _ ⟨g, rfl⟩ x y
  · rintro h _ ⟨g, rfl⟩ x y
    exact h g x y

/-- Equivalently: constancy on the orbitals. -/
theorem mem_orbitalAlgebra_iff_orb (M : Matrix X X R) :
    M ∈ orbitalAlgebra R G X ↔
      ∀ p q : X × X, orb G p = orb G q → M p.1 p.2 = M q.1 q.2 := by
  rw [mem_orbitalAlgebra_iff]
  constructor
  · intro h p q hpq
    have hp : p ∈ orb G q := by
      rw [← hpq]; exact self_mem_orb (H := G) p
    obtain ⟨g, hg⟩ := mem_orb.mp hp
    rw [← hg]
    exact h g q.1 q.2
  · intro h g x y
    exact h (g • x, g • y) (x, y) (orb_smul g ((x, y) : X × X))

/-- The indicator matrix of a set of ordered pairs. -/
def orbitalAdj (R : Type*) [CommRing R] {X : Type*} [DecidableEq X] (Ω : Finset (X × X)) :
    Matrix X X R :=
  Matrix.of fun x y => if (x, y) ∈ Ω then 1 else 0

/-- The defining conditional of `orbitalAdj`, as a rewrite. Deliberately **not** `@[simp]`:
`simp` would unfold membership in an orbital straight to an existential over the group, stepping
past the orbit-level lemmas that make such goals tractable. Consumers rewrite with this and then
close the conditional with `if_pos` / `if_neg`. -/
theorem orbitalAdj_apply {R : Type*} [CommRing R] {X : Type*} [DecidableEq X]
    (Ω : Finset (X × X)) (u v : X) :
    orbitalAdj R Ω u v = if (u, v) ∈ Ω then 1 else 0 := rfl

/-- The trace of an orbital adjacency counts the diagonal pairs the orbital holds. -/
theorem trace_orbitalAdj {R : Type*} [CommRing R] {X : Type*} [Fintype X] [DecidableEq X]
    (Ω : Finset (X × X)) :
    (orbitalAdj R Ω).trace = ((Ω.filter fun p => p.1 = p.2).card : R) := by
  classical
  rw [Matrix.trace]
  rw [show ∑ x, (orbitalAdj R Ω).diag x = ∑ x : X, if (x, x) ∈ Ω then (1 : R) else 0 from
    Finset.sum_congr rfl fun x _ => by rw [Matrix.diag_apply, orbitalAdj_apply]]
  rw [Finset.sum_boole]
  congr 1
  apply Finset.card_nbij' (i := fun x => (x, x)) (j := fun p => p.1)
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨hx.2, rfl⟩
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp ⊢
    have hpd : (p.1, p.1) = p := Prod.ext rfl hp.2
    exact ⟨Finset.mem_univ _, hpd ▸ hp.1⟩
  · intro x _
    rfl
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact Prod.ext rfl hp.2

/-! ## Transpose orbitals

The transpose of an orbital is an orbital: `Prod.swap` commutes with the diagonal action.
This is what the counting side of `Scheme/OrbitalOrthogonality.lean` runs on — for a
self-paired action every orbital is its own transpose (`Scheme/SelfPaired.lean`), but the
count below is true, and stated, without that hypothesis. -/

/-- The transpose of a set of ordered pairs. -/
def transposePairs {X : Type*} (Ω : Finset (X × X)) : Finset (X × X) :=
  Ω.map (Equiv.prodComm X X).toEmbedding

theorem mem_transposePairs {X : Type*} {Ω : Finset (X × X)} {p : X × X} :
    p ∈ transposePairs Ω ↔ p.swap ∈ Ω := by
  rw [transposePairs, Finset.mem_map_equiv, Equiv.prodComm_symm]
  rfl

@[simp] theorem card_transposePairs {X : Type*} (Ω : Finset (X × X)) :
    #(transposePairs Ω) = #Ω :=
  Finset.card_map _

@[simp] theorem transposePairs_transposePairs {X : Type*} (Ω : Finset (X × X)) :
    transposePairs (transposePairs Ω) = Ω := by
  ext p
  rw [mem_transposePairs, mem_transposePairs, Prod.swap_swap]

/-- `Prod.swap` commutes with the diagonal action, so it carries orbits to orbits. -/
theorem orb_swap {X : Type*} {G : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidableEq X] (p : X × X) :
    orb G (Prod.swap p) = transposePairs (orb G p) := by
  ext q
  rw [mem_transposePairs, mem_orb, mem_orb]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [show g • p = Prod.swap (g • p.swap) from rfl, hg]⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [show g • p.swap = Prod.swap (g • p) from rfl, hg, Prod.swap_swap]⟩

/-- **The transpose of an orbital is an orbital.** -/
theorem transposePairs_mem_orbits {X : Type*} {G : Type*} [Group G] [Fintype G]
    [MulAction G X] [Fintype X] [DecidableEq X] {Ω : Finset (X × X)}
    (hΩ : Ω ∈ orbits G (X × X)) : transposePairs Ω ∈ orbits G (X × X) := by
  obtain ⟨p, hp⟩ := nonempty_of_mem_orbits hΩ
  rw [show Ω = orb G p from ((mem_iff_orb_eq hΩ).mp hp).symm, ← orb_swap]
  exact orb_mem_orbits _

/-- **The transpose count**: the trace of a product of orbital adjacencies is the size of
the first orbital when the second is its transpose, and zero otherwise — orbits are equal
or disjoint. -/
theorem trace_orbitalAdj_mul_orbitalAdj {Ω Ω' : Finset (X × X)}
    (hΩ : Ω ∈ orbits G (X × X)) (hΩ' : Ω' ∈ orbits G (X × X)) :
    (orbitalAdj R Ω * orbitalAdj R Ω').trace
      = if Ω' = transposePairs Ω then (#Ω : R) else 0 := by
  classical
  have hexp : (orbitalAdj R Ω * orbitalAdj R Ω').trace
      = ∑ p : X × X, if p ∈ Ω ∧ p.swap ∈ Ω' then (1 : R) else 0 := by
    rw [Matrix.trace]
    rw [show ∑ x, (orbitalAdj R Ω * orbitalAdj R Ω').diag x
        = ∑ x, ∑ y, (if (x, y) ∈ Ω then (1 : R) else 0)
            * if (y, x) ∈ Ω' then (1 : R) else 0 from
      Finset.sum_congr rfl fun x _ => by
        rw [Matrix.diag_apply, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun y _ => by rw [orbitalAdj_apply, orbitalAdj_apply]]
    rw [show (∑ x, ∑ y, (if (x, y) ∈ Ω then (1 : R) else 0)
          * if (y, x) ∈ Ω' then (1 : R) else 0)
        = ∑ p : X × X, (if p ∈ Ω then (1 : R) else 0)
            * if p.swap ∈ Ω' then (1 : R) else 0 from
      (Fintype.sum_prod_type (f := fun p : X × X =>
        (if p ∈ Ω then (1 : R) else 0) * if p.swap ∈ Ω' then (1 : R) else 0)).symm]
    exact Finset.sum_congr rfl fun p _ => by
      by_cases h1 : p ∈ Ω <;> by_cases h2 : p.swap ∈ Ω' <;> simp [h1, h2]
  rw [hexp]
  rw [show ∑ p : X × X, (if p ∈ Ω ∧ p.swap ∈ Ω' then (1 : R) else 0)
      = ∑ p : X × X, (if p ∈ Ω ∩ transposePairs Ω' then (1 : R) else 0) from
    Finset.sum_congr rfl fun p _ => by
      simp only [Finset.mem_inter, mem_transposePairs]]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases heq : Ω' = transposePairs Ω
  · rw [if_pos heq, heq, transposePairs_transposePairs, Finset.inter_self]
  · rw [if_neg heq]
    have hdisj : Ω ∩ transposePairs Ω' = ∅ := by
      by_contra hne
      obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hne
      rw [Finset.mem_inter] at hp
      have := eq_of_mem_orbits_of_mem (transposePairs_mem_orbits hΩ') hΩ hp.2 hp.1
      exact heq (by rw [← this, transposePairs_transposePairs])
    rw [hdisj]
    simp

/-- The indicator of an orbital lies in the algebra. -/
theorem orbitalAdj_mem_orbitalAlgebra {Ω : Finset (X × X)} (hΩ : Ω ∈ orbits G (X × X)) :
    orbitalAdj R Ω ∈ orbitalAlgebra R G X := by
  rw [mem_orbitalAlgebra_iff]
  intro g x y
  have hmem : ((g • x, g • y) ∈ Ω) ↔ ((x, y) ∈ Ω) := by
    rw [mem_iff_orb_eq hΩ, mem_iff_orb_eq hΩ]
    have hprod : (g • x, g • y) = g • ((x, y) : X × X) := rfl
    rw [hprod, orb_smul]
  simp only [orbitalAdj, Matrix.of_apply, hmem]

/-- The orbital indicators are linearly independent. -/
theorem linearIndependent_orbitalAdj [Nontrivial R] :
    LinearIndependent R
      (fun Ω : ↥(orbits G (X × X)) => orbitalAdj R (Ω : Finset (X × X))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc Ω
  obtain ⟨Ω, hΩ⟩ := Ω
  obtain ⟨p, hp⟩ := nonempty_of_mem_orbits hΩ
  have h := congrFun (congrFun hc p.1) p.2
  rw [Matrix.sum_apply] at h
  have hterm : ∀ Ω' : ↥(orbits G (X × X)),
      (c Ω' • orbitalAdj R (Ω' : Finset (X × X))) p.1 p.2
        = if p ∈ (Ω' : Finset (X × X)) then c Ω' else 0 := by
    intro Ω'
    simp only [orbitalAdj, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun Ω' _ => hterm Ω'), Finset.sum_eq_single ⟨Ω, hΩ⟩] at h
  · simpa [hp] using h
  · intro Ω' _ hne
    rw [if_neg]
    intro hp'
    exact hne (Subtype.ext (eq_of_mem_orbits_of_mem Ω'.2 hΩ hp' hp))
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- The orbital indicators span the algebra. -/
theorem span_orbitalAdj_eq :
    Submodule.span R
        (Set.range (fun Ω : ↥(orbits G (X × X)) => orbitalAdj R (Ω : Finset (X × X))))
      = (orbitalAlgebra R G X).toSubmodule := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨Ω, rfl⟩
    exact orbitalAdj_mem_orbitalAlgebra Ω.2
  · intro M hM
    rw [Subalgebra.mem_toSubmodule, mem_orbitalAlgebra_iff] at hM
    have hrep : M = ∑ Ω ∈ orbits G (X × X),
        (if h : Ω.Nonempty then M h.choose.1 h.choose.2 else 0) • orbitalAdj R Ω := by
      ext x y
      rw [Matrix.sum_apply]
      have hstep : ∀ Ω ∈ orbits G (X × X),
          ((if h : Ω.Nonempty then M h.choose.1 h.choose.2 else 0) • orbitalAdj R Ω) x y
            = if (x, y) ∈ Ω then M x y else 0 := by
        intro Ω hΩ
        simp only [orbitalAdj, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        by_cases hmem : (x, y) ∈ Ω
        · rw [if_pos hmem, if_pos hmem, mul_one]
          have hne : Ω.Nonempty := nonempty_of_mem_orbits hΩ
          rw [dif_pos hne]
          have h1 : orb G ((x, y) : X × X) = Ω := (mem_iff_orb_eq hΩ).mp hmem
          have h2 : hne.choose ∈ orb G ((x, y) : X × X) := by
            rw [h1]; exact hne.choose_spec
          obtain ⟨g, hg⟩ := mem_orb.mp h2
          rw [← hg]
          exact hM g x y
        · rw [if_neg hmem, if_neg hmem, mul_zero]
      rw [Finset.sum_congr rfl hstep,
        Finset.sum_eq_single (orb G ((x, y) : X × X))]
      · rw [if_pos (self_mem_orb (H := G) ((x, y) : X × X))]
      · intro Ω hΩ hne
        rw [if_neg]
        intro hmem
        exact hne ((mem_iff_orb_eq hΩ).mp hmem).symm
      · intro hcon
        exact absurd (orb_mem_orbits (H := G) ((x, y) : X × X)) hcon
    rw [hrep]
    exact Submodule.sum_mem _ fun Ω hΩ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨Ω, hΩ⟩, rfl⟩)

/-- The orbital indicators, as a basis of the algebra. -/
noncomputable def orbitalBasis [Nontrivial R] :
    Module.Basis ↥(orbits G (X × X)) R ↥(orbitalAlgebra R G X) :=
  Module.Basis.mk
    (v := fun Ω => ⟨orbitalAdj R (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩)
    ((linearIndependent_orbitalAdj (R := R) (G := G) (X := X)).of_comp
      (orbitalAlgebra R G X).toSubmodule.subtype)
    (by
      have hmap : Submodule.map (orbitalAlgebra R G X).toSubmodule.subtype
            (Submodule.span R (Set.range fun Ω : ↥(orbits G (X × X)) =>
              (⟨orbitalAdj R (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩ :
                ↥(orbitalAlgebra R G X))))
          = Submodule.map (orbitalAlgebra R G X).toSubmodule.subtype ⊤ := by
        rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
        exact span_orbitalAdj_eq
      exact le_of_eq (Submodule.map_injective_of_injective
        (Submodule.injective_subtype _) hmap).symm)

/-- The orbital basis is definitionally the family of orbital indicators. `orbitalBasis` is a
`Module.Basis.mk`, so this is `Basis.coe_mk`; without a named form nothing downstream can
unfold a basis vector (`exact?` does not find it). -/
theorem coe_orbitalBasis [Nontrivial R] :
    ⇑(orbitalBasis (R := R) (G := G) (X := X)) = fun Ω : ↥(orbits G (X × X)) =>
      (⟨orbitalAdj R (Ω : Finset (X × X)), orbitalAdj_mem_orbitalAlgebra Ω.2⟩ :
        ↥(orbitalAlgebra R G X)) :=
  Module.Basis.coe_mk _ _

/-- The underlying matrix of an orbital basis vector is the orbital indicator. -/
theorem val_orbitalBasis [Nontrivial R] (Ω : ↥(orbits G (X × X))) :
    ((orbitalBasis (R := R) (G := G) (X := X) Ω : ↥(orbitalAlgebra R G X)) : Matrix X X R)
      = orbitalAdj R (Ω : Finset (X × X)) :=
  congrArg Subtype.val (congrFun coe_orbitalBasis Ω)

/-- **The dimension of the orbital algebra is the number of orbitals.** -/
theorem finrank_orbitalAlgebra {K : Type*} [Field K] :
    Module.finrank K (orbitalAlgebra K G X) = (orbits G (X × X)).card := by
  rw [← Subalgebra.finrank_toSubmodule, ← span_orbitalAdj_eq,
    finrank_span_eq_card linearIndependent_orbitalAdj, Fintype.card_coe]

end Orbital

end ECCLib.Scheme

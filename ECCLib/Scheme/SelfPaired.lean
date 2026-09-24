/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.CommutativeSubalgebra
import ECCLib.Scheme.Orbital

/-!
# Self-paired orbitals, and commutativity

An action is **self-paired** when every ordered pair can be swapped by a group element. That
single condition makes every member of the orbital algebra symmetric, and symmetry of every
member makes the algebra commutative — with no representation theory anywhere.

## Main definitions

* `IsSelfPaired` — every ordered pair can be swapped.
* `Subalgebra.IsCommutative` — commutativity carried as a class on a subalgebra, with the
  `CommRing` instance it entails.

## Main results

* `isSymm_of_isSelfPaired` — members of a self-paired orbital algebra are symmetric.
* `mul_comm_of_isSelfPaired` — hence the algebra is commutative.
* `isSelfPaired_of_forall_isSymm` — the converse of the first: symmetry of every member forces
  self-pairing.
* `isSelfPaired_iff_forall_isSymm` — **the two together, as the iff the literature states.**
* `forall_isSymm_congr_ring` — a corollary: symmetry of the orbital algebra is the *same*
  condition over every nontrivial commutative ring.
* `mul_comm_of_regular`, `isCommutative_of_regular` — a regular action of an abelian group has a
  commutative orbital algebra: the third supplier of commutativity, and the one that shows
  commutativity is strictly weaker than self-pairing.

## On the name

`IsSelfPaired` is exactly the classical condition **generously transitive**. Martin–Tanaka,
*Commutative association schemes* (arXiv:0811.2475), §3 p. 7, define it as: *"for any distinct
`x, y ∈ X` there is an element `g ∈ G` such that `gx = y` and `gy = x`"* — this predicate,
verbatim.

The classical definition carries no separate transitivity clause, and this predicate *implies*
transitivity anyway — take `x ≠ y` and the witness `g` sends `x` to `y`.
`IsGenerouslyTransitive` would be the canonical name.

Martin–Tanaka §3 also records what this condition buys, which is more than commutativity: it is
equivalent to the permutation representation being multiplicity-free *with every irreducible
constituent realizable over `ℝ`* — i.e. to `(G, G_x)` being a **Gelfand pair** whose scheme is
symmetric.

## The relationship is an iff, and it is with *symmetry*, not commutativity

Godsil §1.3.3 states it as an equivalence: the commutant of a permutation group is the
Bose–Mesner algebra of a **symmetric** association scheme if and only if the group is generously
transitive. `isSymm_of_isSelfPaired` is one direction; `isSelfPaired_of_forall_isSymm`
supplies the other, and needs no transitivity hypothesis — a
single orbital indicator does the work.

**The iff is false with `commutative` in place of `symmetric`, and the substitution is tempting.**
Commutativity is strictly weaker. The classical witness is the conjugacy-class scheme of a
non-abelian group (Godsil, Example 1.1.5: "our first example of a scheme that is not symmetric"),
and the nearest witness here is the regular action of a group of odd order, which is commutative
because circulants commute and is not self-paired because `2g = 0` forces `g = 0`.

**That witness is compiled at a single object.** `mul_comm_of_regular` below proves that a
regular action of an abelian group has a commutative orbital algebra, which supplies
`Subalgebra.IsCommutative (orbitalAlgebra ℂ Cyc3 Cyc3)`; beside `not_isSelfPaired_Cyc3` that is
one object, commutative and not self-paired. The pair sits in
`Scheme/OrbitalSpectrumCheck.lean`.

## What supplies commutativity, and what consumes it

Commutativity is a hypothesis of the spectral layer, never a conclusion of it. Self-pairing is
**one** sufficient condition; circulancy is another, and the translation layer uses that
one; a regular action of an abelian group is a third, proved below as `mul_comm_of_regular`. None
implies another, so they are kept apart: `Subalgebra.IsCommutative` is the interface the spectral
layer consumes, and this file supplies two ways of discharging it.

The third supplier earns its place by being a *separating* example rather than a convenience.
Self-pairing gives commutativity; commutativity does not give self-pairing, and the regular action
of an odd-order abelian group is exactly where the implication fails.

`Subalgebra.IsCommutative` and its `CommRing` instance live in
`ECCLib/CommutativeSubalgebra.lean`, the lowest layer that can state them, because
`ECCLib/Matrix/SpectralDetermination.lean` also uses them and does not import the orbital
layer.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Self-paired actions -/

section SelfPaired

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {R : Type*} [CommRing R]

/-- Every ordered pair can be swapped: each orbital is equal to its transpose. -/
def IsSelfPaired (G : Type*) [Group G] (X : Type*) [MulAction G X] : Prop :=
  ∀ x y : X, ∃ g : G, g • x = y ∧ g • y = x

/-- **For a self-paired action every orbital is its own transpose** — the specialization
under which the transpose count of `Scheme/Orbital.lean` becomes a plain diagonal. -/
theorem transposePairs_eq_self_of_isSelfPaired (hsp : IsSelfPaired G X)
    {Ω : Finset (X × X)} (hΩ : Ω ∈ orbits G (X × X)) : transposePairs Ω = Ω := by
  ext p
  rw [mem_transposePairs, mem_iff_orb_eq hΩ, mem_iff_orb_eq hΩ]
  obtain ⟨g, hg1, hg2⟩ := hsp p.1 p.2
  have hswap : g • p = p.swap := Prod.ext hg1 hg2
  rw [show orb G p.swap = orb G p from by rw [← hswap]; exact orb_smul g p]

/-- In a self-paired orbital algebra every member is symmetric. -/
theorem isSymm_of_isSelfPaired (hsp : IsSelfPaired G X) {M : Matrix X X R}
    (hM : M ∈ orbitalAlgebra R G X) : M.IsSymm := by
  rw [mem_orbitalAlgebra_iff] at hM
  ext x y
  obtain ⟨g, hg1, hg2⟩ := hsp x y
  have h := hM g x y
  rw [hg1, hg2] at h
  exact h

/-- **Self-pairing implies commutativity**, by transposing a product. No representation theory,
and no transitivity. -/
theorem mul_comm_of_isSelfPaired (hsp : IsSelfPaired G X) {M N : Matrix X X R}
    (hM : M ∈ orbitalAlgebra R G X) (hN : N ∈ orbitalAlgebra R G X) : M * N = N * M := by
  have h1 := isSymm_of_isSelfPaired (R := R) hsp (mul_mem hM hN)
  have h2 := isSymm_of_isSelfPaired (R := R) hsp hM
  have h3 := isSymm_of_isSelfPaired (R := R) hsp hN
  calc M * N = (M * N)ᵀ := h1.symm
    _ = Nᵀ * Mᵀ := Matrix.transpose_mul _ _
    _ = N * M := by rw [h2, h3]

/-- A self-paired action discharges the commutativity interface the spectral layer consumes. -/
theorem isCommutative_orbitalAlgebra_of_isSelfPaired (hsp : IsSelfPaired G X) :
    Subalgebra.IsCommutative (orbitalAlgebra R G X) :=
  ⟨fun a b => Subtype.ext (mul_comm_of_isSelfPaired hsp a.2 b.2)⟩

/-! ## The converse -/

/-- **Symmetry of every member forces self-pairing.** The orbital of `(x, y)` has a symmetric
indicator, so it contains `(y, x)`, and the group element carrying one to the other is exactly
the swap self-pairing asks for. No transitivity hypothesis is needed, and no property of the
ring beyond `1 ≠ 0`. -/
theorem isSelfPaired_of_forall_isSymm [Nontrivial R]
    (h : ∀ M : Matrix X X R, M ∈ orbitalAlgebra R G X → M.IsSymm) :
    IsSelfPaired G X := by
  classical
  intro x y
  have hsymm := h (orbitalAdj R (orb G ((x, y) : X × X)))
    (orbitalAdj_mem_orbitalAlgebra (orb_mem_orbits _))
  have hxy : orbitalAdj R (orb G ((x, y) : X × X)) x y = (1 : R) := by
    rw [orbitalAdj_apply, if_pos (self_mem_orb _)]
  have hyx : orbitalAdj R (orb G ((x, y) : X × X)) y x = (1 : R) := by
    have hT := congrFun (congrFun hsymm x) y
    rw [Matrix.transpose_apply] at hT
    exact hT.trans hxy
  have hmem : ((y, x) : X × X) ∈ orb G ((x, y) : X × X) := by
    by_contra hno
    rw [orbitalAdj_apply, if_neg hno] at hyx
    exact zero_ne_one hyx
  obtain ⟨g, hg⟩ := mem_orb.mp hmem
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

/-- **Self-pairing is exactly symmetry of the orbital algebra** (Godsil §1.3.3). Note that the
right-hand side mentions `R` and the left-hand side does not: symmetry of the orbital algebra is
the same condition over every nontrivial commutative ring, so nothing is lost by testing it over
whichever one is at hand. -/
theorem isSelfPaired_iff_forall_isSymm [Nontrivial R] :
    IsSelfPaired G X ↔ ∀ M : Matrix X X R, M ∈ orbitalAlgebra R G X → M.IsSymm :=
  ⟨fun hsp _ hM => isSymm_of_isSelfPaired hsp hM, isSelfPaired_of_forall_isSymm⟩

/-- **Symmetry of the orbital algebra does not depend on the ring.** Both sides of
`isSelfPaired_iff_forall_isSymm` are equivalent to a condition on the action alone, so the
statement transfers across any two nontrivial commutative rings. This is why testing symmetry over
whichever ring is at hand — `ℤ` in the check module, `ℂ` in the spectral layer — loses nothing. -/
theorem forall_isSymm_congr_ring {R₁ R₂ : Type*} [CommRing R₁] [Nontrivial R₁]
    [CommRing R₂] [Nontrivial R₂] :
    (∀ M : Matrix X X R₁, M ∈ orbitalAlgebra R₁ G X → M.IsSymm) ↔
      ∀ M : Matrix X X R₂, M ∈ orbitalAlgebra R₂ G X → M.IsSymm :=
  (isSelfPaired_iff_forall_isSymm (R := R₁)).symm.trans (isSelfPaired_iff_forall_isSymm (R := R₂))

end SelfPaired

/-! ## The third supplier: a regular action of an abelian group

Commutativity without self-pairing. This is what makes `isSelfPaired_iff_forall_isSymm`'s use of
`IsSymm` rather than `Subalgebra.IsCommutative` a mathematical requirement and not a preference. -/

section Regular

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
variable {R : Type*} [CommRing R]

/-- Translation invariance in circulant form: a member of the orbital algebra of a regular action
is determined by its first row. -/
theorem apply_eq_apply_one {P : Matrix G G R} (hP : P ∈ orbitalAlgebra R G G) (a b : G) :
    P a b = P 1 (a⁻¹ * b) := by
  rw [mem_orbitalAlgebra_iff] at hP
  have h := hP a⁻¹ a b
  simp only [smul_eq_mul, inv_mul_cancel] at h
  exact h.symm

/-- **A regular action of an abelian group has a commutative orbital algebra.** Members are
circulant, so products are convolutions, and the reindexing `z ↦ x * y * z⁻¹` — an involution of
`G` — exchanges the two factors. Commutativity of `G` is used exactly there. -/
theorem mul_comm_of_regular {M N : Matrix G G R}
    (hM : M ∈ orbitalAlgebra R G G) (hN : N ∈ orbitalAlgebra R G G) : M * N = N * M := by
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft (x * y))) _ _ fun z => ?_
  change M x z * N z y = N x (x * y * z⁻¹) * M (x * y * z⁻¹) y
  rw [apply_eq_apply_one hM x z, apply_eq_apply_one hN z y,
    apply_eq_apply_one hN x (x * y * z⁻¹), apply_eq_apply_one hM (x * y * z⁻¹) y]
  have e1 : x⁻¹ * (x * y * z⁻¹) = z⁻¹ * y := by
    rw [mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_comm]
  have e2 : (x * y * z⁻¹)⁻¹ * y = x⁻¹ * z := by
    rw [mul_inv, mul_inv, inv_inv, mul_assoc, mul_comm z y, ← mul_assoc, mul_assoc x⁻¹,
      inv_mul_cancel, mul_one]
  rw [e1, e2, mul_comm]

/-- ...so it discharges the spectral layer's commutativity interface, with no self-pairing. -/
theorem isCommutative_of_regular : Subalgebra.IsCommutative (orbitalAlgebra R G G) :=
  ⟨fun a b => Subtype.ext (mul_comm_of_regular a.2 b.2)⟩

end Regular

end ECCLib.Scheme

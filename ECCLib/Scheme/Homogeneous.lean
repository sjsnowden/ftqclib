/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.CoherentAlgebra
import ECCLib.Scheme.SelfPaired

/-!
# Homogeneity: when the identity is one of the orbital indicators

A coherent algebra is **homogeneous** when the identity matrix is one of its 01-basis elements.
For a permutation commutant that happens exactly when the action is transitive, because the
diagonal of `X × X` is always a union of orbitals and is a single orbital precisely then.

The substantive direction is Godsil §16.10.2: **a commutative coherent algebra is homogeneous.**
Its proof is the reason `Matrix/CoherentAlgebra.lean` had to come first — it runs entirely
through the all-ones matrix `J`, which is a coherent-algebra axiom and not a subalgebra one.

## Main results

* `eq_of_mem_diagOrbital` — the orbital of `(x, x)` consists of diagonal pairs.
* `isPretransitive_of_commute_of_one` — if the diagonal orbital's indicator commutes with `J`,
  the action is transitive.
* `isPretransitive_of_isCommutative` — **Godsil §16.10.2**: commutativity forces transitivity.
* `orbitalAdj_diag_eq_one` — under transitivity the diagonal orbital *is* the identity matrix.
* `isPretransitive_iff_exists_orbitalAdj_eq_one` — **homogeneous ⟺ transitive.**
* `isPretransitive_of_isSelfPaired` — self-pairing gives transitivity directly, needing no
  finiteness and no algebra at all.

## How the proof works, and why `J` is doing the work

Let `D` be the indicator of the orbital of `(x, x)`. Every pair in that orbital is diagonal, so
`D` has support on the diagonal only. Multiplying a diagonal matrix by the all-ones matrix reads
off a row sum on one side and a column sum on the other, and for a diagonal matrix those collapse
to single entries:

`(D * J) x y = D x x`   and   `(J * D) x y = D y y`.

So `D * J = J * D` forces `D x x = D y y`. Since `D x x = 1` by construction, `D y y = 1`, which
says `(y, y)` lies in the orbital of `(x, x)` — and the group element witnessing that carries `x`
to `y`. Transitivity.

This is shorter than the alternative route, which exhibits two orbital indicators that fail to
commute when transitivity fails. That version is kept as a compiled witness in
`Scheme/HomogeneousCheck.lean`, because an explicit non-commuting pair says something the
contrapositive does not.

## Implementation notes

`isPretransitive_of_commute_of_one` is stated on the single commuting pair rather than on the
whole algebra, so the strength actually consumed is visible: nothing about the algebra beyond
`D` and `J` commuting is used, and `Subalgebra.IsCommutative` is one way to supply that among
others.

`[Nontrivial R]` is genuinely required by everything that reads a conclusion out of a matrix
entry: over the trivial ring `1 = 0`, and no fact about orbits follows from an entry's value.

`isPretransitive_of_isSelfPaired` deliberately does **not** go through this file's machinery, even
though it could. Its statement mentions no matrix, so carrying `[Fintype X]`, `[Fintype G]` and
`[DecidableEq X]` merely to reach it through the algebra would be hypotheses the type does not
use — which is exactly what the `unusedFintypeInType` linter flags. The Godsil composition is
preserved as a compiled row in the check module instead, where it costs nothing.

## References

Godsil, *Association Schemes* (2010), §16.10 — the definition of homogeneous, Lemma 16.10.2, and
the remark that the commutant of a permutation group is homogeneous exactly when the group is
transitive.
-/

namespace ECCLib.Scheme

open Matrix Finset MulAction

section Homogeneous

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {R : Type*} [CommRing R]

omit [Fintype X] in
/-- **The diagonal orbital is diagonal.** Both coordinates of a point in the orbit of `(x, x)`
are the same translate of `x`. -/
theorem eq_of_mem_diagOrbital {x u v : X} (h : ((u, v) : X × X) ∈ orb G ((x, x) : X × X)) :
    u = v := by
  obtain ⟨g, hg⟩ := mem_orb.mp h
  exact (congrArg Prod.fst hg).symm.trans (congrArg Prod.snd hg)

omit [Fintype X] in
/-- The diagonal orbital's indicator is `1` on the diagonal entry it is built from. -/
theorem diagOrbital_apply_self (x : X) :
    orbitalAdj R (orb G ((x, x) : X × X)) x x = (1 : R) := by
  rw [orbitalAdj_apply, if_pos (self_mem_orb _)]

omit [Fintype X] in
/-- Off the diagonal the indicator vanishes. -/
theorem diagOrbital_apply_of_ne {x u v : X} (huv : u ≠ v) :
    orbitalAdj R (orb G ((x, x) : X × X)) u v = (0 : R) := by
  rw [orbitalAdj_apply, if_neg]
  exact fun h => huv (eq_of_mem_diagOrbital h)

/-- Multiplying the diagonal orbital's indicator by the all-ones matrix on the right reads off a
row sum, which for a diagonal matrix is a single entry. -/
theorem diagOrbital_mul_of_one (x u v : X) :
    (orbitalAdj R (orb G ((x, x) : X × X)) * (Matrix.of 1 : Matrix X X R)) u v
      = orbitalAdj R (orb G ((x, x) : X × X)) u u := by
  rw [Matrix.mul_apply, Finset.sum_eq_single u]
  · rw [of_one_apply, mul_one]
  · intro z _ hzu
    rw [diagOrbital_apply_of_ne (Ne.symm hzu), zero_mul]
  · intro h
    exact absurd (mem_univ u) h

/-- ...and on the left it reads off a column sum. -/
theorem of_one_mul_diagOrbital (x u v : X) :
    ((Matrix.of 1 : Matrix X X R) * orbitalAdj R (orb G ((x, x) : X × X))) u v
      = orbitalAdj R (orb G ((x, x) : X × X)) v v := by
  rw [Matrix.mul_apply, Finset.sum_eq_single v]
  · rw [of_one_apply, one_mul]
  · intro z _ hzv
    rw [diagOrbital_apply_of_ne hzv, mul_zero]
  · intro h
    exact absurd (mem_univ v) h

/-- **The engine of Godsil 16.10.2**, stated on the single commuting pair that is actually used:
if the diagonal orbital's indicator commutes with the all-ones matrix, the action is transitive. -/
theorem isPretransitive_of_commute_of_one [Nontrivial R]
    (h : ∀ x : X, orbitalAdj R (orb G ((x, x) : X × X)) * (Matrix.of 1 : Matrix X X R)
      = (Matrix.of 1 : Matrix X X R) * orbitalAdj R (orb G ((x, x) : X × X))) :
    IsPretransitive G X := by
  refine ⟨fun x y => ?_⟩
  have hrow := diagOrbital_mul_of_one (R := R) (G := G) x x y
  have hcol := of_one_mul_diagOrbital (R := R) (G := G) x x y
  have hyy : orbitalAdj R (orb G ((x, x) : X × X)) y y = (1 : R) := by
    rw [← hcol, ← h x, hrow, diagOrbital_apply_self]
  have hmem : ((y, y) : X × X) ∈ orb G ((x, x) : X × X) := by
    by_contra hno
    rw [orbitalAdj_apply, if_neg hno] at hyy
    exact zero_ne_one hyy
  obtain ⟨g, hg⟩ := mem_orb.mp hmem
  exact ⟨g, congrArg Prod.fst hg⟩

/-- **Godsil 16.10.2: a commutative coherent algebra is homogeneous.** Here in the form the
library can use — commutativity of the orbital algebra forces the action to be transitive.
Note that the only commuting pair consumed is the diagonal orbital against `J`. -/
theorem isPretransitive_of_isCommutative [Nontrivial R]
    (h : Subalgebra.IsCommutative (orbitalAlgebra R G X)) :
    IsPretransitive G X := by
  refine isPretransitive_of_commute_of_one (R := R) fun x => ?_
  have hD : orbitalAdj R (orb G ((x, x) : X × X)) ∈ orbitalAlgebra R G X :=
    orbitalAdj_mem_orbitalAlgebra (orb_mem_orbits _)
  have hJ : (Matrix.of 1 : Matrix X X R) ∈ orbitalAlgebra R G X :=
    of_one_mem_permCommutant _
  exact congrArg Subtype.val (h.mul_comm' ⟨_, hD⟩ ⟨_, hJ⟩)

omit [Fintype X] [DecidableEq X] [Fintype G] in
/-- **Self-pairing gives transitivity**, and the swapping element is already the witness: no
algebra, no ring, no finiteness.

Godsil reaches the same conclusion by composition — self-paired forces commutativity, and
commutativity forces homogeneity by 16.10.2 — and that composition is compiled in
`Scheme/HomogeneousCheck.lean`. It is *not* used here, because routing a one-line fact through
the whole coherent-algebra layer would import hypotheses the statement does not need, which the
`unusedFintypeInType` and `unusedDecidableInType` linters correctly object to. -/
theorem isPretransitive_of_isSelfPaired (hsp : IsSelfPaired G X) : IsPretransitive G X :=
  ⟨fun x y => (hsp x y).imp fun _ h => h.1⟩

/-! ## The converse, and the iff -/

omit [Fintype X] in
/-- Under transitivity the diagonal orbital gives the identity matrix — the action is
**homogeneous**. -/
theorem orbitalAdj_diag_eq_one [IsPretransitive G X] (x : X) :
    orbitalAdj R (orb G ((x, x) : X × X)) = (1 : Matrix X X R) := by
  ext u v
  rw [Matrix.one_apply, orbitalAdj_apply]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · exact fun h => eq_of_mem_diagOrbital h
  · rintro rfl
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x u
    exact mem_orb.mpr ⟨g, by rw [Prod.ext_iff]; exact ⟨hg, hg⟩⟩

/-- If any orbital's indicator is the identity matrix, the action is transitive: that orbital must
be the whole diagonal, and a single orbit containing every `(x, x)` carries `x` to `y`. -/
theorem isPretransitive_of_orbitalAdj_eq_one [Nontrivial R] {Ω : Finset (X × X)}
    (hΩ : Ω ∈ orbits G (X × X)) (h : orbitalAdj R Ω = (1 : Matrix X X R)) :
    IsPretransitive G X := by
  have hdiag : ∀ z : X, ((z, z) : X × X) ∈ Ω := by
    intro z
    by_contra hno
    have : orbitalAdj R Ω z z = (0 : R) := by rw [orbitalAdj_apply, if_neg hno]
    rw [h, Matrix.one_apply_eq] at this
    exact zero_ne_one this.symm
  refine ⟨fun x y => ?_⟩
  have hx : orb G ((x, x) : X × X) = Ω := (mem_iff_orb_eq hΩ).mp (hdiag x)
  have hyy : ((y, y) : X × X) ∈ orb G ((x, x) : X × X) := by
    rw [hx]; exact hdiag y
  obtain ⟨g, hg⟩ := mem_orb.mp hyy
  exact ⟨g, congrArg Prod.fst hg⟩

/-- **Homogeneous ⟺ transitive.** The commutant of a permutation group has the identity among its
orbital indicators exactly when the group is transitive. -/
theorem isPretransitive_iff_exists_orbitalAdj_eq_one [Nonempty X] [Nontrivial R] :
    IsPretransitive G X ↔
      ∃ Ω ∈ orbits G (X × X), orbitalAdj R Ω = (1 : Matrix X X R) := by
  constructor
  · intro hpt
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨orb G ((x, x) : X × X), orb_mem_orbits _, orbitalAdj_diag_eq_one x⟩
  · rintro ⟨Ω, hΩ, h⟩
    exact isPretransitive_of_orbitalAdj_eq_one (R := R) hΩ h

end Homogeneous

end ECCLib.Scheme

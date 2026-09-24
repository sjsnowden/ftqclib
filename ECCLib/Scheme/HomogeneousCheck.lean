/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.Homogeneous

/-!
# Checks for `ECCLib/Scheme/Homogeneous.lean`

Axiom sweeps, the Godsil composition that `Homogeneous.lean` deliberately does not use, and the
**alternative proof of 16.10.2** — an explicit pair of orbital indicators that fail to commute
when transitivity fails. The contrapositive form says only that *something* fails to commute;
the pair says which two, and that is worth compiling.
-/

namespace ECCLib.Scheme

open Matrix Finset MulAction

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.eq_of_mem_diagOrbital' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eq_of_mem_diagOrbital

/-- info: 'ECCLib.Scheme.diagOrbital_apply_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.diagOrbital_apply_self

/-- info: 'ECCLib.Scheme.diagOrbital_apply_of_ne' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.diagOrbital_apply_of_ne

/-- info: 'ECCLib.Scheme.diagOrbital_mul_of_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.diagOrbital_mul_of_one

/-- info: 'ECCLib.Scheme.of_one_mul_diagOrbital' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.of_one_mul_diagOrbital

/-- info: 'ECCLib.Scheme.isPretransitive_of_commute_of_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isPretransitive_of_commute_of_one

/-- info: 'ECCLib.Scheme.isPretransitive_of_isCommutative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isPretransitive_of_isCommutative

/-! **Axiom-free.** `isPretransitive_of_isSelfPaired` takes the swapping element as the witness
directly; it uses no choice, no propext, and no quotient. This is the compiled form of why routing
it through the coherent-algebra layer was the wrong shape — that route would have imported
`Classical.choice` along with the finiteness the linters objected to. -/
/-- info: 'ECCLib.Scheme.isPretransitive_of_isSelfPaired' does not depend on any axioms -/
#guard_msgs in
#print axioms ECCLib.Scheme.isPretransitive_of_isSelfPaired

/-- info: 'ECCLib.Scheme.orbitalAdj_diag_eq_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbitalAdj_diag_eq_one

/-- info: 'ECCLib.Scheme.isPretransitive_of_orbitalAdj_eq_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isPretransitive_of_orbitalAdj_eq_one

/-- info: 'ECCLib.Scheme.isPretransitive_iff_exists_orbitalAdj_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isPretransitive_iff_exists_orbitalAdj_eq_one

section Alternative

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]
variable {R : Type*} [CommRing R]

/-! ## The Godsil composition, compiled but not depended on

`Homogeneous.lean` proves `isPretransitive_of_isSelfPaired` in one line from the swapping element,
because routing it through the algebra would carry finiteness hypotheses the statement does not
use. The composition the literature actually performs — self-paired forces commutativity, and
commutativity forces homogeneity — is nonetheless available, and agrees. -/

example [Nontrivial R] (hsp : IsSelfPaired G X) : IsPretransitive G X :=
  isPretransitive_of_isCommutative (R := R) (isCommutative_orbitalAlgebra_of_isSelfPaired hsp)

/-! ## The alternative proof of 16.10.2, with the witnesses named

If `y` lies outside the orbit of `x`, the diagonal orbital of `x` and the orbital of `(x, y)` do
not commute: their products differ at the single entry `(x, y)`, taking the values `1` and `0`.
`Homogeneous.lean` proves transitivity through `J` instead, which is shorter; this version is
kept because it exhibits the failure rather than deducing it. -/

omit [Fintype X] in
/-- A point outside the orbit of `x` has its diagonal pair outside the diagonal orbital of `x`. -/
theorem diagPair_not_mem_diagOrbital {x y : X} (hy : y ∉ orb G x) :
    ((y, y) : X × X) ∉ orb G ((x, x) : X × X) := by
  intro h
  obtain ⟨g, hg⟩ := mem_orb.mp h
  exact hy (mem_orb.mpr ⟨g, congrArg Prod.fst hg⟩)

/-- **Two orbital indicators that fail to commute when transitivity fails.** -/
theorem exists_not_commute_of_not_mem_orb [Nontrivial R] {x y : X} (hy : y ∉ orb G x) :
    ∃ A B : Matrix X X R, A ∈ orbitalAlgebra R G X ∧ B ∈ orbitalAlgebra R G X ∧
      A * B ≠ B * A := by
  classical
  refine ⟨orbitalAdj R (orb G ((x, x) : X × X)), orbitalAdj R (orb G ((x, y) : X × X)),
    orbitalAdj_mem_orbitalAlgebra (orb_mem_orbits _),
    orbitalAdj_mem_orbitalAlgebra (orb_mem_orbits _), ?_⟩
  intro hcomm
  have hAB : (orbitalAdj R (orb G ((x, x) : X × X)) *
      orbitalAdj R (orb G ((x, y) : X × X))) x y = (1 : R) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [diagOrbital_apply_self, orbitalAdj_apply, if_pos (self_mem_orb _), one_mul]
    · intro z _ hzx
      rw [diagOrbital_apply_of_ne (Ne.symm hzx), zero_mul]
    · intro h
      exact absurd (mem_univ x) h
  have hBA : (orbitalAdj R (orb G ((x, y) : X × X)) *
      orbitalAdj R (orb G ((x, x) : X × X))) x y = (0 : R) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rcases eq_or_ne z y with rfl | hzy
    · rw [orbitalAdj_apply (R := R) (orb G ((x, x) : X × X)) z z,
        if_neg (diagPair_not_mem_diagOrbital hy), mul_zero]
    · rw [diagOrbital_apply_of_ne hzy, mul_zero]
  rw [hcomm, hBA] at hAB
  exact zero_ne_one hAB

/-- ...and hence the same conclusion as `isPretransitive_of_isCommutative`, by the other route. -/
theorem isPretransitive_of_isCommutative' [Nontrivial R]
    (h : ∀ M N : Matrix X X R, M ∈ orbitalAlgebra R G X → N ∈ orbitalAlgebra R G X →
      M * N = N * M) :
    IsPretransitive G X := by
  refine ⟨fun x y => ?_⟩
  by_contra hno
  obtain ⟨A, B, hA, hB, hne⟩ :=
    exists_not_commute_of_not_mem_orb (R := R) (fun hmem => hno (mem_orb.mp hmem))
  exact hne (h A B hA hB)

end Alternative

/-! ## Why the iff next door is stated with symmetry, not commutativity

The iff in `Scheme/SelfPaired.lean` uses **symmetry**, and that is a mathematical requirement:
commutativity is strictly weaker. The separating example is
`commutative_not_isSelfPaired_Cyc3` in `Scheme/OrbitalSpectrumCheck.lean` — the regular action of
`ZMod 3`, whose orbital algebra is commutative by `mul_comm_of_regular` and which is not
self-paired because `2g = 0` forces `g = 0`. Both halves of that example concern the same
group. -/

end ECCLib.Scheme

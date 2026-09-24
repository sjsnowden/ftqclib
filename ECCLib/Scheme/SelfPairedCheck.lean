/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.SelfPaired
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance rows for self-pairing

Axiom sweeps, and the rows showing that self-pairing implies commutativity over an arbitrary
commutative ring — not merely over `ℂ`, where the spectral tier lives.
-/

namespace ECCLib.Scheme

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.Scheme.isSymm_of_isSelfPaired' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isSymm_of_isSelfPaired

/-- info: 'ECCLib.Scheme.mul_comm_of_isSelfPaired' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mul_comm_of_isSelfPaired

/-- info: 'ECCLib.Scheme.isCommutative_orbitalAlgebra_of_isSelfPaired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCommutative_orbitalAlgebra_of_isSelfPaired

/-- info: 'ECCLib.Scheme.isSelfPaired_of_forall_isSymm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isSelfPaired_of_forall_isSymm

/-- info: 'ECCLib.Scheme.isSelfPaired_iff_forall_isSymm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isSelfPaired_iff_forall_isSymm

/-- info: 'ECCLib.Scheme.forall_isSymm_congr_ring' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.forall_isSymm_congr_ring

/-- info: 'ECCLib.Scheme.apply_eq_apply_one' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.apply_eq_apply_one

/-- info: 'ECCLib.Scheme.mul_comm_of_regular' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mul_comm_of_regular

/-- info: 'ECCLib.Scheme.isCommutative_of_regular' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.isCommutative_of_regular

/-! ## The iff, and the strengthening that is FALSE

`isSelfPaired_iff_forall_isSymm` is stated with `IsSymm`. Replacing that with
`Subalgebra.IsCommutative` gives a statement that does not hold: commutativity is strictly
weaker. The classical witness is the conjugacy-class scheme of a non-abelian group; the nearest
one here is the regular action of a group of odd order.

The separating example is compiled — `commutative_not_isSelfPaired_Cyc3` in
`Scheme/OrbitalSpectrumCheck.lean` — so this is a proved distinction, not a cautionary remark.

These rows exercise the iff in both directions over a ring the spectral tier cannot use, which
pins that neither half needs `ℂ`, and `forall_isSymm_congr_ring` says that choice never
mattered. -/

section Iff

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]

/-- The forward half over `ℤ`. Named so the module owns a declaration. -/
theorem isSymm_of_isSelfPaired_int (hsp : IsSelfPaired G X) {M : Matrix X X ℤ}
    (hM : M ∈ orbitalAlgebra ℤ G X) : M.IsSymm :=
  (isSelfPaired_iff_forall_isSymm (R := ℤ)).mp hsp M hM

/-- ...and the converse half over the same ring. -/
example (h : ∀ M : Matrix X X ℤ, M ∈ orbitalAlgebra ℤ G X → M.IsSymm) : IsSelfPaired G X :=
  (isSelfPaired_iff_forall_isSymm (R := ℤ)).mpr h

/-- **The ring-independence corollary**: symmetry over `ℤ` and over `ℂ` are the same condition,
with no route through `IsSelfPaired` written by hand. -/
example : (∀ M : Matrix X X ℤ, M ∈ orbitalAlgebra ℤ G X → M.IsSymm) ↔
    ∀ M : Matrix X X ℂ, M ∈ orbitalAlgebra ℂ G X → M.IsSymm :=
  forall_isSymm_congr_ring

/-- ...and it transfers to a ring with zero divisors too, which the spectral tier cannot use. -/
example : (∀ M : Matrix X X ℤ, M ∈ orbitalAlgebra ℤ G X → M.IsSymm) ↔
    ∀ M : Matrix X X (ZMod 6), M ∈ orbitalAlgebra (ZMod 6) G X → M.IsSymm := by
  haveI : Fact (1 < 6) := ⟨by norm_num⟩
  exact forall_isSymm_congr_ring

end Iff

/-! ## Discriminating rows: commutativity from self-pairing is ring-generic

The spectral tier needs `ℂ`, but the *route to commutativity* does not. These rows exercise it
over rings the spectral tier cannot use, which is what makes `Subalgebra.IsCommutative` worth
having as an interface rather than an `ℂ`-only conclusion. -/

section Generic

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {G : Type*} [Group G] [Fintype G] [MulAction G X]

/-- Over `ZMod 2`. -/
example (hsp : IsSelfPaired G X) {M N : Matrix X X (ZMod 2)}
    (hM : M ∈ orbitalAlgebra (ZMod 2) G X) (hN : N ∈ orbitalAlgebra (ZMod 2) G X) :
    M * N = N * M :=
  mul_comm_of_isSelfPaired hsp hM hN

/-- Over `ℤ`, which is not a field. -/
example (hsp : IsSelfPaired G X) {M N : Matrix X X ℤ}
    (hM : M ∈ orbitalAlgebra ℤ G X) (hN : N ∈ orbitalAlgebra ℤ G X) : M * N = N * M :=
  mul_comm_of_isSelfPaired hsp hM hN

/-- ...and the commutativity interface is discharged at the same generality. -/
example (hsp : IsSelfPaired G X) : Subalgebra.IsCommutative (orbitalAlgebra (ZMod 2) G X) :=
  isCommutative_orbitalAlgebra_of_isSelfPaired hsp

/-- The symmetry that drives it, also ring-generic. -/
example (hsp : IsSelfPaired G X) {M : Matrix X X ℤ} (hM : M ∈ orbitalAlgebra ℤ G X) :
    M.IsSymm :=
  isSymm_of_isSelfPaired hsp hM

end Generic

/-! ## The hypothesis is satisfiable, and by the case that matters

The **full symmetric group** acting on any type is self-paired, because a transposition swaps its
two points. That is not a curiosity: it is the reason Johnson-type schemes are commutative, and it
is what `Scheme/Johnson.lean` discharges concretely. -/

open scoped Classical in
theorem isSelfPaired_perm {X : Type*} : IsSelfPaired (Equiv.Perm X) X :=
  fun x y => ⟨Equiv.swap x y, Equiv.swap_apply_left x y, Equiv.swap_apply_right x y⟩

end ECCLib.Scheme

/-- info: 'ECCLib.Scheme.transposePairs_eq_self_of_isSelfPaired' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.transposePairs_eq_self_of_isSelfPaired

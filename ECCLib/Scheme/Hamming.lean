/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitCount
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Data.ZMod.Basic

/-!
# The Hamming scheme's orbits

The orbit classification for wreath-type symmetry: with a group `G` acting on the alphabet
`A` by additive automorphisms and TRANSITIVELY on `A ∖ {0}` (`TransOnNonzero G A`), two words
have the same Hamming weight iff a monomial map — a coordinate permutation followed by
coordinatewise `G`-scalings — carries one to the other (`hammingNorm_eq_iff_monomial`; the
generic form of the library's field-case `Coding.hammingNorm_eq_iff_monomial`). Packaged:
the monomial group `monomialSubgroup ι A G : Subgroup (AddAut (ι → A))` (the closure of the
scalings and the permutations — no new group instances) preserves weight
(`hammingNorm_monomial`), and its orbits on `ι → A` ARE the weight shells
(`orbit_eq_shell`, `orb_eq_shell`).

Two boundary facts, both machine-checked:
* **The `ZMod 4` obstruction**: `Pi.single i 1` and
  `Pi.single i 2` have equal weight but NO additive automorphism of `(ZMod 4)^ι` carries one
  to the other (`2 • single i 2 = 0 ≠ 2 • single i 1`) — so for every `ι` and every group of
  additive automorphisms the weight shells are NOT orbits (`no_transitive_group`). Transitivity
  on the nonzero alphabet forces the alphabet elementary abelian; cf. Mathlib's
  `ZMod.AddAutEquivUnits : AddAut (ZMod n) ≃* (ZMod n)ˣ`.
* **The Klein coincidence (the Pauli case)**: for the Pauli alphabet
  `ZMod 2 × ZMod 2`, the FULL automorphism group (`AddAut (ZMod 2 × ZMod 2) = GL(2,𝔽₂) =
  Sp(2,𝔽₂) ≅ S₃`, the single-qubit Clifford group mod Pauli) IS transitive on the three
  nonzero elements (`klein_transOnNonzero`, by three explicit automorphisms), so the Pauli
  weight shells are exactly the orbits of the local-symplectic wreath group
  (`klein_orbit_eq_shell`).

No Delsarte import (the bridge lives in `Scheme/DelsarteBridge.lean`); the generic orbit
classification does not import `MacWilliams.lean`.
-/

namespace ECCLib.Scheme

open Finset

/-! ## The core classification, group-free packaging -/

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [DecidableEq A]
variable {G : Type*} [Group G] [DistribMulAction G A]

omit [DecidableEq ι] in
open Classical in
/-- **The converse direction**: equal Hamming weight forces a monomial map. Generalises the
library's `Coding.exists_monomial_of_hammingNorm_eq` (`F^×` on a field) to any group
acting transitively on the nonzero alphabet; the support-matching skeleton
(`Fintype.equivOfCardEq` + `Equiv.subtypeCongr`) is the same, the value-fixing step is the
transitivity hypothesis. -/
theorem exists_monomial_of_hammingNorm_eq (htrans : TransOnNonzero G A)
    {x y : ι → A} (h : hammingNorm x = hammingNorm y) :
    ∃ (σ : Equiv.Perm ι) (d : ι → G), y = fun i => d i • x (σ i) := by
  have hcard : Fintype.card {i // y i ≠ 0} = Fintype.card {i // x i ≠ 0} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h.symm
  have hcardc : Fintype.card {i // ¬ y i ≠ 0} = Fintype.card {i // ¬ x i ≠ 0} := by
    have h1 : Fintype.card {i // ¬ y i ≠ 0}
        = Fintype.card ι - Fintype.card {i // y i ≠ 0} := Fintype.card_subtype_compl _
    have h2 : Fintype.card {i // ¬ x i ≠ 0}
        = Fintype.card ι - Fintype.card {i // x i ≠ 0} := Fintype.card_subtype_compl _
    rw [h1, h2, hcard]
  let e₁ : {i // y i ≠ 0} ≃ {i // x i ≠ 0} := Fintype.equivOfCardEq hcard
  let e₂ : {i // ¬ y i ≠ 0} ≃ {i // ¬ x i ≠ 0} := Fintype.equivOfCardEq hcardc
  let σ : Equiv.Perm ι := Equiv.subtypeCongr e₁ e₂
  have hpos : ∀ i, y i ≠ 0 → x (σ i) ≠ 0 := by
    intro i hi
    have hσ : σ i = (e₁ ⟨i, hi⟩ : ι) := by
      change (Equiv.sumCompl fun j => x j ≠ 0)
        ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl fun j => y j ≠ 0).symm i)) = _
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun j => y j ≠ 0) (a := i) hi]
      rfl
    rw [hσ]
    exact (e₁ ⟨i, hi⟩).2
  have hneg : ∀ i, y i = 0 → x (σ i) = 0 := by
    intro i hi
    have hni : ¬ y i ≠ 0 := by simpa using hi
    have hσ : σ i = (e₂ ⟨i, hni⟩ : ι) := by
      change (Equiv.sumCompl fun j => x j ≠ 0)
        ((Equiv.sumCongr e₁ e₂) ((Equiv.sumCompl fun j => y j ≠ 0).symm i)) = _
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun j => y j ≠ 0) (a := i) hni]
      rfl
    rw [hσ]
    have h2 := (e₂ ⟨i, hni⟩).2
    simpa using h2
  have key : ∀ i, ∃ g : G, g • x (σ i) = y i := by
    intro i
    by_cases hi : y i = 0
    · exact ⟨1, by rw [one_smul, hneg i hi, hi]⟩
    · exact htrans _ _ (hpos i hi) hi
  choose d hd using key
  exact ⟨σ, d, funext fun i => (hd i).symm⟩

omit [DecidableEq ι] in
/-- **The orbit classification**: under transitivity, the monomial relation is exactly equality
of Hamming weight. -/
theorem hammingNorm_eq_iff_monomial (htrans : TransOnNonzero G A) {x y : ι → A} :
    hammingNorm x = hammingNorm y ↔
      ∃ (σ : Equiv.Perm ι) (d : ι → G), y = fun i => d i • x (σ i) := by
  constructor
  · exact exists_monomial_of_hammingNorm_eq htrans
  · rintro ⟨σ, d, rfl⟩
    have hd : hammingNorm (fun i => d i • x (σ i)) = hammingNorm (fun i => x (σ i)) := by
      unfold hammingNorm
      congr 1
      refine Finset.filter_congr fun i _ => ?_
      simp [smul_eq_zero_iff_eq]
    rw [hd]
    unfold hammingNorm
    refine (Finset.card_bij' (fun i _ => σ i) (fun j _ => σ.symm j) ?_ ?_ ?_ ?_).symm
    · intro i hi
      simpa using hi
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      simpa using hj
    · intro i _
      simp
    · intro j _
      simp

end Core

/-! ## The monomial group as a subgroup of the word automorphisms -/

section Monomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [DecidableEq A]
variable {G : Type*} [Group G] [DistribMulAction G A]

/-- Coordinatewise scaling by a tuple of symmetries. -/
def scaleAut (g : ι → G) : AddAut (ι → A) :=
  AddEquiv.piCongrRight (fun i => DistribMulAction.toAddEquiv A (g i))

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] in
@[simp] theorem scaleAut_apply (g : ι → G) (v : ι → A) (i : ι) :
    scaleAut g v i = g i • v i := rfl

/-- Coordinate permutation. -/
def permAut (σ : Equiv.Perm ι) : AddAut (ι → A) where
  toFun v := fun i => v (σ i)
  invFun v := fun i => v (σ.symm i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' _ _ := rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] in
@[simp] theorem permAut_apply (σ : Equiv.Perm ι) (v : ι → A) (i : ι) :
    permAut σ v i = v (σ i) := rfl

/-- **The monomial group**: the subgroup of `AddAut (ι → A)` generated by the coordinatewise
scalings and the coordinate permutations. -/
def monomialSubgroup (ι A G : Type*) [Fintype ι] [DecidableEq ι] [AddCommGroup A]
    [Group G] [DistribMulAction G A] : Subgroup (AddAut (ι → A)) :=
  Subgroup.closure ({φ | ∃ g : ι → G, φ = scaleAut (A := A) g}
    ∪ {φ | ∃ σ : Equiv.Perm ι, φ = permAut (A := A) σ})

omit [DecidableEq A] in
theorem scaleAut_mem (g : ι → G) : scaleAut (A := A) g ∈ monomialSubgroup ι A G :=
  Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)

omit [DecidableEq A] in
theorem permAut_mem (σ : Equiv.Perm ι) : permAut (A := A) σ ∈ monomialSubgroup ι A G :=
  Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩)

omit [DecidableEq ι] in
theorem hammingNorm_scaleAut (g : ι → G) (v : ι → A) :
    hammingNorm (scaleAut (A := A) g v) = hammingNorm v := by
  unfold hammingNorm
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only [scaleAut_apply, ne_eq, smul_eq_zero_iff_eq]

omit [DecidableEq ι] in
theorem hammingNorm_permAut (σ : Equiv.Perm ι) (v : ι → A) :
    hammingNorm (permAut (A := A) σ v) = hammingNorm v := by
  unfold hammingNorm
  refine Finset.card_bij' (fun i _ => σ i) (fun j _ => σ.symm j) ?_ ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, permAut_apply] at hj ⊢
    simpa using hj
  · intro i _
    simp
  · intro j _
    simp

/-- **Forward direction**: the whole monomial group preserves the weight. -/
theorem hammingNorm_monomial {φ : AddAut (ι → A)}
    (hφ : φ ∈ monomialSubgroup ι A G) (v : ι → A) :
    hammingNorm (φ v) = hammingNorm v := by
  induction hφ using Subgroup.closure_induction generalizing v with
  | mem x hx =>
      rcases hx with ⟨g, rfl⟩ | ⟨σ, rfl⟩
      · exact hammingNorm_scaleAut g v
      · exact hammingNorm_permAut σ v
  | one => rfl
  | mul x y _ _ ihx ihy => rw [show (x * y) v = x (y v) from rfl, ihx, ihy]
  | inv x hx ihx =>
      have h := ihx (x⁻¹ v)
      rw [show x (x⁻¹ v) = v from by
        change (x * x⁻¹) v = v
        rw [mul_inv_cancel]
        rfl] at h
      exact h.symm

/-- **Packaged converse**: under transitivity, equal weight is witnessed by an element of
the monomial group. -/
theorem exists_mem_monomialSubgroup_of_hammingNorm_eq (htrans : TransOnNonzero G A)
    {x y : ι → A} (h : hammingNorm x = hammingNorm y) :
    ∃ φ ∈ monomialSubgroup ι A G, φ x = y := by
  obtain ⟨σ, d, hy⟩ := exists_monomial_of_hammingNorm_eq (G := G) htrans h
  refine ⟨scaleAut d * permAut σ, Subgroup.mul_mem _ (scaleAut_mem d) (permAut_mem σ), ?_⟩
  rw [hy]
  rfl

/-- **The classification as an orbit statement**: the orbits of the monomial group on the word
space are the Hamming weight shells. -/
theorem orbit_eq_shell (htrans : TransOnNonzero G A) (x y : ι → A) :
    y ∈ MulAction.orbit (↥(monomialSubgroup ι A G)) x ↔ hammingNorm y = hammingNorm x := by
  constructor
  · rintro ⟨⟨φ, hφ⟩, rfl⟩
    exact hammingNorm_monomial hφ x
  · intro h
    obtain ⟨φ, hφ, hx⟩ := exists_mem_monomialSubgroup_of_hammingNorm_eq htrans h.symm
    exact ⟨⟨φ, hφ⟩, hx⟩

variable [Fintype A]

/-- The monomial group is finite (a subgroup of the automorphisms of a finite group). -/
noncomputable instance : Fintype ↥(monomialSubgroup ι A G) := Fintype.ofFinite _

/-- **In the scheme layer's vocabulary**: the orbit `Finset` of a word is its weight shell. -/
theorem orb_eq_shell (htrans : TransOnNonzero G A) (x : ι → A) :
    orb (↥(monomialSubgroup ι A G)) x
      = Finset.univ.filter (fun y => hammingNorm y = hammingNorm x) := by
  ext y
  rw [mem_orb, Finset.mem_filter, ← orbit_eq_shell htrans x y, MulAction.mem_orbit_iff]
  simp only [Finset.mem_univ, true_and]

end Monomial

/-! ## The `ZMod 4` obstruction -/

section ZMod4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem single_two_add_self (i : ι) :
    (Pi.single i (2 : ZMod 4) + Pi.single i (2 : ZMod 4) : ι → ZMod 4) = 0 := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply]
    decide
  · simp [Pi.single_eq_of_ne hj]

omit [Fintype ι] in
theorem single_one_add_self_ne (i : ι) :
    (Pi.single i (1 : ZMod 4) + Pi.single i (1 : ZMod 4) : ι → ZMod 4) ≠ 0 := by
  intro h
  have := congrFun h i
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this
  exact absurd this (by decide)

theorem hammingNorm_single_one (i : ι) :
    hammingNorm (Pi.single i (1 : ZMod 4) : ι → ZMod 4) = 1 := by
  rw [hammingNorm]
  have hfilt : (Finset.univ.filter
      fun j => (Pi.single i (1 : ZMod 4) : ι → ZMod 4) j ≠ 0) = {i} := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [ne_eq, mem_filter, mem_univ, Pi.single_eq_same, true_and, mem_singleton, iff_true]
      decide
    · simp [hj]
  rw [hfilt]
  simp

theorem hammingNorm_single_two (i : ι) :
    hammingNorm (Pi.single i (2 : ZMod 4) : ι → ZMod 4) = 1 := by
  rw [hammingNorm]
  have hfilt : (Finset.univ.filter
      fun j => (Pi.single i (2 : ZMod 4) : ι → ZMod 4) j ≠ 0) = {i} := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [ne_eq, mem_filter, mem_univ, Pi.single_eq_same, true_and, mem_singleton, iff_true]
      decide
    · simp [hj]
  rw [hfilt]
  simp

/-- **The sharp obstruction.** `Pi.single i 1` and `Pi.single i 2` both have weight `1` in
`(ZMod 4)^ι`, yet NO additive automorphism carries one to the other (`2 • single i 2 = 0`
while `2 • single i 1 ≠ 0`). -/
theorem weight_one_shell_not_an_orbit (i : ι) (f : (ι → ZMod 4) ≃+ (ι → ZMod 4)) :
    hammingNorm (Pi.single i (1 : ZMod 4) : ι → ZMod 4)
        = hammingNorm (Pi.single i (2 : ZMod 4) : ι → ZMod 4)
      ∧ f (Pi.single i (1 : ZMod 4)) ≠ Pi.single i (2 : ZMod 4) := by
  refine ⟨by rw [hammingNorm_single_one, hammingNorm_single_two], ?_⟩
  intro h
  have hsum : f (Pi.single i (1 : ZMod 4) + Pi.single i (1 : ZMod 4))
      = Pi.single i (2 : ZMod 4) + Pi.single i (2 : ZMod 4) := by
    rw [map_add, h]
  rw [single_two_add_self, ← map_zero f] at hsum
  exact single_one_add_self_ne i (f.injective hsum)

omit [DecidableEq ι] in
/-- For EVERY `ι` and EVERY group of additive automorphisms of `(ZMod 4)^ι`, the weight
shells are not orbits: "equal weight ⟹ some `h` carries `x` to `y`" is FALSE. The
alphabet `ZMod 4` is not elementary abelian, and no transitive `G` exists
(`ZMod.AddAutEquivUnits`: its automorphisms are `{±1}`). -/
theorem no_transitive_group (i : ι) (H : Type*) [Group H]
    [DistribMulAction H (ι → ZMod 4)] :
    ¬ (∀ x y : ι → ZMod 4, hammingNorm x = hammingNorm y → ∃ h : H, h • x = y) := by
  classical
  intro hall
  obtain ⟨h, hh⟩ := hall (Pi.single i 1) (Pi.single i 2)
    ((weight_one_shell_not_an_orbit i (AddEquiv.refl _)).1)
  exact (weight_one_shell_not_an_orbit i (DistribMulAction.toAddEquiv _ h)).2 hh

end ZMod4

/-! ## The Klein coincidence: the Pauli case -/

section Klein

/-- The shear `(a, b) ↦ (a, a + b)` of the Klein group (self-inverse). -/
def kleinShearL : AddAut (ZMod 2 × ZMod 2) where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.1 + p.2)
  left_inv p := by
    revert p
    decide
  right_inv p := by
    revert p
    decide
  map_add' x y := by
    revert x y
    decide

/-- The shear `(a, b) ↦ (a + b, b)` of the Klein group (self-inverse). -/
def kleinShearR : AddAut (ZMod 2 × ZMod 2) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by
    revert p
    decide
  right_inv p := by
    revert p
    decide
  map_add' x y := by
    revert x y
    decide

/-- The coordinate swap of the Klein group. -/
def kleinSwap : AddAut (ZMod 2 × ZMod 2) := AddEquiv.prodComm

/-- Four explicit automorphisms (the identity and the three transpositions of the nonzero
elements) already move any nonzero element to any other — kernel-decided. -/
theorem klein_list_trans : ∀ a b : ZMod 2 × ZMod 2, a ≠ 0 → b ≠ 0 →
    ∃ g ∈ [(1 : AddAut (ZMod 2 × ZMod 2)), kleinSwap, kleinShearL, kleinShearR], g a = b := by
  decide

/-- **The Klein coincidence**: the full automorphism group of the Pauli alphabet
(`AddAut (ZMod 2 × ZMod 2) = GL(2,𝔽₂) = Sp(2,𝔽₂) ≅ S₃`, the single-qubit Clifford group
mod Pauli) is transitive on the nonzero elements. -/
theorem klein_transOnNonzero :
    TransOnNonzero (AddAut (ZMod 2 × ZMod 2)) (ZMod 2 × ZMod 2) := by
  intro a b ha hb
  obtain ⟨g, -, hg⟩ := klein_list_trans a b ha hb
  exact ⟨g, hg⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Pauli case**: the Pauli weight shells of `ι → ZMod 2 × ZMod 2` are exactly
the orbits of the local-symplectic wreath group (coordinatewise `Sp(2,𝔽₂)` with coordinate
permutations) — the symmetry group of the quantum weight enumerator. -/
theorem klein_orbit_eq_shell (x y : ι → ZMod 2 × ZMod 2) :
    y ∈ MulAction.orbit
        (↥(monomialSubgroup ι (ZMod 2 × ZMod 2) (AddAut (ZMod 2 × ZMod 2)))) x
      ↔ hammingNorm y = hammingNorm x :=
  orbit_eq_shell klein_transOnNonzero x y

end Klein

end ECCLib.Scheme

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.AddChar

/-!
# The orbit layer and the contragredient action

Carrier-generic orbit combinatorics for a finite group `H` acting on a finite type `W`
(instantiated at the group `V` and at its dual `AddChar V ℂ`): the orbit `orb H w` and the
orbit set `orbits H W` as `Finset`s — kernel-computable on the primal side, unlike
`MulAction.orbitRel.Quotient` (no computable `Fintype` instance in Mathlib) —
with the regrouping identity `sum_orbits` and the stability reindex `sum_orb_smul`.

The dual action is the contragredient `(h • χ) v = χ (h⁻¹ • v)`, declared as `scoped`
instances (a global instance would form a non-defeq diamond at `H = ℤˣ` against Mathlib's
`Units.instSMul`), `SMul` first with its `@[simp]` unfolder, then `MulAction` and the
`MulDistribMulAction` upgrade. Consumers `open scoped ECCLib.Scheme`.
-/

namespace ECCLib.Scheme

open Finset
open scoped BigOperators

/-! ## Orbits as `Finset`s -/

section Orbits

variable {H : Type*} [Group H] [Fintype H]
variable {W : Type*} [DecidableEq W] [MulAction H W]

/-- The `H`-orbit of `w`, as a `Finset`. -/
def orb (H : Type*) [Group H] [Fintype H] [MulAction H W] (w : W) : Finset W :=
  Finset.univ.image (fun h : H => h • w)

@[simp] theorem mem_orb {v w : W} : w ∈ orb H v ↔ ∃ h : H, h • v = w := by
  simp [orb]

theorem self_mem_orb (v : W) : v ∈ orb H v := mem_orb.mpr ⟨1, one_smul _ _⟩

theorem orb_nonempty (v : W) : (orb H v).Nonempty := ⟨v, self_mem_orb v⟩

theorem orb_eq_of_mem {v w : W} (h : w ∈ orb H v) : orb H w = orb H v := by
  obtain ⟨g, rfl⟩ := mem_orb.mp h
  ext u
  simp only [mem_orb]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k * g, by rw [smul_smul]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k * g⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]⟩

theorem orb_smul (h : H) (v : W) : orb H (h • v) = orb H v :=
  orb_eq_of_mem (mem_orb.mpr ⟨h, rfl⟩)

variable [Fintype W]

/-- The set of all `H`-orbits of `W`. -/
def orbits (H : Type*) [Group H] [Fintype H] (W : Type*) [Fintype W] [DecidableEq W]
    [MulAction H W] : Finset (Finset W) :=
  Finset.univ.image (orb H (W := W))

theorem orb_mem_orbits (v : W) : orb H v ∈ orbits H W :=
  Finset.mem_image_of_mem _ (mem_univ v)

/-- Membership in an orbit is being that orbit. -/
theorem mem_iff_orb_eq {R : Finset W} (hR : R ∈ orbits H W) {v : W} :
    v ∈ R ↔ orb H v = R := by
  obtain ⟨v₀, -, rfl⟩ := Finset.mem_image.mp hR
  exact ⟨fun hv => orb_eq_of_mem hv, fun hv => hv ▸ self_mem_orb v⟩

theorem nonempty_of_mem_orbits {R : Finset W} (hR : R ∈ orbits H W) : R.Nonempty := by
  obtain ⟨v₀, -, rfl⟩ := Finset.mem_image.mp hR
  exact orb_nonempty v₀

/-- The fibre of `orb` over an orbit IS that orbit — the hinge for regrouping sums. -/
theorem filter_orb_eq {R : Finset W} (hR : R ∈ orbits H W) :
    Finset.univ.filter (fun v : W => orb H v = R) = R := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_iff_orb_eq hR).symm

/-- Two orbits sharing a point coincide. -/
theorem eq_of_mem_orbits_of_mem {R R' : Finset W} (hR : R ∈ orbits H W)
    (hR' : R' ∈ orbits H W) {v : W} (hv : v ∈ R) (hv' : v ∈ R') : R = R' :=
  ((mem_iff_orb_eq hR).mp hv).symm.trans ((mem_iff_orb_eq hR').mp hv')

/-- **Regrouping**: any sum over `W` breaks into a sum over orbits. -/
theorem sum_orbits {M : Type*} [AddCommMonoid M] (f : W → M) :
    ∑ R ∈ orbits H W, ∑ v ∈ R, f v = ∑ v : W, f v := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun v : W => orb H v) (t := orbits H W)
    (fun v _ => orb_mem_orbits v) f]
  exact Finset.sum_congr rfl fun R hR => by rw [filter_orb_eq hR]

/-- Orbits are stable: `h • R = R`, in the reindexing form every constancy proof uses. -/
theorem sum_orb_smul {M : Type*} [AddCommMonoid M] {R : Finset W} (hR : R ∈ orbits H W)
    (h : H) (f : W → M) : ∑ v ∈ R, f (h • v) = ∑ v ∈ R, f v := by
  refine Finset.sum_nbij' (i := fun v => h • v) (j := fun v => h⁻¹ • v) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    rw [mem_iff_orb_eq hR] at hv ⊢
    rw [← hv]
    exact orb_eq_of_mem (mem_orb.mpr ⟨h, rfl⟩)
  · intro v hv
    rw [mem_iff_orb_eq hR] at hv ⊢
    rw [← hv]
    exact orb_eq_of_mem (mem_orb.mpr ⟨h⁻¹, rfl⟩)
  · intro v _
    simp
  · intro v _
    simp
  · intro v _
    rfl

/-- Decidability of Mathlib's orbit relation is not automatic; one line supplies it. -/
scoped instance orbitRelDecidable : DecidableRel (MulAction.orbitRel H W) := fun a b =>
  decidable_of_iff (∃ h : H, h • b = a)
    (by rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff])

/-! ## The bridge to Mathlib's orbit quotient

Stated here, at a bare `MulAction` on a finite type, rather than in the transitivity layer:
an orbit count is not an additive fact, and a consumer that wants one should not have to
import a module about transitivity on the nonzero elements of an abelian group. -/

/-- The quotient by the orbit relation is the `Finset` of orbits. -/
noncomputable def quotientOrbitsEquiv :
    MulAction.orbitRel.Quotient H W ≃ {R : Finset W // R ∈ orbits H W} where
  toFun x := Quotient.liftOn' x (fun v => ⟨orb H v, orb_mem_orbits v⟩) (by
    intro a b hab
    exact Subtype.ext (orb_eq_of_mem (mem_orb.mpr
      (MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)))))
  invFun R := Quotient.mk'' (nonempty_of_mem_orbits R.2).choose
  left_inv x := by
    induction x using Quotient.inductionOn' with
    | h v =>
      have hmem := (nonempty_of_mem_orbits (orb_mem_orbits (H := H) v)).choose_spec
      obtain ⟨g, hg⟩ := mem_orb.mp hmem
      rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, hg⟩
  right_inv R := by
    have hmem := (nonempty_of_mem_orbits R.2).choose_spec
    exact Subtype.ext ((mem_iff_orb_eq R.2).mp hmem)

/-- The abstract orbit count is the computable one. -/
theorem card_orbitRel_quotient :
    Nat.card (MulAction.orbitRel.Quotient H W) = (orbits H W).card := by
  rw [Nat.card_congr quotientOrbitsEquiv]
  exact Nat.card_eq_finsetCard _


end Orbits

/-! ## The contragredient action on characters -/

section Dual

variable {H V M : Type*} [Group H] [AddCommGroup V] [DistribMulAction H V] [CommMonoid M]

/-- `(h • χ) v = χ (h⁻¹ • v)`. Scoped, to avoid a diamond with `Units.instSMul`. -/
scoped instance contraSMul : SMul H (AddChar V M) where
  smul h χ := χ.compAddMonoidHom (DistribSMul.toAddMonoidHom V h⁻¹)

@[simp] theorem contra_smul_apply (h : H) (χ : AddChar V M) (v : V) :
    (h • χ) v = χ (h⁻¹ • v) := rfl

scoped instance contraMulAction : MulAction H (AddChar V M) where
  one_smul χ := by
    ext v
    simp
  mul_smul h₁ h₂ χ := by
    ext v
    simp [mul_smul]

/-- The action is by automorphisms of the dual group. -/
scoped instance contraMulDistribMulAction : MulDistribMulAction H (AddChar V M) where
  smul_mul _ _ _ := by
    ext v
    rfl
  smul_one _ := by
    ext v
    rfl

/-- The pairing is invariant — the whole point of the inverse. -/
theorem pairing_smul (h : H) (χ : AddChar V M) (v : V) : (h • χ) (h • v) = χ v := by
  simp

end Dual

end ECCLib.Scheme

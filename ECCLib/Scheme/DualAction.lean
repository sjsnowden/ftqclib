/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Annihilator
import ECCLib.Scheme.Orbits
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# Characters under a group action

Everything about the contragredient action `(g • χ) v = χ (g⁻¹ • v)` that is not about orbits
of vectors: that it is additive, what it fixes, and how many things it fixes.

The organising fact is one homomorphism. Write `shiftHom g` for `v ↦ g • v - v`; then

* the vectors fixed by `g` are exactly `ker (shiftHom g)` — immediate;
* the characters fixed by `g` are exactly the annihilator of `range (shiftHom g)`, because
  `χ` is fixed iff `χ (g • v) = χ v` for all `v`, iff `χ` kills every `g • v - v`;
* so `g` fixes as many characters as vectors (`card_fixedBy_dual_eq`), since annihilating an
  image counts the kernel (`ECCLib.card_charAnnihSubgroup_range`);
* and summing that over a finite group, Burnside's lemma gives equal orbit counts on the two
  sides (`card_orbits_dual_eq`).

Only the last two statements need finiteness. Nothing here mentions the Hamming setting, a
field, or a shell.

The action's `SMul`/`MulAction` instances are declared in `Orbits.lean`, where the spectral
layer consumes them; this module adds the `DistribMulAction` upgrade, which is what any
statement mentioning `0` on the dual side requires. All of them are `scoped`,
so consumers `open scoped ECCLib.Scheme`.

## Main definitions

* `contraDistrib` — the contragredient action as a `DistribMulAction` (scoped).
* `shiftHom` — the displacement homomorphism `v ↦ g • v - v`.

## Main results

* `fixedBy_eq_ker` — the fixed vectors are `ker (shiftHom g)`.
* `mem_fixedBy_dual_iff` / `fixedBy_dual_eq_annihilator` — the fixed characters annihilate
  `range (shiftHom g)`.
* `card_fixedBy_dual_eq` — a symmetry fixes as many characters as vectors.
* `card_orbits_dual_eq` — hence, by Burnside, equal orbit counts.

## Implementation notes

The action's `SMul` and `MulAction` instances are declared in `Orbits.lean`, not here: the
spectral layer consumes them, and moving them would make those modules import this file
for tidiness alone. All the instances are `scoped`, so consumers
`open scoped ECCLib.Scheme`.
-/

namespace ECCLib.Scheme

open MulAction

/-! ## The action is additive -/

section Action

variable {V : Type*} [AddCommGroup V] {G : Type*} [Group G] [DistribMulAction G V]

/-- The contragredient action fixes the trivial character. -/
theorem contra_smul_zero (h : G) : (h • (0 : AddChar V ℂ)) = 0 := by
  ext a
  rw [contra_smul_apply]
  rfl

/-- …and therefore detects it: a transformed character is trivial iff the character was. -/
theorem contra_smul_eq_zero_iff (h : G) (χ : AddChar V ℂ) : h • χ = 0 ↔ χ = 0 := by
  constructor
  · intro hz
    have hcancel : h⁻¹ • (h • χ) = h⁻¹ • (0 : AddChar V ℂ) := by rw [hz]
    rwa [inv_smul_smul, contra_smul_zero] at hcancel
  · rintro rfl
    exact contra_smul_zero h

/-- The contragredient action is additive on characters — what any statement mentioning `0`
on the dual side needs. -/
scoped instance contraDistrib : DistribMulAction G (AddChar V ℂ) where
  smul_zero h := contra_smul_zero h
  smul_add _ _ _ := by
    ext v
    rfl

/-! ## What a symmetry fixes -/

/-- The **shift homomorphism** of a symmetry `g`: `v ↦ g • v - v`. Its kernel is the fixed
subgroup of `g` and its image is what the fixed characters annihilate. -/
def shiftHom (g : G) : V →+ V :=
  DistribSMul.toAddMonoidHom V g - AddMonoidHom.id V

@[simp] theorem shiftHom_apply (g : G) (v : V) : shiftHom g v = g • v - v := rfl

/-- The vectors fixed by `g` are the kernel of `shiftHom g`. -/
theorem fixedBy_eq_ker (g : G) :
    fixedBy V g = ((AddMonoidHom.ker (shiftHom (V := V) g) : AddSubgroup V) : Set V) := by
  ext v
  simp [mem_fixedBy, AddMonoidHom.mem_ker, sub_eq_zero]

/-- **A character is fixed exactly when it annihilates every shift.** The contragredient
action carries the inverse, so being fixed says `χ (g⁻¹ • v) = χ v`; reindexing turns that
into `χ (g • v) = χ v`, and dividing turns that into `χ (g • v - v) = 1`. -/
theorem mem_fixedBy_dual_iff (g : G) (χ : AddChar V ℂ) :
    g • χ = χ ↔ χ ∈ charAnnihSubgroup (AddMonoidHom.range (shiftHom (V := V) g)) := by
  have hne : ∀ w : V, χ w ≠ 0 := fun w => (χ.val_isUnit w).ne_zero
  have key : ∀ w : V, χ (shiftHom (V := V) g w) = 1 ↔ χ (g • w) = χ w := by
    intro w
    rw [shiftHom_apply, sub_eq_add_neg, χ.map_add_eq_mul, χ.map_neg_eq_inv,
      mul_inv_eq_one₀ (hne w)]
  have hfix : g • χ = χ ↔ ∀ w : V, χ (g • w) = χ w := by
    constructor
    · intro h w
      have hw : (g • χ) (g • w) = χ (g • w) := by rw [h]
      rw [contra_smul_apply, inv_smul_smul] at hw
      exact hw.symm
    · intro h
      ext v
      rw [contra_smul_apply]
      have hv := h (g⁻¹ • v)
      rw [smul_inv_smul] at hv
      exact hv.symm
  rw [hfix, mem_charAnnihSubgroup]
  constructor
  · intro h x hx
    obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.mp hx
    exact (key w).mpr (h w)
  · intro h w
    exact (key w).mp (h _ (AddMonoidHom.mem_range.mpr ⟨w, rfl⟩))

/-- The fixed characters of `g`, as a set, are the annihilator of `range (shiftHom g)`. -/
theorem fixedBy_dual_eq_annihilator (g : G) :
    fixedBy (AddChar V ℂ) g
      = ((charAnnihSubgroup (AddMonoidHom.range (shiftHom (V := V) g)) :
          AddSubgroup (AddChar V ℂ)) : Set (AddChar V ℂ)) := by
  ext χ
  rw [SetLike.mem_coe, mem_fixedBy]
  exact mem_fixedBy_dual_iff g χ

end Action

/-! ## Counting

`Nat.card` needs only finiteness, and the `Fintype` the annihilator machinery uses is
supplied one layer down. -/

section Counting

variable {V : Type*} [AddCommGroup V] [Finite V]
variable {G : Type*} [Group G] [DistribMulAction G V]

/-- **`g` fixes as many characters as vectors.** -/
theorem card_fixedBy_dual_eq (g : G) :
    Nat.card (fixedBy (AddChar V ℂ) g) = Nat.card (fixedBy V g) := by
  rw [fixedBy_dual_eq_annihilator, fixedBy_eq_ker, SetLike.coe_sort_coe, SetLike.coe_sort_coe]
  exact card_charAnnihSubgroup_range _

variable [Finite G]

/-- **Equal orbit counts.** Burnside's lemma on each side turns the orbit count into a sum of
fixed-point counts, and `card_fixedBy_dual_eq` matches those summands one group element at a
time. -/
theorem card_orbits_dual_eq :
    Nat.card (orbitRel.Quotient G (AddChar V ℂ)) = Nat.card (orbitRel.Quotient G V) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype G := Fintype.ofFinite G
  haveI : ∀ g : G, Fintype (fixedBy V g) := fun _ => Fintype.ofFinite _
  haveI : ∀ g : G, Fintype (fixedBy (AddChar V ℂ) g) := fun _ => Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient G V) := Fintype.ofFinite _
  haveI : Fintype (orbitRel.Quotient G (AddChar V ℂ)) := Fintype.ofFinite _
  have hsum : (∑ g : G, Fintype.card (fixedBy (AddChar V ℂ) g))
      = ∑ g : G, Fintype.card (fixedBy V g) :=
    Finset.sum_congr rfl fun g _ => by
      simpa [Nat.card_eq_fintype_card] using card_fixedBy_dual_eq (V := V) g
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (AddChar V ℂ),
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G V] at hsum
  have := Nat.eq_of_mul_eq_mul_right Fintype.card_pos hsum
  simpa [Nat.card_eq_fintype_card] using this

end Counting

end ECCLib.Scheme

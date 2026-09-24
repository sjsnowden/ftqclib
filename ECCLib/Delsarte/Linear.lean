/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.LP
import ECCLib.WeightEnumerator
import ECCLib.Distance

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# The linear bridge: MacWilliams coefficientwise

**`macwilliams_coeff`** — for a linear code over any finite field,
`Σᵢ Aᵢ·K_k(i) = |C|·A'_k`: the Krawtchouk transform of the weight distribution is
`|C|` times the DUAL code's weight distribution. Reference: Cohn–Zhao
arXiv:1212.1913 eq. (4) (the MacWilliams transform with the linear-dual statement;
MS77 p. 137).

The identity is reached through the Delsarte layer's dual shells (`charShellSum` + the `mulShift`
tuple bijection — the field's self-duality) and lands on `weightDist (dualCode C)`, the object the
library's `homMacwilliams` reaches through the evaluated bivariate transform. Two independent routes
to the same coefficient data; concrete agreement rows against the `WitnessCoding` values are in
`LinearCheck.lean`.

Linear codes are presented by ONE Finset idiom throughout
(`hS : ∀ x, x ∈ S ↔ x ∈ C`); the LP master specializes to
linear codes through `minDist_le_hammingDist` (`lp_linear`).
-/

namespace ECCLib.Delsarte

open Finset ECCLib.Coding ECCLib.Heisenberg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The `mulShift` machinery — the field's self-duality, concretely -/

omit [Fintype ι] [DecidableEq ι] in
theorem addChar_val_ne_zero (ψ : AddChar F ℂ) (u : F) : ψ u ≠ 0 := by
  intro h0
  have h1 : ψ u * ψ (-u) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

omit [Fintype ι] [DecidableEq ι] in
theorem mulShift_injective {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    Function.Injective (fun a : F => AddChar.mulShift ψ a) := by
  intro a b hab
  by_contra hne
  have h1 : AddChar.mulShift ψ (a - b) = 1 := by
    ext t
    have h := DFunLike.congr_fun hab t
    simp only [AddChar.mulShift_apply] at h
    rw [AddChar.mulShift_apply, AddChar.one_apply, sub_mul, AddChar.map_sub_eq_div, h,
      div_self (addChar_val_ne_zero ψ (b * t))]
  exact ECCLib.mulShift_ne_one hψ (sub_ne_zero.mpr hne) h1

omit [Fintype ι] [DecidableEq ι] in
theorem mulShift_bijective {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    Function.Bijective (fun a : F => AddChar.mulShift ψ a) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨mulShift_injective hψ, AddChar.card_eq.symm⟩

/-- The character tuple of a word, through a fixed nontrivial character. -/
noncomputable def toTuple (ψ : AddChar F ℂ) (y : ι → F) : ι → AddChar F ℂ :=
  fun i => AddChar.mulShift ψ (y i)

theorem tupleChar_toTuple (ψ : AddChar F ℂ) (y x : ι → F) :
    tupleChar (toTuple ψ y) x = ψ (pairing y x) := by
  unfold tupleChar toTuple pairing
  rw [addChar_map_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [AddChar.mulShift_apply]

theorem hammingNorm_toTuple {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (y : ι → F) :
    hammingNorm (toTuple ψ y) = hammingNorm y := by
  unfold hammingNorm toTuple
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h hy
    exact h (by rw [hy]; exact AddChar.mulShift_zero ψ)
  · intro hy h
    exact ECCLib.mulShift_ne_one hψ hy h

theorem toTuple_injective {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    Function.Injective (toTuple (ι := ι) ψ) := by
  intro y y' h
  funext i
  exact mulShift_injective hψ (congrFun h i)

/-! ## The `fourierOp_indicator` bridge, collapsed onto a presentation -/

theorem sum_pairingChar_presentation {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {C : Submodule F (ι → F)} {S : Finset (ι → F)}
    (hS : ∀ x, x ∈ S ↔ x ∈ C) (y : ι → F) :
    ∑ x ∈ S, ψ (pairing y x)
      = (Nat.card C : ℂ) * Coding.indicator (dualCode C) y := by
  have h := congrFun (Coding.fourierOp_indicator (C := C) hψ) y
  rw [Heisenberg.fourierOp_apply] at h
  calc ∑ x ∈ S, ψ (pairing y x)
      = ∑ x ∈ S, ψ (pairing y x) * Coding.indicator C x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [show Coding.indicator C x = 1 by
          simp [Coding.indicator, (hS x).mp hx], mul_one]
    _ = ∑ x : ι → F, ψ (pairing y x) * Coding.indicator C x := by
        refine Finset.sum_subset (Finset.subset_univ S) fun x _ hx => ?_
        have hxC : x ∉ C := fun hmem => hx ((hS x).mpr hmem)
        rw [show Coding.indicator C x = 0 by simp [Coding.indicator, hxC], mul_zero]
    _ = (Nat.card C : ℂ) * Coding.indicator (dualCode C) y := by
        rw [h]
        rfl

/-- `weightDist` through a presentation. -/
theorem weightDist_presentation {C : Submodule F (ι → F)} {S : Finset (ι → F)}
    (hS : ∀ x, x ∈ S ↔ x ∈ C) (i : ℕ) :
    weightDist C i = (S.filter fun x => hammingNorm x = i).card := by
  unfold Coding.weightDist
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS]

/-! ## The bridge -/

/-- **MacWilliams, coefficientwise** — `Σᵢ Aᵢ·K_k(i) = |C|·A'_k`, proved through the
Delsarte layer's dual shells; `homMacwilliams` reaches the same `A'_k` through the
evaluated transform (a two-route cross-check). -/
theorem macwilliams_coeff {C : Submodule F (ι → F)} {S : Finset (ι → F)}
    (hS : ∀ x, x ∈ S ↔ x ∈ C) (k : ℕ) :
    ∑ i ∈ Finset.range (Fintype.card ι + 1),
        (weightDist C i : ℤ) * kraw (Fintype.card F) (Fintype.card ι) k i
      = (Nat.card C : ℤ) * (weightDist (dualCode C) k : ℤ) := by
  classical
  obtain ⟨ψ, hψ⟩ := Coding.exists_ne_one_addChar (F := F)
  set q := Fintype.card F
  set n := Fintype.card ι
  have key : ((∑ i ∈ Finset.range (n + 1),
      (weightDist C i : ℤ) * kraw q n k i : ℤ) : ℂ)
      = (Nat.card C : ℂ) * (weightDist (dualCode C) k : ℂ) := by
    -- (1) cast and fiberwise-collapse onto the presentation
    have h1 : ((∑ i ∈ Finset.range (n + 1),
        (weightDist C i : ℤ) * kraw q n k i : ℤ) : ℂ)
        = ∑ x ∈ S, ((kraw q n k (hammingNorm x) : ℤ) : ℂ) := by
      push_cast
      rw [Finset.sum_congr rfl (fun i _ => by rw [weightDist_presentation hS i])]
      rw [← Finset.sum_fiberwise_of_maps_to'
        (g := fun x : ι → F => hammingNorm x) (t := Finset.range (n + 1))
        (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le hammingNorm_le_card_fintype))
        (fun i => ((kraw q n k i : ℤ) : ℂ))]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.sum_const, nsmul_eq_mul]
    -- (2) shell identity per codeword, swap
    have h2 : ∑ x ∈ S, ((kraw q n k (hammingNorm x) : ℤ) : ℂ)
        = ∑ χ ∈ Finset.univ.filter
            (fun χ : ι → AddChar F ℂ => hammingNorm χ = k),
            ∑ x ∈ S, tupleChar χ x := by
      rw [Finset.sum_congr rfl fun x _ => (charShellSum k x).symm, Finset.sum_comm]
    -- (3) reindex the tuple shell by the word shell via `toTuple`
    have h3 : ∑ χ ∈ Finset.univ.filter
        (fun χ : ι → AddChar F ℂ => hammingNorm χ = k),
        ∑ x ∈ S, tupleChar χ x
        = ∑ y ∈ Finset.univ.filter (fun y : ι → F => hammingNorm y = k),
            ∑ x ∈ S, ψ (pairing y x) := by
      refine (Finset.sum_nbij (i := toTuple ψ) ?_ ?_ ?_ ?_).symm
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        rw [hammingNorm_toTuple hψ]
        exact hy
      · intro y _ y' _ h
        exact toTuple_injective hψ h
      · intro χ hχ
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hχ
        set y : ι → F := fun i => Fintype.bijInv (mulShift_bijective hψ) (χ i) with hy
        have hty : toTuple ψ y = χ := by
          funext i
          exact Fintype.rightInverse_bijInv (mulShift_bijective hψ) (χ i)
        refine ⟨y, ?_, hty⟩
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
        rw [← hammingNorm_toTuple hψ y, hty]
        exact hχ
      · intro y _
        exact Finset.sum_congr rfl fun x _ => (tupleChar_toTuple ψ y x).symm
    -- (4) evaluate per shell word via the collapsed bridge, then count the dual shell
    have h4 : ∑ y ∈ Finset.univ.filter (fun y : ι → F => hammingNorm y = k),
        ∑ x ∈ S, ψ (pairing y x)
        = (Nat.card C : ℂ) * (weightDist (dualCode C) k : ℂ) := by
      rw [Finset.sum_congr rfl fun y _ => sum_pairingChar_presentation hψ hS y,
        ← Finset.mul_sum]
      congr 1
      have hind : ∀ y ∈ Finset.univ.filter (fun y : ι → F => hammingNorm y = k),
          Coding.indicator (dualCode C) y
            = if y ∈ dualCode C then (1 : ℂ) else 0 := by
        intro y _
        simp [Coding.indicator]
      rw [Finset.sum_congr rfl hind, Finset.sum_ite, Finset.sum_const,
        Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
      unfold Coding.weightDist
      congr 2
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [h1, h2, h3, h4]
  exact_mod_cast key

/-! ## The LP bound for linear codes -/

/-- A presentation has the code's cardinality. -/
theorem card_presentation {C : Submodule F (ι → F)} {S : Finset (ι → F)}
    (hS : ∀ x, x ∈ S ↔ x ∈ C) : S.card = Nat.card C := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext x
  simp [hS]

/-- **The Delsarte LP bound for linear codes**, with the distance hypothesis
discharged by `minDist_le_hammingDist`. -/
theorem lp_linear {C : Submodule F (ι → F)} {S : Finset (ι → F)} {d : ℕ}
    (cert : LPCert (Fintype.card F) (Fintype.card ι) d)
    (hS : ∀ x, x ∈ S ↔ x ∈ C) (hd : d ≤ minDist C) :
    (S.card : ℤ) * cert.beta 0 ≤ cert.value := by
  refine cert.card_mul_le_value (A := F) S ?_
  intro x hx y hy hne
  exact le_trans hd (minDist_le_hammingDist ((hS x).mp hx) ((hS y).mp hy) hne)

end ECCLib.Delsarte

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.SignedLagrangian
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The floor `χ ↔ e` equivalence — frame-pure

The reverse leg of the effective bijection `(L,χ) ↔ floor amplitude`. Everything here is frame-pure:
the floor amplitude `e : 𝔽₂ⁿ → ZMod 4` is the translated (`basepoint 0`) `μ₄` quadratic form, and a
`FloorKernel` packages a Lagrangian `L`, a coset offset `x₀`, and an `L`-shift-consistent `e`.

The shift law is χ-free: translating to basepoint `0`, the stabilizer recurrence reads
`e(u + g.X) = e u + e(g.X) + 2·zDot g u` for `u` in the support `π_X(L)`. (Pure-`Z` generators —
`g.X = 0` — are automatic by isotropy: `ω(g,h) = 0` forces `g.Z · h.X = 0` on the support.) The
decode reads `χ` back: `χ(g) = e(g.X) − e 0 − yWeight g`. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer

/-- `2` is prime. Together with `Mathlib.Algebra.Field.ZMod` this gives `Field (ZMod 2)`, from
which `Module.Free.of_divisionRing` derives `Module.Free (ZMod 2) M` for any `Module (ZMod 2) M`,
and the existing `finiteDimensional_pi`/`finiteDimensional_submodule` instances make every
submodule of `Fin n → ZMod 2` finite-dimensional — so `Module.finBasis (ZMod 2) ·` produces a
`Fin`-indexed basis without further setup. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {n : ℕ}

/-- The `X`-projection `Pauli n → 𝔽₂ⁿ` as a `ZMod 2`-linear map (frame-pure). -/
def xProjₗ : Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun p := p.X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The support space `π_X(L) ⊆ 𝔽₂ⁿ` of a Lagrangian. -/
def supportSpace (L : Submodule (ZMod 2) (Pauli n)) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  L.map xProjₗ

/-- `e` is **`L`-shift-consistent** (basepoint `0`): along each `g ∈ L`, on the support `π_X(L)`,
its shift obeys `e(u + g.X) = e u + e(g.X) + 2·zDot g u` — the χ-free stabilizer recurrence. -/
def ShiftConsistent (L : Submodule (ZMod 2) (Pauli n)) (e : (Fin n → ZMod 2) → ZMod 4) : Prop :=
  ∀ g ∈ L, ∀ u ∈ supportSpace L, e (u + g.X) = e u + e g.X + 2 * ((zDot g u : ℕ) : ZMod 4)

/-- The decode `e ↦ χ`: `χ(g) = e(g.X) − e 0 − yWeight g`. -/
def chiOfE (e : (Fin n → ZMod 2) → ZMod 4) (g : Pauli n) : ZMod 4 :=
  e g.X - e 0 - (yWeight g : ZMod 4)

/-- The `Z`-projection `Pauli n → 𝔽₂ⁿ` as a `ZMod 2`-linear map (frame-pure). -/
def zProjₗ : Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun p := p.Z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The **pure-`X` part** of `L`: the stabilizers with zero `Z`-component (`L ∩ ker(·.Z)`). -/
def purX (L : Submodule (ZMod 2) (Pauli n)) : Submodule (ZMod 2) (Pauli n) :=
  L ⊓ LinearMap.ker zProjₗ

open scoped Classical in
/-- A **good** `L`-lift of a support vector: pure-`X` (`Z = 0`) when the pure-`X` part of `L`
covers `b`, else an arbitrary lift. Pure-`X`-where-possible is what makes the syndrome solve
consistent (`liftToL_pureX`); the basic properties (`liftToL_mem`, `liftToL_X`) are unchanged, so
every downstream lemma is unaffected. -/
noncomputable def liftToL {L : Submodule (ZMod 2) (Pauli n)} {b : Fin n → ZMod 2}
    (hb : b ∈ supportSpace L) : Pauli n :=
  if hbX : b ∈ (purX L).map xProjₗ then (Submodule.mem_map.mp hbX).choose
  else (Submodule.mem_map.mp hb).choose

theorem liftToL_mem {L : Submodule (ZMod 2) (Pauli n)} {b : Fin n → ZMod 2}
    (hb : b ∈ supportSpace L) : liftToL hb ∈ L := by
  unfold liftToL; split_ifs with hbX
  · exact (Submodule.mem_inf.mp (Submodule.mem_map.mp hbX).choose_spec.1).1
  · exact (Submodule.mem_map.mp hb).choose_spec.1

theorem liftToL_X {L : Submodule (ZMod 2) (Pauli n)} {b : Fin n → ZMod 2}
    (hb : b ∈ supportSpace L) : (liftToL hb).X = b := by
  unfold liftToL; split_ifs with hbX
  · exact (Submodule.mem_map.mp hbX).choose_spec.2
  · exact (Submodule.mem_map.mp hb).choose_spec.2

/-- The good lift is **pure-`X`** when `b` is covered by the pure-`X` part of `L`. -/
theorem liftToL_pureX {L : Submodule (ZMod 2) (Pauli n)} {b : Fin n → ZMod 2}
    (hb : b ∈ supportSpace L) (hbX : b ∈ (purX L).map xProjₗ) : (liftToL hb).Z = 0 := by
  unfold liftToL; rw [dif_pos hbX]
  have h := (Submodule.mem_inf.mp (Submodule.mem_map.mp hbX).choose_spec.1).2
  rwa [LinearMap.mem_ker] at h

/-- `purXSupportSub L` is the pure-`X` part `π_X(purX L)` of the support, as a submodule of
`supportSpace L` (via `comap` of the inclusion). The adapted basis bases this block first. -/
noncomputable def purXSupportSub (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule (ZMod 2) (supportSpace L) :=
  ((purX L).map xProjₗ).comap (supportSpace L).subtype

/-- A chosen complement of `purXSupportSub L` inside `supportSpace L`. -/
noncomputable def purXCompl (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule (ZMod 2) (supportSpace L) :=
  (purXSupportSub L).exists_isCompl.choose

theorem purXIsCompl (L : Submodule (ZMod 2) (Pauli n)) :
    IsCompl (purXSupportSub L) (purXCompl L) :=
  (purXSupportSub L).exists_isCompl.choose_spec

theorem purXFinrankAdd (L : Submodule (ZMod 2) (Pauli n)) :
    Module.finrank (ZMod 2) (purXSupportSub L) + Module.finrank (ZMod 2) (purXCompl L)
      = Module.finrank (ZMod 2) (supportSpace L) :=
  Submodule.finrank_add_eq_of_isCompl (purXIsCompl L)

/-- The reindexing `Fin a ⊕ Fin c ≃ Fin (suppDim)` placing the `purXSupportSub` block first. -/
noncomputable def supportReindex (L : Submodule (ZMod 2) (Pauli n)) :
    (Fin (Module.finrank (ZMod 2) (purXSupportSub L)) ⊕ Fin (Module.finrank (ZMod 2) (purXCompl L)))
      ≃ Fin (Module.finrank (ZMod 2) (supportSpace L)) :=
  finSumFinEquiv.trans (finCongr (purXFinrankAdd L))

/-- A `Fin (Module.finrank (ZMod 2) (supportSpace L))`-indexed basis of the support **adapted to
`purXSupportSub L`**: its front block (the `Sum.inl` indices of `supportReindex`) is a basis of the
pure-`X` part `π_X(purX L)`. Built from a complement and reindexed. The lifts of the front block are
pure-`X`, which is what makes `gapHalf` vanish on `purX L`. -/
noncomputable def supportBasis (L : Submodule (ZMod 2) (Pauli n)) :
    Module.Basis (Fin (Module.finrank (ZMod 2) (supportSpace L))) (ZMod 2)
      (supportSpace L) :=
  (((Module.finBasis (ZMod 2) (purXSupportSub L)).prod
      (Module.finBasis (ZMod 2) (purXCompl L))).map
      (Submodule.prodEquivOfIsCompl _ _ (purXIsCompl L))).reindex (supportReindex L)

/-- **Front-block identity.** On the `Sum.inl` indices, `supportBasis` is the chosen basis of the
pure-`X` block `purXSupportSub L`. -/
theorem supportBasis_inl (L : Submodule (ZMod 2) (Pauli n))
    (i : Fin (Module.finrank (ZMod 2) (purXSupportSub L))) :
    supportBasis L (supportReindex L (Sum.inl i))
      = ((Module.finBasis (ZMod 2) (purXSupportSub L) i : purXSupportSub L) : supportSpace L) := by
  unfold supportBasis
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply,
    Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_fst,
    Module.Basis.prod_apply_inl_snd]
  simp

/-- The front-block basis vectors land in `(purX L).map xProjₗ` as bit-vectors — so their lifts are
pure-`X`. -/
theorem supportBasis_inl_mem (L : Submodule (ZMod 2) (Pauli n))
    (i : Fin (Module.finrank (ZMod 2) (purXSupportSub L))) :
    (↑(supportBasis L (supportReindex L (Sum.inl i))) : Fin n → ZMod 2)
      ∈ (purX L).map xProjₗ := by
  rw [supportBasis_inl]
  have hmem : (Module.finBasis (ZMod 2) (purXSupportSub L) i : supportSpace L) ∈ purXSupportSub L :=
    Submodule.coe_mem _
  unfold purXSupportSub at hmem
  rw [Submodule.mem_comap] at hmem
  exact hmem

/-- The abstract `μ₄` **quadratic refinement** over a coordinate vector `ε : Fin k → ZMod 2`: a
linear part `Σ s(εᵢ)·vᵢ` plus an upper-triangular quadratic part `Σ_{j<i} s(εᵢ)s(εⱼ)·2Bᵢⱼ`
(`s(c) := (c.val : ZMod 4)`). `encodeE` is the instance with `vᵢ = χ gᵢ + yWeight gᵢ`,
`Bᵢⱼ = zDot gᵢ bⱼ`. Reusable for the `m ≥ 3` tower. -/
def quadRefine {k : ℕ} (v : Fin k → ZMod 4) (Bh : Fin k → Fin k → ZMod 4)
    (ε : Fin k → ZMod 2) : ZMod 4 :=
  (∑ i, ((ε i).val : ZMod 4) * v i)
  + ∑ i, ∑ j ∈ Finset.univ.filter (· < i),
      ((ε i).val : ZMod 4) * ((ε j).val : ZMod 4) * (2 * Bh i j)

/-- The refinement vanishes at the zero coordinate vector (both sums are `s(0) = 0`). -/
theorem quadRefine_zero {k : ℕ} (v : Fin k → ZMod 4) (Bh : Fin k → Fin k → ZMod 4) :
    quadRefine v Bh 0 = 0 := by
  simp [quadRefine]

/-- **Polar identity (the heart of `ShiftConsistent`).** The refinement's deviation from additivity:
`Q(α+δ) − Q(α) − Q(δ) = −2·Σ s(αᵢ)s(δᵢ)vᵢ + Σ_{j<i}(s(αᵢ)s(δⱼ)+s(αⱼ)s(δᵢ))·2Bᵢⱼ`. The linear
carry is load-bearing; the quadratic-part XOR carries vanish (`val_add_mul_two`). -/
theorem quadRefine_add {k : ℕ} (v : Fin k → ZMod 4) (Bh : Fin k → Fin k → ZMod 4)
    (α δ : Fin k → ZMod 2) :
    quadRefine v Bh (α + δ)
      = quadRefine v Bh α + quadRefine v Bh δ
        + (-2 * (∑ i, ((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * v i)
           + ∑ i, ∑ j ∈ Finset.univ.filter (· < i),
               (((α i).val : ZMod 4) * ((δ j).val : ZMod 4)
                 + ((α j).val : ZMod 4) * ((δ i).val : ZMod 4)) * (2 * Bh i j)) := by
  have hLin : (∑ i, (((α + δ) i).val : ZMod 4) * v i)
      = (∑ i, ((α i).val : ZMod 4) * v i) + (∑ i, ((δ i).val : ZMod 4) * v i)
        - 2 * (∑ i, ((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * v i) := by
    have h1 : ∀ i ∈ Finset.univ, (((α + δ) i).val : ZMod 4) * v i
        = ((α i).val : ZMod 4) * v i + ((δ i).val : ZMod 4) * v i
          - 2 * (((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * v i) := by
      intro i _
      rw [Pi.add_apply, val_add_cast]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hQuad : (∑ i, ∑ j ∈ Finset.univ.filter (· < i),
        (((α + δ) i).val : ZMod 4) * (((α + δ) j).val : ZMod 4) * (2 * Bh i j))
      = (∑ i, ∑ j ∈ Finset.univ.filter (· < i),
          ((α i).val : ZMod 4) * ((α j).val : ZMod 4) * (2 * Bh i j))
        + (∑ i, ∑ j ∈ Finset.univ.filter (· < i),
          ((δ i).val : ZMod 4) * ((δ j).val : ZMod 4) * (2 * Bh i j))
        + (∑ i, ∑ j ∈ Finset.univ.filter (· < i),
          (((α i).val : ZMod 4) * ((δ j).val : ZMod 4)
            + ((α j).val : ZMod 4) * ((δ i).val : ZMod 4)) * (2 * Bh i j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply]
    rw [val_add_mul_two]; ring
  unfold quadRefine
  rw [hLin, hQuad]; ring

/-- **Symmetric decomposition of a full double sum.** Over `Fin k`, a square sum splits into its
diagonal plus the symmetrized strict-lower-triangle:
`Σᵢⱼ F i j = Σᵢ F i i + Σ_{j<i}(F i j + F j i)`. The `j>i` half is folded onto `j<i` by
`Finset.sum_comm'`. -/
theorem sum_univ_sq_split {k : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin k → Fin k → M) :
    ∑ i, ∑ j, F i j
      = (∑ i, F i i) + ∑ i, ∑ j ∈ Finset.univ.filter (· < i), (F i j + F j i) := by
  classical
  have h1 : ∀ i, (∑ j, F i j) = F i i + ∑ j ∈ Finset.univ.erase i, F i j := fun i =>
    (Finset.add_sum_erase Finset.univ (F i) (Finset.mem_univ i)).symm
  have h2 : ∀ i, (∑ j ∈ Finset.univ.erase i, F i j)
      = (∑ j ∈ Finset.univ.filter (· < i), F i j)
        + ∑ j ∈ Finset.univ.filter (i < ·), F i j := by
    intro i
    have hset : Finset.univ.erase i
        = Finset.univ.filter (· < i) ∪ Finset.univ.filter (i < ·) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, and_true, true_and,
        Finset.mem_union]
      constructor
      · intro hji; exact lt_or_gt_of_ne hji
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h
    have hdisj : Disjoint (Finset.univ.filter (· < i)) (Finset.univ.filter (i < ·)) := by
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj1 hj2; exact absurd (hj1.trans hj2) (lt_irrefl j)
    rw [hset, Finset.sum_union hdisj]
  have h3 : (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), F i j)
      = ∑ i, ∑ j ∈ Finset.univ.filter (· < i), F j i := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.univ.filter (i < ·))
      (t' := Finset.univ) (s' := fun j => Finset.univ.filter (· < j))
      (fun x y => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)]
  simp_rw [h1, h2]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_add_distrib, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]

/-- **Polar = full square (generic).** Given diagonal compatibility (`2vᵢ = 2Bᵢᵢ`) and `2`-symmetry
(`2Bᵢⱼ = 2Bⱼᵢ`), the polar deviation equals the full square form `Σᵢⱼ s(αᵢ)s(δⱼ)·2Bᵢⱼ`. -/
theorem quadRefine_polar_eq_square {k : ℕ} (v : Fin k → ZMod 4) (Bh : Fin k → Fin k → ZMod 4)
    (α δ : Fin k → ZMod 2)
    (hdiag : ∀ i, 2 * v i = 2 * Bh i i) (hsymm : ∀ i j, 2 * Bh i j = 2 * Bh j i) :
    -2 * (∑ i, ((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * v i)
      + ∑ i, ∑ j ∈ Finset.univ.filter (· < i),
          (((α i).val : ZMod 4) * ((δ j).val : ZMod 4)
            + ((α j).val : ZMod 4) * ((δ i).val : ZMod 4)) * (2 * Bh i j)
      = ∑ i, ∑ j, ((α i).val : ZMod 4) * ((δ j).val : ZMod 4) * (2 * Bh i j) := by
  have hdterm : ∀ i, ((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * (2 * Bh i i)
      = -2 * (((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * v i) := by
    intro i
    rw [← hdiag i]
    have h4 : (4 : ZMod 4) = 0 := by decide
    linear_combination (((α i).val : ZMod 4) * ((δ i).val : ZMod 4) * v i) * h4
  rw [sum_univ_sq_split (fun i j =>
    ((α i).val : ZMod 4) * ((δ j).val : ZMod 4) * (2 * Bh i j))]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (hdterm i).symm)
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hsymm j i]; ring

/-- The dimension of the support `π_X(L)` — the number of basis vectors. -/
noncomputable abbrev suppDim (S : FramePureSignedStab n) : ℕ :=
  Module.finrank (ZMod 2) (supportSpace S.L)

/-- The `i`-th lift `gᵢ := liftToL (bas i).property ∈ L` of the support-basis vector `bᵢ`. -/
noncomputable def encLift (S : FramePureSignedStab n) (i : Fin (suppDim S)) : Pauli n :=
  liftToL ((supportBasis S.L) i).property

theorem encLift_mem (S : FramePureSignedStab n) (i : Fin (suppDim S)) : encLift S i ∈ S.L :=
  liftToL_mem _

theorem encLift_X (S : FramePureSignedStab n) (i : Fin (suppDim S)) :
    (encLift S i).X = ((supportBasis S.L) i).val :=
  liftToL_X _

/-- The per-basis target value `vᵢ := χ gᵢ + yWeight gᵢ` (` = e(bᵢ)`). -/
noncomputable def encV (S : FramePureSignedStab n) (i : Fin (suppDim S)) : ZMod 4 :=
  S.chi (encLift S i) + (yWeight (encLift S i) : ZMod 4)

/-- The shift form `Bᵢⱼ := zDot gᵢ bⱼ` (in `ZMod 4`). -/
noncomputable def encB (S : FramePureSignedStab n) (i j : Fin (suppDim S)) : ZMod 4 :=
  ((zDot (encLift S i) ((supportBasis S.L) j).val : ℕ) : ZMod 4)

open scoped Classical in
/-- The **encode** `χ ↦ e`: the `μ₄` quadratic refinement over `supportBasis L`. For
`w = Σᵢ εᵢ bᵢ` (coordinates of `w` in the basis), it is `quadRefine` of the per-basis target
`vᵢ = χ gᵢ + yWeight gᵢ` (`encV`) and shift form `Bᵢⱼ = zDot gᵢ bⱼ` (`encB`). Junk (`0`) off
the support. -/
noncomputable def encodeE (S : FramePureSignedStab n) (w : Fin n → ZMod 2) : ZMod 4 :=
  if hw : w ∈ supportSpace S.L then
    quadRefine (encV S) (encB S) ((supportBasis S.L).repr ⟨w, hw⟩)
  else 0

/-- `encodeE` on the support is the quadratic refinement in the basis coordinates of `w`. -/
theorem encodeE_apply (S : FramePureSignedStab n) {w : Fin n → ZMod 2}
    (hw : w ∈ supportSpace S.L) :
    encodeE S w = quadRefine (encV S) (encB S) ((supportBasis S.L).repr ⟨w, hw⟩) := by
  rw [encodeE, dif_pos hw]

/-- **The doubled shift form is symmetric** — the isotropy of `L` (`ω(gᵢ,gⱼ) = 0`). -/
theorem encB_two_symm (S : FramePureSignedStab n) (i j : Fin (suppDim S)) :
    2 * encB S i j = 2 * encB S j i := by
  unfold encB
  rw [← encLift_X S j, ← encLift_X S i]
  exact two_zDot_swap_of_omega (S.isStab _ (encLift_mem S i) _ (encLift_mem S j))

/-- **Diagonal compatibility** `2·vᵢ = 2·Bᵢᵢ`: the `χ`-part squares away (`two_smul_chi`), leaving
`2·yWeight gᵢ = 2·zDot gᵢ gᵢ.X`. -/
theorem encV_encB_two_diag (S : FramePureSignedStab n) (i : Fin (suppDim S)) :
    2 * encV S i = 2 * encB S i i := by
  have hchi : 2 * S.chi (encLift S i) = 0 :=
    S.toFrameSignedStab.two_smul_chi (encLift_mem S i)
  unfold encV encB
  rw [mul_add, hchi, zero_add, ← encLift_X S i]
  rfl

/-- **Basis reconstruction.** A support vector `w` is recovered from its `supportBasis` coordinates:
`w = Σᵢ (repr w)ᵢ • bᵢ` (the `Basis.sum_repr` identity pushed through the submodule inclusion). -/
theorem support_repr_recon (S : FramePureSignedStab n) {w : Fin n → ZMod 2}
    (hw : w ∈ supportSpace S.L) :
    w = ∑ i, ((supportBasis S.L).repr ⟨w, hw⟩ i) • ((supportBasis S.L) i).val := by
  have key := (supportBasis S.L).sum_repr ⟨w, hw⟩
  have hval := congrArg (supportSpace S.L).subtype key
  rw [map_sum] at hval
  simp only [map_smul, Submodule.subtype_apply] at hval
  exact hval.symm

/-- **The geometric half of `ShiftConsistent`.** With `α, δ` the support-basis coordinates of `u`
and `g.X`, the doubled cross dot product unfolds to the full square form of the shift form `encB`:
`2·zDot g u = Σᵢⱼ s(αᵢ)s(δⱼ)·2·encB i j`. The key step is the isotropic swap
`2·zDot g bᵢ = 2·zDot gᵢ g.X` (commuting `g` past the lift `gᵢ`), after which `g.X` reconstructs. -/
theorem two_zDot_eq_double_sum (S : FramePureSignedStab n) {g : Pauli n} (hg : g ∈ S.L)
    {u : Fin n → ZMod 2}
    (α δ : Fin (suppDim S) → ZMod 2)
    (hurec : u = ∑ i, (α i) • ((supportBasis S.L) i).val)
    (hgrec : g.X = ∑ j, (δ j) • ((supportBasis S.L) j).val) :
    2 * ((zDot g u : ℕ) : ZMod 4)
      = ∑ i, ∑ j, ((α i).val : ZMod 4) * ((δ j).val : ZMod 4) * (2 * encB S i j) := by
  rw [hurec, two_zDot_sum_right,
    Finset.sum_congr rfl (fun i _ => two_zDot_smul_right g (α i) ((supportBasis S.L) i).val)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hswap : 2 * ((zDot g ((supportBasis S.L) i).val : ℕ) : ZMod 4)
      = 2 * ((zDot (encLift S i) g.X : ℕ) : ZMod 4) := by
    rw [← encLift_X S i]
    exact two_zDot_swap_of_omega (S.isStab g hg (encLift S i) (encLift_mem S i))
  rw [hswap, hgrec, two_zDot_sum_right,
    Finset.sum_congr rfl
      (fun j _ => two_zDot_smul_right (encLift S i) (δ j) ((supportBasis S.L) j).val),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold encB
  ring

/-- **Basepoint normalization.** `encodeE S 0 = 0` (the zero subtype representation `repr` is `0`,
so `quadRefine_zero` kills both sums). -/
theorem encodeE_zero (S : FramePureSignedStab n) : encodeE S 0 = 0 := by
  unfold encodeE
  rw [dif_pos (Submodule.zero_mem _)]
  have hrepr : (supportBasis S.L).repr
      ⟨(0 : Fin n → ZMod 2), Submodule.zero_mem (supportSpace S.L)⟩ = 0 := by
    rw [show (⟨(0 : Fin n → ZMod 2), Submodule.zero_mem (supportSpace S.L)⟩
      : ↥(supportSpace S.L)) = 0 from rfl, map_zero]
  rw [hrepr, Finsupp.coe_zero]
  exact quadRefine_zero _ _

/-- **`encodeE` is shift-consistent.** Assembles the reduction (`quadRefine_add` +
basis-coordinate additivity), the combinatorial polar = full-square identity
(`quadRefine_polar_eq_square` with the diagonal/symmetry facts), and the geometric expansion
(`two_zDot_eq_double_sum`) into the χ-free stabilizer recurrence. -/
theorem encodeE_shiftConsistent (S : FramePureSignedStab n) :
    ShiftConsistent S.L (encodeE S) := by
  intro g hg u hu
  have hgX : g.X ∈ supportSpace S.L := Submodule.mem_map_of_mem hg
  have hsum : u + g.X ∈ supportSpace S.L := (supportSpace S.L).add_mem hu hgX
  have hsub : (⟨u + g.X, hsum⟩ : ↥(supportSpace S.L)) = ⟨u, hu⟩ + ⟨g.X, hgX⟩ := rfl
  have hrepr_add : (supportBasis S.L).repr ⟨u + g.X, hsum⟩
      = (supportBasis S.L).repr ⟨u, hu⟩ + (supportBasis S.L).repr ⟨g.X, hgX⟩ := by
    rw [hsub, map_add]
  rw [encodeE_apply S hsum, hrepr_add, Finsupp.coe_add, quadRefine_add,
    ← encodeE_apply S hu, ← encodeE_apply S hgX]
  congr 1
  rw [quadRefine_polar_eq_square (encV S) (encB S) _ _
    (encV_encB_two_diag S) (encB_two_symm S)]
  exact (two_zDot_eq_double_sum S hg _ _
    (support_repr_recon S hu) (support_repr_recon S hgX)).symm

/-! ### Decode recovery on the support, and the pure-`Z` gap (where `x₀` bites)

These localize the left round-trip. `chiOfE (encodeE S)` recovers `χ` exactly on the support-basis
lifts (`chiOfE_encodeE_lift`), hence — by the `betaFrame` character law (`chiOfE_valid` + `S.valid`)
— on the whole lift-span. But on the pure-`Z` part of `L` (`g.X = 0`) it returns `0`
(`chiOfE_encodeE_pureZ`), whereas `S.chi` there is the genuine `Z`-stabilizer sign. Since
`L = span{gᵢ} ⊕ (pure-Z ∩ L)`, the *only* discrepancy is on pure-`Z` generators, where `fullChi`'s
`−2·zDot g x₀` must supply the signs: `2·zDot g x₀ = χ(g)`. That linear solve is the whole of the
`x₀` requirement (`syndromeSolvable_all`). -/

/-- **`encodeE` at a basis vector is the target value.** `encodeE S bᵢ = encV S i` — the refinement
at the `i`-th coordinate indicator `repr bᵢ = single i 1` (linear part picks `vᵢ`, quadratic part
needs two distinct indices and so vanishes). -/
theorem encodeE_basis (S : FramePureSignedStab n) (i : Fin (suppDim S)) :
    encodeE S ((supportBasis S.L) i).val = encV S i := by
  rw [encodeE_apply S ((supportBasis S.L) i).property]
  have hrepr : (supportBasis S.L).repr
      ⟨((supportBasis S.L) i).val, ((supportBasis S.L) i).property⟩ = Finsupp.single i 1 := by
    rw [show (⟨((supportBasis S.L) i).val, ((supportBasis S.L) i).property⟩
      : ↥(supportSpace S.L)) = (supportBasis S.L) i from rfl]
    exact (supportBasis S.L).repr_self i
  rw [hrepr]
  have hlin : (∑ k, ((Finsupp.single i (1 : ZMod 2) k).val : ZMod 4) * encV S k) = encV S i := by
    rw [Finset.sum_eq_single i]
    · rw [Finsupp.single_eq_same, show ((1 : ZMod 2).val : ZMod 4) = 1 from by decide, one_mul]
    · intro k _ hk
      have hz : (Finsupp.single i (1 : ZMod 2)) k = 0 := Finsupp.single_eq_of_ne hk
      rw [hz]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
  have hquad : (∑ k, ∑ l ∈ Finset.univ.filter (· < k),
      ((Finsupp.single i (1 : ZMod 2) k).val : ZMod 4)
        * ((Finsupp.single i (1 : ZMod 2) l).val : ZMod 4) * (2 * encB S k l)) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro l hl
    rw [Finset.mem_filter] at hl
    rcases eq_or_ne k i with hki | hk
    · have hli : l ≠ i := by rw [← hki]; exact ne_of_lt hl.2
      have hz : (Finsupp.single i (1 : ZMod 2)) l = 0 := Finsupp.single_eq_of_ne hli
      rw [hz]; simp
    · have hz : (Finsupp.single i (1 : ZMod 2)) k = 0 := Finsupp.single_eq_of_ne hk
      rw [hz]; simp
  unfold quadRefine
  rw [hlin, hquad, add_zero]

/-- **Decode recovers `χ` on the lifts.** `chiOfE (encodeE S) gᵢ = χ gᵢ` (no `x₀` needed). -/
theorem chiOfE_encodeE_lift (S : FramePureSignedStab n) (i : Fin (suppDim S)) :
    chiOfE (encodeE S) (encLift S i) = S.chi (encLift S i) := by
  unfold chiOfE
  rw [encLift_X S i, encodeE_basis S i, encodeE_zero S]
  unfold encV
  ring

/-- **The pure-`Z` gap.** On `g ∈ L` with `g.X = 0`, the bare decode is `0`, so `fullChi`'s
`−2·zDot g x₀` must supply the sign `χ(g)`. This is where `x₀` bites. -/
theorem chiOfE_encodeE_pureZ (S : FramePureSignedStab n) {g : Pauli n} (hgX : g.X = 0) :
    chiOfE (encodeE S) g = 0 := by
  have hyw : (yWeight g : ZMod 4) = 0 := by
    rw [show yWeight g = 0 from by unfold yWeight; rw [hgX]; exact zDot_zero_right g]
    rfl
  unfold chiOfE
  rw [hgX, hyw, sub_zero, sub_self]

/-- A canonical `μ₄` floor state: a Lagrangian `L`, a coset offset `x₀`, and an `L`-shift-consistent
amplitude form `e` normalized at the basepoint. The `m = 2` rung of the graded ladder. -/
structure FloorKernel (n : ℕ) where
  L : Submodule (ZMod 2) (Pauli n)
  hStab : IsStabilizer L
  hFull : Module.finrank (ZMod 2) L = n
  x₀ : Fin n → ZMod 2
  e : (Fin n → ZMod 2) → ZMod 4
  he0 : e 0 = 0
  hshift : ShiftConsistent L e

/-- **Decode lands a valid character.** The decoded `χ = chiOfE e` obeys the `betaFrame`-twisted
law on `L`. (Reduces, after the shift recurrence, to `4·yWeight(p+q) = 0` in `ZMod 4`.) -/
theorem chiOfE_valid (K : FloorKernel n) {p q : Pauli n} (hp : p ∈ K.L) (hq : q ∈ K.L) :
    chiOfE K.e (p + q) = chiOfE K.e p + chiOfE K.e q + betaFrame p q := by
  have hpX : p.X ∈ supportSpace K.L := Submodule.mem_map_of_mem hp
  have hrec := K.hshift q hq p.X hpX
  have hpqX : (p + q).X = p.X + q.X := rfl
  unfold chiOfE betaFrame
  rw [hpqX, hrec, K.he0]
  have hzero : ∀ y : ZMod 4, 2 * y + 2 * y = 0 := by decide
  have hyw : yWeight (p + q) = zDot (p + q) (p + q).X := rfl
  rw [hyw]
  push_cast
  linear_combination -hzero (((zDot (p + q) (p + q).X : ℕ)) : ZMod 4)

/-! ## The decode `fromFloor : FloorKernel → FramePureSignedStab` -/

/-- The **full decode** `(e, x₀) ↦ χ`, including the coset correction: on `L`,
`χ(g) = chiOfE e g − 2·zDot g x₀`; `0` off `L` (tightness). The `−2·zDot g x₀` term supplies the
pure-`Z` (coset) signs that `chiOfE` alone misses — for `g.X = 0` it gives `χ(g) = 2·(g.Z·x₀)`. -/
noncomputable def fullChi (K : FloorKernel n) (g : Pauli n) : ZMod 4 :=
  open scoped Classical in
  if g ∈ K.L then chiOfE K.e g - 2 * ((zDot g K.x₀ : ℕ) : ZMod 4) else 0

theorem fullChi_zero (K : FloorKernel n) : fullChi K 0 = 0 := by
  unfold fullChi
  rw [if_pos K.L.zero_mem]
  simp [chiOfE, X_zero, K.he0, yWeight_zero, zDot_zero_left]

theorem fullChi_valid (K : FloorKernel n) {p q : Pauli n} (hp : p ∈ K.L) (hq : q ∈ K.L) :
    fullChi K (p + q) = fullChi K p + fullChi K q + betaFrame p q := by
  have hpq : p + q ∈ K.L := K.L.add_mem hp hq
  unfold fullChi
  rw [if_pos hpq, if_pos hp, if_pos hq, chiOfE_valid K hp hq, two_zDot_add p q K.x₀]
  ring

/-- A `FloorKernel` decodes to a frame-native signed Lagrangian. -/
noncomputable def fromFloor (K : FloorKernel n) : FramePureSignedStab n where
  toFrameSignedStab :=
    { L := K.L
      chi := fullChi K
      chi_zero := fullChi_zero K
      valid := fun p hp q hq => fullChi_valid K hp hq }
  isStab := K.hStab
  full := K.hFull
  tight := fun p hp => by simp only [fullChi, if_neg hp]

/-! ## The encode `toFloor` and the equivalence

`ShiftConsistent` holds (`encodeE_shiftConsistent`), so `toFloor` takes only a coset offset `x₀` as
extra input (the pure-`Z` linear solve, supplied by `syndromeSolvable_all`).
`floorEquivOfRoundTrips` assembles an `Equiv` from an encode map and the two round-trips. -/

/-- The encode `χ ↦ floor`, conditional only on a coset offset `x₀`. `ShiftConsistent` is supplied
unconditionally by `encodeE_shiftConsistent`. -/
noncomputable def toFloor (S : FramePureSignedStab n) (x₀ : Fin n → ZMod 2) : FloorKernel n :=
  ⟨S.L, S.isStab, S.full, x₀, encodeE S, encodeE_zero S, encodeE_shiftConsistent S⟩

/-! ### The native correspondence (decode ∘ encode = id)

The gauge-free statement: the `(L,χ)` chart and the floor chart present the same object.
`fromFloor` (decode) is total; `encodeE` + `encodeE_shiftConsistent` give a total encode; and for a
coset rep `x₀` consistent with `S`'s syndrome, decoding back recovers `S` exactly. The *encode*
direction is up to the off-support gauge, so a literal `≃` would additionally require normal forms
pinning that gauge. -/

/-- **Native correspondence — decode ∘ encode = id.** For a coset offset `x₀` consistent with `S`'s
syndrome (`chiOfE (encodeE S) g − 2·zDot g x₀ = χ g` on `L`), encoding then decoding recovers `S`.
The hypothesis is the syndrome linear condition: by `chiOfE_encodeE_lift` its content on the support
lifts is `2·zDot gᵢ x₀ = 0`, and by `chiOfE_encodeE_pureZ` on the pure-`Z` part it is the
`Z`-stabilizer signs `2·zDot g x₀ = χ g`. -/
theorem fromFloor_toFloor (S : FramePureSignedStab n) (x₀ : Fin n → ZMod 2)
    (hx₀ : ∀ g ∈ S.L, chiOfE (encodeE S) g - 2 * ((zDot g x₀ : ℕ) : ZMod 4) = S.chi g) :
    fromFloor (toFloor S x₀) = S := by
  apply framePureSignedStab_ext
  apply FrameSignedStab.ext'
  · rfl
  · funext g
    change fullChi (toFloor S x₀) g = S.chi g
    by_cases hg : g ∈ S.L
    · simp only [fullChi, toFloor, if_pos hg]
      exact hx₀ g hg
    · simp only [fullChi, toFloor, if_neg hg, S.tight g hg]

/-- **The literal equivalence, conditional on the round-trips.** A literal `≃` needs the
`x₀`/off-support gauge pinned (normal forms); the native correspondence above does not. This
assembles the `Equiv` from any encode map satisfying both round-trips. -/
noncomputable def floorEquivOfRoundTrips
    (encode : FramePureSignedStab n → FloorKernel n)
    (left : ∀ S, fromFloor (encode S) = S)
    (right : ∀ K, encode (fromFloor K) = K) :
    FramePureSignedStab n ≃ FloorKernel n :=
  ⟨encode, fromFloor, left, right⟩

/-! ## The intrinsic correspondence — `FloorKernel / gauge ≃ FramePureSignedStab`

The correspondence realized as the **gauge-quotient of the decode map**: `fromFloor` is onto, its
fibers are exactly the gauge orbits, so the floor representation mod gauge *is* the signed
Lagrangian — one intrinsic object in two charts, related by a quotient (no coset-carrying duplicate
type). Surjectivity needs syndrome-solvability (`x₀`-existence), supplied by the good lifts
below. -/

/-! ### The syndrome bit functional `gapHalf`

The gap `χ_floor − χ` between decoded and target signs is, on `L`, a `2`-torsion (`{0,2}`) additive
function; its `ℤ/2` "bit" `gapHalf` is the linear functional fed to `exists_dotZ2_eq`. -/

/-- The `{0,2} ⊆ ZMod 4` 2-torsion bit, as `ZMod 2` (`0 ↦ 0`, `2 ↦ 1`). -/
def bit2 (x : ZMod 4) : ZMod 2 := ((x.val / 2 : ℕ) : ZMod 2)

@[simp] theorem bit2_zero : bit2 (0 : ZMod 4) = 0 := by decide

theorem zmod4_two_torsion : ∀ x : ZMod 4, 2 * x = 0 → x = 0 ∨ x = 2 := by decide

/-- On the 2-torsion, `bit2` is a genuine "halving": `2·(bit2 x).val = x`. -/
theorem two_mul_bit2_val {x : ZMod 4} (h : 2 * x = 0) :
    2 * ((bit2 x).val : ZMod 4) = x := by
  rcases zmod4_two_torsion x h with rfl | rfl <;> decide

/-- `bit2` is additive on the 2-torsion. -/
theorem bit2_add {x y : ZMod 4} (hx : 2 * x = 0) (hy : 2 * y = 0) :
    bit2 (x + y) = bit2 x + bit2 y := by
  rcases zmod4_two_torsion x hx with rfl | rfl <;>
    rcases zmod4_two_torsion y hy with rfl | rfl <;> decide

/-- The decoded sign on `L` obeys the `betaFrame` law (`chiOfE_valid` at `x₀ = 0`). -/
theorem chiOfE_encodeE_valid (S : FramePureSignedStab n) {p q : Pauli n}
    (hp : p ∈ S.L) (hq : q ∈ S.L) :
    chiOfE (encodeE S) (p + q)
      = chiOfE (encodeE S) p + chiOfE (encodeE S) q + betaFrame p q :=
  chiOfE_valid (toFloor S 0) hp hq

@[simp] theorem chiOfE_encodeE_zero (S : FramePureSignedStab n) : chiOfE (encodeE S) 0 = 0 := by
  simp [chiOfE, X_zero, encodeE_zero, yWeight_zero]

/-- The decoded sign is `2`-torsion on `L`. -/
theorem chiOfE_encodeE_two_torsion (S : FramePureSignedStab n) {g : Pauli n} (hg : g ∈ S.L) :
    2 * chiOfE (encodeE S) g = 0 := by
  have h := chiOfE_encodeE_valid S hg hg
  rw [pauli_add_self, betaFrame_self, add_zero, chiOfE_encodeE_zero] at h
  rw [two_mul]; exact h.symm

/-- The syndrome **gap** `χ_floor − χ` is `2`-torsion on `L`. -/
theorem gap_two_torsion (S : FramePureSignedStab n) {g : Pauli n} (hg : g ∈ S.L) :
    2 * (chiOfE (encodeE S) g - S.chi g) = 0 := by
  rw [mul_sub, chiOfE_encodeE_two_torsion S hg, S.toFrameSignedStab.two_smul_chi hg, sub_zero]

/-- The syndrome gap is additive on `L` (the shared `betaFrame` twist cancels). -/
theorem gap_add (S : FramePureSignedStab n) {p q : Pauli n} (hp : p ∈ S.L) (hq : q ∈ S.L) :
    chiOfE (encodeE S) (p + q) - S.chi (p + q)
      = (chiOfE (encodeE S) p - S.chi p) + (chiOfE (encodeE S) q - S.chi q) := by
  rw [chiOfE_encodeE_valid S hp hq, S.valid p hp q hq]; ring

/-- The **syndrome bit functional** `gapHalf S : S.L →ₗ ZMod 2`, `g ↦ bit2 (χ_floor g − χ g)`. Its
double recovers the gap (`two_mul_gapHalf_val`); vanishing on the pure-`X` part is exactly the
`exists_dotZ2_eq` hypothesis. -/
noncomputable def gapHalf (S : FramePureSignedStab n) : S.L →ₗ[ZMod 2] ZMod 2 where
  toFun g := bit2 (chiOfE (encodeE S) (g : Pauli n) - S.chi (g : Pauli n))
  map_add' g g' := by
    simp only [Submodule.coe_add, gap_add S g.2 g'.2]
    exact bit2_add (gap_two_torsion S g.2) (gap_two_torsion S g'.2)
  map_smul' c g := by
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
      simp [chiOfE_encodeE_zero, S.toFrameSignedStab.chi_zero]

/-- The gap is twice its bit: `χ_floor g − χ g = 2·(gapHalf g).val`. -/
theorem two_mul_gapHalf_val (S : FramePureSignedStab n) (g : S.L) :
    2 * ((gapHalf S g).val : ZMod 4) = chiOfE (encodeE S) (g : Pauli n) - S.chi (g : Pauli n) :=
  two_mul_bit2_val (gap_two_torsion S g.2)

/-- The `X`-projection commutes with `ZMod 2`-combinations (it is the linear map `xProjₗ`). -/
theorem xProj_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ZMod 2) (p : ι → Pauli n) :
    (∑ i ∈ s, c i • p i).X = ∑ i ∈ s, c i • (p i).X := by
  rw [show (∑ i ∈ s, c i • p i).X = xProjₗ (∑ i ∈ s, c i • p i) from rfl, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul xProjₗ (c i) (p i)

/-- The `Z`-projection commutes with `ZMod 2`-combinations (it is the linear map `zProjₗ`). -/
theorem zProj_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ZMod 2) (p : ι → Pauli n) :
    (∑ i ∈ s, c i • p i).Z = ∑ i ∈ s, c i • (p i).Z := by
  rw [show (∑ i ∈ s, c i • p i).Z = zProjₗ (∑ i ∈ s, c i • p i) from rfl, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul zProjₗ (c i) (p i)

/-- The lifts of the **front block** are pure-`X` (their `Z` part vanishes) — this is where the
adapted basis pays off. -/
theorem encLift_inl_Z (S : FramePureSignedStab n)
    (i : Fin (Module.finrank (ZMod 2) (purXSupportSub S.L))) :
    (encLift S (supportReindex S.L (Sum.inl i))).Z = 0 := by
  unfold encLift
  exact liftToL_pureX _ (supportBasis_inl_mem S.L i)

/-- `gapHalf` vanishes on every basis lift: the decode matches `χ` there (`chiOfE_encodeE_lift`),
so the gap — and its bit — is `0`. -/
theorem gapHalf_encLift (S : FramePureSignedStab n) (j : Fin (suppDim S)) :
    gapHalf S ⟨encLift S j, encLift_mem S j⟩ = 0 := by
  unfold gapHalf
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [chiOfE_encodeE_lift S j, sub_self]
  rfl

/-- **`gapHalf` vanishes on the pure-`X` part of `L`.** A pure-`X` stabilizer `g` reconstructs
over the adapted basis's front block into pure-`X` lifts, with no pure-`Z` remainder (what the front
block being a basis of `π_X(purX L)` buys). `gapHalf` is `ZMod 2`-linear and vanishes on each
lift, so it vanishes on `g`. Discharges the `syndromeSolvable_of` hypothesis. -/
theorem gapHalf_vanish_pureX (S : FramePureSignedStab n) (g : S.L)
    (hgZ : (g : Pauli n).Z = 0) : gapHalf S g = 0 := by
  classical
  let bW := Module.finBasis (ZMod 2) (purXSupportSub S.L)
  have hgsupp : (g : Pauli n).X ∈ supportSpace S.L := Submodule.mem_map_of_mem g.2
  have hgpurX : (g : Pauli n).X ∈ (purX S.L).map xProjₗ :=
    Submodule.mem_map_of_mem (Submodule.mem_inf.mpr ⟨g.2, LinearMap.mem_ker.mpr hgZ⟩)
  have hmemW : (⟨(g : Pauli n).X, hgsupp⟩ : supportSpace S.L) ∈ purXSupportSub S.L := by
    unfold purXSupportSub; rw [Submodule.mem_comap]; exact hgpurX
  let gW : purXSupportSub S.L := ⟨⟨(g : Pauli n).X, hgsupp⟩, hmemW⟩
  let incl : purXSupportSub S.L →ₗ[ZMod 2] (Fin n → ZMod 2) :=
    (supportSpace S.L).subtype ∘ₗ (purXSupportSub S.L).subtype
  have hincl_basis : ∀ i, incl (bW i) = (encLift S (supportReindex S.L (Sum.inl i))).X := by
    intro i
    change ((bW i : supportSpace S.L) : Fin n → ZMod 2) = _
    rw [encLift_X, supportBasis_inl]
  have hreprX : (g : Pauli n).X
      = ∑ i, (bW.repr gW i) • (encLift S (supportReindex S.L (Sum.inl i))).X := by
    have hsr : incl gW = ∑ i, (bW.repr gW i) • incl (bW i) := by
      conv_lhs => rw [← Module.Basis.sum_repr bW gW]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul incl (bW.repr gW i) (bW i)
    have hg : incl gW = (g : Pauli n).X := rfl
    rw [hg] at hsr
    rw [hsr]
    exact Finset.sum_congr rfl fun i _ => by rw [hincl_basis]
  have hdecomp : (g : Pauli n)
      = ∑ i, (bW.repr gW i) • encLift S (supportReindex S.L (Sum.inl i)) := by
    apply Pauli.ext
    · rw [xProj_sum_smul]; exact hreprX
    · rw [zProj_sum_smul, hgZ]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [encLift_inl_Z, smul_zero]
  have hsub : g = ∑ i, (bW.repr gW i)
      • (⟨encLift S (supportReindex S.L (Sum.inl i)), encLift_mem S _⟩ : S.L) := by
    apply Subtype.ext
    rw [hdecomp, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [SetLike.val_smul]
  rw [hsub, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, gapHalf_encLift, smul_zero]

/-- **Dot-product solvability over `𝔽₂`.** A linear functional on `L` vanishing on the pure-`X`
part (`g.Z = 0`) is realized by a dot product `∑ g.Z i · x₀ i`: it factors through `g ↦ g.Z`,
extends to a functional on `𝔽₂ⁿ` (`LinearMap.exists_extend`, `ZMod 2` a field), and the standard dot
product is a perfect pairing. The linear-algebra core of `x₀`-existence. -/
theorem exists_dotZ2_eq (L : Submodule (ZMod 2) (Pauli n)) (φ : L →ₗ[ZMod 2] ZMod 2)
    (hker : ∀ g : L, (g : Pauli n).Z = 0 → φ g = 0) :
    ∃ x₀ : Fin n → ZMod 2, ∀ g : L, (∑ i, (g : Pauli n).Z i * x₀ i) = φ g := by
  classical
  let ζ : L →ₗ[ZMod 2] (Fin n → ZMod 2) := zProjₗ.comp L.subtype
  have hle : LinearMap.ker ζ ≤ LinearMap.ker φ := fun g hg =>
    LinearMap.mem_ker.mpr (hker g (LinearMap.mem_ker.mp hg))
  let ψ : (LinearMap.range ζ) →ₗ[ZMod 2] ZMod 2 :=
    ((LinearMap.ker ζ).liftQ φ hle).comp ζ.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Φ, hΦ⟩ := ψ.exists_extend
  have hdot : ∀ v : Fin n → ZMod 2, Φ v = ∑ i, v i * Φ (Pi.single i 1) := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hs : (Pi.single i (v i) : Fin n → ZMod 2) = v i • Pi.single i 1 := by
      funext j; by_cases h : i = j <;> simp [Pi.single_apply, h]
    rw [hs, map_smul, smul_eq_mul]
  refine ⟨fun i => Φ (Pi.single i 1 : Fin n → ZMod 2), fun g => ?_⟩
  have hζg : ζ g = (g : Pauli n).Z := rfl
  have key : Φ (ζ g) = φ g := by
    have e1 : Φ (ζ g) = ψ ⟨ζ g, LinearMap.mem_range_self ζ g⟩ := by
      have h := LinearMap.congr_fun hΦ ⟨ζ g, LinearMap.mem_range_self ζ g⟩
      simpa using h
    have e2 : ζ.quotKerEquivRange.symm ⟨ζ g, LinearMap.mem_range_self ζ g⟩
        = Submodule.Quotient.mk g := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (ζ.quotKerEquivRange_apply_mk g).symm
    rw [e1]
    change ((LinearMap.ker ζ).liftQ φ hle)
        (ζ.quotKerEquivRange.symm ⟨ζ g, LinearMap.mem_range_self ζ g⟩) = φ g
    rw [e2]
    rfl
  rw [hdot (ζ g)] at key
  rw [← key, hζg]

/-- **Syndrome-solvability**: a coset offset `x₀` realizing `S`'s decode (the `fromFloor_toFloor`
hypothesis). Equivalent to `S` having a consistent support coset; total over all `S` once the good
lifts make the syndrome system solvable. -/
def SyndromeSolvable (S : FramePureSignedStab n) : Prop :=
  ∃ x₀ : Fin n → ZMod 2,
    ∀ g ∈ S.L, chiOfE (encodeE S) g - 2 * ((zDot g x₀ : ℕ) : ZMod 4) = S.chi g

/-- **The bit functional + the solve ⟹ syndrome-solvability.** If `gapHalf S` vanishes on the
pure-`X` part of `L` (proved as `gapHalf_vanish_pureX`), `exists_dotZ2_eq` gives the offset `x₀` and
`two_mul_gapHalf_val` turns the dot product back into the gap. Reduces syndrome-solvability to the
hypothesis `hpureX`. -/
theorem syndromeSolvable_of (S : FramePureSignedStab n)
    (hpureX : ∀ g : S.L, (g : Pauli n).Z = 0 → gapHalf S g = 0) :
    SyndromeSolvable S := by
  obtain ⟨x₀, hx₀⟩ := exists_dotZ2_eq S.L (gapHalf S) hpureX
  refine ⟨x₀, fun g hg => ?_⟩
  have h2 : 2 * ((zDot g x₀ : ℕ) : ZMod 4) = chiOfE (encodeE S) g - S.chi g := by
    rw [two_mul_natCast_four, zDot_cast_two,
      show (∑ i, (g : Pauli n).Z i * x₀ i) = gapHalf S ⟨g, hg⟩ from hx₀ ⟨g, hg⟩]
    exact two_mul_gapHalf_val S ⟨g, hg⟩
  rw [h2]; ring

/-- **Syndrome-solvability, unconditional.** Every signed Lagrangian is syndrome-solvable, because
the adapted basis makes `gapHalf` vanish on the pure-`X` part (`gapHalf_vanish_pureX`). -/
theorem syndromeSolvable_all (S : FramePureSignedStab n) : SyndromeSolvable S :=
  syndromeSolvable_of S (fun g hg => gapHalf_vanish_pureX S g hg)

/-- `fromFloor` is **onto** (every signed Lagrangian is a decoded floor state). -/
theorem fromFloor_surjective :
    Function.Surjective (fromFloor : FloorKernel n → FramePureSignedStab n) := by
  intro S
  obtain ⟨x₀, hx₀⟩ := syndromeSolvable_all S
  exact ⟨toFloor S x₀, fromFloor_toFloor S x₀ hx₀⟩

/-- **The intrinsic floor correspondence, unconditional.** The floor representation modulo
the gauge orbit of the decode map is exactly the signed Lagrangian:
`FloorKernel / ker(fromFloor) ≃ FramePureSignedStab`. -/
noncomputable def floorChartEquiv :
    Quotient (Setoid.ker (fromFloor : FloorKernel n → FramePureSignedStab n))
      ≃ FramePureSignedStab n :=
  Setoid.quotientKerEquivOfSurjective _ fromFloor_surjective

end FTQCLib.Frame

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.BasedComplex

/-!
# Check: T43, based chain complexes over `𝔽₂`

T43.2's witness rows (`docs/STEPS.md`, the unit, phase 2) on the frozen statement of
`FTQCLib/CSS/BasedComplex.lean`. Every row is about an object a T43 headline names: the homology of
a complex (`cssOfComplex_logical_eq_homology`, `finrank_homology_tensor`), the Koszul complex's
boundary (`koszul_d_comp_d`), the relative complex's subcomplex (`relative_d_comp_d`) and the
condition `∂ ∘ ∂ = 0` of `BasedComplex`. No row uses a headline: each homology dimension is computed
from the definitions of `cycles`, `boundaries` and `homology`, by rank–nullity on the incidence
matrices and the quotient's dimension (`finrank_homology_add`, below), with each matrix's rank read
off by `decide` on its injectivity or surjectivity over `ZMod 2`.

The rows:

* **The `[3,1]` repetition code (agreement).** The two-term complex of the checks
  `Z₀Z₁, Z₁Z₂` (`repetitionChecks`) has homology of dimension `1` in degree `1`: the code's one
  logical bit, `dim ker H = 3 - 2`.
* **The hypergraph product of `[1 1]` with itself (agreement).** Tillich and Zémor's product has
  `k = 1`, computed from its own incidence matrices (`∂₁` of rank `2` onto two checks, `∂₂` of rank
  `2` from two checks, `5 - 2 - 2`), and Künneth's right-hand side at `n = 1`, computed from the
  factors' homology, is `1` too: `k₁ k₂ + k₁ᵀ k₂ᵀ = 1 · 1 + 0 · 0`.
* **The orientation (discriminating D1).** That product has `5` qubits; the same-oriented tensor of
  two two-term complexes of `[1 1]`, Li, Preskill and Xu's form, has `4` (docs/decisions/T43.md):
  `hypergraphProduct` is Tillich and Zémor's, not the same-oriented form, at this input.
* **The Koszul complex of `1 + x` on `ZMod 3` (agreement).** Its boundary `∂₁`, on the cells its
  enumeration names, is the check matrix of the cyclic repetition code on three bits
  (`cyclicRepetitionChecks`): check `g` reads bits `g` and `g - 1`.
* **The Koszul complex of `1 + x`, `∂ ∘ ∂ = 0` (agreement).** With one element there are no cells
  of degree `2`, so `∂₁ ∂₂ = 0` with no use of `koszul_d_comp_d`.
* **A cell set that is not a subcomplex (discriminating).** Bit `0` of the repetition code without
  its check `0`: no `Subcomplex` has these cells, so `relative` refuses it.
* **A precomplex with `∂ ∘ ∂ ≠ 0` (discriminating).** One cell in each degree and every incidence
  `1`: no `BasedComplex` has it as its precomplex.
* **The CSS pair is inhabited by a nontrivial example (inhabitation).** `cssOfComplex_isCSSPair`'s
  hypothesis is only `C : BasedComplex`; the `[3,1]` repetition code's complex at degree `1`
  satisfies it with its `X` check matrix nonzero, so the pair is not vacuously trivial.

No row reproduces an example or a table of the corpus papers.

Scope (standard 7.3): each row is about the one small complex it names and proves nothing about
others.

General facts a later step will need, stated privately here (they belong in
`FTQCLib.CSS.BasedComplex`): `boundaries_le_cycles` and `finrank_homology_add`.
-/

namespace FTQCLib.CSS.BasedComplexCheck

open FTQCLib.CSS Matrix

/-! ## Axiom sweep — every theorem of `FTQCLib.CSS.BasedComplex` -/

/-- info: 'FTQCLib.CSS.BasedChainMap.comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedChainMap.comm

/-- info: 'FTQCLib.CSS.BasedChainMap.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedChainMap.mk.inj

/-- info: 'FTQCLib.CSS.BasedChainMap.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedChainMap.mk.injEq

/-- info: 'FTQCLib.CSS.BasedChainMap.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedChainMap.mk.sizeOf_spec

/-- info: 'FTQCLib.CSS.BasedComplex.Subcomplex.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.Subcomplex.mk.inj

/-- info: 'FTQCLib.CSS.BasedComplex.Subcomplex.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.Subcomplex.mk.injEq

/-- info: 'FTQCLib.CSS.BasedComplex.Subcomplex.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.Subcomplex.mk.sizeOf_spec

/-- info: 'FTQCLib.CSS.BasedComplex.Subcomplex.support_boundary_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.Subcomplex.support_boundary_subset

/-- info: 'FTQCLib.CSS.BasedComplex.coboundary_mul_coboundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.coboundary_mul_coboundary

/-- info: 'FTQCLib.CSS.BasedComplex.dFrom_mul_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.dFrom_mul_d

/-- info: 'FTQCLib.CSS.BasedComplex.d_comp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.d_comp_d

/-- info: 'FTQCLib.CSS.BasedComplex.metacheckX_mul_cssX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.metacheckX_mul_cssX

/-- info: 'FTQCLib.CSS.BasedComplex.metacheckZ_mul_cssZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.metacheckZ_mul_cssZ

/-- info: 'FTQCLib.CSS.BasedComplex.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.mk.inj

/-- info: 'FTQCLib.CSS.BasedComplex.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.mk.injEq

/-- info: 'FTQCLib.CSS.BasedComplex.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.mk.sizeOf_spec

/-- info: 'FTQCLib.CSS.BasedComplex.sum_incidence_mul_incidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.sum_incidence_mul_incidence

/-- info: 'FTQCLib.CSS.BasedComplex.sum_sum_tensorIncidence_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.sum_sum_tensorIncidence_mul

/-- info: 'FTQCLib.CSS.BasedComplex.sum_tensorIncidence_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.sum_tensorIncidence_mul

/-- info: 'FTQCLib.CSS.BasedComplex.tensor_d_comp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedComplex.tensor_d_comp_d

/-- info: 'FTQCLib.CSS.BasedPrecomplex.incidence_eq_zero_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedPrecomplex.incidence_eq_zero_of_ne

/-- info: 'FTQCLib.CSS.BasedPrecomplex.mk.inj' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedPrecomplex.mk.inj

/-- info: 'FTQCLib.CSS.BasedPrecomplex.mk.injEq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedPrecomplex.mk.injEq

/-- info: 'FTQCLib.CSS.BasedPrecomplex.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.BasedPrecomplex.mk.sizeOf_spec

/-- info: 'FTQCLib.CSS.cssOfComplex_isCSSPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.cssOfComplex_isCSSPair

/-- info: 'FTQCLib.CSS.cssOfComplex_logical_eq_homology' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.cssOfComplex_logical_eq_homology

/-- info: 'FTQCLib.CSS.cssOfComplex_xLogical_eq_cohomology' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.cssOfComplex_xLogical_eq_cohomology

/-- info: 'FTQCLib.CSS.finrank_homology_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.finrank_homology_tensor

/-- info: 'FTQCLib.CSS.koszul_d_comp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.koszul_d_comp_d

/-- info: 'FTQCLib.CSS.mappingCone_d_comp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.mappingCone_d_comp_d

/-- info: 'FTQCLib.CSS.relative_d_comp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.relative_d_comp_d

/-- info: 'FTQCLib.CSS.sum_mul_sameCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.sum_mul_sameCell

/-- info: 'FTQCLib.CSS.sum_sameCell_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.CSS.sum_sameCell_mul

/-! ## Dimensions over `ZMod 2` -/

/-- The boundaries of a complex are cycles. -/
private theorem boundaries_le_cycles (C : BasedComplex) (i : ℕ) :
    C.boundaries i ≤ C.cycles i := by
  rintro v ⟨w, rfl⟩
  simp [BasedComplex.cycles, Matrix.mulVec_mulVec, C.dFrom_mul_d i]

/-- The dimension of the homology is that of the cycles less that of the boundaries. -/
private theorem finrank_homology_add (C : BasedComplex) (i : ℕ) :
    Module.finrank (ZMod 2) (C.homology i) + Module.finrank (ZMod 2) (C.boundaries i) =
      Module.finrank (ZMod 2) (C.cycles i) := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (boundaries_le_cycles C i))]
  exact Submodule.finrank_quotient_add_finrank _

/-- Rank–nullity for a matrix over `ZMod 2`. -/
private theorem finrank_range_add_finrank_ker {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) +
      Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  simpa only [Module.finrank_fin_fun] using h

/-- A surjective matrix has rank its number of rows. -/
private theorem finrank_range_of_surjective {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : ∀ w : Fin m → ZMod 2, ∃ v, M *ᵥ v = w) :
    Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = m := by
  have hr : LinearMap.range M.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    obtain ⟨v, hv⟩ := h w
    exact ⟨v, hv⟩
  rw [hr, finrank_top, Module.finrank_fin_fun]

/-- An injective matrix has rank its number of columns. -/
private theorem finrank_range_of_injective {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : ∀ v : Fin n → ZMod 2, M *ᵥ v = 0 → v = 0) :
    Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = n := by
  rw [LinearMap.finrank_range_of_inj, Module.finrank_fin_fun]
  intro v w hvw
  have hzero := h (v - w) (by simpa [Matrix.mulVec_sub, sub_eq_zero] using hvw)
  exact sub_eq_zero.mp hzero

/-- The homology of degree `i` from the ranks of the boundary out of degree `i` and into it. -/
private theorem finrank_homology_of_ranks (C : BasedComplex) (i : ℕ) {r_out r_in : ℕ}
    (h_out : Module.finrank (ZMod 2) (LinearMap.range (C.dFrom i).mulVecLin) = r_out)
    (h_in : Module.finrank (ZMod 2) (LinearMap.range (C.d i).mulVecLin) = r_in) :
    Module.finrank (ZMod 2) (C.homology i) = C.cells i - r_out - r_in := by
  have h_sum := finrank_homology_add C i
  have h_nullity := finrank_range_add_finrank_ker (C.dFrom i)
  change _ + Module.finrank (ZMod 2) (LinearMap.range (C.d i).mulVecLin) =
    Module.finrank (ZMod 2) (LinearMap.ker (C.dFrom i).mulVecLin) at h_sum
  omega

/-! ## The `[3,1]` repetition code -/

-- mutant: cssOfComplex_swap | FTQCLib/CSS/BasedComplex.lean | (C.dFrom i, (C.d i)ᵀ)
--   | (C.dFrom i, C.d i)
/-- The checks `Z₀Z₁` and `Z₁Z₂` of the `[3,1]` repetition code. -/
def repetitionChecks : Matrix (Fin 2) (Fin 3) (ZMod 2) :=
  !![1, 1, 0; 0, 1, 1]

-- row: agreement
theorem repetition_homology_one :
    Module.finrank (ZMod 2) ((BasedComplex.twoTerm repetitionChecks).homology 1) = 1 :=
  finrank_homology_of_ranks _ 1
    (finrank_range_of_surjective repetitionChecks (by decide))
    (finrank_range_of_injective ((BasedComplex.twoTerm repetitionChecks).d 1) (by decide))

/-! ## The hypergraph product of `[1 1]` with itself -/

/-- The check matrix `[1 1]`, the two-bit repetition code. -/
def pairChecks : Matrix (Fin 1) (Fin 2) (ZMod 2) :=
  !![1, 1]

/-- The two factors' homology, each dimension from its own incidence matrices: `[1 1]` has
`k = 1` and `kᵀ = 0`, its transpose `k = 0` and `kᵀ = 1`. -/
private theorem pair_factor_homology :
    Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecks).homology 0) = 0 ∧
      Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecks).homology 1) = 1 ∧
      Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecksᵀ).homology 0) = 1 ∧
      Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecksᵀ).homology 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finrank_homology_of_ranks _ 0
      (finrank_range_of_surjective ((BasedComplex.twoTerm pairChecks).dFrom 0) (by decide))
      (finrank_range_of_surjective pairChecks (by decide))
  · exact finrank_homology_of_ranks _ 1
      (finrank_range_of_surjective pairChecks (by decide))
      (finrank_range_of_injective ((BasedComplex.twoTerm pairChecks).d 1) (by decide))
  · exact finrank_homology_of_ranks _ 0
      (finrank_range_of_surjective ((BasedComplex.twoTerm pairChecksᵀ).dFrom 0) (by decide))
      (finrank_range_of_injective pairChecksᵀ (by decide))
  · exact finrank_homology_of_ranks _ 1
      (finrank_range_of_injective pairChecksᵀ (by decide))
      (finrank_range_of_injective ((BasedComplex.twoTerm pairChecksᵀ).d 1) (by decide))

-- row: agreement
theorem hypergraphProduct_pair_k_eq_kunneth :
    Module.finrank (ZMod 2) ((hypergraphProduct pairChecks pairChecks).homology 1) = 1 ∧
      ∑ p : Fin (1 + 1),
          Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecks).homology p) *
            Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecksᵀ).homology (1 - p)) =
        1 := by
  obtain ⟨h0, h1, h0T, h1T⟩ := pair_factor_homology
  refine ⟨?_, ?_⟩
  · have h := finrank_homology_of_ranks (hypergraphProduct pairChecks pairChecks) 1
      (finrank_range_of_surjective
        ((hypergraphProduct pairChecks pairChecks).dFrom 1) (by decide))
      (finrank_range_of_injective ((hypergraphProduct pairChecks pairChecks).d 1) (by decide))
    rw [h]
    decide
  · rw [Fin.sum_univ_two]
    change Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecks).homology 0) *
        Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecksᵀ).homology 1) +
      Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecks).homology 1) *
        Module.finrank (ZMod 2) ((BasedComplex.twoTerm pairChecksᵀ).homology 0) = 1
    rw [h0, h1, h0T, h1T]

-- row: discriminating D1
theorem hypergraphProduct_pair_qubits :
    (hypergraphProduct pairChecks pairChecks).cells 1 = 5 ∧
      ((BasedComplex.twoTerm pairChecks).tensor (BasedComplex.twoTerm pairChecks)).cells 1 = 4 := by
  decide

/-! ## The Koszul complex of `1 + x` on `ZMod 3` -/

/-- The cyclic group of order three, written multiplicatively. -/
abbrev CyclicThree : Type := Multiplicative (ZMod 3)

/-- The one element `1 + x` of `𝔽₂[ℤ₃]`, `x` the generator. -/
noncomputable def onePlusX : Fin 1 → MonoidAlgebra (ZMod 2) CyclicThree :=
  fun _ => 1 + MonoidAlgebra.of (ZMod 2) CyclicThree (Multiplicative.ofAdd 1)

/-- The cyclic repetition code on three bits: check `g` reads bits `g` and `g - 1`. -/
def cyclicRepetitionChecks : Matrix (ZMod 3) (ZMod 3) (ZMod 2) :=
  fun g h => if h = g ∨ h = g - 1 then 1 else 0

/-- The Koszul incidence of `1 + x` between a cell of degree `0` and one of degree `1`. -/
private theorem koszulIncidence_onePlusX (x : KoszulCell CyclicThree 1 0)
    (y : KoszulCell CyclicThree 1 1) :
    koszulIncidence onePlusX x y =
      cyclicRepetitionChecks (Multiplicative.toAdd x.2) (Multiplicative.toAdd y.2) := by
  obtain ⟨⟨S, hS⟩, g⟩ := x
  obtain ⟨⟨T, hT⟩, h⟩ := y
  have hS_empty : S = ∅ := Finset.card_eq_zero.mp hS
  have hT_single : T = {0} := by
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hT
    rw [Subsingleton.elim a 0]
  subst hS_empty hT_single
  simp only [koszulIncidence, Finset.sum_singleton, Finset.erase_singleton, if_true, onePlusX,
    MonoidAlgebra.of_apply, MonoidAlgebra.one_def, MonoidAlgebra.coe_add, Pi.add_apply,
    MonoidAlgebra.single_apply]
  revert g h
  decide

-- row: agreement
theorem koszul_onePlusX_d_zero (σ : Fin ((koszul CyclicThree onePlusX).cells 0))
    (τ : Fin ((koszul CyclicThree onePlusX).cells 1)) :
    (koszul CyclicThree onePlusX).d 0 σ τ =
      cyclicRepetitionChecks (Multiplicative.toAdd (koszulCellEquiv CyclicThree 1 0 σ).2)
        (Multiplicative.toAdd (koszulCellEquiv CyclicThree 1 1 τ).2) :=
  koszulIncidence_onePlusX _ _

-- row: agreement
theorem koszul_onePlusX_d_comp_d :
    (koszul CyclicThree onePlusX).d 0 * (koszul CyclicThree onePlusX).d 1 = 0 := by
  ext σ ρ
  exact Fin.elim0 (by simpa [koszul] using ρ)

/-! ## The CSS pair is inhabited by a nontrivial example -/

-- row: inhabitation
theorem repetition_cssOfComplex_isCSSPair_nontrivial :
    IsCSSPair (cssOfComplex (BasedComplex.twoTerm repetitionChecks) 1).1
        (cssOfComplex (BasedComplex.twoTerm repetitionChecks) 1).2 ∧
      (cssOfComplex (BasedComplex.twoTerm repetitionChecks) 1).1 ≠ 0 :=
  ⟨cssOfComplex_isCSSPair _ 1, by decide⟩

/-! ## Refusals -/

/-- Bit `0` of the repetition code, without its check `0`. -/
def bitWithoutCheck : ∀ i, Finset (Fin ((BasedComplex.twoTerm repetitionChecks).cells i))
  | 1 => {⟨0, by decide⟩}
  | _ => ∅

-- row: discriminating
theorem bitWithoutCheck_not_subcomplex :
    ¬ ∃ A : (BasedComplex.twoTerm repetitionChecks).Subcomplex, A.cellSet = bitWithoutCheck := by
  rintro ⟨A, hA⟩
  have h_mem := A.support_boundary_subset 0 ⟨0, by decide⟩ ⟨0, by decide⟩
    (by rw [hA]; decide) (by decide)
  rw [hA] at h_mem
  exact absurd h_mem (by decide)

/-- One cell in each degree and every incidence `1`: `∂ ∘ ∂ = 1 ≠ 0`. -/
def allOnesPrecomplex : BasedPrecomplex where
  cells _ := 1
  d _ := 1

-- row: discriminating
theorem allOnesPrecomplex_not_complex :
    ¬ ∃ C : BasedComplex, C.toBasedPrecomplex = allOnesPrecomplex := by
  rintro ⟨⟨P, h_comp⟩, rfl⟩
  have h_entry := congrFun (congrFun (h_comp 0) ⟨0, by decide⟩) ⟨0, by decide⟩
  exact absurd h_entry (by decide)

end FTQCLib.CSS.BasedComplexCheck

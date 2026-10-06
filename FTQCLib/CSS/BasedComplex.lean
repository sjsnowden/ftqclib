/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Kunneth
import FTQCLib.CSS.StabilizerCode
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Finset.Sort

/-!
# Based chain complexes over `𝔽₂`

A *based* chain complex has a finite set of cells in each degree, `Fin (c i)`; its chains in
degree `i` are `Fin (c i) → ZMod 2`, and its boundary from degree `i + 1` to degree `i` is an
incidence matrix `Matrix (Fin (c i)) (Fin (c (i + 1))) (ZMod 2)`, with `∂ ∘ ∂ = 0`. Complexes are
graded by `ℕ` and have any length: one of length `L` has no cells above degree `L`. Every
construction here names the cells of what it builds from the cells it is given: the CSS pair, the
tensor product, the Koszul complex, the relative complex and the mapping cone.

## Main definitions

* `FTQCLib.CSS.BasedPrecomplex`: cells and incidence matrices, without `∂ ∘ ∂ = 0`. The Koszul,
  relative and mapping-cone constructions produce one, and their `_d_comp_d` theorems make it a
  `BasedComplex`, as `⟨koszul G f, koszul_d_comp_d G f⟩`.
* `FTQCLib.CSS.BasedComplex`: a based precomplex with `∂ ∘ ∂ = 0`.
* `BasedComplex.cycles`, `BasedComplex.boundaries`, `BasedComplex.homology` and its dimension
  `BasedComplex.betti`.
* `BasedComplex.coboundary`, `cocycles`, `coboundaries`, `cohomology`: cochains as the transposed
  complex, the coboundary `δ^i = ∂_{i+1}ᵀ`.
* `FTQCLib.CSS.cssOfComplex C i`: the CSS pair at degree `i`, with qubits on the cells of degree
  `i`, `H_X = ∂_i` (rows the cells of degree `i - 1`) and `H_Z = ∂_{i+1}ᵀ` (rows the cells of
  degree `i + 1`); the metachecks `BasedComplex.metacheckX` one degree down and
  `BasedComplex.metacheckZ` one degree up.
* `BasedComplex.tensor`: the tensor product, its cells in degree `n` the pairs of a cell of degree
  `p ≤ n` and a cell of degree `n - p`.
* `FTQCLib.CSS.hypergraphProduct H₁ H₂`: Tillich and Zémor's hypergraph product, the tensor product
  of the two-term complex of `H₁` with that of `H₂ᵀ`.
* `FTQCLib.CSS.koszul G f`: the Koszul complex of `f₁, …, f_t` in `MonoidAlgebra (ZMod 2) G`, `G` a
  finite abelian group, its cells in degree `i` a set of `i` of the `f_j` and a group element.
* `FTQCLib.CSS.relative C A`: the chains of `C` modulo those of a subcomplex `A`, on the cells
  outside `A`.
* `FTQCLib.CSS.mappingCone φ`: the mapping cone of a chain map `φ : C → D`, its cells in degree `i`
  those of `D` of degree `i` and those of `C` of degree `i - 1`.

## Main statements

* `cssOfComplex_isCSSPair`: the CSS pair of a complex satisfies `H_X H_Zᵀ = 0`.
* `cssOfComplex_logical_eq_homology`: its `cssZLogical` is the homology at that degree, and
  through `CSS/StabilizerCode.lean`'s dictionary its nontrivial `Z`-logical operators are the
  cycles that are not boundaries.
* `cssOfComplex_xLogical_eq_cohomology`: its `cssXLogical` is the cohomology at that degree.
* `BasedComplex.metacheckX_mul_cssX`, `BasedComplex.metacheckZ_mul_cssZ`: the metachecks
  annihilate the checks.
* `BasedComplex.tensor_d_comp_d`: the tensor product is a complex.
* `finrank_homology_tensor`: Künneth over the field `ZMod 2`, on dimensions.
* `koszul_d_comp_d`, `relative_d_comp_d`, `mappingCone_d_comp_d`: the Koszul complex, the
  relative complex and the mapping cone are complexes.

## Implementation notes

Signs: over `ZMod 2` every sign of the tensor product, the Koszul complex and the mapping cone is
`1`.

Enumerations: a cell set is `Fin (c i)`, so each construction fixes an enumeration of the cells it
names. The tensor product enumerates its pairs by `finSigmaFinEquiv` and `finProdFinEquiv`, the
relative complex its cells in increasing order, the mapping cone by `finSumFinEquiv`; all are
computable. The Koszul complex enumerates its cells by `Fintype.equivFin`, a choice: its homology,
the `k` of its CSS pairs, and its codes up to a permutation of qubits do not depend on it.

The relative boundary is the incidence matrix restricted to the rows and the columns of the cells
outside `A`, the boundary of the quotient, and not `∂` restricted to their span, which need not
land in it.

The hypergraph product of `H₁ : 𝔽₂^{n₁} → 𝔽₂^{m₁}` and `H₂ : 𝔽₂^{n₂} → 𝔽₂^{m₂}` is Tillich and
Zémor's: the tensor product of the two-term complex of `H₁` with that of `H₂ᵀ`. Its qubits in degree
one are the `n₁ n₂ + m₁ m₂` pairs, and its `k` is `k₁ k₂ + k₁ᵀ k₂ᵀ`, with `k = dim ker H` and
`kᵀ = dim ker Hᵀ`, by `finrank_homology_tensor` at `n = 1`. The tensor product of the two two-term
complexes oriented the same way is Tillich and Zémor's product of `H₁` and `H₂ᵀ`
(docs/fidelity/T43.md, Claim 25; docs/STEPS.md, entry 2026-10-03i).

## References

The multicycle paper (Mian, Gwilliam and Krastanov) for homology, cohomology, the CSS complex, its
metachecks and the Koszul complex; the tricycle paper (Jacob, McLauchlan and Browne) for the
tensor product of three two-term complexes and its boundaries. Each citation stands above the
declaration that states it. Künneth, the relative complex and the mapping cone are sourced outside
this target's papers, in docs/fidelity/T43.md (Claims 3, 9, 23 and 24).
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli FTQCLib.Stabilizer Matrix

/-! ### Based precomplexes and complexes -/

/-- A **based precomplex** over `ZMod 2`: `cells i` cells in each degree `i : ℕ`, and for each `i`
the incidence matrix `d i` of the boundary `∂_{i+1}` from degree `i + 1` to degree `i`, its
`(σ, τ)` entry `1` when the cell `σ` is in the boundary of the cell `τ`. The condition
`∂ ∘ ∂ = 0` is not part of it: see `BasedComplex`. -/
structure BasedPrecomplex where
  /-- The number of cells in each degree; the cells of degree `i` are `Fin (cells i)`. -/
  cells : ℕ → ℕ
  /-- The incidence matrix of the boundary `∂_{i+1}` from degree `i + 1` to degree `i`. -/
  d : ∀ i, Matrix (Fin (cells i)) (Fin (cells (i + 1))) (ZMod 2)

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:ha3614be386d9
/-- A **based chain complex** over `ZMod 2`: a based precomplex whose boundary squares to zero,
`∂_{i+1} ∘ ∂_{i+2} = 0` in every degree. The source's complexes are of `𝔽₂`-vector spaces; a
based complex is one with a finite basis fixed in each degree, its cells. -/
structure BasedComplex extends BasedPrecomplex where
  /-- `∂ ∘ ∂ = 0`. -/
  d_comp_d : ∀ i, d i * d (i + 1) = 0

namespace BasedPrecomplex

variable (P : BasedPrecomplex)

/-- The chains of degree `i`: a coefficient in `ZMod 2` for each cell. -/
abbrev Chains (i : ℕ) : Type := Fin (P.cells i) → ZMod 2

/-- The number of cells one degree below `i`: those of degree `i - 1`, none below degree `0`. -/
abbrev cellsBelow : ℕ → ℕ
  | 0 => 0
  | i + 1 => P.cells i

/-- The incidence matrix of the boundary `∂_i` out of degree `i`, into degree `i - 1`; it has no
rows out of degree `0`. -/
def dFrom : ∀ i, Matrix (Fin (P.cellsBelow i)) (Fin (P.cells i)) (ZMod 2)
  | 0 => 0
  | i + 1 => P.d i

/-- The incidence between a cell `σ` of degree `a` and a cell `τ` of degree `b`: the entry of
`d a` when `b = a + 1`, and `0` otherwise. -/
def incidence (a b : ℕ) (σ : Fin (P.cells a)) (τ : Fin (P.cells b)) : ZMod 2 :=
  if h : b = a + 1 then P.d a σ (Fin.cast (congrArg P.cells h) τ) else 0

theorem incidence_eq_zero_of_ne {a b : ℕ} (h : b ≠ a + 1) (σ : Fin (P.cells a))
    (τ : Fin (P.cells b)) : P.incidence a b σ τ = 0 := by
  simp [incidence, h]

end BasedPrecomplex

/-- `1` when a cell `σ` of degree `a` and a cell `τ` of degree `b`, of a cell set counted by `c`,
are the same cell, and `0` otherwise. -/
def sameCell (c : ℕ → ℕ) (a b : ℕ) (σ : Fin (c a)) (τ : Fin (c b)) : ZMod 2 :=
  if a = b ∧ (σ : ℕ) = τ then 1 else 0

/-- A sum against `sameCell` in its second slot picks out the cell itself. -/
theorem sum_sameCell_mul (c : ℕ → ℕ) (a b : ℕ) (σ : Fin (c a))
    (g : ∀ b, Fin (c b) → ZMod 2) :
    ∑ τ : Fin (c b), sameCell c a b σ τ * g b τ = if a = b then g a σ else 0 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single σ]
    · simp [sameCell]
    · intro τ _ hτ
      have hne : ¬ ((σ : ℕ) = τ) := fun e => hτ (Fin.ext e).symm
      simp [sameCell, hne]
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun τ _ => by simp [sameCell, h]

/-- A sum against `sameCell` in its first slot picks out the cell itself. -/
theorem sum_mul_sameCell (c : ℕ → ℕ) (a b : ℕ) (τ : Fin (c b))
    (g : ∀ a, Fin (c a) → ZMod 2) :
    ∑ σ : Fin (c a), g a σ * sameCell c a b σ τ = if a = b then g b τ else 0 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single τ]
    · simp [sameCell]
    · intro σ _ hσ
      have hne : ¬ ((σ : ℕ) = τ) := fun e => hσ (Fin.ext e)
      simp [sameCell, hne]
    · simp
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun σ _ => by simp [sameCell, h]

namespace BasedComplex

variable (C : BasedComplex)

/-- `∂_i ∘ ∂_{i+1} = 0`, with the boundary out of degree `i`. -/
theorem dFrom_mul_d (i : ℕ) : C.dFrom i * C.d i = 0 := by
  cases i with
  | zero => exact Matrix.zero_mul _
  | succ i => exact C.d_comp_d i

/-- `∂ ∘ ∂ = 0` read on cells of any degrees `a`, `b`, `e`. -/
theorem sum_incidence_mul_incidence (a b e : ℕ) (σ : Fin (C.cells a)) (ρ : Fin (C.cells e)) :
    ∑ τ : Fin (C.cells b), C.incidence a b σ τ * C.incidence b e τ ρ = 0 := by
  by_cases hb : b = a + 1
  · subst hb
    by_cases he : e = a + 1 + 1
    · subst he
      have h := congrFun (congrFun (C.d_comp_d a) σ) ρ
      simpa [BasedPrecomplex.incidence, Matrix.mul_apply] using h
    · exact Finset.sum_eq_zero fun τ _ => by
        rw [C.incidence_eq_zero_of_ne he, mul_zero]
  · exact Finset.sum_eq_zero fun τ _ => by rw [C.incidence_eq_zero_of_ne hb, zero_mul]

/-! ### Homology and cohomology -/

/-- The cycles of degree `i`: the kernel of the boundary `∂_i` out of degree `i`. -/
def cycles (i : ℕ) : Submodule (ZMod 2) (Fin (C.cells i) → ZMod 2) :=
  LinearMap.ker (C.dFrom i).mulVecLin

/-- The boundaries of degree `i`: the image of the boundary `∂_{i+1}` into degree `i`. -/
def boundaries (i : ℕ) : Submodule (ZMod 2) (Fin (C.cells i) → ZMod 2) :=
  LinearMap.range (C.d i).mulVecLin

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:hf1b881305057
/-- The **homology** of degree `i`, `H_i = Z_i / B_i`: the cycles modulo the boundaries among
them. -/
abbrev homology (i : ℕ) : Type :=
  C.cycles i ⧸ (C.boundaries i).comap (C.cycles i).subtype

/-- The dimension of the homology of degree `i` over `ZMod 2`: the `i`-th Betti number over
`𝔽₂`. -/
noncomputable def betti (i : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (C.homology i)

/-- The coboundary `δ^i` from the cochains of degree `i` to those of degree `i + 1`: the
transposed incidence matrix `∂_{i+1}ᵀ`. -/
def coboundary (i : ℕ) : Matrix (Fin (C.cells (i + 1))) (Fin (C.cells i)) (ZMod 2) :=
  (C.d i)ᵀ

/-- `δ ∘ δ = 0`: the transposed complex is a cochain complex. -/
theorem coboundary_mul_coboundary (i : ℕ) : C.coboundary (i + 1) * C.coboundary i = 0 := by
  rw [coboundary, coboundary, ← Matrix.transpose_mul, C.d_comp_d, Matrix.transpose_zero]

/-- The cocycles of degree `i`: the kernel of the coboundary `δ^i`. -/
def cocycles (i : ℕ) : Submodule (ZMod 2) (Fin (C.cells i) → ZMod 2) :=
  LinearMap.ker (C.coboundary i).mulVecLin

/-- The coboundaries of degree `i`: the image of the coboundary `δ^{i-1} = ∂_iᵀ` into degree `i`;
none in degree `0`. -/
def coboundaries (i : ℕ) : Submodule (ZMod 2) (Fin (C.cells i) → ZMod 2) :=
  LinearMap.range (C.dFrom i)ᵀ.mulVecLin

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:hfc5c43cb947b
/-- The **cohomology** of degree `i`, `H^i = Z^i / B^i`. -/
abbrev cohomology (i : ℕ) : Type :=
  C.cocycles i ⧸ (C.coboundaries i).comap (C.cocycles i).subtype

/-! ### The CSS pair and its metachecks -/

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 definition:h36fdfec92730
/-- The metacheck matrix of the `X`-checks at degree `i`, `M_X = ∂_{i-1}`: from the `X`-checks,
the cells of degree `i - 1`, to the cells of degree `i - 2`; it has no rows where `i - 2` is
negative. The source places qubits in degree `1` of a complex reaching degree `-1`; here degrees
start at `0`, so a code with both metachecks puts its qubits in degree `2` or above. -/
def metacheckX : ∀ i, Matrix (Fin (C.cellsBelow (i - 1))) (Fin (C.cellsBelow i)) (ZMod 2)
  | 0 => 0
  | i + 1 => C.dFrom i

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 definition:h36fdfec92730
/-- The metacheck matrix of the `Z`-checks at degree `i`, `M_Z = ∂_{i+2}ᵀ`: from the `Z`-checks,
the cells of degree `i + 1`, to the cells of degree `i + 2`. The cited definition writes `∂_4ᵀ`
for its complex `C_{-1} ← ⋯ ← C_3` with qubits in degree `1`, whose last boundary is `∂_3`; this
is `∂_{i+2}` at `i = 1`. -/
def metacheckZ (i : ℕ) : Matrix (Fin (C.cells (i + 2))) (Fin (C.cells (i + 1))) (ZMod 2) :=
  (C.d (i + 1))ᵀ

end BasedComplex

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879
--   equation:eqn: CSS as chain complex
/-- The **CSS pair of a complex at degree `i`**: qubits on the cells of degree `i`, the `X`-check
matrix `H_X = ∂_i` with a row for each cell of degree `i - 1`, and the `Z`-check matrix
`H_Z = ∂_{i+1}ᵀ` with a row for each cell of degree `i + 1`. This is the cited CSS chain complex
`P_X = ∂_1`, `P_Z = ∂_2ᵀ`, at any degree. The multicycle paper's MM codes take the transposed
orientation of their Koszul complex (`P_X = ∂_qᵀ`), which is this pair at degree `q` of the
complex read backwards. -/
def cssOfComplex (C : BasedComplex) (i : ℕ) :
    Matrix (Fin (C.cellsBelow i)) (Fin (C.cells i)) (ZMod 2) ×
      Matrix (Fin (C.cells (i + 1))) (Fin (C.cells i)) (ZMod 2) :=
  (C.dFrom i, (C.d i)ᵀ)

/-- The CSS pair of a complex satisfies the CSS condition `H_X H_Zᵀ = ∂_i ∂_{i+1} = 0`. -/
theorem cssOfComplex_isCSSPair (C : BasedComplex) (i : ℕ) :
    IsCSSPair (cssOfComplex C i).1 (cssOfComplex C i).2 := by
  rw [IsCSSPair, cssOfComplex, Matrix.transpose_transpose]
  exact C.dFrom_mul_d i

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:ha0c05405fd36
/-- **The logical space of a complex's CSS pair is its homology.** The `Z`-logical space
`cssZLogical` of the CSS pair at degree `i` is the homology of degree `i`; and, through
`CSS/StabilizerCode.lean`'s dictionary (`nontrivial_Zlogical_iff_homology`), a `Z`-Pauli on the
cells of degree `i` is a nontrivial logical operator, in the normalizer of the stabilizer and not
in it, exactly when its support is a cycle that is not a boundary. -/
theorem cssOfComplex_logical_eq_homology (C : BasedComplex) (i : ℕ) :
    cssZLogical (cssOfComplex C i).1 (cssOfComplex C i).2 = C.homology i ∧
      ∀ v : Fin (C.cells i) → ZMod 2,
        ((⟨0, v⟩ : Pauli (C.cells i)) ∈
              normalizer (cssStabilizer (cssOfComplex C i).1 (cssOfComplex C i).2) ∧
            (⟨0, v⟩ : Pauli (C.cells i)) ∉
              cssStabilizer (cssOfComplex C i).1 (cssOfComplex C i).2) ↔
          (v ∈ C.cycles i ∧ v ∉ C.boundaries i) :=
  -- `H_Zᵀ = (∂_{i+1}ᵀ)ᵀ` is `∂_{i+1}` by definition, so the carrier and the subspace of the
  -- dictionary are the cycles and the boundaries as they stand.
  ⟨rfl, fun v => nontrivial_Zlogical_iff_homology (cssOfComplex C i).1 (cssOfComplex C i).2 v⟩

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:h6761befd553c
/-- The `X`-logical space `cssXLogical` of the CSS pair at degree `i` is the cohomology of degree
`i`, `ker ∂_{i+1}ᵀ / im ∂_iᵀ`. -/
theorem cssOfComplex_xLogical_eq_cohomology (C : BasedComplex) (i : ℕ) :
    cssXLogical (cssOfComplex C i).1 (cssOfComplex C i).2 = C.cohomology i :=
  rfl

namespace BasedComplex

variable (C : BasedComplex)

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:h6f29d919d5b8
/-- The `X`-metachecks annihilate the `X`-checks: `M_X H_X = ∂_{i-1} ∂_i = 0`. -/
theorem metacheckX_mul_cssX (i : ℕ) : C.metacheckX i * (cssOfComplex C i).1 = 0 := by
  cases i with
  | zero => exact Matrix.zero_mul _
  | succ i => exact C.dFrom_mul_d i

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:h6f29d919d5b8
/-- The `Z`-metachecks annihilate the `Z`-checks:
`M_Z H_Z = ∂_{i+2}ᵀ ∂_{i+1}ᵀ = (∂_{i+1} ∂_{i+2})ᵀ = 0`. -/
theorem metacheckZ_mul_cssZ (i : ℕ) : C.metacheckZ i * (cssOfComplex C i).2 = 0 := by
  rw [metacheckZ, cssOfComplex, ← Matrix.transpose_mul, C.d_comp_d, Matrix.transpose_zero]

end BasedComplex

/-! ### The tensor product -/

namespace BasedPrecomplex

variable (C D : BasedPrecomplex)

/-- The cells of `C ⊗ D` in degree `n`, as pairs: a degree `p ≤ n`, a cell of `C` of degree `p`,
and a cell of `D` of degree `n - p`. -/
abbrev TensorCell (n : ℕ) : Type :=
  Σ p : Fin (n + 1), Fin (C.cells p) × Fin (D.cells (n - p))

/-- The number of cells of `C ⊗ D` in degree `n`, `∑_{p ≤ n} c_p c'_{n-p}`. -/
def tensorCells (n : ℕ) : ℕ :=
  ∑ p : Fin (n + 1), C.cells p * D.cells (n - p)

/-- The enumeration of the pairs of cells of degree `n`. -/
def tensorCellEquiv (n : ℕ) : C.TensorCell D n ≃ Fin (C.tensorCells D n) :=
  (Equiv.sigmaCongrRight fun _ => finProdFinEquiv).trans finSigmaFinEquiv

/-- The incidence of `C ⊗ D` between a pair of degree `n` and a pair of degree `n + 1`, from
`∂(σ ⊗ τ) = ∂σ ⊗ τ + σ ⊗ ∂τ`. -/
def tensorIncidence (n : ℕ) (x : C.TensorCell D n) (y : C.TensorCell D (n + 1)) : ZMod 2 :=
  C.incidence x.1 y.1 x.2.1 y.2.1 * sameCell D.cells (n - x.1) (n + 1 - y.1) x.2.2 y.2.2 +
    sameCell C.cells x.1 y.1 x.2.1 y.2.1 * D.incidence (n - x.1) (n + 1 - y.1) x.2.2 y.2.2

-- source: papers/qldpc_architecture/
-- Jacob_McLauchlan_Browne_2025_trivariate_tricycle_2508.08191 equation:eqn:chain_complex
-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:hb65d24061c3d
/-- The **tensor product** of two based precomplexes: in degree `n` the cells are the pairs of a
cell of degree `p ≤ n` and a cell of degree `n - p`, `(C ⊗ D)_n = ⊕_{p+q=n} C_p ⊗ D_q`, and the
boundary is `∂(σ ⊗ τ) = ∂σ ⊗ τ + σ ⊗ ∂τ`. The cited units take the product of two or three
two-term complexes over a group algebra; this is the product over `ZMod 2` of any two. -/
def tensor : BasedPrecomplex where
  cells := C.tensorCells D
  d n := Matrix.reindex (C.tensorCellEquiv D n) (C.tensorCellEquiv D (n + 1))
    (Matrix.of (C.tensorIncidence D n))

end BasedPrecomplex

/-- Four products of double sums. -/
private theorem sum_sum_expand {α β : Type*} [Fintype α] [Fintype β]
    (a a' e e' : α → ZMod 2) (b b' g g' : β → ZMod 2) :
    ∑ s, ∑ t, (a s * b t + e s * g t) * (a' s * b' t + e' s * g' t) =
      (∑ s, a s * a' s) * (∑ t, b t * b' t) + (∑ s, a s * e' s) * (∑ t, b t * g' t) +
        (∑ s, e s * a' s) * (∑ t, g t * b' t) + (∑ s, e s * e' s) * (∑ t, g t * g' t) := by
  simp only [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  ring

namespace BasedComplex

variable (C D : BasedComplex)

/-- The terms of `∂ ∘ ∂` on `C ⊗ D` through the pairs whose first cell has degree `q`: the terms
`∂σ ⊗ ∂τ`, once through `∂σ ⊗ τ` (when `q` is the degree of `∂σ`) and once through `σ ⊗ ∂τ` (when
`q` is the degree of `σ`); the terms `∂∂σ ⊗ τ` and `σ ⊗ ∂∂τ` vanish. -/
theorem sum_sum_tensorIncidence_mul (n : ℕ) (x : C.TensorCell D.toBasedPrecomplex n)
    (z : C.TensorCell D.toBasedPrecomplex (n + 1 + 1)) (q : Fin (n + 1 + 1)) :
    ∑ s : Fin (C.cells q), ∑ t : Fin (D.cells (n + 1 - q)),
        C.tensorIncidence D.toBasedPrecomplex n x ⟨q, s, t⟩ *
          C.tensorIncidence D.toBasedPrecomplex (n + 1) ⟨q, s, t⟩ z =
      (if (q : ℕ) = z.1 ∧ n - x.1 = n + 1 - q then
          C.incidence x.1 z.1 x.2.1 z.2.1 *
            D.incidence (n - x.1) (n + 1 + 1 - z.1) x.2.2 z.2.2
        else 0) +
      (if (x.1 : ℕ) = q ∧ n + 1 - q = n + 1 + 1 - z.1 then
          C.incidence x.1 z.1 x.2.1 z.2.1 *
            D.incidence (n - x.1) (n + 1 + 1 - z.1) x.2.2 z.2.2
        else 0) := by
  obtain ⟨p, σ, τ⟩ := x
  obtain ⟨r, σ', τ'⟩ := z
  simp only [BasedPrecomplex.tensorIncidence]
  rw [sum_sum_expand, C.sum_incidence_mul_incidence, D.sum_incidence_mul_incidence,
    sum_mul_sameCell C.cells q r σ' (fun b s => C.incidence p b σ s),
    sum_sameCell_mul D.cells (n - p) (n + 1 - q) τ
      (fun b t => D.incidence b (n + 1 + 1 - r) t τ'),
    sum_sameCell_mul C.cells p q σ (fun b s => C.incidence b r s σ'),
    sum_mul_sameCell D.cells (n + 1 - q) (n + 1 + 1 - r) τ'
      (fun b t => D.incidence (n - p) b τ t)]
  rw [zero_mul, mul_zero, zero_add, add_zero]
  congr 1 <;> split_ifs <;> simp_all

/-- `∂ ∘ ∂ = 0` on `C ⊗ D`, entrywise on pairs of cells: each term `∂σ ⊗ ∂τ` arises twice. -/
theorem sum_tensorIncidence_mul (n : ℕ) (x : C.TensorCell D.toBasedPrecomplex n)
    (z : C.TensorCell D.toBasedPrecomplex (n + 1 + 1)) :
    ∑ y, C.tensorIncidence D.toBasedPrecomplex n x y *
      C.tensorIncidence D.toBasedPrecomplex (n + 1) y z = 0 := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, C.sum_sum_tensorIncidence_mul D n x z,
    Finset.sum_add_distrib]
  obtain ⟨p, σ, τ⟩ := x
  obtain ⟨r, σ', τ'⟩ := z
  dsimp only
  by_cases hr : (r : ℕ) = p + 1
  · rw [Finset.sum_eq_single ⟨p + 1, by omega⟩, Finset.sum_eq_single ⟨p, by omega⟩]
    · rw [if_pos (by simp; omega), if_pos (by simp; omega)]
      exact CharTwo.add_self_eq_zero _
    · intro q _ hq
      rw [if_neg]
      intro h
      exact hq (Fin.ext (by simp; omega))
    · simp
    · intro q _ hq
      rw [if_neg]
      intro h
      exact hq (Fin.ext (by simp; omega))
    · simp
  · simp [C.incidence_eq_zero_of_ne hr]

/-- **The tensor product of two complexes is a complex.** -/
theorem tensor_d_comp_d (n : ℕ) :
    (C.tensor D.toBasedPrecomplex).d n * (C.tensor D.toBasedPrecomplex).d (n + 1) = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  simp only [BasedPrecomplex.tensor, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.of_apply]
  refine (Fintype.sum_equiv (C.tensorCellEquiv D.toBasedPrecomplex (n + 1)).symm _
    (fun y => C.tensorIncidence D.toBasedPrecomplex n _ y *
      C.tensorIncidence D.toBasedPrecomplex (n + 1) y _) fun _ => rfl).trans ?_
  exact C.sum_tensorIncidence_mul D n _ _

/-- The **tensor product** of two based complexes, `BasedPrecomplex.tensor` with
`∂ ∘ ∂ = 0`. -/
def tensor : BasedComplex where
  toBasedPrecomplex := C.toBasedPrecomplex.tensor D.toBasedPrecomplex
  d_comp_d := C.tensor_d_comp_d D

/-- The **two-term complex** of a check matrix `H : 𝔽₂^n → 𝔽₂^m`: its `n` bits are the cells of
degree `1`, its `m` checks the cells of degree `0`, and its one boundary is `H`. -/
def twoTerm {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : BasedComplex where
  cells
    | 0 => m
    | 1 => n
    | _ + 2 => 0
  d
    | 0 => H
    | _ + 1 => 0
  d_comp_d
    | 0 => Matrix.mul_zero _
    | _ + 1 => Matrix.zero_mul _

end BasedComplex

/-! ### Künneth over `ZMod 2`

The proof of `finrank_homology_tensor` is the field case of Künneth (docs/fidelity/T43.md, Claim 9),
argued on dimensions with `CSS/Kunneth.lean`: each complex, its boundary cut at `N = n + 2`
(`truncD`), is a deformation retract of cells with no boundary (`Kunneth.exists_splitting`); on all
the cells of degree below `N` the Kronecker product of the two retracts is a retract of the tensor
boundary (`Kunneth.kronecker_retract`), which counts the cycles of `C ⊗ D` in degree `n`
(`Kunneth.finrank_cyclesIn_of_retract`); and the homology of a based complex is that of the graded
model of its cells (`finrank_homology_add_of_model`).
-/

section Kunneth

open Kunneth
open scoped Kronecker

/-- The homology has the dimension of the cycles less that of the boundaries. -/
private theorem finrank_homology_add_finrank_boundaries (B : BasedComplex) (n : ℕ) :
    Module.finrank (ZMod 2) (B.homology n) + Module.finrank (ZMod 2) (B.boundaries n) =
      Module.finrank (ZMod 2) (B.cycles n) := by
  have hle : B.boundaries n ≤ B.cycles n := by
    rintro _ ⟨w, rfl⟩
    rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, B.dFrom_mul_d, Matrix.zero_mulVec]
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)]
  exact Submodule.finrank_quotient_add_finrank _

/-- The homology of a based complex in degree `n` from a graded model of its cells of degrees up
to `n + 1`. -/
private theorem finrank_homology_add_of_model (B : BasedComplex) (n : ℕ) {ι : Type*} [Fintype ι]
    (δ : ι → ℕ) (d : Matrix ι ι (ZMod 2)) (hd : IsGraded δ δ 1 d)
    (e : ∀ k, k ≤ n + 1 → Fin (B.cells k) → ι) (he : ∀ k hk, Function.Injective (e k hk))
    (hr : ∀ k hk x, (∃ σ, e k hk σ = x) ↔ δ x = k)
    (hent : ∀ k (hk : k ≤ n) σ τ, d (e k (by omega) σ) (e (k + 1) (by omega) τ) = B.d k σ τ) :
    Module.finrank (ZMod 2) (B.homology n) + Module.finrank (ZMod 2) (boundariesIn δ d n) =
      Module.finrank (ZMod 2) (cyclesIn δ d n) := by
  obtain ⟨h1, h2⟩ : Module.finrank (ZMod 2) (B.cycles n) =
        Module.finrank (ZMod 2) (cyclesIn δ d n) ∧
      Module.finrank (ZMod 2) (B.boundaries n) =
        Module.finrank (ZMod 2) (boundariesIn δ d n) := by
    cases n with
    | zero =>
      exact finrank_cycles_boundaries_eq_of_embedding δ d hd 0 (B.dFrom 0) (B.d 0)
        (fun σ => Fin.elim0 σ) (e 0 (by omega)) (e 1 (by omega)) (fun σ => Fin.elim0 σ)
        (he _ _) (he _ _)
        (fun x => ⟨fun ⟨σ, _⟩ => Fin.elim0 σ, fun h => by omega⟩) (hr _ _) (hr _ _)
        (fun σ => Fin.elim0 σ) (hent 0 le_rfl)
    | succ j =>
      exact finrank_cycles_boundaries_eq_of_embedding δ d hd (j + 1) (B.dFrom (j + 1))
        (B.d (j + 1)) (e j (by omega)) (e (j + 1) (by omega)) (e (j + 2) (by omega))
        (he _ _) (he _ _) (he _ _)
        (fun x => by rw [hr]; omega) (hr _ _) (hr _ _) (hent j (by omega)) (hent (j + 1) le_rfl)
  rw [← h1, ← h2]
  exact finrank_homology_add_finrank_boundaries B n

/-- The identity on all the cells of degree below `N` is `sameCell`. -/
private theorem one_allCells_apply_eq_sameCell {c : ℕ → ℕ} {N : ℕ} (x y : AllCells c N) :
    (1 : Matrix (AllCells c N) (AllCells c N) (ZMod 2)) x y = sameCell c x.1 y.1 x.2 y.2 := by
  obtain ⟨i, σ⟩ := x
  obtain ⟨j, τ⟩ := y
  rw [Matrix.one_apply, sameCell]
  by_cases h : (i : ℕ) = j ∧ (σ : ℕ) = τ
  · rw [if_pos (allCells_mk_eq_mk_iff.2 h), if_pos h]
  · rw [if_neg (fun e => h (allCells_mk_eq_mk_iff.1 e)), if_neg h]

/-- The boundary of `C` with no boundary out of degree `N - 1` or above. -/
private def truncD (C : BasedComplex) (N : ℕ) (i : ℕ) :
    Matrix (Fin (C.cells i)) (Fin (C.cells (i + 1))) (ZMod 2) :=
  if i + 1 < N then C.d i else 0

/-- The cut boundary squares to zero. -/
private theorem truncD_mul (C : BasedComplex) (N i : ℕ) :
    truncD C N i * truncD C N (i + 1) = 0 := by
  unfold truncD
  split_ifs <;> simp [C.d_comp_d]

/-- The cut boundary vanishes out of degree `N - 1` and above. -/
private theorem truncD_top (C : BasedComplex) (N a : ℕ) (h : N ≤ a + 1) : truncD C N a = 0 := by
  rw [truncD, if_neg (by omega)]

/-- Below degree `N` the cut boundary's incidences are `C`'s. -/
private theorem incidenceEntry_truncD (C : BasedComplex) (N : ℕ) {a b : ℕ} (hb : b < N)
    (σ : Fin (C.cells a)) (τ : Fin (C.cells b)) :
    incidenceEntry C.cells (truncD C N) a b σ τ = C.incidence a b σ τ := by
  unfold incidenceEntry BasedPrecomplex.incidence
  split_ifs with h
  · subst h
    rw [truncD, if_pos hb]
  · rfl

/-- **The dimension of the homology of `C` from a splitting** of its boundary cut at `N`, in each
degree `p` with `p + 1 < N`. -/
private theorem finrank_homology_of_splitting (C : BasedComplex) (N : ℕ) {h : ℕ → ℕ}
    {f : ∀ i, Matrix (Fin (h i)) (Fin (C.cells i)) (ZMod 2)}
    {g : ∀ i, Matrix (Fin (C.cells i)) (Fin (h i)) (ZMod 2)}
    {s : ∀ i, Matrix (Fin (C.cells (i + 1))) (Fin (C.cells i)) (ZMod 2)}
    (hs : IsSplitting C.cells (truncD C N) h f g s) (p : ℕ) (hp : p + 1 < N) :
    Module.finrank (ZMod 2) (C.homology p) = h p := by
  obtain ⟨h1, h2, h3, h4⟩ := allCells_identities_of_splitting hs N (truncD_top C N)
  have hret := finrank_cyclesIn_of_retract (fun x : AllCells C.cells N => (x.1 : ℕ))
    (fun a : AllCells h N => (a.1 : ℕ)) (allBoundary C.cells (truncD C N) N)
    (allRaise C.cells s N) (allBlock f N) (allBlock g N) (allBoundary_isGraded _ _ N)
    (allRaise_isGraded _ _ N) (allBlock_isGraded _ N)
    (allBlock_isGraded _ N) (allBoundary_mul_allBoundary _ (truncD_mul C N)) h1 h2 h3 h4 p
  have hbr := finrank_homology_add_of_model C p (fun x : AllCells C.cells N => (x.1 : ℕ))
    (allBoundary C.cells (truncD C N) N) (allBoundary_isGraded _ _ N)
    (fun k hk => degreeEmbedding C.cells N k (by omega))
    (fun k hk => degreeEmbedding_injective _ N k _)
    (fun k hk => exists_degreeEmbedding_eq_iff _ N k _) (fun k hk _ _ => by
      simp only [degreeEmbedding, allBoundary, Matrix.of_apply]
      rw [incidenceEntry_truncD C N (by omega)]
      simp [BasedPrecomplex.incidence])
  have hcard : Fintype.card {a : AllCells h N // (a.1 : ℕ) = p} = h p := by
    rw [card_subtype_of_embedding _ (degreeEmbedding h N p (by omega))
      (degreeEmbedding_injective _ N p _) (exists_degreeEmbedding_eq_iff _ N p _), Fintype.card_fin]
  omega

/-- The boundary of the tensor product of the two cut complexes on pairs of cells is that of
`C ⊗ D`. -/
private theorem kronecker_pairEmbedding (C D : BasedComplex) (N k : ℕ) (hk : k + 1 < N)
    (x : C.TensorCell D.toBasedPrecomplex k) (y : C.TensorCell D.toBasedPrecomplex (k + 1)) :
    (allBoundary C.cells (truncD C N) N ⊗ₖ 1 + 1 ⊗ₖ allBoundary D.cells (truncD D N) N :
          Matrix (AllCells C.cells N × AllCells D.cells N) (AllCells C.cells N × AllCells D.cells N)
            (ZMod 2))
        (pairEmbedding C.cells D.cells N k (by omega) x)
        (pairEmbedding C.cells D.cells N (k + 1) hk y) =
      C.tensorIncidence D.toBasedPrecomplex k x y := by
  obtain ⟨p, σ, τ⟩ := x
  obtain ⟨q, σ', τ'⟩ := y
  have := q.isLt
  simp only [Matrix.add_apply, kroneckerMap_apply, pairEmbedding, allBoundary, Matrix.of_apply,
    one_allCells_apply_eq_sameCell, BasedPrecomplex.tensorIncidence]
  rw [incidenceEntry_truncD C N (by omega), incidenceEntry_truncD D N (by omega)]

/-- **The dimension of the homology of `C ⊗ D` from splittings** of the two boundaries cut at
`N`, in each degree `n` with `n + 1 < N`. -/
private theorem finrank_homology_tensor_of_splitting (C D : BasedComplex) (N : ℕ) {h h' : ℕ → ℕ}
    {f : ∀ i, Matrix (Fin (h i)) (Fin (C.cells i)) (ZMod 2)}
    {g : ∀ i, Matrix (Fin (C.cells i)) (Fin (h i)) (ZMod 2)}
    {s : ∀ i, Matrix (Fin (C.cells (i + 1))) (Fin (C.cells i)) (ZMod 2)}
    {f' : ∀ i, Matrix (Fin (h' i)) (Fin (D.cells i)) (ZMod 2)}
    {g' : ∀ i, Matrix (Fin (D.cells i)) (Fin (h' i)) (ZMod 2)}
    {s' : ∀ i, Matrix (Fin (D.cells (i + 1))) (Fin (D.cells i)) (ZMod 2)}
    (hs : IsSplitting C.cells (truncD C N) h f g s)
    (hs' : IsSplitting D.cells (truncD D N) h' f' g' s') (n : ℕ) (hn : n + 1 < N) :
    Module.finrank (ZMod 2) ((C.tensor D).homology n) = ∑ p : Fin (n + 1), h p * h' (n - p) := by
  obtain ⟨h1, h2, h3, h4⟩ := allCells_identities_of_splitting hs N (truncD_top C N)
  obtain ⟨h1', h2', h3', h4'⟩ := allCells_identities_of_splitting hs' N (truncD_top D N)
  obtain ⟨k1, k2, k3, k4, k5⟩ := kronecker_retract
    (allBoundary_mul_allBoundary _ (truncD_mul C N)) h1 h2 h3 h4
    (allBoundary_mul_allBoundary _ (truncD_mul D N)) h1' h2' h3' h4'
  have hdT := (allBoundary_isGraded C.cells (truncD C N) N).kronecker
    (IsGraded.one (fun x : AllCells D.cells N => (x.1 : ℕ))) (add_zero 1) |>.add
    ((IsGraded.one (fun x : AllCells C.cells N => (x.1 : ℕ))).kronecker
      (allBoundary_isGraded D.cells (truncD D N) N) (zero_add 1))
  have hST := (allRaise_isGraded C.cells s N).kronecker
    (IsGraded.one (fun x : AllCells D.cells N => (x.1 : ℕ))) (add_zero (-1)) |>.add
    (((allBlock_isGraded g N).mul (allBlock_isGraded f N) (add_zero 0)).kronecker
      (allRaise_isGraded D.cells s' N) (zero_add (-1)))
  have hFT := (allBlock_isGraded f N).kronecker (allBlock_isGraded f' N) (add_zero 0)
  have hGT := (allBlock_isGraded g N).kronecker (allBlock_isGraded g' N) (add_zero 0)
  have hret := finrank_cyclesIn_of_retract _ _ _ _ _ _ hdT hST hFT hGT k1 k2 k3 k4 k5 n
  have hbr := finrank_homology_add_of_model (C.tensor D) n
    (fun z : AllCells C.cells N × AllCells D.cells N => (z.1.1 : ℕ) + z.2.1) _ hdT
    (fun k hk i => pairEmbedding C.cells D.cells N k (by omega)
      ((C.tensorCellEquiv D.toBasedPrecomplex k).symm i))
    (fun k hk => (pairEmbedding_injective _ _ N k (by omega)).comp (Equiv.injective _))
    (fun k hk z => by
      rw [← exists_pairEmbedding_eq_iff C.cells D.cells N k (by omega) z]
      exact ⟨fun ⟨i, hi⟩ => ⟨_, hi⟩, fun ⟨x, hx⟩ =>
        ⟨C.tensorCellEquiv D.toBasedPrecomplex k x, by
          dsimp only
          rw [Equiv.symm_apply_apply, hx]⟩⟩)
    (fun k hk _ _ => kronecker_pairEmbedding C D N k (by omega) _ _)
  have hcard : Fintype.card {z : AllCells h N × AllCells h' N // (z.1.1 : ℕ) + z.2.1 = n} =
      ∑ p : Fin (n + 1), h p * h' (n - p) := by
    rw [card_subtype_of_embedding _ (pairEmbedding h h' N n (by omega))
      (pairEmbedding_injective _ _ N n _) (exists_pairEmbedding_eq_iff _ _ N n _),
      Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
  have := hret.symm.trans hbr.symm
  rw [hcard] at this
  omega

end Kunneth

/-- **Künneth over the field `ZMod 2`, on dimensions.** The homology of `C ⊗ D` in degree `n` has
dimension `∑_{p ≤ n} dim H_p(C) · dim H_{n-p}(D)`. Known for complexes of finite-dimensional
vector spaces over a field (docs/fidelity/T43.md, Claim 9); at `n = 1` on the hypergraph product
it gives `k = k₁ k₂ + k₁ᵀ k₂ᵀ`. -/
theorem finrank_homology_tensor (C D : BasedComplex) (n : ℕ) :
    Module.finrank (ZMod 2) ((C.tensor D).homology n) =
      ∑ p : Fin (n + 1),
        Module.finrank (ZMod 2) (C.homology p) *
          Module.finrank (ZMod 2) (D.homology (n - p)) := by
  obtain ⟨h, f, g, s, hs⟩ :=
    Kunneth.exists_splitting C.cells (truncD C (n + 2)) (truncD_mul C (n + 2))
  obtain ⟨h', f', g', s', hs'⟩ :=
    Kunneth.exists_splitting D.cells (truncD D (n + 2)) (truncD_mul D (n + 2))
  rw [finrank_homology_tensor_of_splitting C D (n + 2) hs hs' n (by omega)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.isLt
  rw [finrank_homology_of_splitting C (n + 2) hs p (by omega),
    finrank_homology_of_splitting D (n + 2) hs' (n - p) (by omega)]

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 equation:h2c83a6a0405b
/-- The **hypergraph product** of check matrices `H₁` and `H₂`, Tillich and Zémor's: the tensor
product of the two-term complex of `H₁` with that of `H₂ᵀ`. In degree `1` its cells are the
`n₁ n₂ + m₁ m₂` pairs of two bits or of two checks, its CSS pair at degree `1` is the hypergraph
product code, and its `k = k₁ k₂ + k₁ᵀ k₂ᵀ` comes from the factors' by `finrank_homology_tensor`.
The cited unit is a tensor product of two-term complexes over a group algebra on one cell each;
the tensor of the two two-term complexes oriented the same way is Li, Preskill and Xu's product,
which is this one taken of `H₁` and `H₂ᵀ` (docs/fidelity/T43.md, Claim 25; docs/STEPS.md, entry
2026-10-03i). -/
def hypergraphProduct {m₁ n₁ m₂ n₂ : ℕ} (H₁ : Matrix (Fin m₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin m₂) (Fin n₂) (ZMod 2)) : BasedComplex :=
  (BasedComplex.twoTerm H₁).tensor (BasedComplex.twoTerm H₂ᵀ)

/-! ### The Koszul complex over `𝔽₂[G]` -/

/-- A cell of the Koszul complex of `f₁, …, f_t` in degree `i`: a set of `i` of the indices of the
`f_j`, the wedge `e_S`, and a group element, a basis vector of `𝔽₂[G]`. -/
abbrev KoszulCell (G : Type*) (t i : ℕ) : Type _ :=
  {S : Finset (Fin t) // S.card = i} × G

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 statement:h8355a2085423
/-- The enumeration of the Koszul cells of degree `i`: there are `(t choose i) · |G|` of them, the
rank `t choose i` over `𝔽₂[G]` times the dimension `|G|` of `𝔽₂[G]` over `𝔽₂`. -/
noncomputable def koszulCellEquiv (G : Type*) [Fintype G] (t i : ℕ) :
    Fin (t.choose i * Fintype.card G) ≃ KoszulCell G t i :=
  (finCongr (by simp [Fintype.card_finset_len])).trans (Fintype.equivFin (KoszulCell G t i)).symm

/-- The incidence of the Koszul complex between a cell `(S, g)` of degree `i` and a cell `(T, h)`
of degree `i + 1`: the coefficient of `g` in `f_j · h` when `S = T \ {j}`, that is `f_j (g h⁻¹)`,
and `0` when `S` is not `T` less one index. -/
def koszulIncidence {G : Type*} [CommGroup G] {t i : ℕ} (f : Fin t → MonoidAlgebra (ZMod 2) G)
    (x : KoszulCell G t i) (y : KoszulCell G t (i + 1)) : ZMod 2 :=
  ∑ j ∈ y.1.1, if y.1.1.erase j = x.1.1 then f j (x.2 * y.2⁻¹) else 0

-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 definition:h94c22a275338
-- source: papers/qldpc_architecture/
-- Mian_Gwilliam_Krastanov_2026_multivariate_multicycle_2601.18879 definition:eq:explicit_formula
/-- The **Koszul complex** of `f₁, …, f_t` in the group algebra `MonoidAlgebra (ZMod 2) G` of a
finite abelian group `G`: in degree `i` the free module on the wedges `e_S`, `|S| = i`, with
`∂ e_T = ∑_{j ∈ T} f_j e_{T \ {j}}` (every sign `1` over `𝔽₂`), the tensor product of the
complexes `R ← R` given by the `f_j`. Its cells in degree `i` are the pairs of a set `S` of `i`
indices and a group element (`KoszulCell`), enumerated by `koszulCellEquiv`. The cited units state
it over any commutative ring `R`, and the MM codes over `𝔽₂[x₁, …, x_D]/⟨x_k^{ℓ_k} - 1⟩`, which
is `𝔽₂[G]` for `G = ℤ_{ℓ₁} × ⋯ × ℤ_{ℓ_D}`; here `R = 𝔽₂[G]` for any finite abelian `G`. The toric
codes (`f_j = 1 + x_j`), the bivariate bicycle, the trivariate tricycle and the multicycle codes
are instances (remark:thm:koszul_tensor, remark:mm:4dtoric of the same paper). -/
noncomputable def koszul (G : Type*) [CommGroup G] [Fintype G] {t : ℕ}
    (f : Fin t → MonoidAlgebra (ZMod 2) G) : BasedPrecomplex where
  cells i := t.choose i * Fintype.card G
  d i := Matrix.of fun σ τ =>
    koszulIncidence f (koszulCellEquiv G t i σ) (koszulCellEquiv G t (i + 1) τ)

/-- The coefficient of `g k⁻¹` in `f_j f_l`, as a sum over the middle group element `h`: the
term of `∂ ∘ ∂` from `(S, g)` to `(U, k)` that removes `l` first and then `j`. -/
private def koszulPair {G : Type*} [CommGroup G] [Fintype G] {t : ℕ}
    (f : Fin t → MonoidAlgebra (ZMod 2) G) (g k : G) (j l : Fin t) : ZMod 2 :=
  ∑ h : G, f j (g * h⁻¹) * f l (h * k⁻¹)

/-- The two orders of removing `j` and `l` give the same coefficient, `f_j f_l = f_l f_j`: the
middle element `h` of one is `g k h⁻¹` of the other, which needs `G` commutative. -/
private theorem koszulPair_comm {G : Type*} [CommGroup G] [Fintype G] {t : ℕ}
    (f : Fin t → MonoidAlgebra (ZMod 2) G) (g k : G) (j l : Fin t) :
    koszulPair f g k j l = koszulPair f g k l j := by
  unfold koszulPair
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft (g * k))) _ _ fun h => ?_
  have h1 : g * (g * k * h⁻¹)⁻¹ = h * k⁻¹ := by
    rw [_root_.mul_inv_rev, inv_inv, _root_.mul_inv_rev, ← mul_assoc, mul_comm g h, mul_assoc h g,
      mul_left_comm g k⁻¹ g⁻¹, mul_inv_cancel, mul_one]
  have h2 : g * k * h⁻¹ * k⁻¹ = g * h⁻¹ := by
    rw [mul_right_comm, mul_inv_cancel_right]
  rw [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft, h1, h2, mul_comm]

/-- A sum over ordered pairs of distinct elements of a symmetric function vanishes over `ZMod 2`:
the pairs `(l, j)` and `(j, l)` cancel. -/
private theorem sum_sum_erase_eq_zero {α : Type*} [DecidableEq α] (U : Finset α)
    (ψ : α → α → ZMod 2) (hψ : ∀ a b, ψ a b = ψ b a) :
    ∑ l ∈ U, ∑ j ∈ U.erase l, ψ l j = 0 := by
  simp only [← Finset.filter_ne' U, Finset.sum_filter]
  rw [← Finset.sum_product' (s := U) (t := U) (fun l j => if j ≠ l then ψ l j else 0)]
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p _ hp => ?_)
    (fun p hp => Finset.mem_product.2 ⟨(Finset.mem_product.1 hp).2, (Finset.mem_product.1 hp).1⟩)
    (fun p _ => Prod.swap_swap p)
  · by_cases h : p.2 = p.1
    · rw [Prod.fst_swap, Prod.snd_swap, if_neg (not_not.2 h), if_neg (not_not.2 h.symm),
        add_zero]
    · rw [Prod.fst_swap, Prod.snd_swap, if_pos h, if_pos (Ne.symm h), hψ p.2 p.1]
      exact CharTwo.add_self_eq_zero _
  · intro hs
    apply hp
    have h : p.2 = p.1 := (congrArg Prod.fst hs : _)
    rw [if_neg (not_not.2 h)]

/-- The terms of `∂ ∘ ∂` from `(S, g)` of degree `i` to `(U, k)` of degree `i + 2`: through the
cell `(U \ {l}, h)` for each `l ∈ U` and `h`, and then removing `j` from `U \ {l}`. -/
private theorem sum_koszulIncidence_mul_eq {G : Type*} [CommGroup G] [Fintype G] {t i : ℕ}
    (f : Fin t → MonoidAlgebra (ZMod 2) G) (x : KoszulCell G t i)
    (z : KoszulCell G t (i + 1 + 1)) :
    ∑ y : KoszulCell G t (i + 1), koszulIncidence f x y * koszulIncidence f y z =
      ∑ l ∈ z.1.1, ∑ j ∈ z.1.1.erase l,
        if (z.1.1.erase l).erase j = x.1.1 then koszulPair f x.2 z.2 j l else 0 := by
  unfold koszulIncidence
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hcard : (z.1.1.erase l).card = i + 1 := by
    rw [Finset.card_erase_of_mem hl, z.1.2]
    rfl
  rw [Fintype.sum_prod_type, Finset.sum_eq_single_of_mem ⟨z.1.1.erase l, hcard⟩
    (Finset.mem_univ _)]
  · dsimp only
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · exact Finset.sum_eq_zero fun h _ => zero_mul _
  · intro T _ hT
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg fun e => hT (Subtype.ext e.symm), mul_zero]

/-- `∂ ∘ ∂ = 0` on the Koszul cells: each term removing `l` then `j` cancels the term removing `j`
then `l`. -/
private theorem sum_koszulIncidence_mul {G : Type*} [CommGroup G] [Fintype G] {t i : ℕ}
    (f : Fin t → MonoidAlgebra (ZMod 2) G) (x : KoszulCell G t i)
    (z : KoszulCell G t (i + 1 + 1)) :
    ∑ y : KoszulCell G t (i + 1), koszulIncidence f x y * koszulIncidence f y z = 0 := by
  rw [sum_koszulIncidence_mul_eq]
  refine sum_sum_erase_eq_zero z.1.1 _ fun a b => ?_
  rw [Finset.erase_right_comm, koszulPair_comm]

-- source: papers/qldpc_architecture/
-- Jacob_McLauchlan_Browne_2025_trivariate_tricycle_2508.08191 equation:eqn:del_3
/-- **The Koszul complex is a complex**: `∂ ∘ ∂ = 0`, since `f_j f_k = f_k f_j` in the commutative
group algebra and the two orders of removing `j` and `k` cancel over `𝔽₂`. -/
theorem koszul_d_comp_d (G : Type*) [CommGroup G] [Fintype G] {t : ℕ}
    (f : Fin t → MonoidAlgebra (ZMod 2) G) (i : ℕ) :
    (koszul G f).d i * (koszul G f).d (i + 1) = 0 := by
  ext σ ρ
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine (Equiv.sum_comp (koszulCellEquiv G t (i + 1)) fun y =>
    koszulIncidence f (koszulCellEquiv G t i σ) y *
      koszulIncidence f y (koszulCellEquiv G t (i + 1 + 1) ρ)).trans ?_
  exact sum_koszulIncidence_mul f _ _

/-! ### The relative complex -/

/-- A **subcomplex** of a based complex spanned by cells: a set of cells in each degree containing
the support of the boundary of each of its cells. -/
structure BasedComplex.Subcomplex (C : BasedComplex) where
  /-- The cells of the subcomplex in each degree. -/
  cellSet : ∀ i, Finset (Fin (C.cells i))
  /-- The boundary of a cell of the subcomplex is supported on cells of the subcomplex. -/
  support_boundary_subset : ∀ i (σ : Fin (C.cells (i + 1))) (τ : Fin (C.cells i)),
    σ ∈ cellSet (i + 1) → C.d i τ σ ≠ 0 → τ ∈ cellSet i

/-- The cells of degree `i` outside the subcomplex `A`, in increasing order. -/
def BasedComplex.Subcomplex.otherCell {C : BasedComplex} (A : C.Subcomplex) (i : ℕ) :
    Fin (A.cellSet i)ᶜ.card ↪o Fin (C.cells i) :=
  (A.cellSet i)ᶜ.orderEmbOfFin rfl

/-- The **relative complex** of a based complex `C` and a subcomplex `A`: the chains of `C` modulo
those of `A`. Its cells are the cells of `C` outside `A`, and its boundary is `C`'s incidence
matrix on their rows and columns, the boundary of the quotient. -/
def relative (C : BasedComplex) (A : C.Subcomplex) : BasedPrecomplex where
  cells i := (A.cellSet i)ᶜ.card
  d i := (C.d i).submatrix (A.otherCell i) (A.otherCell (i + 1))

/-- A sum over the cells outside `A`, enumerated by `otherCell`, is the sum over the complement. -/
private theorem sum_otherCell {C : BasedComplex} (A : C.Subcomplex) (i : ℕ)
    (g : Fin (C.cells i) → ZMod 2) :
    ∑ b, g (A.otherCell i b) = ∑ τ ∈ (A.cellSet i)ᶜ, g τ := by
  have h := Finset.sum_map Finset.univ ((A.cellSet i)ᶜ.orderEmbOfFin rfl).toEmbedding g
  rw [Finset.map_orderEmbOfFin_univ] at h
  exact h.symm

/-- **The relative complex is a complex**: a term of `∂ ∘ ∂` through a cell of `A` starts from a
cell of `A`, by `support_boundary_subset`, so it is not a term between cells outside `A`. -/
theorem relative_d_comp_d (C : BasedComplex) (A : C.Subcomplex) (i : ℕ) :
    (relative C A).d i * (relative C A).d (i + 1) = 0 := by
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine (sum_otherCell A (i + 1) fun τ =>
    C.d i (A.otherCell i a) τ * C.d (i + 1) τ (A.otherCell (i + 1 + 1) c)).trans ?_
  have hA : ∑ τ ∈ A.cellSet (i + 1),
      C.d i (A.otherCell i a) τ * C.d (i + 1) τ (A.otherCell (i + 1 + 1) c) = 0 := by
    refine Finset.sum_eq_zero fun τ hτ => ?_
    by_contra h
    have hmem := A.support_boundary_subset i τ _ hτ (left_ne_zero_of_mul h)
    exact Finset.mem_compl.1 ((A.cellSet i)ᶜ.orderEmbOfFin_mem rfl a) hmem
  have hfull := congrFun (congrFun (C.d_comp_d i) (A.otherCell i a)) (A.otherCell (i + 1 + 1) c)
  rw [Matrix.mul_apply, Matrix.zero_apply, ← Finset.sum_compl_add_sum (A.cellSet (i + 1)), hA,
    add_zero] at hfull
  exact hfull

/-! ### The mapping cone -/

/-- A **chain map** `φ : C → D` of based complexes: for each degree `i` the matrix of
`φ_i : C_i → D_i`, commuting with the boundaries, `∂^D_{i+1} φ_{i+1} = φ_i ∂^C_{i+1}`. -/
structure BasedChainMap (C D : BasedComplex) where
  /-- The matrix of `φ_i`, a row for each cell of `D` of degree `i`. -/
  f : ∀ i, Matrix (Fin (D.cells i)) (Fin (C.cells i)) (ZMod 2)
  /-- `φ` commutes with the boundaries. -/
  comm : ∀ i, D.d i * f (i + 1) = f i * C.d i

/-- The **mapping cone** of a chain map `φ : C → D`: in degree `i` its cells are the disjoint union
of those of `D` of degree `i` and those of `C` of degree `i - 1`, and its boundary is the block
matrix `(∂^D, φ; 0, ∂^C)`, every sign `1` over `𝔽₂`. -/
def mappingCone {C D : BasedComplex} (φ : BasedChainMap C D) : BasedPrecomplex where
  cells i := D.cells i + C.cellsBelow i
  d i := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (D.d i) (φ.f i) 0 (C.dFrom i))

/-- **The mapping cone is a complex**: the diagonal blocks of `∂ ∘ ∂` are `∂^D ∂^D` and
`∂^C ∂^C`, and its corner is `∂^D φ + φ ∂^C`, zero over `𝔽₂` since `φ` is a chain map. -/
theorem mappingCone_d_comp_d {C D : BasedComplex} (φ : BasedChainMap C D) (i : ℕ) :
    (mappingCone φ).d i * (mappingCone φ).d (i + 1) = 0 := by
  have hC : C.dFrom (i + 1) = C.d i := rfl
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (D.d i) (φ.f i) 0 (C.dFrom i)) *
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (D.d (i + 1)) (φ.f (i + 1)) 0 (C.dFrom (i + 1))) = 0
  have hself : φ.f i * C.d i + φ.f i * C.d i = 0 := by
    ext a b
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, hC, D.d_comp_d, φ.comm, hself, C.dFrom_mul_d, Matrix.mul_zero,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero, add_zero, add_zero,
    Matrix.fromBlocks_zero]
  rfl

end FTQCLib.CSS

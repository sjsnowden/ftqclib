/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.BasedComplex
import FTQCLib.CSS.SurfaceCodeDistance

/-!
# The toric and planar surface codes

The toric code of Dennis, Kitaev, Landahl and Preskill is the CSS pair, at degree `1`, of the
`L × L` square lattice on the torus: qubits on the `2L²` edges (links), an `X` check for each vertex
(site) on the edges that meet it, and a `Z` check for each face (plaquette) on the edges it
contains. Here it is `cssOfComplex (torusComplex L) 1`, so its stabilizers, logical operators and
syndromes are those of `CSS/StabilizerCode.lean`'s dictionary through
`cssOfComplex_logical_eq_homology` (T43). The planar code is the CSS pair at degree `1` of T43's
relative complex: the `L × (L + 1)` grid of vertices modulo its top and bottom rows, the rough
boundaries.

## Main definitions

* `FTQCLib.CSS.torusComplex L`: the torus as a based complex, its cells `ZMod L × ZMod L` (vertices
  and faces) and `Fin 2 × (ZMod L × ZMod L)` (edges), its boundaries the incidences
  `torusVertexEdge` and `torusEdgeFace` counted mod 2.
* `FTQCLib.CSS.toricCode L`: its CSS pair at degree `1`, `H_X = ∂₁` and `H_Z = ∂₂ᵀ`.
* `FTQCLib.CSS.torusKoszul L`: T43's Koszul complex of `f_i = 1 + x_i`, `i = 0, 1`, on
  `𝔽₂[ZMod L × ZMod L]`, and the cell maps `torusVertexCell`, `torusEdgeCell`, `torusFaceCell`
  that index its cells by the group's elements.
* `FTQCLib.CSS.toricGens L`: every star and every plaquette but those of the point `0`.
* `FTQCLib.CSS.gridComplex L`, `FTQCLib.CSS.roughBoundary L`, `FTQCLib.CSS.planarComplex L`,
  `FTQCLib.CSS.planarCode L`: the grid, its top and bottom rows as a subcomplex, the relative
  complex and its CSS pair at degree `1`.
* `FTQCLib.CSS.planarGens L`: every star and every plaquette of the patch.
* `torusRowLoop`, `torusDualLoop`, `planarZString`, `planarXString`: a logical operator of each type
  and weight `L` on each code.
* `FTQCLib.CSS.CorrectsUpToBoundary`: the decoding problem. The syndrome of an error is its image
  under the checks, the boundary of the error chain; a decoder returns a chain with that syndrome;
  it is correct on the error when the correction plus the error is a boundary, a trivial cycle.

## Main statements

* `toricCode_eq_koszul`: the torus's two check matrices are the Koszul complex's at degree `1`,
  with the cells matched by the cell maps.
* `toricCode_k`, `planarCode_k`: `k = 2` on the torus and `k = 1` on the patch.
* `toricCode_distance`, `planarCode_distance`: for each check type, every nontrivial cycle has
  weight at least `L`, and the named string of that type is a nontrivial cycle of weight `L`.
* `toricCode_independentGens`, `planarCode_independentGens`: the generating sets T29's encoder
  needs, linearly independent and generating the stabilizer; on the torus all the stars sum to
  zero, and so do all the plaquettes.

## How the review question is answered

* The toric code is `cssOfComplex (torusComplex L) 1`, the CSS pair of the torus's vertex–edge and
  edge–face incidence; `toricCode_eq_koszul` equates both its check matrices with those of T43's
  `koszul` for `f_i = 1 + x_i` (`torusPolynomial`), each cell sent to the Koszul cell named by the
  same group element (`(∅, g)`, `({j}, g)`, `({0, 1}, g)`).
* `d = L` is stated for both check types, on the torus (`toricCode_distance`) and on the patch
  (`planarCode_distance`): `Z` type as cycles that are not boundaries, `X` type as cocycles that are
  not coboundaries (the dual lattice); `k = 2` is `toricCode_k` and `k = 1` is `planarCode_k`.
* The decoding problem is `CorrectsUpToBoundary`: correction plus error in the range of the
  boundary. On either code, `Z` errors are decoded with `check = H_X` and `boundary = H_Zᵀ`, where
  the range is `boundaries 1`; `X` errors with `check = H_Z` and `boundary = H_Xᵀ`, where the range
  is `coboundaries 1`.
* The independent generating sets for T29 are `toricGens` and `planarGens`.

## Implementation notes

`L ≥ 1` throughout, as `[NeZero L]`: `ZMod 0` is `ℤ`, not finite.

The incidence is counted mod 2 (docs/fidelity/T34.md, condition 1): `torusVertexEdge s ℓ` is the
number of ends of `ℓ` at `s` mod 2, and `torusEdgeFace ℓ P` the number of times `ℓ` is a side of `P`
mod 2. The two agree with the relation "is an end of" for `L ≥ 2`; at `L = 1` every loop edge has
its one vertex twice and the face has each loop twice, so both boundaries vanish, as in the Koszul
complex (`1 + x = 0` in `𝔽₂[ZMod 1 × ZMod 1]`), and the code is `[[2, 2, 1]]`.

Conventions: the edge `(j, a)` runs from `a` to `a + torusStep L j`, horizontal for `j = 0` and
vertical for `j = 1`; the face `P` has the sides `(0, P)`, `(0, P + torusStep L 1)`, `(1, P)` and
`(1, P + torusStep L 0)`. These are the Koszul complex's: `∂ ({j}, h)` is `f_j h`, the vertices `h`
and `x_j h`, and `∂ ({0, 1}, h)` is `f_0 h e₁ + f_1 h e₀`. The Koszul complex enumerates its cells
by `koszulCellEquiv`, a choice (`Fintype.equivFin`), so the agreement is stated through
`torusKoszulVertexEquiv`, `torusKoszulEdgeEquiv` and `torusKoszulFaceEquiv`, which go through the
cell maps and that choice (docs/fidelity/T34.md, condition 2).

The grid is the tensor product (T43) of a path of `L` vertices, the columns, with a path of `L + 1`
vertices, the rows: a cell `⟨p, c, r⟩` of degree `i` is a cell `c` of the column path of degree `p`
and a cell `r` of the row path of degree `i - p`. So a vertex is `⟨0, c, r⟩`, a vertical edge
`⟨0, c, r⟩` with `r` an edge of the row path (rows `r` to `r + 1`), a horizontal edge `⟨1, c, r⟩`
with `c` an edge of the column path, and a face `⟨1, c, r⟩` with both edges; `∂ ∘ ∂ = 0` is T43's
`tensor_d_comp_d`. The rough boundaries are the cells whose row factor is a vertex on row `0` or
row `L` (`OnRoughBoundary`): those vertices and the horizontal edges between them. The relative
complex keeps the other cells: `L(L - 1)` interior vertices (the sites), `L² + (L - 1)²` edges and
`L(L - 1)` faces, as Dennis et al. count. A relative cycle of the primal lattice (a `Z` string)
joins the two rough boundaries, and a relative cocycle (an `X` string) joins the two smooth ones,
the left and right columns (docs/fidelity/T34.md, condition 4).

Which claims are sourced and which inferred (standard 11.4; docs/fidelity/T34.md): the codes, their
checks, `k = 2`, `k = 1`, `d = L`, the relations among the torus's checks, the independence of the
patch's checks and the decoding problem are Dennis et al.'s, cited above each declaration. The
Koszul presentation (Claim 17), the planar code as T43's relative complex (Claim 10), the cut
argument behind the distance (Claims 6 and 13) and the decoding predicate as phase 6's
specification (Claim 16) are inferred; the cited paper states `d = L` without proof.

## References

Dennis, Kitaev, Landahl and Preskill, *Topological quantum memory*, Section "Surface codes"
(subsections "Toric codes" and "Planar codes"); each citation stands above the declaration that
states it.
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli FTQCLib.Stabilizer Matrix

variable (L : ℕ)

/-! ### Independent rows -/

/-- A sum over the complement of `i0`, read as a sum over all indices with the coefficient at `i0`
set to zero. -/
private theorem sum_dite_eq_sum_subtype {α : Type*} [Fintype α] [DecidableEq α] (i0 : α)
    (g : {t // t ≠ i0} → ZMod 2) (F : α → ZMod 2) :
    ∑ t, (if h : t = i0 then 0 else g ⟨t, h⟩) * F t = ∑ i, g i * F i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), dif_pos rfl, zero_mul, zero_add,
    Finset.sum_subtype (p := fun t => t ≠ i0) (Finset.univ.erase i0) (fun t => by simp)]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_neg i.2]

/-- When a family sums to zero, the members other than `i0` span what the whole family spans. -/
private theorem span_range_subtype_ne {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    [Module (ZMod 2) M] (v : ι → M) (i0 : ι) (hv : ∑ i, v i = 0) :
    Submodule.span (ZMod 2) (Set.range fun s : {s // s ≠ i0} => v s) =
      Submodule.span (ZMod 2) (Set.range v) := by
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases h : i = i0
    · subst h
      have hi : v i = -∑ j ∈ Finset.univ.erase i, v j := by
        rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ (Finset.mem_univ i), hv]
      rw [SetLike.mem_coe, hi]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj =>
        Submodule.subset_span ⟨⟨j, Finset.ne_of_mem_erase hj⟩, rfl⟩)
    · exact Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

/-- `X`-type and `Z`-type Paulis on independent supports are independent together. -/
private theorem linearIndependent_sum_elim_xz {n : ℕ} {ι κ : Type*}
    (u : ι → Fin n → ZMod 2) (w : κ → Fin n → ZMod 2) (hu : LinearIndependent (ZMod 2) u)
    (hw : LinearIndependent (ZMod 2) w) :
    LinearIndependent (ZMod 2)
      (Sum.elim (fun i => (⟨u i, 0⟩ : Pauli n)) fun k => (⟨0, w k⟩ : Pauli n)) := by
  have hX := hu.map' pauliXEmbed (LinearMap.ker_eq_bot.2 pauliXEmbed_injective)
  have hZ := hw.map' pauliZEmbed (LinearMap.ker_eq_bot.2 pauliZEmbed_injective)
  have hd : Disjoint (LinearMap.range (pauliXEmbed (n := n)))
      (LinearMap.range (pauliZEmbed (n := n))) := by
    refine Submodule.disjoint_def.2 ?_
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    have h := congrArg Pauli.X hb
    simp only [pauliXEmbed_apply, pauliZEmbed_apply] at h
    simp only [pauliXEmbed_apply, ← h]
    rfl
  refine hX.sum_type hZ (hd.mono (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))
  · rintro _ ⟨i, rfl⟩
    exact ⟨u i, rfl⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨w k, rfl⟩

/-- The `X`-type generators of rows that span: the span of the rows other than `i0`, when all the
rows sum to zero, is the `X`-stabilizer. -/
private theorem span_cssXGen_subtype_ne {n r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (e : ι ≃ Fin r) (i0 : ι) (hM : ∑ t, M (e t) = 0) :
    Submodule.span (ZMod 2) (Set.range fun s : {s // s ≠ i0} => cssXGen M (e s)) =
      cssXStabilizer M := by
  rw [span_range_subtype_ne (fun t => cssXGen M (e t)) i0, cssXStabilizer]
  · exact congrArg _ (EquivLike.range_comp (cssXGen M) e)
  · change ∑ t, pauliXEmbed (M (e t)) = 0
    rw [← map_sum, hM, map_zero]

/-- The `Z`-type counterpart of `span_cssXGen_subtype_ne`. -/
private theorem span_cssZGen_subtype_ne {n r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (e : ι ≃ Fin r) (i0 : ι) (hM : ∑ t, M (e t) = 0) :
    Submodule.span (ZMod 2) (Set.range fun s : {s // s ≠ i0} => cssZGen M (e s)) =
      cssZStabilizer M := by
  rw [span_range_subtype_ne (fun t => cssZGen M (e t)) i0, cssZStabilizer]
  · exact congrArg _ (EquivLike.range_comp (cssZGen M) e)
  · change ∑ t, pauliZEmbed (M (e t)) = 0
    rw [← map_sum, hM, map_zero]

/-- The rank of a matrix whose rows sum to zero and whose rows other than one are independent. -/
private theorem rank_eq_of_sum_eq_zero {n r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin r) (Fin n) (ZMod 2)) (e : ι ≃ Fin r) (i0 : ι) (hM : ∑ t, M (e t) = 0)
    (hli : LinearIndependent (ZMod 2) fun s : {s // s ≠ i0} => M (e s)) :
    M.rank = Fintype.card ι - 1 := by
  rw [Matrix.rank_eq_finrank_span_row]
  have h := span_range_subtype_ne (fun t => M (e t)) i0 hM
  have hr : Set.range (fun t => M (e t)) = Set.range M.row := EquivLike.range_comp M e
  rw [← hr, ← h, finrank_span_eq_card hli]
  simp [Fintype.card_subtype_compl]

/-- The rows `r b` of `M`, restricted to the columns `q j`, are independent when every function on
the rows that vanishes off `r` and is orthogonal to those columns vanishes. -/
private theorem linearIndependent_submatrix_rows {α β : Type*} [Fintype α] [DecidableEq α]
    {p m : ℕ} (M : Matrix α β (ZMod 2)) (r : Fin p → α) (hr : Function.Injective r)
    (q : Fin m → β)
    (h : ∀ c : α → ZMod 2, (∀ σ, σ ∉ Set.range r → c σ = 0) →
      (∀ j, ∑ σ, c σ * M σ (q j) = 0) → c = 0) :
    LinearIndependent (ZMod 2) fun b j => M (r b) (q j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg b
  set c : α → ZMod 2 := fun σ => ∑ b', if r b' = σ then g b' else 0 with hc
  have hc0 : ∀ σ, σ ∉ Set.range r → c σ = 0 := fun σ hσ =>
    Finset.sum_eq_zero fun b' _ => if_neg fun e => hσ ⟨b', e⟩
  have hrel : ∀ j, ∑ σ, c σ * M σ (q j) = 0 := by
    intro j
    have hj := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
    rw [← hj, hc]
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hb := congrFun (h c hc0 hrel) (r b)
  rw [hc] at hb
  simpa only [hr.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hb

/-- A cell lies outside the subcomplex exactly when it is enumerated by `otherCell`. -/
private theorem mem_range_otherCell {C : BasedComplex} (A : C.Subcomplex) (i : ℕ)
    (σ : Fin (C.cells i)) : σ ∈ Set.range (A.otherCell i) ↔ σ ∉ A.cellSet i := by
  have h := Finset.range_orderEmbOfFin (A.cellSet i)ᶜ rfl
  change σ ∈ Set.range ((A.cellSet i)ᶜ.orderEmbOfFin rfl) ↔ _
  rw [h, Finset.mem_coe, Finset.mem_compl]

/-! ### The torus -/

/-- A point of the `L × L` torus, `ZMod L × ZMod L`: a vertex, or the face whose lower-left corner
it is. -/
abbrev TorusPoint : Type := ZMod L × ZMod L

/-- An edge of the torus: a direction `j`, `0` horizontal and `1` vertical, and its start `a`; it
runs from `a` to `a + torusStep L j`. -/
abbrev TorusEdge : Type := Fin 2 × TorusPoint L

/-- The unit step in direction `j`: `(1, 0)` for `j = 0` and `(0, 1)` for `j = 1`. -/
def torusStep (j : Fin 2) : TorusPoint L :=
  ![(1, 0), (0, 1)] j

/-- The vertex–edge incidence of the torus: the number of ends of the edge `ℓ` at the vertex `s`,
mod 2. -/
def torusVertexEdge (s : TorusPoint L) (ℓ : TorusEdge L) : ZMod 2 :=
  (if s = ℓ.2 then 1 else 0) + (if s = ℓ.2 + torusStep L ℓ.1 then 1 else 0)

/-- The edge–face incidence of the torus: the number of times the edge `ℓ` is a side of the face
`P`, mod 2. The sides of `P` in direction `j` start at `P` and at `P` plus the step in the other
direction, `ℓ.1.rev`. -/
def torusEdgeFace (ℓ : TorusEdge L) (P : TorusPoint L) : ZMod 2 :=
  (if ℓ.2 = P then 1 else 0) + (if ℓ.2 = P + torusStep L ℓ.1.rev then 1 else 0)

/-- `∂ ∘ ∂ = 0` on the torus, at a vertex `s` and a face `P`: each corner of `P` is an end of two of
its sides. -/
theorem sum_torusVertexEdge_mul_torusEdgeFace [NeZero L] (s P : TorusPoint L) :
    ∑ ℓ : TorusEdge L, torusVertexEdge L s ℓ * torusEdgeFace L ℓ P = 0 := by
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, torusVertexEdge, torusEdgeFace, h0, h1,
    add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, ← sub_eq_iff_eq_add,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_right_comm s (torusStep L 1) (torusStep L 0)]
  generalize (if s = P then (1 : ZMod 2) else 0) = a
  generalize (if s - torusStep L 0 = P then (1 : ZMod 2) else 0) = b
  generalize (if s - torusStep L 1 = P then (1 : ZMod 2) else 0) = c
  generalize (if s - torusStep L 0 - torusStep L 1 = P then (1 : ZMod 2) else 0) = e
  revert a b c e
  decide

section Torus

variable [NeZero L]

/-- The enumeration of the torus's points, row-major through `ZMod.finEquiv`. -/
def torusPointEquiv : TorusPoint L ≃ Fin (L * L) :=
  ((ZMod.finEquiv L).toEquiv.symm.prodCongr (ZMod.finEquiv L).toEquiv.symm).trans finProdFinEquiv

/-- The enumeration of the torus's edges: the direction, then the start. -/
def torusEdgeEquiv : TorusEdge L ≃ Fin (2 * (L * L)) :=
  ((Equiv.refl (Fin 2)).prodCongr (torusPointEquiv L)).trans finProdFinEquiv

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h41a4212e9a7f
-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h541068807c48
/-- The **`L × L` torus** as a based complex: `L²` vertices in degree `0`, `2L²` edges in degree
`1` and `L²` faces in degree `2`, enumerated by `torusPointEquiv` and `torusEdgeEquiv`, with the
boundary of an edge its two ends and the boundary of a face its four sides, counted mod 2. -/
def torusComplex : BasedComplex where
  cells
    | 0 => L * L
    | 1 => 2 * (L * L)
    | 2 => L * L
    | _ + 3 => 0
  d
    | 0 => Matrix.of fun s ℓ =>
        torusVertexEdge L ((torusPointEquiv L).symm s) ((torusEdgeEquiv L).symm ℓ)
    | 1 => Matrix.of fun ℓ P =>
        torusEdgeFace L ((torusEdgeEquiv L).symm ℓ) ((torusPointEquiv L).symm P)
    | _ + 2 => 0
  d_comp_d
    | 0 => by
        ext s P
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine (Fintype.sum_equiv (torusEdgeEquiv L).symm _
          (fun ℓ => torusVertexEdge L ((torusPointEquiv L).symm s) ℓ *
            torusEdgeFace L ℓ ((torusPointEquiv L).symm P)) fun _ => rfl).trans ?_
        exact sum_torusVertexEdge_mul_torusEdgeFace L _ _
    | 1 => Matrix.mul_zero _
    | _ + 2 => Matrix.zero_mul _

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h41a4212e9a7f
-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143 figure:fig_checks
/-- The **toric code**: the CSS pair at degree `1` of the torus's incidence, on `2L²` qubits, with
`H_X = ∂₁` (a star `X_s` on the edges at each vertex `s`) and `H_Z = ∂₂ᵀ` (a plaquette `Z_P` on the
sides of each face `P`). -/
def toricCode :
    Matrix (Fin (L * L)) (Fin (2 * (L * L))) (ZMod 2) ×
      Matrix (Fin (L * L)) (Fin (2 * (L * L))) (ZMod 2) :=
  cssOfComplex (torusComplex L) 1

/-! ### The Koszul presentation -/

/-- `f_j = 1 + x_j` in `𝔽₂[ZMod L × ZMod L]`, the group written multiplicatively, with `x_j` the
unit step in direction `j`. -/
noncomputable def torusPolynomial (j : Fin 2) :
    MonoidAlgebra (ZMod 2) (Multiplicative (TorusPoint L)) :=
  1 + MonoidAlgebra.of (ZMod 2) _ (Multiplicative.ofAdd (torusStep L j))

/-- T43's Koszul complex of `1 + x₀, 1 + x₁` on `𝔽₂[ZMod L × ZMod L]`. -/
noncomputable def torusKoszul : BasedComplex :=
  ⟨koszul (Multiplicative (TorusPoint L)) (torusPolynomial L), koszul_d_comp_d _ _⟩

/-- A vertex `g` of the torus is the Koszul cell `(∅, g)`. -/
def torusVertexCell : TorusPoint L ≃ KoszulCell (Multiplicative (TorusPoint L)) 2 0 where
  toFun s := (⟨∅, rfl⟩, Multiplicative.ofAdd s)
  invFun x := Multiplicative.toAdd x.2
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨⟨S, hS⟩, g⟩ := x
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp hS
    rfl

/-- An edge `(j, g)` of the torus is the Koszul cell `({j}, g)`. -/
def torusEdgeCell : TorusEdge L ≃ KoszulCell (Multiplicative (TorusPoint L)) 2 1 where
  toFun ℓ := (⟨{ℓ.1}, Finset.card_singleton _⟩, Multiplicative.ofAdd ℓ.2)
  invFun x := (if (0 : Fin 2) ∈ x.1.1 then 0 else 1, Multiplicative.toAdd x.2)
  left_inv ℓ := by
    obtain ⟨j, a⟩ := ℓ
    fin_cases j <;> rfl
  right_inv x := by
    obtain ⟨⟨S, hS⟩, g⟩ := x
    have key : ∀ S : Finset (Fin 2), S.card = 1 → {if (0 : Fin 2) ∈ S then 0 else 1} = S := by
      decide
    ext1
    · exact Subtype.ext (key S hS)
    · rfl

/-- A face `g` of the torus is the Koszul cell `({0, 1}, g)`. -/
def torusFaceCell : TorusPoint L ≃ KoszulCell (Multiplicative (TorusPoint L)) 2 2 where
  toFun P := (⟨Finset.univ, rfl⟩, Multiplicative.ofAdd P)
  invFun x := Multiplicative.toAdd x.2
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨⟨S, hS⟩, g⟩ := x
    have key : ∀ S : Finset (Fin 2), S.card = 2 → Finset.univ = S := by
      decide
    obtain rfl := key S hS
    rfl

/-- The torus's vertices matched with the Koszul complex's cells of degree `0`, through
`torusVertexCell` and the Koszul enumeration. -/
noncomputable def torusKoszulVertexEquiv :
    Fin ((torusComplex L).cells 0) ≃ Fin ((torusKoszul L).cells 0) :=
  (torusPointEquiv L).symm.trans
    ((torusVertexCell L).trans (koszulCellEquiv (Multiplicative (TorusPoint L)) 2 0).symm)

/-- The torus's edges matched with the Koszul complex's cells of degree `1`, through
`torusEdgeCell` and the Koszul enumeration. -/
noncomputable def torusKoszulEdgeEquiv :
    Fin ((torusComplex L).cells 1) ≃ Fin ((torusKoszul L).cells 1) :=
  (torusEdgeEquiv L).symm.trans
    ((torusEdgeCell L).trans (koszulCellEquiv (Multiplicative (TorusPoint L)) 2 1).symm)

/-- The torus's faces matched with the Koszul complex's cells of degree `2`, through
`torusFaceCell` and the Koszul enumeration. -/
noncomputable def torusKoszulFaceEquiv :
    Fin ((torusComplex L).cells 2) ≃ Fin ((torusKoszul L).cells 2) :=
  (torusPointEquiv L).symm.trans
    ((torusFaceCell L).trans (koszulCellEquiv (Multiplicative (TorusPoint L)) 2 2).symm)

omit [NeZero L] in
/-- The coefficient of `g` in `1 + x_j` is `1` at `g = 0` and at `g = x_j`, counted mod 2. -/
private theorem torusPolynomial_apply (j : Fin 2) (a : TorusPoint L) :
    torusPolynomial L j (Multiplicative.ofAdd a) =
      (if a = 0 then 1 else 0) + (if a = torusStep L j then 1 else 0) := by
  classical
  rw [torusPolynomial, MonoidAlgebra.one_def, MonoidAlgebra.of_apply]
  erw [Finsupp.add_apply]
  rw [MonoidAlgebra.single_apply, MonoidAlgebra.single_apply]
  congr 1
  · simp only [eq_comm (a := (1 : Multiplicative (TorusPoint L))), ofAdd_eq_one]
  · simp [eq_comm]

omit [NeZero L] in
/-- The Koszul incidence between the vertex `(∅, a)` and the edge `({j}, b)` is the torus's
vertex–edge incidence: the coefficient of `a - b` in `1 + x_j`. -/
private theorem koszulIncidence_torusVertexCell_torusEdgeCell (a : TorusPoint L)
    (e : TorusEdge L) :
    koszulIncidence (torusPolynomial L) (torusVertexCell L a) (torusEdgeCell L e) =
      torusVertexEdge L a e := by
  obtain ⟨j, b⟩ := e
  simp only [koszulIncidence, torusVertexCell, torusEdgeCell, Equiv.coe_fn_mk,
    Finset.sum_singleton, Finset.erase_singleton, if_true, ← ofAdd_neg, ← ofAdd_add,
    torusPolynomial_apply, torusVertexEdge, ← sub_eq_add_neg, sub_eq_iff_eq_add, zero_add,
    add_comm (torusStep L j) b]

omit [NeZero L] in
/-- The Koszul incidence between the edge `({j}, b)` and the face `({0, 1}, P)` is the torus's
edge–face incidence: the coefficient of `b - P` in `1 + x_{j.rev}`, the other direction. -/
private theorem koszulIncidence_torusEdgeCell_torusFaceCell (e : TorusEdge L)
    (P : TorusPoint L) :
    koszulIncidence (torusPolynomial L) (torusEdgeCell L e) (torusFaceCell L P) =
      torusEdgeFace L e P := by
  obtain ⟨j, b⟩ := e
  have key : ∀ i j : Fin 2, Finset.univ.erase i = {j} ↔ i = j.rev := by
    decide
  simp only [koszulIncidence, torusFaceCell, torusEdgeCell, Equiv.coe_fn_mk, key,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ← ofAdd_neg, ← ofAdd_add,
    torusPolynomial_apply, torusEdgeFace, ← sub_eq_add_neg, sub_eq_iff_eq_add, zero_add,
    add_comm (torusStep L j.rev) P]

/-- **The toric code is the Koszul code of `1 + x₀, 1 + x₁`.** Both check matrices of the torus's
incidence are those of T43's Koszul complex on `𝔽₂[ZMod L × ZMod L]` at degree `1`, each vertex,
edge and face read as the Koszul cell of the same group element. Inferred, not sourced
(docs/fidelity/T34.md, Claim 17). -/
theorem toricCode_eq_koszul :
    (toricCode L).1 = (cssOfComplex (torusKoszul L) 1).1.submatrix
        (torusKoszulVertexEquiv L) (torusKoszulEdgeEquiv L) ∧
      (toricCode L).2 = (cssOfComplex (torusKoszul L) 1).2.submatrix
        (torusKoszulFaceEquiv L) (torusKoszulEdgeEquiv L) := by
  refine ⟨?_, ?_⟩
  · ext s ℓ
    change torusVertexEdge L ((torusPointEquiv L).symm s) ((torusEdgeEquiv L).symm ℓ) =
      koszulIncidence (torusPolynomial L)
        (koszulCellEquiv _ 2 0 ((koszulCellEquiv _ 2 0).symm
          (torusVertexCell L ((torusPointEquiv L).symm s))))
        (koszulCellEquiv _ 2 1 ((koszulCellEquiv _ 2 1).symm
          (torusEdgeCell L ((torusEdgeEquiv L).symm ℓ))))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      koszulIncidence_torusVertexCell_torusEdgeCell]
  · ext P ℓ
    change torusEdgeFace L ((torusEdgeEquiv L).symm ℓ) ((torusPointEquiv L).symm P) =
      koszulIncidence (torusPolynomial L)
        (koszulCellEquiv _ 2 1 ((koszulCellEquiv _ 2 1).symm
          (torusEdgeCell L ((torusEdgeEquiv L).symm ℓ))))
        (koszulCellEquiv _ 2 2 ((koszulCellEquiv _ 2 2).symm
          (torusFaceCell L ((torusPointEquiv L).symm P))))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      koszulIncidence_torusEdgeCell_torusFaceCell]

/-! ### The toric code's parameters and generators -/

/-- The star matrix, read on the torus's points and edges, is the vertex–edge incidence. -/
private theorem toricCode_fst_apply (s : TorusPoint L) (ℓ : TorusEdge L) :
    (toricCode L).1 (torusPointEquiv L s) (torusEdgeEquiv L ℓ) = torusVertexEdge L s ℓ := by
  change torusVertexEdge L ((torusPointEquiv L).symm (torusPointEquiv L s))
    ((torusEdgeEquiv L).symm (torusEdgeEquiv L ℓ)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The plaquette matrix, read on the torus's points and edges, is the edge–face incidence. -/
private theorem toricCode_snd_apply (P : TorusPoint L) (ℓ : TorusEdge L) :
    (toricCode L).2 (torusPointEquiv L P) (torusEdgeEquiv L ℓ) = torusEdgeFace L ℓ P := by
  change torusEdgeFace L ((torusEdgeEquiv L).symm (torusEdgeEquiv L ℓ))
    ((torusPointEquiv L).symm (torusPointEquiv L P)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- A sum against the vertex–edge incidence of an edge picks out the edge's two ends. -/
private theorem sum_mul_torusVertexEdge (c : TorusPoint L → ZMod 2) (ℓ : TorusEdge L) :
    ∑ s, c s * torusVertexEdge L s ℓ = c ℓ.2 + c (ℓ.2 + torusStep L ℓ.1) := by
  simp only [torusVertexEdge, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A sum against the edge–face incidence of an edge picks out the two faces it bounds. -/
private theorem sum_mul_torusEdgeFace (c : TorusPoint L → ZMod 2) (ℓ : TorusEdge L) :
    ∑ P, c P * torusEdgeFace L ℓ P = c ℓ.2 + c (ℓ.2 - torusStep L ℓ.1.rev) := by
  simp only [torusEdgeFace, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    ← sub_eq_iff_eq_add, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- A function on the torus invariant under both unit steps is constant: the torus is connected. -/
private theorem eq_of_step_invariant (c : TorusPoint L → ZMod 2)
    (h : ∀ a j, c (a + torusStep L j) = c a) (a : TorusPoint L) : c a = c 0 := by
  have hn : ∀ j (k : ℕ) b, c (b + k • torusStep L j) = c b := by
    intro j k
    induction k with
    | zero => intro b; rw [zero_smul, add_zero]
    | succ k ih =>
      intro b
      rw [succ_nsmul, ← add_assoc, h, ih]
  have ha : a = 0 + a.1.val • torusStep L 0 + a.2.val • torusStep L 1 := by
    ext <;> simp [torusStep]
  rw [ha, hn, hn]

/-- The rows other than that of `0`, of a check matrix on the torus whose relations are invariant
under the steps, are independent. -/
private theorem linearIndependent_toric_rows
    (M : Matrix (Fin (L * L)) (Fin (2 * (L * L))) (ZMod 2))
    (hM : ∀ c : TorusPoint L → ZMod 2,
      (∀ ℓ, ∑ t, c t * M (torusPointEquiv L t) (torusEdgeEquiv L ℓ) = 0) →
        ∀ a j, c (a + torusStep L j) = c a) :
    LinearIndependent (ZMod 2) fun s : {s : TorusPoint L // s ≠ 0} => M (torusPointEquiv L s) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set c : TorusPoint L → ZMod 2 := fun t => if h : t = 0 then 0 else g ⟨t, h⟩ with hc
  have hrel : ∀ ℓ, ∑ t, c t * M (torusPointEquiv L t) (torusEdgeEquiv L ℓ) = 0 := by
    intro ℓ
    rw [hc, sum_dite_eq_sum_subtype]
    have hℓ := congrFun hg (torusEdgeEquiv L ℓ)
    rw [Finset.sum_apply, Pi.zero_apply] at hℓ
    exact hℓ
  have hi := eq_of_step_invariant L c (hM c hrel) i
  rw [hc] at hi
  simpa only [dif_neg i.2, dif_pos rfl] using hi

/-- A relation among the stars is invariant under the steps: the edge `(j, a)` has its ends at `a`
and `a + x_j`. -/
private theorem toric_rel_X (c : TorusPoint L → ZMod 2)
    (hc : ∀ ℓ, ∑ t, c t * (toricCode L).1 (torusPointEquiv L t) (torusEdgeEquiv L ℓ) = 0)
    (a : TorusPoint L) (j : Fin 2) : c (a + torusStep L j) = c a := by
  have h : ∑ t, c t * torusVertexEdge L t (j, a) = 0 := by
    rw [← hc (j, a)]
    exact Finset.sum_congr rfl fun t _ => by rw [toricCode_fst_apply]
  rw [sum_mul_torusVertexEdge] at h
  exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add, add_comm]; exact h)

/-- A relation among the plaquettes is invariant under the steps: the edge `(j.rev, a + x_j)`
bounds the faces `a + x_j` and `a`. -/
private theorem toric_rel_Z (c : TorusPoint L → ZMod 2)
    (hc : ∀ ℓ, ∑ t, c t * (toricCode L).2 (torusPointEquiv L t) (torusEdgeEquiv L ℓ) = 0)
    (a : TorusPoint L) (j : Fin 2) : c (a + torusStep L j) = c a := by
  have h : ∑ t, c t * torusEdgeFace L (j.rev, a + torusStep L j) t = 0 := by
    rw [← hc (j.rev, a + torusStep L j)]
    exact Finset.sum_congr rfl fun t _ => by rw [toricCode_snd_apply]
  rw [sum_mul_torusEdgeFace, Fin.rev_rev, add_sub_cancel_right] at h
  exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add]; exact h)

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h90d1802c273b
/-- All the stars sum to zero: each edge has two ends. -/
private theorem sum_toricCode_fst : ∑ t, (toricCode L).1 (torusPointEquiv L t) = 0 := by
  funext ℓ'
  obtain ⟨ℓ, rfl⟩ := (torusEdgeEquiv L).surjective ℓ'
  rw [Finset.sum_apply, Pi.zero_apply]
  calc ∑ t, (toricCode L).1 (torusPointEquiv L t) (torusEdgeEquiv L ℓ)
      = ∑ t, (fun _ => (1 : ZMod 2)) t * torusVertexEdge L t ℓ :=
        Finset.sum_congr rfl fun t _ => by rw [toricCode_fst_apply, one_mul]
    _ = 1 + 1 := sum_mul_torusVertexEdge L (fun _ => 1) ℓ
    _ = 0 := by decide

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h90d1802c273b
/-- All the plaquettes sum to zero: each edge is a side of two faces. -/
private theorem sum_toricCode_snd : ∑ t, (toricCode L).2 (torusPointEquiv L t) = 0 := by
  funext ℓ'
  obtain ⟨ℓ, rfl⟩ := (torusEdgeEquiv L).surjective ℓ'
  rw [Finset.sum_apply, Pi.zero_apply]
  calc ∑ t, (toricCode L).2 (torusPointEquiv L t) (torusEdgeEquiv L ℓ)
      = ∑ t, (fun _ => (1 : ZMod 2)) t * torusEdgeFace L ℓ t :=
        Finset.sum_congr rfl fun t _ => by rw [toricCode_snd_apply, one_mul]
    _ = 1 + 1 := sum_mul_torusEdgeFace L (fun _ => 1) ℓ
    _ = 0 := by decide

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h90d1802c273b
/-- **The toric code encodes two qubits**: its `Z`-logical space, the homology of the torus in
degree `1` (`cssOfComplex_logical_eq_homology`), has dimension `2`, at every `L ≥ 1`. -/
theorem toricCode_k :
    Module.finrank (ZMod 2) (cssZLogical (toricCode L).1 (toricCode L).2) = 2 := by
  -- `k = n - rk H_X - rk H_Z` with each rank `L² - 1`: the source's count of `2(L² - 1)`
  -- independent checks.
  have hcss : IsCSSPair (toricCode L).1 (toricCode L).2 := cssOfComplex_isCSSPair _ _
  rw [finrank_cssZLogical hcss,
    rank_eq_of_sum_eq_zero _ (torusPointEquiv L) 0 (sum_toricCode_fst L)
      (linearIndependent_toric_rows L _ (toric_rel_X L)),
    rank_eq_of_sum_eq_zero _ (torusPointEquiv L) 0 (sum_toricCode_snd L)
      (linearIndependent_toric_rows L _ (toric_rel_Z L))]
  have hL : 1 ≤ L * L := Nat.mul_pos (NeZero.pos L) (NeZero.pos L)
  simp only [Fintype.card_prod, ZMod.card]
  generalize L * L = N at hL ⊢
  omega

/-- The generators T29's encoder takes on the torus: the star of every vertex but `0` and the
plaquette of every face but `0`, as Paulis. -/
def toricGens :
    {s : TorusPoint L // s ≠ 0} ⊕ {P : TorusPoint L // P ≠ 0} → Pauli (2 * (L * L)) :=
  Sum.elim (fun s => cssXGen (toricCode L).1 (torusPointEquiv L s.1))
    (fun P => cssZGen (toricCode L).2 (torusPointEquiv L P.1))

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h90d1802c273b
/-- **An independent generating set of the toric code's stabilizer**: every star and every
plaquette but one of each (`toricGens`) are linearly independent and generate the stabilizer; all
the stars sum to zero, and so do all the plaquettes, so none of the full sets is independent. -/
theorem toricCode_independentGens :
    LinearIndependent (ZMod 2) (toricGens L) ∧
      Submodule.span (ZMod 2) (Set.range (toricGens L)) =
        cssStabilizer (toricCode L).1 (toricCode L).2 ∧
      ∑ s, (toricCode L).1 s = 0 ∧ ∑ P, (toricCode L).2 P = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact linearIndependent_sum_elim_xz _ _ (linearIndependent_toric_rows L _ (toric_rel_X L))
      (linearIndependent_toric_rows L _ (toric_rel_Z L))
  · rw [toricGens, Set.Sum.elim_range, Submodule.span_union, cssStabilizer,
      ← span_cssXGen_subtype_ne _ (torusPointEquiv L) 0 (sum_toricCode_fst L),
      ← span_cssZGen_subtype_ne _ (torusPointEquiv L) 0 (sum_toricCode_snd L)]
  · rw [← Equiv.sum_comp (torusPointEquiv L)]
    exact sum_toricCode_fst L
  · rw [← Equiv.sum_comp (torusPointEquiv L)]
    exact sum_toricCode_snd L

/-- The horizontal loop through the origin, `{(0, (x, 0)) : x}`: a `Z` string on a nontrivial cycle
of the torus, of weight `L`. -/
def torusRowLoop : Fin ((torusComplex L).cells 1) → ZMod 2 := fun ℓ =>
  if ((torusEdgeEquiv L).symm ℓ).1 = 0 ∧ ((torusEdgeEquiv L).symm ℓ).2.2 = 0 then 1 else 0

/-- The vertical edges on the row through the origin, `{(1, (x, 0)) : x}`: an `X` string on a
nontrivial cycle of the dual lattice, of weight `L`. -/
def torusDualLoop : Fin ((torusComplex L).cells 1) → ZMod 2 := fun ℓ =>
  if ((torusEdgeEquiv L).symm ℓ).1 = 1 ∧ ((torusEdgeEquiv L).symm ℓ).2.2 = 0 then 1 else 0

/-! ### The toric code's distance

The cut argument (inferred, docs/fidelity/T34.md, Claim 6). A cut `torusCut j a` is the set of
edges in direction `j` whose start has the coordinate of `a` in direction `j`: the edges crossing
one line across the torus. It is a cocycle, so it meets every boundary evenly, and two
neighbouring cuts differ by a coboundary, so a cycle meets every cut in one direction with the
same parity. A loop `torusLoop j a` is the set of edges in direction `j` along the line through
`a`: a cycle, and two neighbouring loops differ by a boundary. The first cut and the first loop in
each direction are dual, and the cycles exceed the boundaries by two dimensions (the ranks of
`toricCode_k`), so a cycle meeting both first cuts evenly is a boundary
(`mem_of_finrank_le_of_apply_eq_zero`). A cycle that is not a boundary therefore meets every cut
in some direction oddly, and has an edge on each of `L` disjoint cuts. The cocycles are argued the
same way with the roles of cuts and loops exchanged. -/

/-- The dot product with a fixed vector, as a linear map. -/
private def dotProductLin {n : Type*} [Fintype n] (u : n → ZMod 2) :
    (n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun w := u ⬝ᵥ w
  map_add' := dotProduct_add u
  map_smul' c w := dotProduct_smul c u w

omit [NeZero L] in
/-- In `Fin 2`, the other direction is not the direction. -/
private theorem fin_two_rev_ne (j : Fin 2) : j.rev ≠ j := by
  fin_cases j <;> decide

/-- The coordinate of a point of the torus in direction `k`. -/
private def torusCoord (k : Fin 2) (a : TorusPoint L) : ZMod L :=
  ![a.1, a.2] k

omit [NeZero L] in
/-- A unit step moves the coordinate in its own direction by one and leaves the other. -/
private theorem torusCoord_add_torusStep (k i : Fin 2) (a : TorusPoint L) :
    torusCoord L k (a + torusStep L i) = torusCoord L k a + if i = k then 1 else 0 := by
  fin_cases k <;> fin_cases i <;> rfl

omit [NeZero L] in
/-- A unit step back moves the coordinate in its own direction by one and leaves the other. -/
private theorem torusCoord_sub_torusStep (k i : Fin 2) (a : TorusPoint L) :
    torusCoord L k (a - torusStep L i) = torusCoord L k a - if i = k then 1 else 0 := by
  fin_cases k <;> fin_cases i <;> rfl

omit [NeZero L] in
/-- A point of the torus is fixed by its two coordinates. -/
private theorem torusPoint_ext (k : Fin 2) {a b : TorusPoint L}
    (h : torusCoord L k a = torusCoord L k b) (h' : torusCoord L k.rev a = torusCoord L k.rev b) :
    a = b := by
  fin_cases k
  · exact Prod.ext h h'
  · exact Prod.ext h' h

/-- The boundary of a chain at a vertex: in each direction, the edge leaving it and the edge
arriving at it. -/
private theorem sum_torusVertexEdge_mul (s : TorusPoint L) (w : TorusEdge L → ZMod 2) :
    ∑ ℓ, torusVertexEdge L s ℓ * w ℓ = ∑ j, (w (j, s) + w (j, s - torusStep L j)) := by
  simp only [Fintype.sum_prod_type, torusVertexEdge, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, ← sub_eq_iff_eq_add, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The coboundary of a cochain at a face: its four sides, two in each direction. -/
private theorem sum_torusEdgeFace_mul (P : TorusPoint L) (w : TorusEdge L → ZMod 2) :
    ∑ ℓ, torusEdgeFace L ℓ P * w ℓ = ∑ j, (w (j, P) + w (j, P + torusStep L j.rev)) := by
  simp only [Fintype.sum_prod_type, torusEdgeFace, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A chain is a cycle when its boundary vanishes at every vertex. -/
private theorem mem_torus_cycles_iff (v : Fin ((torusComplex L).cells 1) → ZMod 2) :
    v ∈ (torusComplex L).cycles 1 ↔ ∀ s, ∑ j, (v (torusEdgeEquiv L (j, s)) +
      v (torusEdgeEquiv L (j, s - torusStep L j))) = 0 := by
  have h : ∀ s, ((toricCode L).1 *ᵥ v) (torusPointEquiv L s) = ∑ j, (v (torusEdgeEquiv L (j, s)) +
      v (torusEdgeEquiv L (j, s - torusStep L j))) := by
    intro s
    rw [← sum_torusVertexEdge_mul L s (fun ℓ => v (torusEdgeEquiv L ℓ))]
    change ∑ ℓ, (toricCode L).1 (torusPointEquiv L s) ℓ * v ℓ = _
    rw [← (torusEdgeEquiv L).sum_comp]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [toricCode_fst_apply]
  rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  change (toricCode L).1 *ᵥ v = 0 ↔ _
  constructor
  · intro hv s
    rw [← h s, hv, Pi.zero_apply]
  · intro hv
    funext s'
    obtain ⟨s, rfl⟩ := (torusPointEquiv L).surjective s'
    rw [h s, hv s, Pi.zero_apply]

/-- A cochain is a cocycle when its coboundary vanishes at every face. -/
private theorem mem_torus_cocycles_iff (u : Fin ((torusComplex L).cells 1) → ZMod 2) :
    u ∈ (torusComplex L).cocycles 1 ↔ ∀ P, ∑ j, (u (torusEdgeEquiv L (j, P)) +
      u (torusEdgeEquiv L (j, P + torusStep L j.rev))) = 0 := by
  have h : ∀ P, ((toricCode L).2 *ᵥ u) (torusPointEquiv L P) = ∑ j, (u (torusEdgeEquiv L (j, P)) +
      u (torusEdgeEquiv L (j, P + torusStep L j.rev))) := by
    intro P
    rw [← sum_torusEdgeFace_mul L P (fun ℓ => u (torusEdgeEquiv L ℓ))]
    change ∑ ℓ, (toricCode L).2 (torusPointEquiv L P) ℓ * u ℓ = _
    rw [← (torusEdgeEquiv L).sum_comp]
    exact Finset.sum_congr rfl fun ℓ _ => by rw [toricCode_snd_apply]
  rw [BasedComplex.cocycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  change (toricCode L).2 *ᵥ u = 0 ↔ _
  constructor
  · intro hu P
    rw [← h P, hu, Pi.zero_apply]
  · intro hu
    funext P'
    obtain ⟨P, rfl⟩ := (torusPointEquiv L).surjective P'
    rw [h P, hu P, Pi.zero_apply]

/-- A cochain that is, on each edge, a function `g` of the vertices summed over the edge's two
ends is the coboundary of `g`. -/
private theorem mem_torus_coboundaries (g : TorusPoint L → ZMod 2)
    (c : Fin ((torusComplex L).cells 1) → ZMod 2)
    (hc : ∀ ℓ, c (torusEdgeEquiv L ℓ) = g ℓ.2 + g (ℓ.2 + torusStep L ℓ.1)) :
    c ∈ (torusComplex L).coboundaries 1 := by
  rw [BasedComplex.coboundaries]
  refine LinearMap.mem_range.2 ⟨fun s => g ((torusPointEquiv L).symm s), ?_⟩
  rw [Matrix.mulVecLin_apply]
  funext ℓ'
  obtain ⟨ℓ, rfl⟩ := (torusEdgeEquiv L).surjective ℓ'
  rw [hc, ← sum_mul_torusVertexEdge]
  change ∑ s, (toricCode L).1 s (torusEdgeEquiv L ℓ) * g ((torusPointEquiv L).symm s) = _
  rw [← (torusPointEquiv L).sum_comp]
  exact Finset.sum_congr rfl fun s _ => by
    rw [toricCode_fst_apply, Equiv.symm_apply_apply, mul_comm]

/-- A chain that is, on each edge, a function `f` of the faces summed over the two faces the edge
bounds is the boundary of `f`. -/
private theorem mem_torus_boundaries (f : TorusPoint L → ZMod 2)
    (c : Fin ((torusComplex L).cells 1) → ZMod 2)
    (hc : ∀ ℓ, c (torusEdgeEquiv L ℓ) = f ℓ.2 + f (ℓ.2 - torusStep L ℓ.1.rev)) :
    c ∈ (torusComplex L).boundaries 1 := by
  rw [BasedComplex.boundaries]
  refine LinearMap.mem_range.2 ⟨fun P => f ((torusPointEquiv L).symm P), ?_⟩
  rw [Matrix.mulVecLin_apply]
  funext ℓ'
  obtain ⟨ℓ, rfl⟩ := (torusEdgeEquiv L).surjective ℓ'
  rw [hc, ← sum_mul_torusEdgeFace]
  change ∑ P, (toricCode L).2 P (torusEdgeEquiv L ℓ) * f ((torusPointEquiv L).symm P) = _
  rw [← (torusPointEquiv L).sum_comp]
  exact Finset.sum_congr rfl fun P _ => by
    rw [toricCode_snd_apply, Equiv.symm_apply_apply, mul_comm]

/-- The cut across the torus in direction `j` at `a`: the edges in direction `j` whose start has
the coordinate of `a` in direction `j`. -/
private def torusCut (j : Fin 2) (a : TorusPoint L) : Fin ((torusComplex L).cells 1) → ZMod 2 :=
  fun ℓ => if ((torusEdgeEquiv L).symm ℓ).1 = j ∧
    torusCoord L j ((torusEdgeEquiv L).symm ℓ).2 = torusCoord L j a then 1 else 0

/-- The loop around the torus in direction `j` through `a`: the edges in direction `j` whose start
has the coordinate of `a` in the other direction. -/
private def torusLoop (j : Fin 2) (a : TorusPoint L) : Fin ((torusComplex L).cells 1) → ZMod 2 :=
  fun ℓ => if ((torusEdgeEquiv L).symm ℓ).1 = j ∧
    torusCoord L j.rev ((torusEdgeEquiv L).symm ℓ).2 = torusCoord L j.rev a then 1 else 0

/-- A cut read on an edge of the torus. -/
private theorem torusCut_apply (j : Fin 2) (a : TorusPoint L) (ℓ : TorusEdge L) :
    torusCut L j a (torusEdgeEquiv L ℓ) =
      if ℓ.1 = j ∧ torusCoord L j ℓ.2 = torusCoord L j a then 1 else 0 := by
  dsimp only [torusCut]
  rw [Equiv.symm_apply_apply]

/-- A loop read on an edge of the torus. -/
private theorem torusLoop_apply (j : Fin 2) (a : TorusPoint L) (ℓ : TorusEdge L) :
    torusLoop L j a (torusEdgeEquiv L ℓ) =
      if ℓ.1 = j ∧ torusCoord L j.rev ℓ.2 = torusCoord L j.rev a then 1 else 0 := by
  dsimp only [torusLoop]
  rw [Equiv.symm_apply_apply]

/-- A cut is a cocycle: a face has its two sides in direction `j` both on the cut or both off
it. -/
private theorem torusCut_mem_cocycles (j : Fin 2) (a : TorusPoint L) :
    torusCut L j a ∈ (torusComplex L).cocycles 1 := by
  rw [mem_torus_cocycles_iff]
  intro P
  rw [Finset.sum_eq_single j]
  · rw [torusCut_apply, torusCut_apply]
    simp only [torusCoord_add_torusStep, if_neg (fin_two_rev_ne j), add_zero,
      CharTwo.add_self_eq_zero]
  · intro i _ hi
    rw [torusCut_apply, torusCut_apply]
    simp only [hi, false_and, if_false, add_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- A loop is a cycle: a vertex has its two edges in direction `j` both on the loop or both off
it. -/
private theorem torusLoop_mem_cycles (j : Fin 2) (a : TorusPoint L) :
    torusLoop L j a ∈ (torusComplex L).cycles 1 := by
  rw [mem_torus_cycles_iff]
  intro s
  rw [Finset.sum_eq_single j]
  · rw [torusLoop_apply, torusLoop_apply]
    simp only [torusCoord_sub_torusStep, if_neg (fin_two_rev_ne j).symm, sub_zero,
      CharTwo.add_self_eq_zero]
  · intro i _ hi
    rw [torusLoop_apply, torusLoop_apply]
    simp only [hi, false_and, if_false, add_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Two neighbouring cuts differ by the coboundary of the vertices on one line. -/
private theorem torusCut_add_mem_coboundaries (j : Fin 2) (a : TorusPoint L) :
    torusCut L j (a + torusStep L j) + torusCut L j a ∈ (torusComplex L).coboundaries 1 := by
  refine mem_torus_coboundaries L
    (fun s => if torusCoord L j s = torusCoord L j a + 1 then 1 else 0) _ fun ℓ => ?_
  obtain ⟨i, b⟩ := ℓ
  rw [Pi.add_apply, torusCut_apply, torusCut_apply]
  dsimp only
  simp only [torusCoord_add_torusStep, if_true]
  by_cases hi : i = j
  · subst hi
    simp only [true_and, if_true, add_left_inj]
  · simp only [hi, false_and, if_false, add_zero, CharTwo.add_self_eq_zero]

/-- Two neighbouring loops differ by the boundary of the faces on one line. -/
private theorem torusLoop_add_mem_boundaries (j : Fin 2) (a : TorusPoint L) :
    torusLoop L j (a + torusStep L j.rev) + torusLoop L j a ∈ (torusComplex L).boundaries 1 := by
  refine mem_torus_boundaries L
    (fun P => if torusCoord L j.rev P = torusCoord L j.rev a then 1 else 0) _ fun ℓ => ?_
  obtain ⟨i, b⟩ := ℓ
  rw [Pi.add_apply, torusLoop_apply, torusLoop_apply]
  dsimp only
  simp only [torusCoord_add_torusStep, torusCoord_sub_torusStep, if_true, Fin.rev_inj]
  by_cases hi : i = j
  · subst hi
    simp only [true_and, if_true, sub_eq_iff_eq_add]
    exact add_comm _ _
  · simp only [hi, false_and, if_false, sub_zero, CharTwo.add_self_eq_zero]

/-- The first cut in direction `j` meets the first loop in direction `k` once when `j = k`, at the
edge `(j, 0)`, and not at all otherwise. -/
private theorem torusCut_dotProduct_torusLoop (j k : Fin 2) :
    torusCut L j 0 ⬝ᵥ torusLoop L k 0 = if j = k then 1 else 0 := by
  change ∑ ℓ : Fin (2 * (L * L)), torusCut L j 0 ℓ * torusLoop L k 0 ℓ = _
  rw [← (torusEdgeEquiv L).sum_comp, Finset.sum_eq_single (j, 0)]
  · rw [torusCut_apply, torusLoop_apply]
    simp only [and_true, if_true, one_mul]
  · rintro ⟨i, b⟩ _ hne
    rw [torusCut_apply, torusLoop_apply]
    dsimp only
    split_ifs with h1 h2
    · obtain ⟨rfl, hb⟩ := h1
      obtain ⟨rfl, hb'⟩ := h2
      exact absurd (by rw [torusPoint_ext L i hb hb']) hne
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A cut does not change along its own line: a step in the other direction. -/
private theorem torusCut_add_torusStep_of_ne {i j : Fin 2} (hi : i ≠ j) (a : TorusPoint L) :
    torusCut L j (a + torusStep L i) = torusCut L j a := by
  funext ℓ'
  obtain ⟨ℓ, rfl⟩ := (torusEdgeEquiv L).surjective ℓ'
  rw [torusCut_apply, torusCut_apply, torusCoord_add_torusStep, if_neg hi, add_zero]

/-- A loop does not change along its own line: a step in its direction. -/
private theorem torusLoop_add_torusStep_of_ne {i j : Fin 2} (hi : i ≠ j.rev) (a : TorusPoint L) :
    torusLoop L j (a + torusStep L i) = torusLoop L j a := by
  funext ℓ'
  obtain ⟨ℓ, rfl⟩ := (torusEdgeEquiv L).surjective ℓ'
  rw [torusLoop_apply, torusLoop_apply, torusCoord_add_torusStep, if_neg hi, add_zero]

/-- A cycle meets every cut in direction `j` with the same parity. -/
private theorem torusCut_dotProduct_eq (j : Fin 2) {v : Fin ((torusComplex L).cells 1) → ZMod 2}
    (hv : v ∈ (torusComplex L).cycles 1) (a : TorusPoint L) :
    torusCut L j a ⬝ᵥ v = torusCut L j 0 ⬝ᵥ v := by
  refine eq_of_step_invariant L (fun a => torusCut L j a ⬝ᵥ v) (fun a i => ?_) a
  by_cases hi : i = j
  · subst hi
    have h := BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles
      (torusCut_add_mem_coboundaries L i a) hv
    rw [add_dotProduct] at h
    exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add]; exact h)
  · exact congrArg (· ⬝ᵥ v) (torusCut_add_torusStep_of_ne L hi a)

/-- A cocycle meets every loop in direction `j` with the same parity. -/
private theorem torusLoop_dotProduct_eq (j : Fin 2) {u : Fin ((torusComplex L).cells 1) → ZMod 2}
    (hu : u ∈ (torusComplex L).cocycles 1) (a : TorusPoint L) :
    torusLoop L j a ⬝ᵥ u = torusLoop L j 0 ⬝ᵥ u := by
  refine eq_of_step_invariant L (fun a => torusLoop L j a ⬝ᵥ u) (fun a i => ?_) a
  by_cases hi : i = j.rev
  · subst hi
    have h := BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries hu
      (torusLoop_add_mem_boundaries L j a)
    rw [dotProduct_comm, add_dotProduct] at h
    exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add]; exact h)
  · exact congrArg (· ⬝ᵥ u) (torusLoop_add_torusStep_of_ne L hi a)

/-- A chain meeting every one of a family of sets indexed by the torus's points, the set at `a`
within the edges whose start has the coordinate of `a` in direction `k`, has at least `L` edges:
one on each of `L` disjoint sets. -/
private theorem le_card_of_cuts (k : Fin 2) (v : Fin ((torusComplex L).cells 1) → ZMod 2)
    (S : TorusPoint L → Fin ((torusComplex L).cells 1) → ZMod 2)
    (hS : ∀ a ℓ, S a ℓ ≠ 0 → torusCoord L k ((torusEdgeEquiv L).symm ℓ).2 = torusCoord L k a)
    (hv : ∀ a, S a ⬝ᵥ v ≠ 0) : L ≤ (Finset.univ.filter fun ℓ => v ℓ ≠ 0).card := by
  have hex : ∀ x : ZMod L, ∃ ℓ, S (x, x) ℓ ≠ 0 ∧ v ℓ ≠ 0 := by
    intro x
    have h := hv (x, x)
    rw [dotProduct] at h
    obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨ℓ, left_ne_zero_of_mul hℓ, right_ne_zero_of_mul hℓ⟩
  choose f hfS hfv using hex
  have hcoord : ∀ x, torusCoord L k ((torusEdgeEquiv L).symm (f x)).2 = x := by
    intro x
    rw [hS _ _ (hfS x)]
    fin_cases k <;> rfl
  calc L = (Finset.univ : Finset (ZMod L)).card := by rw [Finset.card_univ, ZMod.card]
    _ ≤ _ := Finset.card_le_card_of_injOn f
        (fun x _ => Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfv x⟩))
        (fun x _ y _ hxy => by rw [← hcoord x, ← hcoord y, hxy])

omit [NeZero L] in
/-- A cut or a loop is nonzero only on its own edges. -/
private theorem coord_eq_of_ite_ne_zero {p : Prop} [Decidable p] {q r : ZMod L}
    (h : (if p ∧ q = r then (1 : ZMod 2) else 0) ≠ 0) : q = r := by
  by_cases hc : p ∧ q = r
  · exact hc.2
  · exact absurd (if_neg hc) h

/-- The edges in direction `j` on the row `0` number `L`. -/
private theorem card_filter_torusEdge_row (j : Fin 2) :
    (Finset.univ.filter fun ℓ : Fin (2 * (L * L)) =>
      (if ((torusEdgeEquiv L).symm ℓ).1 = j ∧ ((torusEdgeEquiv L).symm ℓ).2.2 = 0 then (1 : ZMod 2)
        else 0) ≠ 0).card = L := by
  refine (Finset.card_nbij' (t := (Finset.univ : Finset (ZMod L)))
    (fun ℓ => ((torusEdgeEquiv L).symm ℓ).2.1)
    (fun x => torusEdgeEquiv L (j, (x, 0))) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun x _ => ?_) (fun ℓ hℓ => ?_) (fun x _ => ?_)).trans ?_
  · rw [Finset.mem_coe, Finset.mem_filter, Equiv.symm_apply_apply]
    exact ⟨Finset.mem_univ _, by rw [if_pos ⟨rfl, rfl⟩]; exact one_ne_zero⟩
  · rw [Finset.mem_coe, Finset.mem_filter] at hℓ
    by_cases hc : ((torusEdgeEquiv L).symm ℓ).1 = j ∧ ((torusEdgeEquiv L).symm ℓ).2.2 = 0
    · rw [Equiv.apply_eq_iff_eq_symm_apply]
      exact Prod.ext hc.1.symm (Prod.ext rfl hc.2.symm)
    · exact absurd (if_neg hc) hℓ.2
  · dsimp only
    rw [Equiv.symm_apply_apply]
  · rw [Finset.card_univ, ZMod.card]

/-- The cycles exceed the boundaries by two dimensions: `2L² - (L² - 1)` against `L² - 1`, the ranks
of `toricCode_k`. -/
private theorem finrank_torus_cycles_le :
    Module.finrank (ZMod 2) ((torusComplex L).cycles 1) ≤
      Module.finrank (ZMod 2) ((torusComplex L).boundaries 1) + Fintype.card (Fin 2) := by
  have h1 : Module.finrank (ZMod 2) ((torusComplex L).cycles 1) =
      2 * (L * L) - (toricCode L).1.rank :=
    finrank_cssZLogicalCarrier (toricCode L).1
  have h2 : Module.finrank (ZMod 2) ((torusComplex L).boundaries 1) =
      ((toricCode L).2)ᵀ.rank := rfl
  rw [h1, h2, Matrix.rank_transpose, rank_eq_of_sum_eq_zero _ (torusPointEquiv L) 0
      (sum_toricCode_fst L) (linearIndependent_toric_rows L _ (toric_rel_X L)),
    rank_eq_of_sum_eq_zero _ (torusPointEquiv L) 0 (sum_toricCode_snd L)
      (linearIndependent_toric_rows L _ (toric_rel_Z L)), Fintype.card_prod, ZMod.card,
    Fintype.card_fin]
  generalize L * L = N
  omega

/-- The cocycles exceed the coboundaries by two dimensions, as the cycles do the boundaries. -/
private theorem finrank_torus_cocycles_le :
    Module.finrank (ZMod 2) ((torusComplex L).cocycles 1) ≤
      Module.finrank (ZMod 2) ((torusComplex L).coboundaries 1) + Fintype.card (Fin 2) := by
  have h1 : Module.finrank (ZMod 2) ((torusComplex L).cocycles 1) =
      2 * (L * L) - (toricCode L).2.rank :=
    finrank_cssXLogicalCarrier (toricCode L).2
  have h2 : Module.finrank (ZMod 2) ((torusComplex L).coboundaries 1) =
      ((toricCode L).1)ᵀ.rank := rfl
  rw [h1, h2, Matrix.rank_transpose, rank_eq_of_sum_eq_zero _ (torusPointEquiv L) 0
      (sum_toricCode_fst L) (linearIndependent_toric_rows L _ (toric_rel_X L)),
    rank_eq_of_sum_eq_zero _ (torusPointEquiv L) 0 (sum_toricCode_snd L)
      (linearIndependent_toric_rows L _ (toric_rel_Z L)), Fintype.card_prod, ZMod.card,
    Fintype.card_fin]
  generalize L * L = N
  omega

/-- A cycle that is not a boundary meets the first cut in some direction oddly. -/
private theorem exists_torusCut_dotProduct_ne_zero {v : Fin ((torusComplex L).cells 1) → ZMod 2}
    (hv : v ∈ (torusComplex L).cycles 1) (hnb : v ∉ (torusComplex L).boundaries 1) :
    ∃ j, torusCut L j 0 ⬝ᵥ v ≠ 0 := by
  by_contra h
  exact hnb (mem_of_finrank_le_of_apply_eq_zero ((torusComplex L).cycles 1)
    ((torusComplex L).boundaries 1)
    (cssZLogicalSubspace_le_cssZLogicalCarrier (cssOfComplex_isCSSPair (torusComplex L) 1))
    (finrank_torus_cycles_le L) (fun j => dotProductLin (torusCut L j 0))
    (fun j _ hb => BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries
      (torusCut_mem_cocycles L j 0) hb)
    (fun k => torusLoop L k 0) (fun k => torusLoop_mem_cycles L k 0)
    (fun j k => torusCut_dotProduct_torusLoop L j k) hv
    (fun j => not_not.1 fun hj => h ⟨j, hj⟩))

/-- A cocycle that is not a coboundary meets the first loop in some direction oddly. -/
private theorem exists_torusLoop_dotProduct_ne_zero {u : Fin ((torusComplex L).cells 1) → ZMod 2}
    (hu : u ∈ (torusComplex L).cocycles 1) (hnc : u ∉ (torusComplex L).coboundaries 1) :
    ∃ j, torusLoop L j 0 ⬝ᵥ u ≠ 0 := by
  by_contra h
  refine hnc (mem_of_finrank_le_of_apply_eq_zero ((torusComplex L).cocycles 1)
    ((torusComplex L).coboundaries 1)
    (cssXLogicalSubspace_le_cssXLogicalCarrier (cssOfComplex_isCSSPair (torusComplex L) 1))
    (finrank_torus_cocycles_le L) (fun j => dotProductLin (torusLoop L j 0)) (fun j c hc => ?_)
    (fun k => torusCut L k 0) (fun k => torusCut_mem_cocycles L k 0) (fun j k => ?_) hu
    (fun j => not_not.1 fun hj => h ⟨j, hj⟩))
  · change torusLoop L j 0 ⬝ᵥ c = 0
    rw [dotProduct_comm]
    exact BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles hc
      (torusLoop_mem_cycles L j 0)
  · change torusLoop L j 0 ⬝ᵥ torusCut L k 0 = _
    rw [dotProduct_comm, torusCut_dotProduct_torusLoop]
    exact if_congr eq_comm rfl rfl

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h1c1a0d539819
-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h66af746f66e3
/-- **The toric code has distance `L`, for both check types.** `Z` type: every cycle that is not a
boundary has weight at least `L`, and `torusRowLoop` is such a cycle of weight `L`. `X` type, on the
dual lattice: every cocycle that is not a coboundary has weight at least `L`, and `torusDualLoop` is
such a cocycle of weight `L`. Through `nontrivial_Zlogical_iff_homology` and
`nontrivial_Xlogical_iff_cohomology` these are the nontrivial logical operators of each type. The
source states `d = L` without proof; the cut argument is inferred (docs/fidelity/T34.md,
Claim 6). -/
theorem toricCode_distance :
    ((∀ v ∈ (torusComplex L).cycles 1, v ∉ (torusComplex L).boundaries 1 →
        L ≤ (Finset.univ.filter fun ℓ => v ℓ ≠ 0).card) ∧
      torusRowLoop L ∈ (torusComplex L).cycles 1 ∧
      torusRowLoop L ∉ (torusComplex L).boundaries 1 ∧
      (Finset.univ.filter fun ℓ => torusRowLoop L ℓ ≠ 0).card = L) ∧
    ((∀ v ∈ (torusComplex L).cocycles 1, v ∉ (torusComplex L).coboundaries 1 →
        L ≤ (Finset.univ.filter fun ℓ => v ℓ ≠ 0).card) ∧
      torusDualLoop L ∈ (torusComplex L).cocycles 1 ∧
      torusDualLoop L ∉ (torusComplex L).coboundaries 1 ∧
      (Finset.univ.filter fun ℓ => torusDualLoop L ℓ ≠ 0).card = L) := by
  have hrow : torusRowLoop L = torusLoop L 0 0 := rfl
  have hdual : torusDualLoop L = torusCut L 1 0 := rfl
  refine ⟨⟨fun v hv hnb => ?_, ?_, fun hb => ?_, card_filter_torusEdge_row L 0⟩,
    ⟨fun u hu hnc => ?_, ?_, fun hc => ?_, card_filter_torusEdge_row L 1⟩⟩
  · obtain ⟨j, hj⟩ := exists_torusCut_dotProduct_ne_zero L hv hnb
    exact le_card_of_cuts L j v (torusCut L j) (fun a ℓ h => coord_eq_of_ite_ne_zero L h)
      (fun a => by rw [torusCut_dotProduct_eq L j hv a]; exact hj)
  · rw [hrow]
    exact torusLoop_mem_cycles L 0 0
  · have h := BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries
      (torusCut_mem_cocycles L 0 0) hb
    rw [hrow, torusCut_dotProduct_torusLoop, if_pos rfl] at h
    exact one_ne_zero h
  · obtain ⟨j, hj⟩ := exists_torusLoop_dotProduct_ne_zero L hu hnc
    exact le_card_of_cuts L j.rev u (torusLoop L j) (fun a ℓ h => coord_eq_of_ite_ne_zero L h)
      (fun a => by rw [torusLoop_dotProduct_eq L j hu a]; exact hj)
  · rw [hdual]
    exact torusCut_mem_cocycles L 1 0
  · have h := BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles hc
      (torusLoop_mem_cycles L 1 0)
    rw [hdual, torusCut_dotProduct_torusLoop, if_pos rfl] at h
    exact one_ne_zero h

end Torus

/-! ### The planar patch -/

/-- The incidence of a path of `m` vertices: its edge `e` joins the vertices `e` and `e + 1`. -/
def pathIncidence (m : ℕ) : Matrix (Fin m) (Fin (m - 1)) (ZMod 2) :=
  Matrix.of fun v e => if (v : ℕ) = e ∨ (v : ℕ) = e + 1 then 1 else 0

/-- A path of `m` vertices as a based complex: vertices in degree `0`, edges in degree `1`. -/
def pathComplex (m : ℕ) : BasedComplex :=
  BasedComplex.twoTerm (pathIncidence m)

/-- The grid of `L` columns and `L + 1` rows of vertices: the tensor product of the column path and
the row path. -/
def gridComplex : BasedComplex :=
  (pathComplex L).tensor (pathComplex (L + 1))

/-- A cell of the grid of degree `i` as its pair `⟨p, c, r⟩`: `c` a cell of the column path of
degree `p`, `r` a cell of the row path of degree `i - p`. -/
def gridCellEquiv (i : ℕ) :
    Fin ((gridComplex L).cells i) ≃
      (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex i :=
  ((pathComplex L).tensorCellEquiv (pathComplex (L + 1)).toBasedPrecomplex i).symm

/-- A cell of the grid lies on a rough boundary when its row factor is a vertex on row `0` or row
`L`: those vertices, and the horizontal edges between them. -/
def OnRoughBoundary (i : ℕ) (σ : Fin ((gridComplex L).cells i)) : Prop :=
  ((gridCellEquiv L i σ).1 : ℕ) = i ∧
    (((gridCellEquiv L i σ).2.2 : ℕ) = 0 ∨ ((gridCellEquiv L i σ).2.2 : ℕ) = L)

instance (i : ℕ) : DecidablePred (OnRoughBoundary L i) := fun _ => by
  unfold OnRoughBoundary
  infer_instance

/-- The rough boundaries are closed under the boundary: a cell in the boundary of a cell on a rough
boundary is on it too. -/
theorem onRoughBoundary_of_d_ne_zero (i : ℕ) (σ : Fin ((gridComplex L).cells (i + 1)))
    (τ : Fin ((gridComplex L).cells i)) (hσ : OnRoughBoundary L (i + 1) σ)
    (hne : (gridComplex L).d i τ σ ≠ 0) : OnRoughBoundary L i τ := by
  have hd : (gridComplex L).d i τ σ = (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex i (gridCellEquiv L i τ)
      (gridCellEquiv L (i + 1) σ) := rfl
  unfold OnRoughBoundary at hσ ⊢
  rw [hd] at hne
  generalize gridCellEquiv L i τ = x at hne ⊢
  generalize gridCellEquiv L (i + 1) σ = y at hne hσ
  obtain ⟨p, c, r⟩ := x
  obtain ⟨q, c', r'⟩ := y
  dsimp only at hσ hne ⊢
  obtain ⟨hq, hr'⟩ := hσ
  have hp := p.isLt
  have hsame : sameCell (pathComplex L).cells p q c c' = 0 := by
    rw [sameCell, if_neg]
    rintro ⟨h, -⟩
    omega
  rw [BasedPrecomplex.tensorIncidence, hsame, zero_mul, add_zero] at hne
  have hqp : (q : ℕ) = p + 1 := by
    by_contra h
    exact left_ne_zero_of_mul hne (BasedPrecomplex.incidence_eq_zero_of_ne _ h _ _)
  have hrow := right_ne_zero_of_mul hne
  rw [sameCell] at hrow
  split_ifs at hrow with h
  · refine ⟨by omega, ?_⟩
    rw [h.2]
    exact hr'
  · exact absurd rfl hrow

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143 figure:fig_planar
/-- The **rough boundaries** of the patch, the top and bottom rows, as a subcomplex of the grid. -/
def roughBoundary : (gridComplex L).Subcomplex where
  cellSet i := Finset.univ.filter (OnRoughBoundary L i)
  support_boundary_subset i σ τ hσ hne := by
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨Finset.mem_univ _, onRoughBoundary_of_d_ne_zero L i σ τ hσ.2 hne⟩

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hcc80b9737850
-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h6c7addffa91c
/-- The **planar patch** as T43's relative complex: the grid modulo its rough boundaries. Its
cycles of degree `1` are the cycles relative to the rough edges. -/
def planarComplex : BasedComplex :=
  ⟨relative (gridComplex L) (roughBoundary L), relative_d_comp_d _ _⟩

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hcc80b9737850
/-- The **planar code**: the CSS pair at degree `1` of the planar patch. Its stars have three edges
on the smooth boundaries (the left and right columns), its plaquettes three edges on the rough
ones. -/
def planarCode :=
  cssOfComplex (planarComplex L) 1

/-- The incidence of the grid between a vertex `x` and the vertical edge `⟨0, a, e⟩`, column vertex
`a` and row edge `e`: `1` when `x` is in column `a` on row `e` or row `e + 1`. -/
private theorem tensorIncidence_vertex_vertical
    (x : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 0)
    (a : Fin ((pathComplex L).cells ((0 : Fin 2) : ℕ)))
    (e : Fin ((pathComplex (L + 1)).cells (1 - ((0 : Fin 2) : ℕ)))) :
    (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x ⟨0, a, e⟩ =
      if (x.2.1 : ℕ) = a ∧ ((x.2.2 : ℕ) = e ∨ (x.2.2 : ℕ) = e + 1) then 1 else 0 := by
  obtain ⟨p, a', r⟩ := x
  obtain rfl : p = 0 := Fin.fin_one_eq_zero p
  change (0 : ZMod 2) * _ + (if (0 : ℕ) = 0 ∧ (a' : ℕ) = a then (1 : ZMod 2) else 0) *
      (if (r : ℕ) = e ∨ (r : ℕ) = e + 1 then 1 else 0) = _
  simp only [zero_mul, zero_add, true_and, ite_mul, one_mul, ← ite_and]

/-- The incidence of the grid between the vertical edge `⟨0, a, e⟩` and a face `τ`: `1` when `a` is
an end of the face's column edge and `e` is its row edge. -/
private theorem tensorIncidence_vertical_face
    (a : Fin ((pathComplex L).cells ((0 : Fin 2) : ℕ)))
    (e : Fin ((pathComplex (L + 1)).cells (1 - ((0 : Fin 2) : ℕ))))
    (τ : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 2)
    (hτ : (τ.1 : ℕ) = 1) :
    (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 ⟨0, a, e⟩ τ =
      if ((a : ℕ) = τ.2.1 ∨ (a : ℕ) = τ.2.1 + 1) ∧ (e : ℕ) = τ.2.2 then 1 else 0 := by
  obtain ⟨⟨q, hq⟩, ce, re⟩ := τ
  obtain rfl : q = 1 := hτ
  change (if (a : ℕ) = ce ∨ (a : ℕ) = ce + 1 then (1 : ZMod 2) else 0) *
      (if (1 : ℕ) = 1 ∧ (e : ℕ) = re then 1 else 0) +
    (if (0 : ℕ) = 1 ∧ (a : ℕ) = ce then 1 else 0) * _ = _
  simp only [true_and, ite_mul, one_mul, zero_mul, ← ite_and, zero_ne_one, false_and, if_false,
    add_zero]

/-- Every face of the grid is a pair of a column edge and a row edge. -/
private theorem face_fst
    (τ : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 2) : (τ.1 : ℕ) = 1 := by
  obtain ⟨⟨q, hq⟩, ce, re⟩ := τ
  rcases q with _ | _ | _ | q
  · exact Fin.elim0 (re : Fin 0)
  · rfl
  · exact Fin.elim0 (ce : Fin 0)
  · omega

/-- Two vertices of the grid with the same column and row are the same vertex. -/
private theorem vertex_ext
    (x y : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 0)
    (h1 : (x.2.1 : ℕ) = y.2.1) (h2 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  obtain ⟨p, a, r⟩ := x
  obtain ⟨q, b, s⟩ := y
  obtain rfl : p = 0 := Fin.fin_one_eq_zero p
  obtain rfl : q = 0 := Fin.fin_one_eq_zero q
  obtain rfl : a = b := Fin.ext h1
  obtain rfl : r = s := Fin.ext h2
  rfl

/-- Two faces of the grid with the same column edge and row edge are the same face. -/
private theorem face_ext
    (x y : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 2)
    (h1 : (x.2.1 : ℕ) = y.2.1) (h2 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  have hx := face_fst L x
  have hy := face_fst L y
  obtain ⟨⟨p, hp⟩, a, r⟩ := x
  obtain ⟨⟨q, hq⟩, b, s⟩ := y
  obtain rfl : p = 1 := hx
  obtain rfl : q = 1 := hy
  obtain rfl : a = b := Fin.ext h1
  obtain rfl : r = s := Fin.ext h2
  rfl

/-- A function on the grid's vertices that vanishes on the bottom row, and whose sum on the two
ends of each vertical edge vanishes, vanishes: induction up the rows. -/
private theorem grid_vertex_eq_zero
    (c : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 0 → ZMod 2)
    (h0 : ∀ x, (x.2.2 : ℕ) = 0 → c x = 0)
    (hrel : ∀ (a : Fin ((pathComplex L).cells ((0 : Fin 2) : ℕ)))
      (e : Fin ((pathComplex (L + 1)).cells (1 - ((0 : Fin 2) : ℕ)))),
      ∑ x, c x * (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x
        ⟨0, a, e⟩ = 0)
    (x : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 0) : c x = 0 := by
  suffices h : ∀ n x, ((x : (pathComplex L).TensorCell
      (pathComplex (L + 1)).toBasedPrecomplex 0).2.2 : ℕ) = n → c x = 0 from h _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx
  rcases n with _ | n
  · exact h0 x hx
  have hb : ∀ y : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 0,
      (y.2.1 : ℕ) < L ∧ (y.2.2 : ℕ) < L + 1 := by
    rintro ⟨p, a, r⟩
    obtain rfl : p = 0 := Fin.fin_one_eq_zero p
    exact ⟨a.isLt, r.isLt⟩
  obtain ⟨ha, hr⟩ := hb x
  have hsum := hrel ⟨x.2.1, ha⟩ ⟨n, by change n < L + 1 - 1; omega⟩
  rw [Finset.sum_eq_single x] at hsum
  · rw [tensorIncidence_vertex_vertical, if_pos ⟨rfl, Or.inr hx⟩, mul_one] at hsum
    exact hsum
  · intro x' _ hne
    rw [tensorIncidence_vertex_vertical]
    split_ifs with hc
    · obtain ⟨h1', h2' | h2'⟩ := hc
      · rw [ih n (by omega) x' h2', zero_mul]
      · exact absurd (vertex_ext L x' x h1' (by rw [h2', hx])) hne
    · rw [mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A function on the grid's faces whose sum on the faces beside each vertical edge vanishes
vanishes: induction from the left column. -/
private theorem grid_face_eq_zero
    (c : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 2 → ZMod 2)
    (hrel : ∀ (a : Fin ((pathComplex L).cells ((0 : Fin 2) : ℕ)))
      (e : Fin ((pathComplex (L + 1)).cells (1 - ((0 : Fin 2) : ℕ)))),
      ∑ τ, c τ * (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1
        ⟨0, a, e⟩ τ = 0)
    (τ : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 2) : c τ = 0 := by
  suffices h : ∀ n τ, ((τ : (pathComplex L).TensorCell
      (pathComplex (L + 1)).toBasedPrecomplex 2).2.1 : ℕ) = n → c τ = 0 from h _ τ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro τ hτ
  have h1 := face_fst L τ
  have hb : ∀ y : (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex 2,
      (y.2.1 : ℕ) < L - 1 ∧ (y.2.2 : ℕ) < L + 1 - 1 := by
    intro y
    have hy := face_fst L y
    obtain ⟨⟨q, hq⟩, ce, re⟩ := y
    obtain rfl : q = 1 := hy
    exact ⟨ce.isLt, re.isLt⟩
  obtain ⟨ha, hr⟩ := hb τ
  have hsum := hrel ⟨n, by change n < L; omega⟩ ⟨τ.2.2, hr⟩
  rw [Finset.sum_eq_single τ] at hsum
  · rw [tensorIncidence_vertical_face L _ _ τ h1, if_pos ⟨Or.inl hτ.symm, rfl⟩, mul_one] at hsum
    exact hsum
  · intro τ' _ hne
    rw [tensorIncidence_vertical_face L _ _ τ' (face_fst L τ')]
    split_ifs with hc
    · obtain ⟨h1' | h1', h2'⟩ := hc
      · exact absurd (face_ext L τ' τ (by rw [← h1', hτ]) h2'.symm) hne
      · rw [ih (τ'.2.1 : ℕ) (by simp only at h1'; omega) τ' rfl, zero_mul]
    · rw [mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The stars of the patch are independent: a relation among them vanishes on the bottom rough
row and is constant up each column. -/
private theorem linearIndependent_planarCode_fst :
    LinearIndependent (ZMod 2) fun b => (planarCode L).1 b := by
  refine linearIndependent_submatrix_rows ((gridComplex L).d 0) ((roughBoundary L).otherCell 0)
    ((roughBoundary L).otherCell _).injective ((roughBoundary L).otherCell 1) ?_
  intro c hc0 hrel
  funext σ
  have h := grid_vertex_eq_zero L (fun x => c ((gridCellEquiv L 0).symm x)) ?_ ?_
    (gridCellEquiv L 0 σ)
  · change c ((gridCellEquiv L 0).symm (gridCellEquiv L 0 σ)) = 0 at h
    rwa [Equiv.symm_apply_apply] at h
  · intro x hx
    refine hc0 _ ?_
    rw [mem_range_otherCell, not_not]
    change _ ∈ Finset.univ.filter (OnRoughBoundary L 0)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold OnRoughBoundary
    generalize hy : gridCellEquiv L 0 ((gridCellEquiv L 0).symm x) = y
    rw [Equiv.apply_symm_apply] at hy
    subst hy
    exact ⟨Fin.val_eq_zero _, Or.inl hx⟩
  · intro a e
    obtain ⟨j, hj⟩ : (gridCellEquiv L 1).symm ⟨0, a, e⟩ ∈
        Set.range ((roughBoundary L).otherCell 1) := by
      rw [mem_range_otherCell]
      change _ ∉ Finset.univ.filter (OnRoughBoundary L 1)
      rw [Finset.mem_filter]
      intro h
      have h1 := h.2.1
      rw [Equiv.apply_symm_apply] at h1
      exact Nat.zero_ne_one h1
    have hj' := hrel j
    rw [hj, ← (gridCellEquiv L 0).symm.sum_comp] at hj'
    rw [← hj']
    refine Finset.sum_congr rfl fun x _ => ?_
    change _ = _ * (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0
      (gridCellEquiv L 0 ((gridCellEquiv L 0).symm x))
      (gridCellEquiv L 1 ((gridCellEquiv L 1).symm ⟨0, a, e⟩))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The plaquettes of the patch are independent: a relation among them vanishes on the left
column and is constant along each row. -/
private theorem linearIndependent_planarCode_snd :
    LinearIndependent (ZMod 2) fun f => (planarCode L).2 f := by
  refine linearIndependent_submatrix_rows ((gridComplex L).d 1)ᵀ ((roughBoundary L).otherCell 2)
    ((roughBoundary L).otherCell _).injective ((roughBoundary L).otherCell 1) ?_
  intro c _ hrel
  funext τ
  have h := grid_face_eq_zero L (fun x => c ((gridCellEquiv L 2).symm x)) ?_
    (gridCellEquiv L 2 τ)
  · change c ((gridCellEquiv L 2).symm (gridCellEquiv L 2 τ)) = 0 at h
    rwa [Equiv.symm_apply_apply] at h
  · intro a e
    obtain ⟨j, hj⟩ : (gridCellEquiv L 1).symm ⟨0, a, e⟩ ∈
        Set.range ((roughBoundary L).otherCell 1) := by
      rw [mem_range_otherCell]
      change _ ∉ Finset.univ.filter (OnRoughBoundary L 1)
      rw [Finset.mem_filter]
      intro h
      have h1 := h.2.1
      rw [Equiv.apply_symm_apply] at h1
      exact Nat.zero_ne_one h1
    have hj' := hrel j
    rw [hj, ← (gridCellEquiv L 2).symm.sum_comp] at hj'
    rw [← hj']
    refine Finset.sum_congr rfl fun x _ => ?_
    change _ = _ * (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1
      (gridCellEquiv L 1 ((gridCellEquiv L 1).symm ⟨0, a, e⟩))
      (gridCellEquiv L (1 + 1) ((gridCellEquiv L 2).symm x))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### The planar code's parameters

The patch's cells are counted on the pairs of the tensor product: the column path has `L` vertices
and `L - 1` edges, the row path `L + 1` vertices and `L` edges, and the rough boundaries' `2L`
vertices and `2(L - 1)` edges are taken away. -/

/-- A cell of the grid of degree `i`, as a pair of a cell of the column path and a cell of the row
path. -/
private abbrev GridCell (i : ℕ) : Type :=
  (pathComplex L).TensorCell (pathComplex (L + 1)).toBasedPrecomplex i

/-- The rows at the two ends of the row path, `0` and `L`, are two. -/
private theorem sum_ite_rough_row [NeZero L] :
    ∑ r : Fin (L + 1), (if (r : ℕ) = 0 ∨ (r : ℕ) = L then 1 else 0) = 2 := by
  rw [← Finset.card_filter]
  have h : (Finset.univ.filter fun r : Fin (L + 1) => (r : ℕ) = 0 ∨ (r : ℕ) = L) =
      {0, Fin.last L} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, Fin.val_last]
  rw [h, Finset.card_pair]
  intro h0
  have h1 := congrArg Fin.val h0
  rw [Fin.val_zero, Fin.val_last] at h1
  exact NeZero.ne L h1.symm

/-- The grid's cells of degree `i` on the rough boundaries, counted on the pairs. -/
private theorem card_cellSet_roughBoundary (i : ℕ) :
    ((roughBoundary L).cellSet i).card = ∑ x : GridCell L i,
      if (x.1 : ℕ) = i ∧ ((x.2.2 : ℕ) = 0 ∨ (x.2.2 : ℕ) = L) then 1 else 0 := by
  change (Finset.univ.filter (OnRoughBoundary L i)).card = _
  rw [Finset.card_filter]
  exact (Finset.sum_congr rfl fun σ _ => if_congr Iff.rfl rfl rfl).trans
    (Equiv.sum_comp (gridCellEquiv L i)
      fun x => if (x.1 : ℕ) = i ∧ ((x.2.2 : ℕ) = 0 ∨ (x.2.2 : ℕ) = L) then 1 else 0)

/-- The patch's cells of degree `i`: the grid's, less those on the rough boundaries. -/
private theorem planarComplex_cells (i : ℕ) :
    (planarComplex L).cells i = (gridComplex L).cells i - ((roughBoundary L).cellSet i).card := by
  change ((roughBoundary L).cellSet i)ᶜ.card = _
  rw [Finset.card_compl, Fintype.card_fin]

/-- The grid's vertices: `L` columns by `L + 1` rows. -/
private theorem gridComplex_cells_zero : (gridComplex L).cells 0 = L * (L + 1) := by
  change ∑ p : Fin 1, (pathComplex L).cells p * (pathComplex (L + 1)).cells (0 - p) = _
  rw [Fin.sum_univ_one]
  rfl

/-- The grid's edges: `L` columns of `L` vertical edges, and `L + 1` rows of `L - 1` horizontal
edges. -/
private theorem gridComplex_cells_one :
    (gridComplex L).cells 1 = L * (L + 1 - 1) + (L - 1) * (L + 1) := by
  change ∑ p : Fin 2, (pathComplex L).cells p * (pathComplex (L + 1)).cells (1 - p) = _
  rw [Fin.sum_univ_two]
  rfl

/-- The grid's faces: `L - 1` columns by `L` rows. -/
private theorem gridComplex_cells_two :
    (gridComplex L).cells 2 = L * 0 + (L - 1) * (L + 1 - 1) + 0 * (L + 1) := by
  change ∑ p : Fin 3, (pathComplex L).cells p * (pathComplex (L + 1)).cells (2 - p) = _
  rw [Fin.sum_univ_three]
  rfl

/-- The vertices on the rough boundaries: the `L` columns on rows `0` and `L`. -/
private theorem card_roughBoundary_zero [NeZero L] :
    ((roughBoundary L).cellSet 0).card = L * 2 := by
  rw [card_cellSet_roughBoundary, Fintype.sum_sigma, Fin.sum_univ_one, Fintype.sum_prod_type]
  change ∑ c : Fin L, ∑ r : Fin (L + 1),
    (if (0 : ℕ) = 0 ∧ ((r : ℕ) = 0 ∨ (r : ℕ) = L) then 1 else 0) = _
  simp only [true_and, sum_ite_rough_row, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

/-- The edges on the rough boundaries: the `L - 1` horizontal edges of rows `0` and `L`. -/
private theorem card_roughBoundary_one [NeZero L] :
    ((roughBoundary L).cellSet 1).card = (L - 1) * 2 := by
  rw [card_cellSet_roughBoundary, Fintype.sum_sigma, Fin.sum_univ_two, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  change (∑ a : Fin L, ∑ e : Fin (L + 1 - 1),
      (if (0 : ℕ) = 1 ∧ ((e : ℕ) = 0 ∨ (e : ℕ) = L) then 1 else 0)) +
    ∑ c : Fin (L - 1), ∑ r : Fin (L + 1),
      (if (1 : ℕ) = 1 ∧ ((r : ℕ) = 0 ∨ (r : ℕ) = L) then 1 else 0) = _
  simp only [zero_ne_one, false_and, if_false, Finset.sum_const_zero, zero_add, true_and,
    sum_ite_rough_row, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- No face is on the rough boundaries. -/
private theorem card_roughBoundary_two : ((roughBoundary L).cellSet 2).card = 0 := by
  rw [card_cellSet_roughBoundary]
  exact Finset.sum_eq_zero fun x _ => if_neg fun h => by
    have hx := face_fst L x
    omega

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hc1165ba8cd2d
/-- The patch has one edge more than it has vertices and faces together: `L² + (L - 1)²` edges,
`L(L - 1)` vertices and `L(L - 1)` faces, the source's count. -/
private theorem planarComplex_cells_one [NeZero L] :
    (planarComplex L).cells 1 = (planarComplex L).cells 0 + (planarComplex L).cells 2 + 1 := by
  rw [planarComplex_cells, planarComplex_cells, planarComplex_cells, card_roughBoundary_zero,
    card_roughBoundary_one, card_roughBoundary_two, gridComplex_cells_zero, gridComplex_cells_one,
    gridComplex_cells_two]
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos L)).symm⟩
  have h1 : (m + 1) * (m + 1 + 1 - 1) + (m + 1 - 1) * (m + 1 + 1) =
      (m + 1 - 1) * 2 + (2 * (m * m) + 2 * m + 1) := by
    simp only [Nat.add_sub_cancel]
    ring
  have h2 : (m + 1) * (m + 1 + 1) = (m + 1) * 2 + m * (m + 1) := by ring
  have h3 : (m + 1) * 0 + (m + 1 - 1) * (m + 1 + 1 - 1) + 0 * (m + 1 + 1) - 0 = m * (m + 1) := by
    simp only [Nat.add_sub_cancel, mul_zero, zero_mul, zero_add, add_zero, Nat.sub_zero]
  rw [h1, h2, h3, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  ring

/-- A matrix whose rows are independent has rank its number of rows. -/
private theorem rank_eq_of_linearIndependent {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : LinearIndependent (ZMod 2) fun i => M i) : M.rank = m := by
  rw [Matrix.rank_eq_finrank_span_row]
  exact (finrank_span_eq_card h).trans (Fintype.card_fin m)

/-- The star matrix of the patch has rank its number of vertices. -/
private theorem rank_planarCode_fst : (planarCode L).1.rank = (planarComplex L).cells 0 :=
  rank_eq_of_linearIndependent _ (linearIndependent_planarCode_fst L)

/-- The plaquette matrix of the patch has rank its number of faces. -/
private theorem rank_planarCode_snd : (planarCode L).2.rank = (planarComplex L).cells 2 :=
  rank_eq_of_linearIndependent _ (linearIndependent_planarCode_snd L)

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hc1165ba8cd2d
-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h894fa9154918
/-- **The planar code encodes one qubit**: its `Z`-logical space, the relative homology in degree
`1`, has dimension `1`, at every `L ≥ 1`. -/
theorem planarCode_k [NeZero L] :
    Module.finrank (ZMod 2) (cssZLogical (planarCode L).1 (planarCode L).2) = 1 := by
  -- `k = n - rk H_X - rk H_Z` with every star and every plaquette independent: the source's
  -- `L² + (L - 1)² - 2L(L - 1) = 1`.
  have hcss : IsCSSPair (planarCode L).1 (planarCode L).2 := cssOfComplex_isCSSPair _ _
  rw [finrank_cssZLogical hcss, rank_planarCode_fst, rank_planarCode_snd]
  have h := planarComplex_cells_one L
  omega

/-- The generators T29's encoder takes on the patch: every star and every plaquette, as Paulis. -/
def planarGens :
    Fin ((planarComplex L).cellsBelow 1) ⊕ Fin ((planarComplex L).cells 2) →
      Pauli ((planarComplex L).cells 1) :=
  Sum.elim (cssXGen (planarCode L).1) (cssZGen (planarCode L).2)

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hc1165ba8cd2d
/-- **An independent generating set of the planar code's stabilizer**: every star and every
plaquette of the patch (`planarGens`) are linearly independent and generate the stabilizer. -/
theorem planarCode_independentGens [NeZero L] :
    LinearIndependent (ZMod 2) (planarGens L) ∧
      Submodule.span (ZMod 2) (Set.range (planarGens L)) =
        cssStabilizer (planarCode L).1 (planarCode L).2 := by
  refine ⟨?_, ?_⟩
  · exact linearIndependent_sum_elim_xz _ _ (linearIndependent_planarCode_fst L)
      (linearIndependent_planarCode_snd L)
  · rw [planarGens, Set.Sum.elim_range, Submodule.span_union]
    rfl

/-- The column of vertical edges at column `0`, from the bottom rough boundary to the top one: a
`Z` string on a nontrivial relative cycle, of weight `L`. -/
def planarZString : Fin ((planarComplex L).cells 1) → ZMod 2 := fun b =>
  if ((gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)).1 : ℕ) = 0 ∧
      ((gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)).2.1 : ℕ) = 0 then 1 else 0

/-- The vertical edges between rows `0` and `1`, from the left smooth boundary to the right one:
an `X` string on a nontrivial relative cycle of the dual lattice, of weight `L`. -/
def planarXString : Fin ((planarComplex L).cells 1) → ZMod 2 := fun b =>
  if ((gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)).1 : ℕ) = 0 ∧
      ((gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)).2.2 : ℕ) = 0 then 1 else 0

/-! ### The planar code's distance

The cut argument on the patch (inferred, docs/fidelity/T34.md, Claim 13). The grid's edges are read
on their pairs: a vertical edge `⟨0, a, e⟩` joins the vertices of column `a` on rows `e` and
`e + 1`, a horizontal edge `⟨1, c, r⟩` the vertices of columns `c` and `c + 1` on row `r`. The cut
`gridCut k` is the `L` vertical edges from row `k` to row `k + 1`, and the column `gridColumn a` the
`L` vertical edges of column `a`; neither has an edge on the rough boundaries. A cut is a relative
cocycle, and two neighbouring cuts differ by the coboundary of the row of vertices between them, so
a relative cycle meets every cut with the same parity. A column is a relative cycle, its two ends on
the rough rows, and two neighbouring columns differ by the relative boundary of the faces between
them, so a relative cocycle meets every column with the same parity. Each cut meets each column
once, and the cycles exceed the boundaries by one dimension (the count of `planarCode_k`), so a
relative cycle that is not a boundary meets the first cut oddly
(`mem_of_finrank_le_of_apply_eq_zero`), hence each of the `L` disjoint cuts. The cocycles are
argued the same way with the cuts and the columns exchanged. -/

/-- The cut between rows `k` and `k + 1`: the vertical edges whose row edge is `k`. -/
private def gridCut (k : ℕ) (y : GridCell L 1) : ZMod 2 :=
  if (y.1 : ℕ) = 0 ∧ (y.2.2 : ℕ) = k then 1 else 0

/-- The column `a`: the vertical edges whose column vertex is `a`. -/
private def gridColumn (a : ℕ) (y : GridCell L 1) : ZMod 2 :=
  if (y.1 : ℕ) = 0 ∧ (y.2.1 : ℕ) = a then 1 else 0

/-- The vertices on row `r`. -/
private def gridRow (r : ℕ) (x : GridCell L 0) : ZMod 2 :=
  if (x.2.2 : ℕ) = r then 1 else 0

/-- The faces between columns `c` and `c + 1`: those whose column edge is `c`. -/
private def gridFaceColumn (c : ℕ) (z : GridCell L 2) : ZMod 2 :=
  if (z.2.1 : ℕ) = c then 1 else 0

/-- A chain of the grid read on the patch's edges, the grid's edges off the rough boundaries. -/
private def planarChain (F : GridCell L 1 → ZMod 2) : Fin ((planarComplex L).cells 1) → ZMod 2 :=
  fun b => F (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b))

/-- The vertex of column `c` on row `r`. -/
private def gridVertex (c r : ℕ) (hc : c < L) (hr : r < L + 1) : GridCell L 0 :=
  ⟨0, ⟨c, hc⟩, ⟨r, hr⟩⟩

/-- The vertical edge of column `a` from row `e` to row `e + 1`. -/
private def gridVertical (a e : ℕ) (ha : a < L) (he : e < L) : GridCell L 1 :=
  ⟨0, ⟨a, ha⟩, ⟨e, by change e < L + 1 - 1; omega⟩⟩

/-- The face between columns `c` and `c + 1` and rows `r` and `r + 1`. -/
private def gridFace (c r : ℕ) (hc : c + 1 < L) (hr : r < L) : GridCell L 2 :=
  ⟨⟨1, by omega⟩, ⟨c, by change c < L - 1; omega⟩, ⟨r, by change r < L + 1 - 1; omega⟩⟩

omit L in
/-- An indicator that is not zero has its condition. -/
private theorem of_ite_ne_zero {p : Prop} [Decidable p] (h : (if p then (1 : ZMod 2) else 0) ≠ 0) :
    p := by
  by_contra hp
  exact h (if_neg hp)

omit L in
/-- A sum over `ZMod 2` vanishes when its terms vanish but at two equal ones. -/
private theorem sum_eq_zero_of_pair {α : Type*} [Fintype α] [DecidableEq α] (f : α → ZMod 2)
    (a b : α) (hab : a ≠ b) (hf : f a = f b) (h : ∀ x, x ≠ a ∧ x ≠ b → f x = 0) :
    ∑ x, f x = 0 := by
  rw [Fintype.sum_eq_add a b hab h, hf]
  exact CharTwo.add_self_eq_zero _

/-- Two cells of the grid with the same degrees and the same cells of the paths are the same. -/
private theorem gridCell_ext {i : ℕ} (x y : GridCell L i) (h0 : (x.1 : ℕ) = y.1)
    (h1 : (x.2.1 : ℕ) = y.2.1) (h2 : (x.2.2 : ℕ) = y.2.2) : x = y := by
  obtain ⟨p, a, r⟩ := x
  obtain ⟨q, b, s⟩ := y
  obtain rfl : p = q := Fin.ext h0
  obtain rfl : a = b := Fin.ext h1
  obtain rfl : r = s := Fin.ext h2
  rfl

/-- A vertex has its column below `L` and its row at most `L`. -/
private theorem gridVertex_lt (x : GridCell L 0) : (x.2.1 : ℕ) < L ∧ (x.2.2 : ℕ) < L + 1 := by
  obtain ⟨p, a, r⟩ := x
  obtain rfl : p = 0 := Fin.fin_one_eq_zero p
  exact ⟨a.isLt, r.isLt⟩

/-- A vertical edge has its column and its row edge below `L`. -/
private theorem gridVertical_lt (y : GridCell L 1) (hy : (y.1 : ℕ) = 0) :
    (y.2.1 : ℕ) < L ∧ (y.2.2 : ℕ) < L := by
  obtain ⟨q, a, e⟩ := y
  obtain rfl : q = 0 := Fin.ext hy
  have he : (e : ℕ) < L + 1 - 1 := e.isLt
  dsimp only
  exact ⟨a.isLt, by omega⟩

/-- A horizontal edge has its column edge below `L - 1` and its row at most `L`. -/
private theorem gridHorizontal_lt (y : GridCell L 1) (hy : (y.1 : ℕ) = 1) :
    (y.2.1 : ℕ) + 1 < L ∧ (y.2.2 : ℕ) < L + 1 := by
  obtain ⟨q, c, r⟩ := y
  obtain rfl : q = 1 := Fin.ext hy
  have hc : (c : ℕ) < L - 1 := c.isLt
  dsimp only
  exact ⟨by omega, r.isLt⟩

/-- A face has its column edge below `L - 1` and its row edge below `L`. -/
private theorem gridFace_lt (z : GridCell L 2) : (z.2.1 : ℕ) + 1 < L ∧ (z.2.2 : ℕ) < L := by
  have hz := face_fst L z
  obtain ⟨⟨q, hq⟩, c, r⟩ := z
  obtain rfl : q = 1 := hz
  have hc : (c : ℕ) < L - 1 := c.isLt
  have hr : (r : ℕ) < L + 1 - 1 := r.isLt
  dsimp only
  exact ⟨by omega, by omega⟩

/-- The incidence of a vertex and a vertical edge, on their coordinates. -/
private theorem incidence_vertex_vertical (x : GridCell L 0) (y : GridCell L 1)
    (hy : (y.1 : ℕ) = 0) :
    (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x y =
      if (x.2.1 : ℕ) = y.2.1 ∧ ((x.2.2 : ℕ) = y.2.2 ∨ (x.2.2 : ℕ) = y.2.2 + 1) then 1 else 0 := by
  obtain ⟨q, a, e⟩ := y
  obtain rfl : q = 0 := Fin.ext hy
  exact tensorIncidence_vertex_vertical L x a e

/-- The incidence of a vertex and a horizontal edge: `1` when the vertex is on the edge's row in
column `c` or `c + 1`. -/
private theorem incidence_vertex_horizontal (x : GridCell L 0) (y : GridCell L 1)
    (hy : (y.1 : ℕ) = 1) :
    (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x y =
      if ((x.2.1 : ℕ) = y.2.1 ∨ (x.2.1 : ℕ) = y.2.1 + 1) ∧ (x.2.2 : ℕ) = y.2.2 then 1 else 0 := by
  obtain ⟨p, a, r⟩ := x
  obtain rfl : p = 0 := Fin.fin_one_eq_zero p
  obtain ⟨q, c, s⟩ := y
  obtain rfl : q = 1 := Fin.ext hy
  change (if (a : ℕ) = c ∨ (a : ℕ) = c + 1 then (1 : ZMod 2) else 0) *
      (if (0 : ℕ) = 0 ∧ (r : ℕ) = s then 1 else 0) +
    (if (0 : ℕ) = 1 ∧ (a : ℕ) = c then 1 else 0) * _ = _
  simp only [true_and, ite_mul, one_mul, zero_mul, ← ite_and, zero_ne_one, false_and, if_false,
    add_zero]

/-- The incidence of a vertical edge and a face, on their coordinates. -/
private theorem incidence_vertical_face (y : GridCell L 1) (hy : (y.1 : ℕ) = 0)
    (z : GridCell L 2) :
    (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 y z =
      if ((y.2.1 : ℕ) = z.2.1 ∨ (y.2.1 : ℕ) = z.2.1 + 1) ∧ (y.2.2 : ℕ) = z.2.2 then 1 else 0 := by
  obtain ⟨q, a, e⟩ := y
  obtain rfl : q = 0 := Fin.ext hy
  exact tensorIncidence_vertical_face L a e z (face_fst L z)

/-- The incidence of a horizontal edge and a face: `1` when the edge's column edge is the face's
and its row is `r` or `r + 1` for the face's row edge `r`. -/
private theorem incidence_horizontal_face (y : GridCell L 1) (hy : (y.1 : ℕ) = 1)
    (z : GridCell L 2) :
    (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 y z =
      if (y.2.1 : ℕ) = z.2.1 ∧ ((y.2.2 : ℕ) = z.2.2 ∨ (y.2.2 : ℕ) = z.2.2 + 1) then 1 else 0 := by
  have hz := face_fst L z
  obtain ⟨q, c, s⟩ := y
  obtain rfl : q = 1 := Fin.ext hy
  obtain ⟨⟨q', hq'⟩, ce, re⟩ := z
  obtain rfl : q' = 1 := hz
  change (0 : ZMod 2) * _ + (if (1 : ℕ) = 1 ∧ (c : ℕ) = ce then (1 : ZMod 2) else 0) *
    (if (s : ℕ) = re ∨ (s : ℕ) = re + 1 then 1 else 0) = _
  simp only [zero_mul, zero_add, true_and, ite_mul, one_mul, ← ite_and]

/-- A cut has no horizontal edge. -/
private theorem gridCut_eq_zero (k : ℕ) (y : GridCell L 1) (hy : (y.1 : ℕ) = 1) :
    gridCut L k y = 0 :=
  if_neg fun h => by omega

/-- A column has no horizontal edge. -/
private theorem gridColumn_eq_zero (a : ℕ) (y : GridCell L 1) (hy : (y.1 : ℕ) = 1) :
    gridColumn L a y = 0 :=
  if_neg fun h => by omega

/-- A cut is a cocycle of the grid: a face has its two vertical sides both on the cut or both off
it. -/
private theorem sum_tensorIncidence_mul_gridCut (k : ℕ) (z : GridCell L 2) :
    ∑ y, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 y z *
      gridCut L k y = 0 := by
  obtain ⟨hc, hr⟩ := gridFace_lt L z
  refine sum_eq_zero_of_pair _ (gridVertical L z.2.1 z.2.2 (by omega) hr)
    (gridVertical L (z.2.1 + 1) z.2.2 hc hr) (fun h => ?_) ?_ fun y hy => ?_
  · have h1 := congrArg (fun y : GridCell L 1 => (y.2.1 : ℕ)) h
    dsimp only [gridVertical] at h1
    omega
  · rw [incidence_vertical_face L _ rfl, incidence_vertical_face L _ rfl,
      if_pos ⟨Or.inl rfl, rfl⟩, if_pos ⟨Or.inr rfl, rfl⟩]
    rfl
  · by_contra hne
    obtain ⟨hy0, -⟩ := of_ite_ne_zero (right_ne_zero_of_mul hne)
    have hT := left_ne_zero_of_mul hne
    rw [incidence_vertical_face L y hy0 z] at hT
    obtain ⟨ha | ha, he⟩ := of_ite_ne_zero hT
    · exact hy.1 (gridCell_ext L _ _ hy0 ha he)
    · exact hy.2 (gridCell_ext L _ _ hy0 ha he)

/-- A column is a cycle of the grid at each vertex off the rough rows: the vertex has its two
vertical edges both on the column or both off it. -/
private theorem sum_tensorIncidence_mul_gridColumn (a : ℕ) (x : GridCell L 0)
    (h0 : (x.2.2 : ℕ) ≠ 0) (hL : (x.2.2 : ℕ) ≠ L) :
    ∑ y, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x y *
      gridColumn L a y = 0 := by
  obtain ⟨hc, hr⟩ := gridVertex_lt L x
  refine sum_eq_zero_of_pair _ (gridVertical L x.2.1 x.2.2 hc (by omega))
    (gridVertical L x.2.1 (x.2.2 - 1) hc (by omega)) (fun h => ?_) ?_ fun y hy => ?_
  · have h2 := congrArg (fun y : GridCell L 1 => (y.2.2 : ℕ)) h
    dsimp only [gridVertical] at h2
    omega
  · rw [incidence_vertex_vertical L x _ rfl, incidence_vertex_vertical L x _ rfl,
      if_pos ⟨rfl, Or.inl rfl⟩,
      if_pos ⟨rfl, Or.inr (show (x.2.2 : ℕ) = x.2.2 - 1 + 1 by omega)⟩]
    rfl
  · by_contra hne
    obtain ⟨hy0, -⟩ := of_ite_ne_zero (right_ne_zero_of_mul hne)
    have hT := left_ne_zero_of_mul hne
    rw [incidence_vertex_vertical L x y hy0] at hT
    obtain ⟨ha, he | he⟩ := of_ite_ne_zero hT
    · exact hy.1 (gridCell_ext L _ _ hy0 ha.symm he.symm)
    · exact hy.2 (gridCell_ext L _ _ hy0 ha.symm (show (y.2.2 : ℕ) = x.2.2 - 1 by omega))

/-- The coboundary of the row `k + 1` is the sum of the cuts on either side of it: a vertical edge
has one end on the row when its row edge is `k` or `k + 1`, and a horizontal edge on the row has
both. -/
private theorem sum_tensorIncidence_mul_gridRow (k : ℕ) (hk : k + 1 < L) (y : GridCell L 1) :
    ∑ x, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x y *
      gridRow L (k + 1) x = gridCut L (k + 1) y + gridCut L k y := by
  rcases Nat.lt_or_ge (y.1 : ℕ) 1 with hy | hy
  · replace hy : (y.1 : ℕ) = 0 := by omega
    obtain ⟨ha, he⟩ := gridVertical_lt L y hy
    rw [Fintype.sum_eq_single (gridVertex L y.2.1 (k + 1) ha (by omega)) fun x hx => ?_]
    · rw [incidence_vertex_vertical L _ y hy]
      dsimp only [gridVertex, gridRow, gridCut]
      split_ifs <;> first | rfl | (exfalso; omega)
    · by_contra hne
      have hR := of_ite_ne_zero (right_ne_zero_of_mul hne)
      have hT := left_ne_zero_of_mul hne
      rw [incidence_vertex_vertical L x y hy] at hT
      obtain ⟨ha', -⟩ := of_ite_ne_zero hT
      have hx0 := x.1.isLt
      exact hx (gridCell_ext L _ _ (show (x.1 : ℕ) = 0 by omega) ha' hR)
  · replace hy : (y.1 : ℕ) = 1 := by
      have := y.1.isLt
      omega
    obtain ⟨hc, hr⟩ := gridHorizontal_lt L y hy
    rw [gridCut_eq_zero L _ y hy, gridCut_eq_zero L _ y hy, add_zero]
    refine sum_eq_zero_of_pair _ (gridVertex L y.2.1 y.2.2 (by omega) hr)
      (gridVertex L (y.2.1 + 1) y.2.2 hc hr) (fun h => ?_) ?_ fun x hx => ?_
    · have h1 := congrArg (fun x : GridCell L 0 => (x.2.1 : ℕ)) h
      dsimp only [gridVertex] at h1
      omega
    · rw [incidence_vertex_horizontal L _ y hy, incidence_vertex_horizontal L _ y hy,
        if_pos ⟨Or.inl rfl, rfl⟩, if_pos ⟨Or.inr rfl, rfl⟩]
      rfl
    · by_contra hne
      have hT := left_ne_zero_of_mul hne
      rw [incidence_vertex_horizontal L x y hy] at hT
      obtain ⟨ha | ha, he⟩ := of_ite_ne_zero hT
      · have hx0 := x.1.isLt
        exact hx.1 (gridCell_ext L _ _ (show (x.1 : ℕ) = 0 by omega) ha he)
      · have hx0 := x.1.isLt
        exact hx.2 (gridCell_ext L _ _ (show (x.1 : ℕ) = 0 by omega) ha he)

/-- The boundary of the faces between columns `k` and `k + 1`, off the rough rows, is the sum of
the two columns: each horizontal edge off the rough rows is a side of two of the faces. -/
private theorem sum_tensorIncidence_mul_gridFaceColumn (k : ℕ) (hk : k + 1 < L)
    (y : GridCell L 1) (hy : ¬((y.1 : ℕ) = 1 ∧ ((y.2.2 : ℕ) = 0 ∨ (y.2.2 : ℕ) = L))) :
    ∑ z, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 y z *
      gridFaceColumn L k z = gridColumn L (k + 1) y + gridColumn L k y := by
  rcases Nat.lt_or_ge (y.1 : ℕ) 1 with hy0 | hy1
  · replace hy0 : (y.1 : ℕ) = 0 := by omega
    obtain ⟨ha, he⟩ := gridVertical_lt L y hy0
    rw [Fintype.sum_eq_single (gridFace L k y.2.2 hk he) fun z hz => ?_]
    · rw [incidence_vertical_face L y hy0]
      dsimp only [gridFace, gridFaceColumn, gridColumn]
      split_ifs <;> first | rfl | (exfalso; omega)
    · by_contra hne
      have hC := of_ite_ne_zero (right_ne_zero_of_mul hne)
      have hT := left_ne_zero_of_mul hne
      rw [incidence_vertical_face L y hy0] at hT
      obtain ⟨-, he'⟩ := of_ite_ne_zero hT
      exact hz (gridCell_ext L _ _ (face_fst L z) hC he'.symm)
  · replace hy1 : (y.1 : ℕ) = 1 := by
      have := y.1.isLt
      omega
    obtain ⟨hc, hr⟩ := gridHorizontal_lt L y hy1
    have hr0 : (y.2.2 : ℕ) ≠ 0 := fun h => hy ⟨hy1, Or.inl h⟩
    have hrL : (y.2.2 : ℕ) ≠ L := fun h => hy ⟨hy1, Or.inr h⟩
    rw [gridColumn_eq_zero L _ y hy1, gridColumn_eq_zero L _ y hy1, add_zero]
    refine sum_eq_zero_of_pair _ (gridFace L k y.2.2 hk (by omega))
      (gridFace L k (y.2.2 - 1) hk (by omega)) (fun h => ?_) ?_ fun z hz => ?_
    · have h2 := congrArg (fun z : GridCell L 2 => (z.2.2 : ℕ)) h
      dsimp only [gridFace] at h2
      omega
    · rw [incidence_horizontal_face L y hy1, incidence_horizontal_face L y hy1]
      dsimp only [gridFace, gridFaceColumn]
      split_ifs <;> first | rfl | (exfalso; omega)
    · by_contra hne
      have hC := of_ite_ne_zero (right_ne_zero_of_mul hne)
      have hT := left_ne_zero_of_mul hne
      rw [incidence_horizontal_face L y hy1] at hT
      obtain ⟨-, he | he⟩ := of_ite_ne_zero hT
      · exact hz.1 (gridCell_ext L _ _ (face_fst L z) hC he.symm)
      · exact hz.2 (gridCell_ext L _ _ (face_fst L z) hC (show (z.2.2 : ℕ) = y.2.2 - 1 by omega))

/-- The cut between rows `k` and `k + 1` meets the column `a` once, at the edge `⟨0, a, k⟩`. -/
private theorem sum_gridCut_mul_gridColumn (k a : ℕ) (hk : k < L) (ha : a < L) :
    ∑ y, gridCut L k y * gridColumn L a y = 1 := by
  rw [Fintype.sum_eq_single (gridVertical L a k ha hk) fun y hy => ?_]
  · rw [gridCut, gridColumn, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, one_mul]
  · by_contra hne
    obtain ⟨hy0, hyk⟩ := of_ite_ne_zero (left_ne_zero_of_mul hne)
    obtain ⟨-, hya⟩ := of_ite_ne_zero (right_ne_zero_of_mul hne)
    exact hy (gridCell_ext L _ _ hy0 hya hyk)

/-- A cell of the patch is a cell of the grid off the rough boundaries. -/
private theorem not_rough_otherCell (i : ℕ) (b : Fin ((planarComplex L).cells i)) :
    ¬(((gridCellEquiv L i ((roughBoundary L).otherCell i b)).1 : ℕ) = i ∧
      (((gridCellEquiv L i ((roughBoundary L).otherCell i b)).2.2 : ℕ) = 0 ∨
        ((gridCellEquiv L i ((roughBoundary L).otherCell i b)).2.2 : ℕ) = L)) := by
  intro h
  have hb := ((roughBoundary L).cellSet i)ᶜ.orderEmbOfFin_mem rfl b
  rw [Finset.mem_compl] at hb
  exact hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)

/-- A sum over the patch's cells of degree `i` is the sum over the grid's, for a function that
vanishes on the rough boundaries. -/
private theorem sum_planar (i : ℕ) (g : GridCell L i → ZMod 2)
    (hg : ∀ x : GridCell L i, (x.1 : ℕ) = i → ((x.2.2 : ℕ) = 0 ∨ (x.2.2 : ℕ) = L) → g x = 0) :
    ∑ b : Fin ((planarComplex L).cells i),
        g (gridCellEquiv L i ((roughBoundary L).otherCell i b)) = ∑ x, g x := by
  have h := Finset.sum_map Finset.univ
    (((roughBoundary L).cellSet i)ᶜ.orderEmbOfFin rfl).toEmbedding
    fun σ => g (gridCellEquiv L i σ)
  rw [Finset.map_orderEmbOfFin_univ] at h
  refine h.symm.trans ?_
  rw [Finset.sum_subset (Finset.subset_univ _) fun σ _ hσ => ?_]
  · exact Equiv.sum_comp (gridCellEquiv L i) g
  · rw [Finset.notMem_compl] at hσ
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 hσ
    exact hg _ h1 h2

/-- A chain of the grid read on the patch is a relative cycle when its boundary vanishes at the
vertices off the rough rows. -/
private theorem planarChain_mem_cycles (F : GridCell L 1 → ZMod 2)
    (hF : ∀ y : GridCell L 1, (y.1 : ℕ) = 1 → ((y.2.2 : ℕ) = 0 ∨ (y.2.2 : ℕ) = L) → F y = 0)
    (h : ∀ x : GridCell L 0, (x.2.2 : ℕ) ≠ 0 → (x.2.2 : ℕ) ≠ L →
      ∑ y, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x y *
        F y = 0) :
    planarChain L F ∈ (planarComplex L).cycles 1 := by
  rw [BasedComplex.cycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext a
  have ha := not_rough_otherCell L 0 a
  have ha0 := (gridCellEquiv L 0 ((roughBoundary L).otherCell 0 a)).1.isLt
  change ∑ b : Fin ((planarComplex L).cells 1), (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex 0
      (gridCellEquiv L 0 ((roughBoundary L).otherCell 0 a))
      (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)) *
    F (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)) = 0
  exact (sum_planar L 1 (fun y => (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex 0
      (gridCellEquiv L 0 ((roughBoundary L).otherCell 0 a)) y * F y)
    fun y h1 h2 => by dsimp only; rw [hF y h1 h2, mul_zero]).trans
    (h _ (fun h0 => ha ⟨by omega, Or.inl h0⟩) fun hL => ha ⟨by omega, Or.inr hL⟩)

/-- A chain of the grid read on the patch is a relative cocycle when its coboundary vanishes at
every face. -/
private theorem planarChain_mem_cocycles (F : GridCell L 1 → ZMod 2)
    (hF : ∀ y : GridCell L 1, (y.1 : ℕ) = 1 → ((y.2.2 : ℕ) = 0 ∨ (y.2.2 : ℕ) = L) → F y = 0)
    (h : ∀ z : GridCell L 2,
      ∑ y, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 y z *
        F y = 0) :
    planarChain L F ∈ (planarComplex L).cocycles 1 := by
  rw [BasedComplex.cocycles, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext c
  exact (sum_planar L 1 (fun y => (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex 1 y
      (gridCellEquiv L 2 ((roughBoundary L).otherCell 2 c)) * F y)
    fun y h1 h2 => by dsimp only; rw [hF y h1 h2, mul_zero]).trans (h _)

/-- A chain of the grid read on the patch is a relative boundary when, off the rough rows, it is
the boundary of a chain of faces. -/
private theorem planarChain_mem_boundaries (F : GridCell L 1 → ZMod 2) (f : GridCell L 2 → ZMod 2)
    (h : ∀ y : GridCell L 1, ¬((y.1 : ℕ) = 1 ∧ ((y.2.2 : ℕ) = 0 ∨ (y.2.2 : ℕ) = L)) →
      ∑ z, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 1 y z *
        f z = F y) :
    planarChain L F ∈ (planarComplex L).boundaries 1 := by
  refine LinearMap.mem_range.2
    ⟨fun c => f (gridCellEquiv L 2 ((roughBoundary L).otherCell 2 c)), ?_⟩
  rw [Matrix.mulVecLin_apply]
  funext b
  exact (sum_planar L 2 (fun z => (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex 1
      (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)) z * f z)
    fun z h1 _ => absurd h1 (by have := face_fst L z; omega)).trans
    (h _ (not_rough_otherCell L 1 b))

/-- A chain of the grid read on the patch is a relative coboundary when it is the coboundary of a
function on the vertices that vanishes on the rough rows. -/
private theorem planarChain_mem_coboundaries (F : GridCell L 1 → ZMod 2)
    (g : GridCell L 0 → ZMod 2)
    (hg : ∀ x : GridCell L 0, ((x.2.2 : ℕ) = 0 ∨ (x.2.2 : ℕ) = L) → g x = 0)
    (h : ∀ y : GridCell L 1,
      ∑ x, (pathComplex L).tensorIncidence (pathComplex (L + 1)).toBasedPrecomplex 0 x y *
        g x = F y) :
    planarChain L F ∈ (planarComplex L).coboundaries 1 := by
  refine LinearMap.mem_range.2
    ⟨fun a => g (gridCellEquiv L 0 ((roughBoundary L).otherCell 0 a)), ?_⟩
  rw [Matrix.mulVecLin_apply]
  funext b
  change ∑ a : Fin ((planarComplex L).cells 0), (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex 0
      (gridCellEquiv L 0 ((roughBoundary L).otherCell 0 a))
      (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)) *
    g (gridCellEquiv L 0 ((roughBoundary L).otherCell 0 a)) = _
  exact (sum_planar L 0 (fun x => (pathComplex L).tensorIncidence
      (pathComplex (L + 1)).toBasedPrecomplex 0 x
      (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)) * g x)
    fun x _ h2 => by dsimp only; rw [hg x h2, mul_zero]).trans (h _)

/-- The dot product of two chains of the grid read on the patch, when one has no rough edge. -/
private theorem planarChain_dotProduct (F F' : GridCell L 1 → ZMod 2)
    (hF : ∀ y : GridCell L 1, (y.1 : ℕ) = 1 → ((y.2.2 : ℕ) = 0 ∨ (y.2.2 : ℕ) = L) → F y = 0) :
    planarChain L F ⬝ᵥ planarChain L F' = ∑ y, F y * F' y :=
  sum_planar L 1 (fun y => F y * F' y) fun y h1 h2 => by dsimp only; rw [hF y h1 h2, zero_mul]

/-- A cut is a relative cocycle. -/
private theorem planarCut_mem_cocycles (k : ℕ) :
    planarChain L (gridCut L k) ∈ (planarComplex L).cocycles 1 :=
  planarChain_mem_cocycles L _ (fun y h1 _ => gridCut_eq_zero L k y h1)
    (sum_tensorIncidence_mul_gridCut L k)

/-- A column is a relative cycle. -/
private theorem planarColumn_mem_cycles (a : ℕ) :
    planarChain L (gridColumn L a) ∈ (planarComplex L).cycles 1 :=
  planarChain_mem_cycles L _ (fun y h1 _ => gridColumn_eq_zero L a y h1)
    (sum_tensorIncidence_mul_gridColumn L a)

/-- Two neighbouring cuts differ by a relative coboundary, that of the row between them. -/
private theorem planarCut_add_mem_coboundaries (k : ℕ) (hk : k + 1 < L) :
    planarChain L (gridCut L (k + 1)) + planarChain L (gridCut L k) ∈
      (planarComplex L).coboundaries 1 :=
  planarChain_mem_coboundaries L (fun y => gridCut L (k + 1) y + gridCut L k y)
    (gridRow L (k + 1)) (fun x hx => if_neg fun h => by omega)
    (sum_tensorIncidence_mul_gridRow L k hk)

/-- Two neighbouring columns differ by a relative boundary, that of the faces between them. -/
private theorem planarColumn_add_mem_boundaries (k : ℕ) (hk : k + 1 < L) :
    planarChain L (gridColumn L (k + 1)) + planarChain L (gridColumn L k) ∈
      (planarComplex L).boundaries 1 :=
  planarChain_mem_boundaries L (fun y => gridColumn L (k + 1) y + gridColumn L k y)
    (gridFaceColumn L k) (sum_tensorIncidence_mul_gridFaceColumn L k hk)

/-- Each cut meets each column once. -/
private theorem planarCut_dotProduct_planarColumn (k a : ℕ) (hk : k < L) (ha : a < L) :
    planarChain L (gridCut L k) ⬝ᵥ planarChain L (gridColumn L a) = 1 :=
  (planarChain_dotProduct L _ _ fun y h1 _ => gridCut_eq_zero L k y h1).trans
    (sum_gridCut_mul_gridColumn L k a hk ha)

/-- A relative cycle meets every cut with the same parity. -/
private theorem planarCut_dotProduct_eq {v : Fin ((planarComplex L).cells 1) → ZMod 2}
    (hv : v ∈ (planarComplex L).cycles 1) (k : ℕ) (hk : k < L) :
    planarChain L (gridCut L k) ⬝ᵥ v = planarChain L (gridCut L 0) ⬝ᵥ v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles
      (planarCut_add_mem_coboundaries L k hk) hv
    rw [add_dotProduct] at h
    rw [← ih (by omega)]
    exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add]; exact h)

/-- A relative cocycle meets every column with the same parity. -/
private theorem planarColumn_dotProduct_eq {u : Fin ((planarComplex L).cells 1) → ZMod 2}
    (hu : u ∈ (planarComplex L).cocycles 1) (k : ℕ) (hk : k < L) :
    planarChain L (gridColumn L k) ⬝ᵥ u = planarChain L (gridColumn L 0) ⬝ᵥ u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries hu
      (planarColumn_add_mem_boundaries L k hk)
    rw [dotProduct_comm, add_dotProduct] at h
    rw [← ih (by omega)]
    exact eq_of_sub_eq_zero (by rw [CharTwo.sub_eq_add]; exact h)

/-- The relative cycles exceed the relative boundaries by one dimension, the count of
`planarCode_k`. -/
private theorem finrank_planar_cycles_le [NeZero L] :
    Module.finrank (ZMod 2) ((planarComplex L).cycles 1) ≤
      Module.finrank (ZMod 2) ((planarComplex L).boundaries 1) + Fintype.card (Fin 1) := by
  have h1 : Module.finrank (ZMod 2) ((planarComplex L).cycles 1) =
      (planarComplex L).cells 1 - (planarCode L).1.rank :=
    finrank_cssZLogicalCarrier (planarCode L).1
  have h2 : Module.finrank (ZMod 2) ((planarComplex L).boundaries 1) =
      ((planarCode L).2)ᵀ.rank := rfl
  rw [h1, h2, Matrix.rank_transpose, rank_planarCode_fst, rank_planarCode_snd, Fintype.card_fin]
  have h := planarComplex_cells_one L
  omega

/-- The relative cocycles exceed the relative coboundaries by one dimension. -/
private theorem finrank_planar_cocycles_le [NeZero L] :
    Module.finrank (ZMod 2) ((planarComplex L).cocycles 1) ≤
      Module.finrank (ZMod 2) ((planarComplex L).coboundaries 1) + Fintype.card (Fin 1) := by
  have h1 : Module.finrank (ZMod 2) ((planarComplex L).cocycles 1) =
      (planarComplex L).cells 1 - (planarCode L).2.rank :=
    finrank_cssXLogicalCarrier (planarCode L).2
  have h2 : Module.finrank (ZMod 2) ((planarComplex L).coboundaries 1) =
      ((planarCode L).1)ᵀ.rank := rfl
  rw [h1, h2, Matrix.rank_transpose, rank_planarCode_fst, rank_planarCode_snd, Fintype.card_fin]
  have h := planarComplex_cells_one L
  omega

/-- A relative cycle that is not a relative boundary meets the first cut oddly. -/
private theorem planarCut_dotProduct_ne_zero [NeZero L]
    {v : Fin ((planarComplex L).cells 1) → ZMod 2} (hv : v ∈ (planarComplex L).cycles 1)
    (hnb : v ∉ (planarComplex L).boundaries 1) : planarChain L (gridCut L 0) ⬝ᵥ v ≠ 0 := by
  have hL := NeZero.pos L
  intro h
  refine hnb (mem_of_finrank_le_of_apply_eq_zero ((planarComplex L).cycles 1)
    ((planarComplex L).boundaries 1)
    (cssZLogicalSubspace_le_cssZLogicalCarrier (cssOfComplex_isCSSPair (planarComplex L) 1))
    (finrank_planar_cycles_le L) (fun _ : Fin 1 => dotProductLin (planarChain L (gridCut L 0)))
    (fun _ _ hb => BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries
      (planarCut_mem_cocycles L 0) hb)
    (fun _ => planarChain L (gridColumn L 0)) (fun _ => planarColumn_mem_cycles L 0)
    (fun j k => ?_) hv fun _ => h)
  rw [Subsingleton.elim j k, if_pos rfl]
  exact planarCut_dotProduct_planarColumn L 0 0 hL hL

/-- A relative cocycle that is not a relative coboundary meets the first column oddly. -/
private theorem planarColumn_dotProduct_ne_zero [NeZero L]
    {u : Fin ((planarComplex L).cells 1) → ZMod 2} (hu : u ∈ (planarComplex L).cocycles 1)
    (hnc : u ∉ (planarComplex L).coboundaries 1) :
    planarChain L (gridColumn L 0) ⬝ᵥ u ≠ 0 := by
  have hL := NeZero.pos L
  intro h
  refine hnc (mem_of_finrank_le_of_apply_eq_zero ((planarComplex L).cocycles 1)
    ((planarComplex L).coboundaries 1)
    (cssXLogicalSubspace_le_cssXLogicalCarrier (cssOfComplex_isCSSPair (planarComplex L) 1))
    (finrank_planar_cocycles_le L)
    (fun _ : Fin 1 => dotProductLin (planarChain L (gridColumn L 0))) (fun _ c hc => ?_)
    (fun _ => planarChain L (gridCut L 0)) (fun _ => planarCut_mem_cocycles L 0)
    (fun j k => ?_) hu fun _ => h)
  · change planarChain L (gridColumn L 0) ⬝ᵥ c = 0
    rw [dotProduct_comm]
    exact BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles hc
      (planarColumn_mem_cycles L 0)
  · rw [Subsingleton.elim j k, if_pos rfl]
    change planarChain L (gridColumn L 0) ⬝ᵥ planarChain L (gridCut L 0) = 1
    rw [dotProduct_comm]
    exact planarCut_dotProduct_planarColumn L 0 0 hL hL

/-- A chain meeting each of `L` sets oddly has at least `L` edges, when the sets are told apart by a
coordinate of their edges: one edge on each. -/
private theorem le_card_of_dotProduct_ne_zero {n : ℕ} (S : ℕ → Fin n → ZMod 2)
    (coordinate : Fin n → ℕ) (hS : ∀ k b, S k b ≠ 0 → coordinate b = k) (v : Fin n → ZMod 2)
    (hv : ∀ k < L, S k ⬝ᵥ v ≠ 0) : L ≤ (Finset.univ.filter fun b => v b ≠ 0).card := by
  have hex : ∀ k : Fin L, ∃ b, S k b ≠ 0 ∧ v b ≠ 0 := by
    intro k
    have h := hv k k.isLt
    rw [dotProduct] at h
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨b, left_ne_zero_of_mul hb, right_ne_zero_of_mul hb⟩
  choose f hfS hfv using hex
  calc L = (Finset.univ : Finset (Fin L)).card := by rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.card_le_card_of_injOn f
        (fun k _ => Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfv k⟩))
        (fun k _ k' _ hkk => Fin.ext (by
          rw [← hS k (f k) (hfS k), ← hS k' (f k') (hfS k'), hkk]))

/-- A chain of the grid read on the patch has at most `L` edges when its edges are told apart by a
coordinate below `L`. -/
private theorem card_planarChain_le (F : GridCell L 1 → ZMod 2) (coordinate : GridCell L 1 → ℕ)
    (hF : ∀ y, F y ≠ 0 → coordinate y < L)
    (hinj : ∀ y y', F y ≠ 0 → F y' ≠ 0 → coordinate y = coordinate y' → y = y') :
    (Finset.univ.filter fun b => planarChain L F b ≠ 0).card ≤ L := by
  calc _ ≤ (Finset.range L).card := Finset.card_le_card_of_injOn
        (fun b => coordinate (gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)))
        (fun b hb => Finset.mem_coe.2 (Finset.mem_range.2
          (hF _ (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2)))
        (fun b hb b' hb' h => ((roughBoundary L).otherCell 1).injective
          ((gridCellEquiv L 1).injective (hinj _ _ (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
            (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).2 h)))
    _ = L := Finset.card_range L

/-- A column has at most `L` edges, one for each row edge. -/
private theorem card_planarColumn_le (a : ℕ) :
    (Finset.univ.filter fun b => planarChain L (gridColumn L a) b ≠ 0).card ≤ L :=
  card_planarChain_le L _ (fun y => (y.2.2 : ℕ))
    (fun y hy => (gridVertical_lt L y (of_ite_ne_zero hy).1).2)
    fun _ _ hy hy' h => gridCell_ext L _ _ ((of_ite_ne_zero hy).1.trans (of_ite_ne_zero hy').1.symm)
      ((of_ite_ne_zero hy).2.trans (of_ite_ne_zero hy').2.symm) h

/-- A cut has at most `L` edges, one for each column. -/
private theorem card_planarCut_le (k : ℕ) :
    (Finset.univ.filter fun b => planarChain L (gridCut L k) b ≠ 0).card ≤ L :=
  card_planarChain_le L _ (fun y => (y.2.1 : ℕ))
    (fun y hy => (gridVertical_lt L y (of_ite_ne_zero hy).1).1)
    fun _ _ hy hy' h => gridCell_ext L _ _ ((of_ite_ne_zero hy).1.trans (of_ite_ne_zero hy').1.symm)
      h ((of_ite_ne_zero hy).2.trans (of_ite_ne_zero hy').2.symm)

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:hc1165ba8cd2d
-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143 figure:fig_planar
/-- **The planar code has distance `L`, for both check types.** `Z` type: every relative cycle that
is not a relative boundary has weight at least `L`, and `planarZString`, rough boundary to rough
boundary, is such a cycle of weight `L`. `X` type: every relative cocycle that is not a coboundary
has weight at least `L`, and `planarXString`, smooth boundary to smooth boundary, is such a cocycle
of weight `L`. The cut argument on the patch is inferred (docs/fidelity/T34.md, Claim 13). -/
theorem planarCode_distance [NeZero L] :
    ((∀ v ∈ (planarComplex L).cycles 1, v ∉ (planarComplex L).boundaries 1 →
        L ≤ (Finset.univ.filter fun ℓ => v ℓ ≠ 0).card) ∧
      planarZString L ∈ (planarComplex L).cycles 1 ∧
      planarZString L ∉ (planarComplex L).boundaries 1 ∧
      (Finset.univ.filter fun ℓ => planarZString L ℓ ≠ 0).card = L) ∧
    ((∀ v ∈ (planarComplex L).cocycles 1, v ∉ (planarComplex L).coboundaries 1 →
        L ≤ (Finset.univ.filter fun ℓ => v ℓ ≠ 0).card) ∧
      planarXString L ∈ (planarComplex L).cocycles 1 ∧
      planarXString L ∉ (planarComplex L).coboundaries 1 ∧
      (Finset.univ.filter fun ℓ => planarXString L ℓ ≠ 0).card = L) := by
  have hL := NeZero.pos L
  have hZ : planarZString L = planarChain L (gridColumn L 0) := rfl
  have hX : planarXString L = planarChain L (gridCut L 0) := rfl
  have hcut : ∀ k b, planarChain L (gridCut L k) b ≠ 0 →
      ((gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)).2.2 : ℕ) = k :=
    fun _ _ h => (of_ite_ne_zero h).2
  have hcolumn : ∀ a b, planarChain L (gridColumn L a) b ≠ 0 →
      ((gridCellEquiv L 1 ((roughBoundary L).otherCell 1 b)).2.1 : ℕ) = a :=
    fun _ _ h => (of_ite_ne_zero h).2
  refine ⟨⟨fun v hv hnb => ?_, ?_, fun hb => ?_, ?_⟩, ⟨fun u hu hnc => ?_, ?_, fun hc => ?_, ?_⟩⟩
  · refine le_card_of_dotProduct_ne_zero L (fun k => planarChain L (gridCut L k)) _ hcut v
      fun k hk => ?_
    rw [planarCut_dotProduct_eq L hv k hk]
    exact planarCut_dotProduct_ne_zero L hv hnb
  · rw [hZ]
    exact planarColumn_mem_cycles L 0
  · have h := BasedComplex.dotProduct_eq_zero_of_mem_cocycles_of_mem_boundaries
      (planarCut_mem_cocycles L 0) hb
    rw [hZ, planarCut_dotProduct_planarColumn L 0 0 hL hL] at h
    exact one_ne_zero h
  · rw [hZ]
    refine le_antisymm (card_planarColumn_le L 0) (le_card_of_dotProduct_ne_zero L
      (fun k => planarChain L (gridCut L k)) _ hcut _ fun k hk => ?_)
    rw [planarCut_dotProduct_planarColumn L k 0 hk hL]
    exact one_ne_zero
  · refine le_card_of_dotProduct_ne_zero L (fun a => planarChain L (gridColumn L a)) _ hcolumn u
      fun a ha => ?_
    rw [planarColumn_dotProduct_eq L hu a ha]
    exact planarColumn_dotProduct_ne_zero L hu hnc
  · rw [hX]
    exact planarCut_mem_cocycles L 0
  · have h := BasedComplex.dotProduct_eq_zero_of_mem_coboundaries_of_mem_cycles hc
      (planarColumn_mem_cycles L 0)
    rw [hX, planarCut_dotProduct_planarColumn L 0 0 hL hL] at h
    exact one_ne_zero h
  · rw [hX]
    refine le_antisymm (card_planarCut_le L 0) (le_card_of_dotProduct_ne_zero L
      (fun a => planarChain L (gridColumn L a)) _ hcolumn _ fun a ha => ?_)
    rw [dotProduct_comm, planarCut_dotProduct_planarColumn L 0 a hL ha]
    exact one_ne_zero

/-! ### The decoding problem -/

-- source: papers/quantum_codes/
-- Dennis_Kitaev_Landahl_Preskill_2001_topological_quantum_memory_quant-ph_0110143
--   paragraph:h13d809e81ca7
/-- **The decoding problem, stated homologically.** For a complex
`C_{i+1} → C_i → C_{i-1}` with boundaries `boundary` and `check`, an error is a chain `error` of
degree `i`; its syndrome is `check *ᵥ error`, its boundary; a decoder maps each syndrome to a
correction. The decoder corrects `error` up to a boundary when its correction has the error's
syndrome and the correction plus the error is a boundary, `im boundary`, a trivial cycle; the
correction need not be the error. On a CSS pair `(H_X, H_Z)`, `Z` errors take `check = H_X` and
`boundary = H_Zᵀ` (on `cssOfComplex C i`, `im boundary = C.boundaries i`), and `X` errors take
`check = H_Z` and `boundary = H_Xᵀ` (`C.coboundaries i`). The specification T65's minimum-weight
decoder and phase 6's decoders are proved against (docs/fidelity/T34.md, Claim 16). -/
def CorrectsUpToBoundary {m n r : ℕ} (check : Matrix (Fin m) (Fin n) (ZMod 2))
    (boundary : Matrix (Fin n) (Fin r) (ZMod 2)) (decoder : (Fin m → ZMod 2) → Fin n → ZMod 2)
    (error : Fin n → ZMod 2) : Prop :=
  check *ᵥ decoder (check *ᵥ error) = check *ᵥ error ∧
    decoder (check *ᵥ error) + error ∈ LinearMap.range boundary.mulVecLin

end FTQCLib.CSS

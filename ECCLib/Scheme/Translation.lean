/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.PermCommutant
import ECCLib.Scheme.Orbits
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The translation-scheme algebra and the commutant theorem

For a finite abelian group `V` with a symmetry group `[Group H] [DistribMulAction H V]`:

* `IsCompat H M` — `M : Matrix V V ℂ` is invariant under simultaneous translation of its
  indices and under the simultaneous `H`-action;
* **`isCompat_iff`** — the compatible operators are exactly the circulants
  (`Matrix.circulant`, `circulant k i j = k (i − j)`) of `H`-invariant kernels;
* **`isCompat_iff_commute`** — the commutant form: commuting with every translation
  permutation matrix and every `H` permutation matrix;
* `schemeAlgebra H V` — DEFINED as Mathlib's `Subalgebra.centralizer` of those two
  families (so the algebra structure is free), with `mem_schemeAlgebra_iff` identifying it
  with `IsCompat`; commutativity from `Matrix.circulant_mul_comm`;
* `adj R` — the adjacency operator of an orbit; `linearIndependent_adj`, `span_adj_eq`,
  the basis `schemeBasis` (`Module.Basis.span`) and **`finrank_schemeAlgebra`**:
  the algebra's dimension IS the number of `H`-orbits.

References: Delsarte 1973 §2.2 Thm 2.1 / Godsil 2010 §1.3 / Martin–Tanaka 2009 §6 (the
Schur-ring formulation).
-/

namespace ECCLib.Scheme

open Finset Matrix
open scoped BigOperators

/-! ## A generic matrix lemma: commuting with a permutation matrix

`commute_permMatrix_iff` lives at the lowest layer that can state it,
`ECCLib/Matrix/PermCommutant.lean`, for any `Semiring`. -/

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {H : Type*} [Group H] [Fintype H] [DistribMulAction H V]

/-! ## Compatibility and invariant kernels -/

/-- Compatible with the translations of `V` and with the `H`-action. -/
def IsCompat (H : Type*) [Group H] [DistribMulAction H V] (M : Matrix V V ℂ) : Prop :=
  (∀ x y g : V, M (x + g) (y + g) = M x y) ∧ (∀ (h : H) (x y : V), M (h • x) (h • y) = M x y)

/-- `k` is an `H`-invariant function on `V`. -/
def IsInv (H : Type*) [Group H] [DistribMulAction H V] (k : V → ℂ) : Prop :=
  ∀ (h : H) (v : V), k (h • v) = k v

omit [Fintype H] [Fintype V] [DecidableEq V] in
/-- **Presentation theorem**: the compatible operators are exactly the circulants of
`H`-invariant kernels. -/
theorem isCompat_iff (M : Matrix V V ℂ) :
    IsCompat H M ↔ ∃ k : V → ℂ, IsInv H k ∧ M = Matrix.circulant k := by
  constructor
  · rintro ⟨htr, hH⟩
    refine ⟨fun v => M v 0, fun h v => ?_, ?_⟩
    · have := hH h v 0
      rwa [smul_zero] at this
    · ext i j
      rw [Matrix.circulant_apply]
      have := htr (i - j) 0 j
      rw [sub_add_cancel, zero_add] at this
      exact this
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun x y g => ?_, fun h x y => ?_⟩
    · simp only [Matrix.circulant_apply, add_sub_add_right_eq_sub]
    · simp only [Matrix.circulant_apply, ← smul_sub]
      exact hk h (x - y)

omit [Fintype H] in
/-- **The commutant form.** `M` is compatible iff it commutes with every translation
permutation matrix and with every `H` permutation matrix. -/
theorem isCompat_iff_commute (M : Matrix V V ℂ) :
    IsCompat H M ↔
      (∀ g : V, M * (Equiv.addRight g).permMatrix ℂ = (Equiv.addRight g).permMatrix ℂ * M) ∧
      (∀ h : H, M * (MulAction.toPerm h : Equiv.Perm V).permMatrix ℂ
          = (MulAction.toPerm h : Equiv.Perm V).permMatrix ℂ * M) := by
  constructor
  · rintro ⟨htr, hH⟩
    exact ⟨fun g => (commute_permMatrix_iff _ M).mpr (fun x y => htr x y g),
           fun h => (commute_permMatrix_iff _ M).mpr (fun x y => hH h x y)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x y g => (commute_permMatrix_iff _ M).mp (h1 g) x y,
           fun h x y => (commute_permMatrix_iff _ M).mp (h2 h) x y⟩

/-! ## The algebra structure on invariant kernels -/

omit [Fintype H] [DecidableEq V] in
/-- **Closure under the product**: `circulant k * circulant l = circulant (circulant k *ᵥ l)`
(Mathlib), and the product kernel of invariant kernels is invariant. -/
theorem isInv_mulVec {k l : V → ℂ} (hk : IsInv H k) (hl : IsInv H l) :
    IsInv H (Matrix.circulant k *ᵥ l) := by
  intro h u
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply]
  rw [← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm V) (fun j => k (h • u - j) * l j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  change k (h • u - h • j) * l (h • j) = k (u - j) * l j
  rw [← smul_sub, hk, hl]

omit [Fintype H] [Fintype V] in
/-- The unit kernel `δ₀` is invariant. -/
theorem isInv_single : IsInv H (Pi.single (0 : V) (1 : ℂ)) := by
  intro h v
  have hz : h • v = 0 ↔ v = 0 := by
    constructor
    · intro hv
      have := congrArg (fun w => h⁻¹ • w) hv
      simpa using this
    · rintro rfl
      exact smul_zero h
  simp [Pi.single_apply, hz]

omit [Fintype H] [Fintype V] [DecidableEq V] in
theorem isInv_add {k l : V → ℂ} (hk : IsInv H k) (hl : IsInv H l) : IsInv H (k + l) :=
  fun h v => by simp [hk h v, hl h v]

omit [Fintype H] [Fintype V] [DecidableEq V] in
theorem isInv_smul {k : V → ℂ} (c : ℂ) (hk : IsInv H k) : IsInv H (c • k) :=
  fun h v => by simp [hk h v]

/-! ## The scheme algebra as a centralizer -/

/-- The translation permutation matrices. -/
def transMats (V : Type*) [AddCommGroup V] [Fintype V] [DecidableEq V] :
    Set (Matrix V V ℂ) :=
  Set.range (fun g : V => (Equiv.addRight g).permMatrix ℂ)

/-- The `H` permutation matrices. -/
def actMats (H : Type*) [Group H] (V : Type*) [AddCommGroup V] [Fintype V] [DecidableEq V]
    [DistribMulAction H V] : Set (Matrix V V ℂ) :=
  Set.range (fun h : H => (MulAction.toPerm h : Equiv.Perm V).permMatrix ℂ)

/-- **The scheme algebra**: the commutant of the translations and the `H`-action inside
`Matrix V V ℂ`, as Mathlib's centralizer subalgebra. -/
noncomputable def schemeAlgebra (H : Type*) [Group H] (V : Type*) [AddCommGroup V]
    [Fintype V] [DecidableEq V] [DistribMulAction H V] : Subalgebra ℂ (Matrix V V ℂ) :=
  Subalgebra.centralizer ℂ (transMats V ∪ actMats H V)

omit [Fintype H] in
/-- Membership in the scheme algebra IS compatibility. -/
theorem mem_schemeAlgebra_iff (M : Matrix V V ℂ) :
    M ∈ schemeAlgebra H V ↔ IsCompat H M := by
  rw [schemeAlgebra, Subalgebra.mem_centralizer_iff, isCompat_iff_commute]
  constructor
  · intro h
    exact ⟨fun g => (h _ (Or.inl ⟨g, rfl⟩)).symm, fun k => (h _ (Or.inr ⟨k, rfl⟩)).symm⟩
  · rintro ⟨h1, h2⟩ P hP
    rcases hP with ⟨g, rfl⟩ | ⟨k, rfl⟩
    · exact (h1 g).symm
    · exact (h2 k).symm

omit [Fintype H] in
/-- Membership in the scheme algebra IS being the circulant of an invariant kernel. -/
theorem mem_schemeAlgebra_iff_circulant (M : Matrix V V ℂ) :
    M ∈ schemeAlgebra H V ↔ ∃ k : V → ℂ, IsInv H k ∧ M = Matrix.circulant k := by
  rw [mem_schemeAlgebra_iff, isCompat_iff]

omit [Fintype H] in
/-- The scheme algebra is commutative. -/
theorem schemeAlgebra_mul_comm {M N : Matrix V V ℂ} (hM : M ∈ schemeAlgebra H V)
    (hN : N ∈ schemeAlgebra H V) : M * N = N * M := by
  obtain ⟨k, -, rfl⟩ := (mem_schemeAlgebra_iff_circulant M).mp hM
  obtain ⟨l, -, rfl⟩ := (mem_schemeAlgebra_iff_circulant N).mp hN
  exact Matrix.circulant_mul_comm k l

/-! ## The orbit basis -/

/-- The adjacency operator of a subset `R` — the circulant of its indicator. -/
noncomputable def adj (R : Finset V) : Matrix V V ℂ :=
  Matrix.circulant (fun v => if v ∈ R then 1 else 0)

/-- The indicator of an orbit is an invariant kernel. -/
theorem isInv_indicator_orbit {R : Finset V} (hR : R ∈ orbits H V) :
    IsInv H (fun v => if v ∈ R then (1 : ℂ) else 0) := by
  intro h v
  have : h • v ∈ R ↔ v ∈ R := by
    rw [mem_iff_orb_eq hR, mem_iff_orb_eq hR, orb_smul]
  simp only [this]

theorem adj_mem_schemeAlgebra {R : Finset V} (hR : R ∈ orbits H V) :
    adj R ∈ schemeAlgebra H V :=
  (mem_schemeAlgebra_iff_circulant _).mpr ⟨_, isInv_indicator_orbit hR, rfl⟩

/-- The value of a kernel on a (nonempty) class: evaluated at a chosen point. -/
noncomputable def orbVal (k : V → ℂ) (R : Finset V) : ℂ :=
  if h : R.Nonempty then k h.choose else 0

/-- An invariant kernel is constant on each orbit, at the value `orbVal`. -/
theorem orbVal_eq {k : V → ℂ} (hk : IsInv H k) {R : Finset V} (hR : R ∈ orbits H V)
    {v : V} (hv : v ∈ R) : orbVal k R = k v := by
  have hne : R.Nonempty := nonempty_of_mem_orbits hR
  rw [orbVal, dif_pos hne]
  have h1 : orb H v = R := (mem_iff_orb_eq hR).mp hv
  have h2 : hne.choose ∈ orb H v := by
    rw [h1]
    exact hne.choose_spec
  obtain ⟨h, hh⟩ := mem_orb.mp h2
  rw [← hh, hk]

/-- **Spanning**: an invariant kernel's circulant is the orbit-coordinate combination of
the adjacency operators. -/
theorem circulant_eq_sum_adj {k : V → ℂ} (hk : IsInv H k) :
    Matrix.circulant k = ∑ R ∈ orbits H V, orbVal k R • adj R := by
  ext i j
  rw [Matrix.circulant_apply, Matrix.sum_apply]
  have hstep : ∀ R ∈ orbits H V, (orbVal k R • adj R) i j
      = if i - j ∈ R then k (i - j) else 0 := by
    intro R hR
    simp only [adj, Matrix.smul_apply, Matrix.circulant_apply, smul_eq_mul]
    by_cases hmem : i - j ∈ R
    · rw [if_pos hmem, if_pos hmem, mul_one, orbVal_eq hk hR hmem]
    · rw [if_neg hmem, if_neg hmem, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_eq_single (orb H (i - j))]
  · rw [if_pos (self_mem_orb (H := H) (i - j))]
  · intro R hR hne
    rw [if_neg]
    intro hmem
    exact hne ((mem_iff_orb_eq hR).mp hmem).symm
  · intro hcon
    exact absurd (orb_mem_orbits (H := H) (i - j)) hcon

/-- The adjacency operators of the orbits are linearly independent. -/
theorem linearIndependent_adj :
    LinearIndependent ℂ (fun R : ↥(orbits H V) => adj (R : Finset V)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg R
  obtain ⟨R, hR⟩ := R
  obtain ⟨v, hv⟩ := nonempty_of_mem_orbits hR
  have h := congrFun (congrFun hg v) 0
  rw [Matrix.sum_apply] at h
  have hterm : ∀ R' : ↥(orbits H V),
      (g R' • adj (R' : Finset V)) v 0 = if v ∈ (R' : Finset V) then g R' else 0 := by
    intro R'
    simp only [adj, Matrix.smul_apply, Matrix.circulant_apply, sub_zero, smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun R' _ => hterm R'), Finset.sum_eq_single ⟨R, hR⟩] at h
  · simpa [hv] using h
  · intro R' _ hne
    rw [if_neg]
    intro hv'
    exact hne (Subtype.ext (eq_of_mem_orbits_of_mem R'.2 hR hv' hv))
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- The span of the adjacency operators is the scheme algebra. -/
theorem span_adj_eq :
    Submodule.span ℂ (Set.range (fun R : ↥(orbits H V) => adj (R : Finset V)))
      = (schemeAlgebra H V).toSubmodule := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨R, rfl⟩
    exact adj_mem_schemeAlgebra R.2
  · intro M hM
    rw [Subalgebra.mem_toSubmodule] at hM
    obtain ⟨k, hk, rfl⟩ := (mem_schemeAlgebra_iff_circulant M).mp hM
    rw [circulant_eq_sum_adj hk]
    exact Submodule.sum_mem _ fun R hR =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨R, hR⟩, rfl⟩)

/-- **The orbit basis** of the span of the adjacency operators (= the scheme algebra, by
`span_adj_eq`). -/
noncomputable def schemeBasis :
    Module.Basis ↥(orbits H V) ℂ
      (Submodule.span ℂ (Set.range (fun R : ↥(orbits H V) => adj (R : Finset V)))) :=
  Module.Basis.span linearIndependent_adj

/-- **The dimension of the scheme algebra is the number of `H`-orbits.** -/
theorem finrank_schemeAlgebra :
    Module.finrank ℂ (schemeAlgebra H V) = (orbits H V).card := by
  rw [← Subalgebra.finrank_toSubmodule, ← span_adj_eq,
    finrank_span_eq_card linearIndependent_adj, Fintype.card_coe]

end ECCLib.Scheme

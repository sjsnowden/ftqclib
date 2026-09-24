/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Distance
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Reed–Solomon codes are MDS

The evaluation code of polynomials of degree `< k` at an injective family of points meets the
Singleton bound with equality — the specification the Reed–Solomon decoders
(`GaoDecoder.lean`) are verified against.

* `rsEval a` — evaluation at the points `a : ι → F`, as a linear map `F[X] →ₗ[F] (ι → F)`;
* `rsCode a k` — the **Reed–Solomon code**: the image of `Polynomial.degreeLT F k` under
  `rsEval a`;
* `finrank_rsCode` — `dim = k` when `k ≤ n` and `a` is injective: a nonzero polynomial of degree
  `< k` cannot vanish at `n ≥ k` distinct points (`Polynomial.card_roots'`), so evaluation is
  injective on `degreeLT F k`;
* **`minDist_rsCode`** — **the MDS theorem**, in additive form:
  `minDist (rsCode a k) + k = n + 1` for `1 ≤ k ≤ n`. `≤` is the Singleton bound
  (`singleton_bound` + the dimension); `≥` is root-counting: a nonzero codeword has at most
  `k − 1` zero coordinates. The `k = 0` case is excluded by hypothesis: `rsCode a 0 = ⊥` has junk
  distance `0` and the equality genuinely fails there.
-/

namespace ECCLib.Coding

open Polynomial

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [DecidableEq F]

/-! ## The evaluation map and the code -/

/-- **Evaluation at the point family `a`**, as a linear map `F[X] →ₗ[F] (ι → F)`. -/
noncomputable def rsEval (a : ι → F) : Polynomial F →ₗ[F] (ι → F) where
  toFun p := fun i => p.eval (a i)
  map_add' p q := by
    funext i
    simp [Polynomial.eval_add]
  map_smul' c p := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

@[simp] theorem rsEval_apply (a : ι → F) (p : Polynomial F) (i : ι) :
    rsEval a p i = p.eval (a i) := rfl

/-- The **Reed–Solomon code**: evaluations of the polynomials of degree `< k` at the points `a`. -/
noncomputable def rsCode (a : ι → F) (k : ℕ) : Submodule F (ι → F) :=
  Submodule.map (rsEval a) (Polynomial.degreeLT F k)

omit [Fintype F] [Fintype ι] [DecidableEq ι] [DecidableEq F] in
theorem mem_rsCode {a : ι → F} {k : ℕ} {y : ι → F} :
    y ∈ rsCode a k ↔ ∃ p ∈ Polynomial.degreeLT F k, rsEval a p = y :=
  Submodule.mem_map

/-! ## Root counting -/

/-- **The counting lemma**: a nonzero polynomial vanishes at no more than `natDegree` of the
(distinct) points `a i`. -/
lemma card_eval_zero_le {a : ι → F} (ha : Function.Injective a) {p : Polynomial F}
    (hp : p ≠ 0) :
    (Finset.univ.filter (fun i => p.eval (a i) = 0)).card ≤ p.natDegree := by
  calc (Finset.univ.filter (fun i => p.eval (a i) = 0)).card
      ≤ p.roots.toFinset.card := by
        refine Finset.card_le_card_of_injOn a (fun i hi => ?_) ha.injOn
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
        simp only [Finset.mem_coe, Multiset.mem_toFinset]
        exact (Polynomial.mem_roots hp).mpr hi
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- A polynomial of degree `< k ≤ n` vanishing at all `n` points is zero. -/
lemma eq_zero_of_rsEval_eq_zero {a : ι → F} (ha : Function.Injective a) {k : ℕ}
    (hk : k ≤ Fintype.card ι) {p : Polynomial F} (hp : p ∈ Polynomial.degreeLT F k)
    (h0 : rsEval a p = 0) : p = 0 := by
  by_contra hne
  have hall : Finset.univ.filter (fun i => p.eval (a i) = 0) = Finset.univ := by
    rw [Finset.filter_eq_self]
    intro i _
    exact congrFun h0 i
  have hcard := card_eval_zero_le ha hne
  rw [hall, Finset.card_univ] at hcard
  have hdeg : p.natDegree < k :=
    (Polynomial.natDegree_lt_iff_degree_lt hne).mpr (Polynomial.mem_degreeLT.mp hp)
  omega

/-! ## The dimension -/

/-- Evaluation is injective on `degreeLT F k` when `k ≤ n`. -/
theorem rsEval_comp_injective {a : ι → F} (ha : Function.Injective a) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    Function.Injective ((rsEval a).comp (Polynomial.degreeLT F k).subtype) := by
  intro p q hpq
  have hpq' : rsEval a (p : Polynomial F) = rsEval a (q : Polynomial F) := hpq
  have h0 : rsEval a ((p : Polynomial F) - (q : Polynomial F)) = 0 := by
    rw [map_sub, hpq', sub_self]
  exact Subtype.ext (sub_eq_zero.mp
    (eq_zero_of_rsEval_eq_zero ha hk (sub_mem p.2 q.2) h0))

/-- **The dimension of the Reed–Solomon code is `k`** (for `k ≤ n`, injective points). -/
theorem finrank_rsCode {a : ι → F} (ha : Function.Injective a) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    Module.finrank F (rsCode a k) = k := by
  haveI : FiniteDimensional F (Polynomial.degreeLT F k) :=
    LinearEquiv.finiteDimensional (Polynomial.degreeLTEquiv F k).symm
  have hrange : LinearMap.range ((rsEval a).comp (Polynomial.degreeLT F k).subtype)
      = rsCode a k := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [← hrange, LinearMap.finrank_range_of_inj (rsEval_comp_injective ha hk),
    (Polynomial.degreeLTEquiv F k).finrank_eq, Module.finrank_pi, Fintype.card_fin]

/-! ## The MDS theorem -/

/-- For `1 ≤ k` (and `k ≤ n`, so the index type is nonempty) the code is nontrivial: it contains
the constant function `1` — the evaluation of the constant polynomial. -/
theorem rsCode_ne_bot {a : ι → F} {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    rsCode a k ≠ ⊥ := by
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_lt_of_le hk1 hkn)
  refine (Submodule.ne_bot_iff _).mpr ⟨fun _ => 1, ?_, ?_⟩
  · refine mem_rsCode.mpr ⟨Polynomial.C 1, ?_, ?_⟩
    · rw [Polynomial.mem_degreeLT, Polynomial.degree_C one_ne_zero]
      exact_mod_cast hk1
    · funext i
      rw [rsEval_apply, Polynomial.eval_C]
  · intro h
    exact one_ne_zero (congrFun h (Classical.arbitrary ι))

/-- **Reed–Solomon codes are MDS**: `minDist (rsCode a k) + k = n + 1` for `1 ≤ k ≤ n` and
injective evaluation points — the Singleton bound is attained with equality. `≤` is
`singleton_bound` + `finrank_rsCode`; `≥` is root-counting on the attained minimum-weight
codeword. -/
theorem minDist_rsCode {a : ι → F} (ha : Function.Injective a) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card ι) :
    minDist (rsCode a k) + k = Fintype.card ι + 1 := by
  have hle : minDist (rsCode a k) + k ≤ Fintype.card ι + 1 := by
    have h := singleton_bound (rsCode a k)
    rw [finrank_rsCode ha hkn] at h
    exact h
  have hge : Fintype.card ι + 1 ≤ minDist (rsCode a k) + k := by
    obtain ⟨y, hyC, hy0, hwt⟩ := exists_minDist (rsCode_ne_bot (a := a) hk1 hkn)
    obtain ⟨p, hp, hpy⟩ := mem_rsCode.mp hyC
    subst hpy
    have hpne : p ≠ 0 := by
      rintro rfl
      exact hy0 (map_zero _)
    have hnd : p.natDegree < k :=
      (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr (Polynomial.mem_degreeLT.mp hp)
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => p.eval (a i) = 0)
    rw [Finset.card_univ] at hsplit
    have hzeros : (Finset.univ.filter (fun i => p.eval (a i) = 0)).card ≤ p.natDegree :=
      card_eval_zero_le ha hpne
    have hwty : (Finset.univ.filter (fun i => ¬ p.eval (a i) = 0)).card
        = hammingNorm (rsEval a p) := rfl
    rw [hwt] at hwty
    omega
  omega

end ECCLib.Coding

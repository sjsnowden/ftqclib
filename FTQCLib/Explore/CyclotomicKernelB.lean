/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.EliminationOrder
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The cyclotomic kernel, antipodal cancellation, and the scale obstruction

**Question.** A carrier state's amplitude at a free word `w` is `(c/√2^h)·Σ_y ζ^{Q(w,y)}`. The
gauge rewrites R1–R7 keep the multiset of phases at each free word (`boundTerms`,
`FTQCLib/Carrier/EliminationOrder.lean`), an element of the group ring `ℤ[C_{2^m}]`, and the
amplitude is its image in `ℤ[ζ_{2^m}]`. Does the kernel of that map name the rule the frame lacks?

**How the outcome is read.** Five results, each checked here.

1. **The kernel.** Over any commutative ring `R` and at every `k`, the kernel of the fold
   `R[X]/(X^{2k} − 1) → R[X]/(X^k + 1)` is the `R`-span of the antipodal pairs `X^a + X^{a+k}`
   (`mem_ker_fold_iff`). In a domain of characteristic zero an integer polynomial vanishes at a
   primitive `2^m`-th root exactly when `X^{2^{m−1}} + 1` divides it (`aeval_eq_zero_iff`), so at
   `k = 2^{m−1}` the second ring embeds and the fold's kernel is the whole kernel of evaluation. In
   coordinates: `Σ_z f(z)·μ^z = 0` exactly when `f(z) = f(z + 2^{m−1})` for every residue `z`
   (`sum_eq_zero_iff_antipodal`), and two phase multisets have the same character sum exactly when
   their antipodal differences agree (`sum_map_charOf_eq_iff`). Two things are load-bearing: the
   statement fails at `m = 0` (`not_sum_eq_zero_iff_antipodal_zero`), and away from powers of two,
   where the sixth roots' `1 + ω + ω² = 0` is not antipodal (`sixth_root_not_antipodal`).
2. **The rule.** Antipodal cancellation (`CancelData`, `elimCancel`): an involution `τ` of the bound
   words, the same for every free word, whose moved words carry exponent the top bit `2^{m−1}` more
   than their partners; the paths it moves are dropped, the kept words re-enumerated at a lower
   height, and the scale corrected by `√2^{h'}/√2^h`. Certified against the amplitude
   (`amp_elimCancel`).
3. **T04.** Each of T04's two stuck outcomes cancels one antipodal pair to the same height-one
   record, which one rotate takes to one height-zero record, of scale `1/√2`
   (`EliminationOrder'.outcomes_join`, `EliminationOrder'.floor_c`).
4. **The scale obstruction.** Every gauge rewrite, both eliminations and cancellation multiply
   `‖c‖²` by an integer power of `2` (`sameScaleClass_of_extStep`). Two carrier states at `n = 0`
   have one amplitude, `(3 + i)/2`, with `‖c‖² = 1` and `‖c‖² = 5/2`
   (`ScaleWitness.pathState`, `ScaleWitness.scalarState`); no chain of such rules, taken in either
   direction, relates them (`ScaleWitness.scale_obstruction`). Equational completeness over
   records whose scale is an arbitrary complex number is false for every rule set of this kind.
5. **What cancellation does not reach.** Cancellation needs one pairing for every free word.
   Vilmart's rule (HH) with a bound partner cancels pairs that move with the free word: at
   `n = 1`, `m = 3`, the exponent `4·y₀·(y₁ + w₀) + y₁` sums to the `T` phase `ζ₈^{w₀}` at height
   zero, yet no elimination is available at either bound bit and the only involution with the
   cancel shape is the identity (`HHWitness.hh_witness`).

## Main definitions

* `fold` — the fold of the cyclic group ring onto `R[X]/(X^k + 1)`.
* `CancelData`, `KeepData`, `elimCancel` — the cancel shape, the kept words, the cancelled record.
* `ExtStep`, `ExtRel` — R1–R7, collapse, rotate and cancel, and the equivalence they generate.
* `SameScaleClass` — `‖c‖²` up to an integer power of `2`.
* `EliminationOrder'.cancelled`, `EliminationOrder'.floor` — T04's join at heights one and zero.
* `ScaleWitness.pathState`, `ScaleWitness.scalarState`, `HHWitness.hhState` — the witnesses.

## Main results

* `mem_ker_fold_iff`, `aeval_eq_zero_iff`, `sum_eq_zero_iff_antipodal`, `sum_map_charOf_eq_iff`.
* `amp_elimCancel`, `stateEq_of_extRel`.
* `EliminationOrder'.outcomes_join`.
* `sameScaleClass_of_extRel`, `ScaleWitness.scale_obstruction`.
* `HHWitness.hh_witness`.

## Implementation notes

* Standalone (`FTQCLib/Explore/README.md`): `lake build FTQCLib.Explore.CyclotomicKernelB`,
  imported by nothing. Written beside `FTQCLib/Explore/CyclotomicKernel.lean`, another session's
  answer to the same question, and independent of it.
* The evaluation lemmas of `EliminationOrder.lean` that are private there are restated here, and
  the one-qubit Lagrangian `⟨X₀⟩` of the check modules is restated as `HHWitness.lagX`.
* Every finite check over bound words is `decide` over at most sixteen pairs of words, after the
  exponent is rewritten into the values of the word's bits.
-/

namespace FTQCLib.Explore.CyclotomicKernelB

/-! ## The kernel of the fold -/

section Fold

open Polynomial

variable (R : Type*) [CommRing R] (k : ℕ)

/-- `X^{2k} − 1 = (X^k + 1)·(X^k − 1)`: the antipodal ideal contains the cyclic one. -/
theorem span_cyclic_le_span_antipodal :
    Ideal.span {(X ^ (2 * k) - 1 : R[X])} ≤ Ideal.span {(X ^ k + 1 : R[X])} :=
  Ideal.span_singleton_le_span_singleton.mpr ⟨X ^ k - 1, by ring⟩

/-- The fold `R[X]/(X^{2k} − 1) → R[X]/(X^k + 1)`: the group ring of the cyclic group of order
`2k` onto the ring in which `X^k = −1`. -/
noncomputable def fold :
    R[X] ⧸ Ideal.span {(X ^ (2 * k) - 1 : R[X])} →+* R[X] ⧸ Ideal.span {(X ^ k + 1 : R[X])} :=
  Ideal.Quotient.factor (span_cyclic_le_span_antipodal R k)

/-- The fold's kernel as an ideal: generated by the class of `X^k + 1`. -/
theorem ker_fold :
    RingHom.ker (fold R k)
      = Ideal.span {Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])}) (X ^ k + 1)} := by
  rw [fold, Ideal.Quotient.factor_ker, Ideal.map_span, Set.image_singleton]

/-- **The kernel of the fold.** An element of `R[X]/(X^{2k} − 1)` folds to zero exactly when it is
an `R`-combination of the antipodal pairs `X^a + X^{a+k}`. No hypothesis on `R` or `k`. -/
theorem mem_ker_fold_iff (x : R[X] ⧸ Ideal.span {(X ^ (2 * k) - 1 : R[X])}) :
    x ∈ RingHom.ker (fold R k)
      ↔ x ∈ Submodule.span R
          (Set.range fun a : ℕ =>
            Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])}) (X ^ a + X ^ (a + k))) := by
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective x
    subst hq
    rw [RingHom.mem_ker, fold, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨p, rfl⟩ := hx
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [mul_add, map_add]
      exact Submodule.add_mem _ hp hq
    | monomial a r =>
      have hr : (X ^ k + 1) * monomial a r = r • (X ^ a + X ^ (a + k) : R[X]) := by
        rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul]
        ring
      rw [hr]
      have hsmul := map_smul (Ideal.Quotient.mkₐ R (Ideal.span {(X ^ (2 * k) - 1 : R[X])})) r
        (X ^ a + X ^ (a + k) : R[X])
      rw [Ideal.Quotient.mkₐ_eq_mk] at hsmul
      rw [hsmul]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a, rfl⟩)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [RingHom.mem_ker, fold, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact ⟨X ^ a, by ring⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul r y _ hy => exact Submodule.smul_of_tower_mem _ r hy

end Fold

/-! ## Evaluation at a primitive `2^m`-th root -/

section Evaluation

open Polynomial

variable {K : Type*} [CommRing K]

/-- A sum over `ZMod N` is the sum over `range N` of the residues' values. -/
theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] {N : ℕ} [NeZero N] (F : ZMod N → M) :
    ∑ z : ZMod N, F z = ∑ j ∈ Finset.range N, F j := by
  refine Finset.sum_nbij' (fun z => z.val) (fun j => (j : ZMod N)) (fun z _ => ?_)
    (fun _ _ => Finset.mem_univ _) (fun z _ => ZMod.natCast_zmod_val z) (fun j hj => ?_)
    (fun z _ => by rw [ZMod.natCast_zmod_val])
  · exact Finset.mem_range.mpr (ZMod.val_lt z)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)

/-- The fold of a sum over `ZMod N`, `N = 2h`: with `μ^h = −1` the terms at `j` and `j + h` pair,
leaving one coefficient `f j − f (j + h)` for each `j < h`. -/
theorem sum_zmod_fold {N h : ℕ} [NeZero N] (hN : N = 2 * h) {μ : K} (hμ : μ ^ h = -1)
    (f : ZMod N → ℤ) :
    ∑ z : ZMod N, (f z : K) * μ ^ z.val
      = ∑ j ∈ Finset.range h, ((f j - f (j + h) : ℤ) : K) * μ ^ j := by
  have hval : ∑ z : ZMod N, (f z : K) * μ ^ z.val
      = ∑ j ∈ Finset.range N, (f j : K) * μ ^ j := by
    rw [sum_zmod_eq_sum_range (fun z : ZMod N => (f z : K) * μ ^ z.val)]
    exact Finset.sum_congr rfl fun j hj => by
      rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]
  rw [hval, show Finset.range N = Finset.range (h + h) by rw [hN, two_mul], Finset.sum_range_add,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, hμ, show ((h + j : ℕ) : ZMod N) = (j : ZMod N) + (h : ZMod N) by push_cast; ring]
  push_cast
  ring

/-- A primitive `2^m`-th root of unity in a domain has `μ^{2^{m−1}} = −1`. -/
theorem pow_two_pow_pred_eq_neg_one [IsDomain K] {m : ℕ} (hm : 1 ≤ m) {μ : K}
    (hμ : IsPrimitiveRoot μ (2 ^ m)) : μ ^ 2 ^ (m - 1) = -1 := by
  have hsq : μ ^ 2 ^ (m - 1) * μ ^ 2 ^ (m - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel hm, hμ.pow_eq_one]
  refine (mul_self_eq_one_iff.mp hsq).resolve_left ?_
  exact hμ.pow_ne_one_of_pos_of_lt (by positivity) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- `Φ_{2^m} = X^{2^{m−1}} + 1`. -/
theorem cyclotomic_two_pow {m : ℕ} (hm : 1 ≤ m) (R : Type*) [CommRing R] :
    cyclotomic (2 ^ m) R = X ^ 2 ^ (m - 1) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two, Finset.sum_range_succ,
    Finset.sum_range_one, pow_zero, pow_one, Nat.add_sub_cancel, add_comm]

/-- **Evaluation at a primitive `2^m`-th root.** In a domain of characteristic zero, an integer
polynomial vanishes at `μ` exactly when `X^{2^{m−1}} + 1` divides it: `ℤ[X]/(X^{2^{m−1}} + 1)`
embeds in the domain, so the fold at `k = 2^{m−1}` loses nothing that evaluation keeps. -/
theorem aeval_eq_zero_iff [IsDomain K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) {μ : K}
    (hμ : IsPrimitiveRoot μ (2 ^ m)) (p : ℤ[X]) :
    aeval μ p = 0 ↔ (X ^ 2 ^ (m - 1) + 1 : ℤ[X]) ∣ p := by
  constructor
  · intro hp
    let F := FractionRing K
    -- `F` is a `ℤ`-algebra twice over (through `K`, and as a ring); `minpoly` is read with the
    -- ring's structure, so that one is fixed here.
    letI : Algebra ℤ F := Ring.toIntAlgebra F
    have hμ' : IsPrimitiveRoot (algebraMap K F μ) (2 ^ m) :=
      hμ.map_of_injective (IsFractionRing.injective K F)
    have hp' : p.eval₂ (Int.castRingHom F) (algebraMap K F μ) = 0 := by
      rw [← RingHom.ext_int ((algebraMap K F).comp (Int.castRingHom K)) (Int.castRingHom F),
        ← hom_eval₂]
      exact (congrArg (algebraMap K F) hp).trans (map_zero _)
    have hdvd := minpoly.isIntegrallyClosed_dvd (hμ'.isIntegral (by positivity)) hp'
    rwa [← cyclotomic_eq_minpoly hμ' (by positivity), cyclotomic_two_pow hm] at hdvd
  · rintro ⟨q, rfl⟩
    rw [map_mul, map_add, map_pow, aeval_X, map_one, pow_two_pow_pred_eq_neg_one hm hμ,
      neg_add_cancel, zero_mul]

/-- The coefficients of `Σ_{i<h} d_i X^i`. -/
private theorem coeff_sum_C_mul_X_pow (d : ℕ → ℤ) (h j : ℕ) :
    (∑ i ∈ Finset.range h, C (d i) * X ^ i).coeff j = if j < h then d j else 0 := by
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hj : j < h <;> simp [hj]

/-- **The kernel, in coordinates.** In a domain of characteristic zero, with `μ` a primitive
`2^m`-th root of unity and `1 ≤ m`, an integer combination `Σ_z f(z)·μ^z` over `ZMod (2^m)`
vanishes exactly when `f` takes one value on each antipodal pair `z`, `z + 2^{m−1}`. -/
theorem sum_eq_zero_iff_antipodal [IsDomain K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) {μ : K}
    (hμ : IsPrimitiveRoot μ (2 ^ m)) (f : ZMod (2 ^ m) → ℤ) :
    ∑ z : ZMod (2 ^ m), (f z : K) * μ ^ z.val = 0 ↔ ∀ z, f z = f (z + 2 ^ (m - 1)) := by
  set h := 2 ^ (m - 1) with hh
  have hN : 2 ^ m = 2 * h := by rw [hh, ← pow_succ', Nat.sub_add_cancel hm]
  have hcast : (2 : ZMod (2 ^ m)) ^ (m - 1) = (h : ZMod (2 ^ m)) := by rw [hh]; push_cast; rfl
  rw [sum_zmod_fold hN (pow_two_pow_pred_eq_neg_one hm hμ), hcast]
  constructor
  · intro hsum
    set d : ℕ → ℤ := fun j => f j - f (j + h) with hd
    have hD : aeval μ (∑ i ∈ Finset.range h, C (d i) * X ^ i) = 0 := by
      rw [← hsum, map_sum]
      simp [hd]
    have hzero := eq_zero_of_dvd_of_degree_lt ((aeval_eq_zero_iff hm hμ _).mp hD) (by
      rw [degree_add_eq_left_of_degree_lt (by rw [degree_one, degree_X_pow]; positivity),
        degree_X_pow, degree_lt_iff_coeff_zero]
      intro j hj
      rw [coeff_sum_C_mul_X_pow, if_neg (by omega)])
    have hdj : ∀ j < h, f j = f (j + h) := fun j hj => by
      have := congrArg (fun p : ℤ[X] => p.coeff j) hzero
      simp only [coeff_sum_C_mul_X_pow, if_pos hj, coeff_zero, hd] at this
      omega
    intro z
    by_cases hz : z.val < h
    · simpa [ZMod.natCast_zmod_val] using hdj z.val hz
    · obtain ⟨j, hj⟩ : ∃ j, j = z.val - h := ⟨_, rfl⟩
      have hjh : j < h := by have := ZMod.val_lt z; omega
      have hzj : z = (j : ZMod (2 ^ m)) + h := by
        rw [hj, Nat.cast_sub (by omega), ZMod.natCast_zmod_val]; ring
      have hwrap : z + h = (j : ZMod (2 ^ m)) := by
        rw [hzj, add_assoc, ← Nat.cast_add, ← two_mul, ← hN, ZMod.natCast_self, add_zero]
      rw [hwrap, hzj, hdj j hjh]
  · intro hf
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hf, sub_self, Int.cast_zero, zero_mul]

end Evaluation

/-! ### Where the hypotheses bite -/

/-- At `m = 0` the coordinate statement fails: the one residue is its own antipode, so every `f`
is antipodal, but `f = 1` does not sum to zero. -/
theorem not_sum_eq_zero_iff_antipodal_zero :
    ¬ ∀ f : ZMod (2 ^ 0) → ℤ,
      ((∑ z : ZMod (2 ^ 0), (f z : ℂ) * (1 : ℂ) ^ z.val = 0) ↔ ∀ z, f z = f (z + 2 ^ (0 - 1))) := by
  intro h
  haveI : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.mpr (by norm_num)
  have h1 := (h fun _ => 1).mpr fun _ => rfl
  rw [Fintype.sum_subsingleton _ 0] at h1
  simp at h1

/-- Away from powers of two the antipodal pairs do not span the kernel: at a primitive sixth root
`μ`, `1 + μ² + μ⁴ = 0`, while the coefficients at `0` and at its antipode `3` differ. -/
theorem sixth_root_not_antipodal {μ : ℂ} (hμ : IsPrimitiveRoot μ 6) :
    ∃ f : ZMod 6 → ℤ, ∑ z : ZMod 6, (f z : ℂ) * μ ^ z.val = 0 ∧ f 0 ≠ f (0 + 3) := by
  refine ⟨fun z => if z.val % 2 = 0 then 1 else 0, ?_, by decide⟩
  have hω : IsPrimitiveRoot (μ ^ 2) 3 := hμ.pow_of_dvd (by norm_num) (by norm_num : 2 ∣ 6)
  have hgeom := hω.geom_sum_eq_zero (by norm_num)
  rw [sum_zmod_eq_sum_range (fun z : ZMod 6 => ((if z.val % 2 = 0 then 1 else 0 : ℤ) : ℂ)
    * μ ^ z.val)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hgeom ⊢
  have hv : ∀ j : ℕ, j < 6 → ((j : ZMod 6)).val = j := fun j hj => ZMod.val_cast_of_lt hj
  rw [hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num),
    hv 4 (by norm_num), hv 5 (by norm_num)]
  norm_num
  linear_combination hgeom

/-! ## The frame's character -/

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Frame.Walkthrough

/-- **The kernel, for the frame's character.** `Σ_z f(z)·charOf m z = 0` exactly when `f` is
constant on antipodal pairs. -/
theorem sum_charOf_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) (f : ZMod (2 ^ m) → ℤ) :
    ∑ z : ZMod (2 ^ m), (f z : ℂ) * charOf m z = 0 ↔ ∀ z, f z = f (z + 2 ^ (m - 1)) := by
  simp_rw [charOf_eq_zeta_pow]
  exact sum_eq_zero_iff_antipodal hm (isPrimitiveRoot_zeta m) f

/-- A multiset's character sum, counted residue by residue. -/
theorem sum_map_charOf_eq_sum_count (m : ℕ) (s : Multiset (ZMod (2 ^ m))) :
    (s.map (charOf m)).sum = ∑ z, ((s.count z : ℤ) : ℂ) * charOf m z := by
  classical
  calc (s.map (charOf m)).sum = ∑ z ∈ s.toFinset, s.count z • charOf m z :=
        Finset.sum_multiset_map_count s (charOf m)
    _ = ∑ z, s.count z • charOf m z :=
        Finset.sum_subset (Finset.subset_univ _) fun z _ hz => by
          rw [Multiset.count_eq_zero.mpr (by simpa using hz), zero_smul]
    _ = ∑ z, ((s.count z : ℤ) : ℂ) * charOf m z :=
        Finset.sum_congr rfl fun z _ => by rw [nsmul_eq_mul, Int.cast_natCast]

/-- **Two phase multisets, one amplitude.** Two multisets of exponents have the same character
sum exactly when, residue by residue, the count at `z` less the count at its antipode agrees. -/
theorem sum_map_charOf_eq_iff {m : ℕ} (hm : 1 ≤ m) (s t : Multiset (ZMod (2 ^ m))) :
    (s.map (charOf m)).sum = (t.map (charOf m)).sum
      ↔ ∀ z, (s.count z : ℤ) - s.count (z + 2 ^ (m - 1))
          = t.count z - t.count (z + 2 ^ (m - 1)) := by
  rw [← sub_eq_zero, sum_map_charOf_eq_sum_count, sum_map_charOf_eq_sum_count,
    ← Finset.sum_sub_distrib]
  have hsub : ∀ z, ((s.count z : ℤ) : ℂ) * charOf m z - ((t.count z : ℤ) : ℂ) * charOf m z
      = (((s.count z : ℤ) - t.count z : ℤ) : ℂ) * charOf m z := fun z => by push_cast; ring
  simp_rw [hsub]
  rw [sum_charOf_eq_zero_iff hm]
  exact forall_congr' fun z => by omega

variable {n : ℕ}

/-- The multiset of exponents at a free word: one entry per bound word. -/
noncomputable def phaseMultiset {m h : ℕ} (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2) :
    Multiset (ZMod (2 ^ m)) :=
  (Finset.univ : Finset (Fin h → ZMod 2)).val.map fun y => Q.eval (Fin.append w y)

/-- The raw amplitude is the scale over `√2^h` times the phase multiset's character sum. -/
theorem ampCore_eq_phaseMultiset (m h : ℕ) (Q : DiagPhase (n + h) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m h Q c w
      = c / (Real.sqrt 2 : ℂ) ^ h * ((phaseMultiset Q w).map (charOf m)).sum := by
  rw [ampCore_eq_sum_charOf, phaseMultiset, Multiset.map_map]
  rfl

/-- `√2 ≠ 0` in `ℂ`. -/
theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- **The kernel on carrier records.** At one free word, two exponents with the same precision,
height and nonzero scale give the same raw amplitude exactly when their phase multisets have the
same antipodal differences. -/
theorem ampCore_eq_iff_antipodal {m h : ℕ} (hm : 1 ≤ m) (Q Q' : DiagPhase (n + h) m) {c : ℂ}
    (hc : c ≠ 0) (w : Fin n → ZMod 2) :
    ampCore m h Q c w = ampCore m h Q' c w
      ↔ ∀ z, ((phaseMultiset Q w).count z : ℤ) - (phaseMultiset Q w).count (z + 2 ^ (m - 1))
          = (phaseMultiset Q' w).count z - (phaseMultiset Q' w).count (z + 2 ^ (m - 1)) := by
  rw [ampCore_eq_phaseMultiset, ampCore_eq_phaseMultiset,
    mul_right_inj' (div_ne_zero hc (pow_ne_zero _ sqrt_two_ne_zero))]
  exact sum_map_charOf_eq_iff hm _ _

/-! ## Antipodal cancellation -/

/-- The character of the top bit is `−1`. -/
theorem charOf_two_pow_pred {m : ℕ} (hm : 1 ≤ m) :
    charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
  have h := charOf_two_pow_mul hm 1
  simpa using h

/-- **Paths cancel in antipodal pairs.** If an involution of a finite set of paths moves each path
to one whose exponent is the top bit more, the character sum over all paths is the sum over the
paths it fixes. -/
theorem sum_charOf_eq_sum_fixed {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 1 ≤ m)
    {τ : ι → ι} (hτ : Function.Involutive τ) {F : ι → ZMod (2 ^ m)}
    (hF : ∀ y, τ y ≠ y → F (τ y) = F y + 2 ^ (m - 1)) :
    ∑ y, charOf m (F y) = ∑ y ∈ Finset.univ.filter (fun y => τ y = y), charOf m (F y) := by
  have hmoved : ∑ y ∈ Finset.univ.filter (fun y => ¬ τ y = y), charOf m (F y) = 0 := by
    refine Finset.sum_involution (fun y _ => τ y) (fun y hy => ?_) (fun y hy _ => ?_)
      (fun y hy => ?_) (fun y _ => hτ y)
    · rw [hF y (Finset.mem_filter.mp hy).2, charOf_add, charOf_two_pow_pred hm]
      ring
    · exact (Finset.mem_filter.mp hy).2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hτ y]
      exact fun h => hy h.symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => τ y = y), hmoved, add_zero]

/-- **The cancel shape.** `τ` is an involution of the bound words, one for every free word, and at
every support word each word `τ` moves has exponent the top bit `2^{m−1}` more than its
partner's. -/
def CancelData {m h : ℕ} (Q : DiagPhase (n + h) m) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2) (τ : (Fin h → ZMod 2) → Fin h → ZMod 2) : Prop :=
  Function.Involutive τ ∧ ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y, τ y ≠ y →
    Q.eval (Fin.append w (τ y)) = Q.eval (Fin.append w y) + 2 ^ (m - 1)

/-- **The kept words.** `e` enumerates the bound words `τ` fixes, each once. -/
def KeepData {h h' : ℕ} (τ : (Fin h → ZMod 2) → Fin h → ZMod 2)
    (e : (Fin h' → ZMod 2) → Fin h → ZMod 2) : Prop :=
  Function.Injective e ∧ ∀ y, τ y = y ↔ ∃ z, e z = y

/-- **Cancel.** The paths `τ` pairs dropped: the bound register is the kept words, read through
`e` by the exponent `Q'` supplied as data; the scale is `c·√2^{h'}/√2^h`; the support is
unchanged. -/
noncomputable def elimCancel {m h' : ℕ} (h : ℕ) (Q' : DiagPhase (n + h') m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) : KernelSumState n :=
  ⟨m, h', Q', c * (Real.sqrt 2 : ℂ) ^ h' / (Real.sqrt 2 : ℂ) ^ h, L, x₀⟩

/-- The kept words carry the whole character sum. -/
theorem sum_charOf_keep {m h h' : ℕ} (hm : 1 ≤ m) {F : (Fin h → ZMod 2) → ZMod (2 ^ m)}
    {τ : (Fin h → ZMod 2) → Fin h → ZMod 2} (hτ : Function.Involutive τ)
    (hF : ∀ y, τ y ≠ y → F (τ y) = F y + 2 ^ (m - 1))
    {e : (Fin h' → ZMod 2) → Fin h → ZMod 2} (he : KeepData τ e) :
    ∑ z, charOf m (F (e z)) = ∑ y, charOf m (F y) := by
  rw [sum_charOf_eq_sum_fixed hm hτ hF]
  have himage : Finset.univ.image e = Finset.univ.filter (fun y => τ y = y) := by
    ext y
    simp [he.2 y]
  rw [← himage, Finset.sum_image fun a _ b _ hab => he.1 hab]

/-- **The cancel certificate.** With the cancel shape on the support and the output exponent
reading the input's through `e` there, the cancelled record denotes the input's state. -/
theorem amp_elimCancel {m h h' : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h) m} (c : ℂ)
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    {τ : (Fin h → ZMod 2) → Fin h → ZMod 2} (hτ : CancelData Q L x₀ τ)
    {e : (Fin h' → ZMod 2) → Fin h → ZMod 2} (he : KeepData τ e) {Q' : DiagPhase (n + h') m}
    (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ z : Fin h' → ZMod 2,
      Q'.eval (Fin.append w z) = Q.eval (Fin.append w (e z))) :
    amp (elimCancel h Q' c L x₀) = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := elimCancel h Q' c L x₀) hw,
      amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
    change ampCore m h' Q' (c * (Real.sqrt 2 : ℂ) ^ h' / (Real.sqrt 2 : ℂ) ^ h) w
      = ampCore m h Q c w
    rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf,
      Finset.sum_congr rfl fun z _ => by rw [hQ' w hw z],
      sum_charOf_keep (F := fun y => Q.eval (Fin.append w y)) hm hτ.1 (hτ.2 w hw) he]
    have h2 := sqrt_two_ne_zero
    field_simp
  · rw [amp_neg (S := elimCancel h Q' c L x₀) hw,
      amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

/-! ## The extended rules -/

/-- One step of the extended rules: a gauge rewrite R1–R7, a collapse or rotate elimination with
the hypotheses of its certificate, or an antipodal cancellation. -/
inductive ExtStep : KernelSumState n → KernelSumState n → Prop
  /-- R1–R7. -/
  | gauge {S T : KernelSumState n} (hST : GaugeStep S T) : ExtStep S T
  /-- Collapse (`amp_elimCollapse`). -/
  | collapse {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h + 1) m} (c : ℂ)
      {L : Submodule (ZMod 2) (Pauli n)} {x₀ σ : Fin n → ZMod 2} {ε : ZMod 2}
      (hsign : SignAffine Q L x₀ σ ε) {L'' : Submodule (ZMod 2) (Pauli n)}
      {x₀'' : Fin n → ZMod 2}
      (hsupp : ∀ w : Fin n → ZMod 2,
        (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X) ∧ ε + dotF2 σ w = 0) :
      ExtStep ⟨m, h + 1, Q, c, L, x₀⟩ (elimCollapse Q c L'' x₀'')
  /-- Rotate (`amp_elimRotate`). -/
  | rotate {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h + 1) m} (c : ℂ)
      {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2} {a : ZMod (2 ^ m)}
      {Λ : DiagPhase (n + h) m} (hrot : RotateData Q L x₀ a Λ)
      {L'' : Submodule (ZMod 2) (Pauli n)} {x₀'' : Fin n → ZMod 2}
      (hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X)) :
      ExtStep ⟨m, h + 1, Q, c, L, x₀⟩ (elimRotate Q a Λ c L'' x₀'')
  /-- Antipodal cancellation (`amp_elimCancel`). -/
  | cancel {m h h' : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h) m} (c : ℂ)
      {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
      {τ : (Fin h → ZMod 2) → Fin h → ZMod 2} (hτ : CancelData Q L x₀ τ)
      {e : (Fin h' → ZMod 2) → Fin h → ZMod 2} (he : KeepData τ e) {Q' : DiagPhase (n + h') m}
      (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ z : Fin h' → ZMod 2,
        Q'.eval (Fin.append w z) = Q.eval (Fin.append w (e z))) :
      ExtStep ⟨m, h, Q, c, L, x₀⟩ (elimCancel h Q' c L x₀)

/-- The extended rules, each in either direction. -/
def ExtRel : KernelSumState n → KernelSumState n → Prop :=
  Relation.EqvGen ExtStep

/-- Each extended step keeps the denotation. -/
theorem stateEq_of_extStep {S T : KernelSumState n} (hST : ExtStep S T) : StateEq S T := by
  cases hST with
  | gauge h => exact stateEq_of_gaugeStep h
  | collapse hm c hsign hsupp => exact (amp_elimCollapse hm c hsign hsupp).symm
  | rotate hm c hrot hsupp => exact (amp_elimRotate hm c hrot hsupp).symm
  | cancel hm c hτ he hQ' => exact (amp_elimCancel hm c hτ he hQ').symm

/-- **Soundness of the extended rules.** -/
theorem stateEq_of_extRel {S T : KernelSumState n} (hST : ExtRel S T) : StateEq S T := by
  induction hST with
  | rel _ _ h => exact stateEq_of_extStep h
  | refl _ => exact StateEq.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Forward chains of extended steps keep the denotation. -/
theorem stateEq_of_reflTransGen {S T : KernelSumState n}
    (hST : Relation.ReflTransGen ExtStep S T) : StateEq S T := by
  induction hST with
  | refl => exact StateEq.refl _
  | tail _ h ih => exact ih.trans (stateEq_of_extStep h)

/-- The moved exponent evaluates as the original at the word read through the transposition
(private in `EliminationOrder.lean`). -/
theorem eval_boundToLast {m h : ℕ} (j : Fin (h + 1)) (Q : DiagPhase (n + (h + 1)) m)
    (v : Fin (n + h + 1) → ZMod 2) :
    DiagPhase.eval (boundToLast j Q) v
      = DiagPhase.eval Q (v ∘ Equiv.swap (Fin.natAdd n j) (Fin.last (n + h))) := by
  unfold boundToLast DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  rfl

/-! ## T04: the two stuck outcomes, joined at height zero -/

namespace EliminationOrder'

open FTQCLib.Frame.Walkthrough.EliminationOrder FTQCLib.Hierarchy.DiagPhase

/-- `lambdaB` evaluates to `1 − y₀·y₁` (private in `EliminationOrder.lean`). -/
theorem eval_lambdaB (v : Fin (0 + 2) → ZMod 2) :
    DiagPhase.eval lambdaB v = 1 - ((v 0).val : ZMod (2 ^ 2)) * ((v 1).val : ZMod (2 ^ 2)) := by
  unfold lambdaB DiagPhase.eval
  simp [DiagPhase.liftBinary]

/-- A word of two bits. -/
theorem word_two (y : Fin 2 → ZMod 2) : y = ![y 0, y 1] := by
  funext i
  fin_cases i <;> rfl

/-- A word of one bit. -/
theorem word_one (z : Fin 1 → ZMod 2) : z = ![z 0] := by
  funext i
  fin_cases i
  rfl

/-- The support of a record with no free bits and `L = ⊥` is the one empty word. -/
theorem mem_support_bot (w : Fin 0 → ZMod 2) :
    ∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 0)), w = 0 + p.X :=
  ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩

/-- Sequence A's outcome exponent. -/
noncomputable def qA : DiagPhase (0 + 2) 2 :=
  snocFreeze 0 (boundToLast (h := 2) 0 inputExponent) + MvPolynomial.C (-1) * lambdaA

/-- Sequence B's outcome exponent. -/
noncomputable def qB : DiagPhase (0 + 2) 2 :=
  snocFreeze 0 (boundToLast (h := 2) 1 inputExponent) + MvPolynomial.C (-1) * lambdaB

/-- The outcomes' common scale `(1 + i)/√2`. -/
noncomputable def cAB : ℂ := 1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)

theorem outcomeA_eq : outcomeA = ⟨2, 2, qA, cAB, ⊥, 0⟩ := rfl

theorem outcomeB_eq : outcomeB = ⟨2, 2, qB, cAB, ⊥, 0⟩ := rfl

/-- A's pairing: flip `y₁` where `y₀ = 1`. It pairs the words `10` and `11`, of exponents `0`
and `2`. -/
def τA (y : Fin 2 → ZMod 2) : Fin 2 → ZMod 2 := ![y 0, y 1 + y 0]

/-- B's pairing: flip `y₀` where `y₁ = 1`. It pairs the words `01` and `11`, of exponents `3`
and `1`. -/
def τB (y : Fin 2 → ZMod 2) : Fin 2 → ZMod 2 := ![y 0 + y 1, y 1]

/-- A's kept words: `y₀ = 0`, read `z ↦ 0z`. -/
def eA (z : Fin 1 → ZMod 2) : Fin 2 → ZMod 2 := ![0, z 0]

/-- B's kept words: `y₁ = 0`, read `z ↦ (1 + z)0`, so that both kept exponents are `3z`. -/
def eB (z : Fin 1 → ZMod 2) : Fin 2 → ZMod 2 := ![1 + z 0, 0]

/-- The kept exponent of both outcomes: `3·z`. -/
noncomputable def q3 : DiagPhase (0 + 1) 2 := MvPolynomial.C 3 * MvPolynomial.X 0

theorem involutive_τA : Function.Involutive τA := by
  have h : ∀ y, τA (τA y) = y := by decide
  exact h

theorem involutive_τB : Function.Involutive τB := by
  have h : ∀ y, τB (τB y) = y := by decide
  exact h

theorem cancelData_A : CancelData qA ⊥ 0 τA := by
  refine ⟨involutive_τA, fun w _ y hy => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [word_two y] at hy ⊢
  generalize y 0 = a, y 1 = b at hy ⊢
  revert hy
  simp only [qA, τA, eval_add, eval_mul, eval_C, snocFreeze_eval, eval_boundToLast,
    inputExponent, lambdaA, eval_X]
  revert a b
  decide

theorem cancelData_B : CancelData qB ⊥ 0 τB := by
  refine ⟨involutive_τB, fun w _ y hy => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [word_two y] at hy ⊢
  generalize y 0 = a, y 1 = b at hy ⊢
  revert hy
  simp only [qB, τB, eval_add, eval_mul, eval_C, snocFreeze_eval, eval_boundToLast,
    inputExponent, eval_lambdaB, eval_X]
  revert a b
  decide

theorem keepData_A : KeepData τA eA := ⟨by decide, by decide⟩

theorem keepData_B : KeepData τB eB := ⟨by decide, by decide⟩

theorem keep_A : ∀ w : Fin 0 → ZMod 2, (∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 0)), w = 0 + p.X) →
    ∀ z : Fin 1 → ZMod 2, q3.eval (Fin.append w z) = qA.eval (Fin.append w (eA z)) := by
  intro w _ z
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [word_one z]
  generalize z 0 = a
  simp only [q3, qA, eA, eval_add, eval_mul, eval_C, snocFreeze_eval, eval_boundToLast,
    inputExponent, lambdaA, eval_X]
  revert a
  decide

theorem keep_B : ∀ w : Fin 0 → ZMod 2, (∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 0)), w = 0 + p.X) →
    ∀ z : Fin 1 → ZMod 2, q3.eval (Fin.append w z) = qB.eval (Fin.append w (eB z)) := by
  intro w _ z
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [word_one z]
  generalize z 0 = a
  simp only [q3, qB, eB, eval_add, eval_mul, eval_C, snocFreeze_eval, eval_boundToLast,
    inputExponent, eval_lambdaB, eval_X]
  revert a
  decide

/-- The height-one record both outcomes cancel to: exponent `3·z`, scale `cAB/√2`. -/
noncomputable def cancelled : KernelSumState 0 := elimCancel 2 q3 cAB ⊥ 0

theorem extStep_outcomeA : ExtStep outcomeA cancelled := by
  rw [outcomeA_eq]
  exact ExtStep.cancel (by norm_num) cAB cancelData_A keepData_A keep_A

theorem extStep_outcomeB : ExtStep outcomeB cancelled := by
  rw [outcomeB_eq]
  exact ExtStep.cancel (by norm_num) cAB cancelData_B keepData_B keep_B

/-- The rotate shape at the one bound bit of `cancelled`: difference `3`, with `2·3 = 2`. -/
theorem rotateData_q3 : RotateData (n := 0) (h := 0) q3 ⊥ 0 3 0 := by
  refine ⟨by decide, fun w _ y => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  obtain rfl : y = 0 := Subsingleton.elim _ _
  refine ⟨0, ?_, ?_⟩
  · simp [DiagPhase.eval]
  · rw [lastDiff_eval]
    simp only [q3, eval_mul, eval_C, eval_X]
    decide

/-- **The floor.** The height-zero record `cancelled` rotates to. -/
noncomputable def floor : KernelSumState 0 :=
  elimRotate (n := 0) (h := 0) q3 3 0 cancelled.c ⊥ 0

theorem extStep_cancelled : ExtStep cancelled floor :=
  ExtStep.rotate (m := 2) (h := 0) (by norm_num) _ rotateData_q3 fun _ => Iff.rfl

/-- **T04's two stuck outcomes, joined.** Each cancels one antipodal pair to `cancelled`, which one
rotate takes to `floor`, of height zero; `floor` denotes the input's state. -/
theorem outcomes_join :
    Relation.ReflTransGen ExtStep outcomeA floor
      ∧ Relation.ReflTransGen ExtStep outcomeB floor
      ∧ cancelled.h = 1 ∧ floor.h = 0 ∧ StateEq floor input := by
  have hA : Relation.ReflTransGen ExtStep outcomeA floor :=
    (Relation.ReflTransGen.single extStep_outcomeA).tail extStep_cancelled
  have hB : Relation.ReflTransGen ExtStep outcomeB floor :=
    (Relation.ReflTransGen.single extStep_outcomeB).tail extStep_cancelled
  exact ⟨hA, hB, rfl, rfl, (stateEq_of_reflTransGen hA).symm.trans stateEq_outcomeA_input⟩

/-- `charOf 2 1 = i`. -/
theorem charOf_two_one : charOf 2 1 = Complex.I := by
  have h := charOf_two_pow_sub_two_mul (m := 2) le_rfl 1
  simpa using h

/-- `charOf 2 3 = −i`. -/
theorem charOf_two_three : charOf 2 3 = -Complex.I := by
  have h := charOf_two_pow_sub_two_mul (m := 2) le_rfl 3
  rw [show (2 : ZMod (2 ^ 2)) ^ (2 - 2) * ((3 : ℕ) : ZMod (2 ^ 2)) = 3 by decide] at h
  rw [h, pow_succ, Complex.I_sq]
  ring

/-- `floor` is the scalar `1/√2`: its scale is `(1 + i)/√2 · √2/2 · (1 − i)/√2`. -/
theorem floor_c : floor.c = 1 / (Real.sqrt 2 : ℂ) := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hne := sqrt_two_ne_zero
  change cAB * (Real.sqrt 2 : ℂ) ^ 1 / (Real.sqrt 2 : ℂ) ^ 2 * (1 + charOf 2 3)
      / (Real.sqrt 2 : ℂ) = 1 / (Real.sqrt 2 : ℂ)
  rw [cAB, charOf_two_one, charOf_two_three, h2]
  field_simp
  linear_combination (-1 : ℂ) * Complex.I_sq

end EliminationOrder'

/-! ## The scale obstruction -/

/-- Two records' scales are in one class when `‖c‖²` differs by an integer power of `2`. -/
def SameScaleClass (S T : KernelSumState n) : Prop :=
  ∃ k : ℤ, ‖T.c‖ ^ 2 = ‖S.c‖ ^ 2 * (2 : ℝ) ^ k

theorem SameScaleClass.refl (S : KernelSumState n) : SameScaleClass S S :=
  ⟨0, by rw [zpow_zero, mul_one]⟩

theorem SameScaleClass.symm {S T : KernelSumState n} (h : SameScaleClass S T) :
    SameScaleClass T S := by
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  rw [hk, mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, mul_one]

theorem SameScaleClass.trans {S T U : KernelSumState n} (h₁ : SameScaleClass S T)
    (h₂ : SameScaleClass T U) : SameScaleClass S U := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exact ⟨k₁ + k₂, by rw [hk₂, hk₁, mul_assoc, ← zpow_add₀ two_ne_zero]⟩

/-- Equal scales are in one class. -/
theorem sameScaleClass_of_c_eq {S T : KernelSumState n} (h : S.c = T.c) : SameScaleClass S T :=
  ⟨0, by rw [h, zpow_zero, mul_one]⟩

/-- The character has modulus one. -/
theorem norm_charOf (m : ℕ) (z : ZMod (2 ^ m)) : ‖charOf m z‖ = 1 := by
  unfold charOf
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `‖√2‖² = 2` in `ℂ`. -/
theorem norm_sqrt_two_sq : ‖(Real.sqrt 2 : ℂ)‖ ^ 2 = 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]

/-- `‖√2^j‖² = 2^j` in `ℂ`. -/
theorem norm_sqrt_two_pow_sq (j : ℕ) : ‖(Real.sqrt 2 : ℂ) ^ j‖ ^ 2 = (2 : ℝ) ^ j := by
  rw [norm_pow, ← pow_mul, mul_comm, pow_mul, norm_sqrt_two_sq]

/-- The rotate scale has modulus `√2`: with `2a = 2^{m−1}`, `charOf a = ±i`. -/
theorem norm_one_add_charOf_sq {m : ℕ} (hm : 1 ≤ m) {a : ZMod (2 ^ m)}
    (ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1)) : ‖1 + charOf m a‖ ^ 2 = 2 := by
  have hsq : charOf m a * charOf m a = -1 := by
    rw [← charOf_add, ← two_mul, ha, charOf_two_pow_pred hm]
  have hroots : (charOf m a - Complex.I) * (charOf m a + Complex.I) = 0 := by
    linear_combination hsq - Complex.I_sq
  rcases mul_eq_zero.mp hroots with h | h
  · rw [sub_eq_zero.mp h, Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  · rw [eq_neg_of_add_eq_zero_left h, Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num

/-- Every gauge rewrite keeps the scale's modulus. -/
theorem sameScaleClass_of_gaugeStep {S T : KernelSumState n} (hST : GaugeStep S T) :
    SameScaleClass S T := by
  cases hST with
  | addC Q a c L x₀ =>
    exact ⟨0, by simp only [norm_mul, norm_charOf, mul_one, zpow_zero]⟩
  | offsetAddMem Q c L x₀ hv => exact SameScaleClass.refl _
  | congrXProj Q c L L' x₀ hsh => exact sameScaleClass_of_c_eq rfl
  | congrSupport Q Q' c L x₀ hQ => exact sameScaleClass_of_c_eq rfl
  | renameBound Q Q' c L x₀ σ hQ => exact sameScaleClass_of_c_eq rfl
  | hRaiseIndep i u u' S horth hui hrep hui' hrep' hm => exact sameScaleClass_of_c_eq rfl
  | liftTo k hmk Q c L x₀ => exact sameScaleClass_of_c_eq rfl

/-- **Every extended step multiplies `‖c‖²` by a power of two:** R1 by a character, collapse by
`2`, rotate by `‖1 + charOf a‖²/2 = 1`, cancellation by `2^{h'}/2^h`, the rest by `1`. -/
theorem sameScaleClass_of_extStep {S T : KernelSumState n} (hST : ExtStep S T) :
    SameScaleClass S T := by
  cases hST with
  | gauge h => exact sameScaleClass_of_gaugeStep h
  | @collapse m h hm Q c L x₀ σ ε hsign L'' x₀'' hsupp =>
    refine ⟨1, ?_⟩
    change ‖(Real.sqrt 2 : ℂ) * c‖ ^ 2 = ‖c‖ ^ 2 * (2 : ℝ) ^ (1 : ℤ)
    rw [norm_mul, mul_pow, norm_sqrt_two_sq, zpow_one, mul_comm]
  | @rotate m h hm Q c L x₀ a Λ hrot L'' x₀'' hsupp =>
    refine ⟨0, ?_⟩
    change ‖c * (1 + charOf m a) / (Real.sqrt 2 : ℂ)‖ ^ 2 = ‖c‖ ^ 2 * (2 : ℝ) ^ (0 : ℤ)
    rw [norm_div, norm_mul, div_pow, mul_pow, norm_one_add_charOf_sq hm hrot.1,
      norm_sqrt_two_sq, zpow_zero, mul_one, mul_div_cancel_right₀ _ two_ne_zero]
  | @cancel m h h' hm Q c L x₀ τ hτ e he Q' hQ' =>
    refine ⟨(h' : ℤ) - h, ?_⟩
    change ‖c * (Real.sqrt 2 : ℂ) ^ h' / (Real.sqrt 2 : ℂ) ^ h‖ ^ 2
      = ‖c‖ ^ 2 * (2 : ℝ) ^ ((h' : ℤ) - h)
    rw [norm_div, norm_mul, div_pow, mul_pow, norm_sqrt_two_pow_sq, norm_sqrt_two_pow_sq,
      zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, mul_div_assoc]

/-- **The invariant.** The extended rules, used in either direction, keep `‖c‖²` up to a power of
two. -/
theorem sameScaleClass_of_extRel {S T : KernelSumState n} (hST : ExtRel S T) :
    SameScaleClass S T := by
  induction hST with
  | rel _ _ h => exact sameScaleClass_of_extStep h
  | refl S => exact SameScaleClass.refl S
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

namespace ScaleWitness

open FTQCLib.Hierarchy.DiagPhase

/-- The controlled-`S` phase `i^{y₀y₁}` summed over two bound bits, scale `1`: amplitude
`(1 + 1 + 1 + i)/2`. -/
noncomputable def pathState : KernelSumState 0 :=
  ⟨2, 2, MvPolynomial.X 0 * MvPolynomial.X 1, 1, ⊥, 0⟩

/-- The same amplitude as a height-zero record: scale `(3 + i)/2`. -/
noncomputable def scalarState : KernelSumState 0 :=
  ⟨2, 0, 0, (3 + Complex.I) / 2, ⊥, 0⟩

/-- A sum over the four words of two bits. -/
theorem sum_words_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → ZMod 2) → M) :
    ∑ y, F y = F ![0, 0] + F ![0, 1] + (F ![1, 0] + F ![1, 1]) := by
  rw [← (piFinTwoEquiv fun _ => ZMod 2).symm.sum_comp F, Fintype.sum_prod_type]
  simp only [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide : (0 : ZMod 2) ∉ ({1} : Finset (ZMod 2))),
    Finset.sum_singleton]
  rfl

theorem amp_pathState : amp pathState = fun _ => (3 + Complex.I) / 2 := by
  funext w
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [amp_pos (EliminationOrder'.mem_support_bot 0)]
  change ampCore 2 2 (MvPolynomial.X 0 * MvPolynomial.X 1) 1 0 = _
  rw [ampCore_eq_sum_charOf, sum_words_two]
  simp only [eval_mul, eval_X]
  have e00 : ((((Fin.append (0 : Fin 0 → ZMod 2) ![0, 0] : Fin (0 + 2) → ZMod 2) 0).val
      : ZMod (2 ^ 2)) * (((Fin.append (0 : Fin 0 → ZMod 2) ![0, 0] : Fin (0 + 2) → ZMod 2) 1).val
      : ZMod (2 ^ 2))) = 0 := by decide
  have e01 : ((((Fin.append (0 : Fin 0 → ZMod 2) ![0, 1] : Fin (0 + 2) → ZMod 2) 0).val
      : ZMod (2 ^ 2)) * (((Fin.append (0 : Fin 0 → ZMod 2) ![0, 1] : Fin (0 + 2) → ZMod 2) 1).val
      : ZMod (2 ^ 2))) = 0 := by decide
  have e10 : ((((Fin.append (0 : Fin 0 → ZMod 2) ![1, 0] : Fin (0 + 2) → ZMod 2) 0).val
      : ZMod (2 ^ 2)) * (((Fin.append (0 : Fin 0 → ZMod 2) ![1, 0] : Fin (0 + 2) → ZMod 2) 1).val
      : ZMod (2 ^ 2))) = 0 := by decide
  have e11 : ((((Fin.append (0 : Fin 0 → ZMod 2) ![1, 1] : Fin (0 + 2) → ZMod 2) 0).val
      : ZMod (2 ^ 2)) * (((Fin.append (0 : Fin 0 → ZMod 2) ![1, 1] : Fin (0 + 2) → ZMod 2) 1).val
      : ZMod (2 ^ 2))) = 1 := by decide
  rw [e00, e01, e10, e11, charOf_zero, EliminationOrder'.charOf_two_one]
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h2]
  ring

theorem amp_scalarState : amp scalarState = fun _ => (3 + Complex.I) / 2 := by
  funext w
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [amp_pos (EliminationOrder'.mem_support_bot 0)]
  change ampCore 2 0 (0 : DiagPhase (0 + 0) 2) ((3 + Complex.I) / 2) 0 = _
  rw [ampCore_eq_sum_charOf, Fintype.sum_unique]
  simp [DiagPhase.eval, charOf_zero]

theorem stateEq_pathState_scalarState : StateEq pathState scalarState :=
  amp_pathState.trans amp_scalarState.symm

/-- A record with no free bits and `L = ⊥` and nonzero denotation is a carrier state. -/
theorem isCarrier_of_bot {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (0 + h) m) (c : ℂ)
    (hne : amp (⟨m, h, Q, c, ⊥, 0⟩ : KernelSumState 0) ≠ 0) :
    IsCarrier (⟨m, h, Q, c, ⊥, 0⟩ : KernelSumState 0) := by
  have hzero : ∀ p : Pauli 0, p = 0 := fun p => Pauli.ext (Subsingleton.elim _ _)
    (Subsingleton.elim _ _)
  refine ⟨hm, fun p _ q _ => ?_, fun p _ => ?_, hne⟩
  · rw [hzero p]
    exact omega_zero_left q
  · rw [hzero p]
    exact Submodule.zero_mem _

/-- The amplitude `(3 + i)/2` is not zero. -/
theorem three_add_I_div_two_ne_zero : (3 + Complex.I) / 2 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem isCarrier_pathState : IsCarrier pathState := by
  refine isCarrier_of_bot (by norm_num) _ _ ?_
  intro h
  exact three_add_I_div_two_ne_zero (congrFun (amp_pathState.symm.trans h) 0)

theorem isCarrier_scalarState : IsCarrier scalarState := by
  refine isCarrier_of_bot (by norm_num) _ _ ?_
  intro h
  exact three_add_I_div_two_ne_zero (congrFun (amp_scalarState.symm.trans h) 0)

/-- `5/2` is not an integer power of two. -/
theorem five_div_two_ne_zpow (k : ℤ) : (5 / 2 : ℝ) ≠ (2 : ℝ) ^ k := by
  intro hk
  have h5 : (5 : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [zpow_add_one₀ two_ne_zero, ← hk]
    norm_num
  rcases Int.eq_nat_or_neg (k + 1) with ⟨t, ht | ht⟩
  · rw [ht, zpow_natCast] at h5
    have h5' : (5 : ℕ) = 2 ^ t := by exact_mod_cast h5
    rcases t with _ | t
    · norm_num at h5'
    · rw [pow_succ] at h5'
      omega
  · rw [ht, zpow_neg, zpow_natCast] at h5
    have hle : ((2 : ℝ) ^ t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    linarith

/-- The two scales are in different classes: `‖1‖² = 1` and `‖(3 + i)/2‖² = 5/2`. -/
theorem not_sameScaleClass : ¬ SameScaleClass pathState scalarState := by
  rintro ⟨k, hk⟩
  have hs : ‖(3 + Complex.I) / 2‖ ^ 2 = 5 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_apply, Complex.normSq_apply]
    norm_num
  change ‖(3 + Complex.I) / 2‖ ^ 2 = ‖(1 : ℂ)‖ ^ 2 * (2 : ℝ) ^ k at hk
  rw [hs, norm_one, one_pow, one_mul] at hk
  exact five_div_two_ne_zpow k hk

/-- A relation whose steps keep the scale class keeps it along its equivalence closure. -/
theorem sameScaleClass_of_eqvGen {n : ℕ} (r : KernelSumState n → KernelSumState n → Prop)
    (hr : ∀ S T, r S T → SameScaleClass S T) {S T : KernelSumState n}
    (h : Relation.EqvGen r S T) : SameScaleClass S T := by
  induction h with
  | rel S T hST => exact hr S T hST
  | refl S => exact SameScaleClass.refl S
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **No rule set that keeps the scale class is complete.** Any relation whose steps keep `‖c‖²`
up to a power of two, closed under both directions and chaining, leaves `pathState` and
`scalarState` unrelated. -/
theorem not_eqvGen_of_sameScaleClass (r : KernelSumState 0 → KernelSumState 0 → Prop)
    (hr : ∀ S T, r S T → SameScaleClass S T) : ¬ Relation.EqvGen r pathState scalarState :=
  fun h => not_sameScaleClass (sameScaleClass_of_eqvGen r hr h)

/-- **The scale obstruction.** Two carrier states with one amplitude that no chain of gauge
rewrites, collapses, rotations and cancellations, in either direction, relates. -/
theorem scale_obstruction :
    IsCarrier pathState ∧ IsCarrier scalarState ∧ StateEq pathState scalarState
      ∧ ¬ ExtRel pathState scalarState :=
  ⟨isCarrier_pathState, isCarrier_scalarState, stateEq_pathState_scalarState,
    not_eqvGen_of_sameScaleClass ExtStep fun _ _ => sameScaleClass_of_extStep⟩

end ScaleWitness

/-! ## What cancellation does not reach: a pairing that moves with the free word -/

namespace HHWitness

open FTQCLib.Hierarchy.DiagPhase

/-- `⟨X₀⟩` on one qubit: its shadow is every word. -/
noncomputable def lagX : Submodule (ZMod 2) (Pauli 1) := Submodule.span (ZMod 2) {paulix 0}

theorem isStabilizer_lagX : IsStabilizer lagX := by
  intro p hp q hq
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
  rw [omega_smul_left, omega_smul_right, omega_self]
  simp

theorem lagX_support (w : Fin 1 → ZMod 2) : ∃ p ∈ lagX, w = (0 : Fin 1 → ZMod 2) + p.X := by
  refine ⟨(w 0) • paulix 0, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
  funext i
  fin_cases i
  simp [paulix]

/-- Every word on one qubit is `![0]` or `![1]`. -/
theorem word_cases (w : Fin 1 → ZMod 2) : w = ![0] ∨ w = ![1] := by
  rcases zmod_two_eq_zero_or_one (w 0) with h | h
  · left
    funext i
    fin_cases i
    exact h
  · right
    funext i
    fin_cases i
    exact h

/-- The exponent `4·y₀·(y₁ + w₀) + y₁` over `ZMod 8`: variable `0` is the free bit `w₀`, `1` and
`2` are the bound bits `y₀`, `y₁`. Summing `y₀` forces `y₁ = w₀`, leaving the phase `ζ₈^{w₀}`:
Vilmart's (HH) with a bound partner. -/
noncomputable def qHH : DiagPhase (1 + 2) 3 :=
  MvPolynomial.C 4 * MvPolynomial.X 1 * (MvPolynomial.X 2 + MvPolynomial.X 0) + MvPolynomial.X 2

/-- The record: two bound bits, scale `1`, support every word. -/
noncomputable def hhState : KernelSumState 1 := ⟨3, 2, qHH, 1, lagX, 0⟩

/-- Its reduct under (HH): height zero, the `T` phase `ζ₈^{w₀}`. -/
noncomputable def tState : KernelSumState 1 := ⟨3, 0, MvPolynomial.X 0, 1, lagX, 0⟩

/-- `charOf 3 4 = −1`. -/
theorem charOf_three_four : charOf 3 4 = -1 := by
  have h := charOf_two_pow_pred (m := 3) (by norm_num)
  rwa [show (2 : ZMod (2 ^ 3)) ^ (3 - 1) = 4 by decide] at h

/-- `charOf 3 5 = −charOf 3 1`. -/
theorem charOf_three_five : charOf 3 5 = -charOf 3 1 := by
  rw [show (5 : ZMod (2 ^ 3)) = 1 + 4 by decide, charOf_add, charOf_three_four, mul_neg_one]

theorem sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The record's amplitude is the `T` phase: `ζ₈^{w₀}`. -/
theorem amp_hhState (w : Fin 1 → ZMod 2) :
    amp hhState w = charOf 3 ((w 0).val : ZMod (2 ^ 3)) := by
  rw [amp_pos (lagX_support w)]
  change ampCore 3 2 qHH 1 w = _
  rw [ampCore_eq_sum_charOf, ScaleWitness.sum_words_two, sqrt_two_sq]
  rcases word_cases w with rfl | rfl
  · have e00 : qHH.eval (Fin.append ![0] ![0, 0]) = 0 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    have e01 : qHH.eval (Fin.append ![0] ![0, 1]) = 1 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    have e10 : qHH.eval (Fin.append ![0] ![1, 0]) = 0 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    have e11 : qHH.eval (Fin.append ![0] ![1, 1]) = 5 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    simp only [e00, e01, e10, e11, charOf_zero, charOf_three_five, Matrix.cons_val_zero,
      ZMod.val_zero, Nat.cast_zero]
    ring
  · have e00 : qHH.eval (Fin.append ![1] ![0, 0]) = 0 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    have e01 : qHH.eval (Fin.append ![1] ![0, 1]) = 1 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    have e10 : qHH.eval (Fin.append ![1] ![1, 0]) = 4 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    have e11 : qHH.eval (Fin.append ![1] ![1, 1]) = 1 := by
      simp only [qHH, eval_add, eval_mul, eval_C, eval_X]; decide
    simp only [e00, e01, e10, e11, charOf_zero, charOf_three_four, Matrix.cons_val_zero,
      ZMod.val_one, Nat.cast_one]
    ring

theorem amp_tState (w : Fin 1 → ZMod 2) :
    amp tState w = charOf 3 ((w 0).val : ZMod (2 ^ 3)) := by
  rw [amp_pos (lagX_support w)]
  change ampCore 3 0 (MvPolynomial.X 0) 1 w = _
  rw [ampCore_eq_sum_charOf, Fintype.sum_unique, eval_X]
  simp only [pow_zero, div_one, one_mul]
  congr 2

theorem stateEq_hhState_tState : StateEq hhState tState :=
  funext fun w => (amp_hhState w).trans (amp_tState w).symm

theorem isCarrier_hhState : IsCarrier hhState := by
  refine ⟨(by norm_num : (1 : ℕ) ≤ 3), isStabilizer_lagX,
    orthogonal_le_of_lagrangian isStabilizer_lagX (finrank_span_singleton (by decide)), ?_⟩
  intro h
  have h0 := congrFun h ![0]
  rw [amp_hhState] at h0
  exact charOf_ne_zero 3 _ h0

/-- **No elimination.** Along `y₀` the difference `4·(y₁ + w₀)` reads the bound bit `y₁`, so it is
not a sign of the free word, and it is even, so it is not a rotation; along `y₁` the difference
`4·y₀ + 1` is odd, so it is neither. -/
theorem eliminationStuck_hhState : EliminationStuck (n := 1) (h := 1) qHH lagX 0 := by
  intro j
  fin_cases j
  · rintro (⟨σ, ε, hs⟩ | ⟨a, Λ, h1, h2⟩)
    · have key := (hs ![0] (lagX_support _) ![0]).trans (hs ![0] (lagX_support _) ![1]).symm
      revert key
      simp only [lastDiff_eval, eval_boundToLast, qHH, eval_add, eval_mul, eval_C, eval_X]
      decide
    · obtain ⟨b, -, hb⟩ := h2 ![0] (lagX_support _) ![0]
      clear h2
      revert h1 hb
      simp only [lastDiff_eval, eval_boundToLast, qHH, eval_add, eval_mul, eval_C, eval_X]
      revert a b
      decide
  · rintro (⟨σ, ε, hs⟩ | ⟨a, Λ, h1, h2⟩)
    · have e0 := hs ![0] (lagX_support _) ![0]
      revert e0
      generalize ε + dotF2 σ ![0] = t
      simp only [lastDiff_eval, eval_boundToLast, qHH, eval_add, eval_mul, eval_C, eval_X]
      revert t
      decide
    · obtain ⟨b, -, hb⟩ := h2 ![0] (lagX_support _) ![0]
      clear h2
      revert h1 hb
      simp only [lastDiff_eval, eval_boundToLast, qHH, eval_add, eval_mul, eval_C, eval_X]
      revert a b
      decide

/-- **No cancellation.** No two bound words have exponents antipodal at both free words, so the
only involution with the cancel shape is the identity. The pairs (HH) cancels, `y₀ ↔ y₀ + 1` on
the words with `y₁ ≠ w₀`, are different pairs at the two free words. -/
theorem cancelData_hhState_trivial {τ : (Fin 2 → ZMod 2) → Fin 2 → ZMod 2}
    (hτ : CancelData qHH lagX 0 τ) (y : Fin 2 → ZMod 2) : τ y = y := by
  by_contra hy
  have key : ∀ y y' : Fin 2 → ZMod 2, y' ≠ y →
      ¬ (qHH.eval (Fin.append ![0] y') = qHH.eval (Fin.append ![0] y) + 2 ^ (3 - 1)
        ∧ qHH.eval (Fin.append ![1] y') = qHH.eval (Fin.append ![1] y) + 2 ^ (3 - 1)) := by
    simp only [qHH, eval_add, eval_mul, eval_C, eval_X]
    decide
  exact key y (τ y) hy ⟨hτ.2 ![0] (lagX_support _) y hy, hτ.2 ![1] (lagX_support _) y hy⟩

/-- **The witness.** A carrier state at height two, denoting the height-zero `T` phase, at which
no elimination and no nontrivial cancellation is available. -/
theorem hh_witness :
    IsCarrier hhState ∧ StateEq hhState tState ∧ tState.h = 0
      ∧ EliminationStuck (n := 1) (h := 1) qHH lagX 0
      ∧ ∀ τ, CancelData qHH lagX 0 τ → ∀ y, τ y = y :=
  ⟨isCarrier_hhState, stateEq_hhState_tState, rfl, eliminationStuck_hhState,
    fun _ hτ => cancelData_hhState_trivial hτ⟩

end HHWitness

/-! ## Axioms -/

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.mem_ker_fold_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_ker_fold_iff

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.aeval_eq_zero_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aeval_eq_zero_iff

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.sum_eq_zero_iff_antipodal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_eq_zero_iff_antipodal

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.not_sum_eq_zero_iff_antipodal_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_sum_eq_zero_iff_antipodal_zero

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.sixth_root_not_antipodal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixth_root_not_antipodal

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.sum_map_charOf_eq_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_map_charOf_eq_iff

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.ampCore_eq_iff_antipodal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_eq_iff_antipodal

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.amp_elimCancel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_elimCancel

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.stateEq_of_extRel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_extRel

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.EliminationOrder'.outcomes_join' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EliminationOrder'.outcomes_join

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.EliminationOrder'.floor_c' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EliminationOrder'.floor_c

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.sameScaleClass_of_extRel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sameScaleClass_of_extRel

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.ScaleWitness.scale_obstruction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ScaleWitness.scale_obstruction

/-- info: 'FTQCLib.Explore.CyclotomicKernelB.HHWitness.hh_witness' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HHWitness.hh_witness

end FTQCLib.Explore.CyclotomicKernelB

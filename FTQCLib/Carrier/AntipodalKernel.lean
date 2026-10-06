/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierRules
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The cyclotomic kernel and the row decomposition

A helper module for `RewriteCompleteness.lean` (T07, `docs/TARGETS.md`): the amplitude a carrier
state gives a free word reads its phase counts through the cyclotomic image `ζ_{2^m}`
(`FTQCLib.Carrier.HadamardPhase.ampCore`), and the direct route compares two such counts ("rows")
of a shared length by that image. Three results are ported here, unchanged in statement, from
`FTQCLib/Explore/CyclotomicKernel.lean` (an unimported, standalone exploration):

* `foldMap_eq_zero_iff` — over any commutative ring and at `0 < k`, the kernel of the fold
  `R[X]/(X^{2k} − 1) → R[X]/(X^k + 1)` is the `R`-span of the `k` antipodal pairs `X^a + X^{a+k}`.
* `minpoly_int_two_pow` — over any field of characteristic zero, `X^{2^{m−1}} + 1` is the minimal
  polynomial over `ℤ` of a primitive `2^m`-th root of unity.
* `ampCore_eq_iff_antipodal` — at one free word, two exponents at the same precision `1 ≤ m`, the
  same height and the same nonzero scale give the same amplitude exactly when the difference of
  their phase counts agrees at every pair of antipodal residues `a, a + 2^{m−1}`.

New here is the row decomposition: two rows of one length (functions `ZMod (2^m) → ℕ` with equal
total) whose difference is already antipodal-symmetric (the hypothesis `ampCore_eq_iff_antipodal`
reduces the amplitude equality to) split as `C + N` and `C + P` for a common row `C`, with `N` and
`P` each a sum of antipodal pairs and, since the halves have the same total, the same number of
them.

## Main results

* `foldMap_eq_zero_iff`, `minpoly_int_two_pow`, `ampCore_eq_iff_antipodal` — the ported kernel.
* `rootOfUnity_mem_two_pow` — a root of unity of order a power of two in `ℚ(ζ_{2^m})` is a
  `2^m`-th root, since `ℚ(ζ_{2^k})` has degree `2^{k−1}`. `rewrite_conservative` uses it to keep
  the scale ratio at the states' own precision.
* `row_decomposition` — two rows of one length with an antipodal-symmetric difference are `C + N`
  and `C + P`, with `N` and `P` each pair-symmetric and of the same total, hence the same number of
  antipodal pairs.

## Implementation notes

* The polynomial and cyclotomic sections are copied whole from
  `FTQCLib/Explore/CyclotomicKernel.lean` (`span_le_span`, `foldMap`, `antipodalPair`,
  `mk_pow_mul_mem_span`; `natDegree_minpoly_two_pow`,
  `eq_zero_of_sum_range_eq_zero`, `pow_two_pow_pred_eq_neg_one`); the group-ring section likewise
  (`evalRoot`, `sum_zmod_eq_sum_range`, `two_pow_pred_add_self`, `evalRoot_eq_sum_fold`,
  `evalRoot_eq_zero_iff`), since `ampCore_eq_iff_antipodal` rests on all of them. Only the four
  headline names above are re-exported in this module's docstring; the rest are its private
  scaffolding, exactly as in the source.
* `row_decomposition`'s `C` is the pointwise minimum of the two rows; `N` and `P` are what is left
  of each above `C`. Pair symmetry of `N` and `P` follows from the antipodal-symmetric difference
  by a pointwise `omega` fact relating truncated subtraction of naturals to `max (a - b) 0` over
  `ℤ`; the shared total follows by cancelling `∑ C` from `∑ f = ∑ g`.
-/

namespace FTQCLib.Frame.Walkthrough.AntipodalKernel

/-! ## The polynomial kernel, over any commutative ring -/

section PolynomialKernel

open Polynomial

variable {R : Type*} [CommRing R]

/-- `X^{2k} − 1` is a multiple of `X^k + 1`. -/
theorem span_le_span (k : ℕ) :
    Ideal.span {(X ^ (2 * k) - 1 : R[X])} ≤ Ideal.span {(X ^ k + 1 : R[X])} := by
  rw [Ideal.span_singleton_le_span_singleton]
  exact ⟨X ^ k - 1, by ring⟩

/-- The quotient map from `R[X]/(X^{2k} − 1)` (the group ring of the cyclic group of order `2k`)
onto `R[X]/(X^k + 1)`. -/
noncomputable abbrev foldMap (k : ℕ) :
    R[X] ⧸ Ideal.span {(X ^ (2 * k) - 1 : R[X])} →+* R[X] ⧸ Ideal.span {(X ^ k + 1 : R[X])} :=
  Ideal.Quotient.factor (span_le_span k)

/-- The antipodal pair `X^a + X^{a+k}` in `R[X]/(X^{2k} − 1)`. -/
noncomputable abbrev antipodalPair (k a : ℕ) : R[X] ⧸ Ideal.span {(X ^ (2 * k) - 1 : R[X])} :=
  Ideal.Quotient.mk _ (X ^ a + X ^ (a + k))

/-- Every shift of `X^k + 1` reduces, modulo `X^{2k} − 1`, to an antipodal pair with `a < k`. -/
theorem mk_pow_mul_mem_span {k : ℕ} (hk : 0 < k) (a : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])}) (X ^ a * (X ^ k + 1))
      ∈ Submodule.span R (Set.range fun b : Fin k => (antipodalPair k b : R[X] ⧸ _)) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases lt_or_ge a k with ha | ha
    · refine Submodule.subset_span ⟨⟨a, ha⟩, ?_⟩
      change Ideal.Quotient.mk _ (X ^ a + X ^ (a + k)) = _
      congr 1
      ring
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + k := ⟨a - k, (Nat.sub_add_cancel ha).symm⟩
      have hred : Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])})
            (X ^ (b + k) * (X ^ k + 1))
          = Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])}) (X ^ b * (X ^ k + 1)) := by
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact ⟨X ^ b, by ring⟩
      rw [hred]
      exact ih b (by omega)

/-- **The kernel of the fold, over any commutative ring.** At `0 < k`, the kernel of
`R[X]/(X^{2k} − 1) → R[X]/(X^k + 1)` is the `R`-span of the `k` antipodal pairs `X^a + X^{a+k}`,
`a < k`. -/
theorem foldMap_eq_zero_iff {k : ℕ} (hk : 0 < k)
    (x : R[X] ⧸ Ideal.span {(X ^ (2 * k) - 1 : R[X])}) :
    foldMap k x = 0
      ↔ x ∈ Submodule.span R (Set.range fun a : Fin k => (antipodalPair k a : R[X] ⧸ _)) := by
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [foldMap, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨q, rfl⟩ := hx
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [mul_add, map_add]
      exact Submodule.add_mem _ hp hq
    | monomial a r =>
      have hsmul : Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])})
            ((X ^ k + 1) * monomial a r)
          = r • Ideal.Quotient.mk (Ideal.span {(X ^ (2 * k) - 1 : R[X])})
            (X ^ a * (X ^ k + 1)) := by
        rw [← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul]
        congr 1
        rw [Polynomial.smul_eq_C_mul, ← C_mul_X_pow_eq_monomial]
        ring
      rw [hsmul]
      exact Submodule.smul_mem _ r (mk_pow_mul_mem_span hk a)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [foldMap, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact ⟨X ^ (a : ℕ), by ring⟩
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul r y _ hy =>
      change Ideal.Quotient.factorₐ R (span_le_span k) (r • y) = 0
      rw [map_smul]
      change r • foldMap k y = 0
      rw [hy, smul_zero]

end PolynomialKernel

/-! ## The cyclotomic quotient: powers below the fold are independent -/

section Cyclotomic

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The minimal polynomial of a primitive `2^m`-th root over `ℚ` has degree `2^{m−1}`. -/
theorem natDegree_minpoly_two_pow {m : ℕ} (hm : 1 ≤ m) {μ : K} (hμ : IsPrimitiveRoot μ (2 ^ m)) :
    (minpoly ℚ μ).natDegree = 2 ^ (m - 1) := by
  rw [← cyclotomic_eq_minpoly_rat hμ (by positivity), natDegree_cyclotomic,
    Nat.totient_prime_pow Nat.prime_two hm]
  simp

/-- **The fold is faithful.** `1, μ, …, μ^{2^{m−1}−1}` are independent over `ℚ` for a primitive
`2^m`-th root `μ`: a rational combination of them vanishes only when every coefficient does. This
is `ℚ[X]/(X^{2^{m−1}} + 1) → K` being injective, the cyclotomic polynomial being irreducible. -/
theorem eq_zero_of_sum_range_eq_zero {m : ℕ} (hm : 1 ≤ m) {μ : K}
    (hμ : IsPrimitiveRoot μ (2 ^ m)) (g : ℕ → ℚ)
    (hg : ∑ j ∈ Finset.range (2 ^ (m - 1)), (g j : K) * μ ^ j = 0) :
    ∀ j < 2 ^ (m - 1), g j = 0 := by
  have hli := linearIndependent_pow (K := ℚ) μ
  rw [natDegree_minpoly_two_pow hm hμ] at hli
  intro j hj
  refine Fintype.linearIndependent_iff.mp hli (fun i => g i) ?_ ⟨j, hj⟩
  rw [← hg, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Rat.smul_def]

omit [CharZero K] in
/-- `μ^{2^{m−1}} = −1` for a primitive `2^m`-th root, in any field: `μ^{2^{m−1}}` is a primitive
square root of one. -/
theorem pow_two_pow_pred_eq_neg_one {m : ℕ} (hm : 1 ≤ m) {μ : K}
    (hμ : IsPrimitiveRoot μ (2 ^ m)) : μ ^ (2 ^ (m - 1)) = -1 := by
  have h2 : 2 ^ m / 2 ^ (m - 1) = 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have hprim := hμ.pow_of_dvd (by positivity) (pow_dvd_pow 2 (Nat.sub_le m 1))
  rw [h2] at hprim
  exact hprim.eq_neg_one_of_two_right

/-- `X^{2^{m−1}} + 1` is the `2^m`-th cyclotomic polynomial over `ℤ`, the minimal polynomial of a
primitive `2^m`-th root. -/
theorem minpoly_int_two_pow {m : ℕ} (hm : 1 ≤ m) {μ : K} (hμ : IsPrimitiveRoot μ (2 ^ m)) :
    minpoly ℤ μ = X ^ (2 ^ (m - 1)) + 1 := by
  rw [← cyclotomic_eq_minpoly hμ (by positivity)]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two, Nat.add_sub_cancel]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one]
  ring

/-- **The roots of unity of `ℚ(μ)` of order a power of two.** For a primitive `2^m`-th root `μ`,
`1 ≤ m`, a root of unity of order a power of two that lies in `ℚ(μ)` is a `2^m`-th root: a
primitive `2^j`-th root with `j > m` has a minimal polynomial over `ℚ` of degree `2^{j−1}`
(`natDegree_minpoly_two_pow`, the degree `minpoly_int_two_pow` gives), which exceeds the degree
`2^{m−1}` of `ℚ(μ)`. -/
theorem rootOfUnity_mem_two_pow {m k : ℕ} (hm : 1 ≤ m) {μ ζ : K}
    (hμ : IsPrimitiveRoot μ (2 ^ m)) (hζ : ζ ^ 2 ^ k = 1)
    (hmem : ζ ∈ IntermediateField.adjoin ℚ {μ}) : ζ ^ 2 ^ m = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hζ)
  by_cases hjm : j ≤ m
  · exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow 2 hjm)
  · exfalso
    have hprim : IsPrimitiveRoot ζ (2 ^ j) := hj ▸ IsPrimitiveRoot.orderOf ζ
    have hμint : IsIntegral ℚ μ := (hμ.isIntegral (by positivity)).tower_top
    haveI := IntermediateField.adjoin.finiteDimensional hμint
    have hle := minpoly.natDegree_le (K := ℚ) (⟨ζ, hmem⟩ : IntermediateField.adjoin ℚ {μ})
    have heq := IntermediateField.minpoly_eq (K := ℚ) (⟨ζ, hmem⟩ : IntermediateField.adjoin ℚ {μ})
    have hdeg : (minpoly ℚ ζ).natDegree ≤ (minpoly ℚ μ).natDegree := by
      rw [← IntermediateField.adjoin.finrank hμint]
      convert hle using 2
      exact heq.symm
    rw [natDegree_minpoly_two_pow (by omega) hprim, natDegree_minpoly_two_pow hm hμ] at hdeg
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hdeg
    omega

end Cyclotomic

/-! ## The group ring of `ZMod (2^m)` and its image in the cyclotomic field

An element of the group ring `ℤ[C_{2^m}]` is a function `f : ZMod (2^m) → ℤ` (the count of each
phase); its image under a primitive root `μ` is `Σ_a f(a)·μ^{a.val}`. -/

section GroupRing

variable {K : Type*} [Field K] [CharZero K]

/-- The image of a group-ring element under the root `μ`. -/
noncomputable def evalRoot (m : ℕ) (μ : K) (f : ZMod (2 ^ m) → ℤ) : K :=
  ∑ a : ZMod (2 ^ m), (f a : K) * μ ^ a.val

/-- A sum over `ZMod N` is the sum over `range N` of the residues. -/
theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (N : ℕ) [NeZero N]
    (F : ZMod N → M) : ∑ a : ZMod N, F a = ∑ j ∈ Finset.range N, F (j : ZMod N) := by
  refine Finset.sum_nbij' (fun a => a.val) (fun j => (j : ZMod N)) (fun a _ => ?_) (fun _ _ => ?_)
    (fun a _ => ?_) (fun j hj => ?_) (fun a _ => ?_)
  · exact Finset.mem_range.mpr (ZMod.val_lt a)
  · exact Finset.mem_univ _
  · exact ZMod.natCast_zmod_val a
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · rw [ZMod.natCast_zmod_val]

/-- The top bit `2^{m−1}` added to itself is zero in `ZMod (2^m)`. -/
theorem two_pow_pred_add_self {m : ℕ} (hm : 1 ≤ m) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) + (2 : ZMod (2 ^ m)) ^ (m - 1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [Nat.add_sub_cancel, ← two_mul, ← pow_succ']
  exact_mod_cast ZMod.natCast_self (2 ^ (k + 1))

omit [CharZero K] in
/-- The image folded onto the first half of the residues: the antipodal differences
`f(j) − f(j + 2^{m−1})` against `μ^j`, `j < 2^{m−1}`. -/
theorem evalRoot_eq_sum_fold {m : ℕ} (hm : 1 ≤ m) {μ : K} (hμ : IsPrimitiveRoot μ (2 ^ m))
    (f : ZMod (2 ^ m) → ℤ) :
    evalRoot m μ f
      = ∑ j ∈ Finset.range (2 ^ (m - 1)),
          (((f (j : ZMod (2 ^ m)) - f ((j : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) ^ (m - 1)) : ℤ)
            : K) * μ ^ j) := by
  have hN : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  unfold evalRoot
  rw [sum_zmod_eq_sum_range (2 ^ m) (fun a => (f a : K) * μ ^ a.val)]
  have hval : ∀ j ∈ Finset.range (2 ^ m),
      (f (j : ZMod (2 ^ m)) : K) * μ ^ (j : ZMod (2 ^ m)).val
        = (f (j : ZMod (2 ^ m)) : K) * μ ^ j :=
    fun j hj => by rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]
  rw [Finset.sum_congr rfl hval]
  rw [show Finset.range (2 ^ m) = Finset.range (2 ^ (m - 1) + 2 ^ (m - 1)) from by rw [← hN],
    Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_add, pow_two_pow_pred_eq_neg_one hm hμ]
  push_cast
  ring_nf

/-- **The kernel of `ℤ[C_{2^m}] → K`, pointwise.** A group-ring element has image zero under a
primitive `2^m`-th root exactly when it takes the same value at every pair of antipodal residues
`a, a + 2^{m−1}`: it is a sum of antipodal pairs. -/
theorem evalRoot_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) {μ : K} (hμ : IsPrimitiveRoot μ (2 ^ m))
    (f : ZMod (2 ^ m) → ℤ) :
    evalRoot m μ f = 0 ↔ ∀ a : ZMod (2 ^ m), f (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = f a := by
  rw [evalRoot_eq_sum_fold hm hμ]
  constructor
  · intro h
    have hj := eq_zero_of_sum_range_eq_zero hm hμ
      (fun j => ((f (j : ZMod (2 ^ m)) - f ((j : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) ^ (m - 1)) : ℤ)
        : ℚ))
      (by simpa only [Rat.cast_intCast] using h)
    have hlow : ∀ j : ℕ, j < 2 ^ (m - 1) →
        f ((j : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) ^ (m - 1)) = f (j : ZMod (2 ^ m)) := by
      intro j hjk
      have h0 := hj j hjk
      rw [Int.cast_eq_zero, sub_eq_zero] at h0
      exact h0.symm
    have hN : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    intro a
    rcases lt_or_ge a.val (2 ^ (m - 1)) with ha | ha
    · have h1 := hlow a.val ha
      rwa [ZMod.natCast_zmod_val] at h1
    · have hlt : a.val - 2 ^ (m - 1) < 2 ^ (m - 1) := by
        have := ZMod.val_lt a
        omega
      have ha' : a = ((a.val - 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) + (2 : ZMod (2 ^ m)) ^ (m - 1) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val a]
        rw [show a.val = (a.val - 2 ^ (m - 1)) + 2 ^ (m - 1) by omega]
        push_cast
        rw [Nat.add_sub_cancel]
      rw [ha', add_assoc, two_pow_pred_add_self hm, add_zero]
      exact (hlow _ hlt).symm
  · intro h
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [h, sub_self, Int.cast_zero, zero_mul]

end GroupRing

/-! ## The amplitude reads the phase multiset through the cyclotomic image -/

section Amplitude

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough

variable {n : ℕ}

/-- The number of bound words at which the exponent takes the phase `a`, at the free word `w`. -/
noncomputable def phaseCount {m h : ℕ} (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2)
    (a : ZMod (2 ^ m)) : ℕ :=
  (Finset.univ.filter fun y : Fin h → ZMod 2 => Q.eval (Fin.append w y) = a).card

/-- The character sum over the bound register is the image of the phase counts. -/
theorem sum_charOf_eq_evalRoot {m h : ℕ} (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2) :
    ∑ y : Fin h → ZMod 2, charOf m (Q.eval (Fin.append w y))
      = evalRoot m (zeta m) (fun a => (phaseCount Q w a : ℤ)) := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0 : ℕ) < 2 ^ m).ne'⟩
  unfold evalRoot phaseCount
  rw [← Finset.sum_fiberwise Finset.univ (fun y : Fin h → ZMod 2 => Q.eval (Fin.append w y))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2]), Finset.sum_const,
    nsmul_eq_mul, charOf_eq_zeta_pow]
  push_cast
  ring

/-- `evalRoot` is additive in the group-ring element. -/
theorem evalRoot_sub {K : Type*} [Field K] (m : ℕ) (μ : K) (f g : ZMod (2 ^ m) → ℤ) :
    evalRoot m μ (f - g) = evalRoot m μ f - evalRoot m μ g := by
  unfold evalRoot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  push_cast [Pi.sub_apply]
  ring

/-- **The amplitude and the kernel.** At one free word, two exponents at the same precision
`1 ≤ m`, the same height and the same nonzero scale give the same amplitude exactly when the
difference of their phase counts is a sum of antipodal pairs. -/
theorem ampCore_eq_iff_antipodal {m h : ℕ} (hm : 1 ≤ m) (Q Q' : DiagPhase (n + h) m) {c : ℂ}
    (hc : c ≠ 0) (w : Fin n → ZMod 2) :
    ampCore m h Q' c w = ampCore m h Q c w
      ↔ ∀ a : ZMod (2 ^ m),
          (phaseCount Q' w (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) : ℤ)
              - phaseCount Q w (a + (2 : ZMod (2 ^ m)) ^ (m - 1))
            = (phaseCount Q' w a : ℤ) - phaseCount Q w a := by
  have hscale : c / (Real.sqrt 2 : ℂ) ^ h ≠ 0 := by
    refine div_ne_zero hc (pow_ne_zero _ ?_)
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf, mul_right_inj' hscale,
    sum_charOf_eq_evalRoot, sum_charOf_eq_evalRoot, ← sub_eq_zero, ← evalRoot_sub,
    evalRoot_eq_zero_iff hm (isPrimitiveRoot_zeta m)]
  rfl

end Amplitude

/-! ## The row decomposition -/

section RowDecomposition

/-- **The row decomposition.** Two rows `f`, `g : ZMod (2^m) → ℕ` of one length (`∑ f = ∑ g`) whose
difference is antipodal-symmetric (agrees at `a` and `a + 2^{m−1}`, the condition
`ampCore_eq_iff_antipodal` reduces amplitude equality to) split as `f = C + N` and `g = C + P` for a
common row `C`: `N` and `P` are each themselves antipodal-symmetric (so each is a sum of antipodal
pairs), and since `∑ N = ∑ P`, the same number of them. -/
theorem row_decomposition {m : ℕ} (f g : ZMod (2 ^ m) → ℕ)
    (hsum : ∑ a, f a = ∑ a, g a)
    (hker : ∀ a : ZMod (2 ^ m),
        (f (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) : ℤ) - g (a + (2 : ZMod (2 ^ m)) ^ (m - 1))
          = (f a : ℤ) - g a) :
    ∃ C N P : ZMod (2 ^ m) → ℕ, f = C + N ∧ g = C + P ∧
      (∀ a, N (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = N a) ∧
      (∀ a, P (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = P a) ∧
      ∑ a, N a = ∑ a, P a := by
  refine ⟨fun a => min (f a) (g a), fun a => f a - min (f a) (g a),
    fun a => g a - min (f a) (g a), ?_, ?_, ?_, ?_, ?_⟩
  · funext a
    change f a = min (f a) (g a) + (f a - min (f a) (g a))
    omega
  · funext a
    change g a = min (f a) (g a) + (g a - min (f a) (g a))
    omega
  · intro a
    have hcast : ∀ b : ZMod (2 ^ m), ((f b - min (f b) (g b) : ℕ) : ℤ) = max ((f b : ℤ) - g b) 0 :=
      fun b => by omega
    have h1 := hcast (a + (2 : ZMod (2 ^ m)) ^ (m - 1))
    have h2 := hcast a
    rw [hker a] at h1
    have : ((f (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) - min (f (a + (2 : ZMod (2 ^ m)) ^ (m - 1)))
        (g (a + (2 : ZMod (2 ^ m)) ^ (m - 1))) : ℕ) : ℤ)
        = ((f a - min (f a) (g a) : ℕ) : ℤ) := by rw [h1, h2]
    exact_mod_cast this
  · intro a
    have hcast : ∀ b : ZMod (2 ^ m), ((g b - min (f b) (g b) : ℕ) : ℤ) = max ((g b : ℤ) - f b) 0 :=
      fun b => by omega
    have h1 := hcast (a + (2 : ZMod (2 ^ m)) ^ (m - 1))
    have h2 := hcast a
    rw [show (g (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) : ℤ) - f (a + (2 : ZMod (2 ^ m)) ^ (m - 1))
        = (g a : ℤ) - f a from by have := hker a; omega] at h1
    have : ((g (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) - min (f (a + (2 : ZMod (2 ^ m)) ^ (m - 1)))
        (g (a + (2 : ZMod (2 ^ m)) ^ (m - 1))) : ℕ) : ℤ)
        = ((g a - min (f a) (g a) : ℕ) : ℤ) := by rw [h1, h2]
    exact_mod_cast this
  · have hf : ∑ a, f a = ∑ a, min (f a) (g a) + ∑ a, (f a - min (f a) (g a)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by omega)
    have hg : ∑ a, g a = ∑ a, min (f a) (g a) + ∑ a, (g a - min (f a) (g a)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by omega)
    have hcancel := hsum
    rw [hf, hg] at hcancel
    exact Nat.add_left_cancel hcancel

end RowDecomposition

end FTQCLib.Frame.Walkthrough.AntipodalKernel

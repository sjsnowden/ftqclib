/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.EliminationOrder
import FTQCLib.Carrier.ResidualBit
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The cyclotomic kernel and the rule the frame lacks

**Question.** A carrier state's amplitude at a free word `w` is `(c/√2^h)·Σ_y ζ^{Q(w,y)}`,
`ζ = zeta m`. The gauge rewrites R1–R7 keep the multiset of phases at each word (`boundTerms`,
`FTQCLib/Carrier/EliminationOrder.lean`), an element of the group ring `ℤ[C_{2^m}]`, and the
amplitude is its image in `ℤ[ζ]`. The kernel of `ℤ[C_{2^m}] → ℤ[ζ]` should be spanned by the
antipodal pairs `[a] + [a + 2^{m−1}]`. Does that kernel name the rule the frame lacks, the one that
relates T04's two stuck outcomes (`elimination_order_matters`)?

**How the outcome is read.** Four findings, each machine-checked here.

1. **The kernel.** Over any commutative ring and at `0 < k`, the kernel of
   `R[X]/(X^{2k} − 1) → R[X]/(X^k + 1)` is the `R`-span of the `k` antipodal pairs
   (`foldMap_eq_zero_iff`). At `k = 2^{m−1}` the second ring is `ℤ[ζ]`, since
   `X^{2^{m−1}} + 1` is the minimal polynomial of a primitive `2^m`-th root in any field of
   characteristic zero (`minpoly_int_two_pow`); composed, a polynomial vanishes at the root exactly
   when its class is an integer combination of antipodal pairs (`aeval_eq_zero_iff_mem_span`).
   Pointwise on `ZMod (2^m) → ℤ`: the image is zero exactly when the element takes one value on each
   antipodal pair of residues (`evalRoot_eq_zero_iff`). On carrier records: at one free word, two
   exponents with the same precision, height and nonzero scale give the same amplitude exactly when
   their phase counts differ by antipodal pairs (`ampCore_eq_iff_antipodal`).
2. **R8, antipodal rephasing.** Paths paired antipodally sum to zero, so the exponent may be changed
   on them as long as it stays paired (`AntipodalStep`, certified by `stateEq_of_antipodalStep`).
   The pairing is any permutation, uniform over the free words; the certificate holds per word
   (`ampCore_eq_of_antipodalOn`). R8 relates T04's two outcomes in one step, where no chain of R1–R7
   does (`T04.antipodalStep_recB_recA`, `T04.t04_outcomes`).
3. **R8 does not reach the floor.** Along any forward derivation (gauge rewrites either way, R8,
   collapse and rotate as written) the modulus of the scale never goes down
   (`normSq_c_le_of_forward`), and a height-zero record's amplitude has the scale's modulus
   wherever it is nonzero. T04's input and both outcomes have `|c| ≥ 1` and amplitude `1/√2`, so
   no forward derivation takes any of them to height zero (`not_forward_floor`,
   `T04.t04_outcomes`). A height-zero state does exist (`T04.floor`), and both outcomes reach it
   by a derivation that raises the height once: one inverse collapse, one R5, one R8, three
   rotations (`T04.derivable_outcomeA_floor`).
4. **R9, antipodal halving.** The height-changing form of the same cancellation deletes the paired
   paths: if they are half of the bound words and the rest is the image of an embedding of the
   shorter words, the record drops a bound bit and its scale is divided by `√2`
   (`HalvingStep`, `stateEq_of_halvingStep`, `normSq_c_of_halvingStep`). With R9, both outcomes and
   the input go forward to one record at height zero (`T04.t04_halving`,
   `T04.forward9_input_floorHalf`).
5. **The scale is a second gap.** Every rule, R9 included, multiplies `|c|²` by a power of two
   (`scaleClass_of_derivable9`). A record at height two with phases `0, 0, 0, 1` and scale `1` has
   the amplitude `(3 + i)/2` of a floor record with scale `(3 + i)/2`, and no derivation relates
   them (`not_derivable9_corner`): with arbitrary complex scales, R1–R9 and the eliminations are not
   complete in T07's sense.

The load-bearing hypotheses: `0 < k` in the fold, `1 ≤ m` in the pointwise kernel
(`evalRoot_zero_ne_zero`), and the pairing of the output exponent in R8
(`antipodalOn_signBit_and_not_stateEq`).

## Main definitions

* `foldMap`, `antipodalPair` — the fold of the cyclic group ring, and the pairs spanning its kernel.
* `evalRoot`, `phaseCount` — a group-ring element's image under a root; a word's phase counts.
* `AntipodalOn`, `AntipodalStep` (R8), `HalvingStep` (R9).
* `ElimStep`, `Step`, `Derivable`, `ForwardStep`, `Forward`, `Forward9`, `Step9`, `Derivable9` —
  eliminations, the extended rules, derivations and forward derivations, without and with R9.

## Main results

* `foldMap_eq_zero_iff`, `aeval_eq_zero_iff_mem_span`, `evalRoot_eq_zero_iff`,
  `ampCore_eq_iff_antipodal` — the kernel, over any ring, over `ℤ[ζ]`, pointwise, on carriers.
* `stateEq_of_antipodalStep`, `stateEq_of_halvingStep`, `stateEq_of_derivable` — soundness.
* `normSq_c_le_of_forward`, `not_forward_floor` — the scale-modulus obstruction.
* `T04.t04_outcomes`, `T04.t04_halving`, `T04.forward9_input_floorHalf` — T04's witness.
* `scaleClass_of_derivable9`, `not_derivable9_corner` — the scale invariant and its witness.

## Implementation notes

* Standalone (`FTQCLib/Explore/README.md`): built with
  `lake build FTQCLib.Explore.CyclotomicKernel`, imported by nothing.
* T04's outcomes are moved to plain exponents (`T04.qA`, `T04.qB`) by R4 before anything else; the
  private evaluation lemmas of `EliminationOrder.lean` are restated where needed.
* Every finite check over bound words is `decide` over at most sixteen words after the exponent is
  evaluated to its bits.
* The team write-up is `explore/cyclotomic/REPORT.html`.
-/

namespace FTQCLib.Explore.CyclotomicKernel

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

end Cyclotomic

/-! ## The group ring of `ZMod (2^m)` and its image in the cyclotomic field

An element of the group ring `ℤ[C_{2^m}]` is a function `f : ZMod (2^m) → ℤ` (the count of each
phase); its image under a primitive root `μ` is `Σ_a f(a)·μ^{a.val}`. -/

section GroupRing

open Polynomial

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

/-- `X^{2^{m−1}} + 1` is the `2^m`-th cyclotomic polynomial over `ℤ`, the minimal polynomial of a
primitive `2^m`-th root. -/
theorem minpoly_int_two_pow {m : ℕ} (hm : 1 ≤ m) {μ : K} (hμ : IsPrimitiveRoot μ (2 ^ m)) :
    minpoly ℤ μ = X ^ (2 ^ (m - 1)) + 1 := by
  rw [← cyclotomic_eq_minpoly hμ (by positivity)]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two, Nat.add_sub_cancel]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, pow_one]
  ring

/-- **The kernel of `ℤ[C_{2^m}] → ℤ[μ]`, as generated.** With `ℤ[C_{2^m}] = ℤ[X]/(X^{2^m} − 1)`
(written `X^{2·2^{m−1}} − 1`), a polynomial vanishes at a primitive `2^m`-th root exactly when its
class is an integer combination of the `2^{m−1}` antipodal pairs `X^a + X^{a+2^{m−1}}`. The fold of
`foldMap_eq_zero_iff` composed with the faithful evaluation `ℤ[X]/(X^{2^{m−1}} + 1) → K`. -/
theorem aeval_eq_zero_iff_mem_span {m : ℕ} (hm : 1 ≤ m) {μ : K} (hμ : IsPrimitiveRoot μ (2 ^ m))
    (p : ℤ[X]) :
    aeval μ p = 0
      ↔ Ideal.Quotient.mk (Ideal.span {(X ^ (2 * 2 ^ (m - 1)) - 1 : ℤ[X])}) p
          ∈ Submodule.span ℤ (Set.range fun a : Fin (2 ^ (m - 1)) =>
              (antipodalPair (2 ^ (m - 1)) a : ℤ[X] ⧸ _)) := by
  refine Iff.trans ?_ (foldMap_eq_zero_iff (R := ℤ) (k := 2 ^ (m - 1)) (by positivity) _)
  rw [foldMap, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    ← minpoly_int_two_pow hm hμ]
  exact minpoly.isIntegrallyClosed_dvd_iff (hμ.isIntegral (by positivity)) p

end GroupRing

/-! ## The amplitude reads the phase multiset through the cyclotomic image

At a free word `w`, the carrier amplitude is `(c/√2^h)·Σ_y charOf(Q(w, y))`. Grouping the bound
words by their phase, the sum is the image of the phase counts (an element of `ℤ[C_{2^m}]`) under
`zeta m`. Two exponents at the same precision, height and nonzero scale therefore give the same
amplitude at `w` exactly when their counts differ by a sum of antipodal pairs. -/

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

/-! ## R8: antipodal rephasing -/

section Rephasing

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough

variable {n : ℕ}

/-- At the free word `w`, the bound words `P` are paired antipodally by `τ`: `τ` maps `P` onto
itself, and moves each phase on `P` by the top bit `2^{m−1}`. -/
def AntipodalOn {m h : ℕ} (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2)
    (P : Finset (Fin h → ZMod 2)) (τ : Equiv.Perm (Fin h → ZMod 2)) : Prop :=
  (∀ y, y ∈ P ↔ τ y ∈ P) ∧
    ∀ y ∈ P, Q.eval (Fin.append w (τ y)) = Q.eval (Fin.append w y) + (2 : ZMod (2 ^ m)) ^ (m - 1)

/-- The character of the top bit is `−1`. -/
theorem charOf_two_pow_pred {m : ℕ} (hm : 1 ≤ m) :
    charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
  have h := charOf_two_pow_mul (m := m) hm 1
  simpa using h

/-- **Antipodal paths cancel.** Paths paired antipodally contribute nothing to the character
sum. The pairing is any permutation of `P`; it need not be an involution. -/
theorem sum_charOf_eq_zero_of_antipodalOn {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h) m}
    {w : Fin n → ZMod 2} {P : Finset (Fin h → ZMod 2)} {τ : Equiv.Perm (Fin h → ZMod 2)}
    (hP : AntipodalOn Q w P τ) :
    ∑ y ∈ P, charOf m (Q.eval (Fin.append w y)) = 0 := by
  have hperm : ∑ y ∈ P, charOf m (Q.eval (Fin.append w (τ y)))
      = ∑ y ∈ P, charOf m (Q.eval (Fin.append w y)) :=
    Finset.sum_equiv τ hP.1 (fun _ _ => rfl)
  have hneg : ∑ y ∈ P, charOf m (Q.eval (Fin.append w (τ y)))
      = -∑ y ∈ P, charOf m (Q.eval (Fin.append w y)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [hP.2 y hy, charOf_add, charOf_two_pow_pred hm]
    ring
  rw [hperm] at hneg
  exact self_eq_neg.mp hneg

/-- **The rephasing certificate, per word.** Two exponents that agree off `P` and are each paired
antipodally on `P` (by possibly different permutations) give the same amplitude at `w`. -/
theorem ampCore_eq_of_antipodalOn {m h : ℕ} (hm : 1 ≤ m) {Q Q' : DiagPhase (n + h) m} (c : ℂ)
    {w : Fin n → ZMod 2} {P : Finset (Fin h → ZMod 2)} {τ τ' : Equiv.Perm (Fin h → ZMod 2)}
    (hoff : ∀ y ∉ P, Q'.eval (Fin.append w y) = Q.eval (Fin.append w y))
    (hQ : AntipodalOn Q w P τ) (hQ' : AntipodalOn Q' w P τ') :
    ampCore m h Q' c w = ampCore m h Q c w := by
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf]
  congr 1
  rw [← Finset.sum_add_sum_compl P, ← Finset.sum_add_sum_compl P (fun y => charOf m _),
    sum_charOf_eq_zero_of_antipodalOn hm hQ, sum_charOf_eq_zero_of_antipodalOn hm hQ']
  congr 1
  exact Finset.sum_congr rfl (fun y hy => by rw [hoff y (Finset.mem_compl.mp hy)])

/-- **R8, antipodal rephasing.** One set `P` of bound words, the same at every free word, on which
both exponents are paired antipodally, and off which they agree on the support. The exponent may be
changed arbitrarily on `P` as long as it stays paired: the paths on `P` sum to zero either way. -/
inductive AntipodalStep : KernelSumState n → KernelSumState n → Prop
  | rephase {m h : ℕ} (hm : 1 ≤ m) (Q Q' : DiagPhase (n + h) m) (c : ℂ)
      (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) (P : Finset (Fin h → ZMod 2))
      (τ τ' : Equiv.Perm (Fin h → ZMod 2))
      (hoff : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y ∉ P,
        Q'.eval (Fin.append w y) = Q.eval (Fin.append w y))
      (hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q w P τ)
      (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q' w P τ') :
      AntipodalStep ⟨m, h, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩

/-- R8 is symmetric. -/
theorem AntipodalStep.symm {S T : KernelSumState n} (hST : AntipodalStep S T) :
    AntipodalStep T S := by
  cases hST with
  | rephase hm Q Q' c L x₀ P τ τ' hoff hQ hQ' =>
    exact .rephase hm Q' Q c L x₀ P τ' τ (fun w hw y hy => (hoff w hw y hy).symm) hQ' hQ

/-- **R8 is sound.** -/
theorem stateEq_of_antipodalStep {S T : KernelSumState n} (hST : AntipodalStep S T) :
    StateEq S T := by
  cases hST with
  | @rephase m h hm Q Q' c L x₀ P τ τ' hoff hQ hQ' =>
    funext w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · rw [amp_pos (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw,
        amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
      exact ampCore_eq_of_antipodalOn hm c (hoff w hw) (hQ w hw) (hQ' w hw)
    · rw [amp_neg (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw,
        amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

end Rephasing

/-! ## Derivations, and the scale modulus along forward derivations -/

section Derivations

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough

variable {n : ℕ}

/-- An elimination of the last bound bit, collapse or rotate, with the hypotheses of its
certificate. An elimination at another bit is this after an instance of R5 (`boundToLast`). -/
inductive ElimStep : KernelSumState n → KernelSumState n → Prop
  | collapse {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + h + 1) m) (c : ℂ)
      {L : Submodule (ZMod 2) (Pauli n)} {x₀ σ : Fin n → ZMod 2} {ε : ZMod 2}
      (hsign : SignAffine Q L x₀ σ ε) {L'' : Submodule (ZMod 2) (Pauli n)} {x₀'' : Fin n → ZMod 2}
      (hsupp : ∀ w : Fin n → ZMod 2,
        (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X) ∧ ε + dotF2 σ w = 0) :
      ElimStep ⟨m, h + 1, Q, c, L, x₀⟩ (elimCollapse Q c L'' x₀'')
  | rotate {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + h + 1) m) (c : ℂ)
      {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2} {a : ZMod (2 ^ m)}
      {Λ : DiagPhase (n + h) m} (hrot : RotateData Q L x₀ a Λ)
      {L'' : Submodule (ZMod 2) (Pauli n)} {x₀'' : Fin n → ZMod 2}
      (hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X)) :
      ElimStep ⟨m, h + 1, Q, c, L, x₀⟩ (elimRotate Q a Λ c L'' x₀'')

/-- One rule of the extended system: a gauge rewrite R1–R7, R8, or an elimination. -/
inductive Step : KernelSumState n → KernelSumState n → Prop
  | gauge {S T : KernelSumState n} : GaugeStep S T → Step S T
  | antipodal {S T : KernelSumState n} : AntipodalStep S T → Step S T
  | elim {S T : KernelSumState n} : ElimStep S T → Step S T

/-- A derivation: the rules of `Step`, each used in either direction (the equational closure of
T07). -/
def Derivable : KernelSumState n → KernelSumState n → Prop :=
  Relation.EqvGen Step

/-- A forward step: a gauge rewrite in either direction, R8, or an elimination read as it is
written (the height goes down). -/
def ForwardStep (S T : KernelSumState n) : Prop :=
  GaugeStep S T ∨ GaugeStep T S ∨ AntipodalStep S T ∨ ElimStep S T

/-- A forward derivation: forward steps in sequence. Every elimination strategy is one. -/
def Forward : KernelSumState n → KernelSumState n → Prop :=
  Relation.ReflTransGen ForwardStep

/-- An elimination keeps the denotation. -/
theorem stateEq_of_elimStep {S T : KernelSumState n} (hST : ElimStep S T) : StateEq S T := by
  cases hST with
  | collapse hm Q c hsign hsupp => exact (amp_elimCollapse hm c hsign hsupp).symm
  | rotate hm Q c hrot hsupp => exact (amp_elimRotate hm c hrot hsupp).symm

/-- One rule keeps the denotation. -/
theorem stateEq_of_step {S T : KernelSumState n} (hST : Step S T) : StateEq S T := by
  cases hST with
  | gauge h => exact stateEq_of_gaugeStep h
  | antipodal h => exact stateEq_of_antipodalStep h
  | elim h => exact stateEq_of_elimStep h

/-- **Soundness of derivations.** -/
theorem stateEq_of_derivable {S T : KernelSumState n} (hST : Derivable S T) : StateEq S T := by
  unfold Derivable at hST
  induction hST with
  | rel _ _ h => exact stateEq_of_step h
  | refl _ => exact StateEq.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A forward derivation is a derivation. -/
theorem derivable_of_forward {S T : KernelSumState n} (hST : Forward S T) : Derivable S T := by
  unfold Forward at hST
  induction hST with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih =>
    refine Relation.EqvGen.trans _ _ _ ih ?_
    rcases hstep with h | h | h | h
    · exact Relation.EqvGen.rel _ _ (Step.gauge h)
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Step.gauge h))
    · exact Relation.EqvGen.rel _ _ (Step.antipodal h)
    · exact Relation.EqvGen.rel _ _ (Step.elim h)

/-- A gauge rewrite keeps the modulus of the scale. -/
theorem normSq_c_of_gaugeStep {S T : KernelSumState n} (hST : GaugeStep S T) :
    Complex.normSq S.c = Complex.normSq T.c := by
  cases hST with
  | addC Q a c L x₀ => simp only [Complex.normSq_mul, normSq_charOf, mul_one]
  | offsetAddMem Q c L x₀ hv => rfl
  | congrXProj Q c L L' x₀ hsh => rfl
  | congrSupport Q Q' c L x₀ hQ => rfl
  | renameBound Q Q' c L x₀ σ hQ => rfl
  | hRaiseIndep i u u' S horth hui hrep hui' hrep' hm => rfl
  | liftTo k hmk Q c L x₀ => rfl

/-- R8 keeps the scale. -/
theorem c_of_antipodalStep {S T : KernelSumState n} (hST : AntipodalStep S T) : S.c = T.c := by
  cases hST
  rfl

/-- `|√2|² = 2`. -/
theorem normSq_sqrt_two : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]

/-- A rotate constant's branch sum has modulus `√2`: `charOf a` is `±i` when `2a = 2^{m−1}`. -/
theorem normSq_one_add_charOf_rotate {m : ℕ} (hm : 1 ≤ m) {a : ZMod (2 ^ m)}
    (ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1)) : Complex.normSq (1 + charOf m a) = 2 := by
  have hsq : charOf m a * charOf m a = -1 := by
    rw [← charOf_add, ← two_mul, ha, charOf_two_pow_pred hm]
  have hfac : (charOf m a - Complex.I) * (charOf m a + Complex.I) = 0 := by
    linear_combination hsq - Complex.I_sq
  rcases mul_eq_zero.mp hfac with h | h
  · rw [sub_eq_zero.mp h, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im]
    norm_num
  · rw [eq_neg_of_add_eq_zero_left h, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im]
    norm_num

/-- **Forward eliminations never lower the modulus of the scale.** Collapse multiplies it by
`√2`, rotate keeps it. -/
theorem normSq_c_le_of_elimStep {S T : KernelSumState n} (hST : ElimStep S T) :
    Complex.normSq S.c ≤ Complex.normSq T.c := by
  cases hST with
  | collapse hm Q c hsign hsupp =>
    change Complex.normSq c ≤ Complex.normSq ((Real.sqrt 2 : ℂ) * c)
    rw [Complex.normSq_mul, normSq_sqrt_two]
    linarith [Complex.normSq_nonneg c]
  | rotate hm Q c hrot hsupp =>
    change Complex.normSq c ≤ Complex.normSq (c * (1 + charOf _ _) / (Real.sqrt 2 : ℂ))
    rw [Complex.normSq_div, Complex.normSq_mul, normSq_one_add_charOf_rotate hm hrot.1,
      normSq_sqrt_two]
    linarith [Complex.normSq_nonneg c]

/-- **The scale modulus is monotone along forward derivations.** -/
theorem normSq_c_le_of_forward {S T : KernelSumState n} (hST : Forward S T) :
    Complex.normSq S.c ≤ Complex.normSq T.c := by
  unfold Forward at hST
  induction hST with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    refine ih.trans ?_
    rcases hstep with h | h | h | h
    · exact (normSq_c_of_gaugeStep h).le
    · exact (normSq_c_of_gaugeStep h).ge
    · exact (congrArg Complex.normSq (c_of_antipodalStep h)).le
    · exact normSq_c_le_of_elimStep h

/-- With no free bits the one word is always on the support. -/
theorem mem_support_zero (S : KernelSumState 0) : ∃ p ∈ S.L, (0 : Fin 0 → ZMod 2) = S.x₀ + p.X :=
  ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩

/-- **A floor record's amplitude has modulus `|c|` wherever it is nonzero.** -/
theorem normSq_amp_of_h_eq_zero (T : KernelSumState n) (hT : T.h = 0) {w : Fin n → ZMod 2}
    (hw : amp T w ≠ 0) : Complex.normSq (amp T w) = Complex.normSq T.c := by
  obtain ⟨m, h, Q, c, L, x₀⟩ := T
  change h = 0 at hT
  subst hT
  have hsupp : ∃ p ∈ L, w = x₀ + p.X := by
    by_contra hns
    exact hw (amp_neg hns)
  rw [amp_pos hsupp]
  change Complex.normSq (ampCore m 0 Q c w) = Complex.normSq c
  rw [ampCore_eq_sum_charOf, Fintype.sum_unique, pow_zero, div_one, Complex.normSq_mul,
    normSq_charOf, mul_one]

/-- **No forward derivation reaches the floor below the scale.** If the amplitude has, at some word
where it is nonzero, modulus below the scale's, no forward derivation reaches height zero: the
scale's modulus never goes down forward, and a floor record's amplitude has the scale's modulus
wherever it is nonzero. -/
theorem not_forward_floor {S : KernelSumState n} {w : Fin n → ZMod 2} (hw : amp S w ≠ 0)
    (hlt : Complex.normSq (amp S w) < Complex.normSq S.c) :
    ¬ ∃ T, Forward S T ∧ T.h = 0 := by
  rintro ⟨T, hST, hT⟩
  have hamp : amp T = amp S := (stateEq_of_derivable (derivable_of_forward hST)).symm
  have h1 := normSq_amp_of_h_eq_zero T hT (w := w) (by rw [hamp]; exact hw)
  rw [hamp] at h1
  have h2 := normSq_c_le_of_forward hST
  linarith

/-! ## R9: antipodal halving

R8 never changes the height or the scale. The height-changing form of the same cancellation deletes
the paths of `P` outright: when `P` is paired antipodally and its complement is the image of an
embedding of the words one bit shorter, the record loses a bound bit and its scale is divided by
`√2` (the prefactor `1/√2^h` loses one factor, the sum loses only terms that cancel). -/

/-- **The halving certificate, per word.** -/
theorem ampCore_halve {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + (h + 1)) m}
    {Q' : DiagPhase (n + h) m} (c : ℂ) {w : Fin n → ZMod 2}
    (e : (Fin h → ZMod 2) ↪ (Fin (h + 1) → ZMod 2)) {P : Finset (Fin (h + 1) → ZMod 2)}
    {τ : Equiv.Perm (Fin (h + 1) → ZMod 2)}
    (hP : ∀ y', y' ∈ P ↔ ∀ y, e y ≠ y')
    (hQ' : ∀ y, Q'.eval (Fin.append w y) = Q.eval (Fin.append w (e y)))
    (hpair : AntipodalOn Q w P τ) :
    ampCore m h Q' (c / (Real.sqrt 2 : ℂ)) w = ampCore m (h + 1) Q c w := by
  have hcompl : Pᶜ = Finset.univ.map e := by
    ext y'
    rw [Finset.mem_compl, hP, Finset.mem_map]
    simp only [Finset.mem_univ, true_and, not_forall, not_not]
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf, ← Finset.sum_add_sum_compl P,
    sum_charOf_eq_zero_of_antipodalOn hm hpair, zero_add, hcompl, Finset.sum_map]
  simp only [hQ']
  rw [pow_succ, div_div, mul_comm ((Real.sqrt 2 : ℂ) ^ h)]

/-- **R9, antipodal halving.** One embedding `e` of the shorter bound words and one pairing `τ`
of the rest `P`, the same at every free word; the halved exponent reads `Q` through `e` on the
support. -/
inductive HalvingStep : KernelSumState n → KernelSumState n → Prop
  | halve {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + (h + 1)) m) (Q' : DiagPhase (n + h) m)
      (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
      (e : (Fin h → ZMod 2) ↪ (Fin (h + 1) → ZMod 2)) (P : Finset (Fin (h + 1) → ZMod 2))
      (τ : Equiv.Perm (Fin (h + 1) → ZMod 2)) (hP : ∀ y', y' ∈ P ↔ ∀ y, e y ≠ y')
      (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y,
        Q'.eval (Fin.append w y) = Q.eval (Fin.append w (e y)))
      (hpair : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q w P τ) :
      HalvingStep ⟨m, h + 1, Q, c, L, x₀⟩ ⟨m, h, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩

/-- **R9 is sound.** -/
theorem stateEq_of_halvingStep {S T : KernelSumState n} (hST : HalvingStep S T) :
    StateEq S T := by
  cases hST with
  | @halve m h hm Q Q' c L x₀ e P τ hP hQ' hpair =>
    funext w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · rw [amp_pos (S := (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_pos (S := (⟨m, h, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n)) hw]
      exact (ampCore_halve hm c e hP (hQ' w hw) (hpair w hw)).symm
    · rw [amp_neg (S := (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_neg (S := (⟨m, h, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n)) hw]

/-- R9 lowers the modulus of the scale by `√2`: it is the move the forward obstruction says is
missing. -/
theorem normSq_c_of_halvingStep {S T : KernelSumState n} (hST : HalvingStep S T) :
    Complex.normSq T.c = Complex.normSq S.c / 2 := by
  cases hST
  change Complex.normSq (_ / (Real.sqrt 2 : ℂ)) = _
  rw [Complex.normSq_div, normSq_sqrt_two]

/-- A forward step with R9 added. -/
def ForwardStep9 (S T : KernelSumState n) : Prop :=
  ForwardStep S T ∨ HalvingStep S T

/-- A forward derivation with R9 added. -/
def Forward9 : KernelSumState n → KernelSumState n → Prop :=
  Relation.ReflTransGen ForwardStep9

/-- Forward derivations with R9 keep the denotation. -/
theorem stateEq_of_forward9 {S T : KernelSumState n} (hST : Forward9 S T) : StateEq S T := by
  unfold Forward9 at hST
  induction hST with
  | refl => exact StateEq.refl _
  | tail _ hstep ih =>
    refine ih.trans ?_
    rcases hstep with h | h
    · exact stateEq_of_derivable (derivable_of_forward (Relation.ReflTransGen.single h))
    · exact stateEq_of_halvingStep h

end Derivations

/-! ## T04's two stuck outcomes -/

namespace T04

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Frame.Walkthrough
open FTQCLib.Frame.Walkthrough.EliminationOrder
open MvPolynomial (C X)

/-- `boundToLast` evaluates through the transposition (restated: the original is private). -/
theorem eval_boundToLast {n m h : ℕ} (j : Fin (h + 1)) (Q : DiagPhase (n + (h + 1)) m)
    (v : Fin (n + h + 1) → ZMod 2) :
    DiagPhase.eval (boundToLast j Q) v
      = DiagPhase.eval Q (v ∘ Equiv.swap (Fin.natAdd n j) (Fin.last (n + h))) := by
  unfold boundToLast DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  rfl

/-- `DiagPhase.eval` is subtractive. -/
theorem eval_sub' {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    DiagPhase.eval (A - B) v = DiagPhase.eval A v - DiagPhase.eval B v := by
  simp [DiagPhase.eval]

/-- `DiagPhase.eval` of `0`. -/
theorem eval_zero' {N m : ℕ} (v : Fin N → ZMod 2) : DiagPhase.eval (0 : DiagPhase N m) v = 0 := by
  simp [DiagPhase.eval]

/-- `DiagPhase.eval` of `1`. -/
theorem eval_one' {N m : ℕ} (v : Fin N → ZMod 2) : DiagPhase.eval (1 : DiagPhase N m) v = 1 := by
  simp [DiagPhase.eval]

/-- Outcome A's exponent in plain form: `3·y₁ + 3·y₀·y₁`. -/
noncomputable def qA : DiagPhase (0 + 2) 2 := C 3 * X 1 + C 3 * X 0 * X 1

/-- Outcome B's exponent in plain form: `3 + y₀ + y₀·y₁`. -/
noncomputable def qB : DiagPhase (0 + 2) 2 := C 3 + X 0 + X 0 * X 1

/-- The outcomes' common scale `(1 + i)/√2`, written as `elimRotate` writes it. -/
noncomputable def cOut : ℂ := 1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)

/-- A word of two bits is `![a, b]`. -/
theorem word_two (y : Fin 2 → ZMod 2) : y = ![y 0, y 1] := by
  funext i
  fin_cases i <;> rfl

/-- A word of three bits is `![a, b, d]`. -/
theorem word_three (y : Fin 3 → ZMod 2) : y = ![y 0, y 1, y 2] := by
  funext i
  fin_cases i <;> rfl

/-- The one-word support of a record with no free bits, `L = ⊥`, offset `0`. -/
theorem supp_bot (w : Fin 0 → ZMod 2) : ∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 0)), w = 0 + p.X :=
  ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩

/-- Outcome A's exponent agrees with `qA` at every word. -/
theorem eval_outcomeA (y : Fin 2 → ZMod 2) :
    DiagPhase.eval qA (Fin.append (0 : Fin 0 → ZMod 2) y)
      = DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
          + C (-1) * lambdaA : DiagPhase (0 + 2) 2) (Fin.append (0 : Fin 0 → ZMod 2) y) := by
  rw [word_two y]
  generalize y 0 = a
  generalize y 1 = b
  simp only [qA, inputExponent, lambdaA, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
    DiagPhase.eval_X, snocFreeze_eval, eval_boundToLast]
  revert a b
  decide

/-- Outcome B's exponent agrees with `qB` at every word. -/
theorem eval_outcomeB (y : Fin 2 → ZMod 2) :
    DiagPhase.eval qB (Fin.append (0 : Fin 0 → ZMod 2) y)
      = DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 1 inputExponent)
          + C (-1) * lambdaB : DiagPhase (0 + 2) 2) (Fin.append (0 : Fin 0 → ZMod 2) y) := by
  rw [word_two y]
  generalize y 0 = a
  generalize y 1 = b
  simp only [qB, inputExponent, lambdaB, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
    DiagPhase.eval_X, eval_sub', eval_one', snocFreeze_eval, eval_boundToLast]
  revert a b
  decide

/-- Outcome A with its exponent in plain form. -/
noncomputable def recA : KernelSumState 0 := ⟨2, 2, qA, cOut, ⊥, 0⟩

/-- Outcome B with its exponent in plain form. -/
noncomputable def recB : KernelSumState 0 := ⟨2, 2, qB, cOut, ⊥, 0⟩

/-- Outcome A is `recA` by R4. -/
theorem gauge_outcomeA_recA : GaugeStep outcomeA recA :=
  GaugeStep.congrSupport qA _ cOut ⊥ 0 (fun w _ y => by
    obtain rfl : w = 0 := Subsingleton.elim _ _
    exact (eval_outcomeA y).symm)

/-- Outcome B is `recB` by R4. -/
theorem gauge_outcomeB_recB : GaugeStep outcomeB recB :=
  GaugeStep.congrSupport qB _ cOut ⊥ 0 (fun w _ y => by
    obtain rfl : w = 0 := Subsingleton.elim _ _
    exact (eval_outcomeB y).symm)

/-- Outcome A is `recA`, as a step. -/
theorem step_outcomeA_recA : Step outcomeA recA := Step.gauge gauge_outcomeA_recA

/-- Outcome B is `recB`, as a step. -/
theorem step_outcomeB_recB : Step outcomeB recB := Step.gauge gauge_outcomeB_recB

/-- The paths the rephasing moves: the words `00` and `11`. -/
def pairsAB : Finset (Fin 2 → ZMod 2) := {![0, 0], ![1, 1]}

/-- The pairing: add `11`, which swaps `00` and `11`. -/
def flipAB : Equiv.Perm (Fin 2 → ZMod 2) := Equiv.addRight ![1, 1]

/-- `flipAB` keeps `pairsAB`. -/
theorem flipAB_mem (y : Fin 2 → ZMod 2) : y ∈ pairsAB ↔ flipAB y ∈ pairsAB := by
  rw [word_two y]
  generalize y 0 = a
  generalize y 1 = b
  simp only [flipAB, Equiv.coe_addRight]
  revert a b
  decide

/-- On `00, 11`, `qA` takes `0, 2`: an antipodal pair. -/
theorem antipodalOn_qA (w : Fin 0 → ZMod 2) : AntipodalOn qA w pairsAB flipAB := by
  refine ⟨flipAB_mem, fun y hy => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  simp only [pairsAB, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;>
  · simp only [qA, flipAB, Equiv.coe_addRight, DiagPhase.eval_add, DiagPhase.eval_mul,
      DiagPhase.eval_C, DiagPhase.eval_X]
    decide

/-- On `00, 11`, `qB` takes `3, 1`: an antipodal pair. -/
theorem antipodalOn_qB (w : Fin 0 → ZMod 2) : AntipodalOn qB w pairsAB flipAB := by
  refine ⟨flipAB_mem, fun y hy => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  simp only [pairsAB, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;>
  · simp only [qB, flipAB, Equiv.coe_addRight, DiagPhase.eval_add, DiagPhase.eval_mul,
      DiagPhase.eval_C, DiagPhase.eval_X]
    decide

/-- Off `00, 11`, `qA` and `qB` agree: both are `3` at `01` and `0` at `10`. -/
theorem eval_qB_eq_qA_off (y : Fin 2 → ZMod 2) (hy : y ∉ pairsAB) :
    DiagPhase.eval qB (Fin.append (0 : Fin 0 → ZMod 2) y)
      = DiagPhase.eval qA (Fin.append (0 : Fin 0 → ZMod 2) y) := by
  rw [word_two y] at hy ⊢
  generalize y 0 = a at hy ⊢
  generalize y 1 = b at hy ⊢
  simp only [qA, qB, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
  revert a b
  decide

/-- **R8 relates the two stuck outcomes' plain forms in one step**: rephase the antipodal pair
at `00, 11` from `(0, 2)` to `(3, 1)`. -/
theorem antipodalStep_recB_recA : AntipodalStep recB recA :=
  .rephase (by norm_num) qA qB cOut ⊥ 0 pairsAB flipAB flipAB
    (fun w _ y hy => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      exact eval_qB_eq_qA_off y hy)
    (fun w _ => antipodalOn_qA w) (fun w _ => antipodalOn_qB w)

/-- **The two stuck outcomes are derivable from each other without their input**: R4, R8, R4.
No chain of R1–R7 alone relates them (`not_gaugeRel_outcomeA_outcomeB`). -/
theorem derivable_outcomeB_outcomeA : Derivable outcomeB outcomeA :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ step_outcomeB_recB)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ (Step.antipodal antipodalStep_recB_recA))
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step_outcomeA_recA)))

/-! ### The outcomes' amplitude, and the forward obstruction -/

/-- At precision two the character of `t` is `i^t`. -/
theorem charOf_two_natCast (t : ℕ) : charOf 2 (t : ZMod (2 ^ 2)) = Complex.I ^ t := by
  have h := charOf_two_pow_sub_two_mul (m := 2) le_rfl t
  rwa [Nat.sub_self, pow_zero, one_mul] at h

/-- A sum over the four words of two bits. -/
theorem sum_words_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → ZMod 2) → M) :
    ∑ y, F y = F ![0, 0] + F ![0, 1] + (F ![1, 0] + F ![1, 1]) := by
  rw [← (piFinTwoEquiv fun _ => ZMod 2).symm.sum_comp F, Fintype.sum_prod_type]
  have hsum : ∀ g : ZMod 2 → M, ∑ p, g p = g 0 + g 1 := fun g => by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hsum, hsum, hsum]
  rfl

/-- `√2 ≠ 0` in `ℂ`. -/
theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- `√2 · √2 = 2` in `ℂ`. -/
theorem sqrt_two_mul_self : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `charOf 2 1 = i`. -/
theorem charOf_two_one : charOf 2 1 = Complex.I := by
  have h := charOf_two_natCast 1
  rwa [Nat.cast_one, pow_one] at h

/-- **The outcomes' amplitude is `1/√2`**, read through `recA`: its four phases `0, 3, 0, 2` sum to
`1 − i`, and `(1 + i)/√2 · (1 − i)/2 = 1/√2`. -/
theorem amp_recA_zero : amp recA 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [amp_pos (mem_support_zero recA)]
  change ampCore 2 2 qA cOut 0 = _
  rw [ampCore_eq_sum_charOf, sum_words_two]
  have e : ∀ a b : ZMod 2, DiagPhase.eval qA (Fin.append (0 : Fin 0 → ZMod 2) ![a, b])
      = (((3 * b.val + 3 * a.val * b.val) % 4 : ℕ) : ZMod (2 ^ 2)) := by
    intro a b
    simp only [qA, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
    revert a b
    decide
  rw [e, e, e, e]
  simp only [charOf_two_natCast]
  norm_num
  unfold cOut
  rw [charOf_two_one]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by rw [sq, sqrt_two_mul_self]
  have hne := sqrt_two_ne_zero
  field_simp
  linear_combination (-1 : ℂ) * hs - Complex.I_sq

/-- The outcomes' scale has modulus one. -/
theorem normSq_cOut : Complex.normSq cOut = 1 := by
  unfold cOut
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_one, one_mul,
    normSq_one_add_charOf_rotate (m := 2) (by norm_num) (a := 1) (by decide), normSq_sqrt_two]
  norm_num

/-- `|1/√2|² = 1/2`. -/
theorem normSq_inv_sqrt_two : Complex.normSq (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  rw [map_inv₀, normSq_sqrt_two]
  norm_num

/-- Outcome A's amplitude is `1/√2`. -/
theorem amp_outcomeA_zero : amp outcomeA 0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [stateEq_of_step step_outcomeA_recA]
  exact amp_recA_zero

/-- **No forward derivation takes outcome A to height zero**, with R8 or without it: its scale has
modulus `1`, its amplitude modulus `1/√2`. -/
theorem not_forward_floor_outcomeA : ¬ ∃ T, Forward outcomeA T ∧ T.h = 0 := by
  refine not_forward_floor (w := 0) ?_ ?_
  · rw [amp_outcomeA_zero]
    exact inv_ne_zero sqrt_two_ne_zero
  rw [amp_outcomeA_zero, normSq_inv_sqrt_two, show outcomeA.c = cOut from rfl, normSq_cOut]
  norm_num

/-- **No forward derivation takes outcome B to height zero.** -/
theorem not_forward_floor_outcomeB : ¬ ∃ T, Forward outcomeB T ∧ T.h = 0 := by
  refine not_forward_floor (w := 0) ?_ ?_
  · rw [stateEq_of_derivable derivable_outcomeB_outcomeA, amp_outcomeA_zero]
    exact inv_ne_zero sqrt_two_ne_zero
  rw [stateEq_of_derivable derivable_outcomeB_outcomeA, amp_outcomeA_zero, normSq_inv_sqrt_two,
    show outcomeB.c = cOut from rfl, normSq_cOut]
  norm_num

/-- **No forward derivation takes T04's input to height zero**, in any elimination order: its scale
is `1`. -/
theorem not_forward_floor_input : ¬ ∃ T, Forward input T ∧ T.h = 0 := by
  refine not_forward_floor (w := 0) ?_ ?_
  · rw [← stateEq_outcomeA_input, amp_outcomeA_zero]
    exact inv_ne_zero sqrt_two_ne_zero
  rw [← stateEq_outcomeA_input, amp_outcomeA_zero, normSq_inv_sqrt_two,
    show input.c = 1 from rfl, Complex.normSq_one]
  norm_num

/-! ### One inverse collapse, one rephasing, three rotations

The derivation that reaches height zero: outcome A (plain form `recA`) is the collapse of `up`, a
record at height three with an unused last bit and scale `cOut/√2`; relabelled so the unused bit is
first (`upFirst`), R8 rephases the pair `010, 111` from `(0, 2)` to `(3, 1)` (`upStar`); three
rotations then eliminate the last bit each time, and the floor record is `R4` and `R1` away from
`⟨2, 0, 0, 1/√2, ⊥, 0⟩`. -/

/-- `recA`'s exponent with an unused third bit last: `3·y₁ + 3·y₀·y₁`. -/
noncomputable def wLast : DiagPhase (0 + 2 + 1) 2 := C 3 * X 1 + C 3 * X 0 * X 1

/-- The same with the unused bit first: `3·y₂ + 3·y₁·y₂`. -/
noncomputable def wFirst : DiagPhase (0 + 3) 2 := C 3 * X 2 + C 3 * X 1 * X 2

/-- `wFirst` rephased at `010` (`0 ↦ 3`) and `111` (`2 ↦ 1`). -/
noncomputable def qStar : DiagPhase (0 + 2 + 1) 2 :=
  wFirst + C 3 * ((1 - X 0) * X 1 * (1 - X 2) + X 0 * X 1 * X 2)

/-- The scale at height three. -/
noncomputable def cUp : ℂ := cOut / (Real.sqrt 2 : ℂ)

/-- The first rotation's bit: `1 − y₀·y₁`. -/
noncomputable def lam1 : DiagPhase (0 + 2) 2 := 1 - X 0 * X 1

/-- The second rotation's bit: `1 − y₀`. -/
noncomputable def lam2 : DiagPhase (0 + 1) 2 := 1 - X 0

/-- The exponent after the first rotation. -/
noncomputable def q1 : DiagPhase (0 + 1 + 1) 2 := snocFreeze 0 qStar + C (-1) * lam1

/-- The exponent after the second rotation. -/
noncomputable def q2 : DiagPhase (0 + 0 + 1) 2 := snocFreeze 0 q1 + C (-1) * lam2

/-- The scale after the first rotation. -/
noncomputable def c1 : ℂ := cUp * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)

/-- The scale after the second rotation. -/
noncomputable def c2 : ℂ := c1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)

/-- The scale after the third rotation. -/
noncomputable def c3 : ℂ := c2 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)

/-- The floor state of T04's amplitude: height zero, exponent zero, scale `1/√2`. -/
noncomputable def floor : KernelSumState 0 := ⟨2, 0, 0, (Real.sqrt 2 : ℂ)⁻¹, ⊥, 0⟩

/-- **The inverse collapse.** `up` collapses its unused last bit to `recA`'s exponent at scale
`√2 · cUp`. -/
theorem elimStep_up :
    ElimStep (⟨2, 2 + 1, wLast, cUp, ⊥, 0⟩ : KernelSumState 0)
      (elimCollapse (h := 2) wLast cUp ⊥ 0) := by
  refine ElimStep.collapse (h := 2) (σ := 0) (ε := 0) (by norm_num) wLast cUp (fun w _ y => ?_)
    (fun w => ?_)
  · obtain rfl : w = 0 := Subsingleton.elim _ _
    rw [word_two y]
    generalize y 0 = a
    generalize y 1 = b
    simp only [wLast, lastDiff_eval, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
      DiagPhase.eval_X, dotF2, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    revert a b
    decide
  · exact ⟨fun h => ⟨h, by simp [dotF2]⟩, fun h => h.1⟩

/-- The collapsed record is `recA`: R4 on the exponent, and `√2 · (cOut/√2) = cOut`. -/
theorem derivable_collapse_recA : Derivable (elimCollapse (h := 2) wLast cUp ⊥ 0) recA := by
  have hc : (Real.sqrt 2 : ℂ) * cUp = cOut := by
    unfold cUp
    field_simp [sqrt_two_ne_zero]
  have hstep :
      Step (elimCollapse (h := 2) wLast cUp ⊥ 0) ⟨2, 2, qA, (Real.sqrt 2 : ℂ) * cUp, ⊥, 0⟩ :=
    Step.gauge (GaugeStep.congrSupport (n := 0) (h := 2) qA (snocFreeze 0 wLast) _ ⊥ 0
      (fun w _ y => by
        obtain rfl : w = 0 := Subsingleton.elim _ _
        rw [word_two y]
        generalize y 0 = a
        generalize y 1 = b
        simp only [wLast, qA, snocFreeze_eval, DiagPhase.eval_add, DiagPhase.eval_mul,
          DiagPhase.eval_C, DiagPhase.eval_X]
        revert a b
        decide))
  rw [hc] at hstep
  exact Relation.EqvGen.rel _ _ hstep

/-- The relabelling that puts the unused bit first: `y ↦ (y₁, y₂, y₀)`. -/
def cycleWord : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2) where
  toFun y := ![y 1, y 2, y 0]
  invFun y := ![y 2, y 0, y 1]
  left_inv y := by
    funext i
    fin_cases i <;> rfl
  right_inv y := by
    funext i
    fin_cases i <;> rfl

/-- **R5.** `upFirst` is `up` read through `cycleWord`. -/
theorem step_upFirst_up :
    Step (⟨2, 3, wFirst, cUp, ⊥, 0⟩ : KernelSumState 0) ⟨2, 2 + 1, wLast, cUp, ⊥, 0⟩ :=
  Step.gauge (GaugeStep.renameBound (n := 0) (h := 3) wLast wFirst cUp ⊥ 0 cycleWord (fun w y => by
    obtain rfl : w = 0 := Subsingleton.elim _ _
    rw [word_three y]
    generalize y 0 = a
    generalize y 1 = b
    generalize y 2 = d
    simp only [wLast, wFirst, cycleWord, Equiv.coe_fn_mk, DiagPhase.eval_add, DiagPhase.eval_mul,
      DiagPhase.eval_C, DiagPhase.eval_X]
    revert a b d
    decide))

/-- The rephased paths: `010` and `111`. -/
def pairsUp : Finset (Fin 3 → ZMod 2) := {![0, 1, 0], ![1, 1, 1]}

/-- The pairing: add `101`, which swaps `010` and `111`. -/
def flipUp : Equiv.Perm (Fin 3 → ZMod 2) := Equiv.addRight ![1, 0, 1]

/-- `flipUp` keeps `pairsUp`. -/
theorem flipUp_mem (y : Fin 3 → ZMod 2) : y ∈ pairsUp ↔ flipUp y ∈ pairsUp := by
  rw [word_three y]
  generalize y 0 = a
  generalize y 1 = b
  generalize y 2 = d
  simp only [flipUp, Equiv.coe_addRight]
  revert a b d
  decide

/-- **R8.** `upFirst` rephased at `010, 111` is `upStar`. -/
theorem step_upStar_upFirst :
    Step (⟨2, 2 + 1, qStar, cUp, ⊥, 0⟩ : KernelSumState 0) ⟨2, 3, wFirst, cUp, ⊥, 0⟩ :=
  Step.antipodal (.rephase (n := 0) (h := 3) (by norm_num) wFirst qStar cUp ⊥ 0 pairsUp flipUp
    flipUp
    (fun w _ y hy => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      rw [word_three y] at hy ⊢
      generalize y 0 = a at hy ⊢
      generalize y 1 = b at hy ⊢
      generalize y 2 = d at hy ⊢
      simp only [qStar, wFirst, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
        DiagPhase.eval_X, eval_sub', eval_one']
      revert a b d
      decide)
    (fun w _ => ⟨flipUp_mem, fun y hy => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      simp only [pairsUp, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;>
      · simp only [wFirst, flipUp, Equiv.coe_addRight, DiagPhase.eval_add, DiagPhase.eval_mul,
          DiagPhase.eval_C, DiagPhase.eval_X]
        decide⟩)
    (fun w _ => ⟨flipUp_mem, fun y hy => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      simp only [pairsUp, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;>
      · simp only [qStar, wFirst, flipUp, Equiv.coe_addRight, DiagPhase.eval_add,
          DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, eval_sub', eval_one']
        decide⟩))

/-- The first rotation's shape: along the last bit of `qStar` the difference is
`1 + 2·(1 − y₀y₁)`. -/
theorem rotateData_qStar : RotateData (n := 0) (h := 2) qStar ⊥ 0 1 lam1 := by
  refine ⟨by decide, fun w _ y => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [word_two y]
  generalize y 0 = a
  generalize y 1 = b
  refine ⟨1 + a * b, ?_, ?_⟩
  · simp only [lam1, eval_sub', eval_one', DiagPhase.eval_mul, DiagPhase.eval_X]
    revert a b
    decide
  · simp only [qStar, wFirst, lastDiff_eval, DiagPhase.eval_add, DiagPhase.eval_mul,
      DiagPhase.eval_C, DiagPhase.eval_X, eval_sub', eval_one']
    revert a b
    decide

/-- The second rotation's shape: along the last bit of `q1` the difference is `1 + 2·(1 − y₀)`. -/
theorem rotateData_q1 : RotateData (n := 0) (h := 1) q1 ⊥ 0 1 lam2 := by
  refine ⟨by decide, fun w _ y => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  have hy : y = ![y 0] := by
    funext i
    fin_cases i
    rfl
  rw [hy]
  generalize y 0 = a
  refine ⟨1 + a, ?_, ?_⟩
  · simp only [lam2, eval_sub', eval_one', DiagPhase.eval_X]
    revert a
    decide
  · simp only [q1, lam1, qStar, wFirst, lastDiff_eval, snocFreeze_eval, DiagPhase.eval_add,
      DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, eval_sub', eval_one']
    revert a
    decide

/-- The third rotation's shape: along the last bit of `q2` the difference is `1`. -/
theorem rotateData_q2 : RotateData (n := 0) (h := 0) q2 ⊥ 0 1 0 := by
  refine ⟨by decide, fun w _ y => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  obtain rfl : y = 0 := Subsingleton.elim _ _
  refine ⟨0, ?_, ?_⟩
  · rw [eval_zero']
    decide
  · simp only [q2, lam2, q1, lam1, qStar, wFirst, lastDiff_eval, snocFreeze_eval,
      DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, eval_sub',
      eval_one']
    decide

/-- The first rotation. -/
theorem step_rot1 :
    Step (⟨2, 2 + 1, qStar, cUp, ⊥, 0⟩ : KernelSumState 0)
      (elimRotate (h := 2) qStar 1 lam1 cUp ⊥ 0) :=
  Step.elim (ElimStep.rotate (h := 2) (by norm_num) qStar cUp rotateData_qStar (fun _ => Iff.rfl))

/-- The second rotation. -/
theorem step_rot2 :
    Step (elimRotate (h := 2) qStar 1 lam1 cUp ⊥ 0) (elimRotate (h := 1) q1 1 lam2 c1 ⊥ 0) :=
  Step.elim (ElimStep.rotate (h := 1) (by norm_num) q1 c1 rotateData_q1 (fun _ => Iff.rfl))

/-- The third rotation. -/
theorem step_rot3 :
    Step (elimRotate (h := 1) q1 1 lam2 c1 ⊥ 0) (elimRotate (h := 0) q2 1 0 c2 ⊥ 0) :=
  Step.elim (ElimStep.rotate (h := 0) (by norm_num) q2 c2 rotateData_q2 (fun _ => Iff.rfl))

/-- The floor record's exponent is the constant `2` (R4). -/
theorem step_floor_R4 :
    Step (elimRotate (h := 0) q2 1 0 c2 ⊥ 0)
      (⟨2, 0, 0 + C 2, c3, ⊥, 0⟩ : KernelSumState 0) :=
  Step.gauge (GaugeStep.congrSupport (n := 0) (h := 0) (0 + C 2) _ c3 ⊥ 0 (fun w _ y => by
    obtain rfl : w = 0 := Subsingleton.elim _ _
    obtain rfl : y = 0 := Subsingleton.elim _ _
    simp only [q2, lam2, q1, lam1, qStar, wFirst, snocFreeze_eval, DiagPhase.eval_add,
      DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, eval_sub', eval_one', eval_zero']
    decide))

/-- The constant `2` moved into the scale (R1). -/
theorem step_floor_R1 :
    Step (⟨2, 0, 0 + C 2, c3, ⊥, 0⟩ : KernelSumState 0) ⟨2, 0, 0, c3 * charOf 2 2, ⊥, 0⟩ :=
  Step.gauge (GaugeStep.addC (n := 0) (h := 0) 0 2 c3 ⊥ 0)

/-- The scale at the floor: `(1 + i)^4 / (√2)^5 · (−1) = 1/√2`. -/
theorem c3_mul_charOf_two : c3 * charOf 2 2 = (Real.sqrt 2 : ℂ)⁻¹ := by
  have h2 : charOf 2 2 = -1 := by
    have h := charOf_two_natCast 2
    rwa [Nat.cast_ofNat, Complex.I_sq] at h
  unfold c3 c2 c1 cUp cOut
  rw [h2, charOf_two_one]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by rw [sq, sqrt_two_mul_self]
  have hne := sqrt_two_ne_zero
  field_simp
  linear_combination (-4 - 4 * Complex.I - (Complex.I ^ 2 + 1)) * Complex.I_sq
    - ((Real.sqrt 2 : ℂ) ^ 2 + 2) * hs

/-- **Outcome A reaches the floor state by a derivation**: R4, one inverse collapse, R5, R8, three
rotations, R4, R1. -/
theorem derivable_outcomeA_floor : Derivable outcomeA floor := by
  have e : ∀ {S T : KernelSumState 0}, Step S T → Derivable S T :=
    fun h => Relation.EqvGen.rel _ _ h
  have t : ∀ {S T U : KernelSumState 0}, Derivable S T → Derivable T U → Derivable S U :=
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂
  have s : ∀ {S T : KernelSumState 0}, Derivable S T → Derivable T S :=
    fun h => Relation.EqvGen.symm _ _ h
  have hfloor : (⟨2, 0, 0, c3 * charOf 2 2, ⊥, 0⟩ : KernelSumState 0) = floor := by
    rw [c3_mul_charOf_two]
    rfl
  rw [← hfloor]
  exact t (e step_outcomeA_recA) <| t (s derivable_collapse_recA) <|
    t (s (e (Step.elim elimStep_up))) <| t (s (e step_upFirst_up)) <|
    t (s (e step_upStar_upFirst)) <| t (e step_rot1) <| t (e step_rot2) <| t (e step_rot3) <|
    t (e step_floor_R4) (e step_floor_R1)

/-- **Outcome B reaches the same floor state**, through R8 to outcome A. -/
theorem derivable_outcomeB_floor : Derivable outcomeB floor :=
  Relation.EqvGen.trans _ _ _ derivable_outcomeB_outcomeA derivable_outcomeA_floor

/-- **T04's two stuck outcomes against R8.** R8 relates them where R1–R7 do not; both reach one
state at height zero by a derivation, and it denotes their state; no forward derivation (gauge
rewrites either way, R8, eliminations as written) reaches height zero from either of them or from
their input. -/
theorem t04_outcomes :
    Derivable outcomeB outcomeA ∧ ¬ GaugeRel outcomeA outcomeB
      ∧ Derivable outcomeA floor ∧ Derivable outcomeB floor ∧ floor.h = 0
      ∧ StateEq floor input
      ∧ (¬ ∃ T, Forward outcomeA T ∧ T.h = 0) ∧ (¬ ∃ T, Forward outcomeB T ∧ T.h = 0)
      ∧ (¬ ∃ T, Forward input T ∧ T.h = 0) :=
  ⟨derivable_outcomeB_outcomeA, not_gaugeRel_outcomeA_outcomeB, derivable_outcomeA_floor,
    derivable_outcomeB_floor, rfl,
    (stateEq_of_derivable derivable_outcomeA_floor).symm.trans stateEq_outcomeA_input,
    not_forward_floor_outcomeA, not_forward_floor_outcomeB, not_forward_floor_input⟩

/-! ### R9 takes both outcomes forward to one floor state -/

/-- The one-bit words onto `01, 10`: `y ↦ (y, 1 + y)`, the complement of `pairsAB`. -/
def offDiag : (Fin 1 → ZMod 2) ↪ (Fin 2 → ZMod 2) where
  toFun y := ![y 0, 1 + y 0]
  inj' y y' hyy := by
    have h0 := congrFun hyy 0
    funext i
    fin_cases i
    exact h0

/-- `pairsAB` is the complement of `offDiag`'s image. -/
theorem mem_pairsAB_iff (y' : Fin 2 → ZMod 2) : y' ∈ pairsAB ↔ ∀ y, offDiag y ≠ y' := by
  rw [word_two y']
  generalize y' 0 = a
  generalize y' 1 = b
  revert a b
  decide

/-- Both outcomes halved: `3 + y` (the phases `3, 0` both outcomes keep at `01, 10`). -/
noncomputable def qHalf : DiagPhase (0 + 1) 2 := C 3 + X 0

/-- The common record at height one. -/
noncomputable def half : KernelSumState 0 := ⟨2, 1, qHalf, cOut / (Real.sqrt 2 : ℂ), ⊥, 0⟩

/-- The one floor record both outcomes reach: `half` rotated. -/
noncomputable def floorHalf : KernelSumState 0 :=
  elimRotate (h := 0) qHalf 1 0 (cOut / (Real.sqrt 2 : ℂ)) ⊥ 0

/-- A word of one bit is `![a]`. -/
theorem word_one (y : Fin 1 → ZMod 2) : y = ![y 0] := by
  funext i
  fin_cases i
  rfl

/-- **R9 on outcome A**: delete the pair `00, 11` (phases `0, 2`). -/
theorem halvingStep_recA : HalvingStep recA half :=
  .halve (n := 0) (h := 1) (by norm_num) qA qHalf cOut ⊥ 0 offDiag pairsAB flipAB mem_pairsAB_iff
    (fun w _ y => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      rw [word_one y]
      generalize y 0 = a
      simp only [qHalf, qA, offDiag, Function.Embedding.coeFn_mk, DiagPhase.eval_add,
        DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      revert a
      decide)
    (fun w _ => antipodalOn_qA w)

/-- **R9 on outcome B**: delete the pair `00, 11` (phases `3, 1`). -/
theorem halvingStep_recB : HalvingStep recB half :=
  .halve (n := 0) (h := 1) (by norm_num) qB qHalf cOut ⊥ 0 offDiag pairsAB flipAB mem_pairsAB_iff
    (fun w _ y => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      rw [word_one y]
      generalize y 0 = a
      simp only [qHalf, qB, offDiag, Function.Embedding.coeFn_mk, DiagPhase.eval_add,
        DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      revert a
      decide)
    (fun w _ => antipodalOn_qB w)

/-- `half` rotates: along its one bit the difference is `1`. -/
theorem elimStep_half : ElimStep half floorHalf :=
  ElimStep.rotate (h := 0) (by norm_num) qHalf _ (a := 1) (Λ := 0)
    ⟨by decide, fun w _ y => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      obtain rfl : y = 0 := Subsingleton.elim _ _
      refine ⟨0, by rw [eval_zero']; decide, ?_⟩
      simp only [qHalf, lastDiff_eval, DiagPhase.eval_add, DiagPhase.eval_C, DiagPhase.eval_X]
      decide⟩
    (fun _ => Iff.rfl)

/-- **With R9, both stuck outcomes go forward to one state at height zero**: R4, R9, rotate. The
floor record is the same record for both. -/
theorem t04_halving :
    Forward9 outcomeA floorHalf ∧ Forward9 outcomeB floorHalf ∧ floorHalf.h = 0
      ∧ StateEq floorHalf input := by
  have hA : Forward9 outcomeA floorHalf :=
    Relation.ReflTransGen.head (Or.inl (Or.inl gauge_outcomeA_recA))
      (Relation.ReflTransGen.head (Or.inr halvingStep_recA)
        (Relation.ReflTransGen.single (Or.inl (Or.inr (Or.inr (Or.inr elimStep_half))))))
  have hB : Forward9 outcomeB floorHalf :=
    Relation.ReflTransGen.head (Or.inl (Or.inl gauge_outcomeB_recB))
      (Relation.ReflTransGen.head (Or.inr halvingStep_recB)
        (Relation.ReflTransGen.single (Or.inl (Or.inr (Or.inr (Or.inr elimStep_half))))))
  exact ⟨hA, hB, rfl, (stateEq_of_forward9 hA).symm.trans stateEq_outcomeA_input⟩

/-! ### R9 on the input: no order, one floor -/

/-- Two-bit words onto `000, 011, 001, 101`: `y ↦ (y₀y₁, (1 + y₀)y₁, y₀ ∨ y₁)`. -/
def inEmbed : (Fin 2 → ZMod 2) ↪ (Fin 3 → ZMod 2) where
  toFun y := ![y 0 * y 1, (1 + y 0) * y 1, y 0 + y 1 + y 0 * y 1]
  inj' y y' hyy := by
    rw [word_two y, word_two y'] at hyy ⊢
    generalize y 0 = a at hyy ⊢
    generalize y 1 = b at hyy ⊢
    generalize y' 0 = a' at hyy ⊢
    generalize y' 1 = b' at hyy ⊢
    revert a b a' b'
    decide

/-- The input's deleted paths: `010, 100` (phases `3, 1`) and `110, 111` (phases `0, 2`). -/
def pairsIn : Finset (Fin 3 → ZMod 2) := {![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]}

/-- The pairing of `pairsIn`. -/
def flipIn : Equiv.Perm (Fin 3 → ZMod 2) :=
  Equiv.swap ![0, 1, 0] ![1, 0, 0] * Equiv.swap ![1, 1, 0] ![1, 1, 1]

/-- `pairsIn` is the complement of `inEmbed`'s image. -/
theorem mem_pairsIn_iff (y' : Fin 3 → ZMod 2) : y' ∈ pairsIn ↔ ∀ y, inEmbed y ≠ y' := by
  rw [word_three y']
  generalize y' 0 = a
  generalize y' 1 = b
  generalize y' 2 = d
  revert a b d
  decide

/-- The input's exponent is paired antipodally on `pairsIn` by `flipIn`. -/
theorem antipodalOn_input (w : Fin 0 → ZMod 2) : AntipodalOn inputExponent w pairsIn flipIn := by
  obtain rfl : w = 0 := Subsingleton.elim _ _
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · rw [word_three y]
    generalize y 0 = a
    generalize y 1 = b
    generalize y 2 = d
    revert a b d
    decide
  · simp only [pairsIn, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
    · simp only [inputExponent, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
        DiagPhase.eval_X]
      decide

/-- The input halved: `3·y₁ + 2·y₀·y₁`. -/
noncomputable def qIn : DiagPhase (0 + 2) 2 := C 3 * X 1 + C 2 * X 0 * X 1

/-- **R9 on the input.** -/
theorem halvingStep_input :
    HalvingStep input (⟨2, 2, qIn, 1 / (Real.sqrt 2 : ℂ), ⊥, 0⟩ : KernelSumState 0) :=
  .halve (n := 0) (h := 2) (by norm_num) inputExponent qIn 1 ⊥ 0 inEmbed pairsIn flipIn
    mem_pairsIn_iff
    (fun w _ y => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      rw [word_two y]
      generalize y 0 = a
      generalize y 1 = b
      simp only [qIn, inputExponent, inEmbed, Function.Embedding.coeFn_mk, DiagPhase.eval_add,
        DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      revert a b
      decide)
    (fun w _ => antipodalOn_input w)

/-- The halved input rotates at its last bit with `Λ = 1 − y₀`. -/
theorem elimStep_qIn :
    ElimStep (⟨2, 2, qIn, 1 / (Real.sqrt 2 : ℂ), ⊥, 0⟩ : KernelSumState 0)
      (elimRotate (h := 1) qIn 1 lam2 (1 / (Real.sqrt 2 : ℂ)) ⊥ 0) :=
  ElimStep.rotate (h := 1) (by norm_num) qIn _
    ⟨by decide, fun w _ y => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      rw [word_one y]
      generalize y 0 = a
      refine ⟨1 + a, ?_, ?_⟩
      · simp only [lam2, eval_sub', eval_one', DiagPhase.eval_X]
        revert a
        decide
      · simp only [qIn, lastDiff_eval, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
          DiagPhase.eval_X]
        revert a
        decide⟩
    (fun _ => Iff.rfl)

/-- The rotated input is `half` (R4, and `(1/√2)·(1 + i)/√2 = cOut/√2`). -/
theorem gauge_rotIn_half :
    GaugeStep (elimRotate (h := 1) qIn 1 lam2 (1 / (Real.sqrt 2 : ℂ)) ⊥ 0) half := by
  have hc : 1 / (Real.sqrt 2 : ℂ) * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ)
      = cOut / (Real.sqrt 2 : ℂ) := by
    unfold cOut
    ring
  have hstep : GaugeStep (elimRotate (h := 1) qIn 1 lam2 (1 / (Real.sqrt 2 : ℂ)) ⊥ 0)
      ⟨2, 1, qHalf, 1 / (Real.sqrt 2 : ℂ) * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ), ⊥, 0⟩ :=
    GaugeStep.congrSupport (n := 0) (h := 1) qHalf _ _ ⊥ 0 (fun w _ y => by
      obtain rfl : w = 0 := Subsingleton.elim _ _
      rw [word_one y]
      generalize y 0 = a
      simp only [qIn, qHalf, lam2, snocFreeze_eval, DiagPhase.eval_add, DiagPhase.eval_mul,
        DiagPhase.eval_C, DiagPhase.eval_X, eval_sub', eval_one']
      revert a
      decide)
  rw [hc] at hstep
  exact hstep

/-- **With R9, T04's input goes forward to the same floor record as both outcomes**: R9, rotate,
R4, rotate. -/
theorem forward9_input_floorHalf : Forward9 input floorHalf :=
  Relation.ReflTransGen.head (Or.inr halvingStep_input)
    (Relation.ReflTransGen.head (Or.inl (Or.inr (Or.inr (Or.inr elimStep_qIn))))
      (Relation.ReflTransGen.head (Or.inl (Or.inl gauge_rotIn_half))
        (Relation.ReflTransGen.single (Or.inl (Or.inr (Or.inr (Or.inr elimStep_half)))))))

end T04

/-! ## The scale's modulus up to powers of two is invariant

Every rule here multiplies the scale by a root of unity, by `√2^{±1}`, or by a rotate factor of
modulus one, so `|c|²` moves only by powers of two. Two records with the same amplitude whose scales
differ by any other modulus are related by no derivation, with R9 or without it. -/

section ScaleClass

open FTQCLib FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough
open MvPolynomial (C X)

variable {n : ℕ}

/-- One rule of the system with R9. -/
def Step9 (S T : KernelSumState n) : Prop :=
  Step S T ∨ HalvingStep S T

/-- A derivation with R9: its rules in either direction. -/
def Derivable9 : KernelSumState n → KernelSumState n → Prop :=
  Relation.EqvGen Step9

/-- One rule multiplies `|c|²` by a power of two. -/
theorem scaleClass_of_step9 {S T : KernelSumState n} (hST : Step9 S T) :
    ∃ k : ℤ, Complex.normSq T.c = (2 : ℝ) ^ k * Complex.normSq S.c := by
  rcases hST with (h | h | h) | h
  · exact ⟨0, by rw [zpow_zero, one_mul, normSq_c_of_gaugeStep h]⟩
  · exact ⟨0, by rw [zpow_zero, one_mul, c_of_antipodalStep h]⟩
  · cases h with
    | collapse hm Q c hsign hsupp =>
      refine ⟨1, ?_⟩
      change Complex.normSq ((Real.sqrt 2 : ℂ) * c) = _
      rw [Complex.normSq_mul, normSq_sqrt_two, zpow_one]
    | rotate hm Q c hrot hsupp =>
      refine ⟨0, ?_⟩
      change Complex.normSq (c * (1 + charOf _ _) / (Real.sqrt 2 : ℂ)) = _
      rw [Complex.normSq_div, Complex.normSq_mul, normSq_one_add_charOf_rotate hm hrot.1,
        normSq_sqrt_two, zpow_zero, one_mul]
      field_simp
  · refine ⟨-1, ?_⟩
    rw [normSq_c_of_halvingStep h, zpow_neg_one]
    ring

/-- **Derivations multiply `|c|²` by a power of two.** -/
theorem scaleClass_of_derivable9 {S T : KernelSumState n} (hST : Derivable9 S T) :
    ∃ k : ℤ, Complex.normSq T.c = (2 : ℝ) ^ k * Complex.normSq S.c := by
  unfold Derivable9 at hST
  induction hST with
  | rel _ _ h => exact scaleClass_of_step9 h
  | refl _ => exact ⟨0, by rw [zpow_zero, one_mul]⟩
  | symm _ _ _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨-k, ?_⟩
    rw [hk, ← mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul]
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨k₁, hk₁⟩ := ih₁
    obtain ⟨k₂, hk₂⟩ := ih₂
    refine ⟨k₂ + k₁, ?_⟩
    rw [hk₂, hk₁, ← mul_assoc, ← zpow_add₀ two_ne_zero]

/-- Derivations with R9 keep the denotation. -/
theorem stateEq_of_derivable9 {S T : KernelSumState n} (hST : Derivable9 S T) : StateEq S T := by
  unfold Derivable9 at hST
  induction hST with
  | rel _ _ h =>
    rcases h with h | h
    · exact stateEq_of_step h
    · exact stateEq_of_halvingStep h
  | refl _ => exact StateEq.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `5/2` is no integer power of two. -/
theorem two_zpow_ne_five_halves (k : ℤ) : (2 : ℝ) ^ k ≠ 5 / 2 := by
  intro hk
  have h5 : (2 : ℝ) ^ (k + 1) = 5 := by
    rw [zpow_add₀ two_ne_zero, hk, zpow_one]
    norm_num
  rcases Int.eq_nat_or_neg (k + 1) with ⟨j, hj | hj⟩
  · rw [hj, zpow_natCast] at h5
    have hnat : 2 ^ j = 5 := by exact_mod_cast h5
    rcases j with _ | j
    · norm_num at hnat
    · rw [pow_succ] at hnat
      omega
  · rw [hj, zpow_neg, zpow_natCast] at h5
    have hle : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    linarith

/-- The corner exponent `y₀·y₁`: phases `0, 0, 0, 1`, image `3 + i`. -/
noncomputable def qCorner : DiagPhase (0 + 2) 2 := X 0 * X 1

/-- The corner record at height two, scale one: amplitude `(3 + i)/2`. -/
noncomputable def corner : KernelSumState 0 := ⟨2, 2, qCorner, 1, ⊥, 0⟩

/-- The same amplitude at height zero. -/
noncomputable def cornerFloor : KernelSumState 0 := ⟨2, 0, 0, (3 + Complex.I) / 2, ⊥, 0⟩

/-- The corner record and its floor presentation have the same amplitude. -/
theorem stateEq_corner : StateEq corner cornerFloor := by
  funext w
  obtain rfl : w = 0 := Subsingleton.elim _ _
  rw [amp_pos (mem_support_zero corner), amp_pos (mem_support_zero cornerFloor)]
  change ampCore 2 2 qCorner 1 0 = ampCore 2 0 0 ((3 + Complex.I) / 2) 0
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf, T04.sum_words_two, Fintype.sum_unique]
  have e : ∀ a b : ZMod 2, DiagPhase.eval qCorner (Fin.append (0 : Fin 0 → ZMod 2) ![a, b])
      = (((a.val * b.val) % 4 : ℕ) : ZMod (2 ^ 2)) := by
    intro a b
    simp only [qCorner, DiagPhase.eval_mul, DiagPhase.eval_X]
    revert a b
    decide
  rw [e, e, e, e, T04.eval_zero']
  simp only [T04.charOf_two_natCast, charOf_zero]
  norm_num
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by rw [sq, T04.sqrt_two_mul_self]
  rw [hs]
  ring

/-- **Equal amplitude, no derivation.** The corner record and its floor presentation denote one
state, and no derivation of R1–R9 with the eliminations, in either direction, relates them: their
scales' moduli differ by `5/2`. -/
theorem not_derivable9_corner :
    StateEq corner cornerFloor ∧ ¬ Derivable9 corner cornerFloor := by
  refine ⟨stateEq_corner, fun h => ?_⟩
  obtain ⟨k, hk⟩ := scaleClass_of_derivable9 h
  have hc : Complex.normSq ((3 + Complex.I) / 2) = 5 / 2 := by
    rw [Complex.normSq_div, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    norm_num
  change Complex.normSq ((3 + Complex.I) / 2) = (2 : ℝ) ^ k * Complex.normSq 1 at hk
  rw [hc, Complex.normSq_one, mul_one] at hk
  exact two_zpow_ne_five_halves k hk.symm

end ScaleClass

/-! ## The hypotheses are load-bearing -/

section Hypotheses

open FTQCLib FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough
open MvPolynomial (C X)

/-- At `m = 0` the pointwise kernel fails: `ZMod 1` has one residue, the antipodal condition holds
of every element, and the constant `1` has image `1`. -/
theorem evalRoot_zero_ne_zero : evalRoot (K := ℂ) 0 1 (fun _ => 1) ≠ 0 := by
  unfold evalRoot
  simp

/-- A bit and its sign: `y` at precision one takes `0, 1`, an antipodal pair. -/
noncomputable def signBit : DiagPhase (0 + 1) 1 := X 0

/-- **R8 needs the output paired.** `signBit` is paired on both words by the flip, the zero
exponent is not, and they agree off the (full) set vacuously; the two records differ (`0` against
`√2`). -/
theorem antipodalOn_signBit_and_not_stateEq :
    AntipodalOn (n := 0) signBit 0 Finset.univ (Equiv.addRight ![1])
      ∧ ¬ StateEq (⟨1, 1, 0, 1, ⊥, 0⟩ : KernelSumState 0) ⟨1, 1, signBit, 1, ⊥, 0⟩ := by
  have hy : ∀ y : Fin 1 → ZMod 2, y = ![y 0] := fun y => by
    funext i
    fin_cases i
    rfl
  refine ⟨⟨fun y => by simp, fun y _ => ?_⟩, fun h => ?_⟩
  · rw [hy y]
    generalize y 0 = a
    simp only [signBit, Equiv.coe_addRight, DiagPhase.eval_X]
    revert a
    decide
  · have h0 := congrFun h 0
    rw [amp_pos (T04.supp_bot 0), amp_pos (T04.supp_bot 0)] at h0
    change ampCore 1 1 0 1 0 = ampCore 1 1 signBit 1 0 at h0
    have hsum : ∀ F : (Fin 1 → ZMod 2) → ℂ, ∑ y, F y = F ![0] + F ![1] := fun F => by
      rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp F,
        show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
        Finset.sum_insert (by decide), Finset.sum_singleton]
      congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
    have hneg : charOf 1 1 = -1 := by
      have h1 := charOf_two_pow_pred (m := 1) le_rfl
      rwa [Nat.sub_self, pow_zero] at h1
    rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf, hsum, hsum] at h0
    have e0 : Fin.append (0 : Fin 0 → ZMod 2) ![(0 : ZMod 2)] 0 = 0 := by decide
    have e1 : Fin.append (0 : Fin 0 → ZMod 2) ![(1 : ZMod 2)] 0 = 1 := by decide
    simp only [signBit, DiagPhase.eval_X, T04.eval_zero'] at h0
    norm_num [charOf_zero, hneg, e0, e1] at h0

end Hypotheses

/-! ## The axiom sweep — build-failing, one guard per headline result -/

/-- info: 'FTQCLib.Explore.CyclotomicKernel.foldMap_eq_zero_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms foldMap_eq_zero_iff

/-- info: 'FTQCLib.Explore.CyclotomicKernel.evalRoot_eq_zero_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalRoot_eq_zero_iff

/-- info: 'FTQCLib.Explore.CyclotomicKernel.aeval_eq_zero_iff_mem_span'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aeval_eq_zero_iff_mem_span

/-- info: 'FTQCLib.Explore.CyclotomicKernel.ampCore_eq_iff_antipodal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ampCore_eq_iff_antipodal

/-- info: 'FTQCLib.Explore.CyclotomicKernel.stateEq_of_antipodalStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_antipodalStep

/-- info: 'FTQCLib.Explore.CyclotomicKernel.stateEq_of_derivable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_derivable

/-- info: 'FTQCLib.Explore.CyclotomicKernel.normSq_c_le_of_forward'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_c_le_of_forward

/-- info: 'FTQCLib.Explore.CyclotomicKernel.not_forward_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_forward_floor

/-- info: 'FTQCLib.Explore.CyclotomicKernel.T04.antipodalStep_recB_recA'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T04.antipodalStep_recB_recA

/-- info: 'FTQCLib.Explore.CyclotomicKernel.T04.derivable_outcomeA_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T04.derivable_outcomeA_floor

/-- info: 'FTQCLib.Explore.CyclotomicKernel.T04.t04_outcomes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T04.t04_outcomes

/-- info: 'FTQCLib.Explore.CyclotomicKernel.evalRoot_zero_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalRoot_zero_ne_zero

/-- info: 'FTQCLib.Explore.CyclotomicKernel.antipodalOn_signBit_and_not_stateEq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms antipodalOn_signBit_and_not_stateEq

/-- info: 'FTQCLib.Explore.CyclotomicKernel.stateEq_of_halvingStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_halvingStep

/-- info: 'FTQCLib.Explore.CyclotomicKernel.normSq_c_of_halvingStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normSq_c_of_halvingStep

/-- info: 'FTQCLib.Explore.CyclotomicKernel.T04.t04_halving'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T04.t04_halving

/-- info: 'FTQCLib.Explore.CyclotomicKernel.T04.forward9_input_floorHalf'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms T04.forward9_input_floorHalf

/-- info: 'FTQCLib.Explore.CyclotomicKernel.stateEq_of_derivable9'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_derivable9

/-- info: 'FTQCLib.Explore.CyclotomicKernel.scaleClass_of_derivable9'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scaleClass_of_derivable9

/-- info: 'FTQCLib.Explore.CyclotomicKernel.not_derivable9_corner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_derivable9_corner

end FTQCLib.Explore.CyclotomicKernel

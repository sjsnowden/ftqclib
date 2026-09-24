/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CharSumGates
import FTQCLib.Examples.HadamardCharSumFrame
import FTQCLib.Hierarchy.RzApprox

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # The frame-native Gauss-sum pairing on the character-sum carrier

The character-sum carrier `KernelSumState` (`FTQCLib/Examples/HadamardPhase.lean`) carries an amplitude
function `w ↦ ampCore S w` — a finite Gauss sum over 𝔽₂. This file equips those amplitudes with their
**own** ℓ²-overlap, the finite **Gauss-sum pairing** `⟨S, T⟩ = Σ_w conj(ampCore S w)·ampCore T w`, and its
induced norm `carrierNormSq S = Σ_w |ampCore S w|²`. Everything is built from `ampCore` and `ℂ` — it imports
no `FTQCLib.Hilbert`: the inner product is reconstructed from the frame's own character data, not borrowed from
`EuclideanSpace`.

The point of the pairing is that **`H` is unitary for it** — a finite-Fourier Parseval identity, provable
from the parallelogram law on `H`'s two Walsh branches, with no Hilbert space. So in this native measure the
`√2`-per-`H` toll that the max-row-sum measure pays (`SU2CoverageLinfty.lean`) disappears *for the right
reason*: `H` preserves the pairing.

This file: the pairing and norm, and the abstract single-bit **Walsh isometry** — the
mathematical heart, stated for an arbitrary amplitude function so the carrier application is a clean
corollary. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Hierarchy Complex

variable {n : ℕ}

/-! ## The Gauss-sum pairing and the native norm -/

/-- The frame-native **Gauss-sum pairing** of two carrier states at the same precision: the finite
ℓ²-overlap `Σ_w conj(ampCore S w)·ampCore T w` of their amplitude functions. A finite 𝔽₂ character sum
valued in `ℂ`; imports no `FTQCLib.Hilbert`. -/
noncomputable def carrierInner (S T : KernelSumState n) : ℂ :=
  ∑ w : Fin n → ZMod 2, (starRingEnd ℂ) (ampCore S.m S.h S.Q S.c w) * ampCore T.m T.h T.Q T.c w

/-- The frame-native **norm squared** of a carrier state: `Σ_w |ampCore S w|²`, the diagonal of the
Gauss-sum pairing. -/
noncomputable def carrierNormSq (S : KernelSumState n) : ℝ :=
  ∑ w : Fin n → ZMod 2, Complex.normSq (ampCore S.m S.h S.Q S.c w)

/-- `carrierNormSq` is the real part of the self-pairing. -/
theorem carrierNormSq_eq_inner (S : KernelSumState n) :
    (carrierNormSq S : ℂ) = carrierInner S S := by
  unfold carrierNormSq carrierInner
  push_cast
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Complex.normSq_eq_conj_mul_self]

/-! ## The abstract single-bit Walsh isometry -/

/-- The Walsh sign `(-1)^b` as a complex number. -/
noncomputable def signOf (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

/-- The single-bit **Walsh transform** of an amplitude function `f` at output bit `k`:
`(W f)(w) = (1/√2)·(f(w[k←0]) + (-1)^{w_k}·f(w[k←1]))`. This is exactly what `H` on bit `k` does to an
amplitude function. -/
noncomputable def walshTransform (k : Fin n) (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) : ℂ :=
  (1 / (Real.sqrt 2 : ℂ)) *
    (f (Function.update w k 0) + signOf (w k) * f (Function.update w k 1))

/-- The parallelogram law for `Complex.normSq`. -/
theorem normSq_parallelogram (a b : ℂ) :
    Complex.normSq (a + b) + Complex.normSq (a - b)
      = 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- `|1/√2|² = 1/2`. -/
theorem normSq_half : Complex.normSq (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
  rw [map_div₀, Complex.normSq_one, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The single-bit Walsh transform is an isometry for the native ℓ²-norm.** `Σ_w |(W f)(w)|² =
Σ_w |f(w)|²` — the finite-Fourier Parseval identity, from the parallelogram law on the two branches.
This is "`H` is unitary" as an 𝔽₂ Gauss-sum orthogonality, importing no Hilbert space. -/
theorem walsh_normSq_isometry (k : Fin n) (f : (Fin n → ZMod 2) → ℂ) :
    ∑ w : Fin n → ZMod 2, Complex.normSq (walshTransform k f w)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w) := by
  set e := Equiv.funSplitAt k (ZMod 2) with he
  have hk : ∀ (b : ZMod 2) (u : {j // j ≠ k} → ZMod 2), (e.symm (b, u)) k = b := by
    intro b u
    simp [he, Equiv.funSplitAt, Equiv.piSplitAt]
  have hupd : ∀ (b c : ZMod 2) (u : {j // j ≠ k} → ZMod 2),
      Function.update (e.symm (b, u)) k c = e.symm (c, u) := by
    intro b c u
    funext j
    by_cases hj : j = k
    · subst hj; rw [Function.update_self]; simp [he, Equiv.funSplitAt, Equiv.piSplitAt]
    · rw [Function.update_of_ne hj]; simp [he, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [← Equiv.sum_comp e.symm (fun w => Complex.normSq (walshTransform k f w)),
    ← Equiv.sum_comp e.symm (fun w => Complex.normSq (f w)),
    Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
    Finset.sum_comm (s := (Finset.univ : Finset (ZMod 2)))]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [walshTransform, hupd, hk, signOf, if_true,
    if_neg (by decide : (1 : ZMod 2) ≠ 0), one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [Complex.normSq_mul, Complex.normSq_mul, normSq_half]
  linarith [normSq_parallelogram (f (e.symm (0, u))) (f (e.symm (1, u)))]

/-! ## `H` on the carrier is the Walsh transform, so it preserves the native norm -/

/-- The Walsh sign as a power of `-1`: `(-1)^{b} = signOf b`. -/
theorem neg_one_pow_val (b : ZMod 2) : (-1 : ℂ) ^ b.val = signOf b := by
  have hb : b.val = 0 ∧ b = 0 ∨ b.val = 1 ∧ b = 1 := by revert b; decide
  rcases hb with ⟨hv, hb⟩ | ⟨hv, hb⟩
  · rw [hv, pow_zero, hb, signOf, if_pos rfl]
  · rw [hv, pow_one, hb, signOf, if_neg (by decide)]

/-- **`H` on the carrier IS the Walsh transform of the amplitude.** `applyHFiner k` on bit `k` sends the
amplitude function `w ↦ ampCore S w` to its single-bit Walsh transform — the character-sum Hadamard computes
the Walsh transform, at the level of `ampCore` (via the branch-evaluation `hBranch_eval`). Frame-pure. -/
theorem ampCore_applyHFiner_eq_walsh {n : ℕ} (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m)
    (w : Fin n → ZMod 2) :
    ampCore (applyHFiner k S).m (applyHFiner k S).h (applyHFiner k S).Q (applyHFiner k S).c w
      = walshTransform k (fun w' => ampCore S.m S.h S.Q S.c w') w := by
  change ampCore S.m (S.h + 1) (hSumExp k S.Q) S.c w
      = walshTransform k (fun w' => ampCore S.m S.h S.Q S.c w') w
  rw [ampCore_applyHFiner_two_term, hBranch_eval hm, hBranch_eval hm, walshTransform]
  simp only [show ((0 : ZMod 2).val) = 0 from by decide, show ((1 : ZMod 2).val) = 1 from by decide,
    zero_mul, one_mul, pow_zero, neg_one_pow_val]

/-- **`H` preserves the native norm.** `carrierNormSq (applyHFiner k S) = carrierNormSq S`: the
character-sum Hadamard is an isometry for the Gauss-sum pairing. This is the load-bearing "`√2` disappears"
content — `H` is unitary *for the frame's own pairing*, an 𝔽₂ Parseval identity, importing no `FTQCLib.Hilbert`. -/
theorem carrierNormSq_applyHFiner {n : ℕ} (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m) :
    carrierNormSq (applyHFiner k S) = carrierNormSq S := by
  unfold carrierNormSq
  rw [Finset.sum_congr rfl
    (fun w _ => congrArg Complex.normSq (ampCore_applyHFiner_eq_walsh k S hm w))]
  exact walsh_normSq_isometry k (fun w' => ampCore S.m S.h S.Q S.c w')

/-! ## A diagonal gate preserves the native norm (unit-modulus phase) -/

/-- **A diagonal gate multiplies the amplitude by a unit-modulus phase.** `applyDiagSum S D` on the free
block scales `ampCore` pointwise by `exp(i·realPhase D w)` — the renamed `D` reads only the free
coordinates, so its phase is constant in the summation variables and factors out of the Gauss sum. -/
theorem ampCore_applyDiagSum {n : ℕ} (S : KernelSumState n) (D : DiagPhase n S.m)
    (w : Fin n → ZMod 2) :
    ampCore (applyDiagSum S D).m (applyDiagSum S D).h (applyDiagSum S D).Q (applyDiagSum S D).c w
      = Complex.exp (Complex.I * (DiagPhase.realPhase D w : ℂ)) * ampCore S.m S.h S.Q S.c w := by
  change ampCore S.m S.h (S.Q + MvPolynomial.rename (Fin.castAdd S.h) D) S.c w
      = Complex.exp (Complex.I * (DiagPhase.realPhase D w : ℂ)) * ampCore S.m S.h S.Q S.c w
  unfold ampCore
  have hterm : ∀ y : Fin S.h → ZMod 2,
      Complex.exp (Complex.I * (DiagPhase.realPhase
          (S.Q + MvPolynomial.rename (Fin.castAdd S.h) D) (Fin.append w y) : ℂ))
        = Complex.exp (Complex.I * (DiagPhase.realPhase D w : ℂ))
          * Complex.exp (Complex.I * (DiagPhase.realPhase S.Q (Fin.append w y) : ℂ)) := by
    intro y
    rw [exp_realPhase_add, realPhase_rename_castAdd, mul_comm]
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum]
  ring

/-- `|exp(i·θ)|² = 1` for real `θ`. -/
theorem normSq_exp_I_real (θ : ℝ) : Complex.normSq (Complex.exp (Complex.I * (θ : ℂ))) = 1 := by
  rw [mul_comm, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- **A diagonal gate preserves the native norm.** `carrierNormSq (applyDiagSum S D) =
carrierNormSq S`: `R_z` and every diagonal gate is an isometry for the Gauss-sum pairing, since it scales
each amplitude by a unit-modulus phase. -/
theorem carrierNormSq_applyDiagSum {n : ℕ} (S : KernelSumState n) (D : DiagPhase n S.m) :
    carrierNormSq (applyDiagSum S D) = carrierNormSq S := by
  unfold carrierNormSq
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [ampCore_applyDiagSum, Complex.normSq_mul, normSq_exp_I_real, one_mul]

/-! ## `H` contributes zero to the approximation error

The telescoping ingredient: the Walsh transform is a *linear* isometry, so it preserves the pairing
**distance** between two amplitude functions, not merely each norm. In a word `… H … H …` versus its dyadic
approximant, the two share identical `H` layers, so each `H` layer leaves the distance unchanged — it costs
nothing. The `√2`-per-`H` toll of the max-row-sum measure is gone: in the native pairing an `H` layer is
free, and only the `R_z`-vs-dyadic-`R_z` layers contribute their arc `≤ π/2^m`. -/

/-- **`H` preserves the native pairing-distance.** `Σ_w |Wf(w) − Wg(w)|² = Σ_w |f(w) − g(w)|²` — the Walsh
transform is a linear isometry, so an `H` layer common to a word and its approximant contributes `0` to the
error. This is the frame-native `‖H − H‖ = 0` of the operator telescope, with no Hilbert space. -/
theorem walsh_dist_isometry (k : Fin n) (f g : (Fin n → ZMod 2) → ℂ) :
    ∑ w : Fin n → ZMod 2, Complex.normSq (walshTransform k f w - walshTransform k g w)
      = ∑ w : Fin n → ZMod 2, Complex.normSq (f w - g w) := by
  have hlin : ∀ w, walshTransform k f w - walshTransform k g w
      = walshTransform k (fun w' => f w' - g w') w := by
    intro w; unfold walshTransform; ring
  simp_rw [hlin]
  exact walsh_normSq_isometry k (fun w' => f w' - g w')

/-- **`H` on the carrier contributes zero error (word form).** The native pairing-distance between
`applyHFiner k S` and `applyHFiner k T` equals that between `S` and `T` (both at `1 ≤ m`): applying the same
`H` to both sides of an approximation leaves the error untouched. -/
theorem carrier_dist_applyHFiner {n : ℕ} (k : Fin n) (S T : KernelSumState n)
    (hmS : 1 ≤ S.m) (hmT : 1 ≤ T.m) :
    ∑ w : Fin n → ZMod 2, Complex.normSq
        (ampCore (applyHFiner k S).m (applyHFiner k S).h (applyHFiner k S).Q (applyHFiner k S).c w
          - ampCore (applyHFiner k T).m (applyHFiner k T).h (applyHFiner k T).Q (applyHFiner k T).c w)
      = ∑ w : Fin n → ZMod 2, Complex.normSq
          (ampCore S.m S.h S.Q S.c w - ampCore T.m T.h T.Q T.c w) := by
  rw [Finset.sum_congr rfl (fun w _ => by
    rw [ampCore_applyHFiner_eq_walsh k S hmS w, ampCore_applyHFiner_eq_walsh k T hmT w])]
  exact walsh_dist_isometry k (fun w' => ampCore S.m S.h S.Q S.c w')
    (fun w' => ampCore T.m T.h T.Q T.c w')

/-! ## The per-layer error accounting: `H` free, `R_z` pays its chord

The native squared-distance between two carrier states, and the two facts that drive the telescoping: an `H`
layer common to both sides leaves the distance unchanged (free), and an `R_z` layer with two different angles
on a common state contributes exactly its phase chord — bounded by the arc `π/2^m` via `rz_dyadic_approx`. -/

/-- The frame-native **squared distance** of two carrier states: `Σ_w |ampCore S w − ampCore T w|²`, the
Gauss-sum pairing's `‖S − T‖²`. -/
noncomputable def carrierDistSq (S T : KernelSumState n) : ℝ :=
  ∑ w : Fin n → ZMod 2,
    Complex.normSq (ampCore S.m S.h S.Q S.c w - ampCore T.m T.h T.Q T.c w)

/-- **An `H` layer is free.** The native distance between `applyHFiner k S` and `applyHFiner k T` equals that
between `S` and `T` — `H`, common to a word and its approximant, contributes `0` to the error. -/
theorem carrierDistSq_applyHFiner {n : ℕ} (k : Fin n) (S T : KernelSumState n)
    (hmS : 1 ≤ S.m) (hmT : 1 ≤ T.m) :
    carrierDistSq (applyHFiner k S) (applyHFiner k T) = carrierDistSq S T :=
  carrier_dist_applyHFiner k S T hmS hmT

/-- The amplitude difference of two diagonal gates on a common state: `(exp(iθ₁) − exp(iθ₂))·ampCore S`. -/
theorem ampCore_applyDiagSum_sub {n : ℕ} (S : KernelSumState n) (D₁ D₂ : DiagPhase n S.m)
    (w : Fin n → ZMod 2) :
    ampCore (applyDiagSum S D₁).m (applyDiagSum S D₁).h (applyDiagSum S D₁).Q (applyDiagSum S D₁).c w
        - ampCore (applyDiagSum S D₂).m (applyDiagSum S D₂).h (applyDiagSum S D₂).Q (applyDiagSum S D₂).c w
      = (Complex.exp (Complex.I * (DiagPhase.realPhase D₁ w : ℂ))
          - Complex.exp (Complex.I * (DiagPhase.realPhase D₂ w : ℂ)))
        * ampCore S.m S.h S.Q S.c w := by
  rw [ampCore_applyDiagSum, ampCore_applyDiagSum]; ring

/-- **An `R_z` layer pays its chord.** Two diagonal gates `D₁, D₂` on a common state `S` are apart by their
phase chord: `carrierDistSq ≤ c · carrierNormSq S`, where `c` bounds `|exp(iθ₁) − exp(iθ₂)|²` on every input.
Fed the arc bound `π/2^m` (from `rz_dyadic_approx`) this is the per-`R_z`-layer error. -/
theorem carrierDistSq_applyDiagSum_le {n : ℕ} (S : KernelSumState n) (D₁ D₂ : DiagPhase n S.m)
    (c : ℝ) (hc : ∀ w, Complex.normSq (Complex.exp (Complex.I * (DiagPhase.realPhase D₁ w : ℂ))
        - Complex.exp (Complex.I * (DiagPhase.realPhase D₂ w : ℂ))) ≤ c) :
    carrierDistSq (applyDiagSum S D₁) (applyDiagSum S D₂) ≤ c * carrierNormSq S := by
  unfold carrierDistSq carrierNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun w _ => ?_)
  rw [ampCore_applyDiagSum_sub, Complex.normSq_mul]
  exact mul_le_mul_of_nonneg_right (hc w) (Complex.normSq_nonneg _)

/-! ## The finite ℓ² triangle inequality, native (no `EuclideanSpace`)

Minkowski for the Gauss-sum pairing, hand-built from Mathlib's discrete Cauchy–Schwarz
(`Finset.sum_mul_sq_le_sq_mul_sq`) — importing no `EuclideanSpace`/`PiLp`, so the frame's own pairing is
never definitionally identified with the Hilbert `QState` geometry. This is what lets the per-layer error
accounting telescope over a whole word. -/

/-- `z.re ≤ √(normSq z)`. -/
theorem re_le_sqrt_normSq (z : ℂ) : z.re ≤ Real.sqrt (Complex.normSq z) := by
  calc z.re ≤ |z.re| := le_abs_self _
    _ = Real.sqrt (z.re ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (Complex.normSq z) := by
        apply Real.sqrt_le_sqrt
        rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg z.im]

/-- **Finite ℓ² Cauchy–Schwarz on the amplitude functions (native).** `Σ_w Re(f w · conj(g w)) ≤
√(Σ|f|²)·√(Σ|g|²)` — from Mathlib's real discrete Cauchy–Schwarz, no inner-product space. -/
theorem carrier_cauchy_schwarz (f g : (Fin n → ZMod 2) → ℂ) :
    (∑ w : Fin n → ZMod 2, (f w * (starRingEnd ℂ) (g w)).re)
      ≤ Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (f w))
        * Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (g w)) := by
  have hA0 : 0 ≤ ∑ w : Fin n → ZMod 2, Complex.normSq (f w) :=
    Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg _)
  have hterm : ∀ w, (f w * (starRingEnd ℂ) (g w)).re
      ≤ Real.sqrt (Complex.normSq (f w)) * Real.sqrt (Complex.normSq (g w)) := by
    intro w
    refine (re_le_sqrt_normSq _).trans ?_
    rw [Complex.normSq_mul, Complex.normSq_conj, Real.sqrt_mul (Complex.normSq_nonneg _)]
  refine (Finset.sum_le_sum (fun w _ => hterm w)).trans ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → ZMod 2))
    (fun w => Real.sqrt (Complex.normSq (f w))) (fun w => Real.sqrt (Complex.normSq (g w)))
  rw [Finset.sum_congr rfl (fun w _ => Real.sq_sqrt (Complex.normSq_nonneg (f w))),
    Finset.sum_congr rfl (fun w _ => Real.sq_sqrt (Complex.normSq_nonneg (g w)))] at hcs
  have hsum0 : 0 ≤ ∑ w : Fin n → ZMod 2,
      Real.sqrt (Complex.normSq (f w)) * Real.sqrt (Complex.normSq (g w)) :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc (∑ w : Fin n → ZMod 2, Real.sqrt (Complex.normSq (f w)) * Real.sqrt (Complex.normSq (g w)))
      = Real.sqrt ((∑ w : Fin n → ZMod 2,
          Real.sqrt (Complex.normSq (f w)) * Real.sqrt (Complex.normSq (g w))) ^ 2) :=
        (Real.sqrt_sq hsum0).symm
    _ ≤ Real.sqrt ((∑ w : Fin n → ZMod 2, Complex.normSq (f w))
          * ∑ w : Fin n → ZMod 2, Complex.normSq (g w)) := Real.sqrt_le_sqrt hcs
    _ = _ := Real.sqrt_mul hA0 _

/-- **Finite ℓ² Minkowski / triangle inequality (native).** `√(Σ|f+g|²) ≤ √(Σ|f|²) + √(Σ|g|²)`. Built by
expanding the square and applying `carrier_cauchy_schwarz` — no `EuclideanSpace`. -/
theorem carrier_minkowski (f g : (Fin n → ZMod 2) → ℂ) :
    Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (f w + g w))
      ≤ Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (f w))
        + Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (g w)) := by
  have hA0 : 0 ≤ ∑ w : Fin n → ZMod 2, Complex.normSq (f w) :=
    Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg _)
  have hB0 : 0 ≤ ∑ w : Fin n → ZMod 2, Complex.normSq (g w) :=
    Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg _)
  have hexp : (∑ w : Fin n → ZMod 2, Complex.normSq (f w + g w))
      = (∑ w : Fin n → ZMod 2, Complex.normSq (f w))
        + (∑ w : Fin n → ZMod 2, Complex.normSq (g w))
        + 2 * (∑ w : Fin n → ZMod 2, (f w * (starRingEnd ℂ) (g w)).re) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => by rw [Complex.normSq_add])
  rw [hexp]
  have hle : (∑ w : Fin n → ZMod 2, Complex.normSq (f w))
        + (∑ w : Fin n → ZMod 2, Complex.normSq (g w))
        + 2 * (∑ w : Fin n → ZMod 2, (f w * (starRingEnd ℂ) (g w)).re)
      ≤ (Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (f w))
          + Real.sqrt (∑ w : Fin n → ZMod 2, Complex.normSq (g w))) ^ 2 := by
    nlinarith [carrier_cauchy_schwarz f g, Real.sq_sqrt hA0, Real.sq_sqrt hB0,
      Real.sqrt_nonneg (∑ w : Fin n → ZMod 2, Complex.normSq (f w)),
      Real.sqrt_nonneg (∑ w : Fin n → ZMod 2, Complex.normSq (g w))]
  refine (Real.sqrt_le_sqrt hle).trans ?_
  rw [Real.sqrt_sq (by positivity)]

/-- The frame-native **distance** of two carrier states: `√(carrierDistSq S T)`. -/
noncomputable def carrierDist (S T : KernelSumState n) : ℝ := Real.sqrt (carrierDistSq S T)

/-- **The native distance is a genuine metric (triangle inequality).** `carrierDist S U ≤ carrierDist S T
+ carrierDist T U`, from `carrier_minkowski` — so the per-layer error accounting telescopes over words. -/
theorem carrierDist_triangle (S T U : KernelSumState n) :
    carrierDist S U ≤ carrierDist S T + carrierDist T U := by
  unfold carrierDist carrierDistSq
  have hmink := carrier_minkowski
    (fun w => ampCore S.m S.h S.Q S.c w - ampCore T.m T.h T.Q T.c w)
    (fun w => ampCore T.m T.h T.Q T.c w - ampCore U.m U.h U.Q U.c w)
  have heq : (∑ w : Fin n → ZMod 2,
        Complex.normSq (ampCore S.m S.h S.Q S.c w - ampCore U.m U.h U.Q U.c w))
      = ∑ w : Fin n → ZMod 2, Complex.normSq
          ((ampCore S.m S.h S.Q S.c w - ampCore T.m T.h T.Q T.c w)
            + (ampCore T.m T.h T.Q T.c w - ampCore U.m U.h U.Q U.c w)) := by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    congr 1; ring
  rw [heq]
  exact hmink

/-! ## The amplitude-level telescope — shared core for both composites

The composite word-bounds live on amplitude functions (the ideal `R_z(θ)` word is not a carrier state), so
the H layer is `walshTransform` and the `R_z` layer is `phaseMul` — both acting directly on `(Fin n → ZMod
2) → ℂ`. `ampDist`/`ampNorm` are the native ℓ² distance/norm; the layers are isometries (H free via
`walsh_*_isometry`; a phase is unit-modulus), and two phases differ by their chord. -/

/-- The native ℓ² norm of an amplitude function. -/
noncomputable def ampNorm (f : (Fin n → ZMod 2) → ℂ) : ℝ := Real.sqrt (∑ w, Complex.normSq (f w))

/-- The native ℓ² distance of two amplitude functions (`carrierDist S T = ampDist (ampFun S) (ampFun T)`). -/
noncomputable def ampDist (f g : (Fin n → ZMod 2) → ℂ) : ℝ :=
  Real.sqrt (∑ w, Complex.normSq (f w - g w))

/-- Triangle inequality for `ampDist` (from the native Minkowski). -/
theorem ampDist_triangle (f g h : (Fin n → ZMod 2) → ℂ) : ampDist f h ≤ ampDist f g + ampDist g h := by
  unfold ampDist
  rw [show (∑ w, Complex.normSq (f w - h w))
      = ∑ w, Complex.normSq ((f w - g w) + (g w - h w)) from
    Finset.sum_congr rfl (fun w _ => by congr 1; ring)]
  exact carrier_minkowski (fun w => f w - g w) (fun w => g w - h w)

/-- **H is free in `ampDist`** — the Walsh transform is a distance isometry. -/
theorem ampDist_walsh (k : Fin n) (f g : (Fin n → ZMod 2) → ℂ) :
    ampDist (walshTransform k f) (walshTransform k g) = ampDist f g := by
  unfold ampDist; rw [walsh_dist_isometry]

/-- **H preserves `ampNorm`.** -/
theorem ampNorm_walsh (k : Fin n) (f : (Fin n → ZMod 2) → ℂ) :
    ampNorm (walshTransform k f) = ampNorm f := by
  unfold ampNorm; rw [walsh_normSq_isometry]

/-- The `R_z(θ)` layer on an amplitude function: multiply by the unit-modulus phase `exp(i·θ·w_i)`
(anchored form). -/
noncomputable def phaseMul (θ : ℝ) (i : Fin n) (f : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  fun w => Complex.exp (Complex.I * ((θ * (w i).val : ℝ) : ℂ)) * f w

theorem phaseMul_sub_self (θ₁ θ₂ : ℝ) (i : Fin n) (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) :
    phaseMul θ₁ i f w - phaseMul θ₂ i f w
      = (Complex.exp (Complex.I * ((θ₁ * (w i).val : ℝ) : ℂ))
          - Complex.exp (Complex.I * ((θ₂ * (w i).val : ℝ) : ℂ))) * f w := by
  unfold phaseMul; ring

/-- **A common phase layer is free in `ampDist`.** -/
theorem ampDist_phaseMul_same (θ : ℝ) (i : Fin n) (f g : (Fin n → ZMod 2) → ℂ) :
    ampDist (phaseMul θ i f) (phaseMul θ i g) = ampDist f g := by
  unfold ampDist
  refine congrArg Real.sqrt (Finset.sum_congr rfl (fun w _ => ?_))
  rw [show phaseMul θ i f w - phaseMul θ i g w
      = Complex.exp (Complex.I * ((θ * (w i).val : ℝ) : ℂ)) * (f w - g w) from by
        unfold phaseMul; ring,
    Complex.normSq_mul, normSq_exp_I_real, one_mul]

/-- **A phase layer preserves `ampNorm`.** -/
theorem ampNorm_phaseMul (θ : ℝ) (i : Fin n) (f : (Fin n → ZMod 2) → ℂ) :
    ampNorm (phaseMul θ i f) = ampNorm f := by
  unfold ampNorm phaseMul
  refine congrArg Real.sqrt (Finset.sum_congr rfl (fun w _ => ?_))
  rw [Complex.normSq_mul, normSq_exp_I_real, one_mul]

/-- **Two phase layers differ by their chord.** `ampDist (phaseMul θ₁ · f) (phaseMul θ₂ · f) ≤ √c · ampNorm
f`, where `c` bounds the phase chord `|exp(iθ₁·w_i) − exp(iθ₂·w_i)|²` on every input. Fed the arc bound this
is the per-`R_z`-layer error. -/
theorem ampDist_phaseMul_le (θ₁ θ₂ : ℝ) (i : Fin n) (f : (Fin n → ZMod 2) → ℂ) (c : ℝ)
    (hc : ∀ w : Fin n → ZMod 2, Complex.normSq
        (Complex.exp (Complex.I * ((θ₁ * (w i).val : ℝ) : ℂ))
          - Complex.exp (Complex.I * ((θ₂ * (w i).val : ℝ) : ℂ))) ≤ c) :
    ampDist (phaseMul θ₁ i f) (phaseMul θ₂ i f) ≤ Real.sqrt c * ampNorm f := by
  have hc0 : 0 ≤ c := le_trans (Complex.normSq_nonneg _) (hc (fun _ => 0))
  unfold ampDist ampNorm
  rw [← Real.sqrt_mul hc0]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun w _ => ?_)
  rw [phaseMul_sub_self, Complex.normSq_mul]
  exact mul_le_mul_of_nonneg_right (hc w) (Complex.normSq_nonneg _)

/-! ## The chord ≤ arc bound, and the per-`R_z`-layer error from the frame's dyadic approximation -/

/-- **Chord ≤ arc.** `‖exp(i·a) − exp(i·b)‖ ≤ δ` whenever `|a − b − 2πk| ≤ δ`. Self-contained (copied from
`SU2CoverageLinfty` to keep this file's imports minimal). -/
theorem chord_le_arc {a b δ : ℝ} (k : ℤ) (hk : |a - b - 2 * Real.pi * k| ≤ δ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ δ := by
  have hfac : Complex.exp (Complex.I * (b : ℂ))
        * (Complex.exp (Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)) - 1)
      = Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    rw [show Complex.I * (b : ℂ) + Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)
          = Complex.I * (a : ℂ) + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hnorm1 : ‖Complex.exp (Complex.I * (b : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [← hfac, norm_mul, hnorm1, one_mul]
  calc ‖Complex.exp (Complex.I * ((a - b - 2 * Real.pi * k : ℝ) : ℂ)) - 1‖
      ≤ ‖(a - b - 2 * Real.pi * k : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a - b - 2 * Real.pi * k| := Real.norm_eq_abs _
    _ ≤ δ := hk

/-- **The per-`R_z`-layer chord bound from the frame's dyadic approximation.** For every angle `θ` and
precision `m` there is a coefficient `c` whose dyadic phase `2π·c.val/2^m` is within chord `π/2^m` of `θ` on
every input bit — the hypothesis `ampDist_phaseMul_le` consumes, `c` and its accuracy straight from
`rz_dyadic_approx`. -/
theorem phaseMul_chord (θ : ℝ) (m : ℕ) :
    ∃ c : ZMod (2 ^ m), ∀ w : Fin 1 → ZMod 2, Complex.normSq
        (Complex.exp (Complex.I * ((2 * Real.pi * (c.val : ℝ) / 2 ^ m * (w 0).val : ℝ) : ℂ))
          - Complex.exp (Complex.I * ((θ * (w 0).val : ℝ) : ℂ))) ≤ (Real.pi / 2 ^ m) ^ 2 := by
  obtain ⟨c, hc⟩ := DiagPhase.rz_dyadic_approx θ (0 : Fin 1) m
  refine ⟨c, fun w => ?_⟩
  have hval : (w 0).val = 0 ∨ (w 0).val = 1 := by have := (w 0).val_lt; omega
  rcases hval with h0 | h1
  · rw [h0]
    simp only [Nat.cast_zero, mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self,
      map_zero]
    positivity
  · obtain ⟨k, hk⟩ := hc w
    rw [DiagPhase.realPhase_linear, h1, Nat.cast_one] at hk
    rw [h1, Nat.cast_one, mul_one, mul_one, Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _)
    refine chord_le_arc k ?_
    rw [one_mul] at hk
    convert hk using 2
    ring

/-! ## Coverage of the ideal `R_z(θ)` Euler word -/

open Real in
/-- **Coverage of the ideal.** For every Euler angles `α, β, γ` and precision `m` there
are dyadic tower coefficients `a, b, c` — chosen from the angles alone — whose frame word
`R_z(2πa/2^m)·H·R_z(2πb/2^m)·H·R_z(2πc/2^m)` is within native ℓ² distance `3·π/2^m·‖f₀‖` of the *exact*
`R_z(α)·H·R_z(β)·H·R_z(γ)` word **uniformly over every base amplitude `f₀`** — the frame covers the
SU(2) boundary in its own Gauss-sum metric. (Quantifier order matters and is the strong one:
`∃ a b c, ∀ f₀`; the order `∀ f₀, ∃ a b c` would let the coefficients depend on the base
amplitude, which is strictly weaker than the approximation claim.) Tighter
than the max-row-sum `su2_coverage`'s `6·π/2^m` because H is a genuine isometry here (H layers are free). The
ideal word is an amplitude function, not a carrier state, so the bound lives one level below `carrierDist`. -/
theorem coverage_of_ideal (α β γ : ℝ) (m : ℕ) :
    ∃ a b c : ZMod (2 ^ m), ∀ f₀ : (Fin 1 → ZMod 2) → ℂ,
      ampDist
        (phaseMul (2 * Real.pi * (a.val : ℝ) / 2 ^ m) 0
          (walshTransform 0 (phaseMul (2 * Real.pi * (b.val : ℝ) / 2 ^ m) 0
            (walshTransform 0 (phaseMul (2 * Real.pi * (c.val : ℝ) / 2 ^ m) 0 f₀)))))
        (phaseMul α 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
      ≤ 3 * (Real.pi / 2 ^ m) * ampNorm f₀ := by
  obtain ⟨a, ha⟩ := phaseMul_chord α m
  obtain ⟨b, hb⟩ := phaseMul_chord β m
  obtain ⟨c, hc⟩ := phaseMul_chord γ m
  refine ⟨a, b, c, fun f₀ => ?_⟩
  set A := 2 * Real.pi * (a.val : ℝ) / 2 ^ m with hA
  set B := 2 * Real.pi * (b.val : ℝ) / 2 ^ m with hB
  set C := 2 * Real.pi * (c.val : ℝ) / 2 ^ m with hC
  have hstep1 :
      ampDist (phaseMul A 0 (walshTransform 0 (phaseMul B 0 (walshTransform 0 (phaseMul C 0 f₀)))))
              (phaseMul A 0 (walshTransform 0 (phaseMul B 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
        ≤ Real.pi / 2 ^ m * ampNorm f₀ := by
    rw [ampDist_phaseMul_same, ampDist_walsh, ampDist_phaseMul_same, ampDist_walsh]
    have h := ampDist_phaseMul_le C γ 0 f₀ ((Real.pi / 2 ^ m) ^ 2) hc
    rwa [Real.sqrt_sq (by positivity)] at h
  have hstep2 :
      ampDist (phaseMul A 0 (walshTransform 0 (phaseMul B 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
              (phaseMul A 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
        ≤ Real.pi / 2 ^ m * ampNorm f₀ := by
    rw [ampDist_phaseMul_same, ampDist_walsh]
    have h := ampDist_phaseMul_le B β 0 (walshTransform 0 (phaseMul γ 0 f₀)) ((Real.pi / 2 ^ m) ^ 2) hb
    rwa [Real.sqrt_sq (by positivity), ampNorm_walsh, ampNorm_phaseMul] at h
  have hstep3 :
      ampDist (phaseMul A 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
              (phaseMul α 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
        ≤ Real.pi / 2 ^ m * ampNorm f₀ := by
    have h := ampDist_phaseMul_le A α 0
      (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))) ((Real.pi / 2 ^ m) ^ 2) ha
    rwa [Real.sqrt_sq (by positivity), ampNorm_walsh, ampNorm_phaseMul, ampNorm_walsh,
      ampNorm_phaseMul] at h
  have ht1 := ampDist_triangle
    (phaseMul A 0 (walshTransform 0 (phaseMul B 0 (walshTransform 0 (phaseMul C 0 f₀)))))
    (phaseMul A 0 (walshTransform 0 (phaseMul B 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
    (phaseMul α 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
  have ht2 := ampDist_triangle
    (phaseMul A 0 (walshTransform 0 (phaseMul B 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
    (phaseMul A 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
    (phaseMul α 0 (walshTransform 0 (phaseMul β 0 (walshTransform 0 (phaseMul γ 0 f₀)))))
  have hN : (0 : ℝ) ≤ ampNorm f₀ := Real.sqrt_nonneg _
  nlinarith [hstep1, hstep2, hstep3, ht1, ht2]

/-- The single-qubit Euler word `R_z(θ₁)·H·R_z(θ₂)·H·R_z(θ₃)` on an amplitude function. -/
noncomputable def eulerWord (θ₁ θ₂ θ₃ : ℝ) (f₀ : (Fin 1 → ZMod 2) → ℂ) : (Fin 1 → ZMod 2) → ℂ :=
  phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul θ₃ 0 f₀))))

open Real in
/-- **Coverage of the ideal, packaged.** `coverage_of_ideal` restated with `eulerWord` — same
strong quantifier order: the coefficients are uniform over the base amplitude. -/
theorem coverage_euler (α β γ : ℝ) (m : ℕ) :
    ∃ a b c : ZMod (2 ^ m), ∀ f₀ : (Fin 1 → ZMod 2) → ℂ,
      ampDist (eulerWord (2 * Real.pi * (a.val : ℝ) / 2 ^ m) (2 * Real.pi * (b.val : ℝ) / 2 ^ m)
          (2 * Real.pi * (c.val : ℝ) / 2 ^ m) f₀) (eulerWord α β γ f₀)
        ≤ 3 * (Real.pi / 2 ^ m) * ampNorm f₀ := by
  unfold eulerWord; exact coverage_of_ideal α β γ m

open Real in
/-- **Concrete `2π/3` coverage, m = 2, 3, 4:** native ℓ² distance `≤ 3·(π/2^m)·‖f₀‖` — i.e. `3π/4, 3π/8,
3π/16` times `‖f₀‖`, exactly HALF the max-row-sum `su2_coverage`/`SU2Table.example_2pi3_m*` bound
(`6·π/2^m = 3π/2, 3π/4, 3π/8`), because H is an isometry in this native metric. -/
theorem cover_2pi3_m2 :
    ∃ a b c : ZMod (2 ^ 2), ∀ f₀ : (Fin 1 → ZMod 2) → ℂ,
      ampDist (eulerWord (2 * Real.pi * (a.val : ℝ) / 2 ^ 2) (2 * Real.pi * (b.val : ℝ) / 2 ^ 2)
          (2 * Real.pi * (c.val : ℝ) / 2 ^ 2) f₀)
        (eulerWord (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) f₀)
        ≤ 3 * (Real.pi / 2 ^ 2) * ampNorm f₀ :=
  coverage_euler (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) 2

open Real in
theorem cover_2pi3_m3 :
    ∃ a b c : ZMod (2 ^ 3), ∀ f₀ : (Fin 1 → ZMod 2) → ℂ,
      ampDist (eulerWord (2 * Real.pi * (a.val : ℝ) / 2 ^ 3) (2 * Real.pi * (b.val : ℝ) / 2 ^ 3)
          (2 * Real.pi * (c.val : ℝ) / 2 ^ 3) f₀)
        (eulerWord (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) f₀)
        ≤ 3 * (Real.pi / 2 ^ 3) * ampNorm f₀ :=
  coverage_euler (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) 3

open Real in
theorem cover_2pi3_m4 :
    ∃ a b c : ZMod (2 ^ 4), ∀ f₀ : (Fin 1 → ZMod 2) → ℂ,
      ampDist (eulerWord (2 * Real.pi * (a.val : ℝ) / 2 ^ 4) (2 * Real.pi * (b.val : ℝ) / 2 ^ 4)
          (2 * Real.pi * (c.val : ℝ) / 2 ^ 4) f₀)
        (eulerWord (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) f₀)
        ≤ 3 * (Real.pi / 2 ^ 4) * ampNorm f₀ :=
  coverage_euler (2 * Real.pi / 3) (2 * Real.pi / 3) (2 * Real.pi / 3) 4

/-! ## The Euler-word Lipschitz bound and the carrier connection (precision comparison)

The general amplitude telescope: two Euler words on the same base are apart by the sum of their per-layer
phase chords, H layers free. `coverage_of_ideal` is the dyadic-vs-ideal instance; the dyadic-vs-dyadic
instance is the precision/refinement (truncation) story. `carrierDist_eq_ampDist` makes these genuine
`carrierDist` statements between carrier states. -/

/-- **The native distance is the amplitude distance of the carrier's amplitudes.** -/
theorem carrierDist_eq_ampDist (S T : KernelSumState n) :
    carrierDist S T = ampDist (fun w => ampCore S.m S.h S.Q S.c w) (fun w => ampCore T.m T.h T.Q T.c w) :=
  rfl

/-- **Euler-word Lipschitz bound.** Two Euler words on a common base `f₀` are within
`(δ₁+δ₂+δ₃)·‖f₀‖` when their per-layer phase chords are bounded by `δ₁,δ₂,δ₃`. H layers contribute nothing.
Both composites are instances: `θ`-vs-dyadic (coverage) and dyadic-vs-dyadic (precision comparison). -/
theorem eulerWord_ampDist_le (θ₁ θ₂ θ₃ φ₁ φ₂ φ₃ : ℝ) (δ₁ δ₂ δ₃ : ℝ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ₃ : 0 ≤ δ₃) (f₀ : (Fin 1 → ZMod 2) → ℂ)
    (h₁ : ∀ w : Fin 1 → ZMod 2, Complex.normSq
      (Complex.exp (Complex.I * ((θ₁ * (w 0).val : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((φ₁ * (w 0).val : ℝ) : ℂ))) ≤ δ₁ ^ 2)
    (h₂ : ∀ w : Fin 1 → ZMod 2, Complex.normSq
      (Complex.exp (Complex.I * ((θ₂ * (w 0).val : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((φ₂ * (w 0).val : ℝ) : ℂ))) ≤ δ₂ ^ 2)
    (h₃ : ∀ w : Fin 1 → ZMod 2, Complex.normSq
      (Complex.exp (Complex.I * ((θ₃ * (w 0).val : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((φ₃ * (w 0).val : ℝ) : ℂ))) ≤ δ₃ ^ 2) :
    ampDist (eulerWord θ₁ θ₂ θ₃ f₀) (eulerWord φ₁ φ₂ φ₃ f₀) ≤ (δ₁ + δ₂ + δ₃) * ampNorm f₀ := by
  unfold eulerWord
  have hstep1 :
      ampDist (phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul θ₃ 0 f₀)))))
              (phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
        ≤ δ₃ * ampNorm f₀ := by
    rw [ampDist_phaseMul_same, ampDist_walsh, ampDist_phaseMul_same, ampDist_walsh]
    have h := ampDist_phaseMul_le θ₃ φ₃ 0 f₀ (δ₃ ^ 2) h₃
    rwa [Real.sqrt_sq hδ₃] at h
  have hstep2 :
      ampDist (phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
              (phaseMul θ₁ 0 (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
        ≤ δ₂ * ampNorm f₀ := by
    rw [ampDist_phaseMul_same, ampDist_walsh]
    have h := ampDist_phaseMul_le θ₂ φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)) (δ₂ ^ 2) h₂
    rwa [Real.sqrt_sq hδ₂, ampNorm_walsh, ampNorm_phaseMul] at h
  have hstep3 :
      ampDist (phaseMul θ₁ 0 (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
              (phaseMul φ₁ 0 (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
        ≤ δ₁ * ampNorm f₀ := by
    have h := ampDist_phaseMul_le θ₁ φ₁ 0
      (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))) (δ₁ ^ 2) h₁
    rwa [Real.sqrt_sq hδ₁, ampNorm_walsh, ampNorm_phaseMul, ampNorm_walsh, ampNorm_phaseMul] at h
  have ht1 := ampDist_triangle
    (phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul θ₃ 0 f₀)))))
    (phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
    (phaseMul φ₁ 0 (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
  have ht2 := ampDist_triangle
    (phaseMul θ₁ 0 (walshTransform 0 (phaseMul θ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
    (phaseMul θ₁ 0 (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
    (phaseMul φ₁ 0 (walshTransform 0 (phaseMul φ₂ 0 (walshTransform 0 (phaseMul φ₃ 0 f₀)))))
  have hN : (0 : ℝ) ≤ ampNorm f₀ := Real.sqrt_nonneg _
  nlinarith [hstep1, hstep2, hstep3, ht1, ht2]

open Real in
/-- **Precision/truncation (concrete resource cost).** Dropping the finest bit of the `m = 4` `2π/3`
approximant (innermost coefficient `5 → 4`, binary `101 → 100`) shifts that `R_z` angle by `2π/16 = π/8`, so
the full word and the truncated word are within `(π/8)·‖f₀‖` in the native metric — the resource cost of the
dropped rung, the SU(2) analogue of F5's `truncated_2pi3_dist`. The other two layers are shared and free. -/
theorem precision_2pi3_truncation (θ₂ θ₃ : ℝ) (f₀ : (Fin 1 → ZMod 2) → ℂ) :
    ampDist (eulerWord (2 * Real.pi * 5 / 2 ^ 4) θ₂ θ₃ f₀)
        (eulerWord (2 * Real.pi * 4 / 2 ^ 4) θ₂ θ₃ f₀)
      ≤ Real.pi / 8 * ampNorm f₀ := by
  have key := eulerWord_ampDist_le (2 * Real.pi * 5 / 2 ^ 4) θ₂ θ₃ (2 * Real.pi * 4 / 2 ^ 4) θ₂ θ₃
    (Real.pi / 8) 0 0 (by positivity) le_rfl le_rfl f₀ ?_ ?_ ?_
  · simpa using key
  · intro w
    have hval : (w 0).val = 0 ∨ (w 0).val = 1 := by have := (w 0).val_lt; omega
    rcases hval with h0 | h1
    · rw [h0]; simp only [Nat.cast_zero, mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
        sub_self, map_zero]; positivity
    · rw [h1, Nat.cast_one, mul_one, mul_one, Complex.normSq_eq_norm_sq]
      apply pow_le_pow_left₀ (norm_nonneg _)
      refine chord_le_arc 0 ?_
      rw [show (2 * Real.pi * 5 / 2 ^ 4 - 2 * Real.pi * 4 / 2 ^ 4 - 2 * Real.pi * ((0 : ℤ) : ℝ))
          = Real.pi / 8 from by push_cast; ring, abs_of_nonneg (by positivity)]
  · intro w; simp only [sub_self, map_zero]; positivity
  · intro w; simp only [sub_self, map_zero]; positivity

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GaussSum
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Zero

set_option linter.style.longLine false

/-!
# The definite quadratic Gauss sign — the DFT-Vandermonde determinant proof (Schur / Murty–Pathak)

The definite value `g = √p` (p ≡ 1 mod 4) / `i√p` (p ≡ 3 mod 4). Route: the finite Fourier matrix
`A_{rs} = ω^{rs}` (a Vandermonde matrix in the nodes `ω^r`) has `Tr A = g`; its eigenvalues lie in
`√p·{1,i,−1,−i}`; the multiplicity split is pinned non-circularly by the eigenspace dimensions,
`|g|² = p`, and `det A` computed independently via the Vandermonde product (whose sign is the positivity
of a finite sine product).

The foundational algebra comes first: the DFT matrix, character-orthogonality as a geometric sum,
and `A² = p·P`, the identity from which the whole spectral structure follows.
-/

namespace ECCLib.GaussSign

open scoped BigOperators
open Matrix Finset

variable {p : ℕ} [Fact p.Prime] (ω : ℂ)

/-- The **finite Fourier matrix** `A_{rs} = ω^{rs}`, presented as the Vandermonde matrix in the nodes
`ω^r`. (`(vandermonde v) r s = (v r)^s`, so here `(ω^r)^s = ω^{rs}`.) -/
noncomputable def dftMatrix : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.vandermonde (fun r : Fin p => ω ^ (r : ℕ))

/-- The **reversal** matrix `P_{rs} = [p ∣ r+s]` (the permutation `x ↦ −x`). -/
def reversal (p : ℕ) : Matrix (Fin p) (Fin p) ℂ :=
  fun r s => if p ∣ ((r : ℕ) + (s : ℕ)) then 1 else 0

omit [Fact p.Prime] in
/-- **Character orthogonality as a geometric sum.** `∑_{t<p} (ω^k)^t = p` if `p ∣ k`, else `0`. -/
lemma geom_sum_pow (hω : IsPrimitiveRoot ω p) (k : ℕ) :
    ∑ t : Fin p, (ω ^ k) ^ (t : ℕ) = if p ∣ k then (p : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ k) ^ t)]
  by_cases hk : p ∣ k
  · have h1 : ω ^ k = 1 := (hω.pow_eq_one_iff_dvd k).mpr hk
    simp [h1, hk]
  · have hne : (ω ^ k) ≠ 1 := fun h => hk ((hω.pow_eq_one_iff_dvd k).mp h)
    have hp : (ω ^ k) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [geom_sum_eq hne p, hp, sub_self, zero_div, if_neg hk]

omit [Fact p.Prime] in
/-- **`A² = p·P`.** The Fourier matrix squares to `p` times the reversal, by orthogonality:
`(A²)_{rs} = ∑_t ω^{t(r+s)} = p·[p ∣ r+s]`. -/
theorem dftMatrix_sq (hω : IsPrimitiveRoot ω p) :
    (dftMatrix ω) * (dftMatrix ω) = (p : ℂ) • reversal p := by
  ext r s
  rw [Matrix.mul_apply]
  simp only [dftMatrix, Matrix.vandermonde_apply, Matrix.smul_apply, reversal, smul_eq_mul]
  have hsummand : ∀ t : Fin p,
      (ω ^ (r : ℕ)) ^ (t : ℕ) * (ω ^ (t : ℕ)) ^ (s : ℕ) = (ω ^ ((r : ℕ) + (s : ℕ))) ^ (t : ℕ) := by
    intro t
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    ring
  simp_rw [hsummand]
  rw [geom_sum_pow ω hω ((r : ℕ) + (s : ℕ))]
  split <;> simp

/-- The reversal condition in `ZMod p` terms: `p ∣ (r+s) ↔ (r+s : ZMod p) = 0`. This bridges the
`Fin p`-indexed divisibility (needed for the Vandermonde/`det`) to `ZMod p`, where the reversal is the
native negation `x ↦ −x`. -/
lemma reversal_apply_zmod (r s : Fin p) :
    reversal p r s = if ((r : ℕ) : ZMod p) + ((s : ℕ) : ZMod p) = 0 then (1 : ℂ) else 0 := by
  have h : (((r : ℕ) : ZMod p) + ((s : ℕ) : ZMod p) = 0) ↔ p ∣ ((r : ℕ) + (s : ℕ)) := by
    rw [← Nat.cast_add]; exact CharP.cast_eq_zero_iff (ZMod p) p _
  simp only [reversal]
  exact if_congr h.symm rfl rfl

/-- **The reversal is an involution: `P² = I`.** Reindexing the double sum to `ZMod p` (via the
bijection `s ↦ (s : ZMod p)`), the reversal is negation, so the product of indicators is supported on
the single point `s = −r`, and collapses to `[r = t]`. -/
theorem reversal_mul_self :
    reversal p * reversal p = (1 : Matrix (Fin p) (Fin p) ℂ) := by
  set φ : Fin p → ZMod p := fun i => ((i : ℕ) : ZMod p) with hφ
  have hφinj : Function.Injective φ := by
    intro i j h
    have hi : (φ i).val = (i : ℕ) := ZMod.val_cast_of_lt i.isLt
    have hj : (φ j).val = (j : ℕ) := ZMod.val_cast_of_lt j.isLt
    exact Fin.ext (by rw [← hi, ← hj, h])
  have hφbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [ZMod.card, Fintype.card_fin]⟩
  ext r t
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [reversal_apply_zmod]
  rw [Fintype.sum_bijective φ hφbij _
      (fun y : ZMod p => (if φ r + y = 0 then (1 : ℂ) else 0) * (if y + φ t = 0 then 1 else 0))
      (fun s => rfl)]
  rw [Finset.sum_eq_single (-φ r)]
  · have hcond : (-φ r + φ t = 0) ↔ (r = t) := by rw [neg_add_eq_zero]; exact hφinj.eq_iff
    rw [add_neg_cancel, if_pos rfl, one_mul]
    exact if_congr hcond rfl rfl
  · intro y _ hy
    rw [if_neg (fun h => hy (by linear_combination h : y = -φ r)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`A⁴ = p²·I`.** From `A² = p·P` and `P² = I`. This forces every eigenvalue `λ` of `A` to
satisfy `λ⁴ = p²`, i.e. `λ ∈ √p·{1, i, −1, −i}`. -/
theorem dftMatrix_pow_four (hω : IsPrimitiveRoot ω p) :
    (dftMatrix ω) ^ 4 = (p ^ 2 : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  simp only [pow_two, dftMatrix_sq ω hω]
  rw [smul_mul_assoc, mul_smul_comm, reversal_mul_self, smul_smul, ← pow_two]

/-- **Unitarity: `A · Aᴴ = p·I`** — the finite Fourier matrix is `√p` times a unitary (the Weil
`S = (0 −1; 1 0)` element is unitary). The conjugate of a root of unity is its inverse `ω^{p−1}`, so
`(A·Aᴴ)_{rs} = ∑_t ω^{t(r+(p−1)s)} = p·[r=s]` by character orthogonality. Consequently
`|det A|² = det(A·Aᴴ) = pᵖ`. Holds for any primitive `ω` (the definite-sign layers do not use it). -/
theorem dftMatrix_mul_conjTranspose (hω : IsPrimitiveRoot ω p) :
    (dftMatrix (p := p) ω) * (dftMatrix (p := p) ω)ᴴ = (p : ℂ) • (1 : Matrix (Fin p) (Fin p) ℂ) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hstar : star ω = ω ^ (p - 1) := by
    have h1 : ω ^ (p - 1) * ω = 1 := by rw [← pow_succ, Nat.sub_add_cancel hp1]; exact hω.pow_eq_one
    have hnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one (Fact.out : p.Prime).pos.ne'
    rw [show star ω = (starRingEnd ℂ) ω from rfl, ← Complex.inv_eq_conj hnorm]
    exact inv_eq_of_mul_eq_one_left h1
  ext r s
  rw [Matrix.mul_apply]
  simp only [dftMatrix, Matrix.conjTranspose_apply, Matrix.vandermonde_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have hsummand : ∀ t : Fin p, (ω ^ (r : ℕ)) ^ (t : ℕ) * star ((ω ^ (s : ℕ)) ^ (t : ℕ))
      = (ω ^ ((r : ℕ) + (p - 1) * (s : ℕ))) ^ (t : ℕ) := by
    intro t
    rw [star_pow, star_pow, hstar, ← mul_pow, ← pow_mul, ← pow_add]
  simp_rw [hsummand]
  rw [geom_sum_pow ω hω ((r : ℕ) + (p - 1) * (s : ℕ))]
  have hiff : p ∣ ((r : ℕ) + (p - 1) * (s : ℕ)) ↔ r = s := by
    rw [← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp1,
      Nat.cast_one, ZMod.natCast_self, zero_sub, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]
    constructor
    · intro h
      exact Fin.ext (by rw [← ZMod.val_cast_of_lt r.isLt, ← ZMod.val_cast_of_lt s.isLt, h])
    · intro h; rw [h]
  by_cases h : r = s
  · rw [if_pos (hiff.mpr h), if_pos h]; ring
  · rw [if_neg (fun hd => h (hiff.mp hd)), if_neg h]; ring

omit [Fact p.Prime] in
/-- **The trace: `Tr A = ∑_r ω^{r²}` — the quadratic Gauss sum.** This is Murty §2's anchor: the
sign of the Gauss sum is the sign of this matrix trace. -/
lemma dftMatrix_trace : (dftMatrix (p := p) ω).trace = ∑ r : Fin p, ω ^ ((r : ℕ) * (r : ℕ)) := by
  simp only [Matrix.trace, Matrix.diag_apply, dftMatrix, Matrix.vandermonde_apply]
  exact Finset.sum_congr rfl fun r _ => (pow_mul ω (r : ℕ) (r : ℕ)).symm

/-- **`Tr P = 1` for odd `p`.** The reversal `x ↦ −x` has a single fixed point (`x = 0`), since
`2x = 0` forces `x = 0` when `p ≠ 2`. -/
theorem reversal_trace (hp2 : p ≠ 2) : (reversal p).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag_apply, reversal_apply_zmod]
  rw [Finset.sum_eq_single (0 : Fin p)]
  · simp
  · intro r _ hr
    have hrne : (r : ℕ) ≠ 0 := fun h => hr (Fin.val_eq_zero_iff.mp h)
    have hφr : ((r : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p (r : ℕ)]
      exact fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hrne) hd) (not_le.mpr r.isLt)
    have h2 : (2 : ZMod p) ≠ 0 := by
      have h2' : ((2 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p 2]
        exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
      simpa using h2'
    rw [if_neg]
    intro h
    exact hφr ((mul_eq_zero.mp (by rw [two_mul]; exact h)).resolve_left h2)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`Tr(A²) = p` for odd `p`.** A `g`-free trace; combined with the spectral trace-power-sum it fixes
the multiplicity split `a+c = (p+1)/2`, `b+d = (p−1)/2`. -/
theorem dftMatrix_trace_sq (hω : IsPrimitiveRoot ω p) (hp2 : p ≠ 2) :
    (dftMatrix (p := p) ω * dftMatrix (p := p) ω).trace = (p : ℂ) := by
  rw [dftMatrix_sq ω hω]
  simp [reversal_trace hp2]

/-- **Spectral entry: `A` annihilates `X⁴ − p²`.** Hence `minpoly A ∣ X⁴ − p²`, which is
squarefree over `ℂ` (four distinct roots `√p·{1, i, −1, −i}`) — so `A` is diagonalizable with those
eigenvalues, the hinge of the multiplicity count. -/
theorem dftMatrix_aeval (hω : IsPrimitiveRoot ω p) :
    Polynomial.aeval (dftMatrix (p := p) ω) (Polynomial.X ^ 4 - Polynomial.C ((p : ℂ) ^ 2)) = 0 := by
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, dftMatrix_pow_four ω hω,
    Algebra.algebraMap_eq_smul_one, sub_self]

/-- `minpoly A ∣ X⁴ − p²`. Over `ℂ` the right side is squarefree with roots `√p·{1,i,−1,−i}`, so every
eigenvalue of `A` (root of `minpoly`, hence of `charpoly`) is one of those four values. -/
theorem dftMatrix_minpoly_dvd (hω : IsPrimitiveRoot ω p) :
    minpoly ℂ (dftMatrix (p := p) ω) ∣ (Polynomial.X ^ 4 - Polynomial.C ((p : ℂ) ^ 2)) :=
  minpoly.dvd ℂ _ (dftMatrix_aeval ω hω)

/-! ## Multiplicity-extraction core — preliminaries, root confinement and count

We fix the canonical square root `s := √p : ℂ` (`sqrtp`), confine every eigenvalue of `A` to
`{s, −s, i·s, −i·s}`, and count the roots (`= p`). Convention: `a,b,c,d` (built later) are the
multiplicities of `s, −s, i·s, −i·s`. -/

/-- The canonical complex square root `s = √p`, characterised by `s² = p`. -/
noncomputable def sqrtp (p : ℕ) : ℂ := (Real.sqrt (p : ℝ) : ℂ)

/-- `s² = p`: the defining property of the canonical square root. -/
theorem sqrtp_sq (p : ℕ) : (sqrtp p) ^ 2 = (p : ℂ) := by
  unfold sqrtp
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  simp

/-- **Spectral confinement, quartic form.** Every spectral value `r` of the Fourier matrix satisfies
`r⁴ = p²`. This is the spectral image of `aeval A (X⁴ − p²) = 0` (`dftMatrix_aeval`):
`eval r (X⁴−p²) ∈ spectrum (aeval A …) = {0}`. -/
theorem dftMatrix_pow_four_of_mem_spectrum (hω : IsPrimitiveRoot ω p) {r : ℂ}
    (hr : r ∈ spectrum ℂ (dftMatrix (p := p) ω)) : r ^ 4 = (p : ℂ) ^ 2 := by
  haveI : Nonempty (Fin p) := ⟨⟨0, (Fact.out : p.Prime).pos⟩⟩
  have himg := spectrum.subset_polynomial_aeval (dftMatrix (p := p) ω)
    (Polynomial.X ^ 4 - Polynomial.C ((p : ℂ) ^ 2)) (Set.mem_image_of_mem _ hr)
  rw [dftMatrix_aeval ω hω, spectrum.zero_eq, Set.mem_singleton_iff] at himg
  simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero] using himg

omit [Fact p.Prime] in
/-- **The quartic roots.** Any `r` with `r⁴ = p²` is one of the four values `±s, ±i·s`. Purely
algebraic: `(r²)² = (s²)²` splits via `x²=y² ↔ x=±y`, then `−s² = (i·s)²` handles the imaginary
pair. -/
theorem four_value_of_pow_four {r : ℂ} (h : r ^ 4 = (p : ℂ) ^ 2) :
    r = sqrtp p ∨ r = -sqrtp p ∨ r = Complex.I * sqrtp p ∨ r = -(Complex.I * sqrtp p) := by
  have hs : (sqrtp p) ^ 2 = (p : ℂ) := sqrtp_sq p
  have h1 : (r ^ 2) ^ 2 = ((sqrtp p) ^ 2) ^ 2 := by rw [hs, ← h]; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
  · have hIs : (Complex.I * sqrtp p) ^ 2 = -((sqrtp p) ^ 2) := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [← hIs] at h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h3))

/-- **Root confinement.** Every eigenvalue of the Fourier matrix is one of `±s, ±i·s`. -/
theorem dftMatrix_spectrum_subset (hω : IsPrimitiveRoot ω p) {r : ℂ}
    (hr : r ∈ spectrum ℂ (dftMatrix (p := p) ω)) :
    r = sqrtp p ∨ r = -sqrtp p ∨ r = Complex.I * sqrtp p ∨ r = -(Complex.I * sqrtp p) :=
  four_value_of_pow_four (dftMatrix_pow_four_of_mem_spectrum ω hω hr)

/-- **Root confinement (charpoly form).** Every root of the characteristic polynomial is one of
`±s, ±i·s`. -/
theorem dftMatrix_charpoly_root_mem (hω : IsPrimitiveRoot ω p) {r : ℂ}
    (hr : r ∈ (dftMatrix (p := p) ω).charpoly.roots) :
    r = sqrtp p ∨ r = -sqrtp p ∨ r = Complex.I * sqrtp p ∨ r = -(Complex.I * sqrtp p) := by
  haveI : Nonempty (Fin p) := ⟨⟨0, (Fact.out : p.Prime).pos⟩⟩
  exact dftMatrix_spectrum_subset ω hω
    (Matrix.mem_spectrum_of_isRoot_charpoly ((Polynomial.mem_roots'.1 hr).2))

omit [Fact p.Prime] in
/-- **Root count.** The characteristic polynomial has exactly `p` roots (with multiplicity), since
it splits over `ℂ` and has degree `p`. -/
theorem dftMatrix_charpoly_roots_card :
    (dftMatrix (p := p) ω).charpoly.roots.card = p := by
  rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-! ### The multiplicity split via semisimplicity + two traces

`A` is diagonalizable over `ℂ` because it annihilates the squarefree `X⁴ − p²`. Working with the
endomorphism `dftEnd = toLinAlgEquiv' A` of `Fin p → ℂ`, we take the internal direct sum of its four
eigenspaces and read the trace of `id` (`= p = a+b+c+d`) and of `A²` (`= p = p(a+b) − p(c+d)`) off the
components; together these give `a+b = (p+1)/2`, `c+d = (p−1)/2`. -/

/-- The Fourier matrix as an endomorphism of `Fin p → ℂ` (the algebra image of `A`). -/
noncomputable def dftEnd (ω : ℂ) : Module.End ℂ (Fin p → ℂ) :=
  Matrix.toLinAlgEquiv' (dftMatrix (p := p) ω)

/-- `dftEnd` annihilates `X⁴ − p²`: the endomorphism image of `dftMatrix_aeval` under the algebra
isomorphism `toLinAlgEquiv'`. -/
theorem dftEnd_aeval (hω : IsPrimitiveRoot ω p) :
    Polynomial.aeval (dftEnd (p := p) ω) (Polynomial.X ^ 4 - Polynomial.C ((p : ℂ) ^ 2)) = 0 := by
  rw [dftEnd, Polynomial.aeval_algHom_apply, dftMatrix_aeval ω hω, map_zero]

/-- **Semisimplicity.** `dftEnd` is semisimple (diagonalizable): it annihilates `X⁴ − p²`, which
is squarefree over `ℂ` (four distinct roots). -/
theorem dftEnd_isSemisimple (hω : IsPrimitiveRoot ω p) : (dftEnd (p := p) ω).IsSemisimple := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hsq : Squarefree (Polynomial.X ^ 4 - Polynomial.C ((p : ℂ) ^ 2)) :=
    (Polynomial.separable_X_pow_sub_C ((p : ℂ) ^ 2) (by norm_num) (pow_ne_zero 2 hp0)).squarefree
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (dftEnd_aeval ω hω)

/-- `s = √p ≠ 0` (as `p > 0`). -/
theorem sqrtp_ne_zero : sqrtp p ≠ 0 := by
  rw [sqrtp, Ne, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)).ne'

/-- The four fourth-roots of unity `1, −1, i, −i`. -/
noncomputable def dftRoots : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

omit [Fact p.Prime] in
/-- The four values `1, −1, i, −i` are distinct. -/
theorem dftRoots_injective : Function.Injective (dftRoots) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first | rfl | (exfalso; norm_num [dftRoots, Complex.ext_iff] at h)

/-- The four eigenvalues `s, −s, i·s, −i·s` of the Fourier matrix, indexed by `Fin 4`. -/
noncomputable def dftEigs (p : ℕ) : Fin 4 → ℂ :=
  ![sqrtp p, -sqrtp p, Complex.I * sqrtp p, -(Complex.I * sqrtp p)]

omit [Fact p.Prime] in
/-- `dftEigs = s · dftRoots`. -/
theorem dftEigs_eq_smul (i : Fin 4) : dftEigs p i = sqrtp p * dftRoots i := by
  fin_cases i <;> simp [dftEigs, dftRoots] <;> ring

/-- The four eigenvalues are distinct (since `s ≠ 0` and `1, −1, i, −i` are distinct). -/
theorem dftEigs_injective : Function.Injective (dftEigs p) := by
  intro i j h
  refine dftRoots_injective ?_
  rw [dftEigs_eq_smul, dftEigs_eq_smul] at h
  exact mul_left_cancel₀ sqrtp_ne_zero h

/-- **Eigenvalue confinement.** Every eigenvalue of `dftEnd` is one of `s, −s, i·s, −i·s`.
Lifts the matrix-spectrum confinement across the algebra iso via `AlgEquiv.spectrum_eq`. -/
theorem dftEnd_hasEigenvalue_mem (hω : IsPrimitiveRoot ω p) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (dftEnd (p := p) ω) μ) : ∃ i : Fin 4, μ = dftEigs p i := by
  have hspec : μ ∈ spectrum ℂ (dftMatrix (p := p) ω) := by
    have h := hμ.mem_spectrum
    rwa [dftEnd, AlgEquiv.spectrum_eq] at h
  rcases dftMatrix_spectrum_subset ω hω hspec with h | h | h | h
  · exact ⟨0, by simp [dftEigs, h]⟩
  · exact ⟨1, by simp [dftEigs, h]⟩
  · exact ⟨2, by simp [dftEigs, h]⟩
  · exact ⟨3, by simp [dftEigs, h]⟩

/-- **Internal direct sum.** The four eigenspaces of `dftEnd` decompose `Fin p → ℂ` as an
internal direct sum: they are independent (distinct eigenvalues) and span everything (semisimple,
and every eigenvalue is one of the four). -/
theorem dftEnd_eigenspace_isInternal (hω : IsPrimitiveRoot ω p) :
    DirectSum.IsInternal
      (fun i : Fin 4 => Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p i)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (Module.End.eigenspaces_iSupIndep (dftEnd (p := p) ω)).comp dftEigs_injective
  · rw [eq_top_iff, ← (dftEnd_isSemisimple ω hω).iSup_eigenspace_eq_top]
    refine iSup_le fun μ => ?_
    by_cases hμ : Module.End.HasEigenvalue (dftEnd (p := p) ω) μ
    · obtain ⟨i, rfl⟩ := dftEnd_hasEigenvalue_mem ω hω hμ
      exact le_iSup (fun i : Fin 4 => Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p i)) i
    · have hbot : Module.End.eigenspace (dftEnd (p := p) ω) μ = ⊥ := by
        by_contra hne; exact hμ hne
      rw [hbot]; exact bot_le

omit [Fact p.Prime] in
/-- `(dftEigs i)² = p · (dftRoots i)²`, so the squares are `p, p, −p, −p`. -/
theorem dftEigs_sq (i : Fin 4) : (dftEigs p i) ^ 2 = (p : ℂ) * (dftRoots i) ^ 2 := by
  rw [dftEigs_eq_smul, mul_pow, sqrtp_sq]

open Module in
/-- **The multiplicity split.** The multiplicity split `a+b = (p+1)/2`, `c+d = (p−1)/2` (odd `p`),
where `a,b,c,d` are the `finrank`s of the four eigenspaces of `dftEnd`. Proof: two traces on the
internal direct sum — `Tr(id) = p = a+b+c+d` and `Tr(A²) = p = p(a+b) − p(c+d)` — combined by
`omega`. -/
theorem dftEnd_multiplicity_split (hω : IsPrimitiveRoot ω p) (hp2 : p ≠ 2) :
    finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 0)) +
        finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 1)) = (p + 1) / 2 ∧
    finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 2)) +
        finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 3)) = (p - 1) / 2 := by
  classical
  set f := dftEnd (p := p) ω with hf
  set N : Fin 4 → Submodule ℂ (Fin p → ℂ) :=
    fun i => Module.End.eigenspace f (dftEigs p i) with hN
  change finrank ℂ (N 0) + finrank ℂ (N 1) = (p + 1) / 2 ∧
    finrank ℂ (N 2) + finrank ℂ (N 3) = (p - 1) / 2
  have hInt : DirectSum.IsInternal N := dftEnd_eigenspace_isInternal ω hω
  -- f maps each eigenspace to itself
  have hmaps : ∀ i, Set.MapsTo f (N i) (N i) := by
    intro i x hx
    have hx' : f x = dftEigs p i • x := by
      have hmem : x ∈ Module.End.eigenspace f (dftEigs p i) := hx
      rwa [Module.End.mem_eigenspace_iff] at hmem
    change f x ∈ Module.End.eigenspace f (dftEigs p i)
    rw [Module.End.mem_eigenspace_iff, hx', map_smul, hx']
  -- Trace of the identity: p = Σ finrank(N i)
  have hmid : ∀ i, Set.MapsTo (⇑(LinearMap.id : Module.End ℂ (Fin p → ℂ))) (N i) (N i) :=
    fun i => Set.mapsTo_id _
  have htr_id : (p : ℂ) = ∑ i, (finrank ℂ (N i) : ℂ) := by
    have h := LinearMap.trace_eq_sum_trace_restrict hInt (f := LinearMap.id) hmid
    rw [LinearMap.trace_id,
      show (finrank ℂ (Fin p → ℂ) : ℂ) = (p : ℂ) by rw [finrank_fin_fun]] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show LinearMap.id.restrict (hmid i) = LinearMap.id from
      LinearMap.ext fun x => Subtype.ext rfl, LinearMap.trace_id]
  -- Trace of A²: p = Σ (dftEigs i)² · finrank(N i)
  have hmaps2 : ∀ i, Set.MapsTo (⇑(f ^ 2)) (N i) (N i) := by
    intro i
    have hcoe : ⇑(f ^ 2) = ⇑f ∘ ⇑f := by funext x; rw [pow_two, Module.End.mul_apply]; rfl
    rw [hcoe]; exact (hmaps i).comp (hmaps i)
  have htr_sq : (p : ℂ) = ∑ i, (dftEigs p i) ^ 2 * (finrank ℂ (N i) : ℂ) := by
    have hlhs : LinearMap.trace ℂ (Fin p → ℂ) (f ^ 2) = (p : ℂ) := by
      have hpow : (f ^ 2 : Module.End ℂ (Fin p → ℂ))
          = Matrix.toLin' (dftMatrix (p := p) ω * dftMatrix (p := p) ω) := by
        rw [hf, dftEnd, pow_two, ← map_mul]; ext v : 1; rfl
      rw [hpow, Matrix.trace_toLin'_eq, dftMatrix_trace_sq ω hω hp2]
    rw [← hlhs, LinearMap.trace_eq_sum_trace_restrict hInt (f := f ^ 2) hmaps2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hrs2 : (f ^ 2).restrict (hmaps2 i) = (dftEigs p i) ^ 2 • LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext
      have hx2 : f (x : Fin p → ℂ) = dftEigs p i • (x : Fin p → ℂ) :=
        Module.End.mem_eigenspace_iff.mp (by simpa only [hN] using x.2)
      simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        SetLike.val_smul, pow_two, Module.End.mul_apply, hx2, map_smul, smul_smul]
    rw [hrs2, map_smul, LinearMap.trace_id, smul_eq_mul]
  -- Combine: extract integer facts and finish with omega.
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hF1 : finrank ℂ (N 0) + finrank ℂ (N 1) + finrank ℂ (N 2) + finrank ℂ (N 3) = p := by
    have h := htr_id; rw [Fin.sum_univ_four] at h; exact_mod_cast h.symm
  have hF2 : (finrank ℂ (N 0) : ℤ) + finrank ℂ (N 1) - finrank ℂ (N 2) - finrank ℂ (N 3) = 1 := by
    have h := htr_sq
    rw [Fin.sum_univ_four, dftEigs_sq, dftEigs_sq, dftEigs_sq, dftEigs_sq] at h
    have hr0 : (dftRoots 0) ^ 2 = 1 := by simp [dftRoots]
    have hr1 : (dftRoots 1) ^ 2 = 1 := by simp [dftRoots]
    have hr2 : (dftRoots 2) ^ 2 = -1 := by simp [dftRoots, Complex.I_sq]
    have hr3 : (dftRoots 3) ^ 2 = -1 := by simp [dftRoots, Complex.I_sq]
    rw [hr0, hr1, hr2, hr3] at h
    have h3 : (finrank ℂ (N 0) : ℂ) + finrank ℂ (N 1) - finrank ℂ (N 2) - finrank ℂ (N 3) = 1 :=
      mul_left_cancel₀ hp0 (by linear_combination -h)
    exact_mod_cast h3
  refine ⟨?_, ?_⟩ <;> omega

open Module in
/-- **Trace = eigenvalue sum.** `Tr A = ∑ᵢ (dftEigs i)·finrank(Nᵢ)`, the finrank-native reading of
the Gauss sum. Same direct-sum trace machinery as the multiplicity split, with `f = dftEnd` (power
1). -/
theorem dftMatrix_trace_eq_split (hω : IsPrimitiveRoot ω p) :
    (dftMatrix (p := p) ω).trace = ∑ i, dftEigs p i *
      (finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p i)) : ℂ) := by
  classical
  set f := dftEnd (p := p) ω with hf
  set N : Fin 4 → Submodule ℂ (Fin p → ℂ) :=
    fun i => Module.End.eigenspace f (dftEigs p i) with hN
  have hInt : DirectSum.IsInternal N := dftEnd_eigenspace_isInternal ω hω
  have hmaps : ∀ i, Set.MapsTo f (N i) (N i) := by
    intro i x hx
    have hx' : f x = dftEigs p i • x := by
      have hmem : x ∈ Module.End.eigenspace f (dftEigs p i) := hx
      rwa [Module.End.mem_eigenspace_iff] at hmem
    change f x ∈ Module.End.eigenspace f (dftEigs p i)
    rw [Module.End.mem_eigenspace_iff, hx', map_smul, hx']
  have hlhs : (dftMatrix (p := p) ω).trace = LinearMap.trace ℂ (Fin p → ℂ) f := by
    rw [hf, dftEnd,
      show Matrix.toLinAlgEquiv' (dftMatrix (p := p) ω)
        = Matrix.toLin' (dftMatrix (p := p) ω) from by ext v : 1; rfl,
      Matrix.trace_toLin'_eq]
  rw [hlhs, LinearMap.trace_eq_sum_trace_restrict hInt (f := f) hmaps]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrs : f.restrict (hmaps i) = dftEigs p i • LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext
    have hx2 : f (x : Fin p → ℂ) = dftEigs p i • (x : Fin p → ℂ) :=
      Module.End.mem_eigenspace_iff.mp (by simpa only [hN] using x.2)
    simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      SetLike.val_smul, hx2]
  rw [hrs, map_smul, LinearMap.trace_id, smul_eq_mul]

open Module in
/-- **Gauss sum = `s·((a−b)+(c−d)i)`.** The Gauss sum `∑ᵣ ωʳ²` in terms of `s = √p` and the four
eigenspace multiplicities: real part from the `±s` pair, imaginary from the `±i·s` pair. -/
theorem dftMatrix_trace_gauss (hω : IsPrimitiveRoot ω p) :
    (∑ r : Fin p, ω ^ ((r : ℕ) * (r : ℕ))) = sqrtp p *
      (((finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 0)) : ℂ)
          - finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 1)))
        + ((finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 2)) : ℂ)
          - finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 3))) * Complex.I) := by
  rw [← dftMatrix_trace, dftMatrix_trace_eq_split ω hω, Fin.sum_univ_four]
  simp only [dftEigs_eq_smul, dftRoots, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  ring

omit [Fact p.Prime] in
/-- **Vandermonde form.** `det A = ∏_{i<j} (ωʲ − ωⁱ)`, immediate since `A` is the Vandermonde
matrix in the nodes `ωʳ`. Holds for any `ω`; the definite *sign* of `det A` (the archimedean
phase-collapse, below) needs the *standard* root `ω = exp(2πi/p)` — for `ω = exp(2πik/p)` the
Gauss sum is `(k/p)·g`, a different sign. -/
theorem dftMatrix_det :
    (dftMatrix (p := p) ω).det = ∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (ω ^ (j : ℕ) - ω ^ (i : ℕ)) := by
  rw [dftMatrix, Matrix.det_vandermonde]

/-! ### The definite sign of `det A`, at the standard root `ω₀ = exp(2πi/p)`

The definite sign is root-specific, so this layer fixes `ω₀`. Each Vandermonde factor Euler-factors
as `ω₀ʲ − ω₀ⁱ = exp(π(i+j)/p·I)·2i·sin(π(j−i)/p)`; the exponential phases collapse (their exponent
sum is `≡ 0 mod 2p`), the sine product is positive, and the magnitude is `p^{p/2}`, giving
`det A = i^{C(p,2)}·p^{p/2}`. This part builds the Euler entry: the identity and the per-factor
form. -/

/-- **Euler identity.** `exp(xI) − exp(−xI) = 2i·sin x`. -/
theorem exp_mul_I_sub_exp_neg_mul_I (x : ℂ) :
    Complex.exp (x * Complex.I) - Complex.exp (-x * Complex.I) = 2 * Complex.I * Complex.sin x := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring

/-- The **standard primitive `p`-th root** `ω₀ = exp(2πi/p)`. -/
noncomputable def stdRoot (p : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))

omit [Fact p.Prime] in
theorem stdRoot_isPrimitiveRoot (hp0 : p ≠ 0) : IsPrimitiveRoot (stdRoot p) p :=
  Complex.isPrimitiveRoot_exp p hp0

omit [Fact p.Prime] in
/-- `ω₀ᵏ = exp((2πk/p)·i)`. -/
theorem stdRoot_pow (k : ℕ) :
    (stdRoot p) ^ k = Complex.exp (((2 * Real.pi * k / p : ℝ)) * Complex.I) := by
  rw [stdRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

omit [Fact p.Prime] in
/-- **Per-factor Euler factorization** at the standard root:
`ω₀ʲ − ω₀ⁱ = exp(π(i+j)/p·I)·2i·sin(π(j−i)/p)`. -/
theorem stdRoot_pow_sub (i j : ℕ) :
    (stdRoot p) ^ j - (stdRoot p) ^ i
      = Complex.exp (((Real.pi * ((i : ℝ) + j) / p) : ℝ) * Complex.I)
        * (2 * Complex.I * (Real.sin (Real.pi * ((j : ℝ) - i) / p) : ℂ)) := by
  have hj : (stdRoot p) ^ j
      = Complex.exp (((Real.pi * ((i : ℝ) + j) / p : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((Real.pi * ((j : ℝ) - i) / p : ℝ) : ℂ) * Complex.I) := by
    rw [stdRoot_pow, ← Complex.exp_add]; congr 1; push_cast; ring
  have hi : (stdRoot p) ^ i
      = Complex.exp (((Real.pi * ((i : ℝ) + j) / p : ℝ) : ℂ) * Complex.I)
        * Complex.exp (-((Real.pi * ((j : ℝ) - i) / p : ℝ) : ℂ) * Complex.I) := by
    rw [stdRoot_pow, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hj, hi, ← mul_sub, exp_mul_I_sub_exp_neg_mul_I, Complex.ofReal_sin]

/-! ### The spectral determinant `det A = ∏ᵢ (dftEigs i)^{finrank}` -/

open Module in
/-- **Bridge (count = finrank).** For the semisimple `dftEnd`, the multiplicity of an eigenvalue as a
charpoly root equals the eigenspace dimension — the single point where roots meet finranks. -/
theorem dftEnd_finrank_eq_count (hω : IsPrimitiveRoot ω p) (v : ℂ) :
    finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) v)
      = (dftMatrix (p := p) ω).charpoly.roots.count v := by
  classical
  have hfss : (dftEnd (p := p) ω).IsFinitelySemisimple :=
    Module.End.isFinitelySemisimple_iff_isSemisimple.mpr (dftEnd_isSemisimple ω hω)
  have hchar : (dftEnd (p := p) ω).charpoly = (dftMatrix (p := p) ω).charpoly := by
    rw [dftEnd, show Matrix.toLinAlgEquiv' (dftMatrix (p := p) ω)
      = Matrix.toLin' (dftMatrix (p := p) ω) from by ext v : 1; rfl]
    exact Matrix.charpoly_toLin' _
  rw [← hfss.maxGenEigenspace_eq_eigenspace v, LinearMap.finrank_maxGenEigenspace_eq,
    Polynomial.count_roots, hchar]

open Module in
/-- **Spectral determinant.** `det A = ∏ᵢ (dftEigs i)^{finrank(Nᵢ)}`, via `det = roots.prod`, the
confinement of roots to the four eigenvalues, and the count↔finrank bridge. -/
theorem dftMatrix_det_spectral (hω : IsPrimitiveRoot ω p) :
    (dftMatrix (p := p) ω).det =
      ∏ i : Fin 4, (dftEigs p i) ^ finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p i)) := by
  classical
  have hsub : (dftMatrix (p := p) ω).charpoly.roots.toFinset ⊆ Finset.image (dftEigs p) Finset.univ := by
    intro v hv
    rw [Multiset.mem_toFinset] at hv
    rw [Finset.mem_image]
    rcases dftMatrix_charpoly_root_mem ω hω hv with h | h | h | h
    · exact ⟨0, Finset.mem_univ _, by simp [dftEigs, h]⟩
    · exact ⟨1, Finset.mem_univ _, by simp [dftEigs, h]⟩
    · exact ⟨2, Finset.mem_univ _, by simp [dftEigs, h]⟩
    · exact ⟨3, Finset.mem_univ _, by simp [dftEigs, h]⟩
  rw [Matrix.det_eq_prod_roots_charpoly, Finset.prod_multiset_count_of_subset _ _ hsub,
    Finset.prod_image (fun x _ y _ h => dftEigs_injective h)]
  exact Finset.prod_congr rfl fun i _ => by rw [dftEnd_finrank_eq_count ω hω]

/-! ### Sine positivity, phase collapse, and the definite sign of `det A` -/

omit [Fact p.Prime] in
/-- **Sine positivity.** The Vandermonde sine product is a positive real: for `i < j` in `Fin p`,
`0 < π(j−i)/p < π`, so every factor is positive. -/
theorem dftMatrix_sin_prod_pos (hp0 : 0 < p) :
    0 < ∏ i : Fin p, ∏ j ∈ Finset.Ioi i, Real.sin (Real.pi * ((j : ℝ) - i) / p) := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_Ioi] at hj
  have hijn : (i : ℕ) < (j : ℕ) := hj
  have hij : (i : ℝ) < (j : ℝ) := by exact_mod_cast hijn
  have hjp : (j : ℝ) < p := by exact_mod_cast j.isLt
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  apply Real.sin_pos_of_pos_of_lt_pi
  · have hd : (0 : ℝ) < (j : ℝ) - i := by linarith
    exact div_pos (mul_pos Real.pi_pos hd) hp'
  · rw [div_lt_iff₀ hp']
    nlinarith [Real.pi_pos]

omit [Fact p.Prime] in
/-- **Phase-sum divisibility.** `2p ∣ Σ_{i<j}(i+j)`. Each value `v` occurs in exactly `p−1` of the pairs
(as `i` with `j>v`: `p−1−v` times, as `j` with `i<v`: `v` times), so the sum is `(p−1)·Σᵢ i`; with
`2Σᵢ = p(p−1)` and odd `p = 2m+1` this equals `2p·m²`. (This replaces the exp/`Real.pi` phase form with
the algebraic root-of-unity route the file already uses.) -/
theorem phaseSum_dvd (hodd : Odd p) :
    2 * p ∣ ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ)) := by
  have hT2 : 2 * ∑ i : Fin p, (i : ℕ) = p * (p - 1) := by
    have hrange : ∑ i : Fin p, (i : ℕ) = ∑ i ∈ Finset.range p, i :=
      Fin.sum_univ_eq_sum_range (fun k => k) p
    rw [hrange, mul_comm, Finset.sum_range_id_mul_two]
  have hA : ∀ i : Fin p, ∑ _j ∈ Finset.Ioi i, (i : ℕ) = (p - 1 - (i : ℕ)) * (i : ℕ) := by
    intro i; rw [Finset.sum_const, Fin.card_Ioi, smul_eq_mul]
  have hswap : (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, (j : ℕ))
      = ∑ j : Fin p, ∑ _i ∈ Finset.Iio j, (j : ℕ) :=
    Finset.sum_comm' (fun i j => by simp [Finset.mem_Ioi, Finset.mem_Iio])
  have hB : (∑ i : Fin p, ∑ j ∈ Finset.Ioi i, (j : ℕ)) = ∑ j : Fin p, (j : ℕ) * (j : ℕ) := by
    rw [hswap]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_const, Fin.card_Iio, smul_eq_mul]
  have hS : ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ)) = (p - 1) * ∑ i : Fin p, (i : ℕ) := by
    calc ∑ i : Fin p, ∑ j ∈ Finset.Ioi i, ((i : ℕ) + (j : ℕ))
        = ∑ i : Fin p, (p - 1 - (i : ℕ)) * (i : ℕ) + ∑ j : Fin p, (j : ℕ) * (j : ℕ) := by
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.sum_congr rfl (fun i _ => hA i), hB]
      _ = (p - 1) * ∑ i : Fin p, (i : ℕ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hlt : (i : ℕ) < p := i.isLt
          rw [← Nat.add_mul]; congr 1; omega
  rw [hS]
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m ^ 2, ?_⟩
  have h2 : 2 * ((p - 1) * ∑ i : Fin p, (i : ℕ)) = 2 * (2 * p * m ^ 2) := by
    rw [show 2 * ((p - 1) * ∑ i : Fin p, (i : ℕ))
        = (p - 1) * (2 * ∑ i : Fin p, (i : ℕ)) from by ring, hT2]
    have hp1 : p - 1 = 2 * m := by omega
    rw [hp1]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

/-- **Phase collapse.** The accumulated exponential phase of the Vandermonde factors is `1`: each
`exp(iπ(i+j)/p)` is `ζ^{i+j}` for the primitive `2p`-th root `ζ = exp(2πi/(2p))`, so the whole product is
`ζ^S = 1` since `2p ∣ S` (`phaseSum_dvd`). -/
theorem phase_collapse (hp2 : p ≠ 2) :
    ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
        Complex.exp (((Real.pi * ((i : ℝ) + j) / p) : ℝ) * Complex.I) = 1 := by
  have h2p : 2 * p ≠ 0 := by have := (Fact.out : p.Prime).pos; omega
  have hζ : IsPrimitiveRoot
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 * p : ℕ) : ℂ))) (2 * p) :=
    Complex.isPrimitiveRoot_exp (2 * p) h2p
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  have hfac : ∀ i j : Fin p,
      Complex.exp (((Real.pi * ((i : ℝ) + j) / p) : ℝ) * Complex.I)
        = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 * p : ℕ) : ℂ))) ^ ((i : ℕ) + (j : ℕ)) := by
    intro i j
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simp_rw [hfac, Finset.prod_pow_eq_pow_sum]
  exact (hζ.pow_eq_one_iff_dvd _).mpr (phaseSum_dvd ((Fact.out : p.Prime).odd_of_ne_two hp2))

/-- **Archimedean determinant.** At the standard root, `det A = i^{C(p,2)}·R` for a positive real
`R` (`= 2^{C(p,2)}·∏∏ sin`). The `i^{C(p,2)}` is the definite phase; the magnitude is left implicit in
`R > 0` (it is recovered for free by matching with the spectral determinant). -/
theorem dftMatrix_det_arch (hp2 : p ≠ 2) :
    ∃ R : ℝ, 0 < R ∧
      (dftMatrix (p := p) (stdRoot p)).det = Complex.I ^ (p.choose 2) * (R : ℂ) := by
  classical
  have hcard : ∑ i : Fin p, (Finset.Ioi i).card = p.choose 2 := by
    have hc : ∑ i : Fin p, (Finset.Ioi i).card = ∑ i : Fin p, (p - 1 - (i : ℕ)) := by
      simp only [Fin.card_Ioi]
    have hr : ∑ i : Fin p, (p - 1 - (i : ℕ)) = ∑ k ∈ Finset.range p, (p - 1 - k) :=
      Fin.sum_univ_eq_sum_range (fun k => p - 1 - k) p
    rw [hc, hr, Finset.sum_range_reflect (fun k => k) p, Finset.sum_range_id, Nat.choose_two_right]
  refine ⟨2 ^ (p.choose 2)
      * ∏ i : Fin p, ∏ j ∈ Finset.Ioi i, Real.sin (Real.pi * ((j : ℝ) - i) / p), ?_, ?_⟩
  · have hpos := dftMatrix_sin_prod_pos (p := p) (Fact.out : p.Prime).pos
    positivity
  · have hB : (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
          (2 * Complex.I * (Real.sin (Real.pi * ((j : ℝ) - i) / p) : ℂ)))
        = (2 * Complex.I) ^ (p.choose 2)
          * ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, Real.sin (Real.pi * ((j : ℝ) - i) / p) : ℝ) : ℂ) := by
      rw [Finset.prod_congr rfl fun i _ => Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      congr 1
      · simp_rw [Finset.prod_const]; rw [Finset.prod_pow_eq_pow_sum, hcard]
      · simp only [← Complex.ofReal_prod]
    rw [dftMatrix_det]
    simp_rw [stdRoot_pow_sub]
    rw [Finset.prod_congr rfl fun i _ => Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      phase_collapse hp2, one_mul, hB, mul_pow]
    push_cast
    ring

/-! ### The magnitude `|g|² = p`, via the library's `quadGaussSum` -/

/-- The matrix-trace Gauss sum is the library's `quadGaussSum` for the standard additive character
`ψ(x) = ω₀^{x.val}` — reindexing `Fin p ≃ ZMod p` and reducing the exponent mod `p` (`ω₀^p = 1`). -/
theorem dftMatrix_trace_eq_quadGaussSum (hp0 : p ≠ 0) :
    (∑ r : Fin p, (stdRoot p) ^ ((r : ℕ) * (r : ℕ)))
      = ECCLib.quadGaussSum (AddChar.zmodChar p ((stdRoot_isPrimitiveRoot hp0).pow_eq_one)) := by
  haveI : NeZero p := ⟨hp0⟩
  have hζp : (stdRoot p) ^ p = 1 := (stdRoot_isPrimitiveRoot hp0).pow_eq_one
  set φ : Fin p → ZMod p := fun i => ((i : ℕ) : ZMod p) with hφ
  have hφbij : Function.Bijective φ := by
    refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨?_, by rw [ZMod.card, Fintype.card_fin]⟩
    intro i j h
    have hi : (φ i).val = (i : ℕ) := ZMod.val_cast_of_lt i.isLt
    have hj : (φ j).val = (j : ℕ) := ZMod.val_cast_of_lt j.isLt
    exact Fin.ext (by rw [← hi, ← hj, h])
  rw [ECCLib.quadGaussSum]
  simp_rw [AddChar.zmodChar_apply]
  refine Fintype.sum_bijective φ hφbij (fun r => (stdRoot p) ^ ((r : ℕ) * (r : ℕ)))
    (fun x => (stdRoot p) ^ (x ^ 2).val) ?_
  intro r
  simp only [hφ]
  rw [show (((r : ℕ) : ZMod p)) ^ 2 = (((r : ℕ) * (r : ℕ) : ℕ) : ZMod p) from by push_cast; ring,
    ZMod.val_natCast]
  exact pow_eq_pow_mod _ hζp

/-- **`|g|² = p`.** The magnitude of the Gauss sum, from `quadGaussSum_normSq`. Gives the dichotomy
`(a−b)² + (c−d)² = 1`. -/
theorem gaussSum_normSq (hp2 : p ≠ 2) :
    ‖∑ r : Fin p, (stdRoot p) ^ ((r : ℕ) * (r : ℕ))‖ ^ 2 = (p : ℝ) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  haveI : NeZero p := ⟨hp0⟩
  have hrc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [dftMatrix_trace_eq_quadGaussSum hp0,
    ECCLib.quadGaussSum_normSq hrc
      (ECCLib.ne_one_of_isPrimitive
        (AddChar.zmodChar_primitive_of_primitive_root p (stdRoot_isPrimitiveRoot hp0))),
    ZMod.card]

/-! ### The definite sign — final assembly -/

open Module in
/-- **Spectral determinant, evaluated.** `det A = s^{a+b+c+d}·i^{2b+c+3d}` — the four eigenvalues
`s,−s,i·s,−i·s` are `i^{0},i^{2},i^{1},i^{3}` times `s`. -/
theorem dftMatrix_det_spectral_eval (hω : IsPrimitiveRoot ω p) :
    (dftMatrix (p := p) ω).det
      = (sqrtp p) ^ (finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 0))
          + finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 1))
          + finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 2))
          + finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 3)))
        * Complex.I ^ (2 * finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 1))
          + finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 2))
          + 3 * finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 3))) := by
  rw [dftMatrix_det_spectral ω hω, Fin.prod_univ_four]
  generalize finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 0)) = n0
  generalize finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 1)) = n1
  generalize finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 2)) = n2
  generalize finrank ℂ (Module.End.eigenspace (dftEnd (p := p) ω) (dftEigs p 3)) = n3
  have e0 : dftEigs p 0 = Complex.I ^ 0 * sqrtp p := by simp [dftEigs]
  have e1 : dftEigs p 1 = Complex.I ^ 2 * sqrtp p := by rw [Complex.I_sq]; simp [dftEigs]
  have e2 : dftEigs p 2 = Complex.I ^ 1 * sqrtp p := by simp [dftEigs]
  have e3 : dftEigs p 3 = Complex.I ^ 3 * sqrtp p := by
    rw [show Complex.I ^ 3 = -Complex.I from by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq, pow_one]; ring]
    simp [dftEigs]
  rw [e0, e1, e2, e3]
  simp only [mul_pow, ← pow_mul]
  rw [show Complex.I ^ (0 * n0) * sqrtp p ^ n0 * (Complex.I ^ (2 * n1) * sqrtp p ^ n1)
      * (Complex.I ^ (1 * n2) * sqrtp p ^ n2) * (Complex.I ^ (3 * n3) * sqrtp p ^ n3)
      = (sqrtp p ^ n0 * sqrtp p ^ n1 * sqrtp p ^ n2 * sqrtp p ^ n3)
        * (Complex.I ^ (0 * n0) * Complex.I ^ (2 * n1) * Complex.I ^ (1 * n2) * Complex.I ^ (3 * n3))
      from by ring]
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  congr 1
  omega

/-- `Complex.I` has order 4. -/
theorem orderOf_I : orderOf Complex.I = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Complex.I_sq]; ring, fun m hm hm0 => ?_⟩
  interval_cases m
  · rw [pow_one]; simp [Complex.ext_iff]
  · rw [Complex.I_sq]; norm_num
  · rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, Complex.I_sq, pow_one]; simp [Complex.ext_iff]

set_option maxHeartbeats 1200000 in
-- The final assembly threads many hypotheses through several `omega`/`nlinarith` calls on a large
-- context; the default heartbeat budget is insufficient.
open Module in
/-- **The definite quadratic Gauss sign.** For odd prime `p` and the standard root `ω₀ = exp(2πi/p)`,
`∑ᵣ ω₀^{r²} = √p` if `p ≡ 1 (mod 4)` and `= i·√p` if `p ≡ 3 (mod 4)`. -/
theorem quadGaussSum_sign (hp2 : p ≠ 2) :
    (∑ r : Fin p, (stdRoot p) ^ ((r : ℕ) * (r : ℕ)))
      = if p % 4 = 1 then (sqrtp p : ℂ) else Complex.I * (sqrtp p) := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).pos.ne'
  have hω₀ : IsPrimitiveRoot (stdRoot p) p := stdRoot_isPrimitiveRoot hp0
  have hs0 : sqrtp p ≠ 0 := sqrtp_ne_zero
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2; omega
  -- numeric facts about the four multiplicities
  have hS3 := dftMatrix_trace_gauss (stdRoot p) hω₀
  obtain ⟨hab, hcd⟩ := dftEnd_multiplicity_split (stdRoot p) hω₀ hp2
  have hspec := dftMatrix_det_spectral_eval (stdRoot p) hω₀
  obtain ⟨R, hRpos, hRdet⟩ := dftMatrix_det_arch hp2
  set a := finrank ℂ (Module.End.eigenspace (dftEnd (p := p) (stdRoot p)) (dftEigs p 0)) with ha
  set b := finrank ℂ (Module.End.eigenspace (dftEnd (p := p) (stdRoot p)) (dftEigs p 1)) with hb
  set c := finrank ℂ (Module.End.eigenspace (dftEnd (p := p) (stdRoot p)) (dftEigs p 2)) with hc
  set d := finrank ℂ (Module.End.eigenspace (dftEnd (p := p) (stdRoot p)) (dftEigs p 3)) with hd
  have hsum : a + b + c + d = p := by omega
  -- (a-b)² + (c-d)² = 1
  have hnorm : ((a : ℤ) - b) ^ 2 + ((c : ℤ) - d) ^ 2 = 1 := by
    have hg := gaussSum_normSq hp2
    rw [hS3, norm_mul, mul_pow] at hg
    have hsn : ‖sqrtp p‖ ^ 2 = (p : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq, sqrtp, Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]
    have hzn : ‖((a : ℂ) - b) + ((c : ℂ) - d) * Complex.I‖ ^ 2 = ((a : ℝ) - b) ^ 2 + ((c : ℝ) - d) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq,
        show ((a : ℂ) - b) + ((c : ℂ) - d) * Complex.I
          = (((a : ℝ) - b : ℝ) : ℂ) + (((c : ℝ) - d : ℝ) : ℂ) * Complex.I from by push_cast; ring,
        Complex.normSq_add_mul_I]
    rw [hsn, hzn] at hg
    have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
    have hr : ((a : ℝ) - b) ^ 2 + ((c : ℝ) - d) ^ 2 = 1 :=
      mul_left_cancel₀ hp' (by rw [mul_one]; linarith [hg])
    exact_mod_cast hr
  -- phase: I^{2b+c+3d} = I^{C(p,2)}
  have hphase : Complex.I ^ (2 * b + c + 3 * d) = Complex.I ^ (p.choose 2) := by
    have heq : (sqrtp p) ^ (a + b + c + d) * Complex.I ^ (2 * b + c + 3 * d)
        = Complex.I ^ (p.choose 2) * (R : ℂ) := by rw [← hspec, hRdet]
    have hRabs : (Real.sqrt p) ^ (a + b + c + d) = R := by
      have hsA : ‖sqrtp p‖ = Real.sqrt p := by
        rw [sqrtp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hRA : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
      have h := congrArg norm heq
      simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, one_mul, hsA, hRA] at h
      exact h
    rw [show (sqrtp p) ^ (a + b + c + d) = (R : ℂ) from by
      rw [sqrtp, ← Complex.ofReal_pow, hRabs], mul_comm (Complex.I ^ (p.choose 2))] at heq
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hRpos.ne') heq
  -- mod 4
  have hmod4 : (2 * b + c + 3 * d) ≡ p.choose 2 [MOD 4] := by
    have hne : Complex.I ≠ 0 := Complex.I_ne_zero
    have hu : (Units.mk0 Complex.I hne) ^ (2 * b + c + 3 * d)
        = (Units.mk0 Complex.I hne) ^ (p.choose 2) := by
      apply Units.ext; push_cast; exact hphase
    have ho : orderOf (Units.mk0 Complex.I hne) = 4 := by
      rw [← orderOf_units, Units.val_mk0]; exact orderOf_I
    have := pow_eq_pow_iff_modEq.mp hu
    rwa [ho] at this
  -- eliminate: g = s·((a-b)+(c-d)I); pin the axis and sign
  rw [hS3]
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hchoose : p.choose 2 = p * (p - 1) / 2 := Nat.choose_two_right p
  -- linearize `C(p,2) = 3m + 4t` using `Even (m(m-1))`
  obtain ⟨t, ht⟩ : Even (m * (m - 1)) := by
    rcases Nat.even_or_odd m with he | ho
    · exact he.mul_right _
    · exact (Nat.Odd.sub_odd ho odd_one).mul_left _
  have hmm : m * m = m + 2 * t := by
    have h2 : m * (m - 1) = m * m - m := Nat.mul_pred m m
    have h3 : m ≤ m * m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · omega
      · exact Nat.le_mul_of_pos_left m h
    omega
  have hCval : p.choose 2 = 2 * (m * m) + m := by
    rw [hchoose, hm, Nat.add_sub_cancel,
      show (2 * m + 1) * (2 * m) = (2 * (m * m) + m) * 2 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hmod4' : (2 * b + c + 3 * d) % 4 = (3 * m + 4 * t) % 4 := by
    have h : (2 * b + c + 3 * d) % 4 = (p.choose 2) % 4 := hmod4
    rw [hCval, hmm] at h; rw [h]; congr 1; ring
  -- dichotomy from |g|²
  have hnorm2 : ((a : ℤ) - b) * ((a : ℤ) - b) + ((c : ℤ) - d) * ((c : ℤ) - d) = 1 := by
    have hh := hnorm; rw [pow_two, pow_two] at hh; exact hh
  have hdisj : ((a : ℤ) - b = 1 ∧ (c : ℤ) - d = 0) ∨ ((a : ℤ) - b = -1 ∧ (c : ℤ) - d = 0)
      ∨ ((a : ℤ) - b = 0 ∧ (c : ℤ) - d = 1) ∨ ((a : ℤ) - b = 0 ∧ (c : ℤ) - d = -1) := by
    have hxlo : -1 ≤ (a : ℤ) - b := by nlinarith [hnorm2, sq_nonneg ((a : ℤ) - b + 1), mul_self_nonneg ((c:ℤ)-d)]
    have hxhi : (a : ℤ) - b ≤ 1 := by nlinarith [hnorm2, sq_nonneg ((a : ℤ) - b - 1), mul_self_nonneg ((c:ℤ)-d)]
    have hylo : -1 ≤ (c : ℤ) - d := by nlinarith [hnorm2, sq_nonneg ((c : ℤ) - d + 1), mul_self_nonneg ((a:ℤ)-b)]
    have hyhi : (c : ℤ) - d ≤ 1 := by nlinarith [hnorm2, sq_nonneg ((c : ℤ) - d - 1), mul_self_nonneg ((a:ℤ)-b)]
    rcases (by omega : (a : ℤ) - b = -1 ∨ (a : ℤ) - b = 0 ∨ (a : ℤ) - b = 1) with hx | hx | hx <;>
      rcases (by omega : (c : ℤ) - d = -1 ∨ (c : ℤ) - d = 0 ∨ (c : ℤ) - d = 1) with hy | hy | hy <;>
        rw [hx, hy] at hnorm2 ⊢ <;> omega
  rcases hp4 with h4 | h4
  · -- p ≡ 1 (mod 4): a-b = 1, c-d = 0
    rw [if_pos h4]
    have hxy : (a : ℤ) - b = 1 ∧ (c : ℤ) - d = 0 := by omega
    have ea : ((a : ℂ) - b) = 1 := by exact_mod_cast hxy.1
    have ec : ((c : ℂ) - d) = 0 := by exact_mod_cast hxy.2
    rw [ea, ec]; ring
  · -- p ≡ 3 (mod 4): a-b = 0, c-d = 1
    rw [if_neg (by omega)]
    have hxy : (a : ℤ) - b = 0 ∧ (c : ℤ) - d = 1 := by omega
    have ea : ((a : ℂ) - b) = 0 := by exact_mod_cast hxy.1
    have ec : ((c : ℂ) - d) = 1 := by exact_mod_cast hxy.2
    rw [ea, ec]; ring

/-- **The definite sign, stated on the named object.** `quadGaussSum ψ₀` — the library's
`∑_{x∈ZMod p} ψ₀(x²)` for the canonical additive character `ψ₀(a) = ω₀^{a.val}` (`ω₀ = exp(2πi/p)`)
— equals `√p` (`p≡1 mod 4`) / `i·√p` (`p≡3 mod 4`). This is `quadGaussSum_sign` composed with the
*proven* bridge `dftMatrix_trace_eq_quadGaussSum`, so the theorem is about the intended Gauss sum,
not a lookalike. -/
theorem quadGaussSum_sign_char (hp2 : p ≠ 2) :
    ECCLib.quadGaussSum
        (AddChar.zmodChar p ((stdRoot_isPrimitiveRoot (p := p) (Fact.out : p.Prime).pos.ne').pow_eq_one))
      = if p % 4 = 1 then (sqrtp p : ℂ) else Complex.I * (sqrtp p) := by
  rw [← dftMatrix_trace_eq_quadGaussSum (Fact.out : p.Prime).pos.ne']
  exact quadGaussSum_sign hp2


end ECCLib.GaussSign

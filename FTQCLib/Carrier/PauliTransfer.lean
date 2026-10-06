/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Doubling
import FTQCLib.Pauli.Symplectic

/-!
# The Walsh transform as the H-word, and the Pauli transfer matrix

The statement of T50 (`docs/TARGETS.md`; `docs/fidelity/T50.md`; `docs/decisions/T50.md`). A
protocol's channel (T49) is read in the Pauli basis through its Choi state, and the three Pauli
representations of a channel (the Kraus operators' Pauli coefficients, the χ matrix and the Pauli
transfer matrix) are stated against the frame's own objects.

**One Pauli convention.** The Pauli with bits `(a, b)` is the real matrix `P = X^a Z^b`
(`pauliMatrix`): `∣x⟩ ↦ (−1)^{b·x} ∣x ⊕ a⟩`, `Z^b` first, then `X^a`. Its entries are those of
`pauliOperator` (`FTQCLib/Hilbert/PauliOp.lean`, not imported: this module is frame-pure, D5), and
the frame's Hermitian action `pauliAct` (`FTQCLib/Stabilizer/AmplitudeStabilizer.lean`) is
`i^{a·b}` times it. Every daggered Pauli below is `(pauliMatrix P)ᴴ`, and the convention is used
throughout: the coefficients `c(P) = 2^{−n} tr(P† K)` (`pauliCoeff`), the χ form `P ρ Q†`, and the
transfer matrix `R(P, Q) = 2^{−n} tr(P† Λ(Q))` (`ptm`). The dagger in `R` is what makes the
diagonal duality hold for real Paulis: without it, `R(Q, Q)` changes sign at every `Q` with `a·b`
odd, since `Q² = −I` there (the identity channel at `n = 1`, `Q = XZ`, gives `−1`).

**The symplectic Walsh transform** (`walsh2n`) is `Ŵf(q) = 2^{−n} Σ_p (−1)^{ω(p, q)} f(p)`, with
`ω` the symplectic pairing `omega`. It is normalised as the H-word is: H on each of the `2n` bits
(`hadamardLayer`) computes `2^{−n} Σ_v (−1)^{v·w} g(v)`, and `ω(p, q)` is the dot product of `p`'s
bits `(a, b)` with `q`'s bits exchanged, `(q.Z, q.X)` (`symplecticBits`). So `Ŵ` is the H-word's
referee after the symplectic relabelling (`walsh2n_eq_runAmp`). The duality and the eigenvalues
use `2^n Ŵ`, the unnormalised sum, and say so.

**The Bell reading** (`bellRead`). The Choi state `choiRead p σ` (T49: reference bits, data bits,
read outcome bits, unread outcome bits) is run through the word `bellReadWord`: CNOT from each
reference bit `i` to the data bit `n + i`, then H on each reference bit. It is a T05 word, so the
result is a carrier state at the protocol's precision. Its amplitude at `(b, a, o, e)`, the Z bits
in the first half and the X bits in the second, is `2^{n/2} c_{o,e}(X^a Z^b)`, where `K_{o,e}`
(`krausOp`) is the block of T49's dilation at the read string `o` and the unread string `e`
(`bellRead_choi_eq_pauliCoeff`). The factor `2^{n/2}` is T49's unnormalised floor: `idAt n m` is
`δ_{x = y}` at scale `1`, `2^{n/2}` times the normalised Bell state.

**χ per read string** (`chi`). At each read string `o`, `χ_o(P, Q)` is `2^{−n}` times the Gram data
of the Bell-read state over the unread bits (T27's `gram`), at the read words `(P, o)` and `(Q, o)`.
It is per read string: the Gram data's blocks `o ≠ o′` are the coherent reading's cross terms, which
no `χ_o` records. It equals `Σ_e c_{o,e}(P) conj(c_{o,e}(Q))`, quadratic in the Kraus operators,
and the branch at `o` (`channelBranch`, the `(o, o)` block of T49's `channel`) is
`ρ ↦ Σ_{P,Q} χ_o(P, Q) P ρ Q†` (`channel_eq_chi_sum`).

**The transfer matrix is χ in another basis** (`ptm_eq_chi_basis`). `R` is the branch's coordinates
in the basis `ρ ↦ 2^{−n} tr(Q† ρ) P` of the maps on matrices, χ its coordinates in the basis
`ρ ↦ P ρ Q†`, and `transferOfChi` is the change of coordinates, a bijection of
`Matrix (Pauli n) (Pauli n) ℂ`. It is not a transform of the Choi amplitude, which is linear in the
Kraus operators where `R` is quadratic. **The diagonal duality** holds for every channel, here every
protocol's branch at every reading: `R(Q, Q) = 2^n Ŵ(χ's diagonal)(Q) = Σ_P χ(P, P)(−1)^{ω(P, Q)}`
(`ptm_diag_eq_walsh_chi_diag`).

**Pauli channels** (`IsPauliChannel`). A map is a Pauli channel when it is `ρ ↦ Σ_P d(P) P ρ P†`.
A protocol's branch is one exactly when its χ is diagonal, and `R` is then diagonal
(`pauliChannel_iff_chi_diagonal`), with the eigenvalues `λ = 2^n Ŵp` of the duality. With every
outcome bit unread, χ's diagonal is a probability distribution on `Pauli n` with values in
`ℤ[ζ_{2^∞}, ½]` (`chi_diag_isDistribution`); with outcome bits read, a single branch's diagonal
sums to the branch's weight and is in general a subdistribution, so the theorem is not stated there.
The bridge to T52's distributions runs one way: `1/3` is no protocol's value.

## Main definitions

* `pauliOfBits`, `symplecticBits` — a Pauli read off `n + n` bits, X bits first; and its bits with
  the X and Z halves exchanged, the symplectic relabelling.
* `walsh2n`, `hadamardLayer` — the symplectic Walsh transform `Ŵ` on `2n` bits, and H on every bit.
* `pauliMatrix`, `pauliCoeff` — `X^a Z^b` as a matrix, and `c(P) = 2^{−n} tr(P† K)`.
* `krausOp` — the Kraus operator `K_{o,e}`, a block of T49's dilation.
* `bellReadWord`, `bellRead` — the Bell reading of the Choi state, a T05 word and its run.
* `chi`, `channelBranch` — χ at a read string, and the branch of the channel there.
* `ptm`, `transferOfChi` — the Pauli transfer matrix of a map on matrices, and χ's change of basis.
* `IsPauliChannel`, `IsPauliDistribution` — Pauli channels, and probability distributions on
  `Pauli n`.

## Main results

* `walsh2n_eq_runAmp` — `Ŵ` is the H-word's referee after the symplectic relabelling (T50.3.1).
* `bellRead_choi_eq_pauliCoeff` — the Bell reading is a carrier state at the protocol's precision,
  with amplitude `2^{n/2} c_{o,e}(P)` at `(b, a, o, e)` (T50.3.2).
* `channel_eq_chi_sum` — χ is the Kraus coefficients' Gram data, and the branch is
  `Σ χ(P, Q) P ρ Q†` (T50.3.2).
* `ptm_eq_chi_basis` — the transfer matrix is χ in another basis (T50.3.2).
* `ptm_diag_eq_walsh_chi_diag` — the diagonal duality, with its `2^n` (T50.3.2).
* `pauliChannel_iff_chi_diagonal` — a Pauli channel is diagonal χ, and has diagonal `R` (T50.3.2).
* `chi_diag_isDistribution` — with every outcome bit unread, χ's diagonal is a distribution with
  values in `ℤ[ζ_{2^∞}, ½]` (T50.3.2).

## Implementation notes

* **Precision.** The theorems on protocols take `1 ≤ m`, as T49's do; the definitions are total.
* **Indices.** Matrices on the data bits are indexed by `Fin n → ZMod 2`, row the output word and
  column the input, as T49's `dilation` is. χ and `R` are indexed by `Pauli n`.
* **The duality's form.** `ptm_diag_eq_walsh_chi_diag` states both `2^n Ŵ` and the explicit sum, so
  that neither normalisation is left to the reader.

## References

* I. L. Chuang and M. A. Nielsen, *Prescription for experimental determination of the dynamics of a
  quantum black box*, arXiv:quant-ph/9610001, equation (3.2): the χ matrix. Not in the pinned
  corpus; the fidelity note's Claim 10.
* S. T. Flammia and J. J. Wallman, *Efficient estimation of Pauli channels*, arXiv:1907.12976,
  equations (11) and (16) to (20): Pauli channels, their rates and eigenvalues. Not in the pinned
  corpus; Claims 16, 18 and 21.
* Y. Zhang, W. Yu, P. Zeng, G. Liu and X. Ma, arXiv:2203.10320, equation (A23): the diagonal duality
  for a general channel. Not in the pinned corpus; Claims 14 and 15.
* The corpus units are cited above the declarations that restate them.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Matrix

variable {n : ℕ}

/-! ## The symplectic Walsh transform as the H-word -/

/-- **A Pauli read off `n + n` bits**: the X bits `a` are the first `n`, the Z bits `b` the last
`n`. -/
def pauliOfBits (v : Fin (n + n) → ZMod 2) : Pauli n :=
  ⟨v ∘ Fin.castAdd n, v ∘ Fin.natAdd n⟩

/-- **The symplectic relabelling** of a Pauli's bits: the Z bits `b` first and the X bits `a`
last, the X and Z halves of `(a, b)` exchanged. The pairing `ω(p, q)` is the dot product of `p`'s
bits `(p.X, p.Z)` with `symplecticBits q`; the Bell reading's first half holds the Z bits, so it
reads at these bits too. -/
def symplecticBits (q : Pauli n) : Fin (n + n) → ZMod 2 :=
  Fin.append q.Z q.X

-- source: papers/higher_order_fourier/
-- HinscheBao_2025_clifford_testing_algorithms_lower_bounds_2510.07164 definition:h22d0e218494a
/-- **The symplectic Walsh transform** `Ŵ` on `2n` bits:
`Ŵf(q) = 2^{−n} Σ_p (−1)^{ω(p, q)} f(p)`, with `ω` the symplectic pairing (`omega`, the source's
`[x, y] = a·b′ + a′·b` with `x = (p.X, p.Z)`). Normalised as the H-word is (`walsh2n_eq_runAmp`):
`2^{−n}` is `(1/√2)^{2n}`. The duality and a Pauli channel's eigenvalues are `2^n Ŵ`, the
unnormalised transform. -/
noncomputable def walsh2n (f : Pauli n → ℂ) (q : Pauli n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ p : Pauli n, signOf (omega p q) * f p

/-- **The H-word** on `N` bits at precision `m`: H on every bit, in order. -/
def hadamardLayer (N m : ℕ) : GateWord N m :=
  List.ofFn GateLetter.hadamard

/-- The function `w ↦ Π_i φ_i(w_i)` on `N` bits, a product of one-bit functions. -/
private def productAmp {N : ℕ} (φ : Fin N → ZMod 2 → ℂ) : (Fin N → ZMod 2) → ℂ :=
  fun w => ∏ i, φ i (w i)

/-- H on one bit, on a one-bit function: `x ↦ (1/√2)(φ(0) + (−1)^x φ(1))`, the one-bit case of
`walshTransform`. -/
private noncomputable def walshBit (φ : ZMod 2 → ℂ) : ZMod 2 → ℂ :=
  fun x => (1 / (Real.sqrt 2 : ℂ)) * (φ 0 + signOf x * φ 1)

/-- A product of one-bit functions at a word updated at `k`: the `k`-th factor at the new bit,
the others at the word. -/
private theorem productAmp_update {N : ℕ} (φ : Fin N → ZMod 2 → ℂ) (w : Fin N → ZMod 2)
    (k : Fin N) (c : ZMod 2) :
    productAmp φ (Function.update w k c) = φ k c * ∏ i ∈ ({k} : Finset (Fin N))ᶜ, φ i (w i) := by
  unfold productAmp
  rw [Fintype.prod_eq_mul_prod_compl k, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (fun h => Finset.mem_compl.mp hi (Finset.mem_singleton.mpr h))]

/-- H at bit `k` on a product of one-bit functions is the product with the `k`-th factor
transformed by `walshBit`. -/
private theorem walshTransform_productAmp {N : ℕ} (k : Fin N) (φ : Fin N → ZMod 2 → ℂ) :
    walshTransform k (productAmp φ) = productAmp (Function.update φ k (walshBit (φ k))) := by
  funext w
  have hrest : ∏ i ∈ ({k} : Finset (Fin N))ᶜ, Function.update φ k (walshBit (φ k)) i (w i)
      = ∏ i ∈ ({k} : Finset (Fin N))ᶜ, φ i (w i) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (fun h => Finset.mem_compl.mp hi (Finset.mem_singleton.mpr h))]
  unfold walshTransform
  rw [productAmp_update, productAmp_update]
  unfold productAmp
  rw [Fintype.prod_eq_mul_prod_compl k, Function.update_self, hrest]
  unfold walshBit
  ring

/-- **H on a list of distinct bits, on a product**: each listed factor is transformed once, by
`amp_applyH`'s referee `walshTransform` letter by letter. -/
private theorem runAmp_map_hadamard_productAmp {N m : ℕ} (l : List (Fin N)) (hl : l.Nodup)
    (φ : Fin N → ZMod 2 → ℂ) :
    runAmp (l.map (GateLetter.hadamard (m := m))) (productAmp φ)
      = productAmp (fun i => if i ∈ l then walshBit (φ i) else φ i) := by
  induction l generalizing φ with
  | nil => simp only [List.map_nil, runAmp_nil, List.not_mem_nil, if_false]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, runAmp_cons]
    change runAmp (l.map GateLetter.hadamard) (walshTransform k (productAmp φ)) = _
    rw [walshTransform_productAmp, ih hl.2]
    congr 1
    funext i
    by_cases hik : i = k
    · subst hik
      rw [if_neg hl.1, Function.update_self, if_pos List.mem_cons_self]
    · rw [Function.update_of_ne hik]
      simp only [List.mem_cons, hik, false_or]

/-- `(−1)^{a + b} = (−1)^a (−1)^b`. -/
private theorem signOf_add (a b : ZMod 2) : signOf (a + b) = signOf a * signOf b := by
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl
  · rw [add_zero, signOf_zero, one_mul]
  · rw [zero_add, signOf_zero, one_mul]
  · rw [add_zero, signOf_zero, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, signOf_zero, signOf_one]
    ring

/-- The sign of a sum is the product of the signs. -/
private theorem signOf_sum {N : ℕ} (s : Finset (Fin N)) (g : Fin N → ZMod 2) :
    signOf (∑ i ∈ s, g i) = ∏ i ∈ s, signOf (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, signOf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signOf_add, ih]

/-- H on one bit sends the indicator of `b` to `x ↦ (1/√2)(−1)^{x b}`. -/
private theorem walshBit_indicator (b : ZMod 2) :
    walshBit (fun x => if x = b then (1 : ℂ) else 0)
      = fun x => (1 / (Real.sqrt 2 : ℂ)) * signOf (x * b) := by
  funext x
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  unfold walshBit
  beta_reduce
  rcases h b with rfl | rfl
  · rw [if_pos rfl, if_neg (show (1 : ZMod 2) ≠ 0 by decide)]
    simp only [mul_zero, add_zero, signOf_zero]
  · rw [if_neg (show (0 : ZMod 2) ≠ 1 by decide), if_pos rfl]
    simp only [mul_one, zero_add]

/-- A word's referee is zero on the zero function. -/
private theorem runAmp_zero {N m : ℕ} (W : GateWord N m) : runAmp W 0 = 0 := by
  have h := runAmp_add_smul W 0 0 1
  rw [one_smul, add_zero, one_smul] at h
  exact left_eq_add.mp h

/-- A word's referee commutes with a finite linear combination. -/
private theorem runAmp_sum_smul {N m : ℕ} (W : GateWord N m) {α : Type*} (s : Finset α)
    (c : α → ℂ) (g : α → (Fin N → ZMod 2) → ℂ) :
    runAmp W (∑ a ∈ s, c a • g a) = ∑ a ∈ s, c a • runAmp W (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, runAmp_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, runAmp_add_smul, ih, add_comm]

/-- A function on `N` bits is the combination of the indicators of its words, each indicator a
product of one-bit indicators. -/
private theorem eq_sum_productAmp_indicator {N : ℕ} (g : (Fin N → ZMod 2) → ℂ) :
    g = ∑ v, g v • productAmp (fun i x => if x = v i then (1 : ℂ) else 0) := by
  funext u
  rw [Finset.sum_apply, Finset.sum_eq_single u]
  · rw [Pi.smul_apply, smul_eq_mul]
    unfold productAmp
    rw [Finset.prod_eq_one (fun i _ => if_pos rfl), mul_one]
  · intro v _ hv
    rw [Pi.smul_apply, smul_eq_mul]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (Ne.symm hv)
    unfold productAmp
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

/-- **The H-word on `N` bits is the full Walsh transform**, `(1/√2)^N Σ_v (−1)^{w·v} g(v)`: by
linearity on the indicators of words, each a product on which the letters act factor by
factor. -/
private theorem runAmp_hadamardLayer {N m : ℕ} (g : (Fin N → ZMod 2) → ℂ) (w : Fin N → ZMod 2) :
    runAmp (hadamardLayer N m) g w
      = (1 / (Real.sqrt 2 : ℂ)) ^ N * ∑ v, signOf (∑ i, w i * v i) * g v := by
  have hword : hadamardLayer N m = (List.finRange N).map GateLetter.hadamard :=
    List.ofFn_eq_map
  conv_lhs => rw [eq_sum_productAmp_indicator g]
  rw [runAmp_sum_smul, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [hword, runAmp_map_hadamard_productAmp _ (List.nodup_finRange N), Pi.smul_apply,
    smul_eq_mul]
  unfold productAmp
  simp only [List.mem_finRange, if_true]
  rw [Finset.prod_congr rfl (fun i _ => congrFun (walshBit_indicator (v i)) (w i)),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← signOf_sum]
  ring

/-- The bits of a Pauli, X bits first: `pauliOfBits` is a bijection. -/
private def pauliBitsEquiv : Pauli n ≃ (Fin (n + n) → ZMod 2) where
  toFun p := Fin.append p.X p.Z
  invFun := pauliOfBits
  left_inv p := by
    unfold pauliOfBits
    refine Pauli.ext ?_ ?_
    · funext i
      exact Fin.append_left p.X p.Z i
    · funext i
      exact Fin.append_right p.X p.Z i
  right_inv _ := Fin.append_castAdd_natAdd

/-- The dot product of `q`'s exchanged bits with `p`'s bits is `ω(p, q)`. -/
private theorem sum_symplecticBits_mul (p q : Pauli n) :
    ∑ i, symplecticBits q i * Fin.append p.X p.Z i = omega p q := by
  unfold symplecticBits omega
  rw [Fin.sum_univ_add, add_comm]
  simp only [Fin.append_left, Fin.append_right]
  congr 1 <;> exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- `(1/√2)^{2n} = 2^{−n}`: the H-word's normalisation is `Ŵ`'s. -/
private theorem one_div_sqrt_two_pow_add (n : ℕ) :
    (1 / (Real.sqrt 2 : ℂ)) ^ (n + n) = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← two_mul, pow_mul, div_pow, one_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_ofNat, one_div, inv_pow]

/-- **`Ŵ` is the H-word after the symplectic relabelling.** At any precision, the referee of H on
all `2n` bits (T05's `runAmp`, the Walsh transform letter by letter, `amp_applyH`), applied to `f`
read through `pauliOfBits` and evaluated at `q`'s exchanged bits `symplecticBits q`, is `Ŵf(q)`,
with the same normalisation. Proved at T50.3.1. -/
theorem walsh2n_eq_runAmp (m : ℕ) (f : Pauli n → ℂ) (q : Pauli n) :
    walsh2n f q = runAmp (hadamardLayer (n + n) m) (f ∘ pauliOfBits) (symplecticBits q) := by
  rw [runAmp_hadamardLayer, one_div_sqrt_two_pow_add, walsh2n,
    ← Equiv.sum_comp pauliBitsEquiv]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  change _ = signOf (∑ i, symplecticBits q i * Fin.append p.X p.Z i)
    * f (pauliOfBits (pauliBitsEquiv p))
  rw [sum_symplecticBits_mul,
    show pauliOfBits (pauliBitsEquiv p) = p from pauliBitsEquiv.left_inv p]

/-! ## Pauli coefficients and the Kraus operators -/

/-- **The Pauli `X^a Z^b`** with `a = P.X`, `b = P.Z`, as a matrix on the data words, row the output
and column the input: `∣x⟩ ↦ (−1)^{b·x} ∣x ⊕ a⟩`. Real, with entries those of `pauliOperator P`
(Hilbert side, not imported); the frame's Hermitian `pauliAct P` is `i^{a·b}` times it. -/
noncomputable def pauliMatrix (P : Pauli n) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  fun w x => if w = x + P.X then (-1 : ℂ) ^ zDot P x else 0

-- source: papers/higher_order_fourier/
-- HinscheBao_2025_clifford_testing_algorithms_lower_bounds_2510.07164 definition:he02cb23f1a96
/-- **The Pauli coefficient** of a matrix `K` at `P`: `c(P) = 2^{−n} tr(P† K)`, with `P` the real
`X^a Z^b` (`pauliMatrix`). The source's Fourier coefficient is `tr(A P_x)/2^n` for the Hermitian
Weyl operator `P_x = i^{a·b} X^a Z^b`; in the real convention the dagger is needed, and the two
coefficients differ by the unit phase `i^{a·b}`, which no diagonal statement below sees. -/
noncomputable def pauliCoeff (K : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (P : Pauli n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * trace ((pauliMatrix P)ᴴ * K)

/-- **The Kraus operator** `K_{o,e}` of a protocol read through `σ`, at the read string `o` and the
unread string `e`: the `2^n × 2^n` block of T49's dilation at `(o, e)`, row the data word out and
column the data word in. The branch at `o` is `ρ ↦ Σ_e K_{o,e} ρ K_{o,e}†`. -/
noncomputable def krausOp {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (o : Fin r → ZMod 2) (e : Fin u → ZMod 2) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  fun w x => dilation p σ ((w, o), e) x

/-! ### The proofs' lemmas: signs and the character sum -/

/-- The dot product `b·x = Σ_i b_i x_i` of two words, in `ZMod 2`. -/
private def bitDot (b x : Fin n → ZMod 2) : ZMod 2 :=
  ∑ i, b i * x i

/-- The dot product is symmetric. -/
private theorem bitDot_comm (b x : Fin n → ZMod 2) : bitDot b x = bitDot x b := by
  unfold bitDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The dot product is additive on the left. -/
private theorem bitDot_add_left (b b' x : Fin n → ZMod 2) :
    bitDot (b + b') x = bitDot b x + bitDot b' x := by
  unfold bitDot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])

/-- The dot product is additive on the right. -/
private theorem bitDot_add_right (b x x' : Fin n → ZMod 2) :
    bitDot b (x + x') = bitDot b x + bitDot b x' := by
  rw [bitDot_comm, bitDot_add_left, bitDot_comm x, bitDot_comm x']

/-- `(−1)^a (−1)^a = 1`. -/
private theorem signOf_mul_self (a : ZMod 2) : signOf a * signOf a = 1 := by
  have h : a + a = 0 := by
    have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
    exact h2 a
  rw [← signOf_add, h, signOf_zero]

/-- A Walsh sign is real. -/
private theorem conj_signOf (a : ZMod 2) : starRingEnd ℂ (signOf a) = signOf a := by
  unfold signOf
  split <;> simp

/-- `(−1)` to the power `zDot P x` is the Walsh sign of the dot product `P.Z · x`. -/
private theorem neg_one_pow_zDot (P : Pauli n) (x : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDot P x = signOf (bitDot P.Z x) := by
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  unfold zDot bitDot
  rw [← Finset.prod_pow_eq_pow_sum, signOf_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rcases h (P.Z i) with h1 | h1 <;> rcases h (x i) with h2 | h2 <;> rw [h1, h2]
  · rw [ZMod.val_zero, mul_zero, pow_zero, mul_zero, signOf_zero]
  · rw [ZMod.val_zero, zero_mul, pow_zero, zero_mul, signOf_zero]
  · rw [ZMod.val_zero, mul_zero, pow_zero, mul_zero, signOf_zero]
  · rw [show (1 : ZMod 2).val = 1 from rfl, mul_one, pow_one, mul_one, signOf_one]

/-- **The character sum**: `Σ_w (−1)^{z·w}` is `2^n` at `z = 0` and `0` otherwise. -/
private theorem sum_signOf_bitDot (z : Fin n → ZMod 2) :
    ∑ w : Fin n → ZMod 2, signOf (bitDot z w) = if z = 0 then (2 : ℂ) ^ n else 0 := by
  have hbit : ∀ g : ZMod 2 → ℂ, ∑ c, g c = g 0 + g 1 := fun g => Fin.sum_univ_two g
  have hsum : ∀ w : Fin n → ZMod 2, signOf (bitDot z w) = ∏ i, signOf (z i * w i) :=
    fun w => signOf_sum _ _
  simp only [hsum]
  rw [← Fintype.prod_sum (fun i c => signOf (z i * c))]
  simp only [hbit, mul_zero, mul_one, signOf_zero]
  by_cases hz : z = 0
  · subst hz
    rw [if_pos rfl]
    simp only [Pi.zero_apply, signOf_zero]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  · rw [if_neg hz]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [(h (z i)).resolve_left hi, signOf_one]
    ring

/-- In `ZMod 2`, `w = x + a` exactly when `x = w + a`. -/
private theorem eq_add_iff_eq_add (w x a : Fin n → ZMod 2) : w = x + a ↔ x = w + a := by
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  constructor <;> rintro rfl <;> funext i <;> simp only [Pi.add_apply, add_assoc, h, add_zero]

/-- In `ZMod 2`, `y + x = 0` exactly when `y = x`. -/
private theorem bits_add_eq_zero_iff (y x : Fin n → ZMod 2) : y + x = 0 ↔ y = x := by
  rw [add_eq_zero_iff_eq_neg]
  have h : -x = x := funext fun i => ZMod.neg_eq_self_mod_two (x i)
  rw [h]

/-! ### The proofs' lemmas: Pauli matrices -/

/-- `X^a Z^b` entry by entry, with the Walsh sign of the dot product. -/
private theorem pauliMatrix_apply (P : Pauli n) (w x : Fin n → ZMod 2) :
    pauliMatrix P w x = if w = x + P.X then signOf (bitDot P.Z x) else 0 := by
  unfold pauliMatrix
  rw [neg_one_pow_zDot]

/-- `X^a Z^b` entry by entry, read along the row. -/
private theorem pauliMatrix_apply' (P : Pauli n) (w x : Fin n → ZMod 2) :
    pauliMatrix P w x = if x = w + P.X then signOf (bitDot P.Z (w + P.X)) else 0 := by
  rw [pauliMatrix_apply]
  by_cases h : x = w + P.X
  · rw [if_pos h, if_pos ((eq_add_iff_eq_add w x P.X).mpr h), h]
  · rw [if_neg h, if_neg (fun h' => h ((eq_add_iff_eq_add w x P.X).mp h'))]

/-- `P† M` at `(w, x)` is `(−1)^{b·w} M(w + a, x)`. -/
private theorem conjTranspose_pauliMatrix_mul_apply (P : Pauli n)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (w x : Fin n → ZMod 2) :
    ((pauliMatrix P)ᴴ * M) w x = signOf (bitDot P.Z w) * M (w + P.X) x := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, pauliMatrix_apply, Complex.star_def,
    apply_ite (starRingEnd ℂ), map_zero, conj_signOf, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- `P M` at `(w, x)` is `(−1)^{b·(w + a)} M(w + a, x)`. -/
private theorem pauliMatrix_mul_apply (P : Pauli n)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (w x : Fin n → ZMod 2) :
    (pauliMatrix P * M) w x = signOf (bitDot P.Z (w + P.X)) * M (w + P.X) x := by
  rw [Matrix.mul_apply]
  simp only [pauliMatrix_apply', ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `M P` at `(w, x)` is `M(w, x + a) (−1)^{b·x}`. -/
private theorem mul_pauliMatrix_apply (P : Pauli n)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (w x : Fin n → ZMod 2) :
    (M * pauliMatrix P) w x = M w (x + P.X) * signOf (bitDot P.Z x) := by
  rw [Matrix.mul_apply]
  simp only [pauliMatrix_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `M P†` at `(w, x)` is `M(w, x + a) (−1)^{b·(x + a)}`. -/
private theorem mul_conjTranspose_pauliMatrix_apply (P : Pauli n)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (w x : Fin n → ZMod 2) :
    (M * (pauliMatrix P)ᴴ) w x = M w (x + P.X) * signOf (bitDot P.Z (x + P.X)) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, pauliMatrix_apply', Complex.star_def,
    apply_ite (starRingEnd ℂ), map_zero, conj_signOf, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- `tr(P† M) = Σ_w (−1)^{b·w} M(w + a, w)`. -/
private theorem trace_conjTranspose_pauliMatrix_mul (P : Pauli n)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    trace ((pauliMatrix P)ᴴ * M) = ∑ w, signOf (bitDot P.Z w) * M (w + P.X) w := by
  simp only [Matrix.trace, Matrix.diag, conjTranspose_pauliMatrix_mul_apply]

/-- **Orthogonality**: `tr(P† Q) = 2^n δ_{P, Q}`. -/
private theorem trace_pauliMatrix_orth (P Q : Pauli n) :
    trace ((pauliMatrix P)ᴴ * pauliMatrix Q) = if P = Q then (2 : ℂ) ^ n else 0 := by
  rw [trace_conjTranspose_pauliMatrix_mul]
  simp only [pauliMatrix_apply]
  by_cases hX : P.X = Q.X
  · have hw : ∀ w : Fin n → ZMod 2, w + P.X = w + Q.X := fun w => by rw [hX]
    simp only [hw, if_true]
    rw [Finset.sum_congr rfl (fun w _ => (signOf_add _ _).symm)]
    simp only [← bitDot_add_left]
    rw [sum_signOf_bitDot]
    have hiff : P.Z + Q.Z = 0 ↔ P = Q := by
      rw [Pauli.ext_iff, bits_add_eq_zero_iff]
      exact ⟨fun h => ⟨hX, h⟩, fun h => h.2⟩
    by_cases hPQ : P = Q
    · rw [if_pos (hiff.mpr hPQ), if_pos hPQ]
    · rw [if_neg (fun h => hPQ (hiff.mp h)), if_neg hPQ]
  · have hw : ∀ w : Fin n → ZMod 2, ¬ (w + P.X = w + Q.X) := fun w h => hX (add_left_cancel h)
    simp only [hw, if_false, mul_zero, Finset.sum_const_zero]
    rw [if_neg (fun h => hX (by rw [h]))]

/-- The Pauli coefficients of a combination of Paulis are its coefficients. -/
private theorem pauliCoeff_sum_smul (d : Pauli n → ℂ) (P : Pauli n) :
    pauliCoeff (∑ Q, d Q • pauliMatrix Q) P = d P := by
  unfold pauliCoeff
  rw [Matrix.mul_sum, Matrix.trace_sum]
  simp only [Matrix.mul_smul, Matrix.trace_smul, trace_pauliMatrix_orth, smul_eq_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [mul_comm, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), mul_one]

/-- **Linear independence**: a combination of Paulis vanishing at every entry has every
coefficient zero. -/
private theorem eq_zero_of_sum_mul_pauliMatrix (d : Pauli n → ℂ)
    (h : ∀ w x, ∑ P, d P * pauliMatrix P w x = 0) (P : Pauli n) : d P = 0 := by
  have hM : ∑ Q, d Q • pauliMatrix Q = 0 := by
    ext w x
    rw [Matrix.sum_apply]
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h w x
  rw [← pauliCoeff_sum_smul d P, hM]
  unfold pauliCoeff
  rw [Matrix.mul_zero, Matrix.trace_zero, mul_zero]

/-- The Paulis with their bits. -/
private def pauliProdEquiv : ((Fin n → ZMod 2) × (Fin n → ZMod 2)) ≃ Pauli n where
  toFun ab := ⟨ab.1, ab.2⟩
  invFun P := (P.X, P.Z)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A sum over the Paulis is a sum over their X bits and their Z bits. -/
private theorem sum_pauli (f : Pauli n → ℂ) :
    ∑ P, f P = ∑ a : Fin n → ZMod 2, ∑ b : Fin n → ZMod 2, f ⟨a, b⟩ := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv pauliProdEquiv _ _ (fun _ => rfl)).symm

/-- `x + (w + x) = w` in `ZMod 2`. -/
private theorem add_add_self_left (w x : Fin n → ZMod 2) : x + (w + x) = w := by
  funext i
  simp only [Pi.add_apply]
  generalize w i = p
  generalize x i = q
  revert p q
  decide

/-- **The Pauli expansion**: every matrix is `Σ_P c(P) P`, with `c(P) = 2^{−n} tr(P† M)`. -/
private theorem pauli_expansion (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    M = ∑ P, pauliCoeff M P • pauliMatrix P := by
  ext w x
  rw [Matrix.sum_apply, sum_pauli]
  simp only [Matrix.smul_apply, smul_eq_mul, pauliMatrix_apply]
  rw [Finset.sum_eq_single (w + x)]
  · have hw : w = x + (w + x) := (add_add_self_left w x).symm
    simp only [← hw, if_true]
    have hinner : ∀ y : Fin n → ZMod 2,
        ∑ b : Fin n → ZMod 2, signOf (bitDot b y) * signOf (bitDot b x)
          = if y = x then (2 : ℂ) ^ n else 0 := fun y => by
      have hs : ∑ b : Fin n → ZMod 2, signOf (bitDot b y) * signOf (bitDot b x)
          = ∑ b : Fin n → ZMod 2, signOf (bitDot (y + x) b) :=
        Finset.sum_congr rfl (fun b _ => by rw [← signOf_add, ← bitDot_add_right, bitDot_comm])
      rw [hs, sum_signOf_bitDot]
      by_cases hyx : y = x
      · rw [if_pos hyx, if_pos ((bits_add_eq_zero_iff y x).mpr hyx)]
      · rw [if_neg hyx, if_neg (fun h => hyx ((bits_add_eq_zero_iff y x).mp h))]
    simp only [pauliCoeff, trace_conjTranspose_pauliMatrix_mul]
    symm
    calc ∑ b : Fin n → ZMod 2, ((2 : ℂ) ^ n)⁻¹ * (∑ y : Fin n → ZMod 2,
          signOf (bitDot b y) * M (y + (w + x)) y) * signOf (bitDot b x)
        = ∑ y : Fin n → ZMod 2, ((2 : ℂ) ^ n)⁻¹ * M (y + (w + x)) y
            * ∑ b : Fin n → ZMod 2, signOf (bitDot b y) * signOf (bitDot b x) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun b _ => ?_))
          ring
      _ = M w x := by
          simp only [hinner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          rw [add_add_self_left, mul_comm, ← mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [if_neg (fun h => ha ((eq_add_iff_eq_add w a x).mp (h.trans (add_comm x a)))), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Conjugating a Pauli by a Pauli**: `Q† P Q = (−1)^{ω(P, Q)} P`. -/
private theorem conjTranspose_mul_mul_pauliMatrix (P Q : Pauli n) :
    (pauliMatrix Q)ᴴ * pauliMatrix P * pauliMatrix Q = signOf (omega P Q) • pauliMatrix P := by
  ext w x
  rw [mul_pauliMatrix_apply, conjTranspose_pauliMatrix_mul_apply, Matrix.smul_apply, smul_eq_mul,
    pauliMatrix_apply, pauliMatrix_apply]
  by_cases h : w = x + P.X
  · have h' : w + Q.X = x + Q.X + P.X := by rw [h, add_right_comm]
    rw [if_pos h', if_pos h, h]
    have hω : omega P Q = bitDot P.Z Q.X + bitDot Q.Z P.X := by
      rw [bitDot_comm Q.Z]
      rfl
    rw [hω]
    simp only [bitDot_add_right, signOf_add]
    linear_combination (signOf (bitDot Q.Z P.X) * signOf (bitDot P.Z x)
      * signOf (bitDot P.Z Q.X)) * signOf_mul_self (bitDot Q.Z x)
  · have h' : ¬ (w + Q.X = x + Q.X + P.X) := fun h' =>
      h (add_right_cancel (h'.trans (add_right_comm _ _ _)))
    rw [if_neg h', if_neg h, mul_zero, zero_mul, mul_zero]

/-- **Conjugating a Pauli by a Pauli**, the other way: `P Q P† = (−1)^{ω(Q, P)} Q`. -/
private theorem pauliMatrix_mul_mul_conjTranspose (P Q : Pauli n) :
    pauliMatrix P * pauliMatrix Q * (pauliMatrix P)ᴴ = signOf (omega Q P) • pauliMatrix Q := by
  ext w x
  rw [mul_conjTranspose_pauliMatrix_apply, pauliMatrix_mul_apply, Matrix.smul_apply, smul_eq_mul,
    pauliMatrix_apply, pauliMatrix_apply]
  by_cases h : w = x + Q.X
  · have h' : w + P.X = x + P.X + Q.X := by rw [h, add_right_comm]
    rw [if_pos h', if_pos h, h]
    have hω : omega Q P = bitDot Q.Z P.X + bitDot P.Z Q.X := by
      rw [bitDot_comm P.Z]
      rfl
    rw [hω]
    simp only [bitDot_add_right, signOf_add]
    linear_combination (signOf (bitDot P.Z Q.X) * signOf (bitDot Q.Z x)
        * signOf (bitDot Q.Z P.X) * signOf (bitDot P.Z P.X) * signOf (bitDot P.Z P.X))
        * signOf_mul_self (bitDot P.Z x)
      + (signOf (bitDot P.Z Q.X) * signOf (bitDot Q.Z x) * signOf (bitDot Q.Z P.X))
        * signOf_mul_self (bitDot P.Z P.X)
  · have h' : ¬ (w + P.X = x + P.X + Q.X) := fun h' =>
      h (add_right_cancel (h'.trans (add_right_comm _ _ _)))
    rw [if_neg h', if_neg h, mul_zero, zero_mul, mul_zero]

/-! ### The proofs' lemmas: the ring condition

The first two restate private lemmas of `FTQCLib.Carrier.UnreadBits` (and of
`FTQCLib.Carrier.Doubling`), with the same names. -/

/-- `½` lies in the ring. -/
private theorem inv_two_mem_dyadicCyclotomicRing : (2 : ℂ)⁻¹ ∈ dyadicCyclotomicRing :=
  Subring.subset_closure (Or.inl rfl)

/-- A Walsh sign lies in the ring. -/
private theorem signOf_mem_dyadicCyclotomicRing (b : ZMod 2) :
    signOf b ∈ dyadicCyclotomicRing := by
  unfold signOf
  split
  · exact Subring.one_mem _
  · exact Subring.neg_mem _ (Subring.one_mem _)

/-- Every entry of a Kraus operator lies in the ring: it is a Choi amplitude (`amp_choi`,
`choi_mem_dyadic`). -/
private theorem krausOp_mem_dyadicCyclotomicRing {m k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (hm : 1 ≤ m) (o : Fin r → ZMod 2) (e : Fin u → ZMod 2)
    (w x : Fin n → ZMod 2) : krausOp p σ o e w x ∈ dyadicCyclotomicRing := by
  change p.interpretAmp (delta x) (Fin.append w (Fin.append o e ∘ σ)) ∈ _
  rw [← amp_choi p hm]
  exact choi_mem_dyadic p hm _

/-- A matrix with entries in the ring has its Pauli coefficients in the ring. -/
private theorem pauliCoeff_mem_dyadicCyclotomicRing
    (K : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hK : ∀ w x, K w x ∈ dyadicCyclotomicRing)
    (P : Pauli n) : pauliCoeff K P ∈ dyadicCyclotomicRing := by
  rw [pauliCoeff, trace_conjTranspose_pauliMatrix_mul, ← inv_pow]
  exact Subring.mul_mem _ (Subring.pow_mem _ inv_two_mem_dyadicCyclotomicRing n)
    (Subring.sum_mem _ (fun w _ =>
      Subring.mul_mem _ (signOf_mem_dyadicCyclotomicRing _) (hK _ _)))

/-! ## The Bell reading of the Choi state -/

/-- A bit of the doubled register `n + n`, as a bit of the read register `((n + n) + r) + u`: the
reference and data bits come first. -/
def doubledBit (n r u : ℕ) (i : Fin (n + n)) : Fin (((n + n) + r) + u) :=
  Fin.castAdd u (Fin.castAdd r i)

/-- The reference bit `i` and the data bit `n + i` are distinct bits of the read register. -/
theorem doubledBit_castAdd_ne_natAdd (n r u : ℕ) (i : Fin n) :
    doubledBit n r u (Fin.castAdd n i) ≠ doubledBit n r u (Fin.natAdd n i) := fun h =>
  castAdd_ne_natAdd i i (Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h))

/-- **The Bell reading word** on the read register of a Choi state at precision `m`: CNOT from each
reference bit `i` to the data bit `n + i`, then H on each reference bit. A T05 word, so it runs a
carrier state to a carrier state; the outcome bits are spectators. -/
def bellReadWord (n r u m : ℕ) : GateWord (((n + n) + r) + u) m :=
  List.ofFn (fun i : Fin n => GateLetter.cnot (doubledBit n r u (Fin.castAdd n i))
      (doubledBit n r u (Fin.natAdd n i)) (doubledBit_castAdd_ne_natAdd n r u i))
    ++ List.ofFn (fun i : Fin n => GateLetter.hadamard (doubledBit n r u (Fin.castAdd n i)))

/-- **The Choi state read in the Bell basis**: `bellReadWord` run on T49's `choiRead p σ`. Its
first half holds the Z bits of a Pauli, its second the X bits, then the read and the unread outcome
bits. -/
noncomputable def bellRead {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) :
    KernelSumState (((n + n) + r) + u) :=
  run (bellReadWord n r u m) (choiRead p σ)

/-! ### The proofs' lemmas: the Bell reading word, block by block -/

/-- A letter on `N` bits, read on `N + K` bits at the first `N`. -/
private noncomputable def castAddLetter {N M : ℕ} (K : ℕ) : GateLetter N M → GateLetter (N + K) M
  | .hadamard i => .hadamard (Fin.castAdd K i)
  | .diagonal D => .diagonal (MvPolynomial.rename (Fin.castAdd K) D)
  | .cnot i j hij => .cnot (Fin.castAdd K i) (Fin.castAdd K j)
      fun h => hij (Fin.castAdd_injective N K h)

/-- A letter moved onto the first block acts on the slice at the last block's word. -/
private theorem letterAmp_castAddLetter {N M K : ℕ} (l : GateLetter N M)
    (F : (Fin (N + K) → ZMod 2) → ℂ) (t : Fin K → ZMod 2) :
    (fun v => letterAmp (castAddLetter K l) F (Fin.append v t))
      = letterAmp l (fun v => F (Fin.append v t)) := by
  funext v
  cases l with
  | hadamard i =>
    change walshTransform (Fin.castAdd K i) F (Fin.append v t)
      = walshTransform i (fun v => F (Fin.append v t)) v
    unfold walshTransform
    rw [update_append_castAdd, update_append_castAdd, Fin.append_left]
  | diagonal D =>
    change charOf M (DiagPhase.eval (MvPolynomial.rename (Fin.castAdd K) D) (Fin.append v t))
        * F (Fin.append v t)
      = charOf M (DiagPhase.eval D v) * F (Fin.append v t)
    rw [eval_rename_castAdd]
  | cnot i j hij =>
    change F (DiagPhase.cnotBitMap (Fin.castAdd K i) (Fin.castAdd K j) (Fin.append v t))
      = F (Fin.append (DiagPhase.cnotBitMap i j v) t)
    unfold DiagPhase.cnotBitMap
    rw [Fin.append_left, Fin.append_left, update_append_castAdd]

/-- A word moved onto the first block acts on the slice at the last block's word. -/
private theorem runAmp_castAddWord {N M K : ℕ} (W : GateWord N M)
    (F : (Fin (N + K) → ZMod 2) → ℂ) (v : Fin N → ZMod 2) (t : Fin K → ZMod 2) :
    runAmp (W.map (castAddLetter K)) F (Fin.append v t)
      = runAmp W (fun v' => F (Fin.append v' t)) v := by
  induction W generalizing F with
  | nil => rfl
  | cons l W ih =>
    rw [List.map_cons, runAmp_cons, runAmp_cons, ih, letterAmp_castAddLetter]

/-- The Bell reading word on the doubled register `n + n` alone: CNOT from each reference bit `i`
to the data bit `n + i`, then H on each reference bit. -/
private noncomputable def bellPairWord (n m : ℕ) : GateWord (n + n) m :=
  List.ofFn (fun i : Fin n => GateLetter.cnot (Fin.castAdd n i) (Fin.natAdd n i)
      (castAdd_ne_natAdd i i))
    ++ (hadamardLayer n m).map (castAddLetter n)

/-- The Bell reading word is `bellPairWord` on the first block, the outcome bits spectators. -/
private theorem bellReadWord_eq (n r u m : ℕ) :
    bellReadWord n r u m = ((bellPairWord n m).map (castAddLetter r)).map (castAddLetter u) := by
  unfold bellReadWord bellPairWord hadamardLayer
  simp only [List.map_append, List.map_ofFn]
  rfl

/-- **The CNOT layer** over a list of distinct pairs: at `(x, y)` it reads the input at
`(x, y + x_l)`, `x_l` the reference word on the listed bits. -/
private theorem runAmp_cnotPairs {m : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (G : (Fin (n + n) → ZMod 2) → ℂ) (x y : Fin n → ZMod 2) :
    runAmp (l.map (fun i => (GateLetter.cnot (Fin.castAdd n i) (Fin.natAdd n i)
        (castAdd_ne_natAdd i i) : GateLetter (n + n) m))) G (Fin.append x y)
      = G (Fin.append x (y + fun j => if j ∈ l then x j else 0)) := by
  induction l generalizing G with
  | nil =>
    have h0 : (fun j : Fin n => if j ∈ ([] : List (Fin n)) then x j else 0) = 0 := by
      funext j
      simp
    rw [h0, add_zero]
    rfl
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, runAmp_cons, ih hl.2]
    change G (DiagPhase.cnotBitMap (Fin.castAdd n k) (Fin.natAdd n k) (Fin.append x _)) = _
    unfold DiagPhase.cnotBitMap
    rw [Fin.append_left, Fin.append_right, update_append_natAdd]
    congr 2
    funext j
    by_cases hjk : j = k
    · subst hjk
      simp [hl.1]
    · rw [Function.update_of_ne hjk]
      simp [hjk]

/-- **The Bell reading on the doubled register**: at `(b, a)` it is
`(1/√2)^n Σ_x (−1)^{b·x} G(x, a + x)`. -/
private theorem runAmp_bellPairWord {m : ℕ} (G : (Fin (n + n) → ZMod 2) → ℂ)
    (b a : Fin n → ZMod 2) :
    runAmp (bellPairWord n m) G (Fin.append b a)
      = (1 / (Real.sqrt 2 : ℂ)) ^ n * ∑ x, signOf (bitDot b x) * G (Fin.append x (a + x)) := by
  unfold bellPairWord
  rw [runAmp_append, runAmp_castAddWord, runAmp_hadamardLayer]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  beta_reduce
  rw [List.ofFn_eq_map, runAmp_cnotPairs _ (List.nodup_finRange n)]
  simp only [List.mem_finRange, if_true]
  rfl

/-- The register of the Choi state read through `σ`, its reference bits `x`, data bits `y` and
read outcome bits `o`, against the protocol's register. Restates the private lemma of
`FTQCLib.Carrier.Doubling` with the same name and proof. -/
private theorem append_comp_readingEquiv {n k r u : ℕ} (σ : Fin k ≃ Fin (r + u))
    (X : Fin ((n + n) + r) → ZMod 2) (e : Fin u → ZMod 2) :
    Fin.append X e ∘ readingEquiv (n + n) σ
      = Fin.append ((X ∘ Fin.castAdd r) ∘ Fin.castAdd n)
          (Fin.append ((X ∘ Fin.castAdd r) ∘ Fin.natAdd n)
            (Fin.append (X ∘ Fin.natAdd (n + n)) e ∘ σ))
        ∘ Fin.cast (Nat.add_assoc n n k) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have e1 : readingEquiv (n + n) σ (Fin.castAdd k j) = Fin.castAdd u (Fin.castAdd r j) := by
      simp only [readingEquiv, Equiv.coe_trans, Function.comp_apply,
        finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl, Equiv.coe_refl,
        id_eq, finSumFinEquiv_apply_left, finCongr_apply]
      exact Fin.ext rfl
    rw [Function.comp_apply, Function.comp_apply, e1, Fin.append_left]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · have e2 : Fin.cast (Nat.add_assoc n n k) (Fin.castAdd k (Fin.castAdd n l))
          = Fin.castAdd (n + k) l := Fin.ext rfl
      rw [e2, Fin.append_left]
      rfl
    · have e2 : Fin.cast (Nat.add_assoc n n k) (Fin.castAdd k (Fin.natAdd n l))
          = Fin.natAdd n (Fin.castAdd k l) := Fin.ext rfl
      rw [e2, Fin.append_right, Fin.append_left]
      rfl
  · have e1 : readingEquiv (n + n) σ (Fin.natAdd (n + n) j)
        = Fin.cast (Nat.add_assoc (n + n) r u).symm (Fin.natAdd (n + n) (σ j)) := by
      simp only [readingEquiv, Equiv.coe_trans, Function.comp_apply,
        finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right, finCongr_apply]
    have e2 : Fin.cast (Nat.add_assoc n n k) (Fin.natAdd (n + n) j)
        = Fin.natAdd n (Fin.natAdd n j) := Fin.ext (by simp; omega)
    rw [Function.comp_apply, Function.comp_apply, e1, e2, Fin.append_right, Fin.append_right,
      Function.comp_apply]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) (σ j)
    · have e3 : Fin.cast (Nat.add_assoc (n + n) r u).symm (Fin.natAdd (n + n) (Fin.castAdd u l))
          = Fin.castAdd u (Fin.natAdd (n + n) l) := Fin.ext rfl
      rw [e3, Fin.append_left, Fin.append_left]
      rfl
    · have e3 : Fin.cast (Nat.add_assoc (n + n) r u).symm (Fin.natAdd (n + n) (Fin.natAdd r l))
          = Fin.natAdd (n + n + r) l := Fin.ext (by simp; omega)
      rw [e3, Fin.append_right, Fin.append_right]

/-- The Choi state read through `σ`, at `(x, y, o, e)`, is the Kraus operator `K_{o,e}` at row `y`
and column `x`. -/
private theorem amp_choiRead_append {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (x y : Fin n → ZMod 2) (o : Fin r → ZMod 2) (e : Fin u → ZMod 2) :
    amp (choiRead p σ) (Fin.append (Fin.append (Fin.append x y) o) e) = krausOp p σ o e y x := by
  unfold choiRead
  rw [amp_reindexFreeBits]
  simp only [append_comp_readingEquiv, append_comp_castAdd, append_comp_natAdd]
  exact amp_choi p hm x _

/-- The read Choi state is a carrier state at the protocol's precision (`isCarrier_choi`, kept by
the reindexing). -/
private theorem isCarrier_choiRead {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) : IsCarrier (choiRead p σ) ∧ (choiRead p σ).m = m := by
  refine ⟨isCarrier_reindexFreeBits _ _ (isCarrier_choi p hm).1, ?_⟩
  have hcast : ∀ {N N' : ℕ} (h : N = N') (S : KernelSumState N), (castBits h S).m = S.m := by
    intro _ _ h S
    subst h
    rfl
  unfold choiRead reindexFreeBits
  rw [hcast]
  exact (isCarrier_choi p hm).2

/-- `(√2)^n · 2^{−n} = (1/√2)^n`. -/
private theorem sqrt_two_pow_mul_inv (n : ℕ) :
    (Real.sqrt 2 : ℂ) ^ n * ((2 : ℂ) ^ n)⁻¹ = (1 / (Real.sqrt 2 : ℂ)) ^ n := by
  have hs : (Real.sqrt 2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ ofReal_sqrt_two_ne_zero
  have h2 : (Real.sqrt 2 : ℂ) ^ n * (Real.sqrt 2 : ℂ) ^ n = 2 ^ n := by
    rw [← mul_pow, ← sq, sqrt_two_sq_complex]
  rw [← h2, one_div, inv_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- **The Bell-read amplitude**: at `(b, a, o, e)` it is `2^{n/2} c_{o,e}(X^a Z^b)`. -/
private theorem amp_bellRead {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (P : Pauli n) (o : Fin r → ZMod 2) (e : Fin u → ZMod 2) :
    amp (bellRead p σ) (Fin.append (Fin.append (symplecticBits P) o) e)
      = (Real.sqrt 2 : ℂ) ^ n * pauliCoeff (krausOp p σ o e) P := by
  have hC := isCarrier_choiRead p σ hm
  unfold bellRead
  rw [amp_run _ hC.1 hC.2, bellReadWord_eq, runAmp_castAddWord, runAmp_castAddWord, symplecticBits,
    runAmp_bellPairWord]
  simp only [amp_choiRead_append p σ hm]
  rw [pauliCoeff, trace_conjTranspose_pauliMatrix_mul, ← mul_assoc, sqrt_two_pow_mul_inv]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [add_comm P.X x]

-- source: papers/higher_order_fourier/
-- BuGuJaffe_2025_quantum_HOF_clifford_hierarchy_2508.15908 definition:hbcb8f6c85f63
/-- **The Choi amplitude read in the Bell basis is `2^{n/2}` times the Pauli coefficients.** For a
protocol at precision `m ≥ 1` read through `σ`, the Bell reading is a carrier state at precision `m`
(a T05 word on T49's carrier Choi state), and its amplitude at `(b, a, o, e)` (the Z bits `b`, the
X bits `a`, the read string `o`, the unread string `e`) is `2^{n/2} c_{o,e}(X^a Z^b)`, with
`c_{o,e}` the Pauli coefficients of the Kraus operator `K_{o,e}`. The source's Choi state is on the
normalised `∣Φ⟩ = 2^{−n/2} Σ_j ∣j⟩∣j⟩`, where the same reading gives `c_{o,e}` exactly; T49's floor
is `Σ_j ∣j⟩∣j⟩`, and that is the whole factor `2^{n/2}` (the identity channel at `n = 1` reads `√2`
at `I`, where `c(I) = 1`). Proved at T50.3.2. -/
theorem bellRead_choi_eq_pauliCoeff {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) :
    IsCarrier (bellRead p σ) ∧ (bellRead p σ).m = m ∧
      ∀ (P : Pauli n) (o : Fin r → ZMod 2) (e : Fin u → ZMod 2),
        amp (bellRead p σ) (Fin.append (Fin.append (symplecticBits P) o) e)
          = (Real.sqrt 2 : ℂ) ^ n * pauliCoeff (krausOp p σ o e) P := by
  have hC := isCarrier_choiRead p σ hm
  exact ⟨isCarrier_run _ hC.1 hC.2, (run_m _ _).trans hC.2, fun P o e => amp_bellRead p σ hm P o e⟩

/-! ## χ per read string, and the branch -/

/-- **The χ matrix of the branch at the read string `o`**: `2^{−n}` times the Gram data over the
unread bits (T27's `gram`) of the Bell-read Choi state, at the read words `(P, o)` and `(Q, o)`,
each Pauli at its exchanged bits `symplecticBits`. Defined on the frame's carrier state, not on
operators; it is `Σ_e c_{o,e}(P) conj(c_{o,e}(Q))` (`channel_eq_chi_sum`). Per read string: the
blocks of the Gram data at two different read strings are the coherent reading's cross terms, which
no `chi` records. -/
noncomputable def chi {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (o : Fin r → ZMod 2) : Matrix (Pauli n) (Pauli n) ℂ :=
  fun P Q => ((2 : ℂ) ^ n)⁻¹ *
    gram (amp (bellRead p σ)) (Fin.append (symplecticBits P) o) (Fin.append (symplecticBits Q) o)

/-- **The branch at the read string `o`** of a protocol's channel read through `σ`: the `(o, o)`
block of T49's `channel p σ ρ`, the unread outcome bits traced out, so
`ρ ↦ Σ_e K_{o,e} ρ K_{o,e}†`. With every outcome bit unread (`r = 0`) it is the whole channel. -/
noncomputable def channelBranch {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (o : Fin r → ZMod 2) (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  fun w w' => channel p σ ρ (w, o) (w', o)

/-! ### The proofs' lemmas: χ and the Kraus operators -/

/-- **χ from the Bell reading**: `2^{−n}` times the Gram data is `Σ_e c_e(P) conj(c_e(Q))`, the
factor `2^{n/2}` of each amplitude giving `2^n`. -/
private theorem chi_eq_sum_pauliCoeff {m k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (hm : 1 ≤ m) (o : Fin r → ZMod 2) (P Q : Pauli n) :
    chi p σ o P Q = ∑ e : Fin u → ZMod 2,
      pauliCoeff (krausOp p σ o e) P * starRingEnd ℂ (pauliCoeff (krausOp p σ o e) Q) := by
  unfold chi gram
  simp only [amp_bellRead p σ hm, map_mul, map_pow, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have h2 : (Real.sqrt 2 : ℂ) ^ n * (Real.sqrt 2 : ℂ) ^ n = 2 ^ n := by
    rw [← mul_pow, ← sq, sqrt_two_sq_complex]
  have hinv : ((2 : ℂ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  linear_combination (pauliCoeff (krausOp p σ o e) P
      * starRingEnd ℂ (pauliCoeff (krausOp p σ o e) Q) * ((2 : ℂ) ^ n)⁻¹) * h2
    + (pauliCoeff (krausOp p σ o e) P * starRingEnd ℂ (pauliCoeff (krausOp p σ o e) Q)) * hinv

/-- The entry of `A ρ B†` at `(a, b)` is `Σ_{x, x'} ρ(x, x') · A(a, x) · conj (B(b, x'))`. -/
private theorem mul_mul_conjTranspose_apply {α β : Type*} [Fintype α] (A B : Matrix β α ℂ)
    (ρ : Matrix α α ℂ) (a b : β) :
    (A * ρ * Bᴴ) a b = ∑ x, ∑ x', ρ x x' * (A a x * starRingEnd ℂ (B b x')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- The branch at `o` is `ρ ↦ Σ_e K_{o,e} ρ K_{o,e}†`. -/
private theorem channelBranch_eq_sum_krausOp {m k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (o : Fin r → ZMod 2)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    channelBranch p σ o ρ = ∑ e, krausOp p σ o e * ρ * (krausOp p σ o e)ᴴ := by
  ext w w'
  unfold channelBranch channel
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [mul_mul_conjTranspose_apply, mul_mul_conjTranspose_apply]
  rfl

/-- A sandwich of two combinations of Paulis is the double combination of the sandwiches. -/
private theorem sum_smul_mul_mul_conjTranspose (c : Pauli n → ℂ)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    (∑ P, c P • pauliMatrix P) * ρ * (∑ Q, c Q • pauliMatrix Q)ᴴ
      = ∑ P, ∑ Q, (c P * starRingEnd ℂ (c Q)) • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def]
  exact Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => by rw [mul_comm]))

/-- **χ is the Kraus coefficients' Gram data, and the branch is the χ sum.** For a protocol at
precision `m ≥ 1` read through `σ`, at every read string `o`: `χ_o(P, Q)`, defined as `2^{−n}` times
the Bell-read state's Gram data, is `Σ_e c_{o,e}(P) conj(c_{o,e}(Q))`, quadratic in the Kraus
operators; and the branch at `o` is `ρ ↦ Σ_{P,Q} χ_o(P, Q) P ρ Q†`, with `P = X^a Z^b` and the
dagger on the right (Chuang and Nielsen's equation (3.2), in the real convention; not in the
corpus). Proved at T50.3.2. -/
theorem channel_eq_chi_sum {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (o : Fin r → ZMod 2) :
    (∀ P Q : Pauli n, chi p σ o P Q = ∑ e : Fin u → ZMod 2,
        pauliCoeff (krausOp p σ o e) P * starRingEnd ℂ (pauliCoeff (krausOp p σ o e) Q)) ∧
      ∀ ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
        channelBranch p σ o ρ
          = ∑ P : Pauli n, ∑ Q : Pauli n,
              chi p σ o P Q • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ) := by
  refine ⟨chi_eq_sum_pauliCoeff p σ hm o, fun ρ => ?_⟩
  rw [channelBranch_eq_sum_krausOp]
  simp only [chi_eq_sum_pauliCoeff p σ hm o]
  calc ∑ e, krausOp p σ o e * ρ * (krausOp p σ o e)ᴴ
      = ∑ e : Fin u → ZMod 2, ∑ P : Pauli n, ∑ Q : Pauli n,
          (pauliCoeff (krausOp p σ o e) P * starRingEnd ℂ (pauliCoeff (krausOp p σ o e) Q))
            • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        have h := sum_smul_mul_mul_conjTranspose (fun P => pauliCoeff (krausOp p σ o e) P) ρ
        simp only [← pauli_expansion] at h
        exact h
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun P _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun Q _ => ?_)
        rw [Finset.sum_smul]

/-! ## The Pauli transfer matrix -/

-- source: papers/tensor_network_simulation/
-- Rudolph_2025_pauli_propagation_framework_2505.21606 paragraph:h1e5185612f8e
/-- **The Pauli transfer matrix** of a map `Λ` on matrices of the data words:
`R(P, Q) = 2^{−n} tr(P† Λ(Q))`, with `P = X^a Z^b` real. The source's `[E]_ij = Tr[P_i E(P_j)]` is
on the normalised Hermitian Pauli strings `2^{−n/2} P_i`, which is this with `2^{−n}` written out;
for real Paulis the dagger is needed, since `Q² = −I` when `a·b` is odd. A protocol's is
`ptm (channelBranch p σ o)`. -/
noncomputable def ptm
    (Λ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    Matrix (Pauli n) (Pauli n) ℂ :=
  fun P Q => ((2 : ℂ) ^ n)⁻¹ * trace ((pauliMatrix P)ᴴ * Λ (pauliMatrix Q))

/-- **χ in the transfer basis**: the transfer matrix of the map `ρ ↦ Σ_{P′,Q′} c(P′, Q′) P′ ρ Q′†`,
`R(P, Q) = 2^{−n} Σ_{P′,Q′} c(P′, Q′) tr(P† P′ Q Q′†)`. A fixed linear change of coordinates of
`Matrix (Pauli n) (Pauli n) ℂ`, from the basis `ρ ↦ P ρ Q†` of the maps on matrices to the basis
`ρ ↦ 2^{−n} tr(Q† ρ) P`; not a similarity of `4^n × 4^n` matrices. -/
noncomputable def transferOfChi (c : Matrix (Pauli n) (Pauli n) ℂ) : Matrix (Pauli n) (Pauli n) ℂ :=
  fun P Q => ((2 : ℂ) ^ n)⁻¹ * ∑ P' : Pauli n, ∑ Q' : Pauli n,
    c P' Q' * trace ((pauliMatrix P)ᴴ * (pauliMatrix P' * pauliMatrix Q * (pauliMatrix Q')ᴴ))

/-! ### The proofs' lemmas: the change of basis -/

/-- The map with coordinates `c` in the basis `ρ ↦ P ρ Q†`. -/
private noncomputable def chiMap (c : Matrix (Pauli n) (Pauli n) ℂ)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  ∑ P, ∑ Q, c P Q • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ)

/-- The transfer matrix of the map with coordinates `c` is `transferOfChi c`. -/
private theorem ptm_chiMap (c : Matrix (Pauli n) (Pauli n) ℂ) :
    ptm (chiMap c) = transferOfChi c := by
  ext P Q
  unfold ptm transferOfChi chiMap
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

/-- The map with coordinates `c` is linear in its argument. -/
private theorem chiMap_sum_smul (c : Matrix (Pauli n) (Pauli n) ℂ) (d : Pauli n → ℂ)
    (B : Pauli n → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    chiMap c (∑ R, d R • B R) = ∑ R, d R • chiMap c (B R) := by
  unfold chiMap
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
    smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun Q _ => Finset.sum_congr rfl (fun R _ => by rw [mul_comm]))

/-- The transfer matrix of `Λ` is zero only when `Λ` vanishes on the Paulis. -/
private theorem chiMap_pauliMatrix_eq_zero (c : Matrix (Pauli n) (Pauli n) ℂ)
    (h : transferOfChi c = 0) (Q : Pauli n) : chiMap c (pauliMatrix Q) = 0 := by
  have hcoeff : ∀ P, pauliCoeff (chiMap c (pauliMatrix Q)) P = 0 := fun P => by
    change ptm (chiMap c) P Q = 0
    rw [ptm_chiMap, h]
    rfl
  rw [pauli_expansion (chiMap c (pauliMatrix Q))]
  simp only [hcoeff, zero_smul, Finset.sum_const_zero]

/-- **The coordinates are faithful**: `transferOfChi c = 0` only at `c = 0`. The map vanishes on
the Paulis, so on every matrix (`pauli_expansion`), so on each matrix unit `∣x⟩⟨x'∣`, where its
entries are `Σ_{P,Q} c(P, Q) P(w, x) conj(Q(w', x'))`; the Paulis are independent twice. -/
private theorem eq_zero_of_transferOfChi_eq_zero (c : Matrix (Pauli n) (Pauli n) ℂ)
    (h : transferOfChi c = 0) : c = 0 := by
  have hall : ∀ ρ, chiMap c ρ = 0 := fun ρ => by
    rw [pauli_expansion ρ, chiMap_sum_smul]
    simp only [chiMap_pauliMatrix_eq_zero c h, smul_zero, Finset.sum_const_zero]
  have hunit : ∀ w x w' x' : Fin n → ZMod 2,
      ∑ P, (∑ Q, c P Q * starRingEnd ℂ (pauliMatrix Q w' x')) * pauliMatrix P w x = 0 := by
    intro w x w' x'
    have hE := congrFun (congrFun (hall (fun y y' => if y = x ∧ y' = x' then 1 else 0)) w) w'
    unfold chiMap at hE
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_mul_conjTranspose_apply,
      ite_mul, one_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Matrix.zero_apply] at hE
    rw [← hE]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun Q _ => by ring)
  ext P Q
  have hrow : ∀ w' x', ∑ R, c P R * starRingEnd ℂ (pauliMatrix R w' x') = 0 := fun w' x' =>
    eq_zero_of_sum_mul_pauliMatrix _ (fun w x => hunit w x w' x') P
  have hconj : starRingEnd ℂ (c P Q) = 0 := by
    refine eq_zero_of_sum_mul_pauliMatrix (fun R => starRingEnd ℂ (c P R))
      (fun w' x' => ?_) Q
    have h' := congrArg (starRingEnd ℂ) (hrow w' x')
    simpa only [map_sum, map_mul, Complex.conj_conj, map_zero] using h'
  rw [Matrix.zero_apply]
  exact (map_eq_zero (starRingEnd ℂ)).mp hconj

/-- `transferOfChi` as a linear map. -/
private noncomputable def transferLinear :
    Matrix (Pauli n) (Pauli n) ℂ →ₗ[ℂ] Matrix (Pauli n) (Pauli n) ℂ where
  toFun := transferOfChi
  map_add' c c' := by
    ext P Q
    simp only [transferOfChi, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a c := by
    ext P Q
    simp only [transferOfChi, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

/-- `transferOfChi` is a bijection: an injective linear endomorphism of a finite-dimensional
space. -/
private theorem transferOfChi_bijective : Function.Bijective (transferOfChi (n := n)) := by
  have hinj : Function.Injective (transferLinear (n := n)) :=
    (injective_iff_map_eq_zero transferLinear).mpr
      (fun c hc => eq_zero_of_transferOfChi_eq_zero c hc)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **The diagonal of `transferOfChi`**: `Σ_P c(P, P) (−1)^{ω(P, Q)}`, the off-diagonal
coordinates dropping out since `tr(Q† P Q Q′†) = (−1)^{ω(P, Q)} tr(P Q′†)`. -/
private theorem transferOfChi_diag (c : Matrix (Pauli n) (Pauli n) ℂ) (Q : Pauli n) :
    transferOfChi c Q Q = ∑ P, c P P * signOf (omega P Q) := by
  unfold transferOfChi
  have hterm : ∀ P' Q' : Pauli n,
      trace ((pauliMatrix Q)ᴴ * (pauliMatrix P' * pauliMatrix Q * (pauliMatrix Q')ᴴ))
        = if Q' = P' then signOf (omega P' Q) * 2 ^ n else 0 := fun P' Q' => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, conjTranspose_mul_mul_pauliMatrix,
      Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm, trace_pauliMatrix_orth,
      smul_eq_mul, mul_ite, mul_zero]
  simp only [hterm, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.mul_sum]
  have hinv : ((2 : ℂ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  exact Finset.sum_congr rfl (fun P _ => by
    linear_combination (c P P * signOf (omega P Q)) * hinv)

/-- **The transfer matrix is χ in another basis.** For a protocol at precision `m ≥ 1` read through
`σ`, at every read string `o`, the branch's transfer matrix is `transferOfChi` of its χ, and
`transferOfChi` is a bijection: the two are coordinates of one map in two bases of the maps on
matrices, both quadratic in the Kraus operators. Neither is a transform of the Choi amplitude, which
is linear in them (`16^n` entries of `R` against `4^n` of the amplitude at each `(o, e)`). Proved at
T50.3.2. -/
theorem ptm_eq_chi_basis {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (o : Fin r → ZMod 2) :
    ptm (channelBranch p σ o) = transferOfChi (chi p σ o) ∧
      Function.Bijective (transferOfChi (n := n)) := by
  have hbr : channelBranch p σ o = chiMap (chi p σ o) :=
    funext fun ρ => (channel_eq_chi_sum p σ hm o).2 ρ
  rw [hbr, ptm_chiMap]
  exact ⟨rfl, transferOfChi_bijective⟩

/-- **The diagonal duality**, for every channel: for a protocol at precision `m ≥ 1` read through
`σ`, at every read string `o` and every `Q`, the branch's transfer-matrix diagonal is `2^n Ŵ` of χ's
diagonal, `R(Q, Q) = Σ_P χ(P, P)(−1)^{ω(P, Q)}`: both forms are stated, so that the factor `2^n`
between the H-word's normalisation and the unnormalised sum is explicit. No Pauli-channel
hypothesis: a single branch, which need not preserve trace, is included. It holds because
`Q† P Q = (−1)^{ω(P, Q)} P` and `tr(P P′†) = 2^n δ_{P, P′}`, which needs the dagger in `R` (Zhang,
Yu, Zeng, Liu and Ma, equation (A23), for Hermitian Paulis; not in the corpus). Proved at
T50.3.2. -/
theorem ptm_diag_eq_walsh_chi_diag {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u))
    (hm : 1 ≤ m) (o : Fin r → ZMod 2) (Q : Pauli n) :
    ptm (channelBranch p σ o) Q Q = (2 : ℂ) ^ n * walsh2n (fun P => chi p σ o P P) Q ∧
      ptm (channelBranch p σ o) Q Q = ∑ P : Pauli n, chi p σ o P P * signOf (omega P Q) := by
  have hbr : channelBranch p σ o = chiMap (chi p σ o) :=
    funext fun ρ => (channel_eq_chi_sum p σ hm o).2 ρ
  have hT : ptm (channelBranch p σ o) Q Q = ∑ P : Pauli n, chi p σ o P P * signOf (omega P Q) := by
    rw [hbr, ptm_chiMap, transferOfChi_diag]
  refine ⟨?_, hT⟩
  rw [hT, walsh2n, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]
  exact Finset.sum_congr rfl (fun P _ => mul_comm _ _)

/-! ## Pauli channels -/

/-- **A Pauli channel**: a map on matrices of the data words of the form
`ρ ↦ Σ_P d(P) P ρ P†` for some `d : Pauli n → ℂ`, with `P = X^a Z^b`. The real and the Hermitian
conventions give the same maps, since `P ρ P†` does not see a unit phase. -/
def IsPauliChannel
    (Λ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    Prop :=
  ∃ d : Pauli n → ℂ, ∀ ρ, Λ ρ = ∑ P : Pauli n, d P • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ)

/-- **A probability distribution on `Pauli n`**: nonnegative values summing to `1`. -/
def IsPauliDistribution (d : Pauli n → ℝ) : Prop :=
  (∀ P, 0 ≤ d P) ∧ ∑ P : Pauli n, d P = 1

/-! ### The proofs' lemmas: the distribution -/

/-- **Parseval**: `Σ_P |c(P)|² = 2^{−n} Σ_{w,x} |K(w, x)|²`, from the expansion and orthogonality,
`tr(K† K) = 2^n Σ_P |c(P)|²`. -/
private theorem sum_pauliCoeff_mul_conj (K : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    ∑ P, pauliCoeff K P * starRingEnd ℂ (pauliCoeff K P)
      = ((2 : ℂ) ^ n)⁻¹ * ∑ x, ∑ w, starRingEnd ℂ (K w x) * K w x := by
  have htr : trace (Kᴴ * K)
      = (2 : ℂ) ^ n * ∑ P, pauliCoeff K P * starRingEnd ℂ (pauliCoeff K P) := by
    conv_lhs => rw [pauli_expansion K]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.sum_mul,
      Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      trace_pauliMatrix_orth, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Complex.star_def]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P _ => by ring)
  have htr' : trace (Kᴴ * K) = ∑ x, ∑ w, starRingEnd ℂ (K w x) * K w x := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def]
  rw [← htr', htr, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]

/-- With no read outcome bits, the data bits and the unread bits together run over the protocol's
whole register, once each. -/
private theorem sum_append_reading {k u : ℕ} (σ : Fin k ≃ Fin (0 + u))
    (f : (Fin (n + k) → ZMod 2) → ℂ) :
    ∑ e : Fin u → ZMod 2, ∑ w : Fin n → ZMod 2,
        f (Fin.append w (Fin.append (0 : Fin 0 → ZMod 2) e ∘ σ)) = ∑ v, f v := by
  have hfill : ∀ (h : Fin (0 + u) → ZMod 2) (i : Fin (0 + u)),
      Fin.append (0 : Fin 0 → ZMod 2) (h ∘ Fin.natAdd 0) i = h i := by
    intro h i
    refine Fin.addCases (fun l => l.elim0) (fun l => ?_) i
    rw [Fin.append_right]
    rfl
  let E : (Fin u → ZMod 2) ≃ (Fin k → ZMod 2) :=
    { toFun := fun e => Fin.append (0 : Fin 0 → ZMod 2) e ∘ σ
      invFun := fun g => (g ∘ σ.symm) ∘ Fin.natAdd 0
      left_inv := fun e => by
        funext j
        simp only [Function.comp_apply, Equiv.apply_symm_apply, Fin.append_right]
      right_inv := fun g => by
        funext j
        change Fin.append (0 : Fin 0 → ZMod 2) ((g ∘ σ.symm) ∘ Fin.natAdd 0) (σ j) = g j
        rw [hfill]
        simp only [Function.comp_apply, Equiv.symm_apply_apply] }
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.prodCongr (Equiv.refl _) E).trans (Fin.appendEquiv n k)) _ _
    (fun _ => rfl)

/-- A point mass has inner sum `1` with itself. -/
private theorem innerSum_delta_self {N : ℕ} (x : Fin N → ZMod 2) :
    innerSum (delta x) (delta x) = 1 := by
  unfold innerSum delta
  rw [Finset.sum_eq_single x (fun v _ hv => by rw [if_neg hv, zero_mul])
    (fun h => absurd (Finset.mem_univ x) h)]
  simp

/-- **χ's diagonal sums to `1`** with every outcome bit unread: Parseval, then the isometry of the
referee on each point mass (`innerSum_interpretAmp`). -/
private theorem sum_chi_diag {m k u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (0 + u))
    (hm : 1 ≤ m) : ∑ P, chi p σ 0 P P = 1 := by
  simp only [chi_eq_sum_pauliCoeff p σ hm]
  rw [Finset.sum_comm]
  simp only [sum_pauliCoeff_mul_conj]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hx : ∀ x : Fin n → ZMod 2, ∑ e : Fin u → ZMod 2, ∑ w : Fin n → ZMod 2,
      starRingEnd ℂ (krausOp p σ 0 e w x) * krausOp p σ 0 e w x = 1 := fun x => by
    have h := sum_append_reading σ
      (fun v => starRingEnd ℂ (p.interpretAmp (delta x) v) * p.interpretAmp (delta x) v)
    change ∑ e : Fin u → ZMod 2, ∑ w : Fin n → ZMod 2,
        starRingEnd ℂ (p.interpretAmp (delta x) (Fin.append w (Fin.append 0 e ∘ σ)))
          * p.interpretAmp (delta x) (Fin.append w (Fin.append 0 e ∘ σ)) = 1
    rw [h, ← innerSum_delta_self x, ← innerSum_interpretAmp p]
    unfold innerSum
    exact Finset.sum_congr rfl (fun v _ => mul_comm _ _)
  simp only [hx, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  exact inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)

/-- **A Pauli channel is one whose χ is diagonal**, and its transfer matrix is then diagonal. For a
protocol at precision `m ≥ 1` read through `σ`, the branch at the read string `o` is a Pauli channel
exactly when `χ_o(P, Q) = 0` for `P ≠ Q`; and then `R(P, Q) = 0` for `P ≠ Q`, its diagonal being
the eigenvalues `λ = 2^n Ŵp` of `ptm_diag_eq_walsh_chi_diag`, `p` χ's diagonal (Flammia and
Wallman, equations (11) and (16) to (20); not in the corpus). Proved at T50.3.2. -/
theorem pauliChannel_iff_chi_diagonal {m k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (hm : 1 ≤ m) (o : Fin r → ZMod 2) :
    (IsPauliChannel (channelBranch p σ o) ↔ ∀ P Q : Pauli n, P ≠ Q → chi p σ o P Q = 0) ∧
      (IsPauliChannel (channelBranch p σ o) →
        ∀ P Q : Pauli n, P ≠ Q → ptm (channelBranch p σ o) P Q = 0) := by
  have hbr : channelBranch p σ o = chiMap (chi p σ o) :=
    funext fun ρ => (channel_eq_chi_sum p σ hm o).2 ρ
  have hdiag : IsPauliChannel (channelBranch p σ o) → ∀ P Q : Pauli n, P ≠ Q →
      chi p σ o P Q = 0 := by
    rintro ⟨d, hd⟩ P Q hPQ
    have hmap : channelBranch p σ o = chiMap (fun P Q => if P = Q then d P else 0) := by
      funext ρ
      rw [hd ρ]
      unfold chiMap
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.sum_eq_single P (fun Q _ hQ => by beta_reduce; rw [if_neg (Ne.symm hQ), zero_smul])
        (fun h => absurd (Finset.mem_univ P) h)]
      beta_reduce
      rw [if_pos rfl]
    have hT : transferOfChi (chi p σ o) = transferOfChi (fun P Q => if P = Q then d P else 0) := by
      rw [← ptm_chiMap, ← ptm_chiMap, ← hbr, hmap]
    rw [transferOfChi_bijective.1 hT]
    exact if_neg hPQ
  refine ⟨⟨hdiag, fun h => ⟨fun P => chi p σ o P P, fun ρ => ?_⟩⟩, fun hP P Q hPQ => ?_⟩
  · rw [(channel_eq_chi_sum p σ hm o).2 ρ]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    exact Finset.sum_eq_single P (fun Q _ hQ => by rw [h P Q (Ne.symm hQ), zero_smul])
      (fun h' => absurd (Finset.mem_univ P) h')
  · rw [hbr, ptm_chiMap]
    unfold transferOfChi
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun P' _ => ?_))
    rw [Finset.sum_eq_single P' (fun Q' _ hQ' => by rw [hdiag hP P' Q' (Ne.symm hQ'), zero_mul])
      (fun h' => absurd (Finset.mem_univ P') h'), pauliMatrix_mul_mul_conjTranspose,
      Matrix.mul_smul, Matrix.trace_smul, trace_pauliMatrix_orth, if_neg hPQ, smul_zero,
      mul_zero]

/-- **With every outcome bit unread, χ's diagonal is a distribution on `Pauli n`**, with values in
`ℤ[ζ_{2^∞}, ½]`. For a protocol at precision `m ≥ 1` read with no read outcome bits, so that the
one branch is the whole channel and preserves trace (T49's isometry, `innerSum_interpretAmp`),
`P ↦ χ(P, P)` is real, nonnegative and sums to `1`, and each value lies in `dyadicCyclotomicRing`.
No Pauli-channel hypothesis: for a Pauli channel this is its distribution, which T52 takes. With
outcome bits read a single branch's diagonal sums to the branch's weight, so the statement is made
only here; summing the branches is the other trace-preserving case, not stated. The ring condition
makes the bridge to T52 one way: a distribution with a value outside the ring, such as `1/3`, is no
protocol's. Proved at T50.3.2. -/
theorem chi_diag_isDistribution {m k u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (0 + u))
    (hm : 1 ≤ m) :
    ∃ d : Pauli n → ℝ, IsPauliDistribution d ∧
      ∀ P : Pauli n, chi p σ 0 P P = d P ∧ (d P : ℂ) ∈ dyadicCyclotomicRing := by
  have hchi : ∀ P : Pauli n, chi p σ 0 P P
      = ((∑ e : Fin u → ZMod 2, Complex.normSq (pauliCoeff (krausOp p σ 0 e) P) : ℝ) : ℂ) :=
    fun P => by
      rw [chi_eq_sum_pauliCoeff p σ hm, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun e _ => Complex.mul_conj _)
  refine ⟨fun P => ∑ e : Fin u → ZMod 2, Complex.normSq (pauliCoeff (krausOp p σ 0 e) P),
    ⟨fun P => Finset.sum_nonneg (fun e _ => Complex.normSq_nonneg _), ?_⟩,
    fun P => ⟨hchi P, ?_⟩⟩
  · have h := sum_chi_diag p σ hm
    simp only [hchi] at h
    exact_mod_cast h
  · rw [← hchi P, chi_eq_sum_pauliCoeff p σ hm]
    exact Subring.sum_mem _ (fun e _ => Subring.mul_mem _
      (pauliCoeff_mem_dyadicCyclotomicRing _ (krausOp_mem_dyadicCyclotomicRing p σ hm 0 e) P)
      (starRingEnd_mem_dyadicCyclotomicRing
        (pauliCoeff_mem_dyadicCyclotomicRing _ (krausOp_mem_dyadicCyclotomicRing p σ hm 0 e) P)))

end FTQCLib.Frame.Walkthrough

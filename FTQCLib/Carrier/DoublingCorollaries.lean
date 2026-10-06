/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.PauliTransfer
import FTQCLib.Stabilizer.Error
import ECCLib.Delsarte.LP
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Corollaries of the doubling: weight enumerators, Knill–Laflamme, the Pauli twirl

The statement of T51 (`docs/TARGETS.md`; `docs/fidelity/T51.md`). Three classical results of
quantum coding are stated as corollaries of T50's Pauli reading of a protocol's channel and of
T27's Gram data. Everything is frame-pure (D5): operators are matrices on the data words
`Fin n → ZMod 2`, Paulis are T50's real `X^a Z^b` (`pauliMatrix`), and nothing from
`FTQCLib.Hilbert` is imported.

**Stabilizer codes** (`IsStabilizerEncoder`). A stabilizer code is given by its phase-free
stabilizer subspace `S : Submodule (ZMod 2) (Pauli n)`, isotropic (`IsStabilizer`), and an encoder
`V`, a `2^n × 2^ℓ` matrix with orthonormal columns (`Vᴴ V = 1`) on which every `s ∈ S` acts as a
scalar, with `ℓ + dim S = n`. The scalar is the code's sign at `s`: the phase-free `S` does not fix
the signs, and the encoder does. The columns then span the whole joint eigenspace, and
`codeProjector V = V Vᴴ` is the code's projector `Π`, of trace `K = 2^ℓ`. `N(S)` is
`normalizer S`, the `ω`-orthogonal of `S`, and the distance is `distance S`
(`FTQCLib/Stabilizer/Error.lean`).

**The weight enumerators** (`weightEnumeratorA`, `weightEnumeratorB`). For a matrix `M` and a
weight `d`, `A_d(M) = Σ_{wt P = d} |tr(P M)|²` and `B_d(M) = Σ_{wt P = d} tr(P M P† M†)`, Rains's
unnormalised `A_d(M, M†)` and `B_d(M, M†)`. At `M = Π` the summands are Shor and Laflamme's
`A(E) = |tr(E Π)|²` and `B(E) = tr(E Π E† Π)`, and their `A_d`, `B_d` are these divided by `K²` and
`K`. The real Paulis change nothing: `P† = ±P`, and both summands are blind to the sign.

**The enumerators are T50's two diagonals of `ρ ↦ Π ρ Π`** (`quantum_macwilliams`). The map is the
branch, at the code's syndrome, of the protocol that conditions on a basis of `S` with every outcome
bit read; its Choi state is `Π`'s doubled state (T49), and T50 reads it: `χ(P, P) = 4^{−n} A(P)`
and `R(P, P) = 2^{−n} B(P)`. So T50's diagonal duality `R(Q, Q) = Σ_P χ(P, P)(−1)^{ω(P, Q)}` is
`B(Q) = 2^{−n} Σ_P A(P)(−1)^{ω(P, Q)}`, and summed over the `Q` of weight `d` it is the quantum
MacWilliams identity `B_d = 2^{−n} Σ_j K_d(j) A_j`, with ECCLib's quaternary Krawtchouk numbers
`kraw 4 n d j`. ECCLib's classical identity (`ECCLib/MacWilliams.lean`) is stated for linear codes
over a field with the dot product; a stabilizer group is an additive code with `ω`, so it is not
applied as stated: the weight classes are counted by ECCLib's `kraw`, and its character sum
`sum_char_over_subgroup` is the transport (fidelity note, Claim 6).

**The bounds, transported.** For a stabilizer code `A_j` and `B_j` are `4^ℓ` and `2^ℓ` times the
numbers of elements of weight `j` of `S` and of `N(S)` (Gottesman's counts), which gives the
linear programme's constraints `K B_j ≥ A_j ≥ 0`, with equality below the distance (Rains). From
them: the quantum Singleton bound `2(d − 1) + ℓ ≤ n` for every code, degenerate included; ECCLib's
LP certificates (`LPCert`) applied to `N(S)` for nondegenerate codes; and the quantum Hamming bound
for nondegenerate codes only, the one case in which it is proved.

**Knill–Laflamme as T27's Gram condition** (`knillLaflamme_iff`). Lay the error images out as one
amplitude function (`errorImages`): read bits the codeword index `i` and the error label `a`, unread
bits the `n` physical qubits, `(i, a, u) ↦ (A_a V)(u, i)`. T27's `gram` of it at `(i, a)` and
`(j, b)` is `⟨j| Vᴴ A_b† A_a V |i⟩`, and the code corrects the errors (`CorrectsErrors`: a
trace-preserving recovery `R` with every `R_r A_a` a scalar on the code) exactly when this Gram data
is `δ_{ij} C_{ba}` for one matrix `C`: the Gram data of the code's identity beside an environment
vector per error. For Pauli errors on a stabilizer code it evaluates to `E_a + E_b ∈ S` or
`E_a + E_b ∉ N(S)`, phase-free, degeneracy included (`knillLaflamme_stabilizer_iff`).

**The Pauli twirl** (`pauliTwirl`, `pauli_twirl`). The average of `ρ ↦ T† Λ(T ρ T†) T` over the
`4^n` Paulis `T`. Character orthogonality on `Pauli n`, `Σ_T (−1)^{ω(T, c)} = 4^n δ_{c, 0}`,
multiplies χ entrywise by `δ_{P, Q}`: the twirl keeps χ's diagonal and removes the rest. That is all
that is stated of it: a Pauli channel with the same diagonal and the same transfer-matrix diagonal,
nothing about how far the original channel is from it.

## Main definitions

* `codeProjector`, `IsStabilizerEncoder` — the projector `V Vᴴ`, and an encoder of a stabilizer
  code.
* `enumeratorTermA`, `enumeratorTermB` — the summands `|tr(P M)|²` and `tr(P M P† M†)`.
* `weightEnumeratorA`, `weightEnumeratorB` — their sums over the Paulis of weight `d`.
* `errorImages`, `CorrectsErrors` — the error images as one amplitude function, and correction by
  a trace-preserving recovery.
* `pauliTwirl` — the Pauli twirl of a map on matrices.

## Main results

* `quantum_macwilliams` — the enumerators as T50's χ and transfer-matrix diagonals of
  `ρ ↦ Π ρ Π`, the identity per Pauli, per weight class and as generating functions, the counts
  and the LP's constraints, and the Singleton, LP and (nondegenerate) Hamming bounds (T51.3.1).
* `knillLaflamme_iff` — correction exactly when the error images' Gram data is `δ_{ij} C_{ba}`
  (T51.3.2).
* `knillLaflamme_stabilizer_iff` — its evaluation on Pauli errors and stabilizer codes (T51.3.2).
* `pauli_twirl` — character orthogonality, and the twirl keeps χ's diagonal (T51.3.3).

## Implementation notes

* **Indices.** Errors and recovery operators are families indexed by bit strings
  (`Fin e → ZMod 2`), as every finite family is after padding with repeats or zeros. The codeword
  index is `Fin ℓ → ZMod 2`.
* **Normalisation.** The enumerators are unnormalised (Rains's); Shor and Laflamme's are these
  divided by `K²` and `K`, `K = 2^ℓ`. Every factor is stated where it appears.
* **Precision.** The protocol of `quantum_macwilliams` is at precision `2`, which every Pauli
  conditioning letter admits; T50's theorems need `1 ≤ m`.
* **Knill–Laflamme's recovery.** Where Knill and Laflamme run Gram–Schmidt on the images
  `A_a |0_L⟩`, the proof of `knillLaflamme_iff` diagonalises the Hermitian matrix `C` with
  Mathlib's spectral theorem; `Mathlib.Analysis.Matrix.Spectrum` is imported for that alone.

## References

* D. Gottesman, *Stabilizer codes and quantum error correction*, arXiv:quant-ph/9705052: the
  stabilizer criterion, the counts and the nondegenerate Hamming bound. In the pinned corpus, not on
  T51's Corpus line; the fidelity note's Claims 2, 7 and 10.
* A. R. Calderbank, E. M. Rains, P. W. Shor and N. J. A. Sloane, *Quantum error correction via
  codes over GF(4)*: Lemma 1 (the phase-free criterion), Theorem 5 (MacWilliams for additive
  codes). In the pinned corpus, not on T51's Corpus line; Claims 6 and 10.
* E. Kowalski, Proposition 1.10: character orthogonality. Not on T51's Corpus line; Claim 12.
* The units of T51's Corpus line are cited above the declarations that restate them.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Matrix

variable {n : ℕ}

/-! ## Stabilizer codes -/

/-- **The projector of a code** with encoder `V`: `Π = V Vᴴ`, the orthogonal projector onto the
span of `V`'s columns when `Vᴴ V = 1`. -/
noncomputable def codeProjector {ℓ : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  V * Vᴴ

/-- **An encoder of the stabilizer code of `S`**: `S` is isotropic, `ℓ + dim S = n`, `V` has
orthonormal columns, and every `s ∈ S` acts on `V` as a scalar, the code's sign at `s` (the real
`X^a Z^b` has eigenvalues `±1` or `±i`). The columns then span the whole joint eigenspace of
dimension `2^ℓ`, and `codeProjector V` is the code's projector. The phase-free `S` does not choose
the signs; the encoder does. Isotropy follows from the scalar action on `V ≠ 0` (two Paulis acting
as scalars commute there); it is kept as a field so that the definition reads as the source's
stabilizer code, and costs a witness nothing. -/
def IsStabilizerEncoder {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) : Prop :=
  IsStabilizer S ∧ ℓ + Module.finrank (ZMod 2) S = n ∧ Vᴴ * V = 1 ∧
    ∀ s ∈ S, ∃ c : ℂ, pauliMatrix s * V = c • V

/-! ## The weight enumerators -/

-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 paragraph:hf92cc7bfdf3f
-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 equation:h42d9173de6e1
/-- **The `A` summand** at the Pauli `P`: `|tr(P M)|²`, as `tr(P M) · conj(tr(P M))`. Shor and
Laflamme's `tr(E O₁) tr(E† O₂)` at `O₁ = O₂ = Π` Hermitian, and Rains's `|Tr(E M)|²`; the real
`P = X^a Z^b` is the Hermitian Pauli times a unit, which the modulus does not see. -/
noncomputable def enumeratorTermA (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (P : Pauli n) :
    ℂ :=
  trace (pauliMatrix P * M) * starRingEnd ℂ (trace (pauliMatrix P * M))

-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 paragraph:hf92cc7bfdf3f
-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 equation:hda1c25245f9d
/-- **The `B` summand** at the Pauli `P`: `tr(P M P† M†)`. Shor and Laflamme's `tr(E O₁ E† O₂)` at
`O₁ = O₂ = Π`, and Rains's `Tr(E M₁ E M₂)` at `M₁ = M`, `M₂ = M†` with Hermitian `E`; the real
`P` and its dagger give the same value, the two unit phases cancelling. -/
noncomputable def enumeratorTermB (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (P : Pauli n) :
    ℂ :=
  trace (pauliMatrix P * M * (pauliMatrix P)ᴴ * Mᴴ)

-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 equation:hda1c25245f9d
/-- **The weight enumerator `A`** of `M` at the weight `d`: `A_d = Σ_{wt P = d} |tr(P M)|²`,
Rains's unnormalised `A_d(M, M†)`. A stabilizer code's is at `M = codeProjector V`; Shor and
Laflamme's `A_d` is this divided by `(tr Π)² = 4^ℓ`. -/
noncomputable def weightEnumeratorA (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (d : ℕ) : ℂ :=
  ∑ P ∈ Finset.univ.filter (fun P : Pauli n => weight P = d), enumeratorTermA M P

-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 equation:hda1c25245f9d
/-- **The weight enumerator `B`** of `M` at the weight `d`: `B_d = Σ_{wt P = d} tr(P M P† M†)`,
Rains's unnormalised `B_d(M, M†)`. A stabilizer code's is at `M = codeProjector V`; Shor and
Laflamme's `B_d` is this divided by `tr(Π Π) = 2^ℓ`. -/
noncomputable def weightEnumeratorB (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (d : ℕ) : ℂ :=
  ∑ P ∈ Finset.univ.filter (fun P : Pauli n => weight P = d), enumeratorTermB M P

/-! ### The proofs' lemmas: signs and the dot product

Restated from `FTQCLib/Carrier/PauliTransfer.lean`, where they are private. -/

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
private theorem signOf_sum {α : Type*} (s : Finset α) (g : α → ZMod 2) :
    signOf (∑ i ∈ s, g i) = ∏ i ∈ s, signOf (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, signOf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, signOf_add, ih]

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

/-- The dot product with the zero word on the left is zero. -/
private theorem bitDot_zero_left (x : Fin n → ZMod 2) : bitDot 0 x = 0 := by
  unfold bitDot
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]

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

/-- `p + p = 0` in `Pauli n`. -/
private theorem pauli_add_self (p : Pauli n) : p + p = 0 := by
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  ext i
  · exact h (p.X i)
  · exact h (p.Z i)

/-! ### The proofs' lemmas: products, daggers and traces of Paulis

The first three restated from `FTQCLib/Carrier/PauliTransfer.lean`, where they are private. -/

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

/-- `P M` at `(w, x)` is `(−1)^{b·(w + a)} M(w + a, x)`. -/
private theorem pauliMatrix_mul_apply (P : Pauli n)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (w x : Fin n → ZMod 2) :
    (pauliMatrix P * M) w x = signOf (bitDot P.Z (w + P.X)) * M (w + P.X) x := by
  rw [Matrix.mul_apply]
  simp only [pauliMatrix_apply', ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `P f` at `w` is `(−1)^{b·(w + a)} f(w + a)`. -/
private theorem pauliMatrix_mulVec (P : Pauli n) (f : (Fin n → ZMod 2) → ℂ)
    (w : Fin n → ZMod 2) :
    (pauliMatrix P *ᵥ f) w = signOf (bitDot P.Z (w + P.X)) * f (w + P.X) := by
  simp only [Matrix.mulVec, dotProduct, pauliMatrix_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The Pauli with no bits is the identity. -/
private theorem pauliMatrix_zero : pauliMatrix (0 : Pauli n) = 1 := by
  ext w x
  rw [pauliMatrix_apply, Matrix.one_apply, X_zero, Z_zero, add_zero, bitDot_zero_left,
    signOf_zero]

/-- **The product of two Paulis**: `P_p P_q = (−1)^{p.Z·q.X} P_{p+q}`. -/
private theorem pauliMatrix_mul (p q : Pauli n) :
    pauliMatrix p * pauliMatrix q = signOf (bitDot p.Z q.X) • pauliMatrix (p + q) := by
  have key : ∀ a b c d : ZMod 2, (a + b = c + d) ↔ (a = c + (b + d)) := by decide
  ext w x
  rw [pauliMatrix_mul_apply, Matrix.smul_apply, smul_eq_mul, pauliMatrix_apply,
    pauliMatrix_apply, X_add, Z_add]
  have hiff : (w + p.X = x + q.X) ↔ (w = x + (p.X + q.X)) :=
    ⟨fun h => funext fun i => (key (w i) (p.X i) (x i) (q.X i)).mp (congrFun h i),
      fun h => funext fun i => (key (w i) (p.X i) (x i) (q.X i)).mpr (congrFun h i)⟩
  by_cases h : w + p.X = x + q.X
  · rw [if_pos h, if_pos (hiff.mp h), h, bitDot_add_right, bitDot_add_left, signOf_add,
      signOf_add]
    ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h')), mul_zero, mul_zero]

/-- A Pauli squares to its sign: `P_q P_q = (−1)^{q.Z·q.X}`. -/
private theorem pauliMatrix_mul_self (q : Pauli n) :
    pauliMatrix q * pauliMatrix q = signOf (bitDot q.Z q.X) • (1 : Matrix _ _ ℂ) := by
  rw [pauliMatrix_mul, pauli_add_self, pauliMatrix_zero]

/-- **The dagger of a Pauli**: `P_q† = (−1)^{q.Z·q.X} P_q`. -/
private theorem conjTranspose_pauliMatrix (q : Pauli n) :
    (pauliMatrix q)ᴴ = signOf (bitDot q.Z q.X) • pauliMatrix q := by
  ext w x
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, pauliMatrix_apply,
    pauliMatrix_apply]
  by_cases h : w = x + q.X
  · rw [if_pos ((eq_add_iff_eq_add w x q.X).mp h), if_pos h, Complex.star_def, conj_signOf, h,
      bitDot_add_right, signOf_add]
    ring
  · rw [if_neg (fun h' => h ((eq_add_iff_eq_add w x q.X).mpr h')), if_neg h, star_zero,
      mul_zero]

/-- **The trace of a Pauli**: `tr P_q = 2^n δ_{q, 0}`. -/
private theorem trace_pauliMatrix (q : Pauli n) :
    trace (pauliMatrix q) = if q = 0 then (2 : ℂ) ^ n else 0 := by
  simp only [Matrix.trace, Matrix.diag, pauliMatrix_apply]
  by_cases hX : q.X = 0
  · have hw : ∀ w : Fin n → ZMod 2, w = w + q.X := fun w => by rw [hX, add_zero]
    simp only [← hw, if_true]
    rw [sum_signOf_bitDot]
    have hiff : q.Z = 0 ↔ q = 0 :=
      ⟨fun h => Pauli.ext hX h, fun h => by rw [h, Z_zero]⟩
    by_cases hq : q = 0
    · rw [if_pos (hiff.mpr hq), if_pos hq]
    · rw [if_neg (fun h => hq (hiff.mp h)), if_neg hq]
  · have hw : ∀ w : Fin n → ZMod 2, ¬ (w = w + q.X) := fun w h =>
      hX (by simpa using h.symm)
    simp only [hw, if_false, Finset.sum_const_zero]
    rw [if_neg (fun h => hX (by rw [h, X_zero]))]

/-! ### The proofs' lemmas: the code's projector as a product of conditionings

Conditioning on a basis `g_0, …, g_{r−1}` of `S`, each with the sign of the code at it and the
outcome `0` read, has the Kraus operator `∏_j ½(1 + (−1)^{s_j} G_j)`, `G_j` the Hermitian Pauli of
`g_j`. That product is a Hermitian idempotent fixing the encoder's columns, its Pauli coefficients
vanish off the span of the `g_j` and its trace is `2^{n−r}`; so it is the code's projector. -/

/-- The Hermitian Pauli `q` with the sign `s`, as a matrix: `(−1)^s i^{yWeight q} X^a Z^b`, the
matrix of `SignedPauli.act` (`pauliAct` is `i^{yWeight}` times the real `X^a Z^b`). -/
private noncomputable def hermMatrix (q : Pauli n) (s : ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  ((-1 : ℂ) ^ s.val * Complex.I ^ yWeight q) • pauliMatrix q

/-- The spectral projection `½(1 + (−1)^s G_q)` of conditioning on `q` with the sign `s`, at the
outcome `0`. -/
private noncomputable def projMatrix (q : Pauli n) (s : ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  (1 / 2 : ℂ) • (1 + hermMatrix q s)

/-- `i^y i^y = (−1)^{q.Z·q.X}`, with `y = yWeight q`. -/
private theorem I_pow_yWeight_mul_self (q : Pauli n) :
    Complex.I ^ yWeight q * Complex.I ^ yWeight q = signOf (bitDot q.Z q.X) := by
  rw [← pow_add, ← two_mul, pow_mul, Complex.I_sq, ← neg_one_pow_zDot]
  rfl

/-- The Hermitian Pauli squares to the identity. -/
private theorem hermMatrix_mul_self (q : Pauli n) (s : ZMod 2) :
    hermMatrix q s * hermMatrix q s = 1 := by
  unfold hermMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauliMatrix_mul_self, smul_smul]
  have h : (-1 : ℂ) ^ s.val * Complex.I ^ yWeight q * ((-1 : ℂ) ^ s.val * Complex.I ^ yWeight q)
      * signOf (bitDot q.Z q.X) = 1 := by
    calc _ = ((-1 : ℂ) ^ s.val * (-1 : ℂ) ^ s.val)
          * (Complex.I ^ yWeight q * Complex.I ^ yWeight q) * signOf (bitDot q.Z q.X) := by ring
      _ = 1 := by
          rw [neg_one_pow_val, signOf_mul_self, I_pow_yWeight_mul_self, one_mul, signOf_mul_self]
  rw [h, one_smul]

/-- The Hermitian Pauli is Hermitian. -/
private theorem conjTranspose_hermMatrix (q : Pauli n) (s : ZMod 2) :
    (hermMatrix q s)ᴴ = hermMatrix q s := by
  unfold hermMatrix
  rw [Matrix.conjTranspose_smul, conjTranspose_pauliMatrix, smul_smul, ← I_pow_yWeight_mul_self]
  congr 1
  have h1 : (-Complex.I) ^ yWeight q * Complex.I ^ yWeight q = 1 := by
    rw [← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow]
  simp only [star_mul', star_pow, star_neg, star_one, Complex.star_def, Complex.conj_I]
  linear_combination ((-1 : ℂ) ^ s.val * Complex.I ^ yWeight q) * h1

/-- Two Hermitian Paulis with `ω = 0` commute. -/
private theorem hermMatrix_commute {p q : Pauli n} (h : omega p q = 0) (s t : ZMod 2) :
    Commute (hermMatrix p s) (hermMatrix q t) := by
  have hdot : bitDot p.Z q.X = bitDot q.Z p.X := by
    have h' : bitDot p.Z q.X + bitDot p.X q.Z = 0 := h
    rw [bitDot_comm q.Z]
    have hc : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact hc _ _ h'
  unfold Commute SemiconjBy hermMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, pauliMatrix_mul,
    pauliMatrix_mul, add_comm q p, smul_smul, smul_smul, smul_smul, smul_smul, hdot]
  congr 1
  ring

/-- The projection is idempotent. -/
private theorem projMatrix_idem (q : Pauli n) (s : ZMod 2) :
    IsIdempotentElem (projMatrix q s) := by
  unfold IsIdempotentElem projMatrix
  have h2 : (1 + hermMatrix q s) * (1 + hermMatrix q s) = (2 : ℂ) • (1 + hermMatrix q s) := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hermMatrix_mul_self, two_smul]
    abel
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2, smul_smul]
  norm_num

/-- The projection is Hermitian. -/
private theorem conjTranspose_projMatrix (q : Pauli n) (s : ZMod 2) :
    (projMatrix q s)ᴴ = projMatrix q s := by
  unfold projMatrix
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    conjTranspose_hermMatrix]
  congr 1
  simp

/-- Projections of Paulis with `ω = 0` commute. -/
private theorem projMatrix_commute {p q : Pauli n} (h : omega p q = 0) (s t : ZMod 2) :
    Commute (projMatrix p s) (projMatrix q t) := by
  unfold projMatrix
  have h1 : Commute (1 + hermMatrix p s) (1 + hermMatrix q t) :=
    Commute.add_left (Commute.one_left _)
      (Commute.add_right (Commute.one_right _) (hermMatrix_commute h s t))
  exact (h1.smul_left _).smul_right _

/-- A projection fixes what its Hermitian Pauli fixes. -/
private theorem projMatrix_mul_of {ℓ : ℕ} {q : Pauli n} {s : ZMod 2}
    {V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ} (h : hermMatrix q s * V = V) :
    projMatrix q s * V = V := by
  unfold projMatrix
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, h, ← two_smul ℂ V, smul_smul]
  norm_num

/-- The projection applied to a function. -/
private theorem projMatrix_mulVec (q : Pauli n) (s : ZMod 2) (G : (Fin n → ZMod 2) → ℂ)
    (w : Fin n → ZMod 2) :
    (projMatrix q s *ᵥ G) w = (1 / 2 : ℂ) * (G w + ((-1 : ℂ) ^ s.val * Complex.I ^ yWeight q)
      * (signOf (bitDot q.Z (w + q.X)) * G (w + q.X))) := by
  unfold projMatrix hermMatrix
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, pauliMatrix_mulVec]

/-- **The Kraus operator of the conditionings**: `K_0 = 1` and
`K_{j+1} = ½(1 + (−1)^{s_j} G_j) K_j`. -/
private noncomputable def stabKraus (g : ℕ → Pauli n) (s : ℕ → ZMod 2) :
    ℕ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ
  | 0 => 1
  | j + 1 => projMatrix (g j) (s j) * stabKraus g s j

/-- The product fixes what each Hermitian Pauli fixes. -/
private theorem stabKraus_mul_fix {ℓ : ℕ} (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (r : ℕ)
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (hfix : ∀ i, i < r → hermMatrix (g i) (s i) * V = V) :
    ∀ j, j ≤ r → stabKraus g s j * V = V := by
  intro j
  induction j with
  | zero => intro _; exact Matrix.one_mul V
  | succ j ih =>
    intro hj
    show projMatrix (g j) (s j) * stabKraus g s j * V = V
    rw [Matrix.mul_assoc, ih (by omega), projMatrix_mul_of (hfix j (by omega))]

/-- Each projection commutes with the product, the Paulis having `ω = 0` pairwise. -/
private theorem stabKraus_commute (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (r : ℕ)
    (hcomm : ∀ i k, i < r → k < r → omega (g i) (g k) = 0) :
    ∀ j, j ≤ r → ∀ i, i < r → Commute (projMatrix (g i) (s i)) (stabKraus g s j) := by
  intro j
  induction j with
  | zero => intro _ i _; exact Commute.one_right _
  | succ j ih =>
    intro hj i hi
    exact (projMatrix_commute (hcomm i j hi (by omega)) _ _).mul_right (ih (by omega) i hi)

/-- The product is a Hermitian idempotent. -/
private theorem stabKraus_herm_idem (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (r : ℕ)
    (hcomm : ∀ i k, i < r → k < r → omega (g i) (g k) = 0) :
    ∀ j, j ≤ r → (stabKraus g s j)ᴴ = stabKraus g s j ∧ IsIdempotentElem (stabKraus g s j) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨Matrix.conjTranspose_one, IsIdempotentElem.one⟩
  | succ j ih =>
    intro hj
    obtain ⟨hH, hI⟩ := ih (by omega)
    have hc := stabKraus_commute g s r hcomm j (by omega) j (by omega)
    refine ⟨?_, (projMatrix_idem _ _).mul_of_commute hc hI⟩
    show (projMatrix (g j) (s j) * stabKraus g s j)ᴴ = projMatrix (g j) (s j) * stabKraus g s j
    rw [Matrix.conjTranspose_mul, hH, conjTranspose_projMatrix]
    exact hc.eq.symm

/-- **The product's Pauli coefficients and trace**: `tr(P K_j) = 0` off the span of `g_0, …,
g_{j−1}`, and `tr K_j = 2^{n−j}`, when each `g_j` is outside the span of the earlier ones. -/
private theorem stabKraus_trace (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (r : ℕ)
    (hind : ∀ j, j < r → g j ∉ Submodule.span (ZMod 2) (g '' Set.Iio j)) :
    ∀ j, j ≤ r → (∀ P : Pauli n, P ∉ Submodule.span (ZMod 2) (g '' Set.Iio j) →
        trace (pauliMatrix P * stabKraus g s j) = 0) ∧
      trace (stabKraus g s j) * 2 ^ j = 2 ^ n := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun P hP => ?_, ?_⟩
    · have hP0 : P ≠ 0 := fun h => hP (h ▸ Submodule.zero_mem _)
      show trace (pauliMatrix P * 1) = 0
      rw [Matrix.mul_one, trace_pauliMatrix, if_neg hP0]
    · show trace (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) * 2 ^ 0 = 2 ^ n
      rw [Matrix.trace_one, pow_zero, mul_one]
      simp [ZMod.card]
  | succ j ih =>
    intro hj
    obtain ⟨hzero, htr⟩ := ih (by omega)
    have hsub : Submodule.span (ZMod 2) (g '' Set.Iio j)
        ≤ Submodule.span (ZMod 2) (g '' Set.Iio (j + 1)) :=
      Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ j)))
    have hgj : g j ∈ Submodule.span (ZMod 2) (g '' Set.Iio (j + 1)) :=
      Submodule.subset_span ⟨j, Set.mem_Iio.mpr (Nat.lt_succ_self j), rfl⟩
    have hexp : ∀ M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
        trace (M * stabKraus g s (j + 1)) = (1 / 2 : ℂ) * (trace (M * stabKraus g s j)
          + ((-1 : ℂ) ^ (s j).val * Complex.I ^ yWeight (g j))
            * trace (M * pauliMatrix (g j) * stabKraus g s j)) := by
      intro M
      show trace (M * (projMatrix (g j) (s j) * stabKraus g s j)) = _
      unfold projMatrix hermMatrix
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul,
        ← Matrix.mul_assoc M (pauliMatrix _)]
      simp only [smul_eq_mul]
    refine ⟨fun P hP => ?_, ?_⟩
    · have hPg : P + g j ∉ Submodule.span (ZMod 2) (g '' Set.Iio j) := by
        intro h
        have h' := Submodule.sub_mem _ (hsub h) hgj
        rw [add_sub_cancel_right] at h'
        exact hP h'
      rw [hexp, pauliMatrix_mul, Matrix.smul_mul, Matrix.trace_smul,
        hzero P (fun h => hP (hsub h)), hzero (P + g j) hPg]
      simp
    · have h1 := hexp 1
      rw [Matrix.one_mul, Matrix.one_mul, Matrix.one_mul] at h1
      rw [h1, hzero (g j) (hind j (by omega)), mul_zero, add_zero, pow_succ, ← htr]
      ring

/-- A matrix with `tr(D† D) = 0` is zero. -/
private theorem eq_zero_of_trace_conjTranspose_mul_self {α β : Type*} [Fintype α] [Fintype β]
    (D : Matrix α β ℂ) (h : trace (Dᴴ * D) = 0) : D = 0 := by
  have hsum : trace (Dᴴ * D) = ((∑ i, ∑ j, Complex.normSq (D j i) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]
  rw [hsum, Complex.ofReal_eq_zero] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (D j i)))).mp h
  ext j i
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (D j i))).mp
    (h1 i (Finset.mem_univ _)) j (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp h2

/-- The code's projector is Hermitian. -/
private theorem conjTranspose_codeProjector {ℓ : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) :
    (codeProjector V)ᴴ = codeProjector V := by
  unfold codeProjector
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- **A Hermitian idempotent fixing the encoder's columns, of trace `2^ℓ`, is the code's
projector**: `(K − Π)†(K − Π) = K − Π` has trace `0`. -/
private theorem eq_codeProjector_of {ℓ : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (hVV : Vᴴ * V = 1) (K : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) (hKV : K * V = V)
    (hH : Kᴴ = K) (hI : IsIdempotentElem K) (htr : trace K = 2 ^ ℓ) : K = codeProjector V := by
  have hCI : codeProjector V * codeProjector V = codeProjector V := by
    unfold codeProjector
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hVV, Matrix.one_mul]
  have hKC : K * codeProjector V = codeProjector V := by
    unfold codeProjector
    rw [← Matrix.mul_assoc, hKV]
  have hCK : codeProjector V * K = codeProjector V := by
    have h := congrArg Matrix.conjTranspose hKC
    rwa [Matrix.conjTranspose_mul, conjTranspose_codeProjector, hH] at h
  have htrC : trace (codeProjector V) = 2 ^ ℓ := by
    unfold codeProjector
    rw [Matrix.trace_mul_comm, hVV, Matrix.trace_one]
    simp [ZMod.card]
  have hD : (K - codeProjector V)ᴴ * (K - codeProjector V) = K - codeProjector V := by
    rw [Matrix.conjTranspose_sub, hH, conjTranspose_codeProjector, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hI.eq, hKC, hCK, hCI]
    abel
  have htr0 : trace ((K - codeProjector V)ᴴ * (K - codeProjector V)) = 0 := by
    rw [hD, Matrix.trace_sub, htr, htrC, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_trace_conjTranspose_mul_self _ htr0)

/-- **The sign of a Pauli on the code**: if `P_q V = c V` with `V ≠ 0`, some sign `t` makes the
Hermitian Pauli `(−1)^t G_q` fix `V`, since `(i^y c)² = 1`. -/
private theorem exists_sign_of_eigen {ℓ : ℕ} (q : Pauli n)
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV0 : V ≠ 0) (c : ℂ)
    (hc : pauliMatrix q * V = c • V) : ∃ t : ZMod 2, hermMatrix q t * V = V := by
  have hc2 : c * c = signOf (bitDot q.Z q.X) := by
    have h1 : pauliMatrix q * pauliMatrix q * V = (c * c) • V := by
      rw [Matrix.mul_assoc, hc, Matrix.mul_smul, hc, smul_smul]
    rw [pauliMatrix_mul_self, Matrix.smul_mul, Matrix.one_mul] at h1
    have h2 : (signOf (bitDot q.Z q.X) - c * c) • V = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hV0
  have hu : (Complex.I ^ yWeight q * c) * (Complex.I ^ yWeight q * c) = 1 := by
    calc _ = (Complex.I ^ yWeight q * Complex.I ^ yWeight q) * (c * c) := by ring
      _ = 1 := by rw [I_pow_yWeight_mul_self, hc2, signOf_mul_self]
  rcases mul_self_eq_one_iff.mp hu with h | h
  · refine ⟨0, ?_⟩
    unfold hermMatrix
    rw [Matrix.smul_mul, hc, smul_smul, ZMod.val_zero, pow_zero, one_mul, h, one_smul]
  · refine ⟨1, ?_⟩
    unfold hermMatrix
    rw [Matrix.smul_mul, hc, smul_smul, show (1 : ZMod 2).val = 1 from rfl, pow_one, mul_assoc, h]
    norm_num

/-- **The code's projector is the conditionings' Kraus operator**: for a stabilizer encoder, a
basis of `S` (padded by `0`) and signs make `K_r = Π`, `r = dim S`; and `tr(P Π) = 0` off `S`. -/
private theorem exists_stabKraus {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : IsStabilizerEncoder S V) :
    ∃ (g : ℕ → Pauli n) (s : ℕ → ZMod 2),
      stabKraus g s (Module.finrank (ZMod 2) S) = codeProjector V ∧
      ∀ P, P ∉ S → trace (pauliMatrix P * codeProjector V) = 0 := by
  obtain ⟨hiso, hdim, hVV, hscal⟩ := hV
  set r := Module.finrank (ZMod 2) S with hr
  let b := Module.finBasis (ZMod 2) S
  let g : ℕ → Pauli n := fun j => if h : j < r then (b ⟨j, h⟩ : Pauli n) else 0
  have hgS : ∀ j, g j ∈ S := by
    intro j
    by_cases h : j < r
    · simp only [g, h, dif_pos]
      exact (b ⟨j, h⟩).2
    · simp only [g, h, dif_neg, not_false_eq_true]
      exact S.zero_mem
  have hcomm : ∀ i k, i < r → k < r → omega (g i) (g k) = 0 :=
    fun i k _ _ => hiso _ (hgS i) _ (hgS k)
  have hV0 : V ≠ 0 := by
    intro h
    rw [h, Matrix.mul_zero] at hVV
    exact one_ne_zero hVV.symm
  have hsign : ∀ j, j < r → ∃ t : ZMod 2, hermMatrix (g j) t * V = V := by
    intro j _
    obtain ⟨c, hc⟩ := hscal (g j) (hgS j)
    exact exists_sign_of_eigen (g j) V hV0 c hc
  choose! s hs using hsign
  have hli : LinearIndependent (ZMod 2) (S.subtype ∘ b) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hind : ∀ j, j < r → g j ∉ Submodule.span (ZMod 2) (g '' Set.Iio j) := by
    intro j hj
    have himg : g '' Set.Iio j = (S.subtype ∘ b) '' {i | i.val < j} := by
      ext P
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hir : i < r := lt_trans (Set.mem_Iio.mp hi) hj
        exact ⟨⟨i, hir⟩, Set.mem_Iio.mp hi, by simp [g, hir]⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.val, hi, by simp [g, show i.val < r from i.isLt]⟩
    have hgj : g j = (S.subtype ∘ b) ⟨j, hj⟩ := by simp [g, hj]
    rw [himg, hgj]
    exact hli.notMem_span_image (by simp)
  have hspan : Submodule.span (ZMod 2) (g '' Set.Iio r) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨j, _, rfl⟩; exact hgS j)
  obtain ⟨hHK, hIK⟩ := stabKraus_herm_idem g s r hcomm r le_rfl
  obtain ⟨hzero, htr⟩ := stabKraus_trace g s r hind r le_rfl
  have hKV := stabKraus_mul_fix g s r V hs r le_rfl
  have htrK : trace (stabKraus g s r) = 2 ^ ℓ := by
    have h2 : (2 : ℂ) ^ n = 2 ^ ℓ * 2 ^ r := by rw [← pow_add]; congr 1; omega
    rw [h2] at htr
    exact mul_right_cancel₀ (pow_ne_zero r two_ne_zero) htr
  have hK := eq_codeProjector_of V hVV _ hKV hHK hIK htrK
  refine ⟨g, s, hK, fun P hP => ?_⟩
  rw [← hK]
  exact hzero P (fun h => hP (hspan h))

/-! ### The proofs' lemmas: the protocol of the conditionings, and T50 on its branch -/

/-- A Pauli on the data bits, read on the data bits and `j` outcome bits, with no bits on the
outcome bits. -/
private def padPauli (j : ℕ) (q : Pauli n) : Pauli (n + j) :=
  ⟨Fin.append q.X 0, Fin.append q.Z 0⟩

/-- **The protocol of the conditionings**: condition on `g_0`, …, `g_{j−1}` in turn, each on the
data bits with the sign `s_i`. At precision `2` every conditioning letter is admitted. -/
private noncomputable def stabProto (g : ℕ → Pauli n) (s : ℕ → ZMod 2) :
    (j : ℕ) → Protocol 2 n j
  | 0 => Protocol.nil
  | j + 1 => Protocol.condition (stabProto g s j) ⟨s j, padPauli j (g j)⟩ (fun _ => le_refl 2)

/-- The padded Pauli's `zDot` sees only the data bits. -/
private theorem zDot_padPauli (j : ℕ) (q : Pauli n) (y : Fin n → ZMod 2) (z : Fin j → ZMod 2) :
    zDot (padPauli j q) (Fin.append y z) = zDot q y := by
  unfold zDot padPauli
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, ZMod.val_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- Padding keeps the number of Y. -/
private theorem yWeight_padPauli (j : ℕ) (q : Pauli n) : yWeight (padPauli j q) = yWeight q :=
  zDot_padPauli j q q.X 0

/-- Adding two words with zero outcome bits. -/
private theorem append_zero_add (j : ℕ) (w y : Fin n → ZMod 2) :
    Fin.append w (0 : Fin j → ZMod 2) + Fin.append y 0 = Fin.append (w + y) 0 := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [Pi.add_apply, Fin.append_left]
  · simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, add_zero]

/-- A word with zero outcome bits, without its last bit. -/
private theorem init_append_zero (j : ℕ) (w : Fin n → ZMod 2) :
    Fin.init (Fin.append w (0 : Fin (j + 1) → ZMod 2) : Fin (n + (j + 1)) → ZMod 2)
      = Fin.append w (0 : Fin j → ZMod 2) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · have e : (Fin.castSucc (Fin.castAdd j l) : Fin (n + j + 1)) = Fin.castAdd (j + 1) l :=
      Fin.ext rfl
    change Fin.append w (0 : Fin (j + 1) → ZMod 2) (Fin.castSucc (Fin.castAdd j l)) = _
    rw [e, Fin.append_left, Fin.append_left]
  · have e : (Fin.castSucc (Fin.natAdd n l) : Fin (n + j + 1)) = Fin.natAdd n (Fin.castSucc l) :=
      Fin.ext rfl
    change Fin.append w (0 : Fin (j + 1) → ZMod 2) (Fin.castSucc (Fin.natAdd n l)) = _
    rw [e, Fin.append_right, Fin.append_right]
    rfl

/-- A word with zero outcome bits has last bit `0`. -/
private theorem last_append_zero (j : ℕ) (w : Fin n → ZMod 2) :
    Fin.append w (0 : Fin (j + 1) → ZMod 2) (Fin.last (n + j))
      = 0 := by
  have e : (Fin.last (n + j) : Fin (n + j + 1)) = Fin.natAdd n (Fin.last j) :=
    Fin.ext (by simp only [Fin.val_last, Fin.val_natAdd])
  rw [e, Fin.append_right]
  rfl

/-- **The referee of the conditionings at the outcome `0`** is the product `K_j`. -/
private theorem interpretAmp_stabProto (g : ℕ → Pauli n) (s : ℕ → ZMod 2) :
    ∀ (j : ℕ) (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2),
      (stabProto g s j).interpretAmp f (Fin.append w 0) = (stabKraus g s j *ᵥ f) w := by
  intro j
  induction j with
  | zero =>
    intro f w
    show f (Fin.append w (0 : Fin 0 → ZMod 2)) = ((1 : Matrix _ _ ℂ) *ᵥ f) w
    rw [Matrix.one_mulVec]
    congr 1
    funext i
    exact Fin.append_left w 0 i
  | succ j ih =>
    intro f w
    show pauliProjection ⟨s j, padPauli j (g j)⟩
        (Fin.append w (0 : Fin (j + 1) → ZMod 2) (Fin.last (n + j)))
        ((stabProto g s j).interpretAmp f)
        (Fin.init (Fin.append w (0 : Fin (j + 1) → ZMod 2) : Fin (n + (j + 1)) → ZMod 2))
      = ((projMatrix (g j) (s j) * stabKraus g s j) *ᵥ f) w
    rw [last_append_zero, init_append_zero, ← Matrix.mulVec_mulVec, projMatrix_mulVec]
    unfold pauliProjection SignedPauli.act
    rw [pauliAct_apply]
    have hX : (padPauli j (g j)).X = Fin.append (g j).X 0 := rfl
    rw [hX, append_zero_add, zDot_padPauli, yWeight_padPauli, ih, ih, ZMod.val_zero, pow_zero,
      pow_add, pow_mul, Complex.I_sq, neg_one_pow_zDot]
    ring

/-- The point mass picks a column. -/
private theorem mulVec_delta (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (w x : Fin n → ZMod 2) : (M *ᵥ delta x) w = M w x := by
  simp only [Matrix.mulVec, dotProduct, delta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- **The Kraus operator of the conditionings**, every outcome bit read at `0`, is `K_k`. -/
private theorem krausOp_stabProto (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (k : ℕ)
    (e : Fin 0 → ZMod 2) :
    krausOp (stabProto g s k) (finCongr (Nat.add_zero k).symm) 0 e = stabKraus g s k := by
  have hcomp : (Fin.append (0 : Fin k → ZMod 2) e ∘ finCongr (Nat.add_zero k).symm) = 0 := by
    funext i
    show Fin.append (0 : Fin k → ZMod 2) e (Fin.cast (Nat.add_zero k).symm i) = 0
    rw [show (Fin.cast (Nat.add_zero k).symm i : Fin (k + 0)) = Fin.castAdd 0 i from Fin.ext rfl,
      Fin.append_left]
    rfl
  ext w x
  show (stabProto g s k).interpretAmp (delta x)
      (Fin.append w (Fin.append (0 : Fin k → ZMod 2) e ∘ finCongr (Nat.add_zero k).symm)) = _
  rw [hcomp, interpretAmp_stabProto, mulVec_delta]

/-- The entry of `A ρ B†` at `(a, b)` is `Σ_{x, x'} ρ(x, x') · A(a, x) · conj (B(b, x'))`.
Restated from `FTQCLib/Carrier/PauliTransfer.lean`, where it is private. -/
private theorem mul_mul_conjTranspose_apply {α β : Type*} [Fintype α] (A B : Matrix β α ℂ)
    (ρ : Matrix α α ℂ) (a b : β) :
    (A * ρ * Bᴴ) a b = ∑ x, ∑ x', ρ x x' * (A a x * starRingEnd ℂ (B b x')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- The branch at `o` is `ρ ↦ Σ_e K_{o,e} ρ K_{o,e}†`. Restated from
`FTQCLib/Carrier/PauliTransfer.lean`, where it is private. -/
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

/-- **The branch is `ρ ↦ Π ρ Π`** when the product is the code's projector. -/
private theorem channelBranch_stabProto {ℓ : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (k : ℕ) (hK : stabKraus g s k = codeProjector V) :
    channelBranch (stabProto g s k) (finCongr (Nat.add_zero k).symm) 0
      = fun ρ => codeProjector V * ρ * codeProjector V := by
  funext ρ
  rw [channelBranch_eq_sum_krausOp, Fintype.sum_unique, krausOp_stabProto, hK,
    conjTranspose_codeProjector]

/-- **χ's diagonal is `4^{−n} A`**: the one Kraus operator `Π`, `c(P) = 2^{−n} tr(P† Π)`, and
`P† = ±P`. -/
private theorem chi_stabProto {ℓ : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (g : ℕ → Pauli n) (s : ℕ → ZMod 2) (k : ℕ) (hK : stabKraus g s k = codeProjector V)
    (P : Pauli n) :
    chi (stabProto g s k) (finCongr (Nat.add_zero k).symm) 0 P P
      = ((4 : ℂ) ^ n)⁻¹ * enumeratorTermA (codeProjector V) P := by
  rw [(channel_eq_chi_sum _ _ (by norm_num) 0).1 P P, Fintype.sum_unique, krausOp_stabProto, hK]
  unfold pauliCoeff enumeratorTermA
  rw [conjTranspose_pauliMatrix, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, map_mul,
    map_mul, conj_signOf, map_inv₀, map_pow, map_ofNat]
  have h4 : ((4 : ℂ) ^ n)⁻¹ = ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ := by
    rw [← mul_inv, ← mul_pow]
    norm_num
  rw [h4]
  linear_combination (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹
      * trace (pauliMatrix P * codeProjector V)
      * starRingEnd ℂ (trace (pauliMatrix P * codeProjector V))) * signOf_mul_self (bitDot P.Z P.X)

/-- **The transfer-matrix diagonal of `ρ ↦ Π ρ Π` is `2^{−n} B`**, the signs of `P†` cancelling. -/
private theorem ptm_codeProjector {ℓ : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (P : Pauli n) :
    ptm (fun ρ => codeProjector V * ρ * codeProjector V) P P
      = ((2 : ℂ) ^ n)⁻¹ * enumeratorTermB (codeProjector V) P := by
  unfold ptm enumeratorTermB
  congr 1
  rw [conjTranspose_codeProjector, conjTranspose_pauliMatrix, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [Matrix.mul_assoc]

/-! ### The proofs' lemmas: qubit coordinates, and the Krawtchouk numbers as a character sum -/

/-- A Pauli's two bits on each qubit. -/
private def pauliCoord (P : Pauli n) : Fin n → ZMod 2 × ZMod 2 := fun i => (P.X i, P.Z i)

/-- The Paulis are the words over the four-letter alphabet `ZMod 2 × ZMod 2`. -/
private def pauliCoordEquiv : Pauli n ≃ (Fin n → ZMod 2 × ZMod 2) where
  toFun := pauliCoord
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A sum over the Paulis is a sum over the words. -/
private theorem sum_pauli_coord {M : Type*} [AddCommMonoid M] (f : Pauli n → M) :
    ∑ P, f P = ∑ x : Fin n → ZMod 2 × ZMod 2, f (pauliCoordEquiv.symm x) :=
  Fintype.sum_equiv pauliCoordEquiv _ _ (fun _ => rfl)

/-- The symplectic pairing on one qubit, `a.Z b.X + a.X b.Z`. -/
private def sympl1 (a b : ZMod 2 × ZMod 2) : ZMod 2 :=
  a.2 * b.1 + a.1 * b.2

/-- The sign of `ω` is the product over the qubits. -/
private theorem signOf_omega_prod (P Q : Pauli n) :
    signOf (omega P Q) = ∏ i, signOf (sympl1 (pauliCoord P i) (pauliCoord Q i)) := by
  unfold omega
  rw [← Finset.sum_add_distrib, signOf_sum]
  rfl

/-- The weight is the Hamming weight of the word. -/
private theorem weight_eq_hammingNorm (P : Pauli n) : weight P = hammingNorm (pauliCoord P) := by
  unfold weight hammingNorm pauliCoord
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Prod.mk_eq_zero, not_and_or]

/-- The one-qubit character sum, with the weight marked: `1 + 3X` at `b = 0`, `1 − X` otherwise. -/
private theorem coord_sum_poly (b : ZMod 2 × ZMod 2) :
    ∑ a : ZMod 2 × ZMod 2, Polynomial.C (signOf (sympl1 b a))
        * (if a = 0 then (1 : Polynomial ℂ) else Polynomial.X)
      = if b = 0 then 1 + 3 * Polynomial.X else 1 - Polynomial.X := by
  have hbit : ∀ g : ZMod 2 → Polynomial ℂ, ∑ c, g c = g 0 + g 1 := fun g => Fin.sum_univ_two g
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  obtain ⟨b1, b2⟩ := b
  rw [Fintype.sum_prod_type]
  simp only [hbit]
  rcases h b1 with rfl | rfl <;> rcases h b2 with rfl | rfl <;>
    simp +decide [sympl1, signOf_zero, signOf_one, h11] <;> ring

/-- The one-qubit character sum: `4` at `b = 0`, `0` otherwise. -/
private theorem coord_sum_sign (b : ZMod 2 × ZMod 2) :
    ∑ a : ZMod 2 × ZMod 2, signOf (sympl1 b a) = if b = 0 then (4 : ℂ) else 0 := by
  have hbit : ∀ g : ZMod 2 → ℂ, ∑ c, g c = g 0 + g 1 := fun g => Fin.sum_univ_two g
  have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  obtain ⟨b1, b2⟩ := b
  rw [Fintype.sum_prod_type]
  simp only [hbit]
  rcases h b1 with rfl | rfl <;> rcases h b2 with rfl | rfl <;>
    simp +decide [sympl1, signOf_zero, signOf_one, h11]
  norm_num

-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 equation:alddp
-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 paragraph:kraw
/-- **The weight-marked character sum factorises over the qubits**:
`Σ_Q (−1)^{ω(P, Q)} X^{wt Q} = (1 − X)^{wt P} (1 + 3X)^{n − wt P}`. Shor and Laflamme's count of
their `α_{dd′}` qubit by qubit: a qubit where `P` is `I` gives `1 + 3X`, one where it is not gives
`1 − X`. -/
private theorem sum_signOf_omega_X_pow (P : Pauli n) :
    ∑ Q : Pauli n, Polynomial.C (signOf (omega P Q)) * Polynomial.X ^ weight Q
      = (1 - Polynomial.X) ^ weight P * (1 + 3 * Polynomial.X) ^ (n - weight P) := by
  rw [sum_pauli_coord]
  have hfac : ∀ x : Fin n → ZMod 2 × ZMod 2,
      Polynomial.C (signOf (omega P (pauliCoordEquiv.symm x)))
          * Polynomial.X ^ weight (pauliCoordEquiv.symm x)
        = ∏ i, (Polynomial.C (signOf (sympl1 (pauliCoord P i) (x i)))
          * (if x i = 0 then (1 : Polynomial ℂ) else Polynomial.X)) := by
    intro x
    rw [signOf_omega_prod, weight_eq_hammingNorm, ECCLib.Delsarte.pow_hammingNorm_eq_prod,
      map_prod, ← Finset.prod_mul_distrib]
    rfl
  simp only [hfac]
  rw [← Fintype.prod_sum (fun i a => Polynomial.C (signOf (sympl1 (pauliCoord P i) a))
    * (if a = 0 then (1 : Polynomial ℂ) else Polynomial.X))]
  simp only [coord_sum_poly]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, weight_eq_hammingNorm]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => pauliCoord P i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hwt : (Finset.univ.filter (fun i => ¬ pauliCoord P i = 0)).card
      = hammingNorm (pauliCoord P) := rfl
  rw [hwt, mul_comm]
  congr 2
  omega

/-- **The weight class of the character sum is ECCLib's Krawtchouk number**:
`Σ_{wt Q = d} (−1)^{ω(P, Q)} = K_d(wt P)`, `kraw 4 n d (wt P)`. -/
private theorem sum_filter_weight_signOf_omega (P : Pauli n) (d : ℕ) :
    ∑ Q ∈ Finset.univ.filter (fun Q : Pauli n => weight Q = d), signOf (omega P Q)
      = (ECCLib.Delsarte.kraw 4 n d (weight P) : ℂ) := by
  have h := congrArg (fun p => Polynomial.coeff p d) (sum_signOf_omega_X_pow P)
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at h
  have hrhs : (1 - Polynomial.X) ^ weight P * (1 + 3 * Polynomial.X) ^ (n - weight P)
      = (ECCLib.Delsarte.krawPoly 4 n (weight P)).map (Int.castRingHom ℂ) := by
    have hC : (Polynomial.C (((4 : ℕ) : ℂ) - 1) : Polynomial ℂ) = 3 := by
      rw [show ((4 : ℕ) : ℂ) - 1 = 3 by norm_num]
      exact map_ofNat Polynomial.C 3
    rw [ECCLib.Delsarte.krawPoly_map_complex, hC]
  rw [hrhs, Polynomial.coeff_map, ← ECCLib.Delsarte.kraw_eq_coeff, eq_intCast] at h
  rw [← h, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  by_cases hQ : weight Q = d
  · rw [if_pos hQ, if_pos hQ.symm, mul_one]
  · rw [if_neg hQ, if_neg (Ne.symm hQ), mul_zero]

/-- **The character sum at `z`**:
`Σ_Q (−1)^{ω(P, Q)} z^{wt Q} = (1 − z)^{wt P} (1 + 3z)^{n − wt P}`. -/
private theorem sum_signOf_omega_pow (P : Pauli n) (z : ℂ) :
    ∑ Q : Pauli n, signOf (omega P Q) * z ^ weight Q
      = (1 - z) ^ weight P * (1 + 3 * z) ^ (n - weight P) := by
  have h := congrArg (Polynomial.eval z) (sum_signOf_omega_X_pow P)
  simpa only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_ofNat] using h

/-- A sum over the Paulis is a sum over the weight classes. -/
private theorem sum_by_weight {M : Type*} [AddCommMonoid M] (f : Pauli n → M) :
    ∑ P, f P = ∑ j ∈ Finset.range (n + 1),
      ∑ P ∈ Finset.univ.filter (fun P : Pauli n => weight P = j), f P :=
  (Finset.sum_fiberwise_of_maps_to
    (fun P _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (weight_le_n P))) f).symm

/-- **The duality summed over a weight class**: from `B(Q) = 2^{−n} Σ_P A(P)(−1)^{ω(P, Q)}`,
`B_d = 2^{−n} Σ_j K_d(j) A_j`. -/
private theorem weightEnumeratorB_eq_kraw (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (hdual : ∀ Q : Pauli n, enumeratorTermB M Q
      = ((2 : ℂ) ^ n)⁻¹ * ∑ P : Pauli n, enumeratorTermA M P * signOf (omega P Q)) (d : ℕ) :
    weightEnumeratorB M d = ((2 : ℂ) ^ n)⁻¹ * ∑ j ∈ Finset.range (n + 1),
      (ECCLib.Delsarte.kraw 4 n d j : ℂ) * weightEnumeratorA M j := by
  unfold weightEnumeratorB weightEnumeratorA
  simp only [hdual, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_filter_weight_signOf_omega]
  rw [sum_by_weight]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P hP => ?_)
  rw [(Finset.mem_filter.mp hP).2, mul_comm]

/-- **The duality as generating functions**:
`Σ_d B_d z^d = 2^{−n} Σ_j A_j (1 − z)^j (1 + 3z)^{n − j}`. -/
private theorem weightEnumeratorB_genfun (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (hdual : ∀ Q : Pauli n, enumeratorTermB M Q
      = ((2 : ℂ) ^ n)⁻¹ * ∑ P : Pauli n, enumeratorTermA M P * signOf (omega P Q)) (z : ℂ) :
    ∑ d ∈ Finset.range (n + 1), weightEnumeratorB M d * z ^ d
      = ((2 : ℂ) ^ n)⁻¹ * ∑ j ∈ Finset.range (n + 1),
          weightEnumeratorA M j * (1 - z) ^ j * (1 + 3 * z) ^ (n - j) := by
  have hB : ∑ d ∈ Finset.range (n + 1), weightEnumeratorB M d * z ^ d
      = ∑ Q : Pauli n, enumeratorTermB M Q * z ^ weight Q := by
    rw [sum_by_weight (fun Q => enumeratorTermB M Q * z ^ weight Q)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold weightEnumeratorB
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun Q hQ => ?_)
    rw [(Finset.mem_filter.mp hQ).2]
  have hA : ∑ j ∈ Finset.range (n + 1), weightEnumeratorA M j * (1 - z) ^ j * (1 + 3 * z) ^ (n - j)
      = ∑ P : Pauli n,
          enumeratorTermA M P * ((1 - z) ^ weight P * (1 + 3 * z) ^ (n - weight P)) := by
    rw [sum_by_weight (fun P => enumeratorTermA M P
      * ((1 - z) ^ weight P * (1 + 3 * z) ^ (n - weight P)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold weightEnumeratorA
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun P hP => ?_)
    rw [(Finset.mem_filter.mp hP).2, mul_assoc]
  rw [hB, hA]
  simp only [hdual, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← sum_signOf_omega_pow P z, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  ring

/-! ### The proofs' lemmas: the counts, Gottesman's -/

/-- A finite count as a `Nat.card`. -/
private theorem natCard_eq_card_filter (p : Pauli n → Prop) [DecidablePred p] :
    Nat.card {P : Pauli n // p P} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A subspace of `Pauli n` has `2^{dim}` elements. -/
private theorem card_filter_mem (S : Submodule (ZMod 2) (Pauli n)) [DecidablePred (· ∈ S)] :
    (Finset.univ.filter (· ∈ S)).card = 2 ^ Module.finrank (ZMod 2) S := by
  rw [← Fintype.card_subtype, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- A sum of a constant over a predicate is the count times the constant. -/
private theorem sum_ite_const (p : Pauli n → Prop) [DecidablePred p] (c : ℂ) :
    ∑ P : Pauli n, (if p P then c else 0) = ((Finset.univ.filter p).card : ℂ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- **Character orthogonality over `S`**: `Σ_{P ∈ S} (−1)^{ω(P, Q)}` is `|S|` on `N(S)` and `0`
off it, by translating by an element of `S` that `Q` does not commute with. -/
private theorem sum_mem_signOf_omega (S : Submodule (ZMod 2) (Pauli n)) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ normalizer S)] (Q : Pauli n) :
    ∑ P : Pauli n, (if P ∈ S then signOf (omega P Q) else 0)
      = if Q ∈ normalizer S then ((Finset.univ.filter (· ∈ S)).card : ℂ) else 0 := by
  by_cases hQ : Q ∈ normalizer S
  · rw [if_pos hQ, ← mul_one ((Finset.univ.filter (· ∈ S)).card : ℂ), ← sum_ite_const]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    by_cases hP : P ∈ S
    · rw [if_pos hP, if_pos hP, omega_comm, hQ P hP, signOf_zero]
    · rw [if_neg hP, if_neg hP]
  · rw [if_neg hQ]
    obtain ⟨P0, hP0, hω⟩ : ∃ P0 ∈ S, omega Q P0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ h
    have hω1 : omega P0 Q = 1 := by
      have h2 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      rw [omega_comm]
      exact h2 _ hω
    have hT : ∑ P : Pauli n, (if P ∈ S then signOf (omega P Q) else 0)
        = -∑ P : Pauli n, (if P ∈ S then signOf (omega P Q) else 0) := by
      calc ∑ P : Pauli n, (if P ∈ S then signOf (omega P Q) else 0)
          = ∑ P : Pauli n, (if P + P0 ∈ S then signOf (omega (P + P0) Q) else 0) :=
            (Fintype.sum_equiv (Equiv.addRight P0) _ _ (fun _ => rfl)).symm
        _ = ∑ P : Pauli n, -(if P ∈ S then signOf (omega P Q) else 0) := by
            refine Finset.sum_congr rfl (fun P _ => ?_)
            by_cases hP : P ∈ S
            · rw [if_pos (S.add_mem hP hP0), if_pos hP, omega_add_left, signOf_add, hω1,
                signOf_one]
              ring
            · have hP' : P + P0 ∉ S := fun h => hP (by simpa using S.sub_mem h hP0)
              rw [if_neg hP', if_neg hP, neg_zero]
        _ = _ := Finset.sum_neg_distrib _
    linear_combination hT / 2

/-- The encoder of a code is not zero: `Vᴴ V = 1` on a nonempty index. -/
private theorem ne_zero_of_conjTranspose_mul_self {ℓ : ℕ}
    {V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ} (hVV : Vᴴ * V = 1) : V ≠ 0 := by
  intro h
  rw [h, Matrix.mul_zero] at hVV
  exact one_ne_zero hVV.symm

/-- **`A(P) = 4^ℓ` on `S`**: `tr(P Π) = c · 2^ℓ` with the code's sign `c`, and `|c| = 1`. -/
private theorem enumeratorTermA_of_mem {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : IsStabilizerEncoder S V)
    {P : Pauli n} (hP : P ∈ S) : enumeratorTermA (codeProjector V) P = (4 : ℂ) ^ ℓ := by
  obtain ⟨c, hc⟩ := hV.2.2.2 P hP
  have hVV := hV.2.2.1
  have ht : trace (pauliMatrix P * codeProjector V) = c * 2 ^ ℓ := by
    unfold codeProjector
    rw [← Matrix.mul_assoc, hc, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm, hVV,
      Matrix.trace_one, smul_eq_mul]
    simp [ZMod.card]
  have hc2 : c * c = signOf (bitDot P.Z P.X) := by
    have h1 : pauliMatrix P * pauliMatrix P * V = (c * c) • V := by
      rw [Matrix.mul_assoc, hc, Matrix.mul_smul, hc, smul_smul]
    rw [pauliMatrix_mul_self, Matrix.smul_mul, Matrix.one_mul] at h1
    have h2 : (signOf (bitDot P.Z P.X) - c * c) • V = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h (ne_zero_of_conjTranspose_mul_self hVV)
  have hn1 : Complex.normSq c * Complex.normSq c = 1 := by
    rw [← Complex.normSq_mul, hc2]
    unfold signOf
    split <;> simp
  have hn : Complex.normSq c = 1 := by
    nlinarith [Complex.normSq_nonneg c]
  unfold enumeratorTermA
  rw [ht, map_mul, map_pow, map_ofNat]
  calc c * 2 ^ ℓ * (starRingEnd ℂ c * 2 ^ ℓ) = (c * starRingEnd ℂ c) * (4 : ℂ) ^ ℓ := by
        rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_pow]
        ring
    _ = (4 : ℂ) ^ ℓ := by rw [Complex.mul_conj, hn, Complex.ofReal_one, one_mul]

/-- **The enumerators of a stabilizer code**: `A(P) = 4^ℓ [P ∈ S]` and, from the duality,
`B(Q) = 2^ℓ [Q ∈ N(S)]` (Gottesman's counts, here derived). -/
private theorem enumeratorTerm_counts {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ normalizer S)]
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : IsStabilizerEncoder S V)
    (hzero : ∀ P, P ∉ S → trace (pauliMatrix P * codeProjector V) = 0)
    (hdual : ∀ Q : Pauli n, enumeratorTermB (codeProjector V) Q
      = ((2 : ℂ) ^ n)⁻¹ * ∑ P : Pauli n, enumeratorTermA (codeProjector V) P * signOf (omega P Q)) :
    (∀ P, enumeratorTermA (codeProjector V) P = if P ∈ S then (4 : ℂ) ^ ℓ else 0) ∧
      ∀ Q, enumeratorTermB (codeProjector V) Q = if Q ∈ normalizer S then (2 : ℂ) ^ ℓ else 0 := by
  have hA : ∀ P, enumeratorTermA (codeProjector V) P = if P ∈ S then (4 : ℂ) ^ ℓ else 0 := by
    intro P
    by_cases hP : P ∈ S
    · rw [if_pos hP, enumeratorTermA_of_mem S V hV hP]
    · rw [if_neg hP]
      unfold enumeratorTermA
      rw [hzero P hP, zero_mul]
  refine ⟨hA, fun Q => ?_⟩
  have hsum : ∑ P : Pauli n, enumeratorTermA (codeProjector V) P * signOf (omega P Q)
      = (4 : ℂ) ^ ℓ * ∑ P : Pauli n, (if P ∈ S then signOf (omega P Q) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hA]
    split_ifs <;> ring
  rw [hdual, hsum, sum_mem_signOf_omega, card_filter_mem]
  have hdim := hV.2.1
  by_cases hQ : Q ∈ normalizer S
  · rw [if_pos hQ, if_pos hQ]
    have h4 : (4 : ℂ) ^ ℓ = 2 ^ ℓ * 2 ^ ℓ := by rw [← mul_pow]; norm_num
    have h2 : (2 : ℂ) ^ n = 2 ^ ℓ * 2 ^ Module.finrank (ZMod 2) S := by
      rw [← pow_add, hdim]
    rw [h4, h2]
    push_cast
    field_simp
  · rw [if_neg hQ, if_neg hQ, mul_zero, mul_zero]

/-- **The counts and the LP's constraints**: `A_j = 4^ℓ |S_j|`, `B_j = 2^ℓ |N(S)_j|`,
`|S_j| ≤ |N(S)_j|`, and `2^ℓ B_j = A_j` below the distance. -/
private theorem weightEnumerator_counts {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ normalizer S)]
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hiso : IsStabilizer S)
    (hA : ∀ P, enumeratorTermA (codeProjector V) P = if P ∈ S then (4 : ℂ) ^ ℓ else 0)
    (hB : ∀ Q, enumeratorTermB (codeProjector V) Q
      = if Q ∈ normalizer S then (2 : ℂ) ^ ℓ else 0) (j : ℕ) :
    weightEnumeratorA (codeProjector V) j
        = ((4 ^ ℓ * Nat.card {P : Pauli n // P ∈ S ∧ weight P = j} : ℕ) : ℂ) ∧
      weightEnumeratorB (codeProjector V) j
        = ((2 ^ ℓ * Nat.card {P : Pauli n // P ∈ normalizer S ∧ weight P = j} : ℕ) : ℂ) ∧
      Nat.card {P : Pauli n // P ∈ S ∧ weight P = j}
        ≤ Nat.card {P : Pauli n // P ∈ normalizer S ∧ weight P = j} ∧
      ((j : ℕ∞) < distance S →
        (2 : ℂ) ^ ℓ * weightEnumeratorB (codeProjector V) j
          = weightEnumeratorA (codeProjector V) j) := by
  have hcount : ∀ (p : Pauli n → Prop) [DecidablePred p] (c : ℂ),
      ∑ P ∈ Finset.univ.filter (fun P : Pauli n => weight P = j), (if p P then c else 0)
        = ((Nat.card {P : Pauli n // p P ∧ weight P = j} : ℕ) : ℂ) * c := by
    intro p _ c
    rw [Finset.sum_filter, natCard_eq_card_filter, ← sum_ite_const]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    by_cases h1 : weight P = j <;> by_cases h2 : p P <;> simp [h1, h2]
  have hAj : weightEnumeratorA (codeProjector V) j
      = ((4 ^ ℓ * Nat.card {P : Pauli n // P ∈ S ∧ weight P = j} : ℕ) : ℂ) := by
    unfold weightEnumeratorA
    simp only [hA]
    rw [hcount (· ∈ S)]
    push_cast
    ring
  have hBj : weightEnumeratorB (codeProjector V) j
      = ((2 ^ ℓ * Nat.card {P : Pauli n // P ∈ normalizer S ∧ weight P = j} : ℕ) : ℂ) := by
    unfold weightEnumeratorB
    simp only [hB]
    rw [hcount (· ∈ normalizer S)]
    push_cast
    ring
  refine ⟨hAj, hBj, ?_, fun hj => ?_⟩
  · exact Nat.card_le_card_of_injective
      (fun x => (⟨x.1, subset_normalizer hiso x.2.1, x.2.2⟩ :
        {P : Pauli n // P ∈ normalizer S ∧ weight P = j}))
      (fun x y h => Subtype.ext (by simpa using h))
  · have hiff : ∀ P : Pauli n, (P ∈ normalizer S ∧ weight P = j) ↔ (P ∈ S ∧ weight P = j) := by
      intro P
      constructor
      · rintro ⟨hN, hw⟩
        refine ⟨?_, hw⟩
        rcases detectable_of_weight_lt (e := P) (by rw [hw]; exact hj) with h | h
        · exact h
        · exact absurd hN h
      · rintro ⟨hS, hw⟩
        exact ⟨subset_normalizer hiso hS, hw⟩
    have hcard : Nat.card {P : Pauli n // P ∈ normalizer S ∧ weight P = j}
        = Nat.card {P : Pauli n // P ∈ S ∧ weight P = j} :=
      Nat.card_congr (Equiv.subtypeEquivRight hiff)
    rw [hAj, hBj, hcard]
    push_cast
    have h4 : (4 : ℂ) ^ ℓ = 2 ^ ℓ * 2 ^ ℓ := by rw [← mul_pow]; norm_num
    rw [h4]
    ring

/-! ### The proofs' lemmas: the quantum Singleton bound, by counting on two regions

Not a source's proof (Knill and Laflamme defer theirs). For qubits `A`, character orthogonality on
`S` and on the Paulis inside `A` gives `|N(S)_A| |S| = 4^{|A|} |S_{A^c}|`, where `X_A` is the set
of elements of `X` supported inside `A` and `S_{A^c}` those of `S` vanishing on `A`. When `|A|` is
below the distance, `N(S)_A = S_A`. Two disjoint such regions `A`, `B` then give
`|S|² ≥ 4^{|A| + |B|}`, that is `|A| + |B| ≤ n − ℓ`. -/

/-- A nested indicator is the indicator of the conjunction. -/
private theorem ite_ite_zero {p q : Prop} [Decidable p] [Decidable q] (c : ℂ) :
    (if p then (if q then c else 0) else 0) = if p ∧ q then c else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- **Character orthogonality on the Paulis inside `A`**: `Σ_{P inside A} (−1)^{ω(Q, P)}` is
`4^{|A|}` when `Q` vanishes on `A`, and `0` otherwise. -/
private theorem sum_inside_signOf_omega (A : Finset (Fin n)) (Q : Pauli n) :
    ∑ P : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then signOf (omega Q P) else 0)
      = if ∀ i ∈ A, pauliCoord Q i = 0 then (4 : ℂ) ^ A.card else 0 := by
  rw [sum_pauli_coord]
  have hfac : ∀ x : Fin n → ZMod 2 × ZMod 2,
      (if ∀ i, i ∉ A → pauliCoord (pauliCoordEquiv.symm x) i = 0
        then signOf (omega Q (pauliCoordEquiv.symm x)) else 0)
        = ∏ i, (if i ∈ A ∨ x i = 0 then signOf (sympl1 (pauliCoord Q i) (x i)) else 0) := by
    intro x
    by_cases h : ∀ i, i ∉ A → pauliCoord (pauliCoordEquiv.symm x) i = 0
    · rw [if_pos h, signOf_omega_prod]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hi' : i ∈ A ∨ x i = 0 := by
        by_cases hi : i ∈ A
        · exact Or.inl hi
        · exact Or.inr (h i hi)
      rw [if_pos hi']
      rfl
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi, hx⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (if_neg (fun h' => h'.elim hi hx))).symm
  simp only [hfac]
  rw [← Fintype.prod_sum (fun i a =>
    if i ∈ A ∨ a = 0 then signOf (sympl1 (pauliCoord Q i) a) else 0)]
  have hcoord : ∀ i, (∑ a : ZMod 2 × ZMod 2,
      (if i ∈ A ∨ a = 0 then signOf (sympl1 (pauliCoord Q i) a) else 0))
        = if i ∈ A then (if pauliCoord Q i = 0 then (4 : ℂ) else 0) else 1 := by
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, true_or, if_true]
      exact coord_sum_sign _
    · simp only [hi, false_or, if_false]
      rw [Finset.sum_ite_eq' Finset.univ (0 : ZMod 2 × ZMod 2), if_pos (Finset.mem_univ _)]
      have h0 : sympl1 (pauliCoord Q i) 0 = 0 := by
        unfold sympl1
        simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero]
      rw [h0, signOf_zero]
  simp only [hcoord]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_zero, Finset.prod_const]
  split_ifs <;> rfl

/-- **The count on a region**: `|N(S)_A| |S| = 4^{|A|} |S_{A^c}|`. -/
private theorem card_inside_normalizer (S : Submodule (ZMod 2) (Pauli n))
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ normalizer S)] (A : Finset (Fin n)) :
    (Finset.univ.filter (fun P => P ∈ normalizer S ∧ ∀ i, i ∉ A → pauliCoord P i = 0)).card
        * (Finset.univ.filter (· ∈ S)).card
      = 4 ^ A.card
        * (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ A, pauliCoord P i = 0)).card := by
  have hT : ∑ P : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then
        ∑ Q : Pauli n, (if Q ∈ S then signOf (omega Q P) else 0) else 0)
      = ∑ Q : Pauli n, (if Q ∈ S then
        ∑ P : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then signOf (omega Q P) else 0)
          else 0) := by
    calc _ = ∑ P : Pauli n, ∑ Q : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then
            (if Q ∈ S then signOf (omega Q P) else 0) else 0) := by
          refine Finset.sum_congr rfl (fun P _ => ?_)
          by_cases hP : ∀ i, i ∉ A → pauliCoord P i = 0
          · rw [if_pos hP]
            exact Finset.sum_congr rfl (fun Q _ => (if_pos hP).symm)
          · rw [if_neg hP]
            exact (Finset.sum_eq_zero (fun Q _ => if_neg hP)).symm
      _ = ∑ Q : Pauli n, ∑ P : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then
            (if Q ∈ S then signOf (omega Q P) else 0) else 0) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl (fun Q _ => ?_)
          by_cases hQ : Q ∈ S
          · rw [if_pos hQ]
            exact Finset.sum_congr rfl (fun P _ => by rw [if_pos hQ])
          · rw [if_neg hQ]
            exact Finset.sum_eq_zero (fun P _ => by rw [if_neg hQ, ite_self])
  have hL : ∑ P : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then
        ∑ Q : Pauli n, (if Q ∈ S then signOf (omega Q P) else 0) else 0)
      = ((Finset.univ.filter (fun P => P ∈ normalizer S ∧ ∀ i, i ∉ A → pauliCoord P i = 0)).card
          : ℂ) * ((Finset.univ.filter (· ∈ S)).card : ℂ) := by
    simp only [sum_mem_signOf_omega]
    rw [← sum_ite_const]
    exact Finset.sum_congr rfl (fun P _ => (ite_ite_zero _).trans (if_congr and_comm rfl rfl))
  have hR : ∑ Q : Pauli n, (if Q ∈ S then
        ∑ P : Pauli n, (if ∀ i, i ∉ A → pauliCoord P i = 0 then signOf (omega Q P) else 0)
          else 0)
      = (4 : ℂ) ^ A.card
        * ((Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ A, pauliCoord P i = 0)).card : ℂ) := by
    simp only [sum_inside_signOf_omega]
    rw [mul_comm, ← sum_ite_const]
    exact Finset.sum_congr rfl (fun Q _ => ite_ite_zero _)
  have h := hL.symm.trans (hT.trans hR)
  exact_mod_cast h

/-- **The quantum Singleton bound** `2(d − 1) + ℓ ≤ n`, for every stabilizer code with `ℓ ≥ 1` and
every `d` at most its distance, degenerate included. -/
private theorem singleton_bound_of (S : Submodule (ZMod 2) (Pauli n)) (hiso : IsStabilizer S)
    {ℓ : ℕ} (hdim : ℓ + Module.finrank (ZMod 2) S = n) (hℓ : 1 ≤ ℓ) (d : ℕ)
    (hd : (d : ℕ∞) ≤ distance S) : 2 * (d - 1) + ℓ ≤ n := by
  classical
  set r := Module.finrank (ZMod 2) S with hr
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    omega
  have hcorr : ∀ A : Finset (Fin n), A.card ≤ d - 1 → ∀ P : Pauli n,
      (∀ i, i ∉ A → pauliCoord P i = 0) → P ∈ normalizer S → P ∈ S := by
    intro A hA P hP hN
    have hw : weight P ≤ A.card := by
      unfold weight
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiA
      have h0 := hP i hiA
      simp only [pauliCoord, Prod.mk_eq_zero] at h0
      tauto
    have hlt : (weight P : ℕ∞) < distance S := by
      have hwd : weight P < d := by omega
      exact lt_of_lt_of_le (by exact_mod_cast hwd) hd
    rcases detectable_of_weight_lt hlt with h | h
    · exact h
    · exact absurd hN h
  have hregion : ∀ A : Finset (Fin n), A.card ≤ d - 1 →
      (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i, i ∉ A → pauliCoord P i = 0)).card * 2 ^ r
        = 4 ^ A.card
          * (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ A, pauliCoord P i = 0)).card := by
    intro A hA
    have h := card_inside_normalizer S A
    rw [card_filter_mem] at h
    rw [← h]
    congr 2
    apply Finset.filter_congr
    intro P _
    exact ⟨fun ⟨hS, hP⟩ => ⟨subset_normalizer hiso hS, hP⟩,
      fun ⟨hN, hP⟩ => ⟨hcorr A hA P hP hN, hP⟩⟩
  set A := Finset.univ.filter (fun i : Fin n => (i : ℕ) < d - 1) with hAdef
  set B := Finset.univ.filter (fun i : Fin n => d - 1 ≤ (i : ℕ) ∧ (i : ℕ) < 2 * (d - 1))
    with hBdef
  have hAB : Disjoint A B := by
    rw [hAdef, hBdef, Finset.disjoint_filter]
    intro i _ h1 h2
    omega
  have hunion : A ∪ B = Finset.univ.filter (fun i : Fin n => (i : ℕ) < 2 * (d - 1)) := by
    ext i
    simp only [hAdef, hBdef, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcardA : A.card = min n (d - 1) := Fin.card_filter_val_lt
  have hcardAB : A.card + B.card = min n (2 * (d - 1)) := by
    rw [← Finset.card_union_of_disjoint hAB, hunion]
    exact Fin.card_filter_val_lt
  have hA : A.card ≤ d - 1 := by omega
  have hB : B.card ≤ d - 1 := by omega
  have h1 := hregion A hA
  have h2 := hregion B hB
  have hBA : (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i, i ∉ B → pauliCoord P i = 0)).card
      ≤ (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ A, pauliCoord P i = 0)).card := by
    apply Finset.card_le_card
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    exact ⟨hP.1, fun i hi => hP.2 i (Finset.disjoint_left.mp hAB hi)⟩
  have hAB' : (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i, i ∉ A → pauliCoord P i = 0)).card
      ≤ (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ B, pauliCoord P i = 0)).card := by
    apply Finset.card_le_card
    intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    exact ⟨hP.1, fun i hi => hP.2 i (Finset.disjoint_right.mp hAB hi)⟩
  have hzero : ∀ X : Finset (Fin n),
      0 < (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i, i ∉ X → pauliCoord P i = 0)).card :=
    fun X => Finset.card_pos.mpr ⟨0, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S.zero_mem, fun _ _ => rfl⟩⟩
  set cA := (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i, i ∉ A → pauliCoord P i = 0)).card
  set cB := (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i, i ∉ B → pauliCoord P i = 0)).card
  set eA := (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ A, pauliCoord P i = 0)).card
  set eB := (Finset.univ.filter (fun P => P ∈ S ∧ ∀ i ∈ B, pauliCoord P i = 0)).card
  have hkey : 4 ^ A.card * 4 ^ B.card * (cA * cB) ≤ 2 ^ r * 2 ^ r * (cA * cB) := by
    calc 4 ^ A.card * 4 ^ B.card * (cA * cB) ≤ 4 ^ A.card * 4 ^ B.card * (eA * eB) := by
          apply Nat.mul_le_mul_left
          calc cA * cB ≤ eB * eA := Nat.mul_le_mul hAB' hBA
            _ = eA * eB := mul_comm _ _
      _ = (4 ^ A.card * eA) * (4 ^ B.card * eB) := by ring
      _ = (cA * 2 ^ r) * (cB * 2 ^ r) := by rw [h1, h2]
      _ = 2 ^ r * 2 ^ r * (cA * cB) := by ring
  have hpow : 4 ^ (A.card + B.card) ≤ 4 ^ r := by
    have h := Nat.le_of_mul_le_mul_right hkey (Nat.mul_pos (hzero A) (hzero B))
    rw [pow_add]
    calc 4 ^ A.card * 4 ^ B.card ≤ 2 ^ r * 2 ^ r := h
      _ = 4 ^ r := by rw [← mul_pow]; norm_num
  have hle : A.card + B.card ≤ r := (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow
  omega

/-! ### The proofs' lemmas: ECCLib's LP and Hamming bounds on `N(S)` -/

/-- The Hamming distance of two Paulis' words is the weight of their sum. -/
private theorem hammingDist_pauliCoord (P Q : Pauli n) :
    hammingDist (pauliCoord P) (pauliCoord Q) = weight (P + Q) := by
  have key : ∀ a b : ZMod 2, a = b ↔ a + b = 0 := by decide
  unfold hammingDist weight pauliCoord
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq, X_add, Z_add,
    Pi.add_apply]
  rw [key (P.X i) (Q.X i), key (P.Z i) (Q.Z i), not_and_or]

/-- **The sphere-packing bound** `M·V_q(n, t) ≤ qⁿ`. Restated from
`ECCLib/Delsarte/Corollaries.lean` (`hamming_bound_direct`), which this module does not import. -/
private theorem hamming_bound_direct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {t : ℕ}
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y) :
    C.card * (∑ j ∈ Finset.range (t + 1),
        (Fintype.card ι).choose j * (Fintype.card A - 1) ^ j)
      ≤ Fintype.card A ^ Fintype.card ι := by
  classical
  set ball : (ι → A) → Finset (ι → A) :=
    fun x => Finset.univ.filter fun y => hammingDist x y ≤ t with hball
  have hdisj : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (ball x) (ball y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro z hzx hzy
    rw [hball] at hzx hzy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzx hzy
    have htri : hammingDist x y ≤ hammingDist x z + hammingDist z y :=
      hammingDist_triangle x z y
    have hzy' : hammingDist z y ≤ t := by rwa [hammingDist_comm] at hzy
    have := hd x hx y hy hne
    omega
  calc C.card * (∑ j ∈ Finset.range (t + 1),
        (Fintype.card ι).choose j * (Fintype.card A - 1) ^ j)
      = ∑ x ∈ C, (ball x).card := by
        rw [Finset.sum_congr rfl fun x _ => ECCLib.Delsarte.card_ball x t, Finset.sum_const,
          smul_eq_mul]
    _ = (C.biUnion ball).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (ι → A)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card A ^ Fintype.card ι := by rw [Finset.card_univ, Fintype.card_fun]

/-- **The LP and Hamming bounds on `N(S)`** for nondegenerate codes: `N(S)`, as `2^{n+ℓ}` words
over the four-letter alphabet, is a classical code of the given minimum distance, and ECCLib's
`LPCert` and the sphere-packing bound apply to it unchanged. -/
private theorem lp_hamming_bounds (S : Submodule (ZMod 2) (Pauli n)) {ℓ : ℕ}
    (hdim : ℓ + Module.finrank (ZMod 2) S = n) :
    (∀ (d : ℕ) (c : ECCLib.Delsarte.LPCert 4 n d),
      (∀ P ∈ normalizer S, P ≠ 0 → d ≤ weight P) → (2 : ℤ) ^ (n + ℓ) * c.beta 0 ≤ c.value) ∧
    (∀ t : ℕ, (∀ P ∈ normalizer S, P ≠ 0 → 2 * t + 1 ≤ weight P) →
      2 ^ ℓ * ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j ≤ 2 ^ n) := by
  classical
  set C := (Finset.univ.filter (· ∈ normalizer S)).image (pauliCoord (n := n)) with hC
  have hinj : Function.Injective (pauliCoord (n := n)) := pauliCoordEquiv.injective
  have hcard : C.card = 2 ^ (n + ℓ) := by
    rw [hC, Finset.card_image_of_injective _ hinj, card_filter_mem, finrank_normalizer]
    congr 1
    omega
  have hdist : ∀ d : ℕ, (∀ P ∈ normalizer S, P ≠ 0 → d ≤ weight P) →
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
    intro d hd x hx y hy hxy
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hy
    rw [hammingDist_pauliCoord]
    refine hd _ ((normalizer S).add_mem (Finset.mem_filter.mp hP).2
      (Finset.mem_filter.mp hQ).2) (fun h0 => hxy ?_)
    have hPQ : P = Q := by
      calc P = P + Q + Q := by rw [add_assoc, pauli_add_self, add_zero]
        _ = Q := by rw [h0, zero_add]
    rw [hPQ]
  have hcard4 : Fintype.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Fintype.card_prod, ZMod.card]
  refine ⟨fun d c hd => ?_, fun t ht => ?_⟩
  · have h := ECCLib.Delsarte.LPCert.card_mul_le_value' (A := ZMod 2 × ZMod 2) c hcard4
      (Fintype.card_fin n) C (hdist d hd)
    rw [hcard] at h
    exact_mod_cast h
  · have h := hamming_bound_direct (t := t) C (hdist (2 * t + 1) ht)
    rw [hcard, hcard4, Fintype.card_fin] at h
    have h' : 2 ^ n * (2 ^ ℓ * ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j)
        ≤ 2 ^ n * 2 ^ n := by
      calc 2 ^ n * (2 ^ ℓ * ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j)
          = 2 ^ (n + ℓ) * ∑ j ∈ Finset.range (t + 1), n.choose j * (4 - 1) ^ j := by
            rw [pow_add]
            ring
        _ ≤ 4 ^ n := h
        _ = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    exact Nat.le_of_mul_le_mul_left h' (by positivity)

-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 equation:macw
-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 equation:kraw
-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 equation:hadf9d1264733
-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 theorem:2
-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 corollary:9
-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 paragraph:h70349ec4f166
-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   theorem:theorem:5min
/-- **The quantum MacWilliams identity, as T50's diagonal duality on `ρ ↦ Π ρ Π`, and the bounds
it transports.** For a stabilizer code of `S` with encoder `V` and projector `Π = codeProjector V`
(`K = tr Π = 2^ℓ`):

1. *T50 on `Π`'s doubled state.* Some protocol at precision `2` with `k` conditioning letters (a
   basis of `S`) and every outcome bit read has, at some read string `o`, the branch `ρ ↦ Π ρ Π`;
   its χ diagonal (T50's `chi`, the Gram data of `Π`'s doubled state read in the Bell basis) is
   `χ(P, P) = 4^{−n} A(P)` and its transfer-matrix diagonal is `R(P, P) = 2^{−n} B(P)`, the
   enumerators' summands. The doubled state is linear in `Π`; both diagonals are quadratic.
2. *The duality per Pauli.* T50's `R(Q, Q) = Σ_P χ(P, P)(−1)^{ω(P, Q)}`
   (`ptm_diag_eq_walsh_chi_diag`) read through (1): `B(Q) = 2^{−n} Σ_P A(P)(−1)^{ω(P, Q)}`.
3. *Summed over weight classes*, the quantum MacWilliams identity: `B_d = 2^{−n} Σ_j K_d(j) A_j`
   with ECCLib's quaternary Krawtchouk number `K_d(j) = kraw 4 n d j`, for `d ≤ n`; and as
   generating functions, `Σ_d B_d z^d = 2^{−n} Σ_j A_j (1 − z)^j (1 + 3z)^{n−j}`. Shor and
   Laflamme's form, with their normalisation `K²`, `K` divided out, has `K / 2^n` in front; Rains's
   `A(x, y) = B((x + 3y)/2, (x − y)/2)` is the inverse transform. The identity is reached through
   T50 and ECCLib's `kraw`; ECCLib's `macwilliams`, for linear codes over a field with the dot
   product, is not re-proved and not applied as stated (the fidelity note, Claim 6).
4. *The counts and the LP's constraints.* `A_j = 4^ℓ |S_j|` and `B_j = 2^ℓ |N(S)_j|`, where `X_j`
   is the set of elements of `X` of weight `j`; so `|S_j| ≤ |N(S)_j|` (Rains's `K B_j ≥ A_j ≥ 0`),
   with equality, `K B_j = A_j`, at every weight below the distance (Rains's Corollary 9). These
   are the linear programme's constraints of Shor and Laflamme and of Rains, for every code,
   degenerate included.
5. *The quantum Singleton bound*, for every code with `ℓ ≥ 1`, degenerate included:
   `2(d − 1) + ℓ ≤ n` for every `d` at most the distance. Knill and Laflamme state it for
   `e`-error-correcting codes, `r ≥ 4e + ⌈log k⌉`, which is the case `d = 2e + 1`; this form, at
   every `d`, is Gottesman's.
6. *The LP bound through ECCLib's certificates*, for nondegenerate codes: when every nonzero
   element of `N(S)` has weight at least `d`, `N(S)` is a classical code of `2^{n+ℓ}` words over
   the four-letter alphabet with minimum distance `d`, and every `LPCert 4 n d` bounds it,
   `2^{n+ℓ} β₀ ≤ value`. For a degenerate code `N(S)` has low-weight elements in `S`, ECCLib's
   `IsInnerDistribution` fails, and the LP's content is the constraints of (4).
7. *The quantum Hamming bound, for nondegenerate codes only*: when every nonzero element of `N(S)`
   has weight at least `2t + 1`, `2^ℓ Σ_{j ≤ t} C(n, j) 3^j ≤ 2^n`. It is not stated for degenerate
   codes, for which it is not proved (Gottesman).

Proved at T51.3.1. -/
theorem quantum_macwilliams {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : IsStabilizerEncoder S V) :
    (∃ (k : ℕ) (p : Protocol 2 n k) (o : Fin k → ZMod 2),
      channelBranch p (finCongr (Nat.add_zero k).symm) o
          = (fun ρ => codeProjector V * ρ * codeProjector V) ∧
        ∀ P : Pauli n,
          chi p (finCongr (Nat.add_zero k).symm) o P P
              = ((4 : ℂ) ^ n)⁻¹ * enumeratorTermA (codeProjector V) P ∧
            ptm (channelBranch p (finCongr (Nat.add_zero k).symm) o) P P
              = ((2 : ℂ) ^ n)⁻¹ * enumeratorTermB (codeProjector V) P) ∧
    (∀ Q : Pauli n, enumeratorTermB (codeProjector V) Q
        = ((2 : ℂ) ^ n)⁻¹ * ∑ P : Pauli n,
            enumeratorTermA (codeProjector V) P * signOf (omega P Q)) ∧
    (∀ d : ℕ, d ≤ n → weightEnumeratorB (codeProjector V) d
        = ((2 : ℂ) ^ n)⁻¹ * ∑ j ∈ Finset.range (n + 1),
            (ECCLib.Delsarte.kraw 4 n d j : ℂ) * weightEnumeratorA (codeProjector V) j) ∧
    (∀ z : ℂ, ∑ d ∈ Finset.range (n + 1), weightEnumeratorB (codeProjector V) d * z ^ d
        = ((2 : ℂ) ^ n)⁻¹ * ∑ j ∈ Finset.range (n + 1),
            weightEnumeratorA (codeProjector V) j * (1 - z) ^ j * (1 + 3 * z) ^ (n - j)) ∧
    (∀ j : ℕ,
      weightEnumeratorA (codeProjector V) j
          = ((4 ^ ℓ * Nat.card {P : Pauli n // P ∈ S ∧ weight P = j} : ℕ) : ℂ) ∧
        weightEnumeratorB (codeProjector V) j
          = ((2 ^ ℓ * Nat.card {P : Pauli n // P ∈ normalizer S ∧ weight P = j} : ℕ) : ℂ) ∧
        Nat.card {P : Pauli n // P ∈ S ∧ weight P = j}
          ≤ Nat.card {P : Pauli n // P ∈ normalizer S ∧ weight P = j} ∧
        ((j : ℕ∞) < distance S →
          (2 : ℂ) ^ ℓ * weightEnumeratorB (codeProjector V) j
            = weightEnumeratorA (codeProjector V) j)) ∧
    (1 ≤ ℓ → ∀ d : ℕ, (d : ℕ∞) ≤ distance S → 2 * (d - 1) + ℓ ≤ n) ∧
    (∀ (d : ℕ) (c : ECCLib.Delsarte.LPCert 4 n d),
      (∀ P ∈ normalizer S, P ≠ 0 → d ≤ weight P) → (2 : ℤ) ^ (n + ℓ) * c.beta 0 ≤ c.value) ∧
    (∀ t : ℕ, (∀ P ∈ normalizer S, P ≠ 0 → 2 * t + 1 ≤ weight P) →
      2 ^ ℓ * ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j ≤ 2 ^ n) := by
  classical
  obtain ⟨g, s, hK, hzero⟩ := exists_stabKraus S V hV
  have hbranch := channelBranch_stabProto V g s _ hK
  have hdual : ∀ Q : Pauli n, enumeratorTermB (codeProjector V) Q
      = ((2 : ℂ) ^ n)⁻¹ * ∑ P : Pauli n,
          enumeratorTermA (codeProjector V) P * signOf (omega P Q) := by
    intro Q
    have h := (ptm_diag_eq_walsh_chi_diag (stabProto g s (Module.finrank (ZMod 2) S))
      (finCongr (Nat.add_zero _).symm) (by norm_num) 0 Q).2
    rw [hbranch, ptm_codeProjector] at h
    simp only [chi_stabProto V g s _ hK] at h
    have h4 : ((4 : ℂ) ^ n)⁻¹ = ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      norm_num
    simp only [h4, mul_assoc, ← Finset.mul_sum] at h
    exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero n two_ne_zero)) h
  obtain ⟨hA, hB⟩ := enumeratorTerm_counts S V hV hzero hdual
  refine ⟨⟨_, stabProto g s (Module.finrank (ZMod 2) S), 0, hbranch, fun P =>
      ⟨chi_stabProto V g s _ hK P, by rw [hbranch]; exact ptm_codeProjector V P⟩⟩,
    hdual, fun d _ => weightEnumeratorB_eq_kraw _ hdual d, weightEnumeratorB_genfun _ hdual,
    weightEnumerator_counts S V hV.1 hA hB, fun hℓ d hd => singleton_bound_of S hV.1 hV.2.1 hℓ d hd,
    (lp_hamming_bounds S hV.2.1).1, (lp_hamming_bounds S hV.2.1).2⟩

/-! ## Knill–Laflamme as T27's Gram condition -/

/-- **The error images as one amplitude function**, for T27's `gram`: on `(ℓ + e) + n` bits, the
read bits the codeword index `i` (first `ℓ`) and the error label `a` (next `e`), the unread bits the
`n` physical qubits `u`, and the value `(A_a V)(u, i)`, the `u`-th amplitude of the error `A_a`
applied to the `i`-th codeword. Its Gram data over the read bits at `(i, a)` and `(j, b)` is
`⟨j| Vᴴ A_b† A_a V |i⟩`. -/
noncomputable def errorImages {ℓ e : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    (Fin ((ℓ + e) + n) → ZMod 2) → ℂ :=
  fun w => (A (fun j => w (Fin.castAdd n (Fin.natAdd ℓ j))) * V)
    (fun u => w (Fin.natAdd (ℓ + e) u)) (fun i => w (Fin.castAdd n (Fin.castAdd e i)))

-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   theorem:theorem:linear
/-- **The code with encoder `V` corrects the errors `A`**: some trace-preserving recovery, Kraus
operators `R_r` with `Σ_r R_r† R_r = 1`, has every `R_r A_a` a scalar `λ_{ra}` on the code,
`R_r A_a V = λ_{ra} V`. Knill and Laflamme's error-free recovery (their theorem `linear`: `A_a` is
corrected by `R` exactly when `R_r A_a = λ_{ra} I` on the code). The recovery is a family indexed
by bit strings, of any length. -/
def CorrectsErrors {ℓ e : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Prop :=
  ∃ (s : ℕ) (R : (Fin s → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (lam : (Fin s → ZMod 2) → (Fin e → ZMod 2) → ℂ),
    ∑ r, (R r)ᴴ * R r = 1 ∧ ∀ r a, R r * A a * V = lam r a • V

/-! ### The proofs' lemmas: the Gram data of the error images -/

/-- **The Gram data of the error images** at `(i, a)` and `(j, b)` is the `(j, i)` entry of
`(A_b V)† (A_a V)`. -/
private theorem gram_errorImages {ℓ e : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (i j : Fin ℓ → ZMod 2) (a b : Fin e → ZMod 2) :
    gram (errorImages V A) (Fin.append i a) (Fin.append j b)
      = ((A b * V)ᴴ * (A a * V)) j i := by
  unfold gram errorImages
  simp only [Fin.append_left, Fin.append_right]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm]

/-- **The Gram condition as scalar blocks**: the Gram data is `δ_{ij} C_{ba}` exactly when every
block `(A_b V)† (A_a V)` is `C_{ba}` times the identity. -/
private theorem gram_condition_iff {ℓ e : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    (∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
        ∀ (i j : Fin ℓ → ZMod 2) (a b : Fin e → ZMod 2),
          gram (errorImages V A) (Fin.append i a) (Fin.append j b)
            = if i = j then C b a else 0) ↔
      ∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
        ∀ a b, (A b * V)ᴴ * (A a * V) = C b a • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ) := by
  simp only [gram_errorImages]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun a b => ?_⟩
    ext j i
    rw [hC i j a b, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i j a b => ?_⟩
    rw [hC a b, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   equation:hb058cca9516f
/-- **Necessity**: a recovery with `R_r A_a V = λ_{ra} V` makes every block
`(A_b V)† (A_a V) = Σ_r conj(λ_{rb}) λ_{ra}` times the identity, inserting `Σ_r R_r† R_r = 1`. -/
private theorem scalar_of_correctsErrors {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : Vᴴ * V = 1)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (h : CorrectsErrors V A) :
    ∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
      ∀ a b, (A b * V)ᴴ * (A a * V) = C b a • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ) := by
  obtain ⟨s, R, lam, hsum, hR⟩ := h
  refine ⟨fun b a => ∑ r, star (lam r b) * lam r a, fun a b => ?_⟩
  calc (A b * V)ᴴ * (A a * V) = (A b * V)ᴴ * ((∑ r, (R r)ᴴ * R r) * (A a * V)) := by
        rw [hsum, Matrix.one_mul]
    _ = ∑ r, (R r * A b * V)ᴴ * (R r * A a * V) := by
        rw [Matrix.sum_mul, Matrix.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ∑ r, (star (lam r b) * lam r a) • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hR r b, hR r a, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hV,
          smul_smul]
    _ = _ := by rw [← Finset.sum_smul]

/-- The scalars of the blocks form a Hermitian matrix: the dagger of the `(a, b)` block is the
`(b, a)` block. -/
private theorem isHermitian_of_scalar {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ)
    (hC : ∀ a b, (A b * V)ᴴ * (A a * V) = C b a • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ)) :
    Matrix.IsHermitian C := by
  refine Matrix.IsHermitian.ext (fun a b => ?_)
  have h := congrArg Matrix.conjTranspose (hC a b)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC b a,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one] at h
  have h0 := congrFun (congrFun h 0) 0
  simpa using h0.symm

/-- **The rotated error images** `M_k = Σ_a U_{ak} A_a V` have blocks `M_k† M_l = (U† C U)_{kl}`
times the identity. -/
private theorem rotated_blocks {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (C U : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ)
    (hC : ∀ a b, (A b * V)ᴴ * (A a * V) = C b a • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ))
    (k l : Fin e → ZMod 2) :
    (∑ b, U b k • (A b * V))ᴴ * (∑ a, U a l • (A a * V))
      = (Uᴴ * C * U) k l • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ) := by
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hC,
    smul_smul]
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  ring

/-- **The error images from the rotated ones**: `A_a V = Σ_l conj(U_{al}) M_l` when
`U U† = 1`. -/
private theorem errorImage_eq_sum_rotated {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (U : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ) (hU : U * Uᴴ = 1) (a : Fin e → ZMod 2) :
    A a * V = ∑ l, star (U a l) • ∑ a', U a' l • (A a' * V) := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hUU : ∀ a', ∑ l, star (U a l) * U a' l = (1 : Matrix (Fin e → ZMod 2) _ ℂ) a' a := by
    intro a'
    rw [← hU, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.conjTranspose_apply, mul_comm]
  simp_rw [hUU, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034 equation:recovop
-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034 equation:arecovop
-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034 equation:nutoi
/-- **Sufficiency, given a diagonalisation** `U† C U = diag(d)` with `U U† = 1`. Knill and
Laflamme's recovery: the rotated images `M_k = Σ_a U_{ak} A_a V` have orthogonal ranges
(`M_k† M_l = δ_{kl} d_k`), `R_k = d_k^{−1/2} V M_k†` returns the range of `M_k` to the code, and
`1 − P`, `P = Σ_k d_k^{−1} M_k M_k†` the projector onto the ranges, completes the recovery. The
diagonalisation stands in for the source's Gram–Schmidt on `A_a |0_L⟩`. The recovery is indexed
by `e + 1` bits: the first bit `0` for `R_k`, `k` the rest, and `1` followed by `0` for `1 − P`. -/
private theorem correctsErrors_of_diagonal {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : Vᴴ * V = 1)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (C U : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ)
    (hC : ∀ a b, (A b * V)ᴴ * (A a * V) = C b a • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ))
    (hU : U * Uᴴ = 1) (d : (Fin e → ZMod 2) → ℝ)
    (hD : Uᴴ * C * U = Matrix.diagonal (fun k => (d k : ℂ))) : CorrectsErrors V A := by
  obtain ⟨M, hM⟩ : ∃ M : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ,
      ∀ k, M k = ∑ a, U a k • (A a * V) := ⟨_, fun _ => rfl⟩
  have hMM : ∀ k l, (M k)ᴴ * M l
      = (if k = l then (d k : ℂ) else 0) • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ) := by
    intro k l
    rw [hM, hM, rotated_blocks V A C U hC, hD, Matrix.diagonal_apply]
  have hAV : ∀ a, A a * V = ∑ l, star (U a l) • M l := by
    intro a
    simp_rw [hM]
    exact errorImage_eq_sum_rotated V A U hU a
  have hd : ∀ k, 0 ≤ d k := by
    intro k
    have h := congrFun (congrFun (hMM k k) 0) 0
    rw [if_pos rfl, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_sum] at h
    rw [← Complex.ofReal_inj.mp h]
    exact Finset.sum_nonneg (fun u _ => Complex.normSq_nonneg _)
  have hM0 : ∀ l, d l = 0 → M l = 0 := by
    intro l hl
    apply eq_zero_of_trace_conjTranspose_mul_self
    rw [hMM, if_pos rfl, hl, Complex.ofReal_zero, zero_smul, Matrix.trace_zero]
  have hwd : ∀ l, ((((d l)⁻¹ : ℝ) : ℂ) * (d l : ℂ)) • M l = M l := by
    intro l
    by_cases hl : d l = 0
    · rw [hM0 l hl, smul_zero]
    · rw [← Complex.ofReal_mul, inv_mul_cancel₀ hl, Complex.ofReal_one, one_smul]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
      P = ∑ k, (((d k)⁻¹ : ℝ) : ℂ) • (M k * (M k)ᴴ) := ⟨_, rfl⟩
  have hPM : ∀ l, P * M l = M l := by
    intro l
    rw [hP, Matrix.sum_mul]
    simp_rw [Matrix.smul_mul, Matrix.mul_assoc, hMM, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    rw [Finset.sum_eq_single l (fun k _ hk => by rw [if_neg hk, mul_zero, zero_smul])
      (fun h => absurd (Finset.mem_univ l) h), if_pos rfl, hwd]
  have hPP : P * P = P := by
    calc P * P = P * ∑ k, (((d k)⁻¹ : ℝ) : ℂ) • (M k * (M k)ᴴ) := by rw [← hP]
      _ = ∑ k, (((d k)⁻¹ : ℝ) : ℂ) • (M k * (M k)ᴴ) := by
          rw [Matrix.mul_sum]
          simp_rw [Matrix.mul_smul, ← Matrix.mul_assoc, hPM]
      _ = P := hP.symm
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_sum]
    simp_rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_ofReal]
  obtain ⟨sk, hskd⟩ : ∃ sk : (Fin e → ZMod 2) → ℂ, ∀ k, sk k = ((Real.sqrt (d k)⁻¹ : ℝ) : ℂ) :=
    ⟨_, fun _ => rfl⟩
  have hsk : ∀ k, star (sk k) * sk k = (((d k)⁻¹ : ℝ) : ℂ) := by
    intro k
    rw [hskd, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (inv_nonneg.mpr (hd k))]
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ZMod 2 → (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
      ∀ t k, Rf t k = if t = 0 then sk k • (V * (M k)ᴴ) else if k = 0 then 1 - P else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hR : ∀ t k a, Rf t k * A a * V
      = (if t = 0 then sk k * (star (U a k) * d k) else 0) • V := by
    intro t k a
    rw [hRf]
    by_cases ht : t = 0
    · rw [if_pos ht, if_pos ht, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_assoc, hAV,
        Matrix.mul_sum]
      simp_rw [Matrix.mul_smul, hMM, smul_smul]
      rw [Finset.sum_eq_single k
        (fun l _ hl => by rw [if_neg (Ne.symm hl), mul_zero, zero_smul])
        (fun h => absurd (Finset.mem_univ k) h), if_pos rfl, Matrix.mul_smul, Matrix.mul_one,
        smul_smul]
    · rw [if_neg ht, if_neg ht, zero_smul]
      by_cases hk : k = 0
      · rw [if_pos hk, Matrix.mul_assoc, hAV, Matrix.mul_sum]
        refine Finset.sum_eq_zero (fun l _ => ?_)
        rw [Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul, hPM, sub_self, smul_zero]
      · rw [if_neg hk, Matrix.zero_mul, Matrix.zero_mul]
  have h0 : ∑ k, (Rf 0 k)ᴴ * Rf 0 k = P := by
    rw [hP]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hRf, if_pos rfl, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hsk, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  have h1 : ∑ k, (Rf 1 k)ᴴ * Rf 1 k = 1 - P := by
    simp_rw [hRf, if_neg (show (1 : ZMod 2) ≠ 0 by decide)]
    rw [Finset.sum_eq_single 0
      (fun k _ hk => by rw [if_neg hk, Matrix.conjTranspose_zero, Matrix.zero_mul])
      (fun h => absurd (Finset.mem_univ 0) h), if_pos rfl, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have hsum : ∑ r : Fin (e + 1) → ZMod 2, (Rf (r 0) (Fin.tail r))ᴴ * Rf (r 0) (Fin.tail r) = 1 := by
    rw [← (Fin.consEquiv fun _ => ZMod 2).sum_comp]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.tail_cons]
    rw [Fintype.sum_prod_type,
      show ∀ f : ZMod 2 → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ, ∑ t, f t = f 0 + f 1 from
        fun f => Fin.sum_univ_two f, h0, h1, add_sub_cancel]
  exact ⟨e + 1, fun r => Rf (r 0) (Fin.tail r),
    fun r a => if r 0 = 0 then sk (Fin.tail r) * (star (U a (Fin.tail r)) * d (Fin.tail r)) else 0,
    hsum, fun r a => hR _ _ a⟩

/-- **Sufficiency**: the Hermitian matrix of the blocks' scalars is diagonalised by a unitary
(Mathlib's spectral theorem), and `correctsErrors_of_diagonal` builds the recovery. -/
private theorem correctsErrors_of_scalar {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : Vᴴ * V = 1)
    (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (h : ∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
      ∀ a b, (A b * V)ᴴ * (A a * V) = C b a • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ)) :
    CorrectsErrors V A := by
  obtain ⟨C, hC⟩ := h
  have hH := isHermitian_of_scalar V A C hC
  have hU : (hH.eigenvectorUnitary : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ)
      * (hH.eigenvectorUnitary : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hD := hH.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at hD
  exact correctsErrors_of_diagonal V hV A C _ hC hU hH.eigenvalues hD

/-! ### The proofs' lemmas: the Gram condition on Pauli errors and stabilizer codes -/

/-- A sign is not zero. -/
private theorem signOf_ne_zero (a : ZMod 2) : signOf a ≠ 0 := by
  intro h
  have h1 := signOf_mul_self a
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

/-- **A block of two Pauli images**: `(P_q V)† (P_p V)` is a sign times `V† P_{p+q} V`. -/
private theorem pauli_blocks {ℓ : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (p q : Pauli n) :
    (pauliMatrix q * V)ᴴ * (pauliMatrix p * V)
      = (signOf (bitDot q.Z q.X) * signOf (bitDot q.Z p.X)) • (Vᴴ * pauliMatrix (p + q) * V) := by
  calc (pauliMatrix q * V)ᴴ * (pauliMatrix p * V)
      = Vᴴ * ((pauliMatrix q)ᴴ * pauliMatrix p) * V := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [conjTranspose_pauliMatrix, Matrix.smul_mul, pauliMatrix_mul, smul_smul, add_comm q p,
          Matrix.mul_smul, Matrix.smul_mul]

/-- **A Pauli is a scalar on a stabilizer code exactly in `S ∪ (Pauli n ∖ N(S))`.** On `S` it is
the code's sign. Off `N(S)` the compression `M = V† P V` has `tr(M M†) = B(P) = 0` (Gottesman's
count, `enumeratorTerm_counts`), so `M = 0`. On `N(S) ∖ S` a scalar `c` would have
`c 2^ℓ = tr(P Π) = 0`, so `M = 0` and `B(P) = 0`, against `B(P) = 2^ℓ`. -/
private theorem scalar_pauli_iff {ℓ : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : IsStabilizerEncoder S V)
    (Q : Pauli n) :
    (∃ c : ℂ, Vᴴ * pauliMatrix Q * V = c • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ)) ↔
      Q ∈ S ∨ Q ∉ normalizer S := by
  classical
  obtain ⟨_, _, _, hzero⟩ := exists_stabKraus S V hV
  have hB := (enumeratorTerm_counts S V hV hzero (quantum_macwilliams S V hV).2.1).2 Q
  have hBM : enumeratorTermB (codeProjector V) Q
      = trace ((Vᴴ * pauliMatrix Q * V) * (Vᴴ * pauliMatrix Q * V)ᴴ) := by
    unfold enumeratorTermB
    rw [conjTranspose_codeProjector]
    unfold codeProjector
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Vᴴ]
    simp only [Matrix.mul_assoc]
  have h2 : (2 : ℂ) ^ ℓ ≠ 0 := pow_ne_zero ℓ two_ne_zero
  constructor
  · rintro ⟨c, hc⟩
    by_contra hcon
    obtain ⟨hS, hN⟩ := not_or.mp hcon
    have hN' : Q ∈ normalizer S := not_not.mp hN
    have htr : trace (pauliMatrix Q * codeProjector V) = c * 2 ^ ℓ := by
      unfold codeProjector
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hc, Matrix.trace_smul,
        Matrix.trace_one, smul_eq_mul]
      simp [ZMod.card]
    have hc0 : c = 0 := by
      rw [hzero Q hS] at htr
      exact (mul_eq_zero.mp htr.symm).resolve_right h2
    rw [hBM, hc, hc0, zero_smul, Matrix.zero_mul, Matrix.trace_zero, if_pos hN'] at hB
    exact h2 hB.symm
  · rintro (hS | hN)
    · obtain ⟨c, hc⟩ := hV.2.2.2 Q hS
      exact ⟨c, by rw [Matrix.mul_assoc, hc, Matrix.mul_smul, hV.2.2.1]⟩
    · refine ⟨0, ?_⟩
      rw [zero_smul]
      have h0 : trace ((Vᴴ * pauliMatrix Q * V)ᴴᴴ * (Vᴴ * pauliMatrix Q * V)ᴴ) = 0 := by
        rw [Matrix.conjTranspose_conjTranspose, ← hBM, hB, if_neg hN]
      exact Matrix.conjTranspose_eq_zero.mp (eq_zero_of_trace_conjTranspose_mul_self _ h0)

-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   theorem:theorem:characterization1
-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   theorem:theorem:characterization3
-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 paragraph:eqn:char1
/-- **Knill–Laflamme as T27's Gram condition on the error images.** A code with encoder `V`
(orthonormal columns, any code, not only a stabilizer one) corrects the errors `A_a` exactly when
the Gram data over the read bits of `errorImages V A` (T27's `gram`, the physical qubits summed)
is `δ_{ij} C_{ba}` for one matrix `C`, at every pair of read words `(i, a)`, `(j, b)`. That is
Knill and Laflamme's characterization 1, `⟨i|A_a† A_b|j⟩ = C_{ab} δ_{ij}`, read as Gram data; and
it is the Gram data of the code's identity beside an environment vector `w_a` with Gram matrix `C`,
so by T27's purification it is their characterization 3, the errors acting as
`A_a |Ψ⟩ = σ(|Ψ⟩ ⊗ |E(a)⟩)`. Their statement takes the code with its recovery to be extended;
here the recovery is any trace-preserving Kraus family (`CorrectsErrors`), padded to a bit-string
index. Proved at T51.3.2. -/
theorem knillLaflamme_iff {ℓ e : ℕ} (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ)
    (hV : Vᴴ * V = 1) (A : (Fin e → ZMod 2) → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    CorrectsErrors V A ↔
      ∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
        ∀ (i j : Fin ℓ → ZMod 2) (a b : Fin e → ZMod 2),
          gram (errorImages V A) (Fin.append i a) (Fin.append j b)
            = if i = j then C b a else 0 := by
  rw [gram_condition_iff]
  exact ⟨scalar_of_correctsErrors V hV A, correctsErrors_of_scalar V hV A⟩

/-- **The stabilizer form of Knill–Laflamme, as the Gram condition's evaluation.** For a
stabilizer code of `S` with encoder `V` and Pauli errors `E_a` (as T50's real `X^a Z^b`), the Gram
condition of `knillLaflamme_iff` holds, and so the code corrects the errors, exactly when every
`E_a† E_b`, phase-free `E_a + E_b`, lies in `S` or outside `N(S)`:
`E_a + E_b ∈ S ∪ (Pauli n ∖ N(S))`. Degeneracy is included: two errors with `E_a + E_b ∈ S` act
alike on the code, and the condition admits them. Phase-free as Calderbank, Rains, Shor and
Sloane's Lemma 1; Gottesman's form with phases admits `−s` for `s ∈ S` as well, which the
phase-free `S` already contains. Proved at T51.3.2. -/
theorem knillLaflamme_stabilizer_iff {ℓ e : ℕ} (S : Submodule (ZMod 2) (Pauli n))
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℂ) (hV : IsStabilizerEncoder S V)
    (E : (Fin e → ZMod 2) → Pauli n) :
    ((∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
        ∀ (i j : Fin ℓ → ZMod 2) (a b : Fin e → ZMod 2),
          gram (errorImages V (fun a => pauliMatrix (E a))) (Fin.append i a) (Fin.append j b)
            = if i = j then C b a else 0) ↔
        ∀ a b, E a + E b ∈ S ∨ E a + E b ∉ normalizer S) ∧
      (CorrectsErrors V (fun a => pauliMatrix (E a)) ↔
        ∀ a b, E a + E b ∈ S ∨ E a + E b ∉ normalizer S) := by
  have hpair : ∀ a b, (∃ c : ℂ, (pauliMatrix (E b) * V)ᴴ * (pauliMatrix (E a) * V)
      = c • (1 : Matrix (Fin ℓ → ZMod 2) _ ℂ)) ↔ (E a + E b ∈ S ∨ E a + E b ∉ normalizer S) := by
    intro a b
    rw [← scalar_pauli_iff S V hV, pauli_blocks]
    have hu := mul_ne_zero (signOf_ne_zero (bitDot (E b).Z (E b).X))
      (signOf_ne_zero (bitDot (E b).Z (E a).X))
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(signOf (bitDot (E b).Z (E b).X) * signOf (bitDot (E b).Z (E a).X))⁻¹ * c, ?_⟩
      rw [← smul_smul, ← hc, smul_smul, inv_mul_cancel₀ hu, one_smul]
    · rintro ⟨c, hc⟩
      exact ⟨signOf (bitDot (E b).Z (E b).X) * signOf (bitDot (E b).Z (E a).X) * c,
        by rw [hc, smul_smul]⟩
  have h1 : (∃ C : Matrix (Fin e → ZMod 2) (Fin e → ZMod 2) ℂ,
        ∀ (i j : Fin ℓ → ZMod 2) (a b : Fin e → ZMod 2),
          gram (errorImages V (fun a => pauliMatrix (E a))) (Fin.append i a) (Fin.append j b)
            = if i = j then C b a else 0) ↔
        ∀ a b, E a + E b ∈ S ∨ E a + E b ∉ normalizer S := by
    rw [gram_condition_iff]
    constructor
    · rintro ⟨C, hC⟩ a b
      exact (hpair a b).mp ⟨C b a, hC a b⟩
    · intro h
      choose c hc using fun a b => (hpair a b).mpr (h a b)
      exact ⟨fun b a => c a b, fun a b => hc a b⟩
  exact ⟨h1, (knillLaflamme_iff V hV.2.2.1 _).trans h1⟩

/-! ## The Pauli twirl -/

-- source: papers/clifford_structure/
-- Dankert_Cleve_Emerson_Livine_2006_exact_approximate_unitary_2designs_quant-ph_0606161
--   equation:h15d1fa01322c
/-- **The Pauli twirl** of a map `Λ` on matrices of the data words:
`ρ ↦ 4^{−n} Σ_T T† Λ(T ρ T†) T`, the average over the `4^n` Paulis `T = X^a Z^b`. The source's
twirl `ρ ↦ ∫ dμ(U) U† Λ(U ρ U†) U` at the uniform distribution on the Pauli group; a unit phase on
`T` cancels against its dagger, so the phase-free `Pauli n` is the group averaged over. -/
noncomputable def pauliTwirl
    (Λ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  ((4 : ℂ) ^ n)⁻¹ • ∑ T : Pauli n, (pauliMatrix T)ᴴ * Λ (pauliMatrix T * ρ * (pauliMatrix T)ᴴ)
    * pauliMatrix T

/-! ### The proofs' lemmas: character orthogonality, and conjugation by a Pauli -/

/-- **Character orthogonality on `Pauli n`**: `Σ_T (−1)^{ω(T, c)}` is `4^n` at `c = 0` and `0`
otherwise, qubit by qubit from the one-qubit sum `coord_sum_sign`. -/
private theorem sum_signOf_omega_eq (c : Pauli n) :
    ∑ T : Pauli n, signOf (omega T c) = if c = 0 then (4 : ℂ) ^ n else 0 := by
  have hfac : ∀ x : Fin n → ZMod 2 × ZMod 2,
      signOf (omega (pauliCoordEquiv.symm x) c) = ∏ i, signOf (sympl1 (pauliCoord c i) (x i)) := by
    intro x
    rw [omega_comm, signOf_omega_prod]
    rfl
  rw [sum_pauli_coord]
  simp only [hfac]
  rw [← Fintype.prod_sum (fun i a => signOf (sympl1 (pauliCoord c i) a))]
  simp only [coord_sum_sign]
  by_cases hc : c = 0
  · have hcoord : ∀ i, pauliCoord c i = 0 := fun i => by
      rw [hc]
      rfl
    rw [if_pos hc]
    simp only [hcoord, if_true]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hc]
    obtain ⟨i, hi⟩ : ∃ i, pauliCoord c i ≠ 0 := by
      by_contra h
      push Not at h
      refine hc (Pauli.ext (funext fun i => ?_) (funext fun i => ?_))
      · exact congrArg Prod.fst (h i)
      · exact congrArg Prod.snd (h i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- `P + Q = 0` in `Pauli n` exactly when `P = Q`. -/
private theorem pauli_add_eq_zero_iff (P Q : Pauli n) : P + Q = 0 ↔ P = Q := by
  constructor
  · intro h
    calc P = P + (Q + Q) := by rw [pauli_add_self, add_zero]
      _ = (P + Q) + Q := by rw [add_assoc]
      _ = Q := by rw [h, zero_add]
  · rintro rfl
    exact pauli_add_self P

/-- **Conjugation by a Pauli is a sign**: `T† R T = (−1)^{ω(T, R)} R`. -/
private theorem conjTranspose_mul_pauliMatrix_mul (T R : Pauli n) :
    (pauliMatrix T)ᴴ * pauliMatrix R * pauliMatrix T = signOf (omega T R) • pauliMatrix R := by
  rw [conjTranspose_pauliMatrix, Matrix.smul_mul, Matrix.smul_mul, pauliMatrix_mul T R,
    Matrix.smul_mul, pauliMatrix_mul (T + R) T, smul_smul, smul_smul,
    show T + R + T = R by rw [add_comm T R, add_assoc, pauli_add_self, add_zero]]
  have hω : omega T R = bitDot T.Z R.X + bitDot R.Z T.X := by
    rw [bitDot_comm R.Z]
    rfl
  rw [hω, Z_add, bitDot_add_left, signOf_add, signOf_add]
  congr 1
  linear_combination (signOf (bitDot T.Z R.X) * signOf (bitDot R.Z T.X))
    * signOf_mul_self (bitDot T.Z T.X)

/-- **The other conjugation is the same sign**: `T R T† = (−1)^{ω(T, R)} R`, since `T† = ±T`. -/
private theorem pauliMatrix_mul_mul_conjTranspose (T R : Pauli n) :
    pauliMatrix T * pauliMatrix R * (pauliMatrix T)ᴴ = signOf (omega T R) • pauliMatrix R := by
  rw [← conjTranspose_mul_pauliMatrix_mul, conjTranspose_pauliMatrix, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul]

/-- A Pauli is unitary: `P† P = 1`. -/
private theorem conjTranspose_pauliMatrix_mul_self (Q : Pauli n) :
    (pauliMatrix Q)ᴴ * pauliMatrix Q = 1 := by
  rw [conjTranspose_pauliMatrix, Matrix.smul_mul, pauliMatrix_mul_self, smul_smul,
    signOf_mul_self, one_smul]

/-- **One term of the twirl**: `T† (P (T ρ T†) Q†) T = (−1)^{ω(T, P + Q)} P ρ Q†`. -/
private theorem twirl_term (T P Q : Pauli n) (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    (pauliMatrix T)ᴴ * (pauliMatrix P * (pauliMatrix T * ρ * (pauliMatrix T)ᴴ) * (pauliMatrix Q)ᴴ)
        * pauliMatrix T
      = signOf (omega T (P + Q)) • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ) := by
  have e : (pauliMatrix T)ᴴ
        * (pauliMatrix P * (pauliMatrix T * ρ * (pauliMatrix T)ᴴ) * (pauliMatrix Q)ᴴ)
        * pauliMatrix T
      = ((pauliMatrix T)ᴴ * pauliMatrix P * pauliMatrix T) * ρ
        * ((pauliMatrix T)ᴴ * pauliMatrix Q * pauliMatrix T)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, conjTranspose_mul_pauliMatrix_mul, conjTranspose_mul_pauliMatrix_mul,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_def, conj_signOf, omega_add_right, signOf_add]

/-- **The twirl of a χ sum** keeps the diagonal: character orthogonality multiplies `c(P, Q)` by
`δ_{P, Q}`. -/
private theorem pauliTwirl_chi_sum (c : Matrix (Pauli n) (Pauli n) ℂ) :
    pauliTwirl (fun ρ => ∑ P : Pauli n, ∑ Q : Pauli n,
        c P Q • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ))
      = fun ρ => ∑ P : Pauli n, c P P • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ) := by
  funext ρ
  unfold pauliTwirl
  simp only [Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, twirl_term]
  have hswap : ∑ T : Pauli n, ∑ P : Pauli n, ∑ Q : Pauli n,
        c P Q • signOf (omega T (P + Q)) • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ)
      = ∑ P : Pauli n, ∑ Q : Pauli n,
        (c P Q * ∑ T : Pauli n, signOf (omega T (P + Q)))
          • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Finset.mul_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl (fun T _ => by rw [smul_smul])
  rw [hswap, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.sum_eq_single P]
  · rw [sum_signOf_omega_eq, if_pos (pauli_add_self P), smul_smul]
    congr 1
    have hinv : ((4 : ℂ) ^ n)⁻¹ * (4 : ℂ) ^ n = 1 :=
      inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
    linear_combination c P P * hinv
  · intro Q _ hQ
    rw [sum_signOf_omega_eq, if_neg (fun h => hQ ((pauli_add_eq_zero_iff P Q).mp h).symm),
      mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ P) h

/-- **The transfer-matrix diagonal of a Pauli channel**:
`R(Q, Q) = Σ_P d(P)(−1)^{ω(P, Q)}` for `ρ ↦ Σ_P d(P) P ρ P†`. -/
private theorem ptm_diag_pauliChannel (d : Pauli n → ℂ) (Q : Pauli n) :
    ptm (fun ρ => ∑ P : Pauli n, d P • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ)) Q Q
      = ∑ P : Pauli n, d P * signOf (omega P Q) := by
  unfold ptm
  have htr : trace ((pauliMatrix Q)ᴴ * pauliMatrix Q) = (2 : ℂ) ^ n := by
    rw [conjTranspose_pauliMatrix_mul_self, ← pauliMatrix_zero, trace_pauliMatrix, if_pos rfl]
  have hterm : ∀ P : Pauli n,
      trace ((pauliMatrix Q)ᴴ * (d P • (pauliMatrix P * pauliMatrix Q * (pauliMatrix P)ᴴ)))
        = (2 : ℂ) ^ n * (d P * signOf (omega P Q)) := by
    intro P
    rw [pauliMatrix_mul_mul_conjTranspose, smul_smul, Matrix.mul_smul, Matrix.trace_smul, htr,
      smul_eq_mul]
    ring
  rw [Matrix.mul_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun P _ => hterm P),
    ← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]

/-- **The Pauli twirl as character orthogonality.** Three parts:

1. *Character orthogonality on `Pauli n`*: `Σ_T (−1)^{ω(T, c)} = 4^n δ_{c, 0}`, the characters of
   `𝔽₂^{2n}` being `T ↦ (−1)^{ω(T, c)}` since `ω` is nondegenerate.
2. *On χ*: the twirl of `ρ ↦ Σ_{P,Q} c(P, Q) P ρ Q†` is `ρ ↦ Σ_P c(P, P) P ρ P†`, for every
   matrix `c`, since `T† P T = (−1)^{ω(T, P)} P` multiplies `c(P, Q)` by `(−1)^{ω(T, P + Q)}`, which
   (1) sums to `4^n δ_{P, Q}`.
3. *On a protocol's branch* (T50, precision `m ≥ 1`, read string `o`): the twirl of the branch is
   the Pauli channel `ρ ↦ Σ_P χ_o(P, P) P ρ P†` with the branch's own χ diagonal, and its
   transfer-matrix diagonal is the branch's, `R(Q, Q)` unchanged.

That is all it states: the twirl keeps χ's diagonal and removes the rest. Nothing is stated about
the original channel's distance from its twirl. Dankert, Cleve, Emerson and Livine compute it with
the symplectic character sum (the fidelity note's Claim 11, a display that is not a corpus unit).
Proved at T51.3.3. -/
theorem pauli_twirl {m k r u : ℕ} (p : Protocol m n k) (σ : Fin k ≃ Fin (r + u)) (hm : 1 ≤ m)
    (o : Fin r → ZMod 2) :
    (∀ c : Pauli n,
      ∑ T : Pauli n, signOf (omega T c) = if c = 0 then (4 : ℂ) ^ n else 0) ∧
    (∀ c : Matrix (Pauli n) (Pauli n) ℂ,
      pauliTwirl (fun ρ => ∑ P : Pauli n, ∑ Q : Pauli n,
          c P Q • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ))
        = fun ρ => ∑ P : Pauli n, c P P • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ)) ∧
    pauliTwirl (channelBranch p σ o)
        = (fun ρ => ∑ P : Pauli n, chi p σ o P P • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ)) ∧
      IsPauliChannel (pauliTwirl (channelBranch p σ o)) ∧
      ∀ Q : Pauli n,
        ptm (pauliTwirl (channelBranch p σ o)) Q Q = ptm (channelBranch p σ o) Q Q := by
  have hbr : channelBranch p σ o = fun ρ => ∑ P : Pauli n, ∑ Q : Pauli n,
      chi p σ o P Q • (pauliMatrix P * ρ * (pauliMatrix Q)ᴴ) :=
    funext fun ρ => (channel_eq_chi_sum p σ hm o).2 ρ
  have htw : pauliTwirl (channelBranch p σ o)
      = fun ρ => ∑ P : Pauli n, chi p σ o P P • (pauliMatrix P * ρ * (pauliMatrix P)ᴴ) := by
    rw [hbr]
    exact pauliTwirl_chi_sum (chi p σ o)
  refine ⟨sum_signOf_omega_eq, pauliTwirl_chi_sum, htw,
    ⟨fun P => chi p σ o P P, fun ρ => by rw [htw]⟩, fun Q => ?_⟩
  rw [htw, ptm_diag_pauliChannel, (ptm_diag_eq_walsh_chi_diag p σ hm o Q).2]

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.DoublingCorollaries

/-!
# Check: T51, corollaries of the doubling

T51.2's witness rows (`docs/STEPS.md`) on the frozen statement of `DoublingCorollaries.lean`.
Every T51 headline (`quantum_macwilliams`, `knillLaflamme_iff`, `knillLaflamme_stabilizer_iff`,
`pauli_twirl`) is `sorry`'d when these rows are written, and no row uses one. Each row is about an
object a headline names, computed from the definitions, and compared with an existing object.

The route. Every operator in the rows has integer entries, or is a real scalar times an integer
matrix: the real Pauli `X^a Z^b` (`pauliMatrix`) is the cast of `pauliInt`, the repetition code's
encoder is a `0/1` matrix, and the Bell code's is `1/√2` times one. Traces, products and Gram sums
of casts are casts of the integer computation (`pauliMatrix_eq_map`, `enumeratorTermA_smul_map`,
`gram_errorImages_map`), which the kernel then evaluates by `decide` over the `4^n` Paulis. The
existing objects are the stabilizer group `S`, its normalizer `normalizer S`
(`FTQCLib/Stabilizer/Normalizer.lean`) and `weight` (`FTQCLib/Stabilizer/Error.lean`), counted by
`decide` through the membership test of each one's own definition.

The rows:

* **The Bell code's enumerators (agreement).** The `[[2,0]]` code of `⟨XX, ZZ⟩`, encoder
  `(∣00⟩ + ∣11⟩)/√2`: `A_j` (`weightEnumeratorA` of `codeProjector`) is `4^0` times the number of
  elements of `S` of weight `j`, and `B_j` is `2^0` times that of `N(S)`, at every `j`;
  `A = B = (1, 0, 3)`, the code being self-dual.
* **The repetition code's enumerators (agreement).** The `[[3,1]]` code of `⟨Z₀Z₁, Z₁Z₂⟩`,
  encoder `∣i⟩ ↦ ∣iii⟩`: `A_j = 4 |S_j|` and `B_j = 2 |N(S)_j|` at every `j`;
  `A = (4, 0, 12, 0)`, `B = (2, 6, 6, 18)`.
* **Knill–Laflamme on the bit-flip code, single flips (agreement).** Against `{I, X₀, X₁, X₂}` the
  Gram data of the error images (`gram` of `errorImages`) is `δ_{ij} C_{ba}` with `C = 1`, and
  every `E_a + E_b` lies in `S` or outside `N(S)`: the two sides of the stabilizer criterion agree.
* **Knill–Laflamme with `X₀X₁` (discriminating).** Against `{X₀X₁, X₀, X₁, X₂}` the Gram data is
  `1` at the two different codewords, errors `X₀X₁` and `X₂`, so no `C` gives `δ_{ij} C_{ba}`; and
  `X₀X₁ + X₂ = X₀X₁X₂`, the logical X, lies in `N(S)` but not in `S`. The step's text says
  "against `{X₀X₁}`"; read literally, the one error `X₀X₁` is corrected (every `E_a + E_a = 0`
  lies in `S`), so the row adds `X₀X₁` to the single flips, the nearest set at which the
  criterion fails (inference, recorded in the step's report).
* **The twirl of the `Z₀Z₁` conditioning (agreement).** The step's "CZ-conditioning" is read as
  conditioning on `Z₀Z₁` with the outcome unread (the correction of 2026-10-02 calls it an unread
  conditioning on a Pauli; inference). Its branch, from T49's `channel`, is
  `ρ ↦ ½ρ + ½ Z₀Z₁ ρ Z₀Z₁†`; its Pauli twirl (`pauliTwirl`), from the definition and the
  conjugation `T† Z₀Z₁ T = ±Z₀Z₁` computed at each of the sixteen `T`, is the branch itself, and
  a Pauli channel.
* **A stabilizer encoder is inhabited (inhabitation, T51.4).** `quantum_macwilliams`'s hypothesis
  `IsStabilizerEncoder S V` holds together at the trivial witness `S = ⊥`, `V = 1`, one qubit,
  `ℓ = 1`: `IsStabilizer ⊥` holds vacuously, `1 + finrank ⊥ = 1` since `finrank ⊥ = 0`, `1ᴴ 1 = 1`,
  and the only `s ∈ ⊥` is `0`, on which `pauliMatrix 0 = 1` acts as the scalar `1`.

Scope (standard 7.3): the enumerator rows are about these two codes and every weight; the
Knill–Laflamme rows about the repetition code and the two error sets named; the twirl row about
one protocol on two data bits; the inhabitation
row is about the one trivial witness named. Nothing is concluded about other codes, error sets,
channels or witnesses.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Matrix

variable {n : ℕ}

/-! ## Integer shadows -/

/-- The real Pauli `X^a Z^b` with integer entries. -/
private def pauliInt (P : Pauli n) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℤ :=
  fun w x => if w = x + P.X then (-1 : ℤ) ^ zDot P x else 0

/-- `pauliMatrix` is the cast of `pauliInt`. -/
private theorem pauliMatrix_eq_map (P : Pauli n) :
    pauliMatrix P = (pauliInt P).map (Int.cast : ℤ → ℂ) := by
  ext w x
  simp only [pauliMatrix, pauliInt, Matrix.map_apply]
  split_ifs <;> push_cast <;> rfl

/-- The conjugate transpose of a cast is the cast of the transpose. -/
private theorem conjTranspose_map_intCast {α β : Type*} (M : Matrix α β ℤ) :
    (M.map (Int.cast : ℤ → ℂ))ᴴ = Mᵀ.map (Int.cast : ℤ → ℂ) := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]

/-- The cast of a product is the product of the casts. -/
private theorem map_mul_intCast {α β γ : Type*} [Fintype β] (M : Matrix α β ℤ)
    (N : Matrix β γ ℤ) :
    (M * N).map (Int.cast : ℤ → ℂ) = M.map (Int.cast : ℤ → ℂ) * N.map (Int.cast : ℤ → ℂ) :=
  Matrix.map_mul (f := Int.castRingHom ℂ)

/-- The trace of a cast is the cast of the trace. -/
private theorem trace_map_intCast {α : Type*} [Fintype α] (M : Matrix α α ℤ) :
    trace (M.map (Int.cast : ℤ → ℂ)) = ((trace M : ℤ) : ℂ) := by
  simp [Matrix.trace, Matrix.diag, Matrix.map_apply]

/-- The `A` summand of a real multiple of an integer matrix. -/
private theorem enumeratorTermA_smul_map (c : ℝ)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℤ) (P : Pauli n) :
    enumeratorTermA ((c : ℂ) • M.map (Int.cast : ℤ → ℂ)) P
      = ((c ^ 2 : ℝ) : ℂ) * (((trace (pauliInt P * M)) ^ 2 : ℤ) : ℂ) := by
  unfold enumeratorTermA
  rw [Matrix.mul_smul, trace_smul, pauliMatrix_eq_map, ← map_mul_intCast, trace_map_intCast]
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, map_intCast]
  push_cast
  ring

/-- The `B` summand of a real multiple of an integer matrix. -/
private theorem enumeratorTermB_smul_map (c : ℝ)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℤ) (P : Pauli n) :
    enumeratorTermB ((c : ℂ) • M.map (Int.cast : ℤ → ℂ)) P
      = ((c ^ 2 : ℝ) : ℂ) * ((trace (pauliInt P * M * (pauliInt P)ᵀ * Mᵀ) : ℤ) : ℂ) := by
  unfold enumeratorTermB
  rw [conjTranspose_smul, conjTranspose_map_intCast, pauliMatrix_eq_map,
    conjTranspose_map_intCast]
  simp only [Matrix.mul_smul, Matrix.smul_mul, trace_smul, ← map_mul_intCast, trace_map_intCast,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- The projector of a real multiple of an integer encoder. -/
private theorem codeProjector_smul_map {ℓ : ℕ} (s : ℝ)
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℤ) :
    codeProjector ((s : ℂ) • V.map (Int.cast : ℤ → ℂ))
      = ((s ^ 2 : ℝ) : ℂ) • (V * Vᵀ).map (Int.cast : ℤ → ℂ) := by
  unfold codeProjector
  rw [conjTranspose_smul, conjTranspose_map_intCast, map_mul_intCast, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- The enumerator `A` of a real multiple of an integer matrix. -/
private theorem weightEnumeratorA_smul_map (c : ℝ)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℤ) (d : ℕ) :
    weightEnumeratorA ((c : ℂ) • M.map (Int.cast : ℤ → ℂ)) d
      = ((c ^ 2 : ℝ) : ℂ) * ((∑ P ∈ Finset.univ.filter (fun P : Pauli n => weight P = d),
          (trace (pauliInt P * M)) ^ 2 : ℤ) : ℂ) := by
  unfold weightEnumeratorA
  simp only [enumeratorTermA_smul_map, Int.cast_sum, Finset.mul_sum]

/-- The enumerator `B` of a real multiple of an integer matrix. -/
private theorem weightEnumeratorB_smul_map (c : ℝ)
    (M : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℤ) (d : ℕ) :
    weightEnumeratorB ((c : ℂ) • M.map (Int.cast : ℤ → ℂ)) d
      = ((c ^ 2 : ℝ) : ℂ) * ((∑ P ∈ Finset.univ.filter (fun P : Pauli n => weight P = d),
          trace (pauliInt P * M * (pauliInt P)ᵀ * Mᵀ) : ℤ) : ℂ) := by
  unfold weightEnumeratorB
  simp only [enumeratorTermB_smul_map, Int.cast_sum, Finset.mul_sum]

/-- No Pauli on `n` qubits has weight above `n`. -/
private theorem filter_weight_eq_empty {d : ℕ} (hd : n < d) (p : Pauli n → Prop)
    [DecidablePred p] :
    Finset.univ.filter (fun P : Pauli n => p P ∧ weight P = d) = ∅ := by
  refine Finset.filter_false_of_mem (fun P _ h => ?_)
  exact absurd (h.2 ▸ weight_le_n P) (not_le.mpr hd)

/-- No Pauli on `n` qubits has weight above `n`, without a side condition. -/
private theorem filter_weight_eq_empty_of_lt {d : ℕ} (hd : n < d) :
    Finset.univ.filter (fun P : Pauli n => weight P = d) = ∅ := by
  refine Finset.filter_false_of_mem (fun P _ h => ?_)
  exact absurd (h ▸ weight_le_n P) (not_le.mpr hd)

/-- A count of Paulis by weight as the card of a filter. -/
private theorem natCard_weight (S : Pauli n → Prop) [DecidablePred S] (d : ℕ) :
    Nat.card {P : Pauli n // S P ∧ weight P = d}
      = (Finset.univ.filter (fun P : Pauli n => S P ∧ weight P = d)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ## The weight enumerators -/

/-- The Bell code's stabilizer `⟨XX, ZZ⟩`. -/
def bellStabilizer : Submodule (ZMod 2) (Pauli 2) where
  carrier := {P | P.X 0 = P.X 1 ∧ P.Z 0 = P.Z 1}
  add_mem' := fun {P Q} hP hQ => by
    simp only [Set.mem_setOf_eq, Pauli.X_add, Pauli.Z_add, Pi.add_apply] at *
    rw [hP.1, hP.2, hQ.1, hQ.2]
    exact ⟨rfl, rfl⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c {P} hP => by
    simp only [Set.mem_setOf_eq, Pauli.X_smul, Pauli.Z_smul, Pi.smul_apply] at *
    rw [hP.1, hP.2]
    exact ⟨rfl, rfl⟩

/-- Membership in `bellStabilizer`, by its definition. -/
private instance : DecidablePred (· ∈ bellStabilizer) :=
  fun P => decidable_of_iff (P.X 0 = P.X 1 ∧ P.Z 0 = P.Z 1) Iff.rfl

/-- Membership in the Bell code's normalizer, by `normalizer`'s definition. -/
private instance : DecidablePred (· ∈ normalizer bellStabilizer) :=
  fun P => decidable_of_iff (∀ q : Pauli 2, q ∈ bellStabilizer → omega P q = 0)
    ⟨fun h q hq => h q hq, fun h q hq => h q hq⟩

/-- `∣00⟩ + ∣11⟩` as an integer column. -/
private def bellEncoderInt : Matrix (Fin 2 → ZMod 2) (Fin 0 → ZMod 2) ℤ :=
  fun w _ => if w 0 = w 1 then 1 else 0

/-- The Bell code's encoder, `(∣00⟩ + ∣11⟩)/√2`, no logical qubit. -/
noncomputable def bellEncoder : Matrix (Fin 2 → ZMod 2) (Fin 0 → ZMod 2) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • bellEncoderInt.map (Int.cast : ℤ → ℂ)

/-- `(1/√2)² = ½`. -/
private theorem bell_scale : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 2⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]

/-- The Bell code's `A` summands, summed by weight, in integers, against the count of `S`. -/
private theorem bell_countA (j : ℕ) :
    (∑ P ∈ Finset.univ.filter (fun P : Pauli 2 => weight P = j),
        (trace (pauliInt P * (bellEncoderInt * bellEncoderIntᵀ))) ^ 2 : ℤ)
      = 4 * (Finset.univ.filter (fun P : Pauli 2 => P ∈ bellStabilizer ∧ weight P = j)).card := by
  rcases lt_or_ge 2 j with h | h
  · rw [filter_weight_eq_empty_of_lt h, filter_weight_eq_empty h]
    rfl
  · interval_cases j <;> decide

/-- The Bell code's `B` summands, summed by weight, in integers, against the count of `N(S)`. -/
private theorem bell_countB (j : ℕ) :
    (∑ P ∈ Finset.univ.filter (fun P : Pauli 2 => weight P = j),
        trace (pauliInt P * (bellEncoderInt * bellEncoderIntᵀ) * (pauliInt P)ᵀ
          * (bellEncoderInt * bellEncoderIntᵀ)ᵀ) : ℤ)
      = 4 * (Finset.univ.filter
          (fun P : Pauli 2 => P ∈ normalizer bellStabilizer ∧ weight P = j)).card := by
  rcases lt_or_ge 2 j with h | h
  · rw [filter_weight_eq_empty_of_lt h, filter_weight_eq_empty h]
    rfl
  · interval_cases j <;> decide

/-- The Bell code's `A_j` against the count of `S`. -/
private theorem bell_enumeratorA (j : ℕ) : weightEnumeratorA (codeProjector bellEncoder) j
    = ((4 ^ 0 * Nat.card {P : Pauli 2 // P ∈ bellStabilizer ∧ weight P = j} : ℕ) : ℂ) := by
  rw [bellEncoder, codeProjector_smul_map, bell_scale, weightEnumeratorA_smul_map, natCard_weight,
    bell_countA]
  push_cast
  ring

/-- The Bell code's `B_j` against the count of `N(S)`. -/
private theorem bell_enumeratorB (j : ℕ) : weightEnumeratorB (codeProjector bellEncoder) j
    = ((2 ^ 0 * Nat.card {P : Pauli 2 // P ∈ normalizer bellStabilizer ∧ weight P = j} : ℕ)
      : ℂ) := by
  rw [bellEncoder, codeProjector_smul_map, bell_scale, weightEnumeratorB_smul_map, natCard_weight,
    bell_countB]
  push_cast
  ring

-- source: papers/quantum_codes/
-- Shor_Laflamme_1996_quantum_analog_macwilliams_identities_quant-ph_9610040 paragraph:hf92cc7bfdf3f
-- row: agreement
/-- **The Bell code's enumerators.** For the `[[2,0]]` code of `⟨XX, ZZ⟩` with encoder
`(∣00⟩ + ∣11⟩)/√2`, `A_j = 4^0 |S_j|` and `B_j = 2^0 |N(S)_j|` at every weight `j`, the enumerators
computed from their traces and the counts from `S`, `normalizer` and `weight`; and
`A = B = (1, 0, 3)`. -/
theorem row_bell_enumerators :
    (∀ j : ℕ, weightEnumeratorA (codeProjector bellEncoder) j
        = ((4 ^ 0 * Nat.card {P : Pauli 2 // P ∈ bellStabilizer ∧ weight P = j} : ℕ) : ℂ)) ∧
    (∀ j : ℕ, weightEnumeratorB (codeProjector bellEncoder) j
        = ((2 ^ 0 * Nat.card {P : Pauli 2 // P ∈ normalizer bellStabilizer ∧ weight P = j} : ℕ)
          : ℂ)) ∧
    ![weightEnumeratorA (codeProjector bellEncoder) 0,
        weightEnumeratorA (codeProjector bellEncoder) 1,
        weightEnumeratorA (codeProjector bellEncoder) 2] = ![1, 0, 3] ∧
    ![weightEnumeratorB (codeProjector bellEncoder) 0,
        weightEnumeratorB (codeProjector bellEncoder) 1,
        weightEnumeratorB (codeProjector bellEncoder) 2] = ![1, 0, 3] := by
  refine ⟨bell_enumeratorA, bell_enumeratorB, ?_, ?_⟩
  · have h0 : (Finset.univ.filter
        (fun P : Pauli 2 => P ∈ bellStabilizer ∧ weight P = 0)).card = 1 := by decide
    have h1 : (Finset.univ.filter
        (fun P : Pauli 2 => P ∈ bellStabilizer ∧ weight P = 1)).card = 0 := by decide
    have h2 : (Finset.univ.filter
        (fun P : Pauli 2 => P ∈ bellStabilizer ∧ weight P = 2)).card = 3 := by decide
    simp only [bell_enumeratorA, natCard_weight, h0, h1, h2]
    norm_num
  · have h0 : (Finset.univ.filter
        (fun P : Pauli 2 => P ∈ normalizer bellStabilizer ∧ weight P = 0)).card = 1 := by decide
    have h1 : (Finset.univ.filter
        (fun P : Pauli 2 => P ∈ normalizer bellStabilizer ∧ weight P = 1)).card = 0 := by decide
    have h2 : (Finset.univ.filter
        (fun P : Pauli 2 => P ∈ normalizer bellStabilizer ∧ weight P = 2)).card = 3 := by decide
    simp only [bell_enumeratorB, natCard_weight, h0, h1, h2]
    norm_num

/-- The repetition code's stabilizer `⟨Z₀Z₁, Z₁Z₂⟩`. -/
def repStabilizer : Submodule (ZMod 2) (Pauli 3) where
  carrier := {P | P.X = 0 ∧ P.Z 0 + P.Z 1 + P.Z 2 = 0}
  add_mem' := fun {P Q} hP hQ => by
    simp only [Set.mem_setOf_eq, Pauli.X_add, Pauli.Z_add, Pi.add_apply] at *
    refine ⟨by rw [hP.1, hQ.1, add_zero], ?_⟩
    linear_combination hP.2 + hQ.2
  zero_mem' := ⟨rfl, by decide⟩
  smul_mem' := fun c {P} hP => by
    simp only [Set.mem_setOf_eq, Pauli.X_smul, Pauli.Z_smul, Pi.smul_apply, smul_eq_mul] at *
    refine ⟨by rw [hP.1, smul_zero], ?_⟩
    linear_combination c * hP.2

/-- Membership in `repStabilizer`, by its definition. -/
private instance : DecidablePred (· ∈ repStabilizer) :=
  fun P => decidable_of_iff (P.X = 0 ∧ P.Z 0 + P.Z 1 + P.Z 2 = 0) Iff.rfl

/-- Membership in the repetition code's normalizer, by `normalizer`'s definition. -/
private instance : DecidablePred (· ∈ normalizer repStabilizer) :=
  fun P => decidable_of_iff (∀ q : Pauli 3, q ∈ repStabilizer → omega P q = 0)
    ⟨fun h q hq => h q hq, fun h q hq => h q hq⟩

/-- `∣i⟩ ↦ ∣iii⟩` as an integer matrix. -/
private def repEncoderInt : Matrix (Fin 3 → ZMod 2) (Fin 1 → ZMod 2) ℤ :=
  fun w i => if w = fun _ => i 0 then 1 else 0

/-- The repetition code's encoder, `∣i⟩ ↦ ∣iii⟩`. -/
noncomputable def repEncoder : Matrix (Fin 3 → ZMod 2) (Fin 1 → ZMod 2) ℂ :=
  repEncoderInt.map (Int.cast : ℤ → ℂ)

/-- The repetition code's encoder as `1` times its integer matrix. -/
private theorem repEncoder_eq :
    repEncoder = ((1 : ℝ) : ℂ) • repEncoderInt.map (Int.cast : ℤ → ℂ) := by
  rw [Complex.ofReal_one, one_smul]
  rfl

/-- The repetition code's `A` summands, summed by weight, against the count of `S`. -/
private theorem rep_countA (j : ℕ) :
    (∑ P ∈ Finset.univ.filter (fun P : Pauli 3 => weight P = j),
        (trace (pauliInt P * (repEncoderInt * repEncoderIntᵀ))) ^ 2 : ℤ)
      = 4 * (Finset.univ.filter (fun P : Pauli 3 => P ∈ repStabilizer ∧ weight P = j)).card := by
  rcases lt_or_ge 3 j with h | h
  · rw [filter_weight_eq_empty_of_lt h, filter_weight_eq_empty h]
    rfl
  · interval_cases j <;> decide

/-- `tr(P Π P† Π)` for `Π = V Vᵀ` as a trace over the code, `tr(Vᵀ P V Vᵀ P† V)`. -/
private theorem trace_cycle_codeProjector {ℓ : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℤ) (P : Pauli n) :
    trace (pauliInt P * (V * Vᵀ) * (pauliInt P)ᵀ * (V * Vᵀ)ᵀ)
      = trace (Vᵀ * pauliInt P * V * (Vᵀ * (pauliInt P)ᵀ * V)) := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose,
    show pauliInt P * (V * Vᵀ) * (pauliInt P)ᵀ * (V * Vᵀ)
      = (pauliInt P * V * Vᵀ * (pauliInt P)ᵀ * V) * Vᵀ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The repetition code's `B` summands, summed by weight, against the count of `N(S)`. -/
private theorem rep_countB (j : ℕ) :
    (∑ P ∈ Finset.univ.filter (fun P : Pauli 3 => weight P = j),
        trace (pauliInt P * (repEncoderInt * repEncoderIntᵀ) * (pauliInt P)ᵀ
          * (repEncoderInt * repEncoderIntᵀ)ᵀ) : ℤ)
      = 2 * (Finset.univ.filter
          (fun P : Pauli 3 => P ∈ normalizer repStabilizer ∧ weight P = j)).card := by
  simp only [trace_cycle_codeProjector]
  rcases lt_or_ge 3 j with h | h
  · rw [filter_weight_eq_empty_of_lt h, filter_weight_eq_empty h]
    rfl
  · interval_cases j <;> decide

/-- The repetition code's `A_j` against the count of `S`. -/
private theorem rep_enumeratorA (j : ℕ) : weightEnumeratorA (codeProjector repEncoder) j
    = ((4 ^ 1 * Nat.card {P : Pauli 3 // P ∈ repStabilizer ∧ weight P = j} : ℕ) : ℂ) := by
  rw [repEncoder_eq, codeProjector_smul_map, weightEnumeratorA_smul_map, natCard_weight,
    rep_countA]
  push_cast
  ring

/-- The repetition code's `B_j` against the count of `N(S)`. -/
private theorem rep_enumeratorB (j : ℕ) : weightEnumeratorB (codeProjector repEncoder) j
    = ((2 ^ 1 * Nat.card {P : Pauli 3 // P ∈ normalizer repStabilizer ∧ weight P = j} : ℕ)
      : ℂ) := by
  rw [repEncoder_eq, codeProjector_smul_map, weightEnumeratorB_smul_map, natCard_weight,
    rep_countB]
  push_cast
  ring

-- source: papers/quantum_codes/
-- Rains_1996_quantum_weight_enumerators_quant-ph_9612015 equation:hda1c25245f9d
-- row: agreement
/-- **The repetition code's enumerators.** For the `[[3,1]]` code of `⟨Z₀Z₁, Z₁Z₂⟩` with encoder
`∣i⟩ ↦ ∣iii⟩`, `A_j = 4 |S_j|` and `B_j = 2 |N(S)_j|` at every weight `j`; and
`A = (4, 0, 12, 0)`, `B = (2, 6, 6, 18)`, `N(S)` being the eight Z strings and `X₀X₁X₂` times
them. -/
theorem row_rep_enumerators :
    (∀ j : ℕ, weightEnumeratorA (codeProjector repEncoder) j
        = ((4 ^ 1 * Nat.card {P : Pauli 3 // P ∈ repStabilizer ∧ weight P = j} : ℕ) : ℂ)) ∧
    (∀ j : ℕ, weightEnumeratorB (codeProjector repEncoder) j
        = ((2 ^ 1 * Nat.card {P : Pauli 3 // P ∈ normalizer repStabilizer ∧ weight P = j} : ℕ)
          : ℂ)) ∧
    ![weightEnumeratorA (codeProjector repEncoder) 0,
        weightEnumeratorA (codeProjector repEncoder) 1,
        weightEnumeratorA (codeProjector repEncoder) 2,
        weightEnumeratorA (codeProjector repEncoder) 3] = ![4, 0, 12, 0] ∧
    ![weightEnumeratorB (codeProjector repEncoder) 0,
        weightEnumeratorB (codeProjector repEncoder) 1,
        weightEnumeratorB (codeProjector repEncoder) 2,
        weightEnumeratorB (codeProjector repEncoder) 3] = ![2, 6, 6, 18] := by
  refine ⟨rep_enumeratorA, rep_enumeratorB, ?_, ?_⟩
  · have h0 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ repStabilizer ∧ weight P = 0)).card = 1 := by decide
    have h1 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ repStabilizer ∧ weight P = 1)).card = 0 := by decide
    have h2 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ repStabilizer ∧ weight P = 2)).card = 3 := by decide
    have h3 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ repStabilizer ∧ weight P = 3)).card = 0 := by decide
    simp only [rep_enumeratorA, natCard_weight, h0, h1, h2, h3]
    norm_num
  · have h0 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ normalizer repStabilizer ∧ weight P = 0)).card = 1 := by decide
    have h1 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ normalizer repStabilizer ∧ weight P = 1)).card = 3 := by decide
    have h2 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ normalizer repStabilizer ∧ weight P = 2)).card = 3 := by decide
    have h3 : (Finset.univ.filter
        (fun P : Pauli 3 => P ∈ normalizer repStabilizer ∧ weight P = 3)).card = 9 := by decide
    simp only [rep_enumeratorB, natCard_weight, h0, h1, h2, h3]
    norm_num

/-! ## Knill–Laflamme -/

/-- The Gram data of the error images of Pauli errors on an integer encoder, in integers:
`⟨E_b V_j, E_a V_i⟩`. -/
private theorem gram_errorImages_map {ℓ e : ℕ}
    (V : Matrix (Fin n → ZMod 2) (Fin ℓ → ZMod 2) ℤ) (E : (Fin e → ZMod 2) → Pauli n)
    (i j : Fin ℓ → ZMod 2) (a b : Fin e → ZMod 2) :
    gram (errorImages (V.map (Int.cast : ℤ → ℂ)) (fun a => pauliMatrix (E a)))
        (Fin.append i a) (Fin.append j b)
      = ((∑ u, (pauliInt (E a) * V) u i * (pauliInt (E b) * V) u j : ℤ) : ℂ) := by
  unfold gram errorImages
  simp only [Fin.append_left, Fin.append_right, pauliMatrix_eq_map, ← map_mul_intCast,
    Matrix.map_apply, map_intCast, Int.cast_sum, Int.cast_mul]

/-- The single bit flips with no error: `I, X₀, X₁, X₂` at `00, 10, 01, 11`. -/
def singleFlips (a : Fin 2 → ZMod 2) : Pauli 3 :=
  ⟨![a 0 * (1 - a 1), (1 - a 0) * a 1, a 0 * a 1], 0⟩

/-- The single bit flips with `X₀X₁` in place of no error: `X₀X₁, X₀, X₁, X₂`. -/
def flipsWithPair (a : Fin 2 → ZMod 2) : Pauli 3 :=
  ⟨![1 - a 1, 1 - a 0, a 0 * a 1], 0⟩

-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   theorem:theorem:characterization1
-- row: agreement
/-- **Knill–Laflamme on the bit-flip code, single flips.** The repetition code's encoder has
orthonormal columns, the Gram data of its error images under `{I, X₀, X₁, X₂}` is `δ_{ij} C_{ba}`
with `C = 1`, and every `E_a + E_b` lies in `S` or outside `N(S)`: the Gram condition and the
stabilizer criterion agree. -/
theorem row_kl_singleFlips :
    repEncoderᴴ * repEncoder = 1 ∧
    (∃ C : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ,
      ∀ (i j : Fin 1 → ZMod 2) (a b : Fin 2 → ZMod 2),
        gram (errorImages repEncoder (fun a => pauliMatrix (singleFlips a)))
            (Fin.append i a) (Fin.append j b)
          = if i = j then C b a else 0) ∧
    ∀ a b, singleFlips a + singleFlips b ∈ repStabilizer ∨
      singleFlips a + singleFlips b ∉ normalizer repStabilizer := by
  refine ⟨?_, ⟨1, fun i j a b => ?_⟩, by decide⟩
  · rw [repEncoder, conjTranspose_map_intCast, ← map_mul_intCast,
      show repEncoderIntᵀ * repEncoderInt = 1 by decide,
      Matrix.map_one _ Int.cast_zero Int.cast_one]
  · have h : ∀ (i j : Fin 1 → ZMod 2) (a b : Fin 2 → ZMod 2),
        (∑ u, (pauliInt (singleFlips a) * repEncoderInt) u i
          * (pauliInt (singleFlips b) * repEncoderInt) u j : ℤ)
          = if i = j then (if b = a then 1 else 0) else 0 := by decide
    rw [repEncoder, gram_errorImages_map, h, Matrix.one_apply]
    split_ifs <;> simp

-- source: papers/quantum_codes/
-- Knill_Laflamme_1996_theory_quantum_error_correcting_codes_quant-ph_9604034
--   theorem:theorem:characterization1
-- row: discriminating
/-- **Knill–Laflamme with `X₀X₁`.** Under `{X₀X₁, X₀, X₁, X₂}` the Gram data at the codewords
`0`, `1` and the errors `X₀X₁`, `X₂` is `1`, not `0`, so no `C` gives `δ_{ij} C_{ba}`; and
`X₀X₁ + X₂` lies in `N(S)` and not in `S`, the stabilizer criterion failing at the same pair. -/
theorem row_kl_flipsWithPair :
    (¬ ∃ C : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ,
      ∀ (i j : Fin 1 → ZMod 2) (a b : Fin 2 → ZMod 2),
        gram (errorImages repEncoder (fun a => pauliMatrix (flipsWithPair a)))
            (Fin.append i a) (Fin.append j b)
          = if i = j then C b a else 0) ∧
    flipsWithPair ![0, 0] + flipsWithPair ![1, 1] ∉ repStabilizer ∧
    flipsWithPair ![0, 0] + flipsWithPair ![1, 1] ∈ normalizer repStabilizer := by
  refine ⟨fun ⟨C, hC⟩ => ?_, by decide, by decide⟩
  have h := hC ![0] ![1] ![0, 0] ![1, 1]
  have hval : (∑ u, (pauliInt (flipsWithPair ![0, 0]) * repEncoderInt) u ![0]
      * (pauliInt (flipsWithPair ![1, 1]) * repEncoderInt) u ![1] : ℤ) = 1 := by decide
  rw [repEncoder, gram_errorImages_map, hval, if_neg (by decide)] at h
  simp at h

/-! ## The Pauli twirl -/

/-- `Z₀Z₁`. -/
def zzPauli : Pauli 2 := ⟨0, ![1, 1]⟩

/-- Conditioning on `Z₀Z₁`. -/
noncomputable def czCondition : Protocol 1 2 1 :=
  Protocol.nil.condition ⟨0, zzPauli⟩ (fun h => absurd h (by decide))

/-- The one outcome bit unread. -/
def twirlUnread : Fin 1 ≃ Fin (0 + 1) := Equiv.refl _

/-- A word of two bits is its two values. -/
private theorem bits_two (x : Fin 2 → ZMod 2) : x = ![x 0, x 1] := by
  funext i
  fin_cases i <;> rfl

/-- Split a bit into its two values, as literals. -/
local macro "bit_cases " a:ident : tactic =>
  `(tactic| (rcases zmod_two_dichotomy $a with h | h <;> subst h))

/-- The referee of the `Z₀Z₁` conditioning on a point mass. -/
private theorem kraus_czCondition (a0 a1 b0 b1 c : ZMod 2) :
    czCondition.interpretAmp (delta ![a0, a1]) ![b0, b1, c]
      = if ![b0, b1] = ![a0, a1] then 2⁻¹ * (1 + signOf c * (signOf b0 * signOf b1)) else 0 := by
  bit_cases a0 <;> bit_cases a1 <;> bit_cases b0 <;> bit_cases b1 <;> bit_cases c <;>
    simp (config := {decide := true}) [czCondition, zzPauli, delta, pauliProjection_apply,
      shiftFactor, zDot, yWeight, Fin.init, signOf_zero, signOf_one]

/-- The Kraus operator at the outcome `e` is the projector `½(1 + (−1)^e Z₀Z₁)`. -/
private theorem krausOp_czCondition (o : Fin 0 → ZMod 2) (e : Fin 1 → ZMod 2) :
    krausOp czCondition twirlUnread o e
      = (2⁻¹ : ℂ) • (1 + signOf (e 0) • pauliMatrix zzPauli) := by
  ext w x
  have hword : Fin.append w (Fin.append o e ∘ twirlUnread) = ![w 0, w 1, e 0] := by
    funext i
    fin_cases i <;> rfl
  unfold krausOp dilation
  rw [hword, bits_two x, kraus_czCondition, bits_two w]
  generalize w 0 = b0, w 1 = b1, x 0 = a0, x 1 = a1, e 0 = c
  bit_cases a0 <;> bit_cases a1 <;> bit_cases b0 <;> bit_cases b1 <;> bit_cases c <;>
    simp (config := {decide := true}) [zzPauli, pauliMatrix, zDot,
      signOf_zero, signOf_one]

/-- The entry of `A ρ B†` at `(a, b)`. -/
private theorem sandwich_apply {α β : Type*} [Fintype α] (A B : Matrix β α ℂ)
    (ρ : Matrix α α ℂ) (a b : β) :
    (A * ρ * Bᴴ) a b = ∑ x, ∑ x', ρ x x' * (A a x * starRingEnd ℂ (B b x')) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  ring

/-- The branch from T49's `channel`, as the sum over the unread strings of the Kraus sandwiches. -/
private theorem channelBranch_eq_sum_kraus {m k r u : ℕ} (p : Protocol m n k)
    (σ : Fin k ≃ Fin (r + u)) (o : Fin r → ZMod 2)
    (ρ : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) :
    channelBranch p σ o ρ = ∑ e, krausOp p σ o e * ρ * (krausOp p σ o e)ᴴ := by
  ext w w'
  unfold channelBranch channel
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [sandwich_apply, sandwich_apply]
  rfl

/-- A sum over the words of one bit. -/
private theorem sum_bits_one {M : Type*} [AddCommMonoid M] (f : (Fin 1 → ZMod 2) → M) :
    ∑ x, f x = f ![0] + f ![1] := by
  rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp, sum_zmod_two]
  congr 2 <;> funext i <;> fin_cases i <;> rfl

/-- `Z₀Z₁` is Hermitian. -/
private theorem conjTranspose_pauliMatrix_zz :
    (pauliMatrix zzPauli)ᴴ = pauliMatrix zzPauli := by
  rw [pauliMatrix_eq_map, conjTranspose_map_intCast,
    show (pauliInt zzPauli)ᵀ = pauliInt zzPauli by decide]

/-- The branch of the `Z₀Z₁` conditioning, from T49's `channel`: `½ρ + ½ Z₀Z₁ ρ Z₀Z₁†`. -/
private theorem channelBranch_czCondition (ρ : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ) :
    channelBranch czCondition twirlUnread 0 ρ
      = (2⁻¹ : ℂ) • ρ + (2⁻¹ : ℂ) • (pauliMatrix zzPauli * ρ * (pauliMatrix zzPauli)ᴴ) := by
  rw [channelBranch_eq_sum_kraus, sum_bits_one, krausOp_czCondition, krausOp_czCondition]
  simp only [Matrix.cons_val_zero, signOf_zero, signOf_one, one_smul, neg_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_neg, conjTranspose_pauliMatrix_zz, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, one_mul, mul_one,
    Complex.star_def, map_inv₀, map_ofNat]
  module

/-- The sign of `T† Z₀Z₁ T`, `(−1)^{ω(T, Z₀Z₁)}`. -/
private def zzSign (T : Pauli 2) : ℤ := if omega T zzPauli = 0 then 1 else -1

/-- `T† T = 1` on two bits. -/
private theorem pauliMatrix_unitary_two (T : Pauli 2) :
    (pauliMatrix T)ᴴ * pauliMatrix T = 1 := by
  have h : ∀ T : Pauli 2, (pauliInt T)ᵀ * pauliInt T = 1 := by decide
  rw [pauliMatrix_eq_map, conjTranspose_map_intCast, ← map_mul_intCast, h T,
    Matrix.map_one _ Int.cast_zero Int.cast_one]

/-- `T† Z₀Z₁ T = (−1)^{ω(T, Z₀Z₁)} Z₀Z₁`. -/
private theorem pauliMatrix_conj_zz (T : Pauli 2) :
    (pauliMatrix T)ᴴ * pauliMatrix zzPauli * pauliMatrix T
      = ((zzSign T : ℤ) : ℂ) • pauliMatrix zzPauli := by
  have h : ∀ T : Pauli 2,
      (pauliInt T)ᵀ * pauliInt zzPauli * pauliInt T = zzSign T • pauliInt zzPauli := by decide
  rw [pauliMatrix_eq_map, pauliMatrix_eq_map, conjTranspose_map_intCast, ← map_mul_intCast,
    ← map_mul_intCast, h T]
  ext w x
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    smul_eq_mul, Int.cast_mul]

/-- The sign squares to `1`. -/
private theorem zzSign_mul_self (T : Pauli 2) :
    ((zzSign T : ℤ) : ℂ) * ((zzSign T : ℤ) : ℂ) = 1 := by
  unfold zzSign
  split_ifs <;> norm_num

/-- One term of the twirl of `ρ ↦ ½ρ + ½ Z₀Z₁ ρ Z₀Z₁†`: the term is the map itself. -/
private theorem twirl_term_czCondition (T : Pauli 2)
    (ρ : Matrix (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ℂ) :
    (pauliMatrix T)ᴴ * ((2⁻¹ : ℂ) • (pauliMatrix T * ρ * (pauliMatrix T)ᴴ)
        + (2⁻¹ : ℂ) • (pauliMatrix zzPauli * (pauliMatrix T * ρ * (pauliMatrix T)ᴴ)
          * (pauliMatrix zzPauli)ᴴ)) * pauliMatrix T
      = (2⁻¹ : ℂ) • ρ + (2⁻¹ : ℂ) • (pauliMatrix zzPauli * ρ * (pauliMatrix zzPauli)ᴴ) := by
  have h1 : (pauliMatrix T)ᴴ * (pauliMatrix T * ρ * (pauliMatrix T)ᴴ) * pauliMatrix T = ρ := by
    simp only [← Matrix.mul_assoc, pauliMatrix_unitary_two, Matrix.one_mul]
    rw [Matrix.mul_assoc, pauliMatrix_unitary_two, Matrix.mul_one]
  have h2 : (pauliMatrix T)ᴴ * (pauliMatrix zzPauli * (pauliMatrix T * ρ * (pauliMatrix T)ᴴ)
        * (pauliMatrix zzPauli)ᴴ) * pauliMatrix T
      = ((pauliMatrix T)ᴴ * pauliMatrix zzPauli * pauliMatrix T) * ρ
        * ((pauliMatrix T)ᴴ * pauliMatrix zzPauli * pauliMatrix T)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, h1, h2, pauliMatrix_conj_zz]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_def, map_intCast, zzSign_mul_self, one_smul]

/-- There are `4²` Paulis on two bits. -/
private theorem card_pauli_two : (Fintype.card (Pauli 2) : ℂ) = 4 ^ 2 := by
  rw [show Fintype.card (Pauli 2) = 16 by decide]
  norm_num

-- source: papers/clifford_structure/
-- Dankert_Cleve_Emerson_Livine_2006_exact_approximate_unitary_2designs_quant-ph_0606161
--   equation:h15d1fa01322c
-- row: agreement
/-- **The twirl of the `Z₀Z₁` conditioning.** Conditioning on `Z₀Z₁` with the outcome unread has
the branch `ρ ↦ ½ρ + ½ Z₀Z₁ ρ Z₀Z₁†`, from T49's `channel`; its Pauli twirl, from `pauliTwirl`'s
definition, is the branch itself, and a Pauli channel with the distribution `½` at `I` and at
`Z₀Z₁`. -/
theorem row_twirl_czCondition :
    (∀ ρ, channelBranch czCondition twirlUnread 0 ρ
      = (2⁻¹ : ℂ) • ρ + (2⁻¹ : ℂ) • (pauliMatrix zzPauli * ρ * (pauliMatrix zzPauli)ᴴ)) ∧
    pauliTwirl (channelBranch czCondition twirlUnread 0)
      = channelBranch czCondition twirlUnread 0 ∧
    IsPauliChannel (pauliTwirl (channelBranch czCondition twirlUnread 0)) := by
  have htwirl : pauliTwirl (channelBranch czCondition twirlUnread 0)
      = channelBranch czCondition twirlUnread 0 := by
    funext ρ
    unfold pauliTwirl
    simp only [channelBranch_czCondition, twirl_term_czCondition, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, card_pauli_two, smul_smul]
    rw [inv_mul_cancel₀ (by norm_num), one_smul]
  refine ⟨channelBranch_czCondition, htwirl, ?_⟩
  rw [htwirl]
  refine ⟨fun P => if P = 0 then 2⁻¹ else if P = zzPauli then 2⁻¹ else 0, fun ρ => ?_⟩
  rw [channelBranch_czCondition, Fintype.sum_eq_add 0 zzPauli (by decide)]
  · have h0 : pauliMatrix (0 : Pauli 2) = 1 := by
      rw [pauliMatrix_eq_map, show pauliInt (0 : Pauli 2) = 1 by decide,
        Matrix.map_one _ Int.cast_zero Int.cast_one]
    simp only [↓reduceIte, if_neg (by decide : zzPauli ≠ 0), h0, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  · intro P hP
    dsimp only
    rw [if_neg hP.1, if_neg hP.2, zero_smul]

/-! ## The real Pauli with no bits -/

/-- The real Pauli with no bits is the identity: `pauliMatrix 0 = 1`, restated here since the
topic module's `pauliMatrix_zero` is private to it. -/
private theorem pauliMatrix_zero_eq_one {n : ℕ} : pauliMatrix (0 : Pauli n) = 1 := by
  unfold pauliMatrix
  ext w x
  rw [X_zero, add_zero, zDot_zero_left, pow_zero, Matrix.one_apply]

/-! ## Row: a stabilizer encoder is inhabited -/

-- row: inhabitation
/-- **`quantum_macwilliams`'s hypothesis `IsStabilizerEncoder S V` is inhabited**, at the trivial
witness `S = ⊥`, `V = 1`, one qubit: `IsStabilizer ⊥` holds vacuously, `1 + finrank ⊥ = 1`,
`1ᴴ 1 = 1`, and the only `s ∈ ⊥` is `0`, on which `pauliMatrix 0 = 1` acts as the scalar `1`. -/
theorem row_stabilizerEncoder_inhabited :
    IsStabilizerEncoder (⊥ : Submodule (ZMod 2) (Pauli 1))
      (1 : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ) := by
  refine ⟨fun p hp q _ => ?_, by rw [finrank_bot], by rw [Matrix.conjTranspose_one, Matrix.one_mul],
    fun s hs => ?_⟩
  · rw [Submodule.mem_bot] at hp
    subst hp
    exact omega_zero_left q
  · rw [Submodule.mem_bot] at hs
    subst hs
    exact ⟨1, by rw [pauliMatrix_zero_eq_one, Matrix.one_mul, one_smul]⟩

/-! ## Declared mutants, aimed at a constant the proofs use -/

-- mutant: stabKraus_trace_power | FTQCLib/Carrier/DoublingCorollaries.lean
--   | trace (stabKraus g s j) * 2 ^ j = 2 ^ n
--   | trace (stabKraus g s j) * 2 ^ j = 3 ^ n

/-! ## Axiom sweep of the rows

The rows depend on the three standard axioms only; the headlines are `sorry`'d at this step and are
swept when proved. -/

/-- info: 'FTQCLib.Frame.Walkthrough.row_bell_enumerators' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_bell_enumerators

/-- info: 'FTQCLib.Frame.Walkthrough.row_rep_enumerators' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_rep_enumerators

/-- info: 'FTQCLib.Frame.Walkthrough.row_kl_singleFlips' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_kl_singleFlips

/-- info: 'FTQCLib.Frame.Walkthrough.row_kl_flipsWithPair' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_kl_flipsWithPair

/-- info: 'FTQCLib.Frame.Walkthrough.row_twirl_czCondition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_twirl_czCondition

/-! ## Axiom sweep of the topic module's own headlines (T51.4) -/

/-- info: 'FTQCLib.Frame.Walkthrough.quantum_macwilliams' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quantum_macwilliams

/-- info: 'FTQCLib.Frame.Walkthrough.knillLaflamme_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms knillLaflamme_iff

/-- info: 'FTQCLib.Frame.Walkthrough.knillLaflamme_stabilizer_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms knillLaflamme_stabilizer_iff

/-- info: 'FTQCLib.Frame.Walkthrough.pauli_twirl' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pauli_twirl

end FTQCLib.Frame.Walkthrough

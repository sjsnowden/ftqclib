/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierRules
import FTQCLib.Carrier.AntipodalKernel
import FTQCLib.Carrier.BackwardConstructions

/-!
# Completeness of the rules at every precision, and conservativity

The rules of `CarrierRule` (`CarrierRules.lean`) are complete for the equality of nonzero carrier
states up to the one gap decision D9 names (`docs/TARGETS.md`, T07). Two nonzero carrier states, at
any precisions, are related by the equivalence the rules generate exactly when they denote the same
state (`StateEq`) and the ratio of their scales is dyadic (`IsDyadicRatio`): a root of unity of
order a power of two times an integer power of `√2`. Nothing is assumed of the scales themselves.

The corollary, conservativity: two related carrier states at one precision `m` are related by a
chain every step of which is between carrier states at precision `m`. Each precision's equational
theory is then self-contained: a gate set of Hadamard gates and phases of order a power of two
enters only through `m`, H + CCZ at `m = 1` and Clifford + T at `m = 3`.

The "only if" half is soundness: each step keeps the amplitude (`stateEq_of_carrierRule`) and
multiplies the scale by a dyadic factor (`exists_isDyadicRatio_of_carrierRule`), and a carrier
state's scale is nonzero (`c_ne_zero_of_isCarrier`). The "if" half follows the direct route of
`docs/public/completeness-at-every-precision.html`: widen both supports; lift to one precision
`m ≥ 3` and match heights and scales; compare rows by the kernel of the cyclotomic fold; pad,
relabel each row (`relabel_derivable`) and rephase; finish with R4.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported, and nothing from
`FTQCLib/Explore/`.

## Main results

* `rewrite_complete` — for nonzero carrier states at any precisions, `Relation.EqvGen CarrierRule`
  relates `S` and `T` iff `StateEq S T` and the ratio `T.c / S.c` is dyadic.
* `rewrite_conservative` — two related carrier states at precision `m` are related by a chain of
  steps between carrier states at precision `m`.

## Implementation notes

* "Nonzero carrier state" is `IsCarrier`: positive precision, a Lagrangian, and a denotation that is
  not the zero function. The zero state is not covered: decision D3 makes a zero-weight outcome the
  zero state, and `IsCarrier` excludes it.
* The ratio is written `T.c / S.c`. Both scales are nonzero on carrier states, and `IsDyadicRatio`
  holds of a ratio exactly when it holds of its inverse, so neither the direction nor the division
  carries a condition.
* `rewrite_complete` puts no condition on the precisions `S.m` and `T.m` and none on the carrier
  states of a chain between them: the chain may pass through carrier states at other precisions, and
  through states that are not carrier states.
* `rewrite_conservative` restricts every step of the chain with `CarrierRuleWithin` to the predicate
  "a carrier state at precision `m`", so every state the chain visits is a carrier state at
  precision `m`.
* **The constructions read backwards** (T07.3.2) live in `BackwardConstructions.lean`, public so
  that the gate and these proofs see them: `exists_widen` (widen the support by a collapse),
  `exists_pad` (pad the height by a halving), `exists_unusedBit` (add an unused bound bit) and
  `exists_unrotate` (reverse a rotation). Each returns a carrier state at the same precision, one
  bound bit higher, related to its input by a chain of `CarrierRuleWithin` steps between carrier
  states at that precision, so conservativity and completeness can both use them.
* **The assembly** (T07.3.4) is private here. The precision `M` is at least three, both states'
  precisions and the order `2^k` of the ratio's root of unity, so the root is a character at `M`.
  Heights are matched without changing the scale by a raise (`exists_raise`): a rotation by the
  quarter turn read backwards multiplies the scale by an eighth root of unity, and R1 read backwards
  removes it. The exchange pads both states by one halving whose exponent is known
  (`exists_pad_layer`, since `exists_pad` does not expose its exponent), lays each row out in
  counts (`exists_row_exchange`: a common half, and on the padded half the row's antipodal pairs
  topped up with the pairs `0, 2^{m−1}`), reaches that layout by `relabel_derivable`, and one
  rephasing on the padded half turns the one layout into the other. No final R4 is needed.
* **Conservativity** (T07.3.5) repeats the assembly at the states' own precision `m`, with no lift.
  Widening, restating the support, unused bits, pads, R1, reversed rotations and the exchange each
  give a chain between carrier states at `m`. The ratio is already in reach at `m`: at a free word
  where the states do not vanish, `ζ·√2^f` is a quotient of sums of `2^m`-th roots of unity, so it
  lies in `ℚ(ζ_{2^m})` (`mul_zpow_mem_adjoin`). With `f` even, `ζ` lies there and is a `2^m`-th
  root (`AntipodalKernel.rootOfUnity_mem_two_pow`), and the heights are matched two at a time by an
  unused bit and a pad (`exists_raise_two`). With `f` odd: at `m = 1` the field is `ℚ` and `√2` is
  irrational (`not_mem_adjoin_zeta_one`); at `m ≥ 2` one reversed rotation by the quarter turn
  changes the parity and multiplies the root by an eighth root of unity (`exists_match_within`).

## References

These are cross-checks: each is a completeness theorem for one level or one calculus, and
`rewrite_complete` at that level must agree with it.

* R. Vilmart, *Completeness of Sum-Over-Paths for Toffoli-Hadamard and the Dyadic Fragments of
  Quantum Computation*, arXiv:2205.02600.
* R. Vilmart, arXiv:2307.14223.
* J. van de Wetering and S. Wolffs, arXiv:1904.07545 (phase-free ZH, the fragment at `m = 1`).
* M. Backens et al., arXiv:2103.06610 (ZH over rings containing ½).
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

section Soundness

/-- **Soundness of a chain.** A chain of steps keeps the amplitude and multiplies the scale by a
dyadic ratio. -/
private theorem stateEq_scale_of_eqvGen {S T : KernelSumState n}
    (hST : Relation.EqvGen CarrierRule S T) :
    StateEq S T ∧ ∃ r : ℂ, IsDyadicRatio r ∧ T.c = r * S.c := by
  induction hST with
  | rel A B hAB => exact ⟨stateEq_of_carrierRule hAB, exists_isDyadicRatio_of_carrierRule hAB⟩
  | refl A => exact ⟨StateEq.refl _, 1, isDyadicRatio_one, by rw [one_mul]⟩
  | symm A B _ ih =>
    obtain ⟨hs, r, hr, hc⟩ := ih
    refine ⟨hs.symm, r⁻¹, hr.inv, ?_⟩
    rw [hc, ← mul_assoc, inv_mul_cancel₀ hr.ne_zero, one_mul]
  | trans A B C _ _ ih₁ ih₂ =>
    obtain ⟨hs₁, r₁, hr₁, hc₁⟩ := ih₁
    obtain ⟨hs₂, r₂, hr₂, hc₂⟩ := ih₂
    refine ⟨hs₁.trans hs₂, r₂ * r₁, hr₂.mul hr₁, ?_⟩
    rw [hc₂, hc₁, mul_assoc]

end Soundness

section Moves

/-- A chain of steps within a predicate is a chain of steps. -/
private theorem eqvGen_of_within {p : KernelSumState n → Prop} {A B : KernelSumState n}
    (h : Relation.EqvGen (CarrierRuleWithin p) A B) : Relation.EqvGen CarrierRule A B :=
  Relation.EqvGen.mono (fun _ _ hr => hr.1) h

/-- Every root of unity of order dividing `2^k`, `k ≤ m`, is the character of a residue. -/
private theorem exists_charOf_eq {m k : ℕ} (hkm : k ≤ m) {ζ : ℂ} (hζ : ζ ^ 2 ^ k = 1) :
    ∃ b : ZMod (2 ^ m), charOf m b = ζ := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0 : ℕ) < 2 ^ m).ne'⟩
  have hζm : ζ ^ 2 ^ m = 1 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
    rw [pow_add, pow_mul, hζ, one_pow]
  obtain ⟨i, hi, hiζ⟩ := (isPrimitiveRoot_zeta m).eq_pow_of_pow_eq_one hζm
  exact ⟨(i : ZMod (2 ^ m)), by rw [charOf_eq_zeta_pow, ZMod.val_cast_of_lt hi, hiζ]⟩

/-- **R1 read backwards**, one step. The scale gains the character of `b` and the exponent loses
`b`. -/
private theorem carrierRule_addC {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) (b : ZMod (2 ^ m)) :
    CarrierRule (⟨m, h, Q - MvPolynomial.C b, charOf m b * c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ := by
  have hstep := CarrierRule.gauge (GaugeStep.addC (n := n) Q (-b) (charOf m b * c) L x₀)
  have hscale : charOf m b * c * charOf m (-b) = c := by
    rw [mul_right_comm, ← charOf_add, add_neg_cancel, charOf_zero, one_mul]
  have hQ : Q + MvPolynomial.C (-b) = Q - MvPolynomial.C b := by
    rw [map_neg, sub_eq_add_neg]
  rw [hQ, hscale] at hstep
  exact hstep

/-- **R1 read backwards.** The scale gains the character of `b` and the exponent loses `b`. -/
private theorem eqvGen_addC {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) (b : ZMod (2 ^ m)) :
    Relation.EqvGen CarrierRule
      (⟨m, h, Q - MvPolynomial.C b, charOf m b * c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ :=
  Relation.EqvGen.rel _ _ (carrierRule_addC Q c L x₀ b)

/-- **A raise.** At precision at least three, a carrier state has a carrier state one bound bit
higher with the same scale: a rotation by the quarter turn read backwards, whose scale factor is
an eighth root of unity, then R1 read backwards. -/
private theorem exists_raise {m h : ℕ} (hm3 : 3 ≤ m) {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) :
    ∃ Q' : DiagPhase (n + (h + 1)) m,
      IsCarrier (⟨m, h + 1, Q', c, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen CarrierRule ⟨m, h + 1, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  have hm : 1 ≤ m := by omega
  set a : ZMod (2 ^ m) := (2 : ZMod (2 ^ m)) ^ (m - 2) with ha_def
  have ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
    rw [ha_def, ← pow_succ']
    congr 1
    omega
  obtain ⟨hχ, Q1, hC1, hch1⟩ := exists_unrotate hS ha
  set ω : ℂ := (1 + charOf m a) / (Real.sqrt 2 : ℂ) with hω_def
  have htop : charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
    simpa using charOf_two_pow_mul hm 1
  have hx2 : charOf m a * charOf m a = -1 := by
    rw [← charOf_add, ← two_mul, ha, htop]
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := sqrt_two_sq_complex
  have hω2 : ω ^ 2 = charOf m a := by
    rw [hω_def, div_pow, hs2, div_eq_iff (show (2 : ℂ) ≠ 0 by norm_num)]
    linear_combination hx2
  have hω8 : ω ^ 2 ^ 3 = 1 := by
    have h8 : ω ^ 2 ^ 3 = ((ω ^ 2) ^ 2) ^ 2 := by ring
    rw [h8, hω2, show charOf m a ^ 2 = -1 by rw [sq, hx2]]
    norm_num
  obtain ⟨b, hb⟩ := exists_charOf_eq hm3 hω8
  have hstep := eqvGen_addC Q1 (c * (Real.sqrt 2 : ℂ) / (1 + charOf m a)) L x₀ b
  have hscale : charOf m b * (c * (Real.sqrt 2 : ℂ) / (1 + charOf m a)) = c := by
    rw [hb, hω_def]
    field_simp [ofReal_sqrt_two_ne_zero]
  rw [hscale] at hstep
  have hC : IsCarrier (⟨m, h + 1, Q1 - MvPolynomial.C b, c, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hC1 (stateEq_scale_of_eqvGen hstep).1 hm hS.2.1 hS.2.2.1
  exact ⟨Q1 - MvPolynomial.C b, hC, Relation.EqvGen.trans _ _ _ hstep (eqvGen_of_within hch1)⟩

/-- **Raises to any height.** A carrier state has a carrier state at every greater height with the
same scale. -/
private theorem exists_raise_to {m h : ℕ} (hm3 : 3 ≤ m) {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) {H : ℕ} (hH : h ≤ H) :
    ∃ Q' : DiagPhase (n + H) m,
      IsCarrier (⟨m, H, Q', c, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen CarrierRule ⟨m, H, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hH
  clear hH
  induction k with
  | zero => exact ⟨Q, hS, Relation.EqvGen.refl _⟩
  | succ k ih =>
    obtain ⟨Qk, hCk, hchk⟩ := ih
    obtain ⟨Qk1, hCk1, hchk1⟩ := exists_raise hm3 hCk
    exact ⟨Qk1, hCk1, Relation.EqvGen.trans _ _ _ hchk1 hchk⟩

/-- **Unused bits.** A carrier state has, `k` bound bits higher, a carrier state with scale
`c / √2^k`, by a chain between carrier states at its precision. -/
private theorem exists_unused_iter {m : ℕ} (k : ℕ) {h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) :
    ∃ Q' : DiagPhase (n + (h + k)) m,
      IsCarrier (⟨m, h + k, Q', c / (Real.sqrt 2 : ℂ) ^ k, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + k, Q', c / (Real.sqrt 2 : ℂ) ^ k, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  induction k with
  | zero =>
    refine ⟨Q, ?_, ?_⟩ <;> rw [pow_zero, div_one]
    · exact hS
    · exact Relation.EqvGen.refl _
  | succ k ih =>
    obtain ⟨Qk, hCk, hchk⟩ := ih
    obtain ⟨Qk1, hCk1, hchk1⟩ := exists_unusedBit hCk
    have heq : c / (Real.sqrt 2 : ℂ) ^ k / (Real.sqrt 2 : ℂ)
        = c / (Real.sqrt 2 : ℂ) ^ (k + 1) := by
      rw [pow_succ, div_div]
    rw [heq] at hCk1 hchk1
    exact ⟨Qk1, hCk1, Relation.EqvGen.trans _ _ _ hchk1 hchk⟩

/-- **Widening to every word.** A carrier state whose X-shadow misses at most `d` dimensions has a
carrier state whose X-shadow is every word, with the scale divided by a power of `√2`: widenings
(`exists_widen`), each of which grows the shadow strictly, by a chain between carrier states at its
precision. -/
private theorem exists_full {m : ℕ} (d : ℕ) : ∀ {h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2},
    n - Module.finrank (ZMod 2) (Submodule.map xProj L) ≤ d →
    IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) →
    ∃ (j h' : ℕ) (Q' : DiagPhase (n + h') m) (L' : Submodule (ZMod 2) (Pauli n)),
      Submodule.map xProj L' = ⊤ ∧
      IsCarrier (⟨m, h', Q', c / (Real.sqrt 2 : ℂ) ^ j, L', x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h', Q', c / (Real.sqrt 2 : ℂ) ^ j, L', x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  induction d with
  | zero =>
    intro h Q c L x₀ hd hS
    by_cases hK : Submodule.map xProj L = ⊤
    · refine ⟨0, h, Q, L, hK, ?_, ?_⟩ <;> rw [pow_zero, div_one]
      · exact hS
      · exact Relation.EqvGen.refl _
    · exfalso
      obtain ⟨L1, Q1, hlt, -, -⟩ := exists_widen hS hK
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 := Submodule.finrank_le (Submodule.map xProj L1)
      rw [Module.finrank_fin_fun] at h2
      omega
  | succ d ih =>
    intro h Q c L x₀ hd hS
    by_cases hK : Submodule.map xProj L = ⊤
    · refine ⟨0, h, Q, L, hK, ?_, ?_⟩ <;> rw [pow_zero, div_one]
      · exact hS
      · exact Relation.EqvGen.refl _
    · obtain ⟨L1, Q1, hlt, hC1, hch1⟩ := exists_widen hS hK
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 := Submodule.finrank_le (Submodule.map xProj L1)
      rw [Module.finrank_fin_fun] at h2
      obtain ⟨j, h', Q', L', hL', hC', hch'⟩ := ih (by omega) hC1
      have heq : c / (Real.sqrt 2 : ℂ) / (Real.sqrt 2 : ℂ) ^ j
          = c / (Real.sqrt 2 : ℂ) ^ (j + 1) := by
        rw [pow_succ', div_div]
      rw [heq] at hC' hch'
      exact ⟨j + 1, h', Q', L', hL', hC',
        Relation.EqvGen.trans _ _ _ hch' hch1⟩

/-- **One support.** Two Lagrangians whose X-shadows are every word, with any offsets, carry the
same carrier state up to R3 and R2. -/
private theorem eqvGen_retarget {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    {L L' : Submodule (ZMod 2) (Pauli n)} (x₀ x₀' : Fin n → ZMod 2)
    (hL : Submodule.map xProj L = ⊤) (hL' : Submodule.map xProj L' = ⊤) :
    Relation.EqvGen CarrierRule (⟨m, h, Q, c, L', x₀'⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ := by
  have h3 : CarrierRule (⟨m, h, Q, c, L', x₀'⟩ : KernelSumState n) ⟨m, h, Q, c, L, x₀'⟩ :=
    CarrierRule.gauge (GaugeStep.congrXProj Q c L' L x₀' (hL'.trans hL.symm))
  have hv : x₀' - x₀ ∈ Submodule.map xProj L := by
    rw [hL]
    exact Submodule.mem_top
  have h2 := CarrierRule.gauge (GaugeStep.offsetAddMem (n := n) Q c L x₀ hv)
  have hx : x₀ + (x₀' - x₀) = x₀' := by abel
  rw [hx] at h2
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h3) (Relation.EqvGen.rel _ _ h2)

/-- **Matching heights and scales**, for a ratio `χ(b)·√2^e` with `e` a natural number: `e` unused
bits on the second carrier state, R1 read backwards on the first, and raises on both. -/
private theorem exists_match_nat {m hA hB : ℕ} (hm3 : 3 ≤ m) {QA : DiagPhase (n + hA) m}
    {QB : DiagPhase (n + hB) m} {cA cB : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} (b : ZMod (2 ^ m)) (e : ℕ)
    (hcB : cB = charOf m b * cA * (Real.sqrt 2 : ℂ) ^ e)
    (hSA : IsCarrier (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n))
    (hSB : IsCarrier (⟨m, hB, QB, cB, L, x₀⟩ : KernelSumState n)) :
    ∃ (H : ℕ) (QA' QB' : DiagPhase (n + (H + 1)) m) (C : ℂ), C ≠ 0 ∧
      Relation.EqvGen CarrierRule ⟨m, H + 1, QA', C, L, x₀⟩ ⟨m, hA, QA, cA, L, x₀⟩ ∧
      Relation.EqvGen CarrierRule ⟨m, H + 1, QB', C, L, x₀⟩ ⟨m, hB, QB, cB, L, x₀⟩ := by
  have hm : 1 ≤ m := by omega
  obtain ⟨QB1, hCB1, hchB1⟩ := exists_unused_iter e hSB
  have heq : cB / (Real.sqrt 2 : ℂ) ^ e = charOf m b * cA := by
    rw [hcB, mul_div_assoc, div_self (pow_ne_zero _ ofReal_sqrt_two_ne_zero), mul_one]
  rw [heq] at hCB1 hchB1
  have hchA1 := eqvGen_addC QA cA L x₀ b
  have hCA1 : IsCarrier
      (⟨m, hA, QA - MvPolynomial.C b, charOf m b * cA, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hSA (stateEq_scale_of_eqvGen hchA1).1 hm hSA.2.1 hSA.2.2.1
  obtain ⟨QA2, hCA2, hchA2⟩ :=
    exists_raise_to hm3 hCA1 (H := hA + hB + e + 1) (by omega)
  obtain ⟨QB2, hCB2, hchB2⟩ :=
    exists_raise_to hm3 hCB1 (H := hA + hB + e + 1) (by omega)
  exact ⟨hA + hB + e, QA2, QB2, charOf m b * cA, c_ne_zero_of_isCarrier hCA2,
    Relation.EqvGen.trans _ _ _ hchA2 hchA1,
    Relation.EqvGen.trans _ _ _ hchB2 (eqvGen_of_within hchB1)⟩

/-- **Matching heights and scales**, for a ratio `χ(b)·√2^e` with `e` an integer: the natural case,
for the two carrier states in one order or the other. -/
private theorem exists_match {m hA hB : ℕ} (hm3 : 3 ≤ m) {QA : DiagPhase (n + hA) m}
    {QB : DiagPhase (n + hB) m} {cA cB : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} (b : ZMod (2 ^ m)) (e : ℤ)
    (hcB : cB = charOf m b * cA * (Real.sqrt 2 : ℂ) ^ e)
    (hSA : IsCarrier (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n))
    (hSB : IsCarrier (⟨m, hB, QB, cB, L, x₀⟩ : KernelSumState n)) :
    ∃ (H : ℕ) (QA' QB' : DiagPhase (n + (H + 1)) m) (C : ℂ), C ≠ 0 ∧
      Relation.EqvGen CarrierRule ⟨m, H + 1, QA', C, L, x₀⟩ ⟨m, hA, QA, cA, L, x₀⟩ ∧
      Relation.EqvGen CarrierRule ⟨m, H + 1, QB', C, L, x₀⟩ ⟨m, hB, QB, cB, L, x₀⟩ := by
  rcases le_or_gt 0 e with he | he
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
    rw [zpow_natCast] at hcB
    exact exists_match_nat hm3 b k hcB hSA hSB
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -e by omega)
    have hcA : cA = charOf m (-b) * cB * (Real.sqrt 2 : ℂ) ^ k := by
      have he' : e = -(k : ℤ) := by omega
      rw [hcB, he', zpow_neg, zpow_natCast]
      have h1 : charOf m (-b) * charOf m b = 1 := by
        rw [← charOf_add, neg_add_cancel, charOf_zero]
      have h2 : ((Real.sqrt 2 : ℂ) ^ k)⁻¹ * (Real.sqrt 2 : ℂ) ^ k = 1 :=
        inv_mul_cancel₀ (pow_ne_zero _ ofReal_sqrt_two_ne_zero)
      linear_combination (-(cA * charOf m (-b) * charOf m b) * h2) - cA * h1
    obtain ⟨H, QB', QA', C, hC, hchB, hchA⟩ := exists_match_nat hm3 (-b) k hcA hSB hSA
    exact ⟨H, QA', QB', C, hC, hchA, hchB⟩

end Moves

section Counting

/-! ### Counting values

A row of a carrier state is read through the number of bound words at which it takes each value
(`AntipodalKernel.phaseCount`). Two rows with the same counts are one bijection of the bound words
apart (`exists_perm_of_cnt`), and any counts of the right total are the counts of some row
(`exists_cnt_eq`). -/

/-- The number of words at which `u` takes the value `a`. -/
private def cnt {X G : Type*} [Fintype X] [DecidableEq G] (u : X → G) (a : G) : ℕ :=
  (Finset.univ.filter fun x => u x = a).card

/-- The counts of a function sum to the number of its words. -/
private theorem sum_cnt {X G : Type*} [Fintype X] [Fintype G] [DecidableEq G] (u : X → G) :
    ∑ a, cnt u a = Fintype.card X := by
  simp only [cnt, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- **Any counts are realised.** Counts whose total is the number of words are the counts of a
function. -/
private theorem exists_cnt_eq {X G : Type*} [Fintype X] [Fintype G] [DecidableEq G]
    (κ : G → ℕ) (hκ : ∑ a, κ a = Fintype.card X) : ∃ u : X → G, ∀ a, cnt u a = κ a := by
  have hcard : Fintype.card X = Fintype.card (Σ a : G, Fin (κ a)) := by
    rw [Fintype.card_sigma]
    simp [hκ]
  let E := Fintype.equivOfCardEq hcard
  refine ⟨fun x => (E x).1, fun a => ?_⟩
  simp only [cnt, Finset.card_filter]
  have hE := Equiv.sum_comp E (fun p : (Σ a : G, Fin (κ a)) => if p.1 = a then 1 else 0)
  simp only at hE
  rw [hE, Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- **Equal counts, one bijection.** Two functions with the same counts differ by a bijection of
their words. -/
private theorem exists_perm_of_cnt {X G : Type*} [Fintype X] [DecidableEq G] (u v : X → G)
    (h : ∀ a, cnt u a = cnt v a) : ∃ σ : Equiv.Perm X, ∀ x, v x = u (σ x) := by
  classical
  have e : ∀ a, {x // v x = a} ≃ {x // u x = a} := fun a =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact (h a).symm)
  exact ⟨Equiv.ofFiberEquiv e, fun x => (Equiv.ofFiberEquiv_map e x).symm⟩

/-- The counts of the constant `0` on the words of `h` bits. -/
private theorem cnt_zero {m h : ℕ} (a : ZMod (2 ^ m)) :
    cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m))) a = if a = 0 then 2 ^ h else 0 := by
  unfold cnt
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [if_neg ha]
    simp [Ne.symm ha]

/-- **The layered row.** Where the last bound bit is `0`, the row `O` of the other bound bits;
where it is `1`, the row `Z` of the bits before the last two, plus the top bit `2^{m−1}` times the
bit before the last. On the second half the bit before the last pairs the cells antipodally. -/
private def layer {m h : ℕ} (O : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m))
    (Z : (Fin h → ZMod 2) → ZMod (2 ^ m)) (y : Fin (h + 1 + 1) → ZMod 2) : ZMod (2 ^ m) :=
  if y (Fin.last (h + 1)) = 0 then O (Fin.init y)
  else Z (Fin.init (Fin.init y))
    + (((y (Fin.castSucc (Fin.last h))).val : ℕ) : ZMod (2 ^ m)) * (2 : ZMod (2 ^ m)) ^ (m - 1)

/-- `layer` at a word written with its last bit. -/
private theorem layer_snoc {m h : ℕ} (O : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m))
    (Z : (Fin h → ZMod 2) → ZMod (2 ^ m)) (y : Fin (h + 1) → ZMod 2) (r : ZMod 2) :
    layer O Z (Fin.snoc y r) = if r = 0 then O y
      else Z (Fin.init y) + (((y (Fin.last h)).val : ℕ) : ZMod (2 ^ m))
        * (2 : ZMod (2 ^ m)) ^ (m - 1) := by
  simp only [layer, Fin.snoc_last, Fin.init_snoc, Fin.snoc_castSucc]

/-- **The counts of a layered row**: those of `O`, of `Z`, and of `Z` shifted by the top bit. -/
private theorem cnt_layer {m h : ℕ} (O : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m))
    (Z : (Fin h → ZMod 2) → ZMod (2 ^ m)) (a : ZMod (2 ^ m)) :
    cnt (layer O Z) a = cnt O a + (cnt Z a + cnt Z (a - (2 : ZMod (2 ^ m)) ^ (m - 1))) := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have h1 : (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ m)) = 1 := by
    rw [show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one]
  have h0 : (((0 : ZMod 2).val : ℕ) : ZMod (2 ^ m)) = 0 := by
    rw [show (0 : ZMod 2).val = 0 from rfl, Nat.cast_zero]
  simp only [cnt, Finset.card_filter]
  rw [sum_snoc_peel, huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [layer_snoc, if_neg (show (1 : ZMod 2) ≠ 0 by decide)]
  congr 1
  rw [sum_snoc_peel, huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Fin.init_snoc, Fin.snoc_last, h0, h1, zero_mul, add_zero, one_mul,
    eq_sub_iff_add_eq]

end Counting

section Exchange

/-! ### The exchange of antipodal pairs -/

/-- A step of a relabelling chain (`relabel_derivable`: precision `m`, Lagrangian `L`, the state of
a carrier state `X`) is a step between carrier states at precision `m`. -/
private theorem within_of_relabel {m : ℕ} {L : Submodule (ZMod 2) (Pauli n)} {X : KernelSumState n}
    (hX : IsCarrier X) (hXm : X.m = m) (hXL : X.L = L) {A B : KernelSumState n}
    (hAB : CarrierRuleWithin (fun A => A.m = m ∧ A.L = L ∧ StateEq A X) A B) :
    CarrierRuleWithin (fun A => IsCarrier A ∧ A.m = m) A B := by
  obtain ⟨hr, ⟨hAm, hAL, hAs⟩, ⟨hBm, hBL, hBs⟩⟩ := hAB
  have hc : ∀ Y : KernelSumState n, Y.m = m → Y.L = L → StateEq Y X → IsCarrier Y := by
    intro Y hYm hYL hYs
    refine isCarrier_of_stateEq hX hYs (by rw [hYm, ← hXm]; exact hX.1) ?_ ?_
    · rw [hYL, ← hXL]
      exact hX.2.1
    · rw [hYL, ← hXL]
      exact hX.2.2.1
  exact ⟨hr, ⟨hc A hAm hAL hAs, hAm⟩, ⟨hc B hBm hBL hBs, hBm⟩⟩

/-- The pairing of the second half of a layered row: flip the bit before the last. -/
private def layerPair (h : ℕ) : Equiv.Perm (Fin (h + 1 + 1) → ZMod 2) :=
  Equiv.addRight (Pi.single (Fin.castSucc (Fin.last h)) (1 : ZMod 2))

/-- The second half of the bound words: the last bound bit is `1`. -/
private def layerHalf (h : ℕ) : Finset (Fin (h + 1 + 1) → ZMod 2) :=
  Finset.univ.filter fun y => y (Fin.last (h + 1)) = 1

/-- **A layered row is paired antipodally on its second half.** -/
private theorem antipodalOn_layer {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + (h + 1 + 1)) m)
    (w : Fin n → ZMod 2) (O : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m))
    (Z : (Fin h → ZMod 2) → ZMod (2 ^ m))
    (hQ : ∀ y, Q.eval (Fin.append w y) = layer O Z y) :
    AntipodalOn Q w (layerHalf h) (layerPair h) := by
  have hne : (Fin.castSucc (Fin.last h) : Fin (h + 1 + 1)) ≠ Fin.last (h + 1) :=
    (Fin.castSucc_lt_last _).ne
  have hlast : ∀ y : Fin (h + 1 + 1) → ZMod 2,
      (layerPair h y) (Fin.last (h + 1)) = y (Fin.last (h + 1)) := by
    intro y
    simp only [layerPair, Equiv.coe_addRight, Pi.add_apply, Pi.single_eq_of_ne' hne, add_zero]
  have hbit : ∀ y : Fin (h + 1 + 1) → ZMod 2,
      (layerPair h y) (Fin.castSucc (Fin.last h)) = y (Fin.castSucc (Fin.last h)) + 1 := by
    intro y
    simp only [layerPair, Equiv.coe_addRight, Pi.add_apply, Pi.single_eq_same]
  have hinit : ∀ y : Fin (h + 1 + 1) → ZMod 2,
      Fin.init (Fin.init (layerPair h y)) = Fin.init (Fin.init y) := by
    intro y
    funext i
    have hi : (Fin.castSucc (Fin.castSucc i) : Fin (h + 1 + 1)) ≠ Fin.castSucc (Fin.last h) :=
      (Fin.castSucc_lt_castSucc_iff.mpr (Fin.castSucc_lt_last i)).ne
    simp only [Fin.init, layerPair, Equiv.coe_addRight, Pi.add_apply, Pi.single_eq_of_ne hi,
      add_zero]
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · simp only [layerHalf, Finset.mem_filter, Finset.mem_univ, true_and, hlast]
  · have h1 : y (Fin.last (h + 1)) = 1 := by simpa [layerHalf] using hy
    have h1' : (layerPair h y) (Fin.last (h + 1)) = 1 := by rw [hlast]; exact h1
    rw [hQ, hQ]
    unfold layer
    rw [if_neg (by rw [h1']; decide), if_neg (by rw [h1]; decide), hinit, hbit]
    have hv0 : (((0 : ZMod 2).val : ℕ) : ZMod (2 ^ m)) = 0 := by
      rw [show (0 : ZMod 2).val = 0 from rfl, Nat.cast_zero]
    have hv1 : (((1 : ZMod 2).val : ℕ) : ZMod (2 ^ m)) = 1 := by
      rw [show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one]
    rcases zmod_two_eq_zero_or_one (y (Fin.castSucc (Fin.last h))) with h0 | h0 <;> rw [h0]
    · rw [zero_add, hv0, hv1, zero_mul, add_zero, one_mul]
    · rw [show (1 : ZMod 2) + 1 = 0 from by decide, hv0, hv1, zero_mul, one_mul, add_zero,
        add_assoc (Z _), AntipodalKernel.two_pow_pred_add_self hm, add_zero]

/-- **A pad by halving, with its exponent.** Over `⟨m, h + 1, Q, c, L, x₀⟩` the layered exponent
that reads `Q` on the first half and the pairs `0, 2^{m−1}` on the second, at scale `c·√2`, halves
to it. -/
private theorem exists_pad_layer {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + (h + 1)) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    ∃ Q' : DiagPhase (n + (h + 1 + 1)) m,
      (∀ w y, Q'.eval (Fin.append w y)
        = layer (fun y1 => Q.eval (Fin.append w y1)) (fun _ => (0 : ZMod (2 ^ m))) y) ∧
      CarrierRule (⟨m, h + 1 + 1, Q', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n)
        ⟨m, h + 1, Q, c, L, x₀⟩ := by
  classical
  obtain ⟨Q', hQ'⟩ := exists_diagPhase_append (n := n) (m := m) (h := h + 1 + 1)
    (fun w y => layer (fun y1 => Q.eval (Fin.append w y1)) (fun _ => (0 : ZMod (2 ^ m))) y)
  let e : (Fin (h + 1) → ZMod 2) ↪ (Fin (h + 1 + 1) → ZMod 2) :=
    ⟨fun y => Fin.snoc y 0, fun y y' hyy => by
      simpa only [Fin.init_snoc] using
        congrArg (fun q : Fin (h + 1 + 1) → ZMod 2 => Fin.init q) hyy⟩
  have hP : ∀ y', y' ∈ layerHalf h ↔ ∀ y, e y ≠ y' := by
    intro y'
    simp only [layerHalf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1 y hy
      rw [← hy] at h1
      change (Fin.snoc y (0 : ZMod 2) : Fin (h + 1 + 1) → ZMod 2) (Fin.last (h + 1)) = 1 at h1
      rw [Fin.snoc_last] at h1
      exact absurd h1 (by decide)
    · intro hne'
      rcases zmod_two_eq_zero_or_one (y' (Fin.last (h + 1))) with h0 | h1
      · refine absurd ?_ (hne' (Fin.init y'))
        change (Fin.snoc (Fin.init y') (0 : ZMod 2) : Fin (h + 1 + 1) → ZMod 2) = y'
        rw [← h0]
        exact Fin.snoc_init_self y'
      · exact h1
  have hread : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin (h + 1) → ZMod 2,
      Q.eval (Fin.append w y) = Q'.eval (Fin.append w (e y)) := by
    intro w _ y
    rw [hQ']
    change _ = layer _ _ (Fin.snoc y 0)
    rw [layer_snoc, if_pos rfl]
  have hstep := CarrierRule.halve hm Q' Q (c * (Real.sqrt 2 : ℂ)) L x₀ e (layerHalf h)
    (layerPair h) hP hread (fun w _ => antipodalOn_layer hm Q' w _ _ (hQ' w))
  rw [mul_div_cancel_right₀ c ofReal_sqrt_two_ne_zero] at hstep
  exact ⟨Q', hQ', hstep⟩

/-- Adding the top bit to a residue moves it between the lower and the upper half of the
residues. -/
private theorem lower_add_half {m : ℕ} (hm : 1 ≤ m) (a : ZMod (2 ^ m)) :
    (a + (2 : ZMod (2 ^ m)) ^ (m - 1)).val < 2 ^ (m - 1) ↔ ¬ a.val < 2 ^ (m - 1) := by
  haveI : NeZero (2 ^ m) := ⟨(by positivity : (0 : ℕ) < 2 ^ m).ne'⟩
  have hN : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  have hpos : 0 < 2 ^ (m - 1) := by positivity
  have hhv : ((2 : ZMod (2 ^ m)) ^ (m - 1)).val = 2 ^ (m - 1) := by
    rw [show (2 : ZMod (2 ^ m)) ^ (m - 1) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) by push_cast; rfl,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have ha := ZMod.val_lt a
  rw [ZMod.val_add, hhv]
  rcases lt_or_ge a.val (2 ^ (m - 1)) with h1 | h1
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- **One representative of each antipodal pair.** A pair-symmetric count has a count on the lower
half of the residues from which it is recovered by adding the shift by the top bit, and whose total
is half its total. -/
private theorem exists_half_count {m : ℕ} (hm : 1 ≤ m) (p : ZMod (2 ^ m) → ℕ)
    (hp : ∀ a, p (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = p a) :
    ∃ q : ZMod (2 ^ m) → ℕ, (∀ a, q a + q (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = p a) ∧
      ∑ a, p a = 2 * ∑ a, q a := by
  obtain ⟨q, hq⟩ : ∃ q : ZMod (2 ^ m) → ℕ, ∀ a, q a = if a.val < 2 ^ (m - 1) then p a else 0 :=
    ⟨_, fun _ => rfl⟩
  have hpair : ∀ a, q a + q (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = p a := by
    intro a
    have hlow := lower_add_half hm a
    rw [hq, hq]
    by_cases h1 : a.val < 2 ^ (m - 1)
    · have h2 : ¬ (a + (2 : ZMod (2 ^ m)) ^ (m - 1)).val < 2 ^ (m - 1) := fun h => hlow.mp h h1
      rw [if_pos h1, if_neg h2, add_zero]
    · have h2 : (a + (2 : ZMod (2 ^ m)) ^ (m - 1)).val < 2 ^ (m - 1) := hlow.mpr h1
      rw [if_neg h1, if_pos h2, zero_add, hp]
  have hshift : ∑ a, q (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) = ∑ a, q a :=
    Equiv.sum_comp (Equiv.addRight ((2 : ZMod (2 ^ m)) ^ (m - 1))) q
  refine ⟨q, hpair, ?_⟩
  calc ∑ a, p a = ∑ a, (q a + q (a + (2 : ZMod (2 ^ m)) ^ (m - 1))) :=
        Finset.sum_congr rfl (fun a _ => (hpair a).symm)
    _ = 2 * ∑ a, q a := by rw [Finset.sum_add_distrib, hshift, two_mul]

/-- **The per-row exchange.** Two rows of one length whose counts differ antipodally have layered
forms with one common first half `o`: on the second half, the first row's antipodal pairs and the
second row's, topped up with the pairs `0, 2^{m−1}`, in counts equal to those of the rows padded by
those pairs. -/
private theorem exists_row_exchange {m h : ℕ} (hm : 1 ≤ m)
    (F Gr : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m))
    (hdiff : ∀ a : ZMod (2 ^ m),
      (cnt Gr (a + (2 : ZMod (2 ^ m)) ^ (m - 1)) : ℤ) - cnt F (a + (2 : ZMod (2 ^ m)) ^ (m - 1))
        = (cnt Gr a : ℤ) - cnt F a) :
    ∃ (o : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m)) (zA zB : (Fin h → ZMod 2) → ZMod (2 ^ m)),
      ∀ a : ZMod (2 ^ m),
        cnt o a + (cnt zA a + cnt zA (a - (2 : ZMod (2 ^ m)) ^ (m - 1)))
          = cnt F a + (cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m))) a
            + cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m)))
              (a - (2 : ZMod (2 ^ m)) ^ (m - 1)))
        ∧ cnt o a + (cnt zB a + cnt zB (a - (2 : ZMod (2 ^ m)) ^ (m - 1)))
          = cnt Gr a + (cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m))) a
            + cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m)))
              (a - (2 : ZMod (2 ^ m)) ^ (m - 1))) := by
  set half : ZMod (2 ^ m) := (2 : ZMod (2 ^ m)) ^ (m - 1) with hhalf
  have hhh : half + half = 0 := AntipodalKernel.two_pow_pred_add_self hm
  have hsub : ∀ a : ZMod (2 ^ m), a - half = a + half := fun a => by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left hhh]
  have hback : ∀ a : ZMod (2 ^ m), a + half + half = a := fun a => by
    rw [add_assoc, hhh, add_zero]
  have hzero : ∀ a : ZMod (2 ^ m), a + half = 0 ↔ a = half := fun a => by
    constructor
    · intro h0
      rw [← hback a, h0, zero_add]
    · rintro rfl
      exact hhh
  have hcardO : Fintype.card (Fin (h + 1) → ZMod 2) = 2 ^ (h + 1) := by simp
  have hcardZ : Fintype.card (Fin h → ZMod 2) = 2 ^ h := by simp
  have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [pow_succ, mul_comm]
  -- The counts of the two rows, their antipodal pairs and what is left.
  obtain ⟨φ, hφ⟩ : ∃ φ : ZMod (2 ^ m) → ℕ, ∀ a, cnt F a = φ a := ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ZMod (2 ^ m) → ℕ, ∀ a, cnt Gr a = γ a := ⟨_, fun _ => rfl⟩
  have hφsum : ∑ a, φ a = 2 ^ (h + 1) := by
    rw [← hcardO, ← sum_cnt F]
    exact Finset.sum_congr rfl (fun a _ => (hφ a).symm)
  have hγsum : ∑ a, γ a = 2 ^ (h + 1) := by
    rw [← hcardO, ← sum_cnt Gr]
    exact Finset.sum_congr rfl (fun a _ => (hγ a).symm)
  simp only [hφ, hγ] at hdiff ⊢
  obtain ⟨pf, hpf⟩ : ∃ pf : ZMod (2 ^ m) → ℕ, ∀ a, pf a = min (φ a) (φ (a + half)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨pg, hpg⟩ : ∃ pg : ZMod (2 ^ m) → ℕ, ∀ a, pg a = min (γ a) (γ (a + half)) :=
    ⟨_, fun _ => rfl⟩
  have hpf_le : ∀ a, pf a ≤ φ a := fun a => by rw [hpf]; exact min_le_left _ _
  have hpg_le : ∀ a, pg a ≤ γ a := fun a => by rw [hpg]; exact min_le_left _ _
  have hR : ∀ a, γ a - pg a = φ a - pf a := fun a => by
    have := hdiff a
    rw [hpf, hpg]
    omega
  obtain ⟨pfh, hpfh, hpfs⟩ := exists_half_count hm pf (fun a => by
    rw [hpf, hpf, hback, min_comm])
  obtain ⟨pgh, hpgh, hpgs⟩ := exists_half_count hm pg (fun a => by
    rw [hpg, hpg, hback, min_comm])
  have hpfh' : ∀ a, pfh a + pfh (a + half) = pf a := hpfh
  have hpgh' : ∀ a, pgh a + pgh (a + half) = pg a := hpgh
  have hsplitf : ∑ a, φ a = ∑ a, (φ a - pf a) + ∑ a, pf a := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by have := hpf_le a; omega)
  have hsplitg : ∑ a, γ a = ∑ a, (φ a - pf a) + ∑ a, pg a := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by have := hpg_le a; have := hR a; omega)
  have hpfle : ∑ a, pf a ≤ ∑ a, φ a := Finset.sum_le_sum (fun a _ => hpf_le a)
  set K := ∑ a, pfh a with hK
  have hK' : ∑ a, pgh a = K := by omega
  have hKle : K ≤ 2 ^ h := by omega
  have hs1 : ∀ k : ℕ, ∑ a : ZMod (2 ^ m), (if a = 0 then k else 0) = k := fun k => by simp
  have hs2 : ∀ k : ℕ, ∑ a : ZMod (2 ^ m), (if a = half then k else 0) = k := fun k => by simp
  -- The three layouts.
  obtain ⟨o, ho⟩ := exists_cnt_eq (X := Fin (h + 1) → ZMod 2)
    (fun a => (φ a - pf a) + (if a = 0 then K else 0) + (if a = half then K else 0)) (by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs1, hs2, hcardO]
      omega)
  obtain ⟨zA, hzA⟩ := exists_cnt_eq (X := Fin h → ZMod 2)
    (fun a => pfh a + (if a = 0 then 2 ^ h - K else 0)) (by
      rw [Finset.sum_add_distrib, hs1, hcardZ]
      omega)
  obtain ⟨zB, hzB⟩ := exists_cnt_eq (X := Fin h → ZMod 2)
    (fun a => pgh a + (if a = 0 then 2 ^ h - K else 0)) (by
      rw [Finset.sum_add_distrib, hs1, hcardZ, hK']
      omega)
  refine ⟨o, zA, zB, fun a => ?_⟩
  rw [ho, hzA, hzA, hzB, hzB, cnt_zero, cnt_zero, hsub]
  simp only [hzero a]
  have e1 := hpfh' a
  have e2 := hpgh' a
  have e3 := hpf_le a
  have e4 := hpg_le a
  have e5 := hR a
  constructor <;> split_ifs <;> omega

/-- **The exchange of antipodal pairs.** Two carrier states at one precision, height, scale and
support whose amplitudes agree on the support are related: pad both by halving, relabel each row
(`relabel_derivable`) into the layered forms of `exists_row_exchange`, and rephase the second half
from the one to the other. Every state of the chain is a carrier state at precision `m`. -/
private theorem eqvGen_exchange {m h : ℕ} (hm : 1 ≤ m) (QA QB : DiagPhase (n + (h + 1)) m)
    {c : ℂ} (hc : c ≠ 0) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (hA : IsCarrier (⟨m, h + 1, QA, c, L, x₀⟩ : KernelSumState n))
    (hamp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) →
      ampCore m (h + 1) QB c w = ampCore m (h + 1) QA c w) :
    Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
      (⟨m, h + 1, QA, c, L, x₀⟩ : KernelSumState n) ⟨m, h + 1, QB, c, L, x₀⟩ := by
  obtain ⟨QA', hQA', hpA⟩ := exists_pad_layer hm QA c L x₀
  obtain ⟨QB', hQB', hpB⟩ := exists_pad_layer hm QB c L x₀
  have key : ∀ w : Fin n → ZMod 2, ∃ (o : (Fin (h + 1) → ZMod 2) → ZMod (2 ^ m))
      (zA zB : (Fin h → ZMod 2) → ZMod (2 ^ m)), (∃ p ∈ L, w = x₀ + p.X) →
      ∀ a : ZMod (2 ^ m),
        cnt o a + (cnt zA a + cnt zA (a - (2 : ZMod (2 ^ m)) ^ (m - 1)))
          = cnt (fun y => QA.eval (Fin.append w y)) a
            + (cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m))) a
              + cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m)))
                (a - (2 : ZMod (2 ^ m)) ^ (m - 1)))
        ∧ cnt o a + (cnt zB a + cnt zB (a - (2 : ZMod (2 ^ m)) ^ (m - 1)))
          = cnt (fun y => QB.eval (Fin.append w y)) a
            + (cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m))) a
              + cnt (fun _ : Fin h → ZMod 2 => (0 : ZMod (2 ^ m)))
                (a - (2 : ZMod (2 ^ m)) ^ (m - 1))) := by
    intro w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · obtain ⟨o, zA, zB, hozz⟩ := exists_row_exchange hm (fun y => QA.eval (Fin.append w y))
        (fun y => QB.eval (Fin.append w y))
        ((AntipodalKernel.ampCore_eq_iff_antipodal hm QA QB hc w).mp (hamp w hw))
      exact ⟨o, zA, zB, fun _ => hozz⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun hw' => absurd hw' hw⟩
  choose o zA zB hozz using key
  obtain ⟨QA'', hQA''⟩ := exists_diagPhase_append (n := n) (m := m) (h := h + 1 + 1)
    (fun w y => layer (o w) (zA w) y)
  obtain ⟨QB'', hQB''⟩ := exists_diagPhase_append (n := n) (m := m) (h := h + 1 + 1)
    (fun w y => layer (o w) (zB w) y)
  have hrowA : ∀ w : Fin n → ZMod 2, (fun y => QA'.eval (Fin.append w y))
      = layer (fun y1 => QA.eval (Fin.append w y1)) (fun _ => (0 : ZMod (2 ^ m))) :=
    fun w => funext (hQA' w)
  have hrowB : ∀ w : Fin n → ZMod 2, (fun y => QB'.eval (Fin.append w y))
      = layer (fun y1 => QB.eval (Fin.append w y1)) (fun _ => (0 : ZMod (2 ^ m))) :=
    fun w => funext (hQB' w)
  have hrowA'' : ∀ w : Fin n → ZMod 2, (fun y => QA''.eval (Fin.append w y))
      = layer (o w) (zA w) := fun w => funext (hQA'' w)
  have hrowB'' : ∀ w : Fin n → ZMod 2, (fun y => QB''.eval (Fin.append w y))
      = layer (o w) (zB w) := fun w => funext (hQB'' w)
  have keyA : ∀ w : Fin n → ZMod 2, ∃ σ : Equiv.Perm (Fin (h + 1 + 1) → ZMod 2),
      (∃ p ∈ L, w = x₀ + p.X) → ∀ y,
        QA''.eval (Fin.append w y) = QA'.eval (Fin.append w (σ y)) := by
    intro w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · obtain ⟨σ, hσ⟩ := exists_perm_of_cnt (fun y => QA'.eval (Fin.append w y))
        (fun y => QA''.eval (Fin.append w y)) (fun a => by
          rw [hrowA, hrowA'', cnt_layer, cnt_layer]
          exact ((hozz w hw a).1).symm)
      exact ⟨σ, fun _ y => hσ y⟩
    · exact ⟨1, fun hw' => absurd hw' hw⟩
  have keyB : ∀ w : Fin n → ZMod 2, ∃ σ : Equiv.Perm (Fin (h + 1 + 1) → ZMod 2),
      (∃ p ∈ L, w = x₀ + p.X) → ∀ y,
        QB''.eval (Fin.append w y) = QB'.eval (Fin.append w (σ y)) := by
    intro w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · obtain ⟨σ, hσ⟩ := exists_perm_of_cnt (fun y => QB'.eval (Fin.append w y))
        (fun y => QB''.eval (Fin.append w y)) (fun a => by
          rw [hrowB, hrowB'', cnt_layer, cnt_layer]
          exact ((hozz w hw a).2).symm)
      exact ⟨σ, fun _ y => hσ y⟩
    · exact ⟨1, fun hw' => absurd hw' hw⟩
  choose σA hσA using keyA
  choose σB hσB using keyB
  have hsAB : StateEq (⟨m, h + 1, QA, c, L, x₀⟩ : KernelSumState n) ⟨m, h + 1, QB, c, L, x₀⟩ := by
    funext w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · rw [amp_pos (S := (⟨m, h + 1, QA, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_pos (S := (⟨m, h + 1, QB, c, L, x₀⟩ : KernelSumState n)) hw]
      exact (hamp w hw).symm
    · rw [amp_neg (S := (⟨m, h + 1, QA, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_neg (S := (⟨m, h + 1, QB, c, L, x₀⟩ : KernelSumState n)) hw]
  have hB : IsCarrier (⟨m, h + 1, QB, c, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hA hsAB.symm hm hA.2.1 hA.2.2.1
  have hPA : IsCarrier (⟨m, h + 1 + 1, QA', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hA (stateEq_of_carrierRule hpA) hm hA.2.1 hA.2.2.1
  have hPB : IsCarrier (⟨m, h + 1 + 1, QB', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hB (stateEq_of_carrierRule hpB) hm hA.2.1 hA.2.2.1
  have hrA := Relation.EqvGen.mono (fun _ _ hXY => within_of_relabel hPA rfl rfl hXY)
    (relabel_derivable QA' QA'' (c * (Real.sqrt 2 : ℂ)) L x₀ σA hσA)
  have hrB := Relation.EqvGen.mono (fun _ _ hXY => within_of_relabel hPB rfl rfl hXY)
    (relabel_derivable QB' QB'' (c * (Real.sqrt 2 : ℂ)) L x₀ σB hσB)
  have hRA : IsCarrier (⟨m, h + 1 + 1, QA'', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hPA (stateEq_scale_of_eqvGen (eqvGen_of_within hrA)).1 hm hA.2.1
      hA.2.2.1
  have hRB : IsCarrier (⟨m, h + 1 + 1, QB'', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hPB (stateEq_scale_of_eqvGen (eqvGen_of_within hrB)).1 hm hA.2.1
      hA.2.2.1
  have hoff : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y ∉ layerHalf h,
      QB''.eval (Fin.append w y) = QA''.eval (Fin.append w y) := by
    intro w _ y hy
    have h0 : y (Fin.last (h + 1)) = 0 := by
      rcases zmod_two_eq_zero_or_one (y (Fin.last (h + 1))) with h0 | h1
      · exact h0
      · exact absurd (by simp [layerHalf, h1]) hy
    rw [hQA'', hQB'']
    simp only [layer, if_pos h0]
  have hreph : CarrierRule
      (⟨m, h + 1 + 1, QA'', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n)
      ⟨m, h + 1 + 1, QB'', c * (Real.sqrt 2 : ℂ), L, x₀⟩ :=
    CarrierRule.rephase hm QA'' QB'' (c * (Real.sqrt 2 : ℂ)) L x₀ (layerHalf h) (layerPair h)
      (layerPair h) hoff (fun w _ => antipodalOn_layer hm QA'' w _ _ (hQA'' w))
      (fun w _ => antipodalOn_layer hm QB'' w _ _ (hQB'' w))
  have hpA' : Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m) _ _ :=
    Relation.EqvGen.rel _ _ ⟨hpA, ⟨hPA, rfl⟩, ⟨hA, rfl⟩⟩
  have hpB' : Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m) _ _ :=
    Relation.EqvGen.rel _ _ ⟨hpB, ⟨hPB, rfl⟩, ⟨hB, rfl⟩⟩
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpA')
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hrA)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hreph, ⟨hRA, rfl⟩, ⟨hRB, rfl⟩⟩)
        (Relation.EqvGen.trans _ _ _ hrB hpB')))

end Exchange

section Assembly

/-- **The "if" half.** Two nonzero carrier states denoting one state, with a dyadic scale ratio,
are related: lift both to one precision `M ≥ 3` large enough for the ratio's root of unity (R7),
widen both supports to every word and restate them on one support (R3, R2), match heights and
scales, and exchange the antipodal pairs row by row. -/
private theorem eqvGen_of_stateEq {S T : KernelSumState n} (hS : IsCarrier S) (hT : IsCarrier T)
    (hs : StateEq S T) (hd : IsDyadicRatio (T.c / S.c)) : Relation.EqvGen CarrierRule S T := by
  obtain ⟨ζ, k, e, hζ, hr⟩ := hd
  obtain ⟨mS, hgS, QS, cS, LS, xS⟩ := S
  obtain ⟨mT, hgT, QT, cT, LT, xT⟩ := T
  change cT / cS = ζ * (Real.sqrt 2 : ℂ) ^ e at hr
  obtain ⟨M, hMS, hMT, hMk, hM3⟩ : ∃ M, mS ≤ M ∧ mT ≤ M ∧ k ≤ M ∧ 3 ≤ M :=
    ⟨max (max mS mT) (max k 3), by omega, by omega, by omega, by omega⟩
  have hM1 : 1 ≤ M := by omega
  -- Lift both to precision `M` (R7).
  have hlS := CarrierRule.gauge (GaugeStep.liftTo (n := n) M hMS QS cS LS xS)
  have hlT := CarrierRule.gauge (GaugeStep.liftTo (n := n) M hMT QT cT LT xT)
  have hCS1 := isCarrier_of_stateEq hS (stateEq_of_carrierRule hlS) hM1 hS.2.1 hS.2.2.1
  have hCT1 := isCarrier_of_stateEq hT (stateEq_of_carrierRule hlT) hM1 hT.2.1 hT.2.2.1
  -- Widen both supports to every word.
  obtain ⟨jS, h1, Q1, L1, hL1, hC1, hch1'⟩ :=
    exists_full (n - Module.finrank (ZMod 2) (Submodule.map xProj LS)) le_rfl hCS1
  obtain ⟨jT, h2, Q2, L2, hL2, hC2, hch2'⟩ :=
    exists_full (n - Module.finrank (ZMod 2) (Submodule.map xProj LT)) le_rfl hCT1
  have hch1 := eqvGen_of_within hch1'
  have hch2 := eqvGen_of_within hch2'
  -- Restate the second on the first's support.
  have hre := eqvGen_retarget (m := M) Q2 (cT / (Real.sqrt 2 : ℂ) ^ jT) xS xT hL1 hL2
  have hC2' : IsCarrier
      (⟨M, h2, Q2, cT / (Real.sqrt 2 : ℂ) ^ jT, L1, xS⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hC2 (stateEq_scale_of_eqvGen hre).1.symm hM1 hC1.2.1 hC1.2.2.1
  -- The scale ratio at precision `M`.
  obtain ⟨b, hb⟩ := exists_charOf_eq hMk hζ
  have hcS : cS ≠ 0 := c_ne_zero_of_isCarrier hS
  have hcT : cT = ζ * (Real.sqrt 2 : ℂ) ^ e * cS := by
    rw [← hr, div_mul_cancel₀ _ hcS]
  have hratio : cT / (Real.sqrt 2 : ℂ) ^ jT = charOf M b * (cS / (Real.sqrt 2 : ℂ) ^ jS)
      * (Real.sqrt 2 : ℂ) ^ (e + (jS : ℤ) - (jT : ℤ)) := by
    rw [hb, hcT, zpow_sub₀ ofReal_sqrt_two_ne_zero, zpow_add₀ ofReal_sqrt_two_ne_zero, zpow_natCast,
      zpow_natCast]
    field_simp [ofReal_sqrt_two_ne_zero]
  obtain ⟨H, QA, QB, C, hC, hchA, hchB⟩ :=
    exists_match hM3 b (e + (jS : ℤ) - (jT : ℤ)) hratio hC1 hC2'
  -- The chains from the matched states back to the inputs.
  have hA : Relation.EqvGen CarrierRule (⟨M, H + 1, QA, C, L1, xS⟩ : KernelSumState n)
      ⟨mS, hgS, QS, cS, LS, xS⟩ :=
    Relation.EqvGen.trans _ _ _ hchA
      (Relation.EqvGen.trans _ _ _ hch1 (Relation.EqvGen.rel _ _ hlS))
  have hB : Relation.EqvGen CarrierRule (⟨M, H + 1, QB, C, L1, xS⟩ : KernelSumState n)
      ⟨mT, hgT, QT, cT, LT, xT⟩ :=
    Relation.EqvGen.trans _ _ _ hchB
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hre)
        (Relation.EqvGen.trans _ _ _ hch2 (Relation.EqvGen.rel _ _ hlT)))
  have hAB : StateEq (⟨M, H + 1, QA, C, L1, xS⟩ : KernelSumState n)
      ⟨M, H + 1, QB, C, L1, xS⟩ :=
    (stateEq_scale_of_eqvGen hA).1.trans (hs.trans (stateEq_scale_of_eqvGen hB).1.symm)
  have hCA : IsCarrier (⟨M, H + 1, QA, C, L1, xS⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hS (stateEq_scale_of_eqvGen hA).1 hM1 hC1.2.1 hC1.2.2.1
  have hex := eqvGen_of_within <| eqvGen_exchange hM1 QA QB hC L1 xS hCA (fun w hw => by
    have hw' := congrFun hAB w
    rw [amp_pos (S := (⟨M, H + 1, QA, C, L1, xS⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨M, H + 1, QB, C, L1, xS⟩ : KernelSumState n)) hw] at hw'
    exact hw'.symm)
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hA)
    (Relation.EqvGen.trans _ _ _ hex hB)

end Assembly

section Conservativity

/-! ### Conservativity: every step at the states' own precision

The assembly above lifts to a precision `M ≥ 3` large enough for the ratio's root of unity. At the
states' own precision `m` the ratio is already in reach. Two carrier states on one support that
denote one state give, at a free word where they do not vanish, `ζ·√2^f = s_A / s_B` with `s_A`,
`s_B` sums of `2^m`-th roots of unity (`mul_zpow_mem_adjoin`), so `ζ·√2^f` lies in `ℚ(ζ_{2^m})`.
When `f` is even, `ζ` lies there, and is a `2^m`-th root (`rootOfUnity_mem_two_pow`): R1 reaches
it, and unused bits and pads by halving match the heights two at a time. When `f` is odd, at
`m = 1` the field is `ℚ` and `ζ·√2` would be rational, so `√2` would be; at `m ≥ 2` a reversed
rotation by the quarter turn changes the height by one and the root by an eighth root of unity. -/

/-- A step into a carrier state at precision `m`, from a state at precision `m` on the same
Lagrangian, is a step between carrier states at precision `m`. -/
private theorem within_of_step {m : ℕ} {A B : KernelSumState n} (hAB : CarrierRule A B)
    (hB : IsCarrier B) (hAm : A.m = m) (hBm : B.m = m) (hL : A.L = B.L) :
    IsCarrier A ∧ Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m) A B := by
  have hA : IsCarrier A := by
    refine isCarrier_of_stateEq hB (stateEq_of_carrierRule hAB)
      (by rw [hAm, ← hBm]; exact hB.1) ?_ ?_
    · rw [hL]
      exact hB.2.1
    · rw [hL]
      exact hB.2.2.1
  exact ⟨hA, Relation.EqvGen.rel _ _ ⟨hAB, ⟨hA, hAm⟩, ⟨hB, hBm⟩⟩⟩

/-- **One support, at one precision.** `eqvGen_retarget` by a chain between carrier states at
precision `m`. -/
private theorem retarget_within {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    {L L' : Submodule (ZMod 2) (Pauli n)} (x₀ x₀' : Fin n → ZMod 2)
    (hL : Submodule.map xProj L = ⊤) (hL' : Submodule.map xProj L' = ⊤)
    (hstab : IsStabilizer L) (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L)
    (hS' : IsCarrier (⟨m, h, Q, c, L', x₀'⟩ : KernelSumState n)) :
    IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        (⟨m, h, Q, c, L', x₀'⟩ : KernelSumState n) ⟨m, h, Q, c, L, x₀⟩ := by
  have h3 : CarrierRule (⟨m, h, Q, c, L', x₀'⟩ : KernelSumState n) ⟨m, h, Q, c, L, x₀'⟩ :=
    CarrierRule.gauge (GaugeStep.congrXProj Q c L' L x₀' (hL'.trans hL.symm))
  have hv : x₀' - x₀ ∈ Submodule.map xProj L := by
    rw [hL]
    exact Submodule.mem_top
  have h2 := CarrierRule.gauge (GaugeStep.offsetAddMem (n := n) Q c L x₀ hv)
  have hx : x₀ + (x₀' - x₀) = x₀' := by abel
  rw [hx] at h2
  have hmid : IsCarrier (⟨m, h, Q, c, L, x₀'⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hS' (stateEq_of_carrierRule h3).symm hS'.1 hstab horth
  have hend : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hmid (stateEq_of_carrierRule h2).symm hS'.1 hstab horth
  exact ⟨hend, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨h3, ⟨hS', rfl⟩, ⟨hmid, rfl⟩⟩)
    (Relation.EqvGen.rel _ _ ⟨h2, ⟨hmid, rfl⟩, ⟨hend, rfl⟩⟩)⟩

/-- **Two bits higher, the same scale.** An unused bit (scale `c/√2`) and a pad by halving (scale
`c`), `t` times. -/
private theorem exists_raise_two {m h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) (t : ℕ) {H : ℕ}
    (hH : H = h + 2 * t) :
    ∃ Q' : DiagPhase (n + H) m,
      IsCarrier (⟨m, H, Q', c, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  subst hH
  induction t with
  | zero =>
    rw [Nat.mul_zero, Nat.add_zero]
    exact ⟨Q, hS, Relation.EqvGen.refl _⟩
  | succ t ih =>
    obtain ⟨Qt, hCt, hcht⟩ := ih
    obtain ⟨Q1, hC1, hch1⟩ := exists_unusedBit hCt
    obtain ⟨Q2, hC2, hch2⟩ := exists_pad hC1
    rw [div_mul_cancel₀ c ofReal_sqrt_two_ne_zero] at hC2 hch2
    rw [show h + 2 * (t + 1) = h + 2 * t + 1 + 1 by ring]
    exact ⟨Q2, hC2, Relation.EqvGen.trans _ _ _ hch2 (Relation.EqvGen.trans _ _ _ hch1 hcht)⟩

/-- **The ratio lies in `ℚ(ζ_{2^m})`.** Two states at precision `m` on one support, the first a
carrier state, denoting one state with scales `c_B = ζ·c_A·√2^e`: at a free word where the first
does not vanish, `ζ·√2^{e + h_A − h_B}` is the quotient of their sums of roots of unity. -/
private theorem mul_zpow_mem_adjoin {m hA hB : ℕ} {QA : DiagPhase (n + hA) m}
    {QB : DiagPhase (n + hB) m} {cA cB ζ : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} (e : ℤ)
    (hSA : IsCarrier (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n))
    (hAB : StateEq (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n) ⟨m, hB, QB, cB, L, x₀⟩)
    (hcB : cB = ζ * cA * (Real.sqrt 2 : ℂ) ^ e) :
    ζ * (Real.sqrt 2 : ℂ) ^ (e + hA - hB) ∈ IntermediateField.adjoin ℚ {zeta m} := by
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
  have hcA : cA ≠ 0 := c_ne_zero_of_isCarrier hSA
  obtain ⟨w, hw⟩ : ∃ w, amp (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n) w ≠ 0 := by
    by_contra hc
    exact hSA.2.2.2 (funext fun w => not_not.mp fun hw => hc ⟨w, hw⟩)
  have hsupp : ∃ p ∈ L, w = x₀ + p.X := by
    by_contra hc
    exact hw (amp_neg (S := (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n)) hc)
  have hAB' := congrFun hAB w
  rw [amp_pos (S := (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n)) hsupp,
    amp_pos (S := (⟨m, hB, QB, cB, L, x₀⟩ : KernelSumState n)) hsupp] at hAB'
  rw [amp_pos (S := (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n)) hsupp] at hw
  change ampCore m hA QA cA w = ampCore m hB QB cB w at hAB'
  change ampCore m hA QA cA w ≠ 0 at hw
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf] at hAB'
  rw [ampCore_eq_sum_charOf] at hw
  have hmemS : ∀ {N : ℕ} (P : DiagPhase (n + N) m),
      (∑ y : Fin N → ZMod 2, charOf m (P.eval (Fin.append w y)))
        ∈ IntermediateField.adjoin ℚ {zeta m} := by
    intro N P
    refine sum_mem fun y _ => ?_
    rw [charOf_eq_zeta_pow]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ (zeta m)) _
  have hA_mem := hmemS QA
  have hB_mem := hmemS QB
  set sA := ∑ y : Fin hA → ZMod 2, charOf m (QA.eval (Fin.append w y)) with hsA
  set sB := ∑ y : Fin hB → ZMod 2, charOf m (QB.eval (Fin.append w y)) with hsB
  have hsA0 : sA ≠ 0 := right_ne_zero_of_mul hw
  have hsB0 : sB ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hAB'
    exact hw hAB'
  have hval : ζ * (Real.sqrt 2 : ℂ) ^ (e + hA - hB) = sA / sB := by
    rw [eq_div_iff hsB0, zpow_sub₀ hr, zpow_add₀ hr, zpow_natCast, zpow_natCast]
    rw [hcB] at hAB'
    calc ζ * ((Real.sqrt 2 : ℂ) ^ e * (Real.sqrt 2 : ℂ) ^ hA / (Real.sqrt 2 : ℂ) ^ hB) * sB
        = (Real.sqrt 2 : ℂ) ^ hA / cA
          * (ζ * cA * (Real.sqrt 2 : ℂ) ^ e / (Real.sqrt 2 : ℂ) ^ hB * sB) := by
          field_simp
      _ = (Real.sqrt 2 : ℂ) ^ hA / cA * (cA / (Real.sqrt 2 : ℂ) ^ hA * sA) := by rw [hAB']
      _ = sA := by field_simp
  rw [hval]
  exact div_mem hA_mem hB_mem

/-- **Matching at one precision, with the ratio's root at that precision** and the heights of
one parity: `e` unused bits on the second carrier state, R1 read backwards on the first, and
unused bits with pads by halving, two at a time, on both. -/
private theorem exists_match_even {m hA hB : ℕ} {QA : DiagPhase (n + hA) m}
    {QB : DiagPhase (n + hB) m} {cA cB : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} (b : ZMod (2 ^ m)) (e : ℕ)
    (hcB : cB = charOf m b * cA * (Real.sqrt 2 : ℂ) ^ e) (t : ℕ) (ht : hA + hB + e = 2 * t)
    (hSA : IsCarrier (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n))
    (hSB : IsCarrier (⟨m, hB, QB, cB, L, x₀⟩ : KernelSumState n)) :
    ∃ (H : ℕ) (QA' QB' : DiagPhase (n + (H + 1)) m) (C : ℂ),
      IsCarrier (⟨m, H + 1, QA', C, L, x₀⟩ : KernelSumState n) ∧
      IsCarrier (⟨m, H + 1, QB', C, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H + 1, QA', C, L, x₀⟩ ⟨m, hA, QA, cA, L, x₀⟩ ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H + 1, QB', C, L, x₀⟩ ⟨m, hB, QB, cB, L, x₀⟩ := by
  obtain ⟨QB1, hCB1, hchB1⟩ := exists_unused_iter e hSB
  have heq : cB / (Real.sqrt 2 : ℂ) ^ e = charOf m b * cA := by
    rw [hcB, mul_div_assoc, div_self (pow_ne_zero _ ofReal_sqrt_two_ne_zero), mul_one]
  rw [heq] at hCB1 hchB1
  obtain ⟨hCA1, hchA1⟩ := within_of_step (carrierRule_addC QA cA L x₀ b) hSA rfl rfl rfl
  obtain ⟨QA2, hCA2, hchA2⟩ :=
    exists_raise_two hCA1 (hB + e + 1) (H := hA + 2 * (hB + e) + 1 + 1) (by ring)
  obtain ⟨QB2, hCB2, hchB2⟩ :=
    exists_raise_two hCB1 (t + 1) (H := hA + 2 * (hB + e) + 1 + 1) (by omega)
  exact ⟨hA + 2 * (hB + e) + 1, QA2, QB2, charOf m b * cA, hCA2, hCB2,
    Relation.EqvGen.trans _ _ _ hchA2 hchA1, Relation.EqvGen.trans _ _ _ hchB2 hchB1⟩

/-- **Matching at one precision, heights of one parity.** When `e + h_A − h_B` is even, the
ratio's root of unity is a `2^m`-th root (`rootOfUnity_mem_two_pow`), and `exists_match_even`
applies to the two carrier states in one order or the other. -/
private theorem exists_match_at {m hA hB : ℕ} {QA : DiagPhase (n + hA) m}
    {QB : DiagPhase (n + hB) m} {cA cB ζ : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {k : ℕ} (hζ : ζ ^ 2 ^ k = 1) (e g : ℤ) (hg : e + hA - hB = 2 * g)
    (hcB : cB = ζ * cA * (Real.sqrt 2 : ℂ) ^ e)
    (hSA : IsCarrier (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n))
    (hSB : IsCarrier (⟨m, hB, QB, cB, L, x₀⟩ : KernelSumState n))
    (hAB : StateEq (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n) ⟨m, hB, QB, cB, L, x₀⟩) :
    ∃ (H : ℕ) (QA' QB' : DiagPhase (n + (H + 1)) m) (C : ℂ),
      IsCarrier (⟨m, H + 1, QA', C, L, x₀⟩ : KernelSumState n) ∧
      IsCarrier (⟨m, H + 1, QB', C, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H + 1, QA', C, L, x₀⟩ ⟨m, hA, QA, cA, L, x₀⟩ ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H + 1, QB', C, L, x₀⟩ ⟨m, hB, QB, cB, L, x₀⟩ := by
  have hm : 1 ≤ m := hSA.1
  have hmem := mul_zpow_mem_adjoin e hSA hAB hcB
  have hr2 : (Real.sqrt 2 : ℂ) ^ (2 : ℤ) = 2 := by
    rw [zpow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hg, zpow_mul, hr2] at hmem
  have h2mem : (2 : ℂ) ^ g ∈ IntermediateField.adjoin ℚ {zeta m} :=
    zpow_mem (ofNat_mem _ 2) g
  have hζmem : ζ ∈ IntermediateField.adjoin ℚ {zeta m} := by
    have h := div_mem hmem h2mem
    rwa [mul_div_assoc, div_self (zpow_ne_zero g two_ne_zero), mul_one] at h
  have hζm := AntipodalKernel.rootOfUnity_mem_two_pow hm (isPrimitiveRoot_zeta m) hζ hζmem
  obtain ⟨b, hb⟩ := exists_charOf_eq le_rfl hζm
  rw [← hb] at hcB
  rcases le_or_gt 0 e with he | he
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le he
    rw [zpow_natCast] at hcB
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = g + hB := ⟨(g + hB).toNat, Int.toNat_of_nonneg (by omega)⟩
    exact exists_match_even b j hcB t (by omega) hSA hSB
  · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -e by omega)
    have hcA : cA = charOf m (-b) * cB * (Real.sqrt 2 : ℂ) ^ j := by
      have he' : e = -(j : ℤ) := by omega
      rw [hcB, he', zpow_neg, zpow_natCast]
      have h1 : charOf m (-b) * charOf m b = 1 := by
        rw [← charOf_add, neg_add_cancel, charOf_zero]
      have h2 : ((Real.sqrt 2 : ℂ) ^ j)⁻¹ * (Real.sqrt 2 : ℂ) ^ j = 1 :=
        inv_mul_cancel₀ (pow_ne_zero _ ofReal_sqrt_two_ne_zero)
      linear_combination (-(cA * charOf m (-b) * charOf m b) * h2) - cA * h1
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = hA - g := ⟨((hA : ℤ) - g).toNat,
      Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨H, QB', QA', C, hCB', hCA', hchB, hchA⟩ :=
      exists_match_even (-b) j hcA t (by omega) hSB hSA
    exact ⟨H, QA', QB', C, hCA', hCB', hchA, hchB⟩

/-- **At `m = 1` the heights have one parity.** A root of unity times an odd power of `√2` is not
rational, and `ℚ(ζ_2) = ℚ`: `√2` is irrational. -/
private theorem not_mem_adjoin_zeta_one {ζ : ℂ} {k : ℕ} (hζ : ζ ^ 2 ^ k = 1) (g : ℤ) :
    ζ * (Real.sqrt 2 : ℂ) ^ (2 * g + 1) ∉ IntermediateField.adjoin ℚ {zeta 1} := by
  intro hmem
  have hbot : IntermediateField.adjoin ℚ {zeta 1} = ⊥ := by
    rw [IntermediateField.adjoin_simple_eq_bot_iff]
    have h : zeta 1 = -1 := (isPrimitiveRoot_zeta 1).eq_neg_one_of_two_right
    rw [h]
    exact neg_mem (one_mem _)
  rw [hbot, IntermediateField.mem_bot] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hζn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (by positivity)
  have hn := congrArg norm hq
  rw [norm_mul, norm_zpow, hζn, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), zpow_add₀ (by positivity), zpow_mul, zpow_one,
    zpow_two, Real.mul_self_sqrt (by norm_num)] at hn
  simp only [eq_ratCast, Complex.norm_ratCast] at hn
  apply irrational_sqrt_two
  refine ⟨|q| / 2 ^ g, ?_⟩
  push_cast
  rw [hn]
  field_simp

/-- **Matching at one precision.** Two carrier states at precision `m` on one support denoting one
state, with a dyadic scale ratio, have carrier states at one height and one scale, each related to
its own by a chain between carrier states at precision `m`. -/
private theorem exists_match_within {m hA hB : ℕ} {QA : DiagPhase (n + hA) m}
    {QB : DiagPhase (n + hB) m} {cA cB ζ : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {k : ℕ} (hζ : ζ ^ 2 ^ k = 1) (e : ℤ)
    (hcB : cB = ζ * cA * (Real.sqrt 2 : ℂ) ^ e)
    (hSA : IsCarrier (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n))
    (hSB : IsCarrier (⟨m, hB, QB, cB, L, x₀⟩ : KernelSumState n))
    (hAB : StateEq (⟨m, hA, QA, cA, L, x₀⟩ : KernelSumState n) ⟨m, hB, QB, cB, L, x₀⟩) :
    ∃ (H : ℕ) (QA' QB' : DiagPhase (n + (H + 1)) m) (C : ℂ),
      IsCarrier (⟨m, H + 1, QA', C, L, x₀⟩ : KernelSumState n) ∧
      IsCarrier (⟨m, H + 1, QB', C, L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H + 1, QA', C, L, x₀⟩ ⟨m, hA, QA, cA, L, x₀⟩ ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, H + 1, QB', C, L, x₀⟩ ⟨m, hB, QB, cB, L, x₀⟩ := by
  have hm : 1 ≤ m := hSA.1
  obtain ⟨g, hg | hg⟩ := Int.even_or_odd' (e + hA - hB)
  · exact exists_match_at hζ e g hg hcB hSA hSB hAB
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · exfalso
    obtain rfl : m = 1 := by omega
    have hmem := mul_zpow_mem_adjoin e hSA hAB hcB
    rw [hg] at hmem
    exact not_mem_adjoin_zeta_one hζ g hmem
  -- A reversed rotation by the quarter turn on the second carrier state.
  set a : ZMod (2 ^ m) := (2 : ZMod (2 ^ m)) ^ (m - 2) with ha_def
  have ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1) := by
    rw [ha_def, ← pow_succ']
    congr 1
    omega
  obtain ⟨hχ, QB1, hCB1, hchB1⟩ := exists_unrotate hSB ha
  set ω : ℂ := (1 + charOf m a) / (Real.sqrt 2 : ℂ) with hω_def
  have htop : charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
    simpa using charOf_two_pow_mul hm 1
  have hx2 : charOf m a * charOf m a = -1 := by
    rw [← charOf_add, ← two_mul, ha, htop]
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := sqrt_two_sq_complex
  have hω2 : ω ^ 2 = charOf m a := by
    rw [hω_def, div_pow, hs2, div_eq_iff (show (2 : ℂ) ≠ 0 by norm_num)]
    linear_combination hx2
  have hω8 : ω ^ 2 ^ 3 = 1 := by
    have h8 : ω ^ 2 ^ 3 = ((ω ^ 2) ^ 2) ^ 2 := by ring
    rw [h8, hω2, show charOf m a ^ 2 = -1 by rw [sq, hx2]]
    norm_num
  have hζ' : (ζ * ω⁻¹) ^ 2 ^ (k + 3) = 1 := by
    rw [mul_pow, inv_pow, pow_add, pow_mul, hζ, one_pow, one_mul, mul_comm, pow_mul, hω8,
      one_pow, inv_one]
  have hcB1 : cB * (Real.sqrt 2 : ℂ) / (1 + charOf m a)
      = ζ * ω⁻¹ * cA * (Real.sqrt 2 : ℂ) ^ e := by
    rw [hcB, hω_def, inv_div]
    field_simp
  rw [hcB1] at hCB1 hchB1
  have hAB1 := hAB.trans (stateEq_scale_of_eqvGen (eqvGen_of_within hchB1)).1.symm
  obtain ⟨H, QA', QB', C, hCA', hCB', hchA, hchB⟩ :=
    exists_match_at hζ' e g (by push_cast; omega) rfl hSA hCB1 hAB1
  exact ⟨H, QA', QB', C, hCA', hCB', hchA, Relation.EqvGen.trans _ _ _ hchB hchB1⟩

end Conservativity

/-- **Completeness at every precision.** Two nonzero carrier states, at any precisions, are related
by the equivalence `CarrierRule` generates exactly when they denote the same state and the ratio of
their scales is dyadic (decision D9). -/
theorem rewrite_complete {S T : KernelSumState n} (hS : IsCarrier S) (hT : IsCarrier T) :
    Relation.EqvGen CarrierRule S T ↔ StateEq S T ∧ IsDyadicRatio (T.c / S.c) := by
  constructor
  · intro hST
    obtain ⟨hs, r, hr, hc⟩ := stateEq_scale_of_eqvGen hST
    refine ⟨hs, ?_⟩
    rw [hc, mul_div_assoc, div_self (c_ne_zero_of_isCarrier hS), mul_one]
    exact hr
  · rintro ⟨hs, hd⟩
    exact eqvGen_of_stateEq hS hT hs hd

/-- **Conservativity.** Two related carrier states at precision `m` are related by a chain of steps
every one of which is between carrier states at precision `m`. -/
theorem rewrite_conservative {m : ℕ} {S T : KernelSumState n} (hS : IsCarrier S)
    (hT : IsCarrier T) (hSm : S.m = m) (hTm : T.m = m) (hST : Relation.EqvGen CarrierRule S T) :
    Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m) S T := by
  obtain ⟨hs, r, hd, hc⟩ := stateEq_scale_of_eqvGen hST
  obtain ⟨ζ, k, e, hζ, rfl⟩ := hd
  obtain ⟨mS, hgS, QS, cS, LS, xS⟩ := S
  obtain ⟨mT, hgT, QT, cT, LT, xT⟩ := T
  change mS = m at hSm
  change mT = m at hTm
  subst hSm hTm
  change cT = ζ * (Real.sqrt 2 : ℂ) ^ e * cS at hc
  -- Widen both supports to every word, and restate the second on the first's support.
  obtain ⟨jS, h1, Q1, L1, hL1, hC1, hch1⟩ :=
    exists_full (n - Module.finrank (ZMod 2) (Submodule.map xProj LS)) le_rfl hS
  obtain ⟨jT, h2, Q2, L2, hL2, hC2, hch2⟩ :=
    exists_full (n - Module.finrank (ZMod 2) (Submodule.map xProj LT)) le_rfl hT
  obtain ⟨hC2', hre⟩ := retarget_within Q2 (cT / (Real.sqrt 2 : ℂ) ^ jT) xS xT hL1 hL2
    hC1.2.1 hC1.2.2.1 hC2
  -- The scale ratio, and one state.
  have hratio : cT / (Real.sqrt 2 : ℂ) ^ jT = ζ * (cS / (Real.sqrt 2 : ℂ) ^ jS)
      * (Real.sqrt 2 : ℂ) ^ (e + (jS : ℤ) - (jT : ℤ)) := by
    rw [hc, zpow_sub₀ ofReal_sqrt_two_ne_zero, zpow_add₀ ofReal_sqrt_two_ne_zero, zpow_natCast,
      zpow_natCast]
    field_simp [ofReal_sqrt_two_ne_zero]
  have hAB : StateEq
      (⟨mT, h1, Q1, cS / (Real.sqrt 2 : ℂ) ^ jS, L1, xS⟩ : KernelSumState n)
      ⟨mT, h2, Q2, cT / (Real.sqrt 2 : ℂ) ^ jT, L1, xS⟩ :=
    (stateEq_scale_of_eqvGen (eqvGen_of_within hch1)).1.trans
      (hs.trans ((stateEq_scale_of_eqvGen (eqvGen_of_within hch2)).1.symm.trans
        (stateEq_scale_of_eqvGen (eqvGen_of_within hre)).1))
  -- Match heights and scales at precision `m`, and exchange the antipodal pairs.
  obtain ⟨H, QA, QB, C, hCA, hCB, hchA, hchB⟩ :=
    exists_match_within hζ (e + (jS : ℤ) - (jT : ℤ)) hratio hC1 hC2' hAB
  have hAB' : StateEq (⟨mT, H + 1, QA, C, L1, xS⟩ : KernelSumState n)
      ⟨mT, H + 1, QB, C, L1, xS⟩ :=
    (stateEq_scale_of_eqvGen (eqvGen_of_within hchA)).1.trans
      (hAB.trans (stateEq_scale_of_eqvGen (eqvGen_of_within hchB)).1.symm)
  have hex := eqvGen_exchange hS.1 QA QB (c_ne_zero_of_isCarrier hCA) L1 xS hCA (fun w hw => by
    have hw' := congrFun hAB' w
    rw [amp_pos (S := (⟨mT, H + 1, QA, C, L1, xS⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨mT, H + 1, QB, C, L1, xS⟩ : KernelSumState n)) hw] at hw'
    exact hw'.symm)
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hch1)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hchA)
      (Relation.EqvGen.trans _ _ _ hex
        (Relation.EqvGen.trans _ _ _ hchB
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hre) hch2))))

end FTQCLib.Frame.Walkthrough

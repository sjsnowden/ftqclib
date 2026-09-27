/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.IdempotentPolynomial

/-!
# Acceptance checks for `ECCLib.IdempotentPolynomial`

**Axiom sweep.** Every headline result, the axiom list written out.

**The agreement row.** Lean core reads a bit vector's two's-complement value a second way, as the
balanced residue `Int.bmod x.toNat (2^w)` (`BitVec.toInt_eq_toNat_bmod`). The linear form
`∑ twosCoeff w k · bitₖ` must equal it; the row derives that equality from
`toInt_eq_sum_twosCoeff` and core's lemma, two independent readings of `toInt`.

**Kernel rows.** At width 3 all eight bit vectors are checked by `decide`, against the linear
form and against the square expansion written out term by term.

**Discriminating rows.** The idempotence hypothesis carries the square identity: at `x = 2` over
`ℕ` the identity is false. The sign weight carries the two's-complement form: with the unsigned
weight `2^k` on the top bit the form gives `7`, not `toInt = −1`, at `7#3`.
-/

namespace ECCLib

/-! ## Axiom sweep -/

/-- info: 'ECCLib.sq_sum_mul_of_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sq_sum_mul_of_idem

/-- info: 'ECCLib.ofBits_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofBits_eq_sum

/-- info: 'ECCLib.toNat_eq_sum_getLsbD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toNat_eq_sum_getLsbD

/-- info: 'ECCLib.toInt_eq_sum_twosCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms toInt_eq_sum_twosCoeff

/-- info: 'ECCLib.twosComplement_sq_expand' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twosComplement_sq_expand

/-! ## The agreement row -/

/-- The linear form equals core's balanced-residue reading of the value. -/
example {w : ℕ} (x : BitVec w) :
    ∑ k : Fin w, twosCoeff w k * ((x.getLsbD k).toNat : ℤ) = Int.bmod x.toNat (2 ^ w) := by
  rw [← toInt_eq_sum_twosCoeff, BitVec.toInt_eq_toNat_bmod]

/-! ## Kernel rows, width 3 -/

/-- The linear form at width 3, every bit vector. -/
example : ∀ x : BitVec 3, x.toInt
    = twosCoeff 3 0 * ((x.getLsbD 0).toNat : ℤ) + twosCoeff 3 1 * ((x.getLsbD 1).toNat : ℤ)
      + twosCoeff 3 2 * ((x.getLsbD 2).toNat : ℤ) := by
  decide

/-- The weights at width 3 are `1, 2, −4`. -/
example : (twosCoeff 3 0, twosCoeff 3 1, twosCoeff 3 2) = (1, 2, -4) := by decide

/-- The square at width 3, every bit vector: `toInt² = b₀ + 4b₁ + 16b₂ + 2·(2b₀b₁ − 4b₀b₂ − 8b₁b₂)`,
the diagonal `cₖ²` and each unordered pair's `2cⱼcₖ`. -/
example : ∀ x : BitVec 3, x.toInt ^ 2
    = ((x.getLsbD 0).toNat : ℤ) + 4 * (x.getLsbD 1).toNat + 16 * (x.getLsbD 2).toNat
      + 2 * (2 * (x.getLsbD 0).toNat * (x.getLsbD 1).toNat
        - 4 * (x.getLsbD 0).toNat * (x.getLsbD 2).toNat
        - 8 * (x.getLsbD 1).toNat * (x.getLsbD 2).toNat) := by
  decide

/-! ## Discriminating rows -/

/-- Without idempotence the square identity fails: one variable, `c = 1`, `x = 2` over `ℕ`
(`(1·2)² = 4`, the right side `1²·2 = 2`; the off-diagonal of a singleton is empty). -/
example : ((1 : ℕ) * 2) ^ 2 ≠ 1 ^ 2 * 2 := by decide

/-- With the unsigned weight `2^k` on every bit the form reads `toNat`, not `toInt`: at `7#3`
it gives `7` while `toInt = −1`. -/
example : (7#3).toInt = -1 ∧
    (∑ k : Fin 3, (2 : ℤ) ^ (k : ℕ) * (((7#3).getLsbD k).toNat : ℤ)) = 7 := by
  decide

end ECCLib

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Field.ZMod

set_option linter.unusedSectionVars false

/-! # Phase polynomials for the standard level-3 gates

The Cui–Gottesman–Krishna framework characterises diagonal hierarchy
elements by their phase polynomial: a polynomial
`P ∈ (ZMod (2^m))[j_1, ..., j_n]` represents the diagonal unitary
`U_P = diag(ξ^{P(v)})` with `ξ = exp(2πi / 2^m)`. The Clifford-hierarchy
level of `U_P` is `(m - 1) + totalDegree(P)`.

This file records the standard level-3 diagonal gates as phase
polynomials and computes their levels:

* `tGatePoly i` — the T gate on qubit `i`. Precision `m = 3`,
  polynomial `j_i`, total degree 1, level `2 + 1 = 3`.
* `cczPoly i j k` — the CCZ gate on three distinct qubits. Precision
  `m = 1`, polynomial `j_i · j_j · j_k`, total degree 3, level
  `0 + 3 = 3`.

Both definitions are noncomputable wrappers over Mathlib's
`MvPolynomial.X`. The `level` is verified using
`MvPolynomial.totalDegree_X` from Mathlib.

The CCNOT gate is *not* in this file because it is non-diagonal:
`CCNOT = (I⊗I⊗H) · CCZ · (I⊗I⊗H)`. Its level-3 membership follows
from the level-3 membership of CCZ proved here, combined with the
Clifford-conjugation closure wrapper in `FTQCLib/Hierarchy/Wrapper.lean`.
-/

namespace FTQCLib.Hierarchy

namespace DiagPhase

/-- The phase polynomial for the T gate on qubit `i`: the single
variable `j_i` viewed over the precision-3 ring `ZMod 8`. The
corresponding diagonal unitary is `T_i = diag(1, exp(2πi/8))` on
qubit `i` (tensored with identity elsewhere). -/
noncomputable def tGatePoly {n : ℕ} (i : Fin n) : DiagPhase n 3 :=
  MvPolynomial.X i

/-- The T gate polynomial has total degree 1. -/
@[simp]
theorem tGatePoly_totalDegree {n : ℕ} (i : Fin n) :
    (tGatePoly i).totalDegree = 1 := by
  unfold tGatePoly
  haveI : Fact (1 < 2^3) := ⟨by norm_num⟩
  exact MvPolynomial.totalDegree_X i

/-- The T gate sits at level 3 of the Clifford hierarchy in the
polynomial-phase framework: `level (tGatePoly i) = (3 - 1) + 1 = 3`. -/
@[simp]
theorem tGatePoly_level {n : ℕ} (i : Fin n) :
    (tGatePoly i).level = 3 := by
  unfold level
  rw [tGatePoly_totalDegree]

/-- The phase polynomial for the CCZ gate on three qubits
`i, j, k : Fin n`: the cubic monomial `j_i · j_j · j_k` viewed over
the precision-1 ring `ZMod 2 = F_2`. The corresponding diagonal
unitary applies a `-1` phase exactly when all three qubits are in
state `1`. -/
noncomputable def cczPoly {n : ℕ} (i j k : Fin n) : DiagPhase n 1 :=
  MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X k

/-- The phase polynomial for the dyadic-angle `Z`-rotation
`R_z(2π / 2^m)` on qubit `i`: the single variable `j_i` viewed over
the precision-`m` ring `ZMod (2^m)`. Specialises to `Z` at `m = 1`,
`S` at `m = 2`, `T` at `m = 3`, and `T^{1/2}` at `m = 4`. -/
noncomputable def rzGatePoly {n : ℕ} (i : Fin n) (m : ℕ) : DiagPhase n m :=
  MvPolynomial.X i

/-- The `R_z(2π/2^m)` phase polynomial has total degree 1. -/
@[simp]
theorem rzGatePoly_totalDegree {n : ℕ} (i : Fin n) (m : ℕ)
    [Fact (1 < 2 ^ m)] :
    (rzGatePoly i m).totalDegree = 1 := by
  unfold rzGatePoly
  exact MvPolynomial.totalDegree_X i

/-- The `R_z(2π/2^m)` gate sits at level `m` of the Clifford
hierarchy: level = `(m - 1) + 1 = m`. This is the parametric
extension of `tGatePoly_level` (the `m = 3` case). -/
@[simp]
theorem rzGatePoly_level {n : ℕ} (i : Fin n) (m : ℕ) [Fact (1 < 2 ^ m)]
    (hm : 1 ≤ m) :
    (rzGatePoly i m).level = m := by
  unfold level
  rw [rzGatePoly_totalDegree]
  omega

/-- The CCZ gate polynomial has total degree 3. Proved via
`totalDegree_mul_of_isDomain` (`ZMod 2 = F_2` is an integral domain)
applied twice to chain `X i`, `X j`, `X k`. Each `X _` has total
degree 1 (`MvPolynomial.totalDegree_X`) and is nonzero
(`MvPolynomial.X_ne_zero`); products of distinct or repeated `X _`
remain nonzero. -/
@[simp]
theorem cczPoly_totalDegree {n : ℕ} (i j k : Fin n) :
    (cczPoly i j k).totalDegree = 3 := by
  unfold cczPoly
  -- ZMod (2^1) = ZMod 2 is a field (2 is prime), hence an integral
  -- domain, hence NoZeroDivisors lifts to MvPolynomial via the
  -- Mathlib instance.
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (1 < 2^1) := ⟨by norm_num⟩
  haveI : NoZeroDivisors (ZMod (2^1)) := by
    change NoZeroDivisors (ZMod 2)
    infer_instance
  haveI : NoZeroDivisors (DiagPhase n 1) :=
    inferInstanceAs (NoZeroDivisors (MvPolynomial (Fin n) (ZMod (2^1))))
  -- totalDegree (X i * X j * X k) = totalDegree X i + totalDegree X j + totalDegree X k
  --                                = 1 + 1 + 1 = 3
  have h1 : (MvPolynomial.X j * MvPolynomial.X k : DiagPhase n 1).totalDegree =
            (MvPolynomial.X j : DiagPhase n 1).totalDegree
            + (MvPolynomial.X k : DiagPhase n 1).totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain
      (MvPolynomial.X_ne_zero j) (MvPolynomial.X_ne_zero k)
  -- Reassociate (X i * X j) * X k = X i * (X j * X k) via `ring`.
  have hassoc : (MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X k
                  : DiagPhase n 1)
              = MvPolynomial.X i * (MvPolynomial.X j * MvPolynomial.X k) := by ring
  rw [hassoc]
  rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero i)
        (mul_ne_zero (MvPolynomial.X_ne_zero j) (MvPolynomial.X_ne_zero k))]
  rw [h1]
  rw [MvPolynomial.totalDegree_X i, MvPolynomial.totalDegree_X j,
      MvPolynomial.totalDegree_X k]

/-- The CCZ gate sits at level 3 of the Clifford hierarchy in the
polynomial-phase framework: `level (cczPoly i j k) = (1 - 1) + 3 = 3`. -/
@[simp]
theorem cczPoly_level {n : ℕ} (i j k : Fin n) :
    (cczPoly i j k).level = 3 := by
  unfold level
  rw [cczPoly_totalDegree]

/-- The `S` exponent at precision `m ≥ 2`: the phase `i^{w_i}`. At `m = 1` the coefficient
`2^{m−2}` is `2^0 = 1` (natural-number subtraction), so the polynomial is `X i`, the `Z`
exponent. -/
noncomputable def sGate (m : ℕ) (i : Fin n) : DiagPhase n m :=
  MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 2)) * MvPolynomial.X i

/-- The `CZ` exponent: the phase `(−1)^{w_i w_j}`; at `i = j` the square `X_i²`, which evaluates as
the `Z` exponent. -/
noncomputable def czGate (m : ℕ) (i j : Fin n) : DiagPhase n m :=
  MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * (MvPolynomial.X i * MvPolynomial.X j)

/-- The CS gate phase polynomial: `X i * X j` at precision 2 (phase `i^{v_i v_j}`), a level-three
exponent (`csGate_exact_level`, `FTQCLib/Hilbert/CGKExactness.lean`). -/
noncomputable def csPoly (i j : Fin n) : DiagPhase n 2 :=
  MvPolynomial.X i * MvPolynomial.X j

/-- The `S` exponent's value on a binary point. -/
theorem sGate_eval (m : ℕ) (i : Fin n) (v : Fin n → ZMod 2) :
    (sGate m i).eval v = (2 : ZMod (2 ^ m)) ^ (m - 2) * ((v i).val : ZMod (2 ^ m)) := by
  unfold sGate
  rw [eval_mul, eval_C, eval_X]

/-- The `CZ` exponent's value on a binary point. -/
theorem czGate_eval (m : ℕ) (i j : Fin n) (v : Fin n → ZMod 2) :
    (czGate m i j).eval v =
      (2 : ZMod (2 ^ m)) ^ (m - 1) * (((v i).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m))) := by
  unfold czGate
  rw [eval_mul, eval_C, eval_mul, eval_X, eval_X]

end DiagPhase

end FTQCLib.Hierarchy

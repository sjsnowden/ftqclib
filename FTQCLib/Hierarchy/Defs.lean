/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.ZMod.Basic

set_option linter.unusedSectionVars false

/-! # Diagonal hierarchy elements as polynomial phase functions

A diagonal unitary on `n` qubits is determined by a phase function
`θ : (F₂)ⁿ → ZMod (2^m)`. Concretely, the diagonal unitary `U_P` is

  U_P = diag( ξ^{P(v)} : v ∈ (F₂)ⁿ ),  ξ = exp(2πi / 2^m),

for a polynomial `P` with coefficients in `ZMod (2^m)`. The
Cui–Gottesman–Krishna classification (their Theorem 3 specialised to
qubits, p = 2) states that the level of `U_P` in the Clifford
hierarchy is exactly

  k = (m − 1) + totalDegree(P).

This file introduces the polynomial-phase data type `DiagPhase n m`,
basic operations (evaluation on binary vectors, level, discrete partial
derivative), and a thin layer of utility lemmas.

The connection to the `F₂`-symplectic framework of chapters 1–2:

* Inputs stay in `(F₂)ⁿ = (ZMod 2)ⁿ`, exactly the X- or Z-sector of
  `Pauli n`.
* The output ring `ZMod (2^m)` is a 2-adic refinement of `F₂` via the
  canonical embedding `ZMod 2 ↪ ZMod 4 ↪ ZMod 8 ↪ ⋯`.
* Diagonal Pauli `Z_i` is `U_P` for `P = j_i` over `ZMod 2` (precision
  `m = 1`, degree 1, level 1). Diagonal Clifford `S_i` is `U_P` for
  `P = j_i` over `ZMod 4` (m = 2, level 2). The T gate is `U_P` for
  `P = j_i` over `ZMod 8` (m = 3, level 3). The CCZ gate is `U_P` for
  `P = j_i j_j j_k` over `ZMod 2` (m = 1, deg 3, level 3).
* Non-diagonal hierarchy elements (Hadamard, CNOT, CCNOT) are obtained
  by conjugating diagonal ones by Cliffords; the Clifford layer stays
  in `Sp(2n, F₂)` and is unchanged from chapter 2.

The descent engine of the framework is the *discrete partial
derivative*

  (Δ_i P)(v) := P(v + e_i) − P(v),

which drops the total degree of `P` by at least one. The conjugation
rule (the polynomial-framework analogue of Rengaswamy's Corollary 5)
says `U_P · X^a · U_P^† = X^a · U_{Δ_a P}` (up to a global phase),
exhibiting the level-(k−1) descent.
-/

namespace FTQCLib.Hierarchy

open FTQCLib.Pauli

/-- The data of a diagonal phase function: a multivariate polynomial in
`n` binary qubit variables with coefficients in `ZMod (2^m)`. The
corresponding diagonal unitary is

  U_P = diag(ξ^{P(v) mod 2^m} : v ∈ (F₂)ⁿ),

where `ξ = exp(2πi / 2^m)`. The framework treats `U_P` abstractly via
the polynomial `P`; we never form the literal complex matrix.

We use `abbrev` rather than `def` so that the commutative-ring,
algebra, and grading structure of `MvPolynomial` are visible without
re-declaration. Addition of `DiagPhase` corresponds to multiplication
of the underlying diagonal unitaries. -/
abbrev DiagPhase (n m : ℕ) : Type := MvPolynomial (Fin n) (ZMod (2^m))

namespace DiagPhase

/-- Lift a binary vector `v : Fin n → ZMod 2` to `Fin n → ZMod (2^m)`
via the canonical embedding `ZMod 2 → ZMod (2^m)` sending `0 ↦ 0` and
`1 ↦ 1`. Implemented as the cast `(v i).val` of the underlying `Nat`. -/
def liftBinary {n m : ℕ} (v : Fin n → ZMod 2) : Fin n → ZMod (2^m) :=
  fun i => ((v i).val : ZMod (2^m))

/-- Evaluate the phase polynomial `P` at a binary vector
`v ∈ (F₂)ⁿ`, returning the diagonal-entry exponent of `U_P` at index
`v`. The result lives in `ZMod (2^m)`. Noncomputable because
`MvPolynomial.eval` walks the `AddMonoidAlgebra` structure. -/
noncomputable def eval {n m : ℕ} (P : DiagPhase n m) (v : Fin n → ZMod 2) :
    ZMod (2^m) :=
  MvPolynomial.eval (liftBinary v) P

/-- The Clifford-hierarchy level of the diagonal unitary `U_P`. By
Cui–Gottesman–Krishna Theorem 3 (qubit specialisation), this equals
`(m − 1) + totalDegree(P)` for any non-trivial `P`. For the constant
polynomial `P = 0` the corresponding unitary is `I`, of level 0; our
formula returns `m − 1`, which is an upper bound on the actual level
(the encoding has slack at the trivial case). Noncomputable because
`totalDegree` traverses the polynomial support. -/
noncomputable def level {n m : ℕ} (P : DiagPhase n m) : ℕ :=
  (m - 1) + (P : MvPolynomial (Fin n) (ZMod (2^m))).totalDegree

/-- The discrete partial derivative `Δ_i P` defined by
`(Δ_i P)(v) := P(v + e_i) − P(v)`. As a polynomial operation it is the
substitution `X_i ↦ X_i + 1` minus the identity. The key analytic fact
(`discreteDeriv_totalDegree_lt`, proved separately) is that `Δ_i` drops
the total degree by at least one whenever `P` actually contains the
variable `X_i`. Noncomputable because it uses `MvPolynomial.bind₁`. -/
noncomputable def discreteDeriv {n m : ℕ} (i : Fin n) (P : DiagPhase n m) :
    DiagPhase n m :=
  MvPolynomial.bind₁
    (fun k : Fin n => if k = i then MvPolynomial.X k + 1 else MvPolynomial.X k) P
    - P

/-- `DiagPhase.eval` is additive. -/
theorem eval_add {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    DiagPhase.eval (A + B) v = DiagPhase.eval A v + DiagPhase.eval B v := by
  simp [DiagPhase.eval]

/-- `DiagPhase.eval` is multiplicative. -/
theorem eval_mul {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    DiagPhase.eval (A * B) v = DiagPhase.eval A v * DiagPhase.eval B v := by
  simp [DiagPhase.eval]

/-- `DiagPhase.eval` on a constant. -/
theorem eval_C {N m : ℕ} (a : ZMod (2 ^ m)) (v : Fin N → ZMod 2) :
    DiagPhase.eval (MvPolynomial.C a : DiagPhase N m) v = a := by
  simp [DiagPhase.eval]

/-- `DiagPhase.eval` on a variable. -/
theorem eval_X {N m : ℕ} (j : Fin N) (v : Fin N → ZMod 2) :
    DiagPhase.eval (MvPolynomial.X j : DiagPhase N m) v = ((v j).val : ZMod (2 ^ m)) := by
  simp [DiagPhase.eval, DiagPhase.liftBinary]

end DiagPhase

end FTQCLib.Hierarchy

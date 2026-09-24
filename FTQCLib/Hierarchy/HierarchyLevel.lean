/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.Descent
import FTQCLib.Hierarchy.GatePolynomials

set_option linter.unusedSectionVars false

/-! # The Clifford-hierarchy predicate for diagonal phase polynomials

The Clifford hierarchy `C^(k)` is defined recursively on unitaries:
`C^(1)` is the Pauli group, and `U ∈ C^(k+1)` iff conjugation by `U`
sends every Pauli to `C^(k)`. The Cui–Gottesman–Krishna classification
(arXiv:1608.06596, Theorem 3) says that for qubits the *diagonal*
subgroup of `C^(k)` is exactly the set of unitaries whose phase
function is a polynomial `P` with `(m − 1) + totalDegree(P) ≤ k`. That
is our definition of `IsDiagonalHierarchyLevel`.

This file:

* Defines `IsDiagonalHierarchyLevel k P` as `P.level ≤ k`.
* Proves the **recursive descent theorem**: if `P` is at level `k+1`
  and `P.totalDegree > 0`, then for every qubit `i` the discrete
  derivative `Δ_i P` is at level `k`. This matches the Clifford
  hierarchy's defining recursion `C^(k+1) ⊃ U ⇒ U P U† ∈ C^(k)`,
  translated through the polynomial-framework identity
  `U_P · X_i · U_P† = X_i · U_{Δ_i P}`.
* Proves monotonicity (filtered hierarchy) and closure under
  polynomial addition (the diagonal subgroup at each level is an
  additive subgroup of `DiagPhase n m`).
* Records the level-3 membership for `T` and `CCZ` (the `cczPoly`
  totalDegree computation lives in `FTQCLib/Hierarchy/GatePolynomials.lean`).

This file never constructs the literal matrix; the connection back to the
unitary-side hierarchy in `U(2^n)` is made in `FTQCLib/Hilbert/` (e.g.
`cgk_exact_level`). The *structural* content (the recursive descent on phase
polynomials) is fully formalised here.
-/

namespace FTQCLib.Hierarchy

namespace DiagPhase

variable {n m : ℕ}

/-- The diagonal unitary `U_P` is at level `k` of the Clifford
hierarchy iff the phase polynomial `P` has level at most `k`. By
Cui–Gottesman–Krishna Theorem 3 (qubits), this is the *correct*
characterisation of the diagonal subgroup of `C^(k)` — the operator-
side recursive definition matches the polynomial-side bound. -/
def IsDiagonalHierarchyLevel (k : ℕ) (P : DiagPhase n m) : Prop :=
  P.level ≤ k

/-- The recursive descent theorem. If `U_P` is at level `k+1` and `P`
has positive total degree (so `U_P` is not just a global phase), then
for every qubit `i` the diagonal unitary `U_{Δ_i P}` is at level `k`.

This is the polynomial-side image of the operator identity
`U_P · X_i · U_P† = X_i · U_{Δ_i P}` combined with the defining
recursion of the Clifford hierarchy `C^(k+1) ⊃ U ⇒ U · P · U† ∈ C^(k)`. -/
theorem IsDiagonalHierarchyLevel.descent_succ {k : ℕ} {P : DiagPhase n m}
    (h : IsDiagonalHierarchyLevel (k + 1) P) (hdeg : 0 < P.totalDegree)
    (i : Fin n) :
    IsDiagonalHierarchyLevel k (discreteDeriv i P) := by
  unfold IsDiagonalHierarchyLevel level at h ⊢
  have hlt := discreteDeriv_totalDegree_lt i hdeg
  omega

/-- Monotonicity: a level-`k` element is also at level `k'` for any
`k' ≥ k`. The hierarchy is filtered: `C^(k) ⊆ C^(k')`. -/
theorem IsDiagonalHierarchyLevel.mono {k k' : ℕ} {P : DiagPhase n m}
    (hk : k ≤ k') (h : IsDiagonalHierarchyLevel k P) :
    IsDiagonalHierarchyLevel k' P :=
  h.trans hk

/-- Closure under addition. If `P` and `Q` are both at level `k`, so
is `P + Q`. The diagonal subgroup at each level is an additive
subgroup of `DiagPhase n m`; multiplication of diagonal unitaries
`U_P · U_Q = U_{P + Q}` corresponds to addition of phase polynomials.

This is the polynomial-side image of Rengaswamy–Calderbank–Pfister
Theorem 11 (the group iso for the diagonal-symmetric subgroup),
generalised here from symmetric matrices to arbitrary polynomials. -/
theorem IsDiagonalHierarchyLevel.add {k : ℕ} {P Q : DiagPhase n m}
    (hP : IsDiagonalHierarchyLevel k P) (hQ : IsDiagonalHierarchyLevel k Q) :
    IsDiagonalHierarchyLevel k (P + Q) := by
  unfold IsDiagonalHierarchyLevel level at hP hQ ⊢
  have htd : (P + Q).totalDegree ≤ max P.totalDegree Q.totalDegree :=
    MvPolynomial.totalDegree_add P Q
  omega

/-- The T gate on qubit `i` is at level 3 of the Clifford hierarchy. -/
theorem tGatePoly_isDiagonalHierarchyLevel_three {n : ℕ} (i : Fin n) :
    IsDiagonalHierarchyLevel 3 (tGatePoly i) := by
  unfold IsDiagonalHierarchyLevel
  rw [tGatePoly_level]

/-- The CCZ gate on three qubits is at level 3 of the Clifford hierarchy. -/
theorem cczPoly_isDiagonalHierarchyLevel_three {n : ℕ} (i j k : Fin n) :
    IsDiagonalHierarchyLevel 3 (cczPoly i j k) := by
  unfold IsDiagonalHierarchyLevel
  rw [cczPoly_level]

end DiagPhase

end FTQCLib.Hierarchy

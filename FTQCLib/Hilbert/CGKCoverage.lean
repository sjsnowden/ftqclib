/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKGroupStructure

/-! # Coverage ledger: Cui–Gottesman–Krishna (2017) at p = 2, formally verified

Cui, Gottesman, Krishna, *Diagonal gates in the Clifford hierarchy*,
PRA 95, 012329 (2017); arXiv:1608.06596. Every result of the paper in
the qubit case (`p = 2`) is formalized; this file is the
statement-by-statement map. The `#check` anchors below fail to compile
if any cited name disappears.

## The ledger

| CGK result (p = 2) | Lean name(s) | File |
|---|---|---|
| Hierarchy definition (CGK Eq. 6) | `IsCliffordHierarchy`, `IsCliffordHierarchyDyadic` | Hierarchy.lean, HierarchyDyadic.lean |
| Theorem 1 (diagonal level sets are groups, after Zeng–Chen–Chuang) | `diagonalDyadicSubgroup` (+ the `CommGroup` instance: the levels are abelian) | CGKGroupStructure.lean |
| Theorem 2 (single-qudit exact monomial levels) | `cgk_forward_monomial` (membership), `zGate/sGate/tGate_exact_level` (n-qubit instances, exact) | CGKTwoSided.lean, CGKExactness.lean |
| Theorem 3 (n-qudit classification, Eq. 64) | `cgk_diagonal_dyadic_iff` (k ≥ 2), `cgk_diagonal_dyadic_iff_one` (k = 1), `cgk_diagonal_iff` (unrestricted hierarchy), `cgk_exact_level` (exact form for the polynomial in hand) | CGKTwoSided.lean, CGKExactness.lean |
| Corollary 1 (single-qudit group structure) | `cgkDiagonalParametrization` at `n = 1` | CGKGroupStructure.lean |
| Corollary 2 (n-qudit group structure) | `cgkDiagonalParametrization` — **CORRECTED**: the component at slot `S` is `ℤ/2^(k−|S|+1)`; the printed exponent `⌊(w−wt a)/(p−1)⌋` contradicts Corollary 1 of the same paper | CGKGroupStructure.lean |
| Definition 5 (generating set) | `cgk_generating_set` (corrected: the printed clause `1 ≤ cᵢ ≤ p−1` admits only the all-ones index at p = 2) | CGKGroupStructure.lean |
| Lemma 2 (Faulhaber/Bernoulli converse) | superseded: the reverse direction runs through inclusion-exclusion + `Δ² = −2Δ` + halving, certified by `mobiusCoeff_precision_bound`; no Bernoulli arithmetic needed | CGKReverse*.lean, ProjectiveStrictLevel.lean |
| Conjugation as discrete difference (CGK Eqs. 26–28, 45) | `conjEquiv_diagonalGateEquiv_general`, `shiftBy` machinery | CGKForward.lean |
| Phase-gate examples (Definition 3) | gate suite: `Z@1, S@2, T@3, CS@3, CCZ@3`, membership AND exact levels with strictness | CGKGateTests.lean, CGKExactness.lean |

## Beyond the paper (new here)

* `isCliffordHierarchy_iff_dyadic_of_two_le` — phase-convention
  independence: the hierarchies with arbitrary and with dyadic phases
  coincide at every `k ≥ 2`; no such statement appears in CGK.
* `cgk_exact_level` — exactness for the polynomial in hand: membership
  at level `k` holds exactly when the effective level is at most `k`.
* `tGate_not_mem_clifford_two` — strict gate lower bounds:
  machine-checked `T ∉ C₂` against the unrestricted hierarchy.

## Documented deviations (conventions, not gaps)

* The ambient hierarchy lives on linear automorphisms with `ℂˣ` phases;
  on the DIAGONAL sector the carrier forces unimodular phases, so the
  group statements (Thm 1, Cors 1–2) are against the genuine
  `U(1) = Circle` — no deviation there.
* At `k = 1` the dyadic hierarchy constrains phases to dyadic roots of
  unity, where CGK put all of `U(1)` at every level by fiat; the k = 1
  statements (`cgk_diagonal_dyadic_iff_one`) carry the dyadic clause
  explicitly. At `k ≥ 2` the loose collapse erases the difference.
* Scope: qubits only (`p = 2`). The odd-prime case, which needs
  different reverse-direction arithmetic, is not treated here.
-/

namespace FTQCLib.Hilbert

-- Compile-time anchors: the table's names must exist.
#check @IsCliffordHierarchy
#check @IsCliffordHierarchyDyadic
#check @diagonalDyadicSubgroup
#check @cgk_forward_monomial
#check @cgk_diagonal_dyadic_iff
#check @cgk_diagonal_dyadic_iff_one
#check @cgk_diagonal_iff
#check @cgk_exact_level
#check @cgk_exact_level_scaled
#check @cgk_exact_level_clifford
#check @cgkDiagonalParametrization
#check @cgk_generating_set
#check @isCliffordHierarchy_iff_dyadic_of_two_le
#check @zGate_exact_level
#check @sGate_exact_level
#check @tGate_exact_level
#check @csGate_exact_level
#check @cczGate_exact_level
#check @tGate_not_mem_clifford_two
#check @mem_diagonalDyadicSubgroup_iff_clifford
#check @multilinear_eval_injective
#check @cgk_forward_sharp
#check @cgk_reverse_projective_sharp

end FTQCLib.Hilbert

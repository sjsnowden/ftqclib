/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.PauliOp
import FTQCLib.Hilbert.Diagonal
import FTQCLib.Hierarchy.HierarchyLevel

set_option linter.unusedSectionVars false

/-! # Cui--Gottesman-Krishna equivalence: polynomial-side vs. operational

This file builds the operator-side analogue of the polynomial-framework
Clifford hierarchy from chapter 2 and verifies (in part) the
Cui--Gottesman-Krishna equivalence: the polynomial-side predicate
`IsDiagonalHierarchyLevel k P` from `FTQCLib/Hierarchy/HierarchyLevel.lean`
matches the operator-side statement that `diagonalGate (realPhase P)`
sits at level `k` of the operational Clifford hierarchy on
`QubitSpace n`.

CGK 2017 (arXiv 1608.06596) Theorem 2 (single qudit case, generalised
to multi-qudit in Section IV) states: for the qubit case (p = 2), a
diagonal unitary `U_P = ∑_v exp(2πi · P(v) / 2^m) |v⟩⟨v|` sits at
level `(m-1) + totalDegree(P)` of the Clifford hierarchy. Their
operational definition of the hierarchy is recursive: C^(1) is the
Pauli group with global phases; C^(k) is the set of unitaries U such
that UPU† ∈ C^(k-1) for every P in the Pauli group.

This file:

* **Descent rule (`diagonalGate_paulix_shift`)**. The operator-side
  analogue of the chapter-2 polynomial descent `U_P · X_i · U_P† =
  X_i · U_{Δ_i P}`. For each `i : Fin n`,
  `diagonalGate (realPhase P) ∘ pauliOperator (paulix i)
    = pauliOperator (paulix i) ∘ diagonalGate (P-shift-by-e_i)`.
  This is the structural bridge: conjugation of a Pauli `X_i` by the
  diagonal gate `U_P` produces a diagonal gate whose phase pattern is
  `P` shifted by `e_i`.

The descent rule + chapter-2's polynomial descent (degree drops by ≥ 1
under `Δ_i`) gives the forward direction of CGK by induction. The
reverse direction (CGK Theorem 2's actual content, via Faulhaber's
formula on Bernoulli numbers) is structurally a separate piece.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex

variable {n m : ℕ}

/-- **Operator-side descent rule.** For any phase polynomial `P` and
qubit index `i`, the diagonal gate `diagonalGate (realPhase P)` and
the Pauli operator `pauliOperator (paulix i)` interchange with a
"phase shift": the gate applied after the X-flip equals the X-flip
applied after a phase-shifted diagonal gate. Concretely:

  `diagonalGate (realPhase P) ∘ pauliOperator (paulix i)
   = pauliOperator (paulix i) ∘ diagonalGate (fun v ↦
                                  realPhase P (v + Pi.single i 1))`.

In CGK terms, this is the "descent" identity behind the recursive
characterisation of the Clifford hierarchy: conjugating `X_i` by the
diagonal `U_P` produces another diagonal gate with phase pattern
shifted by `e_i = Pi.single i 1`. -/
theorem diagonalGate_paulix_shift (P : DiagPhase n m) (i : Fin n) :
    (diagonalGate (DiagPhase.realPhase P)) ∘ₗ
      (pauliOperator (paulix i)) =
    (pauliOperator (paulix i)) ∘ₗ
      (diagonalGate (fun v : Fin n → ZMod 2 =>
        DiagPhase.realPhase P (v + Pi.single i 1))) := by
  apply LinearMap.ext
  intro ψ
  funext w
  -- Compute both sides at w. We unpack pauliOperator (paulix i) and
  -- diagonalGate (...) on basis arguments, then verify the equality.
  simp only [LinearMap.coe_comp, Function.comp_apply]
  unfold diagonalGate
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  unfold pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  have hX : (paulix i).X = Pi.single i 1 := rfl
  rw [hX]
  have hzdot : ∀ u : Fin n → ZMod 2, zDotVal (paulix i) u = 0 := by
    intro u
    unfold zDotVal
    refine Finset.sum_eq_zero ?_
    intro j _
    have h0 : ((paulix i).Z j).val = 0 := by
      have hZj : (paulix i).Z j = (0 : ZMod 2) := by
        have hZ : (paulix i).Z = (0 : Fin n → ZMod 2) := rfl
        rw [hZ]; rfl
      rw [hZj]
      exact ZMod.val_zero
    rw [h0]
    ring
  rw [hzdot]
  simp only [pow_zero, one_mul]
  have hw : w - Pi.single i 1 + Pi.single i 1 = w := by ring
  rw [hw]

end FTQCLib.Hilbert

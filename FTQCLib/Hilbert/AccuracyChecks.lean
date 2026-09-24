/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.StabilizerTheory
import FTQCLib.Hilbert.MeasurementCollapse

/-! # Accuracy / non-vacuity instance checks

Concrete instances discharging the formalization-accuracy obligation: each `example` evaluates a
definition to its intended physical value, so a wrong sign or collapsed definition fails to compile.
The Born expectation gives the correct `Z` eigenvalues `±1` and **distinguishes** `|0⟩` from `|1⟩`;
the Hermitian Paulis are genuinely distinct; the object map `(L, χ) ↦ stabProjector` separates
stabilizer states with distinct Lagrangians; and conditioning on an observable the state does not
fix lands in a new Lagrangian. So the operational correspondence and the measurement collapse are
non-vacuous. (See also `pauliHermitian_injective`, `mermin_peres_no_assignment`, and the
dichotomies `expectation_eq_eval` / `bornProb_eq_eval`.) -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli

variable {n : ℕ}

/-- `⟨Z⟩` on `|0⟩` is `+1`. -/
example (i : Fin n) : expectation (qComputational (0 : Fin n → ZMod 2)) (pauliz i) = 1 := by
  rw [expectation_qComputational_of_X_eq_zero (pauliz i) (pauliz_X i) 0]
  simp [zDotVal]

/-- `⟨Z⟩` on `|1⟩` (qubit `i` excited) is `−1` — so `expectation` distinguishes states. -/
example (i : Fin n) :
    expectation (qComputational (Pi.single i 1)) (pauliz i) = -1 := by
  rw [expectation_qComputational_of_X_eq_zero (pauliz i) (pauliz_X i) (Pi.single i 1)]
  have hz : zDotVal (pauliz i) (Pi.single i 1) = 1 := by
    simp only [zDotVal, pauliz_Z]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj]; simp)
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [Pi.single_eq_same]
    decide
  rw [hz]; norm_num

/-- The Hermitian Pauli operators are genuinely distinct: `H(X) ≠ H(Z)`. -/
example : pauliHermitian (paulix (0 : Fin 1)) ≠ pauliHermitian (pauliz 0) := by
  intro h
  have hne : paulix (0 : Fin 1) ≠ pauliz 0 := by
    intro he
    have hX : (paulix (0 : Fin 1)).X = (pauliz 0).X := by rw [he]
    rw [paulix_X, pauliz_X] at hX
    have h0 := congrFun hX 0
    simp at h0
  exact hne (pauliHermitian_injective h)

/-- The object representation `(L, χ) ↦ stabProjector` separates stabilizer states with distinct
Lagrangians: different stabilizer groups give different density operators. So the object-bijection
conjunct of `stabilizer_operational_correspondence` is non-vacuous. -/
example {S S' : SignedStab n} (h : S.L ≠ S'.L) :
    stabProjector S ≠ stabProjector S' :=
  fun he => h (stabProjector_inj he).1

/-- Measuring an observable `Q` the state does not fix collapses to a *different* Lagrangian:
`pauliCondition L Q ≠ L` when `Q ∉ L`, since `Q` stabilizes the conditioned group but not the
original. So the collapse `ludersChannel_stabProjector_notMem` (`S'.L = pauliCondition S.L Q`)
genuinely moves the state to a new stabilizer group. -/
example (L : Submodule (ZMod 2) (Pauli n)) (Q : Pauli n) (hQ : Q ∉ L) :
    FTQCLib.Stabilizer.pauliCondition L Q ≠ L := by
  intro h
  exact hQ (h ▸ FTQCLib.Stabilizer.pauliCondition_mem L Q)

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Bridge.PauliKlein

/-!
# Checks for the Klein-word chart

Kernel-checked examples recompute the chart's claims at small carriers: the metric
identification exhaustively over `Pauli 2`, the symplectic identification exhaustively over
`Pauli 1`, the shell counts `C(n,d)·3^d` at `n = 2, 3`, and the distance correspondence. The
**control** targets the natural mistake: the block arrangement (X-bits followed by Z-bits, the
shape of `linearEquivProd`) is refuted on the single-qubit `Y`, whose weight is `1` but whose
block word has Hamming norm `2` — the per-coordinate chart is load-bearing, not a notational
choice. The canonical `Fintype`/`DecidableEq (Pauli n)` instances (in
`FTQCLib/Pauli/Basic.lean`) are what these `decide`s run on, and their axioms are checked below.
-/

namespace FTQCLib.Pauli

open Finset FTQCLib.Stabilizer

/-! ## The metric identification, kernel-checked -/

/-- Exhaustive over the 16 elements of `Pauli 2`. -/
example : ∀ p : Pauli 2, weight p = hammingNorm (pauliKleinEquiv p) := by decide

/-- The distance correspondence on `Pauli 2`, exhaustive over ordered pairs. -/
example : ∀ p q : Pauli 2,
    weight (p - q) = hammingDist (pauliKleinEquiv p) (pauliKleinEquiv q) := by decide

/-! ## The symplectic identification, kernel-checked -/

/-- Exhaustive over `Pauli 1 × Pauli 1`. -/
example : ∀ p q : Pauli 1,
    omega p q = ∑ i, FTQCLib.ArfSum.hypOmega (pauliKleinEquiv p i) (pauliKleinEquiv q i) := by
  decide

/-! ## The shell counts, kernel-checked -/

/-- `n = 2`: shells `1, 6, 9` filling `16`. -/
example : #(Finset.univ.filter fun p : Pauli 2 => weight p = 0) = 1 ∧
    #(Finset.univ.filter fun p : Pauli 2 => weight p = 1) = 6 ∧
    #(Finset.univ.filter fun p : Pauli 2 => weight p = 2) = 9 := by decide

/-- `n = 3`: shells `1, 9, 27, 27` filling `64`. -/
example : #(Finset.univ.filter fun p : Pauli 3 => weight p = 0) = 1 ∧
    #(Finset.univ.filter fun p : Pauli 3 => weight p = 1) = 9 ∧
    #(Finset.univ.filter fun p : Pauli 3 => weight p = 2) = 27 ∧
    #(Finset.univ.filter fun p : Pauli 3 => weight p = 3) = 27 := by decide

/-- **Instantiation of the theorem**, at a carrier the examples above do not
reach: the weight-`2` shell of `Pauli 5` has `C(5,2)·3² = 90` elements. The examples above
recompute the shell sizes by `decide`; this one *uses* `card_weight_shell`, so the
general statement is exercised and not merely stated. -/
example : #(Finset.univ.filter fun p : Pauli 5 => weight p = 2) = 90 := by
  rw [card_weight_shell]
  decide

/-! ## The control: the transposed arrangement -/

/-- **Control — the per-coordinate arrangement is load-bearing**: reading the
single-qubit `Y` (`X = Z = 1`) through the BLOCK arrangement (X-bits then Z-bits, the
shape of `linearEquivProd`) gives Hamming norm `2`, not the weight `1`. The chart is
the transpose for a reason. -/
example : weight (⟨fun _ => 1, fun _ => 1⟩ : Pauli 1) = 1 ∧
    hammingNorm (fun j : Fin 2 =>
      if j = 0 then ((⟨fun _ => 1, fun _ => 1⟩ : Pauli 1)).X 0
      else ((⟨fun _ => 1, fun _ => 1⟩ : Pauli 1)).Z 0) = 2 := by decide

end FTQCLib.Pauli

/-! ## Axiom sweep (build-failing) -/

/-- info: 'FTQCLib.Pauli.pauliKleinEquiv' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.pauliKleinEquiv

/-- info: 'FTQCLib.Pauli.pauliKleinEquiv_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.pauliKleinEquiv_apply

/-- info: 'FTQCLib.Pauli.weight_eq_hammingNorm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.weight_eq_hammingNorm

/-- info: 'FTQCLib.Pauli.weight_sub_eq_hammingDist' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.weight_sub_eq_hammingDist

/-- info: 'FTQCLib.Pauli.omega_eq_sum_hypOmega' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.omega_eq_sum_hypOmega

/-- info: 'FTQCLib.Pauli.card_weight_shell' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.card_weight_shell

/-- info: 'FTQCLib.Pauli.instDecidableEq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.instDecidableEq

/-- info: 'FTQCLib.Pauli.instFintype' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Pauli.instFintype

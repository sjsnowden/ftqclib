/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Rank

set_option linter.unusedSectionVars false

/-! # The homological dictionary is genuine: each entry is the operational object

"A quantum code is a chain complex" is a genuine definition only if each
homological object actually *is* its stabilizer-formalism counterpart — the
object built from Paulis, the symplectic form `ω`, the stabilizer `S` and its
normalizer `N(S)` — and not merely a well-formed quotient. This file proves
that coincidence, row by row of the chains/cochains dictionary, on the Z-side
(the X-side is the same statement on the dual complex):

* **errors / syndrome** `Zsyndrome_eq_omega` — the homological syndrome
  `(H_X *ᵥ v) i` of a Z-error `(0,v)` *is* its symplectic detection
  `ω(X-check i, (0,v))`.
* **stabilizers** `mem_cssZStabilizer_iff_boundary` — the operational
  Z-stabilizer Paulis are exactly the boundaries `im H_Zᵀ`.
* **logicals** `nontrivial_Zlogical_iff_homology` — a Z-Pauli is a genuine
  nontrivial logical (`∈ N(S) \ S`) iff it is a nontrivial homology class
  (`∈ ker H_X \ im H_Zᵀ`). So `H_1 = cssZLogical` is the operational logical
  space `N(S)/S` (Z-type), not a quotient that merely typechecks.
* **distance** `cssZDistance_le_of_nontrivial` — the systole bounds the weight
  of every genuine nontrivial Z-logical, so it is the code's Z-distance.
-/

namespace FTQCLib.CSS

open FTQCLib.Pauli FTQCLib.Stabilizer Matrix

variable {n r_X r_Z : ℕ}

/-- **Errors / syndrome.** The homological syndrome `(H_X *ᵥ v) i` of a
Z-error `(0,v)` equals its symplectic detection by the `i`-th X-check. The
chain-complex boundary `∂₁ = H_X` *is* the syndrome map. -/
theorem Zsyndrome_eq_omega
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (i : Fin r_X) :
    omega (cssXGen H_X i) (⟨0, v⟩ : Pauli n) = (H_X *ᵥ v) i := by
  simp [omega, cssXGen, Matrix.mulVec, dotProduct]

/-- **Stabilizers.** A Z-Pauli `(0,v)` is an operational Z-stabilizer iff its
support is a boundary `v ∈ im H_Zᵀ`. The homological boundaries are exactly
the stabilizer group. -/
theorem mem_cssZStabilizer_iff_boundary
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    (⟨0, v⟩ : Pauli n) ∈ cssZStabilizer H_Z ↔ v ∈ cssZLogicalSubspace H_Z :=
  ⟨fun h => cssZStabilizer_Z_mem_subspace H_Z h,
   fun h => cssZStabilizer_of_Z_mem_subspace H_Z h⟩

/-- **Logicals.** A Z-Pauli `(0,v)` is a genuine nontrivial logical operator —
in the normalizer but not the stabilizer — iff `v` is a nontrivial homology
class. Hence `H_1 = ker H_X / im H_Zᵀ = cssZLogical` is the operational logical
space `N(S)/S` (Z-type), not merely a well-formed quotient. -/
theorem nontrivial_Zlogical_iff_homology
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    ((⟨0, v⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) ∧
        (⟨0, v⟩ : Pauli n) ∉ cssStabilizer H_X H_Z) ↔
      (v ∈ cssZLogicalCarrier H_X ∧ v ∉ cssZLogicalSubspace H_Z) := by
  rw [mem_normalizer_cssStabilizer_iff, mem_cssStabilizer_iff]
  constructor
  · rintro ⟨⟨_, hv⟩, hns⟩
    exact ⟨hv, fun hvs => hns ⟨Submodule.zero_mem _, hvs⟩⟩
  · rintro ⟨hv, hvs⟩
    exact ⟨⟨Submodule.zero_mem _, hv⟩, fun h => hvs h.2⟩

/-- **Distance.** The systole `cssZDistance` lower-bounds the Hamming weight of
every genuine nontrivial Z-logical, so it is the code's Z-distance — the
minimum weight of an actual nontrivial logical operator. -/
theorem cssZDistance_le_of_nontrivial
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) {v : Fin n → ZMod 2}
    (hN : (⟨0, v⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z))
    (hS : (⟨0, v⟩ : Pauli n) ∉ cssStabilizer H_X H_Z) :
    cssZDistance H_X H_Z ≤
      ((Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card : ℕ∞) := by
  obtain ⟨hcar, hsub⟩ := (nontrivial_Zlogical_iff_homology H_X H_Z v).mp ⟨hN, hS⟩
  unfold cssZDistance
  exact iInf_le_of_le v (iInf_le_of_le hcar (iInf_le _ hsub))

/-! ## X-side mirrors

The identical statements on the dual complex: swap `X ↔ Z`, `H_1 ↔ H^1`,
`∂ ↔ δ`, `d_Z ↔ d_X`. An X-error is a cochain `(v, 0)`, detected by the
Z-checks `H_Z`. -/

/-- **Errors / syndrome (X).** The syndrome `(H_Z *ᵥ v) i` of an X-error
`(v,0)` equals its symplectic detection by the `i`-th Z-check. The coboundary
`δ = H_Z` *is* the X-syndrome map. -/
theorem Xsyndrome_eq_omega
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) (i : Fin r_Z) :
    omega (cssZGen H_Z i) (⟨v, 0⟩ : Pauli n) = (H_Z *ᵥ v) i := by
  simp [omega, cssZGen, Matrix.mulVec, dotProduct]

/-- **Stabilizers (X).** An X-Pauli `(v,0)` is an operational X-stabilizer iff
its support is a coboundary `v ∈ im H_Xᵀ`. -/
theorem mem_cssXStabilizer_iff_coboundary
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    (⟨v, 0⟩ : Pauli n) ∈ cssXStabilizer H_X ↔ v ∈ cssXLogicalSubspace H_X :=
  ⟨fun h => cssXStabilizer_X_mem_subspace H_X h,
   fun h => cssXStabilizer_of_X_mem_subspace H_X h⟩

/-- **Logicals (X).** An X-Pauli `(v,0)` is a genuine nontrivial logical
(`∈ N(S) \ S`) iff `v` is a nontrivial cohomology class. So
`H^1 = ker H_Z / im H_Xᵀ = cssXLogical` is the operational logical space
`N(S)/S` (X-type). -/
theorem nontrivial_Xlogical_iff_cohomology
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (v : Fin n → ZMod 2) :
    ((⟨v, 0⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z) ∧
        (⟨v, 0⟩ : Pauli n) ∉ cssStabilizer H_X H_Z) ↔
      (v ∈ cssXLogicalCarrier H_Z ∧ v ∉ cssXLogicalSubspace H_X) := by
  rw [mem_normalizer_cssStabilizer_iff, mem_cssStabilizer_iff]
  constructor
  · rintro ⟨⟨hv, _⟩, hns⟩
    exact ⟨hv, fun hvs => hns ⟨hvs, Submodule.zero_mem _⟩⟩
  · rintro ⟨hv, hvs⟩
    exact ⟨⟨hv, Submodule.zero_mem _⟩, fun h => hvs h.1⟩

/-- **Distance (X).** The cosystole `cssXDistance` lower-bounds the weight of
every genuine nontrivial X-logical, so it is the code's X-distance. -/
theorem cssXDistance_le_of_nontrivial
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) {v : Fin n → ZMod 2}
    (hN : (⟨v, 0⟩ : Pauli n) ∈ normalizer (cssStabilizer H_X H_Z))
    (hS : (⟨v, 0⟩ : Pauli n) ∉ cssStabilizer H_X H_Z) :
    cssXDistance H_X H_Z ≤
      ((Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card : ℕ∞) := by
  obtain ⟨hcar, hsub⟩ := (nontrivial_Xlogical_iff_cohomology H_X H_Z v).mp ⟨hN, hS⟩
  unfold cssXDistance
  exact iInf_le_of_le v (iInf_le_of_le hcar (iInf_le _ hsub))

end FTQCLib.CSS

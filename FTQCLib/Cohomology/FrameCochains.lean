/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.Cochains
import FTQCLib.Frame.CubicCeiling

/-! # The frame, re-expressed as cochains of the extension

The frame's proven facts are statements about cochains of the cohomology built in `Cochains.lean`.
This file records the dictionary (thin wrappers over existing theorems, no new mathematics):

* the stabilizer sign `χ` is a 1-cochain trivializing `β` on its Lagrangian (`δ¹χ = −β|_L`);
* each gate's sign cochain trivializes the gate's distortion 2-cocycle (`D_T = δ¹c`);
* the cubic ceiling is the Möbius-degree-≤3 filtration on the distortion cochain. -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame

variable {n : ℕ}

/-- **A stabilizer state's sign `χ` trivializes `β` on its Lagrangian.** The `valid` law is exactly
`δ¹χ = −β` on `L`. So `β|_L` is a coboundary — the restricted class `[β|_L] = 0`, which is the
cohomological reason a consistent sign assignment (a stabilizer state) exists at all. -/
theorem chi_trivializes (S : FrameSignedStab n) {p q : Pauli n} (hp : p ∈ S.L) (hq : q ∈ S.L) :
    delta1 S.chi p q = - betaFrame p q := by
  have h := S.valid p hp q hq
  simp only [delta1, LinearMap.coe_mk, AddHom.coe_mk]
  rw [h]; ring

/-- **The gate distortion is a coboundary.** `tvSign_validity` says the `S`-gate's distortion `D_T`
is the 1-coboundary of the sign cochain `tvSignZ`, pulled back along the gate. So the per-gate sign
trivializes the distortion — the cohomology statement of "the gate acts on the frame". -/
theorem frameDistortion_eq_delta1_tvSign (k : Fin n) (p q : Pauli n) :
    frameDistortion (transvectionEquiv (pauliz k)) p q
      = delta1 (tvSignZ k) (transvectionEquiv (pauliz k) p)
          (transvectionEquiv (pauliz k) q) := by
  have h := tvSign_validity k p q
  simp only [delta1, LinearMap.coe_mk, AddHom.coe_mk, frameDistortion]
  rw [← map_add]
  exact h.symm

/-- **The cubic ceiling, cohomologically.** The gate-distortion 2-cochain (on the bit register)
lies in the Möbius-degree-≤3 part of the cochain filtration — the frame-native degree bound at the
Clifford floor. (`transvection_distortion_cubic`, in the cohomology dictionary.) -/
theorem distortion_cochain_degree_le (v : Pauli n) : MobiusDegLE 3 (distortionBits v) :=
  transvection_distortion_cubic v

end FTQCLib.Cohomology

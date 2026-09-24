/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Bridge.MobiusDegree

set_option linter.style.longLine false

/-!
# The frame's floor Möbius calculus and its magic degree are one difference object

`eval_isPolyDegLE_effectiveLevel` (nonclassical degree ≤ `effectiveLevel`) and
`MobiusDegLE_of_isPolyDegLE` (interaction degree ≤ nonclassical degree) are wired here so the
frame's two degree apparatuses read as a single iterated-difference object.

* **Legibility** (`mobiusDegLE_iff_iteratedFwdDiff`): the frame's Möbius/interaction degree
  (`MobiusDegLE`) *is* a coordinate-difference degree — `mobiusCoeff S f` is literally
  `iteratedFwdDiff` over `S`'s basis directions, evaluated at `0`
  (`funcDerivSubset_eq_iteratedFwdDiff`). So the floor's combinatorial degree and the magic side's
  difference degree are read off the *same* operator.
* **One graded object on the floor** (`MobiusDegLE_effectiveLevel_of_multilinear`, the composite
  of the two bounds above): for a multilinear `P : DiagPhase N 2` (ℤ/4 floor), the Möbius degree
  of `eval P` is bounded by the magic-side `effectiveLevel P`.
* **The actual cubic ceiling** (`distortionBits_cubic_as_difference`): the frame's unconditional
  cubic ceiling `transvection_distortion_cubic` (Möbius-degree ≤ 3 of the distortion cochain),
  read as: every 4-fold coordinate difference of the cochain vanishes at `0`.

Consequently the frame's named floor construction is the same difference object the
magic-degree theory runs on.
-/

namespace FTQCLib.Bridge

open FTQCLib.Hierarchy FTQCLib.Hierarchy.BooleanMobius ECCLib FTQCLib FTQCLib.Pauli FTQCLib.Frame

variable {N : ℕ}

/-- A Möbius coefficient IS an iterated coordinate difference at `0`: `mobiusCoeff S f =
iteratedFwdDiff (S's basis directions) f 0`. (`mobiusCoeff = funcDerivSubset · 0`, by
`funcDerivSubset_eq_iteratedFwdDiff`.) -/
theorem mobiusCoeff_eq_iteratedFwdDiff_zero {A : Type*} [AddCommGroup A] (S : Finset (Fin N))
    (f : (Fin N → ZMod 2) → A) :
    mobiusCoeff S f = iteratedFwdDiff (S.toList.map (fun i => Pi.single i (1 : ZMod 2))) f 0 := by
  change funcDerivSubset S f 0 = _
  rw [funcDerivSubset_eq_iteratedFwdDiff]

/-- **The frame's Möbius degree IS a coordinate-difference degree at `0`.** Makes explicit that the floor's
`MobiusDegLE` and the magic side's `IsPolyDegLE` are read off the same `iteratedFwdDiff` operator. -/
theorem mobiusDegLE_iff_iteratedFwdDiff (d : ℕ) (f : (Fin N → ZMod 2) → ZMod 4) :
    FTQCLib.Frame.MobiusDegLE d f ↔ ∀ S : Finset (Fin N), d < S.card →
      iteratedFwdDiff (S.toList.map (fun i => Pi.single i (1 : ZMod 2))) f 0 = 0 := by
  unfold FTQCLib.Frame.MobiusDegLE
  simp_rw [mobiusCoeff_eq_iteratedFwdDiff_zero]

/-- **One graded object on the floor** (`MobiusDegLE_of_isPolyDegLE` composed with
`eval_isPolyDegLE_effectiveLevel`): for a multilinear `P : DiagPhase N 2` (ℤ/4), the frame's
Möbius/interaction degree of `eval P` is bounded by the magic-side `effectiveLevel P`. Both the
floor's combinatorial degree and the difference degree are governed by the one grade. -/
theorem MobiusDegLE_effectiveLevel_of_multilinear {P : DiagPhase N 2}
    (hP : DiagPhase.IsMultilinear P) :
    FTQCLib.Frame.MobiusDegLE (DiagPhase.effectiveLevel P) P.eval :=
  MobiusDegLE_of_isPolyDegLE (eval_isPolyDegLE_effectiveLevel P hP)

/-- **The frame's cubic ceiling, read in the difference calculus.** The unconditional
`transvection_distortion_cubic` (Möbius-degree ≤ 3 of the distortion cochain) says: every 4-fold iterated
coordinate difference of `distortionBits v` vanishes at `0`. -/
theorem distortionBits_cubic_as_difference {n : ℕ} (v : Pauli n)
    (S : Finset (Fin (n * 4))) (hS : 3 < S.card) :
    iteratedFwdDiff (S.toList.map (fun i => Pi.single i (1 : ZMod 2)))
      (distortionBits v) 0 = 0 :=
  (mobiusDegLE_iff_iteratedFwdDiff 3 (distortionBits v)).mp
    (transvection_distortion_cubic v) S hS

end FTQCLib.Bridge

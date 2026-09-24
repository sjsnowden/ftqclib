/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.SignedSymplectic

set_option linter.style.longLine false

/-! # `SignedSymplectic` as the `V`-extension (the 2-group / central-extension reading)

One may ask whether the frame's degree-2 metaplectic data assembles into a categorified object (a
banded 2-group / crossed module), where a *central* sign (`π₁`) and the `V`-sectional data (`π₀`)
live on separate levels. This file records what `SignedSymplectic` itself realizes.

`SignedSymplectic n` is a group extension of the Clifford/symplectic action (`x ↦ x.g`) by the **sign-cochain group**.
Its kernel — the `x` with `x.g = 1` — consists of the sign parts `s` that are *additive characters*
(`kernel_s_additive`, because the identity map has no distortion, `frameDistortion_refl`) and `2`-torsion valued
(`two_smul_s`). So the kernel is the group of additive `ℤ/2`-valued characters of `Pauli n` — the **translation /
`V`-layer** — and `SignedSymplectic` is the (`frameDistortion`-twisted) **`V`-extension** of the symplectic group.
This is exactly `metaplectic_defect_is_sectional`: the defect is the `V`-extension, **not** a `U(1)`-central class.

**What this group does not separate.** `SignedSymplectic` puts everything in one group (the
`V`-extension); it does **not** itself separate a central `π₁` sign from the `π₀` `V`-sectional
data. That separation is a crossed-module presentation, constructed in
`FTQCLib.Cohomology.MetaplecticTwoGroup` (boundary `pauliShift` from the Heisenberg group, band the
central `ℤ/4`). The extension's twisting datum is the `2`-cocycle `frameDistortion`, built from the
Pauli cocycle `betaFrame` (whose `H²(V, ℤ/4)` class is `betaClass`,
`FTQCLib/Cohomology/Cochains.lean`).
-/

open FTQCLib.Pauli FTQCLib.Frame

namespace FTQCLib.Cohomology.SignedSymplectic

variable {n : ℕ}

/-- **The identity map has no distortion.** `frameDistortion (refl) a b = 0`, so a sign cochain over the identity
symplectic is unconstrained by any cocycle — it is an ordinary additive character. -/
@[simp] theorem frameDistortion_refl (a b : Pauli n) :
    frameDistortion (LinearEquiv.refl (ZMod 2) (Pauli n)) a b = 0 := by
  simp [frameDistortion]

/-- **The kernel is additive characters.** If `x.g = 1` (the identity symplectic), the sign part `x.s` is an
*additive* map `x.s (p + q) = x.s p + x.s q` — because the crossed-hom law `valid` loses its `frameDistortion` term
over the identity. With `two_smul_s` (`x.s` is `2`-torsion), the kernel is the group of `ℤ/2`-valued additive
characters of `Pauli n`: the translation / `V`-layer. -/
theorem kernel_s_additive (x : SignedSymplectic n)
    (hx : x.g = LinearEquiv.refl (ZMod 2) (Pauli n)) (p q : Pauli n) :
    x.s (p + q) = x.s p + x.s q := by
  have h := x.valid p q
  rw [hx, frameDistortion_refl, add_zero] at h
  exact h

end FTQCLib.Cohomology.SignedSymplectic

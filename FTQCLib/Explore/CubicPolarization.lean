/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BooleanMobius
import FTQCLib.Hierarchy.GatePolynomials

set_option linter.style.longLine false

/-! # Cubic polarization

A first step toward a characteristic-2 higher-degree analogue of the Weil representation: does the
cubic phase **polarize** to a symmetric trilinear form, and — for the *nonclassical* (`ZMod 8`)
cubic — does its third finite difference land at the "sign level" `2^{m-1}`, confirming the *"each
degree needs one more 2-adic rung"* pattern (quadratic → sign `2` in `ℤ/4`; cubic → sign `4` in
`ℤ/8`)?

The finite difference is the frame's `funcDerivG` (`funcDerivG i f = fun v => f (v + eᵢ) − f v`) — exactly the
higher-order-Fourier additive derivative `Δ_h P(x) = P(x+h) − P(x)`. A nonclassical polynomial has *degree ≤ d*
iff `d+1` such differences vanish (Tao–Ziegler); its degree is the frame's functional/Möbius degree.

The two test phases are the frame's own cubic gates:
* `cczFn` = the `CCZ` exponent `v ↦ v₀·v₁·v₂` over `ZMod 2` — the *classical* cubic (polynomial degree 3);
* `tFn`  = the `T` exponent `v ↦ |v₀|` over `ZMod 8` — the *nonclassical* cubic (polynomial degree 1, but
  nonclassical degree 3).

**Outcome (all `decide`, exact):** yes on both counts. The classical cubic's third difference over three
distinct directions is the constant `1` (`ccz_thirdDiff`), symmetric under permuting the directions
(`thirdDiff_symm`, via `funcDerivG_comm`). The nonclassical cubic's third difference is the constant `4 = 2^{3-1}`
in `ZMod 8` (`tCubic_thirdDiff`) and its fourth difference vanishes (`tCubic_fourthDiff`) — degree exactly 3,
landing at the cubic sign level `2^{m-1}`, the direct analogue of the quadratic Weil sign `2 ∈ ℤ/4`. So the
cubic *does* polarize to a symmetric (constant) trilinear cocycle, and the nonclassical case sits one 2-adic
rung up, at `ℤ/8`.
-/

namespace FTQCLib.Explore.CubicPolarization

open FTQCLib.Hierarchy FTQCLib.Hierarchy.BooleanMobius

/-- The **classical cubic** phase (the `CCZ` exponent) as a computable `ZMod 2`-valued function on `(𝔽₂)³`:
`v ↦ v₀·v₁·v₂`. -/
def cczFn : (Fin 3 → ZMod 2) → ZMod 2 := fun v => v 0 * v 1 * v 2

/-- The **nonclassical cubic** phase (the `T` exponent) as a `ZMod 8`-valued function of one bit:
`v ↦ |v₀|`, the standard lift `{0,1} → ZMod 8`. Polynomial degree 1; nonclassical degree 3. -/
def tFn : (Fin 1 → ZMod 2) → ZMod 8 := fun v => ((v 0).val : ZMod 8)

/-- **CCZ polarizes to the constant trilinear cocycle `1`.** The third finite difference of the classical cubic,
over the three distinct directions, is the constant `1 ∈ ZMod 2` — the top trilinear coefficient. -/
theorem ccz_thirdDiff :
    ∀ v, funcDerivG 0 (funcDerivG 1 (funcDerivG 2 cczFn)) v = 1 := by decide

/-- The third difference of the classical cubic is **symmetric** under permuting the three directions — the
"trilinear form is symmetric" half of "polarizes to a symmetric trilinear form" (from `funcDerivG_comm`). -/
theorem thirdDiff_symm :
    funcDerivG 0 (funcDerivG 1 (funcDerivG 2 cczFn))
      = funcDerivG 2 (funcDerivG 1 (funcDerivG 0 cczFn)) := by
  rw [funcDerivG_comm 0 1, funcDerivG_comm 0 2, funcDerivG_comm 1 2]

/-- **The nonclassical cubic's third difference is the cubic sign level `2^{m-1} = 4`.** The single-variable
`ZMod 8` `T`-phase has third finite difference the constant `4 ∈ ZMod 8` — the direct analogue of the quadratic
Weil sign `2 ∈ ZMod 4`, one 2-adic rung up. -/
theorem tCubic_thirdDiff :
    ∀ v, funcDerivG 0 (funcDerivG 0 (funcDerivG 0 tFn)) v = 4 := by decide

/-- **The nonclassical cubic has degree exactly 3.** The fourth finite difference vanishes: `tFn` is a
nonclassical polynomial of degree 3 (three differences reach the sign level, the fourth kills it). -/
theorem tCubic_fourthDiff :
    ∀ v, funcDerivG 0 (funcDerivG 0 (funcDerivG 0 (funcDerivG 0 tFn))) v = 0 := by decide

end FTQCLib.Explore.CubicPolarization

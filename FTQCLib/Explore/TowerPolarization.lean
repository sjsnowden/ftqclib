/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Explore.CubicPolarization

set_option linter.style.longLine false

/-! # The top finite difference is the sign level `2^{m-1}` — the whole tower

Generalizes `CubicPolarization` from the cubic data point to a **law across the 2-adic tower and both axes**,
confirming that the `ℤ/8` cubic sign `4` was not a coincidence but the pattern.

The frame's finite difference `funcDerivG` is the higher-order-Fourier additive derivative. A single-variable
"nonclassical polynomial" `v ↦ |v|` over `ZMod (2^m)` is the exponent of the precision-`m` gate on the root-of-`Z`
tower (`S` at `m=2`, `T` at `m=3`, `T^{1/2}` at `m=4`).

**Precision axis (this is the tower).** The `m`-fold finite difference of `|v|` over `ZMod (2^m)` is the constant
**`2^{m-1}`**, and the `(m+1)`-fold difference vanishes. So the exponent is a nonclassical polynomial of degree
exactly `m`, whose top coefficient is the **sign level** `2^{m-1}`:

* `m=2` (`S`, `ℤ/4`): `Δ² = 2`  — the quadratic Weil sign, the Clifford floor;
* `m=3` (`T`, `ℤ/8`): `Δ³ = 4`  — the cubic sign, one rung up;
* `m=4` (`T^{1/2}`, `ℤ/16`): `Δ⁴ = 8`.

Why `2^{m-1}`: it is the unique nonzero element of `ZMod (2^m)` fixed by negation (`+2^{m-1} = −2^{m-1}`), i.e. the
order-2 element `μ₂ ⊂ μ_{2^m}`. That the top difference lands exactly there is the algebraic reason it reads as a
*sign*, and it is why each degree needs one more 2-adic rung.

**Interaction axis (the multilinear side).** The degree-`d` multilinear monomial `v₀⋯v_{d-1}` over `ZMod 2` (the
`C^{d-1}Z` exponent) has `d`-fold finite difference the constant `1`, degree exactly `d`:

* `d=2` (`CZ`), `d=3` (`CCZ`), `d=4` (`CCCZ`).

All results are exact (`decide`); axiom-clean. This is the machine-checked form of "the tower is
literal, and the `(interaction, precision)` bigrading is the top-finite-difference structure of the
phase" — the data from which a cubic (and higher) Heisenberg cocycle would be built.
-/

namespace FTQCLib.Explore.TowerPolarization

open FTQCLib.Hierarchy FTQCLib.Hierarchy.BooleanMobius
open FTQCLib.Explore.CubicPolarization (cczFn tFn)

/-! ### Precision axis: `Δ^m |v| = 2^{m-1}` over `ZMod (2^m)` -/

/-- The `S`-phase exponent: `|v|` over `ZMod 4` (precision `m = 2`). -/
def sFn : (Fin 1 → ZMod 2) → ZMod 4 := fun v => ((v 0).val : ZMod 4)

/-- The `T^{1/2}`-phase exponent: `|v|` over `ZMod 16` (precision `m = 4`). -/
def thalfFn : (Fin 1 → ZMod 2) → ZMod 16 := fun v => ((v 0).val : ZMod 16)

/-- `m = 2`: the second difference of the `S`-phase is the quadratic sign `2 = 2^{2-1}` in `ZMod 4`
(the Clifford-floor Weil sign). -/
theorem sq_secondDiff : ∀ v, funcDerivG 0 (funcDerivG 0 sFn) v = 2 := by decide

/-- `m = 2`: the third difference vanishes — the `S`-phase has degree exactly 2. -/
theorem sq_thirdDiff : ∀ v, funcDerivG 0 (funcDerivG 0 (funcDerivG 0 sFn)) v = 0 := by decide

/-- `m = 4`: the fourth difference of the `T^{1/2}`-phase is the sign `8 = 2^{4-1}` in `ZMod 16`. -/
theorem thalf_fourthDiff :
    ∀ v, funcDerivG 0 (funcDerivG 0 (funcDerivG 0 (funcDerivG 0 thalfFn))) v = 8 := by decide

/-- `m = 4`: the fifth difference vanishes — the `T^{1/2}`-phase has degree exactly 4. -/
theorem thalf_fifthDiff :
    ∀ v, funcDerivG 0 (funcDerivG 0 (funcDerivG 0 (funcDerivG 0 (funcDerivG 0 thalfFn)))) v = 0 := by
  decide

/-! ### Interaction axis: `Δ^d (v₀⋯v_{d-1}) = 1` over `ZMod 2` -/

/-- The `CZ` exponent: `v₀·v₁` over `ZMod 2` (interaction degree 2). -/
def czFn : (Fin 2 → ZMod 2) → ZMod 2 := fun v => v 0 * v 1

/-- The `CCCZ` exponent: `v₀·v₁·v₂·v₃` over `ZMod 2` (interaction degree 4). -/
def ccczFn : (Fin 4 → ZMod 2) → ZMod 2 := fun v => v 0 * v 1 * v 2 * v 3

/-- `d = 2`: the second difference of the `CZ` exponent is the constant `1`. -/
theorem cz_secondDiff : ∀ v, funcDerivG 0 (funcDerivG 1 czFn) v = 1 := by decide

/-- `d = 4`: the fourth difference of the `CCCZ` exponent is the constant `1`. -/
theorem cccz_fourthDiff :
    ∀ v, funcDerivG 0 (funcDerivG 1 (funcDerivG 2 (funcDerivG 3 ccczFn))) v = 1 := by decide

end FTQCLib.Explore.TowerPolarization

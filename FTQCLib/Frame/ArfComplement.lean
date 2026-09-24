/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.SignedSymplectic
import FTQCLib.Frame.PrecisionValuation

set_option linter.style.longLine false

/-! # F1 — `−2·D` is the diagonal (Arf) half of the metaplectic sign

The frame's metaplectic sign defect `frameDistortion` (`FTQCLib/Frame/MetaplecticAction.lean`) is a symmetric `ZMod 4`
form with **zero diagonal** (`frameDistortion_self`) — the *alternating* (Arf-layer) half. The difference operator
satisfies `D² = −2·D` (`funcDerivG_funcDerivG`), a relation with a **nonzero** diagonal. So `−2·D ≠ frameDistortion`;
they are the two complementary sectors of the char-2 polarization. This file makes that precise.

The unifying fact (`coboundary_diagonal`): over an `𝔽₂`-space the diagonal of a polarization/coboundary is
`−2·(value)` — the Arf/quadratic-refinement datum. Two consequences pin the complementarity:

* `frameDistortion_diagonal` — on the **sign** carrier: `frameDistortion(g)(a,a) = −(2·s a)` for a `SignedSymplectic`
  `(g,s)`. The sign cochain `s` is `2`-torsion (`two_smul_s`), so this diagonal vanishes (`frameDistortion_self`):
  `frameDistortion` is the pure *alternating* half, carrying no Arf datum.
* `funcDerivG_diagonal` / `funcDerivG_diagonal_eq_zero_of_two_torsion` — on the **phase** carrier: the diagonal
  second difference is `−2·D f`; it vanishes for `2`-torsion (sign-sector) phases but is a genuine **nonzero** Arf
  datum for higher-precision (magic) phases (`funcDerivG_sq_ne_zero`).

So the `−2` is one object (the char-2 `a + a = 0`), appearing as `frameDistortion`'s (vanishing) sign-diagonal and as
the (nonvanishing) magic-phase diagonal `−2·D`. Gurevich–Hadani's char-2 Weil `2β` defect is the external reading:
this diagonal is the metaplectic square-root obstruction.
-/

open FTQCLib.Pauli FTQCLib.Cohomology FTQCLib.Hierarchy.BooleanMobius FTQCLib.Hierarchy.DiagPhase

namespace FTQCLib.Frame.Arf

variable {n : ℕ}

/-- **The diagonal of a coboundary is `−2·(value)` over an `𝔽₂`-space.** For `s : V → M` with `a + a = 0` and
`s 0 = 0`, the coboundary `δs(a,b) = s(a+b) − s a − s b` has diagonal `δs(a,a) = −2·s a`. This is the
Arf/quadratic-refinement datum: the diagonal of a polarization is `−2` times the quadratic value. -/
theorem coboundary_diagonal {V M : Type*} [AddCommGroup V] [AddCommGroup M] (s : V → M) (a : V)
    (ha : a + a = 0) (hs0 : s 0 = 0) :
    s (a + a) - s a - s a = (-2 : ℤ) • s a := by
  rw [ha, hs0]
  abel

/-- **The phase-side Arf datum is `−2·D`.** The diagonal second difference of a phase is `−2` times the linear
difference: `D²f = −2·D f` (`funcDerivG_funcDerivG`) — the diagonal of the phase polarization. -/
theorem funcDerivG_diagonal {A : Type*} [AddCommGroup A] (i : Fin n) (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG i f) = (-2 : ℤ) • funcDerivG i f :=
  funcDerivG_funcDerivG i f

/-- **The Arf datum vanishes for a `2`-torsion (sign-sector) phase.** If `2·f = 0` pointwise, the diagonal second
difference is `0`: the phase is pure-alternating, carrying no Arf datum — the phase-side image of
`frameDistortion`'s zero diagonal. -/
theorem funcDerivG_diagonal_eq_zero_of_two_torsion {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) (htor : ∀ v, (2 : ℤ) • f v = 0) :
    funcDerivG i (funcDerivG i f) = 0 := by
  have hlin : (2 : ℤ) • funcDerivG i f = 0 := by
    funext v
    simp only [Pi.smul_apply, funcDerivG_apply, smul_sub, htor, sub_zero, Pi.zero_apply]
  rw [funcDerivG_funcDerivG, neg_smul, hlin, neg_zero]

/-- **The metaplectic sign defect is `−2·(sign)`: `frameDistortion(g)(a,a) = −(2·s a)`** for a `SignedSymplectic`
`x = (g, s)`, from the crossed-hom law `valid`. The sign cochain `s` is the quadratic refinement, `frameDistortion`
its polarization, and the diagonal is `−2·s`. Since `s` is `2`-torsion (`two_smul_s`), this diagonal **vanishes**
(`frameDistortion_self`) — `frameDistortion` is the pure alternating half. The complementary diagonal Arf datum
`−2·D` is nonzero for higher-precision (magic) phases (`funcDerivG_sq_ne_zero`). -/
theorem frameDistortion_diagonal (x : SignedSymplectic n) (a : Pauli n) :
    frameDistortion x.g a a = -(2 * x.s a) := by
  have hs0 : x.s (0 : Pauli n) = 0 := by
    have h := x.valid 0 0
    rw [add_zero, frameDistortion_self, add_zero] at h
    linear_combination -h
  have h := x.valid a a
  rw [pauli_add_self, hs0] at h
  linear_combination -h

end FTQCLib.Frame.Arf

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BooleanMobius

/-! # Kernel frame — the difference calculus and the fundamental identity

Part of the **operational / difference route** for the kernel frame. This file
is the difference-calculus foundation the frame needs on top of the CGK results
(`FTQCLib.Hilbert.CGK*`):

* `funcDerivG_self_eq_neg_two_zsmul` / `frameDiff_self_eq_neg_two_zsmul` — the
  **same-direction identity** `Δ_a Δ_a = −2 · Δ_a`, the depth-for-degree trade.
* `frameDiff` — the **general-direction** difference `Δ_a f = f(·⊕a) − f`, the
  frame's derived difference operator (the single-coordinate `funcDerivG i` is
  the case `a = e_i`).
* `frameDiff_comp_affine` — the **fundamental identity**: differences commute
  with affine precomposition, with the difference direction transported by the
  *linear part*.

The moves themselves (affine precomposition as a syntactic action) and their
degree-monotonicity are not formalized in this file; what is here is the
fundamental identity and the same-direction difference law.
-/

namespace FTQCLib.Frame

open FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ}

/-- The **general-direction discrete difference** `Δ_a f := f(·⊕a) − f`, for a
direction `a : (F₂)ⁿ`. The frame's derived difference operator; the
single-coordinate `funcDerivG i` is exactly `frameDiff e_i`. -/
def frameDiff {A : Type*} [AddCommGroup A] (a : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → A) : (Fin n → ZMod 2) → A :=
  fun v => f (v + a) - f v

@[simp] lemma frameDiff_apply {A : Type*} [AddCommGroup A] (a : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → A) (v : Fin n → ZMod 2) :
    frameDiff a f v = f (v + a) - f v := rfl

/-- The single-coordinate derivative is the difference in the `e_i` direction. -/
lemma frameDiff_single_eq_funcDerivG {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    frameDiff (Pi.single i (1 : ZMod 2)) f = funcDerivG i f := rfl

/-- **Same-direction identity** (single coordinate). Repeating a difference
direction multiplies by `−2`: `Δ_i (Δ_i f) = −2 • Δ_i f`. The `−2` records the
depth-for-degree trade (each repeated halving costs one degree of the level).
Holds over *any* `AddCommGroup` codomain — the mechanism is the 2-torsion of the
**domain** `(F₂)ⁿ` (`e_i + e_i = 0`), not the codomain — so it covers both
`ZMod (2^m)` and the dyadic value group `ℤ[1/2]/ℤ`. Polymorphic companion of the
real-valued `funcDerivPhase_self_eq_neg_two_smul`. -/
theorem funcDerivG_self_eq_neg_two_zsmul {A : Type*} [AddCommGroup A] (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivG i (funcDerivG i f) = fun v => (-2 : ℤ) • funcDerivG i f v := by
  funext v
  have he : (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) + Pi.single i 1 = 0 := by
    rw [← Pi.single_add, show (1 : ZMod 2) + 1 = 0 from by decide, Pi.single_zero]
  have hv : v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) + Pi.single i 1 = v := by
    rw [add_assoc, he, add_zero]
  simp only [funcDerivG_apply]
  rw [hv]
  abel

/-- **Same-direction identity** (general direction): `Δ_a (Δ_a f) = −2 • Δ_a f`
for any direction `a`, since `a ⊕ a = 0` in `(F₂)ⁿ`. -/
theorem frameDiff_self_eq_neg_two_zsmul {A : Type*} [AddCommGroup A]
    (a : Fin n → ZMod 2) (f : (Fin n → ZMod 2) → A) :
    frameDiff a (frameDiff a f) = fun v => (-2 : ℤ) • frameDiff a f v := by
  funext v
  have ha : a + a = 0 := by
    funext j
    simpa using CharTwo.add_self_eq_zero (a j)
  have hv : v + a + a = v := by rw [add_assoc, ha, add_zero]
  simp only [frameDiff_apply]
  rw [hv]
  abel

/-- **Fundamental identity.** Discrete differences commute with affine
precomposition, the difference direction transported by the **linear part**: if
`Φ` shifts the direction `a` to `d` (i.e. `Φ(v ⊕ a) = Φ(v) ⊕ d` for all `v` —
the abstract form of "`d = A₀·a = Φ(a) ⊕ Φ(0)`" for an affine `Φ` with linear
part `A₀`), then `Δ_a (f ∘ Φ) = (Δ_d f) ∘ Φ`. This is the abstract form of the
identity `Δ_a(f∘A) = (Δ_{A₀a} f)∘A`. -/
theorem frameDiff_comp_affine {A : Type*} [AddCommGroup A] {k : ℕ}
    (Φ : (Fin k → ZMod 2) → (Fin n → ZMod 2)) (a : Fin k → ZMod 2)
    (d : Fin n → ZMod 2) (hΦ : ∀ v, Φ (v + a) = Φ v + d)
    (f : (Fin n → ZMod 2) → A) :
    frameDiff a (f ∘ Φ) = (frameDiff d f) ∘ Φ := by
  funext v
  simp only [frameDiff_apply, Function.comp_apply, hΦ]

end FTQCLib.Frame

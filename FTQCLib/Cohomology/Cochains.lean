/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # The cohomology of the frame: `H²(V, ℤ/4)`

The frame cocycle `betaFrame : V × V → ℤ/4` (`V = Pauli n`, the bit-vector register) is a genuine
2-cocycle (`betaFrame_cocycle`). This file builds the abstract object it lives in: the low-degree
group cohomology of `V` with trivial `ℤ/4` coefficients, as a self-contained ("bespoke") complex we
control, plus a bridge exhibiting `betaFrame` as a 2-cocycle in Mathlib's sense.

Conventions are pinned to the repo: `δ²` matches `betaFrame_cocycle` term-for-term, and `δ¹` matches
the stabilizer `valid` law `χ(p+q) = χ(p) + χ(q) + β(p,q)` (so on a Lagrangian `δ¹χ = −β|_L`). All
coefficients are `ℤ/4`; the cochain spaces are `ℤ/4`-modules (the register's `𝔽₂`-structure is *not*
used as module structure on cochains). -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli

variable {n : ℕ}

/-! ## Cochains and coboundary maps (trivial action) -/

/-- 1-cochains `V → ℤ/4`. -/
abbrev C1 (n : ℕ) : Type := Pauli n → ZMod 4
/-- 2-cochains `V × V → ℤ/4` (curried, matching `betaFrame`). -/
abbrev C2 (n : ℕ) : Type := Pauli n → Pauli n → ZMod 4
/-- 3-cochains `V × V × V → ℤ/4`. -/
abbrev C3 (n : ℕ) : Type := Pauli n → Pauli n → Pauli n → ZMod 4

/-- The 1-coboundary `(δ¹g)(p,q) = g p + g q − g(p+q)`. Orientation fixed by the `valid` law. -/
def delta1 : C1 n →ₗ[ZMod 4] C2 n where
  toFun g := fun p q => g p + g q - g (p + q)
  map_add' g h := by funext p q; simp only [Pi.add_apply]; ring
  map_smul' c g := by funext p q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The 2-coboundary `δ²`, with `(δ²f)(p,q,r) = f(q,r) − f(p+q,r) + f(p,q+r) − f(p,q)`. -/
def delta2 : C2 n →ₗ[ZMod 4] C3 n where
  toFun f := fun p q r => f q r - f (p + q) r + f p (q + r) - f p q
  map_add' f g := by funext p q r; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext p q r; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The complex condition `δ² ∘ δ¹ = 0`. -/
theorem delta2_comp_delta1 : (delta2 (n := n)).comp delta1 = 0 := by
  ext g p q r
  simp only [LinearMap.comp_apply, delta1, delta2, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.zero_apply, Pi.zero_apply, add_assoc]
  ring

/-! ## Cocycles, coboundaries, and `H²` -/

/-- 2-cocycles `Z² = ker δ²`. -/
def Z2 (n : ℕ) : Submodule (ZMod 4) (C2 n) := LinearMap.ker (delta2 (n := n))
/-- 2-coboundaries `B² = im δ¹`. -/
def B2 (n : ℕ) : Submodule (ZMod 4) (C2 n) := LinearMap.range (delta1 (n := n))

/-- Coboundaries are cocycles: `B² ≤ Z²`. -/
theorem B2_le_Z2 : B2 n ≤ Z2 n := by
  rintro f hf
  rw [B2, LinearMap.mem_range] at hf
  obtain ⟨g, rfl⟩ := hf
  rw [Z2, LinearMap.mem_ker, ← LinearMap.comp_apply, delta2_comp_delta1, LinearMap.zero_apply]

/-- **The second cohomology of the frame**, `H²(V, ℤ/4) = Z²/B²` (trivial action). -/
abbrev H2 (n : ℕ) : Type := Z2 n ⧸ ((B2 n).comap (Z2 n).subtype)

/-! ## `betaFrame` as a class -/

/-- `betaFrame` is a 2-cocycle (this is `betaFrame_cocycle` repackaged). -/
theorem betaFrame_mem_Z2 : (betaFrame : C2 n) ∈ Z2 n := by
  rw [Z2, LinearMap.mem_ker]
  funext p q r
  simp only [delta2, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
  exact betaFrame_cocycle p q r

/-- The cocycle `betaFrame`, as an element of `Z²`. -/
def betaZ2 (n : ℕ) : Z2 n := ⟨betaFrame, betaFrame_mem_Z2⟩

/-- **The frame class** `[betaFrame] ∈ H²(V, ℤ/4)`. -/
def betaClass (n : ℕ) : H2 n := Submodule.Quotient.mk (betaZ2 n)

/-! ## Bridge to Mathlib's group cohomology

Mathlib's group cohomology is multiplicative, so `V = Pauli n` is transported through
`Multiplicative`, with `ℤ/4` carrying the trivial action. Then `betaFrame` satisfies
`IsCocycle₂`, orientation matching `betaFrame_cocycle` term-for-term. Mathlib has no
extension/H² bijection yet, so classification stays native; this just certifies interop. -/

section MathlibBridge

open groupCohomology

/-- Trivial `ℤ/4`-action of the multiplicative register (coefficients acted on trivially). -/
local instance trivialSMul : SMul (Multiplicative (Pauli n)) (ZMod 4) := ⟨fun _ a => a⟩

/-- **`betaFrame` is a 2-cocycle in Mathlib's sense** — `IsCocycle₂` on `Multiplicative (Pauli n)`
with trivial `ℤ/4` coefficients, same orientation as the cocycle law. -/
theorem betaFrame_isCocycle₂ :
    IsCocycle₂ (fun x : Multiplicative (Pauli n) × Multiplicative (Pauli n) =>
      betaFrame (Multiplicative.toAdd x.1) (Multiplicative.toAdd x.2)) := by
  intro g h j
  change betaFrame (Multiplicative.toAdd g + Multiplicative.toAdd h) (Multiplicative.toAdd j)
        + betaFrame (Multiplicative.toAdd g) (Multiplicative.toAdd h)
      = betaFrame (Multiplicative.toAdd h) (Multiplicative.toAdd j)
        + betaFrame (Multiplicative.toAdd g) (Multiplicative.toAdd h + Multiplicative.toAdd j)
  linear_combination -betaFrame_cocycle (Multiplicative.toAdd g) (Multiplicative.toAdd h)
    (Multiplicative.toAdd j)

end MathlibBridge

end FTQCLib.Cohomology

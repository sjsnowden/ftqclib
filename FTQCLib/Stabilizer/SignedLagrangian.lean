/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle
import FTQCLib.Stabilizer.Defs

/-! # Frame-native signed Lagrangians — the `(L,χ)` chart, frame-pure

A `FrameSignedStab` is the symplectic chart `(L, χ)` built with **no Hilbert layer**: a
subspace `L` of Paulis and a sign `χ : Pauli n → ZMod 4` obeying the `betaFrame`-twisted
character law on `L`. On the Lagrangian, `χ` automatically lands in `{0,2}` — a real `±1`
(`two_smul_chi`); the full `μ₄` range is used only by the floor *amplitude* polynomial `q`
(a separate object), which encodes `χ` plus the symplectic shift data. The bridge to the
Hilbert `SignedStab` is separate, in `FTQCLib/Hilbert`. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer

variable {n : ℕ}

/-- The frame-native signed Lagrangian `(L,χ)`: a subspace `L` and a sign
`χ : Pauli n → ZMod 4` with the `betaFrame`-twisted character law on `L`. No Hilbert. -/
structure FrameSignedStab (n : ℕ) where
  L : Submodule (ZMod 2) (Pauli n)
  chi : Pauli n → ZMod 4
  chi_zero : chi 0 = 0
  valid : ∀ p ∈ L, ∀ q ∈ L, chi (p + q) = chi p + chi q + betaFrame p q

namespace FrameSignedStab

/-- On the Lagrangian each sign squares to one: `2 · χ g = 0`, i.e. `χ g ∈ {0,2}` (a real `±1`). -/
theorem two_smul_chi (S : FrameSignedStab n) {g : Pauli n} (hg : g ∈ S.L) :
    2 * S.chi g = 0 := by
  have h := S.valid g hg g hg
  rw [pauli_add_self, S.chi_zero, betaFrame_self, add_zero] at h
  rw [two_mul]; exact h.symm

end FrameSignedStab

/-- A *pure* frame signed Lagrangian: `L` a Lagrangian (isotropic, full rank `n`) and `χ` tight
(`= 0` off `L`). The frame-native analog of `PureSignedStab`. -/
structure FramePureSignedStab (n : ℕ) extends FrameSignedStab n where
  isStab : IsStabilizer toFrameSignedStab.L
  full : Module.finrank (ZMod 2) toFrameSignedStab.L = n
  tight : ∀ p, p ∉ toFrameSignedStab.L → toFrameSignedStab.chi p = 0

/-- A `FrameSignedStab` is determined by its `L` and `χ` (the laws are propositional). -/
theorem FrameSignedStab.ext' {A B : FrameSignedStab n} (hL : A.L = B.L) (hchi : A.chi = B.chi) :
    A = B := by
  obtain ⟨LA, cA, czA, vA⟩ := A
  obtain ⟨LB, cB, czB, vB⟩ := B
  subst hL; subst hchi
  rfl

/-- Two pure frame signed Lagrangians agree once their underlying `FrameSignedStab` do. -/
theorem framePureSignedStab_ext {S S' : FramePureSignedStab n}
    (h : S.toFrameSignedStab = S'.toFrameSignedStab) : S = S' := by
  cases S; cases S'; cases h; rfl

end FTQCLib.Frame

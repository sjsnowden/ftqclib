/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.AffinePushforward
import FTQCLib.Stabilizer.PauliCondition
import Mathlib.Data.Complex.Basic

/-! # The kernel-frame state carrier and its conditioning — pure frame

The kernel frame had a *gate* face (phase polynomials) but no *state* or *measurement* face. This file
supplies both, **purely in the frame** — phase-polynomial + `𝔽₂` data, no Hilbert:

* `KernelState` — a pure state named by (support coset `x₀ + π_X(L)`, exponent `q`, constant `c`). The
  exponent is *uncapped* in level, so it also holds the level-3 magic state `|A⟩ = T|+⟩`.
* `freezeAt` — the exponent restriction `X_j ↦ b` (the constant-substitution cousin of
  `affinePushforward`), with its eval-bridge.
* `KernelState.restrict` — the post-`Z`-measurement state, a **frame → frame** operation.

These are the native kernel-frame operations: a gadget is a composition of `affinePushforward` (CNOT)
and `restrict` (measurement) on exponents, and its correctness is a statement about `DiagPhase`. The
Hilbert *interpretation* (`psi`) and the *faithfulness certificate* (the Born projector — that `restrict`
is the real measurement) live separately in `FTQCLib/Hilbert/FrameConditioning.lean`; nothing here depends on
them. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-- A kernel-frame pure state: nonzero exactly on the affine coset `x₀ + π_X(L)`, where its amplitude is
`c · exp(i · realPhase q)`. The exponent `q : DiagPhase n m` is *uncapped* in level — level ≤ 2 for
stabilizer states (the bridge), level 3 for the magic `|A⟩`. The only `ℂ` is the amplitude constant `c`,
the sign/amplitude layer (the analog of `χ` in `(L,χ)`), not a Hilbert vector. -/
structure KernelState (n : ℕ) where
  m  : ℕ
  q  : DiagPhase n m
  c  : ℂ
  L  : Submodule (ZMod 2) (Pauli n)
  x₀ : Fin n → ZMod 2

variable {m : ℕ}

/-! ## `freezeAt` — the exponent restriction `X_j ↦ b` -/

/-- Freeze qubit `j`'s variable to the bit `b` in an exponent: the substitution `X_j ↦ b`. The
constant-substitution cousin of `affinePushforward` — no degree-raising cross term, so no `twoAdicVal`
accounting. This is the exponent half of conditioning on a `Z_j` outcome. -/
noncomputable def freezeAt (j : Fin n) (b : ZMod 2) (q : DiagPhase n m) : DiagPhase n m :=
  MvPolynomial.bind₁
    (fun l => if l = j then MvPolynomial.C ((b.val : ZMod (2 ^ m)))
      else MvPolynomial.X l) q

/-- **Eval-bridge:** freezing `X_j ↦ b` then evaluating at `v` equals evaluating at `v` with coordinate
`j` set to `b`. Mirrors `affinePushforward_eval`. -/
theorem freezeAt_eval (j : Fin n) (b : ZMod 2) (q : DiagPhase n m) (v : Fin n → ZMod 2) :
    (freezeAt j b q).eval v = q.eval (Function.update v j b) := by
  unfold DiagPhase.eval freezeAt
  have h := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
    (DiagPhase.liftBinary v)
    (fun l => if l = j then MvPolynomial.C ((b.val : ZMod (2 ^ m))) else MvPolynomial.X l) q
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  have hfun : (fun l : Fin n =>
      MvPolynomial.eval (DiagPhase.liftBinary v)
        (if l = j then MvPolynomial.C ((b.val : ZMod (2 ^ m))) else MvPolynomial.X l))
      = DiagPhase.liftBinary (Function.update v j b) := by
    funext l
    by_cases hlj : l = j
    · subst hlj
      simp [DiagPhase.liftBinary]
    · rw [if_neg hlj]
      simp [DiagPhase.liftBinary, Function.update_apply, hlj]
  rw [hfun]

/-! ## `restrict` — the native kernel-frame `Z`-measurement (frame → frame) -/

/-- The post-`Z_j`-measurement state with outcome `b`: condition the support on `Z_j`
(`pauliCondition` — drop the generators anticommuting with `Z_j`, adjoin `Z_j`), freeze the exponent
`X_j ↦ b`, and slice the coset offset to coordinate `j = b`. A pure frame → frame operation; no Hilbert.
-/
noncomputable def KernelState.restrict (K : KernelState n) (j : Fin n) (b : ZMod 2) : KernelState n where
  m  := K.m
  q  := freezeAt j b K.q
  c  := K.c
  L  := pauliCondition K.L (pauliz j)
  x₀ := Function.update K.x₀ j b

@[simp] theorem KernelState.restrict_q (K : KernelState n) (j : Fin n) (b : ZMod 2) :
    (K.restrict j b).q = freezeAt j b K.q := rfl

end FTQCLib.Frame

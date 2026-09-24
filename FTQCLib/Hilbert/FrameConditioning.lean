/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.KernelState
import FTQCLib.Hilbert.FrameKernel

/-! # The Hilbert interpretation of a kernel-frame state (the bridge)

The frame operations on `KernelState` (`freezeAt`, `restrict`) live in `FTQCLib/Hierarchy/KernelState.lean`
and use **no Hilbert**. This file supplies only the *interpretation* into the Hilbert layer (`psi`) —
the analog of `ev`/`stabProjector` for `(L,χ)`. It does not contain the faithfulness certificate
(the Born projector: that the frame `restrict` is the actual quantum measurement). The frame gadget
(`tGadget_correct`) does not depend on this file. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

open Classical in
/-- The state vector of a `KernelState`: the diagonal amplitude on its support coset. The
frame → Hilbert interpretation, for a faithfulness certificate (not given in this file) — never
used by the frame operations. -/
noncomputable def KernelState.psi (K : KernelState n) : QState n :=
  Hilbert.toQState (fun w =>
    if ∃ p ∈ K.L, w = K.x₀ + p.X then
      K.c * Complex.exp (Complex.I * (DiagPhase.realPhase K.q w : ℂ))
    else 0)

end FTQCLib.Frame

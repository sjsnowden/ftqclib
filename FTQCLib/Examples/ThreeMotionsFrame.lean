/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CharSumGates

/-! # The footprint of the three motions on the carrier (frame-pure, Step 0)

The three above-floor generators act on the carrier's data `(m, Q, c, L, x₀, h)`. This file records their
exact **footprint on the grade `h` and the support `(L, x₀)`** — the two fields that trichotomize the motions
cleanly, while the exponent `Q` is the shared amplitude substrate all three write:

| motion              | grade `h`   | support `(L, x₀)` | exponent `Q`            |
|---------------------|-------------|-------------------|-------------------------|
| diagonal (phase)    | fixed       | fixed             | `+= D` (add phase)      |
| Hadamard (Fourier)  | **`+1`**    | fixed             | adjoin var + coupling   |
| CNOT (permutation)  | fixed       | **moved**         | relabel free vars       |

So the motions are exactly distinguished by their `(h, support)` footprint: **diagonal fixes both** (the only
pure-phase motion), **Hadamard is the unique grade-grower**, **CNOT is the unique support-mover**. `Q` is
touched by all three (in three distinct modes — add-phase / adjoin-and-couple / relabel), so the correspondence
is "three modes with a signature footprint," not a partition of `Q`. Everything here is `rfl`. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Frame Complex

variable {n : ℕ}

/-! ## Diagonal (phase): fixes grade AND support — the only pure-phase motion -/

@[simp] theorem applyDiagSum_h (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagSum S D).h = S.h := rfl
@[simp] theorem applyDiagSum_L (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagSum S D).L = S.L := rfl
@[simp] theorem applyDiagSum_x0 (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagSum S D).x₀ = S.x₀ := rfl

/-! ## Hadamard (Fourier): the unique grade-grower; fixes support -/

theorem applyHFiner_grade (k : Fin n) (S : KernelSumState n) :
    (applyHFiner k S).h = S.h + 1 := rfl
@[simp] theorem applyHFiner_L (k : Fin n) (S : KernelSumState n) :
    (applyHFiner k S).L = S.L := rfl
@[simp] theorem applyHFiner_x0 (k : Fin n) (S : KernelSumState n) :
    (applyHFiner k S).x₀ = S.x₀ := rfl

/-! ## CNOT (permutation): the unique support-mover; fixes grade -/

@[simp] theorem applyCnotSum_h (i j : Fin n) (S : KernelSumState n) :
    (applyCnotSum i j S).h = S.h := rfl
theorem applyCnotSum_L (i j : Fin n) (S : KernelSumState n) :
    (applyCnotSum i j S).L = Submodule.map (cnotPauli i j) S.L := rfl
theorem applyCnotSum_x0 (i j : Fin n) (S : KernelSumState n) :
    (applyCnotSum i j S).x₀ = DiagPhase.cnotBitMap i j S.x₀ := rfl

end FTQCLib.Frame.Walkthrough

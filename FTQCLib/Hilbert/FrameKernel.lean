/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKForward
import FTQCLib.Hilbert.CGKGroupStructure
import FTQCLib.Hilbert.StabilizerEquiv
import FTQCLib.Hilbert.LemSpan
import FTQCLib.Hierarchy.FrameMoves

/-! # Kernel frame — the kernel map and the state-side carrier

The operator-side frame layer over the CGK results:

* `kernel` — the frame's diagonal kernel `K_P = |x⟩ ↦ e^{2πi·P(x)/2^m}|x⟩`.
* `kernel_add` — the **homomorphism law** `K_{P+Q} = K_P ∘ K_Q`.
* `kernel_conj_pauli` — the **difference law**: conjugating a kernel by the
  Pauli `q` shifts the phase by the discrete difference in direction `q.X`
  (`frameDiff q.X`). Re-read from `conjEquiv_diagonalGateEquiv_general` in the
  verified composition order.
* The **state-side carrier** in frame vocabulary: `Sector`, `ev`,
  `conditioning`, over `SignedStab` / `stabProjector` / `ludersChannel`.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

/-- The frame's **kernel** of an exponent `P`: the diagonal unitary
`|x⟩ ↦ e^{2πi·P(x)/2^m}|x⟩ = diagonalGateEquiv (realPhase P)`. -/
noncomputable def kernel {m : ℕ} (P : DiagPhase n m) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (DiagPhase.realPhase P)

lemma kernel_def {m : ℕ} (P : DiagPhase n m) :
    kernel P = diagonalGateEquiv (DiagPhase.realPhase P) := rfl

/-- **Kernel homomorphism**: adding exponents composes kernels,
`K_{P+Q} = K_P ∘ K_Q`. `realPhase` is additive only modulo `2π`, reconciled by
`realPhase_add_diff_int`. -/
theorem kernel_add {m : ℕ} (P Q : DiagPhase n m) :
    kernel (P + Q) = (kernel P).trans (kernel Q) := by
  symm
  simp only [kernel_def]
  rw [← diagonalGateEquiv_add]
  exact diagonalGateEquiv_eq_of_diff_two_pi (fun v => realPhase_add_diff_int P Q v)

/-- **Difference law**: conjugating a kernel by the Pauli `q` shifts the
phase by the discrete difference in direction `q.X` — the operator face of the
frame's `frameDiff`. For `Z`-type `q` (`q.X = 0`) the difference vanishes and the
kernel commutes with `q`. Re-read from `conjEquiv_diagonalGateEquiv_general`. -/
theorem kernel_conj_pauli {m : ℕ} (P : DiagPhase n m) (q : Pauli n) :
    conjEquiv (kernel P) (pauliEquiv q)
      = (diagonalGateEquiv (frameDiff q.X (DiagPhase.realPhase P))).trans (pauliEquiv q) := by
  simp only [kernel_def]
  exact conjEquiv_diagonalGateEquiv_general (DiagPhase.realPhase P) q

/-! ### State-side carrier — frame vocabulary over verified objects -/

/-- The frame's **sector** `(L, χ)`: a signed Lagrangian — a Lagrangian `L`, a
sign function `χ`, and the β-twisted character law. Verified content:
`SignedStab`. -/
abbrev Sector (n : ℕ) := SignedStab n

/-- The frame's **carrier evaluation**: a sector to its pure-state density. The
carrier `M̃` is the free `ℂ`-module on sectors; `ev` is `stabProjector`; the
relations are `ker ev`, and `ev` is onto `End` by `pureStabDensity_span_top`. -/
noncomputable abbrev ev (S : Sector n) : QState n →ₗ[ℂ] QState n := stabProjector S

/-- The frame's **conditioning operator** `C_{Q,ε}`: the two-sided selective
Lüders channel for measuring the Pauli `Q` with outcome sign `ε`. Verified
content: `ludersChannel`. -/
noncomputable abbrev conditioning (Q : Pauli n) (ε : ℂ) :
    (QState n →ₗ[ℂ] QState n) → (QState n →ₗ[ℂ] QState n) :=
  ludersChannel Q ε

end FTQCLib.Frame

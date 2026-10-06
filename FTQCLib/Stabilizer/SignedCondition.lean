/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.PauliCondition
import FTQCLib.Stabilizer.SignedLagrangian

/-!
# Conditioning a frame signed Lagrangian on a Pauli

Measuring a Pauli `Q` outside a signed Lagrangian `(L, χ)` and keeping the outcome with label `e`
(`e ∈ {0, 2}`, the sign `i^e = ±1` of `Q`) gives the Lagrangian `pauliCondition L Q` with the sign
`measChi`. Fix a witness `M ∈ L` with `ω(M, Q) = 1`; it reads which coset of `L ⊓ Q^⊥` an element
`g` of `pauliCondition L Q` lies in (`mem_K_of_omega_M_zero`, `mem_K_of_omega_M_one`):

* `ω(M, g) = 0`: `g ∈ L ⊓ Q^⊥` keeps its sign, `χ g`;
* `ω(M, g) = 1`: `g + Q ∈ L ⊓ Q^⊥`, and `g`'s sign is `e + χ(g + Q) + β(Q, g + Q)`, the outcome
  label plus the sign of `g + Q` plus the frame cocycle `betaFrame` of the product `Q · (g + Q)`;
* off `pauliCondition L Q` the sign is `0`.

This is the frame form of the Gottesman–Knill update: the sign is valued in `ZMod 4` with the
`betaFrame` cocycle, as `FrameSignedStab` is, and no Hilbert space enters. It is the rule
`FTQCLib.Hilbert.measSign` writes with the complex sign `i^χ` and `pauliPhase`, which is
`i^{betaFrame}`; the agreement of the two is a statement about the Hilbert bridge and is not made
here.

## Main definitions

* `measChi` — the sign after conditioning `(L, χ)` on `Q` with outcome label `e`, read by `M`.

## Main results

* `measChi_of_not_mem`, `measChi_of_omega_eq_zero`, `measChi_of_omega_eq_one` — its three cases.
* `measChi_self` — `Q` itself gets the outcome label.

## Implementation notes

* `measChi` is a function, not a `FrameSignedStab`: the character law of the result is not proved
  here. Where the result is read off a state (T12, `FTQCLib/Carrier/ConditionFloor.lean`), the
  state's own chart supplies it.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer

variable {n : ℕ}

open Classical in
/-- **The sign after conditioning on `Q`.** On `pauliCondition S.L Q`, the sign of `g` is `S.chi g`
where `ω(M, g) = 0`, and `e + S.chi (g + Q) + betaFrame Q (g + Q)` where `ω(M, g) = 1`; off it the
sign is `0`. Here `e` is the outcome label of `Q` and `M` the anticommuting witness. -/
noncomputable def measChi (S : FrameSignedStab n) (Q M : Pauli n) (e : ZMod 4) :
    Pauli n → ZMod 4 :=
  fun g => if g ∈ pauliCondition S.L Q then
    (if omega M g = 0 then S.chi g else e + S.chi (g + Q) + betaFrame Q (g + Q)) else 0

/-- Off the conditioned Lagrangian the sign is `0`. -/
theorem measChi_of_not_mem (S : FrameSignedStab n) (Q M : Pauli n) (e : ZMod 4) {g : Pauli n}
    (hg : g ∉ pauliCondition S.L Q) : measChi S Q M e g = 0 := by
  classical
  rw [measChi, if_neg hg]

/-- Where `ω(M, g) = 0` the sign is the input's. -/
theorem measChi_of_omega_eq_zero (S : FrameSignedStab n) (Q M : Pauli n) (e : ZMod 4)
    {g : Pauli n} (hg : g ∈ pauliCondition S.L Q) (hδ : omega M g = 0) :
    measChi S Q M e g = S.chi g := by
  classical
  rw [measChi, if_pos hg, if_pos hδ]

/-- Where `ω(M, g) = 1` the sign is the outcome label plus the sign of `g + Q` plus the cocycle. -/
theorem measChi_of_omega_eq_one (S : FrameSignedStab n) (Q M : Pauli n) (e : ZMod 4)
    {g : Pauli n} (hg : g ∈ pauliCondition S.L Q) (hδ : omega M g = 1) :
    measChi S Q M e g = e + S.chi (g + Q) + betaFrame Q (g + Q) := by
  classical
  rw [measChi, if_pos hg, if_neg (by rw [hδ]; exact one_ne_zero)]

/-- **The measured Pauli gets the outcome label.** -/
theorem measChi_self (S : FrameSignedStab n) {Q M : Pauli n} (e : ZMod 4) (hMQ : omega M Q = 1) :
    measChi S Q M e Q = e := by
  rw [measChi_of_omega_eq_one S Q M e (pauliCondition_mem S.L Q) hMQ, pauli_add_self, S.chi_zero,
    add_zero]
  -- `β(Q, 0)` and `β(Q, Q)` are the same sum, and the second is `0`.
  simpa [betaFrame] using betaFrame_self Q

end FTQCLib.Frame

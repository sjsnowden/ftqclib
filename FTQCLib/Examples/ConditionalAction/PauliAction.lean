/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.Inject

/-! # Conditional-action machinery: a Pauli action meeting a conditioning

The reusable lemmas of the conditioner / conditional-action layer — how applying a Pauli (an action one
might gate on a measured bit) interacts with a conditioning. These are conditioner-side: they describe
*acting*, not the raw measure-and-condition semantics (that lives in `FTQCLib/Examples/Conditioning/`), and
nothing here is error correction or even "correction" — just a Pauli action and a conditioning. No codes. -/

namespace FTQCLib.ConditionalAction

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Hilbert FTQCLib.Inject

/-- A Pauli conjugation preserves the Lagrangian (its symplectic image is the identity). -/
theorem cliffordAction_pauliEquiv_L {n : ℕ} (M : Pauli n) (S : SignedStab n) :
    (cliffordAction (isCliffordOperator_pauliEquiv M) S).L = S.L := by
  rw [cliffordAction_L, cliffordToSymplectic_pauliEquiv]; simp

/-- **`measSign` under a commuting Pauli action.** When the Pauli `M` commutes with the measured `Q`
(`ω(M,Q)=0`), the post-measurement sign of the `M`-conjugated state is `(-1)^{ω(M,g)}` times the
original — `M` flips signs uniformly and does not disturb the measurement structure. The `ω(M,Q)=0`
hypothesis is what makes the coset branch line up (`ω(M,g+Q)=ω(M,g)`). -/
theorem measSign_cliffordAction_pauliEquiv {n : ℕ} (M : Pauli n) (S : SignedStab n) {Q N : Pauli n}
    (hMQ : omega M Q = 0) (ε : ℂ) (g : Pauli n) :
    measSign (cliffordAction (isCliffordOperator_pauliEquiv M) S) Q N ε g
      = (-1 : ℂ) ^ (omega M g).val * measSign S Q N ε g := by
  simp only [measSign]
  rw [cliffordAction_pauliEquiv_L]
  by_cases hg : g ∈ pauliCondition S.L Q
  · rw [if_pos hg, if_pos hg]
    by_cases hδ : omega N g = 0
    · rw [if_pos hδ, if_pos hδ, cliffordAction_pauliEquiv_sign]
    · rw [if_neg hδ, if_neg hδ, cliffordAction_pauliEquiv_sign,
        show omega M (g + Q) = omega M g from by rw [omega_add_right, hMQ, add_zero]]
      ring
  · rw [if_neg hg, if_neg hg]; ring

/-- **A commuting Pauli action passes through the conditioning.** Measuring `Q` (witness `N`) then
applying a Pauli `M` with `ω(M,Q)=0` equals applying `M` first and then measuring `Q`. So actions on
*other* commuting observables do not disturb the `Q`-measurement. -/
theorem commutingCorrection_passesThrough {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    {N : Pauli n} (hN : N ∈ S.toSignedStab.L) (hNQ : omega N Q = 1)
    (M : Pauli n) (hMQ : omega M Q = 0) :
    cliffordActionPure (isCliffordOperator_pauliEquiv M) (injStepWith S hQ hε N hN hNQ)
      = injStepWith (cliffordActionPure (isCliffordOperator_pauliEquiv M) S)
          (by rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_L]; exact hQ) hε N
          (by rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_L]; exact hN) hNQ := by
  apply pureSignedStab_ext
  apply signedStab_ext
  · simp only [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_L, injStepWith_L]
  · funext g
    rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_sign]
    change (-1 : ℂ) ^ (omega M g).val * measSign S.toSignedStab Q N ε g
      = measSign (cliffordActionPure (isCliffordOperator_pauliEquiv M) S).toSignedStab Q N ε g
    rw [cliffordActionPure_toSignedStab, measSign_cliffordAction_pauliEquiv M S.toSignedStab hMQ]

/-- `injStepWith` depends on the input state as *data* only; its hypotheses are proof-irrelevant. So an
equal input gives an equal conditioned state (this lets us rewrite the state inside a conditioning). -/
theorem injStepWith_congr_state {n : ℕ} {S S' : PureSignedStab n} (hSS : S = S') {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) (hQ' : Q ∉ S'.toSignedStab.L) {ε : ℂ} (hε : ε * ε = 1)
    {M : Pauli n} (hM : M ∈ S.toSignedStab.L) (hM' : M ∈ S'.toSignedStab.L) (hMQ : omega M Q = 1) :
    injStepWith S hQ hε M hM hMQ = injStepWith S' hQ' hε M hM' hMQ := by
  subst hSS; rfl

end FTQCLib.ConditionalAction

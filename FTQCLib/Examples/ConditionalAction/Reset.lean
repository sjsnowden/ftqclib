/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.Inject

/-! # The reconverging branch — conditional correction in the `(L,χ)` frame

The genuinely new control mechanism the operation monoid lacks: a move that **branches on the
measured outcome**. Every operation-monoid element is a single, non-branching map; a measurement
followed by an *outcome-dependent* Pauli correction is not. This file builds that move in its
cleanest, most general form, and shows it **reconverges** — both outcomes are made to agree.

The key fact is sharp: the correction that undoes a measurement's outcome-dependence is (a Pauli
equal to) the **anticommuting witness** `M` itself. Conditioning on `Q` writes the outcome `ε` into
the sign on the `Q`-coset (the generators `g` with `ω(M,g)=1`); applying the Pauli `M` multiplies
each sign by `(-1)^{ω(M,g)}`, which is `-1` exactly on that coset and `+1` elsewhere. The two
effects line up perfectly, so the correction **flips the outcome** `ε ↦ -ε` with no disentanglement
bookkeeping, and the `+1` and `-1` branches reconverge to one state — the frame-side content of
"the branch collapses immediately."

This is the loop's reset step (`reset to |0⟩` is the single-qubit instance, with witness =
correction = `X`), and it is feed-forward stated as an *operation* rather than only read off the
sign. The loop's *iteration* and its *cost* live above the frame and are not treated here; this is
the frame's whole say on branching. -/

namespace FTQCLib.Reset

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Hilbert FTQCLib.Teleport FTQCLib.Inject

/-- **The witness correction flips the measurement outcome.** Condition on `Q` (outcome `ε`), then
apply the anticommuting witness `M` as a Pauli correction: the result is the *opposite-outcome*
conditioned state. The support is unchanged (Pauli conjugation is symplectically trivial); on the
`Q`-coset the `(-1)` from `M`'s sign-flip turns `ε` into `-ε`, and off the coset both factors are
trivial. -/
theorem witnessCorrection_flips_outcome {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {M : Pauli n} (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1)
    {ε : ℂ} (hε : ε * ε = 1) :
    cliffordActionPure (isCliffordOperator_pauliEquiv M) (injStepWith S hQ hε M hM hMQ)
      = injStepWith S hQ (show (-ε) * (-ε) = 1 by rw [neg_mul_neg]; exact hε) M hM hMQ := by
  apply pureSignedStab_ext
  apply signedStab_ext
  · -- support: Pauli conjugation preserves `L`, both sides are `pauliCondition S.L Q`
    rw [cliffordActionPure_toSignedStab, cliffordAction_L, cliffordToSymplectic_pauliEquiv]
    simp [injStepWith_L]
  · -- sign: `(-1)^{ω(M,g)}` flips exactly the `ε`-carrying (coset) signs
    funext g
    rw [cliffordActionPure_toSignedStab, cliffordAction_pauliEquiv_sign]
    by_cases hg : g ∈ pauliCondition S.toSignedStab.L Q
    · by_cases hδ : omega M g = 1
      · have hv : (omega M g).val = 1 := by rw [hδ]; decide
        rw [injStepWith_sign_of_one S hQ hε M hM hMQ hg hδ,
            injStepWith_sign_of_one S hQ (show (-ε) * (-ε) = 1 by rw [neg_mul_neg]; exact hε)
              M hM hMQ hg hδ, hv]
        ring
      · have hδ0 : omega M g = 0 := (by decide : ∀ a : ZMod 2, a ≠ 1 → a = 0) _ hδ
        have hv : (omega M g).val = 0 := by rw [hδ0]; decide
        rw [injStepWith_sign_of_zero S hQ hε M hM hMQ hg hδ0,
            injStepWith_sign_of_zero S hQ (show (-ε) * (-ε) = 1 by rw [neg_mul_neg]; exact hε)
              M hM hMQ hg hδ0, hv]
        ring
    · rw [(injStepWith S hQ hε M hM hMQ).tight g hg,
          (injStepWith S hQ (show (-ε) * (-ε) = 1 by rw [neg_mul_neg]; exact hε) M hM hMQ).tight g hg]
      ring

/-- **The reconverging branch.** Measure `Q`; on the `-1` outcome apply the witness correction
`M`; the result equals the (uncorrected) `+1` outcome. So a measure-then-correct step is
outcome-independent — the two branches collapse to one state. (`ε = -1` in
`witnessCorrection_flips_outcome`; `-(-1) = 1`.) -/
theorem branch_reconverges {n : ℕ} (S : PureSignedStab n) {Q : Pauli n}
    (hQ : Q ∉ S.toSignedStab.L) {M : Pauli n} (hM : M ∈ S.toSignedStab.L) (hMQ : omega M Q = 1) :
    cliffordActionPure (isCliffordOperator_pauliEquiv M)
        (injStepWith S hQ (by norm_num : (-1 : ℂ) * (-1) = 1) M hM hMQ)
      = injStepWith S hQ (by norm_num : (1 : ℂ) * 1 = 1) M hM hMQ := by
  have h := witnessCorrection_flips_outcome S hQ hM hMQ (show (-1 : ℂ) * (-1) = 1 by norm_num)
  simp only [neg_neg] at h
  exact h

/-! ## The canonical instance: reset `|+⟩ → |0⟩`

The textbook "measure `Z`, apply `X` on the `|1⟩` outcome, land in `|0⟩` regardless." Here the
anticommuting witness *is* the physical correction `X`, so `branch_reconverges` specializes exactly. -/

/-- The `|+⟩` Lagrangian `⟨X₀⟩` on one qubit. -/
noncomputable def plusL : Submodule (ZMod 2) (Pauli 1) := Submodule.span (ZMod 2) {paulix 0}

theorem plusL_isStabilizer : IsStabilizer plusL :=
  isStabilizer_span_of_pairwise (by
    intro p hp q hq
    simp only [Set.mem_singleton_iff] at hp hq
    subst hp; subst hq; decide)

theorem plusL_finrank : Module.finrank (ZMod 2) plusL = 1 :=
  finrank_span_singleton (by decide : (paulix 0 : Pauli 1) ≠ 0)

/-- The `|+⟩` state as a pure signed Lagrangian. -/
noncomputable def plusState : PureSignedStab 1 := mkPureSlab plusL_isStabilizer plusL_finrank

theorem Z0_not_mem : pauliz 0 ∉ plusState.toSignedStab.L := by
  show pauliz 0 ∉ plusL
  intro h
  have h0 : omega (pauliz 0) (paulix 0) = 0 :=
    plusL_isStabilizer (pauliz 0) h (paulix 0) (Submodule.subset_span (by simp))
  rw [show omega (pauliz 0) (paulix 0) = 1 from by decide] at h0
  exact one_ne_zero h0

theorem X0_mem : paulix 0 ∈ plusState.toSignedStab.L :=
  Submodule.subset_span (by simp)

/-- **Reset is outcome-independent:** measuring `Z₀` on `|+⟩` and applying the `X₀` correction on the
`-1` outcome lands in the same state as the `+1` outcome (`|0⟩`) — the branch reconverges. -/
theorem resetPlus_outcome_indep :
    cliffordActionPure (isCliffordOperator_pauliEquiv (paulix 0))
        (injStepWith plusState Z0_not_mem (by norm_num : (-1 : ℂ) * (-1) = 1)
          (paulix 0) X0_mem (by decide))
      = injStepWith plusState Z0_not_mem (by norm_num : (1 : ℂ) * 1 = 1)
          (paulix 0) X0_mem (by decide) :=
  branch_reconverges plusState Z0_not_mem X0_mem (by decide)

end FTQCLib.Reset

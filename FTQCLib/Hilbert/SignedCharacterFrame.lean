/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.SignedCharacterWitness
import FTQCLib.Frame.MetaplecticAction
import FTQCLib.Hilbert.FrameSignedBridge

set_option linter.unusedSectionVars false

/-!
# The Hilbert sign character IS the frame's sign cochain (the S gate / `τ_{Z_k}`)

The first quantitative bridge between a Clifford operator's trace-level sign data and the frame's
native ℤ/4 cochain layer:

* `cliffordSign_phaseGate_eq_frame` — **globally in `r`, every `n`, every `k`**:
  `cliffordSign (S_k) r = iZ4 (tvSignZ k r)` — the Hilbert-side conjugation sign of the phase gate
  equals the `iZ4`-image of the frame's transvection sign cochain `2·X_k·Z_k`.
* `phase_trace_frame` — the payoff: `Tr(S_k)·Tr(S_k⁻¹)` **is a frame-pure character sum** — the
  signed character formula (`SignedCharacter.lean`) with every Hilbert sign replaced by the frame
  cochain.

The proof needs one operator evaluation — pinning the conjugation phase `α = i` at the single
label `X_k` by evaluating `S·P_X·S⁻¹` on a delta vector (`GateLifts`' phase unit is private; its
value is *extracted* through a unit-quantified lemma, not imported) — after which the general case
is the `xz`-weight localization at `k` plus a four-case check on the `k`-bits.

**The lift choice:** the frame's design shares ONE cochain `tvSignZ`
across the `Z`/`X`/`Y` transvections (`tvSign_validity{,_X,_Y}`). For `τ_{Z_k}` the matching
Hilbert lift is exactly `phaseGate k` (this file). For `τ_{X_k}` the naive lift `H·S·H` does
**not** match: `(HSH)·Z·(HSH)⁻¹ = −Y` gives `μ_{HSH}(Z_k) = −1` while `iZ4 (tvSignZ k (Z_k)) = +1`.
Since lifts of a fixed symplectic map sweep all `(−1)^{ω(w,·)}`-twists of the sign character, the
frame cochain **selects a specific lift** in each fiber — for `τ_{X_k}` a Pauli multiple of
`HSH`, not `HSH` itself. The selected `X`/`Y` lifts are identified in
`SignedCharacterSelection.lean`; that does not affect this file's identification.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame Complex

variable {n : ℕ}

/-! ## The `xz`-weight localizes at `k` under `phaseAt` -/

/-- Off `k`, `phaseAt` changes nothing, so the `I`-power ratio of the two `xz`-weights is carried
entirely by the `k`-terms. -/
lemma iPow_xzWeight_phaseAt (k : Fin n) (r : Pauli n) :
    Complex.I ^ xzWeight r * (Complex.I ^ xzWeight (phaseAt k r))⁻¹
      = Complex.I ^ ((r.Z k).val * (r.X k).val)
          * (Complex.I ^ ((r.Z k + r.X k).val * (r.X k).val))⁻¹ := by
  classical
  have hsplit : ∀ p : Pauli n, xzWeight p
      = (p.Z k).val * (p.X k).val + ∑ i ∈ Finset.univ.erase k, (p.Z i).val * (p.X i).val := by
    intro p
    unfold xzWeight zDotVal
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have hoff : (∑ i ∈ Finset.univ.erase k, ((phaseAt k r).Z i).val * ((phaseAt k r).X i).val)
      = ∑ i ∈ Finset.univ.erase k, (r.Z i).val * (r.X i).val := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [phaseAt_X, phaseAt_Z, Function.update_of_ne hik]
  have hk : ((phaseAt k r).Z k).val * ((phaseAt k r).X k).val
      = (r.Z k + r.X k).val * (r.X k).val := by
    rw [phaseAt_X, phaseAt_Z, Function.update_self]
  rw [hsplit r, hsplit (phaseAt k r), hk, hoff, pow_add, pow_add, mul_inv]
  have hI : (Complex.I ^ (∑ i ∈ Finset.univ.erase k, (r.Z i).val * (r.X i).val)) ≠ 0 :=
    pow_ne_zero _ Complex.I_ne_zero
  field_simp

/-! ## The phase-unit extraction: `α = i` at the label `X_k` -/

/-- The delta vector at a computational point. -/
noncomputable def deltaQ (v : Fin n → ZMod 2) : QubitSpace n := Pi.single v 1

/-- **Pin the conjugation phase of `S_k` at `X_k` to `i`** by one operator evaluation: apply both
sides of the conjugation law to `δ_0` and read the coordinate `e_k`. The left side picks up
`exp(iπ/2) = i` from the diagonal gate at `e_k`; the right side is the bare unit. Quantifying
over the unit extracts the value of `GateLifts`' private phase constant without naming it. -/
lemma phase_unit_eq (k : Fin n) {u : ℂˣ}
    (hconj : (conjEquiv (phaseGate k) (pauliEquiv (paulix k))).toLinearMap
      = (u : ℂ) • pauliOperator (phaseAt k (paulix k))) :
    (u : ℂ) = Complex.I := by
  classical
  have hLHS : (conjEquiv (phaseGate k) (pauliEquiv (paulix k))).toLinearMap (deltaQ 0)
      (Pi.single k 1) = Complex.I := by
    show (phaseGate k) ((pauliOperator (paulix k)) ((phaseGate k).symm (deltaQ 0))) (Pi.single k 1)
      = Complex.I
    have hSinv : (phaseGate k).symm (deltaQ 0) = deltaQ 0 := by
      funext v
      show Complex.exp (Complex.I * (-(Real.pi / 2 * ((v k).val : ℝ)) : ℝ)) * deltaQ 0 v
        = deltaQ 0 v
      by_cases hv : v = 0
      · subst hv
        simp [deltaQ]
      · rw [show deltaQ (0 : Fin n → ZMod 2) v = 0 from by
          unfold deltaQ
          rw [Pi.single_apply, if_neg hv], mul_zero]
    have hPX : (pauliOperator (paulix k)) (deltaQ 0) = deltaQ (Pi.single k 1) := by
      funext w
      show ((-1 : ℂ)) ^ (zDotVal (paulix k) (w - (paulix k).X)) * deltaQ 0 (w - (paulix k).X)
        = deltaQ (Pi.single k 1) w
      rw [show zDotVal (paulix k) (w - (paulix k).X) = 0 from by
        unfold zDotVal
        rw [paulix_Z]
        simp, pow_zero, one_mul]
      unfold deltaQ
      rw [Pi.single_apply, Pi.single_apply, paulix_X]
      by_cases hw : w = Pi.single k 1
      · rw [if_pos (by rw [hw]; abel), if_pos hw]
      · rw [if_neg (fun hc => hw (by
          have := congrArg (· + (Pi.single k 1 : Fin n → ZMod 2)) hc
          simpa [sub_add_cancel] using this)), if_neg hw]
    rw [hSinv, hPX]
    show Complex.exp (Complex.I * ((Real.pi / 2 * (((Pi.single k 1 : Fin n → ZMod 2) k).val : ℝ)
        : ℝ) : ℂ)) * deltaQ (Pi.single k 1) (Pi.single k 1) = Complex.I
    rw [show ((Pi.single k 1 : Fin n → ZMod 2) k) = 1 from by simp,
      show ((1 : ZMod 2)).val = 1 from by decide]
    rw [show deltaQ (Pi.single k (1 : ZMod 2)) (Pi.single k 1) = 1 from by
      unfold deltaQ; simp, mul_one]
    rw [show (Real.pi / 2 * ((1 : ℕ) : ℝ) : ℝ) = Real.pi / 2 from by push_cast; ring]
    exact exp_I_pi_div_two
  have hRHS : ((u : ℂ) • pauliOperator (phaseAt k (paulix k))) (deltaQ 0) (Pi.single k 1)
      = (u : ℂ) := by
    have hp : (pauliOperator (phaseAt k (paulix k))) (deltaQ 0) (Pi.single k 1) = 1 := by
      show ((-1 : ℂ)) ^ (zDotVal (phaseAt k (paulix k))
          ((Pi.single k 1) - (phaseAt k (paulix k)).X))
          * deltaQ 0 ((Pi.single k 1) - (phaseAt k (paulix k)).X) = 1
      rw [phaseAt_X, paulix_X, sub_self]
      rw [show zDotVal (phaseAt k (paulix k)) (0 : Fin n → ZMod 2) = 0 from by
        unfold zDotVal; simp, pow_zero, one_mul]
      show deltaQ (0 : Fin n → ZMod 2) 0 = 1
      unfold deltaQ
      simp
    have happ : ((u : ℂ) • pauliOperator (phaseAt k (paulix k))) (deltaQ 0) (Pi.single k 1)
        = (u : ℂ) * ((pauliOperator (phaseAt k (paulix k))) (deltaQ 0) (Pi.single k 1)) := by
      simp [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [happ, hp, mul_one]
  have h2 := congrFun (LinearMap.congr_fun hconj (deltaQ 0)) (Pi.single k 1)
  exact (hLHS.symm.trans (h2.trans hRHS)).symm

/-! ## The identification, globally in `r` -/

/-- **The S-gate sign character IS the frame's transvection sign cochain**, globally: for every
`n`, every qubit `k`, and every Pauli label `r`,
`cliffordSign (S_k) r = iZ4 (tvSignZ k r) = i^{2·X_k(r)·Z_k(r)} = (−1)^{X_k(r)·Z_k(r)}`. -/
theorem cliffordSign_phaseGate_eq_frame (k : Fin n) (r : Pauli n) :
    cliffordSign (isCliffordOperator_phaseGate k) r = iZ4 (tvSignZ k r) := by
  classical
  -- extract the phase-unit value from the `X_k` instance
  have hux := phaseGate_conj k (paulix k)
  rw [show ((paulix k).X k).val = 1 from by rw [paulix_X]; simp, pow_one] at hux
  have hval := phase_unit_eq k hux
  -- the sign at `r` via the conjugation law, unit replaced by `i`
  have h := cliffordSign_eq_of_conj (isCliffordOperator_phaseGate k) (phaseGate_conj k r)
  rw [Units.val_pow_eq_pow_val, hval] at h
  rw [h, mul_right_comm, iPow_xzWeight_phaseAt,
    show tvSignZ k r = ((2 * ((r.X k).val * (r.Z k).val) : ℕ) : ZMod 4) from by
      unfold tvSignZ; push_cast; ring,
    iZ4_natCast]
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hval1 : ((1 : ZMod 2)).val = 1 := by decide
  have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
  have h2v : ((2 : ZMod 2)).val = 0 := by decide
  rcases hcases (r.X k) with hx | hx <;> rcases hcases (r.Z k) with hz | hz <;>
    rw [hx, hz] <;>
    norm_num [hval1, h11, h2v, Complex.inv_I, Complex.I_mul_I, Complex.I_sq]

/-- The frame cochain vanishes on the fixed labels of the shear — the frame-side face of
`cliffordSign_phase_of_fixed` (the two sides agree on `Fix` for the trivial reason that both
are `1` there; the content of the identification is off `Fix`, where `μ(Y_k) = −1` is matched
by `tvSignZ = 2`). -/
lemma tvSignZ_eq_zero_of_fixed (k : Fin n) {p : Pauli n} (hp : phaseAt k p = p) :
    tvSignZ k p = 0 := by
  have hx : p.X k = 0 := (phaseAt_fixed_iff k p).mp hp
  unfold tvSignZ
  rw [hx]
  simp

/-! ## The payoff: the trace of `S_k` is a frame-pure character sum -/

/-- **`Tr(S_k)·Tr(S_k⁻¹) = Σ_{fixed p} iZ4 (tvSignZ k p)`** — the signed character
formula for the phase gate with every Hilbert sign replaced by the frame's native ℤ/4 cochain.
The trace product of a Clifford operator, a Hilbert quantity, is computed by a sum the frame
already owns. -/
theorem phase_trace_frame (k : Fin n) :
    LinearMap.trace ℂ (QState n) (qClifford (phaseGate k)).toLinearMap
        * LinearMap.trace ℂ (QState n) (qClifford (phaseGate k)).symm.toLinearMap
      = ∑ p ∈ Finset.univ.filter
          (fun p : Pauli n =>
            cliffordToSymplecticFun (isCliffordOperator_phaseGate k) p = p),
          iZ4 (tvSignZ k p) := by
  classical
  rw [signed_trace_mul_trace_inv (isCliffordOperator_phaseGate k)]
  exact Finset.sum_congr rfl fun p _ => cliffordSign_phaseGate_eq_frame k p

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ConditionFloor
import FTQCLib.Hilbert.ProtocolSemantics
import FTQCLib.Hilbert.MeasurementCollapse
import FTQCLib.Hilbert.FrameSignedBridge

/-!
# Soundness of conditioning: the frame's projection is the Born projector

T19 (`docs/TARGETS.md`): the Hilbert image of T10's output is the Born projector applied to the
image of the input; and through the bridge `frameToHilbert`, T12's frame update of a chart agrees
with the Hilbert measurement update `measSignedStab`, so T12's chart theorem, stated frame-pure,
carries over (`docs/STEPS.md`, entry 2026-09-30f).

**The image.** The Hilbert image of a carrier state `S` is its amplitude `amp S`, a function in
`QubitSpace n = (Fin n → ZMod 2) → ℂ`, read in `QState n` through `toQState`, which is the identity
on functions and changes only the norm (`Hilbert/Inner.lean`). The transport is written in the
statements because `bornProjector` and `pauliHermitian` are maps on `QState n`.

**The Pauli conventions.** The frame acts by
`SignedPauli.act P f w = (−1)^sign · pauliAct P.pauli f w`, with
`pauliAct g f w = i^{yWeight g} · (−1)^{zDot g (w + g.X)} · f (w + g.X)`
(`Stabilizer/AmplitudeStabilizer.lean`). The Hilbert side has `pauliHermitian p = i^{xzWeight p} •
qPauli p` with `qPauli p ψ w = (−1)^{zDotVal p (w − p.X)} · ψ (w − p.X)` (`Hilbert/Inner.lean`).
`xzWeight` is `yWeight` and `zDotVal` is `zDot`, both by definition, and `w − p.X = w + p.X` over
`ZMod 2`; so the two are the same operator, the textbook `i^{x·z} X^x Z^z`, and no sign or phase
changes between them (`docs/fidelity/T19.md`, first point). `toQState_pauliAct` and
`toQState_signedPauliAct` record this in the module.

**The label.** The Born projector of the outcome `b` of a signed Pauli `P` is
`bornProjector P.pauli ε` at `ε = (−1)^{sign + b}`, written `(−1)^{sign.val + b.val}` as T17's
`bornProjection` writes it (`Hilbert/ProtocolSemantics.lean`), so that T20 composes the two
without a rewrite of the exponent. The chart statement's label is `i^{outcomeChi P b}`, which is
`iZ4 (outcomeChi P b)`; it is the same number (`iZ4_outcomeChi`, from `I_pow_outcomeChi`), and
it squares to one (`iZ4_outcomeChi_mul_self`), the hypothesis `hε` of `measSignedStab`.

**The chart statement.** `measChi` (`Stabilizer/SignedCondition.lean`) is a function, not a chart,
so "a chart whose sign is `measChi`" is a `FramePureSignedStab` `C` with
`C.L = pauliCondition C₀.L Q` and `C.chi = measChi C₀.toFrameSignedStab Q M (outcomeChi P b)`, for
the input's chart `C₀` and `Q = P.pauli`. `frameToHilbert` returns a `PureSignedStab` and
`measSignedStab` a `SignedStab`, so the equality is of `(frameToHilbert C).toSignedStab`. The
hypotheses `Q ∉ C₀.L`, `M ∈ C₀.L` and `ω(M, Q) = 1` are those of `measSignedStab` and of T12's
`condition_eq_pauliCondition`; the case `Q ∈ C₀.L`, a certain or impossible outcome, has no
`measSignedStab` and is T12's own.

## Main results

* `pauliProjection_eq_bornProjector` — the frame's projection `pauliProjection P b` is
  `bornProjector P.pauli ((−1)^{sign + b})` through `toQState` (proved at T19.3).
* `toQState_amp_condition` — the Hilbert image of T10's output `condition S P b` is the Born
  projector applied to the image of `S`, for a co-isotropic Lagrangian (the hypothesis of
  `amp_condition`).
* `pauliProjection_eq_bornProjection` — the same, as functions on `QubitSpace n`, against T17's
  conditioning letter's projector `bornProjection P b`.
* `frameToHilbert_measChi` — `frameToHilbert` of a chart whose sign is `measChi` is
  `measSignedStab` at the label `i^{outcomeChi P b}` (proved at T19.3).
* `frameToHilbert_chartOf_condition` — T12's chart theorem `condition_eq_pauliCondition` carried
  through the bridge: the conditioned floor's chart is the Hilbert measurement update of the input
  floor's chart.

## Implementation notes

* `toQState_pauliAct` is proved here, pointwise, since it is the convention check the target
  names; the theorems that follow from the two headlines by composition are proved from them, so
  each depends on `sorryAx` until T19.3 proves the headline it uses.
* The chart statement is an equality of `SignedStab`; its proof is `signedStab_ext` on `L` (by the
  hypothesis on `C.L`) and on `sign`, in the three cases of `measChi` and `measSign`, which test the
  same conditions (`docs/fidelity/T19.md`, Claim 7), with `iZ4_add` and
  `pauliPhase_eq_iZ4_betaFrame` in the third.

## References

* D. Gottesman, *Stabilizer codes and quantum error correction*, quant-ph/9705052, section "The
  Effects of Measurements": the measurement update of a stabilizer.
* D. Gottesman, *The Heisenberg representation of quantum computers*, quant-ph/9807006, section
  "Measurements": the projector `½(I ± A)` of a Pauli measurement.
-/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer FTQCLib.Frame
  FTQCLib.Frame.Walkthrough

variable {n : ℕ}

/-! ## The Pauli conventions -/

/-- Over `ZMod 2`, subtracting a word is adding it. -/
private theorem sub_eq_add_word (w v : Fin n → ZMod 2) : w - v = w + v := by
  funext i
  rw [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- **The frame's Pauli action is the Hermitian Pauli.** `pauliAct p`, read through `toQState`, is
`pauliHermitian p`: the same `i^{x·z} X^x Z^z`, with no change of sign or phase. -/
theorem toQState_pauliAct (p : Pauli n) (f : QubitSpace n) :
    toQState (pauliAct p f) = pauliHermitian p (toQState f) := by
  apply toQState.symm.injective
  funext w
  rw [LinearEquiv.symm_apply_apply, toQState_symm_apply, pauliHermitian_apply_fun,
    toQState_apply, sub_eq_add_word]
  exact mul_assoc _ _ _

/-- **The frame's signed Pauli action is the signed Hermitian Pauli.** `P.act`, read through
`toQState`, is `(−1)^sign • pauliHermitian P.pauli`. -/
theorem toQState_signedPauliAct (P : SignedPauli n) (f : QubitSpace n) :
    toQState (P.act f) = ((-1 : ℂ) ^ P.sign.val) • pauliHermitian P.pauli (toQState f) := by
  rw [← toQState_pauliAct, ← LinearEquiv.map_smul]
  rfl

/-! ## The label -/

/-- The chart statement's label is the Born projector's: `i^{outcomeChi P b} = (−1)^{sign + b}`. -/
theorem iZ4_outcomeChi (P : SignedPauli n) (b : ZMod 2) :
    iZ4 (outcomeChi P b) = (-1 : ℂ) ^ (P.sign.val + b.val) := by
  rw [iZ4, I_pow_outcomeChi, outcomeSign, pow_add, mul_comm]

/-- The label squares to one: the hypothesis `hε` of `measSignedStab`. -/
theorem iZ4_outcomeChi_mul_self (P : SignedPauli n) (b : ZMod 2) :
    iZ4 (outcomeChi P b) * iZ4 (outcomeChi P b) = 1 := by
  rw [iZ4, I_pow_outcomeChi]
  exact outcomeSign_mul_self P b

/-! ## The projection -/

/-- The frame's projection as a vector: `½ • (f + (−1)^b • P.act f)`. -/
private theorem pauliProjection_eq_smul (P : SignedPauli n) (b : ZMod 2) (f : QubitSpace n) :
    pauliProjection P b f = (1 / 2 : ℂ) • (f + ((-1 : ℂ) ^ b.val) • P.act f) := by
  rfl

/-- **The frame's projection is the Born projector.** For a Pauli `P` with its sign and an outcome
`b`, `pauliProjection P b f`, read through `toQState`, is `bornProjector P.pauli ε` applied to the
image of `f`, at `ε = (−1)^{sign + b}`: the projector `½(I + ε H(P))` onto the
`(−1)^b`-eigenspace of `P`. -/
theorem pauliProjection_eq_bornProjector (P : SignedPauli n) (b : ZMod 2) (f : QubitSpace n) :
    toQState (pauliProjection P b f)
      = bornProjector P.pauli ((-1 : ℂ) ^ (P.sign.val + b.val)) (toQState f) := by
  rw [pauliProjection_eq_smul, map_smul, map_add, map_smul, toQState_signedPauliAct, smul_smul,
    bornProjector, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smul_apply, one_div, pow_add, mul_comm ((-1 : ℂ) ^ b.val)]

/-- **The Hilbert image of conditioning.** For a carrier state with co-isotropic Lagrangian, a
Pauli `P` with its sign and an outcome `b`, the Hilbert image of T10's output `condition S P b` is
the Born projector `bornProjector P.pauli ((−1)^{sign + b})` applied to the image of `S`. An
impossible outcome gives zero on both sides. -/
theorem toQState_amp_condition (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (P : SignedPauli n)
    (b : ZMod 2) :
    toQState (amp (condition S P b))
      = bornProjector P.pauli ((-1 : ℂ) ^ (P.sign.val + b.val)) (toQState (amp S)) := by
  rw [amp_condition S horth P b]
  exact pauliProjection_eq_bornProjector P b (amp S)

/-- **The frame's projection is T17's Born projection.** As functions on `QubitSpace n`,
`pauliProjection P b` is `bornProjection P b`, the projector of T17's conditioning letter. -/
theorem pauliProjection_eq_bornProjection (P : SignedPauli n) (b : ZMod 2) :
    pauliProjection P b = ⇑(bornProjection P b) := by
  funext f
  rw [bornProjection, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, ← pauliProjection_eq_bornProjector, LinearEquiv.symm_apply_apply]

/-! ## The chart -/

/-- A bit is `0` or `1`. -/
private theorem zmod2_eq_zero_or_eq_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- The sign of the chart statement at one Pauli `g`, in the three cases of `measChi` and
`measSign`, which test the same conditions. -/
private theorem frameToHilbert_measChi_sign (C₀ C : FramePureSignedStab n) (P : SignedPauli n)
    (b : ZMod 2) (hP : P.pauli ∉ C₀.L) (M : Pauli n) (hM : M ∈ C₀.L)
    (hMP : omega M P.pauli = 1) (hL : C.L = pauliCondition C₀.L P.pauli)
    (hchi : C.chi = measChi C₀.toFrameSignedStab P.pauli M (outcomeChi P b)) (g : Pauli n) :
    (frameToHilbert C).sign g
      = measSign (frameToHilbert C₀).toSignedStab P.pauli M (iZ4 (outcomeChi P b)) g := by
  classical
  show (if g ∈ C.L then iZ4 (C.chi g) else 0) = _
  rw [hL, hchi]
  by_cases hg : g ∈ pauliCondition C₀.L P.pauli
  · rw [if_pos hg]
    rcases zmod2_eq_zero_or_eq_one (omega M g) with hδ | hδ
    · have hgL : g ∈ C₀.L :=
        (Submodule.mem_inf.mp (mem_K_of_omega_M_zero C₀.isStab hP hM hMP hg hδ)).1
      rw [measChi_of_omega_eq_zero _ _ _ _ hg hδ, measSign_of_zero _ _ _ _ hg hδ]
      show _ = if g ∈ C₀.L then iZ4 (C₀.chi g) else 0
      rw [if_pos hgL]
    · have hgL : g + P.pauli ∈ C₀.L :=
        (Submodule.mem_inf.mp (mem_K_of_omega_M_one C₀.isStab hP hM hMP hg hδ)).1
      rw [measChi_of_omega_eq_one _ _ _ _ hg hδ, measSign_of_one _ _ _ _ hg hδ]
      show _ = _ * (if g + P.pauli ∈ C₀.L then iZ4 (C₀.chi (g + P.pauli)) else 0) * _
      rw [if_pos hgL, iZ4_add, iZ4_add, pauliPhase_eq_iZ4_betaFrame]
  · rw [if_neg hg]
    exact (if_neg hg).symm

/-- **Through the bridge, the frame update of a chart is the Hilbert measurement update.** Let `C₀`
be a frame chart, `P` a Pauli with its sign outside `C₀.L`, `M ∈ C₀.L` anticommuting with it, and
`b` an outcome. A chart `C` whose Lagrangian is `pauliCondition C₀.L P.pauli` and whose sign is
`measChi` of `C₀` at the label `outcomeChi P b` is sent by `frameToHilbert` to `measSignedStab` of
`frameToHilbert C₀` at `ε = i^{outcomeChi P b}`. -/
theorem frameToHilbert_measChi (C₀ C : FramePureSignedStab n) (P : SignedPauli n) (b : ZMod 2)
    (hP : P.pauli ∉ C₀.L) (M : Pauli n) (hM : M ∈ C₀.L) (hMP : omega M P.pauli = 1)
    (hL : C.L = pauliCondition C₀.L P.pauli)
    (hchi : C.chi = measChi C₀.toFrameSignedStab P.pauli M (outcomeChi P b)) :
    (frameToHilbert C).toSignedStab
      = measSignedStab (frameToHilbert C₀).toSignedStab (frameToHilbert C₀).isStab
          (frameToHilbert C₀).full hP (iZ4_outcomeChi_mul_self P b) M hM hMP := by
  classical
  apply signedStab_ext hL
  funext g
  exact frameToHilbert_measChi_sign C₀ C P b hP M hM hMP hL hchi g

/-- **T12's chart theorem carries over.** For a height-zero floor `K` at precision at most `2`, a
Pauli `P` with its sign outside its Lagrangian, `M` in it anticommuting with `P`, and a height-zero
floor `K'` at precision at most `2` that is `StateEq` to the conditioned state: `frameToHilbert` of
`K'`'s chart is the Hilbert measurement update `measSignedStab` of `K`'s chart at
`ε = i^{outcomeChi P b}`. -/
theorem frameToHilbert_chartOf_condition (K : KernelState n) (hF : IsFloor (ofKernelState K))
    (hm : K.m ≤ 2) (P : SignedPauli n) (b : ZMod 2) (hP : P.pauli ∉ K.L) (M : Pauli n)
    (hM : M ∈ K.L) (hMP : omega M P.pauli = 1) (K' : KernelState n)
    (hF' : IsFloor (ofKernelState K')) (hm' : K'.m ≤ 2)
    (hK' : StateEq (condition (ofKernelState K) P b) (ofKernelState K')) :
    (frameToHilbert (chartOf K' hF' hm')).toSignedStab
      = measSignedStab (frameToHilbert (chartOf K hF hm)).toSignedStab
          (frameToHilbert (chartOf K hF hm)).isStab (frameToHilbert (chartOf K hF hm)).full hP
          (iZ4_outcomeChi_mul_self P b) M hM hMP := by
  obtain ⟨hL, hchi⟩ := condition_eq_pauliCondition K hF hm P b hP M hM hMP K' hF' hm' hK'
  exact frameToHilbert_measChi (chartOf K hF hm) (chartOf K' hF' hm') P b hP M hM hMP hL hchi

end FTQCLib.Hilbert

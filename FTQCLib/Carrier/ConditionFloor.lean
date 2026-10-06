/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Conditioning
import FTQCLib.Carrier.HadamardGateCertificate
import FTQCLib.Stabilizer.SignedCondition

/-!
# Conditioning on floors, the corrected Z-restriction, and agreement with `(L, χ)`

Conditioning a carrier state on a Pauli with its sign (`condition`,
`FTQCLib/Carrier/Conditioning.lean`) has the projection `½(1 + (−1)^b P)` as its amplitude at any
height (`amp_condition`). This module states what that gives on a floor, how it reads through the
floor chart, and the Z-restriction it corrects (`docs/TARGETS.md`, T12).

**Floors stay floors or vanish** (`isFloor_condition`). On a floor `S`, at any height, the
conditioned state either has amplitude zero (an outcome that cannot occur, D10; with D3 it is the
zero state) or is `StateEq` to a floor at height zero. The second disjunct is up to `StateEq`
(D8): `condition` itself keeps or raises the height and need not be a floor, since its
Lagrangian is the input's whenever `P`'s X-part lies in the support's directions (`|+⟩`
conditioned on `Z` keeps `L = ⟨X⟩`, which does not stabilize `|0⟩`). The two disjuncts exclude
each other, since a floor has a nonzero amplitude. No precision is claimed for the floor.

**Through the floor chart** (`condition_eq_pauliCondition`). A height-zero floor at precision at
most `2` is read by the floor chart as a frame signed Lagrangian `(L, χ)` (`chartOf`,
`FTQCLib/Carrier/HadamardGateCertificate.lean`). For a Pauli `P` outside the input's Lagrangian
`L`, with any `M ∈ L` that anticommutes with it, every height-zero floor at precision at most `2`
that is `StateEq` to the conditioned state is read as Lagrangian `pauliCondition L P` with sign
`measChi` (`FTQCLib/Stabilizer/SignedCondition.lean`), the frame form of the measurement update.
The outcome label is `outcomeChi P b = 2(b + sign)`, whose power of `i` is
`(−1)^b·(−1)^{sign}` (`outcomeSign`), the factor the projection puts on the Hermitian Pauli. A
Pauli in `L` needs no update rule: there the outcome is certain or impossible, so the conditioned
state is the input or has amplitude zero (`outcomeWeight_floor`,
`FTQCLib/Carrier/OutcomeWeight.lean`). Everything here is frame-pure (D5): no Hilbert module is
imported.

**The corrected Z-restriction** (`restrictZ`). `restrictZ j b` is conditioning on `Z_j` with sign
`+` at outcome `b` (`signedZ`), followed by dropping free bit `j` (`dropFreeBit`). Dropping needs
bit `j` determined by the support, which the conditioned state's support need not do:
conditioning on `Z_j` adds a bound bit and keeps the support (`condition_cover`). So between the
two the support is cut to the slice `w_j = b` where the conditioned amplitude lives (`sliceZ`): the
Lagrangian becomes `pauliCondition L Z_j`, whose shadow is the part of `π_X(L)` with bit `j` zero
on an isotropic `L`, and the offset moves to a word of the support with bit `j` equal to `b`; where
the support has no such word the outcome is impossible and the scale is `0`. Every amplitude on the
slice is the conditioned state's, and off it the conditioned amplitude is zero, so the cut changes
no amplitude.

**Where `KernelState.restrict` agrees** (`restrict_eq_restrictZ_iff`). `KernelState.restrict j b`
(`FTQCLib/Hierarchy/KernelState.lean`) keeps qubit `j` and sets the offset's bit `j` to `b`.
Its amplitude is compared with `restrictZ j b`'s with qubit `j` put back at `b`: the two agree
exactly when `e_j ∈ π_X(L)` or `x₀ j = b`, for every carrier state at height zero. If bit `j` is
free (`e_j ∈ π_X(L)`) or already `b` at the offset, the slice is the coset `restrict` names.
Otherwise `restrict`'s coset `x₀ + e_j + π_X(L)_{j=0}` misses the support: on the Bell state
with outcome `1` it gives `|10⟩` where the measured state is `|11⟩`, and where bit `j` is the
constant `1 − b` it gives a nonzero state for an impossible outcome. Neither direction is
weakened: the hypothesis is only `IsCarrier`, whose nonzero scale the converse needs.

## Main definitions

* `outcomeSign` — the outcome label `(−1)^b·(−1)^{sign}` of the Hermitian Pauli.
* `outcomeChi` — the same label as a frame sign, `2(b + sign)` in `ZMod 4`.
* `signedZ` — `Z_j` with sign `+`.
* `sliceZ` — the support cut to the slice `w_j = b`.
* `restrictZ` — conditioning on `Z_j` at outcome `b`, then dropping free bit `j`.

## Main results

* `isFloor_condition` — on a floor, conditioning gives amplitude zero or a state `StateEq` to a
  floor at height zero.
* `condition_eq_pauliCondition` — read through the floor chart, conditioning is
  `pauliCondition` with the sign `measChi`.
* `restrict_eq_restrictZ_iff` — `KernelState.restrict` agrees with `restrictZ` exactly when
  `e_j ∈ π_X(L)` or `x₀ j = b`.

## Implementation notes

* `isFloor_condition`, `condition_eq_pauliCondition` and `restrict_eq_restrictZ_iff` are stated
  here and proved at T12.3.1, T12.3.2 and T12.3.3 (`docs/STEPS.md`, phase 2). `restrictZ` is
  defined here in full; T12.3.3 names it.
* The module is frame-pure (D5): the chart is compared with `measChi`, the measurement update on
  `(L, χ)`, and not with the Hilbert `measSignedStab`. `measChi` is `measSign` with the complex
  sign `i^χ` replaced by `χ` and `pauliPhase` by `betaFrame`; their agreement belongs to the
  Hilbert bridge (phase 3).
* The chart reads precisions `1` and `2` only (`toFour`), so `condition_eq_pauliCondition` is
  stated for every height-zero floor at precision at most `2` that is `StateEq` to the conditioned
  state. `isFloor_condition` does not bound the precision of the floor it gives.
* `isFloor_condition` is proved on amplitudes, not by eliminating the bound bit: the projection is
  stabilized by `pauliCondition L P` (its elements in `L` commute with `P`, and `P` acts as the
  outcome label), which is a Lagrangian, and a nonzero amplitude stabilized by a Lagrangian is a
  height-zero floor at precision two (`exists_floor_of_stabilizedBy`, private), its support one
  coset of the shadow and its values the base value times powers of `i`. So the input's height
  never enters. The interpolating exponent comes from `DiagPhase.exists_diagPhase_eval`
  (`FTQCLib/Hierarchy/Defs.lean`).
* `sliceZ` chooses the new offset by `Classical.choose`, and `dropFreeBit` its reader by
  `Classical.epsilon`; no statement depends on either choice, only on the amplitude.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The outcome label and `Z_j` -/

/-- The outcome label as a frame sign: `2(b + sign)` in `ZMod 4`, the exponent of `i` that is
`outcomeSign P b`. -/
def outcomeChi (P : SignedPauli n) (b : ZMod 2) : ZMod 4 :=
  2 * (((b + P.sign).val : ℕ) : ZMod 4)

/-- `i` to the frame label is the complex label. -/
theorem I_pow_outcomeChi (P : SignedPauli n) (b : ZMod 2) :
    Complex.I ^ (outcomeChi P b).val = outcomeSign P b := by
  unfold outcomeChi outcomeSign
  generalize P.sign = s
  fin_cases b <;> fin_cases s
  · change Complex.I ^ 0 = (-1 : ℂ) ^ 0 * (-1 : ℂ) ^ 0
    norm_num
  · change Complex.I ^ 2 = (-1 : ℂ) ^ 0 * (-1 : ℂ) ^ 1
    norm_num
  · change Complex.I ^ 2 = (-1 : ℂ) ^ 1 * (-1 : ℂ) ^ 0
    norm_num
  · change Complex.I ^ 0 = (-1 : ℂ) ^ 1 * (-1 : ℂ) ^ 1
    norm_num

/-- `Z_j` with sign `+`. -/
def signedZ (j : Fin n) : SignedPauli n :=
  ⟨0, pauliz j⟩

/-- `Z_j` has no Y: its X-part is zero. -/
theorem yWeight_signedZ (j : Fin n) : yWeight (signedZ j).pauli = 0 := by
  simp only [yWeight, zDot, signedZ, pauliz_X, Pi.zero_apply, ZMod.val_zero, mul_zero,
    Finset.sum_const_zero]

/-- The side condition of a conditioning letter on `Z_j` holds at every precision `k`. -/
theorem signedZ_side {k : ℕ} (j : Fin n) : yWeight (signedZ j).pauli % 2 = 1 → 2 ≤ k := by
  rw [yWeight_signedZ]
  intro h
  exact absurd h (by decide)

/-- Conditioning on `Z_j` keeps the words with `w_j = b` and zeroes the rest. -/
theorem pauliProjection_signedZ (j : Fin n) (b : ZMod 2) (f : (Fin n → ZMod 2) → ℂ)
    (w : Fin n → ZMod 2) : pauliProjection (signedZ j) b f w = if w j = b then f w else 0 :=
  pauliProjection_zPauli_single j b f w

/-! ## The corrected Z-restriction -/

open Classical in
/-- **The support cut to the slice `w_j = b`.** The Lagrangian becomes `pauliCondition L Z_j`, and
the offset a word of the support with bit `j` equal to `b`, chosen. Where the support has no such
word the scale is `0`. The exponent, height and precision are unchanged. -/
noncomputable def sliceZ (j : Fin n) (b : ZMod 2) (S : KernelSumState n) : KernelSumState n :=
  if h : ∃ v ∈ Submodule.map xProj S.L, S.x₀ j + v j = b then
    { S with L := pauliCondition S.L (pauliz j), x₀ := S.x₀ + Classical.choose h }
  else
    { S with c := 0, L := pauliCondition S.L (pauliz j) }

/-- **The corrected Z-restriction.** Conditioning on `Z_j` with sign `+` at outcome `b`, the support
cut to the slice `w_j = b` where the conditioned amplitude lives, and free bit `j` dropped. -/
noncomputable def restrictZ (j : Fin (n + 1)) (b : ZMod 2) (S : KernelSumState (n + 1)) :
    KernelSumState n :=
  dropFreeBit j (sliceZ j b (condition S (signedZ j) b))

/-! ## A stabilized amplitude is a floor at height zero -/

/-! ## Floors -/

/-- **Floors stay floors or vanish.** On a floor at any height, conditioning on any Pauli with its
sign at either outcome gives amplitude zero, or a state `StateEq` to a floor at height zero.
Proved at T12.3.1. -/
theorem isFloor_condition {S : KernelSumState n} (hS : IsFloor S) (P : SignedPauli n)
    (b : ZMod 2) :
    amp (condition S P b) = 0 ∨
      ∃ T : KernelSumState n, T.h = 0 ∧ IsFloor T ∧ StateEq (condition S P b) T := by
  by_cases h0 : amp (condition S P b) = 0
  · exact Or.inl h0
  · right
    have hamp := amp_condition S hS.1.2.2.1 P b
    rw [hamp] at h0
    have hL' : IsStabilizer (pauliCondition S.L P.pauli) :=
      pauliCondition_isStabilizer hS.1.2.1 P.pauli
    have hrank : Module.finrank (ZMod 2) (pauliCondition S.L P.pauli) = n :=
      pauliCondition_finrank hS.1.2.1 (finrank_eq_of_isCarrier hS.1) P.pauli
    obtain ⟨T, hT0, hTF, hTamp⟩ := exists_floor_of_stabilizedBy hL'
      (orthogonal_le_of_lagrangian hL' hrank) h0
      (stabilizedBy_pauliCondition hS.1.2.1 hS.2 P b h0)
    exact ⟨T, hT0, hTF, hamp.trans hTamp.symm⟩

/-! ## The floor chart's signs are eigenvalues -/

/-- On the Lagrangian a frame sign squares to one as a power of `i` (`two_smul_chi`). -/
private theorem I_pow_chi_mul_self (S : FrameSignedStab n) {g : Pauli n} (hg : g ∈ S.L) :
    Complex.I ^ (S.chi g).val * Complex.I ^ (S.chi g).val = 1 := by
  rw [← I_pow_val_add, ← two_mul, S.two_smul_chi hg, ZMod.val_zero, pow_zero]

/-- If `x·c = e` with `c` and `e` signs, then `x` is a sign and `c = e·x`. -/
private theorem eq_mul_of_mul_eq {c x e : ℂ} (hc : c * c = 1) (he : e * e = 1) (h : x * c = e) :
    c = e * x := by
  linear_combination (x - c * (e + x * c)) * h + (c * x * x) * hc - c * he

/-- **On the `Q`-coset the eigenvalue carries the cocycle.** For `g ∈ pauliCondition L P` with
`a = g + P` in the input's Lagrangian, `g` acts on the conditioned amplitude as `i` to the outcome
label plus `a`'s sign plus `betaFrame P a`: `P` acts as the outcome label, `a` commutes with `P`,
and `pauliAct_add` puts the factor `i^{betaFrame P a}`. -/
private theorem pauliAct_pauliProjection_of_coset (K : KernelState n)
    (hF : IsFloor (ofKernelState K)) (hm : K.m ≤ 2) (P : SignedPauli n) (b : ZMod 2) {g : Pauli n}
    (hg : g ∈ pauliCondition K.L P.pauli) (haK : g + P.pauli ∈ K.L) {c : ℂ} (hc : c * c = 1)
    (hf : pauliProjection P b (amp (ofKernelState K)) ≠ 0)
    (hact : pauliAct g (pauliProjection P b (amp (ofKernelState K)))
      = fun w => c * pauliProjection P b (amp (ofKernelState K)) w) :
    c = Complex.I ^ (outcomeChi P b + (chartOf K hF hm).chi (g + P.pauli)
      + betaFrame P.pauli (g + P.pauli)).val := by
  rw [I_pow_val_add, I_pow_val_add, I_pow_outcomeChi]
  set σ := Complex.I ^ ((chartOf K hF hm).chi (g + P.pauli)).val
  have hσ : σ * σ = 1 := I_pow_chi_mul_self (chartOf K hF hm).toFrameSignedStab haK
  have hPmem : P.pauli ∈ pauliCondition K.L P.pauli := pauliCondition_mem K.L P.pauli
  have haP : omega (g + P.pauli) P.pauli = 0 :=
    pauliCondition_isStabilizer hF.1.2.1 P.pauli _
      ((pauliCondition K.L P.pauli).add_mem hg hPmem) P.pauli hPmem
  have hcomp := pauliAct_add (g + P.pauli) P.pauli (pauliProjection P b (amp (ofKernelState K)))
  rw [pauliAct_self_pauliProjection, pauliAct_mul_left, pauliAct_pauliProjection haP,
    pauliAct_amp_eq_chi K hF hm haK, pauliProjection_mul_left,
    show g + P.pauli + P.pauli = g by rw [add_assoc, pauli_add_self, add_zero], hact] at hcomp
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hf
  have hw' : pauliProjection P b (amp (ofKernelState K)) w ≠ 0 := hw
  have hscalar : Complex.I ^ (betaFrame P.pauli (g + P.pauli)).val * c = outcomeSign P b * σ := by
    have h1 := congrFun hcomp w
    refine mul_right_cancel₀ hw' ?_
    linear_combination -h1
  have hε : outcomeSign P b * σ * (outcomeSign P b * σ) = 1 := by
    linear_combination (σ * σ) * outcomeSign_mul_self P b + hσ
  exact eq_mul_of_mul_eq hc hε hscalar

/-- **Through the floor chart, conditioning is the measurement update on `(L, χ)`.** For a
height-zero floor `K` at precision at most `2`, a Pauli `P` outside its Lagrangian and any `M` in
it anticommuting with `P`: every height-zero floor `K'` at precision at most `2` that is `StateEq`
to the conditioned state is read by the floor chart as Lagrangian `pauliCondition K.L P` with sign
`measChi` of `K`'s chart, at outcome label `outcomeChi P b`. Proved at T12.3.2. -/
theorem condition_eq_pauliCondition (K : KernelState n) (hF : IsFloor (ofKernelState K))
    (hm : K.m ≤ 2) (P : SignedPauli n) (b : ZMod 2) (hP : P.pauli ∉ K.L) (M : Pauli n)
    (hM : M ∈ K.L) (hMP : omega M P.pauli = 1) (K' : KernelState n)
    (hF' : IsFloor (ofKernelState K')) (hm' : K'.m ≤ 2)
    (hK' : StateEq (condition (ofKernelState K) P b) (ofKernelState K')) :
    (chartOf K' hF' hm').L = pauliCondition K.L P.pauli ∧
      (chartOf K' hF' hm').chi
        = measChi (chartOf K hF hm).toFrameSignedStab P.pauli M (outcomeChi P b) := by
  have hK'amp : amp (condition (ofKernelState K) P b) = amp (ofKernelState K') := hK'
  have hamp : amp (ofKernelState K') = pauliProjection P b (amp (ofKernelState K)) :=
    hK'amp.symm.trans (amp_condition _ hF.1.2.2.1 P b)
  have hf' : amp (ofKernelState K') ≠ 0 := hF'.1.2.2.2
  have hf : pauliProjection P b (amp (ofKernelState K)) ≠ 0 := hamp ▸ hf'
  have hLeq : K'.L = pauliCondition K.L P.pauli :=
    eq_of_stabilizedBy_of_stabilizedBy (finrank_eq_of_isCarrier hF'.1)
      (pauliCondition_finrank hF.1.2.1 (finrank_eq_of_isCarrier hF.1) P.pauli) hf' hF'.2
      (by rw [hamp]; exact stabilizedBy_pauliCondition hF.1.2.1 hF.2 P b hf)
  refine ⟨hLeq, funext fun g => ?_⟩
  by_cases hg : g ∈ pauliCondition K.L P.pauli
  · have hgK' : g ∈ K'.L := hLeq ▸ hg
    have hact := pauliAct_amp_eq_chi K' hF' hm' hgK'
    rw [hamp] at hact
    rcases zmod_two_eq_zero_or_one (omega M g) with hδ | hδ
    · rw [measChi_of_omega_eq_zero _ _ _ _ hg hδ]
      have hgK : g ∈ K.L :=
        (Submodule.mem_inf.mp (mem_K_of_omega_M_zero hF.1.2.1 hP hM hMP hg hδ)).1
      have hgP : omega g P.pauli = 0 :=
        pauliCondition_isStabilizer hF.1.2.1 P.pauli g hg P.pauli (pauliCondition_mem K.L P.pauli)
      refine eq_of_I_pow_val_eq (eq_of_pauliAct_eq hf hact ?_)
      rw [pauliAct_pauliProjection hgP, pauliAct_amp_eq_chi K hF hm hgK, pauliProjection_mul_left]
    · rw [measChi_of_omega_eq_one _ _ _ _ hg hδ]
      have haK : g + P.pauli ∈ K.L :=
        (Submodule.mem_inf.mp (mem_K_of_omega_M_one hF.1.2.1 hP hM hMP hg hδ)).1
      exact eq_of_I_pow_val_eq (pauliAct_pauliProjection_of_coset K hF hm P b hg haK
        (I_pow_chi_mul_self (chartOf K' hF' hm').toFrameSignedStab hgK') hf hact)
  · rw [measChi_of_not_mem _ _ _ _ hg]
    exact (chartOf K' hF' hm').tight g (by rw [chartOf_L, hLeq]; exact hg)

/-! ## Agreement with `KernelState.restrict` -/

/-- **The shadow of `pauliCondition L Z_j`** is the part of `π_X(L)` with bit `j` zero, on an
isotropic `L`. -/
theorem mem_map_pauliCondition_pauliz_iff {L : Submodule (ZMod 2) (Pauli n)}
    (hL : IsStabilizer L) (j : Fin n) (v : Fin n → ZMod 2) :
    v ∈ Submodule.map xProj (pauliCondition L (pauliz j))
      ↔ v ∈ Submodule.map xProj L ∧ v j = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_cases hZ : pauliz j ∈ L
    · rw [pauliCondition_of_mem hZ] at hp
      refine ⟨Submodule.mem_map_of_mem hp, ?_⟩
      rw [xProj_apply, ← omega_pauliz_left]
      exact hL _ hZ p hp
    · rw [pauliCondition_of_not_mem hZ] at hp
      obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp hp
      obtain ⟨haL, hao⟩ := Submodule.mem_inf.mp ha
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hr
      have hrX : (c • pauliz j).X = 0 := by
        rw [X_smul, pauliz_X, smul_zero]
      have haj : a.X j = 0 := by
        rw [← omega_pauliz_left]
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hao) _
          (Submodule.mem_span_singleton_self _)
      rw [xProj_apply, X_add, hrX, add_zero]
      exact ⟨Submodule.mem_map_of_mem haL, haj⟩
  · rintro ⟨⟨p, hp, rfl⟩, hpj⟩
    rw [xProj_apply] at hpj
    refine Submodule.mem_map_of_mem ?_
    by_cases hZ : pauliz j ∈ L
    · rw [pauliCondition_of_mem hZ]
      exact hp
    · rw [pauliCondition_of_not_mem hZ]
      refine Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hp, ?_⟩)
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr (fun q hq => ?_)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
      change omega (c • pauliz j) p = 0
      rw [omega_smul_left, omega_pauliz_left, hpj, mul_zero]

/-- `sliceZ` sets the Lagrangian to `pauliCondition L Z_j` in both branches. -/
theorem sliceZ_L (j : Fin n) (b : ZMod 2) (S : KernelSumState n) :
    (sliceZ j b S).L = pauliCondition S.L (pauliz j) := by
  unfold sliceZ
  split <;> rfl

/-- **The slice changes no amplitude** when the amplitude vanishes off `w_j = b`: on the slice
the support is the input's cut to `w_j = b`, and where the support has no such word the input's
amplitude is zero everywhere. -/
theorem amp_sliceZ {j : Fin n} {b : ZMod 2} {S : KernelSumState n}
    (hL : IsStabilizer S.L) (hS : ∀ w, w j ≠ b → amp S w = 0) :
    amp (sliceZ j b S) = amp S := by
  funext w
  by_cases hv : ∃ v ∈ Submodule.map xProj S.L, S.x₀ j + v j = b
  · have hspec := Classical.choose_spec hv
    have hsl : sliceZ j b S
        = { S with L := pauliCondition S.L (pauliz j), x₀ := S.x₀ + Classical.choose hv } := by
      unfold sliceZ
      exact dif_pos hv
    rw [hsl]
    by_cases hw : w - (S.x₀ + Classical.choose hv)
        ∈ Submodule.map xProj (pauliCondition S.L (pauliz j))
    · have hw' := (mem_map_pauliCondition_pauliz_iff hL j _).mp hw
      have hon : w - S.x₀ ∈ Submodule.map xProj S.L := by
        rw [show w - S.x₀ = (w - (S.x₀ + Classical.choose hv)) + Classical.choose hv by abel]
        exact Submodule.add_mem _ hw'.1 hspec.1
      rw [amp_pos ((mem_support_iff _ w).mpr hw), amp_pos ((mem_support_iff S w).mpr hon)]
    · rw [amp_neg (fun h => hw ((mem_support_iff _ w).mp h))]
      by_cases hwj : w j = b
      · refine (amp_neg (fun h => hw ?_)).symm
        have hon := (mem_support_iff S w).mp h
        refine (mem_map_pauliCondition_pauliz_iff hL j _).mpr
          ⟨?_, ?_⟩
        · rw [show w - (S.x₀ + Classical.choose hv) = (w - S.x₀) - Classical.choose hv by abel]
          exact Submodule.sub_mem _ hon hspec.1
        · rw [Pi.sub_apply, Pi.add_apply]
          linear_combination hwj - hspec.2
      · exact (hS w hwj).symm
  · have hsl : sliceZ j b S = { S with c := 0, L := pauliCondition S.L (pauliz j) } := by
      unfold sliceZ
      exact dif_neg hv
    rw [hsl, amp_c_zero _ rfl]
    by_cases hwj : w j = b
    · refine (amp_neg (fun h => hv ⟨w - S.x₀, (mem_support_iff S w).mp h, ?_⟩)).symm
      rw [Pi.sub_apply, hwj]
      ring
    · exact (hS w hwj).symm

/-- Conditioning on `Z_j` keeps the Lagrangian and the offset: its X-part is zero, in the shadow,
so it is the bound constructor. -/
theorem condition_signedZ (S : KernelSumState n) (j : Fin n) (b : ZMod 2) :
    condition S (signedZ j) b = conditionBound S (signedZ j) b :=
  condition_of_mem (Submodule.zero_mem _) b

/-- **The amplitude of `restrictZ`** is the input's with qubit `j` put back at `b`. -/
theorem amp_restrictZ {S : KernelSumState (n + 1)} (hS : IsCarrier S) (j : Fin (n + 1))
    (b : ZMod 2) (w : Fin n → ZMod 2) :
    amp (restrictZ j b S) w = amp S (Fin.insertNth j b w) := by
  set C := condition S (signedZ j) b with hC
  have hCL : C.L = S.L := by rw [hC, condition_signedZ]; rfl
  have hampC : amp C = fun v => if v j = b then amp S v else 0 := by
    funext v
    rw [hC, amp_condition S hS.2.2.1]
    exact pauliProjection_zPauli_single j b (amp S) v
  have hCiso : IsStabilizer C.L := hCL ▸ hS.2.1
  have hslice : amp (sliceZ j b C) = amp C := by
    refine amp_sliceZ hCiso (fun v hv => ?_)
    rw [hampC]
    exact if_neg hv
  have hj : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∉ Submodule.map xProj (sliceZ j b C).L := by
    rw [sliceZ_L, mem_map_pauliCondition_pauliz_iff hCiso]
    rintro ⟨_, h⟩
    rw [Pi.single_eq_same] at h
    exact one_ne_zero h
  unfold restrictZ
  rw [← hC, amp_dropFreeBit j _ hj, hslice, hampC]
  simp only [Fin.insertNth_apply_same]
  rw [Finset.sum_eq_single b (fun β _ hβ => if_neg hβ) (fun h => absurd (Finset.mem_univ b) h),
    if_pos rfl]

/-- `restrictZ` keeps the precision of a state at positive precision. -/
theorem restrictZ_m {S : KernelSumState (n + 1)} (hm : 1 ≤ S.m) (j : Fin (n + 1)) (b : ZMod 2) :
    (restrictZ j b S).m = S.m := by
  have hs : (sliceZ j b (condition S (signedZ j) b)).m = (condition S (signedZ j) b).m := by
    unfold sliceZ
    split <;> rfl
  change (sliceZ j b (condition S (signedZ j) b)).m = S.m
  rw [hs, condition_signedZ]
  refine conditionPrecision_eq (signedZ j) hm ?_
  intro h
  rw [yWeight_signedZ] at h
  exact absurd h (by decide)

/-- **The conditioned slice keeps the carrier property** where its amplitude is nonzero: the step
of `restrictZ` before its drop, and all of `pinZero` (entry 2026-10-01n). -/
theorem isCarrier_sliceZ_condition {S : KernelSumState n} (hS : IsCarrier S) (j : Fin n)
    (b : ZMod 2) (hne : amp (sliceZ j b (condition S (signedZ j) b)) ≠ 0) :
    IsCarrier (sliceZ j b (condition S (signedZ j) b)) := by
  set C := condition S (signedZ j) b with hC
  have hCL : C.L = S.L := by rw [hC, condition_signedZ]; rfl
  have hSL : (sliceZ j b C).L = pauliCondition S.L (pauliz j) := by rw [sliceZ_L, hCL]
  have hstab : IsStabilizer (sliceZ j b C).L := by
    rw [hSL]
    exact pauliCondition_isStabilizer hS.2.1 _
  have horth : LinearMap.BilinForm.orthogonal omegaBilin (sliceZ j b C).L ≤ (sliceZ j b C).L :=
    orthogonal_le_of_lagrangian hstab (by
      rw [hSL]
      exact pauliCondition_finrank hS.2.1 (finrank_eq_of_isCarrier hS) _)
  have hm : 1 ≤ (sliceZ j b C).m := by
    have hs : (sliceZ j b C).m = C.m := by
      unfold sliceZ
      split <;> rfl
    have hCm : C.m = S.m := by
      rw [hC, condition_signedZ]
      refine conditionPrecision_eq (signedZ j) hS.1 ?_
      intro h
      rw [yWeight_signedZ] at h
      exact absurd h (by decide)
    rw [hs, hCm]
    exact hS.1
  exact ⟨hm, hstab, horth, hne⟩

/-- **`restrictZ` keeps the carrier property** where its amplitude is nonzero. -/
theorem isCarrier_restrictZ {S : KernelSumState (n + 1)} (hS : IsCarrier S) (j : Fin (n + 1))
    (b : ZMod 2) (hne : amp (restrictZ j b S) ≠ 0) : IsCarrier (restrictZ j b S) := by
  set C := condition S (signedZ j) b with hC
  have hCL : C.L = S.L := by rw [hC, condition_signedZ]; rfl
  have hSL : (sliceZ j b C).L = pauliCondition S.L (pauliz j) := by rw [sliceZ_L, hCL]
  have hj : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∉ Submodule.map xProj (sliceZ j b C).L := by
    rw [hSL, mem_map_pauliCondition_pauliz_iff hS.2.1]
    rintro ⟨_, h⟩
    rw [Pi.single_eq_same] at h
    exact one_ne_zero h
  have hne' : amp (sliceZ j b C) ≠ 0 := by
    intro h0
    apply hne
    change amp (dropFreeBit j (sliceZ j b C)) = 0
    rw [amp_dropFreeBit j _ hj, h0]
    funext w
    simp only [Pi.zero_apply, Finset.sum_const_zero]
  exact isCarrier_dropFreeBit j (isCarrier_sliceZ_condition hS j b hne') hj

/-! ## A free bit appended and held at zero (entry 2026-10-01n)

`pinZero` is `restrictZ` on the appended bit without its final drop: the ancilla of
`UnreadBits.lean`'s backward direction. -/

/-- `S` with a new last free bit held at zero: append a free bit, condition on `Z` there at
outcome `0`, and cut the support to the slice. -/
noncomputable def pinZero {N : ℕ} (S : KernelSumState N) : KernelSumState (N + 1) :=
  sliceZ (Fin.last N) 0 (condition (appendFreeBit S) (signedZ (Fin.last N)) 0)

/-- The amplitude of `pinZero S`: `S`'s on the first `N` bits where the last is zero, else zero. -/
theorem amp_pinZero {N : ℕ} {S : KernelSumState N} (hS : IsCarrier S) :
    amp (pinZero S) = fun w => if w (Fin.last N) = 0 then amp S (Fin.init w) else 0 := by
  have hA := isCarrier_appendFreeBit hS
  have hampC : amp (condition (appendFreeBit S) (signedZ (Fin.last N)) 0)
      = fun v => if v (Fin.last N) = 0 then amp S (Fin.init v) else 0 := by
    funext v
    rw [amp_condition _ hA.2.2.1]
    refine (pauliProjection_zPauli_single (Fin.last N) 0 (amp (appendFreeBit S)) v).trans ?_
    rw [amp_appendFreeBit]
  have hCL : (condition (appendFreeBit S) (signedZ (Fin.last N)) 0).L = (appendFreeBit S).L := by
    rw [condition_signedZ]
    rfl
  unfold pinZero
  rw [amp_sliceZ (by rw [hCL]; exact hA.2.1) (fun v hv => by rw [hampC]; exact if_neg hv), hampC]

/-- The support of `pinZero S`: the appended support conditioned on `Z` at the last bit. -/
theorem pinZero_L {N : ℕ} (S : KernelSumState N) :
    (pinZero S).L = pauliCondition (appendFreeBit S).L (pauliz (Fin.last N)) := by
  unfold pinZero
  rw [sliceZ_L, condition_signedZ]
  rfl

/-- `pinZero` keeps the carrier property: a conditioned slice (`isCarrier_sliceZ_condition`) whose
amplitude is `S`'s on the slice, so nonzero. -/
theorem isCarrier_pinZero {N : ℕ} {S : KernelSumState N} (hS : IsCarrier S) :
    IsCarrier (pinZero S) := by
  refine isCarrier_sliceZ_condition (isCarrier_appendFreeBit hS) (Fin.last N) 0 fun h0 => ?_
  apply hS.2.2.2
  funext v
  have hv := congrFun h0 (Fin.snoc (α := fun _ => ZMod 2) v 0)
  change amp (pinZero S) _ = _ at hv
  rw [amp_pinZero hS] at hv
  beta_reduce at hv
  rw [Fin.snoc_last, if_pos rfl, Fin.init_snoc] at hv
  exact hv

/-- Setting bit `j` of `x₀` to `b` adds `(b − x₀ j)·e_j`. -/
private theorem update_eq_add_single (x₀ : Fin (n + 1) → ZMod 2) (j : Fin (n + 1)) (b : ZMod 2) :
    Function.update x₀ j b
      = x₀ + (b - x₀ j) • (Pi.single j (1 : ZMod 2) : Fin (n + 1) → ZMod 2) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
    ring
  · simp only [Function.update_of_ne hij, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hij,
      smul_eq_mul, mul_zero, add_zero]

/-- The support of `K.restrict j b` is the coset of `update x₀ j b` in `π_X(L)`, cut to
`w_j = b`. -/
private theorem mem_support_restrict_iff (K : KernelState (n + 1)) (hL : IsStabilizer K.L)
    (j : Fin (n + 1)) (b : ZMod 2) (w : Fin (n + 1) → ZMod 2) :
    (∃ p ∈ (K.restrict j b).L, w = (K.restrict j b).x₀ + p.X)
      ↔ w - Function.update K.x₀ j b ∈ Submodule.map xProj K.L ∧ w j = b := by
  refine (mem_support_iff (ofKernelState (K.restrict j b)) w).trans ?_
  change w - Function.update K.x₀ j b ∈ Submodule.map xProj (pauliCondition K.L (pauliz j)) ↔ _
  rw [mem_map_pauliCondition_pauliz_iff hL, Pi.sub_apply, Function.update_self, sub_eq_zero]

/-- On its support `K.restrict j b` has `K`'s value: there bit `j` is already `b`. -/
private theorem amp_restrict_pos (K : KernelState (n + 1)) {j : Fin (n + 1)} {b : ZMod 2}
    {w : Fin (n + 1) → ZMod 2} (hw : ∃ p ∈ (K.restrict j b).L, w = (K.restrict j b).x₀ + p.X)
    (hwj : w j = b) :
    amp (ofKernelState (K.restrict j b)) w = K.c * charOf K.m (DiagPhase.eval K.q w) := by
  rw [amp_ofKernelState_pos _ hw]
  change K.c * charOf K.m (DiagPhase.eval (freezeAt j b K.q) w) = _
  rw [freezeAt_eval, ← hwj, Function.update_eq_self]

/-- **Agreement where bit `j` is free or the offset's bit is `b`.** Then `update x₀ j b` lies on
`K`'s support coset, so the two supports cut to `w_j = b` coincide, and so do the values. -/
private theorem restrict_agrees (K : KernelState (n + 1)) (hK : IsCarrier (ofKernelState K))
    (j : Fin (n + 1)) (b : ZMod 2)
    (h : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∈ Submodule.map xProj K.L ∨ K.x₀ j = b) :
    amp (ofKernelState (K.restrict j b))
      = fun w => if w j = b then amp (ofKernelState K) w else 0 := by
  have hshift : Function.update K.x₀ j b - K.x₀ ∈ Submodule.map xProj K.L := by
    rw [update_eq_add_single, add_sub_cancel_left]
    rcases h with he | hx
    · exact Submodule.smul_mem _ _ he
    · rw [hx, sub_self, zero_smul]
      exact Submodule.zero_mem _
  funext w
  by_cases hwj : w j = b
  · rw [if_pos hwj]
    have hiff : w - Function.update K.x₀ j b ∈ Submodule.map xProj K.L
        ↔ w - K.x₀ ∈ Submodule.map xProj K.L := by
      rw [show w - K.x₀ = (w - Function.update K.x₀ j b) + (Function.update K.x₀ j b - K.x₀) by
        abel]
      exact (Submodule.add_mem_iff_left _ hshift).symm
    by_cases hon : w - K.x₀ ∈ Submodule.map xProj K.L
    · have hw := (mem_support_restrict_iff K hK.2.1 j b w).mpr ⟨hiff.mpr hon, hwj⟩
      rw [amp_restrict_pos K hw hwj,
        amp_ofKernelState_pos K ((mem_support_iff (ofKernelState K) w).mpr hon)]
    · rw [amp_ofKernelState_neg K (fun h => hon ((mem_support_iff (ofKernelState K) w).mp h)),
        amp_ofKernelState_neg _ (fun h => hon (hiff.mp
          ((mem_support_restrict_iff K hK.2.1 j b w).mp h).1))]
  · rw [if_neg hwj,
      amp_ofKernelState_neg _ (fun h => hwj ((mem_support_restrict_iff K hK.2.1 j b w).mp h).2)]

/-- **Disagreement otherwise.** If bit `j` is determined and the offset's bit is not `b`, then
`update x₀ j b` is on `restrict`'s support, where its amplitude is nonzero, and off `K`'s, since it
differs from `x₀` by `e_j`. -/
private theorem restrict_disagrees (K : KernelState (n + 1)) (hK : IsCarrier (ofKernelState K))
    (j : Fin (n + 1)) (b : ZMod 2)
    (he : (Pi.single j 1 : Fin (n + 1) → ZMod 2) ∉ Submodule.map xProj K.L) (hx : K.x₀ j ≠ b) :
    amp (ofKernelState (K.restrict j b)) (Function.update K.x₀ j b)
      ≠ amp (ofKernelState K) (Function.update K.x₀ j b) := by
  have hc : K.c ≠ 0 := c_ne_zero_of_isCarrier hK
  have hwj : Function.update K.x₀ j b j = b := Function.update_self j b K.x₀
  have hw := (mem_support_restrict_iff K hK.2.1 j b _).mpr
    ⟨by rw [sub_self]; exact Submodule.zero_mem _, hwj⟩
  have hone : b - K.x₀ j = 1 := by
    have hne : b - K.x₀ j ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    generalize b - K.x₀ j = a at hne ⊢
    revert a
    decide
  have hoff : ¬ ∃ p ∈ K.L, Function.update K.x₀ j b = K.x₀ + p.X := by
    intro h
    have hmem : Function.update K.x₀ j b - K.x₀ ∈ Submodule.map xProj K.L :=
      (mem_support_iff (ofKernelState K) _).mp h
    rw [update_eq_add_single, add_sub_cancel_left, hone, one_smul] at hmem
    exact he hmem
  rw [amp_restrict_pos K hw hwj, amp_ofKernelState_neg K hoff]
  exact mul_ne_zero hc (charOf_ne_zero _ _)

/-- **`KernelState.restrict` agrees with `restrictZ` exactly when `e_j ∈ π_X(L)` or `x₀ j = b`.**
For a carrier state at height zero, `restrict j b`'s amplitude is `restrictZ j b`'s with qubit `j`
put back at `b` (and zero where bit `j` is not `b`) if and only if bit `j` is free on the support
or the offset's bit `j` is `b`. Proved at T12.3.3. -/
theorem restrict_eq_restrictZ_iff (K : KernelState (n + 1)) (hK : IsCarrier (ofKernelState K))
    (j : Fin (n + 1)) (b : ZMod 2) :
    amp (ofKernelState (K.restrict j b))
        = (fun w => if w j = b then amp (restrictZ j b (ofKernelState K)) (Fin.removeNth j w)
            else 0)
      ↔ ((Pi.single j 1 : Fin (n + 1) → ZMod 2) ∈ Submodule.map xProj K.L ∨ K.x₀ j = b) := by
  have hrhs : (fun w => if w j = b then amp (restrictZ j b (ofKernelState K)) (Fin.removeNth j w)
      else 0) = fun w => if w j = b then amp (ofKernelState K) w else 0 := by
    funext w
    by_cases hwj : w j = b
    · rw [if_pos hwj, if_pos hwj, amp_restrictZ hK, ← hwj, Fin.insertNth_self_removeNth]
    · rw [if_neg hwj, if_neg hwj]
  rw [hrhs]
  refine ⟨fun heq => ?_, restrict_agrees K hK j b⟩
  by_contra hno
  rw [not_or] at hno
  have h := congrFun heq (Function.update K.x₀ j b)
  rw [if_pos (Function.update_self j b K.x₀)] at h
  exact restrict_disagrees K hK j b hno.1 hno.2 h

/-! ## Free bits appended and dropped in bulk -/

/-- **`k` free bits appended** as `∣0⟩ + ∣1⟩` each, bits `n, …, n + k − 1`, in that order, by `k`
uses of `appendFreeBit`. The scale is unchanged (D3). -/
noncomputable def appendFreeBits : (k : ℕ) → KernelSumState n → KernelSumState (n + k)
  | 0, S => S
  | k + 1, S => appendFreeBit (appendFreeBits k S)

/-- **The last `k` free bits evaluated at `o` and dropped**, the last first, by `k` uses of
`restrictZ`: the bit `n + i` is read at `o i`. -/
noncomputable def restrictLast :
    (k : ℕ) → (Fin k → ZMod 2) → KernelSumState (n + k) → KernelSumState n
  | 0, _, S => S
  | k + 1, o, S => restrictLast k (Fin.init o) (restrictZ (Fin.last (n + k)) (o (Fin.last k)) S)

/-- Appending `k` free bits keeps the precision. -/
theorem appendFreeBits_m (k : ℕ) (T : KernelSumState n) : (appendFreeBits k T).m = T.m := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Appending `k` free bits keeps the scale (D3). -/
theorem appendFreeBits_c (k : ℕ) (T : KernelSumState n) : (appendFreeBits k T).c = T.c := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Appending `k` free bits keeps the carrier property. -/
theorem isCarrier_appendFreeBits (k : ℕ) {T : KernelSumState n} (hT : IsCarrier T) :
    IsCarrier (appendFreeBits k T) := by
  induction k with
  | zero => exact hT
  | succ k ih => exact isCarrier_appendFreeBit ih

/-- With `k` free bits appended, the amplitude reads only the first `n` bits. -/
theorem amp_appendFreeBits (k : ℕ) (T : KernelSumState n) :
    amp (appendFreeBits k T) = fun u => amp T (fun i => u (Fin.castAdd k i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change amp (appendFreeBit (appendFreeBits k T)) = _
    rw [amp_appendFreeBit, ih]
    rfl

/-- `Fin.append w o` is `Fin.append w (Fin.init o)` with the last bit of `o` after it. -/
private theorem append_eq_snoc_append_init {N k : ℕ} (w : Fin N → ZMod 2)
    (o : Fin (k + 1) → ZMod 2) :
    Fin.append w o = Fin.snoc (Fin.append w (Fin.init o)) (o (Fin.last k)) := by
  conv_lhs => rw [← Fin.snoc_init_self o]
  exact Fin.append_snoc w (Fin.init o) (o (Fin.last k))

/-- **Dropping the last `k` free bits at `o`.** If a carrier state's amplitude, read with its last
`k` bits at `o`, is a nonzero function `G` of the first `n`, the state with them dropped is a
carrier state of amplitude `G`. -/
theorem restrictLast_spec : ∀ (k : ℕ) (o : Fin k → ZMod 2) {T : KernelSumState (n + k)},
    IsCarrier T → ∀ {G : (Fin n → ZMod 2) → ℂ}, G ≠ 0 →
      (∀ w, amp T (Fin.append w o) = G w) →
        IsCarrier (restrictLast k o T) ∧ amp (restrictLast k o T) = G
  | 0, o, T, hT, G, _, h => by
    refine ⟨hT, funext fun w => ?_⟩
    rw [← h w]
    change amp T w = amp T (Fin.append w o)
    congr 1
    funext i
    exact (Fin.append_left w o i).symm
  | k + 1, o, T, hT, G, hG, h => by
    have e : ∀ w, amp (restrictZ (Fin.last (n + k)) (o (Fin.last k)) T)
        (Fin.append w (Fin.init o)) = G w := by
      intro w
      rw [amp_restrictZ hT]
      erw [Fin.insertNth_last']
      rw [← append_eq_snoc_append_init]
      exact h w
    have hne : amp (restrictZ (Fin.last (n + k)) (o (Fin.last k)) T) ≠ 0 := by
      intro h0
      apply hG
      funext w
      rw [← e w, h0]
      rfl
    exact restrictLast_spec k (Fin.init o) (isCarrier_restrictZ hT _ _ hne) hG e

end FTQCLib.Frame.Walkthrough

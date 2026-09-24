/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardAmplitude

/-!
# Check: the amplitude half

The controls are aimed at the hypotheses of `amp_hRaise`, one row each. **The representer is
load-bearing**: on the genuine Bell state with the non-representer `u = 0`, the theorem's
conclusion is *false* at the word `11` (the rule freezes the Hadamarded coordinate to the wrong
branch, and the sign flips). **Co-isotropy is load-bearing**: on the one-qubit state with `L = ⊥`
— isotropic, not co-isotropic, and satisfying the representer conditions vacuously — the
conclusion is again *false*, because the output support has one point where the Walsh transform
has two. **`1 ≤ m` is load-bearing**: at `m = 0` the emitted sign term is `0` in the trivial ring,
against `2^{m−1}` of order two at `m = 1`.

The agreement row reaches one amplitude two ways: the Bell output at `11` is `−1/√2` by the
referee (`amp_hRaise_bell` followed by the Walsh transform of the input) and by the carrier's own
exponent (`hRaise_bell_exponent`, proved independently of `amp_hRaise`, followed by the
`h = 0` reduction and `e^{iπ} = −1`). The kernel rows run the decidable support side of the
odd-parity example through `decide`: the branch value, the surviving branch on support, the other
branch off it.

What no row here tests: `ampCore` is noncomputable (`Complex.exp`), so no amplitude row is a
kernel row — the absence is forced, not skipped; and nothing here is about `applyHFiner`, whose
transport is `amp_applyHFiner` (`HadamardCover.lean`). -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## Shared evaluations on the examples -/

/-- `realPhase` of the zero exponent vanishes. -/
theorem realPhase_zero_poly {N m : ℕ} (v : Fin N → ZMod 2) :
    DiagPhase.realPhase (0 : DiagPhase N m) v = 0 := by
  unfold DiagPhase.realPhase DiagPhase.eval
  rw [map_zero, ZMod.val_zero]
  simp

/-- `1/√2` is a nonzero complex number. -/
theorem one_div_sqrt_two_ne_zero : (1 / (Real.sqrt 2 : ℂ)) ≠ 0 :=
  one_div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))

/-- The Bell amplitude at `11` is `1`. -/
theorem amp_bellState_oneone : amp bellState ![1, 1] = 1 := by
  have hsup : ∃ p ∈ bellState.L, (![1, 1] : Fin 2 → ZMod 2) = bellState.x₀ + p.X :=
    ⟨⟨![1, 1], 0⟩, mem_bellL.mpr ⟨by decide, rfl⟩, by decide⟩
  rw [amp_pos hsup]
  change ampCore 1 0 (0 : DiagPhase (2 + 0) 1) 1 ![1, 1] = 1
  rw [ampCore_zero, realPhase_zero_poly]
  simp

/-- The Bell amplitude at `01` is `0`: off the support coset. -/
theorem amp_bellState_zeroone : amp bellState ![0, 1] = 0 := by
  refine amp_neg ?_
  rintro ⟨p, hp, h⟩
  change (![0, 1] : Fin 2 → ZMod 2) = 0 + p.X at h
  rw [zero_add] at h
  have h1 := hp.1
  rw [← h] at h1
  exact absurd h1 (by decide)

/-- The two Walsh branches of `11` at bit `0`. -/
theorem update_oneone_zero : Function.update (![1, 1] : Fin 2 → ZMod 2) 0 0 = ![0, 1] := by
  decide

/-- The two Walsh branches of `11` at bit `0`. -/
theorem update_oneone_one : Function.update (![1, 1] : Fin 2 → ZMod 2) 0 1 = ![1, 1] := by
  decide

/-- The Walsh sign at a set bit. -/
theorem signOf_one : signOf (1 : ZMod 2) = -1 := by
  unfold signOf
  rw [if_neg (by decide)]

/-- The referee on the Bell input at `11`: `−1/√2`. -/
theorem walsh_amp_bellState_oneone :
    walshTransform 0 (amp bellState) ![1, 1] = -(1 / (Real.sqrt 2 : ℂ)) := by
  unfold walshTransform
  rw [update_oneone_zero, update_oneone_one, amp_bellState_zeroone, amp_bellState_oneone]
  change (1 / (Real.sqrt 2 : ℂ)) * (0 + signOf 1 * 1) = -(1 / (Real.sqrt 2 : ℂ))
  rw [signOf_one]
  ring

/-! ## Control — the representer hypothesis is load-bearing -/

/-- **Control — the representer is load-bearing.** With the non-representer `u = 0` on the Bell
state (`u = 0` represents the coordinate functional only on a shadow that omits bit `0`'s
correlations, which Bell's does not), the rule freezes bit `0` to the wrong branch: its output
amplitude at `11` is `+1/√2`, the referee's is `−1/√2`. A version of `amp_hRaise` without
`hrep` is refuted here. -/
example :
    amp (hRaise 0 (0 : Fin 2 → ZMod 2) bellState) ![1, 1]
      ≠ walshTransform 0 (amp bellState) ![1, 1] := by
  rw [walsh_amp_bellState_oneone]
  have hsup : ∃ p ∈ (hRaise 0 (0 : Fin 2 → ZMod 2) bellState).L,
      (![1, 1] : Fin 2 → ZMod 2) = (hRaise 0 (0 : Fin 2 → ZMod 2) bellState).x₀ + p.X := by
    refine (hRaise_mem_support_iff 0 0 bellState bellL_coisotropic bellL_not_mem_shadow
      ![1, 1]).mpr ⟨1, ⟨![1, 1], 0⟩, mem_bellL.mpr ⟨by decide, rfl⟩, ?_⟩
    rw [update_oneone_one]
    decide
  rw [amp_pos hsup, ampCore_hRaise 0 0 bellState le_rfl ![1, 1]]
  have ht : raiseConst 0 (0 : Fin 2 → ZMod 2) bellState.x₀
      + dotF2 (0 : Fin 2 → ZMod 2) ![1, 1] = 0 := by
    change raiseConst 0 (0 : Fin 2 → ZMod 2) 0 + dotF2 (0 : Fin 2 → ZMod 2) ![1, 1] = 0
    decide
  rw [ht, ZMod.val_zero, zero_mul, pow_zero, one_mul, update_oneone_zero]
  change (1 / (Real.sqrt 2 : ℂ)) * ampCore 1 0 (0 : DiagPhase (2 + 0) 1) 1 ![0, 1]
    ≠ -(1 / (Real.sqrt 2 : ℂ))
  rw [ampCore_zero, realPhase_zero_poly]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  intro h
  have h2 : (2 : ℂ) * (1 / (Real.sqrt 2 : ℂ)) = 0 := by linear_combination h
  exact absurd (mul_eq_zero.mp h2) (by
    rintro (h0 | h0)
    · exact two_ne_zero h0
    · exact one_div_sqrt_two_ne_zero h0)

/-- The control's premise: `u = 0` satisfies `u 0 = 0`, so the refuted hypothesis is `hrep`,
not `hui`. -/
example : (0 : Fin 2 → ZMod 2) 0 = 0 := rfl

/-- The control's other premise: `u = 0` is *not* a representer on Bell's shadow — the shadow
vector `(1,1)` has coordinate `1` and `0 ⬝ (1,1) = 0`. -/
example : ¬ ∀ v ∈ Submodule.map xProj bellL, dotF2 (0 : Fin 2 → ZMod 2) v = v 0 := by
  intro h
  have hv : (![1, 1] : Fin 2 → ZMod 2) ∈ Submodule.map xProj bellL :=
    Submodule.mem_map.mpr ⟨⟨![1, 1], 0⟩, mem_bellL.mpr ⟨by decide, rfl⟩, rfl⟩
  have := h _ hv
  revert this
  decide

/-! ## Control — co-isotropy is load-bearing -/

/-- The one-qubit state with `L = ⊥`: isotropic, not co-isotropic, support the single point `0`. -/
noncomputable def botState : KernelSumState 1 where
  m := 1
  h := 0
  Q := 0
  c := 1
  L := ⊥
  x₀ := 0

/-- The control's premise: the representer conditions hold at `⊥` (vacuously — the shadow is
`⊥`), so the refuted hypothesis below is `horth`. -/
example :
    (0 : Fin 1 → ZMod 2) 0 = 0
      ∧ ∀ v ∈ Submodule.map xProj (⊥ : Submodule (ZMod 2) (Pauli 1)),
          dotF2 (0 : Fin 1 → ZMod 2) v = v 0 := by
  refine ⟨rfl, ?_⟩
  intro v hv
  rw [Submodule.map_bot, Submodule.mem_bot] at hv
  subst hv
  decide

/-- The control's other premise: `⊥` is not co-isotropic (its orthogonal is everything). -/
example :
    ¬ LinearMap.BilinForm.orthogonal omegaBilin (⊥ : Submodule (ZMod 2) (Pauli 1))
        ≤ (⊥ : Submodule (ZMod 2) (Pauli 1)) := by
  intro h
  have hmem : (⟨![1], 0⟩ : Pauli 1)
      ∈ LinearMap.BilinForm.orthogonal omegaBilin (⊥ : Submodule (ZMod 2) (Pauli 1)) := by
    intro p hp
    rw [Submodule.mem_bot] at hp
    subst hp
    change omega 0 _ = 0
    exact omega_zero_left _
  have h0 := Submodule.mem_bot (ZMod 2) |>.mp (h hmem)
  have := congrFun (congrArg Pauli.X h0) 0
  exact absurd this (by decide)

/-- **Control — co-isotropy is load-bearing.** At `⊥` with `u = 0` the theorem's conclusion is
*false* at the word `1`: the output support is the single point `0`, so the left side is `0`,
while the Walsh transform of a one-point amplitude is nonzero at both words. A version of
`amp_hRaise` without `horth` is refuted here. -/
example :
    amp (hRaise 0 (0 : Fin 1 → ZMod 2) botState) ![1]
      ≠ walshTransform 0 (amp botState) ![1] := by
  have hL : ¬ ∃ p ∈ (hRaise 0 (0 : Fin 1 → ZMod 2) botState).L,
      (![1] : Fin 1 → ZMod 2) = (hRaise 0 (0 : Fin 1 → ZMod 2) botState).x₀ + p.X := by
    rintro ⟨p, hp, h⟩
    rw [hRaise_L] at hp
    change p ∈ Submodule.map (pauliSwapOn {0}) (⊥ : Submodule (ZMod 2) (Pauli 1)) at hp
    rw [Submodule.map_bot, Submodule.mem_bot] at hp
    subst hp
    have h0 := congrFun h 0
    revert h0
    decide
  rw [amp_neg hL]
  unfold walshTransform
  have hu0 : Function.update (![1] : Fin 1 → ZMod 2) 0 0 = ![0] := by decide
  have hu1 : Function.update (![1] : Fin 1 → ZMod 2) 0 1 = ![1] := by decide
  have hpos : amp botState ![0] = 1 := by
    have hsup : ∃ p ∈ botState.L, (![0] : Fin 1 → ZMod 2) = botState.x₀ + p.X :=
      ⟨0, Submodule.zero_mem _, by decide⟩
    rw [amp_pos hsup]
    change ampCore 1 0 (0 : DiagPhase (1 + 0) 1) 1 ![0] = 1
    rw [ampCore_zero, realPhase_zero_poly]
    simp
  have hneg : amp botState ![1] = 0 := by
    refine amp_neg ?_
    rintro ⟨p, hp, h⟩
    change p ∈ (⊥ : Submodule (ZMod 2) (Pauli 1)) at hp
    rw [Submodule.mem_bot] at hp
    subst hp
    have h0 := congrFun h 0
    revert h0
    decide
  rw [hu0, hu1, hpos, hneg]
  change (0 : ℂ) ≠ (1 / (Real.sqrt 2 : ℂ)) * (1 + signOf 1 * 0)
  rw [signOf_one, mul_zero, add_zero, mul_one]
  exact one_div_sqrt_two_ne_zero.symm

/-! ## Control — `1 ≤ m` is load-bearing -/

/-- At `m = 0` the ring is trivial and the emitted sign coefficient is `0`: the Walsh sign
cannot be produced there. -/
example : (2 : ZMod (2 ^ 0)) ^ (0 - 1) = 0 := by
  haveI : Subsingleton (ZMod (2 ^ 0)) := by
    rw [pow_zero]
    exact inferInstanceAs (Subsingleton (ZMod 1))
  exact Subsingleton.elim _ _

/-- At `m = 1` the same coefficient is `1 = 2^{m−1}`, of order two: the sign is live. -/
example : ((2 : ZMod (2 ^ 1)) ^ (1 - 1)).val = 1 := by decide

/-! ## Agreement — one amplitude, two routes -/

/-- **Agreement, referee route.** The Bell output at `11` is `−1/√2`, by `amp_hRaise_bell` and
the Walsh transform of the input. -/
example :
    amp (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState) ![1, 1]
      = -(1 / (Real.sqrt 2 : ℂ)) := by
  rw [amp_hRaise_bell, walsh_amp_bellState_oneone]

/-- **Agreement, exponent route.** The same value from the carrier's own exponent:
`hRaise_bell_exponent` gives exponent `z₀·z₁ = 1` at `11`, so the phase is `π` and the amplitude
is `(1/√2)·e^{iπ} = −1/√2`. The `Q`-component of `hRaise` does not read `L`, so the
placeholder record `bellIn` and `bellState` have the same output exponent by `rfl`. -/
example :
    amp (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState) ![1, 1]
      = -(1 / (Real.sqrt 2 : ℂ)) := by
  have hsup : ∃ p ∈ (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).L,
      (![1, 1] : Fin 2 → ZMod 2) = (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).x₀ + p.X := by
    refine (hRaise_mem_support_iff 0 ![0, 1] bellState bellL_coisotropic bellL_not_mem_shadow
      ![1, 1]).mpr ⟨1, ⟨![1, 1], 0⟩, mem_bellL.mpr ⟨by decide, rfl⟩, ?_⟩
    rw [update_oneone_one]
    decide
  rw [amp_pos hsup]
  change ampCore 1 0 (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).Q
    (1 / (Real.sqrt 2 : ℂ)) ![1, 1] = -(1 / (Real.sqrt 2 : ℂ))
  rw [ampCore_zero]
  have hQ : (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).Q
      = (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellIn).Q := rfl
  have heval : @DiagPhase.eval (2 + 0) 1 (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).Q
      ![1, 1] = 1 := by
    rw [hQ]
    refine (hRaise_bell_exponent (![1, 1] : Fin (2 + 0) → ZMod 2)).trans ?_
    change ((((![1, 1] : Fin (2 + 0) → ZMod 2) (Fin.castAdd 0 0)).val : ZMod 2)
        * (((![1, 1] : Fin (2 + 0) → ZMod 2) (Fin.castAdd 0 1)).val : ZMod 2)) = 1
    decide
  have hphase : @DiagPhase.realPhase (2 + 0) 1 (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).Q
      ![1, 1] = Real.pi := by
    unfold DiagPhase.realPhase
    rw [heval]
    have hv : ((1 : ZMod (2 ^ 1))).val = 1 := by decide
    rw [hv]
    norm_num
  rw [hphase,
    show Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I from by ring,
    Complex.exp_pi_mul_I]
  ring

/-! ## Kernel rows — the decidable support side of the odd-parity example -/

/-- Membership in the odd-parity Lagrangian is decidable, through its constraint form. -/
instance decidableMemSParityL : DecidablePred (· ∈ sParityL) := fun p =>
  decidable_of_iff _ (mem_sParityL (p := p)).symm

/-- A generator is in: `Z₀Z₁Z₂` times `X₀X₁`. -/
example : (⟨![1, 1, 0], ![1, 1, 1]⟩ : Pauli 3) ∈ sParityL := by decide

/-- An odd-weight X-part is out. -/
example : (⟨![1, 0, 0], 0⟩ : Pauli 3) ∉ sParityL := by decide

/-- The branch value at the word `011`: `raiseConst = 1`, `u ⬝ w = 0`, so `t = 1`. -/
example :
    raiseConst 0 (![0, 1, 1] : Fin 3 → ZMod 2) (![1, 0, 0] : Fin 3 → ZMod 2)
      + dotF2 (![0, 1, 1] : Fin 3 → ZMod 2) ![0, 1, 1] = 1 := by
  decide

/-- The surviving branch `111` is on the odd-parity support coset `(1,0,0) + even-weight`. -/
example :
    ∃ p ∈ sParityL,
      Function.update (![0, 1, 1] : Fin 3 → ZMod 2) 0 1 = ![1, 0, 0] + p.X := by
  decide

/-- The other branch `011` is off it: `011 − 100 = 111` has odd weight. -/
example :
    ¬ ∃ p ∈ sParityL,
      Function.update (![0, 1, 1] : Fin 3 → ZMod 2) 0 0 = ![1, 0, 0] + p.X := by
  decide

/-- The odd-parity output support contains `011` — `hRaise_mem_support_iff`'s right side has
the witness above, so the theorem's left side holds there. -/
example :
    ∃ p ∈ (hRaise 0 (![0, 1, 1] : Fin 3 → ZMod 2) sParityState).L,
      (![0, 1, 1] : Fin 3 → ZMod 2)
        = (hRaise 0 (![0, 1, 1] : Fin 3 → ZMod 2) sParityState).x₀ + p.X :=
  (hRaise_mem_support_iff 0 ![0, 1, 1] sParityState sParityL_coisotropic
    sParityL_not_mem_shadow ![0, 1, 1]).mpr ⟨1, by
      change ∃ p ∈ sParityL,
        Function.update (![0, 1, 1] : Fin 3 → ZMod 2) 0 1 = ![1, 0, 0] + p.X
      decide⟩

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_sub_right' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms dotF2_sub_right

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_update_of_eq_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dotF2_update_of_eq_zero

/-- info: 'FTQCLib.Frame.Walkthrough.update_sub_offset' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms update_sub_offset

/-- info: 'FTQCLib.Frame.Walkthrough.mem_sup_span_single_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_sup_span_single_iff

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_mem_support_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hRaise_mem_support_iff

/-- info: 'FTQCLib.Frame.Walkthrough.branch_eq_of_mem_support' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms branch_eq_of_mem_support

/-- info: 'FTQCLib.Frame.Walkthrough.exp_hRaise_term' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms exp_hRaise_term

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_hRaise' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ampCore_hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hRaise' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hRaise_indep' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_hRaise_indep

/-- info: 'FTQCLib.Frame.Walkthrough.bellState' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms bellState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hRaise_bell' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_hRaise_bell

/-- info: 'FTQCLib.Frame.Walkthrough.sParityL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sParityL

/-- info: 'FTQCLib.Frame.Walkthrough.mem_sParityL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms mem_sParityL

/-- info: 'FTQCLib.Frame.Walkthrough.sParityL_coisotropic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sParityL_coisotropic

/-- info: 'FTQCLib.Frame.Walkthrough.sParityL_not_mem_shadow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sParityL_not_mem_shadow

/-- info: 'FTQCLib.Frame.Walkthrough.sParityL_representer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sParityL_representer

/-- info: 'FTQCLib.Frame.Walkthrough.sParityState' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms sParityState

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hRaise_sParity' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_hRaise_sParity

end FTQCLib.Frame.Walkthrough

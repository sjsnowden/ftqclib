/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardCover

/-!
# Check: the covering theorem

The control is aimed at `amp_applyHFiner`'s support hypothesis: on the Bell state, whose bit `0`
is *not* X-supported, `applyHFiner` on bit `0` gives amplitude `0` at the word `01` where the
referee gives `1/√2` — so the hypothesis `e_k ∈ π_X(L)` is load-bearing: `applyHFiner` on a
pinned or correlated bit is wrong, not merely uncertified. The premise rows pin that the refuted
hypothesis is that one (`1 ≤ m` holds at Bell).

The kernel rows decide the cover's case split on Bell through the transported instance
`decidableMemShadow`: `e₀` is out of Bell's shadow (the `hRaise` case), and in the shadow of the
raised Lagrangian (so the second `H` is the `applyHFiner` case) — the two membership facts that
drive `amp_applyHFiner_hRaise_bell`, both by `decide`.

The agreement row reaches the mixed round trip's Bell amplitude at `11` two ways: by the
involutivity theorem (`amp_applyHFiner_hRaise_bell`), and by explicit referee arithmetic through
the values of `amp_hRaise_bell` — `applyHFiner`'s Walsh transform of `hRaise`'s Walsh transform,
summed by hand.

What no row here tests: `1 ≤ m` for `applyHFiner` is inherited from
`ampCore_applyHFiner_eq_walsh` and is not separately controlled here (`HadamardAmplitudeCheck`
carries the `m = 0` inertness row); no amplitude row is a kernel row (`Complex.exp`). -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## Shared evaluations on the Bell state -/

/-- `realPhase` of the zero exponent vanishes. -/
theorem realPhase_zero_poly' {N m : ℕ} (v : Fin N → ZMod 2) :
    DiagPhase.realPhase (0 : DiagPhase N m) v = 0 := by
  unfold DiagPhase.realPhase DiagPhase.eval
  rw [map_zero, ZMod.val_zero]
  simp

/-- The Bell amplitude at `11` is `1`. -/
theorem amp_bellState_oneone' : amp bellState ![1, 1] = 1 := by
  have hsup : ∃ p ∈ bellState.L, (![1, 1] : Fin 2 → ZMod 2) = bellState.x₀ + p.X :=
    ⟨⟨![1, 1], 0⟩, mem_bellL.mpr ⟨by decide, rfl⟩, by decide⟩
  rw [amp_pos hsup]
  change ampCore 1 0 (0 : DiagPhase (2 + 0) 1) 1 ![1, 1] = 1
  rw [ampCore_zero, realPhase_zero_poly']
  simp

/-- The Bell amplitude at `01` is `0`. -/
theorem amp_bellState_zeroone' : amp bellState ![0, 1] = 0 := by
  refine amp_neg ?_
  rintro ⟨p, hp, h⟩
  change (![0, 1] : Fin 2 → ZMod 2) = 0 + p.X at h
  rw [zero_add] at h
  have h1 := hp.1
  rw [← h] at h1
  exact absurd h1 (by decide)

/-- The Walsh signs. -/
theorem signOf_zero' : signOf (0 : ZMod 2) = 1 := by
  unfold signOf
  rw [if_pos rfl]

/-- The Walsh signs. -/
theorem signOf_one' : signOf (1 : ZMod 2) = -1 := by
  unfold signOf
  rw [if_neg (by decide)]

/-! ## Control — the X-supported hypothesis of `amp_applyHFiner` is load-bearing -/

/-- **Control — `hk` is load-bearing.** Bell's bit `0` is not X-supported. `applyHFiner 0` keeps
the support, so its amplitude at `01` is `0`; the referee at `01` reads the on-support branch
`11` and gives `1/√2`. A version of `amp_applyHFiner` without `hk` is refuted here:
`applyHFiner` on a bit that is not X-supported is wrong, not merely uncertified. -/
example :
    amp (applyHFiner 0 bellState) ![0, 1] ≠ walshTransform 0 (amp bellState) ![0, 1] := by
  have hoff : ¬ ∃ p ∈ (applyHFiner 0 bellState).L,
      (![0, 1] : Fin 2 → ZMod 2) = (applyHFiner 0 bellState).x₀ + p.X := by
    rintro ⟨p, hp, h⟩
    change (![0, 1] : Fin 2 → ZMod 2) = 0 + p.X at h
    rw [zero_add] at h
    have h1 : p.X 0 = p.X 1 := hp.1
    rw [← h] at h1
    exact absurd h1 (by decide)
  rw [amp_neg hoff]
  unfold walshTransform
  rw [show Function.update (![0, 1] : Fin 2 → ZMod 2) 0 0 = ![0, 1] from by decide,
    show Function.update (![0, 1] : Fin 2 → ZMod 2) 0 1 = ![1, 1] from by decide,
    amp_bellState_zeroone', amp_bellState_oneone']
  change (0 : ℂ) ≠ (1 / (Real.sqrt 2 : ℂ)) * (0 + signOf 0 * 1)
  rw [signOf_zero', one_mul, zero_add, mul_one]
  exact (one_div_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))).symm

/-- The control's premise: `1 ≤ m` holds at Bell, so the refuted hypothesis is `hk`. -/
example : 1 ≤ bellState.m := le_rfl

/-- The control's other premise: `e₀` is not in Bell's shadow (`bellL_not_mem_shadow`). -/
example : (Pi.single 0 1 : Fin 2 → ZMod 2) ∉ Submodule.map xProj bellL :=
  bellL_not_mem_shadow

/-! ## Kernel rows — the cover's case split on Bell, decided -/

/-- Membership in the Bell Lagrangian is decidable, through its constraint form. -/
instance decidableMemBellL : DecidablePred (· ∈ bellL) := fun p =>
  decidable_of_iff _ (mem_bellL (p := p)).symm

/-- Membership in the raised Bell Lagrangian is decidable, through the image description. -/
instance decidableMemBellLSwap :
    DecidablePred (· ∈ Submodule.map (pauliSwapOn {0}) bellL) := fun p =>
  decidable_of_iff (∃ q ∈ bellL, pauliSwapOn {0} q = p) Submodule.mem_map.symm

/-- Before the raise: `e₀ ∉ π_X(bellL)` — the cover takes the `hRaise` case. -/
example : (Pi.single 0 1 : Fin 2 → ZMod 2) ∉ Submodule.map xProj bellL := by decide

/-- After the raise: `e₀ ∈ π_X(swap₀ bellL)` — the second `H` takes the `applyHFiner` case. -/
example :
    (Pi.single 0 1 : Fin 2 → ZMod 2)
      ∈ Submodule.map xProj (Submodule.map (pauliSwapOn {0}) bellL) := by
  decide

/-- The `applyHFiner` disjunct of the cover is false at Bell, bit `0`, by its first conjunct. -/
example :
    ¬ ((Pi.single 0 1 : Fin 2 → ZMod 2) ∈ Submodule.map xProj bellState.L
        ∧ amp (applyHFiner 0 bellState) = walshTransform 0 (amp bellState)) :=
  fun h => bellL_not_mem_shadow h.1

/-! ## Agreement — the mixed round trip's Bell amplitude, two routes -/

/-- **Agreement, theorem route.** After raising and then freeing bit `0`, the Bell amplitude at
`11` is back to `1` — by `amp_applyHFiner_hRaise_bell`. -/
example :
    amp (applyHFiner 0 (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState)) ![1, 1] = 1 := by
  rw [amp_applyHFiner_hRaise_bell, amp_bellState_oneone']

/-- **Agreement, arithmetic route.** The same value by the referee twice, with the values of
`amp_hRaise_bell` in between: `amp (hRaise …)` is the Walsh transform of the Bell amplitude,
which is `1/√2` at `01` and `−1/√2` at `11`; the second Walsh transform at `11` sums them with
the sign `(−1)` to `(1/√2)(1/√2 + 1/√2) = 1`. -/
example :
    amp (applyHFiner 0 (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState)) ![1, 1] = 1 := by
  have hk : (Pi.single 0 1 : Fin 2 → ZMod 2)
      ∈ Submodule.map xProj (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState).L := by
    rw [hRaise_L]
    exact single_mem_shadow_swap bellL_coisotropic bellL_not_mem_shadow
  rw [amp_applyHFiner 0 _ le_rfl hk, amp_hRaise_bell]
  unfold walshTransform
  simp only [show Function.update (![1, 1] : Fin 2 → ZMod 2) 0 0 = ![0, 1] from by decide,
    show Function.update (![1, 1] : Fin 2 → ZMod 2) 0 1 = ![1, 1] from by decide,
    show Function.update (![0, 1] : Fin 2 → ZMod 2) 0 0 = ![0, 1] from by decide,
    show Function.update (![0, 1] : Fin 2 → ZMod 2) 0 1 = ![1, 1] from by decide,
    show (![1, 1] : Fin 2 → ZMod 2) 0 = 1 from by decide,
    show (![0, 1] : Fin 2 → ZMod 2) 0 = 0 from by decide,
    amp_bellState_zeroone', amp_bellState_oneone', signOf_zero', signOf_one']
  have h2 : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  linear_combination (2 : ℂ) * h2

/-! ## The axiom sweep — build-failing, one guard per declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.update_eq_add_smul_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms update_eq_add_smul_single

/-- info: 'FTQCLib.Frame.Walkthrough.mem_support_update_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_support_update_iff

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyHFiner' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms amp_applyHFiner

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_cover' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms hadamard_cover

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_cover_xor' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hadamard_cover_xor

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_total' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms hadamard_total

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyHFiner_hRaise' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_applyHFiner_hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyHFiner_applyHFiner' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_applyHFiner_applyHFiner

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyHFiner_hRaise_bell' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amp_applyHFiner_hRaise_bell

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_cover_sParity' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hadamard_cover_sParity

end FTQCLib.Frame.Walkthrough

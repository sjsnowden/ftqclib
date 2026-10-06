/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ConditionFloor
import FTQCLib.Carrier.ConditioningCheck

/-!
# Check: T12's witness, two rows on the Bell state

T12's witness (`docs/STEPS.md`, T12.2): two rows on `ConditionFloor.lean`'s frozen statement,
computed by hand on the Bell state `bellState` (`HadamardAmplitude.lean`), read as a height-zero
`Hierarchy.KernelState` (`bellK`). Neither of `ConditionFloor.lean`'s three headline theorems is
used here — they were proved at T12.3.1–T12.3.3, after these rows were written — so every row is
proved by unfolding
`KernelState.restrict`/`restrictZ`/`sliceZ`/`condition`/`pauliCondition` directly, exactly as
`ConditioningCheck.lean`'s rows compute `condition` by hand.

* **Row (discriminating).** `KernelState.restrict` and `restrictZ` on the Bell state at bit `0`,
  outcome `1` — the case the docstring and `docs/TARGETS.md`'s 'Need' name. `restrict`'s offset
  update only touches bit `0`, leaving bit `1` at the Bell state's own `0`, so `restrict 0 1` is
  the point `(1, 0) = ∣10⟩`. `restrictZ 0 1` conditions on `Z₀` (a bound step, `Z₀`'s X-part `0`
  is in every shadow), cuts the support to the slice `w₀ = 1` — on `bellL`'s two-point shadow
  `{(0,0),(1,0,1,1)}` ... `{v : v 0 = v 1}`, the only point with `v 0 = 1` is `(1,1)` — and drops
  bit `0`: reinserting it at `1` gives the point `(1,1) = ∣11⟩`. The two points disagree at
  bit `1`: `0` against `1`, so `restrict` and `restrictZ` are discriminated by the word `(1,1)` (or
  equally `(1,0)`), exactly where `e₀ ∉ π_X(L)` (bit `0` is not free: `π_X(pauliCondition bellL
  Z₀) = 0`) and `x₀ 0 = 0 ≠ 1 = b`, the side `restrict_eq_restrictZ_iff`'s right side excludes.
* **Row (agreement).** `X₀X₁` on the Bell state against `pauliCondition` on `bellL`: `X₀X₁ ∈
  bellL` already, so both sides of `condition_eq_pauliCondition`'s domain restriction
  (`P ∉ K.L`) are moot and the Lagrangian does not move — `condition`'s bound constructor keeps
  `bellL` (`conditionBound_L`), and `pauliCondition` on a Pauli already in the subspace is the
  subspace itself (`pauliCondition_of_mem`). The two routes to "the Lagrangian after measuring
  `X₀X₁`" agree, both landing on `bellL`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ## The Bell state as a height-zero `Hierarchy.KernelState` -/

/-- The Bell state read as a `Hierarchy.KernelState`: flat exponent, scale `1`, `L = bellL`, zero
offset. -/
noncomputable def bellK : KernelState 2 := ⟨1, 0, 1, bellL, 0⟩

/-- `ofKernelState bellK` is `bellState`, on the nose: both are `⟨1, 0, 0, 1, bellL, 0⟩`. -/
theorem ofKernelState_bellK : ofKernelState bellK = bellState := rfl

/-! ## A fact the topic module does not state: `signedZ`'s X-part is in every shadow -/

/-- `signedZ j`'s Pauli has X-part `0`, so it lies in every shadow: conditioning on it is always
the bound constructor. -/
theorem signedZ_mem_shadow {n : ℕ} (j : Fin n) (S : Submodule (ZMod 2) (Pauli n)) :
    (signedZ j).pauli.X ∈ Submodule.map xProj S := by
  have hX : (signedZ j).pauli.X = (0 : Fin n → ZMod 2) := rfl
  rw [hX]
  exact Submodule.zero_mem _

/-- The bound constructor keeps the offset (the omitted half of `conditionBound`'s simp set). -/
theorem conditionBound_x₀ {n : ℕ} (S : KernelSumState n) (P : SignedPauli n) (b : ZMod 2) :
    (conditionBound S P b).x₀ = S.x₀ := rfl

/-! ## Row (discriminating): `KernelState.restrict` gives `∣10⟩`, `restrictZ` gives `∣11⟩` -/

/-- **`KernelState.restrict`'s offset at bit `0`, outcome `1`.** Only bit `0` of the offset
moves; bit `1` stays at the Bell state's own `0` — the point `(1, 0)`. -/
theorem restrict_bellK_x0 : (bellK.restrict 0 1).x₀ = (![1, 0] : Fin 2 → ZMod 2) := by
  show Function.update (0 : Fin 2 → ZMod 2) 0 1 = ![1, 0]
  funext i
  fin_cases i <;> simp

/-- Conditioning the Bell state on `Z₀` at outcome `1` is the bound constructor: `Z₀`'s X-part
`0` is in `bellL`'s shadow. -/
theorem condition_bellState_z0 :
    condition (ofKernelState bellK) (signedZ 0) 1
      = conditionBound (ofKernelState bellK) (signedZ 0) 1 :=
  condition_of_mem (signedZ_mem_shadow 0 (ofKernelState bellK).L) 1

/-- The conditioned record's support data: `L` stays `bellL`, the offset stays `0` — the bound
constructor's `h`-raising move leaves both untouched. -/
theorem condition_bellState_z0_L_x0 :
    (condition (ofKernelState bellK) (signedZ 0) 1).L = bellL
      ∧ (condition (ofKernelState bellK) (signedZ 0) 1).x₀ = (0 : Fin 2 → ZMod 2) := by
  rw [condition_bellState_z0, conditionBound_L, conditionBound_x₀]
  exact ⟨rfl, rfl⟩

/-- **The slice exists, at the point `(1, 1)`.** `bellL`'s shadow is `{v : v 0 = v 1}`
(`mem_shadow_bellL_iff`); the point `(1, 1)` is in it and has `0 + v 0 = 1`, the outcome. -/
theorem sliceZ_exists_bellK :
    ∃ v ∈ Submodule.map xProj (condition (ofKernelState bellK) (signedZ 0) 1).L,
      (condition (ofKernelState bellK) (signedZ 0) 1).x₀ 0 + v 0 = 1 := by
  refine ⟨![1, 1], ?_, ?_⟩
  · rw [(condition_bellState_z0_L_x0).1]
    exact (mem_shadow_bellL_iff ![1, 1]).mpr (by decide)
  · rw [(condition_bellState_z0_L_x0).2]
    decide

/-- **The slice's chosen offset is `(1, 1)`.** Any point of `bellL`'s shadow with bit `0` equal
to the outcome `1` has bit `1` equal to `1` too (`mem_shadow_bellL_iff`), so it is `(1, 1)`. -/
theorem sliceZ_choose_eq_bellK :
    Classical.choose sliceZ_exists_bellK = (![1, 1] : Fin 2 → ZMod 2) := by
  generalize hv : Classical.choose sliceZ_exists_bellK = v
  obtain ⟨hmem, heq⟩ := Classical.choose_spec sliceZ_exists_bellK
  rw [hv] at hmem heq
  rw [(condition_bellState_z0_L_x0).1] at hmem
  rw [(condition_bellState_z0_L_x0).2] at heq
  have h01 : v 0 = v 1 := (mem_shadow_bellL_iff _).mp hmem
  have h0 : v 0 = 1 := by simpa using heq
  funext i
  fin_cases i
  · simpa using h0
  · simpa [← h01] using h0

/-- **The sliced record's offset is `(1, 1)`.** `sliceZ` takes the existence branch
(`sliceZ_exists_bellK`), adding the chosen point `(1, 1)` (`sliceZ_choose_eq_bellK`) to the
unchanged offset `0`. -/
theorem sliceZ_bellK_x0 :
    (sliceZ (0 : Fin 2) 1 (condition (ofKernelState bellK) (signedZ 0) 1)).x₀
      = (![1, 1] : Fin 2 → ZMod 2) := by
  classical
  unfold sliceZ
  rw [dif_pos sliceZ_exists_bellK, sliceZ_choose_eq_bellK, (condition_bellState_z0_L_x0).2]
  funext i
  fin_cases i <;> simp

/-- **`restrictZ`'s one offset coordinate is the sliced record's offset at bit `1`.** Dropping
bit `0` (`Fin.succAbove 0 0 = 1`) carries that coordinate forward unchanged, regardless of which
reader `dropFreeBit` chooses — `dropFreeBitBy`'s offset field does not mention the reader. -/
theorem restrictZ_bellK_x0 :
    (restrictZ (0 : Fin 2) 1 (ofKernelState bellK)).x₀ 0
      = (sliceZ (0 : Fin 2) 1 (condition (ofKernelState bellK) (signedZ 0) 1)).x₀ 1 := by
  show (sliceZ (0 : Fin 2) 1 (condition (ofKernelState bellK) (signedZ 0) 1)).x₀
      (Fin.succAbove (0 : Fin 2) (0 : Fin 1)) = _
  congr 1

/-- **Discriminating.** `KernelState.restrict`'s offset at bit `1` is `0` (`restrict_bellK_x0`,
the point `(1, 0) = ∣10⟩`), while `restrictZ`'s one offset coordinate — the value it carries
forward to bit `1` — is `1` (`restrictZ_bellK_x0`, `sliceZ_bellK_x0`, the point
`(1, 1) = ∣11⟩`): the two disagree at the named input, bit `1`. -/
-- row: discriminating
theorem restrict_ne_restrictZ_bellK :
    (bellK.restrict 0 1).x₀ 1 ≠ (restrictZ (0 : Fin 2) 1 (ofKernelState bellK)).x₀ 0 := by
  rw [restrict_bellK_x0, restrictZ_bellK_x0, sliceZ_bellK_x0]
  decide

/-! ## Row (agreement): `X₀X₁` on the Bell state against `pauliCondition` on `bellL` -/

/-- `X₀X₁`: sign `+`, Pauli `paulix 0 + paulix 1`. -/
noncomputable def x0x1Bell : SignedPauli 2 := ⟨0, paulix 0 + paulix 1⟩

/-- `X₀X₁` is already in `bellL`: equal X-entries (both `1`), equal Z-entries (both `0`). -/
theorem x0x1Bell_mem : x0x1Bell.pauli ∈ bellL := by
  show (paulix (0 : Fin 2) + paulix 1).X 0 = (paulix (0 : Fin 2) + paulix 1).X 1
    ∧ (paulix (0 : Fin 2) + paulix 1).Z 0 = (paulix (0 : Fin 2) + paulix 1).Z 1
  simp only [FTQCLib.Pauli.X_add, FTQCLib.Pauli.Z_add, Pi.add_apply, paulix_X, paulix_Z,
    Pi.zero_apply, add_zero]
  decide

/-- **`pauliCondition` on `bellL` at `X₀X₁` is `bellL`.** `X₀X₁` is already in `bellL`
(`x0x1Bell_mem`), so `pauliCondition` returns `bellL` unchanged. -/
theorem pauliCondition_bellL_x0x1 :
    FTQCLib.Stabilizer.pauliCondition bellL x0x1Bell.pauli = bellL :=
  FTQCLib.Stabilizer.pauliCondition_of_mem x0x1Bell_mem

/-- Conditioning the Bell state on `X₀X₁` at outcome `0` is the bound constructor: `X₀X₁`'s
X-part is in `bellL`'s shadow (it is the image of `X₀X₁ ∈ bellL` itself). -/
theorem condition_bellState_x0x1 :
    condition (ofKernelState bellK) x0x1Bell 0
      = conditionBound (ofKernelState bellK) x0x1Bell 0 := by
  refine condition_of_mem ?_ 0
  rw [show (ofKernelState bellK).L = bellL from rfl]
  exact Submodule.mem_map.mpr ⟨x0x1Bell.pauli, x0x1Bell_mem, rfl⟩

/-- **Agreement.** Conditioning the Bell state on `X₀X₁` keeps the Lagrangian `bellL`
(`conditionBound_L`), exactly `pauliCondition bellL` at `X₀X₁` (`pauliCondition_bellL_x0x1`):
both routes to "the Lagrangian after measuring `X₀X₁`" land on `bellL`. -/
-- row: agreement
theorem condition_bellState_x0x1_eq_pauliCondition :
    (condition (ofKernelState bellK) x0x1Bell 0).L
      = FTQCLib.Stabilizer.pauliCondition bellL x0x1Bell.pauli := by
  rw [condition_bellState_x0x1, conditionBound_L, pauliCondition_bellL_x0x1]
  rfl

/-! ## Row (inhabitation): `restrict_eq_restrictZ_iff`'s hypothesis on `bellK` -/

/-- `ofKernelState bellK`'s amplitude at the zero word is `1`: the zero word is on the support
(`p = 0 ∈ bellL`), where the value is `bellK.c · charOf bellK.m (eval bellK.q 0) = 1 · charOf 1 0
= 1`. -/
theorem amp_ofKernelState_bellK_zero : amp (ofKernelState bellK) (0 : Fin 2 → ZMod 2) = 1 := by
  have hw : ∃ p ∈ bellK.L, (0 : Fin 2 → ZMod 2) = bellK.x₀ + p.X := by
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    show (0 : Fin 2 → ZMod 2) = (0 : Fin 2 → ZMod 2) + (0 : Pauli 2).X
    simp
  rw [amp_ofKernelState_pos bellK hw]
  have heval : DiagPhase.eval (bellK.q) (0 : Fin 2 → ZMod 2) = 0 := by
    change DiagPhase.eval (0 : DiagPhase (2 + 0) 1) (0 : Fin 2 → ZMod 2) = 0
    simp [DiagPhase.eval]
  rw [heval, charOf_zero]
  show (1 : ℂ) * 1 = 1
  norm_num

/-- **`restrict_eq_restrictZ_iff`'s hypothesis holds on `bellK`.** `IsCarrier (ofKernelState
bellK)`: precision `1 ≤ bellK.m`, `bellL` a Lagrangian (`bellL_isStabilizer`,
`bellL_coisotropic`), and a nonzero amplitude (`amp_ofKernelState_bellK_zero`). -/
theorem isCarrier_bellK : IsCarrier (ofKernelState bellK) :=
  ⟨le_refl 1, bellL_isStabilizer, bellL_coisotropic,
    fun h => one_ne_zero (amp_ofKernelState_bellK_zero ▸ congrFun h (0 : Fin 2 → ZMod 2))⟩

/-- **Inhabitation.** `restrict_eq_restrictZ_iff`'s hypothesis `IsCarrier (ofKernelState K)`
(`isCarrier_bellK`) holds on the concrete object `bellK`, so the theorem applies to it at bit `0`,
outcome `1`. -/
-- row: inhabitation
theorem restrict_eq_restrictZ_iff_bellK :
    amp (ofKernelState (bellK.restrict 0 1))
        = (fun w => if w 0 = 1
            then amp (restrictZ 0 1 (ofKernelState bellK)) (Fin.removeNth 0 w) else 0)
      ↔ ((Pi.single (0 : Fin 2) 1 : Fin 2 → ZMod 2) ∈ Submodule.map xProj bellK.L
          ∨ bellK.x₀ 0 = 1) :=
  restrict_eq_restrictZ_iff bellK isCarrier_bellK 0 1

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, every public theorem of the topic and check modules -/

/-- info: 'FTQCLib.Frame.Walkthrough.signedZ_mem_shadow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.signedZ_mem_shadow

/-- info: 'FTQCLib.Frame.Walkthrough.conditionBound_x₀' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionBound_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.restrict_bellK_x0' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrict_bellK_x0

/-- info: 'FTQCLib.Frame.Walkthrough.condition_bellState_z0' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_bellState_z0

/-- info: 'FTQCLib.Frame.Walkthrough.condition_bellState_z0_L_x0' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_bellState_z0_L_x0

/-- info: 'FTQCLib.Frame.Walkthrough.sliceZ_exists_bellK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sliceZ_exists_bellK

/-- info: 'FTQCLib.Frame.Walkthrough.sliceZ_choose_eq_bellK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sliceZ_choose_eq_bellK

/-- info: 'FTQCLib.Frame.Walkthrough.sliceZ_bellK_x0' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sliceZ_bellK_x0

/-- info: 'FTQCLib.Frame.Walkthrough.restrictZ_bellK_x0' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrictZ_bellK_x0

/-- info: 'FTQCLib.Frame.Walkthrough.restrict_ne_restrictZ_bellK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrict_ne_restrictZ_bellK

/-- info: 'FTQCLib.Frame.Walkthrough.x0x1Bell_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.x0x1Bell_mem

/-- info: 'FTQCLib.Frame.Walkthrough.pauliCondition_bellL_x0x1' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliCondition_bellL_x0x1

/-- info: 'FTQCLib.Frame.Walkthrough.condition_bellState_x0x1' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_bellState_x0x1

/-- info: 'FTQCLib.Frame.Walkthrough.condition_bellState_x0x1_eq_pauliCondition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_bellState_x0x1_eq_pauliCondition

/-- info: 'FTQCLib.Frame.Walkthrough.amp_ofKernelState_bellK_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_ofKernelState_bellK_zero

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_bellK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_bellK

/-- info: 'FTQCLib.Frame.Walkthrough.restrict_eq_restrictZ_iff_bellK' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrict_eq_restrictZ_iff_bellK

/-- info: 'FTQCLib.Frame.Walkthrough.I_pow_outcomeChi' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.I_pow_outcomeChi

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_condition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isFloor_condition

/-- info: 'FTQCLib.Frame.Walkthrough.condition_eq_pauliCondition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_eq_pauliCondition

/-- info: 'FTQCLib.Frame.Walkthrough.restrict_eq_restrictZ_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrict_eq_restrictZ_iff

/-! ## Declared mutants, aimed at a theorem's conclusion and at a definition a proof uses -/

-- mutant: outcomeChi_label | FTQCLib/Carrier/ConditionFloor.lean
--   | 2 * (((b + P.sign).val : ℕ) : ZMod 4)
--   | (((b + P.sign).val : ℕ) : ZMod 4)
-- mutant: signedZ_sign | FTQCLib/Carrier/ConditionFloor.lean | ⟨0, pauliz j⟩ | ⟨1, pauliz j⟩

/-! ## Axiom sweep: made public or moved here (docs/STEPS.md, entry 2026-09-30h) -/

/-- info: 'FTQCLib.Frame.Walkthrough.amp_restrictZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_restrictZ

/-- info: 'FTQCLib.Frame.Walkthrough.amp_sliceZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_sliceZ

/-- info: 'FTQCLib.Frame.Walkthrough.mem_map_pauliCondition_pauliz_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.mem_map_pauliCondition_pauliz_iff

/-- info: 'FTQCLib.Frame.Walkthrough.sliceZ_L' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sliceZ_L

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_signedZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.yWeight_signedZ

/-- info: 'FTQCLib.Frame.Walkthrough.signedZ_side' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.signedZ_side

/-- info: 'FTQCLib.Frame.Walkthrough.pauliProjection_signedZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliProjection_signedZ

/-- info: 'FTQCLib.Frame.Walkthrough.condition_signedZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_signedZ

/-- info: 'FTQCLib.Frame.Walkthrough.restrictZ_m' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrictZ_m

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_restrictZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_restrictZ

/-- info: 'FTQCLib.Frame.Walkthrough.appendFreeBits_m' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.appendFreeBits_m

/-- info: 'FTQCLib.Frame.Walkthrough.appendFreeBits_c' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.appendFreeBits_c

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_appendFreeBits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_appendFreeBits

/-- info: 'FTQCLib.Frame.Walkthrough.amp_appendFreeBits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_appendFreeBits

/-- info: 'FTQCLib.Frame.Walkthrough.restrictLast_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrictLast_spec

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_sliceZ_condition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_sliceZ_condition

/-- info: 'FTQCLib.Frame.Walkthrough.amp_pinZero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_pinZero

/-- info: 'FTQCLib.Frame.Walkthrough.pinZero_L' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pinZero_L

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_pinZero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_pinZero


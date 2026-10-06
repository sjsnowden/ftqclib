/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.Conditioning
import FTQCLib.Carrier.BoundElimination
import FTQCLib.Carrier.DyadicCharacterCheck
import FTQCLib.Carrier.HadamardAmplitude
import FTQCLib.Carrier.HadamardAmplitudeCheck

/-!
# Check: conditioning on a Pauli, on four small instances

T10's witness (`docs/STEPS.md`, T10.2): four rows on the frozen statement of `Conditioning.lean`,
computed by hand from the constructors `conditionBound`/`conditionRaise` and the test `condition`
picks between them. `Conditioning.lean`'s seven headline theorems (`condition_cover`,
`amp_condition`, ...) were not yet proved when these rows were written (T10.3.1–T10.3.3 proved
them), and none of them is used here; every row
is proved by unfolding `condition`/`conditionBound`/`conditionRaise` and computing `ampCore`
directly, exactly as the check modules of phase 1 compute `ampCore` by hand.

* **Row 1 (agreement).** `Z₀` on the Bell state (`bellState`, `HadamardAmplitude.lean`), both
  outcomes: `Z₀`'s X-part is `0`, always in the shadow, so `condition` takes the bound constructor
  (`condition_of_mem`). Hand-computed through `ampCore_peel_last`, the amplitude survives only at
  the diagonal point matching the outcome, of amplitude `1` — the two outcomes are the two halves
  of the Bell state's two-point support, each of weight `½` (`conditionBound_c`'s `c/√2`, together
  with the extra `1/√2` `ampCore`'s own height normalisation supplies, is exactly the docstring's
  "`1/√2` from the scale and `1/√2` from the height's normalisation").
* **Row 2 (agreement).** `X` on `∣0⟩` (one qubit, `L = ⊥`, `x₀ = 0`): `X`'s X-part is nonzero, off
  the shadow `⊥`, so `condition` takes the raise constructor (`condition_of_not_mem`, added here
  since the topic module states only the `mem` half of the test). Its `h` is unchanged
  (`conditionRaise_h`) and its shadow grows from `⊥` to `⊤` — "no new bound bit, a larger support".
* **Row 3 (agreement).** `Y` on a height-one state at `m = 2`: the same test (`Y`'s X-part lies in
  the full shadow `⊤`) takes the bound constructor one level up, `h : 1 → 2`; `Y`'s odd `Y`-weight
  needs precision two, already met, so `conditionPrecision` does not lift it — "at any height" and
  the precision remark hold away from `h = 0` too.
* **Row 4 (discriminating).** `Z` on `∣0⟩` at outcome `1`, against outcome `0`: the same one-qubit
  point state conditioned on `Z` at the impossible outcome has amplitude identically zero (D10);
  at the possible outcome its amplitude is nonzero. The two outcomes are discriminated by
  evaluation at the single support point.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## A fact the topic module does not state: the off-shadow half of the test -/

/-- The mirror of `condition_of_mem`: off the shadow, `condition` takes the raise constructor,
with the separator `condition` itself picks. -/
theorem condition_of_not_mem {n : ℕ} {S : KernelSumState n} {P : SignedPauli n}
    (hP : P.pauli.X ∉ Submodule.map xProj S.L) (b : ZMod 2) :
    condition S P b
      = conditionRaise S P b
          (Classical.epsilon (Separates (Submodule.map xProj S.L) P.pauli.X)) := by
  unfold condition
  exact if_neg hP

/-! ## Row 1: `Z₀` on the Bell state, both outcomes, each of weight `½` -/

/-- `Z₀` on two qubits: sign `+`, `Z`-part `e₀`. -/
noncomputable def z0Bell : SignedPauli 2 := ⟨0, zPauli (Pi.single (0 : Fin 2) 1)⟩

theorem z0Bell_X : z0Bell.pauli.X = 0 := rfl

theorem z0Bell_mem (L : Submodule (ZMod 2) (Pauli 2)) :
    z0Bell.pauli.X ∈ Submodule.map xProj L := by
  rw [z0Bell_X]; exact Submodule.zero_mem _

theorem branchPhase_z0Bell_eval (w : Fin 2 → ZMod 2) (β b : ZMod 2) :
    DiagPhase.eval (branchPhase (N := 3) 1 (fun j : Fin 2 => (Fin.castAdd 0 j).castSucc) z0Bell b)
      (Fin.snoc w β) = (b.val : ZMod (2 ^ 1)) + (w 0).val := by
  unfold branchPhase z0Bell zPauli yWeight zDot
  simp only [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X,
    Fin.sum_univ_two, Fin.snoc_castSucc, Fin.castAdd_zero, Fin.cast_eq_self, Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), Pi.zero_apply, ZMod.val_zero,
    ZMod.val_one, add_zero, zero_mul, mul_zero, Nat.cast_zero]
  norm_num [iPowExp]

/-- `ampCore` of the bound constructor's exponent, at the diagonal word `(a, a)`: `1` when `a`
matches the outcome `b`, `0` otherwise — the two branches of `ampCore_peel_last` cancel exactly
off the outcome. -/
theorem ampCore_conditionBound_z0Bell (b a : ZMod 2) :
    ampCore (conditionBound bellState z0Bell b).m (conditionBound bellState z0Bell b).h
        (conditionBound bellState z0Bell b).Q (conditionBound bellState z0Bell b).c
        (fun _ => a)
      = if a = b then (1 : ℂ) else 0 := by
  unfold bellState conditionBound
  dsimp only
  generalize_proofs pf
  revert pf
  generalize hm : conditionPrecision 1 z0Bell = m
  intro pf
  have hm1 : m = 1 := by
    rw [← hm]
    unfold conditionPrecision
    have hy : yWeight z0Bell.pauli = 0 := by unfold z0Bell zPauli yWeight zDot; simp
    rw [hy]; rfl
  subst hm1
  rw [ampCore_peel_last, ampCore_zero, ampCore_zero, exp_realPhase_eq_charOf,
    exp_realPhase_eq_charOf, snocFreeze_eval, snocFreeze_eval,
    show FTQCLib.Hilbert.liftTo 1 pf (0 : DiagPhase (2 + 0) 1) = 0 from rfl,
    show shiftSubst Fin.castSucc z0Bell.pauli.X (MvPolynomial.X (Fin.last (2 + 0)))
        (0 : DiagPhase (2 + 0) 1) = 0 from map_zero _,
    DiagPhase.eval_add, DiagPhase.eval_add,
    show DiagPhase.eval (0 : DiagPhase (2 + 0 + 1) 1) (Fin.snoc (fun _ : Fin 2 => a) 0) = 0 from
      by unfold DiagPhase.eval; simp,
    show DiagPhase.eval (0 : DiagPhase (2 + 0 + 1) 1) (Fin.snoc (fun _ : Fin 2 => a) 1) = 0 from
      by unfold DiagPhase.eval; simp,
    zero_add, zero_add, DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_X, DiagPhase.eval_X,
    Fin.snoc_last, Fin.snoc_last, branchPhase_z0Bell_eval, branchPhase_z0Bell_eval]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := sqrt_two_sq_complex
  rcases FTQCLib.Pauli.zmod_two_eq_zero_or_one a with ha | ha <;>
    rcases FTQCLib.Pauli.zmod_two_eq_zero_or_one b with hb | hb <;>
    subst ha <;> subst hb <;>
    simp only [ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      zero_add, add_zero, charOf_zero, show (1 : ZMod (2 ^ 1)) + (1 : ZMod (2 ^ 1)) = 0 from
        by decide] <;>
    norm_num [charOf_one_one, h2] <;>
    field_simp <;>
    rw [hsq] <;>
    ring

theorem mem_shadow_bellL_iff (v : Fin 2 → ZMod 2) :
    v ∈ Submodule.map xProj bellL ↔ v 0 = v 1 := by
  constructor
  · rintro hv
    obtain ⟨p, hp, hpv⟩ := Submodule.mem_map.mp hv
    rw [mem_bellL] at hp
    rw [← hpv, xProj_apply, hp.1]
  · intro hv
    refine Submodule.mem_map.mpr ⟨⟨v, 0⟩, mem_bellL.mpr ⟨hv, rfl⟩, ?_⟩
    rfl

theorem mem_support_bellState_iff (w : Fin 2 → ZMod 2) :
    (∃ p ∈ bellState.L, w = bellState.x₀ + p.X) ↔ w 0 = w 1 := by
  rw [mem_support_iff]
  have hx0 : bellState.x₀ = (0 : Fin 2 → ZMod 2) := rfl
  have hL : bellState.L = bellL := rfl
  rw [hx0, hL, sub_zero]
  exact mem_shadow_bellL_iff w

/-- The conditioned Bell state's support coset is the same diagonal (the bound constructor keeps
`L` and `x₀`). -/
theorem mem_support_condition_bell_iff (b : ZMod 2) (w : Fin 2 → ZMod 2) :
    (∃ p ∈ (condition bellState z0Bell b).L, w = (condition bellState z0Bell b).x₀ + p.X)
      ↔ w 0 = w 1 := by
  rw [condition_of_mem (z0Bell_mem bellState.L) b, conditionBound_L]
  show (∃ p ∈ bellState.L, w = bellState.x₀ + p.X) ↔ w 0 = w 1
  exact mem_support_bellState_iff w

/-- **Agreement.** `Z₀` on the Bell state, both outcomes, each of weight `½`: off the diagonal
both outcomes have amplitude zero (the bound constructor keeps the support); on the diagonal the
amplitude is `1` exactly where the free word matches the outcome — the hand computation of
`amp_condition`'s instance at `Z₀`, matching the referee `pauliProjection_zPauli_single` gives on
`bellState` (`w 0 = w 1`, `w 0 = b`). -/
-- row: agreement
theorem amp_condition_bell_z0 (b : ZMod 2) (w : Fin 2 → ZMod 2) :
    amp (condition bellState z0Bell b) w = if w 0 = w 1 ∧ w 0 = b then 1 else 0 := by
  by_cases hsup : w 0 = w 1
  · have heq : w = fun _ => w 0 := by funext i; fin_cases i <;> simp [hsup]
    have hmem : (∃ p ∈ (condition bellState z0Bell b).L,
        w = (condition bellState z0Bell b).x₀ + p.X) := by
      rw [mem_support_condition_bell_iff]; exact hsup
    rw [amp_pos hmem, condition_of_mem (z0Bell_mem bellState.L) b]
    rw [heq, ampCore_conditionBound_z0Bell]
    simp only [hsup, true_and]
  · rw [amp_neg (fun h => hsup ((mem_support_condition_bell_iff b w).mp h))]
    simp [hsup]

/-! ## Row 2: `X` on `∣0⟩`, no new bound bit, the support grows -/

/-- `X` on one qubit: sign `+`, `X`-part `e₀`. -/
noncomputable def x0Point : SignedPauli 1 := ⟨0, ⟨Pi.single (0 : Fin 1) 1, 0⟩⟩

theorem x0Point_notMem : x0Point.pauli.X ∉ Submodule.map xProj botState.L := by
  show (Pi.single (0 : Fin 1) 1 : Fin 1 → ZMod 2)
      ∉ Submodule.map xProj (⊥ : Submodule (ZMod 2) (Pauli 1))
  rw [Submodule.map_bot]
  simp only [Submodule.mem_bot]
  intro h
  have := congrFun h 0
  simp at this

theorem condition_x0Point_h (b : ZMod 2) : (condition botState x0Point b).h = 0 := by
  rw [condition_of_not_mem x0Point_notMem b, conditionRaise_h]
  rfl

theorem condition_x0Point_L (b : ZMod 2) :
    (condition botState x0Point b).L
      = Submodule.span (ZMod 2) ({x0Point.pauli} : Set (Pauli 1)) := by
  rw [condition_of_not_mem x0Point_notMem b]
  show (botState.L ⊓ LinearMap.BilinForm.orthogonal omegaBilin
          (Submodule.span (ZMod 2) {x0Point.pauli}))
        ⊔ Submodule.span (ZMod 2) {x0Point.pauli}
      = Submodule.span (ZMod 2) ({x0Point.pauli} : Set (Pauli 1))
  have hinf : botState.L ⊓ LinearMap.BilinForm.orthogonal omegaBilin
      (Submodule.span (ZMod 2) {x0Point.pauli}) = ⊥ := by
    show (⊥ : Submodule (ZMod 2) (Pauli 1)) ⊓ _ = ⊥
    exact bot_inf_eq _
  rw [hinf, bot_sup_eq]

/-- **Agreement.** `X` conditioning `∣0⟩`: the test is off the shadow (`X`'s X-part is nonzero,
`⊥`'s shadow is `{0}`), so `condition` takes the raise constructor: no new bound bit
(`conditionRaise_h`), and the Lagrangian becomes `⟨X⟩`, whose shadow is all of `Fin 1 → ZMod 2` —
the support grows from the single point `{0}` to everything. -/
-- row: agreement
theorem condition_x0Point_no_bound_bit_support_grows (b : ZMod 2) :
    (condition botState x0Point b).h = 0
      ∧ Submodule.map xProj (condition botState x0Point b).L = ⊤ := by
  refine ⟨condition_x0Point_h b, ?_⟩
  rw [condition_x0Point_L]
  ext v
  simp only [Submodule.mem_top, iff_true, Submodule.mem_map, Submodule.mem_span_singleton]
  refine ⟨v 0 • x0Point.pauli, ⟨v 0, rfl⟩, ?_⟩
  rw [xProj_apply]
  funext i
  fin_cases i
  show v 0 • (Pi.single (0 : Fin 1) 1 : Fin 1 → ZMod 2) 0 = v 0
  simp

/-! ## Row 3: `Y` on a height-one state at `m = 2` -/

/-- `Y` on one qubit: sign `+`, `X`-part and `Z`-part both `e₀`. -/
noncomputable def y0Pauli : SignedPauli 1 :=
  ⟨0, ⟨Pi.single (0 : Fin 1) 1, Pi.single (0 : Fin 1) 1⟩⟩

/-- A height-one, precision-two carrier state on one qubit, full shadow. -/
noncomputable def fullShadowHeightOneState : KernelSumState 1 :=
  ⟨2, 1, MvPolynomial.X (Fin.last 1), 1, ⊤, 0⟩

theorem y0Pauli_mem : y0Pauli.pauli.X ∈ Submodule.map xProj fullShadowHeightOneState.L := by
  show (Pi.single (0 : Fin 1) 1 : Fin 1 → ZMod 2)
      ∈ Submodule.map xProj (⊤ : Submodule (ZMod 2) (Pauli 1))
  exact Submodule.mem_map.mpr ⟨⟨Pi.single (0 : Fin 1) 1, 0⟩, Submodule.mem_top, rfl⟩

theorem yWeight_y0Pauli : yWeight y0Pauli.pauli = 1 := by
  unfold yWeight zDot
  simp only [Fin.sum_univ_one]
  show (y0Pauli.pauli.Z 0).val * (y0Pauli.pauli.X 0).val = 1
  rfl

/-- **Agreement.** `Y` conditioning a height-one state at `m = 2`: `Y`'s X-part lies in the full
shadow, so `condition` again takes the bound constructor, this time starting from `h = 1`: the
output height is `2` (`conditionBound_h`), matching the shape at height `0` (Row 1) one level up.
`Y`'s odd `Y`-weight needs precision `≥ 2`; already met at `m = 2`, so `conditionPrecision` does
not raise it — the "at any height" and precision remarks of the target hold away from `h = 0`. -/
-- row: agreement
theorem condition_y0Pauli_height_one (b : ZMod 2) :
    condition fullShadowHeightOneState y0Pauli b = conditionBound fullShadowHeightOneState y0Pauli b
      ∧ (conditionBound fullShadowHeightOneState y0Pauli b).h = 2
      ∧ conditionPrecision fullShadowHeightOneState.m y0Pauli = 2 := by
  refine ⟨condition_of_mem y0Pauli_mem b, ?_, ?_⟩
  · rw [conditionBound_h]; rfl
  · unfold conditionPrecision
    rw [yWeight_y0Pauli]
    rfl

/-! ## Row 4: `Z` on `∣0⟩` at outcome `1`, against outcome `0` -/

/-- `Z` on one qubit: sign `+`, `Z`-part `e₀` (the referee's instance
`pauliProjection_zPauli_single` at `j = 0`, but on the raw carrier constructor here). -/
noncomputable def z1Point : SignedPauli 1 := ⟨0, zPauli (Pi.single (0 : Fin 1) 1)⟩

theorem z1Point_mem : z1Point.pauli.X ∈ Submodule.map xProj botState.L := by
  have hX : z1Point.pauli.X = 0 := rfl
  rw [hX]; exact Submodule.zero_mem _

theorem branchPhase_z1Point_eval (w : Fin 1 → ZMod 2) (β b : ZMod 2) :
    DiagPhase.eval (branchPhase (N := 2) 1 (fun j : Fin 1 => (Fin.castAdd 0 j).castSucc) z1Point b)
      (Fin.snoc w β) = (b.val : ZMod (2 ^ 1)) + (w 0).val := by
  unfold branchPhase z1Point zPauli yWeight zDot
  simp only [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X,
    Fin.sum_univ_one, Fin.snoc_castSucc, Fin.castAdd_zero, Fin.cast_eq_self, Pi.single_eq_same,
    Pi.zero_apply, ZMod.val_zero, ZMod.val_one, add_zero, zero_mul, mul_zero, Nat.cast_zero]
  norm_num [iPowExp]

/-- `ampCore` of the bound constructor's exponent, at the support point `0`: `1` at the possible
outcome `b = 0`, `0` at the impossible outcome `b = 1` (D10). -/
theorem ampCore_conditionBound_z1Point (b : ZMod 2) :
    ampCore (conditionBound botState z1Point b).m (conditionBound botState z1Point b).h
        (conditionBound botState z1Point b).Q (conditionBound botState z1Point b).c
        (0 : Fin 1 → ZMod 2)
      = if b = 0 then (1 : ℂ) else 0 := by
  unfold botState conditionBound
  dsimp only
  generalize_proofs pf
  revert pf
  generalize hm : conditionPrecision 1 z1Point = m
  intro pf
  have hm1 : m = 1 := by
    rw [← hm]
    unfold conditionPrecision
    have hy : yWeight z1Point.pauli = 0 := by unfold z1Point zPauli yWeight zDot; simp
    rw [hy]; rfl
  subst hm1
  rw [ampCore_peel_last, ampCore_zero, ampCore_zero, exp_realPhase_eq_charOf,
    exp_realPhase_eq_charOf, snocFreeze_eval, snocFreeze_eval,
    show FTQCLib.Hilbert.liftTo 1 pf (0 : DiagPhase (1 + 0) 1) = 0 from rfl,
    show shiftSubst Fin.castSucc z1Point.pauli.X (MvPolynomial.X (Fin.last (1 + 0)))
        (0 : DiagPhase (1 + 0) 1) = 0 from map_zero _,
    DiagPhase.eval_add, DiagPhase.eval_add,
    show DiagPhase.eval (0 : DiagPhase (1 + 0 + 1) 1) (Fin.snoc (0 : Fin 1 → ZMod 2) 0) = 0 from
      by unfold DiagPhase.eval; simp,
    show DiagPhase.eval (0 : DiagPhase (1 + 0 + 1) 1) (Fin.snoc (0 : Fin 1 → ZMod 2) 1) = 0 from
      by unfold DiagPhase.eval; simp,
    zero_add, zero_add, DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_X, DiagPhase.eval_X,
    Fin.snoc_last, Fin.snoc_last, branchPhase_z1Point_eval, branchPhase_z1Point_eval]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := sqrt_two_sq_complex
  rcases FTQCLib.Pauli.zmod_two_eq_zero_or_one b with hb | hb <;>
    subst hb <;>
    simp only [ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      zero_add, add_zero, charOf_zero, Pi.zero_apply] <;>
    norm_num [charOf_one_one, h2] <;>
    field_simp <;>
    rw [hsq] <;>
    ring

/-- The conditioned point state's support coset contains `0` (the bound constructor keeps `L`
and `x₀`). -/
theorem mem_support_condition_zero_z1 (b : ZMod 2) :
    ∃ p ∈ (condition botState z1Point b).L,
      (0 : Fin 1 → ZMod 2) = (condition botState z1Point b).x₀ + p.X := by
  rw [condition_of_mem z1Point_mem b, conditionBound_L]
  exact ⟨0, Submodule.zero_mem _, rfl⟩

/-- The amplitude, in closed form: off the point `0` it is zero (the bound constructor keeps the
point support); at `0` it is `1` exactly at the possible outcome `b = 0`. -/
theorem amp_condition_zero_z1Point (b : ZMod 2) (w : Fin 1 → ZMod 2) :
    amp (condition botState z1Point b) w = if w = 0 ∧ b = 0 then 1 else 0 := by
  by_cases hw : w = 0
  · subst hw
    rw [amp_pos (mem_support_condition_zero_z1 b), condition_of_mem z1Point_mem b,
      ampCore_conditionBound_z1Point]
    simp
  · rw [amp_neg (fun h => hw (by
        rw [condition_of_mem z1Point_mem b, conditionBound_L] at h
        obtain ⟨p, hp, hpw⟩ := h
        have hzL : botState.L = (⊥ : Submodule (ZMod 2) (Pauli 1)) := rfl
        rw [hzL, Submodule.mem_bot] at hp
        subst hp
        simpa using hpw))]
    simp [hw]

/-- **Discriminating.** Conditioning `∣0⟩` on `Z` at the impossible outcome `1` has amplitude
identically zero (D10); at outcome `0` its amplitude is nonzero (`1`, at the support point `0`).
The two outcomes are discriminated by evaluation at that point. -/
-- row: discriminating
theorem amp_condition_zero_z1Point_outcome_one_zero :
    amp (condition botState z1Point 1) = 0
      ∧ amp (condition botState z1Point 0) ≠ amp (condition botState z1Point 1) := by
  constructor
  · funext w
    rw [amp_condition_zero_z1Point]
    simp
  · intro h
    have h0 := congrFun h (0 : Fin 1 → ZMod 2)
    rw [amp_condition_zero_z1Point, amp_condition_zero_z1Point] at h0
    simp at h0

/-! ## Inhabitation: `amp_condition`'s hypotheses, together on the Bell state -/

/-- **Inhabitation.** `amp_condition`'s hypotheses — a carrier state with a co-isotropic Lagrangian,
a Pauli with its sign, and an outcome — hold together on `bellState` (co-isotropic by
`bellL_coisotropic`, already used by Row 1 above), `z0Bell`, and outcome `0`: exhibiting the
instance exhibits all three at once. -/
-- row: inhabitation
example := amp_condition bellState bellL_coisotropic z0Bell (0 : ZMod 2)

end FTQCLib.Frame.Walkthrough

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.le_conditionPrecision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.le_conditionPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.one_le_conditionPrecision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.one_le_conditionPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.two_le_conditionPrecision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.two_le_conditionPrecision

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_iPowExp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.charOf_iPowExp

/-- info: 'FTQCLib.Frame.Walkthrough.conditionBound_h' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionBound_h

/-- info: 'FTQCLib.Frame.Walkthrough.conditionBound_c' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionBound_c

/-- info: 'FTQCLib.Frame.Walkthrough.conditionBound_L' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionBound_L

/-- info: 'FTQCLib.Frame.Walkthrough.conditionRaise_h' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionRaise_h

/-- info: 'FTQCLib.Frame.Walkthrough.conditionRaise_c' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionRaise_c

/-- info: 'FTQCLib.Frame.Walkthrough.condition_of_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_of_mem

/-- info: 'FTQCLib.Frame.Walkthrough.condition_cover' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_cover

/-- info: 'FTQCLib.Frame.Walkthrough.amp_condition' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_condition

/-- info: 'FTQCLib.Frame.Walkthrough.pauliProjection_zPauli_single' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliProjection_zPauli_single

/-- info: 'FTQCLib.Frame.Walkthrough.amp_conditionOutcome' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_conditionOutcome

/-- info: 'FTQCLib.Frame.Walkthrough.conditionOutcome_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionOutcome_eval

/-- info: 'FTQCLib.Frame.Walkthrough.amp_permuteFreeBits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_permuteFreeBits

/-- info: 'FTQCLib.Frame.Walkthrough.amp_dropFreeBit' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_dropFreeBit

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_dropFreeBit' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_dropFreeBit

/-! Structure-generated declarations of `@[ext] structure SignedPauli`, public members of the
topic module, so the sweep covers them too. -/

/-- info: 'FTQCLib.Frame.Walkthrough.SignedPauli.ext' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.SignedPauli.ext

/-- info: 'FTQCLib.Frame.Walkthrough.SignedPauli.ext_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.SignedPauli.ext_iff

/-- info: 'FTQCLib.Frame.Walkthrough.SignedPauli.mk.inj' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.SignedPauli.mk.inj

/-- info: 'FTQCLib.Frame.Walkthrough.SignedPauli.mk.injEq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.SignedPauli.mk.injEq

/-- info: 'FTQCLib.Frame.Walkthrough.SignedPauli.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.SignedPauli.mk.sizeOf_spec

/-! ## Declared mutants -/

-- mutant: boundScale|FTQCLib/Carrier/Conditioning.lean|c := S.c / (Real.sqrt 2 : ℂ)|c := S.c / 2
-- mutant: outcomeSign_mul_self_conclusion | FTQCLib/Carrier/Conditioning.lean
--   | outcomeSign P b * outcomeSign P b = 1
--   | outcomeSign P b * outcomeSign P b = 0

/-! ## Axiom sweep: made public or moved here (docs/STEPS.md, entry 2026-09-30h) -/

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_conditionBound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ampCore_conditionBound

/-- info: 'FTQCLib.Frame.Walkthrough.ampCore_conditionRaise' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.ampCore_conditionRaise

/-- info: 'FTQCLib.Frame.Walkthrough.amp_appendFreeBit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_appendFreeBit

/-- info: 'FTQCLib.Frame.Walkthrough.amp_conditionBound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_conditionBound

/-- info: 'FTQCLib.Frame.Walkthrough.amp_conditionRaise' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_conditionRaise

/-- info: 'FTQCLib.Frame.Walkthrough.append_add_mul_append' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.append_add_mul_append

/-- info: 'FTQCLib.Frame.Walkthrough.charOf_branchPhase_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.charOf_branchPhase_eval

/-- info: 'FTQCLib.Frame.Walkthrough.dropPauli_liftPauli' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.dropPauli_liftPauli

/-- info: 'FTQCLib.Frame.Walkthrough.exists_readsBit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.exists_readsBit

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_dropPauli' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isStabilizer_dropPauli

/-- info: 'FTQCLib.Frame.Walkthrough.map_xProj_conditionRaise_L' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.map_xProj_conditionRaise_L

/-- info: 'FTQCLib.Frame.Walkthrough.mem_support_add_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.mem_support_add_iff

/-- info: 'FTQCLib.Frame.Walkthrough.mem_support_appendFreeBit_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.mem_support_appendFreeBit_iff

/-- info: 'FTQCLib.Frame.Walkthrough.neg_one_pow_val_add_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.neg_one_pow_val_add_one

/-- info: 'FTQCLib.Frame.Walkthrough.normSq_act' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.normSq_act

/-- info: 'FTQCLib.Frame.Walkthrough.omega_dropPauli_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.omega_dropPauli_left

/-- info: 'FTQCLib.Frame.Walkthrough.omega_succ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.omega_succ

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_appendFreeBit_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_appendFreeBit_le

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_dropPauli_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_dropPauli_le

/-- info: 'FTQCLib.Frame.Walkthrough.outcomeSign_mul_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.outcomeSign_mul_self

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_pauliProjection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliAct_pauliProjection

/-- info: 'FTQCLib.Frame.Walkthrough.pauliAct_self_pauliProjection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliAct_self_pauliProjection

/-- info: 'FTQCLib.Frame.Walkthrough.pauliInit_pauliSnoc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliInit_pauliSnoc

/-- info: 'FTQCLib.Frame.Walkthrough.pauliProjection_appendZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliProjection_appendZ

/-- info: 'FTQCLib.Frame.Walkthrough.pauliProjection_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliProjection_apply

/-- info: 'FTQCLib.Frame.Walkthrough.pauliProjection_mul_left' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliProjection_mul_left

/-- info: 'FTQCLib.Frame.Walkthrough.shiftSubst_eval' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.shiftSubst_eval

/-- info: 'FTQCLib.Frame.Walkthrough.stabilizedBy_pauliCondition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.stabilizedBy_pauliCondition

/-- info: 'FTQCLib.Frame.Walkthrough.sum_normSq_act' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_normSq_act

/-- info: 'FTQCLib.Frame.Walkthrough.sum_normSq_pauliAct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.sum_normSq_pauliAct

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_appendZ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.yWeight_appendZ

/-- info: 'FTQCLib.Frame.Walkthrough.conditionOutcome_m' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionOutcome_m

/-- info: 'FTQCLib.Frame.Walkthrough.conditionPrecision_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.conditionPrecision_eq

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_appendFreeBit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isStabilizer_appendFreeBit

/-- info: 'FTQCLib.Frame.Walkthrough.isStabilizer_raise' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isStabilizer_raise

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_raise_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_raise_le

/-- info: 'FTQCLib.Frame.Walkthrough.condition_L' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.condition_L

/-- info: 'FTQCLib.Frame.Walkthrough.pauliProjection_zero_add_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.pauliProjection_zero_add_one

/-- info: 'FTQCLib.Frame.Walkthrough.amp_conditionOutcome_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_conditionOutcome_ne_zero

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_conditionOutcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_conditionOutcome

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_appendFreeBit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_appendFreeBit

/-- info: 'FTQCLib.Frame.Walkthrough.isCarrier_permuteFreeBits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.isCarrier_permuteFreeBits

/-- info: 'FTQCLib.Frame.Walkthrough.zDot_paulix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.zDot_paulix

/-- info: 'FTQCLib.Frame.Walkthrough.yWeight_paulix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.yWeight_paulix


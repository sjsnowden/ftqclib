/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardPhase
import FTQCLib.Hilbert.GateLifts
import FTQCLib.Examples.HadamardCharSumFrame

/-! # The character-sum Hadamard is equivariant (the Hilbert bridge)

This file shows that the frame-native character-sum Hadamard `applyHFiner` (`HadamardPhase.lean`,
which imports no `FTQCLib.Hilbert`) computes the Walsh transform `hadamardGate` on the Hilbert
side — stated as an **equivariance** `F(applyHFiner k S) = hadamardGate k (F S)`, so it is the
`h → h+1` step of the above-floor correspondence and composition chains for free. Frame-purity is
preserved: this bridge imports `HadamardPhase`, not the reverse. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert Complex


/-! ## The equivariance: the character-sum Hadamard computes the Walsh transform -/

/-- **Amplitude form.** The character-sum Hadamard `applyHFiner` on the amplitude equals the Hilbert
Walsh transform `hadamardGate` of the input amplitude, pointwise. This is `F(applyHFiner k S) = hadamardGate k
(F S)` at the level of `ampCore`. -/
theorem ampCore_hadamard_equiv {n h m : ℕ} (hm : 1 ≤ m) (k : Fin n) (Q : DiagPhase (n + h) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m (h + 1) (hSumExp k Q) c w
      = hadamardGate k (fun w' => ampCore m h Q c w') w := by
  rw [hadamardGate_apply, ampCore_applyHFiner,
    show (1 / (Real.sqrt 2 : ℂ)) = invSqrt2 from by simp [invSqrt2, one_div]]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hBranch_eval hm, Nat.mul_comm b.val (w k).val]

/-- **Function form.** The equivariance as an identity of `QubitSpace` vectors:
`applyHFiner k` on the amplitude is `hadamardGate k` of it. The `h → h+1` step of the above-floor
correspondence; composition chains for free because this is an identity. -/
theorem applyHFiner_hadamard {n : ℕ} (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m) :
    (fun w => ampCore (applyHFiner k S).m (applyHFiner k S).h (applyHFiner k S).Q (applyHFiner k S).c w)
      = hadamardGate k (fun w => ampCore S.m S.h S.Q S.c w) := by
  funext w
  exact ampCore_hadamard_equiv hm k S.Q S.c w

/-! ## The full character-sum correspondence — `F` intertwines every word of fine Hadamards

The equivariance `applyHFiner_hadamard` is the `h → h+1` step. Folded over a *word* of fine
Hadamards it gives the whole above-floor correspondence for the character-sum carrier: the
interpretation map `ampVec` (the amplitude vector `F`) intertwines any list of `applyHFiner`s with
the matching list of Walsh transforms. Because the step is an **unconditional identity**, the
induction needs no separate "respects composition" lemma — this is the graded-monoid-morphism
statement: `F` sends the frame's `h`-graded Hadamard monoid into the Hilbert unitary group one
grade-raising generator at a time. The induction's *base* is the starting state at whatever `h` it
carries; tying that base amplitude to the floor↔Hilbert stabilizer state
(`stabilizerState_isLevel2Kernel_unconditional`) is the separate absolute-form step
(`CharSumCorrespondence.lean`). -/

/-- The interpretation map `F` on the character-sum carrier: the amplitude vector `w ↦ ampCore …`. -/
noncomputable def ampVec (S : KernelSumState n) : QubitSpace n :=
  fun w => ampCore S.m S.h S.Q S.c w

/-- The equivariance restated on `ampVec`: `F(applyHFiner k S) = H_k (F S)` (needs `1 ≤ S.m`). -/
theorem ampVec_applyHFiner {n : ℕ} (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m) :
    ampVec (applyHFiner k S) = hadamardGate k (ampVec S) := by
  unfold ampVec
  exact applyHFiner_hadamard k S hm

/-- Apply a word of fine Hadamards to a state — head outermost (last-applied). -/
noncomputable def applyHFinerWord (ks : List (Fin n)) (S : KernelSumState n) : KernelSumState n :=
  ks.foldr applyHFiner S

/-- The matching word of Walsh transforms — head outermost. -/
noncomputable def hadamardWord (ks : List (Fin n)) (ψ : QubitSpace n) : QubitSpace n :=
  ks.foldr (fun k ψ => hadamardGate k ψ) ψ

@[simp] theorem applyHFinerWord_nil (S : KernelSumState n) : applyHFinerWord [] S = S := rfl
@[simp] theorem applyHFinerWord_cons (k : Fin n) (ks : List (Fin n)) (S : KernelSumState n) :
    applyHFinerWord (k :: ks) S = applyHFiner k (applyHFinerWord ks S) := rfl
@[simp] theorem hadamardWord_nil (ψ : QubitSpace n) : hadamardWord [] ψ = ψ := rfl
@[simp] theorem hadamardWord_cons (k : Fin n) (ks : List (Fin n)) (ψ : QubitSpace n) :
    hadamardWord (k :: ks) ψ = hadamardGate k (hadamardWord ks ψ) := rfl

/-- Every fine Hadamard preserves the precision `m`, so a whole word does — this threads the
`1 ≤ m` hypothesis of `ampVec_applyHFiner` through the induction. -/
theorem applyHFinerWord_m (ks : List (Fin n)) (S : KernelSumState n) :
    (applyHFinerWord ks S).m = S.m := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [applyHFinerWord_cons]; exact ih

/-- **The full character-sum correspondence.** `F = ampVec` intertwines an arbitrary word of fine
Hadamards with the matching word of Walsh transforms:
`F(applyHFinerWord ks S) = hadamardWord ks (F S)`, for any starting state with `1 ≤ S.m`. Base =
the empty word (identity); step = `ampVec_applyHFiner`; the `m`-invariance (`applyHFinerWord_m`)
feeds its hypothesis at each stage. No separate composition lemma is needed: the step is an
identity, so the monoid morphism is free. -/
theorem ampVec_hadamardWord (ks : List (Fin n)) (S : KernelSumState n) (hm : 1 ≤ S.m) :
    ampVec (applyHFinerWord ks S) = hadamardWord ks (ampVec S) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      have hmid : 1 ≤ (applyHFinerWord ks S).m := by rw [applyHFinerWord_m]; exact hm
      rw [applyHFinerWord_cons, hadamardWord_cons,
        ampVec_applyHFiner k (applyHFinerWord ks S) hmid, ih]

end FTQCLib.Frame.Walkthrough

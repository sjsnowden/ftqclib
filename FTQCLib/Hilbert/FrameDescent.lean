/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKForward
import FTQCLib.Hilbert.CGKExactness
import FTQCLib.Hierarchy.FrameMoves

/-! # Kernel frame — the descent characterization (forward direction)

The descent characterization is the frame's form of "level = functional degree" (Clark–Schauz
/ Aichinger–Moosbauer): an exponent has frame level `≤ k` iff all of its
`(k+1)`-fold discrete differences vanish.

This file proves the **forward direction** — `level ≤ k ⟹ (k+1)-fold differences
vanish` — over arbitrary difference directions (the iterated `shiftBy` reaches the
zero polynomial). The mechanism is the verified strict effective-level drop
`shiftByStrictDrop_general`: each nonzero difference drops the level by at least
one, and a constant (level `0`) is killed by one more difference. The
function-side reading is `frameDiff` (`shiftBy_eval_frameDiff`).

The **reverse direction** — `(k+1)-fold differences vanish ⟹ level ≤ k` — is the
Aichinger–Moosbauer functional-degree *lower bound*; it requires the 2-adic
depth accounting (repeated same-direction differences and the `−2Δ` identity,
`frameDiff_self_eq_neg_two_zsmul`) beyond the single-coordinate Möbius data, and
is in `FrameDescentReverse.lean`.
-/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

/-- The **iterated discrete difference** of an exponent over a list of directions
`ds`, applied left-to-right: `iterDiff [s₀,…,s_r] P = shiftBy s_r (… (shiftBy s₀ P))`.
The polynomial face of the frame's iterated `frameDiff`. -/
noncomputable def iterDiff {m : ℕ} (ds : List (Fin n → ZMod 2)) (P : DiagPhase n m) :
    DiagPhase n m :=
  ds.foldl (fun Q d => DiagPhase.shiftBy d Q) P

@[simp] lemma iterDiff_nil {m : ℕ} (P : DiagPhase n m) : iterDiff [] P = P := rfl

lemma iterDiff_cons {m : ℕ} (d : Fin n → ZMod 2) (ds : List (Fin n → ZMod 2))
    (P : DiagPhase n m) :
    iterDiff (d :: ds) P = iterDiff ds (DiagPhase.shiftBy d P) := rfl

/-- The zero exponent is multilinear (empty support). -/
lemma isMultilinear_zero {m : ℕ} : DiagPhase.IsMultilinear (0 : DiagPhase n m) := by
  intro d hd k
  rw [MvPolynomial.support_zero] at hd
  exact absurd hd (Finset.notMem_empty d)

/-- **Constant case.** A multilinear exponent of effective level `0` is a
constant, so any single difference of it is the zero exponent. (Used both for the
genuine constant base and, with `P = 0`, to propagate the zero exponent.) -/
lemma shiftBy_eq_zero_of_effectiveLevel_zero {m : ℕ} {P : DiagPhase n m}
    (s : Fin n → ZMod 2) (h_mul : DiagPhase.IsMultilinear P)
    (h0 : DiagPhase.effectiveLevel P = 0) :
    DiagPhase.shiftBy s P = 0 := by
  have htd : P.totalDegree = 0 :=
    Nat.le_zero.mp (h0 ▸ DiagPhase.totalDegree_le_effectiveLevel P)
  have hP_C : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
  have heval_const : ∀ w, P.eval w = P.coeff 0 := by
    intro w
    conv_lhs => rw [hP_C]
    simp [DiagPhase.eval, MvPolynomial.eval_C]
  apply multilinear_eval_injective (DiagPhase.shiftBy_isMultilinear s h_mul) isMultilinear_zero
  intro v
  rw [DiagPhase.shiftBy_eval_eq, heval_const (v + s), heval_const v, sub_self]
  simp [DiagPhase.eval]

/-- Iterating differences of the zero exponent stays zero. -/
lemma iterDiff_zero {m : ℕ} (ds : List (Fin n → ZMod 2)) :
    iterDiff ds (0 : DiagPhase n m) = 0 := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    rw [iterDiff_cons,
      shiftBy_eq_zero_of_effectiveLevel_zero d isMultilinear_zero DiagPhase.effectiveLevel_zero]
    exact ih

/-- **Descent, forward direction.** A multilinear exponent of effective level
`< ds.length` is annihilated by the iterated difference over `ds`: every
`(k+1)`-fold difference of a level-`≤ k` exponent is the zero exponent. -/
theorem descent_forward {m : ℕ} {ds : List (Fin n → ZMod 2)} :
    ∀ {P : DiagPhase n m}, DiagPhase.IsMultilinear P →
      DiagPhase.effectiveLevel P < ds.length → iterDiff ds P = 0 := by
  induction ds with
  | nil => intro P _ h; exact absurd h (Nat.not_lt_zero _)
  | cons d rest ih =>
    intro P h_mul h
    rw [iterDiff_cons]
    by_cases heff : DiagPhase.effectiveLevel P = 0
    · rw [shiftBy_eq_zero_of_effectiveLevel_zero d h_mul heff, iterDiff_zero]
    · have hpos : 0 < DiagPhase.effectiveLevel P := Nat.pos_of_ne_zero heff
      by_cases hd : d = 0
      · rw [hd, DiagPhase.shiftBy_zero, iterDiff_zero]
      · have hdrop := shiftByStrictDrop_general n m P h_mul hpos d hd
        refine ih (DiagPhase.shiftBy_isMultilinear d h_mul) ?_
        simp only [List.length_cons] at h
        omega

/-- **Frame-vocabulary bridge.** The reading of a polynomial difference is the
function difference `frameDiff`: `(shiftBy s P).eval = Δ_s (P.eval)`. So the
iterated `iterDiff` on exponents reads as the iterated `frameDiff` on the value
function — the descent's function face. -/
lemma shiftBy_eval_frameDiff {m : ℕ} (s : Fin n → ZMod 2) (P : DiagPhase n m) :
    (DiagPhase.shiftBy s P).eval = frameDiff s (P.eval) := by
  funext v
  rw [DiagPhase.shiftBy_eval_eq]
  rfl

end FTQCLib.Frame

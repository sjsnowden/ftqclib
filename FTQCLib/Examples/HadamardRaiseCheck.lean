/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardRaise

/-!
# Check: the correlated-bit Hadamard

Kernel rows recompute the `val`-level arithmetic the eval bridges rest on, exhaustively over
`𝔽₂` at the witness precision `m = 2`, and the branch constant of the discriminating witness.
The **control** is aimed at the main pitfall: at `m = 2` the ordinary-sum form
`raiseForm` and the multilinear form `xorForm` genuinely differ (`2 ≠ 0` at `u = (1,1)`,
`z = (1,1)`) — substituting the ordinary form would be wrong, and
`two_pow_mul_xorForm` is exactly the statement that the `2^{m−1}` sign slot cannot see the
difference. The agreement row is `raiseSubst_zero_eval`: the affine freeze meets the
independently proved `freezeAt_eval` at `u = 0`.

`DiagPhase.eval` is noncomputable (it walks the `AddMonoidAlgebra` structure), so no row can
`decide` an evaluation directly; rows about evaluations go through the proved bridges and then
`decide` the resulting closed `ZMod` arithmetic. The absence of direct kernel rows on `eval` is
forced, not skipped. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib.Hierarchy

/-! ## Kernel rows: the `val`-level arithmetic, exhaustive at the witness precision -/

/-- `val_add_val` recomputed by the kernel at `m = 2`, all four points. -/
example : ∀ a b : ZMod 2,
    (((a + b).val : ZMod (2 ^ 2)))
      = (a.val : ZMod (2 ^ 2)) + (b.val : ZMod (2 ^ 2))
        - 2 * ((a.val : ZMod (2 ^ 2)) * (b.val : ZMod (2 ^ 2))) := by decide

/-- `val_mul_val` recomputed by the kernel at `m = 2`, all four points. -/
example : ∀ a b : ZMod 2,
    (((a * b).val : ZMod (2 ^ 2))) = (a.val : ZMod (2 ^ 2)) * (b.val : ZMod (2 ^ 2)) := by
  decide

/-- The dyadic key at the witness precision: `2^{2−1} · 2 = 0` in `ZMod 4`. -/
example : (2 : ZMod (2 ^ 2)) ^ (2 - 1) * 2 = 0 := by decide

/-- The discriminating witness's branch constant, recomputed by the kernel:
`raiseConst = x₀ 0 + u ⬝ x₀ = 1` for `u = (0,1,1)`, `x₀ = (1,0,0)`. -/
example : raiseConst 0 (![0, 1, 1] : Fin 3 → ZMod 2) (![1, 0, 0]) = 1 := by decide

/-! ## The control: the two forms genuinely differ off the sign slot

A check that could not tell `raiseForm` from `xorForm` would also pass the incorrect definition
that substitutes `raiseForm`. These two rows pin the separation at the smallest carrier that shows
it. -/

/-- **Control, ordinary side**: at `m = 2`, `u = (1,1)`, `b = 0`, `z = (1,1)` the ordinary sum
evaluates to `2` — off the binary range, which is what made substituting it wrong. -/
example : DiagPhase.eval (raiseForm (h := 0) (m := 2) (![1, 1] : Fin 2 → ZMod 2) 0)
    (![1, 1] : Fin (2 + 0) → ZMod 2) = 2 := by
  rw [raiseForm_eval]
  decide

/-- **Control, XOR side**: the multilinear form evaluates to `0 = 1 ⊕ 1` at the same point. -/
example : DiagPhase.eval (xorForm (h := 0) (m := 2) (![1, 1] : Fin 2 → ZMod 2) 0)
    (![1, 1] : Fin (2 + 0) → ZMod 2) = 0 := by
  rw [xorForm_eval]
  decide

/-! ## Discrimination, recorded

* `hRaise_sParity_exponent` (guarded below) is the aimed row: under the ordinary-sum
  substitution its statement is false (`3 ≠ 1` at `z = (0,1,1)`); a definition that skips the
  freeze or drops the `u ⬝ x₀` pairing fails it elsewhere. No `m = 1` row can discriminate any
  of this — there `2 = 0`, so the incorrect substitution passes the Bell example.
* `hRaise_bell_exponent` is the coverage row (the case outside the three other Hadamard
  constructors); it does **not** exercise the freeze (`Q = 0`) or the offset (`x₀ = 0`), and is
  kept as the row that would still pass under those changes to the definition. -/

end FTQCLib.Frame.Walkthrough

/-! ## Axiom sweep (build-failing) — every declaration of `HadamardRaise.lean` -/

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.dotF2

/-- info: 'FTQCLib.Frame.Walkthrough.raiseConst' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.raiseConst

/-- info: 'FTQCLib.Frame.Walkthrough.polyXor' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.polyXor

/-- info: 'FTQCLib.Frame.Walkthrough.polyXorCommutative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.polyXorCommutative

/-- info: 'FTQCLib.Frame.Walkthrough.polyXorAssociative' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.polyXorAssociative

/-- info: 'FTQCLib.Frame.Walkthrough.polyXor_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.polyXor_eval

/-- info: 'FTQCLib.Frame.Walkthrough.val_add_val' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.val_add_val

/-- info: 'FTQCLib.Frame.Walkthrough.val_mul_val' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.val_mul_val

/-- info: 'FTQCLib.Frame.Walkthrough.xorForm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.xorForm

/-- info: 'FTQCLib.Frame.Walkthrough.fold_polyXor_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.fold_polyXor_eval

/-- info: 'FTQCLib.Frame.Walkthrough.xorForm_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.xorForm_eval

/-- info: 'FTQCLib.Frame.Walkthrough.raiseForm' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.raiseForm

/-- info: 'FTQCLib.Frame.Walkthrough.raiseForm_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.raiseForm_eval

/-- info: 'FTQCLib.Hierarchy.two_pow_pred_mul_two' depends on axioms: [propext,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Hierarchy.two_pow_pred_mul_two

/-- info: 'FTQCLib.Frame.Walkthrough.two_pow_mul_xorForm' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.two_pow_mul_xorForm

/-- info: 'FTQCLib.Frame.Walkthrough.two_pow_mul_raiseForm_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.two_pow_mul_raiseForm_eval

/-- info: 'FTQCLib.Frame.Walkthrough.raiseSubst' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.raiseSubst

/-- info: 'FTQCLib.Frame.Walkthrough.raiseSubst_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.raiseSubst_eval

/-- info: 'FTQCLib.Frame.Walkthrough.raiseSubst_zero_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.raiseSubst_zero_eval

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_m' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_m

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_h' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_h

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_L

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_x₀' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_x₀

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_c' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_c

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_eval

/-- info: 'FTQCLib.Frame.Walkthrough.bellIn' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellIn

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_bell_exponent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_bell_exponent

/-- info: 'FTQCLib.Frame.Walkthrough.sParityIn' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.sParityIn

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_sParity_exponent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_sParity_exponent

/-- info: 'FTQCLib.Frame.Walkthrough.update_sub_update' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.update_sub_update

/-- info: 'FTQCLib.Frame.Walkthrough.branch_unique' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.branch_unique

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.FuncDeriv

/-!
# The last variable of a phase exponent

An exponent `Q : DiagPhase (N + 1) m` has a last variable, `Fin.last N`. Two operations on it carry
the bound-register calculus of the frame's carrier: *freezing it away* — substituting a bit for the
last variable and forgetting it, so that `snocFreeze b Q` is an exponent on `N` variables — and *the
difference along it*, `lastDiff Q := snocFreeze 1 Q − snocFreeze 0 Q`, which is the functional
derivative of `FuncDeriv.lean` read at the point whose last coordinate is `0`
(`lastDiff_eval_eq_funcDerivEval`). Freezing composes with `Fin.snoc` on the evaluation side
(`snocFreeze_eval`), which is what lets a character sum over a bound register peel its last bit.

The operations are stated for any `N`; the carrier uses them at `N = n + h` with the last variable
the last bound bit.

## Main definitions

* `snocFreeze b Q` — the last variable frozen to the bit `b` and dropped.
* `lastDiff Q` — the difference of `Q` along its last variable, as an exponent on the rest.

## Main results

* `snocFreeze_eval`, `lastDiff_eval` — evaluation through `Fin.snoc`.
* `lastDiff_eval_eq_funcDerivEval` — the difference is the functional derivative at the zero slice.
* `snocFreeze_add`, `snocFreeze_C`, `lastDiff_add`, `lastDiff_C` — additivity; a constant has no
  difference.

## Implementation notes

`snocFreeze` is `MvPolynomial.bind₁` along `Fin.snoc (X ·) (C b)`, an algebra map, so the additivity
lemmas are `map_add`. `freezeAt` (`FTQCLib/Hierarchy/KernelState.lean`) freezes a variable *in place*
and keeps the arity; the frame needs the arity to drop, hence a second operation.
-/

namespace FTQCLib.Hierarchy.DiagPhase

variable {N m : ℕ}

/-! ## Freezing the last variable away -/

/-- The last variable frozen to the bit `b` and dropped: substitute `C b` for `X (Fin.last N)` and
`X j` for `X (Fin.castSucc j)`. -/
noncomputable def snocFreeze (b : ZMod 2) (Q : DiagPhase (N + 1) m) : DiagPhase N m :=
  MvPolynomial.bind₁
    (Fin.snoc (α := fun _ : Fin (N + 1) => DiagPhase N m)
      (fun j : Fin N => (MvPolynomial.X j : DiagPhase N m))
      (MvPolynomial.C ((b.val : ZMod (2 ^ m))))) Q

/-- Freezing evaluates through `Fin.snoc`. -/
theorem snocFreeze_eval (b : ZMod 2) (Q : DiagPhase (N + 1) m) (z : Fin N → ZMod 2) :
    (snocFreeze b Q).eval z = Q.eval (Fin.snoc z b) := by
  unfold snocFreeze DiagPhase.eval
  have h := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
    (DiagPhase.liftBinary z)
    (Fin.snoc (α := fun _ : Fin (N + 1) => DiagPhase N m)
      (fun j : Fin N => (MvPolynomial.X j : DiagPhase N m))
      (MvPolynomial.C ((b.val : ZMod (2 ^ m))))) Q
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  have hfun : (fun i : Fin (N + 1) =>
      (MvPolynomial.eval (DiagPhase.liftBinary z))
        (Fin.snoc (α := fun _ : Fin (N + 1) => DiagPhase N m)
          (fun j : Fin N => (MvPolynomial.X j : DiagPhase N m))
          (MvPolynomial.C ((b.val : ZMod (2 ^ m)))) i))
      = DiagPhase.liftBinary (Fin.snoc z b) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp [DiagPhase.liftBinary]
    · intro l
      simp [DiagPhase.liftBinary]
  rw [hfun]

/-- Freezing is additive. -/
theorem snocFreeze_add (b : ZMod 2) (P Q : DiagPhase (N + 1) m) :
    snocFreeze b (P + Q) = snocFreeze b P + snocFreeze b Q := by
  unfold snocFreeze
  exact map_add _ _ _

/-- Freezing fixes constants. -/
theorem snocFreeze_C (b : ZMod 2) (c : ZMod (2 ^ m)) :
    snocFreeze b (MvPolynomial.C c : DiagPhase (N + 1) m) = MvPolynomial.C c := by
  unfold snocFreeze
  exact MvPolynomial.bind₁_C_right _ _

/-! ## The difference along the last variable -/

/-- The difference of `Q` along its last variable, as an exponent on the remaining variables. -/
noncomputable def lastDiff (Q : DiagPhase (N + 1) m) : DiagPhase N m :=
  snocFreeze 1 Q - snocFreeze 0 Q

/-- The difference evaluates as the difference of the two frozen values. -/
theorem lastDiff_eval (Q : DiagPhase (N + 1) m) (z : Fin N → ZMod 2) :
    (lastDiff Q).eval z = Q.eval (Fin.snoc z 1) - Q.eval (Fin.snoc z 0) := by
  unfold lastDiff DiagPhase.eval
  rw [map_sub]
  rw [show MvPolynomial.eval (DiagPhase.liftBinary z) (snocFreeze 1 Q)
      = DiagPhase.eval (snocFreeze 1 Q) z from rfl,
    show MvPolynomial.eval (DiagPhase.liftBinary z) (snocFreeze 0 Q)
      = DiagPhase.eval (snocFreeze 0 Q) z from rfl,
    snocFreeze_eval, snocFreeze_eval]
  rfl

/-- The difference is additive. -/
theorem lastDiff_add (P Q : DiagPhase (N + 1) m) : lastDiff (P + Q) = lastDiff P + lastDiff Q := by
  unfold lastDiff
  rw [snocFreeze_add, snocFreeze_add]
  ring

/-- A constant has no difference. -/
theorem lastDiff_C (c : ZMod (2 ^ m)) : lastDiff (MvPolynomial.C c : DiagPhase (N + 1) m) = 0 := by
  unfold lastDiff
  rw [snocFreeze_C, snocFreeze_C, sub_self]

/-- The zero slice shifted at the last coordinate is the one slice. -/
theorem snoc_zero_add_single_last (z : Fin N → ZMod 2) :
    (Fin.snoc z (0 : ZMod 2) : Fin (N + 1) → ZMod 2) + Pi.single (Fin.last N) (1 : ZMod 2)
      = Fin.snoc z 1 := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · rw [Pi.add_apply, Fin.snoc_last, Fin.snoc_last, Pi.single_eq_same, zero_add]
  · intro i
    rw [Pi.add_apply, Fin.snoc_castSucc, Fin.snoc_castSucc,
      Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, add_zero]

/-- **The bridge to the difference calculus.** The difference along the last variable is the
functional derivative of `FuncDeriv.lean` at the last variable, read on the zero slice. -/
theorem lastDiff_eval_eq_funcDerivEval (Q : DiagPhase (N + 1) m) (z : Fin N → ZMod 2) :
    (lastDiff Q).eval z = funcDerivEval (Fin.last N) Q (Fin.snoc z 0) := by
  rw [lastDiff_eval, funcDerivEval_apply, snoc_zero_add_single_last]

end FTQCLib.Hierarchy.DiagPhase

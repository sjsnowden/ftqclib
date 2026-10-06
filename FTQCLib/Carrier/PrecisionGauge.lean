/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierState
import FTQCLib.Hierarchy.PrecisionLift

/-!
# The precision lift as a gauge rewrite (R7)

A carrier state `⟨m, h, Q, c, L, x₀⟩` reads its exponent `Q` at precision `m`: each term contributes
the phase `2π · Q(w ++ y) / 2^m`. The precision lift `FTQCLib.Hilbert.liftTo k hmk Q`
(`FTQCLib/Hierarchy/PrecisionLift.lean`) multiplies every coefficient by `2^(k−m)` and reads the
result at precision `k ≥ m`. The real phase is unchanged (`liftTo_realPhase`), so the lifted carrier
state has the same denotation: the precision is gauge. This is the rewrite R7, named as not treated
in `FTQCLib/Carrier/CarrierAmplitude.lean`.

The need is downstream: T needs precision at least three, and a carrier state leaving Clifford gates
may be at precision two. `liftPrecision` is R7 on a whole carrier state; it keeps the amplitude
(`amp_liftPrecision`) and so the carrier property (`isCarrier_liftPrecision`), which is what the
controlled-H word of `ControlledHadamard.lean` runs on.

Everything here is frame-pure: `DiagPhase`, `Pauli`, `Submodule`, `ℂ`. No `FTQCLib.Hilbert` module
is imported; `liftTo` keeps its full name `FTQCLib.Hilbert.liftTo` from before its move. This module
imports `CarrierState.lean` for `IsCarrier` and, through it, `DyadicCharacter.lean` for `charOf`; it
is the lowest module that sees both the character and the lift (`charOf_eval_liftTo`).

## Main definitions

* `liftPrecision` — R7 on a carrier state: its exponent read at a higher precision.

## Main results

* `charOf_eval_liftTo` — the character of a lifted exponent's value is the character of its value.
* `ampCore_liftTo` — the on-support amplitude is unchanged by the lift.
* `amp_liftTo` — **R7.** Lifting the exponent from precision `m` to `k ≥ m` leaves `amp` fixed.
* `stateEq_liftTo` — the same fact as equality of denotation (`StateEq`).
* `amp_liftPrecision`, `isCarrier_liftPrecision` — R7 on a carrier state keeps its amplitude and
  its carrier property.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The character of a lifted exponent -/

/-- The character of a lifted exponent's value at precision `k` is the character of the exponent's
value at precision `m`: the lift scales the value by `2^(k−m)` and the character's denominator by
the same factor (`FTQCLib.Hilbert.liftTo_realPhase`). -/
theorem charOf_eval_liftTo {N m : ℕ} (k : ℕ) (hmk : m ≤ k) (P : DiagPhase N m)
    (v : Fin N → ZMod 2) :
    charOf k ((FTQCLib.Hilbert.liftTo k hmk P).eval v) = charOf m (P.eval v) := by
  rw [← exp_realPhase_eq_charOf, ← exp_realPhase_eq_charOf, FTQCLib.Hilbert.liftTo_realPhase]

/-! ## The on-support amplitude -/

/-- Lifting the exponent from precision `m` to `k ≥ m` leaves the on-support amplitude unchanged. -/
theorem ampCore_liftTo {m h : ℕ} (k : ℕ) (hmk : m ≤ k) (Q : DiagPhase (n + h) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore k h (FTQCLib.Hilbert.liftTo k hmk Q) c w = ampCore m h Q c w := by
  unfold ampCore
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [congrFun (FTQCLib.Hilbert.liftTo_realPhase k hmk Q) (Fin.append w y)]

/-! ## R7 — the precision lift -/

/-- **R7.** Lifting a carrier state's exponent from precision `m` to `k ≥ m` leaves its amplitude
unchanged: the precision is gauge. -/
theorem amp_liftTo {m h : ℕ} (k : ℕ) (hmk : m ≤ k) (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    amp (⟨k, h, FTQCLib.Hilbert.liftTo k hmk Q, c, L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨k, h, FTQCLib.Hilbert.liftTo k hmk Q, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
    exact ampCore_liftTo k hmk Q c w
  · rw [amp_neg (S := (⟨k, h, FTQCLib.Hilbert.liftTo k hmk Q, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

/-- **R7**, as equality of denotation: a carrier state and its precision lift are the same state. -/
theorem stateEq_liftTo {m h : ℕ} (k : ℕ) (hmk : m ≤ k) (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    StateEq (⟨k, h, FTQCLib.Hilbert.liftTo k hmk Q, c, L, x₀⟩ : KernelSumState n)
      (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) :=
  amp_liftTo k hmk Q c L x₀

/-! ## R7 on a carrier state -/

/-- **R7 on a carrier state.** The exponent is read at precision `k ≥ S.m` through
`FTQCLib.Hilbert.liftTo`; the height, scale and support are unchanged, and so is the amplitude
(`amp_liftTo`). -/
noncomputable def liftPrecision (S : KernelSumState n) (k : ℕ) (hk : S.m ≤ k) :
    KernelSumState n :=
  ⟨k, S.h, FTQCLib.Hilbert.liftTo k hk S.Q, S.c, S.L, S.x₀⟩

/-- **R7 on a carrier state** keeps the amplitude. -/
theorem amp_liftPrecision (S : KernelSumState n) (k : ℕ) (hk : S.m ≤ k) :
    amp (liftPrecision S k hk) = amp S :=
  amp_liftTo k hk S.Q S.c S.L S.x₀

/-- **R7 on a carrier state** keeps the carrier property: the precision only grows, the Lagrangian
is the same, and the amplitude is unchanged (`amp_liftPrecision`). -/
theorem isCarrier_liftPrecision {S : KernelSumState n} (hS : IsCarrier S) (k : ℕ)
    (hk : S.m ≤ k) : IsCarrier (liftPrecision S k hk) := by
  refine ⟨hS.1.trans hk, hS.2.1, hS.2.2.1, ?_⟩
  rw [amp_liftPrecision]
  exact hS.2.2.2

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.RegisterWalkthrough
import FTQCLib.Hierarchy.RzApprox

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # The Rz approximation, composed in the walkthrough's table format

Machine-checked companion to the Rz approximation theorem (`FTQCLib/Hierarchy/RzApprox.lean`), staged as a
register-walkthrough table (`FTQCLib/Examples/RegisterWalkthrough.lean`): put one bit in superposition, then
apply the root-of-`Z` tower gates row by row — one row per binary digit of the rounded angle — reading the
`KernelState` exponent column at each step. Everything is literal `KernelState`/`DiagPhase` data; the rows
rewrite the carrier exponent directly.

Two grades of verified distance to the `R_z(θ)` phase pattern:

* **Symbolic θ (the sharp bound).** `runRows_rz_approx`: for every angle `θ` and precision `m` there is a
  coefficient whose tower rows, run from `|+⟩`, leave the table within arc distance `π/2^m` of the target
  pattern on every input — `rz_dyadic_approx` read through the table. The exponent column of the finished
  table IS the anchored approximant (`runRows_towerRows_q`), at level ≤ m (`runRows_towerRows_level`).
* **Concrete θ = 2π/3 (exact numerals).** The minimal non-dyadic rational instance, at m = 2, 3, 4: the
  coefficients are 1, 3, 5 (binary 1, 11, 101 — the digits are the gate rows), and the exact achieved arc
  distances are `π/6`, `π/12`, `π/24` — equalities, not bounds — each under its guaranteed `π/2^m` and
  halving per rung. `ladder_*_exact` / `ladder_*_within`.

Frame-pure: no `FTQCLib.Hilbert` import. The operator-norm distances for the same tables are the separable
certificate `FTQCLib/Examples/RzTableOperator.lean`. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase MvPolynomial Real

variable {n : ℕ}

/-! ## The table motions: the `|+⟩` row and the accumulating diagonal row -/

/-- The one-bit `|+⟩` table state at precision `m`: support `{0, 1}` (`L = ⊤`, as `tBit`), no phase yet.
The post-`H` row of the table. (Reducible so the table's precision field reduces in later statements.) -/
@[reducible] noncomputable def plusBit (m : ℕ) : KernelState 1 where
  m := m;  q := 0;  c := 1;  L := ⊤;  x₀ := 0

/-- A diagonal table row at the state's own precision: add the gate polynomial into the exponent column.
The same-precision accumulating cousin of `applyDiagFrom0` — this is the direct carrier rewrite, row by
row. -/
@[reducible] noncomputable def applyDiag (K : KernelState n) (P : DiagPhase n K.m) : KernelState n where
  m := K.m;  q := K.q + P;  c := K.c;  L := K.L;  x₀ := K.x₀

/-- Run a list of diagonal rows from `|+⟩`: the finished table. Its exponent column is the sum of the
rows (`runRows_q`), and appending a row is `applyDiag` (`runRows_concat`) — so this IS the row-by-row
table, stated once. -/
@[reducible] noncomputable def runRows (m : ℕ) (rows : List (DiagPhase 1 m)) : KernelState 1 where
  m := m;  q := rows.sum;  c := 1;  L := ⊤;  x₀ := 0

@[simp] theorem runRows_q (m : ℕ) (rows : List (DiagPhase 1 m)) :
    (runRows m rows).q = rows.sum := rfl

@[simp] theorem applyDiag_q (K : KernelState n) (P : DiagPhase n K.m) :
    (applyDiag K P).q = K.q + P := rfl

@[simp] theorem plusBit_q (m : ℕ) : (plusBit m).q = 0 := rfl

/-- The empty table is the `|+⟩` row. -/
theorem runRows_nil (m : ℕ) : runRows m [] = plusBit m := rfl

/-- **The row-by-row reading.** Appending a row to the table is one `applyDiag` motion on the finished
table — running the list IS applying the gates in sequence. -/
theorem runRows_concat (m : ℕ) (rows : List (DiagPhase 1 m)) (P : DiagPhase 1 m) :
    runRows m (rows ++ [P]) = applyDiag (runRows m rows) P :=
  congrArg (fun q : DiagPhase 1 m => KernelState.mk m q 1 ⊤ 0)
    (by rw [List.sum_append, List.sum_singleton, runRows_q])

/-! ## The tower rows of a coefficient: one row per binary digit -/

/-- The tower-gate rows of a coefficient `c`: one diagonal row `C 2^k · X 0` per set bit `k` of `c` —
the binary digits of the rounded angle, as gates. -/
noncomputable def towerRows (m : ℕ) (c : ZMod (2 ^ m)) : List (DiagPhase 1 m) :=
  c.val.bitIndices.map (fun k => C ((2 : ZMod (2 ^ m)) ^ k) * X 0)

/-- **The table composes the approximant.** Running the tower rows of `c` from `|+⟩` accumulates exactly
the anchored approximant `C c · X 0` in the exponent column (`rz_approx_composition`, read through the
table). -/
theorem runRows_towerRows_q (m : ℕ) (c : ZMod (2 ^ m)) :
    (runRows m (towerRows m c)).q = C c * X 0 := by
  change (towerRows m c).sum = C c * X 0
  unfold towerRows
  rw [rz_approx_composition c 0, List.sum_toFinset _ Nat.bitIndices_nodup]

/-- **The cost column.** The finished table's exponent sits at level ≤ m — accuracy `π/2^m` is bought at
level `m` (`rz_approx_level_le`, read through the table). -/
theorem runRows_towerRows_level (m : ℕ) (hm : 1 ≤ m) (c : ZMod (2 ^ m)) :
    (runRows m (towerRows m c)).q.level ≤ m := by
  rw [runRows_towerRows_q]
  exact rz_approx_level_le c 0 hm

/-! ## Grade 2 — symbolic θ: the table approximates any rotation at the sharp bound -/

/-- **The table approximates any rotation (symbolic θ, sharp bound).** For every angle `θ` and precision
`m` there is a coefficient `c` whose tower rows, run from `|+⟩`, leave the table's exponent column within
arc distance `π/2^m` of the `R_z(θ)` phase pattern on every input. `rz_dyadic_approx` staged as a table:
the distance is verified, but for irrational `θ` the coefficient is a classical existential — no numeral
to extract. -/
theorem runRows_rz_approx (θ : ℝ) (m : ℕ) :
    ∃ c : ZMod (2 ^ m), ∀ v : Fin 1 → ZMod 2, ∃ k : ℤ,
      |realPhase (runRows m (towerRows m c)).q v - (v 0).val * θ - 2 * π * k| ≤ π / 2 ^ m := by
  obtain ⟨c, hc⟩ := rz_dyadic_approx θ (0 : Fin 1) m
  refine ⟨c, fun v => ?_⟩
  rw [runRows_towerRows_q]
  exact hc v

/-! ## Grade 1 — the concrete ladder: θ = 2π/3 at m = 2, 3, 4

The minimal non-dyadic rational target. Everything is exact arithmetic: the coefficients are the literals
1, 3, 5, the row lists are explicit, and the achieved arc distances are closed-form numerals proved as
equalities. The input `v₁` is the active branch (bit set). -/

/-- The active-branch input: the bit set. -/
def v₁ : Fin 1 → ZMod 2 := fun _ => 1

/-- The active branch contributes `1` to the phase pattern. -/
theorem v₁_val : ((v₁ 0).val : ℝ) = 1 := by
  rw [show (v₁ 0).val = 1 from by decide, Nat.cast_one]

/-! ### m = 2 — one gate row (`S`), distance exactly π/6 -/

/-- The m = 2 table: a single row, the coefficient-1 gate (the `S` angle `2π/4`). Its exponent is the
anchored approximant with `c = 1`. -/
theorem ladder_two_q :
    (runRows 2 [C (1 : ZMod (2 ^ 2)) * X 0]).q = C (1 : ZMod (2 ^ 2)) * X 0 := by
  rw [runRows_q, List.sum_singleton]

/-- **m = 2, exact distance.** The table's phase sits exactly `π/6` from the `R_z(2π/3)` pattern on the
active branch — a numeral with a proof (bound: `π/4`). -/
theorem ladder_two_exact :
    |realPhase (runRows 2 [C (1 : ZMod (2 ^ 2)) * X 0]).q v₁ - 2 * π / 3| = π / 6 := by
  rw [ladder_two_q, realPhase_linear, v₁_val, one_mul,
    show (((1 : ZMod (2 ^ 2)).val : ℝ)) = 1 from by
      rw [show (1 : ZMod (2 ^ 2)).val = 1 from by decide, Nat.cast_one]]
  have hsign : 2 * π * (1 : ℝ) / 2 ^ 2 - 2 * π / 3 ≤ 0 := by nlinarith [pi_pos]
  rw [abs_of_nonpos hsign]
  ring

/-- **m = 2, the guaranteed bound is met:** `π/6 ≤ π/2²`. -/
theorem ladder_two_within :
    |realPhase (runRows 2 [C (1 : ZMod (2 ^ 2)) * X 0]).q v₁ - 2 * π / 3| ≤ π / 2 ^ 2 := by
  rw [ladder_two_exact, show ((2 : ℝ) ^ 2) = 4 from by norm_num]
  linarith [pi_pos]

/-! ### m = 3 — two gate rows (binary 11), distance exactly π/12 -/

/-- The m = 3 table: two rows, coefficients 1 and 2 (`3 = 11₂`). The exponent column collapses to the
anchored approximant with `c = 3`. -/
theorem ladder_three_q :
    (runRows 3 [C (1 : ZMod (2 ^ 3)) * X 0, C (2 : ZMod (2 ^ 3)) * X 0]).q
      = C (3 : ZMod (2 ^ 3)) * X 0 := by
  rw [runRows_q, show (3 : ZMod (2 ^ 3)) = 1 + 2 from by decide, map_add,
    List.sum_cons, List.sum_singleton]
  ring

/-- **m = 3, exact distance.** Exactly `π/12` on the active branch (bound: `π/8`) — one rung down, the
distance halves. -/
theorem ladder_three_exact :
    |realPhase (runRows 3 [C (1 : ZMod (2 ^ 3)) * X 0, C (2 : ZMod (2 ^ 3)) * X 0]).q v₁
      - 2 * π / 3| = π / 12 := by
  rw [ladder_three_q, realPhase_linear, v₁_val, one_mul,
    show (((3 : ZMod (2 ^ 3)).val : ℝ)) = 3 from by
      rw [show (3 : ZMod (2 ^ 3)).val = 3 from by decide]; norm_num]
  have hsign : 0 ≤ 2 * π * (3 : ℝ) / 2 ^ 3 - 2 * π / 3 := by nlinarith [pi_pos]
  rw [abs_of_nonneg hsign]
  ring

/-- **m = 3, the guaranteed bound is met:** `π/12 ≤ π/2³`. -/
theorem ladder_three_within :
    |realPhase (runRows 3 [C (1 : ZMod (2 ^ 3)) * X 0, C (2 : ZMod (2 ^ 3)) * X 0]).q v₁
      - 2 * π / 3| ≤ π / 2 ^ 3 := by
  rw [ladder_three_exact, show ((2 : ℝ) ^ 3) = 8 from by norm_num]
  linarith [pi_pos]

/-! ### m = 4 — two gate rows (binary 101), distance exactly π/24 -/

/-- The m = 4 table: two rows, coefficients 1 and 4 (`5 = 101₂`). The exponent column collapses to the
anchored approximant with `c = 5`. -/
theorem ladder_four_q :
    (runRows 4 [C (1 : ZMod (2 ^ 4)) * X 0, C (4 : ZMod (2 ^ 4)) * X 0]).q
      = C (5 : ZMod (2 ^ 4)) * X 0 := by
  rw [runRows_q, show (5 : ZMod (2 ^ 4)) = 1 + 4 from by decide, map_add,
    List.sum_cons, List.sum_singleton]
  ring

/-- The m = 4 table, row by row: `|+⟩`, then the coefficient-1 row, then the coefficient-4 row — two
`applyDiag` motions. The table IS the gate sequence. -/
theorem ladder_four_rows :
    runRows 4 [C (1 : ZMod (2 ^ 4)) * X 0, C (4 : ZMod (2 ^ 4)) * X 0]
      = applyDiag (applyDiag (plusBit 4) (C (1 : ZMod (2 ^ 4)) * X 0))
          (C (4 : ZMod (2 ^ 4)) * X 0) :=
  congrArg (fun q : DiagPhase 1 4 => KernelState.mk 4 q 1 ⊤ 0)
    (by simp only [List.sum_cons, List.sum_nil, add_zero, applyDiag_q, plusBit_q, zero_add])

/-- **m = 4, exact distance.** Exactly `π/24` on the active branch (bound: `π/16`) — the ladder
`π/6, π/12, π/24` halves per rung, the sharp rate in numerals. -/
theorem ladder_four_exact :
    |realPhase (runRows 4 [C (1 : ZMod (2 ^ 4)) * X 0, C (4 : ZMod (2 ^ 4)) * X 0]).q v₁
      - 2 * π / 3| = π / 24 := by
  rw [ladder_four_q, realPhase_linear, v₁_val, one_mul,
    show (((5 : ZMod (2 ^ 4)).val : ℝ)) = 5 from by
      rw [show (5 : ZMod (2 ^ 4)).val = 5 from by decide]; norm_num]
  have hsign : 2 * π * (5 : ℝ) / 2 ^ 4 - 2 * π / 3 ≤ 0 := by nlinarith [pi_pos]
  rw [abs_of_nonpos hsign]
  ring

/-- **m = 4, the guaranteed bound is met:** `π/24 ≤ π/2⁴`. -/
theorem ladder_four_within :
    |realPhase (runRows 4 [C (1 : ZMod (2 ^ 4)) * X 0, C (4 : ZMod (2 ^ 4)) * X 0]).q v₁
      - 2 * π / 3| ≤ π / 2 ^ 4 := by
  rw [ladder_four_exact, show ((2 : ℝ) ^ 4) = 16 from by norm_num]
  linarith [pi_pos]

/-- **The cost column of the m = 4 table:** level ≤ 4. Accuracy `π/24` at level 4. -/
theorem ladder_four_level :
    (runRows 4 [C (1 : ZMod (2 ^ 4)) * X 0, C (4 : ZMod (2 ^ 4)) * X 0]).q.level ≤ 4 := by
  rw [ladder_four_q]
  exact rz_approx_level_le (5 : ZMod (2 ^ 4)) 0 (by norm_num)

end FTQCLib.Frame.Walkthrough

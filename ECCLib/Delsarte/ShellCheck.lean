/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Shell
import ECCLib.Delsarte.Distribution

set_option linter.style.longLine false

/-!
# Shell + distribution — regression checks

Kernel-checked rows for the cardinality formulas and the distance distribution
(values computed independently by `#eval`, kernel-confirmed here), plus the
build-failing axiom sweep for the main theorems. `charShellSum` itself is
ℂ-valued (not decidable); its check is the axiom guard plus the fact that its
two inputs — `tupleChar_genfun` and `kraw_eq_coeff` — carry their own checks.
-/

namespace ECCLib.Delsarte

/-! ## Cardinality rows (`card_shell` / `card_sphere` / `card_ball`) -/

theorem check_shell_ternary :
    (Finset.univ.filter fun u : Fin 4 → ZMod 3 => hammingNorm u = 2).card = 24 := by
  decide

theorem check_shell_binary :
    (Finset.univ.filter fun u : Fin 5 → ZMod 2 => hammingNorm u = 2).card = 10 := by
  decide

theorem check_sphere_offcenter :
    (Finset.univ.filter fun y : Fin 4 → ZMod 3 =>
      hammingDist ![1, 0, 2, 0] y = 2).card = 24 := by
  decide

theorem check_ball_ternary :
    (Finset.univ.filter fun y : Fin 4 → ZMod 3 =>
      hammingDist ![0, 0, 0, 0] y ≤ 1).card = 9 := by
  decide

/-- The formulas agree with the theorems at these parameters (two-route check). -/
theorem check_shell_formula : (4 : ℕ).choose 2 * (3 - 1) ^ 2 = 24 := by decide

/-! ## Distance-distribution rows (independently computed values, kernel-confirmed) -/

/-- The binary repetition code `{000, 111}`. -/
def rep3 : Finset (Fin 3 → ZMod 2) := {![0, 0, 0], ![1, 1, 1]}

theorem check_rep3_card : rep3.card = 2 := by decide
theorem check_rep3_pc0 : pairCount rep3 0 = 2 := by decide
theorem check_rep3_pc1 : pairCount rep3 1 = 0 := by decide
theorem check_rep3_pc2 : pairCount rep3 2 = 0 := by decide
theorem check_rep3_pc3 : pairCount rep3 3 = 2 := by decide

/-- A genuinely NONLINEAR code (`1100 + 0011 = 1111 ∉ C`): the carrier the Submodule
layer cannot express. Distribution `[3, 0, 4, 0, 2]`. -/
def nonlin : Finset (Fin 4 → ZMod 2) := {![0, 0, 0, 0], ![1, 1, 0, 0], ![0, 0, 1, 1]}

theorem check_nonlin_card : nonlin.card = 3 := by decide
theorem check_nonlin_pc0 : pairCount nonlin 0 = 3 := by decide
theorem check_nonlin_pc1 : pairCount nonlin 1 = 0 := by decide
theorem check_nonlin_pc2 : pairCount nonlin 2 = 4 := by decide
theorem check_nonlin_pc3 : pairCount nonlin 3 = 0 := by decide
theorem check_nonlin_pc4 : pairCount nonlin 4 = 2 := by decide

/-- Total mass cross-check: `3 + 4 + 2 = 9 = |C|²` (the `sum_pairCount` instance). -/
theorem check_nonlin_mass :
    ∑ i ∈ Finset.range 5, pairCount nonlin i = 9 := by decide

end ECCLib.Delsarte

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Delsarte.charShellSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.charShellSum

/-- info: 'ECCLib.Delsarte.tupleChar_genfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.tupleChar_genfun

/-- info: 'ECCLib.Delsarte.card_shell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.card_shell

/-- info: 'ECCLib.Delsarte.card_sphere' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.card_sphere

/-- info: 'ECCLib.Delsarte.card_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.card_ball

/-- info: 'ECCLib.Delsarte.sum_pairCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.sum_pairCount

/-- info: 'ECCLib.Delsarte.pairCount_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.pairCount_eq_zero_of_lt

/-- info: 'ECCLib.Delsarte.coordSumOfChar' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.coordSumOfChar

/-- info: 'ECCLib.Delsarte.wordChar_genfun' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.wordChar_genfun

/-- info: 'ECCLib.Delsarte.wordShellSum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.wordShellSum

/-- info: 'ECCLib.Delsarte.hammingNorm_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.hammingNorm_neg

/-- info: 'ECCLib.Delsarte.hammingNorm_add_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.hammingNorm_add_le

/-- info: 'ECCLib.Delsarte.exists_word_of_weight' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.exists_word_of_weight

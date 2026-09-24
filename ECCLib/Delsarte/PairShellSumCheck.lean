/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.PairShellSum
import Mathlib.Data.Fin.VecNotation

/-!
# Checks for `ECCLib/Delsarte/PairShellSum.lean`

Axiom sweeps, and **kernel agreement rows**: the shell-sum identity evaluated by `decide` at
small carriers, against the literal `eberlein` values the module claims. These rows exercise
the whole chain — expansion, pattern count, window identification — numerically, in all three
regimes: positive, flipped (value `−1`), and non-separated (both sides vanish).
-/

namespace ECCLib

open Finset

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.pairDiff_factor_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff_factor_split

/-- info: 'ECCLib.PairPattern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.PairPattern

/-- info: 'ECCLib.decidablePairPattern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.decidablePairPattern

/-- info: 'ECCLib.pairDiff_eq_sum_pattern' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff_eq_sum_pattern

/-- info: 'ECCLib.pairSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairSupport

/-- info: 'ECCLib.patternSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.patternSet

/-- info: 'ECCLib.a_ne_b' does not depend on any axioms -/
#guard_msgs in
#print axioms ECCLib.a_ne_b

/-- info: 'ECCLib.injective_a' does not depend on any axioms -/
#guard_msgs in
#print axioms ECCLib.injective_a

/-- info: 'ECCLib.injective_b' does not depend on any axioms -/
#guard_msgs in
#print axioms ECCLib.injective_b

/-- info: 'ECCLib.mem_patternSet_a' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.mem_patternSet_a

/-- info: 'ECCLib.mem_patternSet_b' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.mem_patternSet_b

/-- info: 'ECCLib.patternSet_subset_pairSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.patternSet_subset_pairSupport

/-- info: 'ECCLib.card_patternSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_patternSet

/-- info: 'ECCLib.pattern_inter_pairSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pattern_inter_pairSupport

/-- info: 'ECCLib.mem_pairSupport_a' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.mem_pairSupport_a

/-- info: 'ECCLib.mem_pairSupport_b' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.mem_pairSupport_b

/-- info: 'ECCLib.card_shell_pattern' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_shell_pattern

/-- info: 'ECCLib.card_shell_pattern_eq_zero_low' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_shell_pattern_eq_zero_low

/-- info: 'ECCLib.card_shell_pattern_eq_zero_high' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_shell_pattern_eq_zero_high

/-- info: 'ECCLib.card_pairSupport' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_pairSupport

/-- info: 'ECCLib.inter_pairSupport_pos' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.inter_pairSupport_pos

/-- info: 'ECCLib.card_inter_patternSet_pos' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_inter_patternSet_pos

/-- info: 'ECCLib.card_sdiff_pairSupport_pos' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_sdiff_pairSupport_pos

/-- info: 'ECCLib.card_compl_union_pos' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_compl_union_pos

/-- info: 'ECCLib.sum_shell_pairDiff_pos' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_shell_pairDiff_pos

/-- info: 'ECCLib.sum_shell_pairDiff_eq_zero' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_shell_pairDiff_eq_zero

/-- info: 'ECCLib.pairDiff_update_flip' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.pairDiff_update_flip

/-- info: 'ECCLib.injective_sumElim_update' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.injective_sumElim_update

/-- info: 'ECCLib.sum_shell_pairDiff_sep' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_shell_pairDiff_sep

/-- info: 'ECCLib.sum_shell_pairDiff' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_shell_pairDiff

/-! ## Kernel agreement rows at `J(4,2)`-scale

Carrier `Fin 4`, `K = {0,1}`, `k = 2`, one pair. The `J(4,2)` Eberlein values at `t = 1` are
`E_0(1) = 1`, `E_1(1) = 0`, `E_2(1) = -2` (`Delsarte/EberleinCheck.lean` pins the family). -/

/-- Positive pair (`a = 0 ∈ K`, `b = 2 ∉ K`): the value at `K` is `1`, so each shell sum IS
the Eberlein number. -/
example : pairDiff ℤ ![(0 : Fin 4)] ![2] {0, 1} = 1 := by decide

example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 1} : Finset (Fin 4)) ∩ L) = 2), pairDiff ℤ ![(0 : Fin 4)] ![2] L
    = Delsarte.eberlein 4 2 0 1 := by decide

example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 1} : Finset (Fin 4)) ∩ L) = 1), pairDiff ℤ ![(0 : Fin 4)] ![2] L
    = Delsarte.eberlein 4 2 1 1 := by decide

example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 1} : Finset (Fin 4)) ∩ L) = 0), pairDiff ℤ ![(0 : Fin 4)] ![2] L
    = Delsarte.eberlein 4 2 2 1 := by decide

/-- Flipped pair (`a = 2 ∉ K`, `b = 0 ∈ K`): the value at `K` is `-1`, and every shell sum
carries the sign. -/
example : pairDiff ℤ ![(2 : Fin 4)] ![0] {0, 1} = -1 := by decide

example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 1} : Finset (Fin 4)) ∩ L) = 0), pairDiff ℤ ![(2 : Fin 4)] ![0] L
    = Delsarte.eberlein 4 2 2 1 * (-1) := by decide

/-- Non-separated pair (`a = 0` and `b = 1` both in `K`): the value at `K` and every shell
sum vanish. -/
example : pairDiff ℤ ![(0 : Fin 4)] ![1] {0, 1} = 0 := by decide

example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 1} : Finset (Fin 4)) ∩ L) = 1), pairDiff ℤ ![(0 : Fin 4)] ![1] L
    = 0 := by decide

/-- Two pairs at `J(5,2)` — the asymmetric-valence case that pins conventions: `t = 2`,
`K = {0, 2}`, positive system `a = ![0, 2]`, `b = ![1, 3]`. `E_l(2)` at `J(5,2)`:
`E_0(2) = 1`, `E_1(2) = -1`, `E_2(2) = 0`. -/
example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 2} : Finset (Fin 5)) ∩ L) = 1), pairDiff ℤ ![(0 : Fin 5), 2] ![1, 3] L
    = Delsarte.eberlein 5 2 1 2 := by decide

example : ∑ L ∈ (Finset.univ.powersetCard 2).filter
    (fun L => #(({0, 2} : Finset (Fin 5)) ∩ L) = 0), pairDiff ℤ ![(0 : Fin 5), 2] ![1, 3] L
    = Delsarte.eberlein 5 2 2 2 := by decide

end ECCLib

/-- info: 'ECCLib.sum_star_pairDiff_eq_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_star_pairDiff_eq_zero

/-- info: 'ECCLib.card_star_avoid' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.card_star_avoid

/-- info: 'ECCLib.sum_star_pairDiff_transversal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_star_pairDiff_transversal

/-- info: 'ECCLib.sum_powersetCard_pairDiff_eq_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_powersetCard_pairDiff_eq_zero

/-- info: 'ECCLib.sum_powersetCard_pairDiff_transversal' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.sum_powersetCard_pairDiff_transversal

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Linear
import ECCLib.WitnessCoding

set_option linter.style.longLine false

/-!
# The linear bridge — regression checks

**The two-route agreement, live**: `macwilliams_coeff` (the dual-shell route)
re-derives the dual weight distribution of the worked example `C₃` (the
repetition code in `𝔽₃³`) from the PRIMAL distribution and Krawtchouk numbers — and
lands on exactly the values `WitnessCoding` proves by direct kernel counting
(`witness_weightDist_dual_C₃`, the route through the collapse lemmas beside
`homMacwilliams`). Same numerals, two independent derivations.
-/

namespace ECCLib.Delsarte

open ECCLib.Coding ECCLib.Witness

/-- The bridge instantiated at `C₃` via its `S₃` presentation. -/
theorem check_bridge_C₃ (k : ℕ) :
    ∑ i ∈ Finset.range 4, (weightDist C₃ i : ℤ) * kraw 3 3 k i
      = (Nat.card C₃ : ℤ) * (weightDist (dualCode C₃) k : ℤ) := by
  have h := macwilliams_coeff (C := C₃) (S := S₃) mem_S₃ k
  simpa using h

/-- **NEW-route derivation** of the dual's `A'₂ = 6`: from the primal distribution
`(1, 0, 0, 2)` (kernel witnesses) and two Krawtchouk numerals, through
`macwilliams_coeff`. Compare `witness_weightDist_dual_C₃.2.2.1` — the SAME statement
by the direct counting route. -/
theorem check_agreement_dual_A2 : weightDist (dualCode C₃) 2 = 6 := by
  have h := check_bridge_C₃ 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at h
  rw [witness_weightDist_C₃_zero, witness_weightDist_C₃.2.1, witness_weightDist_C₃.2.2,
    witness_weightDist_C₃.1, card_C₃] at h
  rw [show kraw 3 3 2 0 = 12 from by decide, show kraw 3 3 2 3 = 3 from by decide] at h
  have h6 : (weightDist (dualCode C₃) 2 : ℤ) = 6 := by
    push_cast at h
    omega
  exact_mod_cast h6

/-- The OLD route to the same numeral (cited, not re-proved): direct kernel count. -/
theorem check_agreement_dual_A2_old_route : weightDist (dualCode C₃) 2 = 6 :=
  witness_weightDist_dual_C₃.2.2.1

/-- Agreement at `k = 3` as well: `A'₃ = 2` by the new route. -/
theorem check_agreement_dual_A3 : weightDist (dualCode C₃) 3 = 2 := by
  have h := check_bridge_C₃ 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at h
  rw [witness_weightDist_C₃_zero, witness_weightDist_C₃.2.1, witness_weightDist_C₃.2.2,
    witness_weightDist_C₃.1, card_C₃] at h
  rw [show kraw 3 3 3 0 = 8 from by decide, show kraw 3 3 3 3 = -1 from by decide] at h
  have h2 : (weightDist (dualCode C₃) 3 : ℤ) = 2 := by
    push_cast at h
    omega
  exact_mod_cast h2

theorem check_agreement_dual_A3_old_route : weightDist (dualCode C₃) 3 = 2 :=
  witness_weightDist_dual_C₃.2.2.2

end ECCLib.Delsarte

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Delsarte.macwilliams_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.macwilliams_coeff

/-- info: 'ECCLib.Delsarte.lp_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.lp_linear

/-- info: 'ECCLib.Delsarte.sum_pairingChar_presentation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.sum_pairingChar_presentation

/-- info: 'ECCLib.Delsarte.check_agreement_dual_A2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Delsarte.check_agreement_dual_A2

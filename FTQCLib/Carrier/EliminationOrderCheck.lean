/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.EliminationOrder
import FTQCLib.Carrier.EliminationOrderData

/-!
# Check: the elimination-order witness against the search data

T04's witness (`FTQCLib.Frame.Walkthrough.EliminationOrder`) hand-writes `inputExponent` as "the
first case of `EliminationOrderData.cases`" (that module's docstring). The agreement row here
makes the tie exact rather than asserted: the first case's coefficient list is literally the one
`inputExponent` encodes (monomial `0` is `y₀`, monomial `1` is `y₁`, monomial `6` is `y₀y₁y₂`,
`tools/search/elimination_order.py`'s `admissible_monomials` order), and its two sequences reach
height two, matching `outcomeA.h` and `outcomeB.h` (`elimination_order_matters`'s `rfl` fields).
The discriminating row separates that case from its neighbour two rows down in `cases`: the same
cell and shape, with `y₀`'s and `y₁`'s coefficients swapped (`1 ↔ 3`) — the nearest wrong
coefficient list, at monomial `0`'s value. The inhabitation row is the headline theorem itself: a
concrete witness with no free hypotheses, so exhibiting it is exhibiting all of them held
together.
-/

namespace FTQCLib.Frame.Walkthrough.EliminationOrder

/-! ## The witness's case, against the search data -/

/-- The witness's coefficient list, read off `EliminationOrderData.cases`' first case: monomial
`0` (`y₀`) at `1`, monomial `1` (`y₁`) at `3`, monomial `6` (`y₀y₁y₂`) at `2` — `inputExponent`'s
three terms, in the search's monomial order. -/
def case0Coeffs : List FTQCLib.Carrier.EliminationOrderData.Coeff :=
  [⟨0, 1⟩, ⟨1, 3⟩, ⟨6, 2⟩]

/-- **Agreement.** The search's first case is exactly the witness's cell (`n = 0`, `h = 3`,
`m = 2`), the witness's coefficients, and both sequences reaching height two — the same height
`elimination_order_matters` proves `outcomeA` and `outcomeB` reach (its `rfl` fields
`outcomeA.h = 2`, `outcomeB.h = 2`). -/
-- row: agreement
theorem case0_eq_witness_cell :
    FTQCLib.Carrier.EliminationOrderData.cases.head? =
      some ⟨0, 3, 2, case0Coeffs, [⟨0, 1, true⟩], outcomeA.h, [⟨1, 1, true⟩], outcomeB.h,
        false⟩ := by
  decide

/-- **Discriminating.** The witness's coefficients are not its nearest neighbour two rows down in
`EliminationOrderData.cases`: the case for the same cell and shape with `y₀`'s and `y₁`'s
coefficients swapped (monomial `0` at `3`, monomial `1` at `1` — the exponent
`3·y₀ + y₁ + 2·y₀y₁y₂` in place of `y₀ + 3·y₁ + 2·y₀y₁y₂`). They differ at monomial `0`'s value:
`1` against `3`. -/
-- row: discriminating
theorem case0Coeffs_ne_swapped :
    case0Coeffs ≠ ([⟨0, 3⟩, ⟨1, 1⟩, ⟨6, 2⟩] : List FTQCLib.Carrier.EliminationOrderData.Coeff) := by
  decide

/-- **Inhabitation.** `elimination_order_matters` carries no hypotheses: it is a concrete
conjunction about the fixed witness `input`. Exhibiting it exhibits all nine conjuncts —
`input` is a carrier state, both rotate steps are available, both outcomes denote `input`, both
are stuck at height two, and no gauge rewrite relates them — held together at once. -/
-- row: inhabitation
example := elimination_order_matters

/-! ## `inputExponent`, decoded from the search's coefficient list

`case0_eq_witness_cell` ties `case0Coeffs` — a hand-written list the docstring above asserts reads
off `inputExponent`'s three terms — to the search's first case. This section removes the hand
part: `monomialCell03` is the cell `n = 0, h = 3`'s admissible-monomial list
(`tools/search/elimination_order.py`'s `admissible_monomials`, size then lexicographic order, the
same order `EliminationOrderData`'s docstring names), and `decodeCell03` reads a coefficient list
through it. The theorem below is a compiler check that `inputExponent` — the witness's actual
polynomial, not an assertion about it — decodes from `case0Coeffs` exactly, so the tie from the
witness to the search's data is by the kernel, not by the docstring alone. -/

/-- The bound monomial at each admissible index of the cell `n = 0`, `h = 3`: `admissible_monomials
(0, 3)` lists the three size-one monomials `X₀, X₁, X₂` (indices 0–2), the three size-two products
(indices 3–5), then the one size-three product (index 6). No other index is used by this cell. -/
private noncomputable def monomialCell03 : Nat → FTQCLib.Hierarchy.DiagPhase (0 + 3) 2
  | 0 => MvPolynomial.X 0
  | 1 => MvPolynomial.X 1
  | 2 => MvPolynomial.X 2
  | 3 => MvPolynomial.X 0 * MvPolynomial.X 1
  | 4 => MvPolynomial.X 0 * MvPolynomial.X 2
  | 5 => MvPolynomial.X 1 * MvPolynomial.X 2
  | 6 => MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
  | _ => 0

/-- A coefficient list decoded through `monomialCell03`: the sum, over the list, of each
coefficient's value against its monomial. -/
private noncomputable def decodeCell03 (l : List FTQCLib.Carrier.EliminationOrderData.Coeff) :
    FTQCLib.Hierarchy.DiagPhase (0 + 3) 2 :=
  (l.map fun c =>
    MvPolynomial.C ((c.value : ℕ) : ZMod (2 ^ 2)) * monomialCell03 c.monomialIndex).sum

/-- **Agreement.** `inputExponent`, the witness's input, decodes exactly from `case0Coeffs` through
`monomialCell03`: the compiler checks the witness's polynomial against the search's coefficient
list itself, not merely against an assertion that they agree. -/
-- row: agreement
theorem inputExponent_eq_decode_case0Coeffs :
    inputExponent = decodeCell03 case0Coeffs := by
  unfold decodeCell03 case0Coeffs monomialCell03 inputExponent
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_one,
    Nat.cast_ofNat, MvPolynomial.C_1, one_mul]
  ring

end FTQCLib.Frame.Walkthrough.EliminationOrder

/-! ## The axiom sweep — build-failing, one guard per theorem of the topic module -/

namespace FTQCLib.Frame.Walkthrough

/-- info: 'FTQCLib.Frame.Walkthrough.stateEq_of_gaugeStep' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_gaugeStep

/-- info: 'FTQCLib.Frame.Walkthrough.stateEq_of_gaugeRel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_of_gaugeRel

/-- info: 'FTQCLib.Frame.Walkthrough.boundTerms_eq_of_gaugeStep' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundTerms_eq_of_gaugeStep

/-- info: 'FTQCLib.Frame.Walkthrough.boundTerms_eq_of_gaugeRel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundTerms_eq_of_gaugeRel

end FTQCLib.Frame.Walkthrough

namespace FTQCLib.Frame.Walkthrough.EliminationOrder

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.isCarrier_input' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isCarrier_input

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.rotateData_stepA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotateData_stepA

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.rotateData_stepB' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotateData_stepB

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.stateEq_outcomeA_input' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_outcomeA_input

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.stateEq_outcomeB_input' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stateEq_outcomeB_input

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.eliminationStuck_outcomeA' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eliminationStuck_outcomeA

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.eliminationStuck_outcomeB' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eliminationStuck_outcomeB

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.boundTerms_outcomeA_ne_outcomeB' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundTerms_outcomeA_ne_outcomeB

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.not_gaugeRel_outcomeA_outcomeB' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_gaugeRel_outcomeA_outcomeB

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.elimination_order_matters' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms elimination_order_matters

/-- info: 'FTQCLib.Frame.Walkthrough.EliminationOrder.inputExponent_eq_decode_case0Coeffs' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inputExponent_eq_decode_case0Coeffs

end FTQCLib.Frame.Walkthrough.EliminationOrder

-- mutant: input_exponent_y1_coeff | FTQCLib/Carrier/EliminationOrder.lean | MvPolynomial.C 3 * MvPolynomial.X 1 | MvPolynomial.C 1 * MvPolynomial.X 1

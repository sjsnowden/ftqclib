/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Polynomial

/-!
# Check: the closure lemmas of the nonclassical degree

The axiom sweep of the degree's closure lemmas in `Polynomial.lean` and `Derivative.lean`
(negation, a difference, precomposition with an additive map; docs/STEPS.md, entry 2026-10-01g),
with rows on the mother example, a nonclassical polynomial of degree two on one bit.

* **Discriminating.** A difference lowers the degree by one: the mother example is not of degree
  `≤ 1`, and its difference in any direction is. A lemma that let a difference keep the degree, or
  that applied to the function itself, would be refuted here.
* **Agreement.** Negation and precomposition by the identity keep the mother example's degree two,
  the bound `motherExample_isPolyDegLE_two` proves directly.
* **Inhabitation.** The difference in the direction of the one bit has degree `≤ 1`.
-/

namespace ECCLib

-- row: discriminating
/-- The mother example is not of degree `≤ 1`, and its difference in every direction is. -/
theorem motherExample_fwdDiff_lowers (c : Fin 1 → ZMod 2) :
    ¬ IsPolyDegLE 1 motherExample ∧ IsPolyDegLE 1 (fwdDiff c motherExample) :=
  ⟨motherExample_not_isPolyDegLE_one, motherExample_isPolyDegLE_two.fwdDiff c⟩

-- row: agreement
/-- Negation and precomposition by the identity keep the mother example's degree two. -/
theorem motherExample_neg_comp_id :
    IsPolyDegLE 2 (fun v => -(motherExample v)) ∧
      IsPolyDegLE 2 (motherExample ∘ AddMonoidHom.id (Fin 1 → ZMod 2)) :=
  ⟨motherExample_isPolyDegLE_two.neg,
    motherExample_isPolyDegLE_two.comp_addMonoidHom_right (AddMonoidHom.id _)⟩

-- row: inhabitation
/-- The difference of the mother example along its one bit has degree `≤ 1`. -/
theorem motherExample_fwdDiff_single : IsPolyDegLE 1 (fwdDiff (fun _ => 1) motherExample) :=
  motherExample_isPolyDegLE_two.fwdDiff _

/-! ## Axiom sweep -/

/-- info: 'ECCLib.iteratedFwdDiff_comp_addMonoidHom_right' depends on axioms:
[Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECCLib.iteratedFwdDiff_comp_addMonoidHom_right

/-- info: 'ECCLib.IsPolyDegLE.neg' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECCLib.IsPolyDegLE.neg

/-- info: 'ECCLib.IsPolyDegLE.fwdDiff' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECCLib.IsPolyDegLE.fwdDiff

/-- info: 'ECCLib.IsPolyDegLE.comp_addMonoidHom_right' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECCLib.IsPolyDegLE.comp_addMonoidHom_right

end ECCLib

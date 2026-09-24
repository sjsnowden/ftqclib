/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.DualAction
import ECCLib.Scheme.OrbitCount

/-!
# Dual transitivity

The one alphabet-level statement the Hamming instance's dual side needs: `G` is transitive on
the nontrivial characters of `A` exactly when it is transitive on the nonzero elements of `A`.

No character is constructed. Transitivity is first read as a number — two orbits, because `0`
is an orbit by itself (`transOnNonzero_iff_card_orbits_eq_two`) — and the two numbers are then
equal because each symmetry fixes as many characters as vectors (`card_orbits_dual_eq`).

The `2 ≤ |A|` guard that the orbit-count reading needs does not appear here: the degenerate
case is vacuous on both sides at once, since a one-element group has a one-element dual.

## Main results

* `transOnNonzero_dual_iff` — transitivity on the nontrivial characters is equivalent to
  transitivity on the nonzero elements.
* `transOnNonzero_dual` — the implication form the Hamming instance consumes.

## Implementation notes

The `2 ≤ |A|` guard that the orbit-count reading needs does not appear here: the degenerate
case is vacuous on both sides at once, since a one-element group has a one-element dual.
-/

namespace ECCLib.Scheme

open MulAction

variable {A : Type*} [AddCommGroup A] [Finite A]
variable {G : Type*} [Group G] [Finite G] [DistribMulAction G A]

/-- **Dual transitivity, as an equivalence.** -/
theorem transOnNonzero_dual_iff :
    TransOnNonzero G (AddChar A ℂ) ↔ TransOnNonzero G A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  rcases Nat.lt_or_ge (Fintype.card A) 2 with hsmall | h2
  · have hA1 : Fintype.card A ≤ 1 := by omega
    have hD1 : Fintype.card (AddChar A ℂ) ≤ 1 := by
      rw [AddChar.card_eq]
      omega
    have sA : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hA1
    have sD : Subsingleton (AddChar A ℂ) := Fintype.card_le_one_iff_subsingleton.mp hD1
    exact ⟨fun _ a b _ _ => ⟨1, by rw [one_smul]; exact Subsingleton.elim _ _⟩,
      fun _ χ η _ _ => ⟨1, by rw [one_smul]; exact Subsingleton.elim _ _⟩⟩
  · have hA : 2 ≤ Nat.card A := by rwa [Nat.card_eq_fintype_card]
    have hD : 2 ≤ Nat.card (AddChar A ℂ) := by
      rw [Nat.card_eq_fintype_card, AddChar.card_eq]
      exact h2
    rw [transOnNonzero_iff_card_orbits_eq_two hD, transOnNonzero_iff_card_orbits_eq_two hA,
      card_orbits_dual_eq]

/-- **Dual transitivity**, in the implication form the Hamming instance consumes. -/
theorem transOnNonzero_dual (h : TransOnNonzero G A) : TransOnNonzero G (AddChar A ℂ) :=
  transOnNonzero_dual_iff.mpr h

end ECCLib.Scheme

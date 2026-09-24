/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Bridge.HOFBridge
import FTQCLib.Frame.CubicCeiling

set_option linter.style.longLine false

/-!
# The Möbius ↔ nonclassical degree relationship (a decomposition, not an equivalence)

The frame carries two distinct degree notions, and this file pins their relationship; the
equivalence `MobiusDegLE ↔ IsPolyDegLE` is *false*.

* **Interaction / Möbius degree** (`FTQCLib.Frame.MobiusDegLE`, `ℤ/4` floor) — the ANF / subset-support degree:
  `mobiusCoeff S f = funcDerivSubset S f 0` vanishes for `|S| > d`. It reads iterated *coordinate-subset*
  differences (distinct coordinates) at the single point `0`.
* **Nonclassical degree** (`ECCLib.IsPolyDegLE`) — iterated differences over *arbitrary* directions,
  *everywhere*.

**The relationship is a one-way implication, strict in general.**
`MobiusDegLE_of_isPolyDegLE`: `IsPolyDegLE d f → MobiusDegLE d f` — the interaction degree is `≤` the
nonclassical degree (a Möbius coefficient of order `> d` is a single instance of the length-`> d` differences
that a degree-`≤ d` function annihilates). The converse fails, and the gap is exactly *precision*: the mother
example `|v₀|` over `ℤ/4` has interaction degree **exactly 1** (`not_mobiusDegLE_zero_motherExample` +
`mobiusDegLE_one_motherExample`) but nonclassical degree **exactly 2** (`motherExample_not_isPolyDegLE_one` +
`motherExample_isPolyDegLE_two`) — a gap of `m−1 = 1`.
-/

namespace FTQCLib.Bridge

open FTQCLib.Hierarchy FTQCLib.Hierarchy.BooleanMobius ECCLib

variable {N : ℕ}

/-- **The nonclassical degree bounds the Möbius coefficients:** a degree-`≤ d` function has every Möbius
coefficient of order `> d` equal to zero (its `mobiusCoeff` is a coordinate-subset difference at `0`, of
length `= |S| > d`, hence annihilated). General codomain. -/
theorem mobiusCoeff_eq_zero_of_isPolyDegLE {A : Type*} [AddCommGroup A] {d : ℕ}
    {f : (Fin N → ZMod 2) → A} (h : IsPolyDegLE d f) {S : Finset (Fin N)} (hS : d < S.card) :
    mobiusCoeff S f = 0 := by
  have hlen : d + 1 ≤ (S.toList.map (fun i => Pi.single i (1 : ZMod 2))).length := by
    rw [List.length_map, Finset.length_toList]; omega
  have hz := h.iteratedFwdDiff_eq_zero hlen
  show funcDerivSubset S f 0 = 0
  rw [funcDerivSubset_eq_iteratedFwdDiff, hz]
  simp

/-- **Interaction degree ≤ nonclassical degree** (`ℤ/4` floor): `IsPolyDegLE d f → MobiusDegLE d f`. The
one-way implication; the equivalence `MobiusDegLE ↔ IsPolyDegLE` is false. -/
theorem MobiusDegLE_of_isPolyDegLE {d : ℕ} {f : (Fin N → ZMod 2) → ZMod 4}
    (h : IsPolyDegLE d f) : FTQCLib.Frame.MobiusDegLE d f :=
  fun _ hS => mobiusCoeff_eq_zero_of_isPolyDegLE h hS

/-! ## The strict gap — the mother example: interaction degree exactly 1, nonclassical degree exactly 2 -/

/-- The mother example's interaction degree is `≤ 1` (vacuous over `Fin 1`). -/
theorem mobiusDegLE_one_motherExample : FTQCLib.Frame.MobiusDegLE 1 motherExample := by
  intro S hS
  have := Finset.card_le_univ S
  simp only [Fintype.card_fin] at this
  omega

/-- The mother example's interaction degree is **not** `≤ 0` — its order-1 Möbius coefficient is `1 ≠ 0`.
Together with `mobiusDegLE_one_motherExample`, the interaction degree is exactly `1`. -/
theorem not_mobiusDegLE_zero_motherExample : ¬ FTQCLib.Frame.MobiusDegLE 0 motherExample := by
  intro h
  have hc := h {0} (by decide)
  rw [show mobiusCoeff ({0} : Finset (Fin 1)) motherExample = 1 from by
    show funcDerivSubset ({0} : Finset (Fin 1)) motherExample 0 = 1
    rw [show ({0} : Finset (Fin 1)) = insert 0 ∅ from rfl,
      funcDerivSubset_insert (by simp), funcDerivSubset_empty, funcDerivG_apply]
    decide] at hc
  exact absurd hc (by decide)

/-- **The reverse implication fails — the two degrees genuinely differ.** At `d = 1` the mother example has
Möbius (interaction) degree `≤ 1` but nonclassical degree `> 1`; so `MobiusDegLE d ↛ IsPolyDegLE d`. With
`not_mobiusDegLE_zero_motherExample` and `motherExample_isPolyDegLE_two`: interaction degree `= 1`,
nonclassical degree `= 2`, and the gap is exactly the precision `m − 1 = 1`. -/
theorem mobiusDegLE_not_isPolyDegLE :
    FTQCLib.Frame.MobiusDegLE 1 motherExample ∧ ¬ IsPolyDegLE 1 motherExample :=
  ⟨mobiusDegLE_one_motherExample, motherExample_not_isPolyDegLE_one⟩

end FTQCLib.Bridge

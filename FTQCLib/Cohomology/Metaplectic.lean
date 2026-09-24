/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.FrameCochains
import FTQCLib.Hilbert.AffineSymplecticGroup
import FTQCLib.Hilbert.CliffordSplitN1
import FTQCLib.Hilbert.CliffordGroupAction

/-! # The metaplectic 2-cocycle on `Sp`

The composition layer of the cohomology of the frame. Single Clifford gates are tame (the cubic
ceiling); the hard cohomology is in how their sign cochains *compose* — the **metaplectic** class,
the obstruction to splitting the extension `Clₙ/U(1) → Sp(2n,𝔽₂)`.

This file gives the cohomological packaging: the `n = 1` vanishing, the precise *location* of the
obstruction (operator composition carries none; the obstruction is sectional), and
`MetaplecticNonSplit` as the `n ≥ 2` statement. At `n = 2` the obstruction is witnessed by a small
Klein-four subgroup (not the full Arf invariant): `metaplecticNonSplit_two` (in
`FTQCLib.Cohomology.MetaplecticWitness`) proves the `n = 2` extension non-split unconditionally, via
a computable faithful model of `Cl₂/U(1)` and the witness `S₀, CNOT₀→₁`. So the split/non-split
boundary is established on both sides.

A tempting argument for "non-split for `n ≥ 2`" is flawed: "the Weil representation does not
linearize over `Sp` ⟹ non-split" conflates the `U(1)`-central extension (Weil linearization) with
this `V`-extension (sectional splitting). `metaplectic_defect_is_sectional` below separates the
two. -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Hilbert

variable {n : ℕ}

/-- **The metaplectic obstruction vanishes** at level `n`: the extension `Clₙ/U(1) → Sp(2n,𝔽₂)`
admits a group-hom section — equivalently the metaplectic 2-cocycle is a coboundary, `[m] = 0`.
The cohomology-of-the-frame reading of `CliffordSectionExists`. -/
abbrev MetaplecticTrivial (n : ℕ) : Prop := CliffordSectionExists n

/-- **At `n = 1` the metaplectic class is trivial** — the extension splits
(`cliffordSectionExists_one`, the `S₃` complement `⟨[H], [X·S†]⟩`). The only `n = 1` defect is the
`ℤ/8` Gauss-sum global phase `(H·X·S†)³ = e^{iπ/4}·I`, which dies in `Clₙ/U(1)`; so the metaplectic
(Arf) class is `0` at `n = 1`. -/
theorem metaplecticTrivial_one : MetaplecticTrivial 1 := cliffordSectionExists_one

/-- **When the metaplectic class is trivial, `Clₙ/U(1) ≅ V ⋊ Sp(V)`** — the affine-symplectic form
of the split extension (realized unconditionally only at `n = 1`). -/
noncomputable def cliffordAffineEquivOfTrivial (h : MetaplecticTrivial n) :
    affineSymplecticGroup n ≃* cliffordModPhase n := cliffordAffineEquiv n h

/-- **The operator-level sign cochain carries no metaplectic defect.** Indexed by the Hilbert
*operators* `U, V`, `cliffordSign` is a strict crossed homomorphism — `cliffordSign_mul` has exactly
two sign factors, no 2-cocycle correction (operators compose strictly). So the metaplectic
obstruction lives entirely in the *section* `Sp → Cl/U(1)` — whether symplectic maps lift coherently
— NOT in operator composition. This pins the class's location, and separates this
`V`-extension's splitting from the `U(1)`-central Weil-linearization obstruction. -/
theorem metaplectic_defect_is_sectional {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) (p : Pauli n) :
    cliffordSign (isCliffordOperator_mul hU hV) p
      = cliffordSign hV p * cliffordSign hU (cliffordToSymplecticFun hV p) :=
  cliffordSign_mul hU hV p

/-- **The metaplectic obstruction for `n ≥ 2`.** For `n ≥ 2` the extension does NOT
split (Galindo 2026 arXiv:2603.24743; Mastel 2023 arXiv:2307.05810). At `n = 2`:
* **no element-order obstruction** — every cyclic subgroup of `Sp(4,2)` lifts to `Cl₂/U(1)` at the
  same order;
* but a small **`ℤ₂×ℤ₂` (Klein-four) obstruction** does exist — a commuting order-2 pair
  `a,b ∈ Sp(4,2)` (with `ab` order 2) with no commuting-involution lift.

So the proof needs only this small subgroup witness, *not* the full Arf invariant.

**The case `n = 2` is proved** (`metaplecticNonSplit_two` in
`FTQCLib.Cohomology.MetaplecticWitness`, axiom-clean): via a computable faithful model
`SignedSymplectic 2` of `Cl₂/U(1)` (`cliffordModPhase` itself being ℂ-analytic and
`decide`-blind), the faithful bridge `act : cliffordModPhase 2 →* SignedSymplectic 2`, and the
witness `a = S₀`, `b = CNOT₀→₁`. The no-lift is a short model-internal contradiction (the sign is
2-torsion), not the full Arf invariant. -/
def MetaplecticNonSplit (n : ℕ) : Prop := ¬ CliffordSectionExists n

/-- Consistency: `n = 1` is *not* non-split (it splits, by `metaplecticTrivial_one`). -/
theorem not_metaplecticNonSplit_one : ¬ MetaplecticNonSplit 1 :=
  fun h => h cliffordSectionExists_one

end FTQCLib.Cohomology

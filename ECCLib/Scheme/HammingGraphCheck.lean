/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingGraph

/-!
# Checks for the hypercube spectrum

Kernel rows recompute the `Q₃` and `Q₄` spectra against the literal `kraw` sum —
eigenvalues `3, 1, −1, −3` and `4, 2, 0, −2, −4` with multiplicities `C(n,w)` — plus the
handshakes (zero trace, dimensions filling `2ⁿ`) and a quaternary `H(2,4)` row for the
general-`q` shape. A **control** kernelises the domain guard: one step past `w ≤ n` the
degree-one closed form fails (`K₁` is `ℕ`-truncation junk there), so `dualWeight_le` in
the main theorem is load-bearing. The noncomputable main theorem and multiplicity rows
instantiate live at `Fin 3 → ZMod 2` under `AddAut (ZMod 2)` — character-indexed, so no
`decide`; non-vacuity is a concrete weight-`1` word.
-/

namespace ECCLib.Scheme

open Finset MulAction ECCLib.Delsarte

/-! ## The hypercube spectra, kernel-checked -/

/-- `Q₃`: the eigenvalue row `3, 1, −1, −3` from the literal Krawtchouk sum. -/
example : kraw 2 3 1 0 = 3 ∧ kraw 2 3 1 1 = 1 ∧ kraw 2 3 1 2 = -1 ∧ kraw 2 3 1 3 = -3 := by
  decide

/-- `Q₄`: the eigenvalue row `4, 2, 0, −2, −4`. -/
example : kraw 2 4 1 0 = 4 ∧ kraw 2 4 1 1 = 2 ∧ kraw 2 4 1 2 = 0 ∧ kraw 2 4 1 3 = -2 ∧
    kraw 2 4 1 4 = -4 := by decide

/-- `Q₃` handshakes: the multiplicity-weighted row is the zero trace, and the
multiplicities fill `2³`. -/
example : (∑ w ∈ Finset.range 4, ((3).choose w : ℤ) * kraw 2 3 1 w = 0) ∧
    (∑ w ∈ Finset.range 4, ((3).choose w : ℤ) = 8) := by decide

/-- `Q₄` handshakes. -/
example : (∑ w ∈ Finset.range 5, ((4).choose w : ℤ) * kraw 2 4 1 w = 0) ∧
    (∑ w ∈ Finset.range 5, ((4).choose w : ℤ) = 16) := by decide

/-- The general-`q` shape at quaternary `H(2,4)`: eigenvalues `6, 2, −2`, multiplicities
`C(2,w)·3^w = 1, 6, 9` filling `4²`, zero trace. -/
example : (kraw 4 2 1 0 = 6 ∧ kraw 4 2 1 1 = 2 ∧ kraw 4 2 1 2 = -2) ∧
    (∑ w ∈ Finset.range 3, ((2).choose w * 3 ^ w : ℤ) * kraw 4 2 1 w = 0) ∧
    (∑ w ∈ Finset.range 3, ((2).choose w * 3 ^ w : ℤ) = 16) := by decide

/-- Through `kraw_one` rather than by evaluation. -/
example (w : ℕ) (h : w ≤ 3) : kraw 2 3 1 w = ((2 : ℤ) - 1) * 3 - 2 * w :=
  kraw_one 2 3 w h

/-- **Control — the domain guard is load-bearing**: one step past `w ≤ n` the closed form
fails (`K₁(4)` at `n = 3` is `−4`, the naive line gives `−5`) — `dualWeight_le` in the
main theorem is what keeps the consumption on-domain. -/
example : ¬(kraw 2 3 1 4 = ((2 : ℤ) - 1) * 3 - 2 * 4) := by decide

/-! ## Non-vacuity: live rows at `Fin 3 → ZMod 2` under `AddAut (ZMod 2)` -/

/-- A weight-`1` word exists on the cube — the main theorem's `hammingNorm x = 1` hypothesis
is satisfiable. -/
example : hammingNorm (fun i : Fin 3 => if i = 0 then (1 : ZMod 2) else 0) = 1 := by
  decide

/-- The transitivity triviality, live at the binary alphabet. -/
example : TransOnNonzero (AddAut (ZMod 2)) (ZMod 2) := zmod_two_transOnNonzero

/-- **The hypercube spectrum, live at `Q₃`**: every hypothesis constructed — the split
character of a weight-`1` orbit adjacency at the spectral index of any dual orbit is
`3 − 2·(dual weight)`. -/
example (v : Fin 3 → ZMod 2) (hv : hammingNorm v = 1) (χ : AddChar (Fin 3 → ZMod 2) ℂ) :
    ECCLib.splitChar ℂ
      ↥(schemeAlgebra (↥(monomialSubgroup (Fin 3) (ZMod 2) (AddAut (ZMod 2))))
        (Fin 3 → ZMod 2))
      (translationSpectrumEquiv ⟨orb _ χ, orb_mem_orbits χ⟩)
      ⟨adj (orb _ v), adj_mem_schemeAlgebra (orb_mem_orbits v)⟩
      = (((Fintype.card (Fin 3) : ℤ) - 2 * dualWeight χ : ℤ) : ℂ) :=
  splitChar_adj_hypercube (orb_mem_orbits v) (self_mem_orb v) hv _ (self_mem_orb χ)

/-- **The hypercube multiplicities, live at `Q₃`**: the eigenspace of dual weight `w` has
dimension `C(3,w)`. -/
example (χ : AddChar (Fin 3 → ZMod 2) ℂ) :
    spectralMult (schemeAlgebra (↥(monomialSubgroup (Fin 3) (ZMod 2) (AddAut (ZMod 2))))
        (Fin 3 → ZMod 2))
        (translationSpectrumEquiv ⟨orb _ χ, orb_mem_orbits χ⟩)
      = (Fintype.card (Fin 3)).choose (dualWeight χ) :=
  spectralMult_hypercube _ (self_mem_orb χ)

/-- The general-`q` main theorem instantiates at the Klein (Pauli) alphabet via
`klein_transOnNonzero`. -/
example (v : Fin 3 → ZMod 2 × ZMod 2) (hv : hammingNorm v = 1)
    (χ : AddChar (Fin 3 → ZMod 2 × ZMod 2) ℂ) :
    ECCLib.splitChar ℂ
      ↥(schemeAlgebra
        (↥(monomialSubgroup (Fin 3) (ZMod 2 × ZMod 2) (AddAut (ZMod 2 × ZMod 2))))
        (Fin 3 → ZMod 2 × ZMod 2))
      (translationSpectrumEquiv ⟨orb _ χ, orb_mem_orbits χ⟩)
      ⟨adj (orb _ v), adj_mem_schemeAlgebra (orb_mem_orbits v)⟩
      = ((((Fintype.card (ZMod 2 × ZMod 2) : ℤ) - 1) * Fintype.card (Fin 3)
          - Fintype.card (ZMod 2 × ZMod 2) * dualWeight χ : ℤ) : ℂ) :=
  splitChar_adj_hammingGraph klein_transOnNonzero (orb_mem_orbits v) (self_mem_orb v) hv
    _ (self_mem_orb χ)

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.splitChar_adj_hammingGraph' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.splitChar_adj_hammingGraph

/-- info: 'ECCLib.Scheme.zmod_two_transOnNonzero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.zmod_two_transOnNonzero

/-- info: 'ECCLib.Scheme.splitChar_adj_hypercube' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.splitChar_adj_hypercube

/-- info: 'ECCLib.Scheme.spectralMult_hypercube' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.spectralMult_hypercube

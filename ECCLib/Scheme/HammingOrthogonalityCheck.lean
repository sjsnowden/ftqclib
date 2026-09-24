/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.HammingOrthogonality

/-!
# Acceptance rows for the Krawtchouk orthogonality

The identity is decidable arithmetic: kernel rows check the binary `n = 3` and quaternary
`n = 2` (Klein-scale) instances against the literal `kraw`, with a **control** refuting a
wrong diagonal. The live row instantiates the theorem at the Klein (Pauli) alphabet through
`klein_transOnNonzero` — every hypothesis constructed.
-/

namespace ECCLib.Scheme

open Finset ECCLib.Delsarte

/-- Binary, `n = 3`, diagonal `i = j = 1`: `2³ · C(3,1) = 24`. -/
example : ∑ w ∈ Finset.range (3 + 1),
    ((Nat.choose 3 w * (2 - 1) ^ w : ℕ) : ℤ) * (kraw 2 3 1 w * kraw 2 3 1 w)
      = 24 := by decide

/-- Binary, `n = 3`, off-diagonal `i = 1, j = 2`: orthogonality. -/
example : ∑ w ∈ Finset.range (3 + 1),
    ((Nat.choose 3 w * (2 - 1) ^ w : ℕ) : ℤ) * (kraw 2 3 1 w * kraw 2 3 2 w)
      = 0 := by decide

/-- Quaternary, `n = 2`, diagonal `i = j = 1`: `4² · C(2,1) · 3 = 96`. -/
example : ∑ w ∈ Finset.range (2 + 1),
    ((Nat.choose 2 w * (4 - 1) ^ w : ℕ) : ℤ) * (kraw 4 2 1 w * kraw 4 2 1 w)
      = 96 := by decide

/-- Quaternary, `n = 2`, off-diagonal `i = 0, j = 2`: orthogonality. -/
example : ∑ w ∈ Finset.range (2 + 1),
    ((Nat.choose 2 w * (4 - 1) ^ w : ℕ) : ℤ) * (kraw 4 2 0 w * kraw 4 2 2 w)
      = 0 := by decide

/-- **Control**: the wrong diagonal value is refuted. -/
example : ¬(∑ w ∈ Finset.range (3 + 1),
    ((Nat.choose 3 w * (2 - 1) ^ w : ℕ) : ℤ) * (kraw 2 3 1 w * kraw 2 3 1 w)
      = 0) := by decide

/-- **The theorem instantiates at the Klein (Pauli) alphabet**, every hypothesis
constructed: `A = ZMod 2 × ZMod 2` under its automorphisms, `n = 2`. -/
example : ∑ w ∈ Finset.range (Fintype.card (Fin 2) + 1),
    ((Fintype.card (Fin 2)).choose w
        * (Fintype.card (ZMod 2 × ZMod 2) - 1) ^ w : ℕ)
      * ((kraw (Fintype.card (ZMod 2 × ZMod 2)) (Fintype.card (Fin 2)) 1 w : ℤ)
          * kraw (Fintype.card (ZMod 2 × ZMod 2)) (Fintype.card (Fin 2)) 2 w)
    = if 1 = 2
        then ((Fintype.card (ZMod 2 × ZMod 2) ^ Fintype.card (Fin 2)
            * ((Fintype.card (Fin 2)).choose 1
                * (Fintype.card (ZMod 2 × ZMod 2) - 1) ^ 1) : ℕ) : ℤ)
        else 0 :=
  kraw_orthogonality (ι := Fin 2) klein_transOnNonzero (by norm_num)
    (by norm_num) (by norm_num)

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.exists_dualWeight_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.exists_dualWeight_eq

/-- info: 'ECCLib.Scheme.dualWeight_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.dualWeight_le

/-- info: 'ECCLib.Scheme.shellSet_mem_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.shellSet_mem_orbits

/-- info: 'ECCLib.Scheme.kraw_orthogonality' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.kraw_orthogonality

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.FourierBridge
import Mathlib.Data.ZMod.Basic

/-!
# Checks for the spectral layer

Three kinds of row (nothing indexed by characters is decided):

* **The representative-independence guard**: the class `{1,2}` on `ZMod 4` is NOT an orbit
  of any additive-automorphism group (`c12 ∉ orbits (ZMod 4)ˣ (ZMod 4)` — and `AddAut (ZMod 4)
  ≃* (ZMod 4)ˣ`), and its structure constant is REPRESENTATIVE-DEPENDENT (`0` at `1`, `1` at
  `2`); the genuine orbit `{1,3}` is consistent at both representatives. This shows that
  the orbit structure — not merely a partition — is what makes the algebra close.
* **Normalisation fingerprints**, theorem-proved on explicitly constructed characters: `eig`
  and `pEnt` at the trivial character count points (plain sums, no `|V|⁻¹`).
* **The axiom sweep** on the main theorems, build-failing.
-/

namespace ECCLib.Scheme

open Finset

/-- The non-orbit class `{1,2} ⊆ ZMod 4`. -/
def c12 : Finset (ZMod 4) := {1, 2}
/-- The genuine `(ZMod 4)ˣ`-orbit `{1,3} ⊆ ZMod 4`. -/
def c13 : Finset (ZMod 4) := {1, 3}

/-- `{1,3}` IS an orbit of the units. -/
example : c13 ∈ orbits (ZMod 4)ˣ (ZMod 4) := by decide
/-- `{1,2}` is NOT. -/
example : c12 ∉ orbits (ZMod 4)ˣ (ZMod 4) := by decide
/-- The representative-independence guard: the structure constant `p^{c12}_{c12,c12}` at the
representative `1` … -/
example : (univ.filter fun z : ZMod 4 => z ∈ c12 ∧ (1 - z : ZMod 4) ∈ c12).card = 0 := by
  decide
/-- … and at the representative `2` — DIFFERENT. -/
example : (univ.filter fun z : ZMod 4 => z ∈ c12 ∧ (2 - z : ZMod 4) ∈ c12).card = 1 := by
  decide
/-- On the genuine orbit `{1,3}` the count agrees at both representatives. -/
example : (univ.filter fun z : ZMod 4 => z ∈ c13 ∧ (1 - z : ZMod 4) ∈ c13).card = 0 := by
  decide
example : (univ.filter fun z : ZMod 4 => z ∈ c13 ∧ (3 - z : ZMod 4) ∈ c13).card = 0 := by
  decide

/-- Normalisation fingerprint: `eig 1 (trivial character) = |V|` (plain sum). -/
example : eig (fun _ : ZMod 3 => (1 : ℂ)) (0 : AddChar (ZMod 3) ℂ) = 3 := by
  simp [eig, Finset.card_univ, ZMod.card]
/-- Normalisation fingerprint: `pEnt univ (trivial character) = |V|`. -/
example : pEnt (Finset.univ : Finset (ZMod 3)) (0 : AddChar (ZMod 3) ℂ) = 3 := by
  simp [pEnt, Finset.card_univ, ZMod.card]

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.circulant_mulVec_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.circulant_mulVec_char

/-- info: 'ECCLib.Scheme.charProj_mulVec_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.charProj_mulVec_char

/-- info: 'ECCLib.Scheme.completeOrthogonalIdempotents_charProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.completeOrthogonalIdempotents_charProj

/-- info: 'ECCLib.Scheme.completeOrthogonalIdempotents_orbProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.completeOrthogonalIdempotents_orbProj

/-- info: 'ECCLib.Scheme.PQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.PQ_eq

/-- info: 'ECCLib.Scheme.adj_eq_sum_orbProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.adj_eq_sum_orbProj

/-- info: 'ECCLib.Scheme.orbProj_eq_sum_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbProj_eq_sum_adj

/-- info: 'ECCLib.Scheme.eig_eq_card_mul_fourierT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.eig_eq_card_mul_fourierT

/-- info: 'ECCLib.Scheme.adj_mul_charProj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.adj_mul_charProj

/-- info: 'ECCLib.Scheme.adj_mul_orbProj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.adj_mul_orbProj

/-- info: 'ECCLib.Scheme.trace_charProj' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.trace_charProj

/-- info: 'ECCLib.Scheme.orb_neg' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orb_neg

/-- info: 'ECCLib.Scheme.mem_image_neg' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.mem_image_neg

/-- info: 'ECCLib.Scheme.image_neg_mem_orbits' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.image_neg_mem_orbits

/-- info: 'ECCLib.Scheme.image_neg_image_neg' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.image_neg_image_neg

/-- info: 'ECCLib.Scheme.trace_adj_mul_adj' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.trace_adj_mul_adj

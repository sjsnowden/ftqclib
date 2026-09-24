/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.OrbitalPositivity

/-!
# Acceptance rows for the orbital Delsarte inequality

`orbCount` is computable, so its arithmetic is kernel-checked here on concrete carriers
(against `#`-filters, the square fingerprint's shape, and the C2 Kneser orbital); the
noncomputable identity and inequality instantiate live, with every hypothesis
constructed, in `Scheme/JohnsonDelsarteCheck.lean` at the Johnson carrier. The controls
for the inequality itself — a sign flip is refuted by a concrete code — are the ℚ-mirror
rows there.
-/

namespace ECCLib.Scheme

open Finset

/-- `orbCount` at concrete data: on `Fin 3`, pairs of `C = {0,1}` meeting the strict
upper triangle. -/
example : orbCount ({0, 1} : Finset (Fin 3))
    (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 < p.2) = 1 := by decide

/-- `orbCount` at the diagonal: one pair per element of `C`. -/
example : orbCount ({0, 2} : Finset (Fin 3))
    (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 = p.2) = 2 := by decide

/-- `orbCount` over everything is the square — the fingerprint's shape at a concrete
carrier (here as one set, before the orbital partition refines it). -/
example : orbCount ({0, 1} : Finset (Fin 3)) Finset.univ = 4 := by decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.conjTranspose_coe_orbitalIdem' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.conjTranspose_coe_orbitalIdem

/-- info: 'ECCLib.Scheme.posSemidef_coe_orbitalIdem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.posSemidef_coe_orbitalIdem

/-- info: 'ECCLib.Scheme.orbCount' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.orbCount

/-- info: 'ECCLib.Scheme.filter_mem_orbital_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.filter_mem_orbital_eq

/-- info: 'ECCLib.Scheme.sum_orbCount' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_orbCount

/-- info: 'ECCLib.Scheme.sum_orbCount_mul_eigenmatrixQ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_orbCount_mul_eigenmatrixQ

/-- info: 'ECCLib.Scheme.sum_pair_eq_dotProduct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.sum_pair_eq_dotProduct

/-- info: 'ECCLib.Scheme.delsarte_nonneg_orbital' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.delsarte_nonneg_orbital

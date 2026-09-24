/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.JohnsonDelsarte
import ECCLib.Scheme.Kneser

/-!
# Checks for the constant-weight Delsarte inequality

The `Q`-matrix of `J(4,2)` is integral — rows `(1,3,2)`, `(1,0,−1)`, `(1,−3,2)` — and the
kernel checks it cell by cell against the division-free identification
`C(k,d)·C(n−k,d)·Q(d,j) = m_j·E_d(j)` with the multiplicities in their closed form. The
LP rows then run on a concrete code: the **star** `{01, 02, 03} ⊆ J(4,2)`, inner
distribution `B = (3, 6, 0)` (each `B_d` re-counted by `orbCount` itself, so the numbers
carry their own provenance), satisfies every inequality and attains **equality at
`j = 2`** — a maximal intersecting family sitting on the LP boundary. The full carrier
attains equality at every `j ≠ 0`. The **control** kernelises the sign structure: with
`Q(0,1)` negated, the single-vertex code already violates the "inequality", so the rows
test the actual table, not a tautology. The noncomputable main theorem and identification
instantiate live at `J(4,2)`, every hypothesis constructed.
-/

namespace ECCLib.Scheme.Johnson

open Finset ECCLib.Delsarte
open scoped ComplexOrder

/-- The second eigenmatrix of `J(4,2)`, as a literal table (rows `d`, columns `j`). -/
def qJ42 : Fin 3 → Fin 3 → ℤ := ![![1, 3, 2], ![1, 0, -1], ![1, -3, 2]]

/-- **The division-free identification, cell by cell**: `C(2,d)·C(2,d)·Q(d,j) = m_j·E_d(j)`
at `J(4,2)`, multiplicities in their closed form. -/
example : ∀ d j : Fin 3, (((2).choose d * (2).choose d : ℕ) : ℤ) * qJ42 d j
    = (if (j : ℕ) = 0 then 1 else ((4).choose (j : ℕ) : ℤ) - (4).choose ((j : ℕ) - 1))
      * eberlein 4 2 (d : ℕ) (j : ℕ) := by decide

/-! ## The star `{01, 02, 03}`: inner distribution and the LP rows -/

/-- `B₀ = 3`: the diagonal pairs, re-counted by `orbCount` at the intersection-`2` class. -/
example : orbCount ({⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩}
      : Finset (KSub 4 2))
    (Finset.univ.filter fun p : KSub 4 2 × KSub 4 2 => interCard p = 2) = 3 := by decide

/-- `B₁ = 6`: the distance-one pairs. -/
example : orbCount ({⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩}
      : Finset (KSub 4 2))
    (Finset.univ.filter fun p : KSub 4 2 × KSub 4 2 => interCard p = 1) = 6 := by decide

/-- `B₂ = 0`: the star is intersecting — no disjoint pairs. -/
example : orbCount ({⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩}
      : Finset (KSub 4 2))
    (Finset.univ.filter fun p : KSub 4 2 × KSub 4 2 => interCard p = 0) = 0 := by decide

/-- **The star satisfies every Delsarte inequality** at `J(4,2)`. -/
example : ∀ j : Fin 3, (0 : ℤ) ≤ 3 * qJ42 0 j + 6 * qJ42 1 j + 0 * qJ42 2 j := by decide

/-- **The star attains LP equality at `j = 2`** — a maximal intersecting family on the
boundary of the Delsarte polytope. -/
example : 3 * qJ42 0 2 + 6 * qJ42 1 2 + 0 * qJ42 2 2 = 0 := by decide

/-- The full carrier (`B` = the orbital sizes `6, 24, 6`) attains equality at every
`j ≠ 0` and `|X|² = 36` at `j = 0`. -/
example : ∀ j : Fin 3, 6 * qJ42 0 j + 24 * qJ42 1 j + 6 * qJ42 2 j
    = if j = 0 then 36 else 0 := by decide

/-- **Control — the sign structure is load-bearing**: with `Q(0,1)` negated the
single-vertex code (`B = (1,0,0)`) already violates the "inequality", so the rows above
test the actual table rather than holding vacuously. -/
example : ¬((0 : ℤ) ≤ 1 * (-(qJ42 0 1)) + 0 * qJ42 1 1 + 0 * qJ42 2 1) := by decide

/-- The Kneser tie-in: `orbCount` of the whole carrier at the Kneser orbital of `J(5,2)` is
its edge count. -/
example : orbCount (Finset.univ : Finset (KSub 5 2)) (kneserSet 5 2) = 30 := by decide

/-! ## Non-vacuity: live rows at `J(4,2)` -/

section Live

local instance kSub42DelsarteNonempty : Nonempty (KSub 4 2) := KSub.nonempty (by norm_num)

/-- **The constant-weight Delsarte inequality, live at `J(4,2)`**: every hypothesis
constructed, any code, any spectral index. -/
example (C : Finset (KSub 4 2)) (j : Fin (min 2 (4 - 2) + 1)) :
    0 ≤ ∑ Ω : ↥(orbits (Equiv.Perm (Fin 4)) (KSub 4 2 × KSub 4 2)),
        (orbCount C (Ω : Finset (KSub 4 2 × KSub 4 2)) : ℂ)
          * eigenmatrixQ Ω (johnsonSpectrumEquiv j) :=
  delsarte_nonneg_johnson C j

/-- The division-free identification, live at `J(4,2)`. -/
example (Ω : ↥(orbits (Equiv.Perm (Fin 4)) (KSub 4 2 × KSub 4 2)))
    (j : Fin (min 2 (4 - 2) + 1)) :
    (((2).choose (2 - orbWidth Ω) * (4 - 2).choose (2 - orbWidth Ω) : ℕ) : ℂ)
        * eigenmatrixQ Ω (johnsonSpectrumEquiv j)
      = (spectralMult (orbitalAlgebra ℂ (Equiv.Perm (Fin 4)) (KSub 4 2))
            (johnsonSpectrumEquiv j) : ℂ)
          * ((eberlein 4 2 (2 - orbWidth Ω) (j : ℕ) : ℤ) : ℂ) :=
  choose_mul_eigenmatrixQ_johnson Ω j

/-- The square fingerprint, live at the Johnson carrier. -/
example (C : Finset (KSub 4 2)) :
    ∑ Ω : ↥(orbits (Equiv.Perm (Fin 4)) (KSub 4 2 × KSub 4 2)),
      orbCount C (Ω : Finset (KSub 4 2 × KSub 4 2)) = #C ^ 2 :=
  sum_orbCount C

/-- The idempotents are positive semidefinite, live at the Johnson carrier. -/
example (I : MaximalSpectrum
    ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin 4)) (KSub 4 2))) :
    ((orbitalIdem I : ↥(orbitalAlgebra ℂ (Equiv.Perm (Fin 4)) (KSub 4 2)))
      : Matrix (KSub 4 2) (KSub 4 2) ℂ).PosSemidef :=
  posSemidef_coe_orbitalIdem I

end Live

end ECCLib.Scheme.Johnson

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.Johnson.qJ42' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.qJ42

/-- info: 'ECCLib.Scheme.Johnson.choose_mul_eigenmatrixQ_johnson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.choose_mul_eigenmatrixQ_johnson

/-- info: 'ECCLib.Scheme.Johnson.delsarte_nonneg_johnson' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.delsarte_nonneg_johnson

/-- info: 'ECCLib.Scheme.Johnson.kSub42DelsarteNonempty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.Johnson.kSub42DelsarteNonempty

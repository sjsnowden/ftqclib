/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseDyadic
import FTQCLib.Hilbert.CGKReverseAnchor

set_option linter.unusedSectionVars false

/-! # CGK reverse — level-one assembly

The polynomial-encoding half of the CGK equivalence at low levels: a
diagonal unitary `U` at level `k` of the **dyadic** operational Clifford
hierarchy admits a polynomial-phase encoding `U = diagonalGateEquiv
(realPhase P)` with a controlled bound on `P.level`.

## What this file delivers

* **`cgk_reverse_dyadic_level_one_pm`** — the `±1`-phase level-1 case
  matching `P.level ≤ k = 1`, packaging `cgk_reverse_one_signed`
  against `IsCliffordHierarchyDyadic`.

* **`IsCliffordHierarchyTight`** — a refinement of
  `IsCliffordHierarchyDyadic` that requires the base-case scalar to be
  `±1` (precision m' ≤ 1). Under this restriction, the level-1 reverse
  direction `cgk_reverse_tight_level_one` matches `P.level ≤ k` exactly.

* **`cgk_reverse_dyadic_phase_dyadic_level_one`** and
  **`cgk_reverse_dyadic_phase_dyadic_level_two`** — pointwise
  dyadicity of the phase function at levels 1 and 2.

## General levels

At `k = 1` the reverse direction reduces (by the structural lemma
`Pauli_X_zero_of_diagonal_phasedPauli`) to the `±1`-phase case
`cgk_reverse_dyadic_level_one_pm`. For general `k` the argument runs:

1. **Descent** (`CGKReverseDyadic.lean`'s
   `diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`):
   for `|S| < k`, `D_{Δ_S f} ∈ IsCliffordHierarchyDyadic (k − |S|)`.
2. **Möbius coefficient dyadicity**: for each nonempty `S`,
   `mobiusPhaseCoeff S f` is dyadic mod 2π
   (`mobiusCoeff_dyadic_mod_2pi_level_k` in `CGKReverseGeneral.lean`).
3. **Möbius inversion** (`BooleanMobius.lean`'s `eq_sum_mobiusCoeff`):
   reconstruct `f(v) = Σ_{S ⊆ supp v} c_S` from the dyadic
   coefficients.
4. **Polynomial assembly**: `P = Σ_S (c_S · 2^m / 2π) · ∏_{i ∈ S} X_i`
   over `ZMod (2^m)`.

The resulting witnesses are `cgk_reverse_dyadic_poly_general`
(`CGKReverseGeneral.lean`), the degree-`≤ k` witness
`cgk_reverse_dyadic_poly_mobius_general` (`CGKReverseTightLevel.lean`),
and the sharp projective form `cgk_reverse_projective_sharp`
(`CGKTwoSided.lean`): up to a global phase, a constant-free multilinear
witness at precision `k` with `effectiveLevel ≤ k`.

## Anchors

* CGK 2017 (arXiv:1608.06596) Theorem 2 (single qudit), Lemma 4
  (n-qudit), eq. (62) (level formula at p = 2: `w = (m−1) + d`).
* Gottesman–Chuang 1999 (arXiv:quant-ph/9908010) — operational
  hierarchy definition.
* Rota 1964 — Möbius inversion on locally finite posets.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## Level 1, `±1` global phase (`P.level ≤ k = 1`)

The simplest case of CGK reverse against `IsCliffordHierarchyDyadic`:
when the level-1 scalar is `±1`, the polynomial witness
`phaseAndZPoly c p` at precision 1 has `P.level ≤ 1`. This packages
`cgk_reverse_one_signed` against the dyadic hierarchy. -/

/-- **Level-1 reverse direction with `±1` global phase.** For a
diagonal `U` at level 1 of the dyadic hierarchy whose phased-Pauli
witness has the form `α = (-1)^c.val` for some `c : ZMod 2`, there is a
polynomial witness at precision 1 with `P.level ≤ 1`.

Direct corollary of `cgk_reverse_one_signed`.

Anchor: CGK 2017 Theorem 2, page 3, specialised to `p = 2` and
restricted to base-case phase ∈ {1, −1}. -/
theorem cgk_reverse_dyadic_level_one_pm
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    {α : ℂˣ} {p : Pauli n}
    (hα_eq : U.toLinearMap = (α : ℂ) • (pauliOperator p))
    {c : ZMod 2} (hα_sign : (α : ℂ) = (-1 : ℂ) ^ c.val) :
    ∃ (m' : ℕ) (P : DiagPhase n m'),
      U = diagonalGateEquiv (DiagPhase.realPhase P) ∧
      P.level ≤ 1 :=
  cgk_reverse_one_signed h_diag hα_eq hα_sign

/-! ## The tight dyadic hierarchy

`IsCliffordHierarchyDyadicTight k U` is a refinement of
`IsCliffordHierarchyDyadic k U` that bounds the base-case scalar
precision. Specifically: at the base (level 1), the scalar `α` must
satisfy `(α : ℂ) ∈ {1, -1}`, i.e., be representable at precision 1.

This restriction is the natural CGK setting: every operator at level
1 of the **physical** Clifford hierarchy is a phased Pauli with phase
±1 (no global phase factors of `i` etc. — those would be Hadamard
conjugates of higher-level objects, hence at level ≥ 2 of the
hierarchy on the standard Pauli generators).

Under `IsCliffordHierarchyTight`, the level-1 reverse direction closes
with `P.level ≤ k = 1` exactly.

For `k ≥ 2`, see `CGKReverseGeneral.lean`: there the anchor `g(0)`
dyadic is a hypothesis, since it is not automatic above tight level 1. -/

/-- A dyadic-phased Pauli at the **tight** precision: the scalar is
`±1`. -/
def IsPhasedPauliTight (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : Prop :=
  ∃ (c : ZMod 2) (p : Pauli n),
    U.toLinearMap = ((-1 : ℂ) ^ c.val) • (pauliOperator p)

/-- A tight phased Pauli is in particular a dyadic phased Pauli. -/
theorem IsPhasedPauliTight.toIsPhasedPauliDyadic
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (h : IsPhasedPauliTight U) :
    IsPhasedPauliDyadic U := by
  obtain ⟨c, p, hα⟩ := h
  -- Construct the unit (-1)^c.val.
  have hne : ((-1 : ℂ) ^ c.val) ≠ 0 := by
    refine pow_ne_zero _ ?_
    norm_num
  refine ⟨Units.mk0 ((-1 : ℂ) ^ c.val) hne, p,
          isDyadicScalar_neg_one_pow c.val hne, ?_⟩
  rw [Units.val_mk0]
  exact hα

/-- The operational Clifford hierarchy on `QubitSpace n` with the
**tight** dyadic restriction: base-case scalars are restricted to
`±1`.

* `base`: at level 1, every tight phased Pauli `U` (i.e.
  `U.toLinearMap = (-1)^c.val • pauliOperator p` for some
  `c : ZMod 2`) sits in the hierarchy.
* `step`: at level `k+1`, recursion via Pauli conjugation. -/
inductive IsCliffordHierarchyTight :
    ℕ → (QubitSpace n ≃ₗ[ℂ] QubitSpace n) → Prop where
  | base {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (h : IsPhasedPauliTight U) :
      IsCliffordHierarchyTight 1 U
  | step {k : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
      (h : ∀ p : Pauli n,
        IsCliffordHierarchyTight k (conjEquiv U (pauliEquiv p))) :
      IsCliffordHierarchyTight (k + 1) U

/-- The tight hierarchy implies the loose dyadic hierarchy. -/
theorem IsCliffordHierarchyTight.toCliffordHierarchyDyadic {k : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyTight k U) :
    IsCliffordHierarchyDyadic k U := by
  induction h with
  | base hU => exact .base hU.toIsPhasedPauliDyadic
  | step _ ih => exact .step (fun q => ih q)

/-- The tight hierarchy implies the loose (untight) operational
hierarchy. Direct consequence of `toCliffordHierarchyDyadic` plus
`IsCliffordHierarchyDyadic.toCliffordHierarchy`. -/
theorem IsCliffordHierarchyTight.toCliffordHierarchy {k : ℕ}
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyTight k U) :
    IsCliffordHierarchy k U :=
  h.toCliffordHierarchyDyadic.toCliffordHierarchy

/-! ## Tight hierarchy, level 1 (`P.level ≤ k = 1`)

For `IsCliffordHierarchyTight 1 U` with diagonal `U`, the polynomial
witness is `phaseAndZPoly c p` at precision 1, level ≤ 1. This gives
`P.level ≤ k` against the tight operational predicate. -/

/-- **Reverse direction, tight hierarchy, level 1.** A diagonal
`U` at level 1 of the tight Clifford hierarchy admits a polynomial
witness at precision 1 with `P.level ≤ k = 1`.

Anchor: CGK 2017 Theorem 2 (page 3), specialised to `p = 2` (qubits).
The phase function of a level-1 tight dyadic phased Pauli is
multilinear of degree ≤ 1 in `(F₂)ⁿ`. -/
theorem cgk_reverse_tight_level_one
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_hier : IsCliffordHierarchyTight 1 U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      U = diagonalGateEquiv (DiagPhase.realPhase P) ∧
      P.level ≤ 1 := by
  -- Unpack the level-1 witness. The .step constructor produces level
  -- (k+1) ≥ 2, so the level-1 case is .base only.
  generalize hk_eq : (1 : ℕ) = klvl at h_hier
  cases h_hier with
  | base hU =>
    obtain ⟨c, p, hα_eq⟩ := hU
    -- α = (-1)^c.val. Apply cgk_reverse_dyadic_level_one_pm.
    -- The hypothesis hα_eq has the form
    --   U.toLinearMap = (-1)^c.val • pauliOperator p,
    -- which is exactly the input form of cgk_reverse_one_signed (up to
    -- the trivial `Units.mk0 ((-1)^c.val) hne` packaging).
    have hne : ((-1 : ℂ) ^ c.val) ≠ 0 := by
      refine pow_ne_zero _ ?_
      norm_num
    set α : ℂˣ := Units.mk0 ((-1 : ℂ) ^ c.val) hne with hα_def
    have hα_pkg : U.toLinearMap = (α : ℂ) • (pauliOperator p) := by
      rw [hα_def, Units.val_mk0]
      exact hα_eq
    have hα_sign : (α : ℂ) = (-1 : ℂ) ^ c.val := by
      rw [hα_def, Units.val_mk0]
    exact cgk_reverse_one_signed h_diag hα_pkg hα_sign
  | @step kpred _ h =>
    -- klvl = 1 forces kpred = 0; level 0 is uninhabited.
    have hk0 : kpred = 0 := by omega
    subst hk0
    -- h : ∀ p, IsCliffordHierarchyTight 0 _, which is uninhabited.
    cases h 0

/-! ## General `k`

For `k ≥ 2` the unscaled statement against `IsCliffordHierarchyTight`
would read

```
theorem cgk_reverse_dyadic {n : ℕ}
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) {k : ℕ}
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_hier : IsCliffordHierarchyTight k U) :
    ∃ (m : ℕ) (P : DiagPhase n m),
      U = diagonalGateEquiv (DiagPhase.realPhase P) ∧
      P.level ≤ k
```

It is not proved in this library: at tight level `k ≥ 2` the global
phase `g(0)` is not constrained by the recursive `.step` rule. The
general-level results are the anchored ones in `CGKReverseGeneral.lean`
and the projective form `cgk_reverse_projective_sharp` in
`CGKTwoSided.lean`.

### Why descent alone gives only derivative information

The descent theorem
`diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic`
in `CGKReverseDyadic.lean` says: for `|S| < k`,
`diagonalGateEquiv (funcDerivPhaseSubset S f) ∈ level (k − |S|)`. At
the top of descent (`|S| = k − 1`, level 1),
`isDyadicMod2pi_of_level_one_diagonal` gives the value at `v = 0`
dyadic mod 2π. For `|S| < k − 1` the descent lands at level `≥ 2`.

Conjugating `D_g = diagonalGateEquiv g` by `pauliEquiv q` does not
produce a pure shift `D_{g(· + q.X)}`. The identity
(`conjEquiv_diagonalGateEquiv_general` in `CGKForward.lean`) is

  `conjEquiv (D_g) (pauliEquiv q) =
    (D_{Δ_{q.X} g}).trans (pauliEquiv q)`

where `Δ_{q.X} g(v) = g(v + q.X) - g(v)`. The trailing X-Pauli (basis
shift) prevents reading the conjugate as a pure diagonal, so it yields
derivative information, not function values at non-zero `v`. The
general-level argument in `CGKReverseGeneral.lean` recovers the Möbius
coefficients instead from the mod-2 identity `Δ_i Δ_i g = -2 · Δ_i g`
together with halving. -/

/-! ## Level-2 structural closure

`CGKReverseAnchor.lean` proves the structural anchor at level 2: given
a diagonal `U` at level 2 of the dyadic hierarchy **and** `g(0)` dyadic
mod 2π, the phase function `g(v)` is dyadic mod 2π for every `v`. The
result is exposed here as `cgk_reverse_dyadic_phase_dyadic_level_two`.

The full polynomial-assembly statement
```
∃ m P, U = diagonalGateEquiv (realPhase P) ∧ P.level ≤ k
```
at `k = 2` against the LOOSE dyadic hierarchy is false in general
(because `g(0)` can have arbitrarily-high precision at level ≥ 2 of the
loose hierarchy, forcing `P.level` to scale with that precision). The
anchored version below produces dyadic-phase **values**; polynomial
witnesses are constructed in `CGKReverseGeneral.lean` and
`CGKReverseTightLevel.lean`.

Source: `isDyadicMod2pi_of_level_two_diagonal_anchored` in
`CGKReverseAnchor.lean`, which assembles the level-2 Möbius-coefficient
dyadicity (`mobiusCoeff_dyadic_mod_2pi_level_two`) plus Möbius
inversion (`BooleanMobius.eq_sum_mobiusCoeff`). -/

/-- **Level-2 structural closure (anchored).** For a diagonal `U =
diagonalGateEquiv g` at level 2 of the dyadic hierarchy with `g(0)`
dyadic mod 2π, every `g(v)` is dyadic mod 2π.

This is the structural anchor lemma. Polynomial witnesses
`∃ m P, U = diagonalGateEquiv (realPhase P)` are constructed in
`CGKReverseGeneral.lean`.

Anchor: CGK 2017 (arXiv:1608.06596) §III Lemma 2 eq (50)–(51) at
`p = 2`; Möbius inversion (Rota 1964). -/
theorem cgk_reverse_dyadic_phase_dyadic_level_two
    {n : ℕ} {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 2 (diagonalGateEquiv g))
    (h_zero : IsDyadicMod2pi (g 0)) :
    ∀ v, IsDyadicMod2pi (g v) :=
  isDyadicMod2pi_of_level_two_diagonal_anchored h_hier h_zero

/-- **Level-1 structural closure.** For a diagonal `U = diagonalGateEquiv g`
at level 1 of the dyadic hierarchy, every `g(v)` is dyadic mod 2π.

Unconditional at level 1 (the level-1 base case forces `g(0)` dyadic
as a structural property of the phased-Pauli witness).

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 2 base case at `p = 2`;
`isDyadicMod2pi_of_level_one_diagonal` extended to all `v`. -/
theorem cgk_reverse_dyadic_phase_dyadic_level_one
    {n : ℕ} {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g)) :
    ∀ v, IsDyadicMod2pi (g v) :=
  isDyadicMod2pi_of_level_one_diagonal_all_v h_hier

end FTQCLib.Hilbert

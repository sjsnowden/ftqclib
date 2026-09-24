/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKForward
import FTQCLib.Hilbert.CGKReverseDyadic

set_option linter.unusedSectionVars false

/-! # The polynomial-encodable sub-hierarchy (strict CGK reverse)

The operator-side `IsCliffordHierarchy k U` predicate from
`FTQCLib/Hilbert/Hierarchy.lean` is **invariant under arbitrary global
phase scaling** through its `.step` constructor: `conjEquiv (e^{ic} V) q
= conjEquiv V q`, since the phase scalar cancels. So even refinements
like `IsCliffordHierarchyTight` (which restricts the
base-case scalar to `±1`) admit, at `.step` level `k ≥ 2`, operators
of the form `e^{ic} · I` for arbitrary `c : ℝ`. In particular, the
statement "`U ∈ C^k` ⇒ the phase function `g(v)` is dyadic mod `2π`
for every `v`" is **false** at `k ≥ 2` against `IsCliffordHierarchyTight`.

The remedy is to identify the sub-predicate that **does** admit
unconditional pointwise dyadicity: the **polynomial-encodable** diagonal
operators. This is essentially the polynomial framework, packaged as a
single existential. Concretely:

`IsCliffordHierarchyPolyEncodable k U ↔ ∃ m P, U = diagonalGateEquiv
(realPhase P)` with a level bound matching the
`cgk_forward`-compatible polynomial framework's reach.

## What this file delivers

* **`IsCliffordHierarchyPolyEncodable`** — a diagonal operator `U` is
  polynomial-encodable at hierarchy level `k` iff it equals
  `diagonalGateEquiv (realPhase P)` for some `m`, `P : DiagPhase n m`
  with `P.level ≤ k`.

* **`IsCliffordHierarchyPolyEncodable.toCliffordHierarchy`** — the
  forward inclusion: a polynomial-encodable `U` at level `k` sits in
  the operational Clifford hierarchy at level `k + 1` (the
  off-by-one absorbs the gap between `P.level` and
  `(boolReduce P).effectiveLevel + 1`, which is the precise quantity
  controlled by `cgk_forward`).

* **`isDyadicMod2pi_of_polyEncodable`** — the main statement:
  for every input `v`, the phase function value `g(v)` of a
  polynomial-encodable diagonal `diagonalGateEquiv g` is dyadic
  mod `2π`. This is unconditional, no `g(0)` anchor needed: it falls
  out directly from the definition of `realPhase` as a dyadic-rational
  multiple of `2π`.

## Why this matters

The CGK reverse direction `IsCliffordHierarchy k U → polynomial
witness` needs extra hypotheses or a projective formulation (see
`CGKReverseGeneral.lean` and `cgk_reverse_projective_sharp` in
`CGKTwoSided.lean`). What `IsCliffordHierarchyPolyEncodable`
captures is the **converse statement that is unconditional**: the
polynomial witness ⇒ pointwise dyadicity, with no anchor or
hypothesis on `g(0)`. This is the "fully tight" hierarchy in the
sense that pointwise dyadicity is forced by membership — exactly the
quantitative content of CGK Theorem 3 (the polynomial-framework
direction).

The unscaled reverse `IsCliffordHierarchy k U → IsCliffordHierarchyPolyEncodable k U`
fails in general, because the operational hierarchy is invariant
under global phase; this file does not attempt it.

## Anchors

* CGK 2017 (arXiv:1608.06596) Theorem 3 (qudit specialisation:
  polynomial framework ⇒ Clifford hierarchy), and the level formula
  `w = (m − 1) + d` at `p = 2`.
* `FTQCLib.Hilbert.CGKForward.cgk_forward` — the polynomial-side forward
  direction packaged in terms of `(boolReduce P).effectiveLevel`.
* `FTQCLib.Hierarchy.DiagPhase.realPhase` — the dyadic-rational phase
  angle `2π · (P.eval v).val / 2^m`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## The polynomial-encodable sub-hierarchy -/

/-- **Polynomial-encodable diagonal operator at hierarchy level `k`.**
A diagonal unitary `U` on `QubitSpace n` is polynomial-encodable at
level `k` iff there exist a precision `m` and a phase polynomial
`P : DiagPhase n m` with `P.level ≤ k` such that
`U = diagonalGateEquiv (realPhase P)`.

This is the **polynomial framework** packaged as a single
existential. By design, every member admits unconditional pointwise
dyadicity of its phase function — see
`isDyadicMod2pi_of_polyEncodable` below — because `realPhase P v` is
a dyadic-rational multiple of `2π` by construction.

In contrast to `IsCliffordHierarchy` (which is invariant under global
phase scaling and therefore admits non-dyadic phases at level `≥ 2`)
and `IsCliffordHierarchyTight` (the refinement which restricts
the base scalar to `±1` but is still invariant under global phase via
`.step`), this predicate is **structurally** tied to the polynomial
witness, so pointwise dyadicity falls out for free.

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 3. -/
def IsCliffordHierarchyPolyEncodable
    (k : ℕ) (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) : Prop :=
  ∃ (m : ℕ) (P : DiagPhase n m),
    U = diagonalGateEquiv (DiagPhase.realPhase P) ∧ P.level ≤ k

/-! ## Forward inclusion via `cgk_forward`

The polynomial-encodable predicate maps to the operational Clifford
hierarchy via the existing `cgk_forward` theorem. The precise statement
of `cgk_forward` uses `(boolReduce P).effectiveLevel + 1 ≤ k`, which is
implied by `P.level + 1 ≤ k` (via
`effectiveLevel_le_level` and `effectiveLevel_boolReduce_le`). So a
polynomial witness with `P.level ≤ k` gives membership at level
`k + 1` — the off-by-one absorbs the gap between the abstract
`P.level` bound and the refined `effectiveLevel`-based bound that the
current `cgk_forward` proof discharges.

The sharp statement at level `k` (no off-by-one) is
`IsCliffordHierarchyPolyEncodable.toCliffordHierarchy_sharp` in
`CGKSharpForward.lean`. -/

/-- **Forward inclusion.** A polynomial-encodable diagonal operator at
level `k` sits in the operational Clifford hierarchy at level `k + 1`.

Proof: chain
`(boolReduce P).effectiveLevel ≤ effectiveLevel P ≤ P.level ≤ k`, so
`(boolReduce P).effectiveLevel + 1 ≤ k + 1`, then apply `cgk_forward`.
The conclusion is rewritten through the witness equation
`U = diagonalGateEquiv (realPhase P)`.

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 3 — the polynomial-side
forward direction. -/
theorem IsCliffordHierarchyPolyEncodable.toCliffordHierarchy
    {n k : ℕ} {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h : IsCliffordHierarchyPolyEncodable k U) :
    IsCliffordHierarchy (k + 1) U := by
  obtain ⟨m, P, hU_eq, hP_level⟩ := h
  rw [hU_eq]
  -- Bridge: (boolReduce P).effectiveLevel + 1 ≤ k + 1.
  have h_eff_br : (DiagPhase.boolReduce P).effectiveLevel
      ≤ DiagPhase.effectiveLevel P :=
    effectiveLevel_boolReduce_le P
  have h_eff_lvl : DiagPhase.effectiveLevel P ≤ P.level :=
    DiagPhase.effectiveLevel_le_level P
  have hk : (DiagPhase.boolReduce P).effectiveLevel + 1 ≤ k + 1 := by
    have : (DiagPhase.boolReduce P).effectiveLevel ≤ k :=
      le_trans (le_trans h_eff_br h_eff_lvl) hP_level
    omega
  exact cgk_forward P hk

/-! ## Unconditional pointwise dyadicity

The polynomial witness `realPhase P` is by definition a
dyadic-rational multiple of `2π` at every input. Two diagonal gates
agree iff their phase functions agree mod `2π` (we use it pointwise
via the computational-basis action). So if `diagonalGateEquiv g =
diagonalGateEquiv (realPhase P)`, then `g(v) ≡ realPhase P v
(mod 2π)`, hence `g(v)` is dyadic mod `2π` because `realPhase P v`
is. -/

/-- **`realPhase P v` is dyadic mod `2π`.** Direct from the definition:
`realPhase P v = 2π · (P.eval v).val / 2^m`, which is exactly the
shape of `IsDyadicMod2pi` with the integer offset taken to be `0`.

Anchor: CGK 2017 (arXiv:1608.06596) §III eq (62) at `p = 2`. -/
theorem isDyadicMod2pi_realPhase
    {n m : ℕ} (P : DiagPhase n m) (v : Fin n → ZMod 2) :
    IsDyadicMod2pi (DiagPhase.realPhase P v) := by
  refine ⟨m, P.eval v, 0, ?_⟩
  unfold DiagPhase.realPhase
  push_cast
  ring

/-- **Pointwise extraction.** If `diagonalGateEquiv f = diagonalGateEquiv
g`, then for every `v` we have `f v - g v ∈ 2π · ℤ`. Read off via the
computational-basis evaluation and `Complex.exp_eq_exp_iff_exists_int`. -/
theorem diagonalGateEquiv_eq_pointwise_two_pi
    {n : ℕ} {f g : (Fin n → ZMod 2) → ℝ}
    (h : diagonalGateEquiv f = diagonalGateEquiv g) (v : Fin n → ZMod 2) :
    ∃ (kint : ℤ), f v - g v = 2 * Real.pi * (kint : ℝ) := by
  -- Apply both sides to the computational-basis vector |v⟩.
  have h_apply :
      (diagonalGateEquiv f) (computational v)
        = (diagonalGateEquiv g) (computational v) :=
    congrArg (fun L => L (computational v)) h
  rw [diagonalGateEquiv_apply, diagonalGateEquiv_apply,
      diagonalGate_computational, diagonalGate_computational] at h_apply
  -- h_apply : exp(I · f v) • comp v = exp(I · g v) • comp v.
  -- Evaluate at index v: exp(I · f v) = exp(I · g v).
  have h_eval := congrFun h_apply v
  simp only [Pi.smul_apply, computational_self, smul_eq_mul,
    mul_one] at h_eval
  -- Apply Complex.exp_eq_exp_iff_exists_int.
  rw [Complex.exp_eq_exp_iff_exists_int] at h_eval
  obtain ⟨kint, hk⟩ := h_eval
  -- hk : I · f v = I · g v + kint · (2 π I).
  -- Solve for f v - g v = 2 π kint via the same technique as
  -- isDyadicMod2pi_of_dyadicScalar_arg in CGKReverseDyadic.lean.
  refine ⟨kint, ?_⟩
  have h_sub :
      Complex.I * (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ))
        = (kint : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hk
  -- Multiply by -I.
  have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_neg_I_I : -Complex.I * Complex.I = 1 := by linear_combination -hI_sq
  have h_diff :
      (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ))
        = (kint : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h := congrArg (fun z : ℂ => -Complex.I * z) h_sub
    simp only at h
    have h_lhs :
        -Complex.I * (Complex.I * (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ)))
          = (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ)) := by
      rw [show -Complex.I * (Complex.I *
            (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ)))
            = (-Complex.I * Complex.I) *
              (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ)) from by ring]
      rw [h_neg_I_I, one_mul]
    have h_rhs :
        -Complex.I * ((kint : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
          = (kint : ℂ) * (2 * (Real.pi : ℂ)) := by
      rw [show -Complex.I * ((kint : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
            = (kint : ℂ) * (2 * (Real.pi : ℂ)) *
                (-Complex.I * Complex.I) from by ring]
      rw [h_neg_I_I, mul_one]
    rw [h_lhs, h_rhs] at h
    exact h
  -- Cast h_diff back to ℝ.
  have hreal := congrArg Complex.re h_diff
  have hL_re : (((f v : ℝ) : ℂ) - ((g v : ℝ) : ℂ)).re
                = (f v) - (g v) := by
    rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
  have hR_re : ((kint : ℂ) * (2 * (Real.pi : ℂ))).re
                = (kint : ℝ) * (2 * Real.pi) := by
    rw [Complex.mul_re]
    have h_k_re : (kint : ℂ).re = (kint : ℝ) := Complex.intCast_re kint
    have h_k_im : (kint : ℂ).im = 0 := Complex.intCast_im kint
    have h_two_pi_re : ((2 : ℂ) * (Real.pi : ℂ)).re = 2 * Real.pi := by
      rw [Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im]
    have h_two_pi_im : ((2 : ℂ) * (Real.pi : ℂ)).im = 0 := by
      rw [Complex.mul_im]
      simp [Complex.ofReal_re, Complex.ofReal_im]
    rw [h_k_re, h_k_im, h_two_pi_re, h_two_pi_im, zero_mul, sub_zero]
  rw [hL_re, hR_re] at hreal
  linarith

/-- **Unconditional pointwise dyadicity.** A polynomial-encodable
diagonal operator `diagonalGateEquiv g` has dyadic-mod-`2π` phase
function at every input.

Proof: extract `(m, P)` with `diagonalGateEquiv g = diagonalGateEquiv
(realPhase P)`, then read off `g(v) - realPhase P v ∈ 2π · ℤ` via
`diagonalGateEquiv_eq_pointwise_two_pi`. Since `realPhase P v` is
manifestly dyadic mod `2π` (`isDyadicMod2pi_realPhase`), so is `g(v)`
by the integer-translate closure
(`isDyadicMod2pi_add_int_mul_2pi`).

This is the quantitative content of CGK Theorem 3's
polynomial-framework direction at `p = 2`: membership in the
polynomial-encodable sub-hierarchy structurally forces pointwise
dyadicity, with no `g(0)` anchor or other hypothesis required.

Anchor: CGK 2017 (arXiv:1608.06596) Theorem 3; the dyadic-rational
structure of `realPhase P v` from
`FTQCLib.Hierarchy.DiagPhase.realPhase`. -/
theorem isDyadicMod2pi_of_polyEncodable
    {n k : ℕ} {g : (Fin n → ZMod 2) → ℝ}
    (h : IsCliffordHierarchyPolyEncodable k (diagonalGateEquiv g)) :
    ∀ v, IsDyadicMod2pi (g v) := by
  intro v
  obtain ⟨m, P, hU_eq, _hP_level⟩ := h
  -- g(v) - realPhase P v = 2π · kint for some integer kint.
  obtain ⟨kint, hk⟩ := diagonalGateEquiv_eq_pointwise_two_pi hU_eq v
  -- g(v) = realPhase P v + 2π · kint.
  have hg_eq : g v = DiagPhase.realPhase P v + 2 * Real.pi * (kint : ℝ) := by
    linarith
  rw [hg_eq]
  exact isDyadicMod2pi_add_int_mul_2pi (isDyadicMod2pi_realPhase P v) kint

/-! ## Note on the "fully tight" hierarchy

The predicate `IsCliffordHierarchyPolyEncodable` is the "fully tight"
sub-hierarchy in the sense that the unconditional dyadicity
statement `isDyadicMod2pi_of_polyEncodable` closes at every `k` — no
anchor on `g(0)` and no restriction on the base-case scalar are
needed. This is in contrast to:

* `IsCliffordHierarchy` (operator-side): admits global phase scaling
  through `.step`, so non-dyadic phases survive at level `≥ 2`.
* `IsCliffordHierarchyTight`: tightens the
  base case to `±1`, but `.step` is invariant under arbitrary global
  phase scaling, so the same non-dyadic-phase issue persists at level
  `≥ 2`.
* The level-2 anchored result
  `cgk_reverse_dyadic_phase_dyadic_level_two`: requires an
  explicit `g(0)` dyadic hypothesis.

Extracting a polynomial witness from operator-side hierarchy
membership is treated in `CGKReverseGeneral.lean` (anchored on `g(0)`)
and `CGKTwoSided.lean` (up to a global phase). The polynomial-encodable
sub-hierarchy is the setting in which unconditional pointwise
dyadicity holds at every `k`. -/

end FTQCLib.Hilbert

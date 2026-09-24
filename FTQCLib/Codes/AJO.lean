/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.CSS.Defs
import FTQCLib.CSS.Logical
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.RzHardness

set_option linter.unusedSectionVars false

/-! # Anderson--Jochym-O'Connor: transversal-logical diagonal gates are
polynomially encodable

The Anderson--Jochym-O'Connor 2014 classification (Theorem 1 / Prop 2
of arXiv:1408.5547) says: on any non-trivial stabilizer code, every
transversal diagonal logical gate is polynomially encodable in the
Cui--Gottesman--Krishna sense.

This file gives the F₂-algebraic formulation of the CSS case, in
the F₂-symplectic and polynomial-phase framework of this library.

The structural level is *linear-in-bits phase patterns*, the patterns
of the form `f(v) = ∑ᵢ θᵢ · vᵢ` arising from diagonal transversal
gates. AJO Prop 2 (uniform case `θᵢ = θ`) and Prop 3 (per-qubit
non-uniform) are about these patterns. R_z(θ) is the specific
instance with `θᵢ = θ` for all i; the theorem itself is over the
linearity class.

A purely general phase pattern `f : (F₂)ⁿ → ℝ` is too permissive:
trans-logical conditions only fix `f` modulo `2π` on each coset of
`row(H_X)` within `ker(H_Z)`, leaving any function on the X-logical
quotient `ker(H_Z) / row(H_X) → ℝ/2πℤ` as a valid trans-logical
phase pattern. Most such functions are not polynomially encodable.
The linearity-in-bits constraint is what makes the dyadic conclusion
emerge.

This file defines:

* **`PhasePattern n`** — real-valued functions on binary vectors.
* **`IsTransversalLogical f H_X H_Z`** — F₂-side condition that
  `f` is constant modulo `2π` on each coset of `row(H_X)` within
  `ker(H_Z)`. F₂-side surrogate for "the diagonal unitary realising
  the phase pattern `f` preserves the codespace of the CSS code".
  The full state-vector equivalence (the precise statement of the
  surrogacy) requires Hilbert-space machinery and is not treated here.
* **`IsLinearPhase f`** — `f(v) = ∑ᵢ θᵢ · vᵢ` for some angle vector
  `θ : Fin n → ℝ`. The class of phase patterns arising from diagonal
  transversal gates.
* **`IsPolyEncodable f`** — `f` matches the real-phase function of
  some polynomial-phase encoding `(m, P, φ)` modulo `2π`.

We prove the closure lemmas plus two structural results:
`IsTransversalLogical.zero_to_rowSpan` (m=1 overlap condition) and
`IsTransversalLogical.const_on_coset` (well-defined-ness on the
X-logical quotient).

The main theorem `transversalLogical_polyEncodable` —
`IsLinearPhase f` + `IsTransversalLogical f H_X H_Z` + non-trivial
CSS code → `IsPolyEncodable f` — reduces to the AJO binary-matrix
overlap lemma (pp. 7--8 of AJO 2014). It is stated below as a
target and is not proved in this library.

## Note on formal equivalence to original formulations

This file uses F₂-side algebraic predicates as surrogates for the
original Hilbert-space statements:

  * `IsTransversalLogical f H_X H_Z` surrogates
    "a diagonal V^⊗n with phase pattern f preserves the codespace
    of the CSS code (H_X, H_Z)".
  * `IsPolyEncodable f` surrogates "f arises from a polynomial-phase
    diagonal unitary in the Cui--Gottesman--Krishna framework".

The `IsTransversalLogical` surrogacy is **formally verified** in
`FTQCLib/Hilbert/Diagonal.lean`. The theorem
`isTransversalLogical_iff_preservesCodespace` establishes

    IsTransversalLogical f H_X H_Z ↔ PreservesCodespace f H_X H_Z

where `PreservesCodespace` is the operator-side statement
"diagonalGate f preserves the codespace of the CSS code on the qubit
Hilbert space `QubitSpace n`". The two directions are direct from the
codestate structure: trans-logical conditions are the F₂-side
expression of constancy on cosets, which is exactly what codestate
preservation requires of the diagonal phase factors.

The `IsPolyEncodable` surrogacy traces back to the polynomial-phase
framework of `FTQCLib.Hierarchy.RzHardness`. Its `realPhase` matches the actual radian
phase a `DiagPhase` polynomial produces; the predicate's equivalence
to "the gate is in the diagonal subgroup of `⋃_k C_k`" is the
Cui--Gottesman--Krishna Theorem 3 image we use throughout. -/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Hierarchy Matrix

variable {n r_X r_Z : ℕ}

/-! ## Phase patterns and transversal-logical compatibility -/

/-- A *phase pattern* on `n` qubits is a real-valued function on
binary vectors `(F₂)ⁿ`. A diagonal unitary `U` on `n` qubits acts on
the computational basis by `U |v⟩ = e^{i·f(v)} |v⟩` for some such `f`
(unique modulo `2π`); the polynomial-framework realisations are
the ones with `f` matching the `realPhase` of some `DiagPhase n m`
polynomial. -/
abbrev PhasePattern (n : ℕ) := (Fin n → ZMod 2) → ℝ

/-- A phase pattern `f` is *transversal-logical* on a CSS code with
check matrices `(H_X, H_Z)` iff, for every `v` in `ker(H_Z)` (the
X-supports of codespace states) and every `h` in `row(H_X)` (a
combination of X-stabilizer generators), the phase difference
`f(v + h) - f(v)` is an integer multiple of `2π`.

The condition says `f` modulo `2π` is constant on each coset of
`row(H_X)` within `ker(H_Z)`. In the state-vector picture this is
exactly the requirement that the diagonal unitary
`U_f = diag(e^{i·f(v)})` preserves the codespace of the CSS code
(AJO 2014, Section III.A). -/
def IsTransversalLogical (f : PhasePattern n)
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) : Prop :=
  ∀ v ∈ cssXLogicalCarrier H_Z, ∀ h ∈ cssXLogicalSubspace H_X,
    ∃ k : ℤ, f (v + h) - f v = 2 * Real.pi * k

/-! ## Linear-in-bits phase patterns

The phase patterns arising from diagonal transversal gates have the
form `f(v) = ∑ᵢ θᵢ · (vᵢ).val`, with the per-qubit angles `θᵢ`
encoding the action of each tensor factor of the gate on its qubit's
`|1⟩` state. AJO 2014 Prop 2 (uniform `θᵢ = θ`) and Prop 3 (per-qubit
decompression) are about this class. -/

/-- The linear-in-bits phase pattern with angle vector `θ`:
`f(v) = ∑ᵢ θᵢ · (vᵢ).val`. -/
def linearPhase (θ : Fin n → ℝ) : PhasePattern n :=
  fun v => ∑ i, (v i).val * θ i

/-- A phase pattern is *linear-in-bits* iff it equals `linearPhase θ`
for some angle vector. This is the F₂-side characterisation of phase
patterns arising from diagonal transversal gates. -/
def IsLinearPhase (f : PhasePattern n) : Prop :=
  ∃ θ : Fin n → ℝ, f = linearPhase θ

/-- `linearPhase θ` is, tautologically, linear-in-bits. -/
theorem linearPhase_isLinear (θ : Fin n → ℝ) :
    IsLinearPhase (linearPhase θ) :=
  ⟨θ, rfl⟩

/-- The zero phase pattern is linear-in-bits with the zero angle vector. -/
theorem zero_isLinearPhase :
    IsLinearPhase (fun _ : Fin n → ZMod 2 => (0 : ℝ)) := by
  refine ⟨0, ?_⟩
  funext v
  unfold linearPhase
  simp

/-! ## Polynomial encodability of phase patterns -/

/-- A phase pattern `f` is *polynomially encodable* iff there exist a
precision `m`, a phase polynomial `P : DiagPhase n m`, and a global
offset `φ : ℝ` such that for every binary vector `v`, the
polynomial-framework real phase `realPhase P v` equals `f v + φ`
modulo `2π`.

This is the multi-input generalisation of the encoding condition in
`rz_irrational_not_polyEncodable` (`FTQCLib.Hierarchy.RzHardness`). Polynomially encodable
phase patterns are exactly the ones realised by diagonal unitaries in
the Cui--Gottesman--Krishna framework, equivalently the diagonal
subgroup of `⋃_k C_k` of the Clifford hierarchy. -/
def IsPolyEncodable (f : PhasePattern n) : Prop :=
  ∃ (m : ℕ) (P : DiagPhase n m) (φ : ℝ),
    ∀ v : Fin n → ZMod 2, ∃ k : ℤ,
      DiagPhase.realPhase P v = f v + φ + 2 * Real.pi * k

/-! ## Structural lemmas on `IsTransversalLogical` -/

/-- The zero phase pattern is transversal-logical on every CSS code:
`f(v + h) - f(v) = 0` trivially. -/
theorem isTransversalLogical_zero
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    IsTransversalLogical (fun _ : Fin n → ZMod 2 => (0 : ℝ)) H_X H_Z := by
  intro v _ h _
  refine ⟨0, ?_⟩
  simp

/-- A constant phase pattern is transversal-logical: differences vanish
regardless of code structure. -/
theorem isTransversalLogical_const
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) (c : ℝ) :
    IsTransversalLogical (fun _ : Fin n → ZMod 2 => c) H_X H_Z := by
  intro v _ h _
  refine ⟨0, ?_⟩
  simp

/-- Adding two transversal-logical phase patterns yields a transversal-
logical phase pattern: phase differences add. -/
theorem IsTransversalLogical.add
    {f g : PhasePattern n}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hf : IsTransversalLogical f H_X H_Z)
    (hg : IsTransversalLogical g H_X H_Z) :
    IsTransversalLogical (fun v => f v + g v) H_X H_Z := by
  intro v hv h hh
  obtain ⟨kf, hkf⟩ := hf v hv h hh
  obtain ⟨kg, hkg⟩ := hg v hv h hh
  refine ⟨kf + kg, ?_⟩
  push_cast
  linarith [hkf, hkg]

/-- A scalar integer multiple of a transversal-logical phase pattern is
transversal-logical: scale the integer multiple of `2π`. -/
theorem IsTransversalLogical.intMul
    {f : PhasePattern n}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hf : IsTransversalLogical f H_X H_Z) (c : ℤ) :
    IsTransversalLogical (fun v => (c : ℝ) * f v) H_X H_Z := by
  intro v hv h hh
  obtain ⟨k, hk⟩ := hf v hv h hh
  refine ⟨c * k, ?_⟩
  have : (c : ℝ) * f (v + h) - (c : ℝ) * f v = (c : ℝ) * (f (v + h) - f v) := by ring
  rw [this, hk]
  push_cast
  ring

/-- **The `m = 1` overlap condition.** Instantiate trans-logical at
`v = 0` (always in `ker(H_Z)`): the phase pattern `f` differs from
its value at `0` by an integer multiple of `2π` on every
`h ∈ row(H_X)`. -/
theorem IsTransversalLogical.zero_to_rowSpan
    {f : PhasePattern n}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hTransv : IsTransversalLogical f H_X H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ, f h - f 0 = 2 * Real.pi * k := by
  have h0 : (0 : Fin n → ZMod 2) ∈ cssXLogicalCarrier H_Z :=
    Submodule.zero_mem _
  have := hTransv 0 h0 h hh
  rwa [zero_add] at this

/-- **Constancy on cosets, explicit form.** If `f` is transversal-
logical, then any two `ker(H_Z)`-elements in the same coset of
`row(H_X)` agree modulo `2π`. This is the structural content of the
predicate: `f` modulo `2π` is well-defined on the X-logical quotient
`cssXLogical H_X H_Z = ker(H_Z) / row(H_X)`. -/
theorem IsTransversalLogical.const_on_coset
    {f : PhasePattern n}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hTransv : IsTransversalLogical f H_X H_Z)
    {v w : Fin n → ZMod 2}
    (_hv : v ∈ cssXLogicalCarrier H_Z) (hw : w ∈ cssXLogicalCarrier H_Z)
    (hvw : v - w ∈ cssXLogicalSubspace H_X) :
    ∃ k : ℤ, f v - f w = 2 * Real.pi * k := by
  -- Apply trans-logical at `w` with shift `v - w`.
  have hshift := hTransv w hw (v - w) hvw
  obtain ⟨k, hk⟩ := hshift
  refine ⟨k, ?_⟩
  -- `w + (v - w) = v` over any abelian group; specialise to `Fin n → ZMod 2`.
  have hvw_eq : w + (v - w) = v := by
    ext i
    simp [add_sub_cancel]
  rw [hvw_eq] at hk
  exact hk

/-! ## Structural lemmas on `IsPolyEncodable` -/

/-- The zero phase pattern is polynomially encodable by the zero
polynomial at precision `m = 1` with no global offset. -/
theorem isPolyEncodable_zero :
    IsPolyEncodable (fun _ : Fin n → ZMod 2 => (0 : ℝ)) := by
  refine ⟨1, 0, 0, ?_⟩
  intro v
  refine ⟨0, ?_⟩
  unfold DiagPhase.realPhase
  simp

/-- The constant phase pattern at value `c` is polynomially encodable by
the zero polynomial with global offset `-c`. The encoding equation
`realPhase 0 v = c + (-c) + 2π·0 = 0` holds. -/
theorem isPolyEncodable_const (c : ℝ) :
    IsPolyEncodable (fun _ : Fin n → ZMod 2 => c) := by
  refine ⟨1, 0, -c, ?_⟩
  intro v
  refine ⟨0, ?_⟩
  unfold DiagPhase.realPhase
  simp

/-! ## Scope

The structural AJO Prop 2 for the CSS case — that every linear-in-bits
transversal-logical phase pattern on a non-trivial CSS code is
polynomially encodable — reduces to the AJO binary-matrix overlap
lemma (pp. 7--8 of AJO 2014). The matrix lemma extracts a dyadic
denominator bound from the chain of `m`-fold overlap conditions on
X-supports of stabilizer generators combined with the non-trivial
logical X.

This file establishes the algebraic vocabulary (`PhasePattern`,
`IsTransversalLogical`, `IsLinearPhase`, `IsPolyEncodable`) and the
closure lemmas (`isTransversalLogical_zero`, `_const`, `.add`,
`.intMul`, `isPolyEncodable_zero`, `_const`).

The main theorem statement
```
transversalLogical_polyEncodable :
    IsCSSPair H_X H_Z →
    (∃ v ∈ cssXLogicalCarrier H_Z, v ∉ cssXLogicalSubspace H_X) →
    IsLinearPhase f →
    IsTransversalLogical f H_X H_Z →
    IsPolyEncodable f
```
is the target; it is not proved in this library. Its proof is the
substantive combinatorial content of AJO 2014 Theorem 1 (CSS case).
`FTQCLib.Codes.AJOLogical` and `FTQCLib.Codes.AJOMain` prove the
logical-angle version and special cases under additional structural
hypotheses. -/

end FTQCLib.Codes

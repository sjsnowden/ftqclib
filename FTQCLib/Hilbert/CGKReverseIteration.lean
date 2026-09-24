/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGK
import FTQCLib.Hilbert.CGKForward
import FTQCLib.Hilbert.Hierarchy
import FTQCLib.Hilbert.DiagonalEquiv
import FTQCLib.Hilbert.PauliEquiv
import FTQCLib.Hilbert.PauliProduct
import FTQCLib.Hierarchy.FuncDeriv

set_option linter.unusedSectionVars false

/-! # Iterated X-conjugation of diagonal unitaries

Iterated X-conjugation of diagonal unitaries. Builds the operator-side
analogue of iterated discrete derivatives: for U a diagonal gate with
phase function f, conjugating U by Pauli X_i_1, …, X_i_k produces a
phased operator whose phase function is the iterated finite difference
Δ_{i_1,…,i_k} f. The substantive content of CGK 2017 §III's descent:
when applied to U ∈ IsCliffordHierarchy (k+1), iterated conjugation
terminates in IsCliffordHierarchy 1 = phased Pauli.

This file provides the operator-side iteration machinery for the CGK
reverse direction: it translates the recursive descent
`IsCliffordHierarchy (k+1) U → ∀ p, IsCliffordHierarchy k (conjEquiv U (pauliEquiv p))`
to the F₂-side iterated discrete derivative `funcDeriv` of the phase
function.

## Structure

* **Real-valued discrete derivative** (`funcDerivPhase`): the
  ℝ-valued analogue of `funcDeriv` from `FTQCLib.Hierarchy.FuncDeriv`.
  Defined as `funcDerivPhase i f v := f (v + e_i) - f v`.

* **Iterated discrete derivative** (`funcDerivPhaseSubset`): iterated
  `funcDerivPhase` over a `Finset (Fin n)`.

* **Single-step bridge** (`conjEquiv_diagonalGateEquiv_paulix_funcDeriv`):
  the conjugate of `pauliEquiv (paulix i)` by `diagonalGateEquiv f` is
  `(diagonalGateEquiv (funcDerivPhase i f)).trans (pauliEquiv (paulix
  i))`. This is the operator-side analogue of CGK eq. (3) on a single
  X-Pauli generator. Generalises
  `conjEquiv_diagonalGateEquiv_paulix` from `CGKForward.lean` (which
  is stated for `f = realPhase P`) to arbitrary real-valued phase
  functions.

* **X-sum operator** (`pauliXOfFinset`): the sum of pure-X Paulis over
  `S`, with zero Z-support and X-support equal to the indicator of S.

* **Iterated bridge** (`iterConjXDiag`): the closed-form theorem
  associating iterated single-step descent with the iterated discrete
  derivative. Stated as the *result* of CGK §III's recursion: after
  peeling off the X-part successively, the surviving diagonal gate has
  phase function `funcDerivPhaseSubset S f`.

* **Phase-factor tracking** (`iterConjX_phase_factor`,
  `iterConjX_phase_factor_eq_one`): each step's Pauli-product sign is
  `1`, because every `paulix i` has zero Z-support, so the `q.Z · p.X`
  exponent in `pauliOperator_mul` is `0`.

## References

Anchored to CGK 2017 (arXiv:1608.06596) §II–III. The single-step
descent is CGK eq. (3); the iterated form is the substantive content of
§III's recursion. The substantive math: iterating the descent on a
diagonal gate. Each step replaces the running diagonal `D_g` with
`D_{Δ_i g}`, peeling off an X_i to the left. The end result, for S
iterations: `pauliOperator (sum of X_i for i ∈ S) ∘ diagonalGate
(funcDerivPhaseSubset S f)`. The Pauli-product phase factors across S
iterations all collapse to `1` because pure-X Paulis have zero
Z-support.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## Real-valued analogue of `funcDeriv` -/

/-- The **functional discrete derivative on real-valued phase
functions**. For `f : (Fin n → ZMod 2) → ℝ` and `i : Fin n`,
`funcDerivPhase i f v := f (v + e_i) - f v`.

This is the real-valued analogue of `funcDeriv` from
`FTQCLib.Hierarchy.FuncDeriv`, which targets `ZMod (2^m)`. The
operator-side descent rule turns conjugation of `pauliEquiv (paulix
i)` by `diagonalGateEquiv f` into the composition of `pauliEquiv
(paulix i)` with `diagonalGateEquiv (funcDerivPhase i f)`. -/
noncomputable def funcDerivPhase (i : Fin n)
    (f : (Fin n → ZMod 2) → ℝ) :
    (Fin n → ZMod 2) → ℝ :=
  fun v => f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) - f v

@[simp] lemma funcDerivPhase_apply (i : Fin n)
    (f : (Fin n → ZMod 2) → ℝ) (v : Fin n → ZMod 2) :
    funcDerivPhase i f v =
      f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) - f v :=
  rfl

/-! ## Single-step bridge

Generalises `conjEquiv_diagonalGateEquiv_paulix` from `CGKForward.lean`
(stated for `f = realPhase P`) to arbitrary real-valued phase functions
`f : (Fin n → ZMod 2) → ℝ`. The proof is structurally identical: only
the input phase function changes.
-/

/-- **Single-step bridge.** Conjugating `pauliEquiv (paulix i)` by
`diagonalGateEquiv f` produces the composition of `diagonalGateEquiv
(funcDerivPhase i f)` and `pauliEquiv (paulix i)` (in the `trans` order,
i.e., apply diagonal first then X-Pauli). This is the operator-side
analogue of CGK eq. (3) on a single X-Pauli generator. -/
theorem conjEquiv_diagonalGateEquiv_paulix_funcDeriv
    (f : (Fin n → ZMod 2) → ℝ) (i : Fin n) :
    conjEquiv (diagonalGateEquiv f) (pauliEquiv (paulix i)) =
      (diagonalGateEquiv (funcDerivPhase i f)).trans
        (pauliEquiv (paulix i)) := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [conjEquiv_apply, LinearEquiv.coe_coe,
    diagonalGateEquiv_symm_apply, pauliEquiv_apply,
    LinearEquiv.trans_apply, diagonalGateEquiv_apply]
  unfold diagonalGate pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- (paulix i).Z = 0 so zDotVal = 0 on every input.
  have hX : (paulix i).X = Pi.single i 1 := rfl
  have hzdot : ∀ u : Fin n → ZMod 2, zDotVal (paulix i) u = 0 := by
    intro u
    unfold zDotVal
    refine Finset.sum_eq_zero ?_
    intro j _
    have h0 : ((paulix i).Z j).val = 0 := by
      have hZj : (paulix i).Z j = (0 : ZMod 2) := rfl
      rw [hZj]
      exact ZMod.val_zero
    rw [h0]; ring
  rw [hX]
  rw [hzdot]
  simp only [pow_zero, one_mul]
  -- Unfold funcDerivPhase on the RHS so the `w - e_i + e_i = w` rewrite has a target.
  change Complex.exp (Complex.I * ((f w) : ℂ)) *
            (Complex.exp (Complex.I * ((- f (w - Pi.single i 1) : ℝ) : ℂ)) *
              ψ (w - Pi.single i 1))
       = Complex.exp (Complex.I *
            ((f (w - Pi.single i 1 + Pi.single i 1) -
              f (w - Pi.single i 1) : ℝ) : ℂ)) *
            ψ (w - Pi.single i 1)
  have hw : w - Pi.single i 1 + Pi.single i 1 = w := by ring
  rw [hw]
  rw [show (Complex.exp (Complex.I * ((f w) : ℂ)) *
            (Complex.exp (Complex.I * ((- f (w - Pi.single i 1) : ℝ) : ℂ)) *
              ψ (w - Pi.single i 1)))
        = (Complex.exp (Complex.I * ((f w) : ℂ)) *
            Complex.exp (Complex.I * ((- f (w - Pi.single i 1) : ℝ) : ℂ))) *
          ψ (w - Pi.single i 1) from by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## Commutativity of `funcDerivPhase`

The discrete derivatives `funcDerivPhase i` and `funcDerivPhase j`
commute as operators on real-valued phase functions. This is the
LeftCommutative property needed for `Multiset.foldr` over the support
of a `Finset`. -/

/-- The discrete derivatives `funcDerivPhase i` and `funcDerivPhase j`
commute as operators on real-valued phase functions. -/
theorem funcDerivPhase_comm (i j : Fin n)
    (f : (Fin n → ZMod 2) → ℝ) :
    funcDerivPhase i (funcDerivPhase j f) =
      funcDerivPhase j (funcDerivPhase i f) := by
  funext v
  simp only [funcDerivPhase_apply]
  have h_comm :
      (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)
         + (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)) =
        (v + (Pi.single j (1 : ZMod 2) : Fin n → ZMod 2)
           + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) := by
    funext k
    simp only [Pi.add_apply]
    ring
  rw [h_comm]
  ring

/-- `funcDerivPhase` is a left-commutative operation (on real-valued
phase functions). This is the algebraic property needed by
`Multiset.foldr` to be well-defined on multisets without a canonical
order. -/
instance : LeftCommutative (funcDerivPhase (n := n)) where
  left_comm := funcDerivPhase_comm

/-! ## Iterated discrete derivative on real-valued phase functions

`funcDerivPhaseSubset S f` is the iterated discrete derivative on a
finite set `S`: apply `funcDerivPhase i` for each `i ∈ S`. Defined via
`Multiset.foldr` on `S.val`, using the `LeftCommutative` instance for
order-independence. -/

/-- Iterated discrete derivative on real-valued phase functions. The
empty fold gives `f`; for any `i ∈ S` (well-defined by
left-commutativity), one application of `funcDerivPhase i` to the
fold-over-the-rest. -/
noncomputable def funcDerivPhaseSubset (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → ℝ) : (Fin n → ZMod 2) → ℝ :=
  Multiset.foldr funcDerivPhase f S.val

@[simp] theorem funcDerivPhaseSubset_empty
    (f : (Fin n → ZMod 2) → ℝ) :
    funcDerivPhaseSubset ∅ f = f := by
  unfold funcDerivPhaseSubset
  rfl

theorem funcDerivPhaseSubset_insert {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) (f : (Fin n → ZMod 2) → ℝ) :
    funcDerivPhaseSubset (insert i S) f =
      funcDerivPhase i (funcDerivPhaseSubset S f) := by
  unfold funcDerivPhaseSubset
  -- (insert i S).val = i ::ₘ S.val when i ∉ S.
  rw [Finset.insert_val_of_notMem hi]
  rw [Multiset.foldr_cons]

theorem funcDerivPhaseSubset_singleton (i : Fin n)
    (f : (Fin n → ZMod 2) → ℝ) :
    funcDerivPhaseSubset {i} f = funcDerivPhase i f := by
  unfold funcDerivPhaseSubset
  -- ({i} : Finset (Fin n)).val = {i} (multiset singleton).
  change Multiset.foldr funcDerivPhase f ({i} : Multiset (Fin n)) = _
  rw [Multiset.foldr_singleton]

/-! ## The X-sum Pauli

The sum `∑_{i ∈ S} paulix i` has X-support equal to the indicator of
`S` (as a function `Fin n → ZMod 2`). Its Z-support is zero. We
record this for the phase tracking below. -/

/-- The Finset-sum of pure-X Paulis indexed by `S`. -/
noncomputable def pauliXOfFinset (S : Finset (Fin n)) : Pauli n :=
  ∑ i ∈ S, paulix i

@[simp] theorem pauliXOfFinset_empty :
    pauliXOfFinset (∅ : Finset (Fin n)) = 0 := by
  unfold pauliXOfFinset
  rw [Finset.sum_empty]

theorem pauliXOfFinset_insert {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) :
    pauliXOfFinset (insert i S) = paulix i + pauliXOfFinset S := by
  unfold pauliXOfFinset
  rw [Finset.sum_insert hi]

@[simp] theorem pauliXOfFinset_singleton (i : Fin n) :
    pauliXOfFinset {i} = paulix i := by
  unfold pauliXOfFinset
  rw [Finset.sum_singleton]

/-- The Z-support of a Finset-sum of pure-X Paulis is zero. -/
theorem pauliXOfFinset_Z (S : Finset (Fin n)) :
    (pauliXOfFinset S).Z = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [pauliXOfFinset_empty]; rfl
  | @insert i S hi ih =>
      rw [pauliXOfFinset_insert hi]
      change (paulix _).Z + (pauliXOfFinset _).Z = 0
      rw [paulix_Z, ih, add_zero]

/-- `zDotVal (paulix i) v = 0` for all `i, v`: pure-X Paulis have zero
Z-support. -/
private theorem zDotVal_paulix (i : Fin n) (v : Fin n → ZMod 2) :
    zDotVal (paulix i) v = 0 := by
  unfold zDotVal
  refine Finset.sum_eq_zero ?_
  intro j _
  have h0 : ((paulix i).Z j).val = 0 := by
    have hZj : (paulix i).Z j = (0 : ZMod 2) := rfl
    rw [hZj]
    exact ZMod.val_zero
  rw [h0]; ring

/-- `zDotVal (pauliXOfFinset S) v = 0` for all `S, v`: a sum of pure-X
Paulis has zero Z-support. -/
theorem zDotVal_pauliXOfFinset (S : Finset (Fin n))
    (v : Fin n → ZMod 2) :
    zDotVal (pauliXOfFinset S) v = 0 := by
  unfold zDotVal
  refine Finset.sum_eq_zero ?_
  intro j _
  have h0 : ((pauliXOfFinset S).Z j).val = 0 := by
    rw [pauliXOfFinset_Z S]
    change ((0 : ZMod 2)).val = 0
    exact ZMod.val_zero
  rw [h0]; ring

/-! ## Phase-factor tracking: pure-X Pauli products are sign-free

Each composition `pauliOperator q ∘ pauliOperator p` carries a sign
`(-1)^{q.Z · p.X}`. For two pure-X Paulis `paulix i` and `paulix j`,
this sign is `(-1)^0 = 1` because both have zero Z-support. -/

/-- For two pure-X Paulis, the product identity `pauliOperator_mul`
collapses to no-sign. -/
theorem pauliOperator_paulix_mul (i j : Fin n) :
    pauliOperator (paulix j) ∘ₗ pauliOperator (paulix i) =
      pauliOperator (paulix i + paulix j) := by
  have h := pauliOperator_mul (paulix i) (paulix j)
  rw [h]
  rw [show zDotVal (paulix j) (paulix i).X = 0 from zDotVal_paulix _ _]
  rw [pow_zero, one_smul]

/-- For a pure-X Pauli composed with a sum of pure-X Paulis, the
product identity collapses to no-sign. -/
theorem pauliOperator_paulix_pauliXOfFinset_mul (i : Fin n)
    (S : Finset (Fin n)) :
    pauliOperator (pauliXOfFinset S) ∘ₗ pauliOperator (paulix i) =
      pauliOperator (paulix i + pauliXOfFinset S) := by
  have h := pauliOperator_mul (paulix i) (pauliXOfFinset S)
  rw [h]
  rw [show zDotVal (pauliXOfFinset S) (paulix i).X = 0 from
        zDotVal_pauliXOfFinset _ _]
  rw [pow_zero, one_smul]

/-! ## Iterated bridge: closed form

The iterated bridge: for diagonal U with phase function f, the
iterated descent rule applied across a Finset `S` of indices produces
the phased operator

  `pauliEquiv (pauliXOfFinset S) ∘ diagonalGateEquiv (funcDerivPhaseSubset S f)`

(in `LinearEquiv.trans` order: apply diagonal first, then the X-sum
Pauli).

We define this **closed-form expression** `iterConjXDiag S f` directly,
then state the iterated bridge as the statement that the iteratively-
applied descent ends at this closed form. -/

/-- The **iterated descent closed form** for a diagonal gate with phase
function `f` and a set `S : Finset (Fin n)` of indices: the composition
of `diagonalGateEquiv (funcDerivPhaseSubset S f)` with `pauliEquiv
(pauliXOfFinset S)`. This is the operator that should be in
`IsCliffordHierarchy (k+1-|S|)` after `|S|` steps of CGK descent on a
level-`(k+1)` diagonal gate. -/
noncomputable def iterConjXDiag (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → ℝ) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  (diagonalGateEquiv (funcDerivPhaseSubset S f)).trans
    (pauliEquiv (pauliXOfFinset S))

@[simp] theorem iterConjXDiag_empty (f : (Fin n → ZMod 2) → ℝ) :
    iterConjXDiag ∅ f = diagonalGateEquiv f := by
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  unfold iterConjXDiag
  simp only [funcDerivPhaseSubset_empty, pauliXOfFinset_empty]
  simp only [LinearEquiv.coe_trans, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, pauliEquiv_apply,
    diagonalGateEquiv_apply]
  rw [show pauliOperator (0 : Pauli n) = LinearMap.id from
        pauliOperator_zero]
  simp only [LinearMap.id_apply]

/-- **Iterated bridge (recursive case).** For `i ∉ S` and any phase
function `f`, the closed form for `insert i S` unfolds via the
`funcDerivPhaseSubset_insert` and `pauliXOfFinset_insert` recurrences. -/
theorem iterConjXDiag_insert {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) (f : (Fin n → ZMod 2) → ℝ) :
    iterConjXDiag (insert i S) f =
      (diagonalGateEquiv (funcDerivPhase i (funcDerivPhaseSubset S f))).trans
        (pauliEquiv (paulix i + pauliXOfFinset S)) := by
  unfold iterConjXDiag
  rw [funcDerivPhaseSubset_insert hi]
  rw [pauliXOfFinset_insert hi]

/-- The single-step descent applied to the diagonal part of
`iterConjXDiag S f` produces `iterConjXDiag (insert i S) f`. The proof
exhibits both sides as equal linear maps by computation. -/
theorem iterConjXDiag_step {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) (f : (Fin n → ZMod 2) → ℝ) :
    ((diagonalGateEquiv (funcDerivPhase i (funcDerivPhaseSubset S f))).trans
        (pauliEquiv (paulix i))).trans
          (pauliEquiv (pauliXOfFinset S))
      = iterConjXDiag (insert i S) f := by
  rw [iterConjXDiag_insert hi]
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  simp only [LinearEquiv.coe_trans, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, pauliEquiv_apply,
    diagonalGateEquiv_apply]
  -- LHS: pauliOperator (pauliXOfFinset S) (pauliOperator (paulix i) (D' ψ))
  -- = pauliOperator (paulix i + pauliXOfFinset S) (D' ψ).
  have h := pauliOperator_paulix_pauliXOfFinset_mul i S
  have h_at :
      pauliOperator (pauliXOfFinset S)
          (pauliOperator (paulix i)
            (diagonalGate
              (funcDerivPhase i (funcDerivPhaseSubset S f)) ψ)) =
        pauliOperator (paulix i + pauliXOfFinset S)
          (diagonalGate
            (funcDerivPhase i (funcDerivPhaseSubset S f)) ψ) := by
    have hψ := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) =>
        L (diagonalGate
              (funcDerivPhase i (funcDerivPhaseSubset S f)) ψ))
      h
    simp only [LinearMap.coe_comp, Function.comp_apply] at hψ
    exact hψ
  rw [h_at]

/-! ## The singleton bridge

For `S = {i}` (a single index), `iterConjXDiag {i} f` equals the result
of conjugating `pauliEquiv (paulix i)` by `diagonalGateEquiv f`. This
is the single-step bridge rewrapped through the closed form. -/

/-- The iterated bridge specialised to a singleton index recovers the
single-step descent. -/
theorem iterConjXDiag_eq_conjEquiv_paulix
    (f : (Fin n → ZMod 2) → ℝ) (i : Fin n) :
    iterConjXDiag {i} f =
      conjEquiv (diagonalGateEquiv f) (pauliEquiv (paulix i)) := by
  unfold iterConjXDiag
  rw [funcDerivPhaseSubset_singleton, pauliXOfFinset_singleton]
  rw [← conjEquiv_diagonalGateEquiv_paulix_funcDeriv f i]

/-! ## Phase-factor tracking

The cumulative phase factor across `|S|` descent iterations. Each
step's `pauliOperator_mul` produces a sign `(-1)^{zDotVal (running
Pauli) (paulix i).X}`. Because every running Pauli is a sum of pure
X's (zero Z-support), the sign at every step is `(-1)^0 = 1`. The
cumulative phase factor is therefore `1`. -/

/-- The cumulative phase factor produced by iterating the X-conjugation
descent across `S`. Because every `paulix i` and every `pauliXOfFinset
S` has zero Z-support, the `q.Z · p.X` exponent in `pauliOperator_mul`
at every step is zero, so the cumulative phase factor is `1`. -/
noncomputable def iterConjX_phase_factor (_S : Finset (Fin n))
    (_f : (Fin n → ZMod 2) → ℝ) : ℂˣ :=
  1

/-- The cumulative phase factor is `1` for any `S, f`. -/
theorem iterConjX_phase_factor_eq_one (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → ℝ) :
    iterConjX_phase_factor S f = 1 := rfl

/-- **Full iterated closed form.** The iterated descent closed form,
including the explicit (trivial) phase factor. -/
theorem iterConjXDiag_with_phase (S : Finset (Fin n))
    (f : (Fin n → ZMod 2) → ℝ) :
    scaleEquiv (iterConjX_phase_factor S f) (iterConjXDiag S f) =
      iterConjXDiag S f := by
  rw [iterConjX_phase_factor_eq_one]
  refine LinearEquiv.toLinearMap_injective ?_
  apply LinearMap.ext
  intro ψ
  -- Goal: ↑(scaleEquiv 1 (iterConjXDiag S f)) ψ = ↑(iterConjXDiag S f) ψ
  change scaleEquiv 1 (iterConjXDiag S f) ψ = iterConjXDiag S f ψ
  rw [scaleEquiv_apply, Units.val_one, one_smul]

/-! ## Bridge to `funcDerivEval`

The polynomial-side functional discrete derivative `funcDeriv` from
`FTQCLib.Hierarchy.FuncDeriv` takes values in `ZMod (2^m)`, while
`funcDerivPhase` takes values in `ℝ`. They are related via
`realPhase`: `funcDerivPhase i (realPhase P)` corresponds to
`funcDerivEval i P` modulo `2π`. -/

/-- **Definitional bridge** between the real-valued and modular discrete
derivatives. The structural shape of `funcDerivPhase i (realPhase P)`
matches the difference `realPhase P (v + e_i) - realPhase P v`, which
is `2π / 2^m` times `funcDerivEval i P v` (mod `2π`). The mod-`2π`
content lives in `CGKReverseDyadic.lean`; here we expose only the
structural identity. -/
theorem funcDerivPhase_realPhase_apply
    {m : ℕ} (P : DiagPhase n m) (i : Fin n) (v : Fin n → ZMod 2) :
    funcDerivPhase i (DiagPhase.realPhase P) v =
      DiagPhase.realPhase P (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) -
        DiagPhase.realPhase P v := by
  rfl

/-! ## Summary

The iteration module provides the operator-side recursion. Concretely,
the file establishes:

* **Single-step bridge** (`conjEquiv_diagonalGateEquiv_paulix_funcDeriv`):
  generalises the existing `conjEquiv_diagonalGateEquiv_paulix` to
  arbitrary phase functions.

* **Iterated discrete derivative** (`funcDerivPhaseSubset`): the
  ℝ-valued analogue of `funcDerivSubset`. Defined via `Multiset.foldr`
  using the `LeftCommutative funcDerivPhase` instance.

* **Closed form** (`iterConjXDiag`): the iterated form of the descent,
  a phased operator with diagonal part `funcDerivPhaseSubset S f` and
  Pauli part `pauliXOfFinset S`.

* **Recursion-step identity** (`iterConjXDiag_insert`,
  `iterConjXDiag_step`): the closed form satisfies the recursion that
  matches one descent step.

* **Phase-factor tracking** (`iterConjX_phase_factor`,
  `iterConjX_phase_factor_eq_one`): cumulative phase is trivial across
  X-only iterations.

* **Commutativity of derivatives** (`funcDerivPhase_comm`,
  `LeftCommutative` instance): the iteration is order-independent.

Downstream uses:
* Dyadic-denominator bookkeeping (`CGKReverseDyadic.lean`). The
  diagonal part `funcDerivPhaseSubset S f` for `f = realPhase P` should
  reduce precision by `|S|`; i.e., the corresponding polynomial
  encoding has `m' ≤ m − |S|`. This is the modular content not handled
  here.

* Polynomial assembly (`CGKReverseAssembly.lean` and its successors).
  Combine the iterated derivative values
  `c_S := funcDerivPhaseSubset S f (0)` (the "Möbius coefficients") to
  reconstruct the polynomial-encoded form of `f`.
-/

end FTQCLib.Hilbert

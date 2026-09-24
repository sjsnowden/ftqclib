/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKForward

set_option linter.unusedSectionVars false

/-! # Cui-Gottesman-Krishna, reverse direction (base machinery)

The **reverse direction** of the Cui-Gottesman-Krishna (CGK)
equivalence: a diagonal unitary that sits at level `k` of the
operational Clifford hierarchy admits a polynomial-phase encoding with
`P.level ≤ k`.

CGK 2017 (arXiv:1608.06596) Theorem 2, page 3, gives the single-qudit
statement; Lemma 4, pages 7–8, generalises to `n` qudits. The
operator-side recursion (CGK eq. (7), page 2) says
`U · X(v) · U⁻¹ = V(v) · X(v)` with `V(v) ∈ C_d^{(k)}` for `U ∈
C_d^{(k+1)}`, giving `V(v)` a recursive encoding with one fewer level.

## Möbius inversion replaces Faulhaber/Bernoulli on Boolean inputs

CGK §III's reverse-direction proof (Lemma 2, pages 4–6) invokes
Faulhaber's formula (eq. (53), page 5) to invert the discrete
derivative `Δθ` of a phase polynomial `θ : Z_p → Z_{p^m}`. The
Faulhaber step is required for general `p` because the input domain
`Z_p = {0, …, p−1}` is treated as integer-valued and the phase
polynomials have degree up to `p−1`.

**For `p = 2` (qubits) the Faulhaber apparatus collapses.** The input
domain is Boolean `{0, 1}`, every polynomial reduces to its multilinear
shadow, and the only Faulhaber sum needed is the trivial
`Σ_{k=1}^{j} k = j` on `{0, 1}`. The inversion of `Δθ` on `(F₂)ⁿ` is
exactly **Möbius inversion on the Boolean lattice** with
`μ(R, S) = (−1)^{|S|−|R|}` (Rota 1964 *On the foundations of
combinatorial theory I*).

For `f : (F₂)ⁿ → ℝ/2πℤ`:

  c_S := Δ_S f(0)  (iterated discrete derivative at zero)
  f(v) = Σ_{S ⊆ supp(v)} c_S    (Möbius / Newton-forward inversion)

This Möbius formulation suffices for CGK §III at `p = 2`. The modules
`FTQCLib.Hierarchy.BooleanMobius`, `FTQCLib.Hilbert.CGKReverseIteration`,
`FTQCLib.Hilbert.CGKReverseDyadic` and the assembly
`FTQCLib.Hilbert.CGKReverseAssembly` implement the Boolean version with
no Bernoulli machinery imported.

## What this file delivers (base machinery for the assembly)

* **Structural lemma `Pauli_X_zero_of_diagonal_phasedPauli`**: a phased
  Pauli `α · pauliOperator p` that is also a diagonal gate must have
  `p.X = 0`. Argument: at the computational vector `|0⟩`, the diagonal
  side stays a multiple of `|0⟩` while the Pauli side becomes a multiple
  of `|p.X⟩`; matching forces `p.X = 0`.

* **`phasedZPoly p` / `realPhase_phasedZPoly_eq`**: the polynomial
  encoding of a pure-Z Pauli `p` (with `p.X = 0`) at precision `m' = 1`,
  via the linear polynomial `∑_i (p.Z i).val · X_i` over `ZMod 2`. The
  resulting `realPhase` agrees with the `±1` phase pattern of
  `pauliOperator p`.

* **Base case (no global phase) `cgk_reverse_pure_Z_pauli`**: the
  unsigned diagonal-Z Pauli `pauliEquiv p` (with `p.X = 0`) admits a
  polynomial-phase encoding at precision `m' = 1`, level ≤ 1.

* **Base case (sign global phase) `cgk_reverse_pure_Z_pauli_signed` and
  `cgk_reverse_one_signed`**: the case where the scalar `α` is `±1` —
  i.e., `α = (-1)^c.val` for some `c : ZMod 2` — is closed by the
  combined polynomial `MvPolynomial.C c + phasedZPoly p`.

* **`IsDyadicPhase`, `constPhasePoly`, `realPhase_constPhasePoly`** —
  the constant-phase polynomial at precision `m'` and its `realPhase`
  identification. Lifted in the assembly to package arbitrary dyadic
  global phases.

## Assembly

The final `cgk_reverse_dyadic` is assembled in
`FTQCLib.Hilbert.CGKReverseAssembly`, using:

* this file's `phaseAndZPoly` (`±1` case) and `constPhasePoly`
  (arbitrary dyadic α at precision m') as polynomial witnesses;
* `FTQCLib.Hilbert.HierarchyDyadic.IsCliffordHierarchyDyadic` for the
  tightened operational predicate;
* `FTQCLib.Hilbert.CGKReverseDyadic.isDyadicMod2pi_of_level_one_diagonal`
  as the dyadic anchor at the base of the descent.

## Anchor

* Gottesman–Chuang 1999 (arXiv:quant-ph/9908010) — operational
  hierarchy.
* CGK 2017 (arXiv:1608.06596) Theorem 2 (page 3), Lemma 4 (pages 7–8),
  §III eq. (7), (26)–(27), (45), (62), Lemma 2, Corollary 2.
* Rota 1964 *On the foundations of combinatorial theory I, theory of
  Möbius functions*.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase

variable {n : ℕ}

/-! ## Diagonal phased Paulis have X-support zero

If `U` is both a diagonal gate `diagonalGateEquiv f` and a phased Pauli
`α • pauliOperator p`, then `p.X = 0`. Argument: at the computational
basis vector `|v⟩` with `v = 0`, the diagonal gate produces a multiple
of `|0⟩`, while the Pauli sends it to a multiple of `|p.X⟩`. Matching
forces `|p.X⟩ = |0⟩`, hence `p.X = 0`.
-/

/-- A diagonal phased Pauli has X-support equal to zero. -/
theorem Pauli_X_zero_of_diagonal_phasedPauli
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} {f : (Fin n → ZMod 2) → ℝ}
    {α : ℂˣ} {p : Pauli n}
    (hf : U = diagonalGateEquiv f)
    (hα : U.toLinearMap = (α : ℂ) • (pauliOperator p)) :
    p.X = 0 := by
  -- Apply both forms of U to the computational basis vector |0⟩.
  -- On the diagonal side: diagonalGateEquiv f (computational 0) =
  --   exp(I · f 0) • computational 0 — a multiple of computational 0.
  -- On the Pauli side: (α • pauliOperator p) (computational 0) =
  --   α • ((-1)^0 • computational p.X) = α • computational p.X.
  -- So α • computational p.X = exp(I · f 0) • computational 0 as
  -- functions; evaluating at p.X gives α = (if p.X = 0 then exp ...
  -- else 0). Since α ≠ 0, this forces p.X = 0.
  have h_apply :
      U (computational (0 : Fin n → ZMod 2)) =
        (α : ℂ) • (pauliOperator p) (computational (0 : Fin n → ZMod 2)) := by
    have h := congrArg
      (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) =>
        L (computational (0 : Fin n → ZMod 2)))
      hα
    simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
    exact h
  -- Now use the Pauli action on a computational basis vector.
  rw [pauliOperator_computational p (0 : Fin n → ZMod 2)] at h_apply
  -- pauliOperator p (computational 0) = (-1)^{p.Z · 0} • computational (0 + p.X)
  --                                   = 1 • computational p.X.
  -- Simplify zDotVal p 0 = 0.
  have hzdot : zDotVal p (0 : Fin n → ZMod 2) = 0 := by
    unfold zDotVal
    refine Finset.sum_eq_zero ?_
    intro i _
    have h0 : ((0 : Fin n → ZMod 2) i).val = 0 := by
      change ((0 : ZMod 2)).val = 0
      exact ZMod.val_zero
    rw [h0]; ring
  rw [hzdot, pow_zero] at h_apply
  simp only [one_smul, zero_add] at h_apply
  -- h_apply : U (computational 0) = α • computational p.X.
  -- Also apply the diagonal form.
  have h_diag_apply :
      U (computational (0 : Fin n → ZMod 2)) =
        Complex.exp (Complex.I * f (0 : Fin n → ZMod 2)) •
          computational (0 : Fin n → ZMod 2) := by
    rw [hf, diagonalGateEquiv_apply, diagonalGate_computational]
  -- Combine: α • computational p.X = exp(I·f 0) • computational 0.
  rw [h_diag_apply] at h_apply
  -- h_apply : exp(I·f 0) • computational 0 = α • computational p.X.
  -- Evaluate both sides at p.X.
  have h_eval_pX :
      (Complex.exp (Complex.I * f (0 : Fin n → ZMod 2)) •
          computational (0 : Fin n → ZMod 2)) p.X =
        ((α : ℂ) • computational p.X) p.X :=
    congrFun h_apply p.X
  simp only [Pi.smul_apply, computational_self, smul_eq_mul, mul_one] at h_eval_pX
  -- h_eval_pX : exp(I·f 0) · (computational 0 p.X) = α.
  -- If p.X ≠ 0, then computational 0 p.X = 0, so the LHS = 0; but α ≠ 0. Contradiction.
  by_contra hpX
  have hpX_ne : p.X ≠ 0 := hpX
  have h_comp_zero :
      computational (0 : Fin n → ZMod 2) p.X = 0 :=
    computational_of_ne hpX_ne
  rw [h_comp_zero, mul_zero] at h_eval_pX
  exact (Units.ne_zero α) h_eval_pX.symm

/-! ## The phase pattern of a diagonal Z-Pauli

For `p : Pauli n` with `p.X = 0`, the Pauli operator acts as
`pauliOperator p (computational v) = (-1)^{p.Z · v} • computational v`,
a diagonal gate with the binary phase pattern
`f_p v = π · (p.Z · v mod 2)`. We package this in two forms:

* `phasedZPattern p` — the real-valued phase pattern as a function.
* `phasedZPoly p` — the polynomial encoding at precision `m' = 1`.
-/

/-- The real-valued phase pattern of a pure-Z Pauli `p` (with `p.X = 0`):
the function sending `v` to `π · (p.Z · v mod 2)`. Encodes the diagonal
pattern `exp(I · phase) = (-1)^{p.Z · v}`. -/
noncomputable def phasedZPattern (p : Pauli n) : (Fin n → ZMod 2) → ℝ :=
  fun v => Real.pi * ((zDotVal p v) % 2 : ℕ)

/-- The polynomial encoding of `phasedZPattern p` at precision `m' = 1`:
the linear polynomial `∑_i (p.Z i).val · X_i` over `ZMod 2`. Its
`realPhase` evaluates to `2π · parity / 2 = π · parity` at each `v`. -/
noncomputable def phasedZPoly (p : Pauli n) : DiagPhase n 1 :=
  ∑ i : Fin n, MvPolynomial.C ((p.Z i).val : ZMod 2) * MvPolynomial.X i

/-- Evaluation of `phasedZPoly p` at a binary input `v` gives the
parity of `p.Z · v`, viewed in `ZMod 2`. -/
theorem phasedZPoly_eval (p : Pauli n) (v : Fin n → ZMod 2) :
    (phasedZPoly p).eval v = ((zDotVal p v : ℕ) : ZMod 2) := by
  classical
  unfold phasedZPoly DiagPhase.eval
  rw [map_sum]
  unfold zDotVal
  push_cast
  -- Goal: ∑ i, ((p.Z i).val : ZMod 2) * ((v i).val : ZMod 2)
  --     = (↑(∑ i, (p.Z i).val * (v i).val) : ZMod 2).
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  -- Goal: ((p.Z i).val : ZMod 2) * ((liftBinary v i)) = ...
  -- Note liftBinary v i = ((v i).val : ZMod 2).
  change ((p.Z i).val : ZMod 2) * (DiagPhase.liftBinary v i)
      = ((p.Z i).val : ZMod 2) * ((v i).val : ZMod 2)
  unfold DiagPhase.liftBinary
  rfl

/-- The `realPhase` of `phasedZPoly p` equals `phasedZPattern p`
pointwise. Both evaluate to `π · (p.Z · v mod 2)`. -/
theorem realPhase_phasedZPoly_eq (p : Pauli n) :
    DiagPhase.realPhase (phasedZPoly p) = phasedZPattern p := by
  funext v
  unfold DiagPhase.realPhase phasedZPattern
  rw [phasedZPoly_eval]
  -- Goal: 2π · ((↑(zDotVal p v) : ZMod 2).val : ℝ) / 2^1 = π · ((zDotVal p v % 2 : ℕ) : ℝ).
  change 2 * Real.pi *
        ((((zDotVal p v : ℕ) : ZMod 2)).val : ℝ) / (2 : ℝ)^1
      = Real.pi * (((zDotVal p v) % 2 : ℕ) : ℝ)
  -- The .val of a Nat cast to ZMod 2 is the residue mod 2.
  have h_val : (((zDotVal p v : ℕ) : ZMod 2)).val = (zDotVal p v) % 2 :=
    ZMod.val_natCast 2 (zDotVal p v)
  rw [h_val]
  ring

/-- `(zDotVal p v % 2 : ℕ)` is either `0` or `1`. -/
private lemma zDotVal_mod_two_eq (p : Pauli n) (v : Fin n → ZMod 2) :
    (zDotVal p v) % 2 = 0 ∨ (zDotVal p v) % 2 = 1 := by
  have h := Nat.mod_two_eq_zero_or_one (zDotVal p v)
  exact h

/-- The phase `exp(I · π · k)` for `k : ℕ` equals `(-1)^k`. -/
private lemma exp_I_pi_natCast (k : ℕ) :
    Complex.exp (Complex.I * (Real.pi * (k : ℝ) : ℝ)) = (-1 : ℂ)^k := by
  -- Use `Complex.exp_pi_mul_I^k` style argument.
  -- exp(I · π · k) = (exp(I · π))^k = (-1)^k.
  have hpi : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 :=
    Complex.exp_pi_mul_I
  push_cast
  rw [show Complex.I * ((Real.pi : ℂ) * (k : ℂ))
        = (k : ℂ) * ((Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_nat_mul, hpi]

/-- The diagonal gate produced by `phasedZPattern p` agrees pointwise
with the action of `pauliOperator p` (when `p.X = 0`). Specifically:
both send `ψ` to `v ↦ (-1)^{p.Z · v} · ψ v`. -/
theorem diagonalGate_phasedZPattern_eq (p : Pauli n) (_hpX : p.X = 0)
    (ψ : QubitSpace n) (v : Fin n → ZMod 2) :
    diagonalGate (phasedZPattern p) ψ v = ((-1 : ℂ)^(zDotVal p v)) * ψ v := by
  rw [diagonalGate_apply]
  unfold phasedZPattern
  congr 1
  -- Goal: exp(I · π · (k mod 2)) = (-1)^k for k = zDotVal p v.
  set k := zDotVal p v
  -- Use exp_I_pi_natCast at k % 2 and connect to (-1)^k.
  have h_exp := exp_I_pi_natCast (k % 2)
  -- Convert ((k % 2 : ℕ) : ℝ) to ((k % 2 : ℕ) : ℝ) since the form is already there.
  push_cast
  rw [show Complex.I * ((Real.pi : ℂ) * ((k % 2 : ℕ) : ℂ)) =
        Complex.I * (Real.pi * ((k % 2 : ℕ) : ℝ) : ℝ) from by push_cast; ring]
  rw [h_exp]
  -- Goal: (-1)^(k % 2) = (-1)^k. Reduce both to parity.
  have h_mod : k % 2 = k % 2 := rfl
  -- (-1)^k = (-1)^(k mod 2) since (-1)^2 = 1.
  have h_pow_mod : ((-1 : ℂ))^k = ((-1 : ℂ))^(k % 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul]
    have hsq : ((-1 : ℂ))^2 = 1 := by norm_num
    rw [hsq, one_pow, one_mul]
  rw [h_pow_mod]

/-- The diagonal-gate equivalence `diagonalGateEquiv (phasedZPattern p)`
agrees as a linear map with `pauliOperator p` when `p.X = 0`. -/
theorem diagonalGateEquiv_phasedZPattern_eq_pauliOperator
    (p : Pauli n) (hpX : p.X = 0) :
    (diagonalGateEquiv (phasedZPattern p)).toLinearMap = pauliOperator p := by
  apply LinearMap.ext
  intro ψ
  funext v
  rw [diagonalGateEquiv_toLinearMap]
  rw [diagonalGate_phasedZPattern_eq p hpX]
  -- Goal: (-1)^{p.Z · v} * ψ v = pauliOperator p ψ v.
  unfold pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [hpX, sub_zero]

/-! ## Base case for the reverse direction: identity (and trivial-phase) U

The simplest reverse direction, needing no
Faulhaber/Bernoulli machinery, is for `U` that is a *pure* (un-scaled)
diagonal Pauli — i.e., `U = pauliEquiv p` for some `p` with `p.X = 0`.
These `U` exhaust the diagonal part of the operational level 1 modulo
a global phase. The polynomial witness is `phasedZPoly p` over `ZMod 2`
(precision `m' = 1`, level 1).
-/

/-- **Reverse direction at level 1 (no global phase)**: the diagonal
Pauli `pauliEquiv p` (with `p.X = 0`) admits a polynomial-phase encoding
at precision `m' = 1`, level 1. -/
theorem cgk_reverse_pure_Z_pauli (p : Pauli n) (hpX : p.X = 0) :
    ∃ (m' : ℕ) (P : DiagPhase n m'),
      pauliEquiv p = diagonalGateEquiv (DiagPhase.realPhase P) ∧
      P.level ≤ 1 := by
  refine ⟨1, phasedZPoly p, ?_, ?_⟩
  · -- pauliEquiv p = diagonalGateEquiv (realPhase (phasedZPoly p)).
    refine LinearEquiv.toLinearMap_injective ?_
    rw [diagonalGateEquiv_toLinearMap]
    -- Goal: (pauliEquiv p).toLinearMap = diagonalGate (realPhase (phasedZPoly p)).
    -- pauliEquiv p is defined as having forward map pauliOperator p.
    have h_pe : (pauliEquiv p).toLinearMap = pauliOperator p := rfl
    rw [h_pe]
    rw [realPhase_phasedZPoly_eq]
    -- Goal: pauliOperator p = diagonalGate (phasedZPattern p).
    apply LinearMap.ext
    intro ψ
    funext v
    rw [diagonalGate_phasedZPattern_eq p hpX]
    unfold pauliOperator
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [hpX, sub_zero]
  · -- Level: phasedZPoly p is a sum of degree-1 monomials at m' = 1.
    -- level = (1 - 1) + totalDegree = 0 + totalDegree ≤ 1.
    unfold DiagPhase.level
    -- Goal: (1 - 1) + totalDegree (phasedZPoly p) ≤ 1.
    simp only [Nat.sub_self, zero_add]
    -- Show totalDegree ≤ 1.
    unfold phasedZPoly
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
    refine Finset.sup_le ?_
    intro i _
    -- totalDegree (C c * X i) ≤ totalDegree C c + totalDegree X i.
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C]
    -- Goal: 0 + totalDegree (X i) ≤ 1.
    rw [zero_add]
    -- totalDegree X i ≤ 1 unconditionally (it equals 1 when Nontrivial, 0 otherwise).
    have h : (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2 ^ 1))) =
        MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 1)) := by
      rw [MvPolynomial.X, MvPolynomial.monomial]
    rw [h]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    simp [Finsupp.sum_single_index]

/-! ## Generic level-1 reverse direction with dyadic-phase hypothesis

A general level-1 element of the operational hierarchy is `α • pauliOperator p`
for any unit `α : ℂˣ` and any `p : Pauli n`. The reverse direction
requires:

1. **`p.X = 0`** (proved above: forced by diagonal-ness).
2. **A polynomial representation of the global phase `α`**.

For (2), if `α = exp(I · θ)` with `θ` a dyadic-rational multiple of
`2π`, we can absorb the global phase into the polynomial. For general
`α`, no finite precision `m'` suffices, which is the **encoding
obstruction**.

The hypothesis below makes (2) explicit by asking for a `θ : ℝ` that
witnesses `α = exp(I θ)` and a precision `m'` together with `c : ZMod (2^{m'})`
witnessing `θ = 2π · c.val / 2^{m'}` modulo `2π`.
-/

/-- A unit complex scalar `α` is **dyadic-phase encodable** at precision
`m'` if there exists `c : ZMod (2^{m'})` such that
`α = exp(I · 2π · c.val / 2^{m'})`. Equivalently, `α` is a `2^{m'}`-th
root of unity (allowing global phase rounding). -/
def IsDyadicPhase (α : ℂˣ) (m' : ℕ) : Prop :=
  ∃ c : ZMod (2 ^ m'),
    (α : ℂ) = Complex.exp (Complex.I *
      (((2 * Real.pi * (c.val : ℝ) / (2 : ℝ)^m') : ℝ) : ℂ))

/-- The constant phase polynomial at precision `m'`: the constant
polynomial `C c` over `ZMod (2^{m'})`. -/
noncomputable def constPhasePoly (n m' : ℕ) (c : ZMod (2 ^ m')) :
    DiagPhase n m' :=
  MvPolynomial.C c

/-- The real-phase of `constPhasePoly n m' c` at every input is the
constant `2π · c.val / 2^{m'}`. -/
theorem realPhase_constPhasePoly (n m' : ℕ) (c : ZMod (2 ^ m'))
    (v : Fin n → ZMod 2) :
    DiagPhase.realPhase (constPhasePoly n m' c) v =
      2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ m' := by
  unfold DiagPhase.realPhase DiagPhase.eval constPhasePoly
  rw [MvPolynomial.eval_C]

/-- The total degree of `constPhasePoly n m' c` is `0`. -/
theorem constPhasePoly_totalDegree (n m' : ℕ) (c : ZMod (2 ^ m')) :
    (constPhasePoly n m' c).totalDegree = 0 := by
  unfold constPhasePoly
  exact MvPolynomial.totalDegree_C c

/-- The level of `constPhasePoly n m' c` is `m' - 1`. -/
theorem constPhasePoly_level (n m' : ℕ) (c : ZMod (2 ^ m')) :
    (constPhasePoly n m' c).level = m' - 1 := by
  unfold DiagPhase.level
  rw [constPhasePoly_totalDegree]
  omega

/-! ### Reverse direction at level 1 with global phase ±1

The simplest extension of `cgk_reverse_pure_Z_pauli` adds the `α = ±1`
case: combine the Z-pattern polynomial `phasedZPoly p` with a constant
`c ∈ ZMod 2` (precision 1). For `c = 0` the constant phase is `1`; for
`c = 1` it is `-1`. Both stay at level 1.

A general dyadic `α` (e.g. `α = i` requires `m' = 2` for c = 1) needs
the Z-pattern lifted to precision `m'`; see
`FTQCLib.Hilbert.CGKReverseAssembly`.
-/

/-- The combined polynomial encoding a constant phase `c ∈ ZMod 2` and a
diagonal Z-Pauli `p` at precision 1. -/
noncomputable def phaseAndZPoly (c : ZMod 2) (p : Pauli n) : DiagPhase n 1 :=
  MvPolynomial.C c + phasedZPoly p

/-- The eval of `phaseAndZPoly c p` at `v` is `c + parity(p.Z · v)`. -/
theorem phaseAndZPoly_eval (c : ZMod 2) (p : Pauli n) (v : Fin n → ZMod 2) :
    (phaseAndZPoly c p).eval v = c + ((zDotVal p v : ℕ) : ZMod 2) := by
  unfold phaseAndZPoly DiagPhase.eval
  rw [map_add, MvPolynomial.eval_C]
  congr 1
  exact phasedZPoly_eval p v

/-- The total degree of `phaseAndZPoly c p` is bounded by 1: the constant
contributes degree 0 and `phasedZPoly p` has degree ≤ 1. -/
theorem phaseAndZPoly_totalDegree_le (c : ZMod 2) (p : Pauli n) :
    (phaseAndZPoly c p).totalDegree ≤ 1 := by
  unfold phaseAndZPoly
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [MvPolynomial.totalDegree_C]
  -- Goal: max 0 (phasedZPoly p).totalDegree ≤ 1.
  refine max_le (Nat.zero_le _) ?_
  unfold phasedZPoly
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le ?_
  intro i _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  have h : (MvPolynomial.X i : MvPolynomial (Fin n) (ZMod (2 ^ 1))) =
      MvPolynomial.monomial (Finsupp.single i 1) (1 : ZMod (2 ^ 1)) := by
    rw [MvPolynomial.X, MvPolynomial.monomial]
  rw [h]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  simp [Finsupp.sum_single_index]

/-- The level of `phaseAndZPoly c p` is at most 1. -/
theorem phaseAndZPoly_level_le_one (c : ZMod 2) (p : Pauli n) :
    (phaseAndZPoly c p).level ≤ 1 := by
  unfold DiagPhase.level
  have h := phaseAndZPoly_totalDegree_le c p
  omega

/-- The real-phase of `phaseAndZPoly c p` at `v` equals
`π · ((c + parity(p.Z · v)) mod 2)`, viewed as a real number. -/
theorem realPhase_phaseAndZPoly (c : ZMod 2) (p : Pauli n)
    (v : Fin n → ZMod 2) :
    DiagPhase.realPhase (phaseAndZPoly c p) v =
      Real.pi * (((c + ((zDotVal p v : ℕ) : ZMod 2)).val : ℕ) : ℝ) := by
  unfold DiagPhase.realPhase
  rw [phaseAndZPoly_eval]
  -- Goal: 2π · (eval).val / 2^1 = π · (eval).val.
  push_cast
  ring

/-- **Reverse direction at level 1 with sign global phase ±1**: for
diagonal `U` of the form `α • pauliOperator p` with `α ∈ {1, -1}` and
`p.X = 0`, the gate admits a polynomial-phase encoding at precision 1,
level ≤ 1.

The hypothesis `hα` packages the sign as `α = (-1)^{c.val}` for some
`c : ZMod 2`. -/
theorem cgk_reverse_pure_Z_pauli_signed
    {α : ℂˣ} (c : ZMod 2)
    (hα : (α : ℂ) = (-1 : ℂ) ^ c.val)
    (p : Pauli n) (hpX : p.X = 0) :
    ∃ (m' : ℕ) (P : DiagPhase n m'),
      scaleEquiv α (pauliEquiv p) =
        diagonalGateEquiv (DiagPhase.realPhase P) ∧
      P.level ≤ 1 := by
  refine ⟨1, phaseAndZPoly c p, ?_, phaseAndZPoly_level_le_one c p⟩
  refine LinearEquiv.toLinearMap_injective ?_
  rw [diagonalGateEquiv_toLinearMap]
  apply LinearMap.ext
  intro ψ
  funext v
  -- LHS: scaleEquiv α (pauliEquiv p) ψ v = α • (pauliOperator p ψ) v
  --   = α · (-1)^{p.Z · (v - p.X)} · ψ (v - p.X)
  --   = α · (-1)^{p.Z · v} · ψ v          [using p.X = 0]
  -- RHS: diagonalGate (realPhase (phaseAndZPoly c p)) ψ v
  --   = exp(I · realPhase ...) · ψ v
  --   = exp(I · π · ((c + parity(p.Z·v)) mod 2)) · ψ v
  --   = (-1)^((c + parity(p.Z·v)) mod 2) · ψ v
  --   = (-1)^{c.val + p.Z · v} · ψ v    [parity is additive]
  --   = α · (-1)^{p.Z · v} · ψ v.
  rw [scaleEquiv_toLinearMap]
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, Pi.smul_apply, smul_eq_mul]
  -- LHS: α • (pauliEquiv p ψ v) = α · pauliOperator p ψ v.
  change (α : ℂ) * pauliOperator p ψ v
        = diagonalGate (DiagPhase.realPhase (phaseAndZPoly c p)) ψ v
  rw [diagonalGate_apply, realPhase_phaseAndZPoly]
  -- LHS: α · pauliOp p ψ v. Unfold pauliOp using p.X = 0.
  unfold pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [hpX, sub_zero]
  -- LHS: α · (-1)^{p.Z · v} · ψ v.
  -- RHS: exp(I · π · ((c + parity)..val)) · ψ v.
  rw [hα]
  -- Combine into form: (-1)^c.val · (-1)^{p.Z · v} · ψ v
  --                 = exp(I · π · (c + parity).val) · ψ v.
  -- Simplify the RHS exp term using exp_I_pi_natCast.
  have h_exp : Complex.exp (Complex.I *
        ((Real.pi *
            (((c + ((zDotVal p v : ℕ) : ZMod 2)).val : ℕ) : ℝ) : ℝ) : ℂ))
        = (-1 : ℂ) ^ ((c + ((zDotVal p v : ℕ) : ZMod 2)).val) := by
    exact exp_I_pi_natCast _
  rw [h_exp]
  -- Goal: (-1)^c.val · ((-1)^{p.Z·v} · ψ v)
  --     = (-1)^((c + parity).val) · ψ v.
  -- We need: (-1)^c.val * (-1)^{p.Z·v} = (-1)^((c + parity(p.Z·v)).val).
  -- Both sides depend only on parity, and parity (c.val + p.Z·v) = (c + parity(p.Z·v)).val.
  have helper : ∀ a b : ℕ, a % 2 = b % 2 → ((-1 : ℂ))^a = ((-1 : ℂ))^b := by
    intro a b h
    have hpow : ∀ k : ℕ, ((-1 : ℂ))^k = ((-1 : ℂ))^(k % 2) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k 2]
      rw [pow_add, pow_mul]
      have hsq : ((-1 : ℂ))^2 = 1 := by norm_num
      rw [hsq, one_pow, one_mul]
    rw [hpow a, hpow b, h]
  -- Parity fact: c.val + zDotVal p v ≡ (c + ((zDotVal p v : ℕ) : ZMod 2)).val (mod 2).
  have h_parity : (c.val + zDotVal p v) % 2
                = (c + ((zDotVal p v : ℕ) : ZMod 2)).val % 2 := by
    have h_zmod_eq :
        ((c.val + zDotVal p v : ℕ) : ZMod 2)
          = ((c + ((zDotVal p v : ℕ) : ZMod 2)).val : ZMod 2) := by
      rw [ZMod.natCast_zmod_val (c + ((zDotVal p v : ℕ) : ZMod 2))]
      push_cast
      rw [ZMod.natCast_zmod_val c]
    have := (ZMod.natCast_eq_natCast_iff _ _ 2).mp h_zmod_eq
    rw [Nat.ModEq] at this
    exact this
  -- Conclude: (-1)^(c.val + zDot) = (-1)^((c + parity).val), then split the LHS.
  have h_combined : ((-1 : ℂ))^c.val * ((-1 : ℂ))^(zDotVal p v)
                  = ((-1 : ℂ))^(c + ((zDotVal p v : ℕ) : ZMod 2)).val := by
    rw [← pow_add]
    exact helper _ _ h_parity
  -- Goal (after ring_nf may have happened): match with ψ v as a common factor.
  linear_combination (ψ v) * h_combined

/-! ## Reverse direction at k = 1 (with sign-only global-phase hypothesis)

Combining `Pauli_X_zero_of_diagonal_phasedPauli` (structural: diagonal
forces `p.X = 0`) and `cgk_reverse_pure_Z_pauli_signed` (constructive:
±1 phase plus pure-Z Pauli yields a level-1 polynomial), we get the
level-1 reverse direction for `U` whose phased-Pauli witness has the
form `α = (-1)^c.val` for some `c : ZMod 2`.

For general unit `α`, the encoding obstruction means no finite-precision
polynomial witness exists.
-/

/-- **The k = 1 case of the reverse direction (sign-only global phase)**.
For diagonal `U` at level 1 whose `IsPhasedPauli` witness has a scalar
of the form `(-1)^c.val` for some `c : ZMod 2`, there is a polynomial
witness at precision 1, level ≤ 1.

The general levels are treated in `FTQCLib.Hilbert.CGKReverseGeneral`
and the files it feeds. -/
theorem cgk_reverse_one_signed
    {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    {α : ℂˣ} {p : Pauli n}
    (hα_eq : U.toLinearMap = (α : ℂ) • (pauliOperator p))
    {c : ZMod 2} (hα_sign : (α : ℂ) = (-1 : ℂ) ^ c.val) :
    ∃ (m' : ℕ) (P : DiagPhase n m'),
      U = diagonalGateEquiv (DiagPhase.realPhase P) ∧
      P.level ≤ 1 := by
  -- Extract p.X = 0 from diagonal hypothesis.
  obtain ⟨f, hf⟩ := h_diag
  have hpX : p.X = 0 :=
    Pauli_X_zero_of_diagonal_phasedPauli hf hα_eq
  -- Identify U with scaleEquiv α (pauliEquiv p).
  have hU_eq : U = scaleEquiv α (pauliEquiv p) := by
    refine LinearEquiv.toLinearMap_injective ?_
    rw [hα_eq]
    rw [scaleEquiv_toLinearMap]
    rfl
  rw [hU_eq]
  exact cgk_reverse_pure_Z_pauli_signed c hα_sign p hpX

/-! ## The full reverse direction

The general statement is assembled from:

* The tightened hierarchy `IsCliffordHierarchyDyadic`
  (`FTQCLib.Hilbert.HierarchyDyadic`), which addresses the dyadic-phase
  encoding obstruction: base-case scalars are required to be `2^{m'}`-th
  roots of unity.

* The Möbius-inversion machinery
  (`FTQCLib.Hierarchy.BooleanMobius`,
  `FTQCLib.Hilbert.CGKReverseIteration`,
  `FTQCLib.Hilbert.CGKReverseDyadic`), which replaces the
  Faulhaber/Bernoulli reconstruction of CGK §III.

The `±1`-phase level-1 case `cgk_reverse_one_signed` (above) is the
base case on the operator side. `FTQCLib.Hilbert.CGKReverseAssembly`
treats level 1 with arbitrary dyadic α; `FTQCLib.Hilbert.CGKReverseGeneral`
treats every level `k ≥ 1`; the sharp projective form is
`cgk_reverse_projective_sharp` in `FTQCLib.Hilbert.CGKTwoSided`. -/

end FTQCLib.Hilbert

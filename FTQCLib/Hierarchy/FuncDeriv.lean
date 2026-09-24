/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.Descent
import Mathlib.Tactic.IntervalCases

set_option linter.unusedSectionVars false

/-! # Functional discrete derivative on the qubit phase space

The polynomial-side `discreteDeriv i P := bind₁ (X_i ↦ X_i + 1) P − P`
defined in `FTQCLib/Hierarchy/Defs.lean` is the natural polynomial
substitution for a unit shift in `X_i`. Evaluated at a `ZMod (2^m)`-
valued input it produces the correct *polynomial* derivative. But the
diagonal-unitary descent rule
`U_P · X_i · U_P† = X_i · U_{Δ_i P}`
operates on binary inputs `v ∈ (F₂)ⁿ`, and there `Δ_i` means the
*Boolean* shift `v ↦ v + e_i`. These two shifts disagree:

* The polynomial shift sends `liftBinary v` to `liftBinary v + 1` in
  `ZMod (2^m)`. If `v_i = 1` the new value is `2`, not `0`.
* The Boolean shift sends `v` to `v + e_i` in `(F₂)ⁿ`, then lifts;
  the `i`-th coordinate flips between `0` and `1` in `ZMod (2^m)`.

For `m = 1` (i.e. `ZMod 2`) these agree because `2 = 0`. For `m ≥ 2`
they diverge.

This file introduces the *functional* discrete derivative

  `funcDeriv i f v := f (v + e_i) − f v`,                  -- f : (F₂)ⁿ → ZMod (2^m)

bridges it to a polynomial substitution that does match it on binary
inputs, and proves the partial structural facts available without
invoking the 2-adic refinement of `ZMod (2^m)`.

## Key construction

The polynomial substitution `X_i ↦ 1 − X_i` realises the Boolean shift
exactly on binary inputs: at `x ∈ {0, 1}` we have `1 − x ∈ {1, 0}`,
matching the bit-flip. So we define

  `shiftDeriv i P := bind₁ (X_i ↦ 1 − X_i) P − P`,

and prove **the eval-shift bridge**

  `(shiftDeriv i P).eval (liftBinary v)
     = P.eval (liftBinary (v + e_i)) − P.eval (liftBinary v)`.

This is the analogue of Target A from `FTQCLib/Hilbert/CGKForward.lean`
where `discreteDeriv` is replaced by the binary-correct `shiftDeriv`.
Total-degree non-increase is proved alongside. The strict-drop direction
at the polynomial-degree level alone is **not** provable — see the
"Remaining block" section at the end of this file.
-/

namespace FTQCLib.Hierarchy

open FTQCLib.Pauli

namespace DiagPhase

variable {n m : ℕ}

/-- The **functional discrete derivative** on phase functions
`f : (F₂)ⁿ → ZMod (2^m)`. At `v ∈ (F₂)ⁿ` it returns
`f (v + e_i) − f v`, where `+` is mod-2 addition in `(F₂)ⁿ` (XOR).
This is the operator-side phase difference produced by conjugating
`U_f` by the Pauli `X_i`: applied to `|v⟩`, `X_i U_f X_i` introduces
phase `e^{2πi · (f(v ⊕ e_i) − f(v)) / 2^m}` relative to `U_f`. -/
noncomputable def funcDeriv (i : Fin n)
    (f : (Fin n → ZMod 2) → ZMod (2 ^ m)) :
    (Fin n → ZMod 2) → ZMod (2 ^ m) :=
  fun v => f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) - f v

/-- The functional discrete derivative of the *evaluation function*
`v ↦ P.eval v` of a polynomial phase `P`. This is the F₂-side phase
shift the operator-side descent actually wants; the polynomial-side
`discreteDeriv` does not match it on inputs with `v_i = 1`. -/
noncomputable def funcDerivEval (i : Fin n) (P : DiagPhase n m) :
    (Fin n → ZMod 2) → ZMod (2 ^ m) :=
  funcDeriv i P.eval

lemma funcDeriv_apply (i : Fin n)
    (f : (Fin n → ZMod 2) → ZMod (2 ^ m)) (v : Fin n → ZMod 2) :
    funcDeriv i f v
      = f (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) - f v :=
  rfl

lemma funcDerivEval_apply (i : Fin n) (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    funcDerivEval i P v
      = P.eval (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
          - P.eval v :=
  rfl

/-! ### The eval-shift bridge polynomial `shiftDeriv`

The substitution `X_i ↦ 1 − X_i` is the polynomial expression of the
bit-flip on `{0, 1}`. We define `shiftDeriv i P` as this substitution
minus `P` itself, mirroring the structure of `discreteDeriv` but using
the binary-correct shift. -/

/-- Helper: the substitution that realises the Boolean shift `v ↦ v + e_i`
on `(F₂)ⁿ` (lifted to `ZMod (2^m)` via `liftBinary`). Sends `X_i` to
`1 − X_i` (so `0 ↔ 1` on binary inputs) and `X_k` to `X_k` otherwise. -/
noncomputable def flipShift (i : Fin n) (k : Fin n) :
    MvPolynomial (Fin n) (ZMod (2 ^ m)) :=
  if k = i then (1 - MvPolynomial.X k) else MvPolynomial.X k

/-- The polynomial whose evaluation on `liftBinary v` realises the
Boolean shift `v ↦ v + e_i`: substituting `X_i ↦ 1 − X_i` produces, on
binary inputs, the value of `P` at the flipped vector. The polynomial-
side discrete derivative `shiftDeriv i P` is this substitution minus
`P`, by analogy with `discreteDeriv` (which uses `X_i ↦ X_i + 1`).

Unlike `discreteDeriv`, evaluating `shiftDeriv i P` at `liftBinary v`
**does** match `P.eval (liftBinary (v + e_i)) − P.eval (liftBinary v)`
on every binary input — see `shiftDeriv_eval_eq_funcDerivEval`. -/
noncomputable def shiftDeriv (i : Fin n) (P : DiagPhase n m) :
    DiagPhase n m :=
  MvPolynomial.bind₁ (flipShift (m := m) i) P - P

/-- Unfold `shiftDeriv` to its `bind₁` form. -/
private lemma shiftDeriv_eq (i : Fin n) (P : DiagPhase n m) :
    shiftDeriv i P = MvPolynomial.bind₁ (flipShift (m := m) i) P - P :=
  rfl

/-! ### The eval-shift bridge

The substitution `X_i ↦ 1 − X_i` is exactly what is needed to make the
polynomial-side computation agree with the Boolean-side shift on
binary inputs. The key identity is:

  `eval (liftBinary v) (flipShift i k) = liftBinary (v + e_i) k`

for every `k`. -/

/-- A `ZMod 2` element is either `0` or `1`. Proved via `interval_cases`
on `a.val < 2`. -/
private lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hval : a = (a.val : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  -- Case-split on `a.val < 2` via `interval_cases`.
  interval_cases a.val
  · left; rw [hval]; norm_cast
  · right; rw [hval]; norm_cast

/-- **Key bridge identity**: evaluating `flipShift i k` at the lifted
binary vector `liftBinary v` reproduces the `k`-th coordinate of the
*flipped* lift `liftBinary (v + e_i)`. The case `k ≠ i` is immediate
because `flipShift` is the identity off `i`. The case `k = i` reduces
to the two-element check that flipping a bit interchanges `0` and `1`
when lifted into `ZMod (2^m)`. -/
private lemma eval_flipShift_apply (i k : Fin n) (v : Fin n → ZMod 2) :
    MvPolynomial.eval (liftBinary (m := m) v) (flipShift (m := m) i k)
      = (liftBinary (m := m)
          (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))) k := by
  unfold flipShift
  split_ifs with hki
  · -- k = i: target `1 - (v i).val = ((v i + 1)).val` in ZMod (2^m).
    subst hki
    rw [map_sub, map_one, MvPolynomial.eval_X]
    unfold liftBinary
    -- The `+ 1` is on the `k`-th coordinate, via `Pi.add_apply` + `Pi.single`.
    have hsingle :
        (Pi.single k (1 : ZMod 2) : Fin n → ZMod 2) k = 1 := by
      simp
    have hadd :
        (v + (Pi.single k (1 : ZMod 2) : Fin n → ZMod 2)) k = v k + 1 := by
      change v k + (Pi.single k (1 : ZMod 2) : Fin n → ZMod 2) k = v k + 1
      rw [hsingle]
    rw [hadd]
    -- Case on `v k ∈ {0, 1}`.
    rcases zmod_two_cases (v k) with hvk | hvk
    · -- v k = 0: LHS = 1 - 0 = 1; RHS = ((0 + 1) : ZMod 2).val = 1.
      rw [hvk, zero_add]
      haveI : Fact (1 < 2) := ⟨Nat.one_lt_two⟩
      rw [ZMod.val_one 2, ZMod.val_zero]
      push_cast; ring
    · -- v k = 1: LHS = 1 - 1 = 0; RHS = ((1 + 1) : ZMod 2).val = 0.
      rw [hvk]
      haveI : Fact (1 < 2) := ⟨Nat.one_lt_two⟩
      rw [ZMod.val_one 2]
      have h1plus1 : (1 + 1 : ZMod 2) = 0 := by decide
      rw [h1plus1, ZMod.val_zero]
      push_cast; ring
  · -- k ≠ i: target `liftBinary v k = liftBinary v k`.
    rw [MvPolynomial.eval_X]
    unfold liftBinary
    -- `(v + Pi.single i 1) k = v k` since `Pi.single i 1 k = 0`.
    have hzero :
        (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = 0 := by
      simp [hki]
    have hadd :
        (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) k = v k := by
      change v k + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) k = v k
      rw [hzero, add_zero]
    rw [hadd]

/-- **The eval-shift bridge** (`shiftDeriv` version of Target A). The
polynomial `shiftDeriv i P` evaluated at `liftBinary v` returns the
functional discrete derivative of `P.eval` at `v`.

Proof strategy: use `MvPolynomial.aeval_bind₁` (equivalently
`eval_assoc`) to reduce `eval (liftBinary v) (bind₁ (flipShift i) P)`
to `eval (eval (liftBinary v) ∘ flipShift i) P`, then observe that this
composite agrees with `eval (liftBinary (v + e_i)) P` because of the
`eval_flipShift_apply` bridge. -/
theorem shiftDeriv_eval (i : Fin n) (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    MvPolynomial.eval (liftBinary v) (shiftDeriv i P)
      = MvPolynomial.eval
          (liftBinary (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))) P
        - MvPolynomial.eval (liftBinary v) P := by
  rw [shiftDeriv_eq, map_sub]
  -- Reduce the `bind₁` term via `eval_assoc`.
  congr 1
  -- Goal: eval (liftBinary v) (bind₁ (flipShift i) P)
  --     = eval (liftBinary (v + e_i)) P.
  -- Use `aeval_bind₁`: aeval f (bind₁ g P) = aeval (fun i => aeval f (g i)) P.
  -- Here `f = liftBinary v`, `g = flipShift i`, and `aeval = eval` since the
  -- target ring `ZMod (2^m)` matches the coefficient ring.
  have h := MvPolynomial.aeval_bind₁
      (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
      (liftBinary (m := m) v) (flipShift (m := m) i) P
  -- `bind₁ = aeval` and `aeval f` (with target the same ring) equals `eval f`.
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  -- Goal: eval (fun k => eval (liftBinary v) (flipShift i k)) P
  --     = eval (liftBinary (v + Pi.single i 1)) P.
  -- The two `eval` functions agree because their argument functions agree
  -- pointwise via `eval_flipShift_apply`.
  have hfun : (fun k : Fin n =>
      MvPolynomial.eval (liftBinary (m := m) v) (flipShift (m := m) i k))
      = liftBinary (m := m)
          (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) := by
    funext k
    exact eval_flipShift_apply i k v
  rw [hfun]

/-- **Eval-shift bridge for `funcDerivEval`**: the polynomial
`shiftDeriv i P` realises the functional derivative `funcDerivEval i P`
on every binary input. -/
theorem shiftDeriv_eval_eq_funcDerivEval (i : Fin n) (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    (shiftDeriv i P).eval v = funcDerivEval i P v := by
  unfold funcDerivEval funcDeriv DiagPhase.eval
  exact shiftDeriv_eval i P v

/-! ### Total-degree non-increase

`shiftDeriv` does not raise the total degree. The proof is structurally
identical to `discreteDeriv_totalDegree_le` (in `Descent.lean`): each
substitution `flipShift i k` has total degree at most 1, and `bind₁`
of a degree-≤1 substitution doesn't raise the degree of any monomial.
We re-do the argument here because the substitution is `1 − X i`
rather than `X i + 1`; the monomial bound is the same. -/

/-- `X k` has total degree at most 1 in any `ZMod (2^m)`. (When the
ring is nontrivial this is an equality.) -/
private lemma totalDegree_X_le_one' (k : Fin n) :
    (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree ≤ 1 := by
  have h : (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))) =
      MvPolynomial.monomial (Finsupp.single k 1) (1 : ZMod (2 ^ m)) := by
    rw [MvPolynomial.X, MvPolynomial.monomial]
  rw [h]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  simp [Finsupp.sum_single_index]

/-- Each `flipShift i k` has total degree at most 1. -/
private lemma flipShift_totalDegree_le (i k : Fin n) :
    (flipShift (m := m) i k).totalDegree ≤ 1 := by
  unfold flipShift
  split_ifs with hk
  · -- 1 - X k.
    calc (1 - MvPolynomial.X k :
            MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
        ≤ max (1 : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree
            (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod (2 ^ m))).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ max 0 1 := by
          gcongr
          · rw [MvPolynomial.totalDegree_one]
          · exact totalDegree_X_le_one' k
      _ = 1 := by simp
  · -- X k.
    exact totalDegree_X_le_one' k

/-- Monomial-level bound: `bind₁ (flipShift i)` applied to a single
monomial yields a polynomial of total degree at most the monomial's
own degree `d.sum`. -/
private lemma bind₁_flipShift_monomial_totalDegree_le (i : Fin n)
    (d : Fin n →₀ ℕ) (c : ZMod (2 ^ m)) :
    (MvPolynomial.bind₁ (flipShift (m := m) i)
        (MvPolynomial.monomial d c)).totalDegree ≤ d.sum (fun _ e => e) := by
  rw [MvPolynomial.bind₁_monomial]
  calc (MvPolynomial.C c *
          ∏ k ∈ d.support, flipShift (m := m) i k ^ d k).totalDegree
      ≤ (MvPolynomial.C c).totalDegree
        + (∏ k ∈ d.support, flipShift (m := m) i k ^ d k).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = (∏ k ∈ d.support, flipShift (m := m) i k ^ d k).totalDegree := by
        rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ ∑ k ∈ d.support, (flipShift (m := m) i k ^ d k).totalDegree :=
        MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ k ∈ d.support, d k * (flipShift (m := m) i k).totalDegree := by
        gcongr with k _
        exact MvPolynomial.totalDegree_pow _ _
    _ ≤ ∑ k ∈ d.support, d k * 1 := by
        gcongr with k _
        exact flipShift_totalDegree_le i k
    _ = ∑ k ∈ d.support, d k := by simp
    _ = d.sum (fun _ e => e) := rfl

/-- `bind₁ (flipShift i)` does not raise total degree. -/
private lemma bind₁_flipShift_totalDegree_le (i : Fin n) (P : DiagPhase n m) :
    (MvPolynomial.bind₁ (flipShift (m := m) i) P).totalDegree
      ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum, map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro d hd
  refine (bind₁_flipShift_monomial_totalDegree_le i d (P.coeff d)).trans ?_
  exact MvPolynomial.le_totalDegree hd

/-- **Easy descent bound for `shiftDeriv`**: total degree does not
increase. -/
theorem shiftDeriv_totalDegree_le (i : Fin n) (P : DiagPhase n m) :
    (shiftDeriv i P).totalDegree ≤ P.totalDegree := by
  rw [shiftDeriv_eq]
  calc (MvPolynomial.bind₁ (flipShift (m := m) i) P - P).totalDegree
      ≤ max (MvPolynomial.bind₁ (flipShift (m := m) i) P).totalDegree
          P.totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max P.totalDegree P.totalDegree :=
        max_le_max (bind₁_flipShift_totalDegree_le i P) le_rfl
    _ = P.totalDegree := max_self _

/-! ### Trivial-case structure

When `P.totalDegree = 0`, `P` is constant and `shiftDeriv i P = 0`
identically. This handles the base of the induction in CGK-forward.
-/

/-- `shiftDeriv` annihilates the zero polynomial. -/
@[simp] theorem shiftDeriv_zero (i : Fin n) :
    shiftDeriv (m := m) i 0 = 0 := by
  rw [shiftDeriv_eq]; simp

/-- `shiftDeriv` annihilates constant polynomials. -/
@[simp] theorem shiftDeriv_C (i : Fin n) (c : ZMod (2 ^ m)) :
    shiftDeriv (n := n) i (MvPolynomial.C c) = 0 := by
  rw [shiftDeriv_eq]
  rw [show (MvPolynomial.bind₁ (flipShift (m := m) i) (MvPolynomial.C c)
            : DiagPhase n m) = MvPolynomial.C c from
    MvPolynomial.bind₁_C_right _ c]
  simp

/-- `shiftDeriv` is additive. -/
theorem shiftDeriv_add (i : Fin n) (P Q : DiagPhase n m) :
    shiftDeriv i (P + Q) = shiftDeriv i P + shiftDeriv i Q := by
  rw [shiftDeriv_eq, shiftDeriv_eq, shiftDeriv_eq, map_add]
  abel

/-- When `P` has total degree 0, `shiftDeriv i P` is identically zero.
This is the trivial case of the level-drop induction (a constant phase
gives the identity gate, whose conjugate by any Pauli is the Pauli
itself). -/
theorem shiftDeriv_totalDegree_zero (i : Fin n) {P : DiagPhase n m}
    (hP : P.totalDegree = 0) :
    shiftDeriv i P = 0 := by
  have hC : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hP
  rw [hC, shiftDeriv_C]

/-! ### Representability theorem (partial)

The statement
  `∃ Q : DiagPhase n m,
    (∀ v, Q.eval (liftBinary v) = funcDerivEval i P v) ∧
    Q.totalDegree < P.totalDegree`
is the polynomial-side level-drop bridge needed for the inductive
step of `cgk_forward` (in `FTQCLib/Hilbert/CGKForward.lean`). The witness
`Q = shiftDeriv i P` realises the *value* part (proved here as
`shiftDeriv_eval_eq_funcDerivEval`), and the *degree non-increase*
part is proved here as `shiftDeriv_totalDegree_le`. The strict drop
remains open at the polynomial-degree level (see analysis below). -/

/-- **Value-side representability**: there exists a polynomial whose
evaluation on binary inputs reproduces the functional discrete
derivative of `P.eval`. The witness `shiftDeriv i P` also has total
degree at most that of `P`. -/
theorem exists_polyRep_funcDerivEval (P : DiagPhase n m) (i : Fin n) :
    ∃ Q : DiagPhase n m,
      (∀ v : Fin n → ZMod 2, Q.eval v = funcDerivEval i P v)
      ∧ Q.totalDegree ≤ P.totalDegree := by
  refine ⟨shiftDeriv i P, ?_, shiftDeriv_totalDegree_le i P⟩
  intro v
  exact shiftDeriv_eval_eq_funcDerivEval i P v

/-- **Trivial-case strict drop**: when `P.totalDegree = 0`, the
functional derivative is identically zero and is realised by the
zero polynomial. -/
theorem exists_polyRep_funcDerivEval_zero (P : DiagPhase n m) (i : Fin n)
    (hP : P.totalDegree = 0) :
    ∃ Q : DiagPhase n m,
      (∀ v : Fin n → ZMod 2, Q.eval v = funcDerivEval i P v)
      ∧ Q.totalDegree = 0 := by
  refine ⟨0, ?_, MvPolynomial.totalDegree_zero⟩
  intro v
  -- `funcDerivEval i P v = P.eval (v + e_i) - P.eval v`. For constant
  -- `P` this is zero.
  unfold funcDerivEval funcDeriv DiagPhase.eval
  have hC : P = MvPolynomial.C (P.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hP
  rw [hC]
  simp [MvPolynomial.eval_C]

/-! ### Remaining technical block: strict polynomial-degree drop

The genuine *strict* descent
  `(shiftDeriv i P).totalDegree < P.totalDegree`  when  `P.totalDegree > 0`
is **not** provable purely at the polynomial-total-degree level, even
restricting to multilinear `P`.

To see why, take `m ≥ 2` and the multilinear polynomial `P := X i · A`
where `A : MvPolynomial (Fin n) (ZMod (2^m))` does not involve `X i`.
Then
  `shiftDeriv i P = (1 - X i) · A − X i · A = A − 2 · X i · A`.
Over `ZMod (2^m)` with `m ≥ 2` the coefficient `2 ≠ 0`, so the
`X i · A` term genuinely persists and the total degree of `shiftDeriv i P`
equals that of `P`.

The Cui–Gottesman–Krishna descent still goes through, but only by
recognising that the `2 · X i · A` term comes with an extra factor of
`2` in the coefficient: divided through by the precision-denominator
`2^m`, this *reduces* the effective precision to `2^(m−1)`. The level
formula `(m − 1) + totalDegree(P)` then drops because `m` drops, not
because `totalDegree` drops.

Formalising this 2-adic refinement is the remaining block. Two routes:

1. **Functional decomposition.** Define `funcDeriv` purely as a
   function on `(F₂)ⁿ → ZMod (2^m)`. Show every such function admits
   a multilinear-polynomial representation in `MvPolynomial (Fin n) (ZMod (2^m))`
   (the Möbius / Fourier inversion on `(F₂)ⁿ`), and that the
   multilinear representation of `funcDeriv i (P.eval)` either
   (a) has strictly lower total degree than `P`, or (b) has all
   leading-degree coefficients divisible by 2 (in which case the
   precision-reduction `(P / 2) : DiagPhase n (m−1)` lowers `m`).

2. **2-adic precision lemma.** Prove a finer statement: there exists
   `Q : DiagPhase n (m − 1)` with
   `Q.eval (liftBinary v) ≡ funcDerivEval i P v / 2 (mod 2^{m-1})`
   whenever the leading-degree terms of `shiftDeriv i P` are
   `2`-divisible. Combine with `shiftDeriv_totalDegree_le` to recover
   the `level` drop directly.

Either route is well-defined as a Lean target but adds substantial
2-adic plumbing (`ZMod (2^m) → ZMod (2^(m−1))` reduction, divisibility
predicates on `MvPolynomial`, and the multilinear-Boolean-Fourier
correspondence). We document it here as the **CGK forward-direction
descent block** and proceed with what is fully provable at the
total-degree level. -/

end DiagPhase

end FTQCLib.Hierarchy

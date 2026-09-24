/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.PauliOp

set_option linter.unusedSectionVars false

/-! # Pauli operators as linear equivalences on the qubit Hilbert space

For each `p : Pauli n`, the operator `pauliOperator p` from
`FTQCLib/Hilbert/PauliOp.lean` is its own inverse up to a global `±1` sign.
Squaring on a computational-basis vector `|v⟩` gives

  `pauliOperator p (pauliOperator p |v⟩)
     = (-1)^{p.Z · v} · pauliOperator p |v + p.X⟩
     = (-1)^{p.Z · v} · (-1)^{p.Z · (v + p.X)} |v⟩
     = (-1)^{p.Z · p.X} |v⟩`,

using that `v + p.X + p.X = v` in `(ZMod 2)^n` and that
`(-1)^k` depends only on the parity of `k`. The factor
`(-1)^{p.Z · p.X}` is the standard `±1` ambiguity from anticommutation
between `Z`-support and `X`-support on the same qubit.

This file packages that algebra:

* **`pauliOperator_squared`** — the squared identity above.
* **`pauliEquiv`** — `pauliOperator p` upgraded to a `LinearEquiv`.

The inverse equivalence multiplies by `(-1)^{p.Z · p.X}` to absorb the
overall sign; since `(-1)^k` is its own multiplicative inverse, the
inverse takes the same `pauliOperator p` and rescales by the sign.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-! ## Arithmetic helpers for the squared identity -/

/-- In `(ZMod 2)^n`, `(w - p_X) - p_X = w` because `2·p_X = 0`. -/
private lemma sub_X_sub_X (w p_X : Fin n → ZMod 2) :
    w - p_X - p_X = w := by
  funext i
  simp only [Pi.sub_apply]
  -- Rewrite both subtractions via `sub_eq_add_neg`, then use `neg_eq` in
  -- characteristic 2 to absorb both copies of `p_X i`.
  rw [sub_eq_add_neg, sub_eq_add_neg, CharTwo.neg_eq,
      add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- `(-1 : ℂ)^k` depends only on `k mod 2`. -/
private lemma neg_one_pow_eq_of_mod_two_eq {a b : ℕ} (h : a % 2 = b % 2) :
    ((-1 : ℂ))^a = ((-1 : ℂ))^b := by
  have helper : ∀ k : ℕ, ((-1 : ℂ))^k = ((-1 : ℂ))^(k % 2) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul]
    have hsq : ((-1 : ℂ))^2 = 1 := by norm_num
    rw [hsq, one_pow, one_mul]
  rw [helper a, helper b, h]

/-- Key parity identity. The natural-number expression

    `zDotVal p (w - p.X) + zDotVal p w`

has the same parity as `zDotVal p p.X`. The proof works in `ZMod 2` and
lifts back to `Nat` mod 2. -/
private lemma zDot_double_mod_two (p : Pauli n) (w : Fin n → ZMod 2) :
    (zDotVal p (w - p.X) + zDotVal p w) % 2 =
      zDotVal p p.X % 2 := by
  -- We prove equality of the two sides in `ZMod 2`, then extract the
  -- parity equality via `Nat.ModEq`.
  have key :
      ((zDotVal p (w - p.X) + zDotVal p w : ℕ) : ZMod 2) =
        ((zDotVal p p.X : ℕ) : ZMod 2) := by
    unfold zDotVal
    push_cast
    -- Combine the two sums into one and reduce pointwise.
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Goal in ZMod 2: working under push_cast we should have
    --   ((p.Z i).val : ZMod 2) * (((w - p.X) i).val : ZMod 2)
    --   + ((p.Z i).val : ZMod 2) * ((w i).val : ZMod 2)
    --   = ((p.Z i).val : ZMod 2) * ((p.X i).val : ZMod 2).
    have val_cast : ∀ (a : ZMod 2), ((a.val : ℕ) : ZMod 2) = a :=
      ZMod.natCast_zmod_val
    rw [val_cast, val_cast, val_cast, val_cast]
    -- Now in ZMod 2: p.Z i * (w - p.X) i + p.Z i * w i = p.Z i * p.X i.
    have hwpx : (w - p.X) i = w i - p.X i := by simp
    rw [hwpx]
    -- In ZMod 2 (CharTwo): A*(w-X) + A*w = A*(w + X) + A*w = A*X + (A*w + A*w) = A*X.
    have h_neg : -(p.X i) = p.X i := CharTwo.neg_eq _
    rw [sub_eq_add_neg, h_neg]
    -- Goal: p.Z i * (w i + p.X i) + p.Z i * w i = p.Z i * p.X i.
    rw [mul_add]
    -- Goal: p.Z i * w i + p.Z i * p.X i + p.Z i * w i = p.Z i * p.X i.
    rw [add_assoc, add_comm (p.Z i * p.X i) (p.Z i * w i),
        ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  -- key : (LHS : ZMod 2) = (RHS : ZMod 2). Extract parity equality.
  exact (ZMod.natCast_eq_natCast_iff _ _ 2).mp key

/-! ## The squared identity -/

/-- Applying `pauliOperator p` twice produces a global `±1` sign:

  `pauliOperator p ∘ pauliOperator p = (-1)^{p.Z · p.X} • id`.

The sign `(-1)^{p.Z · p.X}` records the anticommutation between `p`'s
`Z`-support and `p`'s `X`-support on each common qubit. For `Y`-type
qubits (where both `X` and `Z` are present) the local `X·Z = -Z·X`
contributes a factor of `-1`; the total sign is `(-1)^k` for `k` the
overlap weight `|p.X ∧ p.Z|`. -/
theorem pauliOperator_squared (p : Pauli n) :
    pauliOperator p ∘ₗ pauliOperator p =
      ((-1 : ℂ)^(zDotVal p p.X)) • LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, Pi.smul_apply, smul_eq_mul]
  -- Unfold both pauliOperator applications.
  change (-1 : ℂ)^(zDotVal p (w - p.X)) *
        ((-1 : ℂ)^(zDotVal p ((w - p.X) - p.X)) * ψ ((w - p.X) - p.X)) =
       (-1 : ℂ)^(zDotVal p p.X) * ψ w
  -- Collapse w - p.X - p.X = w in ZMod 2.
  rw [sub_X_sub_X]
  -- Combine the powers: (-1)^a * (-1)^b = (-1)^(a+b).
  rw [show (-1 : ℂ)^(zDotVal p (w - p.X)) *
            ((-1 : ℂ)^(zDotVal p w) * ψ w) =
          (-1 : ℂ)^(zDotVal p (w - p.X) + zDotVal p w) * ψ w from by
    rw [pow_add]; ring]
  -- Reduce the exponent modulo 2 using the parity lemma.
  congr 1
  exact neg_one_pow_eq_of_mod_two_eq (zDot_double_mod_two p w)

/-! ## The Pauli operator as a linear equivalence -/

/-- Squared identity at the level of pointwise application. Useful for
unfolding inside `LinearEquiv.ofLinear` proofs. -/
private lemma pauliOperator_apply_pauliOperator (p : Pauli n) (ψ : QubitSpace n) :
    pauliOperator p (pauliOperator p ψ) =
      ((-1 : ℂ)^(zDotVal p p.X)) • ψ := by
  have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
    (pauliOperator_squared p)
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at h
  exact h

/-- The signed Pauli operator `pauliEquiv p : QubitSpace n ≃ₗ[ℂ] QubitSpace n`.

The forward map is `pauliOperator p` (no sign change). The inverse map is
`(-1)^{p.Z · p.X} • pauliOperator p`: composing the forward and inverse
gives `(-1)^k · (pauliOperator p)^2 = (-1)^k · (-1)^k · id = id`,
because `(-1)^k` is its own multiplicative inverse in `ℂ`. -/
noncomputable def pauliEquiv (p : Pauli n) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  LinearEquiv.ofLinear
    (pauliOperator p)
    (((-1 : ℂ)^(zDotVal p p.X)) • pauliOperator p)
    (by
      -- Show: pauliOperator p ∘ₗ (c • pauliOperator p) = id, c = (-1)^k.
      apply LinearMap.ext
      intro ψ
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      -- pauliOperator p (c • pauliOperator p ψ) = c • pauliOperator p (pauliOperator p ψ)
      rw [LinearMap.map_smul]
      rw [pauliOperator_apply_pauliOperator]
      -- Goal: c • (c • ψ) = ψ. Combine smuls, reduce c*c = 1.
      rw [smul_smul]
      rw [show ((-1 : ℂ)^(zDotVal p p.X) * (-1 : ℂ)^(zDotVal p p.X)) = 1 from by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num]
      rw [one_smul])
    (by
      -- Show: (c • pauliOperator p) ∘ₗ pauliOperator p = id.
      apply LinearMap.ext
      intro ψ
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      rw [pauliOperator_apply_pauliOperator]
      -- Goal: c • c • ψ = ψ.
      rw [smul_smul]
      rw [show ((-1 : ℂ)^(zDotVal p p.X) * (-1 : ℂ)^(zDotVal p p.X)) = 1 from by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num]
      rw [one_smul])

/-- The action of `pauliEquiv p` on a state coincides with the action of
the underlying `pauliOperator p`. -/
@[simp] theorem pauliEquiv_apply (p : Pauli n) (ψ : QubitSpace n) :
    pauliEquiv p ψ = pauliOperator p ψ := rfl

/-- The inverse of `pauliEquiv p` rescales `pauliOperator p` by the global
sign `(-1)^{p.Z · p.X}`. -/
@[simp] theorem pauliEquiv_symm_apply (p : Pauli n) (ψ : QubitSpace n) :
    (pauliEquiv p).symm ψ = ((-1 : ℂ)^(zDotVal p p.X)) • pauliOperator p ψ := rfl

end FTQCLib.Hilbert

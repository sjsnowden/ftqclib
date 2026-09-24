/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.PauliEquiv

set_option linter.unusedSectionVars false

/-! # The Pauli-product identity on the qubit Hilbert space

For two Paulis `p, q : Pauli n`, the composition of their operators on
`QubitSpace n` is again a Pauli operator, up to a `±1` phase determined
by the F_2 symplectic pairing between the Z-support of `q` and the
X-support of `p`:

  `pauliOperator q ∘ pauliOperator p
     = (-1)^{q.Z · p.X} • pauliOperator (p + q)`.

Sketch of the derivation on a computational-basis vector `|v⟩`:

  `pauliOperator p |v⟩ = (-1)^{p.Z · v} |v + p.X⟩`,
  `pauliOperator q (pauliOperator p |v⟩)
     = (-1)^{p.Z · v} · pauliOperator q |v + p.X⟩
     = (-1)^{p.Z · v + q.Z · (v + p.X)} |v + p.X + q.X⟩
     = (-1)^{q.Z · p.X} · (-1)^{(p.Z + q.Z) · v} |v + (p + q).X⟩
     = (-1)^{q.Z · p.X} · pauliOperator (p + q) |v⟩`.

The phase `(-1)^{q.Z · p.X}` is the standard sign-cocycle that arises
from putting two Paulis side-by-side: every `Z` of `q` against an `X`
of `p` on the same qubit picks up a `-1`. (The sister contribution
`(-1)^{p.Z · q.X}` is absorbed into the overall `(p + q)` and would
appear if we ordered things the other way.) The pairing
`q.Z · p.X + p.Z · q.X` is the F_2 symplectic form `ω(p, q)` from
`FTQCLib.Pauli.Symplectic`, but the directional half `q.Z · p.X` is what
governs the actual product-of-operators sign.

This file proves:

* **`zDotVal_add_right_mod_two`**, **`zDotVal_add_left_mod_two`** —
  parity additivity of the dot product in each argument.
* **`pauliOperator_mul`** — the product identity above, as composition
  of `LinearMap`s.
* **`pauliEquiv_trans_toLinearMap`** — the corollary at the
  `LinearEquiv` level. Because `pauliEquiv p`'s forward map is
  `pauliOperator p` (the inverse-side rescaling does not appear here),
  this is `pauliOperator_mul` repackaged through `pauliEquiv_apply`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli Complex

variable {n : ℕ}

/-! ## Parity additivity of `zDotVal`

`zDotVal p v = ∑ᵢ (p.Z i).val · (v i).val` is a natural-number
expression. Its parity is bilinear: additive in `p.Z` and in `v`
modulo 2. We need parity-level additivity (not exact equality of
naturals) because `(v + w) i` is the `ZMod 2` sum, not the integer
sum. -/

/-- `zDotVal` is parity-additive in its right argument:
`(zDotVal p (v + w)) % 2 = (zDotVal p v + zDotVal p w) % 2`. -/
lemma zDotVal_add_right_mod_two (p : Pauli n) (v w : Fin n → ZMod 2) :
    (zDotVal p (v + w)) % 2 = (zDotVal p v + zDotVal p w) % 2 := by
  -- Prove equality in `ZMod 2` and lift via `Nat.ModEq`.
  have key :
      ((zDotVal p (v + w) : ℕ) : ZMod 2) =
        ((zDotVal p v + zDotVal p w : ℕ) : ZMod 2) := by
    unfold zDotVal
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- Convert any residual `((·.val : ℕ → ZMod 2))` casts back to
    -- their underlying ZMod 2 element. `push_cast` clears most but
    -- can leave a stray cast on one factor; `simp only` handles all.
    simp only [ZMod.natCast_zmod_val]
    -- Goal in ZMod 2: p.Z i * (v + w) i = p.Z i * v i + p.Z i * w i.
    have hvw : (v + w) i = v i + w i := by simp
    rw [hvw, mul_add]
  exact (ZMod.natCast_eq_natCast_iff _ _ 2).mp key

/-- `zDotVal` is parity-additive in its left argument (Pauli side):
`(zDotVal (p + q) v) % 2 = (zDotVal p v + zDotVal q v) % 2`. -/
lemma zDotVal_add_left_mod_two (p q : Pauli n) (v : Fin n → ZMod 2) :
    (zDotVal (p + q) v) % 2 = (zDotVal p v + zDotVal q v) % 2 := by
  have key :
      ((zDotVal (p + q) v : ℕ) : ZMod 2) =
        ((zDotVal p v + zDotVal q v : ℕ) : ZMod 2) := by
    unfold zDotVal
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [ZMod.natCast_zmod_val]
    -- Goal in ZMod 2: (p + q).Z i * v i = p.Z i * v i + q.Z i * v i.
    have hpq : (p + q).Z i = p.Z i + q.Z i := by simp
    rw [hpq, add_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ 2).mp key

/-- `(-1 : ℂ)^k` depends only on `k mod 2`. (Restated locally to keep
this file's exponent-reduction step self-contained.) -/
lemma neg_one_pow_eq_of_mod_two_eq {a b : ℕ} (h : a % 2 = b % 2) :
    ((-1 : ℂ))^a = ((-1 : ℂ))^b := by
  have helper : ∀ k : ℕ, ((-1 : ℂ))^k = ((-1 : ℂ))^(k % 2) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul]
    have hsq : ((-1 : ℂ))^2 = 1 := by norm_num
    rw [hsq, one_pow, one_mul]
  rw [helper a, helper b, h]

/-! ## A `ZMod 2` shuffling lemma

To prove the product identity we need to identify
`w - q.X - p.X` with `w - (p + q).X` as elements of `(ZMod 2)^n`. -/

/-- In `(ZMod 2)^n`, `w - q.X - p.X = w - (p + q).X`. -/
private lemma sub_qX_sub_pX (p q : Pauli n) (w : Fin n → ZMod 2) :
    w - q.X - p.X = w - (p + q).X := by
  have hpq : (p + q).X = p.X + q.X := by simp
  rw [hpq]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-! ## The product identity

The argument has the same shape as `pauliOperator_squared` in
`PauliEquiv.lean`: unfold both compositions on a fixed `w`, collect
the powers of `-1`, then close by reducing the exponent modulo 2 with
a parity lemma. -/

/-- The exponent-sum parity: at any `w`, the two sign exponents arising
from composing `pauliOperator q` after `pauliOperator p` add (mod 2) to
the right-hand side exponent `zDotVal q p.X + zDotVal (p+q) (w - q.X - p.X)`.

Concretely:

  `(zDotVal q (w - q.X) + zDotVal p ((w - q.X) - p.X)) % 2
     = (zDotVal q p.X + zDotVal (p+q) (w - q.X - p.X)) % 2`.

Both sides reduce to the same `ZMod 2` expression after expanding
parity-additivity of `zDotVal` in both arguments. -/
private lemma zDot_product_mod_two (p q : Pauli n) (w : Fin n → ZMod 2) :
    (zDotVal q (w - q.X) + zDotVal p (w - q.X - p.X)) % 2 =
      (zDotVal q p.X + zDotVal (p + q) (w - q.X - p.X)) % 2 := by
  -- Prove equality of both sides in `ZMod 2` and extract the parity.
  have key :
      ((zDotVal q (w - q.X) + zDotVal p (w - q.X - p.X) : ℕ) : ZMod 2) =
        ((zDotVal q p.X + zDotVal (p + q) (w - q.X - p.X) : ℕ) : ZMod 2) := by
    -- Work entirely in `ZMod 2`. `push_cast` plus `simp only` on the
    -- val-cast lemma converts every `((·.val : ℕ → ZMod 2))` back to
    -- its underlying ZMod 2 element, leaving a polynomial identity.
    unfold zDotVal
    push_cast
    -- Combine each side into a single sum and reduce pointwise.
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [ZMod.natCast_zmod_val]
    -- Substitute pointwise: (w - q.X) i = w i - q.X i,
    -- (w - q.X - p.X) i = w i - q.X i - p.X i, (p + q).Z i = p.Z i + q.Z i.
    have h1 : (w - q.X) i = w i - q.X i := by simp
    have h2 : (w - q.X - p.X) i = w i - q.X i - p.X i := by simp
    have h3 : (p + q).Z i = p.Z i + q.Z i := by simp
    rw [h1, h2, h3]
    -- In `ZMod 2` (CharTwo), subtraction is addition. `ring` closes it.
    ring
  exact (ZMod.natCast_eq_natCast_iff _ _ 2).mp key

/-- **The Pauli-product identity.** Composing two Pauli operators on
`QubitSpace n` gives a third Pauli operator with a `±1` phase factor:

  `pauliOperator q ∘ pauliOperator p
    = (-1)^{q.Z · p.X} • pauliOperator (p + q)`.

The phase `(-1)^{q.Z · p.X}` records the F_2 symplectic pairing of the
Z-support of `q` against the X-support of `p`; equivalently, the
number of qubits where `q` carries a `Z` and `p` carries an `X`. This
is the standard "sign-cocycle" of the Pauli group's projective
representation modulo a global phase.

A practical consequence (used in `IsCliffordHierarchy.mono`):
conjugating any Pauli `q` by a Pauli `p` again yields a Pauli, since
the two sign factors from left- and right-multiplication share the
same support and cancel out the X-shift, leaving `±1 ·
pauliOperator q`. -/
theorem pauliOperator_mul (p q : Pauli n) :
    pauliOperator q ∘ₗ pauliOperator p =
      ((-1 : ℂ)^(zDotVal q p.X)) • pauliOperator (p + q) := by
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  -- Unfold both `pauliOperator` applications on the LHS, and the
  -- single `pauliOperator (p + q)` application on the RHS.
  change (-1 : ℂ)^(zDotVal q (w - q.X)) *
           ((-1 : ℂ)^(zDotVal p ((w - q.X) - p.X)) * ψ ((w - q.X) - p.X)) =
         (-1 : ℂ)^(zDotVal q p.X) *
           ((-1 : ℂ)^(zDotVal (p + q) (w - (p + q).X)) * ψ (w - (p + q).X))
  -- Rewrite the RHS argument to match the LHS form `w - q.X - p.X`
  -- (using `sub_qX_sub_pX p q w : w - q.X - p.X = w - (p + q).X`).
  rw [← sub_qX_sub_pX p q w]
  -- Now both sides reference `w - q.X - p.X`. Combine `(-1)^a · (-1)^b`
  -- into `(-1)^(a + b)` on each side.
  rw [show (-1 : ℂ)^(zDotVal q (w - q.X)) *
            ((-1 : ℂ)^(zDotVal p (w - q.X - p.X)) * ψ (w - q.X - p.X)) =
         (-1 : ℂ)^(zDotVal q (w - q.X) + zDotVal p (w - q.X - p.X)) *
           ψ (w - q.X - p.X) from by
    rw [pow_add]; ring]
  rw [show (-1 : ℂ)^(zDotVal q p.X) *
            ((-1 : ℂ)^(zDotVal (p + q) (w - q.X - p.X)) *
              ψ (w - q.X - p.X)) =
         (-1 : ℂ)^(zDotVal q p.X + zDotVal (p + q) (w - q.X - p.X)) *
           ψ (w - q.X - p.X) from by
    rw [pow_add]; ring]
  -- Reduce both exponents mod 2 to the same value via the parity lemma.
  congr 1
  exact neg_one_pow_eq_of_mod_two_eq (zDot_product_mod_two p q w)

/-- Pointwise corollary: applying the product `pauliOperator q ∘
pauliOperator p` to any state `ψ` equals the scaled `pauliOperator (p +
q)` applied to `ψ`. Convenient when working under `LinearEquiv.trans`
unfolds, which expose pointwise applications. -/
theorem pauliOperator_apply_pauliOperator_apply (p q : Pauli n)
    (ψ : QubitSpace n) :
    pauliOperator q (pauliOperator p ψ) =
      ((-1 : ℂ)^(zDotVal q p.X)) • pauliOperator (p + q) ψ := by
  have h := congrArg (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L ψ)
    (pauliOperator_mul p q)
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearMap.smul_apply] at h
  exact h

/-- The product identity, stated on the underlying linear map of
`pauliEquiv`. Since `pauliEquiv p`'s forward map is `pauliOperator p`
(no global rescaling — the inverse sign sits on `pauliEquiv.symm`),
this is just `pauliOperator_mul` repackaged via `pauliEquiv_apply`.
We avoid the inverse rescaling here — the inverse sign only enters
when one composes with `pauliEquiv.symm`. -/
theorem pauliEquiv_trans_toLinearMap (p q : Pauli n) :
    ((pauliEquiv p).trans (pauliEquiv q)).toLinearMap =
      ((-1 : ℂ)^(zDotVal q p.X)) • (pauliEquiv (p + q)).toLinearMap := by
  apply LinearMap.ext
  intro ψ
  -- LHS: ((pauliEquiv p).trans (pauliEquiv q)) ψ = pauliEquiv q (pauliEquiv p ψ)
  --      = pauliOperator q (pauliOperator p ψ). RHS rescales pauliOperator (p+q).
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, pauliEquiv_apply,
    LinearMap.smul_apply]
  exact pauliOperator_apply_pauliOperator_apply p q ψ

end FTQCLib.Hilbert

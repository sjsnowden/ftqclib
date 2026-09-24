/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.Defs
import FTQCLib.Hierarchy.FuncDeriv
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.GatePolynomials

set_option linter.unusedSectionVars false

/-! # The CNOT (affine) pushforward of a phase polynomial

A `CNOT` with control `i` and target `k` acts on the binary phase-space
`(F₂)ⁿ` by `v ↦ v` with the single coordinate update
`v_k ↦ v_k ⊕ v_i`. On the phase polynomial `P` (whose evaluation gives
the diagonal-unitary exponents) the pull-back / push-forward is the
substitution `X_k ↦ X_k ⊕ X_i`.

The Boolean-correct *multilinear* form of XOR over `ZMod (2^m)` is
`a ⊕ b = a + b − 2 a b` (which agrees with `a ⊕ b` exactly on
`{0, 1}`). Substituting `X_k ↦ X_k + X_i − 2 X_i X_k` therefore realises
the CNOT update on every binary input. This is a **degree-raising**
substitution — the `X_i X_k` cross term is what turns a two-body `ZZ`
phase into the three-body `X_i X_j X_k` term that a CCZ requires, which
is the algebraic content of "conjugating a `ZZ` by a CNOT yields a
three-body `ZZZ`".

This file is **pure phase-polynomial machinery** and does not depend on
any of the Hilbert-space layer. The local bit-map `cnotBitMap` is
definitionally the same as `FTQCLib/Hilbert`'s `cnotPerm` restricted to bit
vectors, but is re-declared here to keep `Hierarchy` independent of
`Hilbert`.

## Main results

* `affinePushforward_eval` — **the core eval-bridge**:
  `(affinePushforward i k P).eval v = P.eval (cnotBitMap i k v)`.
* `affinePushforward_eval_val` — the `ZMod.val` corollary.
* `affinePushforward_add` — additivity (`bind₁` is additive).
* `affinePushforward_cnot_zz` — the concrete `2 → 3` body computation:
  pushing the two-body monomial `c · X_j X_k` forward yields the
  three-body `X_i X_j X_k` term plus a lower-order correction.
-/

namespace FTQCLib.Hierarchy

open MvPolynomial

namespace DiagPhase

variable {n m : ℕ}

/-! ### The CNOT bit-map and its polynomial substitution -/

/-- The action of a `CNOT` (control `i`, target `k`) on a binary vector
`v : Fin n → ZMod 2`: it leaves every coordinate fixed except the target
`k`, which is updated to `v k ⊕ v i = v k + v i` (XOR is `+` in
`ZMod 2`). Definitionally identical to the Hilbert-layer `cnotPerm`
restricted to bit vectors, redeclared here so that `Hierarchy` does not
depend on `Hilbert`. -/
def cnotBitMap (i k : Fin n) (v : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  Function.update v k (v k + v i)

/-- The polynomial substitution realising the CNOT update on binary
inputs. The target variable `X_k` is replaced by the multilinear XOR
form `X_k + X_i − 2 X_i X_k`; every other variable is fixed. On
`{0, 1}` the substitution value equals `v k ⊕ v i`. -/
noncomputable def cnotSubst (i k : Fin n) : Fin n → DiagPhase n m :=
  fun l => if l = k then (X k + X i - 2 * (X i * X k)) else X l

/-- The CNOT push-forward of a phase polynomial: substitute the XOR form
for `X_k` and leave the rest. As a degree-raising substitution it is the
polynomial-side image of conjugating a diagonal unitary by a CNOT. -/
noncomputable def affinePushforward (i k : Fin n) (P : DiagPhase n m) :
    DiagPhase n m :=
  MvPolynomial.bind₁ (cnotSubst i k) P

/-- Unfold `affinePushforward` to its `bind₁` form. -/
private lemma affinePushforward_eq (i k : Fin n) (P : DiagPhase n m) :
    affinePushforward i k P = MvPolynomial.bind₁ (cnotSubst (m := m) i k) P :=
  rfl

/-! ### The eval-bridge

The key point-function identity is that, evaluated at the lifted binary
vector `liftBinary v`, the substitution `cnotSubst i k l` reproduces the
`l`-th coordinate of `liftBinary (cnotBitMap i k v)`. For `l ≠ k` both
sides are `liftBinary v l`; for `l = k` it is the XOR identity
`a + b − 2 a b = a ⊕ b` on `{0, 1}`. -/

/-- A `ZMod 2` element is either `0` or `1`. -/
private lemma dich (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

/-- `ZMod.val` of the two elements of `ZMod 2`, as concrete naturals. -/
private lemma val_zmod2_zero : (0 : ZMod 2).val = 0 := rfl
private lemma val_zmod2_one : (1 : ZMod 2).val = 1 := rfl

/-- **Key bridge identity for the target coordinate** (`l = k`):
the XOR multilinear identity `(v k).val + (v i).val − 2 (v i).val (v k).val
= (v k + v i).val` in `ZMod (2^m)`, abstracted over the two bits `a = v k`
and `b = v i`. Proved by case-splitting both bits `a, b ∈ {0, 1}` and
computing both sides as nat-cast literals. -/
private lemma xor_multilinear_identity (a b : ZMod 2) :
    ((a.val : ZMod (2 ^ m)) + (b.val : ZMod (2 ^ m))
        - 2 * ((b.val : ZMod (2 ^ m)) * (a.val : ZMod (2 ^ m))))
      = (((a + b).val : ℕ) : ZMod (2 ^ m)) := by
  rcases dich a with ha | ha <;> rcases dich b with hb | hb <;> subst ha <;> subst hb
  · -- a = 0, b = 0: LHS = 0, RHS = (0+0).val = 0.
    rw [show ((0 : ZMod 2) + 0) = 0 from by decide]
    rw [val_zmod2_zero, Nat.cast_zero]; ring
  · -- a = 0, b = 1: LHS = 1, RHS = (0+1).val = 1.
    rw [show ((0 : ZMod 2) + 1) = 1 from by decide]
    rw [val_zmod2_zero, val_zmod2_one, Nat.cast_zero, Nat.cast_one]; ring
  · -- a = 1, b = 0: LHS = 1, RHS = (1+0).val = 1.
    rw [show ((1 : ZMod 2) + 0) = 1 from by decide]
    rw [val_zmod2_zero, val_zmod2_one, Nat.cast_zero, Nat.cast_one]; ring
  · -- a = 1, b = 1: LHS = 1 + 1 - 2 = 0, RHS = (1+1).val = (0).val = 0.
    rw [show ((1 : ZMod 2) + 1) = 0 from by decide]
    rw [val_zmod2_one, val_zmod2_zero, Nat.cast_one, Nat.cast_zero]; ring

/-- **Key bridge identity**: evaluating `cnotSubst i k l` at the lifted
binary vector `liftBinary v` reproduces the `l`-th coordinate of the
CNOT-updated lift `liftBinary (cnotBitMap i k v)`.

The case `l ≠ k` is immediate (`cnotSubst` is the identity off `k`, and
`cnotBitMap` updates only `k`). The case `l = k` is the multilinear XOR
identity `a + b − 2 a b = a ⊕ b` (`xor_multilinear_identity`). -/
private lemma eval_cnotSubst_apply (i k l : Fin n) (v : Fin n → ZMod 2) :
    MvPolynomial.eval (liftBinary (m := m) v) (cnotSubst (m := m) i k l)
      = (liftBinary (m := m) (cnotBitMap i k v)) l := by
  unfold cnotSubst
  split_ifs with hlk
  · -- l = k: the XOR identity.
    subst hlk
    -- Distribute `eval` over the XOR form; `eval (2) = 2`, `eval (X j) = (v j).val`.
    simp only [map_sub, map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    unfold liftBinary cnotBitMap
    -- `Function.update v l (v l + v i) l = v l + v i`.
    rw [Function.update_self]
    exact xor_multilinear_identity (v l) (v i)
  · -- l ≠ k: both sides are (v l).val.
    rw [MvPolynomial.eval_X]
    unfold liftBinary cnotBitMap
    rw [Function.update_of_ne hlk]

/-- **The eval-bridge** (CORE). The CNOT push-forward `affinePushforward
i k P`, evaluated at a binary vector `v`, equals `P` evaluated at the
CNOT-updated vector `cnotBitMap i k v`.

Proof strategy (mirrors `shiftDeriv_eval`): rewrite the `bind₁` term via
`aeval_bind₁` to `eval (fun l ↦ eval (liftBinary v) (cnotSubst i k l)) P`,
then note that the inner argument function equals `liftBinary
(cnotBitMap i k v)` by `eval_cnotSubst_apply`. -/
theorem affinePushforward_eval (i k : Fin n) (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    (affinePushforward i k P).eval v = P.eval (cnotBitMap i k v) := by
  unfold DiagPhase.eval
  rw [affinePushforward_eq]
  -- Reduce the `bind₁` via `aeval_bind₁` (= eval composition).
  have h := MvPolynomial.aeval_bind₁
      (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
      (liftBinary (m := m) v) (cnotSubst (m := m) i k) P
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  -- The two argument functions agree pointwise via `eval_cnotSubst_apply`.
  have hfun : (fun l : Fin n =>
      MvPolynomial.eval (liftBinary (m := m) v) (cnotSubst (m := m) i k l))
      = liftBinary (m := m) (cnotBitMap i k v) := by
    funext l
    exact eval_cnotSubst_apply i k l v
  rw [hfun]

/-- **`ZMod.val` corollary** of the eval-bridge: the underlying naturals
agree as well. Handy when transporting the bridge through `ZMod.val`. -/
theorem affinePushforward_eval_val (i k : Fin n) (P : DiagPhase n m)
    (v : Fin n → ZMod 2) :
    ((affinePushforward i k P).eval v).val = (P.eval (cnotBitMap i k v)).val :=
  congrArg ZMod.val (affinePushforward_eval i k P v)

/-! ### Algebraic structure -/

/-- The CNOT push-forward is additive (`bind₁` is an algebra hom, hence
additive). On the operator side this is multiplicativity of the
diagonal unitaries: `U_{P+Q} = U_P U_Q`. -/
theorem affinePushforward_add (i k : Fin n) (P Q : DiagPhase n m) :
    affinePushforward i k (P + Q)
      = affinePushforward i k P + affinePushforward i k Q := by
  rw [affinePushforward_eq, affinePushforward_eq, affinePushforward_eq, map_add]

/-- The CNOT push-forward fixes the zero polynomial. -/
@[simp] theorem affinePushforward_zero (i k : Fin n) :
    affinePushforward (m := m) i k 0 = 0 := by
  rw [affinePushforward_eq, map_zero]

/-! ### The concrete `2 → 3` body computation

Pushing a two-body monomial `c · X_j X_k` forward across a CNOT with
control `i` and target `k` (with `i, j, k` distinct, and `i ≠ k`, `j ≠ k`
so that only the target factor `X_k` is substituted) produces

  `c · X_j · (X_k + X_i − 2 X_i X_k)
     = c · X_j X_k  +  c · X_i X_j  −  2 c · X_i X_j X_k`.

The genuinely three-body term `X_i X_j X_k` is exactly the `CCZ`-type
phase the kernel-frame proof needs; the other two are the lower-order
corrections. -/

/-- **The 2→3 push-forward identity.** For control `i`, target `k`, with
`j ≠ k` (so the source `X_j` is untouched by the substitution), the CNOT
push-forward of the two-body phase `c · X_j X_k` is
`c · X_j X_k + c · X_i X_j − 2 c · X_i X_j X_k`.

The three-body term `−2 c · X_i X_j X_k` (and, more visibly, the
`X_i X_j X_k` monomial inside it) is the `ZZZ`/`CCZ`-type term that
arises from conjugating a two-body `ZZ` by a CNOT. The hypothesis `i ≠ k`
is not needed for the algebraic identity (the substitution rewrites the
target `X_k` regardless), so it is omitted; in the intended physical use
`i, j, k` are pairwise distinct. -/
theorem affinePushforward_cnot_zz (i j k : Fin n) (c : ZMod (2 ^ m))
    (hjk : j ≠ k) :
    affinePushforward i k (C c * (X j * X k) : DiagPhase n m)
      = C c * (X j * X k) + C c * (X i * X j)
        - 2 * (C c * (X i * X j * X k)) := by
  rw [affinePushforward_eq]
  -- bind₁ is an algebra hom: distribute over the product and the C.
  rw [map_mul, map_mul, MvPolynomial.bind₁_C_right]
  -- Evaluate `bind₁ (cnotSubst i k)` on each variable.
  have hXj : MvPolynomial.bind₁ (cnotSubst (m := m) i k) (X j) = X j := by
    rw [MvPolynomial.bind₁_X_right]
    unfold cnotSubst; rw [if_neg hjk]
  have hXk : MvPolynomial.bind₁ (cnotSubst (m := m) i k) (X k)
      = X k + X i - 2 * (X i * X k) := by
    rw [MvPolynomial.bind₁_X_right]
    unfold cnotSubst; rw [if_pos rfl]
  rw [hXj, hXk]
  ring

/-! ### Effective-level theory: the pushforward does not raise level

Clifford conjugation (here, a CNOT) is level-non-increasing. We prove
the polynomial-side statement

  `effectiveLevel (affinePushforward i k P) ≤ effectiveLevel P`

for **multilinear** `P`. This is the non-trivial half of "Clifford
conjugation is level-invariant"; the reverse inequality would follow by
applying the same bound to the inverse CNOT (also a CNOT), but is not
needed downstream and is omitted here.

The mechanism is the same `effectiveLevel` design used for `shiftDeriv`:
the degree-raising cross term `−2 X_i X_k` carries an explicit factor of
`2`, whose two-adic valuation absorbs the one-unit degree increase, so no
monomial of the pushforward exceeds the source's per-monomial level. -/

section LevelTheory
open Finsupp

/-- **Per-monomial pushforward of a multilinear target monomial.** When
`d k = 1` and `i ≠ k`, the CNOT push-forward of `monomial d c` is the
three-monomial sum `monomial d c + monomial (d.erase k + e_i) c −
2 · monomial (d.erase k + e_i + e_k) c`. -/
lemma affinePushforward_monomial_dk_one (i k : Fin n) (d : Fin n →₀ ℕ)
    (c : ZMod (2 ^ m)) (hik : i ≠ k) (hdk : d k = 1) :
    affinePushforward i k (monomial d c : DiagPhase n m)
      = monomial d c
        + monomial (d.erase k + single i 1) c
        - 2 * monomial (d.erase k + single i 1 + single k 1) c := by
  classical
  rw [affinePushforward_eq, bind₁_monomial]
  -- k ∈ d.support since d k = 1 ≠ 0.
  have hk_mem : k ∈ d.support := by
    rw [Finsupp.mem_support_iff, hdk]; norm_num
  -- Split the product on the `k` entry.
  rw [← Finset.mul_prod_erase _ _ hk_mem]
  have h_flipk : cnotSubst (m := m) i k k = (X k + X i - 2 * (X i * X k)) := by
    unfold cnotSubst; rw [if_pos rfl]
  rw [h_flipk, hdk, pow_one]
  have h_off : ∀ l ∈ d.support.erase k, cnotSubst (m := m) i k l = X l := by
    intro l hl
    have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
    unfold cnotSubst; rw [if_neg hlk]
  rw [Finset.prod_congr rfl (fun l hl => by rw [h_off l hl])]
  -- ∏ l ∈ d.support.erase k, X l ^ d l = monomial (d.erase k) 1.
  have h_prod_eq : (∏ l ∈ d.support.erase k, X l ^ d l :
                    MvPolynomial (Fin n) (ZMod (2 ^ m)))
      = ∏ l ∈ (d.erase k).support, X l ^ (d.erase k) l := by
    rw [Finsupp.support_erase]
    refine Finset.prod_congr rfl ?_
    intro l hl
    have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
    rw [Finsupp.erase_apply, if_neg hlk]
  rw [h_prod_eq, prod_X_pow_eq_monomial]
  -- Key Finsupp identity: single k 1 + d.erase k = d (since d k = 1).
  have hsplit : (single k 1 + d.erase k : Fin n →₀ ℕ) = d := by
    ext l
    by_cases hlk : l = k
    · subst hlk
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl, Finsupp.erase_same,
        add_zero, hdk]
    · rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (fun h => hlk h.symm),
        Finsupp.erase_apply, if_neg hlk, zero_add]
  -- The three monomial products.
  have hMk : (X k * monomial (d.erase k) (1 : ZMod (2 ^ m)) : DiagPhase n m)
      = monomial d 1 := by
    rw [X, monomial_mul, mul_one, hsplit]
  have hMi : (X i * monomial (d.erase k) (1 : ZMod (2 ^ m)) : DiagPhase n m)
      = monomial (d.erase k + single i 1) 1 := by
    rw [X, monomial_mul, mul_one]
    congr 1; abel_nf
  have hMik : (X i * X k * monomial (d.erase k) (1 : ZMod (2 ^ m)) : DiagPhase n m)
      = monomial (d.erase k + single i 1 + single k 1) 1 := by
    rw [X, X, monomial_mul, monomial_mul, mul_one, mul_one]
    congr 1; abel_nf
  -- Distribute the product and rewrite each piece.
  rw [sub_mul, add_mul, mul_sub, mul_add]
  rw [show (2 : DiagPhase n m) * (X i * X k) * monomial (d.erase k) 1
        = 2 * (X i * X k * monomial (d.erase k) 1) from by ring]
  rw [hMk, hMi, hMik]
  -- Pull `C c` through each monomial and through the `2`.
  rw [C_mul_monomial, mul_one]
  rw [C_mul_monomial, mul_one]
  rw [show (C c * (2 * monomial (d.erase k + single i 1 + single k 1)
              (1 : ZMod (2 ^ m))) : DiagPhase n m)
        = 2 * monomial (d.erase k + single i 1 + single k 1) c from by
        rw [two_mul_monomial, mul_one, C_mul_monomial, two_mul_monomial,
          mul_comm c 2]]

/-! ### Degree bookkeeping for the pushforward monomials -/

/-- `(single i 1).sum (fun _ e => e) = 1`. -/
private lemma sum_single_one (i : Fin n) :
    (single i 1 : Fin n →₀ ℕ).sum (fun _ e => e) = 1 := by
  rw [Finsupp.sum_single_index]; rfl

/-- `(d + single i 1).sum = d.sum + 1` for any `d`. -/
private lemma sum_add_single (d : Fin n →₀ ℕ) (i : Fin n) :
    (d + single i 1 : Fin n →₀ ℕ).sum (fun _ e => e)
      = d.sum (fun _ e => e) + 1 := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_single_one]

/-- `(d.erase k).sum = d.sum - 1` when `d k = 1` (multilinear target). -/
private lemma sum_erase_target (k : Fin n) {d : Fin n →₀ ℕ} (hdk : d k = 1) :
    (d.erase k).sum (fun _ e => e) = d.sum (fun _ e => e) - 1 := by
  classical
  rw [Finsupp.sum, Finsupp.support_erase, Finsupp.sum]
  have hk_mem : k ∈ d.support := by
    rw [Finsupp.mem_support_iff, hdk]; norm_num
  have h1 : ∑ l ∈ d.support.erase k, (d.erase k) l
      = ∑ l ∈ d.support.erase k, d l := by
    refine Finset.sum_congr rfl ?_
    intro l hl
    have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
    rw [Finsupp.erase_apply, if_neg hlk]
  rw [h1, ← Finset.sum_erase_add _ _ hk_mem, hdk, Nat.add_sub_cancel]

/-- `1 ≤ d.sum` when `d k = 1`. -/
private lemma one_le_sum_of_dk_one (k : Fin n) {d : Fin n →₀ ℕ} (hdk : d k = 1) :
    1 ≤ d.sum (fun _ e => e) := by
  classical
  rw [Finsupp.sum]
  have hk_mem : k ∈ d.support := by
    rw [Finsupp.mem_support_iff, hdk]; norm_num
  calc (1 : ℕ) = d k := hdk.symm
    _ ≤ ∑ l ∈ d.support, d l :=
        Finset.single_le_sum (f := fun (j : Fin n) => d j)
          (fun _ _ => Nat.zero_le _) hk_mem

/-! ### Per-monomial effective-level bound -/

/-- The effective level of `A + B` is bounded by the max of those of `A`
and `B` (re-derived locally; the version in `EffectiveLevel` is private). -/
private lemma effectiveLevel_add_le' (A B : DiagPhase n m) :
    effectiveLevel (A + B) ≤ max (effectiveLevel A) (effectiveLevel B) := by
  classical
  have h_sum : (A + B : DiagPhase n m)
      = ∑ b ∈ ({true, false} : Finset Bool), (if b then A else B) := by
    rw [show ({true, false} : Finset Bool) = ({true} ∪ {false}) from rfl]
    rw [Finset.sum_union (by decide : Disjoint ({true} : Finset Bool) {false})]
    simp
  rw [h_sum]
  refine (effectiveLevel_finsetSum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro b hb
  rw [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · change effectiveLevel A ≤ _; exact le_max_left _ _
  · change effectiveLevel B ≤ _; exact le_max_right _ _

/-- **Per-monomial effective-level bound.** For multilinear `d` (used via
`d k = 1`) with `c ≠ 0` and `i ≠ k`, the pushforward
`affinePushforward i k (monomial d c)` has effective level at most the
source's per-monomial level `effLevelMonom m c d`. Each of the three
pushforward monomials is bounded:
* `monomial d c` — same level;
* `monomial (d.erase k + e_i) c` — same total degree (`d.sum`), same level;
* `−2 · monomial (d.erase k + e_i + e_k) c` — degree `d.sum + 1` but the
  coefficient `2c` has two-adic valuation `≥ v(c) + 1`, so its level is
  `≤ effLevelMonom m c d` (or the term vanishes). -/
lemma affinePushforward_monomial_effectiveLevel_le
    (i k : Fin n) {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)}
    (hc : c ≠ 0) (hik : i ≠ k) (hdk : d k = 1) :
    effectiveLevel (affinePushforward i k (monomial d c) : DiagPhase n m)
      ≤ effLevelMonom m c d := by
  classical
  have hm_pos : 1 ≤ m := by
    by_contra hm
    have hm0 : m = 0 := Nat.lt_one_iff.mp (not_le.mp hm)
    subst hm0
    have : c.val < 1 := ZMod.val_lt c
    exact hc (by
      have hv : c.val = 0 := Nat.lt_one_iff.mp this
      have hcast : c = (c.val : ZMod (2 ^ 0)) := (ZMod.natCast_zmod_val c).symm
      rw [hcast, hv]; simp)
  have h_sum_pos : 1 ≤ d.sum (fun _ e => e) := one_le_sum_of_dk_one k hdk
  have h_v_c_lt : twoAdicVal c < m := twoAdicVal_lt_of_ne_zero hc
  rw [affinePushforward_monomial_dk_one i k d c hik hdk]
  -- Rewrite the subtraction additively for `effectiveLevel_add_le`.
  rw [two_mul_monomial]
  rw [show (monomial d c + monomial (d.erase k + single i 1) c
            - monomial (d.erase k + single i 1 + single k 1)
                ((2 : ZMod (2 ^ m)) * c) : DiagPhase n m)
        = monomial d c + (monomial (d.erase k + single i 1) c
            + monomial (d.erase k + single i 1 + single k 1)
                (-((2 : ZMod (2 ^ m)) * c))) from by
        rw [sub_eq_add_neg, ← map_neg]; abel_nf]
  refine le_trans (effectiveLevel_add_le' _ _) (max_le ?_ ?_)
  · -- monomial d c.
    exact effectiveLevel_monomial_le d c
  refine le_trans (effectiveLevel_add_le' _ _) (max_le ?_ ?_)
  · -- monomial (d.erase k + e_i) c: same total degree, same level.
    refine le_trans (effectiveLevel_monomial_le _ _) ?_
    unfold effLevelMonom
    rw [sum_add_single, sum_erase_target k hdk]
    omega
  · -- monomial (d.erase k + e_i + e_k) (-2c).
    by_cases h2c : (2 : ZMod (2 ^ m)) * c = 0
    · -- term vanishes.
      have h_neg_zero : -((2 : ZMod (2 ^ m)) * c) = 0 := by rw [h2c, neg_zero]
      rw [h_neg_zero]
      rw [show ((monomial (d.erase k + single i 1 + single k 1)
            (0 : ZMod (2 ^ m))) : DiagPhase n m) = 0 from (LinearMap.map_zero _)]
      rw [effectiveLevel_zero]
      exact Nat.zero_le _
    · -- 2c ≠ 0; v(-2c) = v(2c) ≥ v(c) + 1.
      have h_neg_ne : -((2 : ZMod (2 ^ m)) * c) ≠ 0 := neg_ne_zero.mpr h2c
      rw [effectiveLevel_monomial_eq h_neg_ne]
      unfold effLevelMonom
      rw [twoAdicVal_neg]
      rw [sum_add_single, sum_add_single, sum_erase_target k hdk]
      have h_v_two_mul : twoAdicVal c + 1 ≤ twoAdicVal ((2 : ZMod (2 ^ m)) * c) :=
        twoAdicVal_two_mul_ge h2c
      have h_v_2c_lt : twoAdicVal ((2 : ZMod (2 ^ m)) * c) < m :=
        twoAdicVal_lt_of_ne_zero h2c
      omega

/-- When `d k = 0`, the pushforward fixes the monomial. -/
lemma affinePushforward_monomial_dk_zero (i k : Fin n) (d : Fin n →₀ ℕ)
    (c : ZMod (2 ^ m)) (hdk : d k = 0) :
    affinePushforward i k (monomial d c : DiagPhase n m) = monomial d c := by
  classical
  rw [affinePushforward_eq, bind₁_monomial]
  -- Every l ∈ d.support has l ≠ k, so cnotSubst i k l = X l.
  have h_supp : ∀ l ∈ d.support, cnotSubst (m := m) i k l = X l := by
    intro l hl
    have hlk : l ≠ k := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hl) hdk
    unfold cnotSubst; rw [if_neg hlk]
  rw [Finset.prod_congr rfl (fun l hl => by rw [h_supp l hl])]
  rw [prod_X_pow_eq_monomial, C_mul_monomial, mul_one]

/-- Per-monomial bound, both cases combined. -/
lemma affinePushforward_monomial_effectiveLevel_le'
    (i k : Fin n) {d : Fin n →₀ ℕ} {c : ZMod (2 ^ m)}
    (hc : c ≠ 0) (hik : i ≠ k) (h_mul : ∀ l, d l ≤ 1) :
    effectiveLevel (affinePushforward i k (monomial d c) : DiagPhase n m)
      ≤ effLevelMonom m c d := by
  by_cases hdk : d k = 0
  · rw [affinePushforward_monomial_dk_zero i k d c hdk]
    exact effectiveLevel_monomial_le d c
  · have h_di_one : d k = 1 := by have := h_mul k; omega
    exact affinePushforward_monomial_effectiveLevel_le i k hc hik h_di_one

/-! ### The level-non-increase theorem -/

/-- **Clifford (CNOT) conjugation does not raise the effective level**:
for multilinear `P : DiagPhase n m` and `i ≠ k`,
`effectiveLevel (affinePushforward i k P) ≤ effectiveLevel P`.

The pushforward is decomposed monomial-by-monomial; each summand is
bounded by `affinePushforward_monomial_effectiveLevel_le'` and the bounds
are transferred via `effectiveLevel_finsetSum_le`. -/
theorem affinePushforward_effectiveLevel_le
    {P : DiagPhase n m} (i k : Fin n) (hik : i ≠ k)
    (h_mul : IsMultilinear P) :
    effectiveLevel (affinePushforward i k P) ≤ effectiveLevel P := by
  classical
  -- Decompose the pushforward as a sum over P.support.
  have h_decomp : affinePushforward i k P
      = ∑ d ∈ P.support, affinePushforward i k (monomial d (P.coeff d)) := by
    conv_lhs =>
      rw [show P = ∑ d ∈ P.support, monomial d (P.coeff d) from P.as_sum]
    simp only [affinePushforward_eq]
    rw [map_sum]
  rw [h_decomp]
  refine le_trans (effectiveLevel_finsetSum_le _ _) ?_
  refine Finset.sup_le ?_
  intro d hd
  have h_c_ne : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have h_d_mul : ∀ l, d l ≤ 1 := h_mul d hd
  refine le_trans
    (affinePushforward_monomial_effectiveLevel_le' i k h_c_ne hik h_d_mul) ?_
  -- effLevelMonom m (coeff d) d ≤ effectiveLevel P.
  unfold effectiveLevel
  exact Finset.le_sup (f := fun e => effLevelMonom m (P.coeff e) e) hd

end LevelTheory
end DiagPhase

end FTQCLib.Hierarchy

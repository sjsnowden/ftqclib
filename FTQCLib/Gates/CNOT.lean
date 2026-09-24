/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basis

set_option linter.unusedSectionVars false

/-! # The CNOT gate as a symplectic transformation of `Pauli n`

The two-qubit CNOT gate with control `i` and target `j` (`i ≠ j`) acts on
the binary-symplectic representation of `Pauli n` by propagating `X` from
the control to the target and `Z` from the target to the control:

  * `X_j ↦ X_j + X_i`  (X propagates control → target),
  * `Z_i ↦ Z_i + Z_j`  (Z propagates target → control),
  * `X_i` and `Z_j` are unchanged,
  * every coordinate at an index other than `i` or `j` is unchanged.

This file defines `cnotAt i j hij` as a `(ZMod 2)`-linear automorphism of
`Pauli n` and proves it preserves the symplectic form `omegaBilin`. As an
involution (its own inverse) over `ZMod 2`, both `left_inv` and
`right_inv` reduce to the identity `x + x = 0` in characteristic two.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {n : ℕ}

/-- The CNOT gate with control qubit `i` and target qubit `j`, viewed as
a `(ZMod 2)`-linear automorphism of `Pauli n`. The symplectic action is

  * `X_j ↦ X_j + X_i`,
  * `Z_i ↦ Z_i + Z_j`,
  * `X_i`, `Z_j`, and all coordinates at indices ≠ i, j unchanged.

The hypothesis `hij : i ≠ j` is needed because the X-update at `j` and
the Z-update at `i` must address distinct qubits; equivalently, the
gate is only defined on a pair of distinct qubits. -/
def cnotAt (i j : Fin n) (hij : i ≠ j) : Pauli n ≃ₗ[ZMod 2] Pauli n where
  toFun p := ⟨Function.update p.X j (p.X j + p.X i),
              Function.update p.Z i (p.Z i + p.Z j)⟩
  invFun p := ⟨Function.update p.X j (p.X j + p.X i),
               Function.update p.Z i (p.Z i + p.Z j)⟩
  left_inv p := by
    -- We need to show: invFun (toFun p) = p, where both are CNOT.
    -- The X-field of `invFun (toFun p)` evaluated at k is
    --   update (update p.X j (p.X j + p.X i)) j (... + ...) k.
    -- The "..." values are evaluations of update at j and at i.
    -- At j: update p.X j (p.X j + p.X i) j = p.X j + p.X i (by update_self).
    -- At i: update p.X j (p.X j + p.X i) i = p.X i (by update_of_ne hij, since i ≠ j).
    -- So the X-field becomes update p.X j ((p.X j + p.X i) + p.X i).
    -- In char 2: (p.X j + p.X i) + p.X i = p.X j, so this is update p.X j (p.X j) = p.X.
    apply Pauli.ext
    · funext k
      change Function.update (Function.update p.X j (p.X j + p.X i)) j
            (Function.update p.X j (p.X j + p.X i) j +
             Function.update p.X j (p.X j + p.X i) i) k = p.X k
      rw [Function.update_self, Function.update_of_ne hij]
      have heq : (p.X j + p.X i + p.X i : ZMod 2) = p.X j := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [heq, Function.update_idem, Function.update_eq_self]
    · funext k
      change Function.update (Function.update p.Z i (p.Z i + p.Z j)) i
            (Function.update p.Z i (p.Z i + p.Z j) i +
             Function.update p.Z i (p.Z i + p.Z j) j) k = p.Z k
      rw [Function.update_self, Function.update_of_ne hij.symm]
      have heq : (p.Z i + p.Z j + p.Z j : ZMod 2) = p.Z i := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [heq, Function.update_idem, Function.update_eq_self]
  right_inv p := by
    apply Pauli.ext
    · funext k
      change Function.update (Function.update p.X j (p.X j + p.X i)) j
            (Function.update p.X j (p.X j + p.X i) j +
             Function.update p.X j (p.X j + p.X i) i) k = p.X k
      rw [Function.update_self, Function.update_of_ne hij]
      have heq : (p.X j + p.X i + p.X i : ZMod 2) = p.X j := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [heq, Function.update_idem, Function.update_eq_self]
    · funext k
      change Function.update (Function.update p.Z i (p.Z i + p.Z j)) i
            (Function.update p.Z i (p.Z i + p.Z j) i +
             Function.update p.Z i (p.Z i + p.Z j) j) k = p.Z k
      rw [Function.update_self, Function.update_of_ne hij.symm]
      have heq : (p.Z i + p.Z j + p.Z j : ZMod 2) = p.Z i := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [heq, Function.update_idem, Function.update_eq_self]
  map_add' p q := by
    apply Pauli.ext
    · funext k
      change Function.update (p + q).X j ((p + q).X j + (p + q).X i) k =
            (Function.update p.X j (p.X j + p.X i) +
             Function.update q.X j (q.X j + q.X i)) k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        rw [Pi.add_apply, Function.update_self, Function.update_self]
        simp only [X_add, Pi.add_apply]
        ring
      · rw [Function.update_of_ne hk]
        change (p + q).X k = Function.update p.X j _ k + Function.update q.X j _ k
        rw [Function.update_of_ne hk, Function.update_of_ne hk]
        simp [X_add]
    · funext k
      change Function.update (p + q).Z i ((p + q).Z i + (p + q).Z j) k =
            (Function.update p.Z i (p.Z i + p.Z j) +
             Function.update q.Z i (q.Z i + q.Z j)) k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        rw [Pi.add_apply, Function.update_self, Function.update_self]
        simp only [Z_add, Pi.add_apply]
        ring
      · rw [Function.update_of_ne hk]
        change (p + q).Z k = Function.update p.Z i _ k + Function.update q.Z i _ k
        rw [Function.update_of_ne hk, Function.update_of_ne hk]
        simp [Z_add]
  map_smul' c p := by
    apply Pauli.ext
    · funext k
      change Function.update (c • p).X j ((c • p).X j + (c • p).X i) k =
            (c • Function.update p.X j (p.X j + p.X i)) k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        simp only [X_smul, Pi.smul_apply, smul_eq_mul]
        change c * p.X k + c * p.X i = c • Function.update p.X k (p.X k + p.X i) k
        rw [Function.update_self]
        simp [smul_eq_mul, mul_add]
      · rw [Function.update_of_ne hk]
        change (c • p).X k = c • Function.update p.X j _ k
        rw [Function.update_of_ne hk]
        simp [X_smul]
    · funext k
      change Function.update (c • p).Z i ((c • p).Z i + (c • p).Z j) k =
            (c • Function.update p.Z i (p.Z i + p.Z j)) k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        simp only [Z_smul, Pi.smul_apply, smul_eq_mul]
        change c * p.Z k + c * p.Z j = c • Function.update p.Z k (p.Z k + p.Z j) k
        rw [Function.update_self]
        simp [smul_eq_mul, mul_add]
      · rw [Function.update_of_ne hk]
        change (c • p).Z k = c • Function.update p.Z i _ k
        rw [Function.update_of_ne hk]
        simp [Z_smul]

@[simp] lemma cnotAt_X (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    (cnotAt i j hij p).X = Function.update p.X j (p.X j + p.X i) := rfl

@[simp] lemma cnotAt_Z (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    (cnotAt i j hij p).Z = Function.update p.Z i (p.Z i + p.Z j) := rfl

/-- CNOT preserves the symplectic form: the changes at indices `i` and
`j` contribute equal extra terms `Z_j(q) · X_i(p)` and
`X_i(p) · Z_j(q)` to each sum, which cancel in pairs over `ZMod 2`. -/
theorem cnotAt_preserves_omega (i j : Fin n) (hij : i ≠ j) (p q : Pauli n) :
    omega (cnotAt i j hij p) (cnotAt i j hij q) = omega p q := by
  -- Expand both sides
  simp only [omega, cnotAt_X, cnotAt_Z]
  -- Decompose each sum using i and j as the two special indices
  have hji : j ≠ i := fun h => hij h.symm
  -- For each of the four sums (∑ k, …) we split out the contributions
  -- at k = i and k = j, leaving a sum over the complement on which the
  -- updates evaluate to the original functions.
  -- Step 1: rewrite each sum as the sum over `Finset.univ` and use
  -- `Finset.sum_eq_sum_diff_singleton_add` twice to extract `i` and `j`.
  -- We instead use the explicit decomposition via `Finset.sum_ite_eq`
  -- style with `Function.update_apply`.
  -- Each term `Function.update f x v k` equals `if k = x then v else f k`.
  conv_lhs =>
    rw [show (∑ k, Function.update p.Z i (p.Z i + p.Z j) k *
              Function.update q.X j (q.X j + q.X i) k) =
            ∑ k, (if k = i then p.Z i + p.Z j else p.Z k) *
                  (if k = j then q.X j + q.X i else q.X k) from by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Function.update_apply, Function.update_apply]]
    rw [show (∑ k, Function.update p.X j (p.X j + p.X i) k *
              Function.update q.Z i (q.Z i + q.Z j) k) =
            ∑ k, (if k = j then p.X j + p.X i else p.X k) *
                  (if k = i then q.Z i + q.Z j else q.Z k) from by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Function.update_apply, Function.update_apply]]
  -- Now break each sum into k = i, k = j, and k ∉ {i, j}.
  have decomp1 :
      (∑ k, (if k = i then p.Z i + p.Z j else p.Z k) *
              (if k = j then q.X j + q.X i else q.X k)) =
        (p.Z i + p.Z j) * q.X i +
        p.Z j * (q.X j + q.X i) +
        ∑ k ∈ (Finset.univ.erase i).erase j, p.Z k * q.X k := by
    have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ _ hi_mem]
    have hj_mem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨hji, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ _ hj_mem]
    -- Now we have: (∑ k ∈ (univ.erase i).erase j, …) + (term at j) + (term at i)
    -- where the inner sum has k ≠ i and k ≠ j.
    rw [if_pos rfl, if_neg hji]
    rw [if_neg hij, if_pos rfl]
    -- Sum over (univ.erase i).erase j: k ≠ i and k ≠ j, both ifs are else
    have hsum : ∀ k ∈ (Finset.univ.erase i).erase j,
        (if k = i then p.Z i + p.Z j else p.Z k) *
        (if k = j then q.X j + q.X i else q.X k) = p.Z k * q.X k := by
      intro k hk
      rw [Finset.mem_erase, Finset.mem_erase] at hk
      rw [if_neg hk.2.1, if_neg hk.1]
    rw [Finset.sum_congr rfl hsum]
    ring
  have decomp2 :
      (∑ k, (if k = j then p.X j + p.X i else p.X k) *
              (if k = i then q.Z i + q.Z j else q.Z k)) =
        p.X i * (q.Z i + q.Z j) +
        (p.X j + p.X i) * q.Z j +
        ∑ k ∈ (Finset.univ.erase i).erase j, p.X k * q.Z k := by
    have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ _ hi_mem]
    have hj_mem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨hji, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ _ hj_mem]
    rw [if_neg hji, if_pos rfl]
    rw [if_pos rfl, if_neg hij]
    have hsum : ∀ k ∈ (Finset.univ.erase i).erase j,
        (if k = j then p.X j + p.X i else p.X k) *
        (if k = i then q.Z i + q.Z j else q.Z k) = p.X k * q.Z k := by
      intro k hk
      rw [Finset.mem_erase, Finset.mem_erase] at hk
      rw [if_neg hk.1, if_neg hk.2.1]
    rw [Finset.sum_congr rfl hsum]
    ring
  rw [decomp1, decomp2]
  -- For omega p q we do the analogous (trivial) decomposition
  have decomp_pq_zx :
      (∑ k, p.Z k * q.X k) =
        p.Z i * q.X i + p.Z j * q.X j +
        ∑ k ∈ (Finset.univ.erase i).erase j, p.Z k * q.X k := by
    have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ _ hi_mem]
    have hj_mem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨hji, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ _ hj_mem]
    ring
  have decomp_pq_xz :
      (∑ k, p.X k * q.Z k) =
        p.X i * q.Z i + p.X j * q.Z j +
        ∑ k ∈ (Finset.univ.erase i).erase j, p.X k * q.Z k := by
    have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    rw [← Finset.sum_erase_add _ _ hi_mem]
    have hj_mem : j ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      exact ⟨hji, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ _ hj_mem]
    ring
  rw [decomp_pq_zx, decomp_pq_xz]
  -- Now expand and compare. The extra cross-terms are
  -- p.Z j * q.X i (from decomp1, in `(p.Z i + p.Z j) * q.X i`)
  -- p.Z j * q.X i (from decomp1, in `p.Z j * (q.X j + q.X i)`)
  -- p.X i * q.Z j (from decomp2, in `p.X i * (q.Z i + q.Z j)`)
  -- p.X i * q.Z j (from decomp2, in `(p.X j + p.X i) * q.Z j`)
  -- Each pair sums to `2 * _ = 0` in ZMod 2.
  have key : (2 : ZMod 2) = 0 := by decide
  ring_nf
  rw [key]
  ring

/-- The CNOT gate is a symplectic transformation of the bilinear form
`omegaBilin`. This packages `cnotAt_preserves_omega` in the
`IsSymplecticEquiv` predicate. -/
theorem cnotAt_isSymplecticEquiv (i j : Fin n) (hij : i ≠ j) :
    IsSymplecticEquiv (omegaBilin (n := n)) (cnotAt i j hij) :=
  fun p q => by simpa using cnotAt_preserves_omega i j hij p q

end FTQCLib.Gates

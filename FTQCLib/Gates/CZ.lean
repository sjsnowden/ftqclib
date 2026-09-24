/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basis

set_option linter.unusedSectionVars false

/-! # The controlled-Z gate on Pauli strings

The two-qubit controlled-Z gate `CZ_{ij}` acts on the Pauli group by

    X_i ↦ X_i · Z_j,   Z_i ↦ Z_i
    X_j ↦ X_j · Z_i,   Z_j ↦ Z_j

(symmetric in `i, j`; CZ is its own inverse). In the binary symplectic
representation `Pauli n = (X, Z)`, this conjugation rule reads:
the X-sector is unchanged, while the Z-sector picks up the X-entry of
the partner qubit on coordinates `i` and `j`:

    (X, Z) ↦ (X, Z + X_j e_i + X_i e_j).

This file defines:

* `czAt i j hij` — the linear automorphism of `Pauli n` implementing
  CZ on qubits `i, j` (with `i ≠ j`).
* `czAt_isSymplecticEquiv` — `czAt i j hij` is a symplectic
  transformation of `omegaBilin`, i.e. an element of
  $\mathrm{Sp}(2n, \mathbb{F}_2)$.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {n : ℕ}

/-- The Z-sector update induced by `CZ` on qubits `i, j`: the function
`p.Z` with `i ↦ p.Z i + p.X j` and `j ↦ p.Z j + p.X i`. As a function
this requires `i ≠ j` to be well-defined as a "set both at once"
operation, but the two `Function.update`s commute under `i ≠ j` via
`Function.update_comm`. -/
def czZ (i j : Fin n) (p : Pauli n) : Fin n → ZMod 2 :=
  Function.update (Function.update p.Z i (p.Z i + p.X j)) j (p.Z j + p.X i)

/-- `czZ` evaluated at `i` (when `i ≠ j`) gives `p.Z i + p.X j`. -/
lemma czZ_at_i (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    czZ i j p i = p.Z i + p.X j := by
  unfold czZ
  rw [Function.update_of_ne hij, Function.update_self]

/-- `czZ` evaluated at `j` gives `p.Z j + p.X i`. -/
lemma czZ_at_j (i j : Fin n) (p : Pauli n) :
    czZ i j p j = p.Z j + p.X i := by
  unfold czZ
  rw [Function.update_self]

/-- `czZ` evaluated at any `k ∉ {i, j}` is just `p.Z k`. -/
lemma czZ_at_other (i j : Fin n) (p : Pauli n) {k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) : czZ i j p k = p.Z k := by
  unfold czZ
  rw [Function.update_of_ne hkj, Function.update_of_ne hki]

/-- Applying `czZ` twice cancels (each modification is added twice). -/
private lemma czZ_involutive (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    czZ i j ⟨p.X, czZ i j p⟩ = p.Z := by
  funext k
  by_cases hki : k = i
  · rw [hki, czZ_at_i i j hij ⟨p.X, czZ i j p⟩]
    change (czZ i j p) i + p.X j = p.Z i
    rw [czZ_at_i i j hij p, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · by_cases hkj : k = j
    · rw [hkj, czZ_at_j i j ⟨p.X, czZ i j p⟩]
      change (czZ i j p) j + p.X i = p.Z j
      rw [czZ_at_j i j p, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [czZ_at_other i j ⟨p.X, czZ i j p⟩ hki hkj]
      change (czZ i j p) k = p.Z k
      rw [czZ_at_other i j p hki hkj]

/-- `czZ` is additive in `p`: `czZ i j (p + q) = czZ i j p + czZ i j q`.
Direct case analysis at coordinates `i`, `j`, and other. -/
private lemma czZ_add (i j : Fin n) (hij : i ≠ j) (p q : Pauli n) :
    czZ i j (p + q) = czZ i j ⟨p.X, p.Z⟩ + czZ i j ⟨q.X, q.Z⟩ := by
  funext k
  by_cases hki : k = i
  · rw [hki, czZ_at_i i j hij (p + q), Pi.add_apply,
        czZ_at_i i j hij ⟨p.X, p.Z⟩,
        czZ_at_i i j hij ⟨q.X, q.Z⟩]
    change p.Z i + q.Z i + (p.X j + q.X j) = (p.Z i + p.X j) + (q.Z i + q.X j)
    ring
  · by_cases hkj : k = j
    · rw [hkj, czZ_at_j i j (p + q), Pi.add_apply,
          czZ_at_j i j ⟨p.X, p.Z⟩,
          czZ_at_j i j ⟨q.X, q.Z⟩]
      change p.Z j + q.Z j + (p.X i + q.X i) = (p.Z j + p.X i) + (q.Z j + q.X i)
      ring
    · rw [czZ_at_other i j (p + q) hki hkj, Pi.add_apply,
          czZ_at_other i j ⟨p.X, p.Z⟩ hki hkj,
          czZ_at_other i j ⟨q.X, q.Z⟩ hki hkj]
      change p.Z k + q.Z k = p.Z k + q.Z k
      rfl

/-- `czZ` is `ZMod 2`-homogeneous in `p`. -/
private lemma czZ_smul (i j : Fin n) (hij : i ≠ j) (c : ZMod 2) (p : Pauli n) :
    czZ i j ⟨c • p.X, c • p.Z⟩ = c • czZ i j p := by
  funext k
  by_cases hki : k = i
  · rw [hki, czZ_at_i i j hij ⟨c • p.X, c • p.Z⟩]
    change c • p.Z i + c • p.X j = (c • czZ i j p) i
    rw [Pi.smul_apply, czZ_at_i i j hij p, smul_add]
  · by_cases hkj : k = j
    · rw [hkj, czZ_at_j i j ⟨c • p.X, c • p.Z⟩]
      change c • p.Z j + c • p.X i = (c • czZ i j p) j
      rw [Pi.smul_apply, czZ_at_j i j p, smul_add]
    · rw [czZ_at_other i j ⟨c • p.X, c • p.Z⟩ hki hkj]
      change c • p.Z k = (c • czZ i j p) k
      rw [Pi.smul_apply, czZ_at_other i j p hki hkj]

/-- The controlled-Z gate `CZ` on qubits `i` and `j` (with `i ≠ j`),
as a `ZMod 2`-linear automorphism of `Pauli n`. The action on Pauli
representatives is:
  X-sector unchanged;
  Z-sector: at index `i`, add `p.X j`; at index `j`, add `p.X i`.
CZ is its own inverse — each Z-coordinate is modified twice, and the
two modifications cancel in `ZMod 2`. -/
def czAt (i j : Fin n) (hij : i ≠ j) : Pauli n ≃ₗ[ZMod 2] Pauli n where
  toFun p := ⟨p.X, czZ i j p⟩
  invFun p := ⟨p.X, czZ i j p⟩
  left_inv p := by
    ext k
    · rfl
    · exact congr_fun (czZ_involutive i j hij p) k
  right_inv p := by
    ext k
    · rfl
    · exact congr_fun (czZ_involutive i j hij p) k
  map_add' p q := by
    ext k
    · rfl
    · exact congr_fun (czZ_add i j hij p q) k
  map_smul' c p := by
    ext k
    · rfl
    · exact congr_fun (czZ_smul i j hij c p) k

@[simp] lemma czAt_X (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    (czAt i j hij p).X = p.X := rfl

@[simp] lemma czAt_Z (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    (czAt i j hij p).Z = czZ i j p := rfl

/-- `CZ` preserves the symplectic form `omega`: it is an element of
the symplectic group $\mathrm{Sp}(2n, \mathbb{F}_2)$. The "extra" terms
that the Z-sector update introduces in `ω` come in cancelling pairs
because the form is symmetric (in characteristic 2). -/
theorem czAt_preserves_omega (i j : Fin n) (hij : i ≠ j) (p q : Pauli n) :
    omega (czAt i j hij p) (czAt i j hij q) = omega p q := by
  -- Unfold `omega` and the X-component (which is unchanged).
  change (∑ k, (czZ i j p) k * q.X k) + (∑ k, p.X k * (czZ i j q) k)
       = (∑ k, p.Z k * q.X k) + (∑ k, p.X k * q.Z k)
  -- For the first sum, expand at i, j, other:
  have h1 : (∑ k, (czZ i j p) k * q.X k)
          = (∑ k, p.Z k * q.X k) + (p.X j * q.X i + p.X i * q.X j) := by
    have hsum : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        (czZ i j p) k * q.X k
        = p.Z k * q.X k
          + (if k = i then p.X j * q.X i else 0)
          + (if k = j then p.X i * q.X j else 0) := by
      intro k _
      by_cases hki : k = i
      · -- k = i, and hij : i ≠ j so k ≠ j.
        have hkj : k ≠ j := hki ▸ hij
        rw [hki, czZ_at_i i j hij p, if_pos rfl, if_neg hij, add_zero]
        ring
      · by_cases hkj : k = j
        · rw [hkj, czZ_at_j i j p, if_neg hij.symm, if_pos rfl]
          ring
        · rw [czZ_at_other i j p hki hkj, if_neg hki, if_neg hkj, add_zero,
              add_zero]
    rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    have hi : (∑ k, if k = i then p.X j * q.X i else 0) = p.X j * q.X i := by
      rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) i
            (fun _ => p.X j * q.X i),
          if_pos (Finset.mem_univ i)]
    have hj : (∑ k, if k = j then p.X i * q.X j else 0) = p.X i * q.X j := by
      rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) j
            (fun _ => p.X i * q.X j),
          if_pos (Finset.mem_univ j)]
    rw [hi, hj, add_assoc]
  -- Similarly for the second sum:
  have h2 : (∑ k, p.X k * (czZ i j q) k)
          = (∑ k, p.X k * q.Z k) + (p.X i * q.X j + p.X j * q.X i) := by
    have hsum : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        p.X k * (czZ i j q) k
        = p.X k * q.Z k
          + (if k = i then p.X i * q.X j else 0)
          + (if k = j then p.X j * q.X i else 0) := by
      intro k _
      by_cases hki : k = i
      · have hkj : k ≠ j := hki ▸ hij
        rw [hki, czZ_at_i i j hij q, if_pos rfl, if_neg hij, add_zero]
        ring
      · by_cases hkj : k = j
        · rw [hkj, czZ_at_j i j q, if_neg hij.symm, if_pos rfl]
          ring
        · rw [czZ_at_other i j q hki hkj, if_neg hki, if_neg hkj, add_zero,
              add_zero]
    rw [Finset.sum_congr rfl hsum, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    have hi : (∑ k, if k = i then p.X i * q.X j else 0) = p.X i * q.X j := by
      rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) i
            (fun _ => p.X i * q.X j),
          if_pos (Finset.mem_univ i)]
    have hj : (∑ k, if k = j then p.X j * q.X i else 0) = p.X j * q.X i := by
      rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) j
            (fun _ => p.X j * q.X i),
          if_pos (Finset.mem_univ j)]
    rw [hi, hj, add_assoc]
  rw [h1, h2]
  -- The two "extra" pieces sum to `2 * (p.X i * q.X j + p.X j * q.X i) = 0`
  -- in `ZMod 2`.
  have hchar : (2 : ZMod 2) = 0 := by decide
  have hextras :
      (p.X j * q.X i + p.X i * q.X j) + (p.X i * q.X j + p.X j * q.X i)
        = (2 : ZMod 2) * (p.X i * q.X j + p.X j * q.X i) := by ring
  -- Goal: (Σ p.Z q.X + extra1) + (Σ p.X q.Z + extra2) = Σ p.Z q.X + Σ p.X q.Z.
  -- Move things into the right shape.
  rw [show
      (∑ k, p.Z k * q.X k) + (p.X j * q.X i + p.X i * q.X j)
        + ((∑ k, p.X k * q.Z k) + (p.X i * q.X j + p.X j * q.X i))
      = ((∑ k, p.Z k * q.X k) + (∑ k, p.X k * q.Z k))
          + ((p.X j * q.X i + p.X i * q.X j) + (p.X i * q.X j + p.X j * q.X i))
      from by ring,
    hextras, hchar, zero_mul, add_zero]

/-- `czAt i j hij` is a symplectic transformation of `omegaBilin`. -/
theorem czAt_isSymplecticEquiv (i j : Fin n) (hij : i ≠ j) :
    IsSymplecticEquiv (omegaBilin (n := n)) (czAt i j hij) :=
  fun p q => by simpa using czAt_preserves_omega i j hij p q

end FTQCLib.Gates

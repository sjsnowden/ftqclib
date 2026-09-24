/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basis

set_option linter.unusedSectionVars false

/-! # The Hadamard gate

The Hadamard gate `H` on qubit `k` is the involutory Clifford whose
symplectic action on `Pauli n` swaps the `X k` and `Z k` coordinates
and leaves all other coordinates unchanged:

    H_k : (X, Z) ↦ ((X with X k ↔ Z k), (Z with Z k ↔ X k))

equivalently `H_k · X_k · H_k = Z_k` and `H_k · Z_k · H_k = X_k`,
the canonical conjugation relation defining Hadamard up to phase.

This file provides:

* `hadamardAt k` — `H_k` as a `(ZMod 2)`-linear automorphism of
  `Pauli n`, packaged as a `LinearEquiv` with `invFun = toFun` because
  `H` is an involution.
* `hadamardAt_isSymplecticEquiv k` — `H_k` preserves the symplectic
  form, i.e. it is a symplectic transformation in the sense of
  `FTQCLib.Pauli.IsSymplecticEquiv` applied to `omegaBilin`.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {n : ℕ}

/-- The Hadamard gate on qubit `k`, as the linear automorphism of
`Pauli n` obtained by swapping the `X k` and `Z k` binary coordinates.
`H` is its own inverse, so `invFun = toFun`. -/
def hadamardAt (k : Fin n) : Pauli n ≃ₗ[ZMod 2] Pauli n where
  toFun p := ⟨Function.update p.X k (p.Z k), Function.update p.Z k (p.X k)⟩
  invFun p := ⟨Function.update p.X k (p.Z k), Function.update p.Z k (p.X k)⟩
  left_inv p := by
    ext i
    · -- X-component: applying H twice returns the original X
      by_cases h : i = k
      · subst h
        change Function.update (Function.update p.X i (p.Z i)) i
            (Function.update p.Z i (p.X i) i) i = p.X i
        rw [Function.update_self, Function.update_self]
      · change Function.update (Function.update p.X k (p.Z k)) k
            (Function.update p.Z k (p.X k) k) i = p.X i
        rw [Function.update_of_ne h, Function.update_of_ne h]
    · -- Z-component: applying H twice returns the original Z
      by_cases h : i = k
      · subst h
        change Function.update (Function.update p.Z i (p.X i)) i
            (Function.update p.X i (p.Z i) i) i = p.Z i
        rw [Function.update_self, Function.update_self]
      · change Function.update (Function.update p.Z k (p.X k)) k
            (Function.update p.X k (p.Z k) k) i = p.Z i
        rw [Function.update_of_ne h, Function.update_of_ne h]
  right_inv p := by
    ext i
    · by_cases h : i = k
      · subst h
        change Function.update (Function.update p.X i (p.Z i)) i
            (Function.update p.Z i (p.X i) i) i = p.X i
        rw [Function.update_self, Function.update_self]
      · change Function.update (Function.update p.X k (p.Z k)) k
            (Function.update p.Z k (p.X k) k) i = p.X i
        rw [Function.update_of_ne h, Function.update_of_ne h]
    · by_cases h : i = k
      · subst h
        change Function.update (Function.update p.Z i (p.X i)) i
            (Function.update p.X i (p.Z i) i) i = p.Z i
        rw [Function.update_self, Function.update_self]
      · change Function.update (Function.update p.Z k (p.X k)) k
            (Function.update p.X k (p.Z k) k) i = p.Z i
        rw [Function.update_of_ne h, Function.update_of_ne h]
  map_add' p q := by
    ext i
    · -- X-component of H(p + q) equals X-component of H(p) + H(q)
      by_cases h : i = k
      · subst h
        change Function.update (p.X + q.X) i ((p.Z + q.Z) i) i =
          Function.update p.X i (p.Z i) i + Function.update q.X i (q.Z i) i
        rw [Function.update_self, Function.update_self, Function.update_self]
        rfl
      · change Function.update (p.X + q.X) k ((p.Z + q.Z) k) i =
          Function.update p.X k (p.Z k) i + Function.update q.X k (q.Z k) i
        rw [Function.update_of_ne h, Function.update_of_ne h,
            Function.update_of_ne h]
        rfl
    · -- Z-component
      by_cases h : i = k
      · subst h
        change Function.update (p.Z + q.Z) i ((p.X + q.X) i) i =
          Function.update p.Z i (p.X i) i + Function.update q.Z i (q.X i) i
        rw [Function.update_self, Function.update_self, Function.update_self]
        rfl
      · change Function.update (p.Z + q.Z) k ((p.X + q.X) k) i =
          Function.update p.Z k (p.X k) i + Function.update q.Z k (q.X k) i
        rw [Function.update_of_ne h, Function.update_of_ne h,
            Function.update_of_ne h]
        rfl
  map_smul' c p := by
    ext i
    · by_cases h : i = k
      · subst h
        change Function.update (c • p.X) i ((c • p.Z) i) i =
          c • Function.update p.X i (p.Z i) i
        rw [Function.update_self, Function.update_self]
        rfl
      · change Function.update (c • p.X) k ((c • p.Z) k) i =
          c • Function.update p.X k (p.Z k) i
        rw [Function.update_of_ne h, Function.update_of_ne h]
        rfl
    · by_cases h : i = k
      · subst h
        change Function.update (c • p.Z) i ((c • p.X) i) i =
          c • Function.update p.Z i (p.X i) i
        rw [Function.update_self, Function.update_self]
        rfl
      · change Function.update (c • p.Z) k ((c • p.X) k) i =
          c • Function.update p.Z k (p.X k) i
        rw [Function.update_of_ne h, Function.update_of_ne h]
        rfl

@[simp] lemma hadamardAt_X (k : Fin n) (p : Pauli n) :
    (hadamardAt k p).X = Function.update p.X k (p.Z k) := rfl

@[simp] lemma hadamardAt_Z (k : Fin n) (p : Pauli n) :
    (hadamardAt k p).Z = Function.update p.Z k (p.X k) := rfl

/-- The Hadamard gate on qubit `k` preserves the symplectic form: for
all `p, q : Pauli n`, `ω(H_k p, H_k q) = ω(p, q)`.

Proof sketch: unfold `omega` and split each sum into the `i = k` term
plus the `i ≠ k` sum (via `Finset.sum_eq_add_sum_diff_singleton`).
At `i = k` the four products `p.Z k · q.X k, p.X k · q.Z k` become
`p.X k · q.Z k, p.Z k · q.X k` — a relabelling, so the sum is
unchanged. At `i ≠ k` `Function.update` returns the original values
unchanged. -/
theorem hadamardAt_isSymplecticEquiv (k : Fin n) :
    IsSymplecticEquiv (omegaBilin (n := n)) (hadamardAt k) := by
  intro p q
  -- Reduce to a statement about `omega`.
  simp only [omegaBilin_apply, omega, hadamardAt_X, hadamardAt_Z]
  -- The four sums split as their `k`-th term plus the sum over `{k}ᶜ`.
  -- We rewrite each sum that way and check the two parts directly.
  have h_split : ∀ (f : Fin n → ZMod 2),
      ∑ i, f i = f k + ∑ i ∈ Finset.univ.erase k, f i := by
    intro f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), add_comm]
  -- Rewrite both sides as (k-term) + (sum over erase k).
  rw [h_split (fun i => Function.update p.Z k (p.X k) i *
                       Function.update q.X k (q.Z k) i),
      h_split (fun i => Function.update p.X k (p.Z k) i *
                       Function.update q.Z k (q.X k) i),
      h_split (fun i => p.Z i * q.X i),
      h_split (fun i => p.X i * q.Z i)]
  -- Simplify the `k`-th terms via `Function.update_self`.
  simp only [Function.update_self]
  -- Rewrite the two "erase k" sums on the LHS using `Function.update_of_ne`.
  have h_erase_left₁ :
      ∑ i ∈ Finset.univ.erase k,
        Function.update p.Z k (p.X k) i * Function.update q.X k (q.Z k) i =
      ∑ i ∈ Finset.univ.erase k, p.Z i * q.X i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have h_ne : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [Function.update_of_ne h_ne, Function.update_of_ne h_ne]
  have h_erase_left₂ :
      ∑ i ∈ Finset.univ.erase k,
        Function.update p.X k (p.Z k) i * Function.update q.Z k (q.X k) i =
      ∑ i ∈ Finset.univ.erase k, p.X i * q.Z i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have h_ne : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [Function.update_of_ne h_ne, Function.update_of_ne h_ne]
  rw [h_erase_left₁, h_erase_left₂]
  -- Now both sides are (p.X k * q.Z k + Σ_erase p.Z·q.X) +
  --                   (p.Z k * q.X k + Σ_erase p.X·q.Z)
  -- versus            (p.Z k * q.X k + Σ_erase p.Z·q.X) +
  --                   (p.X k * q.Z k + Σ_erase p.X·q.Z).
  -- The two `k`-th cross-terms swap; the erase sums are identical.
  ring

end FTQCLib.Gates

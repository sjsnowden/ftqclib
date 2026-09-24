/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Basis

set_option linter.unusedSectionVars false

/-! # The phase gate `S` on qubit `k`

The single-qubit phase gate `S` (a Clifford operator) acts on Pauli
operators by conjugation as
\[
  S X S^{-1} = Y = i\, X Z,\qquad S Z S^{-1} = Z.
\]
In the binary-symplectic representation (modulo phase) on `Pauli n`, the
action of `S` on qubit `k` is captured by the `(ZMod 2)`-linear map that
leaves the `X`-sector unchanged and sends the `k`-th `Z`-coordinate
\(Z_k \mapsto Z_k + X_k\) while fixing every other coordinate. Phases
($i$ and $-1$) are factored out, so this captures the symplectic action
exactly.

Because we work modulo phase and the underlying field has characteristic
two, the gate is its own inverse: applying the transformation twice maps
$Z_k \mapsto Z_k + 2 X_k = Z_k$.

This file defines:

* `phaseAt k : Pauli n ≃ₗ[ZMod 2] Pauli n` — the phase gate $S$ on
  qubit $k$, packaged as a linear automorphism of `Pauli n`.
* `phaseAt_isSymplecticEquiv k` — the gate preserves the symplectic form
  `omegaBilin`, i.e. it is an element of $\mathrm{Sp}(2n, \mathbb{F}_2)$.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {n : ℕ}

/-- Helper: in characteristic two, `z + x + x = z`. Used to show that
the phase-gate transformation is its own inverse. -/
private lemma charTwo_z_add_x_add_x (z x : ZMod 2) : z + x + x = z := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The phase gate `S` on qubit `k` as a linear automorphism of
`Pauli n` (modulo phase). The `X`-sector is unchanged and the `k`-th
`Z`-coordinate is replaced by `p.Z k + p.X k`; every other coordinate
is fixed. The map is an involution in characteristic two. -/
def phaseAt (k : Fin n) : Pauli n ≃ₗ[ZMod 2] Pauli n where
  toFun p := ⟨p.X, Function.update p.Z k (p.Z k + p.X k)⟩
  invFun p := ⟨p.X, Function.update p.Z k (p.Z k + p.X k)⟩
  left_inv p := by
    ext i
    · rfl
    · by_cases hik : i = k
      · subst hik
        change Function.update (Function.update p.Z i (p.Z i + p.X i)) i
              (Function.update p.Z i (p.Z i + p.X i) i + p.X i) i = p.Z i
        rw [Function.update_self, Function.update_self]
        exact charTwo_z_add_x_add_x _ _
      · change Function.update (Function.update p.Z k (p.Z k + p.X k)) k
              (Function.update p.Z k (p.Z k + p.X k) k + p.X k) i = p.Z i
        rw [Function.update_of_ne hik, Function.update_of_ne hik]
  right_inv p := by
    ext i
    · rfl
    · by_cases hik : i = k
      · subst hik
        change Function.update (Function.update p.Z i (p.Z i + p.X i)) i
              (Function.update p.Z i (p.Z i + p.X i) i + p.X i) i = p.Z i
        rw [Function.update_self, Function.update_self]
        exact charTwo_z_add_x_add_x _ _
      · change Function.update (Function.update p.Z k (p.Z k + p.X k)) k
              (Function.update p.Z k (p.Z k + p.X k) k + p.X k) i = p.Z i
        rw [Function.update_of_ne hik, Function.update_of_ne hik]
  map_add' p q := by
    ext i
    · rfl
    · by_cases hik : i = k
      · subst hik
        change Function.update (p.Z + q.Z) i ((p.Z + q.Z) i + (p.X + q.X) i) i =
             Function.update p.Z i (p.Z i + p.X i) i +
               Function.update q.Z i (q.Z i + q.X i) i
        rw [Function.update_self, Function.update_self, Function.update_self]
        simp [Pi.add_apply]; ring
      · change Function.update (p.Z + q.Z) k ((p.Z + q.Z) k + (p.X + q.X) k) i =
             Function.update p.Z k (p.Z k + p.X k) i +
               Function.update q.Z k (q.Z k + q.X k) i
        rw [Function.update_of_ne hik, Function.update_of_ne hik,
            Function.update_of_ne hik]
        rfl
  map_smul' c p := by
    ext i
    · rfl
    · by_cases hik : i = k
      · subst hik
        change Function.update (c • p.Z) i ((c • p.Z) i + (c • p.X) i) i =
             c • Function.update p.Z i (p.Z i + p.X i) i
        rw [Function.update_self, Function.update_self]
        simp [Pi.smul_apply, smul_eq_mul]; ring
      · change Function.update (c • p.Z) k ((c • p.Z) k + (c • p.X) k) i =
             c • Function.update p.Z k (p.Z k + p.X k) i
        rw [Function.update_of_ne hik, Function.update_of_ne hik]
        rfl

@[simp] lemma phaseAt_X (k : Fin n) (p : Pauli n) :
    (phaseAt k p).X = p.X := rfl

@[simp] lemma phaseAt_Z (k : Fin n) (p : Pauli n) :
    (phaseAt k p).Z = Function.update p.Z k (p.Z k + p.X k) := rfl

/-- Splitting a sum over `Fin n` of the form `Σ_i update f k v i * g i`
into the contribution at `k` and the rest. -/
private lemma sum_update_mul_left (k : Fin n) (f g : Fin n → ZMod 2)
    (v : ZMod 2) :
    (∑ i, Function.update f k v i * g i) =
      (∑ i ∈ Finset.univ.erase k, f i * g i) + v * g k := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hik]
  · rw [Function.update_self]

/-- Splitting a sum over `Fin n` of the form `Σ_i g i * update f k v i`
into the contribution at `k` and the rest. -/
private lemma sum_mul_update_right (k : Fin n) (f g : Fin n → ZMod 2)
    (v : ZMod 2) :
    (∑ i, g i * Function.update f k v i) =
      (∑ i ∈ Finset.univ.erase k, g i * f i) + g k * v := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hik]
  · rw [Function.update_self]

/-- The phase gate preserves the symplectic form: it is a symplectic
transformation, i.e. an element of $\mathrm{Sp}(2n, \mathbb{F}_2)$. The
only contributions to `ω` that change are at index `k`, and the extra
cross-terms `X_k · X_k` cancel in characteristic two. -/
theorem phaseAt_isSymplecticEquiv (k : Fin n) :
    IsSymplecticEquiv (omegaBilin (n := n)) (phaseAt k) := by
  intro p q
  simp only [omegaBilin_apply, omega, phaseAt_X, phaseAt_Z]
  -- Split the modified left-hand sum.
  rw [sum_update_mul_left k p.Z q.X (p.Z k + p.X k),
      sum_mul_update_right k q.Z p.X (q.Z k + q.X k)]
  -- And the unmodified right-hand sums (rewrite them in the same split form
  -- so the algebraic cancellation is visible).
  have hZX : (∑ i, p.Z i * q.X i) =
      (∑ i ∈ Finset.univ.erase k, p.Z i * q.X i) + p.Z k * q.X k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have hXZ : (∑ i, p.X i * q.Z i) =
      (∑ i ∈ Finset.univ.erase k, p.X i * q.Z i) + p.X k * q.Z k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  rw [hZX, hXZ]
  -- Now both sides are split into the same "rest" plus a `k`-contribution.
  -- The `k`-contribution differs by `p.X k * q.X k + p.X k * q.X k`, which
  -- vanishes in characteristic two.
  have hk : (p.Z k + p.X k) * q.X k + p.X k * (q.Z k + q.X k) =
            p.Z k * q.X k + p.X k * q.Z k := by
    have h2 : p.X k * q.X k + p.X k * q.X k = 0 :=
      CharTwo.add_self_eq_zero _
    -- (Z + X) * X' + X * (Z' + X') = Z*X' + X*X' + X*Z' + X*X'
    --                              = Z*X' + X*Z' + (X*X' + X*X')
    --                              = Z*X' + X*Z'.
    have : (p.Z k + p.X k) * q.X k + p.X k * (q.Z k + q.X k) =
           (p.Z k * q.X k + p.X k * q.Z k) +
             (p.X k * q.X k + p.X k * q.X k) := by ring
    rw [this, h2, add_zero]
  -- Goal: (S1 + a) + (S2 + b) = (S1 + a') + (S2 + b') where a + b = a' + b'.
  -- Rearrange both sides to (S1 + S2) + (a + b) and (S1 + S2) + (a' + b'),
  -- then apply `hk`.
  set S1 : ZMod 2 := ∑ i ∈ Finset.univ.erase k, p.Z i * q.X i
  set S2 : ZMod 2 := ∑ i ∈ Finset.univ.erase k, p.X i * q.Z i
  have lhs_rearr :
      S1 + (p.Z k + p.X k) * q.X k + (S2 + p.X k * (q.Z k + q.X k)) =
      (S1 + S2) + ((p.Z k + p.X k) * q.X k + p.X k * (q.Z k + q.X k)) := by
    ring
  have rhs_rearr :
      S1 + p.Z k * q.X k + (S2 + p.X k * q.Z k) =
      (S1 + S2) + (p.Z k * q.X k + p.X k * q.Z k) := by
    ring
  rw [lhs_rearr, rhs_rearr, hk]

end FTQCLib.Gates

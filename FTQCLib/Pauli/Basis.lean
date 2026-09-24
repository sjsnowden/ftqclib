/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Symplectic

set_option linter.unusedSectionVars false

/-! # The standard symplectic basis of `Pauli n`

The `2n` Paulis `paulix i` (a pure `X` on qubit `i`) and `pauliz i` (a
pure `Z` on qubit `i`) form a basis of `Pauli n` with the standard
symplectic relations:

    ω(X_i, Z_j) = δ_{ij},   ω(X_i, X_j) = 0,   ω(Z_i, Z_j) = 0.

These relations are the defining commutation relations of the
single-qubit Pauli operators lifted to the binary-symplectic
representation: two distinct qubits' Paulis commute, and `X` and `Z` on
the same qubit anticommute.

This file defines:

* `paulix`, `pauliz` — the standard single-qubit Pauli
  generators as elements of `Pauli n`.
* `omega_paulix_pauliz`, `omega_paulix_paulix`,
  `omega_pauliz_pauliz` — the standard symplectic relations.

The general statements that any non-degenerate symplectic vector space
over `ZMod 2` admits a symplectic basis, and that two such bases differ
by a symplectic transformation (the Witt extension theorem), are not
stated in this file. Existence of a symplectic basis, abstractly and on the
logical quotient `N(S)/S` (via the non-degeneracy proved in
`FTQCLib.Stabilizer.Logical.omegaQ_nondegenerate`), is in
`FTQCLib.Stabilizer.WittBasis` (`exists_symplecticBasis_of_nondeg_alt`,
`exists_symplecticBasis_logicalQuotient`).
-/

namespace FTQCLib.Pauli

variable {n : ℕ}

/-- The pure `X` Pauli on qubit `i`: an element of `Pauli n` with a single
non-zero entry in the `X`-sector at position `i`. -/
def paulix (i : Fin n) : Pauli n :=
  ⟨Pi.single i 1, 0⟩

/-- The pure `Z` Pauli on qubit `i`: an element of `Pauli n` with a single
non-zero entry in the `Z`-sector at position `i`. -/
def pauliz (i : Fin n) : Pauli n :=
  ⟨0, Pi.single i 1⟩

@[simp] lemma paulix_X (i : Fin n) : (paulix i).X = Pi.single i 1 := rfl
@[simp] lemma paulix_Z (i : Fin n) : (paulix i).Z = 0 := rfl
@[simp] lemma pauliz_X (i : Fin n) : (pauliz i).X = 0 := rfl
@[simp] lemma pauliz_Z (i : Fin n) : (pauliz i).Z = Pi.single i 1 := rfl

/-- The standard anticommutation relation: `ω(X_i, Z_j) = δ_{ij}`. -/
theorem omega_paulix_pauliz (i j : Fin n) :
    omega (paulix i) (pauliz j) = if i = j then 1 else 0 := by
  simp only [omega, paulix_X, paulix_Z, pauliz_X, pauliz_Z, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]; ring
    · intros k _ hki
      rw [Pi.single_eq_of_ne hki]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · rw [if_neg h]
    refine Finset.sum_eq_zero ?_
    intro k _
    by_cases hki : k = i
    · subst hki
      rw [Pi.single_eq_of_ne h]; ring
    · rw [Pi.single_eq_of_ne hki]; ring

/-- The standard commutation relation: `ω(X_i, X_j) = 0`. -/
@[simp]
theorem omega_paulix_paulix (i j : Fin n) :
    omega (paulix i) (paulix j) = 0 := by
  simp [omega]

/-- The standard commutation relation: `ω(Z_i, Z_j) = 0`. -/
@[simp]
theorem omega_pauliz_pauliz (i j : Fin n) :
    omega (pauliz i) (pauliz j) = 0 := by
  simp [omega]

/-- `ω(X_i, X_i) = 0` and `ω(Z_i, Z_i) = 0` — special case of the
above, useful as `simp` hooks. -/
@[simp]
theorem omega_paulix_self (i : Fin n) : omega (paulix i) (paulix i) = 0 :=
  omega_self _

@[simp]
theorem omega_pauliz_self (i : Fin n) : omega (pauliz i) (pauliz i) = 0 :=
  omega_self _

/-- `ω(X_i, Z_i) = 1` — the canonical conjugate-pair relation. -/
theorem omega_paulix_pauliz_self (i : Fin n) :
    omega (paulix i) (pauliz i) = 1 := by
  rw [omega_paulix_pauliz, if_pos rfl]

/-! ## Abstract symplectic bases

A \emph{symplectic basis} of a `ZMod 2`-vector space `V` carrying a
bilinear form `B` is a pair of finite indexed families
`(e_i, f_i : ι → V)` such that
`B(e_i, f_j) = δ_{ij}`, `B(e_i, e_j) = 0`, and `B(f_i, f_j) = 0`.

We package the predicate as `IsSymplecticPair` (one such pair) and use
it both for `omegaBilin` on `Pauli n` and for the descended form on the
logical quotient.
-/

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ι : Type*} [DecidableEq ι]

/-- The symplectic-basis predicate for an indexed pair of families
`(e i, f i : ι → V)` with respect to a bilinear form `B`: the families
satisfy the canonical Pauli commutation relations. The Pauli space
`Pauli n` and the logical quotient `N(S)/S` are the two intended
instantiations. -/
structure IsSymplecticPair
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (e f : ι → V) : Prop where
  /-- `B(e_i, f_j) = δ_{ij}`. -/
  pairing : ∀ i j, B (e i) (f j) = if i = j then 1 else 0
  /-- `B(e_i, e_j) = 0`. -/
  e_isOrtho : ∀ i j, B (e i) (e j) = 0
  /-- `B(f_i, f_j) = 0`. -/
  f_isOrtho : ∀ i j, B (f i) (f j) = 0

/-- The standard symplectic basis `(paulix, pauliz)` of `Pauli n` with
respect to `omegaBilin`. -/
theorem isSymplecticPair_omegaBilin :
    IsSymplecticPair (omegaBilin (n := n)) paulix pauliz where
  pairing i j := by simpa using omega_paulix_pauliz i j
  e_isOrtho i j := by simp
  f_isOrtho i j := by simp

/-- A permutation of pair indices preserves the symplectic-basis
predicate: if `(e, f)` is a symplectic basis and `σ : ι ≃ ι`, then
`(e ∘ σ, f ∘ σ)` is also a symplectic basis. This is the \emph{relabel}
freedom: the choice of which logical qubit is `1`, which is `2`,
\ldots is unconstrained. -/
theorem IsSymplecticPair.comp_equiv
    {B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} {e f : ι → V}
    (hef : IsSymplecticPair B e f) (σ : ι ≃ ι) :
    IsSymplecticPair B (e ∘ σ) (f ∘ σ) where
  pairing i j := by
    simp only [Function.comp_apply]
    rw [hef.pairing]
    by_cases h : i = j
    · simp [h]
    · rw [if_neg h, if_neg (fun heq => h (σ.injective heq))]
  e_isOrtho i j := by simp [Function.comp_apply, hef.e_isOrtho]
  f_isOrtho i j := by simp [Function.comp_apply, hef.f_isOrtho]

/-- A linear automorphism `T : V ≃ₗ V` is a \emph{symplectic
transformation} of the bilinear form `B` iff `B(T x, T y) = B(x, y)`
for all `x, y`. -/
def IsSymplecticEquiv (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (T : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ x y, B (T x) (T y) = B x y

/-- A symplectic transformation sends symplectic bases to symplectic
bases. This is the \emph{virtual SWAP} freedom: any element
of the symplectic group `Sp(2k, F_2)` produces a new symplectic basis
that, together with Pauli frame tracking, realizes a logical
permutation without any physical qubit operation. -/
theorem IsSymplecticPair.map_isSymplecticEquiv
    {B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} {e f : ι → V}
    (hef : IsSymplecticPair B e f) {T : V ≃ₗ[ZMod 2] V}
    (hT : IsSymplecticEquiv B T) :
    IsSymplecticPair B (T ∘ e) (T ∘ f) where
  pairing i j := by
    simp only [Function.comp_apply]
    rw [hT, hef.pairing]
  e_isOrtho i j := by
    simp only [Function.comp_apply]
    rw [hT, hef.e_isOrtho]
  f_isOrtho i j := by
    simp only [Function.comp_apply]
    rw [hT, hef.f_isOrtho]

end FTQCLib.Pauli

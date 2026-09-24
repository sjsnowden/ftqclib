/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Logical
import FTQCLib.Pauli.Basis
import FTQCLib.CSS.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.unusedSectionVars false

/-! # Code automorphisms

A \emph{code automorphism} of a stabilizer code $(S \subseteq
\mathcal{P}_n)$ is a permutation $\sigma$ of the $n$ physical qubits
whose induced action on Pauli strings sends $S$ to itself. The
collection of all such permutations forms a subgroup of $S_n$, the
\emph{automorphism group of the code}.

A permutation $\sigma : \mathrm{Fin}\ n \to \mathrm{Fin}\ n$ acts on
$\mathcal{P}_n$ by relabeling the X- and Z-coordinates simultaneously:
\[
  \sigma \cdot (x, z) \;=\; (x \circ \sigma^{-1}, z \circ \sigma^{-1}).
\]
We use the inverse so that the action is a left action: $(\sigma \tau)
\cdot p = \sigma \cdot (\tau \cdot p)$.

This file defines:

* **Permutation action** `pauliPermute` — the action of a
  permutation `σ : Equiv.Perm (Fin n)` on `Pauli n`, packaged as a
  linear automorphism of `Pauli n`.
* **Preservation of `ω`** `pauliPermute_preserves_omega` — the
  action is a symplectic transformation of `omegaBilin`.
* **Code automorphism** `IsCodeAutomorphism` — the predicate
  that the action of `σ` preserves the stabilizer subspace `S`.

This file does not treat the CSS decomposition of `Aut(code)` or the
induced action on `N(S)/S`.
-/

namespace FTQCLib.Aut

open FTQCLib.Pauli FTQCLib.Stabilizer

variable {n r_X r_Z : ℕ}

/-- The action of a permutation `σ : Equiv.Perm (Fin n)` on `Pauli n`,
relabeling X- and Z-coordinates by `σ⁻¹`. Packaged as a linear
automorphism of `Pauli n`. -/
def pauliPermute (σ : Equiv.Perm (Fin n)) : Pauli n ≃ₗ[ZMod 2] Pauli n where
  toFun p := ⟨p.X ∘ σ.symm, p.Z ∘ σ.symm⟩
  invFun p := ⟨p.X ∘ σ, p.Z ∘ σ⟩
  left_inv p := by
    ext i <;> simp [Function.comp_apply]
  right_inv p := by
    ext i <;> simp [Function.comp_apply]
  map_add' p q := by ext <;> rfl
  map_smul' c p := by ext <;> rfl

@[simp] lemma pauliPermute_X (σ : Equiv.Perm (Fin n)) (p : Pauli n) :
    (pauliPermute σ p).X = p.X ∘ σ.symm := rfl

@[simp] lemma pauliPermute_Z (σ : Equiv.Perm (Fin n)) (p : Pauli n) :
    (pauliPermute σ p).Z = p.Z ∘ σ.symm := rfl

/-- The permutation action preserves the symplectic form: it is an
element of the symplectic group $\mathrm{Sp}(2n, \mathbb{F}_2)$. -/
theorem pauliPermute_preserves_omega (σ : Equiv.Perm (Fin n)) (p q : Pauli n) :
    omega (pauliPermute σ p) (pauliPermute σ q) = omega p q := by
  simp only [omega, pauliPermute_X, pauliPermute_Z, Function.comp_apply]
  congr 1
  · exact Finset.sum_equiv σ.symm (by simp) (by simp)
  · exact Finset.sum_equiv σ.symm (by simp) (by simp)

/-- The permutation action is a symplectic transformation in the sense
of `FTQCLib.Pauli.IsSymplecticEquiv`. -/
theorem pauliPermute_isSymplecticEquiv (σ : Equiv.Perm (Fin n)) :
    IsSymplecticEquiv (omegaBilin (n := n)) (pauliPermute σ) :=
  fun p q => by simpa using pauliPermute_preserves_omega σ p q

/-- A permutation `σ : Equiv.Perm (Fin n)` is a \emph{code automorphism}
of a stabilizer subspace `S` iff its action on `Pauli n` sends `S` to
itself. -/
def IsCodeAutomorphism (S : Submodule (ZMod 2) (Pauli n))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ p ∈ S, pauliPermute σ p ∈ S

/-! ## A1+ helpers: image and inverse preservation -/

/-- A code automorphism preserves the stabilizer exactly: `Submodule.map
(pauliPermute σ) S = S`. The forward direction is the definition; the
reverse uses finite-dimensionality of `S` (an injection of `S` into
itself is surjective). -/
theorem IsCodeAutomorphism.map_eq {S : Submodule (ZMod 2) (Pauli n)}
    {σ : Equiv.Perm (Fin n)} (hσ : IsCodeAutomorphism S σ) :
    Submodule.map (pauliPermute σ).toLinearMap S = S := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨p, hp, rfl⟩
    exact hσ p hp
  · rw [LinearEquiv.finrank_map_eq]

/-- The inverse permutation of a code automorphism also preserves the
stabilizer: `(pauliPermute σ).symm p ∈ S` when `p ∈ S`. -/
theorem IsCodeAutomorphism.symm_preserves {S : Submodule (ZMod 2) (Pauli n)}
    {σ : Equiv.Perm (Fin n)} (hσ : IsCodeAutomorphism S σ)
    {p : Pauli n} (hp : p ∈ S) : (pauliPermute σ).symm p ∈ S := by
  have hp_in_map : p ∈ Submodule.map (pauliPermute σ).toLinearMap S := by
    rw [hσ.map_eq]; exact hp
  obtain ⟨q, hq_in_S, hq_eq⟩ := hp_in_map
  have h_symm_eq : (pauliPermute σ).symm p = q := by
    rw [← hq_eq]; exact (pauliPermute σ).symm_apply_apply q
  rw [h_symm_eq]; exact hq_in_S

/-! ## A1+ : code automorphisms preserve the normalizer -/

/-- A code automorphism preserves the normalizer `N(S)`: it maps elements
that ω-commute with all of `S` to elements that ω-commute with all of
`S`. -/
theorem pauliPermute_preserves_normalizer
    {S : Submodule (ZMod 2) (Pauli n)} {σ : Equiv.Perm (Fin n)}
    (hσ : IsCodeAutomorphism S σ) {p : Pauli n} (hp : p ∈ normalizer S) :
    pauliPermute σ p ∈ normalizer S := by
  intro s hs
  have h_symm_s_in_S : (pauliPermute σ).symm s ∈ S := hσ.symm_preserves hs
  have h_app : pauliPermute σ ((pauliPermute σ).symm s) = s :=
    (pauliPermute σ).apply_symm_apply s
  calc omega (pauliPermute σ p) s
      = omega (pauliPermute σ p) (pauliPermute σ ((pauliPermute σ).symm s)) := by
            rw [h_app]
    _ = omega p ((pauliPermute σ).symm s) :=
        pauliPermute_preserves_omega σ p ((pauliPermute σ).symm s)
    _ = 0 := hp ((pauliPermute σ).symm s) h_symm_s_in_S

/-! ## A2: CSS-specialized code automorphisms

For a CSS code given by `(H_X, H_Z)`, we distinguish two
specializations of code automorphism:

* **X-CSS automorphism**: a qubit permutation that preserves the
  `X`-rowspan and the `Z`-rowspan \emph{separately}.
* **General code automorphism**: any permutation preserving the joint
  stabilizer `S_CSS`. This is the broader notion (it allows X↔Z
  swapping, e.g., the bicycle self-duality `π`).

Both notions sit inside `IsCodeAutomorphism (cssStabilizer H_X H_Z)`;
the X-CSS subclass is the stricter one.
-/

/-- A permutation `σ` is an \emph{X-CSS automorphism} of `(H_X, H_Z)`
if its action on `Pauli n` separately preserves the X-stabilizer
rowspan and the Z-stabilizer rowspan. -/
def IsCSSAutomorphism
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2))
    (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ p ∈ FTQCLib.CSS.cssXStabilizer H_X, pauliPermute σ p ∈ FTQCLib.CSS.cssXStabilizer H_X) ∧
  (∀ p ∈ FTQCLib.CSS.cssZStabilizer H_Z, pauliPermute σ p ∈ FTQCLib.CSS.cssZStabilizer H_Z)

/-- **A2:** an X-CSS automorphism is a code automorphism of the joint
CSS stabilizer subspace. -/
theorem IsCSSAutomorphism.to_isCodeAutomorphism
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {σ : Equiv.Perm (Fin n)} (hσ : IsCSSAutomorphism H_X H_Z σ) :
    IsCodeAutomorphism (FTQCLib.CSS.cssStabilizer H_X H_Z) σ := by
  intro p hp
  rw [FTQCLib.CSS.cssStabilizer, Submodule.mem_sup] at hp
  obtain ⟨pX, hpX, pZ, hpZ, rfl⟩ := hp
  rw [(pauliPermute σ).map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (hσ.1 pX hpX))
    (Submodule.mem_sup_right (hσ.2 pZ hpZ))

/-! ## A3: induced action on `N(S)/S`

A code automorphism `σ` induces a `(ZMod 2)`-linear automorphism of the
logical Pauli group `N(S)/S`. This homomorphism `Aut(code) → Sp(L(S))`
is what carries a physical operation (the qubit permutation) to its
logical Pauli action. -/

/-- The restriction of `pauliPermute σ` to `N(S)`, given `σ` is a code
automorphism. The codomain is again `N(S)` because automorphisms
preserve the normalizer. -/
noncomputable def pauliPermute_restrictedToNormalizer
    (S : Submodule (ZMod 2) (Pauli n)) (σ : Equiv.Perm (Fin n))
    (hσ : IsCodeAutomorphism S σ) :
    (normalizer S) →ₗ[ZMod 2] (normalizer S) :=
  LinearMap.codRestrict (normalizer S)
    ((pauliPermute σ).toLinearMap.comp (normalizer S).subtype)
    (fun p => pauliPermute_preserves_normalizer hσ p.property)

@[simp]
theorem pauliPermute_restrictedToNormalizer_val
    (S : Submodule (ZMod 2) (Pauli n)) (σ : Equiv.Perm (Fin n))
    (hσ : IsCodeAutomorphism S σ) (p : normalizer S) :
    (pauliPermute_restrictedToNormalizer S σ hσ p).val =
      pauliPermute σ p.val := rfl

/-- The restricted permutation maps the comap'd `S` into itself: if `p ∈
N(S)` and `p.val ∈ S`, then `(pauliPermute σ p).val = pauliPermute σ p.val
∈ S`. -/
theorem pauliPermute_restrictedToNormalizer_preserves_comap
    {S : Submodule (ZMod 2) (Pauli n)} {σ : Equiv.Perm (Fin n)}
    (hσ : IsCodeAutomorphism S σ) (p : normalizer S)
    (hp : p ∈ S.comap (normalizer S).subtype) :
    pauliPermute_restrictedToNormalizer S σ hσ p ∈
      S.comap (normalizer S).subtype := by
  have hp_val : p.val ∈ S := hp
  have : (pauliPermute_restrictedToNormalizer S σ hσ p).val ∈ S := hσ p.val hp_val
  exact this

/-- **A3 (linear-map version):** the induced map on `N(S)/S` from a
code automorphism. -/
noncomputable def codeAutomorphism_inducedMap
    (S : Submodule (ZMod 2) (Pauli n)) (σ : Equiv.Perm (Fin n))
    (hσ : IsCodeAutomorphism S σ) :
    (logicalQuotient S) →ₗ[ZMod 2] (logicalQuotient S) :=
  Submodule.mapQ (S.comap (normalizer S).subtype)
    (S.comap (normalizer S).subtype)
    (pauliPermute_restrictedToNormalizer S σ hσ)
    (pauliPermute_restrictedToNormalizer_preserves_comap hσ)

@[simp]
theorem codeAutomorphism_inducedMap_mk
    (S : Submodule (ZMod 2) (Pauli n)) (σ : Equiv.Perm (Fin n))
    (hσ : IsCodeAutomorphism S σ) (p : normalizer S) :
    codeAutomorphism_inducedMap S σ hσ (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk
        (pauliPermute_restrictedToNormalizer S σ hσ p) := rfl

/-- **A3 (symplectic preservation):** the induced map on `N(S)/S`
preserves the descended symplectic form `omegaQBilin`. -/
theorem codeAutomorphism_inducedMap_preserves_omegaQBilin
    (S : Submodule (ZMod 2) (Pauli n)) (σ : Equiv.Perm (Fin n))
    (hσ : IsCodeAutomorphism S σ) (p q : logicalQuotient S) :
    omegaQBilin S
        (codeAutomorphism_inducedMap S σ hσ p)
        (codeAutomorphism_inducedMap S σ hσ q) =
      omegaQBilin S p q := by
  induction p using Quotient.inductionOn with
  | _ p_rep =>
  induction q using Quotient.inductionOn with
  | _ q_rep =>
    change omega (pauliPermute σ p_rep.val) (pauliPermute σ q_rep.val) =
      omega p_rep.val q_rep.val
    exact pauliPermute_preserves_omega σ p_rep.val q_rep.val

end FTQCLib.Aut

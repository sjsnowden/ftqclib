/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Normalizer
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.FieldTheory.Finite.Basic

set_option linter.unusedSectionVars false

/-! # The logical Pauli group `N(S)/S`

For an ω-isotropic stabilizer subspace `S ⊆ Pauli n`, the quotient
`N(S) / S` is the \emph{logical Pauli group}. Its dimension as an
`F_2`-vector space is `2(n − r) = 2k`, where `r = dim S` is the stabilizer
rank and `k = n − r` is the logical-qubit count.

The symplectic form ω on `Pauli n` descends to a non-degenerate symplectic
form on `N(S) / S`, making it symplectically isomorphic to `Pauli k`. The
isomorphism depends on a choice of symplectic basis for `N(S) / S`; two
basis choices differ by a symplectic transformation. That last fact is the
algebraic core of two kinds of operations on logical qubits: pure
relabelling and virtual SWAP.

This file proves:

* **Inclusion** `subset_normalizer` — `S ⊆ N(S)`.
* **Quotient module** `logicalQuotient` — `N(S)/S` as an
  `(ZMod 2)`-module.
* **Descent of ω** `omegaQ` — the symplectic form on the quotient.
* `normalizer_eq_orthogonal` — `N(S) = omegaBilin.orthogonal S`.
* `orthogonal_orthogonal_omegaBilin` — double-orthogonal-complement
  identity for our non-degenerate, reflexive `omegaBilin`.
* **Non-degeneracy** `omegaQ_nondegenerate` — `omegaQ` is
  non-degenerate on `N(S)/S`.

The basis-choice freedom (relabelling and virtual SWAP) is in
`FTQCLib.Pauli.Basis` (`IsSymplecticPair.comp_equiv`,
`IsSymplecticPair.map_isSymplecticEquiv`), and the dimension formulas
`dim N(S) = 2n − dim S`, `dim(N(S)/S) = 2k` are in `FTQCLib.Stabilizer.Dimension`
(`finrank_normalizer`, `finrank_logicalQuotient_eq_two_logicalCount`).
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-- An ω-isotropic subspace is contained in its normalizer. -/
theorem subset_normalizer {S : Submodule (ZMod 2) (Pauli n)}
    (h : IsStabilizer S) : S ≤ normalizer S :=
  fun p hp q hq => h p hp q hq

/-- The logical Pauli group `N(S)/S` as an `(ZMod 2)`-quotient module.
The element of `Pauli n` representing a stabilizer is identified with the
zero element of the quotient; the elements that ω-commute with the
stabilizer are the cosets carrying logical-operator information. -/
abbrev logicalQuotient (S : Submodule (ZMod 2) (Pauli n)) : Type :=
  (normalizer S) ⧸ (S.comap (normalizer S).subtype)

set_option maxHeartbeats 400000 in
-- The bilinearity expansion in the well-definedness proof produces many
-- `omega`-application terms whose unifier work exceeds the default budget;
-- the proof itself is shallow but combinatorially wide.
/-- The descent of the symplectic form `ω` to the quotient `N(S)/S`.

Well-defined because for `s ∈ S` and `q ∈ N(S)`, `ω(s, q) = ω(q, s) = 0`
by the definition of `N(S)` and symmetry of `ω` in characteristic 2. The
descent combines four `omega` applications via bilinearity; each of the
three "correction" terms vanishes for this reason.
-/
def omegaQ {S : Submodule (ZMod 2) (Pauli n)} :
    logicalQuotient S → logicalQuotient S → ZMod 2 :=
  Quotient.lift₂ (fun (a b : ↥(normalizer S)) => omega a.val b.val)
    (fun a₁ b₁ a₂ b₂ ha hb => by
      have h_eq_a : (Submodule.Quotient.mk a₁ :
            (normalizer S) ⧸ (S.comap (normalizer S).subtype)) =
            Submodule.Quotient.mk a₂ := Quotient.sound ha
      have h_eq_b : (Submodule.Quotient.mk b₁ :
            (normalizer S) ⧸ (S.comap (normalizer S).subtype)) =
            Submodule.Quotient.mk b₂ := Quotient.sound hb
      have ha' : a₁ - a₂ ∈ S.comap (normalizer S).subtype :=
        (Submodule.Quotient.eq _).mp h_eq_a
      have hb' : b₁ - b₂ ∈ S.comap (normalizer S).subtype :=
        (Submodule.Quotient.eq _).mp h_eq_b
      have ha_val : a₁.val - a₂.val ∈ S := by
        have h := Submodule.mem_comap.mp ha'
        simp only [Submodule.subtype_apply] at h
        rwa [AddSubgroupClass.coe_sub] at h
      have hb_val : b₁.val - b₂.val ∈ S := by
        have h := Submodule.mem_comap.mp hb'
        simp only [Submodule.subtype_apply] at h
        rwa [AddSubgroupClass.coe_sub] at h
      change omega a₁.val b₁.val = omega a₂.val b₂.val
      have ha_decomp : a₁.val = a₂.val + (a₁.val - a₂.val) := by abel
      have hb_decomp : b₁.val = b₂.val + (b₁.val - b₂.val) := by abel
      rw [ha_decomp, hb_decomp, omega_add_left, omega_add_right,
        omega_add_right]
      have h_a₂Δb : omega a₂.val (b₁.val - b₂.val) = 0 :=
        a₂.property _ hb_val
      have h_Δab₂ : omega (a₁.val - a₂.val) b₂.val = 0 := by
        rw [omega_comm]
        exact b₂.property _ ha_val
      have h_ΔaΔb : omega (a₁.val - a₂.val) (b₁.val - b₂.val) = 0 := by
        have h_sub_val : (a₁ - a₂).val = a₁.val - a₂.val :=
          AddSubgroupClass.coe_sub _ _
        rw [← h_sub_val]
        exact (a₁ - a₂).property _ hb_val
      rw [h_a₂Δb, h_Δab₂, h_ΔaΔb]
      ring)

/-- The normalizer `N(S)` of a stabilizer subspace `S` agrees with the
omega-orthogonal complement `omegaBilin.orthogonal S` (in Mathlib's
bilinear-form sense). The two differ only in the order of arguments to
`ω`, which `omega_comm` resolves. -/
theorem normalizer_eq_orthogonal (S : Submodule (ZMod 2) (Pauli n)) :
    normalizer S = LinearMap.BilinForm.orthogonal (omegaBilin (n := n)) S := by
  ext p
  refine ⟨fun hp q hq => ?_, fun hp q hq => ?_⟩
  · change omega q p = 0
    rw [omega_comm]
    exact hp q hq
  · rw [omega_comm]
    exact hp q hq

/-- The double-orthogonal-complement identity for `omegaBilin`:
`omegaBilin.orthogonal (omegaBilin.orthogonal S) = S`. This is
Mathlib's `orthogonal_orthogonal` applied to our non-degenerate,
reflexive `omegaBilin` on the finite-dimensional `Pauli n`. -/
theorem orthogonal_orthogonal_omegaBilin (S : Submodule (ZMod 2) (Pauli n)) :
    LinearMap.BilinForm.orthogonal (omegaBilin (n := n))
        (LinearMap.BilinForm.orthogonal (omegaBilin (n := n)) S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal
    (omegaBilin_nondegenerate (n := n))
    (omegaBilin_isRefl (n := n)) S

/-- The orthogonal complement of `N(S)` is `S`: a direct consequence of
`normalizer_eq_orthogonal` plus the double-orthogonal-complement identity. -/
theorem orthogonal_normalizer_eq_self (S : Submodule (ZMod 2) (Pauli n)) :
    LinearMap.BilinForm.orthogonal (omegaBilin (n := n)) (normalizer S) = S := by
  rw [normalizer_eq_orthogonal]
  exact orthogonal_orthogonal_omegaBilin S

/-- The descended form `omegaQ` is non-degenerate on `N(S)/S`: if a logical
coset `[p]` is ω-orthogonal to every logical coset `[q]`, then `[p] = 0`.
This combines `normalizer_eq_orthogonal` with the double-orthogonal-complement
identity from Mathlib (`LinearMap.BilinForm.orthogonal_orthogonal`). -/
theorem omegaQ_nondegenerate (S : Submodule (ZMod 2) (Pauli n))
    (p : logicalQuotient S) (hp : ∀ q : logicalQuotient S, omegaQ p q = 0) :
    p = 0 := by
  induction p using Quotient.inductionOn with
  | _ p_rep =>
    have hp_val : ∀ q : ↥(normalizer S), omega p_rep.val q.val = 0 := by
      intro q
      have h := hp ⟦q⟧
      change omega p_rep.val q.val = 0
      exact h
    have hp_in_orth : p_rep.val ∈
        LinearMap.BilinForm.orthogonal (omegaBilin (n := n)) (normalizer S) := by
      intro q hq
      change omega q p_rep.val = 0
      rw [omega_comm]
      exact hp_val ⟨q, hq⟩
    rw [orthogonal_normalizer_eq_self] at hp_in_orth
    change (Submodule.Quotient.mk p_rep : logicalQuotient S) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply]
    exact hp_in_orth

/-! ## `omegaQ` as a Mathlib bilinear form

The form on the quotient comes from `omegaBilin` restricted to
`N(S) × N(S)` and lifted through the quotient. This packages it as a
`LinearMap.BilinForm` so that all of Mathlib's bilinear-form machinery
(orthogonal complement, non-degeneracy, symplectic-basis constructions,
etc.) is available on `logicalQuotient S`.
-/

/-- `omegaBilin` restricted to `N(S) × N(S)`. -/
def omegaOnNormalizer (S : Submodule (ZMod 2) (Pauli n)) :
    (normalizer S) →ₗ[ZMod 2] (normalizer S) →ₗ[ZMod 2] ZMod 2 :=
  (omegaBilin (n := n)).compl₁₂ (normalizer S).subtype (normalizer S).subtype

@[simp]
theorem omegaOnNormalizer_apply (S : Submodule (ZMod 2) (Pauli n))
    (p q : normalizer S) :
    omegaOnNormalizer S p q = omega p.val q.val := rfl

/-- The restricted form is reflexive. -/
theorem omegaOnNormalizer_isRefl (S : Submodule (ZMod 2) (Pauli n)) :
    (omegaOnNormalizer S).IsRefl := by
  intro x y h
  have h1 : omega x.val y.val = 0 := h
  change omega y.val x.val = 0
  rw [omega_comm]; exact h1

/-- The subspace `S.comap (normalizer S).subtype` lies in the kernel of
`omegaOnNormalizer`. This is exactly what makes the form descend to
the quotient: if `x.val ∈ S` then `ω(x.val, y.val) = 0` for every
`y ∈ N(S)`. -/
theorem comap_S_le_ker_omegaOnNormalizer (S : Submodule (ZMod 2) (Pauli n)) :
    (S.comap (normalizer S).subtype) ≤
      LinearMap.ker (omegaOnNormalizer S) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change omega x.val y.val = 0
  have hx_in_S : x.val ∈ S := hx
  rw [omega_comm]
  exact y.property x.val hx_in_S

/-- **Packaged form:** the descended symplectic form on `N(S)/S` as a
`LinearMap.BilinForm`. Use this when applying Mathlib bilinear-form
machinery to the logical Pauli group. -/
def omegaQBilin (S : Submodule (ZMod 2) (Pauli n)) :
    (logicalQuotient S) →ₗ[ZMod 2] (logicalQuotient S) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.IsRefl.liftQ₂ (omegaOnNormalizer S)
    (S.comap (normalizer S).subtype)
    (omegaOnNormalizer_isRefl S)
    (comap_S_le_ker_omegaOnNormalizer S)

/-- `omegaQBilin` computes via representatives: on cosets `[p]`, `[q]`
of `N(S)/S`, the form returns `ω(p, q)`. -/
@[simp]
theorem omegaQBilin_mk (S : Submodule (ZMod 2) (Pauli n))
    (p q : normalizer S) :
    omegaQBilin S (Submodule.Quotient.mk p) (Submodule.Quotient.mk q) =
      omega p.val q.val := rfl

/-- The packaged form agrees with `omegaQ`. -/
theorem omegaQBilin_eq_omegaQ (S : Submodule (ZMod 2) (Pauli n)) :
    (fun p q => omegaQBilin S p q) =
      (omegaQ (S := S)) := by
  funext p q
  induction p using Quotient.inductionOn with
  | _ p_rep =>
  induction q using Quotient.inductionOn with
  | _ q_rep => rfl

end FTQCLib.Stabilizer

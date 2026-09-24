/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Dimension
import FTQCLib.Pauli.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option linter.unusedSectionVars false

/-! # Pauli conditioning of a stabilizer subspace

Given a stabilizer subspace `S ⊆ Pauli n` and a Pauli `Q ∈ Pauli n`, the
**Pauli conditioning** of `S` by `Q` is the unique stabilizer subspace
containing `Q` and agreeing with `S` on `Q^⊥`:

    pauliCondition S Q := (S ∩ Q^⊥) ⊕ ⟨Q⟩

where `Q^⊥ = omegaBilin.orthogonal (span {Q})` is the ω-orthogonal
hyperplane of `Q`.

When `Q ∈ S` already, the formula reduces to `S` itself (since `S ⊆ Q^⊥`
by isotropy and `⟨Q⟩ ⊆ S`). When `Q ∉ S`, the generators of `S` that
ω-commute with `Q` survive (those in `S ∩ Q^⊥`); the generator that
anti-commutes is replaced by `Q`, which now sits in the new stabilizer.

For a Lagrangian (full-rank isotropic) `S` with `finrank S = n`, the
operation preserves the Lagrangian property: `pauliCondition S Q` is
again isotropic and has `finrank = n`. This is the algebraic core of
the Gottesman–Knill measurement step, formulated entirely in terms of
the symplectic-isotropic structure on `Pauli n` — no state vectors, no
probability distributions, no measurement outcomes.

This file proves:

* `pauliCondition` — the Pauli-conditioned stabilizer subspace.
* `pauliCondition_isStabilizer` — isotropy is preserved.
* `pauliCondition_mem` — `Q` lies in the conditioned subspace.
* `pauliCondition_finrank` — full-rank is preserved (Lagrangian to
  Lagrangian).

The full-rank step relies on the auxiliary fact
`orthogonal_eq_self_of_isStabilizer_full` that a Lagrangian is its own
ω-orthogonal complement.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli Module

variable {n : ℕ}

/-! ## The conditioning operation -/

/-- The Pauli conditioning of a stabilizer subspace `S ⊆ Pauli n` by a
Pauli `Q`:

* if `Q ∈ S`, the result is `S` (Q is already in the stabilizer);
* otherwise, the result is `(S ∩ Q^⊥) ⊕ ⟨Q⟩`, where `Q^⊥` is the ω-orthogonal
  complement of `span {Q}`.

`noncomputable` because the `Q ∈ S` decision is not constructive for an
arbitrary submodule. -/
noncomputable def pauliCondition
    (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) (Q : FTQCLib.Pauli n) :
    Submodule (ZMod 2) (FTQCLib.Pauli n) :=
  open Classical in
  if Q ∈ S then S
  else (S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
         (Submodule.span (ZMod 2) {Q})) ⊔ Submodule.span (ZMod 2) {Q}

/-- Unfolds `pauliCondition` in the `Q ∈ S` branch. -/
lemma pauliCondition_of_mem
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} {Q : FTQCLib.Pauli n}
    (h : Q ∈ S) :
    pauliCondition S Q = S := by
  classical
  unfold pauliCondition
  rw [if_pos h]

/-- Unfolds `pauliCondition` in the `Q ∉ S` branch. -/
lemma pauliCondition_of_not_mem
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} {Q : FTQCLib.Pauli n}
    (h : Q ∉ S) :
    pauliCondition S Q =
      (S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
         (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)))) ⊔
        Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)) := by
  classical
  unfold pauliCondition
  rw [if_neg h]

/-! ## Stabilizer-property preservation -/

/-- Pauli conditioning preserves the isotropy property: if `S` is a
stabilizer subspace, so is `pauliCondition S Q`.

When `Q ∈ S`, the result is `S` itself. When `Q ∉ S`, the result is
`(S ⊓ Q^⊥) ⊔ ⟨Q⟩`; both summands ω-commute with each other (the first by
isotropy of `S` and membership in `Q^⊥`, the second by `omega_self`). -/
theorem pauliCondition_isStabilizer
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (Q : FTQCLib.Pauli n) :
    IsStabilizer (pauliCondition S Q) := by
  classical
  by_cases hQS : Q ∈ S
  · rw [pauliCondition_of_mem hQS]
    exact hS
  · rw [pauliCondition_of_not_mem hQS]
    set T : Submodule (ZMod 2) (FTQCLib.Pauli n) :=
      S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) with hT_def
    set R : Submodule (ZMod 2) (FTQCLib.Pauli n) :=
      Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)) with hR_def
    intro p hp q hq
    -- Decompose p and q via `mem_sup`.
    rw [Submodule.mem_sup] at hp hq
    obtain ⟨s₁, hs₁, r₁, hr₁, rfl⟩ := hp
    obtain ⟨s₂, hs₂, r₂, hr₂, rfl⟩ := hq
    -- s₁, s₂ ∈ S ⊓ Q^⊥; r₁, r₂ ∈ span {Q}.
    have hs₁_S : s₁ ∈ S := (Submodule.mem_inf.mp hs₁).1
    have hs₁_ortho : s₁ ∈ LinearMap.BilinForm.orthogonal omegaBilin
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) :=
      (Submodule.mem_inf.mp hs₁).2
    have hs₂_S : s₂ ∈ S := (Submodule.mem_inf.mp hs₂).1
    have hs₂_ortho : s₂ ∈ LinearMap.BilinForm.orthogonal omegaBilin
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) :=
      (Submodule.mem_inf.mp hs₂).2
    -- r₁ = c₁ • Q, r₂ = c₂ • Q.
    rw [Submodule.mem_span_singleton] at hr₁ hr₂
    obtain ⟨c₁, rfl⟩ := hr₁
    obtain ⟨c₂, rfl⟩ := hr₂
    -- Expand ω((s₁ + c₁•Q), (s₂ + c₂•Q)) by bilinearity.
    have hQ_mem : Q ∈ Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)) :=
      Submodule.subset_span (by simp)
    have h_s₁_Q : omega s₁ Q = 0 := by
      have h := hs₁_ortho Q hQ_mem
      change omega Q s₁ = 0 at h
      rw [omega_comm] at h
      exact h
    have h_s₂_Q : omega s₂ Q = 0 := by
      have h := hs₂_ortho Q hQ_mem
      change omega Q s₂ = 0 at h
      rw [omega_comm] at h
      exact h
    have h_Q_s₂ : omega Q s₂ = 0 := by
      rw [omega_comm]; exact h_s₂_Q
    have h_s₁_s₂ : omega s₁ s₂ = 0 := hS s₁ hs₁_S s₂ hs₂_S
    have h_Q_Q : omega Q Q = 0 := omega_self Q
    -- Now compute.
    rw [omega_add_left, omega_add_right, omega_add_right,
        omega_smul_right, omega_smul_left, omega_smul_right,
        omega_smul_left]
    rw [h_s₁_s₂, h_s₁_Q, h_Q_s₂, h_Q_Q]
    ring

/-! ## `Q` is in the conditioned subspace -/

/-- After conditioning on `Q`, the operator `Q` itself stabilizes the
new codespace: `Q ∈ pauliCondition S Q`. Both branches of the update
contain `Q` directly — either `Q ∈ S` (case 1) or `Q ∈ ⟨Q⟩ ≤ S'` (case 2). -/
theorem pauliCondition_mem
    (S : Submodule (ZMod 2) (FTQCLib.Pauli n)) (Q : FTQCLib.Pauli n) :
    Q ∈ pauliCondition S Q := by
  classical
  by_cases hQS : Q ∈ S
  · rw [pauliCondition_of_mem hQS]; exact hQS
  · rw [pauliCondition_of_not_mem hQS]
    have hQ_span : Q ∈ Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)) :=
      Submodule.subset_span (by simp)
    exact Submodule.mem_sup_right hQ_span

/-! ## Full-rank preservation: Lagrangian to Lagrangian -/

/-- For a Lagrangian (full-rank isotropic) stabilizer subspace `S` with
`finrank S = n`, the ω-orthogonal complement of `S` equals `S` itself.

Proof: isotropy gives `S ≤ ω.orthogonal S`, and the non-degeneracy formula
`finrank (ω.orthogonal S) = finrank V − finrank S` plus `finrank V = 2n`
gives `finrank (ω.orthogonal S) = n = finrank S`. Equal-rank inclusion ⇒
equal. -/
private theorem orthogonal_eq_self_of_isStabilizer_full
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (hRank : finrank (ZMod 2) S = n) :
    LinearMap.BilinForm.orthogonal omegaBilin S = S := by
  have h_le : S ≤ LinearMap.BilinForm.orthogonal omegaBilin S := by
    intro s hs q hq
    change omega q s = 0
    rw [omega_comm]
    exact hS s hs q hq
  have h_rank_orth :
      finrank (ZMod 2) (LinearMap.BilinForm.orthogonal omegaBilin S) =
        2 * n - finrank (ZMod 2) S := by
    rw [LinearMap.BilinForm.finrank_orthogonal omegaBilin_nondegenerate,
        finrank_Pauli]
  have h_rank_eq :
      finrank (ZMod 2) S =
        finrank (ZMod 2) (LinearMap.BilinForm.orthogonal omegaBilin S) := by
    rw [h_rank_orth, hRank]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq h_le h_rank_eq).symm

/-- Auxiliary: for a Lagrangian `S` and `Q ∉ S`, there exists `M ∈ S` with
`omega M Q = 1`. Otherwise `Q` would lie in `ω.orthogonal S = S`. -/
theorem exists_anticommuting_of_not_mem_full
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (hRank : finrank (ZMod 2) S = n) {Q : FTQCLib.Pauli n} (hQS : Q ∉ S) :
    ∃ M ∈ S, omega M Q = 1 := by
  by_contra hno
  apply hQS
  rw [← orthogonal_eq_self_of_isStabilizer_full hS hRank]
  intro s hs
  change omega s Q = 0
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (omega s Q) with h0 | h1
  · exact h0
  · exact absurd ⟨s, hs, h1⟩ hno

/-- For a Lagrangian `S` and `Q ∉ S`, the subspace `S ⊓ Q^⊥` has dimension
`n − 1`.

Proof: the linear map `φ : S → ZMod 2`, `φ(s) = ω(s, Q)`, is surjective
(some `M ∈ S` has `ω(M, Q) = 1`), with kernel `S ⊓ Q^⊥`. Rank-nullity on
`φ` then gives `finrank (ker φ) = n − 1`. -/
private theorem finrank_inf_orthogonal_singleton_of_not_mem
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (hRank : finrank (ZMod 2) S = n) {Q : FTQCLib.Pauli n} (hQS : Q ∉ S) :
    finrank (ZMod 2)
      (S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) :
        Submodule (ZMod 2) (FTQCLib.Pauli n)) = n - 1 := by
  -- Build φ : S → ZMod 2 sending s to ω(s, Q).
  let φ : S →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun s => omega s.val Q
      map_add' := fun s t => by
        change omega (s.val + t.val) Q = omega s.val Q + omega t.val Q
        exact omega_add_left _ _ _
      map_smul' := fun c s => by
        change omega (c • s.val) Q = c • omega s.val Q
        rw [omega_smul_left]; rfl }
  -- φ is surjective.
  have h_surj : Function.Surjective φ := by
    obtain ⟨M, hM_S, hM_anti⟩ :=
      exists_anticommuting_of_not_mem_full hS hRank hQS
    intro c
    refine ⟨c • ⟨M, hM_S⟩, ?_⟩
    change omega ((c • ⟨M, hM_S⟩ : S).val) Q = c
    have h_val : ((c • ⟨M, hM_S⟩ : S).val) = c • M := rfl
    rw [h_val, omega_smul_left, hM_anti, mul_one]
  -- Range of φ is ⊤.
  have h_range : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr h_surj
  -- finrank (range φ) = 1.
  have h_rank_range : finrank (ZMod 2) (LinearMap.range φ) = 1 := by
    rw [h_range, finrank_top]
    exact finrank_self _
  -- Rank-nullity for φ.
  have h_rk_nul :
      finrank (ZMod 2) (LinearMap.range φ) + finrank (ZMod 2) (LinearMap.ker φ) =
        finrank (ZMod 2) S := LinearMap.finrank_range_add_finrank_ker φ
  rw [h_rank_range, hRank] at h_rk_nul
  -- ker φ corresponds via the subtype embedding to S ⊓ Q^⊥.
  have h_ker_eq :
      finrank (ZMod 2) (LinearMap.ker φ) =
        finrank (ZMod 2)
          (S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
            (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) :
            Submodule (ZMod 2) (FTQCLib.Pauli n)) := by
    let e : LinearMap.ker φ ≃ₗ[ZMod 2]
        (S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
          (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) :
          Submodule (ZMod 2) (FTQCLib.Pauli n)) :=
      { toFun := fun x =>
          ⟨x.val.val, by
            refine Submodule.mem_inf.mpr ⟨x.val.property, ?_⟩
            intro q hq
            rw [Submodule.mem_span_singleton] at hq
            obtain ⟨c, rfl⟩ := hq
            change omega (c • Q) x.val.val = 0
            rw [omega_smul_left]
            have h_phi : φ x.val = 0 := x.property
            change omega x.val.val Q = 0 at h_phi
            rw [omega_comm] at h_phi
            rw [h_phi, mul_zero]⟩
        invFun := fun y =>
          ⟨⟨y.val, (Submodule.mem_inf.mp y.property).1⟩, by
            have h_ortho : y.val ∈
                LinearMap.BilinForm.orthogonal omegaBilin
                  (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) :=
              (Submodule.mem_inf.mp y.property).2
            have hQ_mem : Q ∈ Submodule.span (ZMod 2)
                ({Q} : Set (FTQCLib.Pauli n)) :=
              Submodule.subset_span (by simp)
            have h := h_ortho Q hQ_mem
            change omega Q y.val = 0 at h
            rw [omega_comm] at h
            change φ ⟨y.val, _⟩ = 0
            change omega y.val Q = 0
            exact h⟩
        left_inv := fun x => by rfl
        right_inv := fun y => by rfl
        map_add' := fun x y => by rfl
        map_smul' := fun c x => by rfl }
    exact e.finrank_eq
  rw [h_ker_eq] at h_rk_nul
  omega

/-- Pauli conditioning preserves the Lagrangian condition: if `S` is a
Lagrangian stabilizer subspace (full-rank, `finrank S = n`), then
`pauliCondition S Q` is again full-rank.

When `Q ∈ S` the subspace is unchanged. When `Q ∉ S`, the result is
`(S ⊓ Q^⊥) ⊔ ⟨Q⟩`, where `S ⊓ Q^⊥` has dimension `n − 1` (codim 1 in `S`,
the kernel of `s ↦ ω(s, Q)`) and `⟨Q⟩` adds back one dimension (since
`Q ∈ Q^⊥` but `Q ∉ S ⊓ Q^⊥`). -/
theorem pauliCondition_finrank
    {S : Submodule (ZMod 2) (FTQCLib.Pauli n)} (hS : IsStabilizer S)
    (hRank : finrank (ZMod 2) S = n) (Q : FTQCLib.Pauli n) :
    finrank (ZMod 2) (pauliCondition S Q) = n := by
  classical
  by_cases hQS : Q ∈ S
  · rw [pauliCondition_of_mem hQS]; exact hRank
  · rw [pauliCondition_of_not_mem hQS]
    obtain ⟨M, hM_S, hM_anti⟩ :=
      exists_anticommuting_of_not_mem_full hS hRank hQS
    have hM_ne_zero : M ≠ 0 := by
      intro h
      rw [h, omega_zero_left] at hM_anti
      exact zero_ne_one hM_anti
    have hQ_ne_zero : Q ≠ 0 := by
      intro h
      rw [h, omega_zero_right] at hM_anti
      exact zero_ne_one hM_anti
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
      · exfalso
        have hRank0 : finrank (ZMod 2) S = 0 := hRank.trans hn0
        have h_S_bot : S = ⊥ :=
          (Submodule.finrank_eq_zero (R := ZMod 2) (M := FTQCLib.Pauli n)).mp hRank0
        rw [h_S_bot] at hM_S
        have hM_zero : M = 0 := hM_S
        exact hM_ne_zero hM_zero
      · exact hn_pos
    -- Compute finrank using finrank_sup_add_finrank_inf_eq.
    set T : Submodule (ZMod 2) (FTQCLib.Pauli n) :=
      S ⊓ LinearMap.BilinForm.orthogonal omegaBilin
        (Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n))) with hT_def
    set R : Submodule (ZMod 2) (FTQCLib.Pauli n) :=
      Submodule.span (ZMod 2) ({Q} : Set (FTQCLib.Pauli n)) with hR_def
    have h_T_rank : finrank (ZMod 2) T = n - 1 :=
      finrank_inf_orthogonal_singleton_of_not_mem hS hRank hQS
    have h_R_rank : finrank (ZMod 2) R = 1 := by
      rw [hR_def]
      exact finrank_span_singleton hQ_ne_zero
    -- Show T ⊓ R = ⊥, i.e. Q ∉ T (since Q ∉ S).
    have h_inf_bot : T ⊓ R = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxT, hxR⟩ := hx
      have hxS : x ∈ S := (Submodule.mem_inf.mp hxT).1
      rw [hR_def, Submodule.mem_span_singleton] at hxR
      obtain ⟨c, rfl⟩ := hxR
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with h0 | h1
      · rw [h0, zero_smul]
      · rw [h1, one_smul] at hxS
        exact absurd hxS hQS
    -- Apply finrank_sup_add_finrank_inf_eq.
    have h_sup_eq :
        finrank (ZMod 2) ((T ⊔ R : Submodule (ZMod 2) (FTQCLib.Pauli n))) +
          finrank (ZMod 2) ((T ⊓ R : Submodule (ZMod 2) (FTQCLib.Pauli n))) =
        finrank (ZMod 2) T + finrank (ZMod 2) R :=
      Submodule.finrank_sup_add_finrank_inf_eq T R
    rw [h_inf_bot, finrank_bot, add_zero, h_T_rank, h_R_rank] at h_sup_eq
    omega

/-! ## X-type / Z-type / mixed-type classification

A Pauli `Q : Pauli n` decomposes canonically into its X-component
`Q.X` (a function `Fin n → ZMod 2`) and Z-component `Q.Z`. The
classification:

* `IsXType Q` — `Q.Z = 0`. `Q` is a product of single-qubit X operators.
* `IsZType Q` — `Q.X = 0`. `Q` is a product of single-qubit Z operators.
* Mixed-type (Y-type) — `Q.X ≠ 0 ∧ Q.Z ≠ 0`. Both supports non-trivial.

Pauli conditioning specialises into X-type conditioning (Q is X-type)
and Z-type conditioning (Q is Z-type). These are the two natural
conditioning operations corresponding to the X-sector / Z-sector
decomposition of `Pauli n`. Mixed-type conditioning is a separate
case but factors through the Clifford structure via the equivariance
theorem in `FTQCLib/Stabilizer/GottesmanKnill.lean`.
-/

/-- A Pauli `Q : Pauli n` is **X-type** iff its Z-component is zero.
Equivalently, `Q` is a product of single-qubit X operators
`paulix i` on the qubits in the support of `Q.X`. -/
def IsXType (Q : FTQCLib.Pauli n) : Prop := Q.Z = 0

/-- A Pauli `Q : Pauli n` is **Z-type** iff its X-component is zero.
Equivalently, `Q` is a product of single-qubit Z operators
`pauliz i` on the qubits in the support of `Q.Z`. -/
def IsZType (Q : FTQCLib.Pauli n) : Prop := Q.X = 0

/-- A Pauli `Q : Pauli n` is **mixed-type** (also called Y-type) iff
both `Q.X` and `Q.Z` are non-zero. -/
def IsMixedType (Q : FTQCLib.Pauli n) : Prop := Q.X ≠ 0 ∧ Q.Z ≠ 0

/-- Every Pauli decomposes canonically as the sum of an X-type and a
Z-type Pauli: `Q = ⟨Q.X, 0⟩ + ⟨0, Q.Z⟩`. This is the vector-space
decomposition of `Pauli n` into its X-sector and Z-sector. -/
theorem pauli_xz_decomp (Q : FTQCLib.Pauli n) :
    Q = (⟨Q.X, 0⟩ : FTQCLib.Pauli n) + ⟨0, Q.Z⟩ := by
  apply FTQCLib.Pauli.ext
  · simp
  · simp

/-- The standard Y-Pauli on qubit `i` (defined as `paulix i + pauliz i`)
decomposes into its X-part `paulix i` and Z-part `pauliz i`. This is
the vector-space content of the chapter 1 identity `Y = X · Z` modulo
phase. -/
@[simp]
theorem paulix_add_pauliz_X (i : Fin n) :
    (paulix i + pauliz i : FTQCLib.Pauli n).X = Pi.single i 1 := by
  simp [FTQCLib.Pauli.X_add]

@[simp]
theorem paulix_add_pauliz_Z (i : Fin n) :
    (paulix i + pauliz i : FTQCLib.Pauli n).Z = Pi.single i 1 := by
  simp [FTQCLib.Pauli.Z_add]

end FTQCLib.Stabilizer

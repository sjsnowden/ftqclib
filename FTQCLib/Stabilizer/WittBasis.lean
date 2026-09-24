/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Witt
import FTQCLib.Stabilizer.WittSpanPair
import FTQCLib.Stabilizer.WittRestrictNondeg
import FTQCLib.Stabilizer.WittFinCons
import Mathlib.LinearAlgebra.Dimension.Finite

set_option linter.unusedSectionVars false

/-! # Full Witt's theorem: symplectic-basis existence

Combines the three Witt helpers (`WittSpanPair`, `WittRestrictNondeg`,
`WittFinCons`) plus the base helpers in `Witt.lean` into the full
recursive construction. Strong induction on `Module.finrank V` drives
the dimension down by 2 at each step via the hyperbolic-pair /
orthogonal-complement decomposition.

This file proves:

* **`witt_aux`** — strong-induction-friendly form: for every `n`,
  every `n`-dim non-degenerate alternating `F_2`-vector space admits
  a symplectic basis of size `n / 2`. (`n` must be even; the proof
  shows this implicitly by deriving the basis.)
* **`exists_symplecticBasis_of_nondeg_alt`** — the clean
  finite-dim entry point.
* **`exists_symplecticBasis_logicalQuotient`** — specialisation to
  `L(S) = N(S)/S` via `omegaQBilin`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

/-- **Witt (auxiliary form, induct on finrank):** every
finite-dimensional `F_2`-vector space carrying a non-degenerate
alternating bilinear form admits a symplectic basis. Strong-induction
on `n = Module.finrank V`. -/
theorem witt_aux (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2),
      LinearMap.BilinForm.Nondegenerate B → B.IsAlt →
      Module.finrank (ZMod 2) V = n →
      ∃ k : ℕ, ∃ e f : Fin k → V,
        n = 2 * k ∧
        (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
        (∀ i j, B (e i) (e j) = 0) ∧
        (∀ i j, B (f i) (f j) = 0) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ _ B hN hA hn
    rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
    · -- Base case: V is trivial.
      subst hn0
      refine ⟨0, Fin.elim0, Fin.elim0, by ring, ?_, ?_, ?_⟩
      all_goals (intro i; exact i.elim0)
    · -- Inductive case: n > 0.
      have h_fin_pos : 0 < Module.finrank (ZMod 2) V := by rw [hn]; exact hn_pos
      have h_NT : Nontrivial V := Module.finrank_pos_iff.mp h_fin_pos
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      obtain ⟨w, hw⟩ := exists_pair_eq_one B hN hv
      -- W := span {v, w}, finrank W = 2
      set W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) ({v, w} : Set V) with hW_def
      have h_W_finrank : Module.finrank (ZMod 2) W = 2 :=
        finrank_span_pair_of_pair_eq_one B hA hw
      have hv_W : v ∈ W := Submodule.subset_span (by simp)
      have hw_W : w ∈ W := Submodule.subset_span (by simp)
      have h_disj : Disjoint W (LinearMap.BilinForm.orthogonal B W) :=
        disjoint_span_pair_orthogonal B hA hw
      -- W' := B.orthogonal W is non-deg alt, finrank n - 2
      set W' : Submodule (ZMod 2) V := LinearMap.BilinForm.orthogonal B W with hW'_def
      have h_W'_nondeg : (LinearMap.BilinForm.restrict B W').Nondegenerate :=
        nondegenerate_restrict_orthogonal_of_disjoint B hN hA W h_disj
      have h_W'_alt : (LinearMap.BilinForm.restrict B W').IsAlt := fun x => hA x.val
      have h_W'_finrank : Module.finrank (ZMod 2) W' = n - 2 := by
        rw [hW'_def, LinearMap.BilinForm.finrank_orthogonal hN, hn, h_W_finrank]
      have h_n_ge2 : 2 ≤ n := by
        have h_le : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V :=
          Submodule.finrank_le W
        rw [h_W_finrank, hn] at h_le
        exact h_le
      have h_W'_lt : Module.finrank (ZMod 2) W' < n := by
        rw [h_W'_finrank]; omega
      -- Recurse on W'
      obtain ⟨k, e_inner, f_inner, h_eq, h1, h2, h3⟩ :=
        IH (Module.finrank (ZMod 2) W') h_W'_lt
          (LinearMap.BilinForm.restrict B W') h_W'_nondeg h_W'_alt rfl
      -- Lift e_inner, f_inner from ↥W' to V via Submodule.subtype
      let e' : Fin k → V := fun i => (e_inner i).val
      let f' : Fin k → V := fun i => (f_inner i).val
      -- Orthogonality conditions: W' = B.orthogonal W means
      -- ∀ y ∈ W, B y (W'-element) = 0
      have hve : ∀ i, B v (e' i) = 0 := fun i => (e_inner i).property v hv_W
      have hvf : ∀ i, B v (f' i) = 0 := fun i => (f_inner i).property v hv_W
      have hwe : ∀ i, B w (e' i) = 0 := fun i => (e_inner i).property w hw_W
      have hwf : ∀ i, B w (f' i) = 0 := fun i => (f_inner i).property w hw_W
      -- The inner symplectic-basis conditions on (e', f') in V follow
      -- from the restricted-form conditions in ↥W'.
      have hef : ∀ i j, B (e' i) (f' j) = if i = j then 1 else 0 := h1
      have hee : ∀ i j, B (e' i) (e' j) = 0 := h2
      have hff : ∀ i j, B (f' i) (f' j) = 0 := h3
      -- Combine (v, w) with (e_inner, f_inner) via Fin.cons
      obtain ⟨e, f, _he0, _hf0, _hes, _hfs, hef', hee', hff'⟩ :=
        extend_symplecticBasis B hA hw hve hvf hwe hwf hef hee hff
      refine ⟨k + 1, e, f, ?_, hef', hee', hff'⟩
      -- n = 2 * (k + 1): combine h_W'_finrank (= n - 2) with h_eq (= 2k).
      have h_n_minus_2 : n - 2 = 2 * k := h_W'_finrank ▸ h_eq
      omega

/-- **Full Witt's theorem:** for a finite-dimensional `F_2`-vector space
`V` carrying a non-degenerate alternating bilinear form `B`, there
exists a symplectic basis of size `k = Module.finrank V / 2`. -/
theorem exists_symplecticBasis_of_nondeg_alt
    (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hN : LinearMap.BilinForm.Nondegenerate B) (hA : B.IsAlt) :
    ∃ k : ℕ, ∃ e f : Fin k → V,
      Module.finrank (ZMod 2) V = 2 * k ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i j, B (e i) (e j) = 0) ∧
      (∀ i j, B (f i) (f j) = 0) :=
  witt_aux (Module.finrank (ZMod 2) V) B hN hA rfl

/-! ## Specialisation to the logical Pauli group `L(S)` -/

variable {n : ℕ}

/-- The descended symplectic form `omegaQBilin S` is alternating: for any
coset `p` in `L(S)`, `ω_{L(S)}([p], [p]) = 0`. Reduces to `omega p p = 0`
via the quotient. -/
theorem omegaQBilin_isAlt (S : Submodule (ZMod 2) (Pauli n)) :
    (omegaQBilin S).IsAlt := by
  intro p
  induction p using Quotient.inductionOn with
  | _ p_rep =>
    change omega p_rep.val p_rep.val = 0
    exact omega_self _

/-- The descended symplectic form `omegaQBilin S` is non-degenerate as a
`LinearMap.BilinForm`. Wraps `omegaQ_nondegenerate` through the
`omegaQBilin` packaging. -/
theorem omegaQBilin_nondegenerate (S : Submodule (ZMod 2) (Pauli n)) :
    LinearMap.BilinForm.Nondegenerate (omegaQBilin S) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · -- left-separating
    induction x using Quotient.inductionOn with
    | _ x_rep =>
      apply omegaQ_nondegenerate
      intro y
      induction y using Quotient.inductionOn with
      | _ y_rep =>
        have := hx (Submodule.Quotient.mk y_rep)
        exact this
  · -- right-separating: use IsAlt ⇒ IsRefl, then reduce to left
    induction x using Quotient.inductionOn with
    | _ x_rep =>
      apply omegaQ_nondegenerate
      intro y
      induction y using Quotient.inductionOn with
      | _ y_rep =>
        have h_alt := omegaQBilin_isAlt S
        have h_refl := h_alt.isRefl
        have := hx (Submodule.Quotient.mk y_rep)
        change omega y_rep.val x_rep.val = 0 at this
        rw [omega_comm] at this
        exact this

/-- **Full Witt on the logical Pauli group:** for any stabilizer
subspace `S ⊆ Pauli n`, there exists a symplectic basis of
`L(S) = N(S)/S`. The size of the basis is `k`, with
`Module.finrank L(S) = 2k`. -/
theorem exists_symplecticBasis_logicalQuotient
    (S : Submodule (ZMod 2) (Pauli n)) :
    ∃ k : ℕ, ∃ e f : Fin k → logicalQuotient S,
      Module.finrank (ZMod 2) (logicalQuotient S) = 2 * k ∧
      (∀ i j, omegaQBilin S (e i) (f j) = if i = j then 1 else 0) ∧
      (∀ i j, omegaQBilin S (e i) (e j) = 0) ∧
      (∀ i j, omegaQBilin S (f i) (f j) = 0) :=
  exists_symplecticBasis_of_nondeg_alt _ (omegaQBilin S)
    (omegaQBilin_nondegenerate S) (omegaQBilin_isAlt S)

end FTQCLib.Stabilizer

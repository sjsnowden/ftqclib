/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Stabilizer.Logical

set_option linter.unusedSectionVars false

/-! # Pauli errors, syndromes, and distance

An \emph{error} affecting a stabilizer code is a Pauli operator applied
to a codeword. In the modulo-phase picture, an error is simply an
element of `Pauli n`; the algebraic structure of the stabilizer code
sorts errors into

* \emph{syndrome classes}: errors that anticommute with the same set of
  stabilizer generators, equivalently, cosets of `N(S)` in `Pauli n`;
* \emph{logical equivalence classes}: errors that act identically on
  the codespace, equivalently, cosets of `S` in `N(S)` — the elements
  of the logical Pauli group `N(S)/S`.

This file defines:

* **E1 (weight)** `weight` — the number of qubits on which an error
  acts non-trivially.
* **E2 (syndrome)** `syndrome` — a linear functional on `S` recording
  which stabilizer generators anticommute with the error.
* **E3 (syndrome equality)** `syndrome_eq_iff` — two errors have the
  same syndrome iff they differ by an element of `N(S)`.
* **E4 (distance)** `distance` — the minimum weight of a non-trivial
  logical operator, i.e., a non-trivial element of `N(S) / S`.

The probabilistic / noise-model picture (random Pauli channels, decoder
analysis) is intentionally out of scope; this file treats a single
error algebraically.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli

variable {n : ℕ}

/-- The \emph{weight} of a Pauli operator: the number of qubits on
which it acts non-trivially, i.e., where either the `X`- or
`Z`-coordinate is non-zero. -/
def weight (p : Pauli n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => p.X i ≠ 0 ∨ p.Z i ≠ 0)).card

@[simp]
theorem weight_zero : weight (0 : Pauli n) = 0 := by
  simp [weight]

theorem weight_le_n (p : Pauli n) : weight p ≤ n := by
  rw [weight]
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The weight of a pure-`X` Pauli is the Hamming weight of its
`X`-coordinate (number of non-zero positions). -/
theorem weight_of_Z_zero {p : Pauli n} (h : p.Z = 0) :
    weight p = (Finset.univ.filter (fun i : Fin n => p.X i ≠ 0)).card := by
  rw [weight]
  congr 1
  ext i
  simp [h]

/-- The weight of a pure-`Z` Pauli is the Hamming weight of its
`Z`-coordinate. -/
theorem weight_of_X_zero {p : Pauli n} (h : p.X = 0) :
    weight p = (Finset.univ.filter (fun i : Fin n => p.Z i ≠ 0)).card := by
  rw [weight]
  congr 1
  ext i
  simp [h]

/-- The \emph{syndrome} of a Pauli operator `e` with respect to a
stabilizer subspace `S`: the linear functional on `S` whose value at
`s ∈ S` is `ω(e, s)`. Anticommutation with a stabilizer generator
contributes `1`; commutation contributes `0`. -/
def syndrome (S : Submodule (ZMod 2) (Pauli n)) (e : Pauli n) :
    S →ₗ[ZMod 2] ZMod 2 where
  toFun s := omega e s.val
  map_add' s t := by
    simp only [Submodule.coe_add, omega_add_right]
  map_smul' c s := by
    simp only [SetLike.val_smul, omega_smul_right, RingHom.id_apply,
      smul_eq_mul]

@[simp]
theorem syndrome_apply (S : Submodule (ZMod 2) (Pauli n))
    (e : Pauli n) (s : S) :
    syndrome S e s = omega e s.val := rfl

/-- In characteristic 2, negation is the identity on `Pauli n`. -/
theorem neg_eq_self (p : Pauli n) : -p = p := by
  ext i
  · change -p.X i = p.X i
    exact CharTwo.neg_eq _
  · change -p.Z i = p.Z i
    exact CharTwo.neg_eq _

/-- Bilinearity of `ω` in the first argument across subtraction. In
characteristic 2 this collapses to addition; the subtraction form is
the one referenced from `syndrome_eq_iff` below. -/
theorem omega_sub_left (p₁ p₂ q : Pauli n) :
    omega (p₁ - p₂) q = omega p₁ q - omega p₂ q := by
  rw [sub_eq_add_neg, neg_eq_self, omega_add_left,
    show omega p₁ q - omega p₂ q = omega p₁ q + omega p₂ q from by
      rw [sub_eq_add_neg, CharTwo.neg_eq]]

/-- **E3 (syndrome equality):** two errors have the same syndrome iff
they differ by an element of the normalizer `N(S)`. -/
theorem syndrome_eq_iff {S : Submodule (ZMod 2) (Pauli n)} (e e' : Pauli n) :
    syndrome S e = syndrome S e' ↔ e - e' ∈ normalizer S := by
  refine ⟨fun h => fun q hq => ?_, fun h => LinearMap.ext fun s => ?_⟩
  · have heq := LinearMap.congr_fun h ⟨q, hq⟩
    simp only [syndrome_apply] at heq
    rw [omega_sub_left, heq, sub_self]
  · simp only [syndrome_apply]
    have h_omega : omega (e - e') s.val = 0 := h s.val s.property
    rw [omega_sub_left] at h_omega
    exact sub_eq_zero.mp h_omega

/-- Errors that differ by a stabilizer have the same syndrome (the
converse — syndrome equality implies differ-by-stabilizer — is FALSE in
general; errors can differ by a non-stabilizer normalizer element and
still produce the same syndrome). -/
theorem syndrome_eq_of_sub_mem {S : Submodule (ZMod 2) (Pauli n)}
    (h : IsStabilizer S) {e e' : Pauli n} (hsub : e - e' ∈ S) :
    syndrome S e = syndrome S e' :=
  (syndrome_eq_iff e e').mpr (subset_normalizer h hsub)

/-- The \emph{distance} of a stabilizer code: the minimum weight of a
non-trivial logical operator. Returned as `ℕ∞` so that codes with no
non-trivial logical operators (`N(S) = S`) get distance `⊤`, and the
expected CSS formula `d = \min(d_X, d_Z)` holds without convention
caveats in the degenerate cases. -/
noncomputable def distance (S : Submodule (ZMod 2) (Pauli n)) : ℕ∞ :=
  ⨅ (e : Pauli n) (_ : e ∈ normalizer S) (_ : e ∉ S), (weight e : ℕ∞)

/-- The distance is bounded by the weight of any specific non-trivial
logical operator. -/
theorem distance_le_weight {S : Submodule (ZMod 2) (Pauli n)} {e : Pauli n}
    (hNS : e ∈ normalizer S) (hS : e ∉ S) :
    distance S ≤ (weight e : ℕ∞) := by
  unfold distance
  exact iInf_le_of_le e (iInf_le_of_le hNS (iInf_le _ hS))

/-- Sub-additivity of weight: `weight(e₁ − e₂) ≤ weight e₁ + weight e₂`.
In characteristic 2 this is the same as `weight(e₁ + e₂) ≤ ...`. -/
theorem weight_sub_le (e1 e2 : Pauli n) :
    weight (e1 - e2) ≤ weight e1 + weight e2 := by
  have h_eq : e1 - e2 = e1 + e2 := by rw [sub_eq_add_neg, neg_eq_self]
  rw [h_eq]
  unfold weight
  apply le_trans _ (Finset.card_union_le _ _)
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hi with hX | hZ
  · rw [X_add, Pi.add_apply] at hX
    by_cases hX1 : e1.X i = 0
    · right; left
      intro hX2
      apply hX
      rw [hX1, hX2]; ring
    · left; left; exact hX1
  · rw [Z_add, Pi.add_apply] at hZ
    by_cases hZ1 : e1.Z i = 0
    · right; right
      intro hZ2
      apply hZ
      rw [hZ1, hZ2]; ring
    · left; right; exact hZ1

/-! ## Error detection and correction

The two classical statements:

* A code of distance `d` \emph{detects} every error of weight `< d`: such
  an error is either a stabilizer (acts trivially on the codespace) or
  it gives a non-zero syndrome (anticommutes with some stabilizer
  generator), so the decoder can spot it.
* A code of distance `d` \emph{corrects} every set of errors of weight
  `≤ t` whenever `2t + 1 ≤ d`: any two errors of weight at most `t`
  with the same syndrome differ by a stabilizer (act identically on the
  codespace), so the decoder's choice is harmless.
-/

/-- **Detection (general):** a stabilizer code with distance `d` detects
any error of weight `< d` — meaning the error is either a stabilizer
(acts trivially) or it anticommutes with some stabilizer (non-zero
syndrome).

The check that detects the error is whichever stabilizer generator it
anticommutes with; the syndrome class of the error pins down the
correct decoding up to logical-equivalence (Proposition
`syndrome_eq_iff`). -/
theorem detectable_of_weight_lt {S : Submodule (ZMod 2) (Pauli n)}
    {e : Pauli n} (h : (weight e : ℕ∞) < distance S) :
    e ∈ S ∨ e ∉ normalizer S := by
  rw [or_iff_not_imp_left]
  intro hS hN
  exact absurd (distance_le_weight hN hS) (not_le.mpr h)

/-- **Correction (general):** a stabilizer code with distance `d`
corrects any pair of errors of weight `≤ t` whenever `2 t < d`: such
errors with the same syndrome differ by a stabilizer, so the decoder's
correction-up-to-stabilizer is well-defined.

In the canonical "correct up to `⌊(d-1)/2⌋` errors" phrasing,
the hypothesis `2 t < d` is the standard sphere-packing condition
relating distance to correction radius. -/
theorem correctable_of_weights_le {S : Submodule (ZMod 2) (Pauli n)}
    {e1 e2 : Pauli n} {t : ℕ}
    (ht : (2 * t : ℕ∞) < distance S)
    (h1 : weight e1 ≤ t) (h2 : weight e2 ≤ t)
    (h_syn : syndrome S e1 = syndrome S e2) :
    e1 - e2 ∈ S := by
  have h_in_N : e1 - e2 ∈ normalizer S := (syndrome_eq_iff e1 e2).mp h_syn
  by_contra h_not_in_S
  have h_dist_le : distance S ≤ (weight (e1 - e2) : ℕ∞) :=
    distance_le_weight h_in_N h_not_in_S
  have h_wt : weight (e1 - e2) ≤ 2 * t := by
    have h_sub := weight_sub_le e1 e2
    omega
  have h_wt_cast : (weight (e1 - e2) : ℕ∞) ≤ (2 * t : ℕ∞) := by
    exact_mod_cast h_wt
  exact absurd (le_trans h_dist_le h_wt_cast) (not_le.mpr ht)

end FTQCLib.Stabilizer

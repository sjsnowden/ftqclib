/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.MacWilliams
import ECCLib.WeightEnumerator
import ECCLib.Distance
import ECCLib.ReedSolomon
import ECCLib.Decoding
import ECCLib.Circuit
import ECCLib.GateDecoder
import ECCLib.WitnessOperators

set_option linter.unusedSectionVars false

/-!
# Computational witnesses for the coding theory

The fully computed example: the **repetition code** `C = span{(1,1,1)} ≤ 𝔽₃³`. Everything is made
explicit — membership, the dual, the cardinalities, both weight enumerators in closed form, and the
MacWilliams identity verified numerically between them. Where a number is checked twice, it is
checked by an *independent* route (direct computation) and through the general theorem:

- `dualCode C` *is* the sum-zero code (both inclusions elementary through the membership
  characterizations); `|C| = 3`, `|C^⊥| = 9`, product `27 = q^n`;
- `W_C(z) = 1 + 2z³` and `W_{C^⊥}(z) = 1 + 6z² + 2z³`, by collapsing the full-space
  indicator sums onto the explicit member sets (weights counted by `decide`);
- MacWilliams at the example: `3·(1+6z²+2z³) = (1+2z)³ + 2(1−z)³` (both sides
  `3+18z²+6z³`), proved twice — *independently* from the closed forms above plus `ring`, and
  through the general theorem `macwilliams` with its sum collapsed over the code;
- the Krawtchouk values at `q = 3`: `1+2z` at `s = 0` and `1−z` at `s = 1`, by three-term
  expansion (independent) and by the general theorem `krawtchouk_sum`;
- a concrete monomial-orbit instance over `𝔽₃²`, by `decide`;
- the homogeneous enumerators in closed form: `W_C(X,Y) = X³ + 2Y³` and
  `W_{C^⊥}(X,Y) = X³ + 6XY² + 2Y³`;
- the homogeneous MacWilliams at the example:
  `3·(X³+6XY²+2Y³) = (X+2Y)³ + 2(X−Y)³`, proved independently (closed forms + `ring`) and
  through the general theorem `homMacwilliams`;
- the weight-distribution numbers: `A(C) = (1,0,0,2)` and `A(C^⊥) = (1,0,6,2)`, by
  explicit filter collapse (independent) and through the general theorems
  `weightDist_zero`/`weightPoly_coeff`;
- the minimum distances `d(C) = 3` and `d(C^⊥) = 2` (via `exists_minDist` + the
  membership characterizations), and **Singleton tightness**: `3 + 1 = 3 + 1` and `2 + 2 = 3 + 1`
  — the repetition code and its dual are both MDS, so the `singleton_bound` is attained
  with equality at both example codes;
- the `[3, 2]` Reed–Solomon code over `𝔽₅` at the points `0, 1, 2`: `d + 2 = 4` by the
  MDS theorem `minDist_rsCode`, and the evaluation of `X` is the explicit weight-2 codeword
  `(0, 1, 2)` attaining it;
- a **computable** minimum-distance decoder `dec₃` for the repetition code (the
  majority-style if-chain), proved `IsMDDecoder` by the ∀-hoisted `decide`; the
  correction instances `Corrects dec₃ C₃ 1` (`2·1 < d = 3`) and the `⌊(d−1)/2⌋` corollary; a
  concrete corrected transmission — send `(1,1,1)`, corrupt one coordinate, decode it back —
  and the sharpness row (two errors mis-decode, correctly);
- a **computable syndrome decoder** for the same code: the difference syndrome map
  `H₃` with `ker H₃ = C₃`, the syndrome-algebraic coset-leader table `leader₃` (weight-`≤1`
  leaders read off the syndrome shape; two weight-2 cosets), `IsCosetLeaderMap` by `decide`,
  MD-ness and one-error correction inherited from the general `synDecoder_isMD`; the same
  transmission corrected through the syndrome route; and the tie-break divergence row — the two
  witness decoders disagree on the maximally ambiguous word `(0,1,2)`, both within the MD spec;
- the **binary** repetition code `C₂ ≤ 𝔽₂³` (the characteristic-2 instantiation): its
  syndrome map `H₂` with `ker H₂ = C₂`, `d = 3`, MDS; and **the syndrome map realized in gates** —
  a two-XOR netlist checked against the field-level map by kernel evaluation, the same netlist as
  the general row compiler `dotC` emits it (correct by the general theorem, not by evaluation),
  and the two agreeing semantically while the compiled form spends 6 gates where 2 suffice.

The dual-code convention (`pairing` orientation) and the weight bookkeeping (`n − wt` vs `wt`) are
exactly what these numbers pin down.
-/

namespace ECCLib.Witness

open ECCLib ECCLib.Heisenberg ECCLib.Coding

/-- Compact vector literals in `𝔽₃³`. -/
def v (a b c : ZMod 3) : Fin 3 → ZMod 3 := fun i => if i = 0 then a else if i = 1 then b else c

/-- The repetition code `C = span{(1,1,1)}`. -/
def C₃ : Submodule (ZMod 3) (Fin 3 → ZMod 3) := Submodule.span (ZMod 3) {v 1 1 1}

/-! ## Membership characterizations -/

/-- `x ∈ C` iff `x` is one of the three explicit codewords. -/
theorem mem_C₃ (x : Fin 3 → ZMod 3) :
    x ∈ C₃ ↔ x = v 0 0 0 ∨ x = v 1 1 1 ∨ x = v 2 2 2 := by
  rw [C₃, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases (by decide : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2) a with rfl | rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (Or.inl (by decide))
    · exact Or.inr (Or.inr (by decide))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩

/-- **The dual identification**: `y ∈ C^⊥` iff `y₀ + y₁ + y₂ = 0` — the dual of the
repetition code is the sum-zero (parity-check) code. -/
theorem mem_dual_C₃ (y : Fin 3 → ZMod 3) :
    y ∈ dualCode C₃ ↔ y 0 + y 1 + y 2 = 0 := by
  rw [mem_dualCode]
  constructor
  · intro h
    have hr := h (v 1 1 1) ((mem_C₃ _).mpr (Or.inr (Or.inl rfl)))
    unfold pairing at hr
    rw [Fin.sum_univ_three] at hr
    simpa [v] using hr
  · intro h x hx
    rcases (mem_C₃ x).mp hx with rfl | rfl | rfl
    · unfold pairing
      rw [Fin.sum_univ_three]
      simp [v]
    · unfold pairing
      rw [Fin.sum_univ_three]
      simpa [v] using h
    · unfold pairing
      rw [Fin.sum_univ_three]
      simp only [v]
      norm_num
      linear_combination 2 * h

/-! ## The cardinalities -/

theorem card_C₃ : Nat.card C₃ = 3 := by
  classical
  have h1 : Module.finrank (ZMod 3) C₃ = 1 :=
    finrank_span_singleton (by decide : v 1 1 1 ≠ 0)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3) (V := ↥C₃), h1,
    ZMod.card, pow_one]

/-- `|C^⊥| = 9`, from the size relation `|C^⊥|·|C| = 27`. -/
theorem card_dual_C₃ : Nat.card (dualCode C₃) = 9 := by
  have h := card_dualCode_mul_card C₃
  rw [card_C₃, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
  omega

/-- **The size relation, concretely**: `9 · 3 = 27 = q^n`. -/
example : Nat.card (dualCode C₃) * Nat.card C₃ = 27 := by
  rw [card_C₃, card_dual_C₃]

/-! ## The weight enumerators in closed form -/

/-- The generic collapse: the full-space indicator sum of a code restricts to any Finset that
enumerates exactly the code's members. -/
theorem weightEnum_collapse (C : Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (S : Finset (Fin 3 → ZMod 3)) (hS : ∀ x, x ∈ S ↔ x ∈ C) (z : ℂ) :
    weightEnum C z = ∑ x ∈ S, z ^ hammingNorm x := by
  unfold weightEnum
  rw [← Finset.sum_subset (Finset.subset_univ S)
    (fun x _ hx => by
      unfold indicator
      rw [if_neg (fun hc => hx ((hS x).mpr hc)), zero_mul])]
  refine Finset.sum_congr rfl fun x hx => ?_
  unfold indicator
  rw [if_pos ((hS x).mp hx), one_mul]

/-- `W_C(z) = 1 + 2z³`. -/
theorem weightEnum_C₃ (z : ℂ) : weightEnum C₃ z = 1 + 2 * z ^ 3 := by
  rw [weightEnum_collapse C₃ {v 0 0 0, v 1 1 1, v 2 2 2}
    (fun x => by rw [mem_C₃]; constructor
                 · intro h; rcases Finset.mem_insert.mp h with h | h
                   · exact Or.inl h
                   · rcases Finset.mem_insert.mp h with h | h
                     · exact Or.inr (Or.inl h)
                     · exact Or.inr (Or.inr (Finset.mem_singleton.mp h))
                 · rintro (rfl | rfl | rfl)
                   · exact Finset.mem_insert_self _ _
                   · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                   · exact Finset.mem_insert_of_mem
                       (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show hammingNorm (v 0 0 0) = 0 from by decide, show hammingNorm (v 1 1 1) = 3 from by decide,
    show hammingNorm (v 2 2 2) = 3 from by decide]
  ring

/-- The nine members of the sum-zero code, as an explicit Finset. -/
def S₉ : Finset (Fin 3 → ZMod 3) :=
  {v 0 0 0, v 1 1 1, v 2 2 2, v 0 1 2, v 0 2 1, v 1 0 2, v 2 0 1, v 1 2 0, v 2 1 0}

/-- `W_{C^⊥}(z) = 1 + 6z² + 2z³` — one word of weight 0, six of weight 2, two of
weight 3. -/
theorem weightEnum_dual_C₃ (z : ℂ) : weightEnum (dualCode C₃) z = 1 + 6 * z ^ 2 + 2 * z ^ 3 := by
  have hset : ∀ x : Fin 3 → ZMod 3, x ∈ S₉ ↔ x 0 + x 1 + x 2 = 0 := by decide
  rw [weightEnum_collapse (dualCode C₃) S₉
    (fun x => (hset x).trans (mem_dual_C₃ x).symm)]
  unfold S₉
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show hammingNorm (v 0 0 0) = 0 from by decide, show hammingNorm (v 1 1 1) = 3 from by decide,
    show hammingNorm (v 2 2 2) = 3 from by decide, show hammingNorm (v 0 1 2) = 2 from by decide,
    show hammingNorm (v 0 2 1) = 2 from by decide, show hammingNorm (v 1 0 2) = 2 from by decide,
    show hammingNorm (v 2 0 1) = 2 from by decide, show hammingNorm (v 1 2 0) = 2 from by decide,
    show hammingNorm (v 2 1 0) = 2 from by decide]
  ring

/-! ## MacWilliams at the example -/

theorem hψp₃ : ψ₃.IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root 3
    (ECCLib.GaussSign.stdRoot_isPrimitiveRoot (by norm_num))

theorem hψ₃_ne : ψ₃ ≠ 1 := ECCLib.ne_one_of_isPrimitive hψp₃

/-- **Route A (independent)**: both sides in closed form from the cardinalities and enumerators,
equality by `ring` —
`3·(1+6z²+2z³) = (1+2z)³ + 2(1−z)³ = 3 + 18z² + 6z³`. Never invokes `macwilliams`. -/
theorem witness_macwilliams_independent (z : ℂ) :
    (Nat.card C₃ : ℂ) * weightEnum (dualCode C₃) z
      = (1 + 2 * z) ^ 3 + 2 * (1 - z) ^ 3 := by
  rw [card_C₃, weightEnum_dual_C₃]
  push_cast
  ring

/-- **Route B (via the general theorem)**: the `macwilliams` identity at `C`, its code-side sum
collapsed over the three codewords. Routes A and B prove the same statement. -/
theorem witness_macwilliams_general (z : ℂ) :
    (Nat.card C₃ : ℂ) * weightEnum (dualCode C₃) z
      = (1 + 2 * z) ^ 3 + 2 * (1 - z) ^ 3 := by
  rw [macwilliams C₃ z]
  rw [← Finset.sum_subset (Finset.subset_univ ({v 0 0 0, v 1 1 1, v 2 2 2} :
      Finset (Fin 3 → ZMod 3)))
    (fun x _ hx => by
      unfold indicator
      rw [if_neg (fun hc => hx ?_), zero_mul]
      rcases (mem_C₃ x).mp hc with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))]
  rw [Finset.sum_congr rfl (fun x hx => by
    unfold indicator
    rw [if_pos ?_, one_mul]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (mem_C₃ _).mpr (Or.inl rfl)
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (mem_C₃ _).mpr (Or.inr (Or.inl rfl))
      · rw [Finset.mem_singleton.mp hx]
        exact (mem_C₃ _).mpr (Or.inr (Or.inr rfl)))]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show hammingNorm (v 0 0 0) = 0 from by decide, show hammingNorm (v 1 1 1) = 3 from by decide,
    show hammingNorm (v 2 2 2) = 3 from by decide]
  rw [ZMod.card, show Fintype.card (Fin 3) = 3 from rfl]
  push_cast
  ring

/-! ## The Krawtchouk values at `q = 3` -/

/-- **Route A (independent)**: `Σ_t z^{[t≠0]}ψ(t·0) = 1 + 2z`, by three-term expansion. -/
theorem witness_krawtchouk_zero_independent (z : ℂ) :
    ∑ t : ZMod 3, (if t = 0 then 1 else z) * ψ₃ (t * 0) = 1 + 2 * z := by
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_pos rfl, if_neg (by decide : ¬(1 : ZMod 3) = 0), if_neg (by decide : ¬(2 : ZMod 3) = 0)]
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
  ring

/-- **Route A′ (independent)**: at `s = 1` the sum is `1 − z` — the cancellation is
`ω + ω² = −1`. -/
theorem witness_krawtchouk_one_independent (z : ℂ) :
    ∑ t : ZMod 3, (if t = 0 then 1 else z) * ψ₃ (t * 1) = 1 - z := by
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show ((0 : ZMod 3) * 1) = 0 from by decide, show ((1 : ZMod 3) * 1) = 1 from by decide,
    show ((2 : ZMod 3) * 1) = 2 from by decide]
  rw [AddChar.map_zero_eq_one, ψ₃_apply 1, ψ₃_apply 2, show (1 : ZMod 3).val = 1 from rfl,
    show (2 : ZMod 3).val = 2 from rfl, pow_one]
  rw [if_pos rfl, if_neg (by decide : ¬(1 : ZMod 3) = 0), if_neg (by decide : ¬(2 : ZMod 3) = 0)]
  linear_combination z * omega_cubic

/-- **Route B (via the general theorem)**: `krawtchouk_sum` at `s = 0` and `s = 1` gives the same
two values. -/
example (z : ℂ) :
    (∑ t : ZMod 3, (if t = 0 then 1 else z) * ψ₃ (t * 0) = 1 + 2 * z)
      ∧ (∑ t : ZMod 3, (if t = 0 then 1 else z) * ψ₃ (t * 1) = 1 - z) := by
  constructor
  · have h := krawtchouk_sum hψ₃_ne z (0 : ZMod 3)
    rw [if_pos rfl, ZMod.card] at h
    rw [h]
    push_cast
    ring
  · have h := krawtchouk_sum hψ₃_ne z (1 : ZMod 3)
    rw [if_neg (by decide)] at h
    exact h

/-! ## A concrete monomial orbit -/

/-- Over `𝔽₃²`, the weight-1 vectors `(1,0)` and `(0,2)` lie on one monomial orbit — a
concrete instance of the shells-are-orbits content, found by kernel computation. -/
example : ∃ (σ : Equiv.Perm (Fin 2)) (d : Fin 2 → ZMod 3),
    (∀ i, d i ≠ 0) ∧
      (fun i => if i = 0 then (0 : ZMod 3) else 2)
        = fun i => d i * (fun j => if j = 0 then (1 : ZMod 3) else 0) (σ i) := by
  refine ⟨Equiv.swap 0 1, fun i => if i = 0 then 1 else 2, by decide, ?_⟩
  funext i
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
  · rfl
  · rfl

/-! ## The homogeneous enumerators in closed form -/

/-- The three members of `C₃`, as an explicit Finset (companion to `S₉`). -/
def S₃ : Finset (Fin 3 → ZMod 3) := {v 0 0 0, v 1 1 1, v 2 2 2}

theorem mem_S₃ : ∀ x, x ∈ S₃ ↔ x ∈ C₃ := fun x => by
  have hset : ∀ y : Fin 3 → ZMod 3,
      y ∈ S₃ ↔ (y = v 0 0 0 ∨ y = v 1 1 1 ∨ y = v 2 2 2) := by decide
  exact (hset x).trans (mem_C₃ x).symm

theorem mem_S₉_dual : ∀ x, x ∈ S₉ ↔ x ∈ dualCode C₃ := fun x => by
  have hset : ∀ y : Fin 3 → ZMod 3, y ∈ S₉ ↔ y 0 + y 1 + y 2 = 0 := by decide
  exact (hset x).trans (mem_dual_C₃ x).symm

/-- The generic collapse for the homogeneous enumerator: the full-space indicator sum restricts to
any Finset that enumerates exactly the code's members (the bivariate companion to
`weightEnum_collapse`). -/
theorem homWeightEnum_collapse (C : Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (S : Finset (Fin 3 → ZMod 3)) (hS : ∀ x, x ∈ S ↔ x ∈ C) (X Y : ℂ) :
    homWeightEnum C X Y = ∑ x ∈ S, X ^ (3 - hammingNorm x) * Y ^ hammingNorm x := by
  unfold homWeightEnum
  simp only [Fintype.card_fin]
  rw [← Finset.sum_subset (Finset.subset_univ S)
    (fun x _ hx => by
      unfold indicator
      rw [if_neg (fun hc => hx ((hS x).mpr hc)), zero_mul])]
  refine Finset.sum_congr rfl fun x hx => ?_
  unfold indicator
  rw [if_pos ((hS x).mp hx), one_mul]

/-- `W_C(X,Y) = X³ + 2Y³`. -/
theorem homWeightEnum_C₃ (X Y : ℂ) : homWeightEnum C₃ X Y = X ^ 3 + 2 * Y ^ 3 := by
  rw [homWeightEnum_collapse C₃ S₃ mem_S₃]
  unfold S₃
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show hammingNorm (v 0 0 0) = 0 from by decide, show hammingNorm (v 1 1 1) = 3 from by decide,
    show hammingNorm (v 2 2 2) = 3 from by decide]
  rw [show (3 : ℕ) - 0 = 3 from rfl, show (3 : ℕ) - 3 = 0 from rfl]
  ring

/-- `W_{C^⊥}(X,Y) = X³ + 6XY² + 2Y³` — one word of weight 0, six of weight 2, two of
weight 3. -/
theorem homWeightEnum_dual_C₃ (X Y : ℂ) :
    homWeightEnum (dualCode C₃) X Y = X ^ 3 + 6 * X * Y ^ 2 + 2 * Y ^ 3 := by
  rw [homWeightEnum_collapse (dualCode C₃) S₉ mem_S₉_dual]
  unfold S₉
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show hammingNorm (v 0 0 0) = 0 from by decide, show hammingNorm (v 1 1 1) = 3 from by decide,
    show hammingNorm (v 2 2 2) = 3 from by decide, show hammingNorm (v 0 1 2) = 2 from by decide,
    show hammingNorm (v 0 2 1) = 2 from by decide, show hammingNorm (v 1 0 2) = 2 from by decide,
    show hammingNorm (v 2 0 1) = 2 from by decide, show hammingNorm (v 1 2 0) = 2 from by decide,
    show hammingNorm (v 2 1 0) = 2 from by decide]
  rw [show (3 : ℕ) - 0 = 3 from rfl, show (3 : ℕ) - 3 = 0 from rfl,
    show (3 : ℕ) - 2 = 1 from rfl]
  ring

/-! ## The homogeneous MacWilliams at the example -/

/-- **Route A (independent)**: `3·W_{C^⊥}(X,Y) = W_C(X+2Y, X−Y)` with both sides in closed
form from the cardinalities and homogeneous enumerators, equality by `ring` —
`3(X³+6XY²+2Y³) = (X+2Y)³ + 2(X−Y)³`. Never invokes `homMacwilliams`. -/
theorem witness_homMacwilliams_independent (X Y : ℂ) :
    (Nat.card C₃ : ℂ) * homWeightEnum (dualCode C₃) X Y
      = homWeightEnum C₃ (X + 2 * Y) (X - Y) := by
  rw [card_C₃, homWeightEnum_dual_C₃, homWeightEnum_C₃]
  push_cast
  ring

/-- **Route B (via the general theorem)**: the `homMacwilliams` identity at `C₃`, with
`q − 1 = 2`. Routes A and B prove the same statement. -/
theorem witness_homMacwilliams_general (X Y : ℂ) :
    (Nat.card C₃ : ℂ) * homWeightEnum (dualCode C₃) X Y
      = homWeightEnum C₃ (X + 2 * Y) (X - Y) := by
  have h2 : ((Fintype.card (ZMod 3) : ℂ)) - 1 = 2 := by
    rw [ZMod.card]
    norm_num
  rw [homMacwilliams C₃ X Y, h2]

/-! ## The weight-distribution numbers -/

/-- The generic collapse for the weight distribution: the classical full-space filter restricts to
any Finset that enumerates exactly the code's members. -/
theorem weightDist_collapse (C : Submodule (ZMod 3) (Fin 3 → ZMod 3))
    (S : Finset (Fin 3 → ZMod 3)) (hS : ∀ x, x ∈ S ↔ x ∈ C) (i : ℕ) :
    weightDist C i = (S.filter (fun x => hammingNorm x = i)).card := by
  classical
  unfold weightDist
  refine congrArg Finset.card (Finset.ext fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_left' (hS x).symm

/-- **Route A (via the general theorem)**: `A₀(C) = 1` is `weightDist_zero` at the example. -/
example : weightDist C₃ 0 = 1 := weightDist_zero C₃

/-- **Route B (independent)**: the same `A₀(C) = 1` by explicit filter collapse. -/
theorem witness_weightDist_C₃_zero : weightDist C₃ 0 = 1 := by
  rw [weightDist_collapse C₃ S₃ mem_S₃]
  decide

/-- `A₃(C) = 2`, and the middle weights are empty: `A₁(C) = A₂(C) = 0`. -/
theorem witness_weightDist_C₃ :
    weightDist C₃ 3 = 2 ∧ weightDist C₃ 1 = 0 ∧ weightDist C₃ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [weightDist_collapse C₃ S₃ mem_S₃]
      decide

/-- The dual's distribution — `A₀ = 1`, `A₂ = 6`, `A₃ = 2`, `A₁ = 0` — the coefficient
list of `1 + 6z² + 2z³` (`weightEnum_dual_C₃`), now as counting data. -/
theorem witness_weightDist_dual_C₃ :
    weightDist (dualCode C₃) 0 = 1 ∧ weightDist (dualCode C₃) 1 = 0
      ∧ weightDist (dualCode C₃) 2 = 6 ∧ weightDist (dualCode C₃) 3 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [weightDist_collapse (dualCode C₃) S₉ mem_S₉_dual]
      decide

/-- **Instance of the general theorem**: the polynomial coefficient is the count —
`[z²] W_{C^⊥} = 6` through `weightPoly_coeff`. -/
example : (weightPoly (dualCode C₃)).coeff 2 = 6 := by
  rw [weightPoly_coeff, witness_weightDist_dual_C₃.2.2.1]
  norm_num

/-! ## Minimum distances and Singleton tightness -/

theorem C₃_ne_bot : C₃ ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨v 1 1 1, (mem_C₃ _).mpr (Or.inr (Or.inl rfl)), by decide⟩

theorem dual_C₃_ne_bot : dualCode C₃ ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨v 0 1 2, (mem_dual_C₃ _).mpr (by decide), by decide⟩

/-- `d(C) = 3` — the distance is attained (`exists_minDist`), and every nonzero codeword
has weight 3. -/
theorem minDist_C₃ : minDist C₃ = 3 := by
  obtain ⟨x, hxC, hx0, hwt⟩ := exists_minDist C₃_ne_bot
  rcases (mem_C₃ x).mp hxC with rfl | rfl | rfl
  · exact absurd (by decide : v 0 0 0 = 0) hx0
  · rw [← hwt]; decide
  · rw [← hwt]; decide

/-- `d(C^⊥) = 2` — attained at the weight-2 codeword `(0,1,2)`; every nonzero sum-zero
word has weight at least 2. -/
theorem minDist_dual_C₃ : minDist (dualCode C₃) = 2 := by
  have hle : minDist (dualCode C₃) ≤ 2 := by
    have h := minDist_le_of_mem ((mem_dual_C₃ (v 0 1 2)).mpr (by decide))
      (by decide : v 0 1 2 ≠ 0)
    rw [show hammingNorm (v 0 1 2) = 2 from by decide] at h
    exact h
  have hge : 2 ≤ minDist (dualCode C₃) := by
    obtain ⟨x, hxC, hx0, hwt⟩ := exists_minDist dual_C₃_ne_bot
    rw [← hwt]
    exact (by decide : ∀ y ∈ S₉, y ≠ 0 → 2 ≤ hammingNorm y) x ((mem_S₉_dual x).mpr hxC) hx0
  omega

theorem finrank_C₃ : Module.finrank (ZMod 3) C₃ = 1 :=
  finrank_span_singleton (by decide : v 1 1 1 ≠ 0)

theorem finrank_dual_C₃ : Module.finrank (ZMod 3) (dualCode C₃) = 2 := by
  have h := finrank_dualCode_add_finrank C₃
  rw [finrank_C₃, Module.finrank_pi, Fintype.card_fin] at h
  omega

/-- **Instance of the general theorem**: the Singleton bound at the example. -/
example : minDist C₃ + Module.finrank (ZMod 3) C₃ ≤ Fintype.card (Fin 3) + 1 :=
  singleton_bound C₃

/-- **Tightness**: the repetition code is MDS — `d + k = n + 1` with equality. -/
example : minDist C₃ + Module.finrank (ZMod 3) C₃ = Fintype.card (Fin 3) + 1 := by
  rw [minDist_C₃, finrank_C₃, Fintype.card_fin]

/-- **Tightness**: the dual is MDS too — `2 + 2 = 3 + 1`. -/
example : minDist (dualCode C₃) + Module.finrank (ZMod 3) (dualCode C₃)
    = Fintype.card (Fin 3) + 1 := by
  rw [minDist_dual_C₃, finrank_dual_C₃, Fintype.card_fin]

/-! ## The Reed–Solomon instance over 𝔽₅ -/

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The evaluation points `0, 1, 2` in `𝔽₅`. -/
def a₅ : Fin 3 → ZMod 5 := fun i => (i : ZMod 5)

theorem a₅_injective : Function.Injective a₅ := by decide

/-- **Instance of the general theorem**: the `[3, 2]` Reed–Solomon code over `𝔽₅` is MDS —
`d + 2 = 3 + 1`, i.e. `d = 2`. -/
example : minDist (rsCode a₅ 2) + 2 = 4 := by
  have h := minDist_rsCode a₅_injective (k := 2) (by norm_num) (by decide)
  rw [Fintype.card_fin] at h
  omega

/-- **The attaining codeword**: the evaluation of `X` at the points is `(0, 1, 2)` — an
explicit weight-2 codeword of the `[3, 2]` code, pinning `d ≤ 2` concretely. -/
example : rsEval a₅ Polynomial.X ∈ rsCode a₅ 2
    ∧ hammingNorm (rsEval a₅ Polynomial.X) = 2 := by
  have heval : rsEval a₅ Polynomial.X = fun i : Fin 3 => (i : ZMod 5) := by
    funext i
    rw [rsEval_apply, Polynomial.eval_X]
    rfl
  constructor
  · refine mem_rsCode.mpr ⟨Polynomial.X, Polynomial.mem_degreeLT.mpr ?_, rfl⟩
    rw [Polynomial.degree_X]
    exact_mod_cast one_lt_two
  · rw [heval]
    decide

/-! ## A computable minimum-distance decoder for the repetition code -/

/-- The majority-style decoder: within distance 1 of a nonzero codeword → that codeword;
otherwise the zero word. **Computable**. -/
def dec₃ : (Fin 3 → ZMod 3) → Option (Fin 3 → ZMod 3) := fun y =>
  some (if hammingDist y (v 1 1 1) ≤ 1 then v 1 1 1
    else if hammingDist y (v 2 2 2) ≤ 1 then v 2 2 2 else v 0 0 0)

/-- `dec₃` is a minimum-distance decoder for `C₃`. -/
theorem dec₃_isMD : IsMDDecoder dec₃ C₃ := by
  have hkey : ∀ y : Fin 3 → ZMod 3, ∀ c' ∈ S₃,
      hammingDist y (if hammingDist y (v 1 1 1) ≤ 1 then v 1 1 1
        else if hammingDist y (v 2 2 2) ≤ 1 then v 2 2 2 else v 0 0 0)
        ≤ hammingDist y c' := by decide
  intro y
  refine ⟨_, rfl, ?_, ?_⟩
  · split_ifs
    · exact (mem_C₃ _).mpr (Or.inr (Or.inl rfl))
    · exact (mem_C₃ _).mpr (Or.inr (Or.inr rfl))
    · exact (mem_C₃ _).mpr (Or.inl rfl)
  · intro c' hc'
    exact hkey y c' ((mem_S₃ c').mpr hc')

/-- **Instance of the general theorem**: `dec₃` corrects one error — `2·1 < d = 3`. -/
theorem dec₃_corrects_one : Corrects dec₃ C₃ 1 :=
  dec₃_isMD.corrects (by rw [minDist_C₃]; omega)

/-- **Instance of the general theorem**: the `⌊(d−1)/2⌋` radius at the example. -/
example : Corrects dec₃ C₃ ((minDist C₃ - 1) / 2) :=
  dec₃_isMD.corrects_half C₃_ne_bot

/-- **A corrected transmission, concretely**: send `(1,1,1)`, corrupt coordinate 0 to
`2`, decode — the sent word returns. -/
example : dec₃ (v 1 1 1 + v 1 0 0) = some (v 1 1 1) := by decide

/-- **The radius is sharp**: corrupt TWO coordinates and the received word `(2,2,1)` is
genuinely closer to `(2,2,2)` than to the sent `(1,1,1)` — the decoder, correctly as an MD
decoder, returns the wrong codeword. `⌊(d−1)/2⌋ = 1` is not an artifact of the proof. -/
example : dec₃ (v 1 1 1 + v 1 1 0) = some (v 2 2 2) := by decide

/-! ## A computable syndrome decoder for the repetition code -/

/-- The syndrome map of the repetition code: consecutive differences. `ker H₃ = C₃`. -/
def H₃ : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 2 → ZMod 3) where
  toFun y := fun j => if j = 0 then y 0 - y 1 else y 1 - y 2
  map_add' y z := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' c y := by
    funext j
    fin_cases j <;> simp <;> ring

theorem ker_H₃ : LinearMap.ker H₃ = C₃ := by
  have hd : ∀ y : Fin 3 → ZMod 3,
      H₃ y = 0 ↔ (y = v 0 0 0 ∨ y = v 1 1 1 ∨ y = v 2 2 2) := by decide
  ext y
  rw [LinearMap.mem_ker]
  exact (hd y).trans (mem_C₃ y).symm

/-- The **computable coset-leader map**, syndrome-algebraic: the weight-`≤1` leaders are
reconstructed directly from the syndrome shape (which difference is zero), and the two
`s₀ = s₁ ≠ 0` cosets take weight-2 leaders. -/
def leader₃ : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3) := fun s =>
  if s 1 = 0 then v (s 0) 0 0
  else if s 0 = 0 then v 0 0 (- s 1)
  else if s 0 = - s 1 then v 0 (s 1) 0
  else v (2 * s 0) (s 0) 0

theorem leader₃_isCosetLeader : IsCosetLeaderMap H₃ leader₃ := by
  unfold IsCosetLeaderMap
  decide

/-- The syndrome decoder for the repetition code — computable end to end. -/
def synDec₃ : (Fin 3 → ZMod 3) → Option (Fin 3 → ZMod 3) := synDecoder H₃ leader₃

/-- The syndrome decoder is a minimum-distance decoder for `C₃` — the general theorem
`synDecoder_isMD` at `ker H₃ = C₃`. -/
theorem synDec₃_isMD : IsMDDecoder synDec₃ C₃ := by
  have h := synDecoder_isMD leader₃_isCosetLeader
  rwa [ker_H₃] at h

/-- **Instance of the general theorem**: the syndrome decoder corrects one error. -/
theorem synDec₃_corrects_one : Corrects synDec₃ C₃ 1 :=
  synDec₃_isMD.corrects (by rw [minDist_C₃]; omega)

/-- **The same transmission, syndrome route**: the corrupted word's syndrome is `(1,0)`,
its coset leader is exactly the error `(1,0,0)`, and subtraction returns the sent word. -/
example : synDec₃ (v 1 1 1 + v 1 0 0) = some (v 1 1 1) := by decide

/-- **MD decoders are not unique**: on the maximally ambiguous word `(0,1,2)` — at
distance 2 from all three codewords — the two witness decoders break the tie differently, both
correctly within the MD specification. -/
example : synDec₃ (v 0 1 2) = some (v 2 2 2) ∧ dec₃ (v 0 1 2) = some (v 0 0 0) := by decide

/-! ## The binary repetition code and its syndrome netlist (the first descent artifact) -/

/-- Compact vector literals in `𝔽₂³`. -/
def w₂ (a b c : ZMod 2) : Fin 3 → ZMod 2 := fun i => if i = 0 then a else if i = 1 then b else c

/-- The **binary** repetition code `{000, 111} ≤ 𝔽₂³` — the characteristic-2 instantiation of the
coding layer, and the code whose syndrome map descends to gates below. -/
def C₂ : Submodule (ZMod 2) (Fin 3 → ZMod 2) := Submodule.span (ZMod 2) {w₂ 1 1 1}

theorem mem_C₂ (x : Fin 3 → ZMod 2) : x ∈ C₂ ↔ x = w₂ 0 0 0 ∨ x = w₂ 1 1 1 := by
  rw [C₂, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  · rintro (rfl | rfl)
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩

theorem C₂_ne_bot : C₂ ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨w₂ 1 1 1, (mem_C₂ _).mpr (Or.inr rfl), by decide⟩

theorem finrank_C₂ : Module.finrank (ZMod 2) C₂ = 1 :=
  finrank_span_singleton (by decide : w₂ 1 1 1 ≠ 0)

/-- `d(C₂) = 3` — the binary repetition code, like its `𝔽₃` sibling, is MDS. -/
theorem minDist_C₂ : minDist C₂ = 3 := by
  obtain ⟨x, hxC, hx0, hwt⟩ := exists_minDist C₂_ne_bot
  rcases (mem_C₂ x).mp hxC with rfl | rfl
  · exact absurd (by decide : w₂ 0 0 0 = 0) hx0
  · rw [← hwt]; decide

example : minDist C₂ + Module.finrank (ZMod 2) C₂ = Fintype.card (Fin 3) + 1 := by
  rw [minDist_C₂, finrank_C₂, Fintype.card_fin]

/-- The binary syndrome map — consecutive sums (in characteristic 2, the differences of `H₃`). -/
def H₂ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun y := fun j => if j = 0 then y 0 + y 1 else y 1 + y 2
  map_add' y z := by
    funext j
    fin_cases j <;> simp <;> ring
  map_smul' c y := by
    funext j
    fin_cases j <;> simp <;> ring

theorem ker_H₂ : LinearMap.ker H₂ = C₂ := by
  have hd : ∀ y : Fin 3 → ZMod 2, H₂ y = 0 ↔ (y = w₂ 0 0 0 ∨ y = w₂ 1 1 1) := by decide
  ext y
  rw [LinearMap.mem_ker]
  exact (hd y).trans (mem_C₂ y).symm

/-- The syndrome netlist, hand-minimal: **two XOR gates**. -/
def synCircuit : Circuit.CircuitVec 3 2 :=
  fun j => if j = 0 then .xor (.wire 0) (.wire 1) else .xor (.wire 1) (.wire 2)

/-- **The descent**: the netlist computes the syndrome map through the bit encoding — the
a field-level object realized in gates, checked by kernel evaluation on all
eight inputs. -/
theorem synCircuit_correct : ∀ y : Fin 3 → ZMod 2,
    Circuit.evalVec synCircuit (fun i => bit (y i)) = fun j => bit (H₂ y j) := by decide

example : Circuit.sizeVec synCircuit = 2 := by decide

/-- The same syndrome map as the **general row compiler** emits it: each syndrome bit is `dotC` of
the corresponding parity-check row. Correctness here is *not* by evaluation — it is the general
theorem `eval_dotC` instantiated, which is how a compiler's output will be certified. -/
def synCompiled : Circuit.CircuitVec 3 2 :=
  fun j => Circuit.dotC (if j = 0 then w₂ 1 1 0 else w₂ 0 1 1)

theorem synCompiled_correct (y : Fin 3 → ZMod 2) :
    Circuit.evalVec synCompiled (fun i => bit (y i)) = fun j => bit (H₂ y j) := by
  funext j
  rw [Circuit.evalVec_apply, synCompiled, Circuit.eval_dotC]
  congr 1
  fin_cases j <;> simp [H₂, w₂, Fin.sum_univ_three]

/-- **The fold's overhead, measured**: the compiled netlist agrees with the hand-minimal
one, but spends **6 gates where 2 suffice** — the uniform fold's `const false` base and its
zero-coefficient masks each cost one XOR. This is the number a constant-folding pass removes, and
it is stated rather than hidden. -/
example : Circuit.sizeVec synCompiled = 6 := by decide

example (y : Fin 3 → ZMod 2) :
    Circuit.evalVec synCompiled (fun i => bit (y i))
      = Circuit.evalVec synCircuit (fun i => bit (y i)) := by
  rw [synCompiled_correct, synCircuit_correct]

/-! ## End-to-end gate-level correction

The field level and the gate level, composed at one concrete code. Field side: `C₂ = ker H₂` with
`minDist = 3`, so a coset-leader syndrome decoder corrects one error (`Decoding.lean`). Gate side:
`synCircuit` computes `H₂` and `Lnet₂` computes the coset-leader map, both through the bit encoding
(`Circuit.lean`). Composing them gives a **netlist** that provably recovers the sent codeword from
any single-coordinate corruption. -/

/-- A coset-leader map for the binary repetition code, as a **syndrome-indexed** table: the four
syndromes of `H₂` get leaders `000`, `001`, `100`, `010`. Its domain is the syndrome module, which
is why it has a small netlist at all. -/
def L₂ : (Fin 2 → ZMod 2) → (Fin 3 → ZMod 2) := fun s =>
  if s 0 = 0 then (if s 1 = 0 then w₂ 0 0 0 else w₂ 0 0 1)
  else (if s 1 = 0 then w₂ 1 0 0 else w₂ 0 1 0)

theorem L₂_isCosetLeader : IsCosetLeaderMap H₂ L₂ := by
  unfold IsCosetLeaderMap
  decide

/-- The coset-leader stage as a netlist: three outputs, each a tabulated boolean function of the
**two syndrome wires** — `Circuit.tabC` at `k = 2`. -/
def Lnet₂ : Circuit.CircuitVec 2 3 :=
  fun i => Circuit.tabC 2 (fun s => bit (L₂ (fun j => unbit (s j)) i))

theorem Lnet₂_correct (s : Fin 2 → ZMod 2) :
    Circuit.evalVec Lnet₂ (fun j => bit (s j)) = fun i => bit (L₂ s i) := by
  funext i
  rw [Circuit.evalVec_apply, Lnet₂, Circuit.eval_tabC]
  simp

/-- **End-to-end correction at the gate level.** For every codeword `c` of the binary repetition
code and every error of Hamming weight at most one, the two-stage netlist
`decoderNet synCircuit Lnet₂`, evaluated on the encoded corrupted word, outputs the encoded sent
codeword. This is a field-level decoder-correctness theorem (`synDecoder_corrects`, via
`minDist_C₂ = 3` and `2·1 < 3`) composed with gate-level semantics preservation. -/
theorem gate_corrects_C₂ (c : Fin 3 → ZMod 2) (hc : c ∈ C₂)
    (e : Fin 3 → ZMod 2) (he : hammingNorm e ≤ 1) :
    Circuit.evalVec (decoderNet synCircuit Lnet₂) (fun i => bit ((c + e) i))
      = fun o => bit (c o) := by
  refine decoderNet_corrects synCircuit_correct Lnet₂_correct L₂_isCosetLeader ?_ c ?_ e he
  · rw [ker_H₂, minDist_C₂]
    omega
  · rwa [ker_H₂]

/-- **The run**: send `(1,1,1)`, corrupt coordinate 0, and the netlist returns the encoded
sent word — the gate-level analogue of the corrected transmission by `dec₃`, evaluated in the
kernel. -/
example : Circuit.evalVec (decoderNet synCircuit Lnet₂)
    (fun i => bit ((w₂ 1 1 1 + w₂ 1 0 0) i)) = fun i => bit (w₂ 1 1 1 i) := by decide

end ECCLib.Witness

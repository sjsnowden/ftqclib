/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ControlledHadamardMinimal

/-!
# The size bound on rows

`ControlledHadamardMinimal.lean` characterises the least height of a function exactly by rows
(`HasRowSums`, `leastHeight_controlledH`), but computes no least height at any input. This module
supplies the arithmetic that decides it from below (`docs/STEPS.md`, T09.3.2; entry 2026-09-30c):
the modulus of a row.

A row of `2 ^ h` characters is a sum of `2 ^ h` complex numbers of modulus one, so it has modulus
at most `2 ^ h`; at height zero a row is one character, so it has modulus exactly one. Hence a
function with rows at height `h` and scale `r` has modulus at most `‖r‖ · 2 ^ h` everywhere (off the
coset it vanishes), and a function with rows at height zero has modulus exactly `‖r‖` on the whole
coset, which holds its support. A function presented by a carrier state and taking two different
nonzero moduli therefore has no rows at height zero, and its least height is at least one.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported.

## Main results

* `norm_le_of_hasRowSums` — rows at height `h` and scale `r` bound the modulus by `‖r‖ · 2 ^ h`.
* `norm_eq_of_hasRowSums_zero` — rows at height zero fix the modulus at `‖r‖` on a coset holding
  the support.
* `one_le_leastHeight_of_norm_ne` — two support words of different moduli force a least height of
  at least one.

## Implementation notes

* The rows of a carrier state at its own height are the topic module's `hasRowSums_amp`. It was
  private there when this module was written, and proved here a second time; it was made public
  after run 5b so that it is proved once (`docs/STEPS.md`, entry 2026-09-30d).
* `one_le_leastHeight_of_norm_ne` assumes a carrier state presenting `f`: `leastHeight f` is `0`
  when none does, and the conclusion would then fail.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The modulus of a row -/

/-- The character has norm one. -/
private theorem norm_charOf (m : ℕ) (z : ZMod (2 ^ m)) : ‖charOf m z‖ = 1 := by
  unfold charOf
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A row of `2 ^ h` characters has norm at most `2 ^ h`. -/
private theorem norm_sum_charOf_le {m h : ℕ} (e : (Fin h → ZMod 2) → ZMod (2 ^ m)) :
    ‖∑ y : Fin h → ZMod 2, charOf m (e y)‖ ≤ 2 ^ h := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_charOf, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  norm_num

/-- A row at height zero is one character, of norm one. -/
private theorem norm_sum_charOf_zero {m : ℕ} (e : (Fin 0 → ZMod 2) → ZMod (2 ^ m)) :
    ‖∑ y : Fin 0 → ZMod 2, charOf m (e y)‖ = 1 := by
  rw [Fintype.sum_unique, norm_charOf]

/-! ## The size bound -/

/-- **The size bound on rows.** A function with rows of `2 ^ h` phases at scale `r` has modulus at
most `‖r‖ · 2 ^ h` at every word: on the coset each value is `r` times a sum of `2 ^ h` numbers of
modulus one, and off it the function vanishes. -/
theorem norm_le_of_hasRowSums {f : (Fin n → ZMod 2) → ℂ} {h : ℕ} {r : ℂ}
    (hrow : HasRowSums f h r) (w : Fin n → ZMod 2) : ‖f w‖ ≤ ‖r‖ * 2 ^ h := by
  obtain ⟨m, x₀, V, hsupp, hrows⟩ := hrow
  by_cases hw : w - x₀ ∈ V
  · obtain ⟨e, he⟩ := hrows w hw
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sum_charOf_le e) (norm_nonneg r)
  · have hzero : f w = 0 := by
      by_contra hne
      exact hw (hsupp w hne)
    rw [hzero, norm_zero]
    positivity

/-- **Rows at height zero have constant modulus.** A function with rows of one phase at scale `r`
has modulus exactly `‖r‖` on the whole of a coset holding its support. -/
theorem norm_eq_of_hasRowSums_zero {f : (Fin n → ZMod 2) → ℂ} {r : ℂ}
    (hrow : HasRowSums f 0 r) :
    ∃ (x₀ : Fin n → ZMod 2) (V : Submodule (ZMod 2) (Fin n → ZMod 2)),
      (∀ w, f w ≠ 0 → w - x₀ ∈ V) ∧ ∀ w, w - x₀ ∈ V → ‖f w‖ = ‖r‖ := by
  obtain ⟨m, x₀, V, hsupp, hrows⟩ := hrow
  refine ⟨x₀, V, hsupp, fun w hw => ?_⟩
  obtain ⟨e, he⟩ := hrows w hw
  rw [he, norm_mul, norm_sum_charOf_zero, mul_one]

/-! ## The least height from below -/

/-- **Two moduli force height one.** If a carrier state presents `f`, and `f` takes two different
nonzero moduli, then no carrier state of height zero presents `f`: its least height is at least
one. -/
theorem one_le_leastHeight_of_norm_ne {f : (Fin n → ZMod 2) → ℂ} {T₀ : KernelSumState n}
    (hT₀ : IsCarrier T₀) (hf : amp T₀ = f) {w₁ w₂ : Fin n → ZMod 2} (hw₁ : f w₁ ≠ 0)
    (hw₂ : f w₂ ≠ 0) (hne : ‖f w₁‖ ≠ ‖f w₂‖) : 1 ≤ leastHeight f := by
  by_contra hlt
  have hzero : leastHeight f = 0 := by omega
  obtain ⟨T, -, hTf, hTh⟩ :=
    Nat.sInf_mem (s := {h : ℕ | ∃ T : KernelSumState n, IsCarrier T ∧ amp T = f ∧ T.h = h})
      ⟨T₀.h, T₀, hT₀, hf, rfl⟩
  have hTh0 : T.h = 0 := hTh.trans hzero
  have hrow := hasRowSums_amp T
  rw [hTf, hTh0] at hrow
  obtain ⟨x₀, V, hsupp, hnorm⟩ := norm_eq_of_hasRowSums_zero hrow
  exact hne ((hnorm w₁ (hsupp w₁ hw₁)).trans (hnorm w₂ (hsupp w₂ hw₂)).symm)

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Inner

/-! # The Kochen–Specker theorem via the Mermin–Peres magic square

State-independent contextuality on two qubits. The nine two-qubit Pauli observables of the
Mermin–Peres square sit in a `3 × 3` grid; each of the six lines (three rows, three columns) is a
commuting triple whose **Hermitian** Pauli operators multiply to `±I`:

```
        X⊗I    I⊗X    X⊗X        (row products  +I, +I, +I)
        I⊗Z    Z⊗I    Z⊗Z
        X⊗Z    Z⊗X    Y⊗Y
       (col)   (col)  (col3 = −I)
```

Five lines give `+I` and the third column gives `−I`. Reading these off the operator algebra
(`pauliHermitian_triple_of_sum_zero`, the only quantum input) reduces Kochen–Specker to a finite
`𝔽₂` impossibility: no assignment of `±1` eigenvalues to the nine observables can respect all six
line products, because the product of all six constraints equals `+1` (every observable occurs in
exactly two lines, so each value is squared) and simultaneously equals the product of the line
signs `(+1)⁵·(−1) = −1`. This is the absence of a global section of the spectral presheaf. Source grounding: Mermin, *PRL* 65, 3373 (1990); Straumann, arXiv:0801.4931.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli FTQCLib.Hilbert Complex

/-! ## The nine observables as symplectic vectors in `Pauli 2` -/

/-- `X⊗I`. -/ def mpO0 : Pauli 2 := ⟨![1, 0], ![0, 0]⟩
/-- `I⊗X`. -/ def mpO1 : Pauli 2 := ⟨![0, 1], ![0, 0]⟩
/-- `X⊗X`. -/ def mpO2 : Pauli 2 := ⟨![1, 1], ![0, 0]⟩
/-- `I⊗Z`. -/ def mpO3 : Pauli 2 := ⟨![0, 0], ![0, 1]⟩
/-- `Z⊗I`. -/ def mpO4 : Pauli 2 := ⟨![0, 0], ![1, 0]⟩
/-- `Z⊗Z`. -/ def mpO5 : Pauli 2 := ⟨![0, 0], ![1, 1]⟩
/-- `X⊗Z`. -/ def mpO6 : Pauli 2 := ⟨![1, 0], ![0, 1]⟩
/-- `Z⊗X`. -/ def mpO7 : Pauli 2 := ⟨![0, 1], ![1, 0]⟩
/-- `Y⊗Y`. -/ def mpO8 : Pauli 2 := ⟨![1, 1], ![1, 1]⟩

/-! ## The six line products at the operator level -/

/-- Row 1: `(X⊗I)(I⊗X)(X⊗X) = +I`. -/
theorem mp_row1 :
    pauliHermitian mpO2 ∘ₗ pauliHermitian mpO1 ∘ₗ pauliHermitian mpO0 = (1 : ℂ) • LinearMap.id := by
  rw [pauliHermitian_triple_of_sum_zero mpO0 mpO1 mpO2
    (by apply Pauli.ext <;> (funext i; fin_cases i <;> decide))]
  congr 1
  simp only [mpO0, mpO1, mpO2, xzWeight, zDotVal, X_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Column 3: `(X⊗X)(Z⊗Z)(Y⊗Y) = −I` — the single line whose product is `−I`. -/
theorem mp_col3 :
    pauliHermitian mpO8 ∘ₗ pauliHermitian mpO5 ∘ₗ pauliHermitian mpO2
      = (-1 : ℂ) • LinearMap.id := by
  rw [pauliHermitian_triple_of_sum_zero mpO2 mpO5 mpO8
    (by apply Pauli.ext <;> (funext i; fin_cases i <;> decide))]
  congr 1
  simp only [mpO2, mpO5, mpO8, xzWeight, zDotVal, X_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.I_sq, show (ZMod.val (1 : ZMod 2)) = 1 by decide,
    show (ZMod.val (0 : ZMod 2)) = 0 by decide]

/-- Row 2: `(I⊗Z)(Z⊗I)(Z⊗Z) = +I`. -/
theorem mp_row2 :
    pauliHermitian mpO5 ∘ₗ pauliHermitian mpO4 ∘ₗ pauliHermitian mpO3 = (1 : ℂ) • LinearMap.id := by
  rw [pauliHermitian_triple_of_sum_zero mpO3 mpO4 mpO5
    (by apply Pauli.ext <;> (funext i; fin_cases i <;> decide))]
  congr 1
  simp only [mpO3, mpO4, mpO5, xzWeight, zDotVal, X_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.I_sq, show (ZMod.val (1 : ZMod 2)) = 1 by decide,
    show (ZMod.val (0 : ZMod 2)) = 0 by decide]

/-- Row 3: `(X⊗Z)(Z⊗X)(Y⊗Y) = +I`. -/
theorem mp_row3 :
    pauliHermitian mpO8 ∘ₗ pauliHermitian mpO7 ∘ₗ pauliHermitian mpO6 = (1 : ℂ) • LinearMap.id := by
  rw [pauliHermitian_triple_of_sum_zero mpO6 mpO7 mpO8
    (by apply Pauli.ext <;> (funext i; fin_cases i <;> decide))]
  congr 1
  simp only [mpO6, mpO7, mpO8, xzWeight, zDotVal, X_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.I_sq, show (ZMod.val (1 : ZMod 2)) = 1 by decide,
    show (ZMod.val (0 : ZMod 2)) = 0 by decide]

/-- Column 1: `(X⊗I)(I⊗Z)(X⊗Z) = +I`. -/
theorem mp_col1 :
    pauliHermitian mpO6 ∘ₗ pauliHermitian mpO3 ∘ₗ pauliHermitian mpO0 = (1 : ℂ) • LinearMap.id := by
  rw [pauliHermitian_triple_of_sum_zero mpO0 mpO3 mpO6
    (by apply Pauli.ext <;> (funext i; fin_cases i <;> decide))]
  congr 1
  simp only [mpO0, mpO3, mpO6, xzWeight, zDotVal, X_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.I_sq, show (ZMod.val (1 : ZMod 2)) = 1 by decide,
    show (ZMod.val (0 : ZMod 2)) = 0 by decide]

/-- Column 2: `(I⊗X)(Z⊗I)(Z⊗X) = +I`. -/
theorem mp_col2 :
    pauliHermitian mpO7 ∘ₗ pauliHermitian mpO4 ∘ₗ pauliHermitian mpO1 = (1 : ℂ) • LinearMap.id := by
  rw [pauliHermitian_triple_of_sum_zero mpO1 mpO4 mpO7
    (by apply Pauli.ext <;> (funext i; fin_cases i <;> decide))]
  congr 1
  simp only [mpO1, mpO4, mpO7, xzWeight, zDotVal, X_add, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Complex.I_sq, show (ZMod.val (1 : ZMod 2)) = 1 by decide,
    show (ZMod.val (0 : ZMod 2)) = 0 by decide]

/-! ## The finite no-go: no global `±1` value assignment -/

/-- **Kochen–Specker / Mermin–Peres.** There is no assignment of `±1` eigenvalues to the
nine observables consistent with the six operator line-products of the magic square (five `+1`, the
third column `−1`, as proved in `mp_row1 … mp_col3`). Equivalently, the spectral presheaf has no
global section: the quantum statistics admit no non-contextual hidden-variable model. -/
theorem mermin_peres_no_assignment :
    ¬ ∃ s : Fin 9 → ℂ,
      (∀ i, s i = 1 ∨ s i = -1) ∧
      s 0 * s 1 * s 2 = 1 ∧ s 3 * s 4 * s 5 = 1 ∧ s 6 * s 7 * s 8 = 1 ∧
      s 0 * s 3 * s 6 = 1 ∧ s 1 * s 4 * s 7 = 1 ∧ s 2 * s 5 * s 8 = -1 := by
  rintro ⟨s, hpm, hrow1, hrow2, hrow3, hcol1, hcol2, hcol3⟩
  have hsq : ∀ i, s i * s i = 1 := fun i => by rcases hpm i with h | h <;> rw [h] <;> ring
  have h1 :
      (s 0 * s 1 * s 2) * (s 3 * s 4 * s 5) * (s 6 * s 7 * s 8)
        * (s 0 * s 3 * s 6) * (s 1 * s 4 * s 7) * (s 2 * s 5 * s 8) = (1 : ℂ) := by
    have hrw :
        (s 0 * s 1 * s 2) * (s 3 * s 4 * s 5) * (s 6 * s 7 * s 8)
          * (s 0 * s 3 * s 6) * (s 1 * s 4 * s 7) * (s 2 * s 5 * s 8)
        = (s 0 * s 0) * (s 1 * s 1) * (s 2 * s 2) * (s 3 * s 3) * (s 4 * s 4)
            * (s 5 * s 5) * (s 6 * s 6) * (s 7 * s 7) * (s 8 * s 8) := by ring
    rw [hrw, hsq 0, hsq 1, hsq 2, hsq 3, hsq 4, hsq 5, hsq 6, hsq 7, hsq 8]; ring
  have h2 :
      (s 0 * s 1 * s 2) * (s 3 * s 4 * s 5) * (s 6 * s 7 * s 8)
        * (s 0 * s 3 * s 6) * (s 1 * s 4 * s 7) * (s 2 * s 5 * s 8) = (-1 : ℂ) := by
    rw [hrow1, hrow2, hrow3, hcol1, hcol2, hcol3]; ring
  have : (1 : ℂ) = -1 := h1.symm.trans h2
  norm_num at this

end FTQCLib.Stabilizer

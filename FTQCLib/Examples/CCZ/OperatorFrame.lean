/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ToffoliFrame
import FTQCLib.Hilbert.CGKForward
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
/-! # Physical CCZ in the operator frame — CCZ = 6 ZZ + 4 H (up to global phase)

A second "frame in use" demonstration. Where `ToffoliFrame` prices the *universal reversible* gate
through its diagonal core, this file prices the *physical* CCZ as a product of **native hardware
pulses** — single-qubit `Rz` rotations and two-qubit `ZZ` interactions, glued by Hadamards.

The source identity is the Hamiltonian factorization
`CCZ = exp(i·π/8·[I − Z_i − Z_j − Z_k + Z_iZ_j + Z_iZ_k + Z_jZ_k − Z_iZ_jZ_k])`,
which follows from `|111⟩⟨111| = ⅛(I−Z_i)(I−Z_j)(I−Z_k)`. The seven one- and two-body terms are
`Rz`/`ZZ` pulses; the three-body term is realised by CNOT-conjugation
`exp(−iπ/8 Z_iZ_jZ_k) = CNOT_{i→k} · ZZ_{jk}(π/4) · CNOT_{i→k}`, each `CNOT_{i→k} = H_k·CZ_{ik}·H_k`,
and each `CZ_{ab} = e^{iπ/4} Rz_a(π/2) Rz_b(π/2) ZZ_{ab}(−π/2)`. The pulse totals are **6 `ZZ` and 4
`H`** (all `H` on qubit `k`).

* `rzOperator` / `zzOperator` — the native diagonal pulses, `exp(−iθ Z/2)` and `exp(−iθ Z⊗Z/2)`.
* `cnotGate_eq_HCZH` — a 2-qubit clone of `toffoliGate_eq_hadamard_conj_ccz` (the Walsh collapse).
* `czGate_eq_native` — `CZ` expands to two `Rz` and one `ZZ` (up to `e^{iπ/4}`).
* `cczDiag_eq` / `zzzGate_eq_cnot_zz_cnot` — the Hamiltonian factorization and the cubic-term lift.
* `cczOperator_eq_native17` — the main theorem: `CCZ = e^{i·5π/8} · (6 ZZ + 4 H + 7 Rz)`, the
  physical gate priced entirely in native pulses, against the independently-defined `cczOperator`.
-/

namespace FTQCLib.Examples.CCZ

open FTQCLib FTQCLib.Hilbert FTQCLib.Hierarchy

variable {n : ℕ}

/-! ### Phase units -/

/-- The unit `e^{i·φ} ∈ ℂˣ`, for packaging a global phase. -/
noncomputable def expUnit (φ : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp (Complex.I * φ)) (Complex.exp_ne_zero _)

@[simp] theorem expUnit_val (φ : ℝ) : (expUnit φ : ℂ) = Complex.exp (Complex.I * φ) := rfl

theorem expUnit_mul (a b : ℝ) : expUnit a * expUnit b = expUnit (a + b) := by
  apply Units.ext
  simp only [Units.val_mul, expUnit_val]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A global phase `e^{i·φ}` absorbs into a diagonal gate as a constant additive phase shift:
`scaleEquiv (expUnit φ) (diagonalGateEquiv g) = diagonalGateEquiv (fun v => φ + g v)`. -/
theorem scaleEquiv_expUnit_diag (φ : ℝ) (g : (Fin n → ZMod 2) → ℝ) :
    scaleEquiv (expUnit φ) (diagonalGateEquiv g) = diagonalGateEquiv (fun v => φ + g v) := by
  apply LinearEquiv.ext
  intro ψ
  funext w
  simp only [scaleEquiv_apply, diagonalGateEquiv_apply, diagonalGate_apply, Pi.smul_apply,
    smul_eq_mul, expUnit_val]
  rw [Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]

/-! ### Native diagonal pulses -/

/-- The single-qubit `Rz_i(θ) = exp(−iθ Z_i/2)` pulse, acting as the phase
`exp(i·(−θ/2 + θ·v_i))` (using `(−1)^{v_i} = 1 − 2·v_i`). -/
noncomputable def rzOperator (i : Fin n) (θ : ℝ) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (fun v => -θ / 2 + θ * ((v i).val : ℝ))

/-- The two-qubit `ZZ_{ij}(θ) = exp(−iθ Z_iZ_j/2)` pulse, acting as the phase
`exp(i·(−θ/2 + θ·v_i + θ·v_j − 2θ·v_i·v_j))` (using `(−1)^{v_i}(−1)^{v_j} = 1 − 2v_i − 2v_j + 4v_iv_j`). -/
noncomputable def zzOperator (i j : Fin n) (θ : ℝ) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (fun v => -θ / 2 + θ * ((v i).val : ℝ) + θ * ((v j).val : ℝ)
    - 2 * θ * (((v i).val * (v j).val : ℕ) : ℝ))

/-! ### Scaling commutes with conjugation and composition -/

/-- Conjugating a scaled equivalence pulls the scalar out: `U (α·V) U⁻¹ = α·(U V U⁻¹)`. -/
theorem conjEquiv_scaleEquiv (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) (α : ℂˣ)
    (V : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    conjEquiv U (scaleEquiv α V) = scaleEquiv α (conjEquiv U V) := by
  apply LinearEquiv.ext
  intro ψ
  simp only [conjEquiv_apply, scaleEquiv_apply, LinearEquiv.map_smul]

/-- A scalar in the *left* factor of a composition pulls out (the right factor is linear). -/
theorem scaleEquiv_trans (α : ℂˣ) (A B : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    (scaleEquiv α A).trans B = scaleEquiv α (A.trans B) := by
  apply LinearEquiv.ext
  intro ψ
  simp only [LinearEquiv.trans_apply, scaleEquiv_apply, LinearEquiv.map_smul]

/-- A scalar in the *right* factor of a composition pulls out. -/
theorem trans_scaleEquiv (α : ℂˣ) (A B : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    A.trans (scaleEquiv α B) = scaleEquiv α (A.trans B) := by
  apply LinearEquiv.ext
  intro ψ
  simp only [LinearEquiv.trans_apply, scaleEquiv_apply]

/-- Nested scalars multiply. -/
theorem scaleEquiv_scaleEquiv (α β : ℂˣ) (A : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    scaleEquiv α (scaleEquiv β A) = scaleEquiv (α * β) A := by
  apply LinearEquiv.ext
  intro ψ
  simp only [scaleEquiv_apply, Units.val_mul, mul_smul]

/-! ### Lemma 1 — conjugating a diagonal gate by CNOT -/

/-- **CNOT conjugates a diagonal gate to a permuted diagonal gate.** `CNOT_{ij} · diag(f) · CNOT_{ij}`
is the diagonal gate of `f ∘ cnotPerm`. -/
theorem cnotGate_conj_diag (i j : Fin n) (hij : i ≠ j) (f : (Fin n → ZMod 2) → ℝ) :
    conjEquiv (cnotGate i j hij) (diagonalGateEquiv f)
      = diagonalGateEquiv (fun v => f (cnotPerm i j v)) := by
  apply LinearEquiv.ext
  intro ψ
  funext w
  simp only [conjEquiv_apply, cnotGate_apply, cnotGate_symm_apply, diagonalGateEquiv_apply,
    diagonalGate_apply, cnotPerm_involutive i j hij]

/-! ### Lemma 2 — CZ acts as a diagonal sign -/

/-- **CZ acts as the diagonal sign** `(-1)^{v_i v_j}`. -/
theorem czGate_apply (i j : Fin n) (g : QubitSpace n) (w : Fin n → ZMod 2) :
    czGate i j g w = (-1 : ℂ) ^ ((w i).val * (w j).val) * g w := by
  unfold czGate
  rw [diagonalGateEquiv_apply, diagonalGate_apply]
  have harg : Complex.I * ((Real.pi * (((w i).val * (w j).val : ℕ) : ℝ) : ℝ) : ℂ)
      = (((w i).val * (w j).val : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-! ### Lemma 3 — CNOT = H·CZ·H -/

/-- **`CNOT_{ij} = H_j · CZ_{ij} · H_j`** as operators (for `i ≠ j`). A 2-qubit clone of
`toffoliGate_eq_hadamard_conj_ccz`: conjugating the diagonal `CZ` by `H_j` rotates the target from the
phase basis to the flip basis, via the Walsh-sum collapse `∑_b (-1)^{c·b} = 2·[c=0]`. -/
theorem cnotGate_eq_HCZH (i j : Fin n) (hij : i ≠ j) :
    cnotGate i j hij = conjEquiv (hadamardEquiv j) (czGate i j) := by
  apply LinearEquiv.ext
  intro ψ
  funext w
  rw [conjEquiv_apply, hadamardEquiv_symm_apply, hadamardEquiv_apply]
  have hsum2 : ∀ f : ZMod 2 → ℂ, ∑ b : ZMod 2, f b = f 0 + f 1 := fun f => Fin.sum_univ_two f
  simp only [cnotGate_apply, cnotPerm, hadamardGate_apply, czGate_apply,
    Function.update_self, Function.update_idem, Function.update_of_ne hij, hsum2]
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (w j) with hwj | hwj <;> rcases dich (w i) with hwi | hwi <;>
    simp only [hwj, hwi, e0, e1, mul_zero, mul_one, one_mul, pow_zero, pow_one,
      add_zero, zero_add, CharTwo.add_self_eq_zero]
  · linear_combination (-2 * ψ (Function.update w j 0)) * invSqrt2_mul_self
  · linear_combination (-2 * ψ (Function.update w j 1)) * invSqrt2_mul_self
  · linear_combination (-2 * ψ (Function.update w j 1)) * invSqrt2_mul_self
  · linear_combination (-2 * ψ (Function.update w j 0)) * invSqrt2_mul_self

/-! ### Lemma 4 — CZ expands to native pulses -/

/-- **`CZ_{ij} = e^{iπ/4} · Rz_i(π/2) · Rz_j(π/2) · ZZ_{ij}(−π/2)`.** The controlled-`Z` is two
single-qubit `Rz` pulses and one `ZZ` interaction, up to the global phase `e^{iπ/4}`. -/
theorem czGate_eq_native (i j : Fin n) :
    czGate i j = scaleEquiv (expUnit (Real.pi / 4))
      ((rzOperator i (Real.pi / 2)).trans
        ((rzOperator j (Real.pi / 2)).trans (zzOperator i j (-(Real.pi / 2))))) := by
  -- Merge the RHS diagonal block, absorb the global phase, then compare phase functions mod 2π.
  unfold rzOperator zzOperator czGate
  rw [← diagonalGateEquiv_add, ← diagonalGateEquiv_add, scaleEquiv_expUnit_diag]
  apply diagonalGateEquiv_eq_of_diff_two_pi
  intro v
  refine ⟨0, ?_⟩
  simp only [Pi.add_apply]
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (v i) with hvi | hvi <;> rcases dich (v j) with hvj | hvj <;>
    simp only [hvi, hvj, show ZMod.val (0 : ZMod 2) = 0 from by decide,
      show ZMod.val (1 : ZMod 2) = 1 from by decide] <;> push_cast <;> ring

/-! ### The cubic kernel `exp(−iπ/8 Z_iZ_jZ_k)` -/

/-- The diagonal gate for the three-body term `exp(−iπ/8 Z_iZ_jZ_k)`, acting as the phase
`exp(−iπ/8·(−1)^{v_i}(−1)^{v_j}(−1)^{v_k})`. With `(−1)^{v_i}(−1)^{v_j}(−1)^{v_k} = 1 − 2v_i − 2v_j −
2v_k + 4v_iv_j + 4v_iv_k + 4v_jv_k − 8v_iv_jv_k`, the phase function is the explicit cubic. -/
noncomputable def zzzGate (i j k : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (fun v =>
    -(Real.pi / 8) + (Real.pi / 4) * ((v i).val : ℝ) + (Real.pi / 4) * ((v j).val : ℝ)
      + (Real.pi / 4) * ((v k).val : ℝ)
      - (Real.pi / 2) * (((v i).val * (v j).val : ℕ) : ℝ)
      - (Real.pi / 2) * (((v i).val * (v k).val : ℕ) : ℝ)
      - (Real.pi / 2) * (((v j).val * (v k).val : ℕ) : ℝ)
      + Real.pi * (((v i).val * (v j).val * (v k).val : ℕ) : ℝ))

/-! ### Lemma 5 — the Hamiltonian factorization -/

/-- The six-pulse diagonal block: three `ZZ(−π/4)` on the pairs and three `Rz(π/4)` on the qubits. -/
noncomputable def pdiag (i j k : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  (zzOperator i j (-(Real.pi / 4))).trans
    ((zzOperator i k (-(Real.pi / 4))).trans
      ((zzOperator j k (-(Real.pi / 4))).trans
        ((rzOperator i (Real.pi / 4)).trans
          ((rzOperator j (Real.pi / 4)).trans (rzOperator k (Real.pi / 4))))))

/-- `cczOperator` as a diagonal phase gate with the cubic real phase `π·v_i·v_j·v_k`. -/
private theorem cczOperator_eq_diag (i j k : Fin n) :
    cczOperator i j k
      = diagonalGateEquiv (fun v => Real.pi * (((v i).val * (v j).val * (v k).val : ℕ) : ℝ)) := by
  apply LinearEquiv.ext
  intro ψ
  funext w
  rw [cczOperator_apply, diagonalGateEquiv_apply, diagonalGate_apply]
  have hval : (w i * w j * w k).val = (w i).val * (w j).val * (w k).val := by
    have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases dich (w i) with h1 | h1 <;> rcases dich (w j) with h2 | h2 <;> rcases dich (w k) with h3 | h3 <;>
      rw [h1, h2, h3] <;> decide
  rw [hval]
  have harg : Complex.I * ((Real.pi * (((w i).val * (w j).val * (w k).val : ℕ) : ℝ) : ℝ) : ℂ)
      = (((w i).val * (w j).val * (w k).val : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- **The Hamiltonian factorization.** `cczOperator i j k = e^{iπ/8} (pdiag zzzGate)`. This is the
operator form of the projector identity `|111><111| = (1/8)(I-Z_i)(I-Z_j)(I-Z_k)`: the six one- and
two-body pulses (`pdiag`) plus the cubic `Z_iZ_jZ_k` term (`zzzGate`) reproduce `CCZ` up to the
residual constant `e^{iπ/8}`. -/
theorem cczDiag_eq (i j k : Fin n) :
    cczOperator i j k = scaleEquiv (expUnit (Real.pi / 8)) ((pdiag i j k).trans (zzzGate i j k)) := by
  rw [cczOperator_eq_diag]
  unfold pdiag zzzGate zzOperator rzOperator
  rw [← diagonalGateEquiv_add, ← diagonalGateEquiv_add, ← diagonalGateEquiv_add,
    ← diagonalGateEquiv_add, ← diagonalGateEquiv_add, ← diagonalGateEquiv_add,
    scaleEquiv_expUnit_diag]
  -- Compare the cubic phase to π/8 + (six-pulse phase + cubic-term phase) mod 2π.
  apply diagonalGateEquiv_eq_of_diff_two_pi
  intro v
  refine ⟨0, ?_⟩
  simp only [Pi.add_apply]
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (v i) with hvi | hvi <;> rcases dich (v j) with hvj | hvj <;> rcases dich (v k) with hvk | hvk <;>
    simp only [hvi, hvj, hvk, show ZMod.val (0 : ZMod 2) = 0 from by decide,
      show ZMod.val (1 : ZMod 2) = 1 from by decide] <;> push_cast <;> ring

/-! ### Lemma 6 — the cubic term via CNOT conjugation -/

/-- **`exp(−iπ/8 Z_iZ_jZ_k) = CNOT_{i→k} · ZZ_{jk}(π/4) · CNOT_{i→k}`.** Conjugating the two-body
`ZZ_{jk}` by `CNOT_{i→k}` (which sends `Z_k ↦ Z_iZ_k`) produces the three-body coupling. -/
theorem zzzGate_eq_cnot_zz_cnot (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k) :
    zzzGate i j k = (cnotGate i k hik).trans
      ((zzOperator j k (Real.pi / 4)).trans (cnotGate i k hik)) := by
  -- The RHS is `conjEquiv (cnotGate i k hik) (zzOperator j k (π/4))` (CNOT is self-inverse).
  have hsymm : (cnotGate i k hik).symm = cnotGate i k hik := by
    apply LinearEquiv.ext
    intro ψ
    funext w
    rw [cnotGate_symm_apply, cnotGate_apply]
  have hconj : (cnotGate i k hik).trans
        ((zzOperator j k (Real.pi / 4)).trans (cnotGate i k hik))
      = conjEquiv (cnotGate i k hik) (zzOperator j k (Real.pi / 4)) := by
    unfold conjEquiv
    rw [hsymm]
  rw [hconj]
  unfold zzOperator
  rw [cnotGate_conj_diag i k hik]
  unfold zzzGate
  apply diagonalGateEquiv_eq_of_diff_two_pi
  intro v
  refine ⟨0, ?_⟩
  -- cnotPerm i k v updates coord k to v_k + v_i; coord j is unchanged (j ≠ k).
  have hk : (cnotPerm i k v) k = v k + v i := by
    unfold cnotPerm; rw [Function.update_self]
  have hj : (cnotPerm i k v) j = v j := by
    unfold cnotPerm; rw [Function.update_of_ne hjk]
  rw [hj, hk]
  -- Now case-split on the three bits (mind the .val of the carry v_k + v_i).
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  rcases dich (v i) with hvi | hvi <;> rcases dich (v j) with hvj | hvj <;> rcases dich (v k) with hvk | hvk <;>
    simp only [hvi, hvj, hvk, e0, e1,
      show (0 : ZMod 2) + 0 = 0 from by decide, show (0 : ZMod 2) + 1 = 1 from by decide,
      show (1 : ZMod 2) + 0 = 1 from by decide, show (1 : ZMod 2) + 1 = 0 from by decide] <;>
    push_cast <;> ring

/-! ### Lemma 7 — the structural decomposition -/

/-- **CCZ as a structural pulse product (with one `ZZ` still inside the CNOT conjugation).**
`cczOperator i j k = e^{iπ/8} · pdiag · CNOT_{i→k} · ZZ_{jk}(π/4) · CNOT_{i→k}`. -/
theorem cczOperator_eq_structural (i j k : Fin n) (_hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cczOperator i j k = scaleEquiv (expUnit (Real.pi / 8))
      ((pdiag i j k).trans ((cnotGate i k hik).trans
        ((zzOperator j k (Real.pi / 4)).trans (cnotGate i k hik)))) := by
  rw [cczDiag_eq i j k, zzzGate_eq_cnot_zz_cnot i j k hik hjk]

/-! ### The full native-pulse expansion -/

/-- The full native-pulse expansion of CCZ (6 `ZZ`, 4 `H`, 7 `Rz`): take `cczOperator_eq_structural`
and expand each `CNOT_{i→k}` to `H_k·CZ_{ik}·H_k` and each `CZ_{ik}` to its native pulses. By
construction this equals `cczOperator i j k` up to the global phase `e^{i·5π/8}`. -/
noncomputable def native17 (i j k : Fin n) (_hik : i ≠ k) :
    QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  (pdiag i j k).trans
    ((conjEquiv (hadamardEquiv k)
        ((rzOperator i (Real.pi / 2)).trans
          ((rzOperator k (Real.pi / 2)).trans (zzOperator i k (-(Real.pi / 2)))))).trans
      ((zzOperator j k (Real.pi / 4)).trans
        (conjEquiv (hadamardEquiv k)
          ((rzOperator i (Real.pi / 2)).trans
            ((rzOperator k (Real.pi / 2)).trans (zzOperator i k (-(Real.pi / 2))))))))

/-- **The physical CCZ priced in native pulses.** `CCZ_{ijk} = e^{i·5π/8} · native17`, where
`native17` is built from **6 `ZZ` interactions, 4 Hadamards (all on `k`), and 7 `Rz`
rotations** — the gate the hardware actually runs. The global phase `5π/8 = π/8 + 2·(π/4)` comes from the residual
constant of the Hamiltonian factorization (`π/8`) plus the `e^{iπ/4}` of each of the two `CZ`s. -/
theorem cczOperator_eq_native17 (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cczOperator i j k
      = scaleEquiv (expUnit (5 * Real.pi / 8)) (native17 i j k hik) := by
  rw [cczOperator_eq_structural i j k hij hik hjk]
  unfold native17
  -- Expand each CNOT = H·CZ·H, then each CZ → native (each contributing a scale of e^{iπ/4}).
  rw [cnotGate_eq_HCZH i k hik, czGate_eq_native i k, conjEquiv_scaleEquiv]
  -- The RHS is now
  --   scaleEquiv (expUnit π/8) (pdiag . (S . (ZZ . S)))   with S = scaleEquiv (expUnit π/4) C
  -- and `native17 = pdiag . (C . (ZZ . C))`. Normalize all inner scales to the outside.
  simp only [scaleEquiv_trans, trans_scaleEquiv, scaleEquiv_scaleEquiv]
  -- Now the global phase is `expUnit π/8 * (expUnit π/4 * expUnit π/4) = expUnit (5π/8)`.
  congr 1
  apply Units.ext
  simp only [Units.val_mul, expUnit_val, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end FTQCLib.Examples.CCZ

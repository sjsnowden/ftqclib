/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardPhase
import FTQCLib.Examples.HadamardCharSumFrame

/-! # Frame-pure carrier operations for the above-floor certificate

The character-sum carrier `KernelSumState` gets the gate operations needed to run circuits above
the floor, all **frame-pure** (no `FTQCLib.Hilbert`): the `h = 0` embedding of a floor `KernelState`,
the diagonal-gate and CNOT applications, and the CNOT amplitude lemmas (moved here from the Hilbert
correspondence). The Hilbert intertwinings and the correspondence certificate live in
`FTQCLib/Hilbert/CharSumCorrespondence.lean`.

**Note.** `applyDiagSum` leaves `L` unchanged: exact for the
amplitude, stale for the Lagrangian of a floor. The floor-keeping diagonal rule carries the shear
as data, `applyDiagShear` with `DiagShiftDatum` (`FTQCLib/Examples/CarrierClifford.lean`). `cnotPauli`
below is the symplectic lift (a non-symplectic alternative map is exhibited as a control in
`CharSumGatesCheck.lean`). -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Frame Complex

variable {n : ℕ}

/-- Embed a floor `KernelState` as the `h = 0` character-sum state
(`DiagPhase (n+0) = DiagPhase n`). -/
noncomputable def ofKernelState (K : KernelState n) : KernelSumState n where
  m := K.m
  h := 0
  Q := K.q
  c := K.c
  L := K.L
  x₀ := K.x₀

/-- Appending the empty tuple is the identity (the `h = 0` point is just `w`). -/
theorem append_fin0 (w : Fin n → ZMod 2) (y : Fin 0 → ZMod 2) :
    Fin.append w y = w := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => l.elim0) i
  rw [Fin.append_left]
  exact congrArg w (Fin.ext rfl)

/-- **`h = 0` reduction.** The character sum over zero summation variables is the single
`KernelState` amplitude `c · exp(i · realPhase Q w)`. -/
theorem ampCore_zero {m : ℕ} (Q : DiagPhase (n + 0) m) (c : ℂ) (w : Fin n → ZMod 2) :
    ampCore m 0 Q c w = c * Complex.exp (Complex.I * (DiagPhase.realPhase Q w : ℂ)) := by
  unfold ampCore
  rw [pow_zero, div_one, Fintype.sum_unique, append_fin0]

/-! ## Diagonal gate on the carrier (grade 0) -/

/-- Apply a diagonal gate `D` (at the state's precision) by adding it to the **free block** of the
exponent. Support, precision, and summation count are unchanged. -/
noncomputable def applyDiagSum (S : KernelSumState n) (D : DiagPhase n S.m) : KernelSumState n where
  m := S.m
  h := S.h
  Q := S.Q + MvPolynomial.rename (Fin.castAdd S.h) D
  c := S.c
  L := S.L
  x₀ := S.x₀

/-- A gate renamed into the free block reads only the free coordinates at an appended point. -/
theorem eval_rename_castAdd {h m : ℕ} (D : DiagPhase n m) (w : Fin n → ZMod 2)
    (y : Fin h → ZMod 2) :
    DiagPhase.eval (MvPolynomial.rename (Fin.castAdd h) D) (Fin.append w y) =
      DiagPhase.eval D w := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_rename,
    show (DiagPhase.liftBinary (Fin.append w y) ∘ (Fin.castAdd h)) = DiagPhase.liftBinary w from by
      funext i; simp only [Function.comp_apply, DiagPhase.liftBinary, Fin.append_left]]

/-- Real-phase form of `eval_rename_castAdd`. -/
theorem realPhase_rename_castAdd {h m : ℕ} (D : DiagPhase n m) (w : Fin n → ZMod 2)
    (y : Fin h → ZMod 2) :
    DiagPhase.realPhase (MvPolynomial.rename (Fin.castAdd h) D) (Fin.append w y)
      = DiagPhase.realPhase D w := by
  unfold DiagPhase.realPhase
  rw [eval_rename_castAdd]

/-! ## CNOT on the carrier (grade 0, moves the support)

`cnotBitMap` (= the Hilbert `cnotPerm`, same definition) is `𝔽₂`-linear and involutive; we lift it
to a `Pauli` linear map for the support Lagrangian. -/

theorem cnotBitMap_add (i k : Fin n) (v w : Fin n → ZMod 2) :
    cnotBitMap i k (v + w) = cnotBitMap i k v + cnotBitMap i k w := by
  funext l
  by_cases hl : l = k
  · subst hl; simp only [cnotBitMap, Function.update_self, Pi.add_apply]; ring
  · simp only [cnotBitMap, Function.update_of_ne hl, Pi.add_apply]

theorem cnotBitMap_smul (i k : Fin n) (c : ZMod 2) (v : Fin n → ZMod 2) :
    cnotBitMap i k (c • v) = c • cnotBitMap i k v := by
  funext l
  by_cases hl : l = k
  · subst hl; simp only [cnotBitMap, Function.update_self, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [cnotBitMap, Function.update_of_ne hl, Pi.smul_apply]

theorem cnotBitMap_involutive (i k : Fin n) (hik : i ≠ k) (v : Fin n → ZMod 2) :
    cnotBitMap i k (cnotBitMap i k v) = v := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  funext l
  by_cases hl : l = k
  · subst hl
    simp only [cnotBitMap, Function.update_self, Function.update_of_ne hik]
    rw [add_assoc, h2, add_zero]
  · simp only [cnotBitMap, Function.update_of_ne hl]

/-- `cnotBitMap i j` adds the `i`-th bit to the `j`-th: it is `x ↦ x + x_i·e_j`. -/
theorem cnotBitMap_eq_add_smul_single (i j : Fin n) (x : Fin n → ZMod 2) :
    cnotBitMap i j x = x + (x i) • (Pi.single j 1 : Fin n → ZMod 2) := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp only [cnotBitMap, Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one]
  · simp only [cnotBitMap, Function.update_of_ne hl, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hl, smul_zero, add_zero]

/-- The `Pauli` lift of CNOT with control `i` and target `j`: the X-block is pushed by
`cnotBitMap i j` (the target bit receives the control) and the Z-block by `cnotBitMap j i` (the
control's Z receives the target's), the conjugation `X_i ↦ X_i X_j`, `Z_j ↦ Z_i Z_j`. This is the
symplectic lift; the earlier form with `cnotBitMap i j` on both blocks is not symplectic
(`CharSumGatesCheck`). -/
noncomputable def cnotPauli (i j : Fin n) : Pauli n →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨cnotBitMap i j p.X, cnotBitMap j i p.Z⟩
  map_add' p q := by apply Pauli.ext <;> simp only [X_add, Z_add, cnotBitMap_add]
  map_smul' c p := by
    apply Pauli.ext <;> simp only [X_smul, Z_smul, cnotBitMap_smul, RingHom.id_apply]

@[simp] theorem cnotPauli_X (i j : Fin n) (p : Pauli n) :
    (cnotPauli i j p).X = cnotBitMap i j p.X := rfl

@[simp] theorem cnotPauli_Z (i j : Fin n) (p : Pauli n) :
    (cnotPauli i j p).Z = cnotBitMap j i p.Z := rfl

/-- The lift is an involution off the diagonal. -/
theorem cnotPauli_cnotPauli (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    cnotPauli i j (cnotPauli i j p) = p := by
  apply Pauli.ext
  · rw [cnotPauli_X, cnotPauli_X, cnotBitMap_involutive i j hij]
  · rw [cnotPauli_Z, cnotPauli_Z, cnotBitMap_involutive j i hij.symm]

/-- The lift as a linear equivalence (`i ≠ j`). -/
noncomputable def cnotPauliEquiv (i j : Fin n) (hij : i ≠ j) : Pauli n ≃ₗ[ZMod 2] Pauli n :=
  LinearEquiv.ofInvolutive (cnotPauli i j) (cnotPauli_cnotPauli i j hij)

/-- The lift preserves dimension (`i ≠ j`). -/
theorem finrank_map_cnotPauli (i j : Fin n) (hij : i ≠ j) (L : Submodule (ZMod 2) (Pauli n)) :
    Module.finrank (ZMod 2) (Submodule.map (cnotPauli i j) L) = Module.finrank (ZMod 2) L :=
  LinearEquiv.finrank_map_eq (cnotPauliEquiv i j hij) L

/-- Apply a CNOT (control `i`, target `j`) to the carrier: push the exponent's free block through
`affinePushforward`, and the support `(L, x₀)` through the CNOT bit-map. -/
noncomputable def applyCnotSum (i j : Fin n) (S : KernelSumState n) : KernelSumState n where
  m := S.m
  h := S.h
  Q := affinePushforward (Fin.castAdd S.h i) (Fin.castAdd S.h j) S.Q
  c := S.c
  L := Submodule.map (cnotPauli i j) S.L
  x₀ := cnotBitMap i j S.x₀

/-! ## CNOT on the amplitude (moved here from the Hilbert correspondence; frame-pure) -/

/-- CNOT on the free block of an appended point acts on the free part only. -/
theorem cnotBitMap_castAdd_append {h : ℕ} (i j : Fin n) (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) :
    cnotBitMap (Fin.castAdd h i) (Fin.castAdd h j) (Fin.append w y)
      = Fin.append (cnotBitMap i j w) y := by
  unfold DiagPhase.cnotBitMap
  rw [Fin.append_left, Fin.append_left, update_append_castAdd]

/-- The frame CNOT on the exponent computes the amplitude at the CNOT-permuted point. -/
theorem ampCore_affinePushforward {h m : ℕ} (i j : Fin n) (Q : DiagPhase (n + h) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m h (affinePushforward (Fin.castAdd h i) (Fin.castAdd h j) Q) c w
      = ampCore m h Q c (cnotBitMap i j w) := by
  have hrp : ∀ y : Fin h → ZMod 2,
      DiagPhase.realPhase (affinePushforward (Fin.castAdd h i) (Fin.castAdd h j) Q) (Fin.append w y)
        = DiagPhase.realPhase Q (Fin.append (cnotBitMap i j w) y) := by
    intro y
    unfold DiagPhase.realPhase
    rw [DiagPhase.affinePushforward_eval, cnotBitMap_castAdd_append]
  unfold ampCore
  congr 1
  exact Finset.sum_congr rfl (fun y _ => by rw [hrp y])

/-- The CNOT-transformed support coset is the CNOT-preimage of the original. -/
theorem cnotSum_support (i j : Fin n) (hij : i ≠ j) (S : KernelSumState n) (w : Fin n → ZMod 2) :
    (∃ p ∈ (applyCnotSum i j S).L, w = (applyCnotSum i j S).x₀ + p.X)
      ↔ (∃ p ∈ S.L, cnotBitMap i j w = S.x₀ + p.X) := by
  constructor
  · rintro ⟨p, hpmap, hw⟩
    obtain ⟨q, hqL, rfl⟩ := Submodule.mem_map.mp hpmap
    refine ⟨q, hqL, ?_⟩
    rw [show (applyCnotSum i j S).x₀ = cnotBitMap i j S.x₀ from rfl, cnotPauli_X] at hw
    rw [hw, cnotBitMap_add, cnotBitMap_involutive i j hij, cnotBitMap_involutive i j hij]
  · rintro ⟨p, hpL, hw⟩
    refine ⟨cnotPauli i j p, Submodule.mem_map.mpr ⟨p, hpL, rfl⟩, ?_⟩
    rw [show (applyCnotSum i j S).x₀ = cnotBitMap i j S.x₀ from rfl, cnotPauli_X, ← cnotBitMap_add,
      ← hw, cnotBitMap_involutive i j hij]

end FTQCLib.Frame.Walkthrough

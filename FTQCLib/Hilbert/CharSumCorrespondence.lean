/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.HadamardCharSumBridge
import FTQCLib.Hilbert.FrameConditioning
import FTQCLib.Hilbert.Diagonal
import FTQCLib.Examples.CharSumGates

/-! # The above-floor certificate: the character-sum representation equals the intended Hilbert state

This file proves that *the continued (character-sum) representation always corresponds to the
intended Hilbert-space state beyond the stabilizer boundary.* The interpretation map
`F : KernelSumState n → QubitSpace n` is the **support-restricted** amplitude (the `h > 0`
extension of `KernelState.psi`); we prove it intertwines the frame's above-floor gate operations
(fine Hadamard, diagonal, CNOT) with the genuine Hilbert gates, and that at `h = 0` it is
`KernelState.psi`. Composing gives `F (runFrame gs S) = runHilbert gs (F S)` — the frame's
continued representation is the intended Hilbert state, for any circuit.

The raw-amplitude engine is `HadamardCharSumBridge`; this file adds the support indicator and the
absolute correspondence.

**Related.** The frame-pure alphabet `NormalGate` with `runNormal`
(`FTQCLib/Examples/CliffordWordFloor.lean`) keeps a height-zero floor at height zero on well-formed
Clifford words and agrees with this module's Hilbert circuit letter by letter (`F_runNormal`,
`CliffordWordFloorCheck.lean`). The relation between `Gate` / `runFrame` here (tail-first, `Diag`
with the Lagrangian unchanged) and `NormalGate` / `runNormal` (head-first, the shear as data) is
`StateEq` per letter; it is not formalized here. -/

namespace FTQCLib.Frame.Correspondence

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Hilbert FTQCLib.Frame FTQCLib.Frame.Walkthrough
  Complex

variable {n : ℕ}

/-! ## The coset/support machinery

The support of a `KernelSumState` is the affine coset
`x₀ + π_X(L) = {w | ∃ p ∈ L, w = x₀ + p.X}`. When bit `k` is X-supported (`e_k ∈ π_X(L)`), the
coset is closed under flipping bit `k` — the lemma needed to carry `hadamardGate`'s bit-`k` mixing
through the support indicator. -/

/-- One direction of coset closure: if `e_k ∈ π_X(L)`, a support point stays in support after flipping
bit `k`. Over `𝔽₂` the flip either does nothing (`b = w_k`) or adds the witness `p₀` exactly once. -/
theorem flip_mem (S : KernelSumState n) (k : Fin n) (b : ZMod 2) (w : Fin n → ZMod 2)
    (hk : ∃ p ∈ S.L, p.X = Pi.single k (1 : ZMod 2)) :
    (∃ p ∈ S.L, w = S.x₀ + p.X) → (∃ p ∈ S.L, Function.update w k b = S.x₀ + p.X) := by
  obtain ⟨p₀, hp₀L, hp₀X⟩ := hk
  have key : ∀ x y : ZMod 2, x ≠ y → x = y + 1 := by decide
  rintro ⟨p, hpL, rfl⟩
  by_cases hb : b = (S.x₀ + p.X) k
  · exact ⟨p, hpL, by rw [hb, Function.update_eq_self]⟩
  · refine ⟨p + p₀, add_mem hpL hp₀L, ?_⟩
    have hb1 : b = (S.x₀ + p.X) k + 1 := key b ((S.x₀ + p.X) k) hb
    funext j
    rw [Function.update_apply, X_add, hp₀X]
    by_cases hj : j = k
    · subst hj
      rw [if_pos rfl, hb1]
      simp only [Pi.add_apply, Pi.single_eq_same]
      ring
    · rw [if_neg hj]
      simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]

/-- **Coset closure.** When bit `k` is X-supported (`e_k ∈ π_X(L)`), support membership is invariant under
flipping bit `k`. -/
theorem coset_flip_closed (S : KernelSumState n) (k : Fin n) (b : ZMod 2) (w : Fin n → ZMod 2)
    (hk : ∃ p ∈ S.L, p.X = Pi.single k (1 : ZMod 2)) :
    (∃ p ∈ S.L, w = S.x₀ + p.X) ↔ (∃ p ∈ S.L, Function.update w k b = S.x₀ + p.X) := by
  constructor
  · exact flip_mem S k b w hk
  · intro h
    have hb := flip_mem S k (w k) (Function.update w k b) hk h
    rwa [Function.update_idem, Function.update_eq_self] at hb

/-! ## The interpretation `F` and the `h = 0` base

`F` is the support-restricted amplitude: the `h > 0` extension of `KernelState.psi`. At `h = 0` it *is*
`psi`, so the base of the induction is the frame's own intended-Hilbert-state map, not a raw amplitude. -/

open Classical in
/-- The interpretation of a character-sum state as a Hilbert vector: the amplitude on its support coset,
zero off it. The `h > 0` extension of `KernelState.psi`. -/
noncomputable def F (S : KernelSumState n) : QubitSpace n :=
  fun w => if (∃ p ∈ S.L, w = S.x₀ + p.X) then ampCore S.m S.h S.Q S.c w else 0

/-- **Base case.** On a floor `KernelState` (embedded at `h = 0`), `F` is exactly the frame's intended
Hilbert state `KernelState.psi`. -/
theorem F_ofKernelState (K : KernelState n) :
    toQState (F (ofKernelState K)) = KernelState.psi K := by
  unfold KernelState.psi
  congr 1
  funext w
  simp only [F, ofKernelState]
  by_cases hw : ∃ p ∈ K.L, w = K.x₀ + p.X
  · rw [if_pos hw, if_pos hw, ampCore_zero]
  · rw [if_neg hw, if_neg hw]

/-- `F` on support is the raw amplitude. -/
theorem F_pos {S : KernelSumState n} {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ S.L, w = S.x₀ + p.X) : F S w = ampCore S.m S.h S.Q S.c w := by
  unfold F; exact if_pos hw

/-- `F` off support is zero. -/
theorem F_neg {S : KernelSumState n} {w : Fin n → ZMod 2}
    (hw : ¬ ∃ p ∈ S.L, w = S.x₀ + p.X) : F S w = 0 := by
  unfold F; exact if_neg hw

/-! ## The gate intertwinings

### The fine Hadamard (with the support indicator). -/

/-- **H-step.** On an X-supported bit (`e_k ∈ π_X(L)`, so the support coset is closed under the bit-`k`
flip), `F` intertwines the frame's character-sum Hadamard with the genuine Walsh transform. The engine is
the raw-amplitude `applyHFiner_hadamard`; the coset lemma carries the support indicator through. -/
theorem F_applyHFiner (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m)
    (hk : ∃ p ∈ S.L, p.X = Pi.single k (1 : ZMod 2)) :
    F (applyHFiner k S) = hadamardGate k (F S) := by
  funext w
  rw [hadamardGate_apply]
  by_cases hw : ∃ p ∈ S.L, w = S.x₀ + p.X
  · rw [F_pos (S := applyHFiner k S) hw, congrFun (applyHFiner_hadamard k S hm) w,
      hadamardGate_apply]
    congr 1
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [F_pos (S := S) ((coset_flip_closed S k b w hk).mp hw)]
  · rw [F_neg (S := applyHFiner k S) hw]
    refine (mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun b _ => ?_))).symm
    rw [F_neg (S := S) (fun hc => hw ((coset_flip_closed S k b w hk).mpr hc)), mul_zero]

/-! ### Diagonal gates (grade 0). -/

/-- Adding a free-block gate `D` to the exponent multiplies the amplitude pointwise by `exp(i·realPhase D w)`
— it factors out of the character sum because it depends only on the free coordinates. -/
theorem ampCore_add_liftFree {h m : ℕ} (Q : DiagPhase (n + h) m) (D : DiagPhase n m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m h (Q + MvPolynomial.rename (Fin.castAdd h) D) c w
      = Complex.exp (Complex.I * (DiagPhase.realPhase D w : ℂ)) * ampCore m h Q c w := by
  unfold ampCore
  have hterm : ∀ y : Fin h → ZMod 2,
      Complex.exp (Complex.I *
          (DiagPhase.realPhase (Q + MvPolynomial.rename (Fin.castAdd h) D) (Fin.append w y) : ℂ))
        = Complex.exp (Complex.I * (DiagPhase.realPhase D w : ℂ))
          * Complex.exp (Complex.I * (DiagPhase.realPhase Q (Fin.append w y) : ℂ)) := by
    intro y
    rw [exp_realPhase_add, realPhase_rename_castAdd, mul_comm]
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum]
  ring

/-- **Diagonal step.** `F` intertwines the frame's diagonal-gate application with the Hilbert diagonal gate.
Support is preserved (diagonal gates don't move the coset). -/
theorem F_applyDiagSum (S : KernelSumState n) (D : DiagPhase n S.m) :
    F (applyDiagSum S D) = diagonalGate (DiagPhase.realPhase D) (F S) := by
  funext w
  rw [diagonalGate_apply]
  simp only [F, applyDiagSum]
  by_cases hw : ∃ p ∈ S.L, w = S.x₀ + p.X
  · rw [if_pos hw, if_pos hw, ampCore_add_liftFree]
  · rw [if_neg hw, if_neg hw, mul_zero]

/-! ### CNOT (grade 0, moves the support). -/

/- `cnotBitMap_castAdd_append`, `ampCore_affinePushforward` and `cnotSum_support` are in
`FTQCLib/Examples/CharSumGates.lean` (frame-pure). -/

/-- **CNOT step.** `F` intertwines the frame CNOT with the Hilbert `cnotGate` (`cnotBitMap = cnotPerm`). -/
theorem F_applyCnotSum (i j : Fin n) (hij : i ≠ j) (S : KernelSumState n) :
    F (applyCnotSum i j S) = cnotGate i j hij (F S) := by
  funext w
  rw [cnotGate_apply, show cnotPerm i j w = cnotBitMap i j w from rfl]
  by_cases hw : ∃ p ∈ S.L, cnotBitMap i j w = S.x₀ + p.X
  · rw [F_pos (S := applyCnotSum i j S) ((cnotSum_support i j hij S w).mpr hw)]
    simp only [applyCnotSum]
    rw [ampCore_affinePushforward, F_pos (S := S) hw]
  · rw [F_neg (S := applyCnotSum i j S)
        (fun hc => hw ((cnotSum_support i j hij S w).mp hc)),
      F_neg (S := S) hw]

/-! ## Circuit assembly

A gate alphabet at a fixed precision `m`, frame and Hilbert interpreters, and the induction folding the three
intertwinings into one statement: `F` intertwines any well-formed circuit with the matching Hilbert circuit. -/

section Assembly

variable {m : ℕ}

/-- The gate alphabet at precision `m`: fine Hadamard, diagonal gate, CNOT. -/
inductive Gate (n m : ℕ) where
  | H : Fin n → Gate n m
  | Diag : DiagPhase n m → Gate n m
  | Cnot : (i j : Fin n) → i ≠ j → Gate n m

/-- The frame action of a gate. The diagonal case needs the state precision to be `m`. -/
noncomputable def applyGate (g : Gate n m) (S : KernelSumState n) : KernelSumState n :=
  match g with
  | .H k => applyHFiner k S
  | .Diag D => if hm : S.m = m then applyDiagSum S (hm ▸ D) else S
  | .Cnot i j _ => applyCnotSum i j S

/-- The Hilbert action of a gate. -/
noncomputable def gateHilbert (g : Gate n m) : QubitSpace n → QubitSpace n :=
  match g with
  | .H k => hadamardGate k
  | .Diag D => diagonalGate (DiagPhase.realPhase D)
  | .Cnot i j hij => cnotGate i j hij

/-- Well-formedness of a single gate at a state: the fine Hadamard needs an X-supported target bit and
positive precision; diagonal and CNOT impose nothing. -/
def gateWF (g : Gate n m) (S : KernelSumState n) : Prop :=
  match g with
  | .H k => (∃ p ∈ S.L, p.X = Pi.single k (1 : ZMod 2)) ∧ 1 ≤ S.m
  | .Diag _ => True
  | .Cnot _ _ _ => True

/-- Precision is gate-invariant. -/
theorem applyGate_m (g : Gate n m) (S : KernelSumState n) : (applyGate g S).m = S.m := by
  cases g with
  | H k => rfl
  | Diag D => simp only [applyGate]; split <;> rfl
  | Cnot i j hij => rfl

/-- `realPhase` is invariant under the precision cast (the cast only retypes the exponent). -/
theorem realPhase_cast {m₁ m₂ : ℕ} (h : m₁ = m₂) (D : DiagPhase n m₁) :
    DiagPhase.realPhase (h ▸ D) = DiagPhase.realPhase D := by
  subst h; rfl

/-- **Per-gate step.** With the precision invariant `S.m = m` and gate well-formedness, `F` intertwines the
frame gate with its Hilbert counterpart. -/
theorem F_applyGate (g : Gate n m) (S : KernelSumState n) (hm : S.m = m)
    (hwf : gateWF g S) : F (applyGate g S) = gateHilbert g (F S) := by
  cases g with
  | H k =>
    obtain ⟨hk, hmS⟩ := hwf
    exact F_applyHFiner k S hmS hk
  | Diag D =>
    simp only [applyGate, gateHilbert, dif_pos hm]
    rw [F_applyDiagSum, realPhase_cast]
  | Cnot i j hij => exact F_applyCnotSum i j hij S

/-- Run a circuit on the frame carrier (head applied outermost). -/
noncomputable def runFrame (gs : List (Gate n m)) (S : KernelSumState n) : KernelSumState n :=
  gs.foldr applyGate S

/-- Run the matching circuit on the Hilbert side. -/
noncomputable def runHilbert (gs : List (Gate n m)) (ψ : QubitSpace n) : QubitSpace n :=
  gs.foldr (fun g ψ => gateHilbert g ψ) ψ

/-- Circuit well-formedness: each gate is well-formed at the state it is applied to. -/
def circuitWF : List (Gate n m) → KernelSumState n → Prop
  | [], _ => True
  | g :: gs, S => gateWF g (runFrame gs S) ∧ circuitWF gs S

theorem runFrame_m (gs : List (Gate n m)) (S : KernelSumState n) : (runFrame gs S).m = S.m := by
  induction gs with
  | nil => rfl
  | cons g gs ih => show (applyGate g (runFrame gs S)).m = S.m; rw [applyGate_m]; exact ih

/-- **The circuit correspondence.** `F` intertwines any well-formed `{H, diagonal, CNOT}` circuit with the
matching Hilbert circuit — the frame's continued representation tracks the intended Hilbert state, gate by
gate. -/
theorem F_runFrame (gs : List (Gate n m)) (S : KernelSumState n) (hm : S.m = m)
    (hwf : circuitWF gs S) : F (runFrame gs S) = runHilbert gs (F S) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := hwf
    show F (applyGate g (runFrame gs S)) = gateHilbert g (runHilbert gs (F S))
    rw [F_applyGate g (runFrame gs S) (by rw [runFrame_m]; exact hm) hg, ih hgs]

/-! ## The certificate

The continued (character-sum) representation of a floor stabilizer state, run under any
well-formed circuit, equals the intended Hilbert-space state — the Hilbert circuit applied to
`KernelState.psi K`. -/

/-- **The above-floor certificate.** For a floor `KernelState K` (at the circuit precision) and any
well-formed `{H, diagonal, CNOT}` circuit `gs`, the character-sum representation `F (runFrame gs ...)`,
interpreted into the Hilbert space, equals the Hilbert circuit applied to the intended stabilizer state
`KernelState.psi K`: the continued representation always corresponds to the intended
Hilbert-space state beyond the stabilizer boundary. -/
theorem charSum_correspondence {n m : ℕ} (gs : List (Gate n m)) (K : KernelState n) (hm : K.m = m)
    (hwf : circuitWF gs (ofKernelState K)) :
    toQState (F (runFrame gs (ofKernelState K)))
      = toQState (runHilbert gs (toQState.symm (KernelState.psi K))) := by
  rw [F_runFrame gs (ofKernelState K) hm hwf]
  congr 2
  rw [← F_ofKernelState K, LinearEquiv.symm_apply_apply]

end Assembly

end FTQCLib.Frame.Correspondence

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CharSumGates
import FTQCLib.Examples.HadamardCharSumFrame

/-!
# The carrier's denotation and its gauge

A carrier record `KernelSumState n = ⟨m, h, Q, c, L, x₀⟩` denotes an amplitude function through
`amp`: `ampCore` (the exponent summed over the bound register, scaled by `c / √2^h`) on the support
coset `x₀ + π_X(L)`, and zero off it. Two records are the same state when their denotations agree
(`StateEq`); the state type is the quotient of records by the kernel of `amp` (`stateSetoid`).

The record is redundant, and the redundancies are theorems that named rewrites preserve `amp`:

* **R1** the constant term of the exponent against the scale — `amp_add_C`;
* **R2** the offset modulo the shadow `π_X(L)` — `amp_offset_add_mem`;
* **R3** the Z-part of `L` — any lift with the same shadow — `amp_congr_xProj`, with the
  extreme case `amp_zeroZ` (every Z-block erased);
* **R4** the exponent off the support coset — `amp_congr_support`;
* **R5** relabelling the bound register by any bijection of its words — `amp_rename_bound`.

R6 (the representer of `hRaise`) is `amp_hRaise_indep` in `HadamardAmplitude.lean`; R7 (the
precision lift) is not treated here. Each rewrite's hypothesis is shown
load-bearing in the check module.

Everything here is frame-pure: `DiagPhase`, `Pauli`, `Submodule`, `ℂ`. No `FTQCLib.Hilbert`.

## Implementation notes

* `amp` is the frame-side twin of `F` (`FTQCLib/Hilbert/CharSumCorrespondence.lean`), whose definition
  uses no Hilbert structure but whose module does; the two definitions coincide term for term.
* The support decision inside `amp` is classical, exactly as in `F`: membership in an arbitrary
  `Submodule` is not decidable in general. Consumers that need computation supply their own
  instance, as the check modules do on the example Lagrangians.
* The gauge theorems are stated on explicit fields `⟨m, h, Q, c, L, x₀⟩`; a record `S` is
  `⟨S.m, S.h, S.Q, S.c, S.L, S.x₀⟩` by structure eta, so they apply to any record.

## Main definitions

* `amp` — the support-restricted amplitude of a record.
* `StateEq`, `stateSetoid` — equality of denotation; the state as a quotient.

## Main results

* `amp_pos`, `amp_neg`, `mem_support_iff` — the two branches of `amp` and the coset form of the
  support.
* `amp_add_C`, `amp_offset_add_mem`, `amp_congr_xProj`, `amp_zeroZ`, `amp_congr_support`,
  `amp_rename_bound` — the gauge rewrites R1–R5.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The frame-side amplitude -/

open Classical in
/-- The support-restricted amplitude of a carrier state: `ampCore` on the support coset, zero off
it. The frame-layer twin of the Hilbert-housed `F`; `KernelState.psi` at `h = 0`. -/
noncomputable def amp (S : KernelSumState n) (w : Fin n → ZMod 2) : ℂ :=
  if ∃ p ∈ S.L, w = S.x₀ + p.X then ampCore S.m S.h S.Q S.c w else 0

/-- `amp` on support is the raw amplitude. -/
theorem amp_pos {S : KernelSumState n} {w : Fin n → ZMod 2}
    (hw : ∃ p ∈ S.L, w = S.x₀ + p.X) : amp S w = ampCore S.m S.h S.Q S.c w := by
  unfold amp
  exact if_pos hw

/-- `amp` off support is zero. -/
theorem amp_neg {S : KernelSumState n} {w : Fin n → ZMod 2}
    (hw : ¬ ∃ p ∈ S.L, w = S.x₀ + p.X) : amp S w = 0 := by
  unfold amp
  exact if_neg hw

/-- Support membership is membership of `w − x₀` in the X-shadow — the coset form in which the
support half of the Hadamard rules (`shadow_swap_eq`, `branch_unique`) is stated. -/
theorem mem_support_iff (S : KernelSumState n) (w : Fin n → ZMod 2) :
    (∃ p ∈ S.L, w = S.x₀ + p.X) ↔ w - S.x₀ ∈ Submodule.map xProj S.L := by
  constructor
  · rintro ⟨p, hp, hw⟩
    refine Submodule.mem_map.mpr ⟨p, hp, ?_⟩
    rw [xProj_apply, hw]
    abel
  · intro h
    obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp h
    refine ⟨p, hp, ?_⟩
    rw [xProj_apply] at hpX
    rw [hpX]
    abel

/-! ## Equality of denotation -/

/-- Two records are the same state when their denotations agree. -/
def StateEq (S T : KernelSumState n) : Prop := amp S = amp T

/-- `StateEq` is reflexive. -/
theorem StateEq.refl (S : KernelSumState n) : StateEq S S := rfl

/-- `StateEq` is symmetric. -/
theorem StateEq.symm {S T : KernelSumState n} (h : StateEq S T) : StateEq T S := Eq.symm h

/-- `StateEq` is transitive. -/
theorem StateEq.trans {S T U : KernelSumState n} (h₁ : StateEq S T) (h₂ : StateEq T U) :
    StateEq S U := Eq.trans h₁ h₂

/-- The state type is the quotient of records by the kernel of `amp`. -/
noncomputable def stateSetoid (n : ℕ) : Setoid (KernelSumState n) := Setoid.ker amp

/-- The setoid's relation is `StateEq`. -/
theorem stateSetoid_rel (S T : KernelSumState n) : stateSetoid n S T ↔ StateEq S T := Iff.rfl

/-! ## R1 — the constant term of the exponent against the scale -/

/-- Adding a constant `a` to the exponent multiplies `ampCore` by the phase
`exp(i·2π·a.val/2^m)`. -/
theorem ampCore_add_C {m h : ℕ} (Q : DiagPhase (n + h) m) (a : ZMod (2 ^ m)) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m h (Q + MvPolynomial.C a) c w
      = ampCore m h Q
          (c * Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)))
          w := by
  unfold ampCore
  have hterm : ∀ y : Fin h → ZMod 2,
      Complex.exp (Complex.I *
          (DiagPhase.realPhase (Q + MvPolynomial.C a) (Fin.append w y) : ℂ))
        = Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ))
          * Complex.exp (Complex.I * (DiagPhase.realPhase Q (Fin.append w y) : ℂ)) := by
    intro y
    rw [exp_realPhase_add]
    have hC : DiagPhase.realPhase (MvPolynomial.C a : DiagPhase (n + h) m) (Fin.append w y)
        = 2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m := by
      unfold DiagPhase.realPhase DiagPhase.eval
      rw [MvPolynomial.eval_C]
    rw [hC, mul_comm]
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum]
  ring

/-- **R1.** The constant `a` in the exponent and the matching phase on `c` are the same state. -/
theorem amp_add_C {m h : ℕ} (Q : DiagPhase (n + h) m) (a : ZMod (2 ^ m)) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    amp (⟨m, h, Q + MvPolynomial.C a, c, L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q,
          c * Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)),
          L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨m, h, Q + MvPolynomial.C a, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨m, h, Q,
        c * Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)),
        L, x₀⟩ : KernelSumState n)) hw]
    exact ampCore_add_C Q a c w
  · rw [amp_neg (S := (⟨m, h, Q + MvPolynomial.C a, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := (⟨m, h, Q,
        c * Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)),
        L, x₀⟩ : KernelSumState n)) hw]

/-! ## R2 — the offset modulo the shadow -/

/-- **R2.** Translating `x₀` by a shadow vector `v ∈ π_X(L)` leaves `amp` fixed. -/
theorem amp_offset_add_mem {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    {v : Fin n → ZMod 2} (hv : v ∈ Submodule.map xProj L) :
    amp (⟨m, h, Q, c, L, x₀ + v⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) := by
  obtain ⟨p₀, hp₀, hp₀X⟩ := Submodule.mem_map.mp hv
  rw [xProj_apply] at hp₀X
  have hvv : v + v = 0 := by
    funext j
    exact (show ∀ x : ZMod 2, x + x = 0 by decide) (v j)
  funext w
  have hiff : (∃ p ∈ L, w = x₀ + v + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X) := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p₀ + p, Submodule.add_mem _ hp₀ hp, ?_⟩
      rw [X_add, hp₀X]
      abel
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p₀ + p, Submodule.add_mem _ hp₀ hp, ?_⟩
      rw [X_add, hp₀X, show x₀ + v + (v + p.X) = x₀ + (v + v) + p.X from by abel, hvv]
      abel
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨m, h, Q, c, L, x₀ + v⟩ : KernelSumState n)) (hiff.mpr hw),
      amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
  · rw [amp_neg (S := (⟨m, h, Q, c, L, x₀ + v⟩ : KernelSumState n)) (fun hc => hw (hiff.mp hc)),
      amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

/-! ## R3 — the Z-part of `L` -/

/-- **R3.** `amp` reads `L` only through its X-shadow: two lifts with the same shadow give the same
denotation. -/
theorem amp_congr_xProj {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (L L' : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (hsh : Submodule.map xProj L = Submodule.map xProj L') :
    amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L', x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · have h1 : w - x₀ ∈ Submodule.map xProj L :=
      (mem_support_iff (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) w).mp hw
    rw [hsh] at h1
    have h2 : ∃ p ∈ L', w = x₀ + p.X :=
      (mem_support_iff (⟨m, h, Q, c, L', x₀⟩ : KernelSumState n) w).mpr h1
    rw [amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨m, h, Q, c, L', x₀⟩ : KernelSumState n)) h2]
  · have h2 : ¬ ∃ p ∈ L', w = x₀ + p.X := by
      intro hc
      have h3 : w - x₀ ∈ Submodule.map xProj L' :=
        (mem_support_iff (⟨m, h, Q, c, L', x₀⟩ : KernelSumState n) w).mp hc
      rw [← hsh] at h3
      exact hw ((mem_support_iff (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) w).mpr h3)
    rw [amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := (⟨m, h, Q, c, L', x₀⟩ : KernelSumState n)) h2]

/-- Erase the Z-block of every Pauli: the extreme change of the Z-part of `L`. -/
def zeroZ : Pauli n →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨p.X, 0⟩
  map_add' p q := by apply Pauli.ext <;> simp
  map_smul' a p := by apply Pauli.ext <;> simp

/-- Erasing the Z-blocks does not change the X-shadow. -/
theorem map_xProj_zeroZ (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map xProj (Submodule.map zeroZ L) = Submodule.map xProj L := by
  rw [← Submodule.map_comp]
  have hc : (xProj : Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2)).comp zeroZ = xProj :=
    LinearMap.ext (fun p => rfl)
  rw [hc]

/-- **R3, the extreme case.** Erasing the whole Z-block of `L` does not move `amp`. -/
theorem amp_zeroZ {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    amp (⟨m, h, Q, c, Submodule.map zeroZ L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) :=
  amp_congr_xProj Q c _ _ x₀ (map_xProj_zeroZ L)

/-! ## R4 — the exponent off the support coset -/

/-- `ampCore` at a word reads the exponent only at that word's bound extensions. -/
theorem ampCore_congr {m h : ℕ} {Q Q' : DiagPhase (n + h) m} (c : ℂ) {w : Fin n → ZMod 2}
    (hQ : ∀ y : Fin h → ZMod 2,
      DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w y)) :
    ampCore m h Q' c w = ampCore m h Q c w := by
  unfold ampCore
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold DiagPhase.realPhase
  rw [hQ y]

/-- **R4.** Two exponents that agree on the support coset (at every bound word) give the same
denotation: the exponent off the coset is gauge. -/
theorem amp_congr_support {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
      DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w y)) :
    amp (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
    exact ampCore_congr c (hQ w hw)
  · rw [amp_neg (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

/-! ## R5 — relabelling the bound register -/

/-- `ampCore` is invariant under any bijection of the bound words carried by the exponent. -/
theorem ampCore_reindex {m h : ℕ} {Q Q' : DiagPhase (n + h) m} (c : ℂ)
    (σ : (Fin h → ZMod 2) ≃ (Fin h → ZMod 2)) {w : Fin n → ZMod 2}
    (hQ : ∀ y : Fin h → ZMod 2,
      DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w (σ y))) :
    ampCore m h Q' c w = ampCore m h Q c w := by
  unfold ampCore
  congr 1
  rw [← Equiv.sum_comp σ
    (fun y => Complex.exp (Complex.I * (DiagPhase.realPhase Q (Fin.append w y) : ℂ)))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  unfold DiagPhase.realPhase
  rw [hQ y]

/-- **R5.** An exponent that reads the bound register through a bijection of its words gives the
same denotation: the labelling of the bound register is gauge. -/
theorem amp_rename_bound {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (σ : (Fin h → ZMod 2) ≃ (Fin h → ZMod 2))
    (hQ : ∀ w : Fin n → ZMod 2, ∀ y : Fin h → ZMod 2,
      DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w (σ y))) :
    amp (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)
      = amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
    exact ampCore_reindex c σ (hQ w)
  · rw [amp_neg (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

end FTQCLib.Frame.Walkthrough

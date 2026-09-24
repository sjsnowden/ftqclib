/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.BooleanMobius
import FTQCLib.Hierarchy.FuncDeriv
import FTQCLib.Bridge.EffectiveLevelIterate
import FTQCLib.Explore.CubicPolarization
import ECCLib.Derivative
import ECCLib.Polynomial
import ECCLib.PhaseObstruction
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

set_option linter.style.longLine false

/-!
# The FTQCLib ↔ ECCLib bridge

The machine-checked link between the frame's own discrete-difference / degree machinery and the
standalone `ECCLib` library (higher-order Fourier analysis). Cross-library import runs one way
(`FTQCLib → ECCLib → Mathlib`), so `ECCLib` stays pure and liftable.

**The atomic identification.** The frame's discrete derivative `funcDerivG i` *is* Mathlib /
ECCLib's forward difference `fwdDiff` in the standard-basis direction `eᵢ = Pi.single i 1`
(`funcDerivG_eq_fwdDiff`, definitional), and the frame's `funcDerivSubset` is `iteratedFwdDiff` over the
mapped basis directions (`funcDerivSubset_eq_iteratedFwdDiff`). This turns "the frame happens to use the
same `Δ_h` as HOF" into a *shared object*: every frame result phrased via `funcDerivG` becomes,
definitionally, a statement about `iteratedFwdDiff`, and the frame inherits `fwdDiff_comm`, the 2-torsion
collapse, and the degree-drop lemmas as HOF instances rather than re-proofs.

**Concrete gate phases as HOF nonclassical polynomials.** The frame's `T`-gate phase
`tFn = |v₀|`
over `ZMod 8` is a ECCLib nonclassical polynomial of degree ≤ 3 (`tFn_isPolyDegLE_three`), and hence
*saturates* the Gowers `U^4` norm (`tFn_gowersNorm_eq_one`): a frame gate phase realized as a HOF object
whose degree = its frame level and whose norm reading is the `PhaseObstruction` saturation. This is the
first point where ECCLib's downstream theory (`PhaseObstruction` / `DualObstruction`) attaches to
the frame's actual gates, and a fidelity check that the abstract machinery returns the right degree on
them.

The general **unit-directions reduction** is built on the ECCLib side
(`ECCLib.isPolyDegLE_of_unitDirections`, `Polynomial.lean`): over `𝔽₂`, degree `≤ d` need only be
checked on the `n` standard-basis directions (with repetition), which are the frame's `funcDerivG`. As a
first consumer, `tFn_isPolyDegLE_three_via_reduction` re-derives the `T`-phase's degree by feeding the frame
probe `tCubic_fourthDiff` through that reduction — the general HOF theorem taking a frame gate as input.

**The general degree theorem.** `eval_isPolyDegLE_effectiveLevel` proves
`IsPolyDegLE (effectiveLevel P) (P.eval)` for every multilinear `P`, not only for a single gate. It
supplies the reduction's hypothesis from the frame's `effectiveLevel` strict-drop
(`shiftDeriv_effectiveLevel_lt`), iterated once `shiftDeriv` is shown to preserve multilinearity
(`FTQCLib/Bridge/EffectiveLevelIterate.lean`). This is what makes `level` an intrinsic
difference-theoretic invariant of the gate rather than a formula read off the polynomial.
-/

namespace FTQCLib.Bridge

open FTQCLib.Hierarchy FTQCLib.Hierarchy.BooleanMobius FTQCLib.Explore.CubicPolarization ECCLib

/-! ## The atomic identification -/

/-- **The frame's discrete derivative is the HOF forward difference** in the standard-basis direction:
`funcDerivG i f = fwdDiff (eᵢ) f`, definitionally (both are `fun v => f (v + eᵢ) − f v`). -/
lemma funcDerivG_eq_fwdDiff {A : Type*} [AddCommGroup A] {n : ℕ} (i : Fin n)
    (f : (Fin n → ZMod 2) → A) :
    funcDerivG i f = fwdDiff (Pi.single i (1 : ZMod 2)) f := rfl

/-- **The frame's iterated subset-derivative is `iteratedFwdDiff`** over the mapped basis directions. -/
lemma funcDerivSubset_eq_iteratedFwdDiff {A : Type*} [AddCommGroup A] {n : ℕ}
    (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → A) :
    funcDerivSubset S f = iteratedFwdDiff (S.toList.map (fun i => Pi.single i (1 : ZMod 2))) f := by
  rw [funcDerivSubset, iteratedFwdDiff, List.foldr_map]
  rfl

/-! ## The `T`-gate phase as a HOF nonclassical polynomial -/

/-- **The frame's `T`-gate phase is a ECCLib nonclassical polynomial of degree ≤ 3.** For every
tuple of four directions the fourth forward difference of `tFn` vanishes: over `Fin 1` each direction is
`0` or `e₀`, so either a `0` kills the difference or all four are `e₀` and `tCubic_fourthDiff` applies. -/
theorem tFn_isPolyDegLE_three : IsPolyDegLE 3 tFn := by
  have hcases : ∀ a : Fin 1 → ZMod 2, a = 0 ∨ a = Pi.single (0 : Fin 1) (1 : ZMod 2) := by decide
  intro ys
  by_cases h : ∀ j, ys j = Pi.single (0 : Fin 1) (1 : ZMod 2)
  · rw [show ys = (fun _ => Pi.single (0 : Fin 1) (1 : ZMod 2)) from funext h]
    funext v
    exact tCubic_fourthDiff v
  · rw [not_forall] at h
    obtain ⟨j, hj⟩ := h
    rcases hcases (ys j) with h0 | he
    · exact iteratedFwdDiff_eq_zero_of_zero_mem tFn (by rw [List.mem_ofFn']; exact ⟨j, h0⟩)
    · exact absurd he hj

/-- **The same degree bound through the general unit-directions reduction.** Rather than case-splitting
directly, feed the frame's own top-difference law `tCubic_fourthDiff` into the Aichinger–Moosbauer reduction
`isPolyDegLE_of_unitDirections`: it suffices to check the fourth difference along the single standard-basis
direction `e₀` (over `Fin 1` every direction *is* `e₀`), which is exactly the frame probe. This is the
end-to-end integration test — the general ECCLib reduction consuming a frame gate phase. -/
theorem tFn_isPolyDegLE_three_via_reduction : IsPolyDegLE 3 tFn := by
  apply isPolyDegLE_of_unitDirections
  intro is
  rw [Subsingleton.elim is (fun _ => (0 : Fin 1))]
  funext v
  simp only [List.ofFn_succ, List.ofFn_zero, iteratedFwdDiff_cons, iteratedFwdDiff_nil,
    ← funcDerivG_eq_fwdDiff]
  exact tCubic_fourthDiff v

/-- **The `T`-gate phase saturates the Gowers `U^4` norm.** Composing `tFn` with any degree-8 additive
character `ψ` of `ZMod 8` (`ζ^8 = 1`), `‖ψ ∘ tFn‖_{U^4} = 1` — the `PhaseObstruction` reading that a
degree-3 phase is a genuine obstruction to `U^4`-uniformity, now on the frame's own `T` gate. The
intended `ψ` is the primitive character `ζ = e^{2πi/8}`; the statement holds for any `ζ^8 = 1`. -/
theorem tFn_gowersNorm_eq_one {ζ : ℂ} (hζ : ζ ^ 8 = 1) :
    gowersNorm 4 (fun v => (AddChar.zmodChar 8 hζ) (tFn v)) = 1 := by
  have hnormζ : ‖ζ‖ = 1 := by
    have h8 : ‖ζ‖ ^ 8 = 1 := by rw [← norm_pow, hζ, norm_one]
    rcases lt_trichotomy ‖ζ‖ 1 with h | h | h
    · exact absurd h8 (pow_lt_one₀ (norm_nonneg ζ) h (by norm_num)).ne
    · exact h
    · exact absurd h8 (one_lt_pow₀ h (by norm_num)).ne'
  have hunit : ∀ t : ZMod 8,
      star ((AddChar.zmodChar 8 hζ) t) = (AddChar.zmodChar 8 hζ) (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv]
    have hnt : ‖(AddChar.zmodChar 8 hζ) t‖ = 1 := by
      rw [AddChar.zmodChar_apply, norm_pow, hnormζ, one_pow]
    rw [show (star ((AddChar.zmodChar 8 hζ) t) : ℂ)
          = (starRingEnd ℂ) ((AddChar.zmodChar 8 hζ) t) from rfl]
    exact (Complex.inv_eq_conj hnt).symm
  exact gowersNorm_addChar_comp_eq_one (AddChar.zmodChar 8 hζ) hunit tFn_isPolyDegLE_three

/-! ## The general degree-equals-`effectiveLevel` theorem

The general statement: **every multilinear diagonal phase `P`
has nonclassical degree `≤ effectiveLevel P`.** Route: the frame's `effectiveLevel` strict-drop, iterated
(`shiftDeriv_foldr_eq_zero_of_lt`, `EffectiveLevelIterate.lean`), gives that every `(effectiveLevel P + 1)`-fold
`shiftDeriv` composition is the zero polynomial; the poly↔function bridge (`shiftDeriv_eval_eq_funcDerivEval` +
`funcDerivG_eq_funcDeriv` + `funcDerivG_eq_fwdDiff`) turns that into vanishing of every
`(effectiveLevel P + 1)`-fold basis-direction forward difference of `eval P`; the built unit-directions reduction
`isPolyDegLE_of_unitDirections` then upgrades it to *all* directions. This is what makes `level` an intrinsic
difference-theoretic invariant of the gate rather than a formula read off the polynomial. -/

/-- **The frame's discrete derivative on `eval P` is realised by the polynomial `shiftDeriv`:**
`funcDerivG i (P.eval) = (shiftDeriv i P).eval`. -/
lemma funcDerivG_eval_eq_eval_shiftDeriv (i : Fin n) (Q : DiagPhase n m) :
    funcDerivG i Q.eval = (DiagPhase.shiftDeriv i Q).eval := by
  funext v
  rw [funcDerivG_eq_funcDeriv, DiagPhase.shiftDeriv_eval_eq_funcDerivEval]
  rfl

/-- An iterated forward difference of `eval P` over basis directions is the `eval` of the corresponding
`shiftDeriv` composition. -/
lemma iteratedFwdDiff_basis_eq_eval_foldr (P : DiagPhase n m) (l : List (Fin n)) :
    iteratedFwdDiff (l.map (fun i => Pi.single i (1 : ZMod 2))) P.eval
      = (l.foldr DiagPhase.shiftDeriv P).eval := by
  induction l with
  | nil => rw [List.map_nil, iteratedFwdDiff_nil, List.foldr_nil]
  | cons i is ih =>
    rw [List.map_cons, iteratedFwdDiff_cons, ih, List.foldr_cons,
      ← funcDerivG_eq_fwdDiff, funcDerivG_eval_eq_eval_shiftDeriv]

/-- **The general degree theorem.** Every multilinear diagonal phase `P` has HOF nonclassical
degree `≤ effectiveLevel P`: `IsPolyDegLE (effectiveLevel P) (P.eval)`, for *every* gate, not just
the single `T`-gate instance. The converse bound, and hence equality for multilinear `P` with no
constant term, is `eval_isPolyDegLE_iff` in `FTQCLib/Bridge/G1Converse.lean`. -/
theorem eval_isPolyDegLE_effectiveLevel (P : DiagPhase n m)
    (hP : DiagPhase.IsMultilinear P) :
    IsPolyDegLE (DiagPhase.effectiveLevel P) P.eval := by
  apply isPolyDegLE_of_unitDirections
  intro is
  have hmap : List.ofFn (fun j => Pi.single (is j) (1 : ZMod 2))
      = (List.ofFn is).map (fun i => Pi.single i (1 : ZMod 2)) := by
    rw [List.map_ofFn, Function.comp_def]
  rw [hmap, iteratedFwdDiff_basis_eq_eval_foldr,
    shiftDeriv_foldr_eq_zero_of_lt P hP _ (by rw [List.length_ofFn]; omega)]
  funext v; simp [DiagPhase.eval]

end FTQCLib.Bridge

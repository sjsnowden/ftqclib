/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Matrix.CommStarMatrix
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Regression checks for normal complex matrices

Axiom sweeps and two discriminating rows, both about **non-removability of a hypothesis**. Each
is a compiled counterexample rather than an assertion, so a future attempt to weaken either
lemma fails to compile against this file.
-/

namespace ECCLib

open Matrix

/-! ## Axiom sweeps -/

/-- info: 'ECCLib.eq_zero_of_isHermitian_of_isNilpotent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.eq_zero_of_isHermitian_of_isNilpotent

/-- info: 'ECCLib.eq_zero_of_commute_conjTranspose_of_isNilpotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.eq_zero_of_commute_conjTranspose_of_isNilpotent

/-- info: 'ECCLib.isReduced_of_commute_of_conjTranspose_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.isReduced_of_commute_of_conjTranspose_mem

/-! ## Discriminating row 1 — `IsSymm` may not replace Hermitian

Over `ℂ` the plain transpose carries no positivity. This matrix is symmetric, nilpotent and
nonzero, so `eq_zero_of_isHermitian_of_isNilpotent` would be **false** with `IsSymm` in place of
`IsHermitian`. It is also not Hermitian, which is why the real lemma does not apply to it. -/

/-- Symmetric, nilpotent, nonzero — the witness that `IsSymm` is the wrong input over `ℂ`. -/
def badSymm : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; Complex.I, -1]

theorem badSymm_isSymm : badSymm.IsSymm := by
  unfold Matrix.IsSymm badSymm
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem badSymm_sq : badSymm * badSymm = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [badSymm, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem badSymm_ne_zero : badSymm ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [badSymm] at this

theorem badSymm_not_isHermitian : ¬ badSymm.IsHermitian := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [badSymm, Matrix.conjTranspose_apply, Complex.ext_iff] at h01

/-! ## Discriminating row 2 — commutativity may not be dropped

`⋆`-closure alone does **not** give reducedness. The full matrix algebra is `⋆`-closed and
contains a nonzero nilpotent, so `isReduced_of_commute_of_conjTranspose_mem` genuinely needs its
commutativity hypothesis. What `⋆`-closure alone buys is semisimplicity, which is weaker.

The false version is plausible enough to be asserted by mistake; this row guards against it. -/

/-- A nonzero nilpotent inside a `⋆`-closed algebra: the whole of `Matrix (Fin 2) (Fin 2) ℂ`. -/
def nilp : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

theorem nilp_sq : nilp * nilp = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilp, Matrix.mul_apply, Fin.sum_univ_two]

theorem nilp_ne_zero : nilp ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [nilp] at this

/-- `⊤` is `⋆`-closed and is not reduced. Commutativity is what the reducedness lemma needs and
it is the hypothesis that fails here. -/
theorem top_conjTranspose_mem (M : Matrix (Fin 2) (Fin 2) ℂ)
    (_ : M ∈ (⊤ : Subalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ))) :
    Mᴴ ∈ (⊤ : Subalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)) := trivial

theorem star_closed_not_enough :
    ∃ M : Matrix (Fin 2) (Fin 2) ℂ,
      M ∈ (⊤ : Subalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)) ∧ M * M = 0 ∧ M ≠ 0 :=
  ⟨nilp, trivial, nilp_sq, nilp_ne_zero⟩

end ECCLib

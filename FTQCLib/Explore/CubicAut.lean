/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Explore.CubicPolarization
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option linter.style.longLine false

/-! # `Aut(T)` of the cubic form collapses to `GL(3,𝔽₂)`

The polarized `CCZ` cubic on `𝔽₂³` is the determinant form, whose stabilizer over `𝔽₂` is *all* of
`GL(3,𝔽₂)` (not a proper "higher-symplectic" subgroup) — a char-2 degeneracy, consistent with
Magaard–Savin. This file proves it.

* `cubicForm_eq_det` (`decide`) — the full trilinear **polarization** of `cczFn` (`v ↦ v₀v₁v₂`) **is** the `3×3`
  determinant form.
* `zmod2_isUnit_eq_one` — over `𝔽₂` the only unit is `1`, so **every** invertible matrix has determinant `1`.
* `cubicForm_gl_invariant` — hence every `M` with `IsUnit M.det` (i.e. every `M ∈ GL(3,𝔽₂)`) stabilizes the cubic
  form: `det(Mu | Mv | Mw) = det M · det(u | v | w) = det(u | v | w)`. The stabilizer is all of `GL(3,𝔽₂)` — the
  determinant cuts out **nothing**, unlike `Sp = Aut(ω)`. So the naive "symmetry-group-of-the-cubic = higher-Sp"
  route degenerates over `𝔽₂`.

An exploratory file (not part of the `FTQCLib` target); see `FTQCLib/Explore/README.md`.
-/

namespace FTQCLib.Explore.CubicAut

open FTQCLib.Explore.CubicPolarization

/-- The full **trilinear polarization** of a cubic phase `P` on `𝔽₂³` (inclusion–exclusion / third difference in
arbitrary directions). Over `ZMod 2` every sign is `+`. -/
def cubicPolar (P : (Fin 3 → ZMod 2) → ZMod 2) (u v w : Fin 3 → ZMod 2) : ZMod 2 :=
  P (u + v + w) - P (u + v) - P (u + w) - P (v + w) + P u + P v + P w - P 0

/-- `det(u | v | w)`, the `3×3` determinant form (explicit Laplace expansion; over `ZMod 2` all signs are `+`).
Equals `det` of the matrix with rows `u, v, w` (hence, by transpose-invariance, of the column matrix). -/
def cubicDet (u v w : Fin 3 → ZMod 2) : ZMod 2 :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- **The polarized `CCZ` cubic IS the determinant form.** The full trilinear polarization
of `v ↦ v₀v₁v₂` equals `det(u | v | w)` on all of `𝔽₂³`. -/
theorem cubicForm_eq_det : ∀ u v w, cubicPolar cczFn u v w = cubicDet u v w := by
  decide

/-- **Over `𝔽₂` the only unit is `1`.** So every invertible matrix has determinant `1`. -/
theorem zmod2_isUnit_eq_one {d : ZMod 2} (h : IsUnit d) : d = 1 := by
  fin_cases d
  · exact absurd rfl h.ne_zero
  · rfl

/-- The determinant form transforms by `det M` under a linear map `M` acting on the columns:
`det(Mu | Mv | Mw) = det M · det(u | v | w)`. -/
theorem cubicDet_mulVec (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (u v w : Fin 3 → ZMod 2) :
    cubicDet (M.mulVec u) (M.mulVec v) (M.mulVec w) = M.det * cubicDet u v w := by
  simp only [cubicDet, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three]
  ring

/-- **The cubic form's stabilizer is all of `GL(3,𝔽₂)` — the char-2 collapse.** Every invertible `M` fixes the
determinant form, so `Aut = GL(3,𝔽₂)`: the determinant cuts out no proper subgroup (contrast `Sp = Aut(ω)`). -/
theorem cubicForm_gl_invariant (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hM : IsUnit M.det)
    (u v w : Fin 3 → ZMod 2) :
    cubicPolar cczFn (M.mulVec u) (M.mulVec v) (M.mulVec w) = cubicPolar cczFn u v w := by
  rw [cubicForm_eq_det, cubicForm_eq_det, cubicDet_mulVec, zmod2_isUnit_eq_one hM, one_mul]

end FTQCLib.Explore.CubicAut

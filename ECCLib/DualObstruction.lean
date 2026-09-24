/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GowersNorm
import ECCLib.PhaseObstruction
import ECCLib.Polynomial

set_option linter.style.longLine false

/-!
# Polynomial phases have dual norm ≤ 1 — the correlation obstruction

`PhaseObstruction` shows that a degree-`≤s` polynomial phase `e(P)` *saturates* the Gowers norm:
`‖e(P)‖_{U^{s+1}} = 1`. This file proves the **complementary, correlation-direction** statement — that
`e(P)` is a *test function of dual norm at most `1`*: correlating with it lower-bounds `‖·‖_{U^{s+1}}`.

This is the phase-polynomial case of the "tightness" results of Candela–González-Sánchez–Szegedy
(*On the inverse theorem for Gowers norms in abelian groups of bounded torsion*, arXiv:2311.13899):

* `correlation_le_gowersNorm` = **`lem:dualnormbound`**: `‖e(P)‖_{U^{s+1}}^* ≤ 1`, in the operational form
  `‖𝔼[f · \overline{e(P)}]‖ ≤ ‖f‖_{U^{s+1}}` for `deg P ≤ s` (unfolding the dual norm as a supremum over `f`).
* `phasePoly_obstruction` = **`prop:propolyobstruct`**: `|⟨f, e(P)⟩| ≥ δ ⟹ ‖f‖_{U^{s+1}} ≥ δ`.

The proof is the paper's, restricted to a genuine phase polynomial (the general statement is for a
*projected* phase polynomial `φ_{*τ}`, a pushforward along a surjective homomorphism `τ` — that layer needs
Gowers-norm pullback-invariance `‖g∘τ‖ = ‖g‖` and is not formalized here):

`‖𝔼[f · \overline{e(P)}]‖ = ‖f · \overline{e(P)}‖_{U¹} ≤ ‖f · \overline{e(P)}‖_{U^{s+1}} = ‖f‖_{U^{s+1}}`,

the three steps being the **U¹ identity** (`gowersNorm_one`), **monotonicity** (`gowersNorm_mono`), and
**phase-multiplication invariance** (`gowersNorm_mul_phase`) — the last because the `(s+1)`-fold
multiplicative derivative of a degree-`≤s` phase is the constant `1` (`PhaseObstruction`'s mechanism, made
multiplicative here via `iterMderiv_mul`). Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V] {G : Type*} [AddCommGroup G]

/-- The multiplicative derivative is multiplicative: `∂_h(f·g) = ∂_h f · ∂_h g`. -/
lemma mderiv_mul (h : V) (f g : V → ℂ) : mderiv h (f * g) = mderiv h f * mderiv h g := by
  funext x; simp only [mderiv, Pi.mul_apply, star_mul']; ring

/-- The iterated multiplicative derivative is multiplicative. -/
lemma iterMderiv_mul (hs : List V) (f g : V → ℂ) :
    iterMderiv hs (f * g) = iterMderiv hs f * iterMderiv hs g := by
  induction hs with
  | nil => rfl
  | cons h hs ih => rw [iterMderiv_cons, iterMderiv_cons, iterMderiv_cons, ih, mderiv_mul]

/-- `IsPolyDegLE` is closed under negation. -/
theorem IsPolyDegLE.neg {d : ℕ} {P : V → G} (h : IsPolyDegLE d P) :
    IsPolyDegLE d (fun x => -(P x)) := by
  intro ys
  rw [show (fun x => -(P x)) = (⇑(-AddMonoidHom.id G)) ∘ P from rfl,
      iteratedFwdDiff_comp_addMonoidHom, h ys]
  funext x; simp

/-- **The `(s+1)`-fold multiplicative derivative of a degree-`≤s` phase is the constant `1`.** -/
lemma iterMderiv_phase_one (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) (ys : Fin (s + 1) → V) :
    iterMderiv (List.ofFn ys) (fun x => ψ (P x)) = 1 := by
  rw [iterMderiv_addChar_comp ψ hψ]
  funext x
  rw [congrFun (hP ys) x]
  simp [AddChar.map_zero_eq_one]

variable [Fintype V]

/-- **Phase-multiplication invariance (inner product).** Multiplying by a degree-`≤s` phase leaves the
Gowers inner product of order `s+1` unchanged. -/
lemma gowersInner_mul_phase (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) (f : V → ℂ) :
    gowersInner (s + 1) (f * (fun x => ψ (P x))) = gowersInner (s + 1) f := by
  rw [gowersInner, gowersInner]
  refine Finset.expect_congr rfl (fun p _ => ?_)
  rw [iterMderiv_mul, iterMderiv_phase_one ψ hψ hP]
  simp

/-- **Phase-multiplication invariance (Gowers norm).** `‖f · e(P)‖_{U^{s+1}} = ‖f‖_{U^{s+1}}` for
`deg P ≤ s`. Multiplying by a degree-`≤s` phase is a `‖·‖_{U^{s+1}}`-isometry. -/
lemma gowersNorm_mul_phase (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) (f : V → ℂ) :
    gowersNorm (s + 1) (f * (fun x => ψ (P x))) = gowersNorm (s + 1) f := by
  rw [gowersNorm_eq, gowersNorm_eq, gowersInner_mul_phase ψ hψ hP]

/-- **The dual-norm bound** (Candela–González-Sánchez–Szegedy, `lem:dualnormbound`, phase-polynomial case):
`‖e(P)‖_{U^{s+1}}^* ≤ 1`, in operational form. The correlation of any `f` with a degree-`≤s` phase `e(P)`
is at most `‖f‖_{U^{s+1}}`. Via the `U¹` identity, monotonicity, and phase-multiplication invariance. -/
theorem correlation_le_gowersNorm (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) (f : V → ℂ) :
    ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (ψ (P x)))‖
      ≤ gowersNorm (s + 1) f := by
  have hconj : (fun x => f x * (starRingEnd ℂ) (ψ (P x))) = f * (fun x => ψ (-(P x))) := by
    funext x; simp only [Pi.mul_apply, starRingEnd_apply, hψ]
  rw [hconj]
  calc ‖Finset.expect Finset.univ (f * (fun x => ψ (-(P x))))‖
      = gowersNorm 1 (f * (fun x => ψ (-(P x)))) := (gowersNorm_one _).symm
    _ ≤ gowersNorm (s + 1) (f * (fun x => ψ (-(P x)))) := gowersNorm_mono (by omega) _
    _ = gowersNorm (s + 1) f := gowersNorm_mul_phase ψ hψ hP.neg f

/-- **The phase-polynomial obstruction** (Candela–González-Sánchez–Szegedy, `prop:propolyobstruct`,
phase-polynomial case): if `f` correlates with a degree-`≤s` phase to level `δ`, then `‖f‖_{U^{s+1}} ≥ δ`.
Together with `PhaseObstruction`'s `‖e(P)‖_{U^{s+1}} = 1`, this makes degree-`s` phases genuine, tight
obstructions to `U^{s+1}`-uniformity — both saturating the norm and detecting it. -/
theorem phasePoly_obstruction (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) (f : V → ℂ) {δ : ℝ}
    (hδ : δ ≤ ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (ψ (P x)))‖) :
    δ ≤ gowersNorm (s + 1) f :=
  hδ.trans (correlation_le_gowersNorm ψ hψ hP f)

end ECCLib

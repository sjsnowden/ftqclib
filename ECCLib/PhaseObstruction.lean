/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GowersNorm
import ECCLib.Polynomial
import Mathlib.Algebra.Group.AddChar

set_option linter.style.longLine false

/-!
# Polynomial phases are the Gowers-norm obstructions

An elementary fact: a phase `ψ ∘ P` of a polynomial `P` of degree `≤ s` **saturates** the Gowers norm,
`‖ψ ∘ P‖_{U^{s+1}} = 1`. So degree-`s` polynomial phases are obstructions to `U^{s+1}`-uniformity — the
extremal, maximally non-uniform functions at level `s+1`. It is the one-line computation every higher-order
Fourier text states before the hard work: the `(s+1)`-fold difference of a degree-`s` polynomial is `0`.

The deep converse is the actual *inverse theorem* (Green–Tao–Ziegler; in the bounded-torsion `ℤ/2^m` setting,
Candela–González-Sánchez–Szegedy): that these phases are, approximately, the **only** obstructions
(`‖f‖_{U^{s+1}}` large ⟹ `f` correlates with a degree-`s` phase). It is a long, hard theorem (GTZ ≈ 116 pp; the
bounded-torsion nilspace version ≈ 26 pp) built on nilsequence / nilspace structure theory — out of scope here.

The mechanism is a clean bridge between the two halves of the library: **the multiplicative derivative of a
phase is the phase of the additive derivative** — `∂_h (ψ ∘ Q) = ψ ∘ D_h Q` — so the Gowers product of `ψ ∘ P`
is `ψ` of an iterated additive difference of `P`, which vanishes exactly when `deg P ≤ s`. Mathlib-only;
FTQCLib-independent.
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V] {G : Type*} [AddCommGroup G]

/-- **The bridge (single step):** the multiplicative derivative of a phase is the phase of the additive
derivative. For a **unitary** additive character `ψ` (one with `conj (ψ t) = ψ (-t)`), `∂_h (ψ ∘ Q) = ψ ∘ D_h Q`. -/
lemma mderiv_addChar_comp (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t)) (h : V) (Q : V → G) :
    mderiv h (fun x => ψ (Q x)) = fun x => ψ (fwdDiff h Q x) := by
  funext x
  simp only [mderiv, fwdDiff]
  rw [hψ (Q x), ← AddChar.map_add_eq_mul, sub_eq_add_neg]

/-- **The bridge (iterated):** `∂_{h₁…h_k}(ψ ∘ P) = ψ ∘ D_{h₁…h_k} P`. -/
lemma iterMderiv_addChar_comp (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    (hs : List V) (P : V → G) :
    iterMderiv hs (fun x => ψ (P x)) = fun x => ψ (iteratedFwdDiff hs P x) := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    rw [iterMderiv_cons, ih, iteratedFwdDiff_cons, mderiv_addChar_comp ψ hψ]

variable [Fintype V]

/-- **Polynomial phases saturate the Gowers norm** (an elementary computation). If `P : V → G` has degree
`≤ s` and `ψ` is a unitary additive character, then `‖ψ ∘ P‖_{U^{s+1}} = 1`: the phase is maximally
non-uniform at level `s+1`, i.e. a genuine obstruction. The deep converse — that such phases are approximately
the *only* obstructions — is the inverse theorem, not proved here. -/
theorem gowersNorm_addChar_comp_eq_one (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) :
    gowersNorm (s + 1) (fun x => ψ (P x)) = 1 := by
  have hinner : gowersInner (s + 1) (fun x => ψ (P x)) = 1 := by
    rw [gowersInner]
    have h1 : ∀ p : V × (Fin (s + 1) → V),
        iterMderiv (List.ofFn p.2) (fun x => ψ (P x)) p.1 = 1 := by
      intro p
      have hbridge := congrFun (iterMderiv_addChar_comp ψ hψ (List.ofFn p.2) P) p.1
      have hz : iteratedFwdDiff (List.ofFn p.2) P p.1 = 0 := by
        have := congrFun (hP p.2) p.1; simpa using this
      rw [hbridge, hz, AddChar.map_zero_eq_one]
    haveI : Nonempty (V × (Fin (s + 1) → V)) := ⟨(0, 0)⟩
    simp only [h1]
    exact Finset.expect_const Finset.univ_nonempty 1
  rw [gowersNorm_eq, hinner, norm_one, Real.one_rpow]

end ECCLib

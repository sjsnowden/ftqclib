/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

/-!
# The Arf sum — the characteristic-2 evaluation of the sign layer

The frame carries the characteristic-2 sign layer as **data** (`χ`/`encodeE` the refinement,
`betaFrame` the ambient cocycle, `ArfComplement`'s `−2·D` the diagonal datum). This file supplies
the **evaluation** — theorems reading such a layer off as one number — stated abstractly. **It does
not instantiate them at the frame's objects**: nothing here mentions `encodeE`, `betaFrame` or
`ArfComplement`, and this file imports no `FTQCLib.*`.

For a quadratic refinement `Q` of a nondegenerate alternating form `ω` over `𝔽₂`,

  `∑_v (−1)^{Q(v)} = ±√|V|`,  the sign being the Arf invariant.

This is the characteristic-2 counterpart of the odd-characteristic Gauss layer, and it is
deliberately organised the same way as the Gauss-sum layer (`ECCLib/GaussSum.lean`):

* **magnitude first** — `arfSum_sq : S² = |V|`, the exact analogue of `quadGaussSum_sq`, proved by
  the same move (square the sum, reindex, apply character orthogonality). It needs **no basis and no
  Arf invariant**: only that `ω` is additive in its first argument and nondegenerate. `Q 0 = 0` and
  `ω u 0 = 0` need not be assumed — they follow from the refinement law together with that
  additivity.
* **definite sign second** — the harder half, requiring a hyperbolic decomposition, exactly as the
  definite Gauss sign did. **Stated on the standard model `κ → Hyp` only**: the reduction of a
  general nondegenerate alternating `(V, ω, Q)` to that model, and the basis-independence of the
  exponent `∑ᵢ Q(eᵢ)Q(fᵢ)` (i.e. that it *is* the Arf invariant rather than one basis-relative
  expression for it), are **not** proved here.

Why the characteristic-2 sum is a *replacement* for the odd-characteristic one rather than a
specialisation of it: in characteristic 2 the field's own squaring map is the Frobenius, its
polarization `2xy` vanishes, and the field-squaring Gauss sums are identically zero
(`ECCLib.quadGaussSum_char_two_eq_zero`). The quadratic datum has to be *supplied*, and this
sum is the evaluation of the supplied datum.

**Scope.** Over an *alternating* form the `ℤ/4` enhancements are forced even, so the value is the
real Arf sign `±2ⁿ` — the full `μ₈` (Brown) range needs a *non-alternating* symmetric form (see
Kirby–Taylor on `Pin⁻` structures and `ℤ/4` enhancements). This sum is not `μ₈`-valued.

The file depends on Mathlib only.
-/

namespace FTQCLib.ArfSum

/-! ## The sign character of `ZMod 2`

Stated as closed `∀`-facts so `decide` can discharge them — `decide` cannot see past a free
variable. -/

/-- `(−1)^b` for `b : ZMod 2`, valued in `ℤ`. -/
def sgn (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

@[simp] theorem sgn_zero : sgn 0 = 1 := rfl

theorem sgn_add : ∀ a b : ZMod 2, sgn (a + b) = sgn a * sgn b := by decide

theorem sgn_mul_self : ∀ b : ZMod 2, sgn b * sgn b = 1 := by decide

theorem sgn_eq_one_iff : ∀ b : ZMod 2, sgn b = 1 ↔ b = 0 := by decide

/-! ## Character orthogonality for `𝔽₂`-valued additive maps -/

variable {V : Type*} [AddCommGroup V] [Fintype V]

omit [Fintype V] in
/-- An additive `φ : V → ZMod 2` sends `0` to `0`. -/
theorem map_zero_of_add {φ : V → ZMod 2} (hφ : ∀ x y, φ (x + y) = φ x + φ y) : φ 0 = 0 := by
  have h := hφ 0 0
  rw [add_zero] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

/-- The sign character `v ↦ (−1)^{φ v}` of an additive `φ : V → ZMod 2`. -/
def sgnChar {φ : V → ZMod 2} (hφ : ∀ x y, φ (x + y) = φ x + φ y) : AddChar V ℤ where
  toFun v := sgn (φ v)
  map_zero_eq_one' := by rw [map_zero_of_add hφ, sgn_zero]
  map_add_eq_mul' x y := by rw [hφ, sgn_add]

/-- **Character orthogonality.** A nonzero additive `φ : V → ZMod 2` has half its values `0` and
half `1`, so its sign character sums to zero. -/
theorem sum_sgn_eq_zero {φ : V → ZMod 2} (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    (hne : ∃ u, φ u ≠ 0) : ∑ v : V, sgn (φ v) = 0 := by
  refine AddChar.sum_eq_zero_of_ne_one (ψ := sgnChar hφ) ?_
  obtain ⟨u, hu⟩ := hne
  intro hone
  refine hu ((sgn_eq_one_iff _).mp ?_)
  have h := congrArg (fun χ : AddChar V ℤ => χ u) hone
  simpa [sgnChar] using h

/-! ## The Arf sum -/

/-- The **Arf sum** `∑_v (−1)^{Q(v)}` of an `𝔽₂`-valued function on a finite abelian group. -/
def arfSum (Q : V → ZMod 2) : ℤ := ∑ v : V, sgn (Q v)

section Refinement

variable {Q : V → ZMod 2} {ω : V → V → ZMod 2}

omit [Fintype V] in
/-- A refinement sends `0` to `0`. -/
theorem refinement_map_zero (hQ : ∀ x y, Q (x + y) = Q x + Q y + ω x y) (hω0 : ω 0 0 = 0) :
    Q 0 = 0 := by
  have h := hQ 0 0
  rw [add_zero, hω0, add_zero] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

omit [Fintype V] in
/-- The form vanishes on the right at `0` — a consequence of the refinement law, not an extra
hypothesis. -/
theorem refinement_form_zero_right (hQ : ∀ x y, Q (x + y) = Q x + Q y + ω x y) (hQ0 : Q 0 = 0)
    (u : V) : ω u 0 = 0 := by
  have h := hQ u 0
  rw [add_zero, hQ0, add_zero] at h
  exact add_left_cancel (a := Q u) (by rw [add_zero]; exact h.symm)

/-- **The magnitude: `S² = |V|`, so `S = ±√|V|`.**

The characteristic-2 analogue of `quadGaussSum_sq`, by the same argument: square the sum, reindex
`v = u + w` so that the refinement law collapses `Q u + Q(u+w)` to `Q w + ω u w`, and apply
character orthogonality in `u`. Only the `w = 0` term survives, contributing `|V|`.

The hypotheses are weaker than the usual alternating/bilinear package: `ω` is used only additively
in its **first** argument, plus nondegeneracy. `Q 0 = 0` and `ω u 0 = 0` need not be assumed — they
follow from the refinement law **together with** that additivity (the chain grounds out in `hω`, not
in `hQ` alone). No claim is made that these hypotheses cannot be weakened further. -/
theorem arfSum_sq (hQ : ∀ x y, Q (x + y) = Q x + Q y + ω x y)
    (hω : ∀ u₁ u₂ w, ω (u₁ + u₂) w = ω u₁ w + ω u₂ w)
    (hnd : ∀ w : V, (∀ u, ω u w = 0) → w = 0) :
    arfSum Q ^ 2 = (Fintype.card V : ℤ) := by
  classical
  have hω0 : ω 0 0 = 0 := map_zero_of_add (φ := fun x => ω x 0) (fun x y => hω x y 0)
  have hQ0 : Q 0 = 0 := refinement_map_zero hQ hω0
  -- the `u`-slice: the refinement law collapses `Q u + Q (u + w)` to `Q w + ω u w`
  have key : ∀ u : V, ∑ v : V, sgn (Q u) * sgn (Q v) = ∑ w : V, sgn (Q w) * sgn (ω u w) := by
    intro u
    rw [← Equiv.sum_comp (Equiv.addLeft u) (fun v => sgn (Q u) * sgn (Q v))]
    refine Finset.sum_congr rfl fun w _ => ?_
    change sgn (Q u) * sgn (Q (u + w)) = sgn (Q w) * sgn (ω u w)
    rw [hQ u w, sgn_add, sgn_add]
    calc sgn (Q u) * (sgn (Q u) * sgn (Q w) * sgn (ω u w))
        = sgn (Q u) * sgn (Q u) * (sgn (Q w) * sgn (ω u w)) := by ring
      _ = sgn (Q w) * sgn (ω u w) := by rw [sgn_mul_self, one_mul]
  rw [sq, arfSum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, key]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single (0 : V)]
  · rw [hQ0, sgn_zero, one_mul]
    simp only [refinement_form_zero_right hQ hQ0, sgn_zero]
    simp
  · intro w _ hw
    refine mul_eq_zero_of_right _ (sum_sgn_eq_zero (φ := fun u => ω u w) (fun x y => hω x y w) ?_)
    by_contra hcon
    exact hw (hnd w fun u => not_not.mp fun hne => hcon ⟨u, hne⟩)
  · intro h
    exact absurd (Finset.mem_univ (0 : V)) h

/-- **The Arf sum is `±√|V|`**, in product form. -/
theorem arfSum_mul_self (hQ : ∀ x y, Q (x + y) = Q x + Q y + ω x y)
    (hω : ∀ u₁ u₂ w, ω (u₁ + u₂) w = ω u₁ w + ω u₂ w)
    (hnd : ∀ w : V, (∀ u, ω u w = 0) → w = 0) :
    arfSum Q * arfSum Q = (Fintype.card V : ℤ) := by
  rw [← sq]; exact arfSum_sq hQ hω hnd

/-- **The sign layer always evaluates to something.** Unlike the characteristic-2 *field-squaring*
Gauss sum — which is identically zero — the Arf sum never vanishes. This is the precise sense in
which the supplied quadratic datum carries the information the field no longer does. -/
theorem arfSum_ne_zero (hQ : ∀ x y, Q (x + y) = Q x + Q y + ω x y)
    (hω : ∀ u₁ u₂ w, ω (u₁ + u₂) w = ω u₁ w + ω u₂ w)
    (hnd : ∀ w : V, (∀ u, ω u w = 0) → w = 0) :
    arfSum Q ≠ 0 := by
  intro h
  have hsq := arfSum_sq hQ hω hnd
  rw [h, sq, mul_zero] at hsq
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hsq.symm

end Refinement


/-! ## Multiplicativity over an orthogonal decomposition

If the space splits orthogonally and `Q` splits with it, the Arf sum factorises. This is what turns
the two-dimensional base case into the general answer. -/

theorem sgn_sum {κ : Type*} (s : Finset κ) (f : κ → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi, sgn_add, ih]

/-- **Multiplicativity over a homogeneous power.** For `κ` copies of a *single* group `W` and a `Q`
splitting coordinatewise as `∑ᵢ Qᵢ`, the Arf sum is the product of the factors' Arf sums. The
dependent case `Πᵢ Wᵢ` with different summands is not proved.

Note the statement needs **no** orthogonality, refinement or form hypothesis — it holds for an
arbitrary family `Q : κ → W → ZMod 2` and is a Fubini/expansion identity. Orthogonality is what
makes `Q` split in the intended application; it does no work in this proof. -/
theorem arfSum_pi {κ : Type*} [Fintype κ] [DecidableEq κ] {W : Type*} [AddCommGroup W] [Fintype W]
    (Q : κ → W → ZMod 2) :
    arfSum (fun x : κ → W => ∑ i, Q i (x i)) = ∏ i, arfSum (Q i) := by
  classical
  simp only [arfSum]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset W)) (fun i w => sgn (Q i w)),
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun x _ => sgn_sum _ _

/-! ## The hyperbolic plane, and the definite sign

Every nondegenerate alternating `𝔽₂` space is an orthogonal sum of hyperbolic planes — but that
decomposition theorem, and the transport of `arfSum` along an isomorphism onto `κ → Hyp`, are **not
formalized here**. So what follows determines the sum *on the standard model*, not on an arbitrary
such space. -/

/-- The hyperbolic plane `𝔽₂²`. -/
abbrev Hyp := ZMod 2 × ZMod 2

/-- The standard symplectic form on the hyperbolic plane, `ω((a,b),(c,d)) = a·d + b·c`. -/
def hypOmega (x y : Hyp) : ZMod 2 := x.1 * y.2 + x.2 * y.1

/-- **The base case.** On a hyperbolic plane every refinement evaluates to `2·(−1)^{Q(e)·Q(f)}` —
the plane's Arf invariant appearing as the sign. -/
theorem hyp_arfSum {Q : Hyp → ZMod 2} (hQ : ∀ x y, Q (x + y) = Q x + Q y + hypOmega x y) :
    arfSum Q = 2 * sgn (Q (1, 0) * Q (0, 1)) := by
  have hQ0 : Q 0 = 0 := refinement_map_zero hQ (by decide)
  have h11 : Q (1, 1) = Q (1, 0) + Q (0, 1) + 1 := by
    have h := hQ (1, 0) (0, 1)
    rw [show ((1 : ZMod 2), (0 : ZMod 2)) + ((0 : ZMod 2), (1 : ZMod 2))
          = ((1 : ZMod 2), (1 : ZMod 2)) from by decide,
      show hypOmega (1, 0) (0, 1) = 1 from by decide] at h
    exact h
  -- right-associated to match the shape `Finset.sum_insert` produces
  have hkey : ∀ a b : ZMod 2,
      (1 : ℤ) + (sgn a + (sgn b + sgn (a + b + 1))) = 2 * sgn (a * b) := by decide
  rw [arfSum, show (Finset.univ : Finset Hyp) = {(0, 0), (1, 0), (0, 1), (1, 1)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [show ((0 : ZMod 2), (0 : ZMod 2)) = (0 : Hyp) from rfl, hQ0, sgn_zero, h11]
  exact hkey _ _

/-- **The Arf sum, evaluated.** On the standard model — an orthogonal sum of `|κ|` hyperbolic
planes, with `Q` splitting accordingly —

  `∑_v (−1)^{Q(v)} = 2^{|κ|} · (−1)^{Arf(Q)}`,  where  `Arf(Q) = ∑ᵢ Q(eᵢ)·Q(fᵢ)`.

The magnitude agrees with `arfSum_sq` (here `|V| = 4^{|κ|}`), and the sign is the Arf invariant.
The value is **real**: `±2^{|κ|}` and nothing else — the `μ₈` (Brown) range needs a non-alternating
form and is not this theorem. -/
theorem arfSum_eq_two_pow_mul_sgn_arf {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Q : κ → Hyp → ZMod 2) (hQ : ∀ i x y, Q i (x + y) = Q i x + Q i y + hypOmega x y) :
    arfSum (fun x : κ → Hyp => ∑ i, Q i (x i))
      = 2 ^ Fintype.card κ * sgn (∑ i, Q i (1, 0) * Q i (0, 1)) := by
  classical
  rw [arfSum_pi, Finset.prod_congr rfl fun i _ => hyp_arfSum (hQ i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, sgn_sum]

/-! ## Computational witnesses

Each value is obtained twice: once by direct finite evaluation (without the general theorems) and
once through the general theorems. The numbers agree with an independent enumeration of
all refinements on one plane, which gives Arf sums `{2, 2, 2, −2}`. -/

section Witness

/-- The `Arf = 0` refinement on one plane: `Q(a,b) = ab`. -/
def Qeven : Hyp → ZMod 2 := fun x => x.1 * x.2

/-- The `Arf = 1` refinement on one plane: `Q(a,b) = ab + a + b`. -/
def Qodd : Hyp → ZMod 2 := fun x => x.1 * x.2 + x.1 + x.2

theorem Qeven_refines : ∀ x y : Hyp, Qeven (x + y) = Qeven x + Qeven y + hypOmega x y := by decide

theorem Qodd_refines : ∀ x y : Hyp, Qodd (x + y) = Qodd x + Qodd y + hypOmega x y := by decide

/-- **Arf 0, route A (independent):** direct evaluation of the four-term sum. -/
theorem witness_even_direct : arfSum Qeven = 2 := by decide

/-- **Arf 0, route B (general theorem):** through `hyp_arfSum`, with `Arf = Q(e)·Q(f) = 0`. -/
theorem witness_even_general : arfSum Qeven = 2 := by
  rw [hyp_arfSum Qeven_refines]; decide

/-- **Arf 1, route A (independent):** the sign flips — three of the four values are `1`. -/
theorem witness_odd_direct : arfSum Qodd = -2 := by decide

/-- **Arf 1, route B (general theorem):** through `hyp_arfSum`, with `Arf = 1·1 = 1`. -/
theorem witness_odd_general : arfSum Qodd = -2 := by
  rw [hyp_arfSum Qodd_refines]; decide

theorem hypOmega_add : ∀ u₁ u₂ w : Hyp,
    hypOmega (u₁ + u₂) w = hypOmega u₁ w + hypOmega u₂ w := by decide

theorem hypOmega_nondeg : ∀ w : Hyp, (∀ u, hypOmega u w = 0) → w = 0 := by decide

/-- **The magnitude, route A (independent)**: `S² = |V| = 4` by direct finite evaluation. -/
theorem witness_sq : arfSum Qodd ^ 2 = (Fintype.card Hyp : ℤ) := by decide

/-- **The magnitude, route B (general theorem)**: the same number through `arfSum_sq`, which is
what makes this a genuine two-route witness rather than one evaluation labelled twice. Ties the two
halves of the file together on one number. -/
theorem witness_sq_general : arfSum Qodd ^ 2 = (Fintype.card Hyp : ℤ) :=
  arfSum_sq Qodd_refines hypOmega_add hypOmega_nondeg

end Witness

end FTQCLib.ArfSum

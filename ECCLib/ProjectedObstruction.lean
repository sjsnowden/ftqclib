/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.DualObstruction

set_option linter.style.longLine false

/-!
# Projected phase polynomials have dual norm ≤ 1

The **projected** case of Candela–González-Sánchez–Szegedy (arXiv:2311.13899, `lem:dualnormbound` /
`prop:propolyobstruct`), lifting `DualObstruction` along a surjective homomorphism `τ : A' → A`.

The paper's obstruction class is not a phase polynomial on `A` but a *projected* one `φ_{*τ}` — the
pushforward of a phase polynomial `φ = e(P)` on `A'` along a surjective hom `τ`. The obstruction is:

* `correlation_le_gowersNorm_proj`: for `deg P ≤ s` on `A'`, `‖𝔼_{y:A'}[f(τy)·\overline{e(P)(y)}]‖ ≤ ‖f‖_{U^{s+1}}`.
* `phasePoly_obstruction_proj`: if `f` correlates that much with the projected phase, then `‖f‖_{U^{s+1}} ≥ δ`.

The whole transfer rests on one algebraic fact — a **surjective group hom pushes the uniform average
forward to the uniform average** (`expect_comp_surjHom`) — which gives **Gowers-norm pullback invariance**
`‖g∘τ‖_{U^d} = ‖g‖_{U^d}` (`gowersNorm_comp_surjHom`, via the multiplicative derivative commuting with `τ`
and the product hom `τ^{d+1}`). The projected obstruction is then `DualObstruction`'s
`correlation_le_gowersNorm` applied to `f∘τ` on `A'`, with the norm pulled back to `A`.

The correlation `𝔼_{y:A'}[f(τy)·\overline{e(P)(y)}]` *is* `⟨f, (e(P))_{*τ}⟩_A` — the pairing with the
pushforward `(e(P))_{*τ}(x) = 𝔼_{y∈τ⁻¹x} e(P)(y)`; here it is written via the pullback `f∘τ`, which is the
same quantity by the fiberwise decomposition. Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

variable {A' A : Type*} [AddCommGroup A'] [Fintype A'] [Nonempty A']
  [AddCommGroup A] [Fintype A]

/-- **A surjective group homomorphism pushes the uniform average forward to the uniform average.**
`𝔼_{y:A'} F(τ y) = 𝔼_{x:A} F(x)`. (All fibers of `τ` are cosets of `ker τ`, hence equinumerous.) -/
lemma expect_comp_surjHom (τ : A' →+ A) (hτ : Function.Surjective τ) (F : A → ℂ) :
    Finset.expect Finset.univ (fun y => F (τ y)) = Finset.expect Finset.univ F := by
  classical
  set n₀ := (Finset.univ.filter (fun y : A' => τ y = 0)).card with hn₀def
  have hfib : ∀ x : A, (Finset.univ.filter (fun y => τ y = x)).card = n₀ := by
    intro x
    obtain ⟨y₀, hy₀⟩ := hτ x
    rw [hn₀def]
    refine Finset.card_nbij' (fun y => y - y₀) (fun z => z + y₀) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
      rw [map_sub, hy, hy₀, sub_self]
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      rw [map_add, hz, hy₀, zero_add]
    · intro y _; simp
    · intro z _; simp
  have hsum : (∑ y : A', F (τ y)) = n₀ • (∑ x : A, F x) := by
    rw [Finset.smul_sum,
      ← Finset.sum_fiberwise_of_maps_to (fun y (_ : y ∈ (Finset.univ : Finset A')) =>
        Finset.mem_univ (τ y)) (fun y => F (τ y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hcst : ∀ y ∈ Finset.univ.filter (fun y => τ y = x), F (τ y) = F x := by
      intro y hy; simp only [Finset.mem_filter] at hy; rw [hy.2]
    rw [Finset.sum_congr rfl hcst, Finset.sum_const, hfib x]
  have hcardNat : Fintype.card A' = Fintype.card A * n₀ := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (fun y (_ : y ∈ (Finset.univ : Finset A')) =>
        Finset.mem_univ (τ y))]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hn₀pos : 0 < n₀ := by
    rw [hn₀def]; exact Finset.card_pos.mpr ⟨0, by simp [map_zero]⟩
  haveI : Nonempty A := ⟨τ (Classical.arbitrary A')⟩
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, hsum, nsmul_eq_mul]
  have hcardC : (Fintype.card A' : ℂ) = (Fintype.card A : ℂ) * n₀ := by exact_mod_cast hcardNat
  rw [hcardC]
  have hn₀C : (n₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn₀pos.ne'
  have hAC : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

omit [Fintype A'] [Nonempty A'] [Fintype A] in
/-- Pushing a hom through the multiplicative derivative: `∂_h(g∘τ) = (∂_{τh} g)∘τ`. -/
lemma mderiv_comp_hom (τ : A' →+ A) (h : A') (g : A → ℂ) :
    mderiv h (fun y => g (τ y)) = fun y => mderiv (τ h) g (τ y) := by
  funext y; simp only [mderiv, map_add]

omit [Fintype A'] [Nonempty A'] [Fintype A] in
/-- Iterated version: `∂_{hs}(g∘τ) = (∂_{map τ hs} g)∘τ`. -/
lemma iterMderiv_comp_hom (τ : A' →+ A) (hs : List A') (g : A → ℂ) :
    iterMderiv hs (fun y => g (τ y)) = fun y => iterMderiv (hs.map τ) g (τ y) := by
  induction hs with
  | nil => rfl
  | cons h hs ih => rw [iterMderiv_cons, ih, mderiv_comp_hom, List.map_cons, iterMderiv_cons]

/-- The product hom `(x, h) ↦ (τ x, τ ∘ h)` on `A' × (Fin d → A')`, used to pull the Gowers average back
along `τ`. -/
def prodHom (τ : A' →+ A) (d : ℕ) : (A' × (Fin d → A')) →+ (A × (Fin d → A)) where
  toFun p := (τ p.1, fun i => τ (p.2 i))
  map_zero' := by
    refine Prod.ext ?_ ?_
    · simp
    · funext i; simp
  map_add' a b := by
    refine Prod.ext ?_ ?_
    · simp [map_add]
    · funext i; simp [map_add]

omit [Fintype A'] [Nonempty A'] [Fintype A] in
lemma prodHom_surjective (τ : A' →+ A) (hτ : Function.Surjective τ) (d : ℕ) :
    Function.Surjective (prodHom τ d) := by
  rintro ⟨x, h⟩
  exact ⟨((hτ x).choose, fun i => (hτ (h i)).choose), by
    simp only [prodHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq]
    exact ⟨(hτ x).choose_spec, by funext i; exact (hτ (h i)).choose_spec⟩⟩

/-- **Pullback invariance of the Gowers inner product** along a surjective hom. -/
lemma gowersInner_comp_surjHom (d : ℕ) (τ : A' →+ A) (hτ : Function.Surjective τ) (g : A → ℂ) :
    gowersInner d (fun y => g (τ y)) = gowersInner d g := by
  rw [gowersInner, gowersInner,
    ← expect_comp_surjHom (prodHom τ d) (prodHom_surjective τ hτ d)
      (fun q : A × (Fin d → A) => iterMderiv (List.ofFn q.2) g q.1)]
  refine Finset.expect_congr rfl (fun p _ => ?_)
  rw [iterMderiv_comp_hom, List.map_ofFn]
  rfl

/-- **Pullback invariance of the Gowers norm** along a surjective hom: `‖g∘τ‖_{U^d} = ‖g‖_{U^d}`. The
`τ^{d+1}`-average of the box product downstairs equals the average upstairs. -/
lemma gowersNorm_comp_surjHom (d : ℕ) (τ : A' →+ A) (hτ : Function.Surjective τ) (g : A → ℂ) :
    gowersNorm d (fun y => g (τ y)) = gowersNorm d g := by
  rw [gowersNorm_eq, gowersNorm_eq, gowersInner_comp_surjHom d τ hτ]

variable {G : Type*} [AddCommGroup G]

/-- **The projected dual-norm bound** (Candela–González-Sánchez–Szegedy `lem:dualnormbound`): the
correlation of `f` on `A` with the projected phase `(e(P))_{*τ}` (`P` a degree-`≤s` phase on `A'`,
`τ : A' → A` surjective) is at most `‖f‖_{U^{s+1}}`. `‖(e(P))_{*τ}‖^*_{U^{s+1}} ≤ 1`. -/
theorem correlation_le_gowersNorm_proj (τ : A' →+ A) (hτ : Function.Surjective τ)
    (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t)) {s : ℕ} {P : A' → G}
    (hP : IsPolyDegLE s P) (f : A → ℂ) :
    ‖Finset.expect Finset.univ (fun y => f (τ y) * (starRingEnd ℂ) (ψ (P y)))‖
      ≤ gowersNorm (s + 1) f := by
  have := correlation_le_gowersNorm ψ hψ hP (fun y => f (τ y))
  rwa [gowersNorm_comp_surjHom (s + 1) τ hτ] at this

/-- **The projected phase-polynomial obstruction** (`prop:propolyobstruct`): if `f` on `A` correlates with
a projected degree-`≤s` phase to level `δ`, then `‖f‖_{U^{s+1}} ≥ δ`. -/
theorem phasePoly_obstruction_proj (τ : A' →+ A) (hτ : Function.Surjective τ)
    (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t)) {s : ℕ} {P : A' → G}
    (hP : IsPolyDegLE s P) (f : A → ℂ) {δ : ℝ}
    (hδ : δ ≤ ‖Finset.expect Finset.univ (fun y => f (τ y) * (starRingEnd ℂ) (ψ (P y)))‖) :
    δ ≤ gowersNorm (s + 1) f :=
  hδ.trans (correlation_le_gowersNorm_proj τ hτ ψ hψ hP f)

/-! ## The pushforward object `φ_{*τ}`

The projected obstruction above is stated via the pullback `f∘τ`. Here we give the explicit **pushforward
object** `φ_{*τ}(x) = 𝔼_{y∈τ⁻¹x} φ(y)` and prove the pairing identity `⟨f, φ_{*τ}⟩_A = ⟨f∘τ, φ⟩_{A'}`, so
the obstruction can be read literally as a bound on the correlation of `f` with the projected phase. The
identity rests on the **fiberwise decomposition** of the uniform average along a surjective hom. -/

/-- Complex conjugation commutes with the finite average over any Finset. -/
lemma starRingEnd_expect {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    (starRingEnd ℂ) (Finset.expect s g) = Finset.expect s (fun i => (starRingEnd ℂ) (g i)) := by
  apply Complex.ext
  · simp [Complex.conj_re, Complex.re_expect]
  · simp [Complex.conj_im, Complex.im_expect, Finset.expect_neg_distrib]

variable [DecidableEq A]

omit [Nonempty A'] in
/-- **Fiberwise decomposition of the uniform average** along a surjective hom:
`𝔼_{y:A'} H(y) = 𝔼_{x:A} 𝔼_{y∈τ⁻¹x} H(y)`. (All fibers are `ker τ`-cosets, hence equinumerous.) -/
lemma expect_fiberwise_surjHom (τ : A' →+ A) (hτ : Function.Surjective τ) (H : A' → ℂ) :
    Finset.expect Finset.univ H
      = Finset.expect Finset.univ
          (fun x : A => Finset.expect (Finset.univ.filter (fun y => τ y = x)) H) := by
  classical
  set n₀ := (Finset.univ.filter (fun y : A' => τ y = 0)).card with hn₀def
  have hfib : ∀ x : A, (Finset.univ.filter (fun y => τ y = x)).card = n₀ := by
    intro x
    obtain ⟨y₀, hy₀⟩ := hτ x
    rw [hn₀def]
    refine Finset.card_nbij' (fun y => y - y₀) (fun z => z + y₀) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
      rw [map_sub, hy, hy₀, sub_self]
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
      rw [map_add, hz, hy₀, zero_add]
    · intro y _; simp
    · intro z _; simp
  have hcardNat : Fintype.card A' = Fintype.card A * n₀ := by
    rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (fun y (_ : y ∈ (Finset.univ : Finset A')) =>
        Finset.mem_univ (τ y))]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hRHS : ∀ x : A, Finset.expect (Finset.univ.filter (fun y => τ y = x)) H
            = (∑ y ∈ Finset.univ.filter (fun y => τ y = x), H y) / (n₀ : ℂ) := by
    intro x; rw [Finset.expect_eq_sum_div_card, hfib]
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  simp only [hRHS, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun y (_ : y ∈ (Finset.univ : Finset A')) => Finset.mem_univ (τ y)), mul_assoc, ← mul_inv]
  congr 2
  rw [hcardNat]; push_cast; ring

/-- The **pushforward** `φ_{*τ}(x) = 𝔼_{y∈τ⁻¹x} φ(y)` of `φ` along a surjective hom `τ`. -/
noncomputable def pushforward (τ : A' →+ A) (φ : A' → ℂ) : A → ℂ :=
  fun x => Finset.expect (Finset.univ.filter (fun y => τ y = x)) φ

omit [Nonempty A'] in
/-- **The pairing identity** `⟨f, φ_{*τ}⟩_A = ⟨f∘τ, φ⟩_{A'}`: correlating `f` with the pushforward on `A`
equals correlating the pullback `f∘τ` with `φ` on `A'`. -/
lemma inner_pushforward (τ : A' →+ A) (hτ : Function.Surjective τ) (f : A → ℂ) (φ : A' → ℂ) :
    Finset.expect Finset.univ (fun y => f (τ y) * (starRingEnd ℂ) (φ y))
      = Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (pushforward τ φ x)) := by
  rw [expect_fiberwise_surjHom τ hτ (fun y => f (τ y) * (starRingEnd ℂ) (φ y))]
  refine Finset.expect_congr rfl (fun x _ => ?_)
  rw [pushforward, starRingEnd_expect, Finset.mul_expect]
  refine Finset.expect_congr rfl (fun y hy => ?_)
  simp only [Finset.mem_filter] at hy
  rw [hy.2]

/-- **The projected obstruction, on the pushforward object.** The correlation of `f` with the projected
phase `(e(P))_{*τ}` is at most `‖f‖_{U^{s+1}}` — the literal reading of `lem:dualnormbound`. -/
theorem correlation_le_gowersNorm_pushforward (τ : A' →+ A) (hτ : Function.Surjective τ)
    (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t)) {s : ℕ} {P : A' → G}
    (hP : IsPolyDegLE s P) (f : A → ℂ) :
    ‖Finset.expect Finset.univ
        (fun x => f x * (starRingEnd ℂ) (pushforward τ (fun y => ψ (P y)) x))‖
      ≤ gowersNorm (s + 1) f := by
  rw [← inner_pushforward τ hτ f (fun y => ψ (P y))]
  exact correlation_le_gowersNorm_proj τ hτ ψ hψ hP f

end ECCLib

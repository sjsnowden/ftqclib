/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Heisenberg

set_option linter.style.longLine false
-- `Fintype F` / `DecidableEq ι` are used in the proof (delta expansion, orthogonality), not the type.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Stone–von Neumann, part 2 — the embedding

In its own file so that changes here do not re-elaborate the 1,300-line Heisenberg development.
-/

namespace ECCLib.Heisenberg

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

section StoneVonNeumann

variable [Fintype F] [DecidableEq ι]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- **Stone–von Neumann, the embedding half.** Any representation of `H(V)`
with central character `ψ` on a nonzero space *contains* the Schrödinger model: there is an
**injective equivariant** `Φ : ℂ[𝔽_q^ι] →ₗ W`. Together with part 1 (`irreducible_of_invariant`) this
gives uniqueness of the **irreducible** representation with a fixed nontrivial central character —
that consequence is `stone_von_neumann_equiv`.

**Scope of this theorem, and where the rest lives.** The classical theorem (Prasad 0912.0574 §4.1)
has a second half: the classification `ℋ = ⊕_α ℋ^α` with each intertwiner unique up to scaling.
This statement is the embedding only — for a possibly-reducible `W` it gives one embedded copy, not
a decomposition. **The full theorem is formalized** as `stone_von_neumann`
(`StoneVonNeumannFull.lean`): every representation with central character `ψ` is `ψ`-isotypic,
`W ≃ κ →₀ S` equivariantly, with Schur uniqueness for equivalences as
`schrodinger_equiv_unique_smul`. The determinacy statement is made there in its correct
form.

Proof (Prasad 0912.0574, specialized): average `ρ` over the modulation subgroup against each character
`ψ⟨·,x⟩` — the Fourier projectors. They sum to the identity by orthogonality, so some projection of a
nonzero vector is a nonzero joint eigenvector `v` with eigenvalue `ψ⟨·,x₀⟩` (self-duality says every
character has this form, so nothing is lost). The translated family `u_x := ρ⟨x₀−x,0,0⟩v` then behaves
exactly like the deltas, and `δ_x ↦ u_x` extends to the intertwiner; its kernel is invariant, so part 1
kills it. -/
theorem stone_von_neumann_embedding (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (ρ : Heis F ι →* Module.End ℂ W)
    (hcen : ∀ s : F, ρ (Heis.central s) = ψ s • (1 : Module.End ℂ W))
    {w : W} (hw : w ≠ 0) :
    ∃ Φ : ((ι → F) → ℂ) →ₗ[ℂ] W, Function.Injective Φ ∧
      ∀ x : Heis F ι, Φ ∘ₗ schrodinger h2 ψ x = ρ x ∘ₗ Φ := by
  classical
  have hcard : (Fintype.card (ι → F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- ### Step 1: a joint eigenvector of the modulation subgroup, by Fourier projectors
  obtain ⟨x₀, v, hv0, heig⟩ :
      ∃ (x₀ : ι → F) (v : W), v ≠ 0 ∧
        ∀ b : ι → F, ρ ⟨0, b, 0⟩ v = ψ (pairing b x₀) • v := by
    set Pw : (ι → F) → W := fun x =>
      (Fintype.card (ι → F) : ℂ)⁻¹ • ∑ m : ι → F, ψ (-(pairing m x)) • ρ ⟨0, m, 0⟩ w with hPw
    have hterm : ∀ m : ι → F,
        ∑ x : ι → F, ψ (-(pairing m x)) • ρ ⟨0, m, 0⟩ w
          = (∑ x : ι → F, ψ (-(pairing m x))) • ρ ⟨0, m, 0⟩ w := fun m =>
      (Finset.sum_smul).symm
    have hcollapse : ∑ m : ι → F, (∑ x : ι → F, ψ (-(pairing m x))) • ρ ⟨0, m, 0⟩ w
        = (Fintype.card (ι → F) : ℂ) • w := by
      rw [Finset.sum_eq_single (0 : ι → F)]
      · have h1 : ∀ x : ι → F, ψ (-(pairing (0 : ι → F) x)) = 1 := by
          intro x
          rw [pairing_zero_left, neg_zero, AddChar.map_zero_eq_one]
        rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one, show (⟨0, 0, 0⟩ : Heis F ι) = 1 from rfl, map_one,
          Module.End.one_apply]
      · intro m _ hm
        have h3 : ∀ x : ι → F, ψ (-(pairing m x)) = ψ (pairing m (-x)) := by
          intro x
          rw [pairing_neg_right]
        have h5 : (∑ x : ι → F, ψ (pairing m (-x))) = ∑ y : ι → F, ψ (pairing m y) :=
          Fintype.sum_equiv (Equiv.neg (ι → F)) (fun x => ψ (pairing m (-x)))
            (fun y => ψ (pairing m y)) fun x => rfl
        rw [Finset.sum_congr rfl fun x _ => h3 x, h5]
        have h4 : ∀ y : ι → F, ψ (pairing m y) = ψ (pairing y m) := by
          intro y
          rw [pairing_symm]
        rw [Finset.sum_congr rfl fun y _ => h4 y, sum_pairingChar_eq_zero hψ hm, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hsum : ∑ x : ι → F, Pw x = w := by
      simp only [hPw]
      rw [← Finset.smul_sum, Finset.sum_comm]
      rw [Finset.sum_congr rfl fun m _ => hterm m, hcollapse, smul_smul,
        inv_mul_cancel₀ hcard, one_smul]
    obtain ⟨x₀, -, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact hw)
    refine ⟨x₀, Pw x₀, hx₀, fun b => ?_⟩
    simp only [hPw]
    rw [map_smul, map_sum]
    have hact : ∀ m : ι → F, ρ ⟨0, b, 0⟩ (ψ (-(pairing m x₀)) • ρ ⟨0, m, 0⟩ w)
        = ψ (-(pairing m x₀)) • ρ ⟨0, b + m, 0⟩ w := by
      intro m
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, Heis.mom_mul_mom]
    rw [Finset.sum_congr rfl fun m _ => hact m,
      Fintype.sum_equiv (Equiv.addLeft b) _
        (fun mm => ψ (-(pairing (mm - b) x₀)) • ρ ⟨0, mm, 0⟩ w) fun m => by
          change ψ (-(pairing m x₀)) • ρ ⟨0, b + m, 0⟩ w
            = ψ (-(pairing (b + m - b) x₀)) • ρ ⟨0, b + m, 0⟩ w
          rw [add_sub_cancel_left]]
    have hcoef : ∀ mm : ι → F, ψ (-(pairing (mm - b) x₀)) • ρ ⟨0, mm, 0⟩ w
        = ψ (pairing b x₀) • (ψ (-(pairing mm x₀)) • ρ ⟨0, mm, 0⟩ w) := by
      intro mm
      rw [smul_smul, ← AddChar.map_add_eq_mul, pairing_sub_left]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun mm _ => hcoef mm, ← Finset.smul_sum, smul_comm]
  -- ### Step 2: the delta family in `W`
  set u : (ι → F) → W := fun x => ρ ⟨x₀ - x, 0, 0⟩ v with hu
  have hu_trans : ∀ a x : ι → F, ρ ⟨a, 0, 0⟩ (u x) = u (x - a) := by
    intro a x
    simp only [hu]
    rw [← Module.End.mul_apply, ← map_mul, Heis.pos_mul_pos,
      show a + (x₀ - x) = x₀ - (x - a) by ring]
  have hu_mom : ∀ b x : ι → F, ρ ⟨0, b, 0⟩ (u x) = ψ (pairing b x) • u x := by
    intro b x
    simp only [hu]
    rw [← Module.End.mul_apply, ← map_mul, Heis.mom_mul_pos]
    have hfac : (⟨x₀ - x, b, -((2 : F)⁻¹ * pairing b (x₀ - x))⟩ : Heis F ι)
        = Heis.central (-(pairing b (x₀ - x))) * ((⟨x₀ - x, 0, 0⟩ : Heis F ι) * ⟨0, b, 0⟩) := by
      rw [Heis.pos_mul_mom, Heis.central_mul]
      refine Heis.ext rfl rfl ?_
      change -((2 : F)⁻¹ * pairing b (x₀ - x))
        = -pairing b (x₀ - x) + (2 : F)⁻¹ * pairing b (x₀ - x)
      have h : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by
        rw [← two_mul]
        exact mul_inv_cancel₀ h2
      linear_combination (-(pairing b (x₀ - x))) * h
    rw [hfac, map_mul, map_mul, hcen, Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, heig b, map_smul, smul_smul,
      ← AddChar.map_add_eq_mul]
    congr 2
    rw [pairing_sub_right]
    ring
  -- ### Step 3: the intertwiner `δ_x ↦ u_x`
  set Φ : ((ι → F) → ℂ) →ₗ[ℂ] W :=
    { toFun := fun f => ∑ x : ι → F, f x • u x
      map_add' := fun f g => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum] }
    with hΦdef
  have hΦ_apply : ∀ f : (ι → F) → ℂ, Φ f = ∑ x : ι → F, f x • u x := fun f => rfl
  have hΦ_delta : ∀ y : ι → F, Φ (delta y) = u y := by
    intro y
    rw [hΦ_apply, Finset.sum_eq_single y]
    · simp [delta]
    · intro x _ hxy
      simp [delta, hxy]
    · intro h
      exact absurd (Finset.mem_univ _) h
  -- ### Step 4: equivariance on the three generator families, then in general
  have hgen_c : ∀ s : F,
      Φ ∘ₗ schrodinger h2 ψ (Heis.central s) = ρ (Heis.central s) ∘ₗ Φ := by
    intro s
    rw [schrodinger_central, hcen]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.one_apply, map_smul]
  have hgen_t : ∀ a : ι → F,
      Φ ∘ₗ schrodinger h2 ψ (⟨a, 0, 0⟩ : Heis F ι) = ρ ⟨a, 0, 0⟩ ∘ₗ Φ := by
    intro a
    rw [schrodinger_translation]
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ_apply, hΦ_apply, map_sum]
    have hR : ∀ x : ι → F, ρ ⟨a, 0, 0⟩ (f x • u x) = f x • u (x - a) := by
      intro x
      rw [map_smul, hu_trans]
    rw [Finset.sum_congr rfl fun x _ => hR x]
    refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
    change (translation a f) x • u x = f (x + a) • u (x + a - a)
    rw [translation_apply, add_sub_cancel_right]
  have hgen_m : ∀ b : ι → F,
      Φ ∘ₗ schrodinger h2 ψ (⟨0, b, 0⟩ : Heis F ι) = ρ ⟨0, b, 0⟩ ∘ₗ Φ := by
    intro b
    rw [schrodinger_modulation]
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hΦ_apply, hΦ_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [modulation_apply, map_smul, hu_mom, smul_smul, mul_comm (f x)]
  have hcomp : ∀ {g gg : Heis F ι},
      Φ ∘ₗ schrodinger h2 ψ g = ρ g ∘ₗ Φ →
      Φ ∘ₗ schrodinger h2 ψ gg = ρ gg ∘ₗ Φ →
      Φ ∘ₗ schrodinger h2 ψ (g * gg) = ρ (g * gg) ∘ₗ Φ := by
    intro g gg hg hh
    rw [map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, hh, ← LinearMap.comp_assoc]
  have hequiv : ∀ x : Heis F ι, Φ ∘ₗ schrodinger h2 ψ x = ρ x ∘ₗ Φ := by
    intro x
    obtain ⟨c, p, m, hx⟩ :
        ∃ c p m, x = (Heis.central c : Heis F ι) * ⟨p, 0, 0⟩ * ⟨0, m, 0⟩ :=
      ⟨_, _, _, Heis.factor x⟩
    rw [hx]
    exact hcomp (hcomp (hgen_c c) (hgen_t p)) (hgen_m m)
  -- ### Step 5: injectivity — the kernel is invariant, and part 1 kills it
  have hpoint : ∀ (g : Heis F ι) (f : (ι → F) → ℂ),
      Φ (schrodinger h2 ψ g f) = ρ g (Φ f) := by
    intro g f
    have h := congrArg (fun T : ((ι → F) → ℂ) →ₗ[ℂ] W => T f) (hequiv g)
    simpa using h
  have hkt : ∀ a : ι → F, ∀ f ∈ LinearMap.ker Φ, translation a f ∈ LinearMap.ker Φ := by
    intro a f hf
    rw [LinearMap.mem_ker] at hf ⊢
    rw [← schrodinger_translation h2 ψ a, hpoint, hf, map_zero]
  have hkm : ∀ b : ι → F, ∀ f ∈ LinearMap.ker Φ, modulation ψ b f ∈ LinearMap.ker Φ := by
    intro b f hf
    rw [LinearMap.mem_ker] at hf ⊢
    rw [← schrodinger_modulation h2 ψ b, hpoint, hf, map_zero]
  have hker : LinearMap.ker Φ = ⊥ := by
    rcases irreducible_of_invariant hψ (LinearMap.ker Φ) hkt hkm with h | h
    · exact h
    · exfalso
      have hmem : delta x₀ ∈ LinearMap.ker Φ := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hΦ_delta] at hmem
      have hux : u x₀ = v := by
        simp only [hu]
        rw [sub_self, show (⟨(0 : ι → F), 0, 0⟩ : Heis F ι) = 1 from rfl, map_one]
        exact Module.End.one_apply v
      exact hv0 (by rw [← hux]; exact hmem)
  exact ⟨Φ, LinearMap.ker_eq_bot.mp hker, hequiv⟩

end StoneVonNeumann


/-! ### Inverses, the irreducible case, and the linearization -/

section Completion

variable [Fintype F] [DecidableEq ι]

omit [Fintype F] [DecidableEq ι] in
/-- `HasWeilOperator` transfers to any **right inverse** `g'` of `g` (the hypothesis is one-sided:
`g ∘ g' = id`). With `hasWeilOperator_id` and `.comp`, the maps carrying a Weil operator are closed
under identity, composition, and passage to such an inverse. No `Subgroup` object is constructed
here, and the ambient `Heis F ι → Heis F ι` under composition is a monoid, not a group. -/
theorem HasWeilOperator.inv {h2 : (2 : F) ≠ 0} {ψ : AddChar F ℂ}
    {g g' : Heis F ι → Heis F ι} (hgg' : ∀ x, g (g' x) = x)
    (hg : HasWeilOperator h2 ψ g) : HasWeilOperator h2 ψ g' := by
  obtain ⟨Wg, hWg⟩ := hg
  refine ⟨Wg⁻¹, fun x => ?_⟩
  have h := hWg (g' x)
  rw [hgg' x] at h
  have h3 : schrodinger h2 ψ (g' x) * (↑Wg⁻¹ : Module.End ℂ ((ι → F) → ℂ))
      = (↑Wg⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x := by
    have hc := congrArg (fun z => (↑Wg⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * z
      * (↑Wg⁻¹ : Module.End ℂ ((ι → F) → ℂ))) h
    simpa [mul_assoc, Units.inv_mul, Units.mul_inv] using hc
  exact h3.symm

omit [Fintype F] [DecidableEq ι] in
/-- The Weyl element satisfies `w⁴ = 1`, i.e. its order **divides** 4 — matching `𝓕̂⁴ = id` below.
Order *exactly* 4 is not claimed and would be false as stated: this carries no hypothesis on `F` or
`ι`, and `fourierMap² = ⟨-pos, -mom, cen⟩` is the identity when `(2 : F) = 0` or `ι` is empty. -/
theorem Heis.fourierMap_pow_four (x : Heis F ι) :
    Heis.fourierMap (Heis.fourierMap (Heis.fourierMap (Heis.fourierMap x))) = x := by
  refine Heis.ext ?_ ?_ rfl <;> simp [Heis.fourierMap]

/-- **Stone–von Neumann, irreducible case**: an *irreducible* representation with central character
`ψ` IS the Schrödinger model — the embedding of `stone_von_neumann_embedding` is onto, hence an equivalence. -/
theorem stone_von_neumann_equiv (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Heis F ι →* Module.End ℂ W)
    (hcen : ∀ s : F, ρ (Heis.central s) = ψ s • (1 : Module.End ℂ W))
    {w : W} (hw : w ≠ 0)
    (hirr : ∀ M : Submodule ℂ W, (∀ (x : Heis F ι), ∀ v ∈ M, ρ x v ∈ M) → M = ⊥ ∨ M = ⊤) :
    ∃ e : ((ι → F) → ℂ) ≃ₗ[ℂ] W,
      ∀ x : Heis F ι, (e : ((ι → F) → ℂ) →ₗ[ℂ] W) ∘ₗ schrodinger h2 ψ x = ρ x ∘ₗ e := by
  obtain ⟨Φ, hinj, hequiv⟩ := stone_von_neumann_embedding h2 hψ ρ hcen hw
  have hpoint : ∀ (g : Heis F ι) (f : (ι → F) → ℂ),
      Φ (schrodinger h2 ψ g f) = ρ g (Φ f) := by
    intro g f
    have h := congrArg (fun T : ((ι → F) → ℂ) →ₗ[ℂ] W => T f) (hequiv g)
    simpa using h
  have hrange : ∀ (x : Heis F ι), ∀ v ∈ LinearMap.range Φ, ρ x v ∈ LinearMap.range Φ := by
    intro x v hv
    obtain ⟨f, rfl⟩ := hv
    exact ⟨schrodinger h2 ψ x f, hpoint x f⟩
  rcases hirr (LinearMap.range Φ) hrange with h | h
  · exfalso
    have hδ : delta (0 : ι → F) ≠ 0 := by
      intro hc
      have h0 := congrFun hc 0
      simp [delta] at h0
    have hΦδ : Φ (delta 0) ≠ 0 := fun hc => hδ (hinj (by rw [hc, map_zero]))
    have hmem : Φ (delta 0) ∈ LinearMap.range Φ := ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hΦδ hmem
  · refine ⟨LinearEquiv.ofBijective Φ ⟨hinj, LinearMap.range_eq_top.mp h⟩, fun x => ?_⟩
    exact hequiv x

/-- `(quadGaussSum ψ)⁴ = |F|²` — the fourth power of the Gauss sum is a known scalar, whichever of
the four sign branches the sum itself lies on. -/
theorem quadGaussSum_pow_four (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ECCLib.quadGaussSum ψ ^ 4 = (Fintype.card F : ℂ) ^ 2 := by
  classical
  have hsq := ECCLib.quadGaussSum_sq hF hψ
  have hd : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  have h4 : ECCLib.quadGaussSum ψ ^ 4 = (ECCLib.quadGaussSum ψ ^ 2) ^ 2 := by
    ring
  rw [h4, hsq]
  rcases hd with h | h <;> rw [h] <;> push_cast <;> ring

theorem quadGaussSum_ne_zero (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ECCLib.quadGaussSum ψ ≠ 0 := by
  intro hc
  have h := ECCLib.quadGaussSum_normSq hF hψ
  rw [hc] at h
  simp at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card F : ℝ) ≠ 0) h.symm

/-- The **trace-normalized DFT** `𝓕̂ := Tr(𝓕)⁻¹ • 𝓕 = ((quadGaussSum ψ)^{|ι|})⁻¹ • 𝓕`, whose
normalizing scalar is the quadratic Gauss sum to the `|ι|`-th power, inverted.

**Odd characteristic only.** The definition carries no hypothesis, but in characteristic 2
`quadGaussSum ψ = 0` (`quadGaussSum_char_two_eq_zero`), so the scalar is `0` and `𝓕̂ = 0`: its trace
is `0`, not `1`, and `𝓕̂⁴ = 0 ≠ id`. The properties below that justify the name —
`trace_fourierNormalized`, `fourierNormalized_pow_four`, `fourierNormalized_unique` — all carry
`ringChar F ≠ 2`. Among the scalar multiples `c·𝓕` satisfying `(c·𝓕)⁴ = id` this is the one of
trace `1`; that there are exactly four such `c` is not proved here. -/
noncomputable def fourierNormalized (ψ : AddChar F ℂ) :
    ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ) :=
  ((ECCLib.quadGaussSum ψ) ^ Fintype.card ι)⁻¹ • fourierOp ψ

theorem trace_fourierNormalized (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (fourierNormalized ψ) = 1 := by
  rw [fourierNormalized, map_smul, trace_fourierOp_eq_quadGaussSum_pow, smul_eq_mul,
    inv_mul_cancel₀ (pow_ne_zero _ (quadGaussSum_ne_zero hF hψ))]

/-- **The linearization at the Weyl element**: `𝓕̂⁴ = id`, matching `w⁴ = 1`
(`Heis.fourierMap_pow_four`). The unnormalized relation is `𝓕⁴ = |V|²·id`; dividing by
`Tr(𝓕) = (quadGaussSum ψ)^{|ι|}` — whose fourth power is `|F|^{2|ι|} = |V|²` by
`quadGaussSum_pow_four` — turns the projective relation into an exact one. -/
theorem fourierNormalized_pow_four (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) :
    (fourierNormalized ψ ∘ₗ fourierNormalized ψ) ∘ₗ (fourierNormalized ψ ∘ₗ fourierNormalized ψ)
      = (LinearMap.id : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)) := by
  classical
  set c := ((ECCLib.quadGaussSum ψ) ^ Fintype.card ι)⁻¹ with hc
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar : c ^ 4 * ((Fintype.card (ι → F) : ℂ)) ^ 2 = 1 := by
    have hg4 := quadGaussSum_pow_four hF hψ
    have hcard2 : ((Fintype.card (ι → F) : ℂ)) ^ 2
        = ((Fintype.card F : ℂ) ^ 2) ^ Fintype.card ι := by
      rw [Fintype.card_fun]
      push_cast
      rw [← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]
    have hc4 : c ^ 4 = (((Fintype.card F : ℂ) ^ 2)⁻¹) ^ Fintype.card ι := by
      rw [hc, inv_pow, ← pow_mul, mul_comm (Fintype.card ι) 4, pow_mul, hg4, ← inv_pow]
    rw [hc4, hcard2, ← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ hq), one_pow]
  have hexpand : (fourierNormalized ψ ∘ₗ fourierNormalized ψ)
        ∘ₗ (fourierNormalized ψ ∘ₗ fourierNormalized ψ)
      = (c * c * (c * c)) •
        ((fourierOp (ι := ι) ψ ∘ₗ fourierOp ψ) ∘ₗ (fourierOp ψ ∘ₗ fourierOp ψ)) := by
    rw [fourierNormalized, ← hc]
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [hexpand, fourierOp_pow_four hψ, smul_smul,
    show c * c * (c * c) * (Fintype.card (ι → F) : ℂ) ^ 2
      = c ^ 4 * (Fintype.card (ι → F) : ℂ) ^ 2 by ring,
    hscalar, one_smul]

/-- **Uniqueness of the normalization**: `𝓕̂` is the only scalar multiple of `𝓕` with trace `1`. -/
theorem fourierNormalized_unique {ψ : AddChar F ℂ} {c : ℂ}
    (htr : LinearMap.trace ℂ ((ι → F) → ℂ) (c • fourierOp ψ) = 1) :
    c • fourierOp (ι := ι) ψ = fourierNormalized ψ := by
  rw [map_smul, trace_fourierOp_eq_quadGaussSum_pow, smul_eq_mul] at htr
  rw [fourierNormalized]
  congr 1
  exact eq_inv_of_mul_eq_one_left htr

end Completion

end ECCLib.Heisenberg



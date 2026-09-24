/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.StoneVonNeumann
import ECCLib.WeilGeneration

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

/-!
# The Weil representation of `Sp(2n, 𝔽_q)` by transport

The transport route to the Weil operators; it needs no generation theorem and applies at every
rank. Given a symplectic `g`, twist the Schrödinger representation by it: `π_g := π ∘ g`. Because
`g` fixes the centre (`Heis.IsSymplectic.map_central`, a theorem, not a hypothesis), `π_g` has the
*same* central character `ψ` as `π`. Stone–von Neumann then hands back an injective equivariant
`Φ : ℂ[𝔽_q^ι] →ₗ ℂ[𝔽_q^ι]` — an injective endomorphism of a finite-dimensional space, hence
bijective, hence a unit. That unit *is* the Weil operator of `g`.

So `hasWeilOperator_of_isSymplectic_svn`: **every symplectic map, at every rank, has a Weil
operator.** No generation theorem, no Bruhat decomposition, no cover, no rank restriction —
`stone_von_neumann_embedding` does all the work.

The explicit route (`WeilGeneration.lean`, `WeilGenerationComplete.lean`) is the constructive
complement: its proof writes the operator down as a word in chirps and DFTs rather than
extracting it from an existence proof, and `hasWeilOperator_of_isSymplectic_explicit` reaches
every rank.
-/

namespace ECCLib.Heisenberg

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

section Transport

variable [Fintype F] [DecidableEq ι]

/-- **The twisted Schrödinger representation** `π_g := π ∘ g`, for `g` symplectic. A representation
of `H(V)` on the *same* space as `π`, which is what makes the intertwiner an endomorphism. -/
noncomputable def twist (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) {g : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) : Heis F ι →* Module.End ℂ ((ι → F) → ℂ) :=
  (schrodinger h2 ψ).comp (Heis.symplecticHom hg)

@[simp] lemma twist_apply (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) {g : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) (x : Heis F ι) :
    twist h2 ψ hg x = schrodinger h2 ψ (g x) := rfl

/-- **The twist has the same central character** — the whole point of `map_central`, and the
hypothesis Stone–von Neumann is stated against. -/
lemma twist_central (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) {g : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) (s : F) :
    twist h2 ψ hg (Heis.central s) = ψ s • (1 : Module.End ℂ ((ι → F) → ℂ)) := by
  rw [twist_apply, hg.map_central, schrodinger_central, Module.End.one_eq_id]

lemma delta_zero_ne_zero : delta (0 : ι → F) ≠ 0 := by
  intro hc
  have h0 := congrFun hc 0
  simp [delta] at h0

/-- **The Weil representation of `Sp(2n, 𝔽_q)`, at every rank**: every symplectic map has a
Weil operator.

Transport under Stone–von Neumann. The twist `π ∘ g` has central character `ψ`
(`twist_central`), so `stone_von_neumann_embedding` gives an injective equivariant `Φ` from the
Schrödinger model into — this is the point — *itself*. An injective endomorphism of a
finite-dimensional space is surjective, so `Φ` is invertible, and its intertwining relation
`Φ ∘ π(x) = π(g·x) ∘ Φ` is precisely the Weil operator condition.

No rank restriction, no generation theorem, no metaplectic cover. -/
theorem hasWeilOperator_of_isSymplectic_svn (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) : HasWeilOperator h2 ψ g := by
  obtain ⟨Φ, hinj, hequiv⟩ := stone_von_neumann_embedding h2 hψ (twist h2 ψ hg) (twist_central h2 ψ hg)
    (delta_zero_ne_zero (F := F) (ι := ι))
  have hbij : Function.Bijective Φ := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e : ((ι → F) → ℂ) ≃ₗ[ℂ] ((ι → F) → ℂ) := LinearEquiv.ofBijective Φ hbij
  have hΦe : ∀ v, e v = Φ v := fun _ => rfl
  refine ⟨⟨Φ, (e.symm : ((ι → F) → ℂ) →ₗ[ℂ] ((ι → F) → ℂ)), ?_, ?_⟩, fun x => ?_⟩
  · refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply, Module.End.one_eq_id,
      LinearMap.id_apply]
    rw [← hΦe]
    exact e.apply_symm_apply v
  · refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply, Module.End.one_eq_id,
      LinearMap.id_apply]
    rw [← hΦe]
    exact e.symm_apply_apply v
  · have h := hequiv x
    rw [twist_apply] at h
    change Φ * schrodinger h2 ψ x = schrodinger h2 ψ (g x) * Φ
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact h

end Transport

end ECCLib.Heisenberg

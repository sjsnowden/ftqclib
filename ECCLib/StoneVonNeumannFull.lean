/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.StoneVonNeumann
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.SimpleModule.Isotypic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Stone–von Neumann, the full theorem

**`stone_von_neumann`**: every representation of
`Heis F ι` with nontrivial central character `ψ` is `ψ`-isotypic,

  `W ≅ ⊕_κ S`,  `S` the Schrödinger model, `Heis` acting diagonally,

with no nonzero hypothesis (`W = 0` takes `κ` empty), plus Schur uniqueness for equivalences
(`schrodinger_equiv_unique_smul`). Together with `stone_von_neumann_embedding` (the embedding) and
`stone_von_neumann_equiv` (the irreducible case) this is Prasad 0912.0574 §4.1's **decomposition**
half, in the finite odd-characteristic setting. *Not* delivered here: Prasad's uniqueness clause in
its general form, that the intertwiner space `Hom_Heis(S, W)` is `|κ|`-dimensional — what is proved
is the Schur case, for equivalences. In particular, **a representation with central character `ψ`
is determined by `ψ` together with a multiplicity set.**

**Scope: finite field of odd characteristic** (`(2 : F) ≠ 0`, which the Schrödinger model needs —
it is built from `(2 : F)⁻¹`). The characteristic-2 Heisenberg group is a different object and is
outside this file entirely.

Route: Mathlib's module-theoretic spine throughout. `ρ` *is* a `Representation ℂ (Heis F ι) W`
definitionally; `ρ.asModule` carries the `ℂ[Heis]`-structure; Maschke gives semisimplicity (finite
group, characteristic zero); `Subrepresentation.ofSubmodule'`/`.toRepresentation` cross between
invariant subspaces and `ℂ[Heis]`-submodules; each simple submodule is equivariantly the Schrödinger
model through `stone_von_neumann_equiv`; `IsIsotypicOfType.linearEquiv_finsupp` assembles the sum.
The one genuinely local step is the equivariant-`ℂ` → `ℂ[Heis]`-linear upgrade, by `Finsupp`
induction on the scalar.

In its own file so that changes here do not re-elaborate the Heisenberg development.
-/

namespace ECCLib.Heisenberg

open MonoidAlgebra

universe u

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

section Instances

variable [Fintype F]

/-- `Heis F ι` is the finite set `(ι → F) × (ι → F) × F`. -/
def heisEquivProd : Heis F ι ≃ (ι → F) × (ι → F) × F where
  toFun x := (x.pos, x.mom, x.cen)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩

instance : Finite (Heis F ι) := Finite.of_equiv _ (heisEquivProd (F := F) (ι := ι)).symm

instance : Nonempty (Heis F ι) := ⟨1⟩

end Instances

section Isotypy

variable [Fintype F] [DecidableEq ι]
variable {W : Type u} [AddCommGroup W] [Module ℂ W]

-- The set_option is Mathlib's own escape for `asModule` statements (see
-- `RepresentationTheory/Semisimple.lean`): the `Ring.toSemiring` diamond does not unify with the
-- concrete `ℂ` shortcut instances at instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Every simple `ℂ[Heis]`-submodule is the Schrödinger model** — the heart of part 2.
Simplicity transfers through the bridge to `stone_von_neumann_equiv`'s irreducibility hypothesis;
the equivariant `ℂ`-equivalence it returns upgrades to a `ℂ[Heis]`-equivalence by `Finsupp`
induction. -/
theorem isIsotypicOfType_schrodinger (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (ρ : Representation ℂ (Heis F ι) W)
    (hcen : ∀ s : F, ρ (Heis.central s) = ψ s • (1 : Module.End ℂ W)) :
    IsIsotypicOfType (MonoidAlgebra ℂ (Heis F ι)) ρ.asModule
      (Representation.asModule
        (schrodinger h2 ψ : Representation ℂ (Heis F ι) ((ι → F) → ℂ))) := by
  classical
  intro m hm
  set σ : Representation ℂ (Heis F ι) ((ι → F) → ℂ) := schrodinger h2 ψ with hσ
  have hatom : IsAtom m := isSimpleModule_iff_isAtom.mp hm
  -- the subrepresentation carried by `m` (Mathlib's bridge)
  set S' : Subrepresentation ρ := Subrepresentation.ofSubmodule' m with hS'
  set mV : Submodule ℂ W := S'.toSubmodule with hmV
  set ρN : Representation ℂ (Heis F ι) ↥mV := S'.toRepresentation with hρN
  have hcenN : ∀ s : F, ρN (Heis.central s) = ψ s • (1 : Module.End ℂ ↥mV) := by
    intro s
    ext v
    have h1 : ((ρN (Heis.central s)) v : W) = ρ (Heis.central s) v.1 := rfl
    rw [h1, hcen s]
    rfl
  -- a nonzero vector, from atomicity
  obtain ⟨x, hxm, hx0⟩ := (Submodule.ne_bot_iff m).mp hatom.1
  have hxV : ρ.asModuleEquiv x ∈ mV := Subrepresentation.mem_ofSubmodule'_iff.mpr hxm
  have hw0 : (⟨ρ.asModuleEquiv x, hxV⟩ : ↥mV) ≠ 0 := by
    intro hc
    apply hx0
    have h1 : ρ.asModuleEquiv x = 0 := congrArg Subtype.val hc
    exact ρ.asModuleEquiv.injective (by rw [h1, map_zero])
  -- irreducibility of the restriction, from atomicity through the rfl-transparent bridge
  have hirr : ∀ M : Submodule ℂ ↥mV, (∀ x : Heis F ι, ∀ v ∈ M, ρN x v ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    set M' : Submodule ℂ W := M.map mV.subtype with hM'
    have hM'le : M' ≤ mV := by
      rintro _ ⟨v, hv, rfl⟩; exact v.2
    have hM'inv : ∀ g : Heis F ι, ∀ w ∈ M', ρ g w ∈ M' := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨ρN g v, hM g v hv, rfl⟩
    set q := Subrepresentation.asSubmodule ⟨M', fun g v hv => hM'inv g v hv⟩ with hq
    have hqle : q ≤ m := by
      intro y hy
      have h1 : ρ.asModuleEquiv y ∈ M' := hy
      have h2' : ρ.asModuleEquiv y ∈ mV := hM'le h1
      exact Subrepresentation.mem_ofSubmodule'_iff.mp h2'
    rcases lt_or_eq_of_le hqle with hlt | heq
    · -- q < m forces q = ⊥, hence M = ⊥
      left
      have hqbot : q = ⊥ := hatom.2 _ hlt
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : (v : W) ∈ M' := ⟨v, hv, rfl⟩
      have hvq : ρ.asModuleEquiv.symm (v : W) ∈ q := hv'
      rw [hqbot, Submodule.mem_bot] at hvq
      exact Subtype.ext hvq
    · -- q = m forces M = ⊤
      right
      rw [Submodule.eq_top_iff']
      intro v
      have hvq : ρ.asModuleEquiv.symm (v : W) ∈ q := by
        rw [heq]
        exact Subrepresentation.mem_ofSubmodule'_iff.mp v.2
      have hvM' : (v : W) ∈ M' := hvq
      obtain ⟨u, hu, huv⟩ := hvM'
      have : u = v := Subtype.ext huv
      rwa [← this]
  -- the irreducible case delivers the equivariant equivalence
  obtain ⟨e, he⟩ := stone_von_neumann_equiv h2 hψ ρN hcenN hw0 hirr
  have hept : ∀ (g : Heis F ι) (s : (ι → F) → ℂ),
      e (schrodinger h2 ψ g s) = ρN g (e s) := by
    intro g s
    have h := congrArg (fun T : ((ι → F) → ℂ) →ₗ[ℂ] ↥mV => T s) (he g)
    simpa using h
  have hesymm : ∀ (g : Heis F ι) (v : ↥mV),
      e.symm (ρN g v) = schrodinger h2 ψ g (e.symm v) := by
    intro g v
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, hept, LinearEquiv.apply_symm_apply]
  -- `↥m ≃ₗ[ℂ] ↥mV`, pointwise the identity through `asModuleEquiv`
  set mEquivMV : ↥m ≃ₗ[ℂ] ↥mV :=
    { toFun := fun y => ⟨ρ.asModuleEquiv y.1, Subrepresentation.mem_ofSubmodule'_iff.mpr y.2⟩
      invFun := fun v => ⟨ρ.asModuleEquiv.symm v.1, Subrepresentation.mem_ofSubmodule'_iff.mp v.2⟩
      map_add' := by intro a b; apply Subtype.ext; simp
      map_smul' := by intro c a; apply Subtype.ext; simp
      left_inv := by intro y; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp } with hmEquivMV
  -- the composite ℂ-equivalence `↥m ≃ S`, then transported to `σ.asModule`
  set Tc : ↥m ≃ₗ[ℂ] σ.asModule :=
    (mEquivMV.trans e.symm).trans σ.asModuleEquiv.symm with hTc
  -- upgrade to `ℂ[Heis]`-linearity
  refine ⟨{ toFun := Tc, invFun := Tc.symm,
            left_inv := Tc.left_inv, right_inv := Tc.right_inv,
            map_add' := map_add Tc, map_smul' := ?_ }⟩
  intro r y
  simp only [RingHom.id_apply]
  induction r using Finsupp.induction_linear with
  | zero => simp only [zero_smul, map_zero]
  | add f g hf hg => simp only [add_smul, map_add, hf, hg]
  | single g c =>
      -- LHS through the four layers; RHS through `single g c = c • of g` and the tower
      have hval : ((single g c • y : ↥m) : ρ.asModule)
          = (single g c : MonoidAlgebra ℂ (Heis F ι)) • (y : ρ.asModule) := rfl
      have step1 : mEquivMV (single g c • y) = c • ρN g (mEquivMV y) := by
        apply Subtype.ext
        change ρ.asModuleEquiv ((single g c • y : ↥m) : ρ.asModule) = _
        rw [hval, ρ.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
          LinearMap.smul_apply]
        rfl
      have step2 : e.symm (c • ρN g (mEquivMV y))
          = c • schrodinger h2 ψ g (e.symm (mEquivMV y)) := by
        rw [map_smul, hesymm]
      have step3 : σ.asModuleEquiv.symm (c • schrodinger h2 ψ g (e.symm (mEquivMV y)))
          = c • (MonoidAlgebra.of ℂ (Heis F ι) g • σ.asModuleEquiv.symm (e.symm (mEquivMV y))) := by
        rw [map_smul]
        congr 1
        exact σ.asModuleEquiv_symm_map_rho g _
      change Tc (single g c • y) = single g c • Tc y
      have hTcy : Tc y = σ.asModuleEquiv.symm (e.symm (mEquivMV y)) := rfl
      have hTcs : Tc (single g c • y)
          = σ.asModuleEquiv.symm (e.symm (mEquivMV (single g c • y))) := rfl
      have hsingle_of : (single g c : MonoidAlgebra ℂ (Heis F ι))
          = c • MonoidAlgebra.of ℂ (Heis F ι) g := by
        rw [MonoidAlgebra.of_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hTcs, step1, step2, step3, hTcy, hsingle_of, smul_assoc]

end Isotypy

section Full

variable [Fintype F] [DecidableEq ι]
variable {W : Type u} [AddCommGroup W] [Module ℂ W]

set_option backward.isDefEq.respectTransparency false in
/-- **STONE–VON NEUMANN** — the decomposition theorem, finite field of **odd characteristic**
(`h2 : (2 : F) ≠ 0`; Prasad 0912.0574 §4.1). Every representation of the Heisenberg group with
nontrivial central character `ψ` is a direct sum of copies of the Schrödinger model, with `Heis`
acting diagonally:

  `W ≃ₗ (κ →₀ ℂ[𝔽_q^ι])`  intertwining `ρ` with the pointwise Schrödinger action.

No nonzero hypothesis: `W = 0` takes `κ` empty. The determinacy statement is exactly this:
**`ρ` is determined by `ψ` together with a
multiplicity set `κ`.** The Schur-type uniqueness available here is
`schrodinger_equiv_unique_smul` (for *equivalences*; the general `Hom`-space statement is not
proved); the embedding and irreducible cases are `stone_von_neumann_embedding` /
`stone_von_neumann_equiv`.

Proof: Maschke (finite group, characteristic zero) makes `ρ.asModule` semisimple over `ℂ[Heis]`;
`isIsotypicOfType_schrodinger` identifies every simple submodule with the Schrödinger model through
`stone_von_neumann_equiv`; Mathlib's `IsIsotypicOfType.linearEquiv_finsupp` assembles the sum, and
the `ℂ[Heis]`-equivalence unpacks to the stated `ℂ`-linear equivariant one. -/
theorem stone_von_neumann (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (ρ : Heis F ι →* Module.End ℂ W)
    (hcen : ∀ s : F, ρ (Heis.central s) = ψ s • (1 : Module.End ℂ W)) :
    ∃ (κ : Type u) (e : W ≃ₗ[ℂ] (κ →₀ ((ι → F) → ℂ))),
      ∀ (x : Heis F ι) (w : W),
        e (ρ x w) = Finsupp.mapRange ⇑(schrodinger h2 ψ x) (map_zero _) (e w) := by
  classical
  haveI : NeZero ((Nat.card (Heis F ι) : ℂ)) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set ρ' : Representation ℂ (Heis F ι) W := ρ with hρ'
  set σ : Representation ℂ (Heis F ι) ((ι → F) → ℂ) := schrodinger h2 ψ with hσ
  obtain ⟨κ, ⟨E⟩⟩ := (isIsotypicOfType_schrodinger h2 hψ ρ' hcen).linearEquiv_finsupp
  -- ℂ-smul agrees with `algebraMap`-smul on both `asModule`s
  have hsmulρ : ∀ (c : ℂ) (x : ρ'.asModule),
      algebraMap ℂ (MonoidAlgebra ℂ (Heis F ι)) c • x = c • x := by
    intro c x
    have h := ρ'.asModuleEquiv_symm_map_smul c (ρ'.asModuleEquiv x)
    rw [map_smul, LinearEquiv.symm_apply_apply] at h
    exact h.symm
  have hsmulσ : ∀ (c : ℂ) (s : σ.asModule),
      algebraMap ℂ (MonoidAlgebra ℂ (Heis F ι)) c • s = c • s := by
    intro c s
    have h := σ.asModuleEquiv_symm_map_smul c (σ.asModuleEquiv s)
    rw [map_smul, LinearEquiv.symm_apply_apply] at h
    exact h.symm
  -- the assembled ℂ-linear equivalence, equivariance proved first on the raw function
  set Φ : W → (κ →₀ ((ι → F) → ℂ)) := fun w =>
    Finsupp.mapRange ⇑σ.asModuleEquiv (map_zero _) (E (ρ'.asModuleEquiv.symm w)) with hΦ
  have hequi : ∀ (x : Heis F ι) (w : W),
      Φ (ρ x w) = Finsupp.mapRange ⇑(schrodinger h2 ψ x) (map_zero _) (Φ w) := by
    intro x w
    simp only [hΦ]
    ext k
    simp only [Finsupp.mapRange_apply]
    rw [ρ'.asModuleEquiv_symm_map_rho, map_smul, Finsupp.smul_apply,
      σ.asModuleEquiv_map_smul, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single,
      one_smul]
  refine ⟨κ,
    { toFun := Φ
      invFun := fun v =>
        ρ'.asModuleEquiv (E.symm (Finsupp.mapRange ⇑σ.asModuleEquiv.symm (map_zero _) v))
      map_add' := by
        intro a b
        simp only [hΦ, map_add]
        refine Finsupp.ext fun k => ?_
        rw [Finsupp.mapRange_apply, Finsupp.add_apply, map_add, Finsupp.add_apply,
          Finsupp.mapRange_apply, Finsupp.mapRange_apply]
      map_smul' := by
        intro c w
        simp only [RingHom.id_apply, hΦ]
        rw [map_smul, ← hsmulρ c, map_smul]
        ext k
        rw [Finsupp.mapRange_apply, Finsupp.smul_apply, hsmulσ, map_smul,
          Finsupp.smul_apply, Finsupp.mapRange_apply]
      left_inv := by
        intro w
        simp only [hΦ]
        have h1 : Finsupp.mapRange ⇑σ.asModuleEquiv.symm (map_zero _)
            (Finsupp.mapRange ⇑σ.asModuleEquiv (map_zero _) (E (ρ'.asModuleEquiv.symm w)))
            = E (ρ'.asModuleEquiv.symm w) := by
          ext k
          simp [Finsupp.mapRange_apply]
        rw [h1, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
      right_inv := by
        intro v
        simp only [hΦ]
        rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
        ext k
        simp [Finsupp.mapRange_apply] }, ?_⟩
  intro x w
  exact hequi x w

/-- **Schur uniqueness for equivariant equivalences**: two equivariant *isomorphisms* from the
Schrödinger model onto the same representation differ by a nonzero scalar. This is
`schrodinger_irreducible` (Schur) in applied form.

**Scope.** This quantifies over `≃ₗ`, not over arbitrary intertwiners `S →ₗ W'`. Prasad's general
uniqueness clause — that `Hom_Heis(S, W)` is `|κ|`-dimensional, so intertwiners are determined up to
the multiplicity space — is *not* proved here; for `|κ| ≥ 2` no equivalence `S ≃ W` exists and this
statement is vacuous. -/
theorem schrodinger_equiv_unique_smul {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (τ : Heis F ι →* Module.End ℂ W')
    {e₁ e₂ : ((ι → F) → ℂ) ≃ₗ[ℂ] W'}
    (he₁ : ∀ x, (e₁ : ((ι → F) → ℂ) →ₗ[ℂ] W') ∘ₗ schrodinger h2 ψ x
      = τ x ∘ₗ (e₁ : ((ι → F) → ℂ) →ₗ[ℂ] W'))
    (he₂ : ∀ x, (e₂ : ((ι → F) → ℂ) →ₗ[ℂ] W') ∘ₗ schrodinger h2 ψ x
      = τ x ∘ₗ (e₂ : ((ι → F) → ℂ) →ₗ[ℂ] W')) :
    ∃ c : ℂ, c ≠ 0 ∧ (e₁ : ((ι → F) → ℂ) →ₗ[ℂ] W') = c • (e₂ : ((ι → F) → ℂ) →ₗ[ℂ] W') := by
  classical
  set f : Module.End ℂ ((ι → F) → ℂ) :=
    (e₂.symm : W' →ₗ[ℂ] ((ι → F) → ℂ)) ∘ₗ (e₁ : ((ι → F) → ℂ) →ₗ[ℂ] W') with hf
  have hpt1 : ∀ x s, e₁ (schrodinger h2 ψ x s) = τ x (e₁ s) := by
    intro x s
    have h := congrArg (fun T : ((ι → F) → ℂ) →ₗ[ℂ] W' => T s) (he₁ x)
    simpa using h
  have hpt2 : ∀ x (v : W'), e₂.symm (τ x v) = schrodinger h2 ψ x (e₂.symm v) := by
    intro x v
    apply e₂.injective
    rw [LinearEquiv.apply_symm_apply]
    have h := congrArg (fun T : ((ι → F) → ℂ) →ₗ[ℂ] W' => T (e₂.symm v)) (he₂ x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hcomm : ∀ x : Heis F ι, f * schrodinger h2 ψ x = schrodinger h2 ψ x * f := by
    intro x
    refine LinearMap.ext fun s => ?_
    change e₂.symm (e₁ (schrodinger h2 ψ x s)) = schrodinger h2 ψ x (e₂.symm (e₁ s))
    rw [hpt1, hpt2]
  obtain ⟨c, hc⟩ := schrodinger_irreducible h2 hψ f hcomm
  refine ⟨c, ?_, ?_⟩
  · intro h0
    have hfz : f = 0 := by rw [hc, h0, zero_smul]
    have h1 : e₂.symm (e₁ (delta (0 : ι → F))) = 0 := by
      have h2' : f (delta (0 : ι → F)) = 0 := by rw [hfz]; exact LinearMap.zero_apply _
      exact h2'
    have h2' : e₁ (delta (0 : ι → F)) = 0 := by
      have h3 := congrArg e₂ h1
      rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
    have h4 : (delta (0 : ι → F) : (ι → F) → ℂ) = 0 :=
      e₁.injective (by rw [h2', map_zero])
    have h5 := congrFun h4 0
    simp [delta] at h5
  · refine LinearMap.ext fun s => ?_
    rw [LinearMap.smul_apply]
    have h1 : f s = c • s := by
      rw [hc]
      rfl
    have h2' := congrArg e₂ h1
    rw [map_smul] at h2'
    have h3 : e₂ (f s) = e₁ s := by
      change e₂ (e₂.symm (e₁ s)) = e₁ s
      rw [LinearEquiv.apply_symm_apply]
    rw [h3] at h2'
    simpa using h2'

end Full

end ECCLib.Heisenberg

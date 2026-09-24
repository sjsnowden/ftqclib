/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.WeilRepresentation
import ECCLib.WeilGenerationComplete

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The metaplectic group and the Weil representation as an actual representation

The `Sp` results of the preceding files conclude `HasWeilOperator h2 ψ g` — a bare `Prop` asserting
that *some* intertwiner exists; by themselves they give no `g ↦ W(g)`, no homomorphism, no
cocycle. This file builds the representation itself, by the **fibre-product** route rather than
by choosing a section into a quotient:

* **`Sp`** — the isometries of `ω`, packaged as a genuine `Subgroup (W ≃ₗ[F] W)`. This is the group
  object a representation is a representation *of*: `Heis.IsSymplectic` is a bespoke predicate on
  raw functions, not a group.
* **`heisOfSp`** — the bridge carrying a linear symplectic `T` to the Heisenberg map it induces
  (act on position/momentum, leave the centre alone). Multiplicative, and `Heis.IsSymplectic`.
* **`Mp`** — the **metaplectic group**: the pairs `(T, U)` with `U` a Weil operator for `T`, a
  subgroup of `Sp × GL(V)`. Closure is exactly `hasWeilOperator_id` / `.comp` / `.inv`.
* **`weilMp : Mp →* GL(V)`** — the **linear metaplectic representation**, literally the second
  projection; its intertwining property holds by construction.
* **`mpProj : Mp →* Sp`** — the covering projection: **surjective** (every symplectic map has a Weil
  operator, `hasWeilOperator_of_isSymplectic_svn`) with **central kernel consisting of scalars**
  (Schur, via `weil_operator_unique`'s engine `schrodinger_irreducible`). That is the central
  extension `1 → ℂˣ → Mp → Sp → 1`.

All of this is unconditional — no cocycle triviality, no cover-splitting assumption. Only the
*splitting* of `mpProj` (a linear representation of `Sp` itself) needs the odd-`q` argument; it is
not claimed here (it is `mpProj_splits` in `WeilSplitting.lean`).
-/

namespace ECCLib.Metaplectic

open ECCLib.Heisenberg ECCLib.Siegel

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The symplectic group as a group object -/

/-- **The symplectic group `Sp`**, as a genuine `Subgroup` of the linear automorphisms of `W`:
the isometries of `ω`. Closure is the existing `isSymplecticEquiv_one/mul/inv`. -/
def Sp (F : Type*) [Field F] (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (W F ι ≃ₗ[F] W F ι) where
  carrier := {T | SpGen.IsSymplecticEquiv (omega (F := F) (ι := ι)) T}
  one_mem' := SpGen.isSymplecticEquiv_one _
  mul_mem' ha hb := SpGen.isSymplecticEquiv_mul _ ha hb
  inv_mem' ha := SpGen.isSymplecticEquiv_inv _ ha

@[simp] theorem mem_Sp {T : W F ι ≃ₗ[F] W F ι} :
    T ∈ Sp F ι ↔ SpGen.IsSymplecticEquiv (omega (F := F) (ι := ι)) T := Iff.rfl

/-- The Heisenberg map induced by a linear symplectic `T`: act on position and momentum, leave the
centre coordinate alone. -/
def heisOfSp (T : W F ι ≃ₗ[F] W F ι) (x : Heis F ι) : Heis F ι :=
  ⟨(T (x.pos, x.mom)).1, (T (x.pos, x.mom)).2, x.cen⟩

@[simp] theorem heisOfSp_pos (T : W F ι ≃ₗ[F] W F ι) (x : Heis F ι) :
    (heisOfSp T x).pos = (T (x.pos, x.mom)).1 := rfl

@[simp] theorem heisOfSp_mom (T : W F ι ≃ₗ[F] W F ι) (x : Heis F ι) :
    (heisOfSp T x).mom = (T (x.pos, x.mom)).2 := rfl

@[simp] theorem heisOfSp_cen (T : W F ι ≃ₗ[F] W F ι) (x : Heis F ι) :
    (heisOfSp T x).cen = x.cen := rfl

@[simp] theorem heisOfSp_one : heisOfSp (1 : W F ι ≃ₗ[F] W F ι) = id := by
  funext x
  exact Heis.ext rfl rfl rfl

theorem heisOfSp_mul (T T' : W F ι ≃ₗ[F] W F ι) :
    heisOfSp (T * T') = heisOfSp T ∘ heisOfSp T' := by
  funext x
  exact Heis.ext rfl rfl rfl

/-- `heisOfSp` of the inverse undoes `heisOfSp` — the form the subgroup's `inv_mem` needs. -/
theorem heisOfSp_apply_inv (T : W F ι ≃ₗ[F] W F ι) (x : Heis F ι) :
    heisOfSp T (heisOfSp T⁻¹ x) = x := by
  have h := heisOfSp_mul T T⁻¹
  rw [mul_inv_cancel, heisOfSp_one] at h
  exact congrFun h.symm x

/-- **The induced Heisenberg map is symplectic** — the bridge that lets the `Sp`-side group index
the Heis-side Weil operators. `map_symp` is `ω`-preservation verbatim: `ω` and `symp` agree
definitionally on position/momentum. -/
theorem isSymplectic_heisOfSp {T : W F ι ≃ₗ[F] W F ι} (hT : T ∈ Sp F ι) :
    Heis.IsSymplectic (heisOfSp T) where
  map_pos x y := by
    have hadd : ((x * y).pos, (x * y).mom)
        = ((x.pos, x.mom) + (y.pos, y.mom) : W F ι) := rfl
    change (T ((x * y).pos, (x * y).mom)).1
      = (T (x.pos, x.mom)).1 + (T (y.pos, y.mom)).1
    rw [hadd, map_add]
    rfl
  map_mom x y := by
    have hadd : ((x * y).pos, (x * y).mom)
        = ((x.pos, x.mom) + (y.pos, y.mom) : W F ι) := rfl
    change (T ((x * y).pos, (x * y).mom)).2
      = (T (x.pos, x.mom)).2 + (T (y.pos, y.mom)).2
    rw [hadd, map_add]
    rfl
  map_cen _ := rfl
  map_symp x y := hT (x.pos, x.mom) (y.pos, y.mom)

/-! ## The metaplectic group, the linear representation, the central extension -/

/-- `U` **intertwines** the Schrödinger representation along the symplectic `T`. -/
def Intertwines (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    (T : W F ι ≃ₗ[F] W F ι) (U : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Prop :=
  ∀ x : Heis F ι, (U : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
    = schrodinger h2 ψ (heisOfSp T x) * (U : Module.End ℂ ((ι → F) → ℂ))

/-- **The metaplectic group** `Mp`: pairs `(T, U)` with `U` a Weil operator for `T`. Closure under
the group operations is exactly the three existing lemmas about Weil operators. -/
def Mp (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) :
    Subgroup (↥(Sp F ι) × (Module.End ℂ ((ι → F) → ℂ))ˣ) where
  carrier := {p | Intertwines h2 ψ (p.1 : W F ι ≃ₗ[F] W F ι) p.2}
  one_mem' := by
    intro x
    simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one, heisOfSp_one, id_eq,
      Units.val_one, one_mul, mul_one]
  mul_mem' := by
    intro a b ha hb x
    have hcoe : ((a * b).1 : W F ι ≃ₗ[F] W F ι)
        = (a.1 : W F ι ≃ₗ[F] W F ι) * (b.1 : W F ι ≃ₗ[F] W F ι) := rfl
    have hstep : heisOfSp ((a * b).1 : W F ι ≃ₗ[F] W F ι) x
        = heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι) (heisOfSp (b.1 : W F ι ≃ₗ[F] W F ι) x) := by
      rw [hcoe, heisOfSp_mul]
      rfl
    rw [hstep, Prod.snd_mul, Units.val_mul]
    calc (a.2 : Module.End ℂ ((ι → F) → ℂ)) * (b.2 : Module.End ℂ ((ι → F) → ℂ))
          * schrodinger h2 ψ x
        = (a.2 : Module.End ℂ ((ι → F) → ℂ))
            * ((b.2 : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x) := by rw [mul_assoc]
      _ = (a.2 : Module.End ℂ ((ι → F) → ℂ))
            * (schrodinger h2 ψ (heisOfSp (b.1 : W F ι ≃ₗ[F] W F ι) x)
              * (b.2 : Module.End ℂ ((ι → F) → ℂ))) := by rw [hb x]
      _ = ((a.2 : Module.End ℂ ((ι → F) → ℂ))
            * schrodinger h2 ψ (heisOfSp (b.1 : W F ι ≃ₗ[F] W F ι) x))
              * (b.2 : Module.End ℂ ((ι → F) → ℂ)) := by rw [mul_assoc]
      _ = (schrodinger h2 ψ (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)
            (heisOfSp (b.1 : W F ι ≃ₗ[F] W F ι) x))
            * (a.2 : Module.End ℂ ((ι → F) → ℂ)))
              * (b.2 : Module.End ℂ ((ι → F) → ℂ)) := by rw [ha _]
      _ = schrodinger h2 ψ (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)
            (heisOfSp (b.1 : W F ι ≃ₗ[F] W F ι) x))
            * ((a.2 : Module.End ℂ ((ι → F) → ℂ))
              * (b.2 : Module.End ℂ ((ι → F) → ℂ))) := by rw [mul_assoc]
  inv_mem' := by
    intro a ha x
    have hcoe : ((a⁻¹).1 : W F ι ≃ₗ[F] W F ι) = (a.1 : W F ι ≃ₗ[F] W F ι)⁻¹ := rfl
    have hcoe2 : ((a⁻¹).2 : (Module.End ℂ ((ι → F) → ℂ))ˣ) = (a.2)⁻¹ := rfl
    -- the hypothesis at the shifted point, using `heisOfSp T (heisOfSp T⁻¹ x) = x`
    have hkey := ha (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)⁻¹ x)
    rw [heisOfSp_apply_inv] at hkey
    have hL : (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ))
          * ((a.2 : Module.End ℂ ((ι → F) → ℂ))
            * schrodinger h2 ψ (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)⁻¹ x))
          * (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ))
        = schrodinger h2 ψ (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)⁻¹ x)
          * (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ)) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    have hR : (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ))
          * (schrodinger h2 ψ x * (a.2 : Module.End ℂ ((ι → F) → ℂ)))
          * (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ))
        = (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x := by
      rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    rw [hcoe, hcoe2]
    calc (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ))
            * (schrodinger h2 ψ x * (a.2 : Module.End ℂ ((ι → F) → ℂ)))
            * (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ)) := hR.symm
      _ = (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ))
            * ((a.2 : Module.End ℂ ((ι → F) → ℂ))
              * schrodinger h2 ψ (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)⁻¹ x))
            * (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ)) := by rw [hkey]
      _ = schrodinger h2 ψ (heisOfSp (a.1 : W F ι ≃ₗ[F] W F ι)⁻¹ x)
            * (↑a.2⁻¹ : Module.End ℂ ((ι → F) → ℂ)) := hL

/-- **The linear metaplectic representation** — the second projection `Mp → GL(V)`. This is the
representation the whole `Sp` half of the library builds toward: a genuine `MonoidHom`,
not an existence statement. -/
noncomputable def weilMp (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) :
    ↥(Mp (ι := ι) h2 ψ) →* (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  (MonoidHom.snd _ _).comp (Mp h2 ψ).subtype

/-- **The covering projection** `Mp → Sp`. -/
noncomputable def mpProj (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) :
    ↥(Mp (ι := ι) h2 ψ) →* ↥(Sp F ι) :=
  (MonoidHom.fst _ _).comp (Mp h2 ψ).subtype

/-- **The defining property of the metaplectic representation**: `weilMp m` intertwines the
Schrödinger representation along the symplectic map `mpProj m`. Holds by construction. -/
theorem weilMp_intertwines (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    (m : ↥(Mp (ι := ι) h2 ψ)) (x : Heis F ι) :
    (weilMp h2 ψ m : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
      = schrodinger h2 ψ (heisOfSp ((mpProj h2 ψ m : ↥(Sp F ι)) : W F ι ≃ₗ[F] W F ι) x)
        * (weilMp h2 ψ m : Module.End ℂ ((ι → F) → ℂ)) :=
  m.2 x

/-- **The covering is surjective**: every symplectic map is covered by a metaplectic element. This
is where every-rank existence (`hasWeilOperator_of_isSymplectic_svn`) enters. -/
theorem mpProj_surjective (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    Function.Surjective (mpProj (ι := ι) h2 ψ) := by
  rintro ⟨T, hT⟩
  obtain ⟨U, hU⟩ := hasWeilOperator_of_isSymplectic_svn h2 hψ (isSymplectic_heisOfSp hT)
  exact ⟨⟨(⟨T, hT⟩, U), hU⟩, rfl⟩

/-- **The kernel consists of scalars** — Schur. An element covering the identity is an operator
commuting with the whole Heisenberg group, hence a scalar. With `mpProj_surjective` this is the
central extension `1 → ℂˣ → Mp → Sp → 1`. -/
theorem ker_mpProj_scalar (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {m : ↥(Mp (ι := ι) h2 ψ)} (hm : m ∈ (mpProj h2 ψ).ker) :
    ∃ c : ℂ, (weilMp h2 ψ m : Module.End ℂ ((ι → F) → ℂ)) = c • LinearMap.id := by
  have hT : (m.1.1 : W F ι ≃ₗ[F] W F ι) = 1 := by
    have := MonoidHom.mem_ker.mp hm
    exact congrArg (fun z : ↥(Sp F ι) => (z : W F ι ≃ₗ[F] W F ι)) this
  refine schrodinger_irreducible h2 hψ _ fun x => ?_
  have hx := m.2 x
  rw [hT, heisOfSp_one] at hx
  exact hx

/-- The kernel is central. -/
theorem ker_mpProj_le_center (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (mpProj (ι := ι) h2 ψ).ker ≤ Subgroup.center _ := by
  intro m hm
  obtain ⟨c, hc⟩ := ker_mpProj_scalar h2 hψ hm
  have hT : (m.1.1 : W F ι ≃ₗ[F] W F ι) = 1 := by
    have := MonoidHom.mem_ker.mp hm
    exact congrArg (fun z : ↥(Sp F ι) => (z : W F ι ≃ₗ[F] W F ι)) this
  rw [Subgroup.mem_center_iff]
  intro n
  refine Subtype.ext (Prod.ext ?_ ?_)
  · refine Subtype.ext ?_
    change (n.1.1 : W F ι ≃ₗ[F] W F ι) * (m.1.1 : W F ι ≃ₗ[F] W F ι)
      = (m.1.1 : W F ι ≃ₗ[F] W F ι) * (n.1.1 : W F ι ≃ₗ[F] W F ι)
    rw [hT, mul_one, one_mul]
  · refine Units.ext ?_
    change (n.1.2 : Module.End ℂ ((ι → F) → ℂ)) * (m.1.2 : Module.End ℂ ((ι → F) → ℂ))
      = (m.1.2 : Module.End ℂ ((ι → F) → ℂ)) * (n.1.2 : Module.End ℂ ((ι → F) → ℂ))
    have hm2 : (m.1.2 : Module.End ℂ ((ι → F) → ℂ)) = c • LinearMap.id := hc
    rw [hm2]
    refine LinearMap.ext fun v => ?_
    simp [Module.End.mul_eq_comp, LinearMap.smul_apply]

end ECCLib.Metaplectic

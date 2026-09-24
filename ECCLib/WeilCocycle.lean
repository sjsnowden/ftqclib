/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.WeilCharacter

set_option linter.unusedSectionVars false
-- As in `Heisenberg.lean`: instances used in proofs, not statements.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The canonical trace-1 section and the computable metaplectic cocycle

`WeilCharacter.lean` proves that every Weil operator has nonzero trace (`weilTrace_ne_zero`);
this file uses it:

* `weilNorm` — **the canonical trace-1 Weil operator** of a symplectic `g`: rescale any witness to
  trace `1`. Canonical means canonical: `weilNorm_unique` shows *any* trace-1 intertwiner equals
  it, so the definition does not depend on the existence proof or the witness chosen.
  This is the canonical choice referred to in the `weilUnit` docstring;
* `weilCocycle` — **the metaplectic 2-cocycle, explicitly computable**:
  `c(g,h) := Tr(W_g · W_h)`, a trace pairing of canonical operators;
* `weilNorm_mul` — the defect equation `W_g · W_h = c(g,h) • W_{g∘h}`: the failure of the
  canonical section to be a homomorphism is exactly `c`;
* `weilCocycle_cocycle` — **the 2-cocycle law** `c(g,h)·c(g∘h,k) = c(g,h∘k)·c(h,k)`, proved by
  evaluating `Tr(W_g W_h W_k)` on both associations — no triple-composite section is ever formed;
* `weilCocycle_ne_zero` — `c` lands in ℂˣ (immediate from `weilTrace_ne_zero` applied to the
  product);
* witnesses: `weilNorm_id = n⁻¹ • 1` and `c(id, g) = c(g, id) = n⁻¹` — the trace-1 section is
  canonical but **not unital** (`c(1,1) ≠ 1`). The unital rescaling `g ↦ n • W_g` has cocycle
  `n·c`; cohomologous, so nothing is lost, and trace-1 is what the trace pairing computes with.

Whether `c` is a coboundary — equivalently whether `mpProj` splits — is not decided here; nothing
here assumes an answer. It is settled in `WeilSplitting.lean` (`weilCocycle_isCoboundary`,
`mpProj_splits`).
-/

namespace ECCLib.WeilCharacter

open ECCLib.Heisenberg ECCLib.WeilComplete

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Rescaling units and composing intertwiners -/

/-- Rescale a unit of `End` by a nonzero scalar. -/
noncomputable def unitSmul (c : ℂ) (hc : c ≠ 0) (W : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
    (Module.End ℂ ((ι → F) → ℂ))ˣ where
  val := c • (W : Module.End ℂ ((ι → F) → ℂ))
  inv := c⁻¹ • ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
  val_inv := by
    rw [smul_mul_smul_comm, Units.mul_inv, mul_inv_cancel₀ hc, one_smul]
  inv_val := by
    rw [smul_mul_smul_comm, Units.inv_mul, inv_mul_cancel₀ hc, one_smul]

@[simp] lemma unitSmul_val (c : ℂ) (hc : c ≠ 0) (W : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
    ((unitSmul c hc W : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = c • (W : Module.End ℂ ((ι → F) → ℂ)) := rfl

/-- A rescaled intertwiner intertwines: scalars commute through the relation. -/
lemma smul_intertwines (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} {g : Heis F ι → Heis F ι} (c : ℂ)
    {W : Module.End ℂ ((ι → F) → ℂ)}
    (hW : ∀ x, W * schrodinger h2 ψ x = schrodinger h2 ψ (g x) * W) (x : Heis F ι) :
    (c • W) * schrodinger h2 ψ x = schrodinger h2 ψ (g x) * (c • W) := by
  rw [smul_mul_assoc, hW x, mul_smul_comm]

/-- **Products of intertwiners intertwine the composite** — `HasWeilOperator.comp`'s computation at
the `End` level, for the canonical-section bookkeeping. -/
lemma mul_intertwines (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} {g h : Heis F ι → Heis F ι}
    {Wg Wh : Module.End ℂ ((ι → F) → ℂ)}
    (hWg : ∀ x, Wg * schrodinger h2 ψ x = schrodinger h2 ψ (g x) * Wg)
    (hWh : ∀ x, Wh * schrodinger h2 ψ x = schrodinger h2 ψ (h x) * Wh) (x : Heis F ι) :
    (Wg * Wh) * schrodinger h2 ψ x = schrodinger h2 ψ ((g ∘ h) x) * (Wg * Wh) := by
  calc (Wg * Wh) * schrodinger h2 ψ x
      = Wg * (Wh * schrodinger h2 ψ x) := by rw [mul_assoc]
    _ = Wg * (schrodinger h2 ψ (h x) * Wh) := by rw [hWh x]
    _ = (Wg * schrodinger h2 ψ (h x)) * Wh := by rw [mul_assoc]
    _ = (schrodinger h2 ψ (g (h x)) * Wg) * Wh := by rw [hWg (h x)]
    _ = schrodinger h2 ψ ((g ∘ h) x) * (Wg * Wh) := by rw [mul_assoc]; rfl

/-! ## The canonical trace-1 section -/

/-- **The canonical trace-1 Weil operator** of a symplectic `g`: the explicit-route witness,
rescaled to trace `1` — legitimate by `weilTrace_ne_zero`. By `weilNorm_unique` below,
this is *the* trace-1 intertwiner: the definition's apparent dependence on the witness is gone.
No choice beyond the witness enters, and the witness washes out — this is the canonical section
the cocycle `weilCocycle` is built on. -/
noncomputable def weilNorm (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) : (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  let hop := hasWeilOperator_of_isSymplectic_explicit h2 hψ hg
  unitSmul (LinearMap.trace ℂ ((ι → F) → ℂ) ((weilUnit hop : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
      Module.End ℂ ((ι → F) → ℂ)))⁻¹
    (inv_ne_zero (weilTrace_ne_zero h2 hψ hg (weilUnit hop) (weilUnit_spec hop)))
    (weilUnit hop)

/-- The canonical operator intertwines. -/
theorem weilNorm_intertwines (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (x : Heis F ι) :
    ((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * schrodinger h2 ψ x
      = schrodinger h2 ψ (g x)
        * ((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) := by
  unfold weilNorm
  exact smul_intertwines h2 _
    (weilUnit_spec (hasWeilOperator_of_isSymplectic_explicit h2 hψ hg)) x

/-- The canonical operator has trace `1`. -/
theorem trace_weilNorm (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    LinearMap.trace ℂ ((ι → F) → ℂ)
      ((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) = 1 := by
  unfold weilNorm
  rw [unitSmul_val, map_smul, smul_eq_mul,
    inv_mul_cancel₀ (weilTrace_ne_zero h2 hψ hg _
      (weilUnit_spec (hasWeilOperator_of_isSymplectic_explicit h2 hψ hg)))]

/-- **Canonicity**: any trace-1 intertwiner for `g` *is* `weilNorm` — the section depends on no
choice. Schur (`weil_operator_unique`) gives the scalar; the trace pins it to `1`. -/
theorem weilNorm_unique (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g)
    (W' : (Module.End ℂ ((ι → F) → ℂ))ˣ)
    (hW' : ∀ x, (W' : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (g x) * (W' : Module.End ℂ ((ι → F) → ℂ)))
    (htr : LinearMap.trace ℂ ((ι → F) → ℂ) (W' : Module.End ℂ ((ι → F) → ℂ)) = 1) :
    W' = weilNorm h2 hψ hg := by
  obtain ⟨c, hc⟩ := weil_operator_unique h2 hψ (weilNorm h2 hψ hg)
    (W' : Module.End ℂ ((ι → F) → ℂ)) (weilNorm_intertwines h2 hψ hg) hW'
  have hc1 : c = 1 := by
    have h := congrArg (LinearMap.trace ℂ ((ι → F) → ℂ)) hc
    rw [htr, map_smul, smul_eq_mul, trace_weilNorm h2 hψ hg, mul_one] at h
    exact h.symm
  rw [hc1, one_smul] at hc
  exact Units.ext hc

/-! ## The computable cocycle -/

/-- **The metaplectic 2-cocycle, explicitly computable**: `c(g,h) := Tr(W_g · W_h)` — a trace
pairing of the canonical operators. `weilNorm_mul` shows it is exactly the multiplicativity
defect of the canonical section; `WeilSplitting.lean` shows it is a coboundary
(`weilCocycle_isCoboundary`). -/
noncomputable def weilCocycle (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g h : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (hh : Heis.IsSymplectic h) : ℂ :=
  LinearMap.trace ℂ ((ι → F) → ℂ)
    (((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      * ((weilNorm h2 hψ hh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))

/-- The cocycle never vanishes — `weilTrace_ne_zero` applied to the product intertwiner. `c` lands
in ℂˣ. -/
theorem weilCocycle_ne_zero (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g h : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (hh : Heis.IsSymplectic h) :
    weilCocycle h2 hψ hg hh ≠ 0 := by
  have hspec : ∀ x, ((weilNorm h2 hψ hg * weilNorm h2 hψ hh :
        (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
      = schrodinger h2 ψ ((g ∘ h) x)
        * ((weilNorm h2 hψ hg * weilNorm h2 hψ hh :
            (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) := by
    intro x
    rw [Units.val_mul]
    exact mul_intertwines h2 (weilNorm_intertwines h2 hψ hg)
      (weilNorm_intertwines h2 hψ hh) x
  have h := weilTrace_ne_zero h2 hψ (isSymplectic_comp hg hh)
    (weilNorm h2 hψ hg * weilNorm h2 hψ hh) hspec
  rw [Units.val_mul] at h
  exact h

/-- **The defect equation**: `W_g · W_h = c(g,h) • W_{g∘h}` — the failure of the canonical section
to be a homomorphism *is* the cocycle. -/
theorem weilNorm_mul (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g h : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) (hh : Heis.IsSymplectic h) :
    ((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * ((weilNorm h2 hψ hh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = weilCocycle h2 hψ hg hh
          • ((weilNorm h2 hψ (isSymplectic_comp hg hh) :
              (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) := by
  obtain ⟨c, hc⟩ := weil_operator_unique h2 hψ (weilNorm h2 hψ (isSymplectic_comp hg hh))
    (((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      * ((weilNorm h2 hψ hh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
    (weilNorm_intertwines h2 hψ (isSymplectic_comp hg hh))
    (fun x => mul_intertwines h2 (weilNorm_intertwines h2 hψ hg)
      (weilNorm_intertwines h2 hψ hh) x)
  have hcval : c = weilCocycle h2 hψ hg hh := by
    have h := congrArg (LinearMap.trace ℂ ((ι → F) → ℂ)) hc
    rw [map_smul, smul_eq_mul, trace_weilNorm h2 hψ (isSymplectic_comp hg hh), mul_one] at h
    exact h.symm.trans rfl
  rw [hc, hcval]

/-- **The 2-cocycle law** `c(g,h)·c(g∘h,k) = c(g,h∘k)·c(h,k)`, by evaluating `Tr(W_g·W_h·W_k)`
along both associations. No section of a triple composite is ever formed, so no
composition-associativity bookkeeping arises. -/
theorem weilCocycle_cocycle (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g h k : Heis F ι → Heis F ι}
    (hg : Heis.IsSymplectic g) (hh : Heis.IsSymplectic h) (hk : Heis.IsSymplectic k) :
    weilCocycle h2 hψ hg hh * weilCocycle h2 hψ (isSymplectic_comp hg hh) hk
      = weilCocycle h2 hψ hg (isSymplectic_comp hh hk) * weilCocycle h2 hψ hh hk := by
  have hL : LinearMap.trace ℂ ((ι → F) → ℂ)
      ((((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
          * ((weilNorm h2 hψ hh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
        * ((weilNorm h2 hψ hk : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
      = weilCocycle h2 hψ hg hh * weilCocycle h2 hψ (isSymplectic_comp hg hh) hk := by
    rw [weilNorm_mul h2 hψ hg hh, smul_mul_assoc, map_smul, smul_eq_mul]
    rfl
  have hR : LinearMap.trace ℂ ((ι → F) → ℂ)
      (((weilNorm h2 hψ hg : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * (((weilNorm h2 hψ hh : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
          * ((weilNorm h2 hψ hk : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))))
      = weilCocycle h2 hψ hg (isSymplectic_comp hh hk) * weilCocycle h2 hψ hh hk := by
    rw [weilNorm_mul h2 hψ hh hk, mul_smul_comm, map_smul, smul_eq_mul]
    rw [mul_comm (weilCocycle h2 hψ hh hk)]
    rfl
  rw [← hL, ← hR, mul_assoc]

/-! ## Witnesses: the identity, and non-unitality -/

/-- The identity is symplectic. -/
theorem isSymplectic_id : Heis.IsSymplectic (id : Heis F ι → Heis F ι) where
  map_pos x y := by simp
  map_mom x y := by simp
  map_cen _ := rfl
  map_symp _ _ := rfl

/-- **The canonical operator of the identity is `n⁻¹ • 1`** — trace-1 forces the scalar, so the
section is *not* unital. (The unital rescaling `g ↦ n • W_g` shifts the cocycle by the coboundary
of the constant `n`; cohomologous, nothing lost.) -/
theorem weilNorm_id (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ((weilNorm h2 hψ (isSymplectic_id (F := F) (ι := ι)) :
        (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = ((Fintype.card (ι → F) : ℂ))⁻¹ • (1 : Module.End ℂ ((ι → F) → ℂ)) := by
  have hn : (Fintype.card (ι → F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hunit := unitSmul ((Fintype.card (ι → F) : ℂ))⁻¹ (inv_ne_zero hn)
    (1 : (Module.End ℂ ((ι → F) → ℂ))ˣ)
  have h := weilNorm_unique h2 hψ (isSymplectic_id (F := F) (ι := ι))
    (unitSmul ((Fintype.card (ι → F) : ℂ))⁻¹ (inv_ne_zero hn) 1)
    (fun x => by
      rw [unitSmul_val, Units.val_one]
      exact smul_intertwines h2 _ (fun y => by rw [one_mul, mul_one, id]) x)
    (by rw [unitSmul_val, Units.val_one, map_smul, smul_eq_mul, trace_one_end,
      inv_mul_cancel₀ hn])
  rw [← h, unitSmul_val, Units.val_one]

/-- `c(id, g) = n⁻¹` for every `g` — the non-unitality, quantified. -/
theorem weilCocycle_id_left (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    weilCocycle h2 hψ (isSymplectic_id (F := F) (ι := ι)) hg
      = ((Fintype.card (ι → F) : ℂ))⁻¹ := by
  unfold weilCocycle
  rw [weilNorm_id h2 hψ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul,
    trace_weilNorm h2 hψ hg, mul_one]

/-- `c(g, id) = n⁻¹` for every `g`. -/
theorem weilCocycle_id_right (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    weilCocycle h2 hψ hg (isSymplectic_id (F := F) (ι := ι))
      = ((Fintype.card (ι → F) : ℂ))⁻¹ := by
  unfold weilCocycle
  rw [weilNorm_id h2 hψ, mul_smul_comm, mul_one, map_smul, smul_eq_mul,
    trace_weilNorm h2 hψ hg, mul_one]

end ECCLib.WeilCharacter

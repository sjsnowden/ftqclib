/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.WeilCocycle
import ECCLib.Metaplectic

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The metaplectic extension SPLITS at odd q — the parity/determinant ratio

The proof:

1. The **parity operator** `P : f ↦ f∘(−·)` is a Weil operator for `−id ∈ Sp`, with `P² = 1`
   and — the odd-`q` entry point of the whole proof — **`Tr P = 1`** (the only fixed point of
   `x ↦ −x` on `𝔽_q^ι` is `0`).
2. Every canonical Weil operator **commutes with `P` exactly**: `P·W` and `W·P` intertwine along
   the same Heisenberg map (`−id` is central), so they differ by a scalar (`weil_operator_unique`),
   and `Tr(P·W) = Tr(W·P) ≠ 0` (`trace_mul_comm` + `weilTrace_ne_zero`) pins the scalar to `1`.
3. The parity eigenspaces `V₊, V₋` are therefore invariant, the restricted section satisfies the
   **same** defect equation with the **same** cocycle, and the restricted determinants give
   `c^{d₊} = δ(det₊)`, `c^{d₋} = δ(det₋)` with `d₊ − d₋ = Tr P = 1`.
4. Hence the **ratio** `weilBoundary T := det₊(W_T)·det₋(W_T)⁻¹` trivializes `c` on the nose:
   `weilBoundary T · weilBoundary T' = c(T,T') · weilBoundary (T·T')` — no Bézout, no transfer,
   no Gauss sums, no presentation, no Schur multiplier.

5. Packaging: `weilLinear : Sp →* (End ℂ V)ˣ` is a genuine **linear Weil representation of
   `Sp(2n, 𝔽_q)`** (`weilLinear_intertwines`), `mpSection` is a `MonoidHom` section of `mpProj`
   (`mpProj_splits`), and `Tr (weilLinear T) = (weilBoundary T)⁻¹` — the coboundary witness is
   literally the reciprocal of the representation's character.

**Headlines:** `weilCocycle_isCoboundary` (the class dies, with a computed witness) and
`mpProj_splits` (the extension splits). The packaging goes through
`ECCLib.CocyclePackaging.rescaled_sec_mul`, a lemma stated over *variables only* so that
instantiating it never forces the kernel to unfold `weilNorm`, `LinearMap.det`, or any
`Classical.choice`; packaging directly at the concrete objects hits a kernel timeout.

Two regimes: at `q` even the entry point fails exactly (`x ↦ −x` is the identity, so the
fixed-point count is `2ⁿ ≠ 1` and no scalar is pinned), matching `metaplecticNonSplit_two` on the
char-2 side. This proves THIS class dies; it makes no claim about `H²(Sp, ℂˣ)`.
-/

namespace ECCLib.WeilCharacter

open ECCLib.Heisenberg ECCLib.Siegel ECCLib.WeilComplete
open ECCLib.Metaplectic

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Pairing and omega under negation -/

lemma pairing_neg_left (b x : ι → F) : pairing (-b) x = -pairing b x := by
  unfold pairing
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply, neg_mul]

lemma pairing_neg_right (b x : ι → F) : pairing b (-x) = -pairing b x := by
  unfold pairing
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.neg_apply, mul_neg]

/-- `−id` is symplectic. -/
theorem neg_mem_Sp : (LinearEquiv.neg F : W F ι ≃ₗ[F] W F ι) ∈ Sp F ι := by
  intro x y
  simp only [LinearEquiv.neg_apply]
  change pairing (-y).2 (-x).1 - pairing (-x).2 (-y).1 = pairing y.2 x.1 - pairing x.2 y.1
  rw [Prod.fst_neg, Prod.snd_neg, Prod.fst_neg, Prod.snd_neg, pairing_neg_left,
    pairing_neg_right, pairing_neg_left, pairing_neg_right]
  ring

/-- The Heisenberg-level parity map, componentwise. -/
lemma heisOfSp_neg_apply (x : Heis F ι) :
    heisOfSp (LinearEquiv.neg F) x = ⟨-x.pos, -x.mom, x.cen⟩ := by
  refine Heis.ext ?_ ?_ ?_
  · rw [heisOfSp_pos, LinearEquiv.neg_apply, Prod.fst_neg]
  · rw [heisOfSp_mom, LinearEquiv.neg_apply, Prod.snd_neg]
  · rw [heisOfSp_cen]

/-- `−id` commutes with every linear map, at the Heisenberg level. -/
lemma heisOfSp_neg_comm (T : W F ι ≃ₗ[F] W F ι) :
    heisOfSp T ∘ heisOfSp (LinearEquiv.neg F)
      = heisOfSp (LinearEquiv.neg F) ∘ heisOfSp T := by
  funext x
  rw [Function.comp_apply, Function.comp_apply, heisOfSp_neg_apply, heisOfSp_neg_apply]
  refine Heis.ext ?_ ?_ ?_
  · rw [heisOfSp_pos, heisOfSp_pos]
    change (T (-x.pos, -x.mom)).1 = -(T (x.pos, x.mom)).1
    rw [show ((-x.pos, -x.mom) : W F ι) = -(x.pos, x.mom) from rfl, map_neg, Prod.fst_neg]
  · rw [heisOfSp_mom, heisOfSp_mom]
    change (T (-x.pos, -x.mom)).2 = -(T (x.pos, x.mom)).2
    rw [show ((-x.pos, -x.mom) : W F ι) = -(x.pos, x.mom) from rfl, map_neg, Prod.snd_neg]
  · rw [heisOfSp_cen, heisOfSp_cen]

/-! ## The parity operator -/

/-- **The parity operator** `f ↦ f∘(−·)`. -/
def parityOp : Module.End ℂ ((ι → F) → ℂ) where
  toFun f := fun y => f (-y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma parityOp_apply (f : (ι → F) → ℂ) (y : ι → F) :
    parityOp f y = f (-y) := rfl

lemma parityOp_sq : (parityOp : Module.End ℂ ((ι → F) → ℂ)) * parityOp = 1 := by
  refine LinearMap.ext fun f => funext fun y => ?_
  change f (- -y) = f y
  rw [neg_neg]

/-- The parity operator as a unit. -/
def parityUnit : (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  ⟨parityOp, parityOp, parityOp_sq, parityOp_sq⟩

/-- **Parity intertwines along `−id`**: `P` is a Weil operator for the central symplectic
element. -/
theorem parity_intertwines (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (x : Heis F ι) :
    (parityOp : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
      = schrodinger h2 ψ (heisOfSp (LinearEquiv.neg F) x) * parityOp := by
  rw [heisOfSp_neg_apply]
  refine LinearMap.ext fun f => funext fun y => ?_
  change (schrodinger h2 ψ x f) (-y)
    = (schrodinger h2 ψ (⟨-x.pos, -x.mom, x.cen⟩ : Heis F ι) (parityOp f)) y
  rw [schrodinger_apply, schrodinger_apply]
  change ψ x.cen * (weyl ψ x.pos x.mom f (-y))
    = ψ x.cen * (weyl ψ (-x.pos) (-x.mom) (parityOp f) y)
  rw [Heisenberg.weyl_apply, Heisenberg.weyl_apply]
  rw [show pairing (-x.mom) (-x.pos) = pairing x.mom x.pos from by
      rw [pairing_neg_left, pairing_neg_right, neg_neg],
    show pairing (-x.mom) y = -pairing x.mom y from pairing_neg_left _ _,
    show pairing x.mom (-y) = -pairing x.mom y from pairing_neg_right _ _]
  rw [parityOp_apply, show -(y + -x.pos) = -y + x.pos from by abel]

/-- **`Tr P = 1`** — the odd-`q` entry point: the only fixed point of `x ↦ −x` is `0`. -/
theorem trace_parityOp (h2 : (2 : F) ≠ 0) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (parityOp : Module.End ℂ ((ι → F) → ℂ)) = 1 := by
  classical
  rw [trace_eq_sum_delta_diag]
  have h : ∀ x : ι → F, (parityOp : Module.End ℂ ((ι → F) → ℂ)) (delta x) x
      = if x = 0 then 1 else 0 := by
    intro x
    change delta x (-x) = _
    unfold delta
    by_cases hx : x = 0
    · subst hx
      rw [if_pos neg_zero, if_pos rfl]
    · rw [if_neg, if_neg hx]
      intro hc
      apply hx
      funext i
      have hi := congrFun hc i
      rw [Pi.neg_apply] at hi
      have h2i : (2 : F) * x i = 0 := by
        linear_combination -hi
      rcases mul_eq_zero.mp h2i with h | h
      · exact absurd h h2
      · exact h
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_ite_eq' Finset.univ (0 : ι → F)
    (fun _ => (1 : ℂ))]
  rw [if_pos (Finset.mem_univ _)]

/-! ## Every Weil operator commutes with parity, exactly -/

/-- The symplecticity of the Heisenberg parity. -/
theorem isSymplectic_heisParity :
    Heis.IsSymplectic (heisOfSp (LinearEquiv.neg F) : Heis F ι → Heis F ι) :=
  isSymplectic_heisOfSp (neg_mem_Sp (F := F) (ι := ι))

/-- **Exact commutation**: any intertwining *unit* along a `heisOfSp T` commutes with the parity
operator on the nose. `P·W` and `W·P` intertwine along the same map (`−id` central), Schur gives
a scalar, and `Tr(PW) = Tr(WP) ≠ 0` pins it to `1`. -/
theorem parity_comm (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (T : W F ι ≃ₗ[F] W F ι) (hT : T ∈ Sp F ι)
    (U : (Module.End ℂ ((ι → F) → ℂ))ˣ)
    (hU : ∀ x, (U : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (heisOfSp T x) * (U : Module.End ℂ ((ι → F) → ℂ))) :
    (U : Module.End ℂ ((ι → F) → ℂ)) * parityOp
      = parityOp * (U : Module.End ℂ ((ι → F) → ℂ)) := by
  set g := heisOfSp T with hg_def
  set ν : Heis F ι → Heis F ι := heisOfSp (LinearEquiv.neg F) with hν_def
  have hUP : ∀ x, ((U : Module.End ℂ ((ι → F) → ℂ)) * parityOp) * schrodinger h2 ψ x
      = schrodinger h2 ψ ((g ∘ ν) x)
        * ((U : Module.End ℂ ((ι → F) → ℂ)) * parityOp) :=
    fun x => mul_intertwines h2 hU (parity_intertwines h2 ψ) x
  have hPU : ∀ x, (parityOp * (U : Module.End ℂ ((ι → F) → ℂ))) * schrodinger h2 ψ x
      = schrodinger h2 ψ ((g ∘ ν) x)
        * (parityOp * (U : Module.End ℂ ((ι → F) → ℂ))) := by
    intro x
    have h := mul_intertwines h2 (parity_intertwines h2 ψ) hU x
    rw [show (ν ∘ g) x = (g ∘ ν) x from by rw [hν_def, hg_def, ← heisOfSp_neg_comm]] at h
    exact h
  obtain ⟨c, hc⟩ := weil_operator_unique h2 hψ (U * parityUnit)
    (parityOp * (U : Module.End ℂ ((ι → F) → ℂ)))
    (fun x => by
      rw [show ((U * parityUnit : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ))
          = (U : Module.End ℂ ((ι → F) → ℂ)) * parityOp from rfl]
      exact hUP x)
    hPU
  have htr := congrArg (LinearMap.trace ℂ ((ι → F) → ℂ)) hc
  rw [LinearMap.trace_mul_comm] at htr
  have hne : LinearMap.trace ℂ ((ι → F) → ℂ)
      ((U * parityUnit : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) ≠ 0 := by
    refine weilTrace_ne_zero h2 hψ (isSymplectic_comp (isSymplectic_heisOfSp hT)
      isSymplectic_heisParity) (U * parityUnit) ?_
    intro x
    rw [show ((U * parityUnit : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ))
        = (U : Module.End ℂ ((ι → F) → ℂ)) * parityOp from rfl]
    exact hUP x
  rw [show ((U * parityUnit : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
      Module.End ℂ ((ι → F) → ℂ))
      = (U : Module.End ℂ ((ι → F) → ℂ)) * parityOp from rfl] at htr hne
  rw [map_smul, smul_eq_mul] at htr
  have hc1 : c = 1 := by
    have h0 : (c - 1) * LinearMap.trace ℂ ((ι → F) → ℂ)
        ((U : Module.End ℂ ((ι → F) → ℂ)) * parityOp) = 0 := by
      linear_combination -htr
    rcases mul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  rw [show ((U * parityUnit : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
      Module.End ℂ ((ι → F) → ℂ))
      = (U : Module.End ℂ ((ι → F) → ℂ)) * parityOp from rfl, hc1, one_smul] at hc
  exact hc.symm

/-! ## The parity eigenspaces and their dimensions -/

/-- The `+1` projection `π₊ = (1 + P)/2`. -/
noncomputable def piPlus : Module.End ℂ ((ι → F) → ℂ) :=
  (2⁻¹ : ℂ) • (1 + parityOp)

/-- The `−1` projection `π₋ = (1 − P)/2`. -/
noncomputable def piMinus : Module.End ℂ ((ι → F) → ℂ) :=
  (2⁻¹ : ℂ) • (1 - parityOp)

lemma piPlus_idem : (piPlus : Module.End ℂ ((ι → F) → ℂ)) * piPlus = piPlus := by
  unfold piPlus
  rw [smul_mul_smul_comm]
  rw [show ((1 : Module.End ℂ ((ι → F) → ℂ)) + parityOp) * (1 + parityOp)
      = 1 + parityOp + parityOp + parityOp * parityOp from by noncomm_ring]
  rw [parityOp_sq]
  rw [show ((1 : Module.End ℂ ((ι → F) → ℂ)) + parityOp + parityOp + 1)
      = (2 : ℂ) • (1 + parityOp) from by
    rw [two_smul]
    abel]
  rw [smul_smul]
  norm_num

lemma piMinus_idem : (piMinus : Module.End ℂ ((ι → F) → ℂ)) * piMinus = piMinus := by
  unfold piMinus
  rw [smul_mul_smul_comm]
  rw [show ((1 : Module.End ℂ ((ι → F) → ℂ)) - parityOp) * (1 - parityOp)
      = 1 - parityOp - parityOp + parityOp * parityOp from by
    rw [sub_mul, one_mul, mul_sub, mul_one]
    abel]
  rw [parityOp_sq]
  rw [show ((1 : Module.End ℂ ((ι → F) → ℂ)) - parityOp - parityOp + 1)
      = (2 : ℂ) • (1 - parityOp) from by
    rw [two_smul]
    abel]
  rw [smul_smul]
  norm_num

lemma piPlus_sub_piMinus :
    (piPlus : Module.End ℂ ((ι → F) → ℂ)) - piMinus = parityOp := by
  unfold piPlus piMinus
  refine LinearMap.ext fun f => funext fun y => ?_
  change (2⁻¹ : ℂ) * (f y + f (-y)) - (2⁻¹ : ℂ) * (f y - f (-y)) = f (-y)
  ring

/-- The parity eigenspaces (reducible, so restriction types align definitionally). -/
noncomputable abbrev Vplus : Submodule ℂ ((ι → F) → ℂ) :=
  LinearMap.range (piPlus (F := F) (ι := ι))
noncomputable abbrev Vminus : Submodule ℂ ((ι → F) → ℂ) :=
  LinearMap.range (piMinus (F := F) (ι := ι))

/-- Rank of an idempotent = its trace (the corestriction trick — no eigen-decomposition API). -/
lemma finrank_range_idem (e : Module.End ℂ ((ι → F) → ℂ)) (he : e * e = e) :
    ((Module.finrank ℂ (LinearMap.range e)) : ℂ) = LinearMap.trace ℂ ((ι → F) → ℂ) e := by
  have hsplit : (LinearMap.range e).subtype ∘ₗ e.rangeRestrict = e := by
    refine LinearMap.ext fun x => ?_
    rfl
  have hci : e.rangeRestrict ∘ₗ (LinearMap.range e).subtype = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, hx⟩ := z
    obtain ⟨y, hy⟩ := hx
    apply Subtype.ext
    change e x = x
    rw [← hy, ← Module.End.mul_apply, he]
  calc ((Module.finrank ℂ (LinearMap.range e)) : ℂ)
      = LinearMap.trace ℂ (LinearMap.range e) LinearMap.id := (LinearMap.trace_id ℂ _).symm
    _ = LinearMap.trace ℂ (LinearMap.range e)
          (e.rangeRestrict ∘ₗ (LinearMap.range e).subtype) := by
        rw [hci]
    _ = LinearMap.trace ℂ ((ι → F) → ℂ) ((LinearMap.range e).subtype ∘ₗ e.rangeRestrict) :=
        LinearMap.trace_comp_comm' _ _
    _ = LinearMap.trace ℂ ((ι → F) → ℂ) e := by rw [hsplit]

/-- **The dimension gap is exactly one**: `dim V₊ = dim V₋ + 1`, from `Tr P = 1`. -/
theorem finrank_Vplus_eq (h2 : (2 : F) ≠ 0) :
    Module.finrank ℂ (Vplus (F := F) (ι := ι))
      = Module.finrank ℂ (Vminus (F := F) (ι := ι)) + 1 := by
  have hp := finrank_range_idem (piPlus (F := F) (ι := ι)) piPlus_idem
  have hm := finrank_range_idem (piMinus (F := F) (ι := ι)) piMinus_idem
  have hsub : ((Module.finrank ℂ (Vplus (F := F) (ι := ι))) : ℂ)
      = ((Module.finrank ℂ (Vminus (F := F) (ι := ι))) : ℂ) + 1 := by
    have hP := trace_parityOp (F := F) (ι := ι) h2
    have hdiff : ((Module.finrank ℂ (Vplus (F := F) (ι := ι))) : ℂ)
        - ((Module.finrank ℂ (Vminus (F := F) (ι := ι))) : ℂ)
        = LinearMap.trace ℂ ((ι → F) → ℂ) (piPlus - piMinus) := by
      rw [map_sub]
      rw [show LinearMap.trace ℂ ((ι → F) → ℂ) (piPlus (F := F) (ι := ι))
          = ((Module.finrank ℂ (Vplus (F := F) (ι := ι))) : ℂ) from hp.symm,
        show LinearMap.trace ℂ ((ι → F) → ℂ) (piMinus (F := F) (ι := ι))
          = ((Module.finrank ℂ (Vminus (F := F) (ι := ι))) : ℂ) from hm.symm]
    rw [piPlus_sub_piMinus, hP] at hdiff
    linear_combination hdiff
  exact_mod_cast hsub

/-! ## The restriction layer -/

lemma comm_piPlus {Wop : Module.End ℂ ((ι → F) → ℂ)}
    (hWP : Wop * parityOp = parityOp * Wop) :
    Wop * piPlus = piPlus * Wop := by
  unfold piPlus
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hWP]

lemma comm_piMinus {Wop : Module.End ℂ ((ι → F) → ℂ)}
    (hWP : Wop * parityOp = parityOp * Wop) :
    Wop * piMinus = piMinus * Wop := by
  unfold piMinus
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hWP]

lemma mapsTo_of_comm {Wop e : Module.End ℂ ((ι → F) → ℂ)}
    (hcomm : Wop * e = e * Wop) :
    ∀ x ∈ LinearMap.range e, Wop x ∈ LinearMap.range e := by
  rintro x ⟨y, rfl⟩
  exact ⟨Wop y, by rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]⟩

/-! ## The canonical section over `Sp`, and its parity commutation -/

variable (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)

/-- The canonical section, indexed by `Sp` elements. -/
noncomputable def secOp (T : ↥(Sp F ι)) : (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  weilNorm h2 hψ (isSymplectic_heisOfSp T.2)

/-- Transport `weilNorm` along an equality of the underlying Heisenberg maps. -/
lemma weilNorm_congr {g g' : Heis F ι → Heis F ι} (hgg : g = g')
    (hg : Heis.IsSymplectic g) (hg' : Heis.IsSymplectic g') :
    weilNorm h2 hψ hg = weilNorm h2 hψ hg' := by
  subst hgg
  rfl

/-- The Sp-level cocycle. -/
noncomputable def cSp (T T' : ↥(Sp F ι)) : ℂ :=
  weilCocycle h2 hψ (isSymplectic_heisOfSp T.2) (isSymplectic_heisOfSp T'.2)

lemma cSp_ne_zero (T T' : ↥(Sp F ι)) : cSp h2 hψ T T' ≠ 0 :=
  weilCocycle_ne_zero h2 hψ _ _

/-- The defect equation over `Sp`: `W_T·W_{T'} = c(T,T')•W_{T·T'}`. -/
lemma secOp_mul (T T' : ↥(Sp F ι)) :
    ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * ((secOp h2 hψ T' : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = cSp h2 hψ T T'
          • ((secOp h2 hψ (T * T') : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
              Module.End ℂ ((ι → F) → ℂ)) := by
  have h := weilNorm_mul h2 hψ (isSymplectic_heisOfSp T.2) (isSymplectic_heisOfSp T'.2)
  have hfun : (heisOfSp (T : W F ι ≃ₗ[F] W F ι)) ∘ (heisOfSp (T' : W F ι ≃ₗ[F] W F ι))
      = heisOfSp ((T * T' : ↥(Sp F ι)) : W F ι ≃ₗ[F] W F ι) := by
    rw [show ((T * T' : ↥(Sp F ι)) : W F ι ≃ₗ[F] W F ι)
        = (T : W F ι ≃ₗ[F] W F ι) * (T' : W F ι ≃ₗ[F] W F ι) from rfl, heisOfSp_mul]
  rw [weilNorm_congr h2 hψ hfun
    (isSymplectic_comp (isSymplectic_heisOfSp T.2) (isSymplectic_heisOfSp T'.2))
    (isSymplectic_heisOfSp (T * T').2)] at h
  exact h

/-- Every canonical section operator commutes with parity. -/
lemma secOp_parity_comm (T : ↥(Sp F ι)) :
    ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) * parityOp
      = parityOp
        * ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) :=
  parity_comm h2 hψ (T : W F ι ≃ₗ[F] W F ι) T.2 (secOp h2 hψ T)
    (weilNorm_intertwines h2 hψ (isSymplectic_heisOfSp T.2))

lemma secOp_inv_parity_comm (T : ↥(Sp F ι)) :
    (((secOp h2 hψ T)⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * parityOp
      = parityOp
        * (((secOp h2 hψ T)⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
            Module.End ℂ ((ι → F) → ℂ)) := by
  have h : Commute ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
      Module.End ℂ ((ι → F) → ℂ)) parityOp := secOp_parity_comm h2 hψ T
  exact h.units_inv_left.eq

/-! ## The restricted determinants and the trivializer -/

/-- The `V₊`-restricted determinant of the canonical section. -/
noncomputable def detPlus (T : ↥(Sp F ι)) : ℂ :=
  LinearMap.det (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
    Module.End ℂ ((ι → F) → ℂ)).restrict
      (p := Vplus) (mapsTo_of_comm (comm_piPlus (secOp_parity_comm h2 hψ T))))

/-- The `V₋`-restricted determinant of the canonical section. -/
noncomputable def detMinus (T : ↥(Sp F ι)) : ℂ :=
  LinearMap.det (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
    Module.End ℂ ((ι → F) → ℂ)).restrict
      (p := Vminus) (mapsTo_of_comm (comm_piMinus (secOp_parity_comm h2 hψ T))))

/-- Restricted determinants never vanish (the inverse restricts too). -/
lemma detPlus_ne_zero (T : ↥(Sp F ι)) : detPlus h2 hψ T ≠ 0 := by
  intro h0
  have hres : (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ)).restrict
        (p := Vplus) (mapsTo_of_comm (comm_piPlus (secOp_parity_comm h2 hψ T))))
      * ((((secOp h2 hψ T)⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ)).restrict
        (p := Vplus) (mapsTo_of_comm (comm_piPlus (secOp_inv_parity_comm h2 hψ T))))
      = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    apply Subtype.ext
    change ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        ((((secOp h2 hψ T)⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ)) (z : (ι → F) → ℂ)) = (z : (ι → F) → ℂ)
    rw [← Module.End.mul_apply, Units.mul_inv]
    rfl
  have hdet := congrArg LinearMap.det hres
  rw [map_mul, LinearMap.det_id] at hdet
  rw [show LinearMap.det (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
      Module.End ℂ ((ι → F) → ℂ)).restrict
      (p := Vplus) (mapsTo_of_comm (comm_piPlus (secOp_parity_comm h2 hψ T))))
      = detPlus h2 hψ T from rfl, h0, zero_mul] at hdet
  exact zero_ne_one hdet

lemma detMinus_ne_zero (T : ↥(Sp F ι)) : detMinus h2 hψ T ≠ 0 := by
  intro h0
  have hres : (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ)).restrict
        (p := Vminus) (mapsTo_of_comm (comm_piMinus (secOp_parity_comm h2 hψ T))))
      * ((((secOp h2 hψ T)⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ)).restrict
        (p := Vminus) (mapsTo_of_comm (comm_piMinus (secOp_inv_parity_comm h2 hψ T))))
      = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    apply Subtype.ext
    change ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        ((((secOp h2 hψ T)⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ)) (z : (ι → F) → ℂ)) = (z : (ι → F) → ℂ)
    rw [← Module.End.mul_apply, Units.mul_inv]
    rfl
  have hdet := congrArg LinearMap.det hres
  rw [map_mul, LinearMap.det_id] at hdet
  rw [show LinearMap.det (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
      Module.End ℂ ((ι → F) → ℂ)).restrict
      (p := Vminus) (mapsTo_of_comm (comm_piMinus (secOp_parity_comm h2 hψ T))))
      = detMinus h2 hψ T from rfl, h0, zero_mul] at hdet
  exact zero_ne_one hdet

/-- The restricted defect equation, determinant form, on `V₊`. -/
lemma detPlus_mul (T T' : ↥(Sp F ι)) :
    detPlus h2 hψ T * detPlus h2 hψ T'
      = cSp h2 hψ T T' ^ (Module.finrank ℂ (Vplus (F := F) (ι := ι)))
        * detPlus h2 hψ (T * T') := by
  have h := secOp_mul h2 hψ T T'
  have hrestr : (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ)).restrict
          (mapsTo_of_comm (comm_piPlus (secOp_parity_comm h2 hψ T))))
        * (((secOp h2 hψ T' : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ)).restrict
            (mapsTo_of_comm (comm_piPlus (secOp_parity_comm h2 hψ T'))))
      = cSp h2 hψ T T'
        • (((secOp h2 hψ (T * T') : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ)).restrict
            (mapsTo_of_comm (comm_piPlus (secOp_parity_comm h2 hψ (T * T'))))) := by
    refine LinearMap.ext fun z => ?_
    apply Subtype.ext
    change (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
        ((((secOp h2 hψ T' : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
          (z : (ι → F) → ℂ))
      = cSp h2 hψ T T'
          • (((secOp h2 hψ (T * T') : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
              Module.End ℂ ((ι → F) → ℂ)) (z : (ι → F) → ℂ))
    rw [← Module.End.mul_apply, h]
    rfl
  have hdet := congrArg LinearMap.det hrestr
  rw [map_mul, LinearMap.det_smul] at hdet
  exact hdet

/-- The restricted defect equation, determinant form, on `V₋`. -/
lemma detMinus_mul (T T' : ↥(Sp F ι)) :
    detMinus h2 hψ T * detMinus h2 hψ T'
      = cSp h2 hψ T T' ^ (Module.finrank ℂ (Vminus (F := F) (ι := ι)))
        * detMinus h2 hψ (T * T') := by
  have h := secOp_mul h2 hψ T T'
  have hrestr : (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
        Module.End ℂ ((ι → F) → ℂ)).restrict
          (mapsTo_of_comm (comm_piMinus (secOp_parity_comm h2 hψ T))))
        * (((secOp h2 hψ T' : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ)).restrict
            (mapsTo_of_comm (comm_piMinus (secOp_parity_comm h2 hψ T'))))
      = cSp h2 hψ T T'
        • (((secOp h2 hψ (T * T') : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
          Module.End ℂ ((ι → F) → ℂ)).restrict
            (mapsTo_of_comm (comm_piMinus (secOp_parity_comm h2 hψ (T * T'))))) := by
    refine LinearMap.ext fun z => ?_
    apply Subtype.ext
    change (((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
        ((((secOp h2 hψ T' : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)))
          (z : (ι → F) → ℂ))
      = cSp h2 hψ T T'
          • (((secOp h2 hψ (T * T') : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
              Module.End ℂ ((ι → F) → ℂ)) (z : (ι → F) → ℂ))
    rw [← Module.End.mul_apply, h]
    rfl
  have hdet := congrArg LinearMap.det hrestr
  rw [map_mul, LinearMap.det_smul] at hdet
  exact hdet

/-- **The explicit trivializer**: the ratio of the restricted determinants. -/
noncomputable def weilBoundary (T : ↥(Sp F ι)) : ℂ :=
  detPlus h2 hψ T * (detMinus h2 hψ T)⁻¹

lemma weilBoundary_ne_zero (T : ↥(Sp F ι)) : weilBoundary h2 hψ T ≠ 0 :=
  mul_ne_zero (detPlus_ne_zero h2 hψ T) (inv_ne_zero (detMinus_ne_zero h2 hψ T))

/-- **The coboundary equation** — the dimension gap being exactly `1` makes the ratio trivialize
the cocycle on the nose: `b(T)·b(T') = c(T,T')·b(T·T')`. -/
theorem weilBoundary_rel (T T' : ↥(Sp F ι)) :
    weilBoundary h2 hψ T * weilBoundary h2 hψ T'
      = cSp h2 hψ T T' * weilBoundary h2 hψ (T * T') := by
  have hp := detPlus_mul h2 hψ T T'
  have hm := detMinus_mul h2 hψ T T'
  rw [finrank_Vplus_eq h2, pow_succ] at hp
  unfold weilBoundary
  have hMne : detMinus h2 hψ (T * T') ≠ 0 := detMinus_ne_zero h2 hψ _
  have hMTne : detMinus h2 hψ T ≠ 0 := detMinus_ne_zero h2 hψ _
  have hMT'ne : detMinus h2 hψ T' ≠ 0 := detMinus_ne_zero h2 hψ _
  have hcpow : cSp h2 hψ T T' ^ (Module.finrank ℂ (Vminus (F := F) (ι := ι))) ≠ 0 :=
    pow_ne_zero _ (cSp_ne_zero h2 hψ T T')
  field_simp
  rw [hp, hm]
  ring

/-- **Cohomological form: the metaplectic cocycle IS A COBOUNDARY.** The trivializer is
the parity determinant ratio; the homomorphic section itself is `mpSection` below. -/
theorem weilCocycle_isCoboundary :
    ∃ b : ↥(Sp F ι) → ℂ, (∀ T, b T ≠ 0) ∧
      ∀ T T' : ↥(Sp F ι),
        b T * b T'
          = weilCocycle h2 hψ (isSymplectic_heisOfSp T.2) (isSymplectic_heisOfSp T'.2)
            * b (T * T') :=
  ⟨weilBoundary h2 hψ, weilBoundary_ne_zero h2 hψ, weilBoundary_rel h2 hψ⟩

end ECCLib.WeilCharacter

/-! # Generic packaging: a trivialized cocycle gives a homomorphism

**Stated over variables only**, so that the kernel never unfolds concrete objects here. The
instantiation below is an *application* of this lemma, so the kernel never unfolds
`weilNorm`, `LinearMap.det`, or any `Classical.choice` while checking the packaging. -/

namespace ECCLib.CocyclePackaging

variable {G : Type*} [Group G] {M : Type*} [Monoid M] {R : Type*} [CommGroup R]

/-- **Rescaling a set-section by a trivializer of its defect cocycle makes it multiplicative.**
`sec` is a set-theoretic section whose multiplicativity defect is the central-scalar cocycle `c`;
`b` trivializes `c`; then `g ↦ ι(b g)⁻¹ · sec g` is a homomorphism. -/
theorem rescaled_sec_mul (iota : R →* Mˣ)
    (hcen : ∀ (r : R) (m : Mˣ), iota r * m = m * iota r)
    {sec : G → Mˣ} {c : G → G → R} {b : G → R}
    (hdefect : ∀ g g', sec g * sec g' = iota (c g g') * sec (g * g'))
    (htriv : ∀ g g', b g * b g' = c g g' * b (g * g'))
    (g g' : G) :
    (iota (b (g * g')))⁻¹ * sec (g * g')
      = ((iota (b g))⁻¹ * sec g) * ((iota (b g'))⁻¹ * sec g') := by
  have hcinv : ∀ (r : R) (m : Mˣ), (iota r)⁻¹ * m = m * (iota r)⁻¹ := by
    intro r m
    rw [← map_inv]
    exact hcen r⁻¹ m
  have hscal : (b g)⁻¹ * (b g')⁻¹ * c g g' = (b (g * g'))⁻¹ := by
    calc (b g)⁻¹ * (b g')⁻¹ * c g g'
        = (b g * b g')⁻¹ * c g g' := by rw [mul_inv]
      _ = (c g g' * b (g * g'))⁻¹ * c g g' := by rw [htriv]
      _ = (b (g * g'))⁻¹ := by
          rw [mul_inv, mul_comm ((c g g')⁻¹) ((b (g * g'))⁻¹), mul_assoc,
            inv_mul_cancel, mul_one]
  symm
  calc ((iota (b g))⁻¹ * sec g) * ((iota (b g'))⁻¹ * sec g')
      = (iota (b g))⁻¹ * ((sec g * (iota (b g'))⁻¹) * sec g') := by
        simp only [mul_assoc]
    _ = (iota (b g))⁻¹ * (((iota (b g'))⁻¹ * sec g) * sec g') := by
        rw [hcinv (b g') (sec g)]
    _ = ((iota (b g))⁻¹ * (iota (b g'))⁻¹) * (sec g * sec g') := by
        simp only [mul_assoc]
    _ = ((iota (b g))⁻¹ * (iota (b g'))⁻¹) * (iota (c g g') * sec (g * g')) := by
        rw [hdefect]
    _ = iota ((b g)⁻¹ * (b g')⁻¹ * c g g') * sec (g * g') := by
        rw [← mul_assoc, map_mul, map_mul, map_inv, map_inv]
    _ = (iota (b (g * g')))⁻¹ * sec (g * g') := by
        rw [hscal, map_inv]

end ECCLib.CocyclePackaging

namespace ECCLib.WeilCharacter

open ECCLib.Heisenberg ECCLib.Siegel ECCLib.WeilComplete
open ECCLib.Metaplectic ECCLib.CocyclePackaging

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)

/-! ## The units layer (no `≠ 0` proofs travel inside any term) -/

/-- Scalars as (central) units of `End`. -/
noncomputable def scalarUnit : ℂˣ →* (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  Units.map (algebraMap ℂ (Module.End ℂ ((ι → F) → ℂ))).toMonoidHom

lemma scalarUnit_mul_val (z : ℂˣ) (W : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
    ((scalarUnit z * W : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = (z : ℂ) • (W : Module.End ℂ ((ι → F) → ℂ)) := by
  rw [Units.val_mul, Algebra.smul_def]
  rfl

lemma scalarUnit_central (z : ℂˣ) (W : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
    scalarUnit z * W = W * scalarUnit z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact Algebra.commutes _ _

/-- The cocycle, as a unit. -/
noncomputable def cSpU (T T' : ↥(Sp F ι)) : ℂˣ :=
  Units.mk0 (cSp h2 hψ T T') (cSp_ne_zero h2 hψ T T')

/-- The trivializer, as a unit. -/
noncomputable def weilBoundaryU (T : ↥(Sp F ι)) : ℂˣ :=
  Units.mk0 (weilBoundary h2 hψ T) (weilBoundary_ne_zero h2 hψ T)

/-- The defect equation, at unit level. -/
lemma secOp_mul_unit (T T' : ↥(Sp F ι)) :
    secOp h2 hψ T * secOp h2 hψ T'
      = scalarUnit (cSpU h2 hψ T T') * secOp h2 hψ (T * T') := by
  apply Units.ext
  rw [Units.val_mul, scalarUnit_mul_val]
  exact secOp_mul h2 hψ T T'

/-- The coboundary equation, at unit level. -/
lemma weilBoundaryU_rel (T T' : ↥(Sp F ι)) :
    weilBoundaryU h2 hψ T * weilBoundaryU h2 hψ T'
      = cSpU h2 hψ T T' * weilBoundaryU h2 hψ (T * T') := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact weilBoundary_rel h2 hψ T T'

/-! ## The linear representation, built first -/

/-- The rescaled section, unit-valued. -/
noncomputable def weilLinearFun (T : ↥(Sp F ι)) : (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  (scalarUnit (weilBoundaryU h2 hψ T))⁻¹ * secOp h2 hψ T

/-- Multiplicativity — **one application of the generic lemma**. -/
lemma weilLinearFun_mul (T T' : ↥(Sp F ι)) :
    weilLinearFun h2 hψ (T * T') = weilLinearFun h2 hψ T * weilLinearFun h2 hψ T' :=
  rescaled_sec_mul scalarUnit scalarUnit_central
    (secOp_mul_unit h2 hψ) (weilBoundaryU_rel h2 hψ) T T'

/-- **The linear Weil representation of `Sp(2n, 𝔽_q)`** — a genuine `MonoidHom`, no cover. -/
noncomputable def weilLinear : ↥(Sp F ι) →* (Module.End ℂ ((ι → F) → ℂ))ˣ :=
  MonoidHom.mk' (weilLinearFun h2 hψ) (weilLinearFun_mul h2 hψ)

lemma weilLinear_apply (T : ↥(Sp F ι)) :
    weilLinear h2 hψ T = weilLinearFun h2 hψ T := rfl

lemma weilLinear_val (T : ↥(Sp F ι)) :
    ((weilLinear h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = (weilBoundary h2 hψ T)⁻¹
        • ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) := by
  rw [weilLinear_apply]
  unfold weilLinearFun
  rw [← map_inv, scalarUnit_mul_val]
  congr 1

/-- The linear representation intertwines the Schrödinger representation along its argument. -/
theorem weilLinear_intertwines (T : ↥(Sp F ι)) (x : Heis F ι) :
    ((weilLinear h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * schrodinger h2 ψ x
      = schrodinger h2 ψ (heisOfSp (T : W F ι ≃ₗ[F] W F ι) x)
        * ((weilLinear h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
            Module.End ℂ ((ι → F) → ℂ)) := by
  rw [weilLinear_val]
  exact smul_intertwines h2 _
    (weilNorm_intertwines h2 hψ (isSymplectic_heisOfSp T.2)) x

/-- The canonical section has trace `1`, in `Sp`-indexed form. -/
lemma trace_secOp (T : ↥(Sp F ι)) :
    LinearMap.trace ℂ ((ι → F) → ℂ)
      ((secOp h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) = 1 :=
  trace_weilNorm h2 hψ (isSymplectic_heisOfSp T.2)

/-- The character of the linear representation is the **reciprocal of the trivializer**. -/
theorem trace_weilLinear (T : ↥(Sp F ι)) :
    LinearMap.trace ℂ ((ι → F) → ℂ)
        ((weilLinear h2 hψ T : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      = (weilBoundary h2 hψ T)⁻¹ := by
  rw [weilLinear_val, map_smul, smul_eq_mul, trace_secOp h2 hψ, mul_one]

/-! ## The section, by `codRestrict` -/

lemma weilLinear_mem (T : ↥(Sp F ι)) :
    ((MonoidHom.id ↥(Sp F ι)).prod (weilLinear h2 hψ)) T ∈ Mp (ι := ι) h2 ψ :=
  fun x => weilLinear_intertwines h2 hψ T x

/-- **The homomorphic section of `mpProj`.** -/
noncomputable def mpSection : ↥(Sp F ι) →* ↥(Mp (ι := ι) h2 ψ) :=
  ((MonoidHom.id ↥(Sp F ι)).prod (weilLinear h2 hψ)).codRestrict
    (Mp (ι := ι) h2 ψ) (weilLinear_mem h2 hψ)

/-- **The metaplectic extension splits at odd `q`.** -/
theorem mpProj_mpSection (T : ↥(Sp F ι)) :
    mpProj h2 ψ (mpSection h2 hψ T) = T := rfl

include hψ in
theorem mpProj_splits :
    ∃ s : ↥(Sp F ι) →* ↥(Mp (ι := ι) h2 ψ),
      ∀ T, mpProj h2 ψ (s T) = T :=
  ⟨mpSection h2 hψ, fun _ => rfl⟩

/-- The section realizes the linear representation: `weilMp ∘ mpSection = weilLinear`. -/
theorem weilMp_mpSection (T : ↥(Sp F ι)) :
    weilMp h2 ψ (mpSection h2 hψ T) = weilLinear h2 hψ T := rfl

end ECCLib.WeilCharacter

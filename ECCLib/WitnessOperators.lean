/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.ProjectiveWeil
import ECCLib.WitnessGauss

set_option linter.unusedSectionVars false

/-!
# Computational witnesses for the Heisenberg and Weil operators

At `F = ZMod 3, ι = Fin 1` (the one-carrier model over `𝔽₃`). As in `WitnessGauss.lean`, each
numeric witness has an *independent* route (direct finite expansion, never invoking the general
theorem) and a route through the general theorem, proving the same statement.

- the concrete instance bundle (`h2₃`, `ψ₃ ≠ 1`) plus a central-character smoke check;
- `𝓕²(δ_{e₁}) = 3·δ_{−e₁}`: the independent route is the two-fold expansion through the
  1-D character sum; the general route is `fourierOp_comp_fourierOp` (`𝓕² = |V|·R`). **This is
  the witness for the DFT/pairing convention** — a transposed `pairing` or a sign error in
  `reversal` breaks the agreement;
- `Tr 𝓕 = 1 + 2ω`: independent route through `trace_fourierOp` (Mathlib's trace-basis
  formula) + direct diagonal expansion; general route through
  `trace_fourierOp_eq_quadGaussSum_pow` + the Gauss-sum expansion of `WitnessGauss.lean`. Ties
  the operator witnesses to the Gauss-sum witnesses in one number;
- two generation-layer word identities checked on **all 27 points** of
  `Heis (ZMod 3) (Fin 1)` by `decide`: the three-shear Bruhat-cell identity and the `c = 0`
  `w`-pivot. Their general proofs run on `linear_combination` certificates, where signs are easy
  to get wrong — the `decide` instances are genuinely independent re-checks;
- **non-vacuity only**, stated as such: Stone–von Neumann's hypotheses are satisfiable
  (instantiated with the Schrödinger representation itself), and the metaplectic layer applies at
  the Weyl element (`heisOfSp Siegel.weyl = Heis.fourierMap`, membership in `Sp`, and `weilProj`
  evaluated through an explicit intertwiner). No independent number exists at this layer; the
  cross-check is structural.
-/

namespace ECCLib.Witness

open ECCLib ECCLib.Heisenberg ECCLib.GaussSign

/-! ## The concrete instance bundle -/

theorem h2₃ : (2 : ZMod 3) ≠ 0 := by decide

theorem ψ₃_ne_one : ψ₃ ≠ 1 := by
  intro h
  have h1 : ψ₃ 1 = 1 := by rw [h]; exact AddChar.one_apply 1
  rw [ψ₃_apply, show (1 : ZMod 3).val = 1 from rfl, pow_one] at h1
  exact ω_ne_one h1

/-- The basis point `e₁ = (1) ∈ 𝔽₃¹`. -/
def e₁ : Fin 1 → ZMod 3 := fun _ => 1

/-- **Smoke check**: the Schrödinger representation instantiates, and the centre acts by the
scalar `ψ₃(1) = ω` — the general theorem `schrodinger_central` at a concrete point. -/
example : schrodinger (ι := Fin 1) h2₃ ψ₃ (Heis.central 1) = ψ₃ 1 • LinearMap.id :=
  schrodinger_central h2₃ ψ₃ 1

/-! ## The 1-D character sum (the expansion engine, independent of every general theorem) -/

/-- `Σ_t ψ₃(st) = 3` at `s = 0`, else `0` — by three-term expansion and `1+ω+ω² = 0`. -/
theorem char_sum_three (s : ZMod 3) :
    ∑ t : ZMod 3, ψ₃ (s * t) = if s = 0 then 3 else 0 := by
  have hexp : ∑ t : ZMod 3, ψ₃ (s * t) = ψ₃ 0 + ψ₃ s + ψ₃ (s * 2) := by
    rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [mul_zero, mul_one]
    ring
  rcases (by decide : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2) s with rfl | rfl | rfl
  · rw [if_pos rfl, hexp]
    rw [show ((0 : ZMod 3) * 2) = 0 from by decide, AddChar.map_zero_eq_one]
    norm_num
  · rw [if_neg (by decide), hexp]
    rw [show ((1 : ZMod 3) * 2) = 2 from by decide, AddChar.map_zero_eq_one,
      ψ₃_apply 1, ψ₃_apply 2, show (1 : ZMod 3).val = 1 from rfl,
      show (2 : ZMod 3).val = 2 from rfl, pow_one]
    linear_combination omega_cubic
  · rw [if_neg (by decide), hexp]
    rw [show ((2 : ZMod 3) * 2) = 1 from by decide, AddChar.map_zero_eq_one,
      ψ₃_apply 2, ψ₃_apply 1, show (1 : ZMod 3).val = 1 from rfl,
      show (2 : ZMod 3).val = 2 from rfl, pow_one]
    linear_combination omega_cubic

/-! ## `𝓕²(δ_{e₁}) = 3·δ_{−e₁}` -/

/-- The DFT of a delta is the character wave — by collapsing the indicator sum. Uses only the
definitions (no general theorem). -/
theorem fourierOp_delta_e₁ :
    fourierOp ψ₃ (delta e₁) = fun y : Fin 1 → ZMod 3 => ψ₃ (y 0) := by
  funext y
  rw [fourierOp_apply]
  rw [Finset.sum_eq_single e₁ ?_ ?_]
  · unfold delta
    rw [if_pos rfl, mul_one]
    congr 1
    unfold pairing
    rw [Fin.sum_univ_one, show e₁ 0 = 1 from rfl, mul_one]
  · intro b _ hb
    unfold delta
    rw [if_neg hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Route A (independent)**: the two-fold expansion. `𝓕(δ_{e₁})` is the wave `ψ(y₀)`; the
second transform is the 1-D character sum at `z₀ + 1`, which is `3` exactly at `z = −e₁`. -/
theorem witness_fourier_sq_independent :
    fourierOp ψ₃ (fourierOp ψ₃ (delta e₁)) = (3 : ℂ) • delta (-e₁) := by
  rw [fourierOp_delta_e₁]
  funext z
  rw [fourierOp_apply]
  have hterm : ∀ y : Fin 1 → ZMod 3,
      ψ₃ (pairing z y) * ψ₃ (y 0) = ψ₃ ((z 0 + 1) * y 0) := by
    intro y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold pairing
    rw [Fin.sum_univ_one]
    ring
  rw [Finset.sum_congr rfl fun y _ => hterm y]
  rw [show (∑ y : Fin 1 → ZMod 3, ψ₃ ((z 0 + 1) * y 0))
      = ∑ t : ZMod 3, ψ₃ ((z 0 + 1) * t) from
    Equiv.sum_comp (Equiv.funUnique (Fin 1) (ZMod 3)) (fun t => ψ₃ ((z 0 + 1) * t))]
  rw [char_sum_three, Pi.smul_apply, smul_eq_mul]
  unfold delta
  have himp : z 0 + 1 = 0 → z = -e₁ := by
    intro h
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi, show (-e₁) 0 = -1 from rfl]
    exact eq_neg_of_add_eq_zero_left h
  by_cases hz : z = -e₁
  · rw [if_pos (by rw [hz, show (-e₁) 0 = -1 from rfl]; ring), if_pos hz]
    norm_num
  · rw [if_neg (fun hc => hz (himp hc)), if_neg hz, mul_zero]


/-- **Route B (via the general theorem)**: `fourierOp_comp_fourierOp` (`𝓕² = |V|·R`) evaluated at
`δ_{e₁}`, with `|V| = 3` and `R(δ_{e₁}) = δ_{−e₁}`. Routes A and B prove the same statement. -/
theorem witness_fourier_sq_general :
    fourierOp ψ₃ (fourierOp ψ₃ (delta e₁)) = (3 : ℂ) • delta (-e₁) := by
  have h := fourierOp_comp_fourierOp (ι := Fin 1) ψ₃_ne_one
  have happ := congrArg (fun T : ((Fin 1 → ZMod 3) → ℂ) →ₗ[ℂ] ((Fin 1 → ZMod 3) → ℂ) =>
    T (delta e₁)) h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at happ
  have hcard : (Fintype.card (Fin 1 → ZMod 3) : ℂ) = 3 := by
    rw [Fintype.card_fun]
    norm_num
  have hrev : reversal (delta e₁) = delta (-e₁) := by
    funext z
    rw [reversal_apply]
    unfold delta
    by_cases hz : -z = e₁
    · rw [if_pos hz, if_pos (neg_eq_iff_eq_neg.mp hz)]
    · rw [if_neg hz, if_neg (fun hc => hz (neg_eq_iff_eq_neg.mpr hc))]
  rw [hcard, hrev] at happ
  exact happ

/-! ## The trace ties the operator witnesses to the Gauss-sum witnesses -/

/-- **Route A (independent)**: the trace by direct diagonal expansion — `trace_fourierOp` is
Mathlib's trace-basis formula, and the diagonal sum reindexes to `Σψ(t²) = 1+2ω`. -/
theorem witness_trace_independent :
    LinearMap.trace ℂ ((Fin 1 → ZMod 3) → ℂ) (fourierOp ψ₃) = 1 + 2 * ω := by
  rw [trace_fourierOp]
  have hcong : (∑ x : Fin 1 → ZMod 3, ψ₃ (pairing x x))
      = ∑ x : Fin 1 → ZMod 3, ψ₃ (x 0 * x 0) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    unfold pairing
    rw [Fin.sum_univ_one]
  rw [hcong, show (∑ x : Fin 1 → ZMod 3, ψ₃ (x 0 * x 0)) = ∑ t : ZMod 3, ψ₃ (t * t) from
    Equiv.sum_comp (Equiv.funUnique (Fin 1) (ZMod 3)) (fun t => ψ₃ (t * t))]
  rw [Finset.sum_congr rfl fun t _ => by rw [← sq]]
  exact quadGaussSum_three_expand

/-- **Route B (via the general theorem)**: `Tr 𝓕 = g^{|ι|}` at `|ι| = 1`, with the independent
expansion of `g`. -/
theorem witness_trace_general :
    LinearMap.trace ℂ ((Fin 1 → ZMod 3) → ℂ) (fourierOp ψ₃) = 1 + 2 * ω := by
  rw [trace_fourierOp_eq_quadGaussSum_pow, show Fintype.card (Fin 1) = 1 from rfl, pow_one]
  exact quadGaussSum_three_expand

/-! ## Generation-layer words, on all 27 points, by `decide` -/

instance : DecidableEq (Heis (ZMod 3) (Fin 1)) := fun a b =>
  decidable_of_iff (a.pos = b.pos ∧ a.mom = b.mom ∧ a.cen = b.cen)
    ⟨fun ⟨h1, h2, h3⟩ => Heis.ext h1 h2 h3, fun h => by subst h; exact ⟨rfl, rfl, rfl⟩⟩

instance : Fintype (Heis (ZMod 3) (Fin 1)) :=
  Fintype.ofEquiv ((Fin 1 → ZMod 3) × (Fin 1 → ZMod 3) × ZMod 3)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun x => (x.pos, x.mom, x.cen)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The three-shear Bruhat-cell identity at `[[1,1],[1,2]]` over `𝔽₃`
(`x' = 0, z = 1`), checked on all 27 points. The general proof ran on `linear_combination`
certificates; this is an independent kernel-computation re-check. -/
example : ∀ x : Heis (ZMod 3) (Fin 1),
    mob 1 1 1 2 x = mob 1 0 0 1 (mob 1 0 1 1 (mob 1 1 0 1 x)) := by decide

/-- The `c = 0` `w`-pivot at `[[2,0],[0,2]]` over `𝔽₃` (`d = a⁻¹ = 2`), checked on all 27
points: `mob 2 0 0 2 = mob 0 2 1 0 ∘ w ∘ w ∘ w` with `w = mob 0 1 (−1) 0`. -/
example : ∀ x : Heis (ZMod 3) (Fin 1),
    mob 2 0 0 2 x
      = mob 0 2 1 0 (mob 0 1 (-1) 0 (mob 0 1 (-1) 0 (mob 0 1 (-1) 0 x))) := by decide

/-! ## Stone–von Neumann: NON-VACUITY ONLY

The theorem's content is `∃ Φ`; there is no independent number to check. This example establishes
only that the hypotheses are simultaneously satisfiable at a concrete instance (`ρ` = the
Schrödinger representation itself, `w = δ₀ ≠ 0`) — i.e. the theorem is not vacuous. Its real
cross-check is structural: the SvN-transport route and the explicit Bruhat route reach the same
Weil operators by disjoint arguments. -/

example : ∃ Φ : ((Fin 1 → ZMod 3) → ℂ) →ₗ[ℂ] ((Fin 1 → ZMod 3) → ℂ),
    Function.Injective Φ ∧
      ∀ x : Heis (ZMod 3) (Fin 1),
        Φ ∘ₗ schrodinger h2₃ ψ₃ x = schrodinger h2₃ ψ₃ x ∘ₗ Φ :=
  stone_von_neumann_embedding h2₃ ψ₃_ne_one (schrodinger h2₃ ψ₃)
    (fun s => by rw [schrodinger_central, Module.End.one_eq_id])
    (delta_zero_ne_zero (F := ZMod 3) (ι := Fin 1))

/-! ## The metaplectic layer: NON-VACUITY ONLY

The layer is definitional composition over the operators witnessed above; no independent number
exists at this level. These establish that the objects are inhabited and connected as claimed. -/

/-- The metaplectic bridge sends the Siegel Weyl element to the Heisenberg Fourier map — the two
"Weyl" objects of the library are literally the same map under `heisOfSp`. -/
theorem heisOfSp_weyl :
    Metaplectic.heisOfSp (Siegel.weyl (F := ZMod 3) (ι := Fin 1)) = Heis.fourierMap := by
  funext x
  exact Heis.ext rfl rfl rfl

/-- `Sp (ZMod 3) (Fin 1)` contains the Weyl element — the group object is inhabited beyond `1`. -/
example : Siegel.weyl ∈ Metaplectic.Sp (ZMod 3) (Fin 1) := Siegel.weyl_isSymplectic

/-- `weilProj` applies at the Weyl element: there is an explicit intertwiner whose `PGL` class it
is. -/
example : ∃ U : (Module.End ℂ ((Fin 1 → ZMod 3) → ℂ))ˣ,
    Metaplectic.weilProj h2₃ ψ₃_ne_one ⟨Siegel.weyl, Siegel.weyl_isSymplectic⟩
      = Metaplectic.toPGL ((Fin 1 → ZMod 3) → ℂ) U := by
  obtain ⟨U, hU⟩ := hasWeilOperator_fourierMap (ι := Fin 1) h2₃ ψ₃_ne_one
  refine ⟨U, Metaplectic.weilProj_eq_of_intertwines h2₃ ψ₃_ne_one ?_⟩
  intro x
  rw [show ((⟨Siegel.weyl, Siegel.weyl_isSymplectic⟩ :
      ↥(Metaplectic.Sp (ZMod 3) (Fin 1))) : Siegel.W (ZMod 3) (Fin 1) ≃ₗ[ZMod 3]
        Siegel.W (ZMod 3) (Fin 1)) = Siegel.weyl from rfl, heisOfSp_weyl]
  exact hU x

end ECCLib.Witness

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.HadamardGateCertificate

/-!
# Floor closure of the free Hadamard rule

`applyHFree i ε` (`HadamardGate`) recollapses an X-free bit whose exponent carries the dyadic sign
`hSignPoly i ε` onto the value `ε`. `CarrierStateHadamard` proves the carrier and floor closures of
`hRaise`, `applyHFiner` and `applyHPinned`, but not of `applyHFree`, so the free rule's certificate
`cert_free` (`HadamardGateCertificate`) takes the output's floor as a hypothesis. This file states
that closure and the certificate without that hypothesis; `cert_free` is left as it is.

The free bit's hypotheses are those of `cert_free`, read on a carrier state `K`: every element of
`K.L` has no `Z`-support at `i` (`hfree`), and the exponent is `q₀ + hSignPoly i ε K.m` with `q₀`
free of bit `i` (`hq`, `hq₀free`). On a co-isotropic `K.L`, `hfree` puts `Xᵢ` in `K.L`, so the
carrier state's support is closed under flipping bit `i`, and the rule's denotation is the Walsh
transform at `i`, as for the pinned rule (`amp_ofKernelState_applyHPinned`). The offset's value at
`i` is not needed for the closure; the certificate keeps `cert_free`'s gauge hypothesis `x₀ i = 0`.

Everything here is frame-pure. No `FTQCLib.Hilbert`.

## Main results

* `amp_ofKernelState_applyHFree` — the free rule's denotation is the Walsh transform at `i`.
* `isCarrier_applyHFree`, `isFloor_applyHFree` — carrier and floor closure for the free rule.
* `chartOf_applyHFree` — the free-mode certificate, with the output's floor discharged by
  `isFloor_applyHFree`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The denotation of the free rule -/

/-- **The free rule is the Walsh transform at `i`.** On a co-isotropic Lagrangian with no
`Z`-support at `i`, and an exponent `q₀ + hSignPoly i ε K.m` with `q₀` free of bit `i`, the free
rule's output denotes the Walsh transform at `i` of the input's denotation. -/
theorem amp_ofKernelState_applyHFree (i : Fin n) (ε : ZMod 2) (K : KernelState n)
    (q₀ : DiagPhase n K.m) (hq : K.q = q₀ + hSignPoly i ε K.m)
    (hq₀free : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q₀ (Function.update w i b) = DiagPhase.eval q₀ w)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin K.L ≤ K.L)
    (hfree : ∀ p ∈ K.L, p.Z i = 0) (hm : 1 ≤ K.m) :
    amp (ofKernelState (applyHFree i ε K)) = walshTransform i (amp (ofKernelState K)) := by
  classical
  -- `hfree` and co-isotropy put the pure `Xᵢ` in `K.L`: it is orthogonal to every element.
  have hX : paulix i ∈ K.L := by
    apply horth
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    rw [LinearMap.BilinForm.IsOrtho, omegaBilin_apply, omega_comm,
      FTQCLib.Gates.omega_paulix_left]
    exact hfree p hp
  -- the freed record meets the pinned rule's hypotheses
  have hpin' : ∀ p ∈ (applyHFree i ε K).L, p.X i = 0 := by
    rintro p ⟨p₀, hp₀, rfl⟩
    rw [pauliSwapOn_X, if_pos (Finset.mem_singleton_self i)]
    exact hfree p₀ hp₀
  have hq' : (applyHFree i ε K).q = q₀ := by
    change K.q + hSignPoly i ε K.m = q₀
    rw [hq, add_assoc, hSignPoly_add_self, add_zero]
  have hqfree' : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval (applyHFree i ε K).q (Function.update w i b)
        = DiagPhase.eval (applyHFree i ε K).q w := by
    intro w b
    rw [hq']
    exact hq₀free w b
  have horth' : LinearMap.BilinForm.orthogonal omegaBilin (applyHFree i ε K).L
      ≤ (applyHFree i ε K).L := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    refine Submodule.mem_map.mpr ⟨pauliSwapOn {i} x, horth ?_, pauliSwapOn_pauliSwapOn _ _⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    have hp' := hx (pauliSwapOn {i} p) (Submodule.mem_map.mpr ⟨p, hp, rfl⟩)
    rw [LinearMap.BilinForm.IsOrtho, omegaBilin_apply] at hp' ⊢
    rw [← omega_pauliSwapOn_singleton i, pauliSwapOn_pauliSwapOn]
    exact hp'
  -- pinning the freed record returns `K` with its offset gauged to `0` at `i`
  have hround : applyHPinned i (applyHFree i ε K)
      = (⟨K.m, K.q, K.c, K.L, Function.update K.x₀ i 0⟩ : KernelState n) := by
    have h0 := applyH_roundTrip' i ε
      (⟨K.m, K.q, K.c, K.L, Function.update K.x₀ i 0⟩ : KernelState n) (Function.update_self _ _ _)
    have h1 : applyHFree i ε
        (⟨K.m, K.q, K.c, K.L, Function.update K.x₀ i 0⟩ : KernelState n) = applyHFree i ε K := by
      change (⟨K.m, K.q + hSignPoly i ε K.m, (Real.sqrt 2 : ℂ) * K.c,
          Submodule.map (pauliSwapOn {i}) K.L,
          Function.update (Function.update K.x₀ i 0) i ε⟩ : KernelState n)
        = ⟨K.m, K.q + hSignPoly i ε K.m, (Real.sqrt 2 : ℂ) * K.c,
          Submodule.map (pauliSwapOn {i}) K.L, Function.update K.x₀ i ε⟩
      rw [Function.update_idem]
    rw [h1] at h0
    exact h0
  -- the gauge: since `Xᵢ ∈ K.L`, the offset's value at `i` does not change the denotation
  have hupd : Function.update K.x₀ i 0 = K.x₀ + ((K.x₀ i) • paulix i).X := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, X_smul, paulix_X, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_same, smul_eq_mul, mul_one]
      exact ((show ∀ x : ZMod 2, x + x = 0 by decide) (K.x₀ j)).symm
    · simp [hj]
  have hg : (K.x₀ i) • paulix i ∈ K.L := Submodule.smul_mem _ _ hX
  have hgauge : amp (ofKernelState
      (⟨K.m, K.q, K.c, K.L, Function.update K.x₀ i 0⟩ : KernelState n))
      = amp (ofKernelState K) := by
    funext w
    have hsupp : (∃ p ∈ K.L, w = Function.update K.x₀ i 0 + p.X)
        ↔ (∃ p ∈ K.L, w = K.x₀ + p.X) := by
      rw [hupd]
      constructor
      · rintro ⟨p, hp, hw⟩
        refine ⟨p + (K.x₀ i) • paulix i, Submodule.add_mem _ hp hg, ?_⟩
        rw [hw, X_add]
        abel
      · rintro ⟨p, hp, hw⟩
        refine ⟨p + (K.x₀ i) • paulix i, Submodule.add_mem _ hp hg, ?_⟩
        rw [hw, X_add]
        rw [show K.x₀ + ((K.x₀ i) • paulix i).X + (p.X + ((K.x₀ i) • paulix i).X)
            = K.x₀ + p.X + (((K.x₀ i) • paulix i).X + ((K.x₀ i) • paulix i).X) by abel,
          vec_add_self, add_zero]
    by_cases hw : ∃ p ∈ K.L, w = K.x₀ + p.X
    · rw [amp_ofKernelState_pos K hw, amp_ofKernelState_pos _ (hsupp.mpr hw)]
    · rw [amp_ofKernelState_neg K hw, amp_ofKernelState_neg _ (fun h => hw (hsupp.mp h))]
  -- the pinned rule's certificate on the freed record, then the Walsh transform's involution
  have hpinned := amp_ofKernelState_applyHPinned i (applyHFree i ε K) horth' hpin' hqfree' hm
  rw [hround, hgauge] at hpinned
  rw [hpinned]
  exact (walshTransform_involutive i _).symm

/-! ## Closure -/

/-- **Carrier closure for `applyHFree`.** The free rule sends carrier states to carrier states,
under the hypotheses that the bit carries no `Z`-support in the Lagrangian and that the exponent
is a part free of the bit plus the dyadic sign. -/
theorem isCarrier_applyHFree (i : Fin n) (ε : ZMod 2) {K : KernelState n}
    (hK : IsCarrier (ofKernelState K)) (hfree : ∀ p ∈ K.L, p.Z i = 0)
    (q₀ : DiagPhase n K.m) (hq : K.q = q₀ + hSignPoly i ε K.m)
    (hq₀free : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q₀ (Function.update w i b) = DiagPhase.eval q₀ w) :
    IsCarrier (ofKernelState (applyHFree i ε K)) := by
  refine ⟨hK.1, isStabilizer_map_pauliSwapOn i hK.2.1,
    coisotropic_map_pauliSwapOn i hK.2.1 (finrank_eq_of_isCarrier hK), ?_⟩
  rw [amp_ofKernelState_applyHFree i ε K q₀ hq hq₀free hK.2.2.1 hfree hK.1]
  exact walshTransform_ne_zero i hK.2.2.2

/-- **Floor closure for `applyHFree`.** The free rule sends floor carrier states to floor carrier
states, under the hypotheses of `isCarrier_applyHFree`. -/
theorem isFloor_applyHFree (i : Fin n) (ε : ZMod 2) {K : KernelState n}
    (hK : IsFloor (ofKernelState K)) (hfree : ∀ p ∈ K.L, p.Z i = 0)
    (q₀ : DiagPhase n K.m) (hq : K.q = q₀ + hSignPoly i ε K.m)
    (hq₀free : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q₀ (Function.update w i b) = DiagPhase.eval q₀ w) :
    IsFloor (ofKernelState (applyHFree i ε K)) := by
  refine ⟨isCarrier_applyHFree i ε hK.1 hfree q₀ hq hq₀free, ?_⟩
  rw [amp_ofKernelState_applyHFree i ε K q₀ hq hq₀free hK.1.2.2.1 hfree hK.1.1]
  exact stabilizedBy_map_pauliSwapOn_walshTransform i hK.2

/-! ## The free-mode certificate without the output's floor -/

/-- **The one-H certificate (free mode, `m = 1`), unconditional on the output.** The hypotheses
of `cert_free` less its output floor `hF'`, which `isFloor_applyHFree` supplies: decoding the
carrier state after the free rule is the chart's `H` after decoding. -/
theorem chartOf_applyHFree (i : Fin n) (q₀ : DiagPhase n 1) (ε : ZMod 2) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (hfree : ∀ p ∈ L, p.Z i = 0) (hx0 : x₀ i = 0)
    (hq₀free : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q₀ (Function.update w i b) = DiagPhase.eval q₀ w)
    (hF : IsFloor (ofKernelState (⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ : KernelState n))) :
    chartOf (applyHFree i ε ⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩)
        (isFloor_applyHFree i ε hF hfree q₀ rfl hq₀free) one_le_two
      = frameTransvectionYAction i
          (chartOf ⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ hF one_le_two) := by
  exact cert_free i q₀ ε c L x₀ hfree hx0 hq₀free hF _

end FTQCLib.Frame.Walkthrough

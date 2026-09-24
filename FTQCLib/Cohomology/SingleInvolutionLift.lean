/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.CliffordModel
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Every symplectic involution lifts to a self-inverse model element

The metaplectic obstruction of `metaplecticNonSplit_two` is purely **joint**: a single symplectic
involution `g` always lifts to a *self-inverse* element of the computable model
`SignedSymplectic n`, for every `n`. So the non-split defect is never carried by one gate — only by
a pair.

The construction. Take any lift `x₀` of `g` (from the bridge `act`). Its square is the pure-sign
element with defect character `κ(p) = x₀.s p + x₀.s (g p)`, which is additive and — because the sign
is 2-torsion — *vanishes on the whole fixed space* `Fix(g) = ker(g+1)`. Dualizing through the
nondegenerate `omegaBilin`, a functional vanishing on `ker T` factors as `omega u (T ·)`
(`crux_dual`), with `T = g + 1`. The pure-sign correction `δ(p) = dbl (omega u p)` cancels the
defect: `(x₀ · wElt)²` has sign `κ + (1+g)·δ = 2κ = 0`. No Arf invariant, no enumeration. -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame FTQCLib.Hilbert

variable {n : ℕ}

/-! ## The linear-algebra crux -/

set_option maxHeartbeats 800000 in
/-- A `ZMod 2`-functional vanishing on `ker T` factors through `T`: `κ p = omega u (T p)`. Pure
finite-dimensional duality over the nondegenerate `omegaBilin`. -/
theorem crux_dual (T : Pauli n →ₗ[ZMod 2] Pauli n)
    (κ : Pauli n →ₗ[ZMod 2] ZMod 2)
    (hker : ∀ p ∈ LinearMap.ker T, κ p = 0) :
    ∃ u : Pauli n, ∀ p, κ p = omega u (T p) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : FiniteDimensional (ZMod 2) (Pauli n) := inferInstance
  have h1 : κ ∈ (LinearMap.ker T).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator κ).mpr hker
  have h2 : κ ∈ LinearMap.range T.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]; exact h1
  obtain ⟨ψ, hψ⟩ := h2
  have hinj : Function.Injective (omegaBilin (n := n)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact omegaBilin_nondegenerate.1 x (fun y => by rw [hx]; rfl)
  obtain ⟨u, hu⟩ :=
    (LinearMap.linearEquivOfInjective (omegaBilin (n := n)) hinj
      Subspace.dual_finrank_eq.symm).surjective ψ
  rw [LinearMap.linearEquivOfInjective_apply] at hu
  refine ⟨u, fun p => ?_⟩
  rw [← hψ, LinearMap.dualMap_apply, ← hu, omegaBilin_apply]

/-! ## The `ZMod 2 ↔ ZMod 4` bridge (on the 2-torsion `{0,2}`) -/

/-- Doubling `ZMod 2 → ZMod 4` (`1 ↦ 2`). -/
def dbl (x : ZMod 2) : ZMod 4 := 2 * (x.val : ZMod 4)

/-- Halving `ZMod 4 → ZMod 2`, a section of `dbl` on the 2-torsion `{0,2}`. -/
def hlv (x : ZMod 4) : ZMod 2 := ((x.val / 2 : ℕ) : ZMod 2)

theorem dbl_add (a b : ZMod 2) : dbl (a + b) = dbl a + dbl b := by revert a b; decide

theorem dbl_hlv {x : ZMod 4} (hx : 2 * x = 0) : dbl (hlv x) = x := by revert hx; revert x; decide

theorem hlv_add {a b : ZMod 4} (ha : 2 * a = 0) (hb : 2 * b = 0) :
    hlv (a + b) = hlv a + hlv b := by revert ha hb; revert a b; decide

/-! ## The repair construction -/

/-- **Repair any lift to an involution.** If `x₀ : SignedSymplectic n` has a self-inverse symplectic
part (`x₀.g² = id`), then there is a self-inverse model element with the same symplectic part. -/
theorem involutionLift_of_sqOne (x₀ : SignedSymplectic n)
    (hsq : ∀ p, x₀.g (x₀.g p) = p) :
    ∃ x : SignedSymplectic n, x.g = x₀.g ∧ x * x = 1 := by
  -- the defect character κ p = x₀.s p + x₀.s (G p)
  have κ_2tor : ∀ p, 2 * (x₀.s p + x₀.s (x₀.g p)) = 0 := by
    intro p; rw [mul_add, SignedSymplectic.two_smul_s, SignedSymplectic.two_smul_s, add_zero]
  have hfd : ∀ p q, frameDistortion x₀.g p q
      + frameDistortion x₀.g (x₀.g p) (x₀.g q) = 0 := by
    intro p q; simp only [frameDistortion, hsq]; ring
  have κ_add : ∀ p q, x₀.s (p + q) + x₀.s (x₀.g (p + q))
      = (x₀.s p + x₀.s (x₀.g p)) + (x₀.s q + x₀.s (x₀.g q)) := by
    intro p q
    rw [map_add x₀.g p q, x₀.valid p q, x₀.valid (x₀.g p) (x₀.g q)]
    linear_combination hfd p q
  -- kbar : the ZMod 2 functional from the defect
  let kbar : Pauli n →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun p => hlv (x₀.s p + x₀.s (x₀.g p))
      map_add' := fun p q => by
        show hlv (x₀.s (p + q) + x₀.s (x₀.g (p + q))) = _
        rw [κ_add p q, hlv_add (κ_2tor p) (κ_2tor q)]
      map_smul' := fun c p => by
        fin_cases c
        · show hlv (x₀.s ((0 : ZMod 2) • p) + x₀.s (x₀.g ((0 : ZMod 2) • p)))
              = (0 : ZMod 2) • hlv (x₀.s p + x₀.s (x₀.g p))
          rw [zero_smul, map_zero, zero_smul,
            show x₀.s 0 + x₀.s 0 = 0 by linear_combination SignedSymplectic.two_smul_s x₀ 0]
          rfl
        · show hlv (x₀.s ((1 : ZMod 2) • p) + x₀.s (x₀.g ((1 : ZMod 2) • p)))
              = (1 : ZMod 2) • hlv (x₀.s p + x₀.s (x₀.g p))
          rw [one_smul, one_smul] }
  -- T = g + 1, kernel = Fix(g); kbar vanishes there
  let T : Pauli n →ₗ[ZMod 2] Pauli n := x₀.g.toLinearMap - LinearMap.id
  have hTp : ∀ p, T p = p + x₀.g p := by
    intro p
    show x₀.g p - p = p + x₀.g p
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (Pauli.pauli_add_self p), add_comm]
  have hker : ∀ p ∈ LinearMap.ker T, kbar p = 0 := by
    intro p hp
    have hgp : x₀.g p = p := by
      have hT0 : p + x₀.g p = 0 := by rw [← hTp]; exact hp
      calc x₀.g p = p + (p + x₀.g p) := by rw [← add_assoc, Pauli.pauli_add_self, zero_add]
        _ = p + 0 := by rw [hT0]
        _ = p := add_zero p
    show hlv (x₀.s p + x₀.s (x₀.g p)) = 0
    rw [hgp, show x₀.s p + x₀.s p = 0 by linear_combination SignedSymplectic.two_smul_s x₀ p]
    rfl
  obtain ⟨u, hu⟩ := crux_dual T kbar hker
  -- the pure-sign correction wElt (g = id, sign δ p = dbl (omega u p))
  let wElt : SignedSymplectic n :=
    { g := LinearEquiv.refl (ZMod 2) (Pauli n)
      hg := isClifford_refl
      s := fun p => dbl (omega u p)
      valid := by
        intro p q
        show dbl (omega u (p + q)) = dbl (omega u p) + dbl (omega u q) + frameDistortion _ p q
        rw [omega_add_right, dbl_add,
          show frameDistortion (LinearEquiv.refl (ZMod 2) (Pauli n)) p q = 0 by
            simp [frameDistortion], add_zero] }
  have hxg : (x₀ * wElt).g = x₀.g := LinearEquiv.refl_trans x₀.g
  -- δ p + δ (g p) = κ p, the defect cancellation
  have hδsum : ∀ p, dbl (omega u p) + dbl (omega u (x₀.g p)) = x₀.s p + x₀.s (x₀.g p) := by
    intro p
    rw [← dbl_add, ← omega_add_right, ← hTp p, ← hu p]
    exact dbl_hlv (κ_2tor p)
  refine ⟨x₀ * wElt, hxg, ?_⟩
  refine SignedSymplectic.ext ?_ ?_
  · show ((x₀ * wElt).g).trans ((x₀ * wElt).g) = LinearEquiv.refl (ZMod 2) (Pauli n)
    rw [hxg]; exact LinearEquiv.ext fun p => hsq p
  · funext p
    show (wElt.s p + x₀.s (wElt.g p)) + (wElt.s (x₀.g p) + x₀.s (wElt.g (x₀.g p))) = 0
    show (dbl (omega u p) + x₀.s p) + (dbl (omega u (x₀.g p)) + x₀.s (x₀.g p)) = 0
    linear_combination hδsum p + κ_2tor p

/-- **Every symplectic involution lifts to a self-inverse model element**, for all `n` — the
metaplectic obstruction is purely joint. -/
theorem singleInvolution_lifts (g : Pauli n ≃ₗ[ZMod 2] Pauli n) (hg : IsClifford g)
    (hg2 : ∀ p, g (g p) = p) :
    ∃ x : SignedSymplectic n, x.g = g ∧ x * x = 1 := by
  obtain ⟨c, hc⟩ := cliffordModPhaseToSp_surjective n ⟨g, mem_spSubgroup.mpr hg⟩
  have hx0g : (act c).g = g := by rw [act_g, hc]
  obtain ⟨x, hxg, hxx⟩ := involutionLift_of_sqOne (act c) (by rw [hx0g]; exact hg2)
  exact ⟨x, by rw [hxg, hx0g], hxx⟩

end FTQCLib.Cohomology

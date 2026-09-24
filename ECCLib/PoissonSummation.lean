/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.FiniteFourier
import ECCLib.Annihilator

/-!
# Finite Poisson summation over a subgroup

For a finite abelian group `V`, a subgroup `H ≤ V`, and `f : V → ℂ`, summing `f` over `H` equals a
sum of its Fourier coefficients over the character annihilator `H^⊥`:

`∑_{x ∈ H} f(x) = |H| · ∑_{ξ ∈ H^⊥} f̂(ξ)`.

The annihilator itself, restricted character orthogonality, and the size relation
`|H^⊥|·|H| = |V|` live one layer down in `ECCLib.Annihilator`, which needs no Fourier
transform; this module is the summation formula alone — `fourier_inversion` plus a sum swap.

For the coding layer, a code is a subgroup `C ≤ V` and its dual is `C^⊥`; Poisson summation is
the MacWilliams engine, and the size relation is the dual-code size condition. Those are what
`ECCLib.Codes` builds on.

## Main results

* `poisson_summation` — `∑_{x ∈ H} f(x) = |H| · ∑_{ξ ∈ H^⊥} f̂(ξ)`.

## Implementation notes

The annihilator, restricted character orthogonality and the size relation live one layer down
in `ECCLib.Annihilator`, which needs no Fourier transform; this module is the summation
formula alone.
-/

namespace ECCLib

open scoped BigOperators ComplexConjugate
open Finset

variable {V : Type*} [AddCommGroup V] [Fintype V]

open Classical in
/-- **Finite Poisson summation over a subgroup.**
`∑_{x ∈ H} f(x) = |H| · ∑_{ξ ∈ H^⊥} f̂(ξ)`. -/
theorem poisson_summation (H : AddSubgroup V) (f : V → ℂ) :
    ∑ x : H, f (x : V) = (Nat.card H : ℂ) * ∑ ξ ∈ charAnnih H, fourierT f ξ := by
  haveI : Nonempty V := ⟨0⟩
  have hinv : ∀ x : H, f (x : V) = ∑ ξ : AddChar V ℂ, fourierT f ξ * ξ (x : V) :=
    fun x => (fourier_inversion f (x : V)).symm
  have step : ∑ x : H, f (x : V)
      = ∑ ξ : AddChar V ℂ, fourierT f ξ * (∑ x : H, ξ (x : V)) := by
    simp_rw [hinv]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun ξ _ => by rw [Finset.mul_sum])
  rw [step]
  simp_rw [sum_char_over_subgroup, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ξ _ => by ring)

end ECCLib

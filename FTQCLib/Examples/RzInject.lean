/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.TGadget
import FTQCLib.Hierarchy.RzApprox

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # `R_z(θ)` approximation by injection of 2^k-th-root states — the resource axis (F5)

The diagonal `R_z(θ)` approximation of `RzTable`, realized by **gate injection** instead of the direct
exponent rewrite: each tower rung is teleported in by consuming its resource state and applying a
measurement-conditional feed-forward correction. Frame-pure at the exponent level — built on the frame-pure
`TGadget.rzGadget_correct` (the whole 2^k-th-root tower injection, correction included). Injection is *one*
resource-consuming route; the direct rewrite (`RzTable`) stays primary. This file makes the **resource cost**
of an approximation explicit and shows the **precision ↔ resource-level** coupling.

* **Full injection** (`rzInject_rung`, the composition): the corrected injected exponent equals the direct
  approximant, so the arc distance is `π/2^m`, identical to the direct route (injection is exact).
* **Truncated tower** (drop the fine rungs): a coarser approximant with fewer / lower-level resource states —
  the precision-vs-resource tradeoff.

The heavier measurement-conditioned *state* realization (`Inject.lean`) is the optional Hilbert-side
companion. -/

namespace FTQCLib.Frame.Inject

open FTQCLib FTQCLib.Hierarchy MvPolynomial

/-! ## The single-rung injection identity, for an arbitrary rung coefficient -/

/-- **Injecting one tower rung, arbitrary coefficient.** Resource `C a · X₁` on the ancilla (the state
`R_z(2π·a/2^m)|+⟩`), CNOT-entangle (`affinePushforward 0 1`), measure `Z₁ = b` (`freezeAt 1 b`), then the
feed-forward correction `2·(a·b)·X₀`, and the data-wire exponent is the injected rung `C a · X₀` up to the
measurement-conditional global-phase constant `C (a·b)`. The coefficient-general form of
`TGadget.rzGadget_correct` (there `a = 1`), by the same `bind₁` algebra. -/
theorem rzInject_rung {m : ℕ} (a : ZMod (2 ^ m)) (b : ZMod 2) :
    freezeAt (1 : Fin 2) b (DiagPhase.affinePushforward 0 1 (C a * X 1))
        + 2 * C (a * (b.val : ZMod (2 ^ m))) * X (0 : Fin 2)
      = C a * X (0 : Fin 2) + C (a * (b.val : ZMod (2 ^ m))) := by
  have h0 : ((0 : Fin 2) = 1) = False := eq_false (by decide)
  have h1 : ((1 : Fin 2) = 1) = True := eq_true rfl
  unfold freezeAt DiagPhase.affinePushforward DiagPhase.cnotSubst
  simp only [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right, map_add, map_sub,
    map_ofNat, h0, h1, if_true, if_false]
  ring

/-! ## The resource ledger: which resource state each precision demands -/

/-- **The resource state for precision `m` is level `m`.** The finest rung `R_{m-1} = Z^{1/2^{m-1}}` is
injected from the resource exponent `rzGatePoly 1 m` (the state `R_z(2π/2^m)|+⟩`), which sits at level `m` —
so reaching arc precision `π/2^m` demands a level-`m` (2^m-th-root) resource state. `precision π/2^m ⟺
resource level m`. -/
theorem resource_finest_level (m : ℕ) (hm : 1 ≤ m) :
    (DiagPhase.rzGatePoly (1 : Fin 2) m).level = m := by
  haveI : Fact (1 < 2 ^ m) := ⟨Nat.one_lt_two_pow (by omega)⟩
  exact DiagPhase.rzGatePoly_level 1 m (by omega)

/-! ## The full injection: composing the rungs = the direct approximant, up to a global phase -/

/-- The measurement-conditional global-phase byproduct the injections accumulate: `Σ_k 2^k · b_k` over the
set bits `k` of the coefficient. A constant term (a global phase), unobservable. -/
noncomputable def byproduct (m : ℕ) (c : ZMod (2 ^ m)) (b : ℕ → ZMod 2) : ZMod (2 ^ m) :=
  ∑ k ∈ c.val.bitIndices.toFinset, (2 : ZMod (2 ^ m)) ^ k * ((b k).val : ZMod (2 ^ m))

/-- **The full injected approximant.** For coefficient `c`, inject one rung per set bit `k` — resource
`C 2^k · X₁`, CNOT-entangle, measure `Z₁ = b_k`, feed-forward correct — and sum the resulting data-wire
exponents. This is the injection realization of the `RzTable` tower composition. -/
noncomputable def injectedApprox (m : ℕ) (c : ZMod (2 ^ m)) (b : ℕ → ZMod 2) : DiagPhase 2 m :=
  ∑ k ∈ c.val.bitIndices.toFinset,
    (freezeAt (1 : Fin 2) (b k) (DiagPhase.affinePushforward 0 1 (C ((2 : ZMod (2 ^ m)) ^ k) * X 1))
      + 2 * C ((2 : ZMod (2 ^ m)) ^ k * ((b k).val : ZMod (2 ^ m))) * X (0 : Fin 2))

/-- **Two routes agree.** The full injected approximant equals the direct `RzTable` approximant `C c · X₀`
plus the measurement-conditional global-phase byproduct `C(Σ 2^k b_k)`. So injection realizes the *same*
approximant up to a global phase — the injection is exact, and the approximation error is entirely the
rounding `c ≈ θ`, unchanged from the direct route. -/
theorem injectedApprox_eq (m : ℕ) (c : ZMod (2 ^ m)) (b : ℕ → ZMod 2) :
    injectedApprox m c b = C c * X (0 : Fin 2) + C (byproduct m c b) := by
  unfold injectedApprox byproduct
  rw [Finset.sum_congr rfl (fun k _ => rzInject_rung ((2 : ZMod (2 ^ m)) ^ k) (b k)),
    Finset.sum_add_distrib]
  congr 1
  · exact (DiagPhase.rz_approx_composition c 0).symm
  · rw [map_sum]

open Real in
/-- **Full injection — the distance is unchanged (example 1).** For any measurement outcomes `b`, there is a
coefficient `c` such that the injected approximant equals the direct `C c · X₀` up to the global-phase
byproduct, and that approximant is within arc `π/2^m` of `R_z(θ)` on every input. So injection achieves the
*same* `π/2^m` as the direct route — it is exact; the rounding `c ≈ θ` is the only error, unchanged. -/
theorem injectedApprox_distance (θ : ℝ) (m : ℕ) (b : ℕ → ZMod 2) :
    ∃ c : ZMod (2 ^ m),
      injectedApprox m c b = C c * X (0 : Fin 2) + C (byproduct m c b) ∧
      ∀ v : Fin 2 → ZMod 2, ∃ k : ℤ,
        |DiagPhase.realPhase (C c * X (0 : Fin 2)) v - (v 0).val * θ - 2 * π * k| ≤ π / 2 ^ m := by
  obtain ⟨c, hc⟩ := DiagPhase.rz_dyadic_approx θ (0 : Fin 2) m
  exact ⟨c, injectedApprox_eq m c b, hc⟩

/-! ## Truncated tower — precision vs resource cost (example 2) -/

/-- Active-branch input on the data wire (`Fin 2`). -/
def w₁ : Fin 2 → ZMod 2 := fun _ => 1

/-- **Truncated — the precision-vs-resource tradeoff (example 2).** Dropping the finest rung (bit `0`, whose
resource is the level-`4` state, by `resource_finest_level`) from the `m = 4` approximant of `2π/3` — keeping
only bit `2` (`C 4 · X₀`, a single injection whose resource is the coarser level-`2` `S`-state) — gives arc
distance exactly `π/6`, versus `π/24` for the full two injections (`RzTable.ladder_four_exact`). One fewer,
cheaper resource state; coarser accuracy — the precision↔resource tradeoff made concrete. -/
theorem truncated_2pi3_dist :
    |DiagPhase.realPhase (C (4 : ZMod (2 ^ 4)) * X (0 : Fin 2)) w₁ - 2 * Real.pi / 3| = Real.pi / 6 := by
  rw [DiagPhase.realPhase_linear,
    show ((w₁ 0).val : ℝ) = 1 from by rw [show (w₁ 0).val = 1 from by decide, Nat.cast_one], one_mul,
    show (((4 : ZMod (2 ^ 4)).val : ℝ)) = 4 from by
      rw [show (4 : ZMod (2 ^ 4)).val = 4 from by decide]; norm_num]
  have hsign : 2 * Real.pi * (4 : ℝ) / 2 ^ 4 - 2 * Real.pi / 3 ≤ 0 := by nlinarith [Real.pi_pos]
  rw [abs_of_nonpos hsign]
  ring

end FTQCLib.Frame.Inject

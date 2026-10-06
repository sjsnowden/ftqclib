/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierRules
import FTQCLib.Carrier.AntipodalKernel

/-!
# The constructions read backwards

Four constructions each take a carrier state and return a carrier state at the same precision, one
bound bit higher, related to it by a chain of `CarrierRuleWithin` steps between carrier states at
that precision: one rule of `CarrierRule` (`CarrierRules.lean`) read backwards, then at most one R4
that restates the exponent. The direct route to completeness at every precision
(`RewriteCompleteness.lean`, `docs/TARGETS.md` T07) uses them to widen both supports and to match
heights and scales, and since none changes the precision, conservativity can use them too.

## Main results

* `exists_widen` — widens the support by a collapse: the scale is divided by `√2` and the X-shadow
  grows strictly.
* `exists_pad` — pads the height by a halving, at height at least one: the scale is multiplied by
  `√2`.
* `exists_unusedBit` — adds an unused bound bit: the scale is divided by `√2`.
* `exists_unrotate` — reverses a rotation by `a` with `2a = 2^{m−1}`: the scale is multiplied by
  `√2 / (1 + ζ^a)`, which is well defined.

## Implementation notes

* Every construction keeps the Lagrangian and the offset except the widening, whose new Lagrangian
  is `(L ∩ x^⊥) + ⟨x⟩` for the X-type Pauli `x` of a word outside the X-shadow.
* The new exponent is found by representability (`DiagPhase.exists_diagPhase_eval`,
  `FTQCLib/Hierarchy/Defs.lean`): every function of the
  words into `ZMod (2^m)` is the value of an exponent, so each construction prescribes its
  exponent's values and never writes a polynomial.
* Each chain is stated from the new carrier state to the old one, the direction in which the rule
  it reads backwards runs.
* The four constructions are public so that a gate row and the proofs of `RewriteCompleteness.lean`
  see them; most helpers are private. Four helpers are also public and shared with
  `ScaleMatching.lean` and/or `RewriteCompleteness.lean`, which restated them privately before this
  module carried the one copy: `ofReal_sqrt_two_ne_zero`, `isCarrier_of_stateEq`,
  `eqvGen_carrierRuleWithin_of_carrierRule` and `exists_diagPhase_append`; `pointPoly`,
  `eval_pointFactor`, `eval_pointPoly` and `exists_diagPhase_eval` moved to
  `FTQCLib/Hierarchy/Defs.lean` (docs/STEPS.md, entry 2026-09-30h). The case split "a bit of
  `ZMod 2` is `0` or `1`" that both restated privately is already public library-wide as
  `FTQCLib.Pauli.zmod_two_eq_zero_or_one` (`FTQCLib/Pauli/Cocycle.lean`, opened here); neither copy
  is kept.
* Everything here is frame-pure: no `FTQCLib.Hilbert` module and nothing from `FTQCLib/Explore/`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

section Constructions

open FTQCLib.Hierarchy.DiagPhase

/-! ### Exponents with prescribed values -/

/-- An exponent with prescribed values at every free word and bound word. Public and shared with
`RewriteCompleteness.lean`, which restated it privately (`exists_diagPhase_append_rc`, with the
proof inlined rather than routed through `exists_diagPhase_eval`) before this module carried the
one copy. -/
theorem exists_diagPhase_append {m h : ℕ}
    (g : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod (2 ^ m)) :
    ∃ Q : DiagPhase (n + h) m, ∀ w y, Q.eval (Fin.append w y) = g w y := by
  obtain ⟨G, hG⟩ := exists_diagPhase_eval (N := n + h) (m := m)
    (fun v => g (fun i => v (Fin.castAdd h i)) (fun i => v (Fin.natAdd n i)))
  refine ⟨G, fun w y => ?_⟩
  rw [hG]
  simp only [Fin.append_left, Fin.append_right]

/-- An exponent with one more bound bit, last, with prescribed values. -/
private theorem exists_diagPhase_snoc {m h : ℕ}
    (g : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod 2 → ZMod (2 ^ m)) :
    ∃ Q : DiagPhase (n + h + 1) m, ∀ w y b, Q.eval (Fin.snoc (Fin.append w y) b) = g w y b := by
  obtain ⟨G, hG⟩ := exists_diagPhase_eval (N := n + h + 1) (m := m)
    (fun v => g (fun i => v (Fin.castSucc (Fin.castAdd h i)))
      (fun i => v (Fin.castSucc (Fin.natAdd n i))) (v (Fin.last (n + h))))
  refine ⟨G, fun w y b => ?_⟩
  rw [hG]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.append_left, Fin.append_right]

/-! ### Carrier states along a chain -/

/-- A state with a Lagrangian and positive precision that denotes the state of a carrier state is a
carrier state. -/
theorem isCarrier_of_stateEq {A B : KernelSumState n} (hB : IsCarrier B)
    (hAB : StateEq A B) (hm : 1 ≤ A.m) (hstab : IsStabilizer A.L)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin A.L ≤ A.L) : IsCarrier A := by
  refine ⟨hm, hstab, horth, ?_⟩
  have h : amp A = amp B := hAB
  rw [h]
  exact hB.2.2.2

/-- **A single step, as a chain.** One step between carrier states at precision `m` is a chain
between carrier states at precision `m`. -/
theorem eqvGen_carrierRuleWithin_of_carrierRule {m : ℕ} {A B : KernelSumState n}
    (hAB : CarrierRule A B) (hA : IsCarrier A) (hAm : A.m = m) (hB : IsCarrier B) (hBm : B.m = m) :
    Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m) A B :=
  Relation.EqvGen.rel _ _ ⟨hAB, ⟨hA, hAm⟩, ⟨hB, hBm⟩⟩

/-! ### An unused bound bit -/

/-- **An unused bound bit.** Over a carrier state `⟨m, h, Q, c, L, x₀⟩` there is a carrier state
one bound bit higher, with scale `c/√2`, whose exponent does not read its last bound bit: a collapse
with `σ = 0` and `ε = 0` drops the bit, and R4 restates the exponent. -/
theorem exists_unusedBit {m h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) :
    ∃ Q' : DiagPhase (n + (h + 1)) m,
      IsCarrier (⟨m, h + 1, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + 1, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  have hm : 1 ≤ m := hS.1
  obtain ⟨Q', hQ'0⟩ := exists_diagPhase_snoc (n := n) (m := m) (h := h)
    (fun w y _ => Q.eval (Fin.append w y))
  have hQ' : ∀ (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) (b : ZMod 2),
      Q'.eval (Fin.snoc (Fin.append w y) b) = Q.eval (Fin.append w y) := hQ'0
  have hsign : SignAffine Q' L x₀ 0 0 := by
    intro w _ y
    rw [lastDiff_eval, hQ', hQ', sub_self]
    simp [dotF2]
  have hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) ↔
      (∃ p ∈ L, w = x₀ + p.X) ∧ (0 : ZMod 2) + dotF2 0 w = 0 := by
    intro w
    simp [dotF2]
  have hstep := CarrierRule.collapse hm Q' (c / (Real.sqrt 2 : ℂ)) L x₀ 0 0 hsign L x₀ hsupp
  have hscale : (Real.sqrt 2 : ℂ) * (c / (Real.sqrt 2 : ℂ)) = c := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ c ofReal_sqrt_two_ne_zero]
  have hmid : elimCollapse Q' (c / (Real.sqrt 2 : ℂ)) L x₀
      = (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n) := by
    unfold elimCollapse
    rw [hscale]
  rw [hmid] at hstep
  have hgauge : CarrierRule (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ :=
    CarrierRule.gauge (GaugeStep.congrSupport Q (snocFreeze 0 Q') c L x₀
      (fun w _ y => by rw [snocFreeze_eval, hQ']))
  have hmidC : IsCarrier (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hS (stateEq_of_carrierRule hgauge) hm hS.2.1 hS.2.2.1
  have htopC : IsCarrier (⟨m, h + 1, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hmidC (stateEq_of_carrierRule hstep) hm hS.2.1 hS.2.2.1
  exact ⟨Q', htopC, Relation.EqvGen.trans _ _ _
    (eqvGen_carrierRuleWithin_of_carrierRule hstep htopC rfl hmidC rfl)
    (eqvGen_carrierRuleWithin_of_carrierRule hgauge hmidC rfl hS rfl)⟩

/-! ### A reversed rotation -/

/-- **A reversed rotation.** Over a carrier state `⟨m, h, Q, c, L, x₀⟩` and a residue `a` with
`2a = 2^{m−1}` there is a carrier state one bound bit higher, with scale `c·√2/(1 + ζ^a)`, whose
exponent grows by `a` along its last bound bit: a rotation by `a` with `Λ = 0` drops the bit, and
R4 restates the exponent. The first conjunct says the scale is well defined. -/
theorem exists_unrotate {m h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) {a : ZMod (2 ^ m)}
    (ha : 2 * a = (2 : ZMod (2 ^ m)) ^ (m - 1)) :
    1 + charOf m a ≠ 0 ∧ ∃ Q' : DiagPhase (n + (h + 1)) m,
      IsCarrier (⟨m, h + 1, Q', c * (Real.sqrt 2 : ℂ) / (1 + charOf m a), L, x₀⟩ :
        KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + 1, Q', c * (Real.sqrt 2 : ℂ) / (1 + charOf m a), L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  have hm : 1 ≤ m := hS.1
  have hχ : 1 + charOf m a ≠ 0 := by
    intro h0
    have hx : charOf m a = -1 := by linear_combination h0
    have htop : charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)) = -1 := by
      simpa using charOf_two_pow_mul hm 1
    have h2 : charOf m a * charOf m a = -1 := by
      rw [← charOf_add, ← two_mul, ha, htop]
    rw [hx] at h2
    norm_num at h2
  refine ⟨hχ, ?_⟩
  obtain ⟨Q', hQ'0⟩ := exists_diagPhase_snoc (n := n) (m := m) (h := h)
    (fun w y b => if b = 0 then Q.eval (Fin.append w y) else Q.eval (Fin.append w y) + a)
  have hQ' : ∀ (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) (b : ZMod 2),
      Q'.eval (Fin.snoc (Fin.append w y) b)
        = if b = 0 then Q.eval (Fin.append w y) else Q.eval (Fin.append w y) + a := hQ'0
  have hrot : RotateData Q' L x₀ a 0 := by
    refine ⟨ha, fun w _ y => ⟨0, ?_, ?_⟩⟩
    · simp [DiagPhase.eval]
    · rw [lastDiff_eval, hQ', hQ', if_neg (by decide : (1 : ZMod 2) ≠ 0), if_pos rfl]
      simp
  have hstep := CarrierRule.rotate hm Q' (c * (Real.sqrt 2 : ℂ) / (1 + charOf m a)) L x₀ a 0
    hrot L x₀ (fun _ => Iff.rfl)
  have hscale : c * (Real.sqrt 2 : ℂ) / (1 + charOf m a) * (1 + charOf m a)
      / (Real.sqrt 2 : ℂ) = c := by
    rw [div_mul_cancel₀ _ hχ, mul_div_cancel_right₀ c ofReal_sqrt_two_ne_zero]
  have hmid : elimRotate Q' a 0 (c * (Real.sqrt 2 : ℂ) / (1 + charOf m a)) L x₀
      = (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n) := by
    unfold elimRotate
    rw [mul_zero, add_zero, hscale]
  rw [hmid] at hstep
  have hgauge : CarrierRule (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ :=
    CarrierRule.gauge (GaugeStep.congrSupport Q (snocFreeze 0 Q') c L x₀
      (fun w _ y => by rw [snocFreeze_eval, hQ', if_pos rfl]))
  have hmidC : IsCarrier (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hS (stateEq_of_carrierRule hgauge) hm hS.2.1 hS.2.2.1
  have htopC : IsCarrier (⟨m, h + 1, Q', c * (Real.sqrt 2 : ℂ) / (1 + charOf m a), L, x₀⟩ :
      KernelSumState n) :=
    isCarrier_of_stateEq hmidC (stateEq_of_carrierRule hstep) hm hS.2.1 hS.2.2.1
  exact ⟨Q', htopC, Relation.EqvGen.trans _ _ _
    (eqvGen_carrierRuleWithin_of_carrierRule hstep htopC rfl hmidC rfl)
    (eqvGen_carrierRuleWithin_of_carrierRule hgauge hmidC rfl hS rfl)⟩

/-! ### A padding by halving -/

/-- **A padding by halving.** Over a carrier state `⟨m, h + 1, Q, c, L, x₀⟩` there is a carrier
state one bound bit higher, with scale `c·√2`, that reads `Q` where its last bound bit is `0` and
carries antipodal pairs (`0` and `2^{m−1}`, paired by the first bound bit) where it is `1`: a
halving deletes the pairs. The height is at least one so that the pairs have a bit to be paired
by. -/
theorem exists_pad {m h : ℕ} {Q : DiagPhase (n + (h + 1)) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) :
    ∃ Q' : DiagPhase (n + (h + 1 + 1)) m,
      IsCarrier (⟨m, h + 1 + 1, Q', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + 1 + 1, Q', c * (Real.sqrt 2 : ℂ), L, x₀⟩ ⟨m, h + 1, Q, c, L, x₀⟩ := by
  classical
  have hm : 1 ≤ m := hS.1
  obtain ⟨Q', hQ'0⟩ := exists_diagPhase_append (n := n) (m := m) (h := h + 1 + 1)
    (fun w y' => if y' (Fin.last (h + 1)) = 0 then Q.eval (Fin.append w (Fin.init y'))
      else if y' 0 = 0 then 0 else (2 : ZMod (2 ^ m)) ^ (m - 1))
  have hQ' : ∀ (w : Fin n → ZMod 2) (y' : Fin (h + 1 + 1) → ZMod 2),
      Q'.eval (Fin.append w y') = if y' (Fin.last (h + 1)) = 0
        then Q.eval (Fin.append w (Fin.init y'))
        else if y' 0 = 0 then 0 else (2 : ZMod (2 ^ m)) ^ (m - 1) := hQ'0
  let e : (Fin (h + 1) → ZMod 2) ↪ (Fin (h + 1 + 1) → ZMod 2) :=
    ⟨fun y => Fin.snoc y 0, fun y y' hyy => by
      simpa only [Fin.init_snoc] using
        congrArg (fun q : Fin (h + 1 + 1) → ZMod 2 => Fin.init q) hyy⟩
  let P : Finset (Fin (h + 1 + 1) → ZMod 2) :=
    Finset.univ.filter fun y' => y' (Fin.last (h + 1)) = 1
  let τ : Equiv.Perm (Fin (h + 1 + 1) → ZMod 2) :=
    Equiv.addRight (Pi.single (0 : Fin (h + 1 + 1)) (1 : ZMod 2))
  have hne : (Fin.last (h + 1) : Fin (h + 1 + 1)) ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    simp at this
  have hlast : ∀ y' : Fin (h + 1 + 1) → ZMod 2,
      (τ y') (Fin.last (h + 1)) = y' (Fin.last (h + 1)) := by
    intro y'
    change y' (Fin.last (h + 1))
        + (Pi.single (0 : Fin (h + 1 + 1)) (1 : ZMod 2) : Fin (h + 1 + 1) → ZMod 2)
          (Fin.last (h + 1))
      = y' (Fin.last (h + 1))
    rw [Pi.single_eq_of_ne hne, add_zero]
  have hfirst : ∀ y' : Fin (h + 1 + 1) → ZMod 2, (τ y') 0 = y' 0 + 1 := by
    intro y'
    change y' 0 + (Pi.single (0 : Fin (h + 1 + 1)) (1 : ZMod 2) : Fin (h + 1 + 1) → ZMod 2) 0
      = y' 0 + 1
    rw [Pi.single_eq_same]
  have hP : ∀ y', y' ∈ P ↔ ∀ y, e y ≠ y' := by
    intro y'
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1 y hy
      rw [← hy] at h1
      change (Fin.snoc y (0 : ZMod 2) : Fin (h + 1 + 1) → ZMod 2) (Fin.last (h + 1)) = 1 at h1
      rw [Fin.snoc_last] at h1
      exact absurd h1 (by decide)
    · intro hne'
      rcases zmod_two_eq_zero_or_one (y' (Fin.last (h + 1))) with h0 | h1
      · refine absurd ?_ (hne' (Fin.init y'))
        change (Fin.snoc (Fin.init y') (0 : ZMod 2) : Fin (h + 1 + 1) → ZMod 2) = y'
        rw [← h0]
        exact Fin.snoc_init_self y'
      · exact h1
  have hread : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin (h + 1) → ZMod 2,
      Q.eval (Fin.append w y) = Q'.eval (Fin.append w (e y)) := by
    intro w _ y
    rw [hQ']
    simp [e]
  have hpair : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q' w P τ := by
    intro w _
    refine ⟨fun y' => ?_, fun y' hy' => ?_⟩
    · simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, hlast]
    · have h1 : y' (Fin.last (h + 1)) = 1 := by simpa [P] using hy'
      have h1' : (τ y') (Fin.last (h + 1)) = 1 := by rw [hlast]; exact h1
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [hQ', hQ', h1', h1, hfirst]
      rcases zmod_two_eq_zero_or_one (y' 0) with h0 | h0
      · simp [h0]
      · simp [h0, h2, AntipodalKernel.two_pow_pred_add_self hm]
  have hstep := CarrierRule.halve hm Q' Q (c * (Real.sqrt 2 : ℂ)) L x₀ e P τ hP hread hpair
  rw [mul_div_cancel_right₀ c ofReal_sqrt_two_ne_zero] at hstep
  have htopC : IsCarrier (⟨m, h + 1 + 1, Q', c * (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hS (stateEq_of_carrierRule hstep) hm hS.2.1 hS.2.2.1
  exact ⟨Q', htopC, eqvGen_carrierRuleWithin_of_carrierRule hstep htopC rfl hS rfl⟩

/-! ### A widening of the support by a collapse -/

/-- The Lagrangian widened by the Pauli `x`: the part of `L` commuting with `x`, and `x`. -/
private def widenL (L : Submodule (ZMod 2) (Pauli n)) (x : Pauli n) :
    Submodule (ZMod 2) (Pauli n) :=
  (L ⊓ LinearMap.ker (omegaBilin x)) ⊔ Submodule.span (ZMod 2) {x}

/-- The elements of `widenL L x`: an element of `L` commuting with `x`, plus a multiple of `x`. -/
private theorem mem_widenL_iff {L : Submodule (ZMod 2) (Pauli n)} {x q : Pauli n} :
    q ∈ widenL L x ↔ ∃ y ∈ L, omega x y = 0 ∧ ∃ a : ZMod 2, q = y + a • x := by
  unfold widenL
  constructor
  · intro hq
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hq
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨y, (Submodule.mem_inf.mp hy).1, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hy).2, a,
      rfl⟩
  · rintro ⟨y, hy, hy0, a, rfl⟩
    exact Submodule.mem_sup.mpr ⟨y, Submodule.mem_inf.mpr ⟨hy, LinearMap.mem_ker.mpr hy0⟩,
      a • x, Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x), rfl⟩

/-- `widenL` of an isotropic subspace is isotropic. -/
private theorem isStabilizer_widenL {L : Submodule (ZMod 2) (Pauli n)} (hstab : IsStabilizer L)
    (x : Pauli n) : IsStabilizer (widenL L x) := by
  intro p hp q hq
  obtain ⟨y, hy, hy0, a, rfl⟩ := mem_widenL_iff.mp hp
  obtain ⟨y', hy', hy0', b, rfl⟩ := mem_widenL_iff.mp hq
  simp only [omega_add_left, omega_add_right, omega_smul_left, omega_smul_right,
    hstab y hy y' hy', omega_comm y x, hy0, hy0', omega_self, mul_zero, add_zero]

/-- An element of `L` corrected by `z` commutes with `x`, when `ω(z, x) = 1`. -/
private theorem lift_mem_widenL {L : Submodule (ZMod 2) (Pauli n)} {x z : Pauli n} (hzL : z ∈ L)
    (hzx : omega z x = 1) {p : Pauli n} (hp : p ∈ L) : p + omega x p • z ∈ widenL L x := by
  refine mem_widenL_iff.mpr ⟨_, L.add_mem hp (L.smul_mem (omega x p) hzL), ?_, 0, by
    rw [zero_smul, add_zero]⟩
  rw [omega_add_right, omega_smul_right, omega_comm x z, hzx, mul_one]
  exact CharTwo.add_self_eq_zero _

/-- `widenL` of a co-isotropic subspace is co-isotropic, given `z ∈ L` with `ω(z, x) = 1`. -/
private theorem orthogonal_widenL_le {L : Submodule (ZMod 2) (Pauli n)}
    (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L) {x z : Pauli n} (hzL : z ∈ L)
    (hzx : omega z x = 1) :
    LinearMap.BilinForm.orthogonal omegaBilin (widenL L x) ≤ widenL L x := by
  intro q hq
  have hq' : ∀ p ∈ widenL L x, omega p q = 0 := fun p hp =>
    LinearMap.BilinForm.isOrtho_def.mp (LinearMap.BilinForm.mem_orthogonal_iff.mp hq p hp)
  have hxL : x ∈ widenL L x :=
    mem_widenL_iff.mpr ⟨0, L.zero_mem, omega_zero_right x, 1, by rw [zero_add, one_smul]⟩
  have hL : q + omega z q • x ∈ L := by
    refine horth ?_
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    rw [LinearMap.BilinForm.isOrtho_def]
    change omega p (q + omega z q • x) = 0
    have hpq := hq' _ (lift_mem_widenL hzL hzx hp)
    rw [omega_add_left, omega_smul_left] at hpq
    rw [omega_add_right, omega_smul_right, omega_comm p x]
    linear_combination hpq
  have hker : omega x (q + omega z q • x) = 0 := by
    rw [omega_add_right, omega_smul_right, omega_self, mul_zero, add_zero]
    exact hq' x hxL
  refine mem_widenL_iff.mpr ⟨_, hL, hker, omega z q, ?_⟩
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero (omega z q), zero_smul, add_zero]

/-- A word outside a subspace of the words is separated from it by a linear form, written as a
pairing with `σ`. -/
private theorem exists_dot_of_notMem {K : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {d : Fin n → ZMod 2} (hd : d ∉ K) :
    ∃ σ : Fin n → ZMod 2, (∀ v ∈ K, dotF2 σ v = 0) ∧ dotF2 σ d = 1 := by
  obtain ⟨f, hfd, hfK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hd inferInstance
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin n → ZMod 2, ∀ w, dotF2 σ w = f w := by
    refine ⟨fun j => f (fun k => if j = k then 1 else 0), fun w => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    unfold dotF2
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_eq_mul, mul_comm]
  refine ⟨σ, fun v hv => ?_, ?_⟩
  · have hmem : f v ∈ K.map f := Submodule.mem_map_of_mem hv
    rw [hfK, Submodule.mem_bot] at hmem
    rw [hσ, hmem]
  · rw [hσ]
    rcases zmod_two_eq_zero_or_one (f d) with h0 | h1
    · exact absurd h0 hfd
    · exact h1

/-- **The widened Lagrangian.** A Lagrangian `L` whose X-shadow misses the word `d` has a
widening `L'`, again a Lagrangian, whose X-shadow contains `d` and cut by one pairing `σ` is the
X-shadow of `L`. -/
private theorem exists_lagrangian_widening {L : Submodule (ZMod 2) (Pauli n)}
    (hstab : IsStabilizer L) (horth : LinearMap.BilinForm.orthogonal omegaBilin L ≤ L)
    {d : Fin n → ZMod 2} (hd : d ∉ Submodule.map xProj L) :
    ∃ (L' : Submodule (ZMod 2) (Pauli n)) (σ : Fin n → ZMod 2),
      IsStabilizer L' ∧ LinearMap.BilinForm.orthogonal omegaBilin L' ≤ L' ∧
      (∀ v, v ∈ Submodule.map xProj L ↔ v ∈ Submodule.map xProj L' ∧ dotF2 σ v = 0) ∧
      d ∈ Submodule.map xProj L' := by
  obtain ⟨σ, hσK, hσd⟩ := exists_dot_of_notMem hd
  have hσL : ∀ p ∈ L, dotF2 σ p.X = 0 := fun p hp => hσK _ (Submodule.mem_map_of_mem hp)
  obtain ⟨xd, hxdX⟩ : ∃ xd : Pauli n, xd.X = d := ⟨⟨d, 0⟩, rfl⟩
  have hzL : zPauli σ ∈ L := by
    refine horth ?_
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    rw [LinearMap.BilinForm.isOrtho_def]
    change omega p (zPauli σ) = 0
    rw [omega_comm, omega_zPauli]
    exact hσL p hp
  have hzx : omega (zPauli σ) xd = 1 := by
    rw [omega_zPauli, hxdX]
    exact hσd
  refine ⟨widenL L xd, σ, isStabilizer_widenL hstab xd, orthogonal_widenL_le horth hzL hzx,
    fun v => ⟨?_, ?_⟩, ?_⟩
  · intro hv
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨Submodule.mem_map.mpr ⟨_, lift_mem_widenL hzL hzx hp, ?_⟩, hσL p hp⟩
    change (p + omega xd p • zPauli σ).X = p.X
    rw [X_add, X_smul, zPauli_X, smul_zero, add_zero]
  · rintro ⟨hv, hσv⟩
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨y, hy, -, a, rfl⟩ := mem_widenL_iff.mp hq
    change dotF2 σ (y + a • xd).X = 0 at hσv
    rw [X_add, X_smul, hxdX, dotF2_add_right, dotF2_smul_right, hσd, mul_one, hσL y hy,
      zero_add] at hσv
    subst hσv
    refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
    change y.X = (y + (0 : ZMod 2) • xd).X
    rw [zero_smul, add_zero]
  · exact Submodule.mem_map.mpr ⟨xd, mem_widenL_iff.mpr ⟨0, L.zero_mem, omega_zero_right xd, 1,
      by rw [zero_add, one_smul]⟩, hxdX⟩

/-- Support membership as membership of `w − x₀` in the X-shadow. -/
private theorem mem_coset_iff {L : Submodule (ZMod 2) (Pauli n)} {x₀ w : Fin n → ZMod 2} :
    (∃ p ∈ L, w = x₀ + p.X) ↔ w - x₀ ∈ Submodule.map xProj L :=
  mem_support_iff (⟨0, 0, 0, 0, L, x₀⟩ : KernelSumState n) w

/-- In characteristic two the pairing with a difference is the sum of the pairings. -/
private theorem dotF2_sub_right_two (σ w x₀ : Fin n → ZMod 2) :
    dotF2 σ (w - x₀) = dotF2 σ x₀ + dotF2 σ w := by
  unfold dotF2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.sub_apply, mul_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring

/-- **A widening of the support by a collapse.** Over a carrier state `⟨m, h, Q, c, L, x₀⟩` whose
X-shadow is not every word there is a carrier state one bound bit higher, with scale `c/√2`, a
strictly larger X-shadow and the same offset: its last bound bit carries the constraint
`2^{m−1}·b·(σ·x₀ + σ·w)` that a collapse turns into the cut back to the support of the input, and
R4 restates the exponent. -/
theorem exists_widen {m h : ℕ} {Q : DiagPhase (n + h) m} {c : ℂ}
    {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2}
    (hS : IsCarrier (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n))
    (hK : Submodule.map xProj L ≠ ⊤) :
    ∃ (L' : Submodule (ZMod 2) (Pauli n)) (Q' : DiagPhase (n + (h + 1)) m),
      Submodule.map xProj L < Submodule.map xProj L' ∧
      IsCarrier (⟨m, h + 1, Q', c / (Real.sqrt 2 : ℂ), L', x₀⟩ : KernelSumState n) ∧
      Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m)
        ⟨m, h + 1, Q', c / (Real.sqrt 2 : ℂ), L', x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  have hm : 1 ≤ m := hS.1
  obtain ⟨d, hd⟩ : ∃ d, d ∉ Submodule.map xProj L := by
    by_contra hc
    exact hK (eq_top_iff.mpr fun v _ => by_contra fun hv => hc ⟨v, hv⟩)
  obtain ⟨L', σ, hstab', horth', hKK', hdK'⟩ := exists_lagrangian_widening hS.2.1 hS.2.2.1 hd
  obtain ⟨Q', hQ'0⟩ := exists_diagPhase_snoc (n := n) (m := m) (h := h)
    (fun w y b => if b = 0 then Q.eval (Fin.append w y) else Q.eval (Fin.append w y)
      + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((dotF2 σ x₀ + dotF2 σ w).val : ℕ) : ZMod (2 ^ m)))
  have hQ' : ∀ (w : Fin n → ZMod 2) (y : Fin h → ZMod 2) (b : ZMod 2),
      Q'.eval (Fin.snoc (Fin.append w y) b) = if b = 0 then Q.eval (Fin.append w y)
        else Q.eval (Fin.append w y)
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((dotF2 σ x₀ + dotF2 σ w).val : ℕ) : ZMod (2 ^ m)) :=
    hQ'0
  have hsign : SignAffine Q' L' x₀ σ (dotF2 σ x₀) := by
    intro w _ y
    rw [lastDiff_eval, hQ', hQ', if_neg (by decide : (1 : ZMod 2) ≠ 0), if_pos rfl,
      add_sub_cancel_left]
  have hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) ↔
      (∃ p ∈ L', w = x₀ + p.X) ∧ dotF2 σ x₀ + dotF2 σ w = 0 := by
    intro w
    rw [mem_coset_iff, mem_coset_iff, hKK', dotF2_sub_right_two]
  have hstep := CarrierRule.collapse hm Q' (c / (Real.sqrt 2 : ℂ)) L' x₀ σ (dotF2 σ x₀) hsign
    L x₀ hsupp
  have hscale : (Real.sqrt 2 : ℂ) * (c / (Real.sqrt 2 : ℂ)) = c := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ c ofReal_sqrt_two_ne_zero]
  have hmid : elimCollapse Q' (c / (Real.sqrt 2 : ℂ)) L x₀
      = (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n) := by
    unfold elimCollapse
    rw [hscale]
  rw [hmid] at hstep
  have hgauge : CarrierRule (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ :=
    CarrierRule.gauge (GaugeStep.congrSupport Q (snocFreeze 0 Q') c L x₀
      (fun w _ y => by rw [snocFreeze_eval, hQ', if_pos rfl]))
  have hmidC : IsCarrier (⟨m, h, snocFreeze 0 Q', c, L, x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hS (stateEq_of_carrierRule hgauge) hm hS.2.1 hS.2.2.1
  have htopC : IsCarrier (⟨m, h + 1, Q', c / (Real.sqrt 2 : ℂ), L', x₀⟩ : KernelSumState n) :=
    isCarrier_of_stateEq hmidC (stateEq_of_carrierRule hstep) hm hstab' horth'
  exact ⟨L', Q', SetLike.lt_iff_le_and_exists.mpr ⟨fun v hv => ((hKK' v).mp hv).1, d, hdK', hd⟩,
    htopC, Relation.EqvGen.trans _ _ _
      (eqvGen_carrierRuleWithin_of_carrierRule hstep htopC rfl hmidC rfl)
      (eqvGen_carrierRuleWithin_of_carrierRule hgauge hmidC rfl hS rfl)⟩

end Constructions

end FTQCLib.Frame.Walkthrough

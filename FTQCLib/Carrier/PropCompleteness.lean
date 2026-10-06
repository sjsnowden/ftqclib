/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FrameCategory
import FTQCLib.Carrier.RewriteCompleteness

/-!
# Completeness of the frame's equational theory as a PROP

The statement of T47 (`docs/TARGETS.md`; `docs/fidelity/T47.md`). It is T07 (`rewrite_complete`,
`rewrite_conservative`, `RewriteCompleteness.lean`) read on the hom-sets of T46's PROP
(`FrameCategory.lean`), and nothing more. A morphism `a → b` is a `StateEq` class of
`KernelSumState (a.bits + b.bits)` (`FrameCategory.Hom`), and two presentations `F` and `G` give one
morphism exactly when they are `StateEq` (`toHom_eq_toHom_iff`). A class has no scale and no
precision, so the scale ratio is of the two presentations, `G.c / F.c`, and the hypotheses are on
presentations.

* **Nonzero.** `prop_complete` asks only that `F`'s amplitude be nonzero, that is, that the morphism
  is not the zero class. This is wider than T07's `IsCarrier`, which also asks for precision at
  least `1` and a Lagrangian; the wider hypothesis reaches T07 through two gauge steps that keep the
  scale, R3 (`GaugeStep.congrXProj`, the Lagrangian replaced by one with the same X-shadow) and R7
  (`GaugeStep.liftTo`, the precision lifted to `max 1 F.m`), the construction of
  `exists_carrier_of_amp_ne_zero` (fidelity note, Claim 1). `G`'s amplitude is then nonzero on
  either side of the equivalence, so it is not a hypothesis. The zero class is outside the
  statement, as T07 and decision D10 leave it.
* **Dyadic ratio.** `IsDyadicRatio (G.c / F.c)`, a root of unity of order a power of two times an
  integer power of `√2`, exactly as in T07. It cannot be dropped: decision D9's pair, `Q = y₀y₁y₂`
  at `c = 1`, `m = 1`, against the height-zero state at `c = 3/√2` on no bits, is one morphism
  `⟨0⟩ → ⟨0⟩` with two presentations no chain relates.
* **Every precision.** No condition on `F.m` or `G.m`, and none on the states of a chain between
  them, which may pass through other precisions and through states that are not carrier states.
* **Conservatively.** `prop_conservative`: two carrier presentations of one morphism at one
  precision `m`, with a dyadic ratio, are related by a chain every state of which is a carrier state
  at precision `m` (`CarrierRuleWithin`). This needs carrier presentations: the first R3 or R7 step
  out of a presentation that is not a carrier state leaves the predicate (fidelity note, Claim 2).

**Which reading of "as a PROP".** Completeness is stated per hom-set, for every pair of objects: on
each hom-set `a → b`, equality of morphisms is exactly the equivalence `CarrierRule` generates on
presentations, under the dyadic hypothesis. It is not claimed that presentations modulo
`Relation.EqvGen CarrierRule` form a PROP under `compState`: composition reads its factors only
through their amplitudes and picks a carrier presentation of each by `Classical.choose`
(`carrierRep`), so the composite's scale is not tied to the factors' scales (fidelity note,
Claim 2). `CarrierRule` rewrites whole presentations, not subterms in a context.

## Cross-checks, not hypotheses

Each of the following is a completeness theorem of the same "equal interpretations iff equal by the
rules" shape for one fragment, and T47 at the matching precision must agree with it. None is proved
here, none is a hypothesis of any declaration, and nothing here depends on them. A carrier state at
precision `m` has phases `2^m`-th roots of unity and scale `c / √2^h`, so the level `n` of a
sum-over-paths term `SOP[1/2^n]` is precision `m = n`, and the named fragments are the frame's
precision-`m` sub-PROPs: the classes with a carrier presentation at precision at most `m`, scales in
the dyadic class of `1`, and the zero class, which T46's identity, symmetry, tensor and composition
keep.

* `m = 3`: the `π/4` (Clifford+T) fragment of the ZX-calculus, complete (Jeandel, Perdrix and
  Vilmart, arXiv:1705.11151, Theorem 1), representing exactly the matrices over `ℤ[1/2][e^{iπ/4}]`,
  the precision-`3` amplitudes at a scale dyadic to `1` (their Proposition 10).
* `m = 1`: the phase-free ZH-calculus, complete and universal for matrices over `ℤ[1/√2]`
  (van de Wetering and Wolffs, arXiv:1904.07545), the Toffoli–Hadamard fragment, H + CCZ. The
  ZH-calculus of Backens et al. (arXiv:2103.06610), complete over `ℤ[1/2]`, has no odd power of
  `√2` and is a sub-case of `m = 1`, narrower in its scalars; both are meant.
* SOP: Vilmart's completeness of `SOP[1/2]` under the rules TH (arXiv:2205.02600), the case
  `m = 1`, and his corollary for the whole dyadic fragment under TH with the rule `(√2)`, which is a
  cross-check at every precision, `m = 1` and `m = 3` among them. Two terms at one level have a
  dyadic scale ratio in D9's sense, so D9's gap does not arise between them.
* Comfort's presentations of the props of linear and affine relations (arXiv:2105.06244, Theorem 17
  of the affine part) are completeness results for supports: read on a carrier state, they check
  its Lagrangian and offset, not its amplitude.

Everything here is frame-pure (decision D5). No `FTQCLib.Hilbert` module is imported.

## Main results

* `FrameCategory.prop_complete` — two presentations of morphisms `a → b`, the first nonzero, with a
  dyadic scale ratio, give one morphism exactly when `Relation.EqvGen CarrierRule` relates them, at
  every precision (T47.3).
* `FrameCategory.prop_conservative` — two carrier presentations at precision `m` of one morphism,
  with a dyadic scale ratio, are related by a chain of carrier states at precision `m` (T47.3).
-/

namespace FTQCLib.Frame.Walkthrough

namespace FrameCategory

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

/-! ### Moving a nonzero presentation to a carrier state by R3 and R7

The construction of `exists_carrier_of_amp_ne_zero` (`FrameCategory.lean`), taken here as a chain
of `CarrierRule` steps that keeps the scale. The Lagrangian with a given X-shadow and its three
lemmas are public there (`shadowLagrangian`, entry 2026-10-02c). -/

-- source: papers/categorical_qm/
-- Comfort_2021_graphical_calculus_lagrangian_relations_2105.06244 definition:h7963d1a59afa
/-- **A nonzero presentation is related to a carrier state with its scale.** R3
(`GaugeStep.congrXProj`) replaces the Lagrangian by `shadowLagrangian` of its X-shadow, and R7
(`GaugeStep.liftTo`, read backwards) lifts the precision to `max 1 m`; neither step changes the
scale. -/
private theorem exists_carrier_eqvGen {N : ℕ} (S : KernelSumState N) (hS : amp S ≠ 0) :
    ∃ T : KernelSumState N, IsCarrier T ∧ T.c = S.c ∧ Relation.EqvGen CarrierRule S T := by
  obtain ⟨m, h, Q, c, L, x₀⟩ := S
  set L' := shadowLagrangian (Submodule.map xProj L) with hL'
  have hsh : Submodule.map xProj L = Submodule.map xProj L' :=
    (map_xProj_shadowLagrangian _).symm
  have h3 : CarrierRule (⟨m, h, Q, c, L, x₀⟩ : KernelSumState N) ⟨m, h, Q, c, L', x₀⟩ :=
    CarrierRule.gauge (GaugeStep.congrXProj Q c L L' x₀ hsh)
  have h7 : CarrierRule
      (⟨max 1 m, h, FTQCLib.Hilbert.liftTo (max 1 m) (le_max_right 1 m) Q, c, L', x₀⟩ :
        KernelSumState N) ⟨m, h, Q, c, L', x₀⟩ :=
    CarrierRule.gauge (GaugeStep.liftTo (max 1 m) (le_max_right 1 m) Q c L' x₀)
  have hamp : StateEq (⟨m, h, Q, c, L, x₀⟩ : KernelSumState N)
      ⟨max 1 m, h, FTQCLib.Hilbert.liftTo (max 1 m) (le_max_right 1 m) Q, c, L', x₀⟩ :=
    (stateEq_of_carrierRule h3).trans (stateEq_of_carrierRule h7).symm
  refine ⟨⟨max 1 m, h, FTQCLib.Hilbert.liftTo (max 1 m) (le_max_right 1 m) Q, c, L', x₀⟩,
    ⟨le_max_left 1 m, isStabilizer_shadowLagrangian _, orthogonal_shadowLagrangian_le _, ?_⟩, rfl,
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h3)
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h7))⟩
  have hamp' : amp (⟨m, h, Q, c, L, x₀⟩ : KernelSumState N)
      = amp (⟨max 1 m, h, FTQCLib.Hilbert.liftTo (max 1 m) (le_max_right 1 m) Q, c, L', x₀⟩ :
        KernelSumState N) := hamp
  rw [← hamp']
  exact hS

/-- **Soundness on chains.** A chain of `CarrierRule` steps, each taken either way, keeps the
amplitude (`stateEq_of_carrierRule`). -/
private theorem stateEq_of_eqvGen {N : ℕ} {S T : KernelSumState N}
    (hST : Relation.EqvGen CarrierRule S T) : StateEq S T := by
  induction hST with
  | rel _ _ h => exact stateEq_of_carrierRule h
  | refl _ => exact StateEq.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

-- source: papers/categorical_qm/
-- jeandel_perdrix_vilmart_1705.11151_zx_clifford_t_complete theorem:thm:main
-- source: papers/categorical_qm/
-- Comfort_2021_graphical_calculus_lagrangian_relations_2105.06244 theorem:h9dc58962670c
/-- **Completeness as a PROP.** On every hom-set `a → b` of T46's PROP, two presentations `F` and
`G`, `F`'s amplitude nonzero and the ratio `G.c / F.c` of their scales dyadic (decision D9), give
one morphism exactly when T07's rules relate them, at any precisions. It is `rewrite_complete` on
representatives: the "if" half is soundness, each step keeping the amplitude
(`stateEq_of_carrierRule`); the "only if" half moves each presentation to a carrier state with the
same scale by R3 and R7, as `exists_carrier_of_amp_ne_zero` does, and applies `rewrite_complete`.
The cited completeness theorems are cross-checks at `m = 3` and on supports (module docstring), not
hypotheses. Proved at T47.3. -/
theorem prop_complete {a b : Obj} {F G : KernelSumState (a.bits + b.bits)} (hF : amp F ≠ 0)
    (hc : IsDyadicRatio (G.c / F.c)) :
    toHom F = toHom G ↔ Relation.EqvGen CarrierRule F G := by
  rw [toHom_eq_toHom_iff]
  constructor
  · intro hFG
    have hG : amp G ≠ 0 := by
      have hFG' : amp F = amp G := hFG
      rw [← hFG']
      exact hF
    obtain ⟨F', hF', hcF, hchF⟩ := exists_carrier_eqvGen F hF
    obtain ⟨G', hG', hcG, hchG⟩ := exists_carrier_eqvGen G hG
    have hs : StateEq F' G' :=
      ((stateEq_of_eqvGen hchF).symm.trans hFG).trans (stateEq_of_eqvGen hchG)
    have hd : IsDyadicRatio (G'.c / F'.c) := by
      rw [hcF, hcG]
      exact hc
    have hch := (rewrite_complete hF' hG').2 ⟨hs, hd⟩
    exact Relation.EqvGen.trans _ _ _ hchF
      (Relation.EqvGen.trans _ _ _ hch (Relation.EqvGen.symm _ _ hchG))
  · exact stateEq_of_eqvGen

/-- **Conservativity as a PROP.** Two carrier presentations at precision `m` of one morphism
`a → b`, with a dyadic ratio of scales, are related by a chain every step of which is between
carrier states at precision `m`: the equational theory of the precision-`m` sub-PROP is
self-contained, H + CCZ at `m = 1` and Clifford+T at `m = 3`. It is `prop_complete` followed by
`rewrite_conservative`. Proved at T47.3. -/
theorem prop_conservative {a b : Obj} {m : ℕ} {F G : KernelSumState (a.bits + b.bits)}
    (hF : IsCarrier F) (hG : IsCarrier G) (hFm : F.m = m) (hGm : G.m = m)
    (hc : IsDyadicRatio (G.c / F.c)) (hFG : toHom F = toHom G) :
    Relation.EqvGen (CarrierRuleWithin fun A => IsCarrier A ∧ A.m = m) F G := by
  have hch := (prop_complete hF.2.2.2 hc).1 hFG
  exact rewrite_conservative hF hG hFm hGm hch

end FrameCategory

end FTQCLib.Frame.Walkthrough

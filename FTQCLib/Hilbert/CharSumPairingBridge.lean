/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CharSumPairing
import FTQCLib.Hilbert.Inner

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! # The canonical isometry bridge: the native Gauss-sum pairing IS the `QState` ℓ² geometry

The **separable Hilbert-side certificate** for Appendage G. The frame-native Gauss-sum pairing
(`FTQCLib/Examples/CharSumPairing.lean`, frame-pure) is reconstructed from the frame's own character data; this
file states the one bridge that makes the bundled operator / spectral API borrowable on demand: the raw
amplitude embedding `embed S = toQState (ampFun S)` into `QState n = EuclideanSpace ℂ (Fin n → ZMod 2)`
carries the native norm, pairing, and distance to the `QState` ones, on the nose.

`carrierDist_eq_dist` is the unifying statement — the native metric on the character-sum carrier IS the
pullback of the `QState` ℓ² metric along `embed`. So the native pairing (G), the Hilbert operator-norm route
(`FTQCLib/Hilbert/RzApproxOperator.lean`: `qDiagCLM`/`qHadamardCLM` intertwine through `embed`), and the
support-restricted correspondence `F` (`FTQCLib/Hilbert/CharSumCorrespondence.lean`, which equals `embed` only
*on support*) all become facts about the single object `embed S`.

**Frame-purity is preserved:** the dependency is one-way (this file imports `CharSumPairing`, not the
reverse); `CharSumPairing.lean` imports no `FTQCLib.Hilbert`. The embedding targets the **raw** amplitude, not
`F`: routing the pairing through the support-restricted `F` would silently demand off-support vanishing of a
raw Gauss sum, so the exact identities live on `embed`. `embed` is a genuine isometry onto its image, but
NOT a bundled `LinearIsometryEquiv` on the carrier — `KernelSumState` is a bare structure, `embed` is not
linear, and `toQState` is sup-norm→ℓ² — so the bundle is delivered as the three identities below. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hilbert Complex

variable {n : ℕ}

/-- The raw amplitude function of a carrier state (the domain of `toQState`). -/
noncomputable def ampFun (S : KernelSumState n) : QubitSpace n :=
  fun w => ampCore S.m S.h S.Q S.c w

/-- **The canonical embedding of a carrier state into the `QState` ℓ² space** — the raw amplitude, viewed
in `EuclideanSpace ℂ (Fin n → ZMod 2)`. Not `F` (which is support-restricted); this is the all-`w` map. -/
noncomputable def embed (S : KernelSumState n) : QState n := toQState (ampFun S)

@[simp] theorem embed_apply (S : KernelSumState n) (w : Fin n → ZMod 2) :
    embed S w = ampCore S.m S.h S.Q S.c w := rfl

/-- **The native norm IS the `QState` norm.** `carrierNormSq S = ‖embed S‖²`. -/
theorem carrierNormSq_eq_normSq (S : KernelSumState n) : carrierNormSq S = ‖embed S‖ ^ 2 := by
  rw [carrierNormSq, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun w _ => sq_nonneg _)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [embed_apply, Complex.normSq_eq_norm_sq]

/-- **The native pairing IS the `QState` inner product.** `carrierInner S T = ⟪embed S, embed T⟫`. -/
theorem carrierInner_eq_inner (S T : KernelSumState n) :
    carrierInner S T = inner ℂ (embed S) (embed T) := by
  rw [carrierInner, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [embed_apply, embed_apply, RCLike.inner_apply]; ring

/-- **The native metric IS the `QState` metric.** `carrierDist S T = dist (embed S) (embed T)` — the
unifying statement: the whole native ℓ² development is the pullback of the `QState` geometry along `embed`. -/
theorem carrierDist_eq_dist (S T : KernelSumState n) :
    carrierDist S T = dist (embed S) (embed T) := by
  rw [carrierDist, carrierDistSq, dist_eq_norm, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [PiLp.sub_apply, embed_apply, embed_apply, Complex.normSq_eq_norm_sq]

end FTQCLib.Frame.Walkthrough

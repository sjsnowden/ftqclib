/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Scheme.DelsarteBridge
import Mathlib.Data.ZMod.Basic

/-!
# Regression checks for the H-free class-map inequality and the Delsarte bridge

Kernel rows are taken on the PRIMAL side only (`AddChar` instances are
classical — nothing indexed by characters or dual shells is `decide`-reachable): class
counts, inner counts, and the `pairCount` agreement at a concrete binary code. The
character-side content is accepted by the build-failing axiom sweep below and by the
defeq tripwire in `DelsarteBridge.lean`.

Sensitivity: replacing the class map by `hammingNorm + 1` breaks the bridge proof, and a
wrong class count is refuted by `decide`.
-/

namespace ECCLib.Scheme

open Finset ECCLib.Delsarte

/-- The binary repetition code of length 2: `{00, 11}`. -/
def rep2 : Finset (Fin 2 → ZMod 2) := {![0, 0], ![1, 1]}

/-- Two ordered pairs at difference weight 0 (the diagonal) … -/
example : classCount rep2 hammingNorm 0 = 2 := by decide
/-- … none at weight 1 … -/
example : classCount rep2 hammingNorm 1 = 0 := by decide
/-- … and two at weight 2. -/
example : classCount rep2 hammingNorm 2 = 2 := by decide
/-- The inner distribution at the difference `11`. -/
example : innerCount rep2 ![1, 1] = 2 := by decide
/-- Agreement with the Delsarte layer's `pairCount` at the concrete code (the general
statement is `classCount_hammingNorm`). -/
example : classCount rep2 hammingNorm 2 = pairCount rep2 2 := by decide
/-- A discriminating row: the wrong count is refuted. -/
example : ¬ (classCount rep2 hammingNorm 2 = 3) := by decide

end ECCLib.Scheme

/-! ## Axiom sweep (build-failing) -/

/-- info: 'ECCLib.Scheme.scheme_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.scheme_spectral

/-- info: 'ECCLib.Scheme.class_delsarte_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.class_delsarte_nonneg

/-- info: 'ECCLib.Scheme.qEnt_shellSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.qEnt_shellSet

/-- info: 'ECCLib.Scheme.bridge_delsarte_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.bridge_delsarte_nonneg

/-- info: 'ECCLib.Scheme.card_shellSet' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms ECCLib.Scheme.card_shellSet

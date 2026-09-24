/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.MacWilliams

/-!
# Verification harness — is the size-relation cross-check genuinely independent?

**Not part of the mathematical library.** The root `ECCLib.lean` does not import this file;
it builds only when named explicitly (`lake build ECCLib.VerifyIndependence`).

`macwilliams_one` is intended as a cross-check: it reaches
`|C^⊥|·|C| = q^n` *through* the MacWilliams identity, i.e. through the DFT, while
`card_dualCode_mul_card` reaches the same number by another route. That is only a real check if the
two routes do not share a layer — a convention error in the Fourier engine would otherwise break
both identically, which is exactly what the cross-check exists to catch.

This file checks that mechanically rather than asserting it: it walks the transitive constant
dependencies of each theorem and reports those whose **names match a hand-maintained substring
list** (`fourierLayer` below). That is weaker than "belongs to the Fourier layer" — a Fourier-layer
constant whose name matches none of the patterns would be missed silently. Read a "none" result as
*no dependency with a Fourier-shaped name*, which is strong evidence but not a proof; computing the
layer by defining module would make the claim exact. Expected output —
`card_dualCode_mul_card`, `finrank_dualCode_add_finrank` and `dualCode_dualCode` report **none**;
`macwilliams_one` reports many, including `fourierOp_indicator`.

Maintenance note: this is metaprogramming against the `Lean.Environment` API and is the most likely
thing in the library to break on a toolchain bump. If it does, the fix is to this file, not to the
mathematics.
-/

open Lean

/-- All constants transitively used by `n` (type and value). -/
partial def transDeps (env : Environment) (n : Name) : NameSet :=
  go n {}
where
  go (c : Name) (seen : NameSet) : NameSet :=
    if seen.contains c then seen
    else
      let seen := seen.insert c
      match env.find? c with
      | none => seen
      | some info =>
        let used := info.type.getUsedConstants ++
          (match info.value? with | some v => v.getUsedConstants | none => #[])
        used.foldl (fun s d => go d s) seen

def fourierLayer : List String :=
  ["fourierOp", "fourierMap", "fourierT", "charAnnih", "pairingChar",
   "Poisson", "poisson", "AddChar", "quadGaussSum", "gaussSum"]

def report (env : Environment) (tgt : Name) : IO Unit := do
  let deps := transDeps env tgt
  let mut hits : Array Name := #[]
  for d in deps.toList do
    for pat in fourierLayer do
      if (d.toString.splitOn pat).length > 1 then
        hits := hits.push d
        break
  IO.println s!"--- {tgt}"
  IO.println s!"    total transitive constants: {deps.toList.length}"
  if hits.isEmpty then
    IO.println "    FOURIER-LAYER DEPENDENCIES: none"
  else
    IO.println s!"    FOURIER-LAYER DEPENDENCIES: {hits.size}"
    for h in hits[0:12] do IO.println s!"      {h}"

run_cmd do
  let env ← Lean.getEnv
  report env `ECCLib.Coding.card_dualCode_mul_card
  report env `ECCLib.Coding.finrank_dualCode_add_finrank
  report env `ECCLib.Coding.dualCode_dualCode
  report env `ECCLib.Coding.macwilliams_one

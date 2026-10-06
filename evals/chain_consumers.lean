import FTQCLib.CSS.Decoder.ToricX
import FTQCLib.CSS.Decoder.ToricZ
import FTQCLib.CSS.Decoder.PlanarX
import FTQCLib.CSS.Decoder.PlanarZ
import Lean

/-!
# Decoder-bridge integrated consumers

The owner compiles this protected module only after all nine decoder-bridge nodes have accepted
certificates. The imported artifacts must be precisely those certificate versions. These rows
instantiate existing accepted theorems; they do not re-prove the decoder obligations.

For both surfaces and both error types, the distance-three row exercises correction of any
weight-at-most-one error under an arbitrary coset-leader decoder. The distance-one row exercises
the degenerate geometry at its permitted zero radius. The explicit crossed check/boundary types
are consumer expectations independent of a worker's chosen proof.

The final examination requires all nine theorem declarations and sweeps their transitive axioms
as well as the consumers' axioms. Import dependencies alone do not claim proof-term dependencies.
-/

namespace Ontologic.ChainConsumers

open Matrix FTQCLib.CSS

/-- Consumer agreement at L=3, t=1 for toric X errors. -/
theorem toricX_three :
    ∀ decoder : (Fin (3 * 3) → ZMod 2) → Fin (2 * (3 * 3)) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (toricCode 3).2.mulVecLin decoder →
      ∀ error : Fin (2 * (3 * 3)) → ZMod 2, hammingNorm error ≤ 1 →
        CorrectsUpToBoundary (toricCode 3).2 (toricCode 3).1ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_toricX_corrects 3 inferInstance decoder hdec 1
      (by decide)

/-- Consumer agreement at L=1, t=0 for toric X errors. -/
theorem toricX_one :
    ∀ decoder : (Fin (1 * 1) → ZMod 2) → Fin (2 * (1 * 1)) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (toricCode 1).2.mulVecLin decoder →
      ∀ error : Fin (2 * (1 * 1)) → ZMod 2, hammingNorm error ≤ 0 →
        CorrectsUpToBoundary (toricCode 1).2 (toricCode 1).1ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_toricX_corrects 1 inferInstance decoder hdec 0
      (by decide)

/-- Consumer agreement at L=3, t=1 for toric Z errors. -/
theorem toricZ_three :
    ∀ decoder : (Fin (3 * 3) → ZMod 2) → Fin (2 * (3 * 3)) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (toricCode 3).1.mulVecLin decoder →
      ∀ error : Fin (2 * (3 * 3)) → ZMod 2, hammingNorm error ≤ 1 →
        CorrectsUpToBoundary (toricCode 3).1 (toricCode 3).2ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_toricZ_corrects 3 inferInstance decoder hdec 1
      (by decide)

/-- Consumer agreement at L=1, t=0 for toric Z errors. -/
theorem toricZ_one :
    ∀ decoder : (Fin (1 * 1) → ZMod 2) → Fin (2 * (1 * 1)) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (toricCode 1).1.mulVecLin decoder →
      ∀ error : Fin (2 * (1 * 1)) → ZMod 2, hammingNorm error ≤ 0 →
        CorrectsUpToBoundary (toricCode 1).1 (toricCode 1).2ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_toricZ_corrects 1 inferInstance decoder hdec 0
      (by decide)

/-- Consumer agreement at L=3, t=1 for planar X errors. -/
theorem planarX_three :
    ∀ decoder : (Fin ((planarComplex 3).cells 2) → ZMod 2) → Fin ((planarComplex 3).cells 1) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (planarCode 3).2.mulVecLin decoder →
      ∀ error : Fin ((planarComplex 3).cells 1) → ZMod 2, hammingNorm error ≤ 1 →
        CorrectsUpToBoundary (planarCode 3).2 (planarCode 3).1ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_planarX_corrects 3 inferInstance decoder hdec 1
      (by decide)

/-- Consumer agreement at L=1, t=0 for planar X errors. -/
theorem planarX_one :
    ∀ decoder : (Fin ((planarComplex 1).cells 2) → ZMod 2) → Fin ((planarComplex 1).cells 1) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (planarCode 1).2.mulVecLin decoder →
      ∀ error : Fin ((planarComplex 1).cells 1) → ZMod 2, hammingNorm error ≤ 0 →
        CorrectsUpToBoundary (planarCode 1).2 (planarCode 1).1ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_planarX_corrects 1 inferInstance decoder hdec 0
      (by decide)

/-- Consumer agreement at L=3, t=1 for planar Z errors. -/
theorem planarZ_three :
    ∀ decoder : (Fin ((planarComplex 3).cellsBelow 1) → ZMod 2) → Fin ((planarComplex 3).cells 1) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (planarCode 3).1.mulVecLin decoder →
      ∀ error : Fin ((planarComplex 3).cells 1) → ZMod 2, hammingNorm error ≤ 1 →
        CorrectsUpToBoundary (planarCode 3).1 (planarCode 3).2ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_planarZ_corrects 3 inferInstance decoder hdec 1
      (by decide)

/-- Consumer agreement at L=1, t=0 for planar Z errors. -/
theorem planarZ_one :
    ∀ decoder : (Fin ((planarComplex 1).cellsBelow 1) → ZMod 2) → Fin ((planarComplex 1).cells 1) → ZMod 2,
      ECCLib.Coding.IsCosetLeaderMap (planarCode 1).1.mulVecLin decoder →
      ∀ error : Fin ((planarComplex 1).cells 1) → ZMod 2, hammingNorm error ≤ 0 →
        CorrectsUpToBoundary (planarCode 1).1 (planarCode 1).2ᵀ decoder error :=
  fun decoder hdec =>
    @Decoder.cosetLeader_planarZ_corrects 1 inferInstance decoder hdec 0
      (by decide)

-- The owner acceptance gate is external; this check additionally refuses absent imported results.
run_cmd do
  let environment ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let mut pending := [`FTQCLib.CSS.Decoder.cosetLeader_residual_syndrome_zero,
    `FTQCLib.CSS.Decoder.cosetLeader_residual_weight_le,
    `FTQCLib.CSS.Decoder.cosetLeader_correctsUpToBoundary,
    `FTQCLib.CSS.Decoder.cosetLeader_cssX_corrects,
    `FTQCLib.CSS.Decoder.cosetLeader_cssZ_corrects,
    `FTQCLib.CSS.Decoder.cosetLeader_toricX_corrects,
    `FTQCLib.CSS.Decoder.cosetLeader_toricZ_corrects,
    `FTQCLib.CSS.Decoder.cosetLeader_planarX_corrects,
    `FTQCLib.CSS.Decoder.cosetLeader_planarZ_corrects,
    `Ontologic.ChainConsumers.toricX_three,
    `Ontologic.ChainConsumers.toricX_one,
    `Ontologic.ChainConsumers.toricZ_three,
    `Ontologic.ChainConsumers.toricZ_one,
    `Ontologic.ChainConsumers.planarX_three,
    `Ontologic.ChainConsumers.planarX_one,
    `Ontologic.ChainConsumers.planarZ_three,
    `Ontologic.ChainConsumers.planarZ_one]
  let mut seen : Lean.NameSet := {}
  let mut queued : Lean.NameSet := pending.foldl (fun names name => names.insert name) {}
  for name in pending do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required decoder theorem or consumer missing: {name}"
  for _ in [0:200000] do
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if !seen.contains name then
        seen := seen.insert name
        match environment.find? name with
        | none => throwError "Missing dependency {name}"
        | some info =>
          match info with
          | .axiomInfo _ =>
            if !permitted.contains name then
              throwError "Unapproved transitive axiom {name}"
          | _ => pure ()
          let dependencies := info.type.getUsedConstants.toList ++
            (match info.value? with | some value => value.getUsedConstants.toList | none => [])
          for dependency in dependencies do
            if !queued.contains dependency then
              queued := queued.insert dependency
              pending := dependency :: pending
  if !pending.isEmpty then
    throwError "Integrated consumer axiom examination exceeded bound"

end Ontologic.ChainConsumers

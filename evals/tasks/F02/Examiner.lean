import FTQCLib.Carrier.ResidualBit
import FTQCLib.Carrier.HadamardAmplitudeCheck
import Lean

/-! Protected composed import and consumer checks for the minimal historical signOf reversal.
The two real consumer modules must share one theorem declaration in this environment. -/

open Lean FTQCLib.Frame.Walkthrough

-- Lean 4.29.1 intentionally merges equal theorem types across imports, ignoring their proofs.
-- Audit each imported module's raw declaration names, before the merged environment loses the sites.
run_cmd do
  let environment ← Lean.getEnv
  let header := environment.header
  let moduleNames := header.moduleNames
  if header.moduleData.size != moduleNames.size then
    throwError "F02 declaration home: incomplete imported module data"
  if header.moduleData.size > 10000 then
    throwError "F02 declaration home: imported module count exceeds the examiner bound"
  for target in [`FTQCLib.Frame.Walkthrough.signOf_zero, `FTQCLib.Frame.Walkthrough.signOf_one] do
    let mut sites : Array Name := #[]
    for index in [0:header.moduleData.size] do
      let data := header.moduleData[index]!
      for name in data.constNames do
        if name == target then
          sites := sites.push moduleNames[index]!
    if sites != #[`FTQCLib.Carrier.CharSumPairing] then
      throwError "F02 declaration home: {target} must occur exactly once in FTQCLib.Carrier.CharSumPairing; observed {sites}"

run_cmd do
  let environment ← Lean.getEnv
  for name in [`FTQCLib.Frame.Walkthrough.signOf_zero, `FTQCLib.Frame.Walkthrough.signOf_one] do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "F02 requires theorem {name}"

example : signOf 0 = 1 := signOf_zero
example : signOf (1 : ZMod 2) = -1 := signOf_one

run_cmd Lean.Elab.Command.liftTermElabM do
  let expectedZero ← Lean.Elab.Term.elabType (← `(signOf (0 : ZMod 2) = (1 : ℂ)))
  let expectedOne ← Lean.Elab.Term.elabType (← `(signOf (1 : ZMod 2) = (-1 : ℂ)))
  for (name, expected) in [(`FTQCLib.Frame.Walkthrough.signOf_zero, expectedZero),
      (`FTQCLib.Frame.Walkthrough.signOf_one, expectedOne)] do
    let info ← getConstInfo name
    unless ← Lean.Meta.isDefEq info.type expected do
      throwError "F02 declaration {name} differs from its protected expected type"

-- Agreement follows directly from the protected definition, independently of the repaired lemmas.
example : signOf (0 : ZMod 2) = (1 : ℂ) := if_pos rfl
example : signOf (1 : ZMod 2) = (-1 : ℂ) := if_neg one_ne_zero

#check FTQCLib.Frame.Walkthrough.walsh_ofKernelState_pair
#check FTQCLib.Frame.Walkthrough.not_exists_kernelState_walsh_of_residual
#check FTQCLib.Frame.Walkthrough.walsh_amp_bellState_oneone

-- A separate bounded transitive walk accepts conventional axioms without prescribing their order.
run_cmd do
  let environment ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let mut pending := [`FTQCLib.Frame.Walkthrough.signOf_zero, `FTQCLib.Frame.Walkthrough.signOf_one,
    `FTQCLib.Frame.Walkthrough.walsh_ofKernelState_pair,
    `FTQCLib.Frame.Walkthrough.not_exists_kernelState_walsh_of_residual,
    `FTQCLib.Frame.Walkthrough.walsh_amp_bellState_oneone]
  let mut seen : Lean.NameSet := {}
  let mut queued : Lean.NameSet := pending.foldl (fun names name => names.insert name) {}
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
    throwError "F02 dependency examination exceeded its declared bound"

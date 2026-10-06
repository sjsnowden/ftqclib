import FTQCLib.Stabilizer.ZShearCheck
import Lean

/-! Protected F01 declaration, exact-type, transitive-axiom and named-consumer checks.
This file is supplied by the owner after capture and is never a worker input. -/

open Lean FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer

run_cmd do
  let environment ← Lean.getEnv
  match environment.find? `FTQCLib.Stabilizer.zShearBy_zShearBy with
  | some (.thmInfo _) => pure ()
  | _ => throwError "F01 requires the original theorem declaration"

example : ∀ {n : ℕ} (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n),
    zShearBy M (zShearBy M p) = p := @zShearBy_zShearBy

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← getConstInfo `FTQCLib.Stabilizer.zShearBy_zShearBy
  let expected ← Lean.Elab.Term.elabType (← `(∀ {n : ℕ}
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n),
    zShearBy M (zShearBy M p) = p))
  unless ← Lean.Meta.isDefEq info.type expected do
    throwError "F01 declaration type differs from the protected expected type"

-- These consumers test that the repaired general theorem remains connected to the original API.
example {n : ℕ} (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (p : Pauli n) :
    zShearByEquiv M (zShearByEquiv M p) = p := zShearBy_zShearBy M p

example : ∀ p : Pauli 2, zShear 0 (Pi.single 1 1) (zShear 0 (Pi.single 1 1) p) = p :=
  zShear_zShear_two

example : zShear 0 (Pi.single 0 1) (paulix 0 + pauliz 0 : Pauli 1) = paulix 0 :=
  zShear_Y_eq_X

-- A subset policy permits proofs using fewer conventional axioms, in any order.
run_cmd do
  let environment ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let mut pending := [`FTQCLib.Stabilizer.zShearBy_zShearBy, `FTQCLib.Stabilizer.zShearByEquiv,
    `FTQCLib.Stabilizer.zShear_zShear_two, `FTQCLib.Stabilizer.zShear_Y_eq_X]
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
    throwError "F01 dependency examination exceeded its declared bound"

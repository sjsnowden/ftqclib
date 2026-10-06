import ECCLib.Decoding
import FTQCLib.CSS.SurfaceCode
import Lean

/-!
# Independent decoder-bridge controls

These finite rows discriminate the intended hypotheses without using any new bridge theorem. The
parity row [1,1] has the two cycles 00 and 11, so its nonzero-cycle minimum is 2. With boundary zero,
the two weight-one errors have the same syndrome but different logical classes: equality 2t = d
does not suffice. With boundary column [1,1], their difference is harmless although they differ.
The assertions below are certificates for these concrete objects alone, not general bridge results.
-/

namespace Ontologic.ChainControls

open Matrix ECCLib.Coding FTQCLib.CSS

def first : Fin 2 → ZMod 2 := ![1, 0]
def second : Fin 2 → ZMod 2 := ![0, 1]
def cycle : Fin 2 → ZMod 2 := ![1, 1]
def parity : Matrix (Fin 1) (Fin 2) (ZMod 2) := fun _ => ![1, 1]
def zeroBoundary : Matrix (Fin 2) (Fin 1) (ZMod 2) := 0
def stabilizerBoundary : Matrix (Fin 2) (Fin 1) (ZMod 2) := fun _ _ => 1
def leader : (Fin 1 → ZMod 2) → Fin 2 → ZMod 2 :=
  fun syndrome => if syndrome 0 = 0 then 0 else second
def overweight : (Fin 1 → ZMod 2) → Fin 2 → ZMod 2 := fun _ => cycle

/-- Agreement: addition and subtraction coincide on these binary residuals. -/
theorem binary_residual_agrees :
    ∀ x y : Fin 2 → ZMod 2, x - y = x + y := by
  decide

/-- The boundary/check composition vanishes for both concrete boundary choices. -/
theorem boundary_is_cycle :
    parity * zeroBoundary = 0 ∧ parity * stabilizerBoundary = 0 := by
  decide

/-- Kernel-checked finite minimum certificate: the nonzero cycle has exactly weight two. -/
theorem nonzero_cycle_minimum :
    hammingNorm cycle = 2 ∧ parity *ᵥ cycle = 0 ∧ cycle ≠ 0 ∧
      ∀ v : Fin 2 → ZMod 2, parity *ᵥ v = 0 → v ≠ 0 → hammingNorm v = 2 := by
  decide

/-- This tie-breaking decoder is a genuine minimum-weight coset-leader map. -/
theorem leader_is_minimal : IsCosetLeaderMap parity.mulVecLin leader := by
  change ∀ y : Fin 2 → ZMod 2,
    parity *ᵥ leader (parity *ᵥ y) = parity *ᵥ y ∧
      hammingNorm (leader (parity *ᵥ y)) ≤ hammingNorm y
  decide

/-- The two radius-one words have the same syndrome and attain the 2t = d boundary. -/
theorem strict_distance_edge :
    hammingNorm first = 1 ∧ hammingNorm second = 1 ∧
      parity *ᵥ first = parity *ᵥ second ∧
      leader (parity *ᵥ first) = second ∧
      hammingNorm (second + first) = 2 ∧ 2 * (1 : ℕ) = 2 := by
  decide

/-- Same syndrome alone cannot establish membership in an arbitrary boundary space. -/
theorem equal_syndrome_is_insufficient :
    second + first ∉ LinearMap.range zeroBoundary.mulVecLin := by
  change ¬ ∃ u : Fin 1 → ZMod 2, zeroBoundary *ᵥ u = second + first
  decide

/-- Weakening strict distance to equality admits this genuine minimum-weight failure. -/
theorem minimum_weight_at_equality_fails :
    ¬ CorrectsUpToBoundary parity zeroBoundary leader first := by
  change ¬ (parity *ᵥ leader (parity *ᵥ first) = parity *ᵥ first ∧
    ∃ u : Fin 1 → ZMod 2, zeroBoundary *ᵥ u = leader (parity *ᵥ first) + first)
  decide

/-- At radius zero, a syndrome-preserving correction of excessive weight still fails. -/
theorem correction_weight_is_essential :
    hammingNorm (0 : Fin 2 → ZMod 2) = 0 ∧
      parity *ᵥ overweight (parity *ᵥ (0 : Fin 2 → ZMod 2)) = 0 ∧
      hammingNorm (overweight (parity *ᵥ (0 : Fin 2 → ZMod 2))) = 2 ∧
      2 * (0 : ℕ) < 2 ∧
      ¬ CorrectsUpToBoundary parity zeroBoundary overweight (0 : Fin 2 → ZMod 2) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  change ¬ (parity *ᵥ overweight (parity *ᵥ (0 : Fin 2 → ZMod 2)) =
    parity *ᵥ (0 : Fin 2 → ZMod 2) ∧
    ∃ u : Fin 1 → ZMod 2,
      zeroBoundary *ᵥ u = overweight (parity *ᵥ (0 : Fin 2 → ZMod 2)) + (0 : Fin 2 → ZMod 2))
  decide

/-- Agreement with quantum correction: a nonzero stabilizer residual is harmless. -/
theorem correction_need_not_equal_error :
    CorrectsUpToBoundary parity stabilizerBoundary leader first ∧
      leader (parity *ᵥ first) ≠ first ∧ leader (parity *ᵥ first) + first ≠ 0 := by
  change (parity *ᵥ leader (parity *ᵥ first) = parity *ᵥ first ∧
    ∃ u : Fin 1 → ZMod 2, stabilizerBoundary *ᵥ u = leader (parity *ᵥ first) + first) ∧
    leader (parity *ᵥ first) ≠ first ∧ leader (parity *ᵥ first) + first ≠ 0
  decide

-- The finite controls themselves must not admit a certificate through an additional axiom.
run_cmd do
  let environment ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let mut pending := [`Ontologic.ChainControls.binary_residual_agrees,
    `Ontologic.ChainControls.boundary_is_cycle,
    `Ontologic.ChainControls.nonzero_cycle_minimum,
    `Ontologic.ChainControls.leader_is_minimal,
    `Ontologic.ChainControls.strict_distance_edge,
    `Ontologic.ChainControls.equal_syndrome_is_insufficient,
    `Ontologic.ChainControls.minimum_weight_at_equality_fails,
    `Ontologic.ChainControls.correction_weight_is_essential,
    `Ontologic.ChainControls.correction_need_not_equal_error]
  let mut seen : Lean.NameSet := {}
  let mut queued : Lean.NameSet := pending.foldl (fun names name => names.insert name) {}
  for name in pending do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required control theorem missing: {name}"
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
    throwError "Control transitive axiom examination exceeded bound"

end Ontologic.ChainControls

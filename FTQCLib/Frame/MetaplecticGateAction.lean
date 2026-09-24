/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Frame.MetaplecticExtension
import FTQCLib.Frame.MetaplecticAction

set_option linter.unusedSectionVars false

/-!
# The unified frame gate action: `MetaGate n` acts on `(L, χ)` states

The migration's payoff: the frame's gate dynamics as ONE action of the metaplectic extension on
the signed-stabilizer states, entirely frame-side.

* `metaGateAction` — a gate `(g, c)` moves the Lagrangian by `g` and transports the character by
  `χ ↦ χ∘g⁻¹ + c∘g⁻¹`. **The structure's validity axiom is exactly the well-definedness proof**:
  the β-twisted character law for the new state is `S.valid` composed with `x.valid`.
* `MulAction (MetaGate n) (FramePureSignedStab n)` — a genuine group action: the extension's
  strictly associative multiplication makes `mul_smul` a bookkeeping identity.
* `metaGateAction_tvZ` / `_tvX` / `_tvY` — the three hand-built transvection actions
  (`frameTransvection{Z,X,Y}Action`) are literally `metaGateAction` at the three transvection
  gates `tv{Z,X,Y}MetaGate`, whose validity fields are the three `tvSign_validity` lemmas
  transported to the extension's shape.

With this file the frame's whole Clifford gate layer is: elements of `MetaGate n` acting on
`FramePureSignedStab n` — one group, one action; the per-gate constructions become instances.
-/

namespace FTQCLib.Frame

open FTQCLib.Pauli FTQCLib.Gates
open Classical

variable {n : ℕ}

/-! ## The action -/

/-- **The unified gate action**: the Lagrangian moves by `g`, the character transports as
`χ ↦ χ∘g⁻¹ + c∘g⁻¹` (zero off the new Lagrangian). Well-definedness of the β-twisted character
law is `S.valid` + the gate's own validity axiom — no per-gate argument. -/
noncomputable def metaGateAction (x : MetaGate n) (S : FramePureSignedStab n) :
    FramePureSignedStab n where
  toFrameSignedStab :=
    { L := S.L.map x.g.toLinearMap
      chi := fun p =>
        if p ∈ S.L.map x.g.toLinearMap
        then S.chi (x.g.symm p) + x.c (x.g.symm p)
        else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), map_zero, S.chi_zero, zero_add]
        have h := x.valid 0 0
        rw [add_zero, map_zero, betaFrame_self] at h
        linear_combination h
      valid := by
        intro p hp q hq
        have hgp : x.g.symm p ∈ S.L := by
          obtain ⟨p₀, hp₀, hep₀⟩ := Submodule.mem_map.mp hp
          rw [← hep₀]
          change x.g.symm (x.g p₀) ∈ S.L
          rw [x.g.symm_apply_apply]
          exact hp₀
        have hgq : x.g.symm q ∈ S.L := by
          obtain ⟨q₀, hq₀, heq₀⟩ := Submodule.mem_map.mp hq
          rw [← heq₀]
          change x.g.symm (x.g q₀) ∈ S.L
          rw [x.g.symm_apply_apply]
          exact hq₀
        have hpq : p + q ∈ S.L.map x.g.toLinearMap := Submodule.add_mem _ hp hq
        simp only [if_pos hp, if_pos hq, if_pos hpq, map_add]
        rw [S.valid _ hgp _ hgq]
        have hval := x.valid (x.g.symm p) (x.g.symm q)
        rw [x.g.apply_symm_apply, x.g.apply_symm_apply] at hval
        linear_combination -hval }
  isStab := FTQCLib.Stabilizer.clifford_preserves_isStabilizer S.isStab x.isClifford
  full := by
    rw [FTQCLib.Stabilizer.clifford_preserves_finrank S.L x.g]
    exact S.full
  tight := fun p hp => if_neg hp

lemma metaGateAction_L (x : MetaGate n) (S : FramePureSignedStab n) :
    (metaGateAction x S).L = S.L.map x.g.toLinearMap := rfl

lemma metaGateAction_chi (x : MetaGate n) (S : FramePureSignedStab n) (p : Pauli n) :
    (metaGateAction x S).chi p
      = if p ∈ S.L.map x.g.toLinearMap
        then S.chi (x.g.symm p) + x.c (x.g.symm p) else 0 := rfl

/-! ## The group action -/

noncomputable instance : SMul (MetaGate n) (FramePureSignedStab n) :=
  ⟨metaGateAction⟩

lemma metaGate_smul_def (x : MetaGate n) (S : FramePureSignedStab n) :
    x • S = metaGateAction x S := rfl

/-- **The frame's gate dynamics is a group action of the extension.** Strict associativity of
the `(g, c)` multiplication makes `mul_smul` a membership-and-rebracketing identity. -/
noncomputable instance : MulAction (MetaGate n) (FramePureSignedStab n) where
  one_smul S := by
    have hL : S.L.map (1 : MetaGate n).g.toLinearMap = S.L := by
      show S.L.map (LinearEquiv.refl (ZMod 2) (Pauli n)).toLinearMap = S.L
      rw [LinearEquiv.refl_toLinearMap, Submodule.map_id]
    apply framePureSignedStab_ext
    apply FrameSignedStab.ext'
    · exact hL
    · funext p
      show (if p ∈ S.L.map (1 : MetaGate n).g.toLinearMap
          then S.chi ((1 : MetaGate n).g.symm p) + (1 : MetaGate n).c ((1 : MetaGate n).g.symm p)
          else 0) = S.chi p
      rw [hL]
      by_cases hp : p ∈ S.L
      · rw [if_pos hp]
        show S.chi p + 0 = S.chi p
        rw [add_zero]
      · rw [if_neg hp]
        exact (S.tight p hp).symm
  mul_smul x y S := by
    apply framePureSignedStab_ext
    apply FrameSignedStab.ext'
    · show S.L.map ((x * y).g).toLinearMap = (S.L.map y.g.toLinearMap).map x.g.toLinearMap
      rw [← Submodule.map_comp]
      rfl
    · funext p
      show (if p ∈ S.L.map ((x * y).g).toLinearMap
          then S.chi ((x * y).g.symm p) + (x * y).c ((x * y).g.symm p) else 0)
        = (if p ∈ (S.L.map y.g.toLinearMap).map x.g.toLinearMap
          then (if x.g.symm p ∈ S.L.map y.g.toLinearMap
              then S.chi (y.g.symm (x.g.symm p)) + y.c (y.g.symm (x.g.symm p)) else 0)
            + x.c (x.g.symm p)
          else 0)
      have hgsym : (x * y).g.symm p = y.g.symm (x.g.symm p) := rfl
      have hmem : (p ∈ S.L.map ((x * y).g).toLinearMap)
          ↔ x.g.symm p ∈ S.L.map y.g.toLinearMap := by
        rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv, hgsym]
      have hmem2 : (p ∈ (S.L.map y.g.toLinearMap).map x.g.toLinearMap)
          ↔ x.g.symm p ∈ S.L.map y.g.toLinearMap :=
        Submodule.mem_map_equiv (S.L.map y.g.toLinearMap)
      by_cases hp : x.g.symm p ∈ S.L.map y.g.toLinearMap
      · rw [if_pos (hmem.mpr hp), if_pos (hmem2.mpr hp), if_pos hp, hgsym]
        show S.chi (y.g.symm (x.g.symm p))
            + (y.c (y.g.symm (x.g.symm p)) + x.c (y.g (y.g.symm (x.g.symm p))))
          = S.chi (y.g.symm (x.g.symm p)) + y.c (y.g.symm (x.g.symm p)) + x.c (x.g.symm p)
        rw [y.g.apply_symm_apply]
        ring
      · rw [if_neg (fun hc => hp (hmem.mp hc)), if_neg (fun hc => hp (hmem2.mp hc))]

/-! ## The three transvection gates, and subsumption of the hand-built actions -/

/-- The `Z_k`-transvection as an extension element: `(τ_{Z_k}, tvSignZ k)`, validity =
`tvSign_validity` transported. -/
noncomputable def tvZMetaGate (k : Fin n) : MetaGate n where
  g := transvectionEquiv (pauliz k)
  c := tvSignZ k
  valid := fun a b => by
    have h := tvSign_validity k (transvectionEquiv (pauliz k) a) (transvectionEquiv (pauliz k) b)
    rw [tvZ_invol, tvZ_invol,
      show transvectionEquiv (pauliz k) a + transvectionEquiv (pauliz k) b
          = transvectionEquiv (pauliz k) (a + b) from
        (map_add (transvectionEquiv (pauliz k)) a b).symm,
      tvZ_invol] at h
    linear_combination h

/-- The `X_k`-transvection as an extension element (the same shared cochain). -/
noncomputable def tvXMetaGate (k : Fin n) : MetaGate n where
  g := transvectionEquiv (paulix k)
  c := tvSignZ k
  valid := fun a b => by
    have h := tvSign_validity_X k (transvectionEquiv (paulix k) a) (transvectionEquiv (paulix k) b)
    rw [tvX_invol, tvX_invol,
      show transvectionEquiv (paulix k) a + transvectionEquiv (paulix k) b
          = transvectionEquiv (paulix k) (a + b) from
        (map_add (transvectionEquiv (paulix k)) a b).symm,
      tvX_invol] at h
    linear_combination h

/-- The `Y_k`-transvection as an extension element (the same shared cochain). -/
noncomputable def tvYMetaGate (k : Fin n) : MetaGate n where
  g := transvectionEquiv (paulix k + pauliz k)
  c := tvSignZ k
  valid := fun a b => by
    have h := tvSign_validity_Y k (transvectionEquiv (paulix k + pauliz k) a)
      (transvectionEquiv (paulix k + pauliz k) b)
    rw [tvY_invol, tvY_invol,
      show transvectionEquiv (paulix k + pauliz k) a + transvectionEquiv (paulix k + pauliz k) b
          = transvectionEquiv (paulix k + pauliz k) (a + b) from
        (map_add (transvectionEquiv (paulix k + pauliz k)) a b).symm,
      tvY_invol] at h
    linear_combination h

/-- **Subsumption**: the hand-built `Z`-transvection action IS the unified action at
`tvZMetaGate` (definitional — the transvection is its own inverse). -/
theorem metaGateAction_tvZ (k : Fin n) (S : FramePureSignedStab n) :
    metaGateAction (tvZMetaGate k) S = frameTransvectionZAction k S :=
  framePureSignedStab_ext (FrameSignedStab.ext' rfl (funext fun _ => rfl))

/-- **Subsumption**: the hand-built `X`-transvection action IS the unified action at
`tvXMetaGate`. -/
theorem metaGateAction_tvX (k : Fin n) (S : FramePureSignedStab n) :
    metaGateAction (tvXMetaGate k) S = frameTransvectionXAction k S :=
  framePureSignedStab_ext (FrameSignedStab.ext' rfl (funext fun _ => rfl))

/-- **Subsumption**: the hand-built `Y`-transvection action IS the unified action at
`tvYMetaGate`. -/
theorem metaGateAction_tvY (k : Fin n) (S : FramePureSignedStab n) :
    metaGateAction (tvYMetaGate k) S = frameTransvectionYAction k S :=
  framePureSignedStab_ext (FrameSignedStab.ext' rfl (funext fun _ => rfl))

end FTQCLib.Frame

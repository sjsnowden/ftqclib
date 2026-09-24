/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardTotality

/-!
# Check: the totality layer

The controls are aimed at the two hypotheses of the support half, one row each: `hi` is
load-bearing (`shadow_swap_eq`'s conclusion is *false* on `Lx`, where the raised bit is
already X-supported) and co-isotropy is load-bearing (the key lemma's conclusion is *false*
on `⊥`, which is isotropic — so isotropy alone cannot replace `horth`). A third control
separates the referee's involutivity from vacuity: `walshTransform` is not the identity.
The Bell rows discharge every hypothesis of `shadow_swap_eq` on the genuine Bell Lagrangian —
the theorems are not vacuously true — and a kernel row pins that the swapped pure-`Z` reader
has X-part exactly `e₀`. The decidability rows run the transported instance through `decide`
in both directions (one `∈`, one `∉`), so the decision procedure is seen to discriminate.

What no row here tests: the amplitude half (`amp_hRaise` certifies `hRaise` against
`walshTransform`); these rows are support-level and referee-level only. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib.Pauli FTQCLib.Stabilizer

/-! ## Controls — each aimed at one hypothesis -/

/-- **Control — `hi` is load-bearing.** At `n = 1`, `L = Lx` the raised bit is already
X-supported, and the theorem's conclusion is *false*: the swap sends `Lx` to `Lz` (shadow
`⊥`) while the right side contains `e₀`. A version of `shadow_swap_eq` without `hi` is
refuted here. -/
example :
    Submodule.map xProj (Submodule.map (pauliSwapOn {0}) (Lx (n := 1)))
      ≠ Submodule.map xProj (Lx (n := 1))
          ⊔ Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 1 → ZMod 2)} := by
  intro h
  have hR : (Pi.single 0 1 : Fin 1 → ZMod 2)
      ∈ Submodule.map xProj (Lx (n := 1))
          ⊔ Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 1 → ZMod 2)} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [← h] at hR
  obtain ⟨q, hq, hqX⟩ := Submodule.mem_map.mp hR
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hq
  have hpZ : p.Z = 0 := mem_Lx.mp hp
  rw [xProj_apply] at hqX
  have h0 := congrFun hqX 0
  rw [pauliSwapOn_X, if_pos (Finset.mem_singleton_self 0), Pi.single_eq_same, hpZ] at h0
  exact absurd h0 (by decide)

/-- **Control — co-isotropy is load-bearing.** The raised bit is off `⊥`'s (empty) shadow,
yet `⊥` has no pure-`Z` reader: the key lemma's conclusion is *false* there. -/
example :
    ¬ ∃ w : Fin 1 → ZMod 2,
        w 0 = 1 ∧ (⟨0, w⟩ : Pauli 1) ∈ (⊥ : Submodule (ZMod 2) (Pauli 1)) := by
  rintro ⟨w, hw1, hwmem⟩
  rw [Submodule.mem_bot] at hwmem
  have hw : w = 0 := congrArg Pauli.Z hwmem
  rw [hw] at hw1
  exact absurd hw1 (by decide)

/-- The control's premise: `⊥` *is* isotropic — which is exactly why isotropy alone cannot
stand in for `horth` in the key lemma. -/
example : IsStabilizer (⊥ : Submodule (ZMod 2) (Pauli 1)) := by
  intro p hp q _
  rw [Submodule.mem_bot] at hp
  rw [hp]
  exact omega_zero_left q

/-- The control's other premise: `hi` holds at `⊥`, so the refuted hypothesis is `horth`
and nothing else. -/
example : (Pi.single 0 1 : Fin 1 → ZMod 2)
    ∉ Submodule.map xProj (⊥ : Submodule (ZMod 2) (Pauli 1)) := by
  intro hmem
  obtain ⟨p, hp, hpX⟩ := Submodule.mem_map.mp hmem
  rw [Submodule.mem_bot] at hp
  rw [hp, map_zero] at hpX
  have h0 := congrFun hpX 0
  rw [Pi.single_eq_same] at h0
  exact absurd h0 (by decide)

/-- **Control — the involution is not vacuous.** `walshTransform` is not the identity: on
`v ↦ (v 0).val` at the point `![0]` it returns `1/√2`, where the identity returns `0`. An
accidental `W = id` would satisfy `walshTransform_involutive`; this row separates the
theorem from that degenerate case. -/
example :
    walshTransform (n := 1) 0 (fun v => ((v 0).val : ℂ)) ![0]
      ≠ (fun v : Fin 1 → ZMod 2 => ((v 0).val : ℂ)) ![0] := by
  have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hsign : signOf ((![0] : Fin 1 → ZMod 2) 0) = 1 := by
    unfold signOf
    rw [if_pos (by decide : (![0] : Fin 1 → ZMod 2) 0 = 0)]
  have hval : walshTransform (n := 1) 0 (fun v => ((v 0).val : ℂ)) ![0]
      = 1 / (Real.sqrt 2 : ℂ) := by
    unfold walshTransform
    simp only [Function.update_self, hsign]
    rw [show ((0 : ZMod 2)).val = 0 by decide, show ((1 : ZMod 2)).val = 1 by decide]
    push_cast
    ring
  have hid : (fun v : Fin 1 → ZMod 2 => ((v 0).val : ℂ)) ![0] = 0 := by
    change (((![0] : Fin 1 → ZMod 2) 0).val : ℂ) = 0
    rw [show (![0] : Fin 1 → ZMod 2) 0 = 0 by decide,
      show ((0 : ZMod 2)).val = 0 by decide]
    exact Nat.cast_zero
  rw [hval, hid]
  exact div_ne_zero one_ne_zero hsqrt

/-! ## The decidability rows — the transported instance computes, both ways -/

/-- The shadow test evaluated by the kernel, negative side: `e₀ ∉ π_X(Lz)`. An instance
that always answered "no" would pass this row alone — the positive row below is its
control. -/
example : (Pi.single 0 1 : Fin 1 → ZMod 2) ∉ Submodule.map xProj (Lz (n := 1)) := by
  letI : DecidablePred (· ∈ Lz (n := 1)) := fun p => decidable_of_iff (p.X = 0) mem_Lz.symm
  decide

/-- The shadow test evaluated by the kernel, positive side: `e₀ ∈ π_X(Lx)`. -/
example : (Pi.single 0 1 : Fin 1 → ZMod 2) ∈ Submodule.map xProj (Lx (n := 1)) := by
  letI : DecidablePred (· ∈ Lx (n := 1)) := fun p => decidable_of_iff (p.Z = 0) mem_Lx.symm
  decide

/-! ## The Bell rows — every hypothesis discharged on the Bell state -/

/-- `shadow_swap_eq` discharged at Bell: the hypotheses of `shadow_swap_eq` are satisfiable at
a genuine entangled Lagrangian — the theorem is not vacuous. -/
example :
    Submodule.map xProj (Submodule.map (pauliSwapOn {0}) bellL)
      = Submodule.map xProj bellL
          ⊔ Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 2 → ZMod 2)} :=
  shadow_swap_eq bellL_coisotropic bellL_not_mem_shadow

/-- Kernel row: the swapped pure-`Z` reader `Z₀Z₁` has X-part exactly `e₀` — the membership
half of `shadow_swap_eq`, recomputed by `decide` with no theorem in the loop. -/
example : xProj (pauliSwapOn {0} (⟨0, ![1, 1]⟩ : Pauli 2)) = Pi.single 0 1 := by decide

/-- The Bell H-shadow is the whole 2-cube: after raising bit `0` the support subcube is
everything, `⟨(1,1)⟩ ⊔ ⟨e₀⟩ = ⊤`. The decomposition of an arbitrary `v` is checked by the
kernel over all four points. -/
example : Submodule.map xProj (Submodule.map (pauliSwapOn {0}) bellL) = ⊤ := by
  rw [shadow_swap_eq bellL_coisotropic bellL_not_mem_shadow, Submodule.eq_top_iff']
  intro v
  have hv := (by decide : ∀ v : Fin 2 → ZMod 2,
    v = v 1 • (![1, 1] : Fin 2 → ZMod 2)
      + (v 0 + v 1) • (Pi.single 0 1 : Fin 2 → ZMod 2)) v
  rw [hv]
  have hgen : (![1, 1] : Fin 2 → ZMod 2) ∈ Submodule.map xProj bellL :=
    Submodule.mem_map.mpr ⟨(⟨![1, 1], 0⟩ : Pauli 2), ⟨by decide, rfl⟩, rfl⟩
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.mem_sup_left hgen))
    (Submodule.smul_mem _ _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))

/-- The gate corollary discharged on the genuine Bell input: `bellIn`'s placeholder `⊤`
replaced by `bellL`, the representer the derived `![0,1]`. The support half of the Bell
example is a theorem instance, not a placeholder. -/
example :
    Submodule.map xProj
        (hRaise 0 ![0, 1] (⟨1, 0, 0, 1, bellL, 0⟩ : KernelSumState 2)).L
      = Submodule.map xProj bellL
          ⊔ Submodule.span (ZMod 2) {(Pi.single 0 1 : Fin 2 → ZMod 2)} :=
  hRaise_shadow 0 ![0, 1] _ bellL_coisotropic bellL_not_mem_shadow

/-! ## The pinned rows — the `u = 0` end of the dichotomy -/

/-- At `L = Lz` the key lemma's reader at bit `0` is `Z₀` itself. -/
example : ((Pi.single 0 1 : Fin 2 → ZMod 2) 0 = 1)
    ∧ (⟨0, Pi.single 0 1⟩ : Pauli 2) ∈ Lz (n := 2) :=
  ⟨by decide, mem_Lz.mpr rfl⟩

/-- Pinning puts `e₀` off the `Lz`-shadow, through the layer's own lemma. -/
example : (Pi.single 0 1 : Fin 2 → ZMod 2) ∉ Submodule.map xProj (Lz (n := 2)) :=
  notMem_shadow_of_pinned fun p hp => by rw [mem_Lz.mp hp]; rfl

/-- Under pinning `u = 0` represents the coordinate functional — `applyHPinned`'s slot as
an instance of the general layer. -/
example : ∀ v ∈ Submodule.map xProj (Lz (n := 2)), dotF2 0 v = v 0 :=
  pinned_representer_zero fun p hp => by rw [mem_Lz.mp hp]; rfl

/-! ## Discrimination, recorded

* The `Lx` and `⊥` controls each refute one hypothesis of the support half with the other
  hypothesis discharged, so neither hypothesis is decorative and neither subsumes the other.
* The Bell rows discharge `hi`, co-isotropy, and isotropy at one genuine instance; they do
  **not** test the amplitude half — no row here reads `Q`, `c`, or the emitted sign, which
  is `amp_hRaise`'s content against `walshTransform`.
* The decidability pair shows the transported instance computes and discriminates; it does
  **not** show anything about spans presented non-constructively — `DecidablePred (· ∈ L)`
  is the caller's obligation. -/

end FTQCLib.Frame.Walkthrough

/-! ## Axiom sweep (build-failing) — every declaration of `HadamardTotality.lean` -/

/-- info: 'LinearMap.BilinForm.orthogonal_sup' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms LinearMap.BilinForm.orthogonal_sup

/-- info: 'LinearMap.BilinForm.orthogonal_inf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms LinearMap.BilinForm.orthogonal_inf

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_add_left' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.dotF2_add_left

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_single' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.dotF2_single

/-- info: 'FTQCLib.Frame.Walkthrough.dotF2_single_left' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.dotF2_single_left

/-- info: 'FTQCLib.Frame.Walkthrough.omega_pureZ' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.omega_pureZ

/-- info: 'FTQCLib.Frame.Walkthrough.omega_pureX' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.omega_pureX

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_omegaBilin_Lz' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_omegaBilin_Lz

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_omegaBilin_eq_self' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_omegaBilin_eq_self

/-- info: 'FTQCLib.Frame.Walkthrough.orthogonal_le_of_lagrangian' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.orthogonal_le_of_lagrangian

/-- info: 'FTQCLib.Frame.Walkthrough.exists_pureZ_read' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.exists_pureZ_read

/-- info: 'FTQCLib.Frame.Walkthrough.exists_representer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.exists_representer

/-- info: 'FTQCLib.Frame.Walkthrough.notMem_shadow_of_representer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.notMem_shadow_of_representer

/-- info: 'FTQCLib.Frame.Walkthrough.representer_iff_notMem_shadow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.representer_iff_notMem_shadow

/-- info: 'FTQCLib.Frame.Walkthrough.hadamard_dichotomy' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hadamard_dichotomy

/-- info: 'FTQCLib.Frame.Walkthrough.notMem_shadow_of_pinned' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.notMem_shadow_of_pinned

/-- info: 'FTQCLib.Frame.Walkthrough.pinned_representer_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.pinned_representer_zero

/-- info: 'FTQCLib.Frame.Walkthrough.decidableMemShadow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.decidableMemShadow

/-- info: 'FTQCLib.Frame.Walkthrough.xProj_pauliSwapOn_singleton' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.xProj_pauliSwapOn_singleton

/-- info: 'FTQCLib.Frame.Walkthrough.shadow_swap_sup' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.shadow_swap_sup

/-- info: 'FTQCLib.Frame.Walkthrough.single_mem_shadow_swap' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.single_mem_shadow_swap

/-- info: 'FTQCLib.Frame.Walkthrough.shadow_swap_eq' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.shadow_swap_eq

/-- info: 'FTQCLib.Frame.Walkthrough.hRaise_shadow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.hRaise_shadow

/-- info: 'FTQCLib.Frame.Walkthrough.branch_pair' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.branch_pair

/-- info: 'FTQCLib.Frame.Walkthrough.walshTransform_involutive' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.walshTransform_involutive

/-- info: 'FTQCLib.Frame.Walkthrough.bellL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellL

/-- info: 'FTQCLib.Frame.Walkthrough.mem_bellL' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.mem_bellL

/-- info: 'FTQCLib.Frame.Walkthrough.bellL_isStabilizer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellL_isStabilizer

/-- info: 'FTQCLib.Frame.Walkthrough.bellL_coisotropic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellL_coisotropic

/-- info: 'FTQCLib.Frame.Walkthrough.bellL_not_mem_shadow' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellL_not_mem_shadow

/-- info: 'FTQCLib.Frame.Walkthrough.bellL_representer' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellL_representer

/-- info: 'FTQCLib.Frame.Walkthrough.bellL_pureZ_read' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FTQCLib.Frame.Walkthrough.bellL_pureZ_read

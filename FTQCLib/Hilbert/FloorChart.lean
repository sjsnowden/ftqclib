/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.FloorEquivalence
import FTQCLib.Hierarchy.FloorCategory
import FTQCLib.Hilbert.FrameSignedBridge

/-! # The floor chart of `SCat ≌ OCat` (the Clifford-equivariant upgrade)

Assembles the pieces: the frame-pure `floorChartEquiv` (floor mod gauge `≃ (L,χ)`), the
frame↔Hilbert `frameHilbertEquiv`, and the abstract `actionCategoryCongr`. The result is the literal
floor chart of `SCat ≌ OCat`: the floor states modulo gauge, as an action groupoid under the
Clifford group, are equivalent to the symplectic theory `SCat` and the operational fragment `OCat`.

**Scope.** The Clifford action carried here on the floor quotient is the one *transported*
through the bridge from the action on stabilizer states. The dynamical content — that this
transported action coincides with the *intrinsic* frame gate moves (`affinePushforward` for CNOT,
polynomial mult for `S`, the Gauss sum for `H`) — is not proved here; the `H` case is the
Gauss-sum / metaplectic-cocycle point. -/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Frame FTQCLib.Pauli CategoryTheory

variable {n : ℕ}

/-- Abbreviation for the gauge quotient of the floor. -/
abbrev FloorQuotient (n : ℕ) :=
  Quotient (Setoid.ker (fromFloor : FloorKernel n → FramePureSignedStab n))

/-- **The floor mod gauge is a Hilbert pure stabilizer state.** Composing the frame-pure
`floorChartEquiv` (floor mod gauge `≃ (L,χ)`) with the bridge `(L,χ) ≃ (L, sign)` closes the loop
from the entire frame floor construction to the established Hilbert stabilizer formalism. -/
noncomputable def floorHilbertEquiv : FloorQuotient n ≃ PureSignedStab n :=
  floorChartEquiv.trans frameHilbertEquiv

/-- **The Clifford action on the symplectic chart `(L,χ)`**, pulled back from the Hilbert
`cliffordAction` along `frameHilbertEquiv`. The `MulAction` laws are inherited from the Hilbert
action through the bijection — no metaplectic-cocycle composition law is constructed here; coherence
is borrowed, not built. -/
noncomputable instance frameCliffordAction :
    MulAction (cliffordSubgroup n) (FramePureSignedStab n) where
  smul g S := frameHilbertEquiv.symm (g • frameHilbertEquiv S)
  one_smul S := by
    show frameHilbertEquiv.symm ((1 : cliffordSubgroup n) • frameHilbertEquiv S) = S
    rw [one_smul, Equiv.symm_apply_apply]
  mul_smul g h S := by
    show frameHilbertEquiv.symm ((g * h) • frameHilbertEquiv S)
      = frameHilbertEquiv.symm
          (g • frameHilbertEquiv (frameHilbertEquiv.symm (h • frameHilbertEquiv S)))
    rw [Equiv.apply_symm_apply, mul_smul]

/-- **The action moves the Lagrangian by the symplectic map** `Φ(g) = cliffordToSymplectic g`: the
floor-chart morphisms act on `L` exactly as the symplectic group does. The cocycle-free geometric
half of "the floor chart is the symplectic action". -/
theorem frameCliffordAction_L (g : cliffordSubgroup n) (S : FramePureSignedStab n) :
    (g • S).L = Submodule.map (cliffordToSymplectic g.2).toLinearMap S.L :=
  rfl

/-- The conjugation sign is a fourth root of unity (it is `±1`, `cliffordSign_mul_self`). -/
theorem isMu4_cliffordSign {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hU : IsCliffordOperator U)
    (p : Pauli n) : IsMu4 (cliffordSign hU p) := by
  rcases mul_self_eq_one_iff.mp (cliffordSign_mul_self hU p) with h | h
  · rw [h]; exact isMu4_one
  · rw [h]; exact isMu4_neg_one

/-- **The action transports the sign by the Heisenberg cocycle.** On `L`, `χ` becomes `χ ∘ Φ⁻¹` plus
the `ZMod 4` sign cocycle `clog ∘ cliffordSign`. Together with `frameCliffordAction_L` this pins the
floor-chart morphisms down as the full symplectic-plus-sign Clifford action on `(L,χ)`. The cocycle
`clog (cliffordSign g q)` is `ZMod 4`-valued but still Hilbert-defined; an intrinsic frame formula
for it (trivial for CNOT/`S`, the Gauss sum for `H`) is not given here. -/
theorem frameCliffordAction_chi (g : cliffordSubgroup n) (S : FramePureSignedStab n) {q : Pauli n}
    (hq : q ∈ S.L) :
    (g • S).chi (cliffordToSymplectic g.2 q) = S.chi q + clog (cliffordSign g.2 q) := by
  classical
  have hmem : cliffordToSymplectic g.2 q ∈ (g • S).L := by
    rw [frameCliffordAction_L]; exact Submodule.mem_map_of_mem hq
  change (if cliffordToSymplectic g.2 q ∈ (g • S).L
      then clog ((g • frameHilbertEquiv S).sign (cliffordToSymplectic g.2 q)) else 0)
      = S.chi q + clog (cliffordSign g.2 q)
  rw [if_pos hmem]
  change clog (cliffordSign g.2 ((cliffordToSymplectic g.2).symm (cliffordToSymplectic g.2 q))
      * (frameToHilbert S).sign ((cliffordToSymplectic g.2).symm (cliffordToSymplectic g.2 q)))
      = S.chi q + clog (cliffordSign g.2 q)
  rw [LinearEquiv.symm_apply_apply]
  change clog (cliffordSign g.2 q * (if q ∈ S.L then iZ4 (S.chi q) else 0))
      = S.chi q + clog (cliffordSign g.2 q)
  rw [if_pos hq, clog_mul (isMu4_cliffordSign _ _) (by unfold iZ4; exact isMu4_iPow _), clog_iZ4,
    add_comm]

/-- **The sign is a frame-native quadratic refinement.** The `ZMod 4` sign cochain
`clog ∘ cliffordSign` obeys the cocycle law whose polarization is the **frame-native** symplectic
distortion `Δ_Φ(a,b) = betaFrame (Φa) (Φb) − betaFrame a b` (`Φ = cliffordToSymplecticFun g`):

`clog (cs (a+b)) = clog (cs a) + clog (cs b) + (betaFrame (Φa) (Φb) − betaFrame a b)`.

So the conjugation sign, read in `ZMod 4`, is structurally a frame object — a quadratic refinement
of the `betaFrame`-distortion under the symplectic map — even though each *value* `clog (cs p)` is
still read off the Hilbert `cliffordSign`. This is the `1`-cochain law, coherence-free (it does not
touch the metaplectic `2`-cocycle of composition). Derived from `cliffordSign_cocycle` and the
identity `pauliPhase = iZ4 ∘ betaFrame`. -/
theorem clog_cliffordSign_cocycle (g : cliffordSubgroup n) (a b : Pauli n) :
    clog (cliffordSign g.2 (a + b))
      = clog (cliffordSign g.2 a) + clog (cliffordSign g.2 b)
        + (betaFrame (cliffordToSymplecticFun g.2 a) (cliffordToSymplecticFun g.2 b)
            - betaFrame a b) := by
  have key := congrArg clog (cliffordSign_cocycle g.2 a b)
  rw [pauliPhase_eq_iZ4_betaFrame, pauliPhase_eq_iZ4_betaFrame,
    clog_mul (isMu4_mul (isMu4_cliffordSign _ _) (isMu4_cliffordSign _ _))
      (by unfold iZ4; exact isMu4_iPow _),
    clog_mul (isMu4_cliffordSign _ _) (isMu4_cliffordSign _ _), clog_iZ4,
    clog_mul (isMu4_cliffordSign _ _) (by unfold iZ4; exact isMu4_iPow _), clog_iZ4] at key
  linear_combination -key

/-- The Clifford action on the floor quotient, **transported** from stabilizer states through
`floorHilbertEquiv`. -/
noncomputable instance floorQuotientCliffordAction :
    MulAction (cliffordSubgroup n) (FloorQuotient n) where
  smul g q := floorHilbertEquiv.symm (g • floorHilbertEquiv q)
  one_smul q := by
    show floorHilbertEquiv.symm ((1 : cliffordSubgroup n) • floorHilbertEquiv q) = q
    rw [one_smul, Equiv.symm_apply_apply]
  mul_smul g h q := by
    show floorHilbertEquiv.symm ((g * h) • floorHilbertEquiv q)
      = floorHilbertEquiv.symm
          (g • floorHilbertEquiv (floorHilbertEquiv.symm (h • floorHilbertEquiv q)))
    rw [Equiv.apply_symm_apply, mul_smul]

/-- `floorHilbertEquiv` is equivariant — immediate from the transported action. -/
theorem floorHilbertEquiv_smul (g : cliffordSubgroup n) (q : FloorQuotient n) :
    floorHilbertEquiv (g • q) = g • floorHilbertEquiv q := by
  show floorHilbertEquiv (floorHilbertEquiv.symm (g • floorHilbertEquiv q)) = _
  rw [Equiv.apply_symm_apply]

/-- **The floor chart of `SCat ≌ OCat`.** The action groupoid of the Clifford group on the gauge
quotient of the floor is equivalent to the symplectic theory `SCat` (hence, composing with the
proven `stabilizerSymplecticEquivalence`, to the operational fragment `OCat`). The floor takes its
place inside the categorical stabilizer correspondence. -/
noncomputable def floorChartCliffordEquivalence :
    ActionCategory (cliffordSubgroup n) (FloorQuotient n) ≌ OCat n :=
  (actionCategoryCongr floorHilbertEquiv floorHilbertEquiv_smul).trans
    stabilizerSymplecticEquivalence

end FTQCLib.Hilbert

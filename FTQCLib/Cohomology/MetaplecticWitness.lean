/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.CliffordModel
import FTQCLib.Gates.Phase
import FTQCLib.Gates.CNOT
import FTQCLib.Gates.Clifford

/-!
# The Klein-four non-split witness and the discharge of `MetaplecticNonSplit 2`

A section of `Φ : Cl₂/U(1) → Sp(4,𝔽₂)` would, pushed forward through the faithful bridge `act`,
give a commuting pair of involution lifts in the computable model `SignedSymplectic 2` for any
commuting pair of `Sp` involutions. There is a commuting `Sp(4,2)` involution
pair with **no** commuting-involution lift in `Cl₂/U(1)`; this file turns that into the discharge.

The discharge factors cleanly:
* `no_section_of_klein_witness` — the **generic reduction** (homomorphism algebra + `act_g`): a
  commuting `Sp` involution pair with no commuting-involution lift in the model ⟹ no section.
* the **witness** — exhibiting that pair and the model-internal `decide` — instantiates it. -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Hilbert FTQCLib.Frame FTQCLib.Gates

/-- **Generic reduction.** If `a, b ∈ Sp(4,2)` are commuting involutions with no commuting-
involution lift in the model `SignedSymplectic 2`, then `Φ : Cl₂/U(1) → Sp(4,2)` has no section.
The proof pushes a hypothetical section `s` forward through `act`: `act (s a)` and `act (s b)` are
model elements whose `g`-parts are `a, b` (`act_g` + the section law) and which are commuting
involutions (homomorphism algebra from `a²=b²=1`, `ab=ba`) — contradicting `hno`. -/
theorem no_section_of_klein_witness (a b : spSubgroup 2)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hno : ¬ ∃ x y : SignedSymplectic 2,
      x.g = a.val ∧ y.g = b.val ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x) :
    ¬ CliffordSectionExists 2 := by
  rintro ⟨s, hs⟩
  refine hno ⟨act (s a), act (s b), ?_, ?_, ?_, ?_, ?_⟩
  · rw [act_g, hs]
  · rw [act_g, hs]
  · rw [← map_mul act (s a) (s a), ← map_mul s a a, ha2, map_one s, map_one act]
  · rw [← map_mul act (s b) (s b), ← map_mul s b b, hb2, map_one s, map_one act]
  · rw [← map_mul act (s a) (s b), ← map_mul s a b, hab,
      map_mul s b a, map_mul act (s b) (s a)]

/-- **The model-internal Klein-four obstruction** — the only model-specific input. A commuting
`Sp(4,2)` involution pair with no commuting-involution lift in the model `SignedSymplectic 2`.
Everything above is unconditional; this is a finite, decidable, model-internal statement,
proved below as `kleinWitnessExists`. -/
def KleinWitnessExists : Prop :=
  ∃ a b : spSubgroup 2, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
    ¬ ∃ x y : SignedSymplectic 2,
      x.g = a.val ∧ y.g = b.val ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x

/-- **`MetaplecticNonSplit 2`, modulo the finite Klein-four witness.** The entire
abstract → computable → reduction machinery (`act`, `act_g`, `no_section_of_klein_witness`) is
unconditional and axiom-clean; the only further input is the model-internal `KleinWitnessExists`,
proved below as `kleinWitnessExists`. -/
theorem metaplecticNonSplit_two_of_witness (h : KleinWitnessExists) :
    ¬ CliffordSectionExists 2 := by
  obtain ⟨a, b, ha2, hb2, hab, hno⟩ := h
  exact no_section_of_klein_witness a b ha2 hb2 hab hno


private theorem fin2_ne : (0 : Fin 2) ≠ 1 := by decide

/-- **No commuting-involution lift of the witness pair.** For `a = S₀ = phaseAt 0` and
`b = CNOT₀→₁ = cnotAt 0 1`, no pair of model elements `x, y` with `x.g = a`, `y.g = b` can be
simultaneously self-inverse and commuting. The short 2-torsion contradiction: `x²=1` at `X₀` plus
`valid` at `(X₀,Z₀)` (`frameDistortion a X₀ Z₀ = 2`) forces `x.s(Z₀)+2 = 0`; while `x*y=y*x` at `Z₁`
(with `a·Z₁=Z₁`, `b·Z₁=Z₀Z₁`, `frameDistortion a Z₀ Z₁ = 0`) forces `x.s(Z₀)=0`.
So `2 = 0` in `ZMod 4`. -/
theorem noJointInvolutionLift :
    ¬ ∃ x y : SignedSymplectic 2,
      x.g = phaseAt 0 ∧ y.g = cnotAt 0 1 fin2_ne ∧
      x * x = 1 ∧ y * y = 1 ∧ x * y = y * x := by
  rintro ⟨x, y, hxg', hyg', hx2, hy2, hxy⟩
  -- Ia at X0 (from x*x = 1): x.s X0 + x.s (x.g X0) = 0
  have hIa : x.s (paulix 0) + x.s (x.g (paulix 0)) = 0 := by
    have h := congrArg (fun z : SignedSymplectic 2 => z.s (paulix 0)) hx2
    simpa only [SignedSymplectic.mul_s, SignedSymplectic.one_s] using h
  -- C at Z1 (from x*y = y*x)
  have hC : y.s (pauliz 1) + x.s (y.g (pauliz 1))
      = x.s (pauliz 1) + y.s (x.g (pauliz 1)) := by
    have h := congrArg (fun z : SignedSymplectic 2 => z.s (pauliz 1)) hxy
    simpa only [SignedSymplectic.mul_s] using h
  rw [hxg'] at hIa hC
  rw [hyg'] at hC
  -- gate actions (concrete)
  have haX0 : phaseAt (0 : Fin 2) (paulix 0) = paulix 0 + pauliz 0 := by decide
  have haZ1 : phaseAt (0 : Fin 2) (pauliz 1) = pauliz 1 := by decide
  have hbZ1 : cnotAt (0 : Fin 2) 1 fin2_ne (pauliz 1) = pauliz 0 + pauliz 1 := by decide
  rw [haX0] at hIa
  rw [hbZ1, haZ1] at hC
  -- valid instances
  have hv1 := x.valid (paulix 0) (pauliz 0)
  have hv2 := x.valid (pauliz 0) (pauliz 1)
  rw [hxg'] at hv1 hv2
  have hfd1 : frameDistortion (phaseAt (0 : Fin 2)) (paulix 0) (pauliz 0) = 2 := by decide
  have hfd2 : frameDistortion (phaseAt (0 : Fin 2)) (pauliz 0) (pauliz 1) = 0 := by decide
  rw [hfd1] at hv1
  rw [hfd2, add_zero] at hv2
  have h2x0 : 2 * x.s (paulix 0) = 0 := SignedSymplectic.two_smul_s x (paulix 0)
  -- x.s Z0 + 2 = 0
  have hZ0a : x.s (pauliz 0) + 2 = 0 := by
    have key : x.s (paulix 0) + (x.s (paulix 0) + x.s (pauliz 0) + 2) = 0 := by
      rw [← hv1]; exact hIa
    linear_combination key - h2x0
  -- x.s Z0 = 0 (from C + valid at (Z0,Z1))
  have hC' : x.s (pauliz 0 + pauliz 1) = x.s (pauliz 1) := by linear_combination hC
  have hZ0b : x.s (pauliz 0) = 0 := by linear_combination hC' - hv2
  -- 2 = 0 in ZMod 4
  exact absurd (by linear_combination hZ0a - hZ0b : (2 : ZMod 4) = 0) (by decide)

/-- **The Klein-four witness is realized** by `a = S₀ = phaseAt 0` and `b = CNOT₀→₁ = cnotAt 0 1`.
Both are commuting involutions in `Sp(4,2)`; the no-lift is a short, direct contradiction in the
model (no enumeration). The sign is 2-torsion, so a hypothetical lift `x` of `a` forces
`x.s (Z₀) + 2 = 0` (from `x²=1` at `X₀` + `valid` at `(X₀,Z₀)`, with `frameDistortion a X₀ Z₀ = 2`),
while commutation `x*y = y*x` at `Z₁` (with `a·Z₁ = Z₁`, `b·Z₁ = Z₀Z₁`, and
`frameDistortion a Z₀ Z₁ = 0`) forces `x.s (Z₀) = 0` — so `2 = 0` in `ZMod 4`. -/
theorem kleinWitnessExists : KleinWitnessExists := by
  refine ⟨⟨phaseAt 0, mem_spSubgroup.mpr (phaseAt_isClifford 0)⟩,
          ⟨cnotAt 0 1 fin2_ne, mem_spSubgroup.mpr (cnotAt_isClifford 0 1 fin2_ne)⟩,
          ?_, ?_, ?_, ?_⟩
  · -- a * a = 1
    refine Subtype.ext (LinearEquiv.ext fun p => ?_)
    exact (phaseAt 0).left_inv p
  · -- b * b = 1
    refine Subtype.ext (LinearEquiv.ext fun p => ?_)
    exact (cnotAt 0 1 fin2_ne).left_inv p
  · -- a * b = b * a
    refine Subtype.ext (LinearEquiv.ext fun p => ?_)
    show phaseAt 0 (cnotAt 0 1 fin2_ne p) = cnotAt 0 1 fin2_ne (phaseAt 0 p)
    refine Pauli.ext ?_ ?_
    · funext i; fin_cases i <;>
        simp [phaseAt_X, cnotAt_X, Function.update]
    · funext i; fin_cases i <;>
        simp [phaseAt_X, phaseAt_Z, cnotAt_X, cnotAt_Z, Function.update] <;>
        abel
  · -- the model-internal no-lift, extracted above
    exact noJointInvolutionLift

/-- **`MetaplecticNonSplit 2`: the extension `Cl₂/U(1) → Sp(4,2)` does not split** — now
unconditional. -/
theorem metaplecticNonSplit_two : ¬ CliffordSectionExists 2 :=
  metaplecticNonSplit_two_of_witness kleinWitnessExists

/-! ## The obstruction is purely joint

The non-split lives entirely in the *pair*, never in a single gate. Each witness gate, on its own,
lifts to a *self-inverse* model element — exhibited below by an explicit sign cochain (degree 2 for
`S₀`, degree 3 for `CNOT₀→₁`), whose `valid` and involution conditions are kernel `decide`. Yet
`noJointInvolutionLift` shows the two lifts can never be chosen to commute. -/

/-- An involution lift of `S₀ = phaseAt 0` in the model: sign `s(p) = 2·(z₀ + x₀·z₀)`. -/
noncomputable def liftS0 : SignedSymplectic 2 where
  g := phaseAt 0
  hg := phaseAt_isClifford 0
  s := fun p => 2 * (((p.Z 0 + p.X 0 * p.Z 0).val : ℕ) : ZMod 4)
  valid := by decide

/-- An involution lift of `CNOT₀→₁ = cnotAt 0 1`: sign `s(p) = 2·(x₀·z₁·(1 + z₀ + x₁))`. -/
noncomputable def liftCN : SignedSymplectic 2 where
  g := cnotAt 0 1 fin2_ne
  hg := cnotAt_isClifford 0 1 fin2_ne
  s := fun p => 2 * (((p.X 0 * p.Z 1 * (1 + p.Z 0 + p.X 1)).val : ℕ) : ZMod 4)
  valid := by decide

/-- `S₀` lifts to a self-inverse model element (a single gate has no obstruction). -/
theorem phaseAt0_lifts : ∃ x : SignedSymplectic 2, x.g = phaseAt 0 ∧ x * x = 1 := by
  refine ⟨liftS0, rfl, SignedSymplectic.ext ?_ ?_⟩
  · exact LinearEquiv.ext fun p => (phaseAt 0).left_inv p
  · funext p
    show liftS0.s p + liftS0.s (phaseAt 0 p) = 0
    revert p; decide

/-- `CNOT₀→₁` lifts to a self-inverse model element (a single gate has no obstruction). -/
theorem cnot_lifts : ∃ y : SignedSymplectic 2, y.g = cnotAt 0 1 fin2_ne ∧ y * y = 1 := by
  refine ⟨liftCN, rfl, SignedSymplectic.ext ?_ ?_⟩
  · exact LinearEquiv.ext fun p => (cnotAt 0 1 fin2_ne).left_inv p
  · funext p
    show liftCN.s p + liftCN.s (cnotAt 0 1 fin2_ne p) = 0
    revert p; decide

/-- **The metaplectic obstruction is purely joint.** Each witness gate individually lifts to a
self-inverse model element (`phaseAt0_lifts`, `cnot_lifts`), yet the commuting pair has no commuting
self-inverse lift (`noJointInvolutionLift`). So the defect of `metaplecticNonSplit_two` is carried
entirely by the pair — never by a single gate. -/
theorem obstruction_purely_joint :
    (∃ x : SignedSymplectic 2, x.g = phaseAt 0 ∧ x * x = 1) ∧
    (∃ y : SignedSymplectic 2, y.g = cnotAt 0 1 fin2_ne ∧ y * y = 1) ∧
    ¬ ∃ x y : SignedSymplectic 2,
        x.g = phaseAt 0 ∧ y.g = cnotAt 0 1 fin2_ne ∧
        x * x = 1 ∧ y * y = 1 ∧ x * y = y * x :=
  ⟨phaseAt0_lifts, cnot_lifts, noJointInvolutionLift⟩

end FTQCLib.Cohomology

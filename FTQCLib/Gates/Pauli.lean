/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Gates.Clifford
import Mathlib.Tactic.LinearCombination

set_option linter.unusedSectionVars false

/-! # The phased Pauli group `C_1` of the Clifford hierarchy

`FTQCLib.Pauli n` records a Pauli operator on `n` qubits modulo phase: just
its `X`-support and `Z`-support, with composition recovered as
componentwise `ZMod 2`-addition. To recover the *full* Pauli group we
must reinstate the phase factor in `{1, i, -1, -i} ≅ ZMod 4`.

This file defines

* `PhasedPauli n` — the full Pauli group on `n` qubits. An element
  `⟨ω, x, z⟩` represents the operator `i^ω · X^x · Z^z` (X factors
  first, then Z factors, in qubit-index order).
* the group structure on `PhasedPauli n`, with composition
  `⟨ω₁, x₁, z₁⟩ · ⟨ω₂, x₂, z₂⟩ = ⟨ω₁ + ω₂ + 2·(z₁·x₂), x₁ + x₂, z₁ + z₂⟩`.
  The `2·(z₁·x₂)` term tracks the `(-1)^(z₁·x₂)` sign produced when
  commuting the `Z^z₁` factors of the left operand past the `X^x₂`
  factors of the right operand to bring everything into the
  canonical-form ordering. The group is non-abelian; the phase
  bookkeeping is asymmetric.
* `forgetPhase : PhasedPauli n → FTQCLib.Pauli n`, the projection to the
  symplectic representation. It is *not* a group homomorphism in the
  multiplicative sense (its codomain is an additive group), but the
  X- and Z-sectors compose additively under it: this is
  `forgetPhase_mul`.
* `IsPauli`, the predicate at the symplectic level. Conjugation by a
  Pauli acts trivially on `Pauli n` modulo phase, so the image of the
  Pauli group under conjugation is `{identity}`: `IsPauli T := T =
  LinearEquiv.refl …`.
* `IsPauli.isClifford` — `C_1 ⊆ C_2`, i.e. every Pauli (symplectically:
  the identity) is Clifford. This is the base case of the Clifford
  hierarchy.
-/

namespace FTQCLib.Gates

open FTQCLib.Pauli

variable {n : ℕ}

/-- The full Pauli group on `n` qubits. An element `⟨phase, X, Z⟩`
represents the unitary `i^phase · X^X · Z^Z`, with the convention that
the `X` factors are applied first, then the `Z` factors, in qubit-index
order. The phase ranges over `ZMod 4`, encoding the four possible
global phases `{1, i, -1, -i}` of a Pauli string. -/
@[ext]
structure PhasedPauli (n : ℕ) where
  phase : ZMod 4
  X     : Fin n → ZMod 2
  Z     : Fin n → ZMod 2

namespace PhasedPauli

/-- Every element of `ZMod 2` is `0` or `1`; useful as a case-split
hypothesis. -/
private lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  -- `ZMod 2 = Fin 2`; enumerate via `Fin.cases`. Direct `decide` on the
  -- universal statement fails because `a` is a free variable; convert
  -- to a closed `∀`-statement first.
  revert a
  decide

/-- The `(ZMod 2)`-valued symplectic dot product `z · x = ∑ᵢ zᵢ · xᵢ`,
lifted to `ZMod 4` so it can be multiplied by `2` and added to the
phase. We sum the natural-number representatives of `zᵢ · xᵢ` rather
than first sum-then-cast, because the cast `ZMod 2 → ZMod 4` is not a
ring homomorphism: in `ZMod 2`, `1 + 1 = 0`, but their `ZMod 4` lifts
sum to `2`, not `0` — and that `2` is precisely the sign tracker we
want. -/
def phaseShift (z x : Fin n → ZMod 2) : ZMod 4 :=
  ∑ i, ((z i).val * (x i).val : ZMod 4)

@[simp] lemma phaseShift_zero_left (x : Fin n → ZMod 2) :
    phaseShift 0 x = 0 := by
  simp [phaseShift]

@[simp] lemma phaseShift_zero_right (z : Fin n → ZMod 2) :
    phaseShift z 0 = 0 := by
  simp [phaseShift]

/-- Per-index identity in `ZMod 4`:
  `((a + b).val * c.val) = a.val * c.val + b.val * c.val
                          + 2 * a.val * b.val * c.val`
holds for `a, b, c : ZMod 2`. Pointwise check by enumerating the eight
0/1 combinations. -/
private lemma phaseShift_pointwise_left (a b c : ZMod 2) :
    (((a + b).val : ZMod 4) * (c.val : ZMod 4)) =
      ((a.val : ZMod 4) * (c.val : ZMod 4))
        + ((b.val : ZMod 4) * (c.val : ZMod 4))
        + 2 * ((a.val : ZMod 4) * (b.val : ZMod 4) * (c.val : ZMod 4)) := by
  rcases zmod_two_cases a with ha | ha <;>
    rcases zmod_two_cases b with hb | hb <;>
      rcases zmod_two_cases c with hc | hc <;>
        (subst ha; subst hb; subst hc; decide)

/-- Per-index identity in `ZMod 4` for the right slot:
  `(c.val * (a + b).val) = c.val·a.val + c.val·b.val + 2·c.val·a.val·b.val`. -/
private lemma phaseShift_pointwise_right (c a b : ZMod 2) :
    ((c.val : ZMod 4) * ((a + b).val : ZMod 4)) =
      ((c.val : ZMod 4) * (a.val : ZMod 4))
        + ((c.val : ZMod 4) * (b.val : ZMod 4))
        + 2 * ((c.val : ZMod 4) * (a.val : ZMod 4) * (b.val : ZMod 4)) := by
  rcases zmod_two_cases a with ha | ha <;>
    rcases zmod_two_cases b with hb | hb <;>
      rcases zmod_two_cases c with hc | hc <;>
        (subst ha; subst hb; subst hc; decide)

/-- Pointwise additivity in the first slot. The cross-term picks up
`2 · (z₁·z₂·x)` per index, because `(z₁ + z₂).val` in `ZMod 4`
contains a cross-term proportional to `z₁.val · z₂.val`. -/
lemma phaseShift_add_left (z₁ z₂ x : Fin n → ZMod 2) :
    phaseShift (z₁ + z₂) x =
      phaseShift z₁ x + phaseShift z₂ x +
        2 * ∑ i, ((z₁ i).val * (z₂ i).val * (x i).val : ZMod 4) := by
  simp only [phaseShift, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hpw := phaseShift_pointwise_left (z₁ i) (z₂ i) (x i)
  have h : (z₁ + z₂) i = z₁ i + z₂ i := Pi.add_apply _ _ i
  rw [h]
  linear_combination hpw

/-- Pointwise additivity in the second slot. Mirror of
`phaseShift_add_left`. -/
lemma phaseShift_add_right (z x₁ x₂ : Fin n → ZMod 2) :
    phaseShift z (x₁ + x₂) =
      phaseShift z x₁ + phaseShift z x₂ +
        2 * ∑ i, ((z i).val * (x₁ i).val * (x₂ i).val : ZMod 4) := by
  simp only [phaseShift, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hpw := phaseShift_pointwise_right (z i) (x₁ i) (x₂ i)
  have h : (x₁ + x₂) i = x₁ i + x₂ i := Pi.add_apply _ _ i
  rw [h]
  linear_combination hpw

/-- Multiplication in the Pauli group. The phase picks up `2·(z₁·x₂)`,
the sign from commuting the left operand's `Z`-string past the right
operand's `X`-string into the canonical X-then-Z ordering. -/
instance : Mul (PhasedPauli n) where
  mul P Q := ⟨P.phase + Q.phase + 2 * phaseShift P.Z Q.X,
              P.X + Q.X, P.Z + Q.Z⟩

@[simp] lemma mul_phase (P Q : PhasedPauli n) :
    (P * Q).phase = P.phase + Q.phase + 2 * phaseShift P.Z Q.X := rfl

@[simp] lemma mul_X (P Q : PhasedPauli n) : (P * Q).X = P.X + Q.X := rfl

@[simp] lemma mul_Z (P Q : PhasedPauli n) : (P * Q).Z = P.Z + Q.Z := rfl

/-- The identity element of the Pauli group: phase `0`, trivial X- and
Z-supports. -/
instance : One (PhasedPauli n) := ⟨⟨0, 0, 0⟩⟩

@[simp] lemma one_phase : (1 : PhasedPauli n).phase = 0 := rfl
@[simp] lemma one_X : (1 : PhasedPauli n).X = 0 := rfl
@[simp] lemma one_Z : (1 : PhasedPauli n).Z = 0 := rfl

/-- The inverse of `⟨ω, x, z⟩` is `⟨2·(z·x) - ω, x, z⟩`. The
X- and Z-supports are involutive (each Pauli is its own inverse modulo
phase); the phase is chosen so that `P · P⁻¹` returns the identity. -/
instance : Inv (PhasedPauli n) where
  inv P := ⟨2 * phaseShift P.Z P.X - P.phase, P.X, P.Z⟩

@[simp] lemma inv_phase (P : PhasedPauli n) :
    (P⁻¹).phase = 2 * phaseShift P.Z P.X - P.phase := rfl

@[simp] lemma inv_X (P : PhasedPauli n) : (P⁻¹).X = P.X := rfl

@[simp] lemma inv_Z (P : PhasedPauli n) : (P⁻¹).Z = P.Z := rfl

/-- `4 · a = 0` in `ZMod 4`. Used to discard cross-terms that arise
when expanding `phaseShift_add_left` / `phaseShift_add_right` inside
the associativity proof. -/
private lemma four_mul_zMod4 (a : ZMod 4) : 4 * a = 0 := by
  have h : (4 : ZMod 4) = 0 := by decide
  rw [h, zero_mul]

/-- The X-sector additively cancels itself in characteristic two. -/
private lemma X_add_self_zero (P : PhasedPauli n) :
    P.X + P.X = (0 : Fin n → ZMod 2) := by
  funext i
  exact CharTwo.add_self_eq_zero _

/-- The Z-sector additively cancels itself in characteristic two. -/
private lemma Z_add_self_zero (P : PhasedPauli n) :
    P.Z + P.Z = (0 : Fin n → ZMod 2) := by
  funext i
  exact CharTwo.add_self_eq_zero _

/-- Multiplication on `PhasedPauli n` is associative. The X- and
Z-sectors are vector-additive (trivially associative); the phase
algebra reduces, after expanding `phaseShift` on sums and absorbing a
common `4·(sum)` residue, to
  `ω₁ + ω₂ + ω₃ + 2·(z₁·x₂) + 2·(z₁·x₃) + 2·(z₂·x₃)`
on each side. -/
theorem mul_assoc' (P Q R : PhasedPauli n) : (P * Q) * R = P * (Q * R) := by
  refine PhasedPauli.ext ?_ ?_ ?_
  · -- Phase: expand using `mul_phase` (twice) on each side, then
    -- decompose the inner `phaseShift` via `_add_left` / `_add_right`.
    change (P.phase + Q.phase + 2 * phaseShift P.Z Q.X) + R.phase
            + 2 * phaseShift (P.Z + Q.Z) R.X
          = P.phase + (Q.phase + R.phase + 2 * phaseShift Q.Z R.X)
            + 2 * phaseShift P.Z (Q.X + R.X)
    rw [phaseShift_add_left, phaseShift_add_right]
    -- Residual `4·(sum)` terms vanish.
    have h4L := four_mul_zMod4
      (∑ i, ((P.Z i).val * (Q.Z i).val * (R.X i).val : ZMod 4))
    have h4R := four_mul_zMod4
      (∑ i, ((P.Z i).val * (Q.X i).val * (R.X i).val : ZMod 4))
    linear_combination h4L - h4R
  · -- X-sector.
    change (P.X + Q.X) + R.X = P.X + (Q.X + R.X)
    rw [add_assoc]
  · -- Z-sector.
    change (P.Z + Q.Z) + R.Z = P.Z + (Q.Z + R.Z)
    rw [add_assoc]

/-- `1` is a left identity. -/
theorem one_mul' (P : PhasedPauli n) : 1 * P = P := by
  refine PhasedPauli.ext ?_ ?_ ?_
  · change (0 : ZMod 4) + P.phase + 2 * phaseShift 0 P.X = P.phase
    rw [phaseShift_zero_left]; ring
  · change (0 : Fin n → ZMod 2) + P.X = P.X
    rw [zero_add]
  · change (0 : Fin n → ZMod 2) + P.Z = P.Z
    rw [zero_add]

/-- `1` is a right identity. -/
theorem mul_one' (P : PhasedPauli n) : P * 1 = P := by
  refine PhasedPauli.ext ?_ ?_ ?_
  · change P.phase + (0 : ZMod 4) + 2 * phaseShift P.Z 0 = P.phase
    rw [phaseShift_zero_right]; ring
  · change P.X + (0 : Fin n → ZMod 2) = P.X
    rw [add_zero]
  · change P.Z + (0 : Fin n → ZMod 2) = P.Z
    rw [add_zero]

/-- `P⁻¹ * P = 1`. The X- and Z-sectors satisfy `p + p = 0` in
characteristic 2; the phase sums to `4 · (z·x) = 0` in `ZMod 4`. -/
theorem inv_mul_cancel' (P : PhasedPauli n) : P⁻¹ * P = 1 := by
  refine PhasedPauli.ext ?_ ?_ ?_
  · change (2 * phaseShift P.Z P.X - P.phase) + P.phase
            + 2 * phaseShift P.Z P.X = 0
    have h := four_mul_zMod4 (phaseShift P.Z P.X)
    linear_combination h
  · change P.X + P.X = (0 : Fin n → ZMod 2)
    exact X_add_self_zero P
  · change P.Z + P.Z = (0 : Fin n → ZMod 2)
    exact Z_add_self_zero P

/-- The phased Pauli group is a (non-abelian) group under composition.
The non-commutativity lives in the phase: `P · Q` and `Q · P` agree on
their X- and Z-supports but differ by `2 · (P.Z·Q.X) + 2 · (Q.Z·P.X)`
in `ZMod 4`. -/
instance : Group (PhasedPauli n) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

end PhasedPauli

/-- Forget the phase: project `PhasedPauli n` onto `FTQCLib.Pauli n` (the
Pauli group modulo phase). This is a function, not a group
homomorphism — the codomain `Pauli n` has an *additive* group
structure (componentwise `(ZMod 2)`-addition on X- and Z-supports),
not the multiplicative Pauli composition. The X- and Z-sectors do
compose additively under multiplication, however: see
`forgetPhase_mul`. -/
def forgetPhase (P : PhasedPauli n) : FTQCLib.Pauli n :=
  ⟨P.X, P.Z⟩

@[simp] lemma forgetPhase_X (P : PhasedPauli n) : (forgetPhase P).X = P.X := rfl
@[simp] lemma forgetPhase_Z (P : PhasedPauli n) : (forgetPhase P).Z = P.Z := rfl

/-- The X- and Z-sectors of `P · Q` are the sums of those of `P` and
`Q`. Equivalently, `forgetPhase` sends the multiplicative Pauli
composition to the additive composition in `FTQCLib.Pauli n`, where the
phase information is discarded. This is the algebraic content of
saying that `FTQCLib.Pauli n` is the Pauli group *modulo phase*: the
quotient by the central `ZMod 4` subgroup of phases. -/
theorem forgetPhase_mul (P Q : PhasedPauli n) :
    forgetPhase (P * Q) = forgetPhase P + forgetPhase Q := by
  refine FTQCLib.Pauli.ext ?_ ?_
  · change (P.X + Q.X) = P.X + Q.X
    rfl
  · change (P.Z + Q.Z) = P.Z + Q.Z
    rfl

/-- A `(ZMod 2)`-linear automorphism `T : Pauli n ≃ₗ Pauli n` is a
**Pauli at the symplectic level** (i.e. lies in `C_1` modulo phase) iff
`T` is the identity. Pauli conjugation acts trivially on the
symplectic representation: a Pauli `P` conjugates another Pauli `Q` to
`P Q P⁻¹ = ±Q`, where the sign is a phase. Modulo phase this is just
`Q`, so the symplectic action is `T = id`. -/
def IsPauli (T : Pauli n ≃ₗ[ZMod 2] Pauli n) : Prop :=
  T = LinearEquiv.refl (ZMod 2) (Pauli n)

/-- `C_1 ⊆ C_2`: every Pauli is Clifford. In the symplectic
representation this is trivial — `IsPauli T` says `T = id`, and the
identity preserves every bilinear form, so `IsClifford T` holds. -/
theorem IsPauli.isClifford {T : Pauli n ≃ₗ[ZMod 2] Pauli n} (h : IsPauli T) :
    IsClifford T := by
  rw [h]
  exact isClifford_refl

end FTQCLib.Gates

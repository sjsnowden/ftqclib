/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.IdempotentPolynomial
import FTQCLib.Frame.CubicCeiling
import FTQCLib.Frame.MobiusProductTower

/-!
# Acceptance checks for `FTQCLib.Frame.MobiusProductTower`

**Axiom sweep.** Every declaration of the module, each with the axiom list Lean reports for it,
build-failing.

**Agreement rows.** `FTQCLib.Frame.CubicCeiling` proves `MobiusDegLE.add` over `ZMod 4`
independently; at `R = ZMod 4` the ring-general statement gives the same fact (the two predicates
unfold to the same condition on `mobiusCoeff`). The **faces** the module's prose names are derived
here from the general staircase: the `ℤ/8` sign-level ceiling `mobiusDegLE_mul_signTop` at `m = 3`,
`a = b = 1`, and `CubicCeiling`'s cubic ceiling `mobiusDegLE_mul_evenEven` at `m = 2`, `a = b = 1`,
`d = e = 2`, each from `mobiusDegLE_mul_of_torsionTop`; the top conditions are matched by
`signTop_iff_torsionTop` and by unfolding `EvenDeg2`.

**The bridge row.** The square of a two's-complement value, read as a function of the bits, has
Möbius degree `≤ 2` at every width: `mobiusDegLE_polynomial_eval` at `X²` over the linear form of
`ECCLib.toInt_eq_sum_twosCoeff`.

**Discriminating rows.** The degree bound is attained: `(b₀ − 2b₁)²` is not of degree `≤ 1` (its top
coefficient is `−4`). The degree-one hypothesis is load-bearing: the square of the degree-2 function
`b₀b₁ + b₂b₃` has a nonzero top coefficient (`2`) at degree 4. The bound `s + d` of the piecewise
theorem is attained at `s = d = 1`. Kernel rows check the segment indicator by evaluation.
-/

namespace FTQCLib.Frame.MobiusTower

open FTQCLib.Hierarchy.BooleanMobius

/-! ## Axiom sweep -/

/-- info: 'FTQCLib.Frame.MobiusTower.MidTop' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MidTop

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE.add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE.add

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE.const_mul' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE.const_mul

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE.mono' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE.mono

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE.pow' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE.pow

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE.prod' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE.prod

/-- info: 'FTQCLib.Frame.MobiusTower.MobiusDegLE.sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MobiusDegLE.sum

/-- info: 'FTQCLib.Frame.MobiusTower.SignTop' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignTop

/-- info: 'FTQCLib.Frame.MobiusTower.TorsionTop' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TorsionTop

/-- info: 'FTQCLib.Frame.MobiusTower.altSum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms altSum

/-- info: 'FTQCLib.Frame.MobiusTower.eq_zero_of_val_ge' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_zero_of_val_ge

/-- info: 'FTQCLib.Frame.MobiusTower.midTop_iff_torsionTop' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms midTop_iff_torsionTop

/-- info: 'FTQCLib.Frame.MobiusTower.mid_mul_mid_descends' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mid_mul_mid_descends

/-- info: 'FTQCLib.Frame.MobiusTower.mid_mul_mid_ne_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mid_mul_mid_ne_zero

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusCoeff_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusCoeff_add

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusCoeff_const_mul' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusCoeff_const_mul

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusCoeff_monomChar' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusCoeff_monomChar

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusCoeff_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusCoeff_mul

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusCoeff_sum' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusCoeff_sum

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_const' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_const

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_monomChar' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_monomChar

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_mul

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_mul_of_torsionTop' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_mul_of_torsionTop

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_mul_signTop' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_mul_signTop

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_one_bit' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_one_bit

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_one_linear' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_one_linear

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_piecewise_polynomial' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_piecewise_polynomial

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_polynomial_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_polynomial_eval

/-- info: 'FTQCLib.Frame.MobiusTower.mobiusDegLE_segmentIndicator' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobiusDegLE_segmentIndicator

/-- info: 'FTQCLib.Frame.MobiusTower.mobius_expansion' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mobius_expansion

/-- info: 'FTQCLib.Frame.MobiusTower.monomChar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monomChar

/-- info: 'FTQCLib.Frame.MobiusTower.monomChar_eval' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monomChar_eval

/-- info: 'FTQCLib.Frame.MobiusTower.monomChar_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms monomChar_mul

/-- info: 'FTQCLib.Frame.MobiusTower.mul_eq_zero_of_val_saturated' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_eq_zero_of_val_saturated

/-- info: 'FTQCLib.Frame.MobiusTower.segmentIndicator' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segmentIndicator

/-- info: 'FTQCLib.Frame.MobiusTower.segmentIndicator_apply' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segmentIndicator_apply

/-- info: 'FTQCLib.Frame.MobiusTower.signTop_iff_torsionTop' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signTop_iff_torsionTop

/-- info: 'FTQCLib.Frame.MobiusTower.signTop_mul_of_midTop' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signTop_mul_of_midTop

/-- info: 'FTQCLib.Frame.MobiusTower.sign_mul_sign' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_mul_sign

/-- info: 'FTQCLib.Frame.MobiusTower.torsionTop_mul' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms torsionTop_mul

/-- info: 'FTQCLib.Frame.MobiusTower.torsion_staircase' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms torsion_staircase

/-! ## The agreement row -/

/-- The ring-general addition closure, at `R = ZMod 4`, gives `CubicCeiling`'s statement. -/
example {N d : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4} (hf : FTQCLib.Frame.MobiusDegLE d f)
    (hg : FTQCLib.Frame.MobiusDegLE d g) : FTQCLib.Frame.MobiusDegLE d (f + g) :=
  MobiusDegLE.add (R := ZMod 4) hf hg

/-- The same statement as `CubicCeiling` proves it, for comparison. -/
example {N d : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4} (hf : FTQCLib.Frame.MobiusDegLE d f)
    (hg : FTQCLib.Frame.MobiusDegLE d g) : FTQCLib.Frame.MobiusDegLE d (f + g) :=
  FTQCLib.Frame.MobiusDegLE.add hf hg

/-! ## The bridge row -/

/-- The kinetic phase's integer part: the square of the two's-complement value of the bits has
Möbius degree `≤ 2` over `ℤ`, at every width. -/
example (w : ℕ) : MobiusDegLE 2
    (fun v : Fin w → ZMod 2 => (∑ k, ECCLib.twosCoeff w k * ((v k).val : ℤ)) ^ 2) := by
  have h := mobiusDegLE_polynomial_eval (d := 2) (Polynomial.X ^ 2 : Polynomial ℤ)
    (by simp) (mobiusDegLE_one_linear (ECCLib.twosCoeff w))
  simpa using h

/-! ## Discriminating rows -/

/-- The bound is attained: `(b₀ − 2b₁)²` over `ℤ` has top Möbius coefficient `−4`, so it is not
of degree `≤ 1`. -/
example : ¬ MobiusDegLE 1
    (fun v : Fin 2 → ZMod 2 => ((v 0).val - 2 * (v 1).val : ℤ) ^ 2) := by
  intro h
  have h2 := h Finset.univ (by decide)
  rw [mobiusCoeff_eq_alt_sum] at h2
  revert h2
  decide

/-- The degree-one hypothesis is load-bearing: `f = b₀b₁ + b₂b₃` has degree `2`, and `f²` has top
Möbius coefficient `2` at degree `4`, so `f²` is not of degree `≤ 2 = natDegree X²`. -/
example : ¬ MobiusDegLE 2
    (fun v : Fin 4 → ZMod 2 =>
      ((v 0).val * (v 1).val + (v 2).val * (v 3).val : ℤ) ^ 2) := by
  intro h
  have h2 := h Finset.univ (by decide)
  rw [mobiusCoeff_eq_alt_sum] at h2
  revert h2
  decide


/-! ## The segmented potential -/

/-- **Agreement, by kernel evaluation:** the segment indicator on two selector bits of three is the
indicator of `v ∘ sel = σ`, for every `σ` and every `v`. -/
example : ∀ (σ : Fin 2 → ZMod 2) (v : Fin 3 → ZMod 2),
    segmentIndicator (R := ℤ) (fun t : Fin 2 => (t.castSucc : Fin 3)) σ v
      = if (fun t : Fin 2 => v t.castSucc) = σ then 1 else 0 := by
  decide

/-- **The arc's compressed potential, at every width.** Position bits `0 .. b − 1` form the offset
`u / 2ᵇ` inside a segment; the top four bits `b .. b + 3` select one of 16 cubics. The phase has
Möbius degree `≤ 7 = 4 + 3` in the `b + 4` bits, whatever the cubics. -/
example (b : ℕ) (p : (Fin 4 → ZMod 2) → Polynomial ℚ) (hp : ∀ σ, (p σ).natDegree ≤ 3) :
    MobiusDegLE 7 (fun v : Fin (b + 4) → ZMod 2 =>
      (p fun t => v (Fin.natAdd b t)).eval
        (∑ i : Fin (b + 4), (if (i : ℕ) < b then (2 : ℚ) ^ (i : ℕ) / 2 ^ b else 0)
          * ((v i).val : ℚ))) :=
  mobiusDegLE_piecewise_polynomial (s := 4) (d := 3) _ _ p hp

/-- **The bound `s + d` is attained:** one selector bit `v₁` choosing between the pieces `0` and
`X` at the linear form `v₀` gives `v₁ v₀`, which is not of degree `≤ 1 = s + d − 1`. -/
example : ¬ MobiusDegLE 1
    (fun v : Fin 2 → ZMod 2 => ((v 1).val * (v 0).val : ℤ)) := by
  intro h
  have h2 := h Finset.univ (by decide)
  rw [mobiusCoeff_eq_alt_sum] at h2
  revert h2
  decide

/-- The attained case is an instance of the theorem at `s = 1`, `d = 1`. -/
example : MobiusDegLE 2
    (fun v : Fin 2 → ZMod 2 =>
      (if v 1 = 1 then (Polynomial.X : Polynomial ℤ) else 0).eval
        (∑ i : Fin 2, (if i = 0 then (1 : ℤ) else 0) * ((v i).val : ℤ))) :=
  mobiusDegLE_piecewise_polynomial (s := 1) (d := 1) (fun _ => 1) _
    (fun σ => if σ 0 = 1 then Polynomial.X else 0)
    (fun σ => by dsimp only; split_ifs <;> simp)

/-! ## The faces of the staircase -/

/-- **Face row, `ℤ/8`:** the sign-level ceiling, derived from the general staircase at `m = 3`. -/
example {N d e : ℕ} {f g : (Fin N → ZMod 2) → ZMod 8} (hf : MobiusDegLE d f)
    (hg : MobiusDegLE e g) (tf : SignTop d f) (tg : SignTop e g) :
    MobiusDegLE (d + e - 1) (f * g) :=
  mobiusDegLE_mul_of_torsionTop (m := 3) (a := 1) (b := 1) hf hg
    ((signTop_iff_torsionTop f).mp tf) ((signTop_iff_torsionTop g).mp tg) (by norm_num)

/-- **Face row, `ℤ/4`:** `CubicCeiling`'s cubic ceiling, derived from the general staircase at
`m = 2`, `a = b = 1`, `d = e = 2`. -/
example {N : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4} (hf : FTQCLib.Frame.MobiusDegLE 2 f)
    (hg : FTQCLib.Frame.MobiusDegLE 2 g) (ef : FTQCLib.Frame.EvenDeg2 f)
    (eg : FTQCLib.Frame.EvenDeg2 g) : FTQCLib.Frame.MobiusDegLE 3 (f * g) :=
  mobiusDegLE_mul_of_torsionTop (m := 2) (a := 1) (b := 1) (d := 2) (e := 2) hf hg
    (fun A hA => by simpa using ef A hA) (fun B hB => by simpa using eg B hB) (by norm_num)

/-- The same statement as `CubicCeiling` proves it, for comparison. -/
example {N : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4} (hf : FTQCLib.Frame.MobiusDegLE 2 f)
    (hg : FTQCLib.Frame.MobiusDegLE 2 g) (ef : FTQCLib.Frame.EvenDeg2 f)
    (eg : FTQCLib.Frame.EvenDeg2 g) : FTQCLib.Frame.MobiusDegLE 3 (f * g) :=
  FTQCLib.Frame.mobiusDegLE_mul_evenEven hf hg ef eg

end FTQCLib.Frame.MobiusTower

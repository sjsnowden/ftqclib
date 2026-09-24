/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle
import FTQCLib.Stabilizer.Dimension
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The Hermitian Pauli action on amplitude functions

The frame's state record denotes an amplitude function `(Fin n → ZMod 2) → ℂ`, and the floor
stratum of the record is the set of records whose Lagrangian stabilizes that function. This file
supplies the action the stratum is defined through, on the modulo-phase Pauli group
`FTQCLib.Pauli n = (ZMod 2)^{2n}`, with the Hermitian sign convention: `g = (X, Z)` acts by
`(pauliAct g f) w = i^{yWeight g} · (−1)^{Z·(w + X)} · f (w + X)`, so `X` shifts, `Z` signs, and a
qubit carrying both (a `Y`) contributes one factor of `i`. With this convention every Pauli
squares to the identity, and two actions compose up to the frame's own `ℤ/4` cocycle: applying
`q` and then `p` is `i^{betaFrame q p}` times the action of `p + q` (`pauliAct_add`). The argument
order is the one the composition forces; the check module's rows separate it from the swapped
order, on which the law is false.

`StabilizedBy L f` says every element of `L` fixes `f` up to a sign `±1`. The main theorem is the
rigidity of the floor: two subspaces of dimension `n` stabilizing one nonzero amplitude are equal
(`eq_of_stabilizedBy_of_stabilizedBy`). Isotropy is not a hypothesis — it is a consequence: two
signed stabilizers of a nonzero function commute, because the composition law read in both
orders gives `i^{betaFrame q p} = i^{betaFrame p q}`, and `betaFrame_swap` turns that into
`omega p q = 0` (`omega_eq_zero_of_stabilizes`). So the join of the two subspaces is isotropic,
hence of dimension at most `n` (`finrank_le_of_isStabilizer`), hence equal to each of them.

Everything here is frame-pure: `Pauli`, `Submodule`, `ℂ`. No `FTQCLib.Hilbert`.

## Main definitions

* `pauliAct` — the Hermitian Pauli action on amplitude functions.
* `StabilizedBy` — a subspace of Paulis fixes an amplitude function up to signs.

## Main results

* `pauliAct_add` — the composition law, with the `ℤ/4` cocycle `betaFrame q p`.
* `pauliAct_pauliAct` — every Pauli acts as an involution.
* `omega_eq_zero_of_stabilizes` — signed stabilizers of a nonzero function commute.
* `isStabilizer_of_stabilizedBy` — a signed stabilizer of a nonzero function is isotropic.
* `eq_of_stabilizedBy_of_stabilizedBy` — a nonzero amplitude has at most one stabilizer of
  dimension `n`.
-/

namespace FTQCLib.Stabilizer

open FTQCLib.Pauli Module

variable {n : ℕ}

/-! ## Powers of `i` -/

/-- A sign is a square of `i`: `(−1)^k = i^{2k}`. -/
theorem neg_one_pow_eq_I_pow (k : ℕ) : (-1 : ℂ) ^ k = Complex.I ^ (2 * k) := by
  rw [pow_mul, Complex.I_sq]

/-- Powers of `i` are read modulo four: exponents equal in `ZMod 4` give equal powers. -/
theorem I_pow_eq_of_natCast_eq {a b : ℕ} (h : (a : ZMod 4) = (b : ZMod 4)) :
    Complex.I ^ a = Complex.I ^ b := by
  rw [Complex.I_pow_eq_pow_mod a, Complex.I_pow_eq_pow_mod b,
    (ZMod.natCast_eq_natCast_iff' a b 4).mp h]

/-- The power of `i` at a sum in `ZMod 4` is the product of the powers. -/
theorem I_pow_val_add (a b : ZMod 4) :
    Complex.I ^ (a + b).val = Complex.I ^ a.val * Complex.I ^ b.val := by
  have h : (((a + b).val : ℕ) : ZMod 4) = ((a.val + b.val : ℕ) : ZMod 4) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [← pow_add]
  exact I_pow_eq_of_natCast_eq h

/-! ## The action -/

/-- The Hermitian Pauli action of `g = (X, Z)` on an amplitude function:
`(pauliAct g f) w = i^{yWeight g} · (−1)^{Z·(w + X)} · f (w + X)`. -/
noncomputable def pauliAct (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ) : (Fin n → ZMod 2) → ℂ :=
  fun w => Complex.I ^ yWeight g * (-1) ^ zDot g (w + g.X) * f (w + g.X)

/-- The action as a single power of `i`: `i^{yWeight g + 2·Z·(w + X)}` times the shifted value. -/
theorem pauliAct_apply (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ) (w : Fin n → ZMod 2) :
    pauliAct g f w = Complex.I ^ (yWeight g + 2 * zDot g (w + g.X)) * f (w + g.X) := by
  unfold pauliAct
  rw [neg_one_pow_eq_I_pow, ← pow_add]

/-- The identity Pauli acts trivially. -/
@[simp] theorem pauliAct_zero (f : (Fin n → ZMod 2) → ℂ) : pauliAct (0 : Pauli n) f = f := by
  funext w
  simp [pauliAct]

/-- Every Pauli sends the zero function to the zero function. -/
@[simp] theorem pauliAct_zero_fun (g : Pauli n) :
    pauliAct g (0 : (Fin n → ZMod 2) → ℂ) = 0 := by
  funext w
  simp [pauliAct]

/-- The action commutes with a constant factor. -/
theorem pauliAct_mul_left (g : Pauli n) (c : ℂ) (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct g (fun w => c * f w) = fun w => c * pauliAct g f w := by
  funext w
  simp only [pauliAct]
  ring

/-- **The composition law.** Applying `q` and then `p` is `i^{betaFrame q p}` times the action of
`p + q`. The argument order is forced by the composition: `betaFrame X Z = 1` and
`betaFrame Z X = 3` differ, and the check module shows the swapped order is false. -/
theorem pauliAct_add (p q : Pauli n) (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct p (pauliAct q f)
      = fun w => Complex.I ^ (betaFrame q p).val * pauliAct (p + q) f w := by
  funext w
  rw [pauliAct_apply, pauliAct_apply, pauliAct_apply, X_add, ← add_assoc, ← mul_assoc,
    ← mul_assoc, ← pow_add, ← pow_add]
  congr 1
  apply I_pow_eq_of_natCast_eq
  have hyw : yWeight (q + p) = yWeight (p + q) := by rw [add_comm q p]
  have hzd : zDot (q + p) (q + p).X = zDot (p + q) (p + q).X := by rw [add_comm q p]
  have hY : yWeight (p + q) = zDot (p + q) (p + q).X := rfl
  have h1 := two_zDot_add p q (w + p.X + q.X)
  have h2 := two_zDot_add_right p (w + p.X) q.X
  have hfour : ∀ y : ZMod 4, 4 * y = 0 := by decide
  push_cast
  rw [ZMod.natCast_zmod_val]
  unfold betaFrame
  rw [hyw, hzd, hY]
  push_cast
  linear_combination -h1 - h2 - hfour ((zDot (p + q) (p + q).X : ℕ) : ZMod 4)
    - hfour ((zDot p q.X : ℕ) : ZMod 4)

/-- **Every Pauli is an involution** on amplitude functions. -/
theorem pauliAct_pauliAct (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct g (pauliAct g f) = f := by
  rw [pauliAct_add, pauli_add_self, betaFrame_self, ZMod.val_zero, pow_zero, pauliAct_zero]
  simp

/-- The action is injective: it kills only the zero function. -/
theorem pauliAct_eq_zero_iff (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct g f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have h' := congrArg (pauliAct g) h
    rwa [pauliAct_pauliAct, pauliAct_zero_fun] at h'
  · rintro rfl
    exact pauliAct_zero_fun g

/-! ## Signed stabilizers -/

/-- `L` stabilizes `f` when every element of `L` fixes `f` up to a sign `±1`. -/
def StabilizedBy (L : Submodule (ZMod 2) (Pauli n)) (f : (Fin n → ZMod 2) → ℂ) : Prop :=
  ∀ g ∈ L, ∃ s : ZMod 2, pauliAct g f = fun w => (-1) ^ s.val * f w

/-- The zero subspace stabilizes everything. -/
theorem stabilizedBy_bot (f : (Fin n → ZMod 2) → ℂ) : StabilizedBy ⊥ f := by
  intro g hg
  rw [Submodule.mem_bot] at hg
  subst hg
  exact ⟨0, by simp⟩

/-- Every subspace stabilizes the zero function — the vacuity that makes `f ≠ 0` load-bearing in
the rigidity theorem. -/
theorem stabilizedBy_zero (L : Submodule (ZMod 2) (Pauli n)) :
    StabilizedBy L (0 : (Fin n → ZMod 2) → ℂ) :=
  fun g _ => ⟨0, by funext w; simp⟩

/-- A subspace of a stabilizer is a stabilizer. -/
theorem StabilizedBy.mono {L L' : Submodule (ZMod 2) (Pauli n)} {f : (Fin n → ZMod 2) → ℂ}
    (h : L' ≤ L) (hs : StabilizedBy L f) : StabilizedBy L' f :=
  fun g hg => hs g (h hg)

/-- **Signed stabilizers of a nonzero amplitude commute.** The composition law read in both
orders gives `i^{betaFrame q p} = i^{betaFrame p q}` on a nonzero function, and `betaFrame_swap`
makes the two exponents differ by `2·omega p q`. -/
theorem omega_eq_zero_of_stabilizes {p q : Pauli n} {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0)
    (hp : ∃ s : ZMod 2, pauliAct p f = fun w => (-1) ^ s.val * f w)
    (hq : ∃ s : ZMod 2, pauliAct q f = fun w => (-1) ^ s.val * f w) :
    omega p q = 0 := by
  obtain ⟨sp, hsp⟩ := hp
  obtain ⟨sq, hsq⟩ := hq
  have h1 : pauliAct p (pauliAct q f) = fun w => (-1) ^ sq.val * ((-1) ^ sp.val * f w) := by
    rw [hsq, pauliAct_mul_left, hsp]
  have h2 : pauliAct q (pauliAct p f) = fun w => (-1) ^ sp.val * ((-1) ^ sq.val * f w) := by
    rw [hsp, pauliAct_mul_left, hsq]
  have h12 : pauliAct p (pauliAct q f) = pauliAct q (pauliAct p f) := by
    rw [h1, h2]
    funext w
    ring
  rw [pauliAct_add, pauliAct_add, add_comm q p] at h12
  have hg : pauliAct (p + q) f ≠ 0 := by
    rw [Ne, pauliAct_eq_zero_iff]
    exact hf
  obtain ⟨w, hw⟩ : ∃ w, pauliAct (p + q) f w ≠ 0 := Function.ne_iff.mp hg
  have hI : Complex.I ^ (betaFrame q p).val = Complex.I ^ (betaFrame p q).val :=
    mul_right_cancel₀ hw (congrFun h12 w)
  rw [betaFrame_swap p q, I_pow_val_add] at hI
  have hne : Complex.I ^ (betaFrame p q).val ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hI' : Complex.I ^ (2 * (((omega p q).val : ℕ) : ZMod 4)).val = 1 := by
    have h := hI
    rw [← mul_one (Complex.I ^ (betaFrame p q).val)] at h
    rw [mul_assoc, one_mul] at h
    exact mul_left_cancel₀ hne h
  rcases zmod_two_eq_zero_or_one (omega p q) with h0 | h1
  · exact h0
  · exfalso
    rw [h1] at hI'
    have hval : (2 * (((1 : ZMod 2).val : ℕ) : ZMod 4)).val = 2 := by decide
    rw [hval, Complex.I_sq] at hI'
    exact absurd hI' (by norm_num)

/-- **A signed stabilizer of a nonzero amplitude is isotropic.** -/
theorem isStabilizer_of_stabilizedBy {L : Submodule (ZMod 2) (Pauli n)}
    {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0) (hs : StabilizedBy L f) : IsStabilizer L :=
  fun p hp q hq => omega_eq_zero_of_stabilizes hf (hs p hp) (hs q hq)

/-- Two signed stabilizers of a nonzero amplitude have an isotropic join. -/
theorem isStabilizer_sup_of_stabilizedBy {L₁ L₂ : Submodule (ZMod 2) (Pauli n)}
    {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0) (hs₁ : StabilizedBy L₁ f)
    (hs₂ : StabilizedBy L₂ f) : IsStabilizer (L₁ ⊔ L₂) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  rw [omega_add_left, omega_add_right, omega_add_right,
    omega_eq_zero_of_stabilizes hf (hs₁ a ha) (hs₁ c hc),
    omega_eq_zero_of_stabilizes hf (hs₁ a ha) (hs₂ d hd),
    omega_eq_zero_of_stabilizes hf (hs₂ b hb) (hs₁ c hc),
    omega_eq_zero_of_stabilizes hf (hs₂ b hb) (hs₂ d hd)]
  simp

/-- **Rigidity of the floor.** Two subspaces of dimension `n` stabilizing one nonzero amplitude
are equal: their join is isotropic, so of dimension at most `n`, so equal to each of them. -/
theorem eq_of_stabilizedBy_of_stabilizedBy {L₁ L₂ : Submodule (ZMod 2) (Pauli n)}
    (hr₁ : finrank (ZMod 2) L₁ = n) (hr₂ : finrank (ZMod 2) L₂ = n)
    {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0) (hs₁ : StabilizedBy L₁ f)
    (hs₂ : StabilizedBy L₂ f) : L₁ = L₂ := by
  have hle : finrank (ZMod 2) ↥(L₁ ⊔ L₂) ≤ n :=
    finrank_le_of_isStabilizer (isStabilizer_sup_of_stabilizedBy hf hs₁ hs₂)
  have e₁ : L₁ = L₁ ⊔ L₂ := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  have e₂ : L₂ = L₁ ⊔ L₂ := Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
  exact e₁.trans e₂.symm

end FTQCLib.Stabilizer

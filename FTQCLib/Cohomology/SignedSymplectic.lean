/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Frame.MetaplecticAction
import FTQCLib.Gates.Transvection

/-! # The signed symplectic group — a computable model of `Clₙ/U(1)`

`Clₙ/U(1)` acts faithfully on the Hermitian Paulis by conjugation: `U H(p) U⁻¹ = i^{s(p)} H(g p)`,
with `g` symplectic and `s : Pauli n → ℤ/4` a sign exponent constrained by the frame cocycle. This
file models that data directly — a **computable** group `SignedSymplectic n` of `(g, s)` pairs, into
which the abstract `cliffordModPhase n` injects (sibling file). The point: `cliffordModPhase` is
ℂ-analytic and `decide`-blind, but this model is finite/decidable, so non-splitting witnesses become
finite checks.

The validity constraint `s(p+q) = s p + s q + frameDistortion g p q` is preserved under composition
by a clean telescoping of `frameDistortion` (no cocycle gymnastics). -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame

variable {n : ℕ}

/-- `IsClifford` is closed under inverse (symplectic maps form a group). -/
theorem IsClifford.symm {T : Pauli n ≃ₗ[ZMod 2] Pauli n} (hT : IsClifford T) :
    IsClifford T.symm := by
  intro p q
  have h := hT (T.symm p) (T.symm q)
  rw [T.apply_symm_apply, T.apply_symm_apply] at h
  exact h.symm

/-- An element of the **signed symplectic group**: a symplectic map `g` with a sign exponent `s`
satisfying the frame-cocycle constraint — the faithful conjugation data of a Clifford mod phase. -/
structure SignedSymplectic (n : ℕ) where
  /-- The symplectic part (the `Sp(2n,𝔽₂)` action on Paulis). -/
  g : Pauli n ≃ₗ[ZMod 2] Pauli n
  /-- `g` is symplectic. -/
  hg : IsClifford g
  /-- The sign exponent in `ℤ/4`. -/
  s : Pauli n → ZMod 4
  /-- The frame-cocycle constraint pinning `s` to `g`. -/
  valid : ∀ p q, s (p + q) = s p + s q + frameDistortion g p q

namespace SignedSymplectic

/-- Equality is determined by the symplectic part and the sign (`Prop` fields are irrelevant). -/
@[ext] theorem ext {x y : SignedSymplectic n} (hg : x.g = y.g) (hs : x.s = y.s) :
    x = y := by
  cases x; cases y; cases hg; cases hs; rfl

/-- Composition: `(x * y)` does `y` then `x` (matching conjugation and the crossed-hom sign law
`s_{xy}(p) = s_y(p) + s_x(g_y p)`). -/
instance : Mul (SignedSymplectic n) :=
  ⟨fun x y =>
    { g := y.g.trans x.g
      hg := y.hg.trans x.hg
      s := fun p => y.s p + x.s (y.g p)
      valid := by
        intro p q
        have hy := y.valid p q
        have hx := x.valid (y.g p) (y.g q)
        simp only [LinearEquiv.trans_apply, map_add, frameDistortion] at *
        rw [hy, hx]; ring }⟩

instance : One (SignedSymplectic n) :=
  ⟨{ g := LinearEquiv.refl (ZMod 2) (Pauli n)
     hg := isClifford_refl
     s := fun _ => 0
     valid := by intro p q; simp [frameDistortion] }⟩

instance : Inv (SignedSymplectic n) :=
  ⟨fun x =>
    { g := x.g.symm
      hg := IsClifford.symm x.hg
      s := fun p => - x.s (x.g.symm p)
      valid := by
        intro p q
        have hx := x.valid (x.g.symm p) (x.g.symm q)
        have hadd : x.g.symm (p + q) = x.g.symm p + x.g.symm q := map_add x.g.symm p q
        rw [hadd, hx]
        simp only [frameDistortion, LinearEquiv.apply_symm_apply]
        ring }⟩

@[simp] lemma mul_g (x y : SignedSymplectic n) : (x * y).g = y.g.trans x.g := rfl
@[simp] lemma mul_s (x y : SignedSymplectic n) : (x * y).s = fun p => y.s p + x.s (y.g p) := rfl
@[simp] lemma one_g : (1 : SignedSymplectic n).g = LinearEquiv.refl (ZMod 2) (Pauli n) := rfl
@[simp] lemma one_s : (1 : SignedSymplectic n).s = fun _ => 0 := rfl
@[simp] lemma inv_g (x : SignedSymplectic n) : x⁻¹.g = x.g.symm := rfl
@[simp] lemma inv_s (x : SignedSymplectic n) : x⁻¹.s = fun p => - x.s (x.g.symm p) := rfl

instance : Group (SignedSymplectic n) :=
  { (inferInstance : Mul (SignedSymplectic n)), (inferInstance : One (SignedSymplectic n)),
    (inferInstance : Inv (SignedSymplectic n)) with
    mul_assoc := by
      intro x y z
      refine SignedSymplectic.ext ?_ ?_
      · rfl
      · funext p; simp only [mul_g, mul_s, LinearEquiv.trans_apply]; ring
    one_mul := by intro x; refine SignedSymplectic.ext rfl ?_; funext p; simp
    mul_one := by intro x; refine SignedSymplectic.ext rfl ?_; funext p; simp
    inv_mul_cancel := by
      intro x
      refine SignedSymplectic.ext ?_ ?_
      · simp only [mul_g, inv_g, one_g]; exact x.g.self_trans_symm
      · funext p
        simp only [mul_s, inv_s, one_s, LinearEquiv.symm_apply_apply]
        ring }

/-- The projection to the symplectic part is a homomorphism into the Clifford/symplectic group. -/
@[simp] lemma mul_apply_g (x y : SignedSymplectic n) (p : Pauli n) :
    (x * y).g p = x.g (y.g p) := rfl

/-- `frameDistortion` vanishes on the diagonal (`betaFrame_self` at both points). -/
theorem frameDistortion_self (x : SignedSymplectic n) (q : Pauli n) :
    frameDistortion x.g q q = 0 := by
  simp only [frameDistortion, betaFrame_self, sub_self]

/-- **The sign exponent is `2`-torsion** (`{0,2}`-valued): from `valid` at `p = q`, since
`frameDistortion g p p = 0`. So each `g` has exactly `2^{2n}` lifts. -/
theorem two_smul_s (x : SignedSymplectic n) (p : Pauli n) : 2 * x.s p = 0 := by
  have h0 : x.s (0 : Pauli n) = 0 := by
    have h := x.valid 0 0
    simp only [add_zero, frameDistortion_self] at h
    linear_combination -h
  have h := x.valid p p
  rw [pauli_add_self, h0, frameDistortion_self, add_zero] at h
  linear_combination -h

end SignedSymplectic

end FTQCLib.Cohomology

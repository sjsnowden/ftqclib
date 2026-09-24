/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle
import FTQCLib.Gates.Clifford
import Mathlib.Algebra.Field.ZMod

set_option linter.unusedSectionVars false

/-!
# The char-2 metaplectic extension, frame-side: gates as `(g, c)` pairs

The definition layer of the metaplectic extension, in the frame's own import cone — **no Hilbert
ingredient**: labels, `betaFrame`, `ω`, ℤ/4. A `MetaGate` is a label automorphism `g` together
with a ℤ/4 cochain `c`, subject to the single cocycle condition
`c a + c b + β(g a, g b) = c (a+b) + β(a, b)`. Everything else is a theorem:

* `MetaGate.isClifford` — validity **forces** `g` symplectic (via the frame-native
  `betaFrame_swap`);
* the `Group` instance — `(x*y).c = y.c + x.c ∘ y.g`, **strictly associative**: the metaplectic
  cocycle is absorbed into the multiplication law;
* `twistGate` / `exists_twist_of_additive` — the kernel over `g = 1` is the label torsor:
  every additive cochain is `2·ω(w,·)` (ω-nondegeneracy via `BilinForm.toDual`).

The Hilbert realization layer (`toMetaGate` and the theorems making this extension the
projective Clifford group) lives in `FTQCLib/Hilbert/MetaplecticExtension.lean`, following the
floor-chart pattern: definition frame-side, certificate Hilbert-side.
-/

namespace FTQCLib.Frame

open FTQCLib.Pauli FTQCLib.Gates

variable {n : ℕ}

private lemma zmod2_dichot : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel

/-! ## The extension -/

/-- **The char-2 metaplectic gate**: a label automorphism together with a ℤ/4 sign cochain,
subject to the frame-pure cocycle condition. Symplecticity of `g` is a *theorem*
(`MetaGate.isClifford`), not a field. -/
@[ext]
structure MetaGate (n : ℕ) where
  g : Pauli n ≃ₗ[ZMod 2] Pauli n
  c : Pauli n → ZMod 4
  valid : ∀ a b : Pauli n,
    c a + c b + betaFrame (g a) (g b) = c (a + b) + betaFrame a b

/-- **Validity forces symplecticity**: the cocycle condition alone makes `g` preserve `ω`
(via the frame-native antisymmetry `betaFrame_swap`). -/
theorem MetaGate.isClifford (x : MetaGate n) : FTQCLib.Gates.IsClifford x.g := by
  intro p q
  rw [omegaBilin_apply, omegaBilin_apply]
  have h1 := x.valid p q
  have h2 := x.valid q p
  rw [add_comm q p, betaFrame_swap (x.g p) (x.g q), betaFrame_swap p q] at h2
  have hE : (2 : ZMod 4) * (((omega (x.g p) (x.g q)).val : ℕ) : ZMod 4)
      = 2 * (((omega p q).val : ℕ) : ZMod 4) := by
    linear_combination h2 - h1
  have key : ∀ u v : ZMod 2, (2 : ZMod 4) * ((u.val : ℕ) : ZMod 4)
      = 2 * ((v.val : ℕ) : ZMod 4) → u = v := by decide +kernel
  exact key _ _ hE

/-! ## The group: strictly associative, the cocycle absorbed -/

instance : One (MetaGate n) :=
  ⟨{ g := LinearEquiv.refl _ _
     c := fun _ => 0
     valid := fun a b => by simp }⟩

instance : Mul (MetaGate n) :=
  ⟨fun x y =>
    { g := y.g.trans x.g
      c := fun p => y.c p + x.c (y.g p)
      valid := fun a b => by
        have h1 := y.valid a b
        have h2 := x.valid (y.g a) (y.g b)
        rw [← map_add] at h2
        simp only [LinearEquiv.trans_apply]
        linear_combination h1 + h2 }⟩

instance : Inv (MetaGate n) :=
  ⟨fun x =>
    { g := x.g.symm
      c := fun p => -(x.c (x.g.symm p))
      valid := fun a b => by
        have h := x.valid (x.g.symm a) (x.g.symm b)
        rw [← map_add] at h
        simp only [LinearEquiv.apply_symm_apply] at h
        linear_combination -h }⟩

@[simp] lemma MetaGate.mul_g (x y : MetaGate n) : (x * y).g = y.g.trans x.g := rfl
@[simp] lemma MetaGate.mul_c (x y : MetaGate n) (p : Pauli n) :
    (x * y).c p = y.c p + x.c (y.g p) := rfl
@[simp] lemma MetaGate.one_g : (1 : MetaGate n).g = LinearEquiv.refl _ _ := rfl
@[simp] lemma MetaGate.one_c (p : Pauli n) : (1 : MetaGate n).c p = 0 := rfl
@[simp] lemma MetaGate.inv_g (x : MetaGate n) : x⁻¹.g = x.g.symm := rfl
@[simp] lemma MetaGate.inv_c (x : MetaGate n) (p : Pauli n) :
    x⁻¹.c p = -(x.c (x.g.symm p)) := rfl

/-- **The extension group.** The multiplication `(x*y).c = y.c + x.c ∘ y.g` is strictly
associative — the metaplectic 2-cocycle is not a defect of this multiplication but absorbed
into it. -/
instance : Group (MetaGate n) where
  mul_assoc x y z := by
    refine MetaGate.ext ?_ ?_
    · exact LinearEquiv.ext fun p => rfl
    · funext p
      simp only [MetaGate.mul_c, MetaGate.mul_g, LinearEquiv.trans_apply]
      ring
  one_mul x := by
    refine MetaGate.ext (LinearEquiv.ext fun p => rfl) ?_
    funext p
    simp only [MetaGate.mul_c, MetaGate.one_c, add_zero]
  mul_one x := by
    refine MetaGate.ext (LinearEquiv.ext fun p => rfl) ?_
    funext p
    simp only [MetaGate.mul_c, MetaGate.one_c, MetaGate.one_g, LinearEquiv.refl_apply, zero_add]
  inv_mul_cancel x := by
    refine MetaGate.ext (LinearEquiv.ext fun p => x.g.symm_apply_apply p) ?_
    funext p
    simp only [MetaGate.mul_c, MetaGate.inv_c, MetaGate.one_c,
      LinearEquiv.symm_apply_apply]
    ring

/-! ## The kernel over `g = 1`: the label torsor -/

/-- The kernel elements: pure sign twists `2·ω(w,·)`. -/
def twistGate (w : Pauli n) : MetaGate n where
  g := LinearEquiv.refl _ _
  c := fun p => ((2 * (omega w p).val : ℕ) : ZMod 4)
  valid := fun a b => by
    have hd : ∀ u v : ZMod 2, ((2 * ((u + v)).val : ℕ) : ZMod 4)
        = ((2 * u.val : ℕ) : ZMod 4) + ((2 * v.val : ℕ) : ZMod 4) := by decide +kernel
    simp only [LinearEquiv.refl_apply]
    rw [omega_add_right, hd]

set_option maxHeartbeats 1000000 in
/-- **The kernel classification**: every additive ℤ/4 cochain is a twist — `2·ω(w,·)` for some
label `w` (unique in effect, by ω-nondegeneracy; not needed here). -/
theorem exists_twist_of_additive (c : Pauli n → ZMod 4)
    (hadd : ∀ a b, c (a + b) = c a + c b) :
    ∃ w : Pauli n, ∀ p, c p = ((2 * (omega w p).val : ℕ) : ZMod 4) := by
  classical
  haveI : FiniteDimensional (ZMod 2) (Pauli n) := inferInstance
  have hc0 : c 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hval : ∀ a, c a = 0 ∨ c a = 2 := by
    intro a
    have h2 : c a + c a = 0 := by
      rw [← hadd, pauli_add_self, hc0]
    have key : ∀ t : ZMod 4, t + t = 0 → t = 0 ∨ t = 2 := by decide +kernel
    exact key _ h2
  -- the induced 𝔽₂ functional
  have hℓadd : ∀ a b, (if c (a + b) = 0 then (0 : ZMod 2) else 1)
      = (if c a = 0 then (0 : ZMod 2) else 1) + (if c b = 0 then (0 : ZMod 2) else 1) := by
    intro a b
    rw [hadd]
    rcases hval a with ha | ha <;> rcases hval b with hb | hb <;> rw [ha, hb] <;> decide +kernel
  let L : Pauli n →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun p => if c p = 0 then (0 : ZMod 2) else 1
      map_add' := hℓadd
      map_smul' := by
        intro r p
        simp only [RingHom.id_apply, smul_eq_mul]
        rcases zmod2_dichot r with hr | hr <;> subst hr
        · rw [zero_smul, zero_mul, if_pos hc0]
        · rw [one_smul, one_mul] }
  have hL : ∀ p, L p = if c p = 0 then (0 : ZMod 2) else 1 := fun _ => rfl
  refine ⟨(LinearMap.BilinForm.toDual omegaBilin (omegaBilin_nondegenerate (n := n))).symm L,
    fun p => ?_⟩
  have hω : omega ((LinearMap.BilinForm.toDual omegaBilin
      (omegaBilin_nondegenerate (n := n))).symm L) p = L p := by
    have h := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := omegaBilin (n := n)) (hB := omegaBilin_nondegenerate) (f := L) (v := p)
    rwa [omegaBilin_apply] at h
  rw [hω, hL]
  rcases hval p with hp | hp <;> rw [hp]
  · rw [if_pos rfl]
    decide +kernel
  · rw [if_neg (by decide)]
    decide +kernel

end FTQCLib.Frame

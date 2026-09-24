/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Cohomology.Cochains

/-! # The Pauli group as the central extension `1 → ℤ/4 → P → V → 1`

The frame cocycle `betaFrame` builds a genuine group: the **Pauli group** `PauliGroup n`, the
central extension of `V = Pauli n` by the phase group `ℤ/4`, with the `betaFrame`-twisted product
`(a,p)·(b,q) = (a + b + β(p,q), p+q)`. Its **associativity is exactly `betaFrame_cocycle`**; the
identity uses `betaFrame`'s vanishing on `0` and inverses use `betaFrame p p = 0`. This is the group
of which `Pauli n` is the quotient — the object the cohomology of the frame classifies. -/

namespace FTQCLib.Cohomology

open FTQCLib FTQCLib.Pauli

variable {n : ℕ}

/-! ## `betaFrame` vanishes on the identity (needed for the unit) -/

theorem betaFrame_zero_left (q : Pauli n) : betaFrame 0 q = 0 := by
  unfold betaFrame
  rw [zero_add, yWeight_zero, X_zero, zDot_zero_right]
  have h4 : (0 + yWeight q + yWeight q + 2 * (0 + zDot q q.X)) = 4 * yWeight q := by
    have : zDot q q.X = yWeight q := rfl
    rw [this]; ring
  rw [h4, Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem betaFrame_zero_right (p : Pauli n) : betaFrame p 0 = 0 := by
  unfold betaFrame
  rw [add_zero, yWeight_zero, zDot_zero_left]
  have h4 : (yWeight p + 0 + yWeight p + 2 * (0 + zDot p p.X)) = 4 * yWeight p := by
    have : zDot p p.X = yWeight p := rfl
    rw [this]; ring
  rw [h4, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-! ## The Pauli group -/

/-- The **Pauli group**: the central extension `ℤ/4 ×_β V` with the `betaFrame`-twisted product.
A phase in `ℤ/4` (the `i`-powers) together with a register element. -/
@[ext] structure PauliGroup (n : ℕ) where
  /-- The `ℤ/4` phase (an `i`-power). -/
  phase : ZMod 4
  /-- The underlying register element (the symplectic data). -/
  base : Pauli n

namespace PauliGroup

instance : Mul (PauliGroup n) :=
  ⟨fun x y => ⟨x.phase + y.phase + betaFrame x.base y.base, x.base + y.base⟩⟩
instance : One (PauliGroup n) := ⟨⟨0, 0⟩⟩
instance : Inv (PauliGroup n) := ⟨fun x => ⟨-x.phase, x.base⟩⟩

@[simp] lemma mul_phase (x y : PauliGroup n) :
    (x * y).phase = x.phase + y.phase + betaFrame x.base y.base := rfl
@[simp] lemma mul_base (x y : PauliGroup n) : (x * y).base = x.base + y.base := rfl
@[simp] lemma one_phase : (1 : PauliGroup n).phase = 0 := rfl
@[simp] lemma one_base : (1 : PauliGroup n).base = 0 := rfl
@[simp] lemma inv_phase (x : PauliGroup n) : x⁻¹.phase = -x.phase := rfl
@[simp] lemma inv_base (x : PauliGroup n) : x⁻¹.base = x.base := rfl

/-- **The Pauli group is a group** — associativity is exactly the 2-cocycle condition
`betaFrame_cocycle`; the unit and inverses come from `betaFrame`'s vanishing on `0` and diagonal. -/
instance : Group (PauliGroup n) :=
  { (inferInstance : Mul (PauliGroup n)), (inferInstance : One (PauliGroup n)),
    (inferInstance : Inv (PauliGroup n)) with
    mul_assoc := by
      rintro x y z
      refine PauliGroup.ext ?_ ?_
      · simp only [mul_phase, mul_base]
        linear_combination -betaFrame_cocycle x.base y.base z.base
      · simp only [mul_base]; rw [add_assoc]
    one_mul := by rintro x; refine PauliGroup.ext ?_ ?_ <;> simp [betaFrame_zero_left]
    mul_one := by rintro x; refine PauliGroup.ext ?_ ?_ <;> simp [betaFrame_zero_right]
    inv_mul_cancel := by
      rintro x; refine PauliGroup.ext ?_ ?_ <;> simp [betaFrame_self, pauli_add_self] }

/-! ## The short exact sequence `1 → ℤ/4 → PauliGroup → V → 1` -/

/-- Inclusion of the `ℤ/4` phase as the central kernel: `a ↦ (a, 0)`. -/
def incl (a : ZMod 4) : PauliGroup n := ⟨a, 0⟩

/-- Projection to the register `V` (the symplectic quotient): `(a,p) ↦ p`. -/
def proj (x : PauliGroup n) : Pauli n := x.base

@[simp] lemma incl_phase (a : ZMod 4) : (incl a : PauliGroup n).phase = a := rfl
@[simp] lemma incl_base (a : ZMod 4) : (incl a : PauliGroup n).base = 0 := rfl
@[simp] lemma proj_apply (x : PauliGroup n) : proj x = x.base := rfl

/-- `incl` is a homomorphism `(ℤ/4, +) → (PauliGroup, ·)`. -/
lemma incl_mul (a b : ZMod 4) : (incl a * incl b : PauliGroup n) = incl (a + b) := by
  refine PauliGroup.ext ?_ ?_ <;> simp [incl]

/-- `incl` is injective — the kernel `ℤ/4` embeds. -/
lemma incl_injective : Function.Injective (incl : ZMod 4 → PauliGroup n) :=
  fun a b h => by simpa [incl] using congrArg PauliGroup.phase h

/-- `proj` is a homomorphism `(PauliGroup, ·) → (V, +)`. -/
lemma proj_mul (x y : PauliGroup n) : proj (x * y) = proj x + proj y := rfl

/-- `proj` is surjective. -/
lemma proj_surjective : Function.Surjective (proj : PauliGroup n → Pauli n) :=
  fun p => ⟨⟨0, p⟩, rfl⟩

/-- **Exactness**: `ker proj = range incl` — an element projects to `0` iff it is a pure phase. -/
lemma proj_eq_zero_iff (x : PauliGroup n) : proj x = 0 ↔ ∃ a, incl a = x := by
  constructor
  · intro h; exact ⟨x.phase, PauliGroup.ext rfl h.symm⟩
  · rintro ⟨a, rfl⟩; rfl

/-- **Centrality**: the image of `incl` is central — this is a *central* extension. -/
lemma incl_central (a : ZMod 4) (y : PauliGroup n) : incl a * y = y * incl a := by
  refine PauliGroup.ext ?_ ?_
  · simp only [mul_phase, incl_phase, incl_base, betaFrame_zero_left, betaFrame_zero_right,
      add_zero]
    ring
  · simp [mul_base, incl_base]

/-! ## The canonical section, and `betaFrame` as the factor set -/

/-- The set-theoretic section `p ↦ (0, p)`. -/
def sec (p : Pauli n) : PauliGroup n := ⟨0, p⟩

@[simp] lemma proj_sec (p : Pauli n) : proj (sec p) = p := rfl

/-- **`betaFrame` is the factor set of the extension** for the canonical section: the failure of
`sec` to be a homomorphism is exactly `incl (betaFrame p q)`. This identifies `[betaFrame]` (the
class `betaClass` of `Cochains.lean`) as the class of the Pauli central extension. -/
lemma sec_mul (p q : Pauli n) : sec p * sec q = incl (betaFrame p q) * sec (p + q) := by
  refine PauliGroup.ext ?_ ?_ <;> simp [sec, incl, betaFrame_zero_left]

end PauliGroup

end FTQCLib.Cohomology

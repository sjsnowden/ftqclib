/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Circuit
import ECCLib.StructureConstants
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Ring

set_option linter.unusedSectionVars false

/-!
# The algebra → gates descent: linear and bilinear maps as netlists

The abstract half of the multiplier construction: everything here is stated for a *based
algebra*, with the concrete `AdjoinRoot` carrier and its computable table arriving separately
(`GateField.lean`).

* **The word layer and totality.** `encW v = fun i => bit (v i)` with its inverse `decW`,
  and `exists_encW_append`: *every* boolean assignment of `n₁ + n₂` wires is the encoding of a
  pair of coordinate words. Without this, a two-argument preservation theorem constrains the
  netlist only on the encoded assignments — a partial specification dressed as a total one.
* **The linear layer.** `linW M = fun k => dotC (M k)`: an `𝔽₂`-matrix as a netlist,
  `evalVec (linW M) (encW x) = encW (M *ᵥ x)`, `sizeVec = p·n`. One line from `eval_dotC`.
* **The flat bilinear netlist.** `bilinNet c`: output `k` is the double XOR fold over
  `(i, j)` of the coefficient-masked AND of left wire `i` and right wire `j` — flat two-level
  emission, never recursive shift-and-add (recursion multiplies the emitted *term* per stage).
* **The general coordinate theorem**, deliberately hypothesis-free and stated over an
  arbitrary commutative base ring: for a basis `B` of an `R`-algebra, with structure constants
  `strConst B i j k = B.repr (B i * B j) k`,
  `B.repr (x*y) k = ∑ᵢ∑ⱼ strConst B i j k · (B.repr x i · B.repr y j)`. No field, no
  irreducibility, no finiteness of `A`, no characteristic. (Mathlib's
  `Algebra.leftMulMatrix_eq_repr_mul` is the external confirmation of the formulation; it is not
  used — `leftMulMatrix` is noncomputable and nothing here needs it.)
* **The abstract multiplier and its relatives.** `mulNet B = bilinNet (strConst B)`:
  multiplication in *any* based `𝔽₂`-algebra descends to an AND/XOR netlist,
  `evalVec_mulNet`. Plus addition (an XOR bus of `m` gates, any basis, via `map_add`) and
  fixed-constant multiplication (`constMulMat`, an instance of the linear layer — zero AND
  gates).

Everything is computable given its data; the noncomputability of any particular basis is the
concrete layer's concern (`GateField.lean` supplies a computable table equal to `strConst` of the
power basis).
-/

namespace ECCLib

open Module Matrix

/-! ## The word layer and totality -/

/-- Encode a coordinate word on the wires. -/
def encW {n : ℕ} (v : Fin n → ZMod 2) : Fin n → Bool := fun i => bit (v i)

/-- Decode the wires to a coordinate word. -/
def decW {n : ℕ} (x : Fin n → Bool) : Fin n → ZMod 2 := fun i => unbit (x i)

@[simp] theorem encW_apply {n : ℕ} (v : Fin n → ZMod 2) (i : Fin n) : encW v i = bit (v i) := rfl

@[simp] theorem decW_encW {n : ℕ} (v : Fin n → ZMod 2) : decW (encW v) = v :=
  funext fun i => unbit_bit (v i)

@[simp] theorem encW_decW {n : ℕ} (x : Fin n → Bool) : encW (decW x) = x :=
  funext fun i => bit_unbit (x i)

/-- **Totality of the two-word encoding**: every assignment of `n₁ + n₂` wires is
`Fin.append (encW v) (encW w)` for a (unique) pair of coordinate words — so preservation
theorems stated on encoded inputs constrain the netlist on *all* inputs. -/
theorem exists_encW_append {n₁ n₂ : ℕ} (x : Fin (n₁ + n₂) → Bool) :
    ∃ v w, x = Fin.append (encW v) (encW w) := by
  refine ⟨decW (fun i => x (Fin.castAdd n₂ i)), decW (fun j => x (Fin.natAdd n₁ j)), ?_⟩
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [Fin.append_left]
    exact (bit_unbit _).symm
  · rw [Fin.append_right]
    exact (bit_unbit _).symm

namespace Circuit

variable {n n₁ n₂ p m : ℕ}

/-! ## The linear layer -/

/-- An `𝔽₂`-matrix as a netlist: one `dotC` row per output. -/
def linW (M : Matrix (Fin p) (Fin n) (ZMod 2)) : CircuitVec n p := fun k => dotC (M k)

/-- **Preservation for the linear layer**: the netlist computes `M *ᵥ x` through the encoding. -/
theorem evalVec_linW (M : Matrix (Fin p) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    evalVec (linW M) (encW x) = encW (M *ᵥ x) := by
  funext k
  change eval (dotC (M k)) (fun i => bit (x i)) = bit ((M *ᵥ x) k)
  rw [eval_dotC]
  congr 1

@[simp] theorem sizeVec_linW (M : Matrix (Fin p) (Fin n) (ZMod 2)) :
    sizeVec (linW M) = p * n := by
  simp [sizeVec, linW]

/-! ## The flat bilinear netlist -/

/-- The **flat two-level bilinear netlist** for a coefficient tensor `c`: output `k` XORs, over
all pairs `(i, j)`, the `c i j k`-masked AND of left wire `i` and right wire `j`. -/
def bilinNet (c : Fin n₁ → Fin n₂ → Fin p → ZMod 2) : CircuitVec (n₁ + n₂) p :=
  fun k => xorFold n₁ (fun i => xorFold n₂ (fun j =>
    if c i j k = 1
    then .and (.wire (Fin.castAdd n₂ i)) (.wire (Fin.natAdd n₁ j))
    else .const false))

/-- **Preservation for the bilinear netlist**: on the two encoded words it computes the bilinear
form `∑ᵢ∑ⱼ c i j k · (v i · w j)`, coordinatewise through the encoding. -/
theorem evalVec_bilinNet (c : Fin n₁ → Fin n₂ → Fin p → ZMod 2)
    (v : Fin n₁ → ZMod 2) (w : Fin n₂ → ZMod 2) :
    evalVec (bilinNet c) (Fin.append (encW v) (encW w))
      = encW (fun k => ∑ i, ∑ j, c i j k * (v i * w j)) := by
  have hz : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  funext k
  refine eval_xorFold _ n₁ _ (fun i => ∑ j, c i j k * (v i * w j)) fun i => ?_
  refine eval_xorFold _ n₂ _ (fun j => c i j k * (v i * w j)) fun j => ?_
  simp only []
  by_cases h : c i j k = 1
  · rw [if_pos h, eval_and, eval_wire, eval_wire, Fin.append_left, Fin.append_right,
      h, one_mul, bit_mul]
    rfl
  · rw [if_neg h, eval_const, hz _ h, zero_mul, bit_zero]

/-- The exact gate count of the bilinear netlist: the fold scaffolding plus one AND per nonzero
coefficient (tree counts, per the model's stated convention). -/
theorem sizeVec_bilinNet (c : Fin n₁ → Fin n₂ → Fin p → ZMod 2) :
    sizeVec (bilinNet c)
      = p * (n₁ + n₁ * n₂) + ∑ k, ∑ i, ∑ j, (if c i j k = 1 then 1 else 0) := by
  have hleaf : ∀ (i : Fin n₁) (j : Fin n₂) (k : Fin p),
      size (if c i j k = 1
        then (Circuit.and (.wire (Fin.castAdd n₂ i)) (.wire (Fin.natAdd n₁ j)) : Circuit (n₁ + n₂))
        else .const false)
      = if c i j k = 1 then 1 else 0 := by
    intro i j k
    split <;> simp
  unfold sizeVec bilinNet
  simp only [size_xorFold, hleaf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

end Circuit

/-! ## The general coordinate theorem

The coordinate theorem lives in `ECCLib/StructureConstants.lean`, which imports only Mathlib.
`strConst`, `repr_mul`, `constMulMat` and `repr_const_mul` are declared in the same `ECCLib`
namespace there, so wanting the coordinate theorem does not mean importing circuit
synthesis. -/

/-! ## The abstract multiplier and its relatives -/

namespace Circuit

variable {m : ℕ} {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- **The abstract multiplier netlist** of a based `𝔽₂`-algebra: the bilinear netlist of its
structure constants. -/
noncomputable def mulNet (B : Basis (Fin m) (ZMod 2) A) : CircuitVec (m + m) m :=
  bilinNet (strConst B)

/-- **The abstract multiplier theorem**: for any based `𝔽₂`-algebra, the netlist computes
multiplication in coordinates, through the encoding. Still generic — the computable table and
the concrete carrier are in `GateField.lean`. -/
theorem evalVec_mulNet (B : Basis (Fin m) (ZMod 2) A) (x y : A) :
    evalVec (mulNet B) (Fin.append (encW fun i => B.repr x i) (encW fun j => B.repr y j))
      = encW (fun k => B.repr (x * y) k) := by
  rw [mulNet, evalVec_bilinNet]
  exact congrArg encW (funext fun k => (repr_mul B x y k).symm)

/-- Coordinate addition as a netlist: the **XOR bus**, one gate per coordinate. -/
def addNet (n : ℕ) : CircuitVec (n + n) n :=
  fun k => .xor (.wire (Fin.castAdd n k)) (.wire (Fin.natAdd n k))

theorem evalVec_addNet {n : ℕ} (v w : Fin n → ZMod 2) :
    evalVec (addNet n) (Fin.append (encW v) (encW w)) = encW (v + w) := by
  funext k
  simp only [evalVec_apply, addNet, eval_xor, eval_wire, Fin.append_left, Fin.append_right]
  exact (bit_add (v k) (w k)).symm

@[simp] theorem sizeVec_addNet (n : ℕ) : sizeVec (addNet n) = n := by
  simp [sizeVec, addNet]

/-- Addition in any based algebra descends to the XOR bus — `B.repr` is additive. -/
theorem evalVec_addNet_repr (B : Basis (Fin m) (ZMod 2) A) (x y : A) :
    evalVec (addNet m) (Fin.append (encW fun i => B.repr x i) (encW fun j => B.repr y j))
      = encW (fun k => B.repr (x + y) k) := by
  rw [evalVec_addNet]
  refine congrArg encW (funext fun k => ?_)
  rw [map_add, Finsupp.add_apply]
  rfl

/-- Multiplication by a fixed constant descends to the **linear** layer — zero AND gates. -/
theorem evalVec_constMulNet (B : Basis (Fin m) (ZMod 2) A) (a x : A) :
    evalVec (linW (constMulMat B a)) (encW fun i => B.repr x i)
      = encW (fun k => B.repr (a * x) k) := by
  rw [evalVec_linW]
  refine congrArg encW (funext fun k => ?_)
  rw [repr_const_mul]
  simp [Matrix.mulVec, dotProduct]

end Circuit

end ECCLib

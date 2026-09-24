/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

set_option linter.unusedSectionVars false

/-! # Pauli group on `n` qubits (modulo phase)

We work in the standard binary symplectic representation of the Pauli group
on `n` qubits, modulo phase. An element of `FTQCLib.Pauli n` records two binary
vectors: `X : Fin n → ZMod 2` (the X-support) and `Z : Fin n → ZMod 2`
(the Z-support). The pair represents the operator

    X^X · Z^Z = (X_1^{X_1} ... X_n^{X_n}) · (Z_1^{Z_1} ... Z_n^{Z_n})

up to a phase in `{±1, ±i}`. Phases are factored out; for stabilizer-code
reasoning they reappear only as the sign carried by the symplectic form
(`omega` in `FTQCLib.Pauli.Symplectic`).

As an abelian group under componentwise addition, `FTQCLib.Pauli n` is
isomorphic to `(ZMod 2)^{2n}`, of order `4^n`. We define `Pauli` as a
`structure` with explicit `X` and `Z` fields rather than as an
abbreviation for `(Fin n → ZMod 2) × (Fin n → ZMod 2)`: the structure form
registers `Module (ZMod 2) (Pauli n)` as a direct instance lookup instead
of a cascade through `Prod.module` + `Pi.module`, which avoids elaborator
timeouts when packaging `omega` as a `LinearMap.BilinForm`.

This file defines `FTQCLib.Pauli` and its `(ZMod 2)`-module structure. The
symplectic form lives in `FTQCLib.Pauli.Symplectic`.
-/

/-- The Pauli group on `n` qubits, modulo phase. An element has two
binary-vector fields: `X` records which qubits have an `X` factor (the
X-support), and `Z` records which have a `Z` factor. A qubit with both an
`X` and a `Z` factor carries a `Y` (modulo phase). -/
@[ext]
structure FTQCLib.Pauli (n : ℕ) where
  X : Fin n → ZMod 2
  Z : Fin n → ZMod 2

namespace FTQCLib.Pauli

variable {n : ℕ}

instance : Zero (Pauli n) := ⟨⟨0, 0⟩⟩

@[simp] lemma X_zero : (0 : Pauli n).X = 0 := rfl
@[simp] lemma Z_zero : (0 : Pauli n).Z = 0 := rfl

instance : Add (Pauli n) := ⟨fun p q => ⟨p.X + q.X, p.Z + q.Z⟩⟩

@[simp] lemma X_add (p q : Pauli n) : (p + q).X = p.X + q.X := rfl
@[simp] lemma Z_add (p q : Pauli n) : (p + q).Z = p.Z + q.Z := rfl

instance : Neg (Pauli n) := ⟨fun p => ⟨-p.X, -p.Z⟩⟩

@[simp] lemma X_neg (p : Pauli n) : (-p).X = -p.X := rfl
@[simp] lemma Z_neg (p : Pauli n) : (-p).Z = -p.Z := rfl

instance : Sub (Pauli n) := ⟨fun p q => ⟨p.X - q.X, p.Z - q.Z⟩⟩

@[simp] lemma X_sub (p q : Pauli n) : (p - q).X = p.X - q.X := rfl
@[simp] lemma Z_sub (p q : Pauli n) : (p - q).Z = p.Z - q.Z := rfl

instance : SMul (ZMod 2) (Pauli n) := ⟨fun c p => ⟨c • p.X, c • p.Z⟩⟩

@[simp] lemma X_smul (c : ZMod 2) (p : Pauli n) : (c • p).X = c • p.X := rfl
@[simp] lemma Z_smul (c : ZMod 2) (p : Pauli n) : (c • p).Z = c • p.Z := rfl

/-- `Pauli n` is an abelian group under componentwise addition. The axioms
descend from the underlying `Fin n → ZMod 2` structure. -/
instance : AddCommGroup (Pauli n) where
  add_assoc p q r := by ext <;> simp [add_assoc]
  zero_add p := by ext <;> simp
  add_zero p := by ext <;> simp
  add_comm p q := by ext <;> simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel p := by
    ext i
    · change (-p).X i + p.X i = (0 : Pauli n).X i
      simp only [X_neg, Pi.neg_apply, X_zero, Pi.zero_apply]
      exact neg_add_cancel _
    · change (-p).Z i + p.Z i = (0 : Pauli n).Z i
      simp only [Z_neg, Pi.neg_apply, Z_zero, Pi.zero_apply]
      exact neg_add_cancel _
  sub_eq_add_neg p q := by ext <;> simp [sub_eq_add_neg]

/-- `Pauli n` is a `(ZMod 2)`-module via componentwise scalar action. -/
instance : Module (ZMod 2) (Pauli n) where
  one_smul p := by ext <;> simp
  mul_smul c d p := by ext <;> simp [mul_assoc]
  smul_zero c := by ext <;> simp
  smul_add c p q := by ext <;> simp [mul_add]
  add_smul c d p := by ext <;> simp [add_mul]
  zero_smul p := by ext <;> simp

/-- Linear isomorphism between `Pauli n` and `(Fin n → ZMod 2) × (Fin n → ZMod 2)`.
Used to transfer finite-dimensionality and other module properties from the
underlying Prod-of-Pi representation. -/
def linearEquivProd : Pauli n ≃ₗ[ZMod 2] ((Fin n → ZMod 2) × (Fin n → ZMod 2)) where
  toFun p := (p.X, p.Z)
  invFun pq := ⟨pq.1, pq.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : Module.Finite (ZMod 2) (Pauli n) :=
  Module.Finite.equiv linearEquivProd.symm

/-! The canonical `DecidableEq`/`Fintype` instances live here, at the type's home, so
that every module uses the same instances: a module importing two separately declared
copies would face an instance diamond, to which `Finset.univ.filter` computations are
sensitive. -/

instance instDecidableEq : DecidableEq (Pauli n) := fun p q =>
  decidable_of_iff (p.X = q.X ∧ p.Z = q.Z)
    ⟨fun h => Pauli.ext h.1 h.2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

instance instFintype : Fintype (Pauli n) :=
  Fintype.ofEquiv ((Fin n → ZMod 2) × (Fin n → ZMod 2))
    { toFun := fun xz => ⟨xz.1, xz.2⟩
      invFun := fun p => (p.X, p.Z)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The X-projection commutes with Finset.sum. -/
theorem X_finsetSum {α : Type*} (s : Finset α) (f : α → Pauli n) :
    (∑ i ∈ s, f i).X = ∑ i ∈ s, (f i).X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, X_add, ih]

/-- The Z-projection commutes with Finset.sum. -/
theorem Z_finsetSum {α : Type*} (s : Finset α) (f : α → Pauli n) :
    (∑ i ∈ s, f i).Z = ∑ i ∈ s, (f i).Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Z_add, ih]

end FTQCLib.Pauli

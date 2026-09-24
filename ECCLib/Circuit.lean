/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Boolean circuits and the characteristic-2 descent

The gate-level target of the certified-extraction layer: a boolean circuit model with a
denotational semantics, and the descent of `𝔽₂` arithmetic onto it.

* **`Circuit n`** — circuits over `n` input wires, gate set `XOR`, `AND`, `NOT` + constants and
  wires (functionally complete, and the set the descent's specification names). `eval` is the
  denotation `(Fin n → Bool) → Bool`; `size` counts gates, wires and constants free.
  `CircuitVec n m = Fin m → Circuit n` is a netlist with `m` outputs.
* **`bit : ZMod 2 ≃ Bool`** (`bitEquiv`) — the field encoding at `q = 2`, with
  `bit_add : bit (a + b) = xor (bit a) (bit b)` and `bit_mul : bit (a * b) = bit a && bit b`.
  Mathlib has no such bridge, so it is built here.
* **`addC` / `mulC`** — field addition and multiplication as **one gate each** (`size = 1`), with
  preservation theorems. This is the base case of the descent: at characteristic 2 the encoding
  is the identity on bits and addition is XOR.
* **`xorFold`** — the reusable fold: *if each subcircuit computes `bit (v i)`, the fold computes
  `bit (∑ i, v i)`* (`eval_xorFold`), with `size_xorFold : size = n + ∑ size (g i)`. Its two
  instantiations are `parityC` (an `𝔽₂`-linear functional as an XOR tree) and `dotC a` (a
  fixed-coefficient dot product) — the primitive a row-by-row compiler consumes.

**Scope, stated rather than hidden.** `Circuit` is a *tree*, so `size` counts gates without
sharing: it is an upper bound on a real netlist's gate count, not the DAG count. Relatedly the
fold emits `n` XOR gates where `n − 1` suffice (the uniform `const false` base costs one gate,
constant-foldable). Neither affects any preservation theorem, only the counts; core Lean's
hash-consed `Std.Sat.AIG` is the natural bridge target for genuine sharing and for CNF/LRAT
certificates.
-/

namespace ECCLib

/-! ## The field encoding at `q = 2` -/

/-- The **bit encoding** of `𝔽₂`. -/
def bit (a : ZMod 2) : Bool := decide (a = 1)

@[simp] theorem bit_zero : bit 0 = false := by decide

@[simp] theorem bit_one : bit 1 = true := by decide

/-- **Addition is XOR.** -/
theorem bit_add (a b : ZMod 2) : bit (a + b) = Bool.xor (bit a) (bit b) := by
  revert a b; decide

/-- **Multiplication is AND.** -/
theorem bit_mul (a b : ZMod 2) : bit (a * b) = (bit a && bit b) := by
  revert a b; decide

theorem bit_injective : Function.Injective bit := by decide

/-- The inverse encoding, `Bool → 𝔽₂`. -/
def unbit (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem unbit_bit (a : ZMod 2) : unbit (bit a) = a := by revert a; decide

@[simp] theorem bit_unbit (b : Bool) : bit (unbit b) = b := by revert b; decide

/-- The encoding as an equivalence — `𝔽₂ ≃ Bool`, the `q = 2` case of the field encoding the
descent's specification asks for. -/
def bitEquiv : ZMod 2 ≃ Bool where
  toFun := bit
  invFun b := if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

/-! ## The circuit model -/

/-- A **boolean circuit** over `n` input wires. -/
inductive Circuit (n : ℕ) : Type where
  | wire (i : Fin n) : Circuit n
  | const (b : Bool) : Circuit n
  | not (c : Circuit n) : Circuit n
  | and (c d : Circuit n) : Circuit n
  | xor (c d : Circuit n) : Circuit n
  deriving DecidableEq, Repr

namespace Circuit

variable {n m : ℕ}

/-- The **denotational semantics** of a circuit. -/
def eval : Circuit n → (Fin n → Bool) → Bool
  | .wire i, x => x i
  | .const b, _ => b
  | .not c, x => !(eval c x)
  | .and c d, x => (eval c x) && (eval d x)
  | .xor c d, x => Bool.xor (eval c x) (eval d x)

@[simp] theorem eval_wire (i : Fin n) (x : Fin n → Bool) : eval (.wire i) x = x i := rfl
@[simp] theorem eval_const (b : Bool) (x : Fin n → Bool) : eval (.const b) x = b := rfl
@[simp] theorem eval_not (c : Circuit n) (x : Fin n → Bool) :
    eval (.not c) x = !(eval c x) := rfl
@[simp] theorem eval_and (c d : Circuit n) (x : Fin n → Bool) :
    eval (.and c d) x = ((eval c x) && (eval d x)) := rfl
@[simp] theorem eval_xor (c d : Circuit n) (x : Fin n → Bool) :
    eval (.xor c d) x = Bool.xor (eval c x) (eval d x) := rfl

/-- The **gate count**: wires and constants are free, each gate costs one. -/
def size : Circuit n → ℕ
  | .wire _ => 0
  | .const _ => 0
  | .not c => size c + 1
  | .and c d => size c + size d + 1
  | .xor c d => size c + size d + 1

@[simp] theorem size_wire (i : Fin n) : size (.wire i : Circuit n) = 0 := rfl
@[simp] theorem size_const (b : Bool) : size (.const b : Circuit n) = 0 := rfl
@[simp] theorem size_not (c : Circuit n) : size (.not c) = size c + 1 := rfl
@[simp] theorem size_and (c d : Circuit n) : size (.and c d) = size c + size d + 1 := rfl
@[simp] theorem size_xor (c d : Circuit n) : size (.xor c d) = size c + size d + 1 := rfl

/-! ## Netlists with several outputs -/

/-- A **netlist**: `m` single-output circuits over the same `n` wires. -/
abbrev CircuitVec (n m : ℕ) := Fin m → Circuit n

/-- The semantics of a netlist, output by output. -/
def evalVec (cv : CircuitVec n m) (x : Fin n → Bool) : Fin m → Bool := fun j => eval (cv j) x

/-- The netlist's total gate count. -/
def sizeVec (cv : CircuitVec n m) : ℕ := ∑ j, size (cv j)

@[simp] theorem evalVec_apply (cv : CircuitVec n m) (x : Fin n → Bool) (j : Fin m) :
    evalVec cv x j = eval (cv j) x := rfl

/-! ## `𝔽₂` arithmetic is one gate per operation -/

/-- Field addition as a circuit: **one XOR gate**. -/
def addC : Circuit 2 := .xor (.wire 0) (.wire 1)

/-- Field multiplication as a circuit: **one AND gate**. -/
def mulC : Circuit 2 := .and (.wire 0) (.wire 1)

/-- **Preservation for addition**: the circuit computes the field sum through the encoding. -/
theorem eval_addC (x : Fin 2 → ZMod 2) :
    eval addC (fun i => bit (x i)) = bit (x 0 + x 1) := by
  simp [addC, bit_add]

/-- **Preservation for multiplication.** -/
theorem eval_mulC (x : Fin 2 → ZMod 2) :
    eval mulC (fun i => bit (x i)) = bit (x 0 * x 1) := by
  simp [mulC, bit_mul]

@[simp] theorem size_addC : size addC = 1 := rfl
@[simp] theorem size_mulC : size mulC = 1 := rfl

/-! ## Input renaming -/

/-- Rename the input wires along `f`. -/
def mapInputs (f : Fin n → Fin m) : Circuit n → Circuit m
  | .wire i => .wire (f i)
  | .const b => .const b
  | .not c => .not (mapInputs f c)
  | .and c d => .and (mapInputs f c) (mapInputs f d)
  | .xor c d => .xor (mapInputs f c) (mapInputs f d)

@[simp] theorem eval_mapInputs (f : Fin n → Fin m) (c : Circuit n) (x : Fin m → Bool) :
    eval (mapInputs f c) x = eval c (fun i => x (f i)) := by
  induction c <;> simp [mapInputs, *]

@[simp] theorem size_mapInputs (f : Fin n → Fin m) (c : Circuit n) :
    size (mapInputs f c) = size c := by
  induction c <;> simp [mapInputs, *]

/-! ## Substitution — composing one netlist into another

`mapInputs` renames wires; it cannot feed one circuit's *outputs* into another's inputs. `subst`
does, and it is what makes a multi-stage datapath expressible at all (the two-stage decoder — a
syndrome stage followed by a coset-leader stage — is the first consumer). -/

/-- Substitute a circuit for each input wire. -/
def subst : Circuit n → (Fin n → Circuit p) → Circuit p
  | .wire i, σ => σ i
  | .const b, _ => .const b
  | .not c, σ => .not (subst c σ)
  | .and c d, σ => .and (subst c σ) (subst d σ)
  | .xor c d, σ => .xor (subst c σ) (subst d σ)

/-- **Compositionality of the semantics**: substituting circuits for wires is evaluating the outer
circuit at the inner circuits' values. -/
@[simp] theorem eval_subst (c : Circuit n) (σ : Fin n → Circuit p) (x : Fin p → Bool) :
    eval (subst c σ) x = eval c (fun i => eval (σ i) x) := by
  induction c <;> simp [subst, *]

/-- How many times wire `i` occurs as a leaf — the multiplicity with which a substituted circuit is
duplicated in a tree model. -/
def leafCount : Circuit n → Fin n → ℕ
  | .wire i, j => if i = j then 1 else 0
  | .const _, _ => 0
  | .not c, j => leafCount c j
  | .and c d, j => leafCount c j + leafCount d j
  | .xor c d, j => leafCount c j + leafCount d j

/-- The exact gate count of a substitution: each substituted circuit is paid for once per leaf.
(In a tree model there is no sharing, so this counts the duplication exactly rather than hiding
it — see the file header.) -/
theorem size_subst (c : Circuit n) (σ : Fin n → Circuit p) :
    size (subst c σ) = size c + ∑ i, leafCount c i * size (σ i) := by
  induction c with
  | wire i => simp [subst, leafCount]
  | const b => simp [subst, leafCount]
  | not c ih =>
      simp only [subst, size_not, leafCount, ih]
      omega
  | and c d ihc ihd =>
      simp only [subst, size_and, leafCount, ihc, ihd, Nat.add_mul, Finset.sum_add_distrib]
      omega
  | xor c d ihc ihd =>
      simp only [subst, size_xor, leafCount, ihc, ihd, Nat.add_mul, Finset.sum_add_distrib]
      omega

/-! ## The XOR fold — the compiler's summation primitive -/

/-- XOR together `n` subcircuits over the same wires. -/
def xorFold : (n : ℕ) → (Fin n → Circuit m) → Circuit m
  | 0, _ => .const false
  | n + 1, g => .xor (g (Fin.last n)) (xorFold n (fun i => g i.castSucc))

/-- **The fold's preservation theorem**: if each subcircuit computes the bit of `v i`, the fold
computes the bit of `∑ i, v i`. This is the statement a row-by-row compiler consumes. -/
theorem eval_xorFold (x : Fin m → Bool) :
    ∀ (n : ℕ) (g : Fin n → Circuit m) (v : Fin n → ZMod 2),
      (∀ i, eval (g i) x = bit (v i)) → eval (xorFold n g) x = bit (∑ i, v i)
  | 0, _, _, _ => by simp [xorFold]
  | n + 1, g, v, h => by
    have ih := eval_xorFold x n (fun i => g i.castSucc) (fun i => v i.castSucc)
      (fun i => h i.castSucc)
    simp only [xorFold, eval_xor, ih, h (Fin.last n)]
    rw [← bit_add, Fin.sum_univ_castSucc, add_comm]

theorem size_xorFold : ∀ (n : ℕ) (g : Fin n → Circuit m),
    size (xorFold n g) = n + ∑ i, size (g i)
  | 0, _ => by simp [xorFold]
  | n + 1, g => by
    simp only [xorFold, size_xor, size_xorFold n]
    rw [Fin.sum_univ_castSucc]
    omega

/-! ## Linear functionals over `𝔽₂` -/

/-- The **parity circuit**: an XOR tree over all `n` wires. -/
def parityC (n : ℕ) : Circuit n := xorFold n (fun i => .wire i)

/-- **An `𝔽₂`-linear functional descends to an XOR tree.** -/
theorem eval_parityC (n : ℕ) (x : Fin n → ZMod 2) :
    eval (parityC n) (fun i => bit (x i)) = bit (∑ i, x i) :=
  eval_xorFold _ n _ x (fun _ => rfl)

@[simp] theorem size_parityC (n : ℕ) : size (parityC n) = n := by
  simp [parityC, size_xorFold]

/-- The **dot-product circuit** for a fixed coefficient vector: mask the wires by `a`, then fold.
This is the primitive that compiles one row of an `𝔽₂`-linear map. -/
def dotC (a : Fin n → ZMod 2) : Circuit n :=
  xorFold n (fun i => if a i = 1 then .wire i else .const false)

/-- **Preservation for a linear form**: the circuit computes `∑ i, a i * x i` through the
encoding. -/
theorem eval_dotC (a x : Fin n → ZMod 2) :
    eval (dotC a) (fun i => bit (x i)) = bit (∑ i, a i * x i) := by
  have hz : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  refine eval_xorFold _ n _ (fun i => a i * x i) (fun i => ?_)
  by_cases h : a i = 1
  · simp [h]
  · simp [hz (a i) h]

@[simp] theorem size_dotC (a : Fin n → ZMod 2) : size (dotC a) = n := by
  have h : ∀ i, size (if a i = 1 then (.wire i : Circuit n) else .const false) = 0 := by
    intro i; split <;> simp
  simp [dotC, size_xorFold, h]

/-! ## Tabulation — every boolean function of few wires is a netlist

Functional completeness, constructively, by Shannon expansion on the first wire. The size is
exponential in the wire count, which is exactly right for a narrow lookup — a table indexed by a
*syndrome* — and exactly wrong for a wide datapath. So this is a primitive to reach for
deliberately, and the size bound below is the exact statement of where it stops being usable. -/

/-- The netlist computing an arbitrary boolean function of `k` wires. -/
def tabC : (k : ℕ) → ((Fin k → Bool) → Bool) → Circuit k
  | 0, f => .const (f Fin.elim0)
  | k + 1, f =>
      .xor (.and (.not (.wire 0)) (mapInputs Fin.succ (tabC k (fun y => f (Fin.cons false y)))))
           (.and (.wire 0) (mapInputs Fin.succ (tabC k (fun y => f (Fin.cons true y)))))

/-- **Tabulation is correct**: the emitted netlist computes the function it was built from. -/
theorem eval_tabC : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool) (x : Fin k → Bool),
    eval (tabC k f) x = f x
  | 0, f, x => by
      have hx : x = Fin.elim0 := funext fun i => i.elim0
      simp [tabC, hx]
  | k + 1, f, x => by
      have hcons : ∀ b : Bool, x 0 = b → f (Fin.cons b (fun i : Fin k => x i.succ)) = f x := by
        intro b hb
        congr 1
        rw [← hb]
        exact Fin.cons_self_tail x
      simp only [tabC, eval_xor, eval_and, eval_not, eval_wire, eval_mapInputs, eval_tabC k]
      cases hb : x 0
      · simp [hcons false hb]
      · simp [hcons true hb]

/-- The gate count of a tabulated function: `4·(2^k − 1)`, stated subtraction-free. Exponential in
the wire count — the boundary condition on this primitive. -/
theorem size_tabC : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool), size (tabC k f) + 4 ≤ 4 * 2 ^ k
  | 0, _ => by simp [tabC]
  | k + 1, f => by
      have h0 := size_tabC k (fun y => f (Fin.cons false y))
      have h1 := size_tabC k (fun y => f (Fin.cons true y))
      have hp : (4 : ℕ) * 2 ^ (k + 1) = 4 * 2 ^ k + 4 * 2 ^ k := by
        rw [pow_succ]
        omega
      simp only [tabC, size_xor, size_and, size_not, size_wire, size_mapInputs]
      omega

theorem size_tabC_le (k : ℕ) (f : (Fin k → Bool) → Bool) : size (tabC k f) ≤ 4 * 2 ^ k := by
  have := size_tabC k f
  omega

end Circuit

end ECCLib

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GateAlgebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

set_option linter.unusedSectionVars false

/-!
# The computable model, the `AdjoinRoot` carrier, and GF(16)

The concrete half of the multiplier construction, joining `GateAlgebra`'s abstract theorem to a
computable, printable netlist:

* **The computable coordinate model**, at dimension `m + 1` in the `Fin.cons` phrasing (no
  `Fin.last` arithmetic, no mod-`m` subtraction, ℕ-valued table exponent so the wrap-around
  hazard is structurally avoided): `xtimeVec`, `powVec`, `tbl`, `mulVecC`.
  All computable — this is the layer that prints and `decide`s.
* **The crux lemma** `emb_xtimeVec`: under the single relation
  `α^(m+1) = ∑ᵢ r i • α^i`, the shift-and-reduce step tracks multiplication by `α` through the
  evaluation `emb α v = ∑ᵢ v i • α^i`.
* **The crossing equations**: `emb_powVec` (`emb (powVec r n) = α^n`), `emb_mulVecC`
  (`emb (mulVecC r v w) = emb v * emb w`), and **`strConst_eq_tbl`** — for any basis whose
  elements are the powers of `α`, the abstract structure constants ARE the computable table.
  This single equation is the whole computable/noncomputable interface; `mulNet_eq_bilinNet_tbl`
  then says the certified abstract multiplier IS the printable netlist.
* **The carrier with no irreducibility**: `ν = X^(m+1) + ∑ᵢ C (r i)·Xⁱ` is monic outright,
  so `AdjoinRoot ν` carries the power basis (`adjBasis`) and the relation (`root_pow_top`) for
  every `m` and every reduction word — the entire multiplier stack, `m = 8` included, has zero
  irreducibility content. The char-2 move: `a + S = 0` and `S + S = 0` give `a = S` by
  cancellation, so no `CharP` instance and no negation juggling is needed.
* **GF(16) with a named polynomial**: `ν₄ = X⁴+X³+X²+X+1` is the 5th cyclotomic
  polynomial over `𝔽₂`, irreducible since `ord₅(2) = 4 = φ(5)`; with `Fact (Irreducible ν₄)`,
  `AdjoinRoot ν₄` is a genuine field — the full conjunction (computable netlist + named `ν` +
  field) holds at one concrete parameter. Caveat: the root of `Φ₅` has order 5, not
  15 — fine for multiplication, not a primitive element.
* **Worked examples**, in-file: the m=4
  anchors and gate count (105), a live `α·α⁴ = α⁵ = 1` netlist run, model commutativity on all
  256 pairs, and the m=8 rows — the AES reduction, the worst table entry, and the 727-gate
  count — by kernel `decide` directly on the Pi model (measured: the worst single
  coordinate costs 397 heartbeats in the kernel; the interpreter's slowness on the Pi model
  does not transfer to the kernel).
-/

namespace ECCLib

open Module Polynomial

variable {m : ℕ}

/-! ## The computable coordinate model -/

/-- Multiplication by `α` on coordinates: shift up, reduce the overflow by the word `r`. -/
def xtimeVec (r v : Fin (m + 1) → ZMod 2) : Fin (m + 1) → ZMod 2 :=
  fun k => (Fin.cons (0 : ZMod 2) (fun i : Fin m => v i.castSucc) : Fin (m + 1) → ZMod 2) k
    + v (Fin.last m) * r k

/-- The coordinates of `α^n`, by iterated `xtimeVec` from `1`. -/
def powVec (r : Fin (m + 1) → ZMod 2) : ℕ → Fin (m + 1) → ZMod 2
  | 0 => Fin.cons 1 0
  | n + 1 => xtimeVec r (powVec r n)

/-- The **computable multiplication table**: the coordinates of `α^(i+j)`. The exponent is
ℕ-valued — `(i + j : Fin _)` would silently wrap mod `m + 1` and make `tbl_spec` unprovable. -/
def tbl (r : Fin (m + 1) → ZMod 2) (i j : Fin (m + 1)) : Fin (m + 1) → ZMod 2 :=
  powVec r ((i : ℕ) + (j : ℕ))

/-- The computable reference multiplier on coordinates. -/
def mulVecC (r : Fin (m + 1) → ZMod 2) (v w : Fin (m + 1) → ZMod 2) : Fin (m + 1) → ZMod 2 :=
  fun k => ∑ i, ∑ j, tbl r i j k * (v i * w j)

/-! ## The evaluation and the crossing equations -/

section Emb

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- Evaluate a coordinate word at `α`. -/
def emb (α : A) (v : Fin (m + 1) → ZMod 2) : A := ∑ i, v i • α ^ (i : ℕ)

variable (r : Fin (m + 1) → ZMod 2) (α : A)

/-- **The crux lemma**: under the reduction relation, `xtimeVec` tracks multiplication by `α`. -/
theorem emb_xtimeVec (hα : α ^ (m + 1) = ∑ i, r i • α ^ (i : ℕ))
    (v : Fin (m + 1) → ZMod 2) :
    emb α (xtimeVec r v) = α * emb α v := by
  unfold emb xtimeVec
  simp only [add_smul]
  rw [Finset.sum_add_distrib, Fin.sum_univ_succ, Fin.cons_zero, zero_smul, zero_add]
  simp only [Fin.cons_succ]
  have hsum2 : (∑ k : Fin (m + 1), (v (Fin.last m) * r k) • α ^ (k : ℕ))
      = v (Fin.last m) • α ^ (m + 1) := by
    rw [hα, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
  rw [hsum2, Finset.mul_sum]
  have hterm : ∀ i : Fin (m + 1), α * (v i • α ^ (i : ℕ)) = v i • α ^ ((i : ℕ) + 1) :=
    fun i => by rw [mul_smul_comm, ← pow_succ']
  simp only [hterm]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]

/-- `powVec` computes the powers of `α`, through the evaluation. -/
theorem emb_powVec (hα : α ^ (m + 1) = ∑ i, r i • α ^ (i : ℕ)) (n : ℕ) :
    emb α (powVec r n) = α ^ n := by
  induction n with
  | zero => simp [emb, powVec, Fin.sum_univ_succ]
  | succ n ih =>
      change emb α (xtimeVec r (powVec r n)) = α ^ (n + 1)
      rw [emb_xtimeVec r α hα, ih, ← pow_succ']

/-- **The computable multiplier is multiplication**, through the evaluation. -/
theorem emb_mulVecC (hα : α ^ (m + 1) = ∑ i, r i • α ^ (i : ℕ))
    (v w : Fin (m + 1) → ZMod 2) :
    emb α (mulVecC r v w) = emb α v * emb α w := by
  unfold emb mulVecC
  simp only [Finset.sum_smul]
  calc ∑ k, ∑ i, ∑ j, (tbl r i j k * (v i * w j)) • α ^ (k : ℕ)
      = ∑ i, ∑ j, ∑ k, (tbl r i j k * (v i * w j)) • α ^ (k : ℕ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, (v i * w j) • α ^ ((i : ℕ) + (j : ℕ)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have h : (∑ k, (tbl r i j k * (v i * w j)) • α ^ (k : ℕ))
            = (v i * w j) • ∑ k, tbl r i j k • α ^ (k : ℕ) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [mul_comm, mul_smul]
        rw [h]
        congr 1
        exact emb_powVec r α hα ((i : ℕ) + (j : ℕ))
    _ = (∑ i, v i • α ^ (i : ℕ)) * (∑ j, w j • α ^ (j : ℕ)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_smul_comm, pow_add]

/-- **The crossing equation**: for any basis whose elements are the powers of `α`, the abstract
structure constants ARE the computable table. Everything above this line is algebra; everything
below it prints. -/
theorem strConst_eq_tbl (B : Basis (Fin (m + 1)) (ZMod 2) A)
    (hB : ∀ i, B i = α ^ (i : ℕ)) (hα : α ^ (m + 1) = ∑ i, r i • α ^ (i : ℕ))
    (i j k : Fin (m + 1)) :
    strConst B i j k = tbl r i j k := by
  unfold strConst
  rw [hB i, hB j, ← pow_add, ← emb_powVec r α hα ((i : ℕ) + (j : ℕ))]
  unfold emb
  simp only [← hB]
  rw [Basis.repr_sum_self]
  rfl

/-- **The certified abstract multiplier IS the printable netlist.** -/
theorem mulNet_eq_bilinNet_tbl (B : Basis (Fin (m + 1)) (ZMod 2) A)
    (hB : ∀ i, B i = α ^ (i : ℕ)) (hα : α ^ (m + 1) = ∑ i, r i • α ^ (i : ℕ)) :
    Circuit.mulNet B = Circuit.bilinNet (fun i j k => tbl r i j k) := by
  unfold Circuit.mulNet
  congr 1
  funext i j k
  exact strConst_eq_tbl r α B hB hα i j k

end Emb

/-! ## The `AdjoinRoot` carrier, `Monic` only -/

section Carrier

variable (m : ℕ) (r : Fin (m + 1) → ZMod 2)

/-- The reduction polynomial `ν = X^(m+1) + ∑ᵢ C (r i)·Xⁱ` — monic by construction, no
irreducibility anywhere in this section. -/
noncomputable def nu : Polynomial (ZMod 2) :=
  X ^ (m + 1) + ∑ i : Fin (m + 1), C (r i) * X ^ (i : ℕ)

theorem nu_monic : (nu m r).Monic :=
  monic_X_pow_add (degree_sum_fin_lt r)

theorem nu_natDegree : (nu m r).natDegree = m + 1 := by
  have hlt : (∑ i : Fin (m + 1), C (r i) * X ^ (i : ℕ)).degree
      < (X ^ (m + 1) : Polynomial (ZMod 2)).degree := by
    rw [degree_X_pow]
    exact degree_sum_fin_lt r
  have h : (nu m r).degree = ((m + 1 : ℕ) : WithBot ℕ) := by
    unfold nu
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  exact natDegree_eq_of_degree_eq_some h

/-- The power basis of the quotient, reindexed to the model dimension. -/
noncomputable def adjBasis : Basis (Fin (m + 1)) (ZMod 2) (AdjoinRoot (nu m r)) :=
  (AdjoinRoot.powerBasis' (nu_monic m r)).basis.reindex (finCongr (nu_natDegree m r))

theorem adjBasis_apply (i : Fin (m + 1)) :
    adjBasis m r i = (AdjoinRoot.root (nu m r)) ^ (i : ℕ) := by
  have h := (AdjoinRoot.powerBasis' (nu_monic m r)).basis_eq_pow
    ((finCongr (nu_natDegree m r)).symm i)
  unfold adjBasis
  rw [Basis.reindex_apply]
  refine h.trans ?_
  rw [AdjoinRoot.powerBasis'_gen]
  rfl

/-- **The reduction relation holds at the root** — proved with the char-2 cancellation move
(`a + S = 0` and `S + S = 0` give `a = S`), so no `CharP` instance is needed. -/
theorem root_pow_top :
    (AdjoinRoot.root (nu m r)) ^ (m + 1)
      = ∑ i : Fin (m + 1), r i • (AdjoinRoot.root (nu m r)) ^ (i : ℕ) := by
  set α := AdjoinRoot.root (nu m r) with hαdef
  have heval : (aeval α) (nu m r)
      = α ^ (m + 1) + ∑ i : Fin (m + 1), r i • α ^ (i : ℕ) := by
    unfold nu
    rw [map_add, map_pow, aeval_X, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, ← Algebra.smul_def]
  have hzero : (aeval α) (nu m r) = 0 := by
    rw [hαdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hadd : α ^ (m + 1) + (∑ i : Fin (m + 1), r i • α ^ (i : ℕ)) = 0 :=
    heval.symm.trans hzero
  have hSS : (∑ i : Fin (m + 1), r i • α ^ (i : ℕ)) + (∑ i : Fin (m + 1), r i • α ^ (i : ℕ))
      = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_smul, (by decide : ∀ a : ZMod 2, a + a = 0) (r i), zero_smul]
  exact add_right_cancel (hadd.trans hSS.symm)

/-- The whole stack at the carrier: **the abstract multiplier of `AdjoinRoot ν` is the
computable netlist of its reduction word** — for every `m` and every `r`, `m = 8` included,
with zero irreducibility content. -/
theorem mulNet_adjBasis :
    Circuit.mulNet (adjBasis m r) = Circuit.bilinNet (fun i j k => tbl r i j k) :=
  mulNet_eq_bilinNet_tbl r (AdjoinRoot.root (nu m r)) (adjBasis m r)
    (adjBasis_apply m r) (root_pow_top m r)

end Carrier

/-! ## GF(16) with a named reduction polynomial -/

/-- The GF(16) reduction word: `ν₄ = X⁴ + X³ + X² + X + 1` (all-ones). -/
def r4 : Fin 4 → ZMod 2 := fun _ => 1

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem nu4_eq_cyclotomic : nu 3 r4 = cyclotomic 5 (ZMod 2) := by
  rw [cyclotomic_prime, Finset.sum_range_succ]
  unfold nu
  simp only [r4]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (1 : ZMod 2) * X ^ i) 4]
  simp [add_comm]

/-- **`ν₄` is irreducible over `𝔽₂`**: it is the 5th cyclotomic polynomial, and
`ord₅(2) = 4 = φ(5)`. -/
theorem nu4_irreducible : Irreducible (nu 3 r4) := by
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5) (by norm_num)
    nu4_eq_cyclotomic.dvd ?_
  rw [nu_natDegree]
  symm
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · decide
  · decide

instance : Fact (Irreducible (nu 3 r4)) := ⟨nu4_irreducible⟩

/-- **GF(16), with the reduction polynomial pinned by name**: the quotient by `ν₄` is a genuine
field, and its multiplier is the computable 105-gate netlist below. (The root of `Φ₅` has
multiplicative order 5, not 15 — fine for multiplication, not a primitive element.) -/
noncomputable abbrev GF16 := AdjoinRoot (nu 3 r4)

noncomputable example : Field GF16 := inferInstance

/-! ## Worked examples, by kernel `decide` on the Pi model -/

section Witness

open Circuit

-- m = 4 anchors (ν₄ = Φ₅, so α has order 5): α³·α³ = α⁶ = α; α⁴ = α³+α²+α+1; α⁵ = 1.
example : List.ofFn (tbl r4 3 3) = [0, 1, 0, 0] := by decide
example : List.ofFn (powVec r4 4) = [1, 1, 1, 1] := by decide
example : List.ofFn (powVec r4 5) = [1, 0, 0, 0] := by decide

set_option maxHeartbeats 400000 in
-- the model is commutative on all 256 pairs; measured at ~61k heartbeats
example : ∀ v w : Fin 4 → ZMod 2, mulVecC r4 v w = mulVecC r4 w v := by decide

-- a live netlist run: α · α⁴ = α⁵ = 1, through the gates:
example : evalVec (bilinNet (fun i j k => tbl r4 i j k))
    (Fin.append (encW (powVec r4 1)) (encW (powVec r4 4)))
      = encW (powVec r4 5) := by decide

-- the m = 4 gate count:
example : sizeVec (bilinNet (fun i j k => tbl r4 i j k)) = 105 := by decide

/-- The GF(256) reduction word: the AES polynomial `X⁸ + X⁴ + X³ + X + 1`. -/
def r8 : Fin 8 → ZMod 2 :=
  fun k => if k.val = 0 ∨ k.val = 1 ∨ k.val = 3 ∨ k.val = 4 then 1 else 0

-- m = 8 anchors: α⁸ is the AES reduction; the worst table entry α¹⁴:
example : List.ofFn (powVec r8 8) = [1, 1, 0, 1, 1, 0, 0, 0] := by decide
example : List.ofFn (tbl r8 7 7) = [0, 1, 0, 1, 1, 0, 0, 1] := by decide

set_option maxHeartbeats 4000000 in
-- the m = 8 gate count, by kernel decide directly on the Pi model: 512 table queries at up to
-- ~400 heartbeats each (the worst single coordinate measured at 397; the interpreter's
-- slowness on the Pi model does not transfer to the kernel)
example : sizeVec (bilinNet (fun i j k => tbl r8 i j k)) = 727 := by decide

end Witness

end ECCLib

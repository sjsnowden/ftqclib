/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The computable polynomial kit

The executable side of the RS decoder: polynomials as **little-endian `List R` coefficient
lists** over an explicit record `FieldOps R` of computable field operations (operations as
plain data, no typeclasses — the GateField style), with structural/fuel recursion throughout,
and a **noncomputable denotation** `toPoly φ : List R → Polynomial F` as the single bridge to
Mathlib's proof-side polynomial theory. Everything meant to execute is computable and
kernel-reducible; Mathlib's `Polynomial` (noncomputable, kernel-opaque) appears only inside
theorems.

* `FieldOps` / `FieldOps.Model` — computable operations, and the proposition that a bijection
  `φ : R → F` transports them to a genuine `Field F`;
* `padd`/`pneg`/`psub`/`psmul`/`pshift`/`pmul`/`peval` — the arithmetic, all structural;
* `toPoly` + the hom lemmas (`toPoly_padd` … `peval_toPoly`) — one list induction each;
* `toPoly_coeff` — the coefficient workhorse: `(toPoly φ p).coeff i = φ (p.getD i ops.zero)`;
* `ptrim`/`pdeg`/`plead` — the semantic degree discipline (`pdeg = natDegree + 1` on nonzero
  denotations, `pdeg = 0` exactly on semantic zero: subtraction-free by construction);
* `pdivMod` — **fuel-based long division** (`termination_by` is kernel-opaque, so fuel is a
  hard constraint, not a style choice), with `pdivMod_spec`: the division identity plus the
  strict remainder bound, via the leading-term cancellation `pdeg_step_lt`;
* `pdiv_unique` — proof-side uniqueness of quotient/remainder in `F[X]`, reconnecting the
  executable division to the true one;
* the `ZMod 2` smoke instance (`zmod2Ops`/`zmod2Model`) with kernel-`decide` examples.

Consumed by `GaoDecoder.lean` (`gaoLoop` and the Gao decoder) and `GaoField.lean` (the
GF(2^m) instantiations, where the kit builds its own coefficient field: scalars are
`List (ZMod 2)` words reduced by the kit's `pdivMod` against the reduction word).
-/

namespace ECCLib.Coding

open Polynomial

variable {R : Type*} {F : Type*} [Field F]

/-! ## The operations record and its model -/

/-- Computable field operations as plain data — no typeclasses, no `Classical`. The
instantiations at GF(2^m) supply the library's certified multiplication and inverse tables. -/
structure FieldOps (R : Type*) where
  zero : R
  one : R
  add : R → R → R
  neg : R → R
  mul : R → R → R
  inv : R → R
  beq : R → R → Bool

/-- `φ : R → F` is a **model** of the operations: a bijection transporting every operation to
a genuine field. `map_inv` is total (`φ (inv 0) = 0⁻¹ = 0`); `beq_iff` makes the boolean
equality semantic. All correctness theorems about the executable layer are stated under a
model. -/
structure FieldOps.Model (ops : FieldOps R) (φ : R → F) : Prop where
  bij : Function.Bijective φ
  map_zero : φ ops.zero = 0
  map_one : φ ops.one = 1
  map_add : ∀ x y, φ (ops.add x y) = φ x + φ y
  map_neg : ∀ x, φ (ops.neg x) = -(φ x)
  map_mul : ∀ x y, φ (ops.mul x y) = φ x * φ y
  map_inv : ∀ x, φ (ops.inv x) = (φ x)⁻¹
  beq_iff : ∀ x y, ops.beq x y = true ↔ φ x = φ y

theorem FieldOps.Model.injective {ops : FieldOps R} {φ : R → F} (M : ops.Model φ) :
    Function.Injective φ :=
  M.bij.injective

theorem FieldOps.Model.beq_zero_iff {ops : FieldOps R} {φ : R → F} (M : ops.Model φ)
    (x : R) : ops.beq x ops.zero = true ↔ φ x = 0 := by
  rw [M.beq_iff, M.map_zero]

/-! ## The arithmetic (computable, structural) -/

variable (ops : FieldOps R)

/-- Coefficient-wise addition (little-endian; lengths may differ). -/
def padd : List R → List R → List R
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => ops.add a b :: padd p q

/-- Coefficient-wise negation. -/
def pneg (p : List R) : List R := p.map ops.neg

/-- Subtraction. -/
def psub (p q : List R) : List R := padd ops p (pneg ops q)

/-- Scalar multiple. -/
def psmul (c : R) (p : List R) : List R := p.map (ops.mul c)

/-- Multiplication by `X^n`: prepend `n` zeros. -/
def pshift (n : ℕ) (p : List R) : List R := List.replicate n ops.zero ++ p

/-- Product, by the schoolbook recursion `(a + Xp)·q = a·q + X·(p·q)`. -/
def pmul : List R → List R → List R
  | [], _ => []
  | a :: p, q => padd ops (psmul ops a q) (ops.zero :: pmul p q)

/-- Horner evaluation. -/
def peval (x : R) : List R → R
  | [] => ops.zero
  | a :: p => ops.add a (ops.mul x (peval x p))

/-! ## The denotation -/

/-- The proof-side denotation of a coefficient list: `toPoly φ (c :: p) = C (φ c) + X · toPoly φ p`.
Noncomputable (Mathlib's `Polynomial`); the one bridge across the executable/spec line. -/
noncomputable def toPoly (φ : R → F) : List R → Polynomial F
  | [] => 0
  | c :: p => C (φ c) + X * toPoly φ p

@[simp] theorem toPoly_nil (φ : R → F) : toPoly φ ([] : List R) = 0 := rfl

theorem toPoly_cons (φ : R → F) (a : R) (p : List R) :
    toPoly φ (a :: p) = C (φ a) + X * toPoly φ p := rfl

theorem toPoly_singleton (φ : R → F) (c : R) : toPoly φ [c] = C (φ c) := by
  simp [toPoly]

/-! ## The hom lemmas (one induction per operation) -/

variable {ops} {φ : R → F}

theorem toPoly_padd (M : ops.Model φ) : ∀ p q : List R,
    toPoly φ (padd ops p q) = toPoly φ p + toPoly φ q
  | [], q => by simp [padd]
  | a :: p, [] => by simp [padd]
  | a :: p, b :: q => by
    simp only [padd, toPoly_cons, M.map_add, C_add]
    rw [toPoly_padd M p q]
    ring

theorem toPoly_pneg (M : ops.Model φ) : ∀ p : List R,
    toPoly φ (pneg ops p) = -toPoly φ p
  | [] => by simp [pneg]
  | a :: p => by
    simp only [pneg, List.map_cons, toPoly_cons, M.map_neg, C_neg]
    rw [show List.map ops.neg p = pneg ops p from rfl, toPoly_pneg M p]
    ring

theorem toPoly_psub (M : ops.Model φ) (p q : List R) :
    toPoly φ (psub ops p q) = toPoly φ p - toPoly φ q := by
  rw [psub, toPoly_padd M, toPoly_pneg M]
  ring

theorem toPoly_psmul (M : ops.Model φ) (c : R) : ∀ p : List R,
    toPoly φ (psmul ops c p) = C (φ c) * toPoly φ p
  | [] => by simp [psmul]
  | a :: p => by
    simp only [psmul, List.map_cons, toPoly_cons, M.map_mul, C_mul]
    rw [show List.map (ops.mul c) p = psmul ops c p from rfl, toPoly_psmul M c p]
    ring

theorem toPoly_pshift (M : ops.Model φ) : ∀ (n : ℕ) (p : List R),
    toPoly φ (pshift ops n p) = X ^ n * toPoly φ p
  | 0, p => by simp [pshift]
  | n + 1, p => by
    simp only [pshift, List.replicate_succ, List.cons_append, toPoly_cons, M.map_zero, C_0,
      zero_add]
    rw [show List.replicate n ops.zero ++ p = pshift ops n p from rfl, toPoly_pshift M n p]
    ring

theorem toPoly_pmul (M : ops.Model φ) : ∀ p q : List R,
    toPoly φ (pmul ops p q) = toPoly φ p * toPoly φ q
  | [], q => by simp [pmul]
  | a :: p, q => by
    simp only [pmul]
    rw [toPoly_padd M, toPoly_psmul M, toPoly_cons, M.map_zero, C_0, zero_add,
      toPoly_pmul M p q, toPoly_cons]
    ring

theorem peval_toPoly (M : ops.Model φ) (x : R) : ∀ p : List R,
    φ (peval ops x p) = (toPoly φ p).eval (φ x)
  | [] => by simp [peval, M.map_zero]
  | a :: p => by
    simp only [peval, M.map_add, M.map_mul, toPoly_cons, eval_add, eval_C, eval_mul, eval_X]
    rw [peval_toPoly M x p]

/-! ## The coefficient workhorse and the structural degree bound -/

theorem toPoly_coeff (M : ops.Model φ) : ∀ (p : List R) (i : ℕ),
    (toPoly φ p).coeff i = φ (p.getD i ops.zero)
  | [], i => by simp [M.map_zero]
  | a :: p, 0 => by
    simp [toPoly_cons, coeff_add, coeff_C, mul_coeff_zero, coeff_X_zero]
  | a :: p, i + 1 => by
    simp only [toPoly_cons, coeff_add, coeff_C, Nat.succ_ne_zero, if_false, coeff_X_mul,
      List.getD_cons_succ, zero_add]
    exact toPoly_coeff M p i

/-- The structural degree bound: any list denotes a polynomial of degree below its length.
Needs nothing about `φ`. -/
theorem toPoly_degree_lt (φ : R → F) : ∀ p : List R,
    (toPoly φ p).degree < (p.length : WithBot ℕ)
  | [] => by simp
  | a :: p => by
    rw [toPoly_cons, List.length_cons]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos p.length)
    · rcases eq_or_ne (toPoly φ p) 0 with h | h
      · rw [h, mul_zero, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hlt := toPoly_degree_lt φ p
        rw [degree_eq_natDegree h] at hlt
        have hnat : (toPoly φ p).natDegree < p.length := by exact_mod_cast hlt
        have hX : X * toPoly φ p ≠ 0 := mul_ne_zero X_ne_zero h
        have hnd : (X * toPoly φ p).natDegree < p.length + 1 := by
          rw [natDegree_mul X_ne_zero h, natDegree_X]
          omega
        rw [degree_eq_natDegree hX]
        exact_mod_cast hnd

/-! ## Trim, degree, leading coefficient -/

variable (ops)

/-- Strip semantic zeros from the top (the high-degree end): the canonicalizer behind `pdeg`. -/
def ptrim : List R → List R
  | [] => []
  | a :: p =>
    match ptrim p with
    | [] => if ops.beq a ops.zero then [] else [a]
    | b :: q => a :: b :: q

/-- The semantic degree, subtraction-free: `pdeg = natDegree + 1` on nonzero denotations and
`0` exactly on semantic zero (`pdeg_eq_natDegree_succ`, `pdeg_eq_zero_iff`). -/
def pdeg (p : List R) : ℕ := (ptrim ops p).length

/-- The semantic leading coefficient. -/
def plead (p : List R) : R := (ptrim ops p).getLast?.getD ops.zero

theorem ptrim_length_le : ∀ p : List R, (ptrim ops p).length ≤ p.length
  | [] => le_refl _
  | a :: p => by
    simp only [ptrim]
    cases hrec : ptrim ops p with
    | nil =>
      cases hbeq : ops.beq a ops.zero <;> simp
    | cons b q =>
      have := ptrim_length_le p
      rw [hrec] at this
      simpa using Nat.succ_le_succ this

theorem pdeg_le_length (p : List R) : pdeg ops p ≤ p.length :=
  ptrim_length_le ops p

theorem ptrim_eq_nil_iff : ∀ p : List R,
    ptrim ops p = [] ↔ ∀ a ∈ p, ops.beq a ops.zero = true
  | [] => by simp [ptrim]
  | a :: p => by
    simp only [ptrim]
    cases hrec : ptrim ops p with
    | nil =>
      have hp : ∀ b ∈ p, ops.beq b ops.zero = true := (ptrim_eq_nil_iff p).mp hrec
      cases hbeq : ops.beq a ops.zero with
      | true => simpa [hbeq] using hp
      | false =>
        rw [if_neg (by simp)]
        constructor
        · intro h
          exact absurd h (List.cons_ne_nil a [])
        · intro h
          have := h a (List.mem_cons_self)
          rw [this] at hbeq
          exact absurd hbeq (by simp)
    | cons b q =>
      constructor
      · intro h
        exact absurd h (List.cons_ne_nil _ _)
      · intro h
        have hall : ∀ x ∈ p, ops.beq x ops.zero = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
        have := (ptrim_eq_nil_iff p).mpr hall
        rw [hrec] at this
        exact absurd this (List.cons_ne_nil _ _)

theorem ptrim_getLast?_beq : ∀ (p : List R) {b : R},
    (ptrim ops p).getLast? = some b → ops.beq b ops.zero = false
  | [], b, h => by simp [ptrim] at h
  | a :: p, b, h => by
    simp only [ptrim] at h
    cases hrec : ptrim ops p with
    | nil =>
      rw [hrec] at h
      cases hbeq : ops.beq a ops.zero
      · rw [hbeq] at h
        simp only [Bool.false_eq_true, if_false, List.getLast?_singleton, Option.some.injEq] at h
        rw [← h]
        exact hbeq
      · rw [hbeq] at h
        simp at h
    | cons c q =>
      rw [hrec, List.getLast?_cons_cons, ← hrec] at h
      exact ptrim_getLast?_beq p h

variable {ops}

/-! ## The semantic degree layer (under a model) -/

theorem toPoly_eq_zero_iff (M : ops.Model φ) (p : List R) :
    toPoly φ p = 0 ↔ ∀ a ∈ p, ops.beq a ops.zero = true := by
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hc := toPoly_coeff M p i
    rw [h, coeff_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at hc
    exact (M.beq_zero_iff _).mpr hc.symm
  · intro h
    ext i
    rw [coeff_zero, toPoly_coeff M, List.getD_eq_getElem?_getD]
    rcases lt_or_ge i p.length with hi | hi
    · rw [List.getElem?_eq_getElem hi, Option.getD_some]
      exact (M.beq_zero_iff _).mp (h _ (p.getElem_mem hi))
    · rw [List.getElem?_eq_none (by omega), Option.getD_none]
      exact M.map_zero

theorem toPoly_ptrim (M : ops.Model φ) : ∀ p : List R,
    toPoly φ (ptrim ops p) = toPoly φ p
  | [] => rfl
  | a :: p => by
    simp only [ptrim]
    cases hrec : ptrim ops p with
    | nil =>
      have hp : toPoly φ p = 0 := by
        have h := toPoly_ptrim M p
        rw [hrec, toPoly_nil] at h
        exact h.symm
      cases hbeq : ops.beq a ops.zero
      · simp only [Bool.false_eq_true, if_false, toPoly_cons, toPoly_nil, hp, mul_zero,
          add_zero]
      · have ha : φ a = 0 := (M.beq_zero_iff a).mp hbeq
        simp only [if_true, toPoly_nil, toPoly_cons, ha, C_0, hp, mul_zero, add_zero]
    | cons b q =>
      have h := toPoly_ptrim M p
      rw [hrec] at h
      calc toPoly φ (a :: b :: q) = C (φ a) + X * toPoly φ (b :: q) := rfl
        _ = C (φ a) + X * toPoly φ p := by rw [h]
        _ = toPoly φ (a :: p) := rfl

theorem pdeg_eq_zero_iff (M : ops.Model φ) (p : List R) :
    pdeg ops p = 0 ↔ toPoly φ p = 0 := by
  rw [pdeg, List.length_eq_zero_iff, ptrim_eq_nil_iff, toPoly_eq_zero_iff M]

/-- `getD` at the last index reads `getLast?`. -/
private theorem getD_last_of_getLast? {l : List R} {b : R} (h : l.getLast? = some b) (z : R) :
    l.getD (l.length - 1) z = b := by
  have hne : l ≠ [] := by
    intro h0
    rw [h0] at h
    simp at h
  have hlt : l.length - 1 < l.length := by
    have : l.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.mp h0)
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at h
  rw [← h, List.getLast_eq_getElem]

theorem pdeg_eq_natDegree_succ (M : ops.Model φ) (p : List R) (hp : toPoly φ p ≠ 0) :
    pdeg ops p = (toPoly φ p).natDegree + 1 := by
  have hne : ptrim ops p ≠ [] := by
    intro h
    exact hp ((toPoly_eq_zero_iff M p).mpr ((ptrim_eq_nil_iff ops p).mp h))
  obtain ⟨b, hb⟩ : ∃ b, (ptrim ops p).getLast? = some b := by
    cases hq : (ptrim ops p).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hq) hne
    | some b => exact ⟨b, rfl⟩
  have hbne : φ b ≠ 0 := by
    intro h0
    have := (M.beq_zero_iff b).mpr h0
    rw [ptrim_getLast?_beq ops p hb] at this
    exact absurd this (by simp)
  have hcoeff : (toPoly φ p).coeff ((ptrim ops p).length - 1) = φ b := by
    rw [← toPoly_ptrim M p, toPoly_coeff M, getD_last_of_getLast? hb]
  have hle : (ptrim ops p).length - 1 ≤ (toPoly φ p).natDegree :=
    le_natDegree_of_ne_zero (hcoeff ▸ hbne)
  have hlt : (toPoly φ p).natDegree < (ptrim ops p).length := by
    have hdeg := toPoly_degree_lt φ (ptrim ops p)
    rw [toPoly_ptrim M] at hdeg
    exact (natDegree_lt_iff_degree_lt hp).mpr hdeg
  have hlen : (ptrim ops p).length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
  rw [pdeg]
  omega

theorem pdeg_le_of_degree_lt (M : ops.Model φ) {p : List R} {m : ℕ}
    (h : (toPoly φ p).degree < (m : WithBot ℕ)) : pdeg ops p ≤ m := by
  by_cases hp : toPoly φ p = 0
  · rw [(pdeg_eq_zero_iff M p).mpr hp]
    exact Nat.zero_le m
  · rw [pdeg_eq_natDegree_succ M p hp]
    have := (natDegree_lt_iff_degree_lt hp).mpr h
    omega

theorem toPoly_degree_lt_pdeg (M : ops.Model φ) (p : List R) :
    (toPoly φ p).degree < (pdeg ops p : WithBot ℕ) := by
  by_cases hp : toPoly φ p = 0
  · rw [hp, degree_zero, (pdeg_eq_zero_iff M p).mpr hp]
    exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hp, pdeg_eq_natDegree_succ M p hp]
    exact_mod_cast Nat.lt_succ_self _

theorem phi_plead (M : ops.Model φ) (p : List R) (hp : toPoly φ p ≠ 0) :
    φ (plead ops p) = (toPoly φ p).leadingCoeff := by
  have hne : ptrim ops p ≠ [] := by
    intro h
    exact hp ((toPoly_eq_zero_iff M p).mpr ((ptrim_eq_nil_iff ops p).mp h))
  obtain ⟨b, hb⟩ : ∃ b, (ptrim ops p).getLast? = some b := by
    cases hq : (ptrim ops p).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hq) hne
    | some b => exact ⟨b, rfl⟩
  have hplead : plead ops p = b := by
    rw [plead, hb, Option.getD_some]
  have hcoeff : (toPoly φ p).coeff ((ptrim ops p).length - 1) = φ b := by
    rw [← toPoly_ptrim M p, toPoly_coeff M, getD_last_of_getLast? hb]
  have hnd : (ptrim ops p).length - 1 = (toPoly φ p).natDegree := by
    have := pdeg_eq_natDegree_succ M p hp
    rw [pdeg] at this
    omega
  rw [hplead, Polynomial.leadingCoeff, ← hnd, hcoeff]

theorem phi_plead_ne_zero (M : ops.Model φ) (p : List R) (hp : toPoly φ p ≠ 0) :
    φ (plead ops p) ≠ 0 := by
  rw [phi_plead M p hp]
  exact leadingCoeff_ne_zero.mpr hp

/-! ## Fuel-based long division

`termination_by` (well-founded recursion) is opaque to kernel `decide`, so
the division runs on explicit fuel; `pdivMod` supplies `length + 1`, which the strict degree
descent (`pdeg_step_lt`) shows is enough. -/

variable (ops)

/-- One long-division run on explicit fuel. At fuel `0` the remainder is returned as-is —
reached only when the remainder is already semantically `0` (see `pdivModAux_spec`). -/
def pdivModAux (d : List R) : ℕ → List R → List R × List R
  | 0, r => ([], r)
  | fuel + 1, r =>
    if pdeg ops r < pdeg ops d then ([], r)
    else
      let c := ops.mul (plead ops r) (ops.inv (plead ops d))
      let k := pdeg ops r - pdeg ops d
      let res := pdivModAux d fuel (psub ops r (pshift ops k (psmul ops c d)))
      (padd ops (pshift ops k [c]) res.1, res.2)

/-- Long division: quotient and remainder, `pdeg` of the remainder strictly below `pdeg d`
(`pdivMod_spec`). Computable, kernel-reducible. -/
def pdivMod (p d : List R) : List R × List R :=
  pdivModAux ops d (p.length + 1) p

variable {ops}

/-- The leading-term cancellation: one division step strictly drops the semantic degree. -/
theorem pdeg_step_lt (M : ops.Model φ) {d r : List R} (hd : pdeg ops d ≠ 0)
    (hr : pdeg ops d ≤ pdeg ops r) :
    pdeg ops (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
      (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d))) < pdeg ops r := by
  have hr0 : toPoly φ r ≠ 0 := by
    intro h
    rw [(pdeg_eq_zero_iff M r).mpr h] at hr
    omega
  have hd0 : toPoly φ d ≠ 0 := fun h => hd ((pdeg_eq_zero_iff M d).mpr h)
  set c : F := φ (ops.mul (plead ops r) (ops.inv (plead ops d))) with hc_def
  have hc : c = (toPoly φ r).leadingCoeff * (toPoly φ d).leadingCoeff⁻¹ := by
    rw [hc_def, M.map_mul, M.map_inv, phi_plead M r hr0, phi_plead M d hd0]
  have hcne : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hr0)
      (inv_ne_zero (leadingCoeff_ne_zero.mpr hd0))
  have hsub : toPoly φ (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
      (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d)))
      = toPoly φ r - X ^ (pdeg ops r - pdeg ops d) * (C c * toPoly φ d) := by
    rw [toPoly_psub M, toPoly_pshift M, toPoly_psmul M]
  set E : Polynomial F := X ^ (pdeg ops r - pdeg ops d) * (C c * toPoly φ d) with hE_def
  have hE_ne : E ≠ 0 := by
    rw [hE_def]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero (C_ne_zero.mpr hcne) hd0)
  have hE_deg : E.degree = (toPoly φ r).degree := by
    rw [hE_def, degree_mul, degree_mul, degree_X_pow, degree_C hcne, zero_add,
      degree_eq_natDegree hd0, degree_eq_natDegree hr0]
    have h1 := pdeg_eq_natDegree_succ M r hr0
    have h2 := pdeg_eq_natDegree_succ M d hd0
    have : pdeg ops r - pdeg ops d + (toPoly φ d).natDegree = (toPoly φ r).natDegree := by
      omega
    exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) this
  have hE_lead : E.leadingCoeff = (toPoly φ r).leadingCoeff := by
    rw [hE_def, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_X_pow, leadingCoeff_C,
      one_mul, hc, mul_assoc, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hd0), mul_one]
  have hlt : (toPoly φ r - E).degree < (toPoly φ r).degree :=
    degree_sub_lt hE_deg.symm hr0 hE_lead.symm
  have hfin : pdeg ops (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
      (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d))) ≤ pdeg ops r - 1 := by
    apply pdeg_le_of_degree_lt M
    rw [hsub]
    calc (toPoly φ r - E).degree < (toPoly φ r).degree := hlt
      _ = ((toPoly φ r).natDegree : WithBot ℕ) := degree_eq_natDegree hr0
      _ = ((pdeg ops r - 1 : ℕ) : WithBot ℕ) := by
          have := pdeg_eq_natDegree_succ M r hr0
          exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) (by omega)
  omega

/-- The division specification: the identity and the strict remainder bound, by induction on
fuel through the cancellation lemma. The side condition `pdeg r ≤ fuel` is what makes the
fuel sufficient. -/
theorem pdivModAux_spec (M : ops.Model φ) {d : List R} (hd : pdeg ops d ≠ 0) :
    ∀ (fuel : ℕ) (r : List R), pdeg ops r ≤ fuel →
      toPoly φ r = toPoly φ d * toPoly φ (pdivModAux ops d fuel r).1
          + toPoly φ (pdivModAux ops d fuel r).2
        ∧ pdeg ops (pdivModAux ops d fuel r).2 < pdeg ops d
  | 0, r, hfuel => by
    refine ⟨?_, ?_⟩
    · change toPoly φ r = toPoly φ d * toPoly φ ([] : List R) + toPoly φ r
      rw [toPoly_nil, mul_zero, zero_add]
    · change pdeg ops r < pdeg ops d
      omega
  | fuel + 1, r, hfuel => by
    by_cases hlt : pdeg ops r < pdeg ops d
    · have heq : pdivModAux ops d (fuel + 1) r = ([], r) := by
        simp only [pdivModAux, if_pos hlt]
      rw [heq]
      exact ⟨by simp, by simpa using hlt⟩
    · have hle : pdeg ops d ≤ pdeg ops r := Nat.le_of_not_lt hlt
      have heq : pdivModAux ops d (fuel + 1) r
          = (padd ops (pshift ops (pdeg ops r - pdeg ops d)
                [ops.mul (plead ops r) (ops.inv (plead ops d))])
              (pdivModAux ops d fuel (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
                (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d)))).1,
             (pdivModAux ops d fuel (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
                (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d)))).2) := by
        simp only [pdivModAux, if_neg hlt]
      rw [heq]
      have hstep := pdeg_step_lt M hd hle
      have hfuel' : pdeg ops (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
          (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d))) ≤ fuel := by
        omega
      obtain ⟨hid, hbound⟩ := pdivModAux_spec M hd fuel _ hfuel'
      refine ⟨?_, by simpa using hbound⟩
      have hsub : toPoly φ (psub ops r (pshift ops (pdeg ops r - pdeg ops d)
          (psmul ops (ops.mul (plead ops r) (ops.inv (plead ops d))) d)))
          = toPoly φ r - X ^ (pdeg ops r - pdeg ops d)
              * (C (φ (ops.mul (plead ops r) (ops.inv (plead ops d)))) * toPoly φ d) := by
        rw [toPoly_psub M, toPoly_pshift M, toPoly_psmul M]
      change toPoly φ r = toPoly φ d * toPoly φ (padd ops _ _) + toPoly φ _
      rw [toPoly_padd M, toPoly_pshift M, toPoly_singleton]
      rw [hsub] at hid
      linear_combination hid

theorem pdivMod_spec (M : ops.Model φ) {p d : List R} (hd : pdeg ops d ≠ 0) :
    toPoly φ p = toPoly φ d * toPoly φ (pdivMod ops p d).1 + toPoly φ (pdivMod ops p d).2
      ∧ pdeg ops (pdivMod ops p d).2 < pdeg ops d :=
  pdivModAux_spec M hd (p.length + 1) p (by have := pdeg_le_length ops p; omega)

/-! ## Division uniqueness (proof-side, Mathlib only)

Reconnects the executable division to the abstract one: quotient and remainder at a nonzero
divisor are unique, so `pdivMod`'s output IS the true quotient whenever the identity and the
degree bound hold. -/

theorem pdiv_unique {d p q₁ r₁ q₂ r₂ : Polynomial F}
    (h₁ : p = d * q₁ + r₁) (h₂ : p = d * q₂ + r₂)
    (hr₁ : r₁.degree < d.degree) (hr₂ : r₂.degree < d.degree) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have hq : q₁ = q₂ := by
    by_contra hne
    have hsub : d * (q₁ - q₂) = r₂ - r₁ := by
      linear_combination h₂ - h₁
    have h1 : d.degree ≤ (d * (q₁ - q₂)).degree := by
      rw [degree_mul]
      have h0 : 0 ≤ (q₁ - q₂).degree := zero_le_degree_iff.mpr (sub_ne_zero.mpr hne)
      exact le_add_of_nonneg_right h0
    have h2 : (r₂ - r₁).degree < d.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hr₂ hr₁)
    rw [hsub] at h1
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  refine ⟨hq, ?_⟩
  rw [hq] at h₁
  have := h₁.symm.trans h₂
  exact add_left_cancel this

/-! ## The `ZMod 2` smoke instance -/

/-- The trivial computable instance: `ZMod 2` modeled by itself. Exercises the kit's shape
and gives kernel-`decide` corners. -/
def zmod2Ops : FieldOps (ZMod 2) where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  inv := (·⁻¹)
  beq := fun x y => decide (x = y)

theorem zmod2Model : zmod2Ops.Model (id : ZMod 2 → ZMod 2) where
  bij := Function.bijective_id
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_mul _ _ := rfl
  map_inv _ := rfl
  beq_iff _ _ := by simp [zmod2Ops]

-- `p(X) = 1 + X²` at `X = 1` in characteristic 2: `1 + 1 = 0`.
example : peval zmod2Ops 1 [1, 0, 1] = 0 := by decide

-- `1 + X²` has semantic degree witness `pdeg = 3` (= natDegree 2 + 1).
example : pdeg zmod2Ops [1, 0, 1] = 3 := by decide

-- `X² + 1 = (X + 1)²` in characteristic 2: division by `X + 1` leaves semantic remainder 0.
example : pdeg zmod2Ops (pdivMod zmod2Ops [1, 0, 1] [1, 1]).2 = 0 := by decide

-- The quotient is `X + 1`, up to trim.
example : ptrim zmod2Ops (pdivMod zmod2Ops [1, 0, 1] [1, 1]).1 = [1, 1] := by decide

end ECCLib.Coding

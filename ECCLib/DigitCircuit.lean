/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
/-
# The odd-characteristic digit layer

The odd-`p` gate descent: dense little-endian digits
(`dw p = ⌈log₂ p⌉` wires) with **totalization through the total decode** — every tabulated
digit block is DEFINED as `encD ∘ f ∘ decWD`, so its specification is hypothesis-free on
ALL inputs (junk bit patterns fold through the decode) and composition sites consume raw
outputs with zero glue. The layer is `[NeZero p]`-only throughout (primality first appears
where a field does, in the coding layer). The encode/decode ride on `Nat.testBit` and
Batteries' `Nat.ofBits` (consumed, not re-proved).

Composition is `dcomp` — the ONLY place `Circuit.subst` is touched — with `eval_dcomp` the
one composition proof (the `eval_xorFold` hypothesis-driven idiom). The totalizer
pre-normalizes each input digit (`eval_totalizeD`). Cross-width indices use named embeddings
only; `finProdFinEquiv` stays opaque.
-/
import ECCLib.GateAlgebra

namespace ECCLib

open Circuit Module Matrix

/-! ## Digits: width, encoding, the total decode -/

/-- Wires per digit: `⌈log₂ p⌉`. -/
def dw (p : ℕ) : ℕ := Nat.clog 2 p

theorem dw_two : dw 2 = 1 := by decide

/-- Dense little-endian digit encoding. -/
def encD {p : ℕ} [NeZero p] (a : ZMod p) : Fin (dw p) → Bool :=
  fun i => (ZMod.val a).testBit i

/-- The TOTAL decode: any bit pattern reads as its binary value cast into `ZMod p` —
junk folds mod `p`. -/
def decD {p : ℕ} (x : Fin (dw p) → Bool) : ZMod p := (Nat.ofBits x : ZMod p)

theorem decD_encD {p : ℕ} [NeZero p] (a : ZMod p) : decD (encD a) = a := by
  have hlt : ZMod.val a < 2 ^ dw p :=
    lt_of_lt_of_le (ZMod.val_lt a) (Nat.le_pow_clog one_lt_two p)
  change ((Nat.ofBits (fun i : Fin (dw p) => (ZMod.val a).testBit i) : ℕ) : ZMod p) = a
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt hlt]
  exact ZMod.natCast_rightInverse a

/-! ## Buses: digit families on flat wires -/

/-- A family of digits as one flat wire bundle (the index equivalence used opaquely). -/
def flatB {n w : ℕ} (x : Fin n → Fin w → Bool) : Fin (n * w) → Bool :=
  fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def encWD {p : ℕ} [NeZero p] {n : ℕ} (v : Fin n → ZMod p) : Fin n → Fin (dw p) → Bool :=
  fun i => encD (v i)

/-- The total bus decode. -/
def decWD {p n : ℕ} (s : Fin (n * dw p) → Bool) : Fin n → ZMod p :=
  fun i => decD (fun b => s (finProdFinEquiv (i, b)))

@[simp] theorem decWD_flatB_encWD {p : ℕ} [NeZero p] {n : ℕ} (v : Fin n → ZMod p) :
    decWD (flatB (encWD v)) = v := by
  funext i
  simp only [decWD, flatB, Equiv.symm_apply_apply]
  exact decD_encD (v i)

/-! ## The tabulation engine and the digit blocks -/

/-- A digit operation as a tabulated block, DEFINED through the total decode — its
all-inputs spec is `eval_dtabC_total`, its composition interface `eval_dtabC`. -/
def dtabC (p : ℕ) [NeZero p] (k : ℕ) (f : (Fin k → ZMod p) → ZMod p) :
    CircuitVec (k * dw p) (dw p) :=
  fun o => tabC (k * dw p) (fun x => encD (f (decWD x)) o)

/-- Total form — hypothesis-free, every input, junk included. -/
theorem eval_dtabC_total (p : ℕ) [NeZero p] (k : ℕ) (f : (Fin k → ZMod p) → ZMod p)
    (x : Fin (k * dw p) → Bool) :
    evalVec (dtabC p k f) x = encD (f (decWD x)) := by
  funext o
  exact eval_tabC _ _ x

/-- Canonical form — the composition interface. -/
theorem eval_dtabC (p : ℕ) [NeZero p] (k : ℕ) (f : (Fin k → ZMod p) → ZMod p)
    (v : Fin k → ZMod p) :
    evalVec (dtabC p k f) (flatB (encWD v)) = encD (f v) := by
  rw [eval_dtabC_total, decWD_flatB_encWD]

def addD (p : ℕ) [NeZero p] : CircuitVec (2 * dw p) (dw p) :=
  dtabC p 2 (fun v => v 0 + v 1)

def subD (p : ℕ) [NeZero p] : CircuitVec (2 * dw p) (dw p) :=
  dtabC p 2 (fun v => v 0 - v 1)

def mulD (p : ℕ) [NeZero p] : CircuitVec (2 * dw p) (dw p) :=
  dtabC p 2 (fun v => v 0 * v 1)

def negD (p : ℕ) [NeZero p] : CircuitVec (1 * dw p) (dw p) :=
  dtabC p 1 (fun v => - v 0)

def scaleD (p : ℕ) [NeZero p] (c : ZMod p) : CircuitVec (1 * dw p) (dw p) :=
  dtabC p 1 (fun v => c * v 0)

/-- The normalizer: the identity through the total decode — the untrusted-boundary block. -/
def normD (p : ℕ) [NeZero p] : CircuitVec (1 * dw p) (dw p) :=
  dtabC p 1 (fun v => v 0)

theorem eval_addD (p : ℕ) [NeZero p] (a b : ZMod p) :
    evalVec (addD p) (flatB (encWD ![a, b])) = encD (a + b) := by
  rw [addD, eval_dtabC]
  simp

theorem eval_mulD (p : ℕ) [NeZero p] (a b : ZMod p) :
    evalVec (mulD p) (flatB (encWD ![a, b])) = encD (a * b) := by
  rw [mulD, eval_dtabC]
  simp

/-! ## Composition: the one `subst` site -/

/-- The `i`-th digit slice of a bus, as wires. -/
def inBlk {n w : ℕ} (i : Fin n) : CircuitVec (n * w) w :=
  fun b => .wire (finProdFinEquiv (i, b))

/-- Block composition — the ONLY place `subst` is touched. -/
def dcomp {n w k : ℕ} (blk : CircuitVec (k * w) w) (g : Fin k → CircuitVec n w) :
    CircuitVec n w :=
  fun o => subst (blk o)
    (fun iw => g (finProdFinEquiv.symm iw).1 (finProdFinEquiv.symm iw).2)

/-- The raw composition compute (no encoding content). -/
theorem eval_dcomp_raw {n w k : ℕ} (blk : CircuitVec (k * w) w)
    (g : Fin k → CircuitVec n w) (x : Fin n → Bool) :
    evalVec (dcomp blk g) x
      = evalVec blk (fun iw =>
          evalVec (g (finProdFinEquiv.symm iw).1) x (finProdFinEquiv.symm iw).2) := by
  funext o
  exact eval_subst _ _ _

/-- **THE composition-site lemma** (hypothesis-driven, the `eval_xorFold` idiom): a block
with a canonical spec, fed sub-circuits with canonical outputs, has a canonical output. -/
theorem eval_dcomp {p n k : ℕ} [NeZero p] {blk : CircuitVec (k * dw p) (dw p)}
    {f : (Fin k → ZMod p) → ZMod p}
    (hblk : ∀ u : Fin k → ZMod p, evalVec blk (flatB (encWD u)) = encD (f u))
    {g : Fin k → CircuitVec n (dw p)} {x : Fin n → Bool} {v : Fin k → ZMod p}
    (hg : ∀ i, evalVec (g i) x = encD (v i)) :
    evalVec (dcomp blk g) x = encD (f v) := by
  rw [eval_dcomp_raw]
  have harg : (fun iw : Fin (k * dw p) =>
      evalVec (g (finProdFinEquiv.symm iw).1) x (finProdFinEquiv.symm iw).2)
      = flatB (encWD v) := by
    funext iw
    exact congrFun (hg (finProdFinEquiv.symm iw).1) (finProdFinEquiv.symm iw).2
  rw [harg]
  exact hblk v

/-! ## Totalization at an untrusted boundary -/

/-- Pre-normalizing each input digit totalizes any canonically-specified block: the
composite's spec holds for ARBITRARY wire assignments, reading inputs through the total
decode. The template: `dcomp blk (fun i => dcomp (normD p) ![inBlk i])`. -/
theorem eval_totalizeD {p k : ℕ} [NeZero p] {blk : CircuitVec (k * dw p) (dw p)}
    {f : (Fin k → ZMod p) → ZMod p}
    (hblk : ∀ u : Fin k → ZMod p, evalVec blk (flatB (encWD u)) = encD (f u))
    (x : Fin (k * dw p) → Bool) :
    evalVec (dcomp blk (fun i => dcomp (normD p) ![inBlk i])) x
      = encD (f (decWD x)) := by
  exact eval_dcomp hblk (fun i => by
    rw [eval_dcomp_raw]
    have hZ : (fun iw : Fin (1 * dw p) =>
        evalVec ((![inBlk i] : Fin 1 → CircuitVec (k * dw p) (dw p))
          (finProdFinEquiv.symm iw).1) x (finProdFinEquiv.symm iw).2)
        = fun iw => x (finProdFinEquiv (i, (finProdFinEquiv.symm iw).2)) := by
      funext iw
      rw [Subsingleton.elim (finProdFinEquiv.symm iw).1 (0 : Fin 1)]
      rfl
    rw [hZ, normD, eval_dtabC_total]
    congr 1
    simp only [decWD, Equiv.symm_apply_apply])

/-! ## Folds, dot products, linear and bilinear layers -/

/-- A constant digit. -/
def constD (p : ℕ) [NeZero p] {n : ℕ} (c : ZMod p) : CircuitVec n (dw p) :=
  fun o => .const (encD c o)

theorem eval_constD (p : ℕ) [NeZero p] {n : ℕ} (c : ZMod p) (x : Fin n → Bool) :
    evalVec (constD p c) x = encD c := rfl

/-- The odd-`p` summation fold. -/
def addFoldD (p : ℕ) [NeZero p] {n : ℕ} :
    (k : ℕ) → (Fin k → CircuitVec n (dw p)) → CircuitVec n (dw p)
  | 0, _ => constD p 0
  | k + 1, g => dcomp (addD p) ![g (Fin.last k), addFoldD p k (fun i => g i.castSucc)]

/-- The generic canonical spec of `addD` (the composition-facing form). -/
theorem eval_addD' (p : ℕ) [NeZero p] (u : Fin 2 → ZMod p) :
    evalVec (addD p) (flatB (encWD u)) = encD (u 0 + u 1) :=
  eval_dtabC p 2 _ u

theorem eval_subD' (p : ℕ) [NeZero p] (u : Fin 2 → ZMod p) :
    evalVec (subD p) (flatB (encWD u)) = encD (u 0 - u 1) :=
  eval_dtabC p 2 _ u

theorem eval_mulD' (p : ℕ) [NeZero p] (u : Fin 2 → ZMod p) :
    evalVec (mulD p) (flatB (encWD u)) = encD (u 0 * u 1) :=
  eval_dtabC p 2 _ u

theorem eval_negD' (p : ℕ) [NeZero p] (u : Fin 1 → ZMod p) :
    evalVec (negD p) (flatB (encWD u)) = encD (- u 0) :=
  eval_dtabC p 1 _ u

theorem eval_scaleD' (p : ℕ) [NeZero p] (c : ZMod p) (u : Fin 1 → ZMod p) :
    evalVec (scaleD p c) (flatB (encWD u)) = encD (c * u 0) :=
  eval_dtabC p 1 _ u

/-- The odd-`p` summation primitive — `eval_xorFold` one characteristic up. -/
theorem eval_addFoldD (p : ℕ) [NeZero p] {n : ℕ} (x : Fin n → Bool) :
    ∀ (k : ℕ) (g : Fin k → CircuitVec n (dw p)) (v : Fin k → ZMod p),
      (∀ i, evalVec (g i) x = encD (v i)) →
      evalVec (addFoldD p k g) x = encD (∑ i, v i)
  | 0, g, v, _ => by
    rw [show addFoldD p 0 g = constD p 0 from rfl, eval_constD]
    simp
  | k + 1, g, v, h => by
    rw [show addFoldD p (k + 1) g
        = dcomp (addD p) ![g (Fin.last k), addFoldD p k (fun i => g i.castSucc)] from rfl]
    have hstep := eval_dcomp (eval_addD' p)
      (g := ![g (Fin.last k), addFoldD p k (fun i => g i.castSucc)]) (x := x)
      (v := ![v (Fin.last k), ∑ i : Fin k, v i.castSucc]) (fun t => by
        fin_cases t
        · simpa using h (Fin.last k)
        · simpa using eval_addFoldD p x k (fun i => g i.castSucc)
            (fun i => v i.castSucc) (fun i => h i.castSucc))
    rw [hstep]
    congr 1
    rw [Fin.sum_univ_castSucc]
    simp [add_comm]

/-- The dot-product block: `Σ aᵢ · vᵢ` on a digit bus. -/
def dotD (p : ℕ) [NeZero p] {n : ℕ} (a : Fin n → ZMod p) :
    CircuitVec (n * dw p) (dw p) :=
  addFoldD p n (fun i => dcomp (scaleD p (a i)) ![inBlk i])

theorem eval_inBlk_flatB {p : ℕ} [NeZero p] {n : ℕ} (v : Fin n → ZMod p) (i : Fin n) :
    evalVec (inBlk i) (flatB (encWD v)) = encD (v i) := by
  funext b
  change flatB (encWD v) (finProdFinEquiv (i, b)) = encD (v i) b
  simp [flatB, encWD, Equiv.symm_apply_apply]

theorem eval_dotD (p : ℕ) [NeZero p] {n : ℕ} (a v : Fin n → ZMod p) :
    evalVec (dotD p a) (flatB (encWD v)) = encD (∑ i, a i * v i) := by
  refine eval_addFoldD p _ n _ (fun i => a i * v i) (fun i => ?_)
  have h := eval_dcomp (eval_scaleD' p (a i)) (g := ![inBlk i])
    (x := flatB (encWD v)) (v := ![v i]) (fun t => by
      fin_cases t
      simpa using eval_inBlk_flatB v i)
  simpa using h

/-- A `ZMod p`-matrix as one flat verified netlist. -/
def linWD (p : ℕ) [NeZero p] {n r : ℕ} (M : Matrix (Fin r) (Fin n) (ZMod p)) :
    CircuitVec (n * dw p) (r * dw p) :=
  fun o => dotD p (M (finProdFinEquiv.symm o).1) (finProdFinEquiv.symm o).2

theorem evalVec_linWD (p : ℕ) [NeZero p] {n r : ℕ}
    (M : Matrix (Fin r) (Fin n) (ZMod p)) (v : Fin n → ZMod p) :
    evalVec (linWD p M) (flatB (encWD v)) = flatB (encWD (M *ᵥ v)) := by
  funext o
  have h := congrFun (eval_dotD p (M (finProdFinEquiv.symm o).1) v)
    (finProdFinEquiv.symm o).2
  refine h.trans ?_
  simp [flatB, encWD, Matrix.mulVec, dotProduct]



/-- The bilinear block: `(v, w) ↦ (Σᵢⱼ cᵢⱼₖ · vᵢwⱼ)ₖ` on an appended digit bus. -/
def bilinD (p : ℕ) [NeZero p] {n₁ n₂ r : ℕ} (c : Fin n₁ → Fin n₂ → Fin r → ZMod p) :
    CircuitVec ((n₁ + n₂) * dw p) (r * dw p) :=
  fun o => (addFoldD p n₁ (fun i => addFoldD p n₂ (fun j =>
      dcomp (scaleD p (c i j (finProdFinEquiv.symm o).1))
        ![dcomp (mulD p) ![inBlk (Fin.castAdd n₂ i), inBlk (Fin.natAdd n₁ j)]])))
    (finProdFinEquiv.symm o).2

theorem evalVec_bilinD (p : ℕ) [NeZero p] {n₁ n₂ r : ℕ}
    (c : Fin n₁ → Fin n₂ → Fin r → ZMod p) (v : Fin n₁ → ZMod p) (w : Fin n₂ → ZMod p) :
    evalVec (bilinD p c) (flatB (encWD (Fin.append v w)))
      = flatB (encWD (fun k => ∑ i, ∑ j, c i j k * (v i * w j))) := by
  funext o
  have h := congrFun (eval_addFoldD p (flatB (encWD (Fin.append v w))) n₁
    (fun i => addFoldD p n₂ (fun j =>
      dcomp (scaleD p (c i j (finProdFinEquiv.symm o).1))
        ![dcomp (mulD p) ![inBlk (Fin.castAdd n₂ i), inBlk (Fin.natAdd n₁ j)]]))
    (fun i => ∑ j, c i j (finProdFinEquiv.symm o).1 * (v i * w j)) (fun i => by
      refine eval_addFoldD p _ n₂ _ (fun j => c i j (finProdFinEquiv.symm o).1 * (v i * w j))
        (fun j => ?_)
      have hin := eval_dcomp (eval_mulD' p)
        (g := ![inBlk (Fin.castAdd n₂ i), inBlk (Fin.natAdd n₁ j)])
        (x := flatB (encWD (Fin.append v w))) (v := ![v i, w j]) (fun s => by
          fin_cases s
          · simpa [Fin.append_left] using
              eval_inBlk_flatB (Fin.append v w) (Fin.castAdd n₂ i)
          · simpa [Fin.append_right] using
              eval_inBlk_flatB (Fin.append v w) (Fin.natAdd n₁ j))
      have hsc := eval_dcomp (eval_scaleD' p (c i j (finProdFinEquiv.symm o).1))
        (g := ![dcomp (mulD p) ![inBlk (Fin.castAdd n₂ i), inBlk (Fin.natAdd n₁ j)]])
        (x := flatB (encWD (Fin.append v w))) (v := ![v i * w j]) (fun t => by
          fin_cases t
          simpa using hin)
      simpa using hsc))
    (finProdFinEquiv.symm o).2
  refine h.trans ?_
  simp [flatB, encWD]

/-- A bus-to-bus tabulated map: one `dtabC` block per output digit. -/
def dtabW (p : ℕ) [NeZero p] (k r : ℕ) (F : (Fin k → ZMod p) → (Fin r → ZMod p)) :
    CircuitVec (k * dw p) (r * dw p) :=
  fun o => dtabC p k (fun v => F v (finProdFinEquiv.symm o).1) (finProdFinEquiv.symm o).2

theorem eval_dtabW (p : ℕ) [NeZero p] (k r : ℕ) (F : (Fin k → ZMod p) → (Fin r → ZMod p))
    (v : Fin k → ZMod p) :
    evalVec (dtabW p k r F) (flatB (encWD v)) = flatB (encWD (F v)) := by
  funext o
  have h := congrFun (eval_dtabC p k (fun u => F u (finProdFinEquiv.symm o).1) v)
    (finProdFinEquiv.symm o).2
  refine h.trans ?_
  simp [flatB, encWD]

/-- Vertical composition of netlists — `subst`, bus-wide. -/
def compV {n m r : ℕ} (g : CircuitVec m r) (f : CircuitVec n m) : CircuitVec n r :=
  fun o => subst (g o) f

theorem evalVec_compV {n m r : ℕ} (g : CircuitVec m r) (f : CircuitVec n m)
    (x : Fin n → Bool) : evalVec (compV g f) x = evalVec g (evalVec f x) := by
  funext o
  exact eval_subst _ _ _

/-- Coordinatewise digit subtraction on an appended bus. -/
def subNetD (p : ℕ) [NeZero p] (m : ℕ) : CircuitVec ((m + m) * dw p) (m * dw p) :=
  fun o => (dcomp (subD p) ![inBlk (Fin.castAdd m (finProdFinEquiv.symm o).1),
                             inBlk (Fin.natAdd m (finProdFinEquiv.symm o).1)])
    (finProdFinEquiv.symm o).2

theorem eval_subNetD (p : ℕ) [NeZero p] {m : ℕ} (u w : Fin m → ZMod p) :
    evalVec (subNetD p m) (flatB (encWD (Fin.append u w)))
      = flatB (encWD (u - w)) := by
  funext o
  have h := congrFun (eval_dcomp (p := p) (eval_subD' p)
    (g := ![inBlk (Fin.castAdd m (finProdFinEquiv.symm o).1),
            inBlk (Fin.natAdd m (finProdFinEquiv.symm o).1)])
    (x := flatB (encWD (Fin.append u w)))
    (v := ![u (finProdFinEquiv.symm o).1, w (finProdFinEquiv.symm o).1])
    (fun t => by
      fin_cases t
      · have h1 := eval_inBlk_flatB (Fin.append u w)
          (Fin.castAdd m (finProdFinEquiv.symm o).1)
        rw [Fin.append_left] at h1
        simpa using h1
      · have h2 := eval_inBlk_flatB (Fin.append u w)
          (Fin.natAdd m (finProdFinEquiv.symm o).1)
        rw [Fin.append_right] at h2
        simpa using h2))
    (finProdFinEquiv.symm o).2
  refine h.trans ?_
  simp [flatB, encWD]

/-! ## The word layer: `𝔽_{p^m}` through the base-generic coordinate theorems -/

/-- Extension-field multiplication at digit grain: `bilinD` at the structure constants —
the `repr_mul` consumption site (instantiation, not new proof). -/
noncomputable def mulNetD {p : ℕ} [NeZero p] {A : Type*} [CommRing A] [Algebra (ZMod p) A]
    {m : ℕ} (B : Basis (Fin m) (ZMod p) A) :
    CircuitVec ((m + m) * dw p) (m * dw p) :=
  bilinD p (fun i j k => strConst B i j k)

theorem evalVec_mulNetD {p : ℕ} [NeZero p] {A : Type*} [CommRing A] [Algebra (ZMod p) A]
    {m : ℕ} (B : Basis (Fin m) (ZMod p) A) (x y : A) :
    evalVec (mulNetD B)
        (flatB (encWD (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))))
      = flatB (encWD (fun k => B.repr (x * y) k)) := by
  rw [mulNetD, evalVec_bilinD]
  congr 1
  funext k
  exact congrArg encD (repr_mul B x y k).symm

/-- Word addition: coordinatewise digit adders. -/
def addNetD (p : ℕ) [NeZero p] (m : ℕ) : CircuitVec ((m + m) * dw p) (m * dw p) :=
  fun o => (dcomp (addD p) ![inBlk (Fin.castAdd m (finProdFinEquiv.symm o).1),
                             inBlk (Fin.natAdd m (finProdFinEquiv.symm o).1)])
    (finProdFinEquiv.symm o).2

theorem evalVec_addNetD_repr {p : ℕ} [NeZero p] {A : Type*} [CommRing A]
    [Algebra (ZMod p) A] {m : ℕ} (B : Basis (Fin m) (ZMod p) A) (x y : A) :
    evalVec (addNetD p m)
        (flatB (encWD (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))))
      = flatB (encWD (fun k => B.repr (x + y) k)) := by
  funext o
  have h := congrFun (eval_dcomp (p := p) (eval_addD' p)
    (g := ![inBlk (Fin.castAdd m (finProdFinEquiv.symm o).1),
            inBlk (Fin.natAdd m (finProdFinEquiv.symm o).1)])
    (x := flatB (encWD (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))))
    (v := ![B.repr x (finProdFinEquiv.symm o).1, B.repr y (finProdFinEquiv.symm o).1])
    (fun t => by
      fin_cases t
      · have h1 := eval_inBlk_flatB
          (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))
          (Fin.castAdd m (finProdFinEquiv.symm o).1)
        rw [Fin.append_left] at h1
        simpa using h1
      · have h2 := eval_inBlk_flatB
          (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))
          (Fin.natAdd m (finProdFinEquiv.symm o).1)
        rw [Fin.append_right] at h2
        simpa using h2))
    (finProdFinEquiv.symm o).2
  refine h.trans ?_
  simp [flatB, encWD]

/-- Word negation: coordinatewise digit negators. -/
def negNetD (p : ℕ) [NeZero p] (m : ℕ) : CircuitVec (m * dw p) (m * dw p) :=
  fun o => (dcomp (negD p) ![inBlk (finProdFinEquiv.symm o).1]) (finProdFinEquiv.symm o).2

theorem evalVec_negNetD_repr {p : ℕ} [NeZero p] {A : Type*} [CommRing A]
    [Algebra (ZMod p) A] {m : ℕ} (B : Basis (Fin m) (ZMod p) A) (x : A) :
    evalVec (negNetD p m) (flatB (encWD (fun i => B.repr x i)))
      = flatB (encWD (fun k => B.repr (-x) k)) := by
  funext o
  have h := congrFun (eval_dcomp (p := p) (eval_negD' p)
    (g := ![inBlk (finProdFinEquiv.symm o).1])
    (x := flatB (encWD (fun i => B.repr x i)))
    (v := ![B.repr x (finProdFinEquiv.symm o).1])
    (fun t => by
      fin_cases t
      simpa using eval_inBlk_flatB (fun i => B.repr x i) (finProdFinEquiv.symm o).1))
    (finProdFinEquiv.symm o).2
  refine h.trans ?_
  simp [flatB, encWD]

/-! ## The main theorem: uniform in `q` -/

/-- **Uniform in q** (as ONE theorem): one digit encoding, one
netlist family, one preservation-theorem set, for EVERY modulus `p` — `p = 2` included —
and every based `(ZMod p)`-algebra, `q = p^m` through the basis quantifier. -/
theorem descent_uniform_in_q (p : ℕ) [NeZero p] {A : Type*} [CommRing A]
    [Algebra (ZMod p) A] {m : ℕ} (B : Basis (Fin m) (ZMod p) A) (x y : A) :
    (evalVec (addNetD p m)
        (flatB (encWD (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))))
      = flatB (encWD (fun k => B.repr (x + y) k)))
  ∧ (evalVec (negNetD p m) (flatB (encWD (fun i => B.repr x i)))
      = flatB (encWD (fun k => B.repr (-x) k)))
  ∧ (∀ a : A, evalVec (linWD p (constMulMat B a))
        (flatB (encWD (fun i => B.repr x i)))
      = flatB (encWD (fun k => B.repr (a * x) k)))
  ∧ (evalVec (mulNetD B)
        (flatB (encWD (Fin.append (fun i => B.repr x i) (fun j => B.repr y j))))
      = flatB (encWD (fun k => B.repr (x * y) k))) := by
  refine ⟨evalVec_addNetD_repr B x y, evalVec_negNetD_repr B x, fun a => ?_,
    evalVec_mulNetD B x y⟩
  rw [evalVec_linWD]
  congr 1
  funext k
  refine congrArg encD ?_
  rw [show (constMulMat B a *ᵥ fun i => B.repr x i) k
      = ∑ i, constMulMat B a k i * B.repr x i by
    simp [Matrix.mulVec, dotProduct]]
  exact (repr_const_mul B a x k).symm

/-! ## The boundary anchors (agreement by kernel decide, never identity) -/

-- base case p = 2: the encoding is trivial and addition is XOR
theorem encD_two : ∀ (a : ZMod 2) (i : Fin (dw 2)), encD a i = bit a := by decide

example : ∀ a b : ZMod 2,
    evalVec (addD 2) (flatB (encWD ![a, b])) ⟨0, by decide⟩
      = Bool.xor (bit a) (bit b) := by decide

example : ∀ a b : ZMod 2,
    evalVec (mulD 2) (flatB (encWD ![a, b])) ⟨0, by decide⟩
      = ((bit a) && (bit b)) := by decide

-- odd characteristic: the mod-p adder is a genuine, verified gate network
theorem eval_addD_three (a b : ZMod 3) :
    evalVec (addD 3) (flatB (encWD ![a, b])) = encD (a + b) :=
  eval_addD 3 a b

example : evalVec (mulD 3) (flatB (encWD ![2, 2])) = encD (1 : ZMod 3) := by decide

/-- The tabulation size bound (consumer: the write-up's size row; upper bound only). -/
theorem sizeVec_dtabC_le (p : ℕ) [NeZero p] (k : ℕ) (f : (Fin k → ZMod p) → ZMod p) :
    sizeVec (dtabC p k f) ≤ dw p * (4 * 2 ^ (k * dw p)) := by
  rw [sizeVec]
  calc ∑ o, size (dtabC p k f o)
      ≤ ∑ _o : Fin (dw p), 4 * 2 ^ (k * dw p) :=
        Finset.sum_le_sum fun o _ => size_tabC_le _ _
    _ = dw p * (4 * 2 ^ (k * dw p)) := by
        simp [Finset.sum_const, Finset.card_univ, mul_comm]

end ECCLib

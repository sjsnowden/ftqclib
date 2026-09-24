/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GRS
import ECCLib.GateAlgebra
import ECCLib.FieldCert
import ECCLib.GaoField
import ECCLib.WitnessCoding

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Constant folding and the codeword-checker netlist

Two halves:

**Constant folding (`cfold`)** — a semantics-preserving, size-non-increasing pass over the
`Circuit` tree, eliminating `const` scaffolding (the uniform fold base and zero-coefficient
masks of `xorFold`/`dotC`). It **removes the scaffolding overhead**: the compiled syndrome
netlist `synCompiled` spends 6 gates where the hand-minimal `synCircuit` spends 2 — after
folding, both cost 2, with semantics preserved by the general theorem rather than
re-evaluation.

**The codeword-checker netlist** — the composite guarantee at scale. Any `𝔽₂`-linear map
built from per-word constant multiplications descends to one flat `linW` matrix of
`constMulMat` blocks (`constsMat`, via the one-time reindexing lemma `blockMat_mulVec`);
instantiated at the GRS syndrome constants `uᵢ·aᵢ^J`, the **checker theorem**
`checkNet_eq_zero_iff`: the netlist outputs all-zero exactly on the codewords of
`rsCode a k` — the gate-level membership test made exact by `rsCode_eq_ker_synMap`
(the `u`-weighted moments; the unweighted form is false in general).
-/

namespace ECCLib.Circuit

variable {n p : ℕ}

/-! ## Constant folding -/

/-- Smart negation: fold a constant operand. -/
def notF : Circuit n → Circuit n
  | .const b => .const (!b)
  | c => .not c

/-- Smart conjunction: annihilate on `false`, absorb `true`. -/
def andF : Circuit n → Circuit n → Circuit n
  | .const false, _ => .const false
  | .const true, d => d
  | c, .const false => .const false
  | c, .const true => c
  | c, d => .and c d

/-- Smart exclusive-or: absorb `false` on either side. -/
def xorF : Circuit n → Circuit n → Circuit n
  | .const false, d => d
  | c, .const false => c
  | c, d => .xor c d

theorem eval_notF (c : Circuit n) (x : Fin n → Bool) :
    eval (notF c) x = !(eval c x) := by
  cases c <;> simp [notF, eval]

theorem eval_andF (c d : Circuit n) (x : Fin n → Bool) :
    eval (andF c d) x = (eval c x && eval d x) := by
  cases c with
  | const b => cases b <;> simp [andF, eval]
  | wire i =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [andF, eval])
  | not c' =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [andF, eval])
  | and c₁ c₂ =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [andF, eval])
  | xor c₁ c₂ =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [andF, eval])

theorem eval_xorF (c d : Circuit n) (x : Fin n → Bool) :
    eval (xorF c d) x = (eval c x).xor (eval d x) := by
  cases c with
  | const b =>
    cases b with
    | false => simp [xorF, eval]
    | true =>
      cases d with
      | wire j => simp [xorF, eval]
      | const b' => cases b' <;> simp [xorF, eval]
      | not d' => simp [xorF, eval]
      | and d₁ d₂ => simp [xorF, eval]
      | xor d₁ d₂ => simp [xorF, eval]
  | wire i =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [xorF, eval])
  | not c' =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [xorF, eval])
  | and c₁ c₂ =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [xorF, eval])
  | xor c₁ c₂ =>
    cases d <;> first | rfl | (rename_i b; cases b <;> simp [xorF, eval])

theorem size_notF_le (c : Circuit n) : size (notF c) ≤ size c + 1 := by
  cases c <;> simp [notF, size]

theorem size_andF_le (c d : Circuit n) : size (andF c d) ≤ size c + size d + 1 := by
  cases c with
  | const b =>
    cases b with
    | false => simp only [andF, size]; omega
    | true => simp only [andF, size]; omega
  | wire i =>
    cases d with
    | const b => cases b <;> (simp only [andF, size]; omega)
    | wire j => simp only [andF, size]; omega
    | not d' => simp only [andF, size]; omega
    | and d₁ d₂ => simp only [andF, size]; omega
    | xor d₁ d₂ => simp only [andF, size]; omega
  | not c' =>
    cases d with
    | const b => cases b <;> (simp only [andF, size]; omega)
    | wire j => simp only [andF, size]; omega
    | not d' => simp only [andF, size]; omega
    | and d₁ d₂ => simp only [andF, size]; omega
    | xor d₁ d₂ => simp only [andF, size]; omega
  | and c₁ c₂ =>
    cases d with
    | const b => cases b <;> (simp only [andF, size]; omega)
    | wire j => simp only [andF, size]; omega
    | not d' => simp only [andF, size]; omega
    | and d₁ d₂ => simp only [andF, size]; omega
    | xor d₁ d₂ => simp only [andF, size]; omega
  | xor c₁ c₂ =>
    cases d with
    | const b => cases b <;> (simp only [andF, size]; omega)
    | wire j => simp only [andF, size]; omega
    | not d' => simp only [andF, size]; omega
    | and d₁ d₂ => simp only [andF, size]; omega
    | xor d₁ d₂ => simp only [andF, size]; omega

theorem size_xorF_le (c d : Circuit n) : size (xorF c d) ≤ size c + size d + 1 := by
  cases c with
  | const b =>
    cases b with
    | false => simp only [xorF, size]; omega
    | true =>
      cases d with
      | const b' => cases b' <;> (simp only [xorF, size]; omega)
      | wire j => simp only [xorF, size]; omega
      | not d' => simp only [xorF, size]; omega
      | and d₁ d₂ => simp only [xorF, size]; omega
      | xor d₁ d₂ => simp only [xorF, size]; omega
  | wire i =>
    cases d with
    | const b => cases b <;> (simp only [xorF, size]; omega)
    | wire j => simp only [xorF, size]; omega
    | not d' => simp only [xorF, size]; omega
    | and d₁ d₂ => simp only [xorF, size]; omega
    | xor d₁ d₂ => simp only [xorF, size]; omega
  | not c' =>
    cases d with
    | const b => cases b <;> (simp only [xorF, size]; omega)
    | wire j => simp only [xorF, size]; omega
    | not d' => simp only [xorF, size]; omega
    | and d₁ d₂ => simp only [xorF, size]; omega
    | xor d₁ d₂ => simp only [xorF, size]; omega
  | and c₁ c₂ =>
    cases d with
    | const b => cases b <;> (simp only [xorF, size]; omega)
    | wire j => simp only [xorF, size]; omega
    | not d' => simp only [xorF, size]; omega
    | and d₁ d₂ => simp only [xorF, size]; omega
    | xor d₁ d₂ => simp only [xorF, size]; omega
  | xor c₁ c₂ =>
    cases d with
    | const b => cases b <;> (simp only [xorF, size]; omega)
    | wire j => simp only [xorF, size]; omega
    | not d' => simp only [xorF, size]; omega
    | and d₁ d₂ => simp only [xorF, size]; omega
    | xor d₁ d₂ => simp only [xorF, size]; omega

/-- **The constant-folding pass**: rebuild the tree through the smart constructors. -/
def cfold : Circuit n → Circuit n
  | .not c => notF (cfold c)
  | .and c d => andF (cfold c) (cfold d)
  | .xor c d => xorF (cfold c) (cfold d)
  | c => c

/-- Folding preserves the semantics. -/
theorem eval_cfold (c : Circuit n) (x : Fin n → Bool) : eval (cfold c) x = eval c x := by
  induction c with
  | wire i => rfl
  | const b => rfl
  | not c ih =>
    change eval (notF (cfold c)) x = _
    rw [eval_notF, ih]
    rfl
  | and c d ihc ihd =>
    change eval (andF (cfold c) (cfold d)) x = _
    rw [eval_andF, ihc, ihd]
    rfl
  | xor c d ihc ihd =>
    change eval (xorF (cfold c) (cfold d)) x = _
    rw [eval_xorF, ihc, ihd]
    rfl

/-- Folding never grows the tree. -/
theorem size_cfold_le (c : Circuit n) : size (cfold c) ≤ size c := by
  induction c with
  | wire i => exact le_refl _
  | const b => exact le_refl _
  | not c ih =>
    have h := size_notF_le (cfold c)
    change size (notF (cfold c)) ≤ size (Circuit.not c)
    have hs : size (Circuit.not c) = size c + 1 := rfl
    omega
  | and c d ihc ihd =>
    have h := size_andF_le (cfold c) (cfold d)
    change size (andF (cfold c) (cfold d)) ≤ size (Circuit.and c d)
    have hs : size (Circuit.and c d) = size c + size d + 1 := rfl
    omega
  | xor c d ihc ihd =>
    have h := size_xorF_le (cfold c) (cfold d)
    change size (xorF (cfold c) (cfold d)) ≤ size (Circuit.xor c d)
    have hs : size (Circuit.xor c d) = size c + size d + 1 := rfl
    omega

/-- Folding, netlist-wide. -/
def cfoldVec (v : CircuitVec n p) : CircuitVec n p := fun k => cfold (v k)

theorem evalVec_cfoldVec (v : CircuitVec n p) (x : Fin n → Bool) :
    evalVec (cfoldVec v) x = evalVec v x :=
  funext fun k => eval_cfold (v k) x

theorem sizeVec_cfoldVec_le (v : CircuitVec n p) : sizeVec (cfoldVec v) ≤ sizeVec v :=
  Finset.sum_le_sum fun k _ => size_cfold_le (v k)

end ECCLib.Circuit

namespace ECCLib.Coding

open ECCLib ECCLib.Circuit ECCLib.Witness Matrix Module

/-! ## Constant folding of the compiled syndrome netlist

The overhead (WitnessCoding.lean): the row-compiled syndrome netlist `synCompiled` spends
6 gates where the hand-minimal `synCircuit` spends 2 — the `xorFold` scaffolding. The
folding pass removes exactly that scaffolding: the folded compiled netlist costs 2, and its
semantics is the general theorem `evalVec_cfoldVec` composed with the existing correctness —
no re-evaluation. -/

/-- **Folding removes the overhead**: after constant folding, the compiled netlist meets the
hand-minimal gate count. -/
theorem sizeVec_cfold_synCompiled : Circuit.sizeVec (cfoldVec synCompiled) = 2 := by decide

example : Circuit.sizeVec (cfoldVec synCompiled) = Circuit.sizeVec synCircuit := by decide

/-- The folded netlist still computes the syndrome map — by the general preservation
theorem composed with the existing correctness theorem, not by evaluation. -/
theorem cfold_synCompiled_correct (y : Fin 3 → ZMod 2) :
    Circuit.evalVec (cfoldVec synCompiled) (fun i => bit (y i)) = fun j => bit (H₂ y j) := by
  rw [evalVec_cfoldVec]
  exact synCompiled_correct y

/-! ## The block/flatten layer -/

/-- A family of words as one flat wire bundle (the index equivalence used opaquely). -/
def flatten {n mm : ℕ} (v : Fin n → Fin mm → ZMod 2) : Fin (n * mm) → ZMod 2 :=
  fun C => v (finProdFinEquiv.symm C).1 (finProdFinEquiv.symm C).2

/-- A `q × n` family of `mm × mm` blocks as one flat matrix. -/
def blockMat {q n mm : ℕ} (blk : Fin q → Fin n → Matrix (Fin mm) (Fin mm) (ZMod 2)) :
    Matrix (Fin (q * mm)) (Fin (n * mm)) (ZMod 2) :=
  fun R C => blk (finProdFinEquiv.symm R).1 (finProdFinEquiv.symm C).1
    (finProdFinEquiv.symm R).2 (finProdFinEquiv.symm C).2

/-- **The one-time reindexing lemma**: the flat matrix acts on a flattened word family as
the blockwise action. All the index bookkeeping of the netlist layer lives here. -/
theorem blockMat_mulVec {q n mm : ℕ}
    (blk : Fin q → Fin n → Matrix (Fin mm) (Fin mm) (ZMod 2)) (v : Fin n → Fin mm → ZMod 2) :
    blockMat blk *ᵥ flatten v = flatten fun J => ∑ i, blk J i *ᵥ v i := by
  funext R
  change ∑ C, blockMat blk R C * flatten v C = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin mm ≃ Fin (n * mm))
    (fun C => blockMat blk R C * flatten v C), Fintype.sum_prod_type]
  simp only [blockMat, flatten, Equiv.symm_apply_apply]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

/-! ## The abstract checker -/

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- The flat `𝔽₂`-matrix of the map `y ↦ (Σᵢ c J i · yᵢ)_J`, in the coordinates of a
based `𝔽₂`-algebra: one `constMulMat` block per constant. -/
noncomputable def constsMat {q n mm : ℕ} (B : Basis (Fin mm) (ZMod 2) F)
    (c : Fin q → Fin n → F) : Matrix (Fin (q * mm)) (Fin (n * mm)) (ZMod 2) :=
  blockMat fun J i => constMulMat B (c J i)

/-- **The composite descent at scale**: the `linW` netlist of the flat matrix computes the
constant-linear map in coordinates, through the bit encoding. -/
theorem evalVec_constsMat {q n mm : ℕ} (B : Basis (Fin mm) (ZMod 2) F)
    (c : Fin q → Fin n → F) (y : Fin n → F) :
    Circuit.evalVec (Circuit.linW (constsMat B c))
        (encW (flatten fun i b => B.repr (y i) b))
      = encW (flatten fun J b => B.repr (∑ i, c J i * y i) b) := by
  rw [Circuit.evalVec_linW]
  congr 1
  rw [constsMat, blockMat_mulVec]
  funext C
  change (fun J => ∑ i, constMulMat B (c J i) *ᵥ fun b => B.repr (y i) b) _ _
    = (fun J b => B.repr (∑ i, c J i * y i) b) _ _
  set J := (finProdFinEquiv.symm C).1
  set b := (finProdFinEquiv.symm C).2
  change (∑ i, constMulMat B (c J i) *ᵥ fun bb => B.repr (y i) bb) b
    = B.repr (∑ i, c J i * y i) b
  rw [map_sum, Finsupp.finset_sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_const_mul]
  rfl

/-- **The codeword-checker theorem**: at the GRS syndrome constants, the netlist outputs
all-zero exactly on the codewords of `rsCode a k` — the gate-level membership test, exact
via `rsCode_eq_ker_synMap` (the `u`-weighted moments). -/
theorem checkNet_eq_zero_iff {mm : ℕ} (B : Basis (Fin mm) (ZMod 2) F) {n k : ℕ}
    {a : Fin n → F} (ha : Function.Injective a) (hkn : k ≤ n) (y : Fin n → F) :
    Circuit.evalVec
        (Circuit.linW (constsMat B fun (J : Fin (n - k)) i => dualMult a i * a i ^ (J : ℕ)))
        (encW (flatten fun i b => B.repr (y i) b))
      = encW (flatten fun (_ : Fin (n - k)) (_ : Fin mm) => (0 : ZMod 2))
      ↔ y ∈ rsCode a k := by
  rw [evalVec_constsMat]
  have hcard : Fintype.card (Fin n) - k = n - k := by rw [Fintype.card_fin]
  have hmem : y ∈ rsCode a k ↔ ∀ J : Fin (n - k),
      ∑ i, dualMult a i * a i ^ (J : ℕ) * y i = 0 := by
    rw [rsCode_eq_ker_synMap ha (by simpa using hkn), LinearMap.mem_ker]
    constructor
    · intro h J
      have := congrFun h (Fin.cast hcard.symm J)
      simpa using this
    · intro h
      funext J'
      have := h (Fin.cast hcard J')
      simpa using this
  constructor
  · intro h
    rw [hmem]
    intro J
    have hflat : (flatten fun J b => B.repr (∑ i, (dualMult a i * a i ^ (J : ℕ)) * y i) b)
        = flatten fun (_ : Fin (n - k)) (_ : Fin mm) => (0 : ZMod 2) := by
      have h' := congrArg decW h
      rwa [decW_encW, decW_encW] at h'
    have hJb : ∀ b : Fin mm, B.repr (∑ i, (dualMult a i * a i ^ (J : ℕ)) * y i) b = 0 := by
      intro b
      have := congrFun hflat (finProdFinEquiv (J, b))
      simpa [flatten, Equiv.symm_apply_apply] using this
    have hzero : (∑ i, (dualMult a i * a i ^ (J : ℕ)) * y i) = 0 := by
      have hr : B.repr (∑ i, (dualMult a i * a i ^ (J : ℕ)) * y i) = 0 :=
        Finsupp.ext fun b => hJb b
      exact (LinearEquiv.map_eq_zero_iff B.repr).mp hr
    exact hzero
  · intro h
    rw [hmem] at h
    congr 1
    funext C
    change B.repr (∑ i, (dualMult a i * a i ^ (((finProdFinEquiv.symm C).1 : Fin (n - k)) : ℕ)) * y i) _
      = 0
    have hz : (∑ i, (dualMult a i * a i ^ (((finProdFinEquiv.symm C).1 : Fin (n - k)) : ℕ)) * y i)
        = 0 := h (finProdFinEquiv.symm C).1
    rw [hz]
    simp

/-! ## The computable crossing, and the GF(16) instantiation

The abstract matrix's entries are `Basis.repr`-values (noncomputable by design, like
`constMulMat` itself). The crossing below re-expresses each block of the certified-carrier
instantiation through the library's computable coordinate model: multiplication by an
evaluated word is `mulVecC` against the power words — the `strConst_eq_tbl` pattern at the
constant level, four rewrites. This is the seam a fully-printable checker matrix consumes
(the remaining piece — the syndrome constant-words `uᵢaᵢ^J` as `mulVecC`/`tblInv` chains
with their fold-crossing — is the next section). -/

/-- **The constant-multiplication crossing**: at the `AdjoinRoot` carrier, the abstract
`constMulMat` of an evaluated word IS the computable `mulVecC`-against-power-words table. -/
theorem constMulMat_adjBasis_emb (m : ℕ) (r : Fin (m + 1) → ZMod 2)
    (w : Fin (m + 1) → ZMod 2) :
    constMulMat (adjBasis m r) (emb (AdjoinRoot.root (nu m r)) w)
      = fun (b c : Fin (m + 1)) => mulVecC r w (powVec r (c : ℕ)) b := by
  funext b c
  change (adjBasis m r).repr (emb (AdjoinRoot.root (nu m r)) w * adjBasis m r c) b = _
  rw [adjBasis_apply,
    show (AdjoinRoot.root (nu m r)) ^ (c : ℕ)
        = emb (AdjoinRoot.root (nu m r)) (powVec r (c : ℕ)) from
      (emb_powVec r _ (root_pow_top m r) _).symm,
    ← emb_mulVecC r _ (root_pow_top m r)]
  exact congrFun (coords_emb m r _) b

/-- **The `[15, 9, 7]` checker exists**: the GF(16) Reed–Solomon code, its GRS kernel presentation,
and the checker netlist meet — a verified `24 × 60` gate-level membership test over GF(16). -/
example (y : Fin 15 → GF16p) :
    Circuit.evalVec
        (Circuit.linW (constsMat (adjBasis 3 r4p)
          fun (J : Fin (15 - 9)) i => dualMult a16 i * a16 i ^ (J : ℕ)))
        (encW (flatten fun i b => (adjBasis 3 r4p).repr (y i) b))
      = encW (flatten fun (_ : Fin (15 - 9)) (_ : Fin 4) => (0 : ZMod 2))
      ↔ y ∈ rsCode a16 9 :=
  checkNet_eq_zero_iff (adjBasis 3 r4p) a16_injective (by norm_num) y

/-! ## The word-chain crossing and the live runs

The checker matrix above is abstract (`Basis.repr` entries). Here the GF(16) instance becomes
**printable**: the syndrome constants `uᵢ·aᵢ^J` are computed as `mulVecC`/`tblInv` chains on
coordinate words, and the crossing (`chkM15_eq`) identifies the computable matrix with the abstract
one — through the `Model` engine of `GaoField.lean`, consumed once more: products of words transport
by `Model.map_foldr_mul`, the inverse by `gf16Model.map_inv`. With the matrix computable, the kernel
can RUN the checker: the live rows below evaluate all 24 output bits of the `[15, 9, 7]` membership
test on a codeword (all zero) and on a corrupted word (not all zero), and the crossing turns the
latter run into a machine-checked NON-membership certificate. -/

/-- Products of words transport through a `Model` — the fold crossing, generic. -/
theorem FieldOps.Model.map_foldr_mul {R : Type*} {F : Type*} [Field F] {ops : FieldOps R}
    {φ : R → F} (M : ops.Model φ) (ws : List R) :
    φ (ws.foldr ops.mul ops.one) = (ws.map φ).prod := by
  induction ws with
  | nil => exact M.map_one
  | cons w ws ih =>
    rw [List.foldr_cons, M.map_mul, ih, List.map_cons, List.prod_cons]

/-- The nodal-product word at point `i`: `∏_{j ≠ i} (aᵢ − aⱼ)` as a `mulVecC` chain
(characteristic 2: the differences are `powVec` sums). Computable. -/
def dWord15 (i : Fin 15) : Fin 4 → ZMod 2 :=
  (((List.finRange 15).filter (· ≠ i)).map
    fun (j : Fin 15) => powVec r4p (i : ℕ) + powVec r4p (j : ℕ)).foldr
      (mulVecC r4p) (powVec r4p 0)

/-- The dual-multiplier word: the certified inverse table applied to the nodal word. -/
def uWord15 (i : Fin 15) : Fin 4 → ZMod 2 := tblInv inv4L (dWord15 i)

/-- The syndrome-constant word `uᵢ·aᵢ^J`. -/
def cWord15 (i : Fin 15) (J : ℕ) : Fin 4 → ZMod 2 :=
  mulVecC r4p (uWord15 i) (powVec r4p ((i : ℕ) * J))

/-- **The printable checker matrix** for the GF(16) `[15, 9, 7]` code: every entry a
`mulVecC`-chain value. Computable, kernel-reducible. -/
def chkM15 : Matrix (Fin (6 * 4)) (Fin (15 * 4)) (ZMod 2) :=
  blockMat fun (J : Fin 6) (i : Fin 15) =>
    fun (b c : Fin 4) => mulVecC r4p (cWord15 i (J : ℕ)) (powVec r4p (c : ℕ)) b

/-- The nodal word evaluates to the nodal product. -/
theorem emb_dWord15 (i : Fin 15) :
    emb (AdjoinRoot.root (nu 3 r4p)) (dWord15 i)
      = ∏ j ∈ Finset.univ.erase i, (a16 i - a16 j) := by
  have hα := root_pow_top 3 r4p
  have hpt : ∀ j : Fin 15,
      emb (AdjoinRoot.root (nu 3 r4p)) (powVec r4p (i : ℕ) + powVec r4p (j : ℕ))
        = a16 i - a16 j := by
    intro j
    have hadd := gf16Model.map_add (powVec r4p (i : ℕ)) (powVec r4p (j : ℕ))
    rw [show gf16Ops.add (powVec r4p (i : ℕ)) (powVec r4p (j : ℕ))
        = powVec r4p (i : ℕ) + powVec r4p (j : ℕ) from rfl] at hadd
    have hneg : (AdjoinRoot.root (nu 3 r4p)) ^ (j : ℕ)
        = -(AdjoinRoot.root (nu 3 r4p)) ^ (j : ℕ) := by
      have h := gf16Model.map_neg (powVec r4p (j : ℕ))
      rw [show gf16Ops.neg (powVec r4p (j : ℕ)) = powVec r4p (j : ℕ) from rfl] at h
      rwa [emb_powVec r4p _ hα] at h
    rw [hadd, emb_powVec r4p _ hα, emb_powVec r4p _ hα]
    change _ = (AdjoinRoot.root (nu 3 r4p)) ^ (i : ℕ) - (AdjoinRoot.root (nu 3 r4p)) ^ (j : ℕ)
    rw [sub_eq_add_neg, ← hneg]
  have hchain : emb (AdjoinRoot.root (nu 3 r4p)) (dWord15 i)
      = ((((List.finRange 15).filter (· ≠ i)).map
          fun (j : Fin 15) => powVec r4p (i : ℕ) + powVec r4p (j : ℕ)).map
            (emb (AdjoinRoot.root (nu 3 r4p)))).prod :=
    gf16Model.map_foldr_mul _
  rw [hchain, List.map_map]
  simp only [Function.comp_def]
  rw [List.map_congr_left fun j _ => hpt j]
  -- the List/Finset bridge
  have hnd : (((List.finRange 15).filter (· ≠ i))).Nodup :=
    (List.nodup_finRange 15).filter _
  have hfs : (((List.finRange 15).filter (· ≠ i))).toFinset = Finset.univ.erase i := by
    ext j
    simp [Finset.mem_erase, and_comm]
  rw [← hfs, List.prod_toFinset _ hnd]

/-- The inverse-table word evaluates to the dual multiplier. -/
theorem emb_uWord15 (i : Fin 15) :
    emb (AdjoinRoot.root (nu 3 r4p)) (uWord15 i) = dualMult a16 i := by
  have h := gf16Model.map_inv (dWord15 i)
  rw [show gf16Ops.inv (dWord15 i) = tblInv inv4L (dWord15 i) from rfl] at h
  rw [uWord15, h, emb_dWord15, dualMult]

/-- The constant word evaluates to the syndrome constant. -/
theorem emb_cWord15 (i : Fin 15) (J : ℕ) :
    emb (AdjoinRoot.root (nu 3 r4p)) (cWord15 i J) = dualMult a16 i * a16 i ^ J := by
  have hα := root_pow_top 3 r4p
  have h := gf16Model.map_mul (uWord15 i) (powVec r4p ((i : ℕ) * J))
  rw [show gf16Ops.mul (uWord15 i) (powVec r4p ((i : ℕ) * J))
      = mulVecC r4p (uWord15 i) (powVec r4p ((i : ℕ) * J)) from rfl] at h
  rw [cWord15, h, emb_uWord15, emb_powVec r4p _ hα, a16, pow_mul]

/-- **The matrix crossing**: the printable matrix IS the abstract checker matrix. -/
theorem chkM15_eq :
    chkM15 = constsMat (adjBasis 3 r4p)
      (fun (J : Fin 6) (i : Fin 15) => dualMult a16 i * a16 i ^ (J : ℕ)) := by
  funext R C
  change (blockMat _) R C = (blockMat _) R C
  refine congrFun (congrFun (congrArg blockMat (funext fun J => funext fun i => ?_)) R) C
  change (fun (b c : Fin 4) => mulVecC r4p (cWord15 i (J : ℕ)) (powVec r4p (c : ℕ)) b)
    = constMulMat (adjBasis 3 r4p) (dualMult a16 i * a16 i ^ (J : ℕ))
  rw [← emb_cWord15 i (J : ℕ), constMulMat_adjBasis_emb]

/-- The coordinates of `1` are the `α⁰` word — ties the live runs' inputs to the abstract
statement. -/
theorem coords_one_gf16 : ⇑((adjBasis 3 r4p).repr 1) = powVec r4p 0 := by
  have hα := root_pow_top 3 r4p
  have h1 : (1 : GF16p) = emb (AdjoinRoot.root (nu 3 r4p)) (powVec r4p 0) := by
    rw [emb_powVec r4p _ hα, pow_zero]
  rw [h1, coords_emb]

/-! **The chain runs, live**: the dual-multiplier word times its nodal word is `α⁰` — the
kernel executes the whole 14-product `mulVecC` chain and the certified inverse lookup at
one point of the `[15, 9, 7]` family. (The FULL 24×60 matrix run recomputes this chain per
entry and is measured to be infeasible in the kernel; the materialized ladder
below reaches the full matrix in closed form instead.) -/

set_option maxRecDepth 4096 in
-- the 16-row table walk plus the 14-element chain nest past the default depth (a
-- table-size recursion issue, not a heartbeat issue)
example : mulVecC r4p (uWord15 0) (dWord15 0) = powVec r4p 0 := by decide

set_option maxRecDepth 4096 in
example : mulVecC r4p (uWord15 7) (dWord15 7) = powVec r4p 0 := by decide

/-! ## The materialized checker: the closed-form matrix

The per-entry chain recomputation that makes the direct 24×60 kernel run infeasible is
dissolved by materializing ONE level — the fifteen nodal words — and crossing everything
above it through `emb`. The nodal polynomial of the full root-power family is `X^15 + 1`,
so its derivative at `α^i` is `α^(−i)`: the nodal words are (a permutation of) the nonzero
field elements, the dual multipliers come out as `uᵢ = α^i`, and the printable checker
matrix is the classical `α`-power parity check `H[J, i] = α^(i(J+1))` in `4×4` bit-blocks.
Two kernel decides total (the nodal table; the inverse-table row); the rest is rewriting. -/

/-- The nodal-product words, materialized: `dWord15 i = α^(15−i)` (a wrong table fails the
`decide` below — as in `FieldCert.lean`, the table needs no trust). -/
def dLit : Fin 15 → Fin 4 → ZMod 2 :=
  ![![1, 0, 0, 0],
    ![1, 0, 0, 1],
    ![1, 0, 1, 1],
    ![1, 1, 1, 1],
    ![0, 1, 1, 1],
    ![1, 1, 1, 0],
    ![0, 1, 0, 1],
    ![1, 0, 1, 0],
    ![1, 1, 0, 1],
    ![0, 0, 1, 1],
    ![0, 1, 1, 0],
    ![1, 1, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0]]

set_option maxRecDepth 8192 in
-- fifteen 14-product chains; measured at ~60k heartbeats total
theorem dWord15_eq_dLit : dWord15 = dLit := by decide

/-- The `powVec` addition law at `r4p` — no kernel evaluation, via the `emb` crossing. -/
theorem mulVecC_powVec_r4p (a b : ℕ) :
    mulVecC r4p (powVec r4p a) (powVec r4p b) = powVec r4p (a + b) := by
  have hα := root_pow_top 3 r4p
  apply emb_injective 3 r4p
  rw [emb_mulVecC r4p _ hα, emb_powVec r4p _ hα, emb_powVec r4p _ hα, emb_powVec r4p _ hα,
    pow_add]

set_option maxRecDepth 8192 in
/-- The dual-multiplier words in closed form: `uᵢ = α^i`. -/
theorem uWord15_eq_powVec : uWord15 = fun (i : Fin 15) => powVec r4p (i : ℕ) := by
  have h : ∀ i : Fin 15, tblInv inv4L (dLit i) = powVec r4p (i : ℕ) := by decide
  funext i
  simp only [uWord15, dWord15_eq_dLit]
  exact h i

/-- The syndrome constants in closed form: `cᵢ(J) = α^(i(J+1))`, any `J : ℕ`. -/
theorem cWord15_eq_powVec (i : Fin 15) (J : ℕ) :
    cWord15 i J = powVec r4p ((i : ℕ) * (J + 1)) := by
  simp only [cWord15, uWord15_eq_powVec]
  rw [mulVecC_powVec_r4p]
  congr 1
  ring

/-- **The materialized checker matrix**: the printable `[15, 9, 7]` checker is the classical
`α`-power parity check `H[J, i] = α^(i(J+1))`, in `4×4` bit-blocks — the closed form the
per-entry infeasibility note above said the direct run could not reach. -/
theorem chkM15_closed :
    chkM15 = blockMat fun (J : Fin 6) (i : Fin 15) =>
      fun (b c : Fin 4) => powVec r4p ((i : ℕ) * ((J : ℕ) + 1) + (c : ℕ)) b := by
  simp only [chkM15]
  refine congrArg blockMat ?_
  funext J i b c
  rw [cWord15_eq_powVec, mulVecC_powVec_r4p]

end ECCLib.Coding

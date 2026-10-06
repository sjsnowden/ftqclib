/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.FrameCategory
import FTQCLib.Hilbert.GateLifts
import FTQCLib.Hilbert.Diagonal
import FTQCLib.Hilbert.BornCollapse
import FTQCLib.Hierarchy.RzHardness
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Hilbert semantics of the protocol syntax and its Kraus family

T17 (`docs/TARGETS.md`). A protocol term `p : Protocol m n k` (T14, `Carrier/Protocol.lean`) on
`n` data bits with `k` outcome bits has a **Hilbert semantics** `hilbertSem p`, written `⟦p⟧`: a
linear map `ℂ^{2^n} → ℂ^{2^n} ⊗ ℂ^{2^k}`, here `QubitSpace n →ₗ[ℂ] QubitSpace (n + k)`, the data
bits first and the outcome bits last, in the order their letters occur (T14's convention: the
`j`-th conditioning letter creates bit `Fin.natAdd n j`, so a register word is `Fin.append y o`).

**Defined by induction on the term, from the Hilbert side's own operators**, and independently of
the frame: nothing here is defined through `Protocol.interpretAmp`, `runAmp`, `letterAmp`,
`pauliProjection` or `charOf`, so that T20's equality of `interpretAmp` with `⟦p⟧` is a theorem and
not a definition.

* The empty term is the identity, `ℂ^{2^n} = ℂ^{2^n} ⊗ ℂ^{2^0}`.
* A gate word is its unitary on **all current free bits, data and outcome alike** (`wordGate`):
  `hadamardGate`, `diagonalGate` at the letter's radian phase `DiagPhase.realPhase`, and
  `cnotGate`, on `QubitSpace (n + k)`. A letter may name an outcome bit as any other bit: H on it,
  a CNOT targeting it, or a diagonal exponent reading it.
* A conditioning letter on the signed Pauli `P` is `conditionIsometry P`, the map
  `ψ ↦ Σ_b Π_b ψ ⊗ e_b`, `Π_b` the Born projector onto the `(−1)^b`-eigenspace of `(−1)^s P`
  (`bornProjection`, which is `bornProjector P ((−1)^{s+b})` transported to `QubitSpace`), and
  `e_b` the basis vector of the new last bit (`appendOutcome` at the one-bit string `b`).

`⟦p⟧` is an isometry for the ℓ² norm (`hilbertSem_isometry`, read through `toQState`).

**The Kraus family** is read off `⟦p⟧` by evaluation: `kraus p o` is the matrix of
`K_o = (I ⊗ ⟨o|) ⟦p⟧`, the outcome bits evaluated at the string `o` (`evalOutcome`;
`kraus_mulVec`), and `Σ_o K_o† K_o = 1` (`kraus_sum_eq_one`). The `K_o` are whatever the term makes
them: a word may act on an outcome bit, and then `K_o` need not be a product of a projector and a
unitary (T17's row `H1`: Z-conditioning, then H on the outcome bit, gives `K_o = Z^o/√2`).

**The product form** holds only under `OutcomeControlsOnly p`: every outcome bit is used only as a
control, in a diagonal letter's exponent or as a CNOT's control, never as an H's bit or a CNOT's
target, and no conditioning Pauli touches an outcome bit. Then `K_o` is `krausProduct p o`, the
product in term order of the Born projectors of the conditioning letters' data parts at their
outcomes and the unitaries `wordAt w o` the words give at `o` (`kraus_eq_prod_of_controlsOnly`).

**The functor** from T46's category (`FrameCategory`) to linear maps: `homMatrix f`, the amplitude
of a morphism as a matrix, `M_f(y, x) = f(x, y)`, is well defined on `StateEq` classes; it sends
composition to the matrix product (`homMatrix_comp`) and the identity to `1` (`homMatrix_id`), and
`ampFunctor` is the functor into `ModuleCat ℂ` sending `f` to `Matrix.toLin' (homMatrix f)`.

## Main definitions

* `letterGate`, `wordGate` — a gate letter's and a gate word's unitary on all free bits.
* `bornProjection` — the Born projector `Π_b` of a signed Pauli, on `QubitSpace`.
* `appendOutcome`, `evalOutcome` — `φ ↦ φ ⊗ e_o` and `(I ⊗ ⟨o|)`, on the last bits.
* `conditionIsometry` — `ψ ↦ Σ_b Π_b ψ ⊗ e_b`.
* `hilbertSem` — `⟦p⟧`, by induction on the term.
* `kraus` — the Kraus operator `K_o` as a matrix, the evaluation of `⟦p⟧` at `o`.
* `LetterControlsOnly`, `OutcomeControlsOnly` — outcome bits used only as controls.
* `restrictDataPauli`, `wordAt`, `krausProduct` — the factors of the product form and the product.
* `homMatrix`, `ampFunctor` — the functor from T46's category to linear maps.

## Main results

* `hilbertSem_isometry` — `⟦p⟧` preserves the ℓ² norm (proved at T17.3).
* `kraus_sum_eq_one` — `Σ_o K_o† K_o = 1` (proved at T17.3).
* `kraus_eq_prod_of_controlsOnly` — under `OutcomeControlsOnly p`, `K_o` is the product form
  (proved at T17.3).
* `kraus_mulVec` — `K_o ψ` is `⟦p⟧ ψ` evaluated at the outcome string `o`.
* `homMatrix_comp`, `homMatrix_id` — the functor laws.

## Implementation notes

* `⟦p⟧` lives on `QubitSpace` (functions), where the gates live; the Born projector lives on
  `QState` (the ℓ² space) and is transported by `toQState`, which is the identity on functions.
  Norms and adjoints are read through `toQState` or on matrices, since `QubitSpace` carries the
  sup norm.
* The diagonal letter `D` acts by `diagonalGate (DiagPhase.realPhase D)`, the multiplication by
  `exp(i·2π·D(w)/2^m)`. That it agrees with the frame's referee is T18, not a definition here.
* The Born projector's sign: a `SignedPauli` is `(−1)^s` times the Hermitian Pauli, so the
  `(−1)^b`-eigenspace projector is `½(I + (−1)^{s+b} H(P))`, `bornProjector` at `ε = (−1)^{s+b}`.
  That it agrees with the frame's `pauliProjection` is T19.
* T14's `Protocol` has no composition or tensor constructor, so "composition and tensor are
  composition and tensor" is a property of derived operations, not a case of the induction; on
  T46's side it is `homMatrix_comp` and Mathlib's functor laws.
* In the product form, a word's factor at `o` is `wordAt w o = (I ⊗ ⟨o|) W (I ⊗ |o⟩)`: under the
  predicate `W` maps `φ ⊗ |o⟩` to `W(o) φ ⊗ |o⟩`, so this reads off the unitary the word gives at
  `o`. A conditioning letter's factor is the Born projector of its Pauli's data part, which under
  the predicate is the whole Pauli. Without the predicate both are still defined, and the product
  differs from `K_o` (row `H1`).
* No `-- source:` citation: T17's section in `docs/TARGETS.md` names no corpus papers. The Kraus
  family read off an isometry is Knill and Laflamme's `A_a = ⟨μ_a| U |e⟩`, and the Born projector
  Gottesman's `½(I ± A)` (`docs/fidelity/T17.md`, Claims 7 and 11).

## References

* E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, arXiv:quant-ph/9604034:
  operators of an evolution read off an isometry, `Σ_a A_a† A_a = I`.
* D. Gottesman, *The Heisenberg representation of quantum computers*, arXiv:quant-ph/9807006: the
  projectors `½(I ± A)` of a Pauli measurement.
* V. Danos, E. Kashefi and P. Panangaden, *The measurement calculus*, arXiv:quant-ph/0412135: the
  branches of a pattern by applying its commands in sequence; here an outcome is a free bit (D2),
  so a word may act on it, which the calculus does not allow.
-/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame.Walkthrough
open scoped Matrix Kronecker

variable {m n : ℕ}

/-! ## The letters' operators -/

/-- **A gate letter's unitary** on all `N` free bits: H on bit `j` (`hadamardGate`), the diagonal
gate at the letter's radian phase `2π·D(w)/2^m` (`diagonalGate`), and CNOT with control `i` and
target `j` (`cnotGate`). The bits are any bits of `Fin N`, outcome bits included. -/
noncomputable def letterGate {N : ℕ} : GateLetter N m → (QubitSpace N →ₗ[ℂ] QubitSpace N)
  | .hadamard j => hadamardGate j
  | .diagonal D => diagonalGate (DiagPhase.realPhase D)
  | .cnot i j hij => (cnotGate i j hij).toLinearMap

/-- **A gate word's unitary** on all `N` free bits: the letters' unitaries composed, head letter
first, as T05's run applies them. -/
noncomputable def wordGate {N : ℕ} : GateWord N m → (QubitSpace N →ₗ[ℂ] QubitSpace N)
  | [] => LinearMap.id
  | g :: gs => wordGate gs ∘ₗ letterGate g

/-- **The Born projector** `Π_b` of a signed Pauli `P = (−1)^s H(Q)`, on `QubitSpace`: the
projector `½(I + (−1)^{s+b} H(Q))` onto the `(−1)^b`-eigenspace of `P` (`bornProjector` at
`ε = (−1)^{s+b}`), transported along `toQState`. -/
noncomputable def bornProjection {N : ℕ} (P : SignedPauli N) (b : ZMod 2) :
    QubitSpace N →ₗ[ℂ] QubitSpace N :=
  toQState.symm.toLinearMap ∘ₗ bornProjector P.pauli ((-1 : ℂ) ^ (P.sign.val + b.val)) ∘ₗ
    toQState.toLinearMap

/-- **`φ ↦ φ ⊗ e_o`**: a function of the first `N` bits tensored with the basis vector of the
string `o` on `k` new last bits. -/
noncomputable def appendOutcome (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) :
    QubitSpace N →ₗ[ℂ] QubitSpace (N + k) where
  toFun φ v := if v ∘ Fin.natAdd N = o then φ (v ∘ Fin.castAdd k) else 0
  map_add' φ χ := by
    funext v
    by_cases h : v ∘ Fin.natAdd N = o
    · simp only [Pi.add_apply, if_pos h]
    · simp only [Pi.add_apply, if_neg h, add_zero]
  map_smul' c φ := by
    funext v
    by_cases h : v ∘ Fin.natAdd N = o
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, if_pos h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, if_neg h, mul_zero]

/-- **`(I ⊗ ⟨o|)`**: the last `k` bits evaluated at the string `o`, the register word read as
`Fin.append y o`. -/
noncomputable def evalOutcome (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) :
    QubitSpace (N + k) →ₗ[ℂ] QubitSpace N :=
  LinearMap.funLeft ℂ ℂ (fun y : Fin N → ZMod 2 => Fin.append y o)

/-- **A conditioning letter's isometry** `ψ ↦ Σ_b Π_b ψ ⊗ e_b`: the Born projector at each outcome
`b`, the outcome a new last bit. -/
noncomputable def conditionIsometry {N : ℕ} (P : SignedPauli N) :
    QubitSpace N →ₗ[ℂ] QubitSpace (N + 1) :=
  ∑ b : ZMod 2, appendOutcome N (fun _ : Fin 1 => b) ∘ₗ bornProjection P b

/-! ## The semantics -/

/-- **The Hilbert semantics** `⟦p⟧ : ℂ^{2^n} → ℂ^{2^n} ⊗ ℂ^{2^k}`, by induction on the term: the
empty term is the identity, a gate word is its unitary on all `n + k` current free bits after
`⟦p⟧`, and a conditioning letter is its isometry after `⟦p⟧`, the outcome a new last bit. -/
noncomputable def hilbertSem : {k : ℕ} → Protocol m n k → (QubitSpace n →ₗ[ℂ] QubitSpace (n + k))
  | _, .nil => LinearMap.id
  | _, .word p w => wordGate w ∘ₗ hilbertSem p
  | _, .condition p P _ => conditionIsometry P ∘ₗ hilbertSem p

@[simp] theorem hilbertSem_nil : hilbertSem (.nil : Protocol m n 0) = LinearMap.id :=
  rfl

@[simp] theorem hilbertSem_word {k : ℕ} (p : Protocol m n k) (w : GateWord (n + k) m) :
    hilbertSem (p.word w) = wordGate w ∘ₗ hilbertSem p :=
  rfl

@[simp] theorem hilbertSem_condition {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) :
    hilbertSem (p.condition P hP) = conditionIsometry P ∘ₗ hilbertSem p :=
  rfl

/-! ### Private: the ℓ² inner product on `QubitSpace` and the maps that keep it -/

/-- The cons equation of `wordGate`, stated privately so that no equation lemma is added to the
statement. -/
private theorem wordGate_cons {N : ℕ} (g : GateLetter N m) (gs : GateWord N m) :
    wordGate (g :: gs) = wordGate gs ∘ₗ letterGate g :=
  rfl

/-- The ℓ² inner product of two functions, read through `toQState`. -/
private noncomputable def innerQ {N : ℕ} (ψ φ : QubitSpace N) : ℂ :=
  inner ℂ (toQState ψ) (toQState φ)

private theorem innerQ_eq_sum {N : ℕ} (ψ φ : QubitSpace N) :
    innerQ ψ φ = ∑ v, star (ψ v) * φ v := by
  rw [innerQ, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [RCLike.inner_apply, mul_comm]
  rfl

/-- A linear map keeps the ℓ² inner product. -/
private def KeepsInner {a b : ℕ} (L : QubitSpace a →ₗ[ℂ] QubitSpace b) : Prop :=
  ∀ ψ φ, innerQ (L ψ) (L φ) = innerQ ψ φ

private theorem keepsInner_id {a : ℕ} :
    KeepsInner (LinearMap.id : QubitSpace a →ₗ[ℂ] QubitSpace a) :=
  fun _ _ => rfl

private theorem keepsInner_comp {a b c : ℕ} {L : QubitSpace b →ₗ[ℂ] QubitSpace c}
    {M : QubitSpace a →ₗ[ℂ] QubitSpace b} (hL : KeepsInner L) (hM : KeepsInner M) :
    KeepsInner (L ∘ₗ M) :=
  fun ψ φ => (hL (M ψ) (M φ)).trans (hM ψ φ)

/-- A sum over `ZMod 2` is the two-term sum. -/
private theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- A sum over the words on `N + k` bits is a sum over the last `k` bits of a sum over the first
`N`, the word read as `Fin.append y o`. -/
private theorem sum_append {M : Type*} [AddCommMonoid M] {N k : ℕ}
    (F : (Fin (N + k) → ZMod 2) → M) :
    ∑ o : Fin k → ZMod 2, ∑ y : Fin N → ZMod 2, F (Fin.append y o) = ∑ v, F v := by
  rw [← (Fin.appendEquiv N k).sum_comp, Fintype.sum_prod_type_right]
  rfl

private theorem keepsInner_diagonal {N : ℕ} (f : (Fin N → ZMod 2) → ℝ) :
    KeepsInner (diagonalGate f) := by
  intro ψ φ
  rw [innerQ_eq_sum, innerQ_eq_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [diagonalGate_apply, diagonalGate_apply, star_mul']
  have hphase : star (Complex.exp (Complex.I * f v)) * Complex.exp (Complex.I * f v) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_I_mul_ofReal]
    norm_num
  linear_combination (star (ψ v) * φ v) * hphase

private theorem keepsInner_cnot {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    KeepsInner (cnotGate i j hij).toLinearMap := by
  intro ψ φ
  rw [innerQ_eq_sum, innerQ_eq_sum]
  simp only [LinearEquiv.coe_coe, cnotGate_apply]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (cnotPerm_involutive i j hij))
    (fun v => star (ψ v) * φ v)

private theorem keepsInner_hadamard {N : ℕ} (k : Fin N) : KeepsInner (hadamardGate k) := by
  intro ψ φ
  cases N with
  | zero => exact k.elim0
  | succ N =>
    rw [innerQ_eq_sum, innerQ_eq_sum, ← (Fin.insertNthEquiv (fun _ => ZMod 2) k).sum_comp,
      ← (Fin.insertNthEquiv (fun _ => ZMod 2) k).sum_comp, Fintype.sum_prod_type_right,
      Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hins : ∀ a : ZMod 2, Fin.insertNthEquiv (fun _ => ZMod 2) k (a, y) = k.insertNth a y :=
      fun _ => rfl
    simp only [hins, hadamardGate_apply, Fin.insertNth_apply_same, Fin.update_insertNth,
      sum_zmod2]
    have hc : star invSqrt2 = invSqrt2 := by
      rw [invSqrt2, Complex.star_def, Complex.conj_ofReal]
    simp only [ZMod.val_zero, mul_zero, pow_zero, one_mul, star_mul', star_add, hc,
      ZMod.val_one, mul_one, pow_one, star_neg, neg_one_mul]
    linear_combination (2 * (star (ψ (k.insertNth 0 y)) * φ (k.insertNth 0 y)
      + star (ψ (k.insertNth 1 y)) * φ (k.insertNth 1 y))) * invSqrt2_mul_self

private theorem keepsInner_letterGate {N : ℕ} (g : GateLetter N m) : KeepsInner (letterGate g) := by
  cases g with
  | hadamard j => exact keepsInner_hadamard j
  | diagonal D => exact keepsInner_diagonal _
  | cnot i j hij => exact keepsInner_cnot i j hij

private theorem keepsInner_wordGate {N : ℕ} (w : GateWord N m) : KeepsInner (wordGate w) := by
  induction w with
  | nil => exact keepsInner_id
  | cons g gs ih => exact keepsInner_comp ih (keepsInner_letterGate g)

private theorem toQState_bornProjection {N : ℕ} (P : SignedPauli N) (b : ZMod 2)
    (ψ : QubitSpace N) :
    toQState (bornProjection P b ψ)
      = bornProjector P.pauli ((-1 : ℂ) ^ (P.sign.val + b.val)) (toQState ψ) := by
  simp only [bornProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- The two Born projectors of a signed Pauli together keep the inner product:
`Σ_b ⟨Π_b ψ, Π_b φ⟩ = ⟨ψ, φ⟩`, since `H(Q)` keeps it and the two signs cancel. -/
private theorem sum_innerQ_bornProjection {N : ℕ} (P : SignedPauli N) (ψ φ : QubitSpace N) :
    ∑ b : ZMod 2, innerQ (bornProjection P b ψ) (bornProjection P b φ) = innerQ ψ φ := by
  simp only [innerQ, toQState_bornProjection, bornProjector, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, pauliHermitian_inner, sum_zmod2, ZMod.val_zero, ZMod.val_one, add_zero,
    pow_succ, map_mul, map_neg, map_one]
  have hsign : starRingEnd ℂ ((-1 : ℂ) ^ P.sign.val) = (-1 : ℂ) ^ P.sign.val := by
    simp only [map_pow, map_neg, map_one]
  have hsq : (-1 : ℂ) ^ P.sign.val * (-1 : ℂ) ^ P.sign.val = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hhalf : starRingEnd ℂ (2⁻¹ : ℂ) = 2⁻¹ := by
    simp only [map_inv₀, map_ofNat]
  rw [hsign, hhalf]
  linear_combination (2⁻¹ : ℂ) * inner ℂ (toQState ψ) (toQState φ) * hsq

private theorem appendOutcome_apply (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) (φ : QubitSpace N)
    (v : Fin (N + k) → ZMod 2) :
    appendOutcome N o φ v = if v ∘ Fin.natAdd N = o then φ (v ∘ Fin.castAdd k) else 0 :=
  rfl

private theorem evalOutcome_apply (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) (ψ : QubitSpace (N + k))
    (y : Fin N → ZMod 2) :
    evalOutcome N o ψ y = ψ (Fin.append y o) :=
  rfl

/-- `⟦P⟧ φ` at the word `(u, t)` is the Born projector at the outcome `t 0`, at `u`. -/
private theorem conditionIsometry_append {N : ℕ} (P : SignedPauli N) (φ : QubitSpace N)
    (u : Fin N → ZMod 2) (t : Fin 1 → ZMod 2) :
    conditionIsometry P φ (Fin.append u t) = bornProjection P (t 0) φ u := by
  simp only [conditionIsometry, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    appendOutcome_apply, append_comp_natAdd, append_comp_castAdd]
  rw [Finset.sum_eq_single (t 0)]
  · rw [if_pos (funext fun i => by rw [Subsingleton.elim i 0])]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (congrFun h 0).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem keepsInner_conditionIsometry {N : ℕ} (P : SignedPauli N) :
    KeepsInner (conditionIsometry P) := by
  intro ψ φ
  rw [innerQ_eq_sum, ← sum_append]
  simp only [conditionIsometry_append]
  rw [← (Equiv.funUnique (Fin 1) (ZMod 2)).symm.sum_comp, ← sum_innerQ_bornProjection P ψ φ]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, innerQ_eq_sum]

private theorem keepsInner_hilbertSem {k : ℕ} (p : Protocol m n k) :
    KeepsInner (hilbertSem p) := by
  induction p with
  | nil => exact keepsInner_id
  | word p w ih => exact keepsInner_comp (keepsInner_wordGate w) ih
  | condition p P hP ih => exact keepsInner_comp (keepsInner_conditionIsometry P) ih

/-- **`⟦p⟧` is an isometry**: it preserves the ℓ² norm, read through `toQState`. -/
theorem hilbertSem_isometry {k : ℕ} (p : Protocol m n k) (ψ : QubitSpace n) :
    ‖toQState (hilbertSem p ψ)‖ = ‖toQState ψ‖ := by
  have h := keepsInner_hilbertSem p ψ ψ
  rw [innerQ, innerQ, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖toQState (hilbertSem p ψ)‖ ^ 2 = ‖toQState ψ‖ ^ 2 := by
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

/-! ## The Kraus family -/

/-- **The Kraus operator** `K_o = (I ⊗ ⟨o|) ⟦p⟧` at the outcome string `o`, as a matrix on the data
bits: the evaluation of `⟦p⟧`'s outcome bits at `o`. -/
noncomputable def kraus {k : ℕ} (p : Protocol m n k) (o : Fin k → ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  LinearMap.toMatrix' (evalOutcome n o ∘ₗ hilbertSem p)

/-- `K_o ψ` is `⟦p⟧ ψ` evaluated at the outcome string `o`. -/
theorem kraus_mulVec {k : ℕ} (p : Protocol m n k) (o : Fin k → ZMod 2) (ψ : QubitSpace n) :
    kraus p o *ᵥ ψ = fun y => hilbertSem p ψ (Fin.append y o) := by
  rw [kraus, LinearMap.toMatrix'_mulVec]
  rfl

/-- The Gram matrix of a map's matrix at `(i, j)` is the inner product of its images of the basis
vectors `i` and `j`. -/
private theorem conjTranspose_mul_toMatrix'_apply {a b : ℕ} (L : QubitSpace a →ₗ[ℂ] QubitSpace b)
    (i j : Fin a → ZMod 2) :
    ((LinearMap.toMatrix' L)ᴴ * LinearMap.toMatrix' L) i j
      = innerQ (L (Pi.single i 1)) (L (Pi.single j 1)) := by
  rw [Matrix.mul_apply, innerQ_eq_sum]
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply]

private theorem innerQ_single {a : ℕ} (i j : Fin a → ZMod 2) :
    innerQ (Pi.single i (1 : ℂ) : QubitSpace a) (Pi.single j 1) = (1 : Matrix _ _ ℂ) i j := by
  rw [innerQ_eq_sum, Matrix.one_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, star_one, mul_one, if_true]
    · rw [Pi.single_eq_of_ne h, mul_zero, if_neg h]
  · intro v _ hv
    rw [Pi.single_eq_of_ne hv, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A map that keeps the inner product has a matrix with orthonormal columns. -/
private theorem conjTranspose_mul_of_keepsInner {a b : ℕ} {L : QubitSpace a →ₗ[ℂ] QubitSpace b}
    (hL : KeepsInner L) : (LinearMap.toMatrix' L)ᴴ * LinearMap.toMatrix' L = 1 := by
  ext i j
  rw [conjTranspose_mul_toMatrix'_apply, hL, innerQ_single]

/-- The Kraus sum is the Gram matrix of `⟦p⟧`'s matrix: the outcome strings and the data words
together run over every word on `n + k` bits. -/
private theorem sum_kraus_eq {k : ℕ} (p : Protocol m n k) :
    ∑ o : Fin k → ZMod 2, (kraus p o)ᴴ * kraus p o
      = (LinearMap.toMatrix' (hilbertSem p))ᴴ * LinearMap.toMatrix' (hilbertSem p) := by
  ext i j
  rw [Matrix.sum_apply, conjTranspose_mul_toMatrix'_apply, innerQ_eq_sum, ← sum_append]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [kraus, conjTranspose_mul_toMatrix'_apply, innerQ_eq_sum]
  rfl

/-- **The Kraus sum** `Σ_o K_o† K_o = 1`, over every outcome string. -/
theorem kraus_sum_eq_one {k : ℕ} (p : Protocol m n k) :
    ∑ o : Fin k → ZMod 2, (kraus p o)ᴴ * kraus p o = 1 := by
  rw [sum_kraus_eq, conjTranspose_mul_of_keepsInner (keepsInner_hilbertSem p)]

/-! ## The product form where outcome bits are controls only -/

/-- **A letter uses the last bits only as controls**: an H acts on one of the first `n` bits, a
CNOT targets one of them, and a diagonal letter may read any bit in its exponent. -/
def LetterControlsOnly (n : ℕ) {N : ℕ} : GateLetter N m → Prop
  | .hadamard j => (j : ℕ) < n
  | .diagonal _ => True
  | .cnot _ j _ => (j : ℕ) < n

/-- **Every outcome bit is used only as a control**: in a diagonal letter's exponent or as a CNOT's
control, never as an H's bit or a CNOT's target; and no conditioning Pauli has an X or a Z on an
outcome bit. -/
def OutcomeControlsOnly : {k : ℕ} → Protocol m n k → Prop
  | _, .nil => True
  | _, .word p w => OutcomeControlsOnly p ∧ ∀ g ∈ w, LetterControlsOnly n g
  | _, .condition p P _ => OutcomeControlsOnly p ∧
      ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0

/-- **The data part of a signed Pauli** on `n + k` bits: its sign and its X and Z on the first `n`
bits. Under `OutcomeControlsOnly` the outcome part is the identity, so nothing is dropped. -/
def restrictDataPauli {k : ℕ} (P : SignedPauli (n + k)) : SignedPauli n :=
  ⟨P.sign, ⟨P.pauli.X ∘ Fin.castAdd k, P.pauli.Z ∘ Fin.castAdd k⟩⟩

/-- **The unitary a word gives at `o`**: `(I ⊗ ⟨o|) W (I ⊗ |o⟩)` on the data bits. Where the word
uses the outcome bits only as controls it maps `φ ⊗ |o⟩` to `W(o) φ ⊗ |o⟩`, and this is `W(o)`. -/
noncomputable def wordAt {k : ℕ} (w : GateWord (n + k) m) (o : Fin k → ZMod 2) :
    QubitSpace n →ₗ[ℂ] QubitSpace n :=
  evalOutcome n o ∘ₗ wordGate w ∘ₗ appendOutcome n o

/-- **The product form**: the product, in term order (the last letter leftmost), of the unitaries
the words give at `o` and the Born projectors of the conditioning letters' data parts at their
outcomes. -/
noncomputable def krausProduct : {k : ℕ} → Protocol m n k → (Fin k → ZMod 2) →
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ
  | _, .nil, _ => 1
  | _, .word p w, o => LinearMap.toMatrix' (wordAt w o) * krausProduct p o
  | k + 1, .condition p P _, o =>
      LinearMap.toMatrix' (bornProjection (restrictDataPauli P) (o (Fin.last k))) *
        krausProduct p (Fin.init o)

/-! ### Private: the slice at an outcome string and the letters that keep it -/

/-- `(I ⊗ ⟨o|)` after `(I ⊗ |o⟩)` is the identity. -/
private theorem evalOutcome_appendOutcome_apply (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2)
    (φ : QubitSpace N) : evalOutcome N o (appendOutcome N o φ) = φ := by
  funext y
  rw [evalOutcome_apply, appendOutcome_apply, if_pos (append_comp_natAdd y o),
    append_comp_castAdd]

/-- **The slice projector** `I ⊗ |o⟩⟨o|`: keep the words whose last `k` bits are `o`. -/
private noncomputable def sliceProj (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) :
    QubitSpace (N + k) →ₗ[ℂ] QubitSpace (N + k) :=
  appendOutcome N o ∘ₗ evalOutcome N o

private theorem sliceProj_apply (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2) (ψ : QubitSpace (N + k))
    (v : Fin (N + k) → ZMod 2) :
    sliceProj N o ψ v = if v ∘ Fin.natAdd N = o then ψ v else 0 := by
  rw [sliceProj, LinearMap.comp_apply, appendOutcome_apply]
  by_cases h : v ∘ Fin.natAdd N = o
  · rw [if_pos h, if_pos h, evalOutcome_apply, ← h]
    exact congrArg ψ Fin.append_castAdd_natAdd
  · rw [if_neg h, if_neg h]

private theorem evalOutcome_sliceProj (N : ℕ) {k : ℕ} (o : Fin k → ZMod 2)
    (ψ : QubitSpace (N + k)) : evalOutcome N o (sliceProj N o ψ) = evalOutcome N o ψ :=
  evalOutcome_appendOutcome_apply N o _

/-- Changing a bit among the first `N` keeps the last `k`. -/
private theorem update_comp_natAdd {N k : ℕ} (v : Fin (N + k) → ZMod 2) (j : Fin (N + k))
    (hj : (j : ℕ) < N) (b : ZMod 2) :
    Function.update v j b ∘ Fin.natAdd N = v ∘ Fin.natAdd N := by
  funext t
  simp only [Function.comp_apply]
  rw [Function.update_of_ne]
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_natAdd] at hval
  omega

/-- A letter that uses the last bits only as controls commutes with the slice projector. -/
private theorem letterGate_sliceProj {k : ℕ} (g : GateLetter (n + k) m)
    (hg : LetterControlsOnly n g) (o : Fin k → ZMod 2) (ψ : QubitSpace (n + k)) :
    letterGate g (sliceProj n o ψ) = sliceProj n o (letterGate g ψ) := by
  funext v
  cases g with
  | hadamard j =>
    have hj : (j : ℕ) < n := hg
    simp only [letterGate, hadamardGate_apply, sliceProj_apply, update_comp_natAdd _ _ hj]
    by_cases h : v ∘ Fin.natAdd n = o
    · simp only [if_pos h]
    · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
  | diagonal D =>
    simp only [letterGate, diagonalGate_apply, sliceProj_apply]
    by_cases h : v ∘ Fin.natAdd n = o
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  | cnot i j hij =>
    have hj : (j : ℕ) < n := hg
    simp only [letterGate, LinearEquiv.coe_coe, cnotGate_apply, sliceProj_apply, cnotPerm,
      update_comp_natAdd _ _ hj]

private theorem wordGate_sliceProj {k : ℕ} (w : GateWord (n + k) m)
    (hw : ∀ g ∈ w, LetterControlsOnly n g) (o : Fin k → ZMod 2) (ψ : QubitSpace (n + k)) :
    wordGate w (sliceProj n o ψ) = sliceProj n o (wordGate w ψ) := by
  induction w generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    rw [wordGate_cons, LinearMap.comp_apply, LinearMap.comp_apply,
      letterGate_sliceProj g (hw g List.mem_cons_self) o ψ,
      ih (fun g' hg' => hw g' (List.mem_cons_of_mem g hg'))]

/-- Under the predicate, `(I ⊗ ⟨o|) W` sees only the slice at `o` of its input. -/
private theorem evalOutcome_wordGate_sliceProj {k : ℕ} (w : GateWord (n + k) m)
    (hw : ∀ g ∈ w, LetterControlsOnly n g) (o : Fin k → ZMod 2) (ψ : QubitSpace (n + k)) :
    evalOutcome n o (wordGate w (sliceProj n o ψ)) = evalOutcome n o (wordGate w ψ) := by
  rw [wordGate_sliceProj w hw o ψ, evalOutcome_sliceProj]

/-- The data part's X after an outcome string is the whole Pauli's X, when its outcome part is
the identity. -/
private theorem pauliX_eq_append {k : ℕ} (P : SignedPauli (n + k))
    (hP : ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0) :
    P.pauli.X = Fin.append (restrictDataPauli P).pauli.X 0 := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right, (hP j).1]
    rfl

private theorem append_sub_pauliX {k : ℕ} (P : SignedPauli (n + k))
    (hP : ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0)
    (y : Fin n → ZMod 2) (o : Fin k → ZMod 2) :
    Fin.append y o - P.pauli.X = Fin.append (y - (restrictDataPauli P).pauli.X) o := by
  rw [pauliX_eq_append P hP]
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [Pi.sub_apply, Fin.append_left]
  · simp only [Pi.sub_apply, Fin.append_right, Pi.zero_apply, sub_zero]

private theorem zDotVal_append {k : ℕ} (P : SignedPauli (n + k))
    (hP : ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0)
    (u : Fin n → ZMod 2) (o : Fin k → ZMod 2) :
    zDotVal P.pauli (Fin.append u o) = zDotVal (restrictDataPauli P).pauli u := by
  rw [zDotVal, zDotVal, Fin.sum_univ_add]
  simp only [Fin.append_left, (hP _).2, ZMod.val_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

private theorem xzWeight_restrictDataPauli {k : ℕ} (P : SignedPauli (n + k))
    (hP : ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0) :
    xzWeight P.pauli = xzWeight (restrictDataPauli P).pauli := by
  rw [xzWeight, xzWeight]
  conv_lhs => rw [pauliX_eq_append P hP]
  exact zDotVal_append P hP _ _

private theorem bornProjection_apply {N : ℕ} (P : SignedPauli N) (b : ZMod 2) (ψ : QubitSpace N)
    (v : Fin N → ZMod 2) :
    bornProjection P b ψ v = 2⁻¹ * (ψ v + (-1 : ℂ) ^ (P.sign.val + b.val) *
      (Complex.I ^ xzWeight P.pauli *
        ((-1 : ℂ) ^ zDotVal P.pauli (v - P.pauli.X) * ψ (v - P.pauli.X)))) := by
  simp only [bornProjection, LinearMap.comp_apply, LinearEquiv.coe_coe, toQState_symm_apply,
    bornProjector, LinearMap.smul_apply, PiLp.smul_apply, LinearMap.add_apply, PiLp.add_apply,
    LinearMap.id_apply, pauliHermitian_apply_fun, toQState_apply, smul_eq_mul]

/-- Under the predicate, the Born projector of `P` read at the outcome string `o` is the Born
projector of its data part. -/
private theorem bornProjection_append {k : ℕ} (P : SignedPauli (n + k))
    (hP : ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0) (b : ZMod 2)
    (φ : QubitSpace (n + k)) (y : Fin n → ZMod 2) (o : Fin k → ZMod 2) :
    bornProjection P b φ (Fin.append y o)
      = bornProjection (restrictDataPauli P) b (evalOutcome n o φ) y := by
  rw [bornProjection_apply, bornProjection_apply, append_sub_pauliX P hP, zDotVal_append P hP,
    xzWeight_restrictDataPauli P hP, evalOutcome_apply, evalOutcome_apply]
  rfl

/-- The word on `n + k + 1` bits ending in `o` is the word on `n + k` bits ending in `init o`,
then the bit `o (last k)`. -/
private theorem append_eq_append_init {k : ℕ} (y : Fin n → ZMod 2) (o : Fin (k + 1) → ZMod 2) :
    Fin.append y o = (Fin.append (Fin.append y (Fin.init o)) (fun _ : Fin 1 => o (Fin.last k)) :
      Fin (n + k + 1) → ZMod 2) := by
  funext i
  change Fin (n + k + 1) at i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hlast : (Fin.last (n + k) : Fin (n + (k + 1))) = Fin.natAdd n (Fin.last k) :=
      Fin.ext rfl
    rw [hlast, Fin.append_right]
    exact (Fin.append_right (Fin.append y (Fin.init o)) (fun _ : Fin 1 => o (Fin.last k)) 0).symm
  · rw [show (Fin.castSucc i : Fin (n + k + 1)) = Fin.castAdd 1 i from rfl, Fin.append_left]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left, show (Fin.castAdd 1 (Fin.castAdd k j) : Fin (n + (k + 1)))
        = Fin.castAdd (k + 1) j from Fin.ext rfl, Fin.append_left]
    · rw [Fin.append_right, show (Fin.castAdd 1 (Fin.natAdd n j) : Fin (n + (k + 1)))
        = Fin.natAdd n (Fin.castSucc j) from Fin.ext rfl, Fin.append_right]
      rfl

/-- Under the predicate, a conditioning letter read at the outcome string `o` is the Born
projector of its Pauli's data part at the last outcome, after the earlier outcomes are read. -/
private theorem evalOutcome_conditionIsometry {k : ℕ} (P : SignedPauli (n + k))
    (hP : ∀ j, P.pauli.X (Fin.natAdd n j) = 0 ∧ P.pauli.Z (Fin.natAdd n j) = 0)
    (o : Fin (k + 1) → ZMod 2) (φ : QubitSpace (n + k)) :
    evalOutcome n o (conditionIsometry P φ)
      = bornProjection (restrictDataPauli P) (o (Fin.last k)) (evalOutcome n (Fin.init o) φ) := by
  funext y
  rw [evalOutcome_apply]
  rw [append_eq_append_init, conditionIsometry_append, bornProjection_append P hP]

/-! ### Private: the equations of `krausProduct`, stated privately so that no equation lemma is
added to the statement -/

private theorem krausProduct_nil (o : Fin 0 → ZMod 2) :
    krausProduct (.nil : Protocol m n 0) o = 1 :=
  rfl

private theorem krausProduct_word {k : ℕ} (p : Protocol m n k) (w : GateWord (n + k) m)
    (o : Fin k → ZMod 2) :
    krausProduct (p.word w) o = LinearMap.toMatrix' (wordAt w o) * krausProduct p o :=
  rfl

private theorem krausProduct_condition {k : ℕ} (p : Protocol m n k) (P : SignedPauli (n + k))
    (hP : yWeight P.pauli % 2 = 1 → 2 ≤ m) (o : Fin (k + 1) → ZMod 2) :
    krausProduct (p.condition P hP) o
      = LinearMap.toMatrix' (bornProjection (restrictDataPauli P) (o (Fin.last k))) *
          krausProduct p (Fin.init o) :=
  rfl

/-- **The product form under `OutcomeControlsOnly`**: where every outcome bit is used only as a
control, `K_o` is the product in term order of the Born projectors and the words' unitaries at
`o`. -/
theorem kraus_eq_prod_of_controlsOnly {k : ℕ} (p : Protocol m n k) (hp : OutcomeControlsOnly p)
    (o : Fin k → ZMod 2) : kraus p o = krausProduct p o := by
  induction p with
  | nil =>
    rw [krausProduct_nil, kraus, hilbertSem_nil, LinearMap.comp_id]
    ext y x
    rw [LinearMap.toMatrix'_apply, evalOutcome_apply, Fin.append_right_nil y o rfl,
      Pi.single_apply, Matrix.one_apply]
    rfl
  | word p w ih =>
    rw [krausProduct_word, ← ih hp.1, kraus, kraus, wordAt, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun ψ => ?_
    rw [hilbertSem_word]
    simp only [LinearMap.comp_apply]
    exact (evalOutcome_wordGate_sliceProj w hp.2 o _).symm
  | condition p P hP ih =>
    rw [krausProduct_condition, ← ih hp.1, kraus, kraus, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun ψ => ?_
    rw [hilbertSem_condition]
    simp only [LinearMap.comp_apply]
    exact evalOutcome_conditionIsometry P hp.2 o _

/-! ## The functor from T46's category to linear maps -/

/-- **The amplitude of a morphism as a matrix**: `M_f(y, x) = f(x, y)`, the class's amplitude at
`Fin.append x y`, from the input `x` to the output `y`; well defined since a class is one
amplitude function. -/
noncomputable def homMatrix {a b : FrameCategory.Obj} (f : FrameCategory.Hom a b) :
    Matrix (Fin b.bits → ZMod 2) (Fin a.bits → ZMod 2) ℂ :=
  Quotient.lift
    (fun F : KernelSumState (a.bits + b.bits) => Matrix.of fun y x => amp F (Fin.append x y))
    (fun _ _ hFG => by
      ext y x
      exact congrFun (hFG : amp _ = amp _) _) f

@[simp] theorem homMatrix_toHom {a b : FrameCategory.Obj} (F : KernelSumState (a.bits + b.bits))
    (x : Fin a.bits → ZMod 2) (y : Fin b.bits → ZMod 2) :
    homMatrix (FrameCategory.toHom F) y x = amp F (Fin.append x y) :=
  rfl

/-- **Composition goes to the matrix product**: `f` then `g` is `M_g M_f`, by `amp_comp`. -/
theorem homMatrix_comp {a b c : FrameCategory.Obj} (f : FrameCategory.Hom a b)
    (g : FrameCategory.Hom b c) :
    homMatrix (FrameCategory.comp f g) = homMatrix g * homMatrix f := by
  obtain ⟨F, rfl⟩ : ∃ F, FrameCategory.toHom F = f := Quotient.exists_rep f
  obtain ⟨G, rfl⟩ : ∃ G, FrameCategory.toHom G = g := Quotient.exists_rep g
  rw [FrameCategory.comp_toHom]
  ext z x
  rw [homMatrix_toHom, amp_comp, Matrix.mul_apply]
  simp only [contractAmp, append_comp_castAdd, append_comp_natAdd, homMatrix_toHom]
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- **The identity goes to the identity matrix**, by `amp_idState`. -/
theorem homMatrix_id (a : FrameCategory.Obj) : homMatrix (FrameCategory.id a) = 1 := by
  ext y x
  change amp (idState a.bits) (Fin.append x y) = (1 : Matrix _ _ ℂ) y x
  rw [amp_idState, Matrix.one_apply]
  simp only [append_comp_castAdd, append_comp_natAdd]
  by_cases h : x = y
  · subst h
    simp only [if_true]
  · simp only [h, Ne.symm h, if_false]

/-- **The functor from T46's category to linear maps**: a register of `N` bits goes to
`ℂ^{2^N}`, and a morphism to the linear map of its amplitude matrix. -/
noncomputable def ampFunctor : CategoryTheory.Functor FrameCategory.Obj (ModuleCat.{0} ℂ) where
  obj a := ModuleCat.of ℂ (QubitSpace a.bits)
  map f := ModuleCat.ofHom (Matrix.toLin' (homMatrix f))
  map_id a := by
    change ModuleCat.ofHom (Matrix.toLin' (homMatrix (FrameCategory.id a))) = _
    rw [homMatrix_id, Matrix.toLin'_one]
    rfl
  map_comp f g := by
    change ModuleCat.ofHom (Matrix.toLin' (homMatrix (FrameCategory.comp f g))) = _
    rw [homMatrix_comp, Matrix.toLin'_mul]
    rfl

/-! ## Added by restatement (docs/STEPS.md, entry 2026-10-02n) -/

/-- **The tensor goes to the Kronecker product**: T46's tensor of `f` and `g` has, as its matrix,
the Kronecker product of theirs, rows and columns read through `Fin.append` (`amp_tensorState`).
With `homMatrix_comp`, composition and tensor are composition and tensor. Proved at T17.3. -/
theorem homMatrix_tensor {a b a' b' : FrameCategory.Obj} (f : FrameCategory.Hom a b)
    (g : FrameCategory.Hom a' b') :
    homMatrix (FrameCategory.tensor f g)
      = Matrix.reindex (Fin.appendEquiv b.bits b'.bits) (Fin.appendEquiv a.bits a'.bits)
          (homMatrix f ⊗ₖ homMatrix g) := by
  obtain ⟨F, rfl⟩ : ∃ F, FrameCategory.toHom F = f := Quotient.exists_rep f
  obtain ⟨G, rfl⟩ : ∃ G, FrameCategory.toHom G = g := Quotient.exists_rep g
  rw [FrameCategory.tensor_toHom]
  ext Y X
  obtain ⟨⟨Y₁, Y₂⟩, rfl⟩ := (Fin.appendEquiv b.bits b'.bits).surjective Y
  obtain ⟨⟨X₁, X₂⟩, rfl⟩ := (Fin.appendEquiv a.bits a'.bits).surjective X
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.kronecker_apply, homMatrix_toHom, homMatrix_toHom]
  change amp (tensorState F G) (Fin.append (Fin.append X₁ X₂) (Fin.append Y₁ Y₂)) = _
  rw [amp_tensorState]
  simp only [← Function.comp_assoc, append_comp_castAdd, append_comp_natAdd]

/-- **Words compose**: the word `w₁` then `w₂` is `w₂`'s unitary after `w₁`'s. Proved at T17.3. -/
theorem wordGate_append {N : ℕ} (w₁ w₂ : GateWord N m) :
    wordGate (w₁ ++ w₂) = wordGate w₂ ∘ₗ wordGate w₁ := by
  induction w₁ with
  | nil => rfl
  | cons g gs ih =>
    rw [List.cons_append, wordGate_cons, wordGate_cons, ih, LinearMap.comp_assoc]

/-- A function that vanishes off the slice at `o` has its inner products on that slice. -/
private theorem innerQ_evalOutcome_of_slice {k : ℕ} (o : Fin k → ZMod 2)
    {f : QubitSpace (n + k)} (hf : sliceProj n o f = f) (g : QubitSpace (n + k)) :
    innerQ (evalOutcome n o f) (evalOutcome n o g) = innerQ f g := by
  rw [innerQ_eq_sum, innerQ_eq_sum, ← sum_append, Finset.sum_eq_single o]
  · rfl
  · intro t _ ht
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [← hf, sliceProj_apply, append_comp_natAdd, if_neg ht, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Under the predicate, the word read at `o` keeps the inner product. -/
private theorem keepsInner_wordAt {k : ℕ} (w : GateWord (n + k) m)
    (hw : ∀ g ∈ w, LetterControlsOnly n g) (o : Fin k → ZMod 2) : KeepsInner (wordAt w o) := by
  intro ψ φ
  have hslice : ∀ χ : QubitSpace n, sliceProj n o (appendOutcome n o χ) = appendOutcome n o χ :=
    fun χ => by rw [sliceProj, LinearMap.comp_apply, evalOutcome_appendOutcome_apply]
  have hword : ∀ χ : QubitSpace n, sliceProj n o (wordGate w (appendOutcome n o χ))
      = wordGate w (appendOutcome n o χ) :=
    fun χ => by rw [← wordGate_sliceProj w hw o, hslice]
  simp only [wordAt, LinearMap.comp_apply]
  rw [innerQ_evalOutcome_of_slice o (hword ψ), keepsInner_wordGate w,
    ← innerQ_evalOutcome_of_slice o (hslice ψ), evalOutcome_appendOutcome_apply,
    evalOutcome_appendOutcome_apply]

/-- **The unitaries the words give at `o`**: a word whose letters use the outcome bits only as
controls gives, at every outcome string `o`, a unitary on the data bits. Proved at T17.3. -/
theorem wordAt_unitary {k : ℕ} (w : GateWord (n + k) m) (hw : ∀ g ∈ w, LetterControlsOnly n g)
    (o : Fin k → ZMod 2) :
    LinearMap.toMatrix' (wordAt w o) ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact conjTranspose_mul_of_keepsInner (keepsInner_wordAt w hw o)

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.CarrierScale
import FTQCLib.Carrier.FinAppend
import FTQCLib.Carrier.GateWordPrecision
import FTQCLib.Carrier.GramIsometry
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Equality of carrier states up to unread bits

A carrier state on `n + k` free bits is read as `n` **read bits** followed by `k` **unread bits**:
outcome bits that no later letter and no reader of the result reads, such as the environment bit
of a loss or a forgotten outcome (`docs/TARGETS.md`, T27; `docs/framing/T27.md`). For an amplitude
function `f` on `𝔽₂ⁿ × 𝔽₂^k` the **unread vector at `x`** is `f(x, ·)` (`unreadVector`) and the
**read function at `u`** is `f(·, u)` (`readFunction`). The **Gram data** over the read bits is

`gram f x y = Σ_u f(x, u) · conj (f(y, u))`,

the unread bits summed and the read bits kept, and `UnreadEq k S T` is the equality of the Gram
data of `amp S` and `amp T` at every pair of read words. It reads `amp` alone, at any precision,
so it is frame-pure; it is an equivalence (`unreadEq_equivalence`) implied by `StateEq`
(`unreadEq_of_stateEq`). With no unread bits it is **not** `StateEq`: the Gram data
`f(x)·conj(f(y))` fixes `f` only up to a scalar of modulus one, and `unreadEq_zero_iff` states
exactly that.

**The extended theory** (`UnreadMove`, `UnreadDerivable`) is the equivalence generated, over pairs
`⟨k, S⟩` with `S` on `n + k` free bits (`UnreadState`), by three moves. The relation ranges over
`k`, since the third move changes it.

* (a) `UnreadMove.rule`: a `CarrierRule` step on the whole register (T06).
* (b) `UnreadMove.runUnread`: the run of a gate word `W` on the `k` unread bits, lifted to the
  register (`liftUnread`), on a carrier state at the word's precision. Its letters are H on an
  unread bit, CNOT between two unread bits and a diagonal letter whose exponent is a polynomial in
  the unread variables alone; a constant exponent counts, and it is the move that relates `f` to
  `−f` at `k = 0`.
* (c) `UnreadMove.drop`: dropping an unread bit `j` that the support determines from the **other
  unread bits** alone (`DeterminedByUnread`: `e_j ∉ π_X(L) + span{e_i : i < n}`). The unqualified
  `dropFreeBit`, whose hypothesis is only `e_j ∉ π_X(L)`, does not keep the Gram data: on the Bell
  pair it drops `u = x` and restores the coherence the environment held.

Appending an ancilla held at zero is (c) read backwards, and relabelling the unread bits is (b) by
CNOT swaps. A letter touching a read bit, and dropping an unread bit the read bits determine, are
not moves: each changes the Gram data.

**The statement.**

* Each move is sound, stated and not assumed: `unreadEq_of_eqvGen_carrierRule` (a),
  `unreadEq_of_run_unread` (b), `unreadEq_of_dropUnread` (c), and `gram_eq_of_derivable` for a
  whole derivation, assembled from the three.
* `unreadEq_iff_exists_isometry`: equal Gram data holds exactly when one unitary on `ℂ^{𝔽₂^k}`
  carries every unread vector of one state to the other's (purification). The unitary is unique
  only when the unread vectors span, so the statement quantifies over it.
* `unreadEq_derivable_iff`, the exact characterisation: for carriers `S` on `n + k` and `T` on
  `n + k'` bits, the extended theory relates them exactly when the scale ratio `T.c / S.c` is dyadic
  (D9) and, for some ancilla counts with `k + a = k' + a'`, some gate word on the unread bits and
  the ancillas carries `f ⊗ δ₀^a` to `g ⊗ δ₀^{a'}` (`padAncillas`). It is stated without T45:
  whether such a word exists exactly when an isometry's matrix has entries in `ℤ[ζ_{2^∞}, ½]` is
  T45's arithmetic, conditional and not claimed here.
* `readModule_eq_of_derivable`, the invariant: a derivation keeps the `ℤ[ζ_{2^∞}, ½]`-module
  spanned by the read functions (`readModule`, over `dyadicCyclotomicRing`). With the note's rows
  O1 and O2, pairs with equal Gram data and scale ratio one whose read functions carry `3/5`, it
  proves where the characterisation's word clause fails, at every precision: the obstruction is a
  non-dyadic isometry, not the scale. This is the research allowance's "proof that it fails
  elsewhere"; the rows themselves are the check module's (`UnreadBitsCheck.lean`).
* The obstruction's arithmetic: every element of the ring times some `2^N` is integral over `ℤ`
  (`exists_two_pow_mul_isIntegral`), so a rational in it has a power of two as its denominator
  (`exists_two_pow_mul_eq_int_of_ratCast_mem`) and `a/5` is not in it when `5 ∤ a`
  (`intCast_div_five_not_mem_dyadicCyclotomicRing`); the ring is closed under conjugation
  (`starRingEnd_mem_dyadicCyclotomicRing`). `not_unreadDerivable_of_readFunction_not_mem` turns the
  invariant into a test: a read function of one state outside the other's module refutes a
  derivation. Added by the run session after run 9b (docs/STEPS.md, entry 2026-10-01j): T27.4 had
  no row proving O1 and O2 not derivable, since nothing proved `3/5` outside the ring.

**Scope of "not derivable" (standard 7.3).** A pair outside the characterisation is not related by
the moves named here, (a) to (c) over the letters of `GateLetter`. That set is closed by its
definition; a new move, such as a non-dyadic letter or a drop determined by the read bits, would
withdraw the conclusion, and any use of the theorems names this move set.

**The measured reading** (Gram data branch by branch, the coherences between read outcome strings
discarded) is `UnreadEq` after each read outcome bit is copied by a CNOT into a fresh unread bit:
a construction before the theory, not a second definition (`docs/framing/T27.md`).

Everything here is frame-pure: `amp`, gate words and `Matrix`. No `FTQCLib.Hilbert`.

## Main definitions

* `unreadVector`, `readFunction`, `gram` — the two slices of an amplitude function and the Gram
  data.
* `UnreadEq` — equality of the Gram data over the read bits.
* `GateLetter.liftUnread`, `liftUnread` — a letter and a word on the unread bits, on the register.
* `readDirections`, `DeterminedByUnread`, `dropUnread` — the drop move's hypothesis and the drop.
* `UnreadState`, `UnreadMove`, `UnreadDerivable` — the extended theory.
* `padAncillas` — an amplitude function with `a` ancillas held at zero after the unread bits.
* `ampMatrix` — the amplitude as a matrix, rows the read words and columns the unread words.
* `dyadicCyclotomicRing`, `readModule` — the ring `ℤ[ζ_{2^∞}, ½]` in `ℂ` and the module of the
  read functions over it.

## Main results

* `unreadEq_equivalence`, `unreadEq_of_stateEq`, `unreadEq_zero_iff` — proved here.
* `unreadEq_of_eqvGen_carrierRule`, `unreadEq_of_run_unread`, `unreadEq_of_dropUnread` — soundness
  of the three moves (T27.3.1); `gram_eq_of_derivable` from them.
* `unreadEq_iff_exists_isometry`, `unreadEq_derivable_iff`, `readModule_eq_of_derivable` —
  T27.3.3, the first from the helper module of T27.3.2.
* `gram_eq_mul_conjTranspose`, `unreadEq_iff_mul_conjTranspose_eq`,
  `unreadEq_iff_exists_unitary_mul` — the bridges: the Gram data is `F Fᴴ` for the amplitude
  matrix `ampMatrix`, and `UnreadEq` is `G = F Uᵀ` for a unitary `U`, the textbook statements.
* `exists_two_pow_mul_isIntegral`, `starRingEnd_mem_dyadicCyclotomicRing`,
  `exists_two_pow_mul_eq_int_of_ratCast_mem`, `intCast_div_five_not_mem_dyadicCyclotomicRing`,
  `not_unreadDerivable_of_readFunction_not_mem` — the obstruction's arithmetic and its test.

## Implementation notes

* The ancilla counts of the characterisation meet in `k + a = k' + a'`, which is not definitional,
  so the right side is read through `Fin.cast`.
* The run move carries `IsCarrier S` and `S.m = m`, the hypotheses of `amp_run`: off a carrier,
  `applyH` need not compute the Walsh transform, and a letter at another precision does nothing.
  Both are the well-formedness of the one state the move acts on, as in `amp_run`, and no
  condition relating two states; a precision the chain cannot match does not arise, since the
  gauge rewrite R7 (`CarrierRule.gauge`, `GaugeStep.liftTo`) lifts it.
* `dyadicCyclotomicRing` is generated by `½` and every root of unity of order a power of two; it
  holds `1/√2 = ½(ζ₈ + ζ₈⁻¹)`, so every letter's matrix has its entries in it.
* The forward direction of `unreadEq_derivable_iff` carries along the chain a dyadic scale ratio
  and a word with ancillas held at zero (`DerivInv`, private), composed at the larger ancilla count
  and precision. A drop is a word: CNOTs from the other unread bits and an X bring the dropped bit
  to zero on the support, and a CNOT permutation moves it last, where it is an ancilla.
* The backward direction appends each ancilla as `pinZero` (private: a free bit appended,
  conditioned on `Z` at outcome `0`, the support sliced), which move (c) drops and T07's rules
  relate to the input; it then lifts the precision (R7), runs the word, and closes with
  `rewrite_complete`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The Gram data over the read bits -/

/-- The unread vector of `f` at the read word `x`: `u ↦ f(x, u)`. -/
def unreadVector {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) :
    (Fin k → ZMod 2) → ℂ :=
  fun u => f (Fin.append x u)

/-- The read function of `f` at the unread word `u`: `x ↦ f(x, u)`. -/
def readFunction {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) (u : Fin k → ZMod 2) :
    (Fin n → ZMod 2) → ℂ :=
  fun x => f (Fin.append x u)

/-- The Gram data of `f` over the read bits: `Σ_u f(x, u) · conj (f(y, u))`, the unread bits summed
and the read bits kept. -/
noncomputable def gram {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) (x y : Fin n → ZMod 2) : ℂ :=
  ∑ u : Fin k → ZMod 2, f (Fin.append x u) * starRingEnd ℂ (f (Fin.append y u))

/-- **Equality up to unread bits.** Two carrier states on `n + k` free bits, the last `k`
unread, have the same Gram data over the read bits at every pair of read words. A relation on
`amp` alone. -/
def UnreadEq (k : ℕ) (S T : KernelSumState (n + k)) : Prop :=
  ∀ x y : Fin n → ZMod 2, gram (amp S) x y = gram (amp T) x y

/-- `UnreadEq` is an equivalence. -/
theorem unreadEq_equivalence (k : ℕ) : Equivalence (UnreadEq (n := n) k) where
  refl _ _ _ := rfl
  symm h x y := (h x y).symm
  trans h₁ h₂ x y := (h₁ x y).trans (h₂ x y)

/-- `StateEq` implies `UnreadEq`: equal amplitudes have equal Gram data. -/
theorem unreadEq_of_stateEq {k : ℕ} {S T : KernelSumState (n + k)} (h : StateEq S T) :
    UnreadEq k S T := by
  intro x y
  unfold StateEq at h
  rw [h]

/-- With no unread bits the Gram data is `f(x) · conj (f(y))`; public for the check rows at `k = 0`
(entry 2026-10-01n). -/
theorem gram_zero (f : (Fin (n + 0) → ZMod 2) → ℂ) (x y : Fin n → ZMod 2) :
    gram f x y = f x * starRingEnd ℂ (f y) := by
  have happend : ∀ (z : Fin n → ZMod 2) (v : Fin 0 → ZMod 2), Fin.append z v = z := fun z v => by
    rw [Fin.append_right_nil z v rfl]
    rfl
  unfold gram
  rw [Fintype.sum_unique, happend x, happend y]

/-- The forward direction of `unreadEq_zero_iff`: equal products `f(x)·conj(f(y))` make `g` a
unit-modulus multiple of `f`, the multiple read off at a word where `f` is not zero. -/
private theorem exists_unit_smul_of_gram_eq (f g : (Fin n → ZMod 2) → ℂ)
    (h : ∀ x y, f x * starRingEnd ℂ (f y) = g x * starRingEnd ℂ (g y)) :
    ∃ μ : ℂ, ‖μ‖ = 1 ∧ g = μ • f := by
  by_cases hf : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf
    have hnorm : Complex.normSq (g x₀) = Complex.normSq (f x₀) := by
      have h₀ := h x₀ x₀
      rw [Complex.mul_conj, Complex.mul_conj] at h₀
      exact_mod_cast h₀.symm
    have hg₀ : g x₀ ≠ 0 := by
      intro hg
      rw [hg, map_zero] at hnorm
      exact hx₀ (Complex.normSq_eq_zero.mp hnorm.symm)
    refine ⟨g x₀ / f x₀, ?_, ?_⟩
    · rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hx₀)]
      have hsq : ‖g x₀‖ ^ 2 = ‖f x₀‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hnorm]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    · funext x
      have hx := h x x₀
      have hconj : starRingEnd ℂ (g x₀) ≠ 0 := (map_ne_zero _).mpr hg₀
      have hcf : starRingEnd ℂ (f x₀) * f x₀ = starRingEnd ℂ (g x₀) * g x₀ := by
        rw [mul_comm, Complex.mul_conj, mul_comm, Complex.mul_conj, hnorm]
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hx₀]
      refine mul_right_cancel₀ hconj ?_
      calc g x * f x₀ * starRingEnd ℂ (g x₀)
          = g x * (starRingEnd ℂ (g x₀) * f x₀) := by ring
        _ = f x * (starRingEnd ℂ (f x₀) * f x₀) := by
            rw [← mul_assoc, ← hx]; ring
        _ = f x * (starRingEnd ℂ (g x₀) * g x₀) := by rw [hcf]
        _ = g x₀ * f x * starRingEnd ℂ (g x₀) := by ring
  · simp only [ne_eq, not_exists, not_not] at hf
    refine ⟨1, norm_one, ?_⟩
    funext x
    have hx := h x x
    rw [hf x, zero_mul, Complex.mul_conj] at hx
    rw [one_smul, hf x]
    exact_mod_cast Complex.normSq_eq_zero.mp (by exact_mod_cast hx.symm)

/-- **No unread bits: `StateEq` up to a unit-modulus scalar, not `StateEq`.** With `k = 0` the
Gram data `f(x)·conj(f(y))` fixes the amplitude only up to a scalar of modulus one: `f` and `−f`
are `UnreadEq` and not `StateEq`. -/
theorem unreadEq_zero_iff (S T : KernelSumState (n + 0)) :
    UnreadEq 0 S T ↔ ∃ μ : ℂ, ‖μ‖ = 1 ∧ amp T = μ • amp S := by
  constructor
  · intro h
    refine exists_unit_smul_of_gram_eq (amp S) (amp T) fun x y => ?_
    have hxy := h x y
    rw [gram_zero, gram_zero] at hxy
    exact hxy
  · rintro ⟨μ, hμ, hT⟩ x y
    rw [gram_zero, gram_zero, hT, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      map_mul]
    have hμμ : μ * starRingEnd ℂ μ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]
      norm_num
    calc amp S x * starRingEnd ℂ (amp S y)
        = (μ * starRingEnd ℂ μ) * (amp S x * starRingEnd ℂ (amp S y)) := by rw [hμμ, one_mul]
      _ = μ * amp S x * (starRingEnd ℂ μ * starRingEnd ℂ (amp S y)) := by ring

/-! ## Words on the unread bits -/

/-- A letter on the `k` unread bits, read on the register of `n + k` free bits: H and CNOT at the
shifted bits, a diagonal exponent with its variables renamed to the unread ones. -/
noncomputable def GateLetter.liftUnread {k m : ℕ} (n : ℕ) :
    GateLetter k m → GateLetter (n + k) m
  | .hadamard i => .hadamard (Fin.natAdd n i)
  | .diagonal D => .diagonal (MvPolynomial.rename (Fin.natAdd n) D)
  | .cnot i j hij => .cnot (Fin.natAdd n i) (Fin.natAdd n j)
      fun h => hij ((Fin.natAdd_inj n).mp h)

/-- A word on the `k` unread bits, read on the register of `n + k` free bits, letter by letter. -/
noncomputable def liftUnread {k m : ℕ} (n : ℕ) (W : GateWord k m) : GateWord (n + k) m :=
  W.map (GateLetter.liftUnread n)

/-! ## Dropping an unread bit the other unread bits determine -/

/-- The read directions `span{e_i : i < n}` in `𝔽₂^{n + k}`. -/
noncomputable def readDirections (n k : ℕ) : Submodule (ZMod 2) (Fin (n + k) → ZMod 2) :=
  Submodule.span (ZMod 2)
    (Set.range fun i : Fin n => (Pi.single (Fin.castAdd k i) 1 : Fin (n + k) → ZMod 2))

/-- The support determines unread bit `j` from the other unread bits alone:
`e_j ∉ π_X(L) + span{e_i : i < n}`. Equivalently, some functional that vanishes on the read
coordinates fixes bit `j` on the support coset, so two words of the support that agree on the other
unread bits agree at `j`, whatever their read bits. -/
def DeterminedByUnread {k : ℕ} (S : KernelSumState (n + k)) (j : Fin k) : Prop :=
  (Pi.single (Fin.natAdd n j) 1 : Fin (n + k) → ZMod 2)
    ∉ Submodule.map xProj S.L ⊔ readDirections n k

/-- Dropping unread bit `j`: `dropFreeBit` at the free bit `n + j`. -/
noncomputable def dropUnread {k : ℕ} (j : Fin (k + 1)) (S : KernelSumState (n + (k + 1))) :
    KernelSumState (n + k) :=
  dropFreeBit (n := n + k) (Fin.natAdd n j) S

/-! ## The extended theory -/

/-- A carrier state together with its count `k` of unread bits, on `n + k` free bits. -/
abbrev UnreadState (n : ℕ) : Type := Σ k : ℕ, KernelSumState (n + k)

/-- **The moves of the extended theory.** (a) a `CarrierRule` step on the whole register; (b) the
run of a word on the unread bits, on a carrier state at the word's precision; (c) dropping an unread
bit that the support determines from the other unread bits. -/
inductive UnreadMove : UnreadState n → UnreadState n → Prop
  /-- (a) A `CarrierRule` step on the whole register. -/
  | rule {k : ℕ} {S T : KernelSumState (n + k)} (hST : CarrierRule S T) : UnreadMove ⟨k, S⟩ ⟨k, T⟩
  /-- (b) A word whose letters touch only the unread bits, run at the state's precision. -/
  | runUnread {k m : ℕ} (W : GateWord k m) {S : KernelSumState (n + k)} (hS : IsCarrier S)
      (hm : S.m = m) : UnreadMove ⟨k, S⟩ ⟨k, run (liftUnread n W) S⟩
  /-- (c) Dropping an unread bit the other unread bits determine. -/
  | drop {k : ℕ} (S : KernelSumState (n + (k + 1))) (j : Fin (k + 1))
      (hj : DeterminedByUnread S j) : UnreadMove ⟨k + 1, S⟩ ⟨k, dropUnread j S⟩

/-- **The extended theory**: the equivalence the three moves generate, over varying `k`. -/
def UnreadDerivable (A B : UnreadState n) : Prop :=
  Relation.EqvGen UnreadMove A B

/-! ## Soundness of the moves -/

/-! ### Words on the unread bits: one map on every unread vector, keeping the inner sums

A word's referee is linear and keeps inner sums (`runAmp_add_smul`, `innerSum_runAmp`, in
`GateWord.lean`). -/

/-- The Gram data at `(x, y)` is the inner sum of the unread vectors at `x` and `y`. -/
private theorem gram_eq_innerSum {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) (x y : Fin n → ZMod 2) :
    gram f x y = innerSum (unreadVector f x) (unreadVector f y) := rfl

/-- The binary lift of `Fin.append x u`, read at the unread coordinates, is the lift of `u`. -/
private theorem liftBinary_append_comp_natAdd {k m : ℕ} (x : Fin n → ZMod 2)
    (u : Fin k → ZMod 2) :
    (DiagPhase.liftBinary (m := m) (Fin.append x u) ∘ Fin.natAdd n) = DiagPhase.liftBinary u := by
  funext i
  change (((Fin.append x u) (Fin.natAdd n i)).val : ZMod (2 ^ m)) = ((u i).val : ZMod (2 ^ m))
  rw [Fin.append_right]

/-- A lifted letter acts on every unread vector as the letter itself. -/
private theorem unreadVector_letterAmp_liftUnread {k m : ℕ} (g : GateLetter k m)
    (f : (Fin (n + k) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) :
    unreadVector (letterAmp (g.liftUnread n) f) x = letterAmp g (unreadVector f x) := by
  funext u
  cases g with
  | hadamard i =>
    change walshTransform (Fin.natAdd n i) f (Fin.append x u)
      = walshTransform i (unreadVector f x) u
    unfold walshTransform unreadVector
    rw [update_append_natAdd, update_append_natAdd, Fin.append_right]
  | diagonal D =>
    change charOf m (DiagPhase.eval (MvPolynomial.rename (Fin.natAdd n) D) (Fin.append x u))
        * f (Fin.append x u)
      = charOf m (DiagPhase.eval D u) * f (Fin.append x u)
    rw [DiagPhase.eval, DiagPhase.eval, MvPolynomial.eval_rename, liftBinary_append_comp_natAdd]
  | cnot i j hij =>
    change f (DiagPhase.cnotBitMap (Fin.natAdd n i) (Fin.natAdd n j) (Fin.append x u))
      = f (Fin.append x (DiagPhase.cnotBitMap i j u))
    unfold DiagPhase.cnotBitMap
    rw [Fin.append_right, Fin.append_right, update_append_natAdd]

/-- A lifted word acts on every unread vector as the word itself: one map, the same at every
read word. -/
private theorem unreadVector_runAmp_liftUnread {k m : ℕ} (W : GateWord k m)
    (f : (Fin (n + k) → ZMod 2) → ℂ) (x : Fin n → ZMod 2) :
    unreadVector (runAmp (liftUnread n W) f) x = runAmp W (unreadVector f x) := by
  induction W generalizing f with
  | nil => rfl
  | cons g gs ih =>
    change unreadVector (runAmp (liftUnread n gs) (letterAmp (g.liftUnread n) f)) x = _
    rw [ih, unreadVector_letterAmp_liftUnread, runAmp_cons]

/-! ### Dropping an unread bit the other unread bits determine -/

/-- A word zero on the unread coordinates lies in the read directions. -/
private theorem append_zero_mem_readDirections {k : ℕ} (z : Fin n → ZMod 2) :
    Fin.append z (0 : Fin k → ZMod 2) ∈ readDirections n k := by
  rw [← Finset.univ_sum_single (Fin.append z (0 : Fin k → ZMod 2)), Fin.sum_univ_add]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_)
    (Submodule.sum_mem _ fun i _ => ?_)
  · have hsmul : (Pi.single (Fin.castAdd k i) (Fin.append z (0 : Fin k → ZMod 2)
        (Fin.castAdd k i)) : Fin (n + k) → ZMod 2)
        = z i • (Pi.single (Fin.castAdd k i) 1 : Fin (n + k) → ZMod 2) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one, Fin.append_left]
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Fin.append_right, Pi.zero_apply, Pi.single_zero]
    exact Submodule.zero_mem _

/-- Two words that differ at unread bit `j` only by the two values of the bit, read words
aside, differ by `e_j` modulo the read directions. -/
private theorem append_sub_append_sub {k : ℕ} (j : Fin (k + 1)) (x y : Fin n → ZMod 2)
    (u : Fin k → ZMod 2) {β β' : ZMod 2} (hββ' : β ≠ β') :
    Fin.append x (Fin.insertNth j β u) - Fin.append y (Fin.insertNth j β' u)
        - Fin.append (x - y) (0 : Fin (k + 1) → ZMod 2)
      = (Pi.single (Fin.natAdd n j) 1 : Fin (n + (k + 1)) → ZMod 2) := by
  have hβ : β - β' = 1 := by
    revert β β'
    decide
  funext l
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · rw [Pi.sub_apply, Pi.sub_apply, Fin.append_left, Fin.append_left, Fin.append_left,
      Pi.single_eq_of_ne (castAdd_ne_natAdd l j), Pi.sub_apply, sub_self]
  · have hins := congrFun (Fin.insertNth_sub_same (α := fun _ => ZMod 2) j β β' u) l
    rw [Pi.sub_apply] at hins
    rw [Pi.sub_apply, Pi.sub_apply, Fin.append_right, Fin.append_right, Fin.append_right,
      Pi.zero_apply, sub_zero, hins, hβ]
    by_cases hl : l = j
    · rw [hl, Pi.single_eq_same, Pi.single_eq_same]
    · have hne : Fin.natAdd n l ≠ Fin.natAdd n j := fun h => hl ((Fin.natAdd_inj n).mp h)
      rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hne]

/-- **The cross terms vanish.** When the other unread bits determine bit `j`, the amplitudes at
`(x, u, β)` and `(y, u, β')` with `β ≠ β'` are never both nonzero: both on the support, their
difference less the read part `(x − y, 0)` would put `e_j` in `π_X(L) + span{e_i : i < n}`. -/
private theorem amp_mul_conj_amp_eq_zero {k : ℕ} {S : KernelSumState (n + (k + 1))}
    {j : Fin (k + 1)} (hj : DeterminedByUnread S j) (x y : Fin n → ZMod 2) (u : Fin k → ZMod 2)
    {β β' : ZMod 2} (hββ' : β ≠ β') :
    amp S (Fin.append x (Fin.insertNth j β u))
      * starRingEnd ℂ (amp S (Fin.append y (Fin.insertNth j β' u))) = 0 := by
  by_contra hne
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hne
  have hs₁ := (mem_support_iff S _).mp (by_contra fun h => h₁ (amp_neg h))
  have hs₂ := (mem_support_iff S _).mp
    (by_contra fun h => h₂ (by rw [amp_neg h, map_zero]))
  have hdiff := Submodule.sub_mem _ hs₁ hs₂
  rw [sub_sub_sub_cancel_right] at hdiff
  have hsup := Submodule.sub_mem_sup hdiff (append_zero_mem_readDirections (k := k + 1) (x - y))
  rw [append_sub_append_sub j x y u hββ'] at hsup
  exact hj hsup

/-- For one value of the other unread bits, the product of the two sums over bit `j` is the sum
of the diagonal products: the cross terms vanish (`amp_mul_conj_amp_eq_zero`). -/
private theorem sum_mul_conj_sum_eq {k : ℕ} {S : KernelSumState (n + (k + 1))}
    {j : Fin (k + 1)} (hj : DeterminedByUnread S j) (x y : Fin n → ZMod 2) (u : Fin k → ZMod 2) :
    (∑ β : ZMod 2, amp S (Fin.append x (Fin.insertNth j β u)))
        * starRingEnd ℂ (∑ β : ZMod 2, amp S (Fin.append y (Fin.insertNth j β u)))
      = ∑ β : ZMod 2, amp S (Fin.append x (Fin.insertNth j β u))
          * starRingEnd ℂ (amp S (Fin.append y (Fin.insertNth j β u))) := by
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  refine Finset.sum_eq_single β (fun β' _ hne => ?_) (fun h => absurd (Finset.mem_univ β) h)
  exact amp_mul_conj_amp_eq_zero hj x y u (Ne.symm hne)

/-- **Move (a) is sound**, and so is any chain of `CarrierRule` steps: they keep `amp`. -/
theorem unreadEq_of_eqvGen_carrierRule {k : ℕ} {S T : KernelSumState (n + k)}
    (hST : Relation.EqvGen CarrierRule S T) : UnreadEq k S T := by
  induction hST with
  | rel S T h => exact unreadEq_of_stateEq (stateEq_of_carrierRule h)
  | refl S => exact (unreadEq_equivalence k).refl S
  | symm S T _ ih => exact (unreadEq_equivalence k).symm ih
  | trans S T U _ _ ih₁ ih₂ => exact (unreadEq_equivalence k).trans ih₁ ih₂

/-- **Move (b) is sound.** A word on the unread bits acts on every unread vector by one linear map,
the same for every read word, and that map keeps `Σ |·|²` (`sum_normSq_runAmp`), so it is unitary
and keeps the Gram data. -/
theorem unreadEq_of_run_unread {k m : ℕ} (W : GateWord k m) {S : KernelSumState (n + k)}
    (hS : IsCarrier S) (hm : S.m = m) : UnreadEq k S (run (liftUnread n W) S) := by
  intro x y
  rw [amp_run (liftUnread n W) hS hm, gram_eq_innerSum, gram_eq_innerSum,
    unreadVector_runAmp_liftUnread, unreadVector_runAmp_liftUnread, innerSum_runAmp]

/-- **Move (c) is sound.** Dropping an unread bit the other unread bits determine keeps the Gram
data over the read bits, though it changes `k`: by `amp_dropFreeBit` the dropped state's amplitude
sums both values of the bit, and the cross terms vanish, since `f(x, u', β)` and `f(y, u', 1 − β)`
are never both nonzero under the hypothesis. -/
theorem unreadEq_of_dropUnread {k : ℕ} (S : KernelSumState (n + (k + 1))) (j : Fin (k + 1))
    (hj : DeterminedByUnread S j) : gram (amp (dropUnread j S)) = gram (amp S) := by
  have hX : (Pi.single (Fin.natAdd n j) 1 : Fin (n + k + 1) → ZMod 2)
      ∉ Submodule.map xProj S.L := fun h => hj (Submodule.mem_sup_left h)
  funext x y
  unfold dropUnread gram
  rw [amp_dropFreeBit (n := n + k) (Fin.natAdd n j) S hX,
    ← (Fin.insertNthEquiv (fun _ => ZMod 2) j).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  beta_reduce
  simp only [insertNth_natAdd_append]
  exact sum_mul_conj_sum_eq hj x y u

/-- **The extended theory is sound**: a derivation keeps the Gram data over the read bits, from the
soundness of each move. -/
theorem gram_eq_of_derivable {A B : UnreadState n} (hAB : UnreadDerivable A B) :
    gram (amp A.2) = gram (amp B.2) := by
  induction hAB with
  | rel A B hAB =>
    cases hAB with
    | rule hST =>
      funext x y
      exact unreadEq_of_eqvGen_carrierRule (Relation.EqvGen.rel _ _ hST) x y
    | runUnread W hS hm =>
      funext x y
      exact unreadEq_of_run_unread W hS hm x y
    | drop S j hj => exact (unreadEq_of_dropUnread S j hj).symm
  | refl A => rfl
  | symm A B _ ih => exact ih.symm
  | trans A B C _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## Equal Gram data is a unitary on the unread bits -/

/-- **Purification.** Equal Gram data holds exactly when one unitary on `ℂ^{𝔽₂^k}` carries the
unread vector of `S` at every read word to that of `T`. The unitary is unique only when the unread
vectors span. -/
theorem unreadEq_iff_exists_isometry {k : ℕ} (S T : KernelSumState (n + k)) :
    UnreadEq k S T ↔ ∃ U ∈ Matrix.unitaryGroup (Fin k → ZMod 2) ℂ,
      ∀ x : Fin n → ZMod 2, Matrix.mulVec U (unreadVector (amp S) x) = unreadVector (amp T) x := by
  constructor
  · intro h
    exact exists_isometry_of_gram_eq (unreadVector (amp S)) (unreadVector (amp T)) h
  · rintro ⟨U, hU, hUST⟩ x y
    exact gram_eq_of_isometry hU hUST x y

/-! ## The characterisation -/

/-- An amplitude function on `n + k` free bits with `a` ancillas held at zero after the unread bits:
at `(x, u, z)` it is `f(x, u)` when `z = 0` and `0` otherwise, that is `f ⊗ δ₀^a`. -/
noncomputable def padAncillas {k : ℕ} (a : ℕ) (f : (Fin (n + k) → ZMod 2) → ℂ) :
    (Fin (n + (k + a)) → ZMod 2) → ℂ :=
  fun w =>
    if ∀ i : Fin a, w (Fin.natAdd n (Fin.natAdd k i)) = 0 then
      f (Fin.append (fun i : Fin n => w (Fin.castAdd (k + a) i))
        (fun i : Fin k => w (Fin.natAdd n (Fin.castAdd a i))))
    else 0

/-! ### Unread vectors, and padding with ancillas held at zero -/

/-- Two functions on the register are equal when their unread vectors agree at every read word. -/
private theorem eq_of_unreadVector_eq {k : ℕ} {F G : (Fin (n + k) → ZMod 2) → ℂ}
    (h : ∀ x, unreadVector F x = unreadVector G x) : F = G := by
  funext w
  have hw := congrFun (h fun i => w (Fin.castAdd k i)) fun i => w (Fin.natAdd n i)
  unfold unreadVector at hw
  rwa [Fin.append_castAdd_natAdd] at hw

/-- The ancillas of `padAncillas` are the padding, read on the unread vectors. -/
private theorem unreadVector_padAncillas {k : ℕ} (a : ℕ) (f : (Fin (n + k) → ZMod 2) → ℂ)
    (x : Fin n → ZMod 2) :
    unreadVector (padAncillas a f) x = padZero (Nat.le_add_right k a) (unreadVector f x) := by
  funext u
  have hcond : (∀ i : Fin a, u (Fin.natAdd k i) = 0) ↔ ∀ i : Fin (k + a), k ≤ i.val → u i = 0 := by
    refine ⟨fun h i hi => ?_, fun h i => h _ (by rw [Fin.val_natAdd]; omega)⟩
    refine Fin.addCases (motive := fun i => k ≤ i.val → u i = 0) (fun i hi => ?_)
      (fun i _ => h i) i hi
    rw [Fin.val_castAdd] at hi
    exact absurd i.isLt (by omega)
  unfold unreadVector padAncillas padZero
  simp only [Fin.append_left, Fin.append_right]
  by_cases h : ∀ i : Fin a, u (Fin.natAdd k i) = 0
  · rw [if_pos h, if_pos (hcond.mp h)]
    rfl
  · rw [if_neg h, if_neg fun h' => h (hcond.mpr h')]

/-- The right side of the characterisation, read through `Fin.cast`, is the padding. -/
private theorem unreadVector_padAncillas_cast {k' a' N : ℕ} (hN : k' + a' = N)
    (g : (Fin (n + k') → ZMod 2) → ℂ) (x : Fin n → ZMod 2) (hk' : k' ≤ N) :
    unreadVector (fun w : Fin (n + N) → ZMod 2 =>
        padAncillas a' g fun i => w (Fin.cast (congrArg (n + ·) hN) i)) x
      = padZero hk' (unreadVector g x) := by
  subst hN
  exact unreadVector_padAncillas a' g x

/-! ### Words: inverses, more bits, more precision

The inverse words, the zero padding, the widened and the raised words are `GateWord.lean`'s and
`GateWordPrecision.lean`'s (entry 2026-10-01n); here, only how inverting meets the lift. -/

/-- Lifting to the register commutes with inverting a letter. -/
private theorem liftUnread_invLetter {k M : ℕ} (g : GateLetter k M) :
    (invLetter g).liftUnread n = invLetter (g.liftUnread n) := by
  cases g with
  | hadamard i => rfl
  | diagonal D => exact congrArg GateLetter.diagonal (map_neg _ D)
  | cnot i j hij => rfl

/-! ### The bit the other unread bits determine -/

/-- **The determining functional.** When the other unread bits determine bit `j`, a functional of
the unread bits, `1` at `j`, is constant on the support: off the value it fixes, the amplitude is
zero at every read word. -/
private theorem exists_unread_functional {k : ℕ} {S : KernelSumState (n + (k + 1))}
    {j : Fin (k + 1)} (hj : DeterminedByUnread S j) :
    ∃ (g : Fin k → ZMod 2) (c : ZMod 2), ∀ (x : Fin n → ZMod 2) (u : Fin k → ZMod 2) (β : ZMod 2),
      amp S (Fin.append x (Fin.insertNth j β u)) ≠ 0 → β + ∑ i, g i * u i = c := by
  obtain ⟨G, hGV, hGj⟩ := exists_separates hj
  have hread : ∀ i : Fin n, G (Fin.castAdd (k + 1) i) = 0 := fun i => by
    have h := hGV _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
    rwa [dotF2_single] at h
  have hjG : G (Fin.natAdd n j) = 1 := by rwa [dotF2_single] at hGj
  refine ⟨fun i => G (Fin.natAdd n (j.succAbove i)), dotF2 G S.x₀, fun x u β hne => ?_⟩
  have hsupp := (mem_support_iff S _).mp (by_contra fun h => hne (amp_neg h))
  have h0 := hGV _ (Submodule.mem_sup_left hsupp)
  rw [dotF2_sub_right, sub_eq_zero] at h0
  rw [← h0]
  unfold dotF2
  have hz : ∑ i : Fin n, G (Fin.castAdd (k + 1) i)
      * Fin.append x (Fin.insertNth j β u) (Fin.castAdd (k + 1) i) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hread, zero_mul]
  rw [Fin.sum_univ_add, hz, zero_add, Fin.sum_univ_succAbove _ j]
  simp only [Fin.append_right, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hjG,
    one_mul]

/-- Off the determined value the amplitude is zero. -/
private theorem amp_insertNth_eq_zero {k : ℕ} {S : KernelSumState (n + (k + 1))}
    {j : Fin (k + 1)} {g : Fin k → ZMod 2} {c : ZMod 2}
    (hfun : ∀ (x : Fin n → ZMod 2) (u : Fin k → ZMod 2) (β : ZMod 2),
      amp S (Fin.append x (Fin.insertNth j β u)) ≠ 0 → β + ∑ i, g i * u i = c)
    {x : Fin n → ZMod 2} {u : Fin k → ZMod 2} {β : ZMod 2} (hβ : β ≠ c - ∑ i, g i * u i) :
    amp S (Fin.append x (Fin.insertNth j β u)) = 0 :=
  by_contra fun hne => hβ (eq_sub_of_add_eq (hfun x u β hne))

/-- The sum over the dropped bit is its one term at the determined value. -/
private theorem sum_insertNth_eq {k : ℕ} {S : KernelSumState (n + (k + 1))}
    {j : Fin (k + 1)} {g : Fin k → ZMod 2} {c : ZMod 2}
    (hfun : ∀ (x : Fin n → ZMod 2) (u : Fin k → ZMod 2) (β : ZMod 2),
      amp S (Fin.append x (Fin.insertNth j β u)) ≠ 0 → β + ∑ i, g i * u i = c)
    (x : Fin n → ZMod 2) (u : Fin k → ZMod 2) :
    ∑ β : ZMod 2, amp S (Fin.append x (Fin.insertNth j β u))
      = amp S (Fin.append x (Fin.insertNth j (c - ∑ i, g i * u i) u)) :=
  Finset.sum_eq_single _ (fun _ _ hβ => amp_insertNth_eq_zero hfun hβ)
    (fun h => absurd (Finset.mem_univ _) h)

/-- The unread vectors after the drop sum the two values of the dropped bit. -/
private theorem unreadVector_dropUnread {k : ℕ} (S : KernelSumState (n + (k + 1)))
    (j : Fin (k + 1)) (hj : DeterminedByUnread S j) (x : Fin n → ZMod 2) :
    unreadVector (amp (dropUnread j S)) x
      = fun u => ∑ β : ZMod 2, amp S (Fin.append x (Fin.insertNth j β u)) := by
  have hX : (Pi.single (Fin.natAdd n j) 1 : Fin (n + k + 1) → ZMod 2)
      ∉ Submodule.map xProj S.L := fun h => hj (Submodule.mem_sup_left h)
  funext u
  unfold dropUnread unreadVector
  rw [amp_dropFreeBit (n := n + k) (Fin.natAdd n j) S hX]
  beta_reduce
  simp only [insertNth_natAdd_append]

/-! ### The invariant of a derivation, for the forward direction -/

/-- Padding by one bit keeps the function where the new bit is zero. -/
private theorem padZero_succ {k : ℕ} (φ : (Fin k → ZMod 2) → ℂ) (v : Fin (k + 1) → ZMod 2) :
    padZero (Nat.le_succ k) φ v = if v (Fin.last k) = 0 then φ (Fin.init v) else 0 := by
  have hcond : (∀ i : Fin (k + 1), k ≤ i.val → v i = 0) ↔ v (Fin.last k) = 0 := by
    refine ⟨fun h => h _ (by rw [Fin.val_last]), fun h i hi => ?_⟩
    have hi' : i = Fin.last k := Fin.ext (by rw [Fin.val_last]; have := i.isLt; omega)
    rw [hi', h]
  unfold padZero
  by_cases h : v (Fin.last k) = 0
  · rw [if_pos (hcond.mpr h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (hcond.mp h')), if_neg h]

/-- Some word on the unread bits and ancillas held at zero, at some precision, carries every
padded unread vector of `f` to that of `g`. -/
private def WordRel {k k' : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ)
    (g : (Fin (n + k') → ZMod 2) → ℂ) : Prop :=
  ∃ (N : ℕ) (hk : k ≤ N) (hk' : k' ≤ N) (M : ℕ) (W : GateWord N M),
    ∀ x, runAmp W (padZero hk (unreadVector f x)) = padZero hk' (unreadVector g x)

private theorem wordRel_refl {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) : WordRel f f :=
  ⟨k, le_rfl, le_rfl, 0, [], fun _ => rfl⟩

private theorem wordRel_symm {k k' : ℕ} {f : (Fin (n + k) → ZMod 2) → ℂ}
    {g : (Fin (n + k') → ZMod 2) → ℂ} (h : WordRel f g) : WordRel g f := by
  obtain ⟨N, hk, hk', M, W, hW⟩ := h
  exact ⟨N, hk', hk, M, invWord W, fun x => by rw [← hW x, runAmp_invWord]⟩

private theorem wordRel_trans {k₁ k₂ k₃ : ℕ} {f₁ : (Fin (n + k₁) → ZMod 2) → ℂ}
    {f₂ : (Fin (n + k₂) → ZMod 2) → ℂ} {f₃ : (Fin (n + k₃) → ZMod 2) → ℂ}
    (h₁ : WordRel f₁ f₂) (h₂ : WordRel f₂ f₃) : WordRel f₁ f₃ := by
  obtain ⟨N₁, hk₁, hk₂, M₁, W₁, hW₁⟩ := h₁
  obtain ⟨N₂, hk₂', hk₃, M₂, W₂, hW₂⟩ := h₂
  have hN₁ : N₁ ≤ max N₁ N₂ := le_max_left _ _
  have hN₂ : N₂ ≤ max N₁ N₂ := le_max_right _ _
  have hM₁ : M₁ ≤ max M₁ M₂ := le_max_left _ _
  have hM₂ : M₂ ≤ max M₁ M₂ := le_max_right _ _
  refine ⟨max N₁ N₂, hk₁.trans hN₁, hk₃.trans hN₂, max M₁ M₂,
    (W₁.map (widenLetter hN₁)).map (precLetter hM₁)
      ++ (W₂.map (widenLetter hN₂)).map (precLetter hM₂), fun x => ?_⟩
  rw [runAmp_append, runAmp_precWord, runAmp_precWord, ← padZero_padZero hk₁ hN₁,
    runAmp_widenWord, hW₁ x, padZero_padZero, ← padZero_padZero hk₂' hN₂, runAmp_widenWord,
    hW₂ x, padZero_padZero]

/-- **The drop move as a word.** CNOTs from the other unread bits and an X bring the dropped bit
to zero on the support, and a permutation moves it last, where it is an ancilla. -/
private theorem wordRel_drop {k : ℕ} (S : KernelSumState (n + (k + 1))) (j : Fin (k + 1))
    (hj : DeterminedByUnread S j) : WordRel (amp S) (amp (dropUnread j S)) := by
  obtain ⟨g, c, hfun⟩ := exists_unread_functional hj
  obtain ⟨Wc, hWc⟩ := exists_realizes_add j c
  obtain ⟨Wx, hWx⟩ := exists_realizes_xor j g Finset.univ
  obtain ⟨Wp, hWp⟩ := exists_realizes_insertLast j
  refine ⟨k + 1, le_rfl, Nat.le_succ k, 1, Wc ++ Wx ++ Wp, fun x => ?_⟩
  rw [padZero_self, ((hWc.append hWx).append hWp) _, unreadVector_dropUnread S j hj x]
  funext v
  rw [padZero_succ]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Fin.update_insertNth]
  unfold unreadVector
  rw [sum_insertNth_eq hfun x (Fin.init v)]
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (v (Fin.last k)) with hb | hb
  · rw [if_pos hb, hb]
    congr 3
    exact (by decide : ∀ t c : ZMod 2, 0 + t + c = c - t) _ _
  · rw [if_neg (by rw [hb]; decide), hb]
    exact amp_insertNth_eq_zero hfun
      ((by decide : ∀ t c : ZMod 2, 1 + t + c ≠ c - t) _ _)

/-- `c'` is `c` times a dyadic ratio. -/
private def ScaleRel (c c' : ℂ) : Prop :=
  ∃ r : ℂ, IsDyadicRatio r ∧ c' = r * c

private theorem scaleRel_refl (c : ℂ) : ScaleRel c c := ⟨1, isDyadicRatio_one, (one_mul c).symm⟩

private theorem scaleRel_symm {c c' : ℂ} (h : ScaleRel c c') : ScaleRel c' c := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r⁻¹, hr.inv, ?_⟩
  rw [hc, ← mul_assoc, inv_mul_cancel₀ hr.ne_zero, one_mul]

private theorem scaleRel_trans {c c' c'' : ℂ} (h₁ : ScaleRel c c') (h₂ : ScaleRel c' c'') :
    ScaleRel c c'' := by
  obtain ⟨r, hr, hc⟩ := h₁
  obtain ⟨s, hs, hc'⟩ := h₂
  exact ⟨s * r, hs.mul hr, by rw [hc', hc, mul_assoc]⟩

/-- A nonzero scaling is by a power of `√2`. -/
private theorem exists_zpow_of_scaledBy {c c' : ℂ} (h : ScaledBy c c') (hc' : c' ≠ 0) :
    ∃ e : ℤ, c' = (Real.sqrt 2 : ℂ) ^ e * c := by
  rcases h with h | h
  · exact absurd h hc'
  · exact h

/-- What a derivation keeps: a dyadic scale ratio and a word with ancillas. -/
private def DerivInv (A B : UnreadState n) : Prop :=
  ScaleRel A.2.c B.2.c ∧ WordRel (amp A.2) (amp B.2)

/-- Each move keeps the invariant. -/
private theorem derivInv_of_move {A B : UnreadState n} (h : UnreadMove A B) : DerivInv A B := by
  cases h with
  | rule hST =>
    obtain ⟨r, hr, hc⟩ := exists_isDyadicRatio_of_carrierRule hST
    refine ⟨⟨r, hr, hc⟩, ?_⟩
    change WordRel (amp _) (amp _)
    rw [show amp _ = amp _ from stateEq_of_carrierRule hST]
    exact wordRel_refl _
  | @runUnread k m W S hS hm =>
    have hU := isCarrier_run (liftUnread n W) hS hm
    obtain ⟨e, he⟩ := exists_zpow_of_scaledBy (scaledBy_run (liftUnread n W) S)
      (c_ne_zero_of_isCarrier hU)
    refine ⟨⟨_, isDyadicRatio_sqrt_two_zpow e, he⟩, k, le_rfl, le_rfl, m, W, fun x => ?_⟩
    change runAmp W (padZero le_rfl (unreadVector (amp S) x))
      = padZero le_rfl (unreadVector (amp (run (liftUnread n W) S)) x)
    rw [padZero_self, padZero_self, amp_run _ hS hm, unreadVector_runAmp_liftUnread]
  | drop S j hj => exact ⟨⟨1, isDyadicRatio_one, (one_mul _).symm⟩, wordRel_drop S j hj⟩

/-- A derivation keeps the invariant. -/
private theorem derivInv_of_derivable {A B : UnreadState n} (h : UnreadDerivable A B) :
    DerivInv A B := by
  induction h with
  | rel A B h => exact derivInv_of_move h
  | refl A => exact ⟨scaleRel_refl _, wordRel_refl _⟩
  | symm A B _ ih => exact ⟨scaleRel_symm ih.1, wordRel_symm ih.2⟩
  | trans A B C _ _ ih₁ ih₂ => exact ⟨scaleRel_trans ih₁.1 ih₂.1, wordRel_trans ih₁.2 ih₂.2⟩

/-! ### Appending ancillas held at zero, for the backward direction -/

private theorem determinedByUnread_pinZero {k : ℕ} {S : KernelSumState (n + k)}
    (hS : IsCarrier S) : DeterminedByUnread (n := n) (k := k + 1) (pinZero S) (Fin.last k) := by
  have hA := isCarrier_appendFreeBit hS
  have hle : Submodule.map xProj (pinZero S).L ⊔ readDirections n (k + 1)
      ≤ LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin (n + k + 1) => ZMod 2)
        (Fin.last (n + k))) := by
    refine sup_le (fun v hv => ?_) (Submodule.span_le.mpr ?_)
    · rw [pinZero_L, mem_map_pauliCondition_pauliz_iff hA.2.1] at hv
      exact hv.2
    · rintro _ ⟨i, rfl⟩
      change (Pi.single (Fin.castAdd (k + 1) i) 1 : Fin (n + (k + 1)) → ZMod 2)
        (Fin.last (n + k)) = 0
      refine Pi.single_eq_of_ne (fun h => ?_) _
      have hval := congrArg Fin.val h
      rw [Fin.val_last, Fin.val_castAdd] at hval
      have := i.isLt
      omega
  intro hmem
  have h := hle hmem
  rw [LinearMap.mem_ker, LinearMap.proj_apply, Fin.natAdd_last, Pi.single_eq_same] at h
  exact one_ne_zero h

/-- A chain of `CarrierRule` steps is a derivation by move (a). -/
private theorem derivable_of_eqvGen_carrierRule {k : ℕ} {S T : KernelSumState (n + k)}
    (h : Relation.EqvGen CarrierRule S T) : UnreadDerivable (n := n) ⟨k, S⟩ ⟨k, T⟩ := by
  induction h with
  | rel S T h => exact Relation.EqvGen.rel _ _ (UnreadMove.rule h)
  | refl S => exact Relation.EqvGen.refl _
  | symm S T _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans S T U _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **Appending an ancilla is move (c) read backwards**, after T07's rules. -/
private theorem derivable_pinZero {k : ℕ} {S : KernelSumState (n + k)} (hS : IsCarrier S) :
    UnreadDerivable (n := n) ⟨k, S⟩ ⟨k + 1, pinZero S⟩ := by
  have hA := isCarrier_appendFreeBit hS
  have hamp : StateEq S (restrictZ (Fin.last (n + k)) 0 (appendFreeBit S)) := by
    funext w
    rw [amp_restrictZ hA, Fin.insertNth_last', amp_appendFreeBit]
    exact (congrArg (amp S) (Fin.init_snoc (α := fun _ => ZMod 2) (0 : ZMod 2) w)).symm
  have hne : amp (restrictZ (Fin.last (n + k)) 0 (appendFreeBit S)) ≠ 0 := by
    rw [← show amp S = _ from hamp]
    exact hS.2.2.2
  have hR := eqvGen_carrierRule_of_scaledBy hS (isCarrier_restrictZ hA _ _ hne) hamp
    (ScaledBy.refl S.c) (scaledBy_restrictZ _ _ (appendFreeBit S))
  have hdrop := UnreadMove.drop (n := n) (k := k) (pinZero S) (Fin.last k)
    (determinedByUnread_pinZero hS)
  exact Relation.EqvGen.trans _ _ _ (derivable_of_eqvGen_carrierRule hR)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hdrop))

/-- The unread vectors of `pinZero` are the padding by one bit. -/
private theorem unreadVector_pinZero {K : ℕ} {S : KernelSumState (n + K)} (hS : IsCarrier S)
    (x : Fin n → ZMod 2) :
    unreadVector (k := K + 1) (amp (pinZero S)) x
      = padZero (Nat.le_succ K) (unreadVector (amp S) x) := by
  funext u
  rw [padZero_succ]
  unfold unreadVector
  rw [amp_pinZero hS]
  have h1 : (Fin.append x u : Fin (n + (K + 1)) → ZMod 2) (Fin.last (n + K)) = u (Fin.last K) := by
    rw [← Fin.natAdd_last, Fin.append_right]
  have h2 : (Fin.init (Fin.append x u : Fin (n + (K + 1)) → ZMod 2) : Fin (n + K) → ZMod 2)
      = Fin.append x (Fin.init u) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      exact Fin.append_left x u i
    · rw [Fin.append_right]
      exact Fin.append_right x u (Fin.castSucc i)
  change (if (Fin.append x u : Fin (n + (K + 1)) → ZMod 2) (Fin.last (n + K)) = 0
      then amp S (Fin.init (Fin.append x u : Fin (n + (K + 1)) → ZMod 2)) else 0) = _
  rw [h1, h2]

/-- Padding a carrier to `N` unread bits is a derivation, keeping the scale up to `√2`. -/
private theorem exists_padded {k : ℕ} {S : KernelSumState (n + k)} (hS : IsCarrier S) (d : ℕ) :
    ∃ S' : KernelSumState (n + (k + d)), IsCarrier S' ∧ ScaledBy S.c S'.c ∧
      (∀ x, unreadVector (amp S') x = padZero (Nat.le_add_right k d) (unreadVector (amp S) x)) ∧
      UnreadDerivable (n := n) ⟨k, S⟩ ⟨k + d, S'⟩ := by
  induction d with
  | zero => exact ⟨S, hS, ScaledBy.refl _, fun x => (padZero_self _ _).symm, Relation.EqvGen.refl _⟩
  | succ d ih =>
    obtain ⟨S', hS', hc, hamp, hder⟩ := ih
    refine ⟨pinZero S', isCarrier_pinZero hS', hc.trans (scaledBy_restrictZ _ _ (appendFreeBit S')),
      fun x => ?_, Relation.EqvGen.trans _ _ _ hder (derivable_pinZero hS')⟩
    rw [← padZero_padZero (Nat.le_add_right k d) (Nat.le_succ (k + d)), ← hamp x]
    exact unreadVector_pinZero hS' x

private theorem exists_padded_to {k N : ℕ} {S : KernelSumState (n + k)} (hS : IsCarrier S)
    (hk : k ≤ N) :
    ∃ S' : KernelSumState (n + N), IsCarrier S' ∧ ScaledBy S.c S'.c ∧
      (∀ x, unreadVector (amp S') x = padZero hk (unreadVector (amp S) x)) ∧
      UnreadDerivable (n := n) ⟨k, S⟩ ⟨N, S'⟩ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact exists_padded hS d

/-- **The backward direction.** Pad both sides to one count, lift the precision, run the word, and
close with `rewrite_complete`. -/
private theorem derivable_of_wordRel {k k' : ℕ} {S : KernelSumState (n + k)}
    {T : KernelSumState (n + k')} (hS : IsCarrier S) (hT : IsCarrier T)
    (hc : IsDyadicRatio (T.c / S.c)) (hW : WordRel (amp S) (amp T)) :
    UnreadDerivable (n := n) ⟨k, S⟩ ⟨k', T⟩ := by
  obtain ⟨N, hk, hk', M, W, hWx⟩ := hW
  obtain ⟨S₁, hS₁, hcS₁, hampS₁, hderS⟩ := exists_padded_to hS hk
  obtain ⟨T₁, hT₁, hcT₁, hampT₁, hderT⟩ := exists_padded_to hT hk'
  have hM : S₁.m ≤ max M S₁.m := le_max_right _ _
  have hS₂ : IsCarrier (liftPrecision S₁ (max M S₁.m) hM) := isCarrier_liftPrecision hS₁ _ hM
  have hU := isCarrier_run (liftUnread n ((W.map (precLetter (le_max_left M S₁.m))))) hS₂ rfl
  have hUT : StateEq (run (liftUnread n (W.map (precLetter (le_max_left M S₁.m))))
      (liftPrecision S₁ (max M S₁.m) hM)) T₁ := by
    refine eq_of_unreadVector_eq fun x => ?_
    rw [amp_run (m := max M S₁.m) _ hS₂ rfl, unreadVector_runAmp_liftUnread, runAmp_precWord,
      amp_liftPrecision,
      hampS₁, hWx, hampT₁]
  have h12 : Relation.EqvGen CarrierRule S₁ (liftPrecision S₁ (max M S₁.m) hM) := by
    refine (rewrite_complete hS₁ hS₂).mpr ⟨(amp_liftPrecision S₁ _ hM).symm, ?_⟩
    change IsDyadicRatio (S₁.c / S₁.c)
    rw [div_self (c_ne_zero_of_isCarrier hS₁)]
    exact isDyadicRatio_one
  have hratio : IsDyadicRatio (T₁.c / (run (liftUnread n (W.map (precLetter (le_max_left M S₁.m))))
      (liftPrecision S₁ (max M S₁.m) hM)).c) := by
    obtain ⟨e₁, he₁⟩ := exists_zpow_of_scaledBy (hcS₁.trans (scaledBy_run
      (liftUnread n (W.map (precLetter (le_max_left M S₁.m)))) (liftPrecision S₁ (max M S₁.m) hM)))
      (c_ne_zero_of_isCarrier hU)
    obtain ⟨e₂, he₂⟩ := exists_zpow_of_scaledBy hcT₁ (c_ne_zero_of_isCarrier hT₁)
    rw [he₁, he₂, ← div_mul_div_comm, div_eq_mul_inv ((Real.sqrt 2 : ℂ) ^ e₂)]
    exact ((isDyadicRatio_sqrt_two_zpow e₂).mul (isDyadicRatio_sqrt_two_zpow e₁).inv).mul hc
  have hUT' := (rewrite_complete hU hT₁).mpr ⟨hUT, hratio⟩
  have hmove := UnreadMove.runUnread (n := n) (W.map (precLetter (le_max_left M S₁.m))) hS₂ rfl
  exact Relation.EqvGen.trans _ _ _ hderS <| Relation.EqvGen.trans _ _ _
    (derivable_of_eqvGen_carrierRule h12) <| Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.rel _ _ hmove) <| Relation.EqvGen.trans _ _ _
    (derivable_of_eqvGen_carrierRule hUT') (Relation.EqvGen.symm _ _ hderT)

/-- **The exact characterisation.** For carrier states `S` on `n + k` and `T` on `n + k'` free bits,
the extended theory relates them exactly when the scale ratio is dyadic (D9) and, for some ancilla
counts with `k + a = k' + a'` and some precision `M`, a gate word on the unread bits and the
ancillas carries `amp S ⊗ δ₀^a` to `amp T ⊗ δ₀^{a'}`. No arithmetic condition on the word, and so
nothing of T45, is part of the statement. -/
theorem unreadEq_derivable_iff {k k' : ℕ} {S : KernelSumState (n + k)}
    {T : KernelSumState (n + k')} (hS : IsCarrier S) (hT : IsCarrier T) :
    UnreadDerivable ⟨k, S⟩ ⟨k', T⟩ ↔
      IsDyadicRatio (T.c / S.c) ∧
        ∃ (a a' : ℕ) (hk : k + a = k' + a') (M : ℕ) (W : GateWord (k + a) M),
          runAmp (liftUnread n W) (padAncillas a (amp S))
            = fun w =>
              padAncillas a' (amp T) fun i => w (Fin.cast (congrArg (n + ·) hk.symm) i) := by
  constructor
  · intro h
    obtain ⟨⟨r, hr, hc⟩, hW⟩ := derivInv_of_derivable h
    refine ⟨?_, ?_⟩
    · change T.c = r * S.c at hc
      rw [hc, mul_div_assoc, div_self (c_ne_zero_of_isCarrier hS), mul_one]
      exact hr
    · obtain ⟨N, hk, hk', M, W, hWx⟩ := hW
      change k ≤ N at hk
      change k' ≤ N at hk'
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
      have ha' : k + a = k' + (k + a - k') := (Nat.add_sub_cancel' hk').symm
      refine ⟨a, k + a - k', ha', M, W, eq_of_unreadVector_eq fun x => ?_⟩
      rw [unreadVector_runAmp_liftUnread, unreadVector_padAncillas, hWx x]
      exact (unreadVector_padAncillas_cast ha'.symm (amp T) x hk').symm
  · rintro ⟨hc, a, a', hk, M, W, hW⟩
    have hk' : k' ≤ k + a := le_of_le_of_eq (Nat.le_add_right k' a') hk.symm
    refine derivable_of_wordRel hS hT hc ⟨k + a, Nat.le_add_right k a, hk', M, W, fun x => ?_⟩
    have hx := congrArg (fun F => unreadVector F x) hW
    simp only at hx
    rw [unreadVector_runAmp_liftUnread, unreadVector_padAncillas,
      unreadVector_padAncillas_cast hk.symm (amp T) x hk'] at hx
    exact hx

/-! ## The invariant -/

/-- The ring `ℤ[ζ_{2^∞}, ½]` inside `ℂ`: generated by `½` and every root of unity of order a
power of two. It holds `1/√2`, so every letter's matrix has its entries in it. -/
def dyadicCyclotomicRing : Subring ℂ :=
  Subring.closure ({(2 : ℂ)⁻¹} ∪ {z : ℂ | ∃ M : ℕ, z ^ 2 ^ M = 1})

/-- The `ℤ[ζ_{2^∞}, ½]`-module spanned by the read functions `f(·, u)`. -/
noncomputable def readModule {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) :
    Submodule dyadicCyclotomicRing ((Fin n → ZMod 2) → ℂ) :=
  Submodule.span dyadicCyclotomicRing (Set.range (readFunction f))

/-! ### The ring holds every letter's entries -/

private theorem mem_dyadicCyclotomicRing_of_pow {z : ℂ} {M : ℕ} (h : z ^ 2 ^ M = 1) :
    z ∈ dyadicCyclotomicRing :=
  Subring.subset_closure (Or.inr ⟨M, h⟩)

private theorem inv_two_mem_dyadicCyclotomicRing : (2 : ℂ)⁻¹ ∈ dyadicCyclotomicRing :=
  Subring.subset_closure (Or.inl rfl)

/-- A character value is a root of unity of order a power of two. -/
private theorem charOf_mem_dyadicCyclotomicRing (m : ℕ) (z : ZMod (2 ^ m)) :
    charOf m z ∈ dyadicCyclotomicRing := by
  refine mem_dyadicCyclotomicRing_of_pow (M := m) ?_
  rw [charOf_eq_zeta_pow, ← pow_mul, mul_comm, pow_mul, (isPrimitiveRoot_zeta m).pow_eq_one,
    one_pow]

/-- `1/√2 = ½(ζ₈ + ζ₈⁻¹)` lies in the ring. -/
private theorem one_div_sqrt_two_mem_dyadicCyclotomicRing :
    1 / (Real.sqrt 2 : ℂ) ∈ dyadicCyclotomicRing := by
  have hsum : charOf 3 1 + charOf 3 (-1) = (Real.sqrt 2 : ℂ) := by
    rw [charOf_three_one, charOf_three_neg_one, ← add_div,
      show (1 + Complex.I + (1 - Complex.I)) = (2 : ℂ) by ring, div_eq_iff ofReal_sqrt_two_ne_zero,
      ← sq, sqrt_two_sq_complex]
  have h : 1 / (Real.sqrt 2 : ℂ) = (2 : ℂ)⁻¹ * (charOf 3 1 + charOf 3 (-1)) := by
    rw [hsum, eq_inv_mul_iff_mul_eq₀ two_ne_zero, ← sqrt_two_sq_complex, sq, mul_assoc, one_div,
      mul_inv_cancel₀ ofReal_sqrt_two_ne_zero, mul_one]
  rw [h]
  exact Subring.mul_mem _ inv_two_mem_dyadicCyclotomicRing
    (Subring.add_mem _ (charOf_mem_dyadicCyclotomicRing 3 1)
      (charOf_mem_dyadicCyclotomicRing 3 (-1)))

private theorem signOf_mem_dyadicCyclotomicRing (b : ZMod 2) :
    signOf b ∈ dyadicCyclotomicRing := by
  unfold signOf
  split
  · exact Subring.one_mem _
  · exact Subring.neg_mem _ (Subring.one_mem _)

/-! ### Each move keeps the module of the read functions -/

private theorem readFunction_mem_readModule {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ)
    (u : Fin k → ZMod 2) : readFunction f u ∈ readModule f :=
  Submodule.subset_span ⟨u, rfl⟩

private theorem smul_mem_readModule {k : ℕ} {f : (Fin (n + k) → ZMod 2) → ℂ} {c : ℂ}
    (hc : c ∈ dyadicCyclotomicRing) {φ : (Fin n → ZMod 2) → ℂ} (hφ : φ ∈ readModule f) :
    c • φ ∈ readModule f := by
  have h := Submodule.smul_mem (readModule f) (⟨c, hc⟩ : dyadicCyclotomicRing) hφ
  rwa [Subring.smul_def] at h

/-- A lifted letter's read functions are combinations of the input's with coefficients in the
ring: `1/√2` and a sign for H, a root of unity for a diagonal letter, a permutation for CNOT. -/
private theorem readFunction_letterAmp_liftUnread_mem {k M : ℕ} (g : GateLetter k M)
    (f : (Fin (n + k) → ZMod 2) → ℂ) (u : Fin k → ZMod 2) :
    readFunction (letterAmp (g.liftUnread n) f) u ∈ readModule f := by
  have hread : readFunction (letterAmp (g.liftUnread n) f) u
      = fun x => letterAmp g (unreadVector f x) u := by
    funext x
    exact congrFun (unreadVector_letterAmp_liftUnread g f x) u
  rw [hread]
  cases g with
  | hadamard i =>
    have h : (fun x => letterAmp (GateLetter.hadamard i : GateLetter k M) (unreadVector f x) u)
        = (1 / (Real.sqrt 2 : ℂ)) • (readFunction f (Function.update u i 0)
          + signOf (u i) • readFunction f (Function.update u i 1)) := by
      funext x
      rfl
    rw [h]
    exact smul_mem_readModule one_div_sqrt_two_mem_dyadicCyclotomicRing
      (Submodule.add_mem _ (readFunction_mem_readModule f _)
        (smul_mem_readModule (signOf_mem_dyadicCyclotomicRing _)
          (readFunction_mem_readModule f _)))
  | diagonal D =>
    have h : (fun x => letterAmp (GateLetter.diagonal D) (unreadVector f x) u)
        = charOf M (DiagPhase.eval D u) • readFunction f u := by
      funext x
      rfl
    rw [h]
    exact smul_mem_readModule (charOf_mem_dyadicCyclotomicRing M _)
      (readFunction_mem_readModule f u)
  | cnot i j hij => exact readFunction_mem_readModule f (DiagPhase.cnotBitMap i j u)

private theorem readModule_letterAmp_liftUnread_le {k M : ℕ} (g : GateLetter k M)
    (f : (Fin (n + k) → ZMod 2) → ℂ) : readModule (letterAmp (g.liftUnread n) f) ≤ readModule f :=
  Submodule.span_le.mpr (by
    rintro _ ⟨u, rfl⟩
    exact readFunction_letterAmp_liftUnread_mem g f u)

/-- A lifted letter keeps the module: the inverse letter is a letter of the same kind. -/
private theorem readModule_letterAmp_liftUnread {k M : ℕ} (g : GateLetter k M)
    (f : (Fin (n + k) → ZMod 2) → ℂ) :
    readModule (letterAmp (g.liftUnread n) f) = readModule f := by
  refine le_antisymm (readModule_letterAmp_liftUnread_le g f) ?_
  have h := readModule_letterAmp_liftUnread_le (invLetter g) (letterAmp (g.liftUnread n) f)
  rwa [liftUnread_invLetter, letterAmp_invLetter] at h

/-- Move (b) keeps the module. -/
private theorem readModule_runAmp_liftUnread {k M : ℕ} (W : GateWord k M)
    (f : (Fin (n + k) → ZMod 2) → ℂ) : readModule (runAmp (liftUnread n W) f) = readModule f := by
  induction W generalizing f with
  | nil => rfl
  | cons g gs ih =>
    change readModule (runAmp (liftUnread n gs) (letterAmp (g.liftUnread n) f)) = _
    rw [ih, readModule_letterAmp_liftUnread]

/-- Move (c) keeps the module: each read function after the drop is a read function of the input,
and the input's read functions off the determined value are zero. -/
private theorem readModule_dropUnread {k : ℕ} (S : KernelSumState (n + (k + 1)))
    (j : Fin (k + 1)) (hj : DeterminedByUnread S j) :
    readModule (amp (dropUnread j S)) = readModule (amp S) := by
  obtain ⟨g, c, hfun⟩ := exists_unread_functional hj
  have hdrop : ∀ u, readFunction (amp (dropUnread j S)) u
      = readFunction (amp S) (Fin.insertNth j (c - ∑ i, g i * u i) u) := by
    intro u
    funext x
    change unreadVector (amp (dropUnread j S)) x u = _
    rw [unreadVector_dropUnread S j hj x]
    exact sum_insertNth_eq hfun x u
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨u, rfl⟩
    rw [hdrop]
    exact readFunction_mem_readModule _ _
  · rintro _ ⟨u, rfl⟩
    rw [← Fin.insertNth_self_removeNth j u]
    by_cases hβ : u j = c - ∑ i, g i * Fin.removeNth j u i
    · rw [hβ, ← hdrop]
      exact readFunction_mem_readModule _ _
    · have h0 : readFunction (amp S) (Fin.insertNth j (u j) (Fin.removeNth j u)) = 0 :=
        funext fun x => amp_insertNth_eq_zero hfun hβ
      rw [h0]
      exact Submodule.zero_mem _

/-- **The invariant.** A derivation keeps the `ℤ[ζ_{2^∞}, ½]`-module spanned by the read functions:
a rule keeps `amp`, a word replaces the read functions by combinations of them through matrices with
entries in the ring and with inverses of the same kind, and a drop removes only read functions that
are zero. A pair whose modules differ, such as one with `3/5` in one side's read functions and not
the other's, is not derivable, at every precision. -/
theorem readModule_eq_of_derivable {A B : UnreadState n} (hAB : UnreadDerivable A B) :
    readModule (amp A.2) = readModule (amp B.2) := by
  induction hAB with
  | rel A B hAB =>
    cases hAB with
    | rule hST =>
      rw [show amp _ = amp _ from stateEq_of_carrierRule hST]
    | runUnread W hS hm =>
      rw [amp_run _ hS hm, readModule_runAmp_liftUnread]
    | drop S j hj => exact (readModule_dropUnread S j hj).symm
  | refl A => rfl
  | symm A B _ ih => exact ih.symm
  | trans A B C _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The obstruction: rationals in the ring, and pairs no derivation relates -/

/-- Every element of `ℤ[ζ_{2^∞}, ½]` becomes integral over `ℤ` after multiplying by a power of
two. -/
theorem exists_two_pow_mul_isIntegral {z : ℂ} (hz : z ∈ dyadicCyclotomicRing) :
    ∃ N : ℕ, IsIntegral ℤ ((2 : ℂ) ^ N * z) := by
  have two : IsIntegral ℤ (2 : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := 2))
  have two_pow : ∀ N : ℕ, IsIntegral ℤ ((2 : ℂ) ^ N) := fun N => two.pow N
  induction hz using Subring.closure_induction with
  | mem z hz =>
    rcases hz with hz | ⟨M, hM⟩
    · refine ⟨1, ?_⟩
      rw [Set.mem_singleton_iff.mp hz, pow_one, mul_inv_cancel₀ two_ne_zero]
      exact isIntegral_one
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact IsIntegral.of_pow (pow_pos two_pos M) (hM ▸ isIntegral_one)
  | zero => exact ⟨0, by simpa using isIntegral_zero⟩
  | one => exact ⟨0, by simpa using isIntegral_one⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨N₁ + N₂, ?_⟩
    have h : (2 : ℂ) ^ (N₁ + N₂) * (x + y) = 2 ^ N₂ * (2 ^ N₁ * x) + 2 ^ N₁ * (2 ^ N₂ * y) := by
      ring
    rw [h]
    exact ((two_pow N₂).mul h₁).add ((two_pow N₁).mul h₂)
  | neg x _ hx =>
    obtain ⟨N, h⟩ := hx
    exact ⟨N, by simpa [mul_neg] using h.neg⟩
  | mul x y _ _ hx hy =>
    obtain ⟨N₁, h₁⟩ := hx
    obtain ⟨N₂, h₂⟩ := hy
    refine ⟨N₁ + N₂, ?_⟩
    have h : (2 : ℂ) ^ (N₁ + N₂) * (x * y) = (2 ^ N₁ * x) * (2 ^ N₂ * y) := by ring
    rw [h]
    exact h₁.mul h₂

/-- The ring is closed under complex conjugation: `½` is real and the conjugate of a root of unity
of order `2^M` is one. -/
theorem starRingEnd_mem_dyadicCyclotomicRing {z : ℂ} (hz : z ∈ dyadicCyclotomicRing) :
    starRingEnd ℂ z ∈ dyadicCyclotomicRing := by
  have h : dyadicCyclotomicRing ≤ dyadicCyclotomicRing.comap (starRingEnd ℂ) := by
    refine Subring.closure_le.mpr fun w hw => ?_
    rcases hw with hw | ⟨M, hM⟩
    · rw [Set.mem_singleton_iff.mp hw]
      exact Subring.subset_closure (Or.inl (by rw [Set.mem_singleton_iff, map_inv₀, map_ofNat]))
    · exact Subring.subset_closure (Or.inr ⟨M, by
        change starRingEnd ℂ w ^ 2 ^ M = 1
        rw [← map_pow, hM, map_one]⟩)
  exact h hz

/-- A rational number in the ring has a power of two as its denominator: some `2^N · q` is an
integer. -/
theorem exists_two_pow_mul_eq_int_of_ratCast_mem {q : ℚ} (hq : (q : ℂ) ∈ dyadicCyclotomicRing) :
    ∃ (N : ℕ) (a : ℤ), (2 : ℚ) ^ N * q = a := by
  obtain ⟨N, hN⟩ := exists_two_pow_mul_isIntegral hq
  have hcast : (2 : ℂ) ^ N * q = (((2 : ℚ) ^ N * q : ℚ) : ℂ) := by push_cast; ring
  rw [hcast] at hN
  have hQ : IsIntegral ℤ ((2 : ℚ) ^ N * q) :=
    (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective).mp hN
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hQ
  exact ⟨N, a, by rw [← ha]; simp⟩

/-- `a/5` is not in the ring when `5` does not divide `a`. -/
theorem intCast_div_five_not_mem_dyadicCyclotomicRing {a : ℤ} (ha : ¬ (5 : ℤ) ∣ a) :
    (a : ℂ) / 5 ∉ dyadicCyclotomicRing := by
  intro h
  have hq : (((a / 5 : ℚ)) : ℂ) ∈ dyadicCyclotomicRing := by push_cast; exact h
  obtain ⟨N, b, hb⟩ := exists_two_pow_mul_eq_int_of_ratCast_mem hq
  have hz : (2 : ℤ) ^ N * a = 5 * b := by
    have : (2 : ℚ) ^ N * a = 5 * b := by rw [← hb]; field_simp
    exact_mod_cast this
  have hco : IsCoprime (5 : ℤ) (2 ^ N) := IsCoprime.pow_right ⟨1, -2, by norm_num⟩
  exact ha (hco.dvd_of_dvd_mul_left ⟨b, hz⟩)

/-- **Not derivable.** If a read function of `B` lies outside the module the read functions of `A`
span, no derivation relates `A` and `B` (`readModule_eq_of_derivable`). -/
theorem not_unreadDerivable_of_readFunction_not_mem {A B : UnreadState n}
    (u : Fin B.1 → ZMod 2) (hu : readFunction (amp B.2) u ∉ readModule (amp A.2)) :
    ¬ UnreadDerivable A B := fun h =>
  hu (readModule_eq_of_derivable h ▸ Submodule.subset_span ⟨u, rfl⟩)

/-! ## Bridges to Mathlib's matrices

The frame's objects as the textbook ones (docs/STEPS.md, entry 2026-10-01k): the Gram data is
the reduced density matrix `F Fᴴ` of the amplitude matrix, and `UnreadEq` is the unitary
freedom of purifications, `G = F Uᵀ`. -/

section MatrixBridge

open scoped Matrix

/-- The amplitude as a matrix: rows the read words `x`, columns the unread words `u`, entry
`f(x, u)`. -/
def ampMatrix {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) :
    Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ :=
  Matrix.of fun x u => f (Fin.append x u)

/-- **The Gram data is `F Fᴴ`**, the reduced density matrix on the read bits of the
(unnormalised) state with amplitude matrix `F`: the unread bits traced out. -/
theorem gram_eq_mul_conjTranspose {k : ℕ} (f : (Fin (n + k) → ZMod 2) → ℂ) :
    Matrix.of (gram f) = ampMatrix f * (ampMatrix f)ᴴ := by
  ext x y
  simp only [Matrix.of_apply, gram, Matrix.mul_apply, ampMatrix, Matrix.conjTranspose_apply,
    Complex.star_def]

/-- `UnreadEq` is equality of the reduced density matrices `F Fᴴ = G Gᴴ`. -/
theorem unreadEq_iff_mul_conjTranspose_eq {k : ℕ} (S T : KernelSumState (n + k)) :
    UnreadEq k S T ↔
      ampMatrix (amp S) * (ampMatrix (amp S))ᴴ = ampMatrix (amp T) * (ampMatrix (amp T))ᴴ := by
  rw [← gram_eq_mul_conjTranspose, ← gram_eq_mul_conjTranspose]
  constructor
  · intro h
    ext x y
    exact h x y
  · intro h x y
    exact congrFun (congrFun (congrArg (fun M => (M : Matrix _ _ ℂ)) h) x) y

/-- **Purification, in matrix form.** `UnreadEq` holds exactly when `G = F Uᵀ` for a unitary `U`
on the unread bits: the textbook unitary freedom of purifications, from
`unreadEq_iff_exists_isometry`. -/
theorem unreadEq_iff_exists_unitary_mul {k : ℕ} (S T : KernelSumState (n + k)) :
    UnreadEq k S T ↔ ∃ U ∈ Matrix.unitaryGroup (Fin k → ZMod 2) ℂ,
      ampMatrix (amp T) = ampMatrix (amp S) * Uᵀ := by
  rw [unreadEq_iff_exists_isometry]
  refine exists_congr fun U => and_congr_right fun _ => ?_
  constructor
  · intro h
    ext x u
    change unreadVector (amp T) x u = _
    rw [← h x]
    simp only [ampMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct, unreadVector, mul_comm]
  · intro h x
    funext u
    have := congrFun (congrFun (congrArg (fun M => (M : Matrix _ _ ℂ)) h) x) u
    simp only [ampMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply] at this
    simp only [Matrix.mulVec, dotProduct, unreadVector, this, mul_comm]

end MatrixBridge

end FTQCLib.Frame.Walkthrough

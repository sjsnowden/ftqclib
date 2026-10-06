/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.BoundElimination
import FTQCLib.Carrier.CarrierState
import FTQCLib.Carrier.HadamardAmplitude
import FTQCLib.Carrier.PrecisionGauge
import FTQCLib.Carrier.ZModTwo

/-!
# Elimination order above height one

The spike T04 (`docs/TARGETS.md`, framed in `docs/framing/T04.md`) asks whether the carrier state an
elimination sequence reaches depends on the order in which bound bits are eliminated, when the
difference of the bit being eliminated reads other bound bits. This file states the answer the
search (`tools/search/elimination_order.py`, cases in `EliminationOrderData`) points to: **the order
matters**. Two maximal elimination sequences from one carrier state reach two carrier states of the
same height and the same amplitude that no gauge rewrite R1–R7 relates.

**The objects.** An elimination step at bound bit `j` moves `j` to the last position of the bound
register by the transposition of `j` with the last bound bit (`boundToLast`, an instance of R5), and
then applies `elimCollapse` or `elimRotate` when its shape (`SignAffine`, `RotateData`) holds there;
the step is available exactly when one of the shapes holds (`StepAvailable`). A carrier state at
which no step is available is `EliminationStuck`: a sequence ending there is maximal. The gauge
rewrites are one constructor each of `GaugeStep`, with the hypotheses of the repository theorem that
proves the rewrite sound; `GaugeRel` is their equivalence closure, and it lies inside `StateEq`
(`stateEq_of_gaugeRel`). An elimination is not a gauge rewrite.

**The certificate is by invariant.** Every disagreement the search found has equal reaches
(`byReach = false` in every case of `EliminationOrderData.cases`), so the separation uses the
framing's invariant: at each support word `w`, the multiset of the terms `c · charOf m (Q(w, y))`
over the bound words `y` (`boundTerms`). Each of R1–R7 preserves it (`boundTerms_eq_of_gaugeStep`),
R6 included, so the equivalence closure does (`boundTerms_eq_of_gaugeRel`).

**The witness.** The first case of `EliminationOrderData.cases`: `n = 0`, `h = 3`, `m = 2`,
exponent `Q = y₀ + 3·y₁ + 2·y₀·y₁·y₂` over `ZMod 4`. The framing's order for the smallest case
(fewest `n + h`, then smallest `m`, then fewest nonzero monomials) ties it with the first
`n = 1, h = 2, m = 2` case; the tie is broken by the data module's order. Along `y₀` the difference
is `1 + 2·y₁·y₂`, along `y₁` it is `3 + 2·y₀·y₂`: both rotate with `a = 1`, and both read the other
bound bits. Sequence A rotates `y₀` away (`Λ = y₂·y₁`, in the input's names), sequence B rotates
`y₁` away (`Λ = 1 − y₀·y₂`). Each outcome is at height two and stuck, and their term multisets are
`c'·{1, 1, −i, −1}` and `c'·{−i, −i, 1, i}` with `c' = (1 + i)/√2`.

Everything here is frame-pure. No `FTQCLib.Hilbert` module is imported; `liftTo` keeps its full
name `FTQCLib.Hilbert.liftTo`.

## Main definitions

* `boundToLast`, `StepAvailable`, `EliminationStuck` — the elimination step's coordinate move, its
  availability, and maximality.
* `GaugeStep`, `GaugeRel` — the gauge rewrites R1–R7 and their equivalence closure.
* `boundTerms` — the multiset invariant of the gauge rewrites.
* `EliminationOrder.input`, `EliminationOrder.outcomeA`, `EliminationOrder.outcomeB` — the witness.

## Main results

* `stateEq_of_gaugeRel` — the gauge relation lies inside equality of denotation.
* `boundTerms_eq_of_gaugeRel` — the gauge relation preserves the term multiset.
* `EliminationOrder.not_gaugeRel_outcomeA_outcomeB` — the two outcomes are not gauge related.
* `EliminationOrder.elimination_order_matters` — the headline: a carrier state, two available
  rotate steps, both outcomes denoting the input's state, both stuck at one height, and no gauge
  rewrite relating them.

## Implementation notes

* `GaugeStep`'s R1 constructor writes the scale's phase as `charOf m a`, which is by definition the
  `Complex.exp` term of `amp_add_C`.
* `GaugeStep` and `GaugeRel` cannot live in `CarrierAmplitude.lean`: R6 needs `hRaise` and R7 needs
  `liftTo`, both above it. They are stated here because T04 is their first consumer.
* The witness is at `n = 0`, so its support is the one empty word, `L = ⊥` (the span of no `X_i`,
  as the framing's full support asks), and no instance of R6 exists at its size; the invariance
  theorems are stated at every `n`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The elimination step and maximality -/

/-- Bound bit `j` moved to the last position of the bound register by the transposition of `j` with
the last bound bit: the coordinate move of an elimination step, an instance of R5. -/
noncomputable def boundToLast {m h : ℕ} (j : Fin (h + 1)) (Q : DiagPhase (n + (h + 1)) m) :
    DiagPhase (n + h + 1) m :=
  MvPolynomial.rename (Equiv.swap (Fin.natAdd n j) (Fin.last (n + h))) Q

/-- The moved exponent evaluates as the original exponent at the word read through the
transposition. -/
private theorem eval_boundToLast {m h : ℕ} (j : Fin (h + 1)) (Q : DiagPhase (n + (h + 1)) m)
    (v : Fin (n + h + 1) → ZMod 2) :
    DiagPhase.eval (boundToLast j Q) v
      = DiagPhase.eval Q (v ∘ Equiv.swap (Fin.natAdd n j) (Fin.last (n + h))) := by
  unfold boundToLast DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  rfl

/-- An elimination step is available at bound bit `j`: after moving `j` last, the collapse shape
holds for some `σ, ε` or the rotate shape holds for some `a, Λ`. -/
def StepAvailable {m h : ℕ} (Q : DiagPhase (n + (h + 1)) m) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2) (j : Fin (h + 1)) : Prop :=
  (∃ (σ : Fin n → ZMod 2) (ε : ZMod 2), SignAffine (boundToLast j Q) L x₀ σ ε) ∨
    ∃ (a : ZMod (2 ^ m)) (Λ : DiagPhase (n + h) m), RotateData (boundToLast j Q) L x₀ a Λ

/-- No elimination step is available at any bound bit: an elimination sequence ending here is
maximal. -/
def EliminationStuck {m h : ℕ} (Q : DiagPhase (n + (h + 1)) m) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2) : Prop :=
  ∀ j : Fin (h + 1), ¬ StepAvailable Q L x₀ j

/-! ## The gauge rewrites R1–R7 -/

/-- One gauge rewrite, R1 to R7, each with the hypotheses of the theorem that proves it sound. -/
inductive GaugeStep : KernelSumState n → KernelSumState n → Prop
  /-- **R1** (`amp_add_C`): the constant term of the exponent against the scale. -/
  | addC {m h : ℕ} (Q : DiagPhase (n + h) m) (a : ZMod (2 ^ m)) (c : ℂ)
      (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
      GaugeStep ⟨m, h, Q + MvPolynomial.C a, c, L, x₀⟩ ⟨m, h, Q, c * charOf m a, L, x₀⟩
  /-- **R2** (`amp_offset_add_mem`): the offset modulo the shadow. -/
  | offsetAddMem {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n))
      (x₀ : Fin n → ZMod 2) {v : Fin n → ZMod 2} (hv : v ∈ Submodule.map xProj L) :
      GaugeStep ⟨m, h, Q, c, L, x₀ + v⟩ ⟨m, h, Q, c, L, x₀⟩
  /-- **R3** (`amp_congr_xProj`): the Z-part of `L`. -/
  | congrXProj {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ) (L L' : Submodule (ZMod 2) (Pauli n))
      (x₀ : Fin n → ZMod 2) (hsh : Submodule.map xProj L = Submodule.map xProj L') :
      GaugeStep ⟨m, h, Q, c, L, x₀⟩ ⟨m, h, Q, c, L', x₀⟩
  /-- **R4** (`amp_congr_support`): the exponent off the support coset. -/
  | congrSupport {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n))
      (x₀ : Fin n → ZMod 2)
      (hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
        DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w y)) :
      GaugeStep ⟨m, h, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩
  /-- **R5** (`amp_rename_bound`): relabelling the bound register by a bijection of its words. -/
  | renameBound {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n))
      (x₀ : Fin n → ZMod 2) (σ : (Fin h → ZMod 2) ≃ (Fin h → ZMod 2))
      (hQ : ∀ w : Fin n → ZMod 2, ∀ y : Fin h → ZMod 2,
        DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w (σ y))) :
      GaugeStep ⟨m, h, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩
  /-- **R6** (`amp_hRaise_indep`): the representer of `hRaise`. -/
  | hRaiseIndep (i : Fin n) (u u' : Fin n → ZMod 2) (S : KernelSumState n)
      (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
      (hui : u i = 0) (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
      (hui' : u' i = 0) (hrep' : ∀ v ∈ Submodule.map xProj S.L, dotF2 u' v = v i)
      (hm : 1 ≤ S.m) :
      GaugeStep (hRaise i u S) (hRaise i u' S)
  /-- **R7** (`amp_liftTo`): the precision lift from `m` to `k ≥ m`. -/
  | liftTo {m h : ℕ} (k : ℕ) (hmk : m ≤ k) (Q : DiagPhase (n + h) m) (c : ℂ)
      (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
      GaugeStep ⟨k, h, FTQCLib.Hilbert.liftTo k hmk Q, c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩

/-- Two carrier states are gauge related when a chain of gauge rewrites R1–R7, each taken in
either direction, leads from one to the other. -/
def GaugeRel : KernelSumState n → KernelSumState n → Prop :=
  Relation.EqvGen GaugeStep

/-- A gauge rewrite keeps the denotation. -/
theorem stateEq_of_gaugeStep {S T : KernelSumState n} (hST : GaugeStep S T) : StateEq S T := by
  cases hST with
  | @addC m h Q a c L x₀ => exact amp_add_C Q a c L x₀
  | @offsetAddMem m h Q c L x₀ v hv => exact amp_offset_add_mem Q c L x₀ hv
  | @congrXProj m h Q c L L' x₀ hsh => exact amp_congr_xProj Q c L L' x₀ hsh
  | @congrSupport m h Q Q' c L x₀ hQ => exact amp_congr_support Q Q' c L x₀ hQ
  | @renameBound m h Q Q' c L x₀ σ hQ => exact amp_rename_bound Q Q' c L x₀ σ hQ
  | hRaiseIndep i u u' S horth hui hrep hui' hrep' hm =>
    exact amp_hRaise_indep i u u' S horth hui hrep hui' hrep' hm
  | @liftTo m h k hmk Q c L x₀ => exact amp_liftTo k hmk Q c L x₀

/-- **Soundness of the gauge relation.** Gauge related carrier states denote the same state. -/
theorem stateEq_of_gaugeRel {S T : KernelSumState n} (hST : GaugeRel S T) : StateEq S T := by
  unfold GaugeRel at hST
  induction hST with
  | rel _ _ h => exact stateEq_of_gaugeStep h
  | refl _ => exact StateEq.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The term multiset -/

open Classical in
/-- At a support word `w`, the multiset of the terms `c · charOf m (Q(w, y))` over the bound words
`y`; the empty multiset off the support. -/
noncomputable def boundTerms (S : KernelSumState n) (w : Fin n → ZMod 2) : Multiset ℂ :=
  if ∃ p ∈ S.L, w = S.x₀ + p.X then
    Multiset.map
      (fun y : Fin S.h → ZMod 2 => S.c * charOf S.m (DiagPhase.eval S.Q (Fin.append w y)))
      (Finset.univ : Finset (Fin S.h → ZMod 2)).val
  else 0

open Classical in
/-- `boundTerms` of an explicit record, with the record's fields read off. -/
private theorem boundTerms_mk {m h : ℕ} (Q : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ w : Fin n → ZMod 2) :
    boundTerms (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) w
      = if ∃ p ∈ L, w = x₀ + p.X then
          Multiset.map
            (fun y : Fin h → ZMod 2 => c * charOf m (DiagPhase.eval Q (Fin.append w y)))
            (Finset.univ : Finset (Fin h → ZMod 2)).val
        else 0 :=
  rfl

/-- Two records at one height have the same term multiset when their supports agree and their
terms agree on the support, bound word by bound word. -/
private theorem boundTerms_congr_terms {m m' h : ℕ} {Q : DiagPhase (n + h) m}
    {Q' : DiagPhase (n + h) m'} {c c' : ℂ} {L L' : Submodule (ZMod 2) (Pauli n)}
    {x₀ x₀' : Fin n → ZMod 2}
    (hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L', w = x₀' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X))
    (hterm : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
      c' * charOf m' (DiagPhase.eval Q' (Fin.append w y))
        = c * charOf m (DiagPhase.eval Q (Fin.append w y))) :
    boundTerms (⟨m', h, Q', c', L', x₀'⟩ : KernelSumState n) = boundTerms ⟨m, h, Q, c, L, x₀⟩ := by
  funext w
  rw [boundTerms_mk, boundTerms_mk]
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [if_pos ((hsupp w).mpr hw), if_pos hw]
    exact Multiset.map_congr rfl fun y _ => hterm w hw y
  · rw [if_neg (fun hw' => hw ((hsupp w).mp hw')), if_neg hw]

/-- R5 keeps the term multiset: the bijection of bound words permutes the terms. -/
private theorem boundTerms_rename {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (σ : (Fin h → ZMod 2) ≃ (Fin h → ZMod 2))
    (hQ : ∀ w : Fin n → ZMod 2, ∀ y : Fin h → ZMod 2,
      DiagPhase.eval Q' (Fin.append w y) = DiagPhase.eval Q (Fin.append w (σ y))) :
    boundTerms (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n) = boundTerms ⟨m, h, Q, c, L, x₀⟩ := by
  funext w
  rw [boundTerms_mk, boundTerms_mk]
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [if_pos hw, if_pos hw]
    conv_rhs => rw [← Multiset.map_univ_val_equiv σ]
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun y _ => by rw [Function.comp_apply, hQ w y]
  · rw [if_neg hw, if_neg hw]

/-- Each gauge rewrite R1–R7 keeps the term multiset at every word. -/
theorem boundTerms_eq_of_gaugeStep {S T : KernelSumState n} (hST : GaugeStep S T) :
    boundTerms S = boundTerms T := by
  cases hST with
  | @addC m h Q a c L x₀ =>
    refine boundTerms_congr_terms (fun _ => Iff.rfl) (fun w _ y => ?_)
    rw [DiagPhase.eval_add, DiagPhase.eval_C, charOf_add]
    ring
  | @offsetAddMem m h Q c L x₀ v hv =>
    refine boundTerms_congr_terms (fun w => ?_) (fun _ _ _ => rfl)
    refine (mem_support_iff (⟨m, h, Q, c, L, x₀ + v⟩ : KernelSumState n) w).trans
      (Iff.trans ?_ (mem_support_iff (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) w).symm)
    change w - (x₀ + v) ∈ Submodule.map xProj L ↔ w - x₀ ∈ Submodule.map xProj L
    constructor
    · intro hmem
      have h' := add_mem hmem hv
      rwa [show w - (x₀ + v) + v = w - x₀ by abel] at h'
    · intro hmem
      have h' := sub_mem hmem hv
      rwa [show w - x₀ - v = w - (x₀ + v) by abel] at h'
  | @congrXProj m h Q c L L' x₀ hsh =>
    refine boundTerms_congr_terms (fun w => ?_) (fun _ _ _ => rfl)
    refine (mem_support_iff (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) w).trans
      (Iff.trans ?_ (mem_support_iff (⟨m, h, Q, c, L', x₀⟩ : KernelSumState n) w).symm)
    change w - x₀ ∈ Submodule.map xProj L ↔ w - x₀ ∈ Submodule.map xProj L'
    rw [hsh]
  | @congrSupport m h Q Q' c L x₀ hQ =>
    exact boundTerms_congr_terms (fun _ => Iff.rfl) (fun w hw y => by rw [hQ w hw y])
  | @renameBound m h Q Q' c L x₀ σ hQ => exact boundTerms_rename Q Q' c L x₀ σ hQ
  | hRaiseIndep i u u' S horth hui hrep hui' hrep' hm =>
    refine boundTerms_congr_terms (L := Submodule.map (pauliSwapOn {i}) S.L)
      (x₀ := Function.update S.x₀ i 0) (fun _ => Iff.rfl) (fun w hw y => ?_)
    obtain ⟨p, hp, hwp⟩ := hw
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hp
    -- On the output support the branch value `raiseConst + u ⬝ w` is `x₀ i + q.X i` for every
    -- representer `u`, so the two exponents agree there.
    have hw' : w = Function.update (S.x₀ + q.X) i (q.Z i) := by
      rw [hwp]
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have hqX : q.X ∈ Submodule.map xProj S.L := Submodule.mem_map.mpr ⟨q, hq, xProj_apply q⟩
    have tu : ∀ r : Fin n → ZMod 2, r i = 0 →
        (∀ z ∈ Submodule.map xProj S.L, dotF2 r z = z i) →
        raiseConst i r S.x₀ + dotF2 r w = S.x₀ i + q.X i := by
      intro r hri hrrep
      rw [hw', dotF2_update_of_eq_zero hri, dotF2_add_right, hrrep _ hqX]
      unfold raiseConst
      exact (show ∀ a b d : ZMod 2, a + b + (b + d) = a + d by decide) _ _ _
    have hfun : (fun j => Fin.append w y (Fin.castAdd S.h j)) = w :=
      funext fun j => Fin.append_left w y j
    have key : DiagPhase.eval (hRaise i u S).Q (Fin.append w y : Fin (n + S.h) → ZMod 2)
        = DiagPhase.eval (hRaise i u' S).Q (Fin.append w y : Fin (n + S.h) → ZMod 2) := by
      rw [hRaise_eval, hRaise_eval, hfun, tu u hui hrep, tu u' hui' hrep']
    exact congrArg (fun z => S.c / (Real.sqrt 2 : ℂ) * charOf S.m z) key
  | @liftTo m h k hmk Q c L x₀ =>
    refine boundTerms_congr_terms (fun _ => Iff.rfl) (fun w _ y => ?_)
    rw [← exp_realPhase_eq_charOf, ← exp_realPhase_eq_charOf,
      congrFun (FTQCLib.Hilbert.liftTo_realPhase k hmk Q) (Fin.append w y)]

/-- The gauge relation keeps the term multiset at every word. -/
theorem boundTerms_eq_of_gaugeRel {S T : KernelSumState n} (hST : GaugeRel S T) :
    boundTerms S = boundTerms T := by
  unfold GaugeRel at hST
  induction hST with
  | rel _ _ h => exact boundTerms_eq_of_gaugeStep h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The witness -/

namespace EliminationOrder

/-- The input exponent `y₀ + 3·y₁ + 2·y₀·y₁·y₂` over `ZMod 4`: the first case of
`EliminationOrderData.cases`. -/
noncomputable def inputExponent : DiagPhase (0 + 3) 2 :=
  MvPolynomial.X 0 + MvPolynomial.C 3 * MvPolynomial.X 1
    + MvPolynomial.C 2 * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)

/-- The input carrier state: no free bits, three bound bits, precision two, scale one. -/
noncomputable def input : KernelSumState 0 :=
  ⟨2, 3, inputExponent, 1, ⊥, 0⟩

/-- Sequence A's rotate bit after `y₀` is moved last: `Λ = y₂·y₁`, read in the renamed variables. -/
noncomputable def lambdaA : DiagPhase (0 + 2) 2 :=
  MvPolynomial.X 0 * MvPolynomial.X 1

/-- Sequence B's rotate bit after `y₁` is moved last: `Λ = 1 − y₀·y₂`, read in the renamed
variables. -/
noncomputable def lambdaB : DiagPhase (0 + 2) 2 :=
  1 - MvPolynomial.X 0 * MvPolynomial.X 1

/-- Sequence A's outcome: `y₀` moved last and rotated away with `a = 1`. -/
noncomputable def outcomeA : KernelSumState 0 :=
  elimRotate (boundToLast (h := 2) 0 inputExponent) 1 lambdaA 1 ⊥ 0

/-- Sequence B's outcome: `y₁` moved last and rotated away with `a = 1`. -/
noncomputable def outcomeB : KernelSumState 0 :=
  elimRotate (boundToLast (h := 2) 1 inputExponent) 1 lambdaB 1 ⊥ 0

/-! ### Evaluation and counting on the witness

The exponents are evaluated by rewriting `DiagPhase.eval` into the values of the word's bits;
the remaining arithmetic in `ZMod 4` over finitely many bits is decided. -/

/-- `lambdaB` evaluates to `1 − y₀·y₁`. -/
private theorem eval_lambdaB (v : Fin (0 + 2) → ZMod 2) :
    DiagPhase.eval lambdaB v = 1 - ((v 0).val : ZMod (2 ^ 2)) * ((v 1).val : ZMod (2 ^ 2)) := by
  unfold lambdaB DiagPhase.eval
  simp [DiagPhase.liftBinary]

/-- The rotate scale `(1 + i)/√2` of both outcomes is not zero. -/
private theorem scale_ne_zero : (1 : ℂ) * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ) ≠ 0 := by
  have h1 : (1 : ℂ) + charOf 2 1 ≠ 0 := one_add_charOf_ne_zero (by norm_num) (by decide)
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
  exact div_ne_zero (by rwa [one_mul]) h2

/-- A sum over the four words of two bits. -/
private theorem sum_words_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → ZMod 2) → M) :
    ∑ y, F y = F ![0, 0] + F ![0, 1] + (F ![1, 0] + F ![1, 1]) := by
  rw [← (piFinTwoEquiv fun _ => ZMod 2).symm.sum_comp F, Fintype.sum_prod_type, sum_zmod_two,
    sum_zmod_two, sum_zmod_two]
  rfl

/-- With no free bits and `L = ⊥`, the one (empty) word is on the support. -/
private theorem mem_support_bot :
    ∃ p ∈ (⊥ : Submodule (ZMod 2) (Pauli 0)), (0 : Fin 0 → ZMod 2) = 0 + p.X :=
  ⟨0, Submodule.zero_mem _, Subsingleton.elim _ _⟩

/-- The amplitude of a record with no free bits and `L = ⊥` at the empty word. -/
private theorem amp_bot_zero {m h : ℕ} (Q : DiagPhase (0 + h) m) (c : ℂ) :
    amp (⟨m, h, Q, c, ⊥, 0⟩ : KernelSumState 0) (0 : Fin 0 → ZMod 2) = ampCore m h Q c 0 :=
  amp_pos mem_support_bot

/-- The term multiset of a record with no free bits and `L = ⊥` at the empty word. -/
private theorem boundTerms_bot_zero {m h : ℕ} (Q : DiagPhase (0 + h) m) (c : ℂ) :
    boundTerms (⟨m, h, Q, c, ⊥, 0⟩ : KernelSumState 0) (0 : Fin 0 → ZMod 2)
      = Multiset.map
          (fun y : Fin h → ZMod 2 =>
            c * charOf m (DiagPhase.eval Q (Fin.append (0 : Fin 0 → ZMod 2) y)))
          (Finset.univ : Finset (Fin h → ZMod 2)).val := by
  rw [boundTerms_mk, if_pos mem_support_bot]

/-- Sequence A's outcome exponent `3·y₁ − y₀·y₁` at the four words: `0, 3, 0, 2`. -/
private theorem eval_outcomeA_words :
    DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
        + MvPolynomial.C (-1) * lambdaA : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![0, 0] : Fin 2 → ZMod 2)) = 0
    ∧ DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
        + MvPolynomial.C (-1) * lambdaA : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![0, 1] : Fin 2 → ZMod 2)) = 3
    ∧ DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
        + MvPolynomial.C (-1) * lambdaA : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![1, 0] : Fin 2 → ZMod 2)) = 0
    ∧ DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
        + MvPolynomial.C (-1) * lambdaA : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![1, 1] : Fin 2 → ZMod 2)) = 2 := by
  simp only [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, snocFreeze_eval,
    eval_boundToLast, inputExponent, lambdaA, DiagPhase.eval_X]
  decide

/-- Sequence B's outcome exponent `y₀ − 1 + y₀·y₁` at the four words: `3, 3, 0, 1`. -/
private theorem eval_outcomeB_words :
    DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 1 inputExponent)
        + MvPolynomial.C (-1) * lambdaB : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![0, 0] : Fin 2 → ZMod 2)) = 3
    ∧ DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 1 inputExponent)
        + MvPolynomial.C (-1) * lambdaB : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![0, 1] : Fin 2 → ZMod 2)) = 3
    ∧ DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 1 inputExponent)
        + MvPolynomial.C (-1) * lambdaB : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![1, 0] : Fin 2 → ZMod 2)) = 0
    ∧ DiagPhase.eval (snocFreeze 0 (boundToLast (h := 2) 1 inputExponent)
        + MvPolynomial.C (-1) * lambdaB : DiagPhase (0 + 2) 2)
        (Fin.append (0 : Fin 0 → ZMod 2) (![1, 1] : Fin 2 → ZMod 2)) = 1 := by
  simp only [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, snocFreeze_eval,
    eval_boundToLast, inputExponent, eval_lambdaB, DiagPhase.eval_X]
  decide

/-- **The parity test for maximality.** At `n = 0`, `h = 1`, `m = 2`, `L = ⊥`: if the difference
after moving bit `j` last is odd at one bound word and even at another, then no step is available
at `j`. The collapse shape makes every difference even, the rotate shape makes every difference
odd (`2a = 2` forces `a` odd). -/
private theorem not_stepAvailable_of_parity {Q : DiagPhase (0 + (1 + 1)) 2} {j : Fin (1 + 1)}
    (yOdd yEven : Fin 1 → ZMod 2)
    (hOdd : (lastDiff (boundToLast j Q)).eval (Fin.append (0 : Fin 0 → ZMod 2) yOdd) = 1
      ∨ (lastDiff (boundToLast j Q)).eval (Fin.append (0 : Fin 0 → ZMod 2) yOdd) = 3)
    (hEven : (lastDiff (boundToLast j Q)).eval (Fin.append (0 : Fin 0 → ZMod 2) yEven) = 0
      ∨ (lastDiff (boundToLast j Q)).eval (Fin.append (0 : Fin 0 → ZMod 2) yEven) = 2) :
    ¬ StepAvailable Q ⊥ 0 j := by
  have kOdd : ∀ t : ZMod 2,
      (1 : ZMod (2 ^ 2)) ≠ 2 ^ (2 - 1) * ((t.val : ℕ) : ZMod (2 ^ 2))
        ∧ (3 : ZMod (2 ^ 2)) ≠ 2 ^ (2 - 1) * ((t.val : ℕ) : ZMod (2 ^ 2)) := by
    decide
  have kEven : ∀ (a : ZMod (2 ^ 2)) (b : ZMod 2), 2 * a = 2 ^ (2 - 1) →
      (0 : ZMod (2 ^ 2)) ≠ a + 2 ^ (2 - 1) * ((b.val : ℕ) : ZMod (2 ^ 2))
        ∧ (2 : ZMod (2 ^ 2)) ≠ a + 2 ^ (2 - 1) * ((b.val : ℕ) : ZMod (2 ^ 2)) := by
    decide
  rintro (⟨σ, ε, hs⟩ | ⟨a, Λ, h1, h2⟩)
  · have h := hs 0 mem_support_bot yOdd
    rcases hOdd with hO | hO
    · exact (kOdd _).1 (hO.symm.trans h)
    · exact (kOdd _).2 (hO.symm.trans h)
  · obtain ⟨b, -, hb⟩ := h2 0 mem_support_bot yEven
    rcases hEven with hE | hE
    · exact (kEven a b h1).1 (hE.symm.trans hb)
    · exact (kEven a b h1).2 (hE.symm.trans hb)

/-- Sequence A's step: the rotate shape at `y₀`. -/
private theorem rotateData_A :
    RotateData (boundToLast (h := 2) 0 inputExponent) ⊥ 0 1 lambdaA := by
  refine ⟨by decide, fun w _ y => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  obtain ⟨a, b, rfl⟩ : ∃ a b : ZMod 2, y = ![a, b] :=
    ⟨y 0, y 1, by funext i; fin_cases i <;> rfl⟩
  refine ⟨a * b, ?_, ?_⟩
  · simp only [lambdaA, DiagPhase.eval_mul, DiagPhase.eval_X]
    revert a b
    decide
  · simp only [lastDiff_eval, eval_boundToLast, inputExponent, DiagPhase.eval_add,
      DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
    revert a b
    decide

/-- Sequence A's outcome and the input have the same amplitude: the rotate certificate, then the
transposition as an instance of R5. -/
private theorem amp_outcomeA_eq : amp outcomeA = amp input := by
  change amp (elimRotate (boundToLast (h := 2) 0 inputExponent) 1 lambdaA 1 ⊥ 0) = amp input
  rw [amp_elimRotate (by norm_num) 1 rotateData_A (fun _ => Iff.rfl)]
  refine amp_rename_bound inputExponent (boundToLast (h := 2) 0 inputExponent) 1 ⊥ 0
    ((Equiv.swap (0 : Fin 3) 2).arrowCongr (Equiv.refl (ZMod 2))) (fun w y => ?_)
  obtain rfl : w = 0 := Subsingleton.elim _ _
  obtain ⟨a, b, d, rfl⟩ : ∃ a b d : ZMod 2, y = ![a, b, d] :=
    ⟨y 0, y 1, y 2, by funext i; fin_cases i <;> rfl⟩
  simp only [eval_boundToLast, inputExponent, DiagPhase.eval_add, DiagPhase.eval_mul,
    DiagPhase.eval_C, DiagPhase.eval_X]
  revert a b d
  decide

/-- The input's amplitude is not the zero function: at the empty word it is
`(1 + i)/√2 · (1 − i)/2`, read through sequence A's outcome. -/
private theorem amp_input_ne_zero : amp input ≠ 0 := by
  intro h
  have h0 := congrFun (amp_outcomeA_eq.trans h) 0
  change amp (⟨2, 2, snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
      + MvPolynomial.C (-1) * lambdaA, 1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ), ⊥, 0⟩ :
      KernelSumState 0) 0 = 0 at h0
  obtain ⟨e00, e01, e10, e11⟩ := eval_outcomeA_words
  rw [amp_bot_zero, ampCore_eq_sum_charOf, sum_words_two, e00, e01, e10, e11, charOf_zero,
    charOf_two_three, charOf_two_two] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact scale_ne_zero h2
    · have h3 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_sqrt_two_ne_zero
      exact pow_ne_zero 2 h3 h2
  · have h2 := congrArg Complex.re h1
    simp at h2

/-- The input is a carrier state. -/
theorem isCarrier_input : IsCarrier input := by
  have hzero : ∀ p : Pauli 0, p = 0 := fun p => Pauli.ext (Subsingleton.elim _ _)
    (Subsingleton.elim _ _)
  refine ⟨(by norm_num : (1 : ℕ) ≤ 2), fun p _ q _ => ?_, fun p _ => ?_, amp_input_ne_zero⟩
  · rw [hzero p]
    exact omega_zero_left q
  · rw [hzero p]
    exact Submodule.zero_mem _

/-- Sequence A's step is available: the rotate shape holds at `y₀` with `a = 1` and `lambdaA`. -/
theorem rotateData_stepA :
    RotateData (boundToLast (h := 2) 0 inputExponent) ⊥ 0 1 lambdaA :=
  rotateData_A

/-- Sequence B's step is available: the rotate shape holds at `y₁` with `a = 1` and `lambdaB`. -/
theorem rotateData_stepB :
    RotateData (boundToLast (h := 2) 1 inputExponent) ⊥ 0 1 lambdaB := by
  refine ⟨by decide, fun w _ y => ?_⟩
  obtain rfl : w = 0 := Subsingleton.elim _ _
  obtain ⟨a, b, rfl⟩ : ∃ a b : ZMod 2, y = ![a, b] :=
    ⟨y 0, y 1, by funext i; fin_cases i <;> rfl⟩
  refine ⟨1 + a * b, ?_, ?_⟩
  · simp only [eval_lambdaB]
    revert a b
    decide
  · simp only [lastDiff_eval, eval_boundToLast, inputExponent, DiagPhase.eval_add,
      DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
    revert a b
    decide

/-- Sequence A's outcome denotes the input's state. -/
theorem stateEq_outcomeA_input : StateEq outcomeA input :=
  amp_outcomeA_eq

/-- Sequence B's outcome denotes the input's state. -/
theorem stateEq_outcomeB_input : StateEq outcomeB input := by
  change amp (elimRotate (boundToLast (h := 2) 1 inputExponent) 1 lambdaB 1 ⊥ 0) = amp input
  rw [amp_elimRotate (by norm_num) 1 rotateData_stepB (fun _ => Iff.rfl)]
  refine amp_rename_bound inputExponent (boundToLast (h := 2) 1 inputExponent) 1 ⊥ 0
    ((Equiv.swap (1 : Fin 3) 2).arrowCongr (Equiv.refl (ZMod 2))) (fun w y => ?_)
  obtain rfl : w = 0 := Subsingleton.elim _ _
  obtain ⟨a, b, d, rfl⟩ : ∃ a b d : ZMod 2, y = ![a, b, d] :=
    ⟨y 0, y 1, y 2, by funext i; fin_cases i <;> rfl⟩
  simp only [eval_boundToLast, inputExponent, DiagPhase.eval_add, DiagPhase.eval_mul,
    DiagPhase.eval_C, DiagPhase.eval_X]
  revert a b d
  decide

/-- Sequence A is maximal: no elimination step is available at either bound bit of its outcome. -/
theorem eliminationStuck_outcomeA :
    EliminationStuck (h := 1) outcomeA.Q outcomeA.L outcomeA.x₀ := by
  intro j
  fin_cases j
  · refine not_stepAvailable_of_parity ![1] ![0] ?_ ?_ <;>
    · dsimp only [outcomeA, elimRotate]
      simp only [lastDiff_eval, eval_boundToLast, snocFreeze_eval, inputExponent, lambdaA,
        DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      decide
  · refine not_stepAvailable_of_parity ![0] ![1] ?_ ?_ <;>
    · dsimp only [outcomeA, elimRotate]
      simp only [lastDiff_eval, eval_boundToLast, snocFreeze_eval, inputExponent, lambdaA,
        DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      decide

/-- Sequence B is maximal: no elimination step is available at either bound bit of its outcome. -/
theorem eliminationStuck_outcomeB :
    EliminationStuck (h := 1) outcomeB.Q outcomeB.L outcomeB.x₀ := by
  intro j
  fin_cases j
  · refine not_stepAvailable_of_parity ![0] ![1] ?_ ?_ <;>
    · dsimp only [outcomeB, elimRotate]
      simp only [lastDiff_eval, eval_boundToLast, snocFreeze_eval, inputExponent, eval_lambdaB,
        DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      decide
  · refine not_stepAvailable_of_parity ![1] ![0] ?_ ?_ <;>
    · dsimp only [outcomeB, elimRotate]
      simp only [lastDiff_eval, eval_boundToLast, snocFreeze_eval, inputExponent, eval_lambdaB,
        DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]
      decide

/-- The two outcomes have different term multisets at the one (empty) word. -/
theorem boundTerms_outcomeA_ne_outcomeB : boundTerms outcomeA ≠ boundTerms outcomeB := by
  change boundTerms (⟨2, 2, snocFreeze 0 (boundToLast (h := 2) 0 inputExponent)
      + MvPolynomial.C (-1) * lambdaA, 1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ), ⊥, 0⟩ :
      KernelSumState 0)
    ≠ boundTerms (⟨2, 2, snocFreeze 0 (boundToLast (h := 2) 1 inputExponent)
      + MvPolynomial.C (-1) * lambdaB, 1 * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ), ⊥, 0⟩ :
      KernelSumState 0)
  intro h
  have h0 := congrFun h 0
  rw [boundTerms_bot_zero, boundTerms_bot_zero] at h0
  -- The sums of the squared terms differ: `2·c²` against `−2·c²`, with `c ≠ 0`.
  have hsq := congrArg Multiset.sum (congrArg (Multiset.map fun z : ℂ => z ^ 2) h0)
  rw [Multiset.map_map, Multiset.map_map, ← Finset.sum_eq_multiset_sum,
    ← Finset.sum_eq_multiset_sum, sum_words_two, sum_words_two] at hsq
  simp only [Function.comp_apply] at hsq
  obtain ⟨a00, a01, a10, a11⟩ := eval_outcomeA_words
  obtain ⟨b00, b01, b10, b11⟩ := eval_outcomeB_words
  rw [a00, a01, a10, a11, b00, b01, b10, b11] at hsq
  generalize hc : (1 : ℂ) * (1 + charOf 2 1) / (Real.sqrt 2 : ℂ) = c at hsq
  rw [charOf_zero, charOf_two_one, charOf_two_two, charOf_two_three] at hsq
  have h4 : c ^ 2 * 4 = 0 := by linear_combination hsq + 2 * c ^ 2 * Complex.I_sq
  have hc0 : c = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h4).resolve_right (by norm_num))
  exact scale_ne_zero (hc.trans hc0)

/-- No chain of gauge rewrites relates the two outcomes. -/
theorem not_gaugeRel_outcomeA_outcomeB : ¬ GaugeRel outcomeA outcomeB :=
  fun h => boundTerms_outcomeA_ne_outcomeB (boundTerms_eq_of_gaugeRel h)

/-- **The elimination order matters.** From the carrier state `input`, the rotate steps at `y₀`
and at `y₁` are both available; each reaches a stuck carrier state of height two denoting the
input's state; and no chain of gauge rewrites R1–R7 relates the two outcomes. -/
theorem elimination_order_matters :
    IsCarrier input
      ∧ RotateData (boundToLast (h := 2) 0 inputExponent) ⊥ 0 1 lambdaA
      ∧ RotateData (boundToLast (h := 2) 1 inputExponent) ⊥ 0 1 lambdaB
      ∧ StateEq outcomeA input ∧ StateEq outcomeB input
      ∧ EliminationStuck (h := 1) outcomeA.Q outcomeA.L outcomeA.x₀
      ∧ EliminationStuck (h := 1) outcomeB.Q outcomeB.L outcomeB.x₀
      ∧ outcomeA.h = 2 ∧ outcomeB.h = 2
      ∧ ¬ GaugeRel outcomeA outcomeB :=
  ⟨isCarrier_input, rotateData_stepA, rotateData_stepB, stateEq_outcomeA_input,
    stateEq_outcomeB_input, eliminationStuck_outcomeA, eliminationStuck_outcomeB, rfl, rfl,
    not_gaugeRel_outcomeA_outcomeB⟩

end EliminationOrder

end FTQCLib.Frame.Walkthrough

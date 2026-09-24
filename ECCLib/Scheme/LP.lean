/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Positivity without a symmetry group (the translation-scheme LP inequality)

The analytic content of the Delsarte inequality, stated with NO symmetry group anywhere:
for a finite abelian group `V`, a subset `C`, and ANY finite set `S` of additive
characters,

  `Σ_v innerCount C v · qEnt S v = Σ_{χ∈S} ‖Σ_{x∈C} χ x‖² ≥ 0`

(`scheme_spectral`), where `qEnt S v = Σ_{χ∈S} χ v` is the dual class sum (conjugate-free,
matching `Delsarte.tupleChar`/`charShellSum`) and `innerCount C v` counts ordered pairs
of `C` with difference `v`. The group enters a translation scheme only to REGROUP this
sum into finitely many unknowns; the regrouping is exposed here through an arbitrary
class map `w : V → κ` (`class_delsarte_nonneg`), so any partition on which the class
sum is constant — orbits of a group, or Hamming weight shells via a generating function —
yields the LP inequality. The Hamming instantiation (`Scheme/DelsarteBridge.lean`)
recovers the library's `Delsarte.delsarte_nonneg` verbatim.

Conventions: dual sums carry no conjugate; the `x ↦ χ(p.2 − p.1)` split is
`conj(χ p.1) · χ p.2`. References: Delsarte 1973 Thm 3.3/(3.8), Martin–Tanaka 2009 §5/§7.
-/

namespace ECCLib.Scheme

open Finset
open scoped BigOperators ComplexConjugate

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The dual class sum of a finite set of characters at a point (conjugate-free). -/
noncomputable def qEnt (S : Finset (AddChar V ℂ)) (v : V) : ℂ := ∑ χ ∈ S, χ v

/-- The code character sum `Σ_{x∈C} χ x`. -/
noncomputable def codeSum (C : Finset V) (χ : AddChar V ℂ) : ℂ := ∑ x ∈ C, χ x

/-- The (unnormalised) inner distribution: ordered pairs of `C` with difference `v`. -/
def innerCount (C : Finset V) (v : V) : ℕ :=
  ((C ×ˢ C).filter fun p => p.2 - p.1 = v).card

/-- The inner distribution regrouped by an arbitrary class map `w : V → κ`. -/
def classCount {κ : Type*} [DecidableEq κ] (C : Finset V) (w : V → κ) (c : κ) : ℕ :=
  ((C ×ˢ C).filter fun p => w (p.2 - p.1) = c).card

omit [Fintype V] [DecidableEq V] in
/-- `χ(y − x) = χ y · conj(χ x)` — the split every identity below rests on (finiteness is
genuinely needed: characters of an infinite group need not be unimodular). -/
theorem char_sub [Finite V] (χ : AddChar V ℂ) (x y : V) :
    χ (y - x) = χ y * conj (χ x) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

/-- Summing a function of the difference against the inner distribution is summing it
over ordered pairs. -/
theorem sum_innerCount_mul {M : Type*} [NonAssocSemiring M] (C : Finset V) (f : V → M) :
    ∑ v : V, (innerCount C v : M) * f v = ∑ p ∈ C ×ˢ C, f (p.2 - p.1) := by
  rw [← Finset.sum_fiberwise' (C ×ˢ C) (fun p : V × V => p.2 - p.1) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

omit [Fintype V] [DecidableEq V] in
/-- The class-map version of `sum_innerCount_mul`. -/
theorem sum_classCount_mul {κ : Type*} [DecidableEq κ] {M : Type*} [NonAssocSemiring M]
    (C : Finset V) (w : V → κ) (K : Finset κ) (hw : ∀ v : V, w v ∈ K) (g : κ → M) :
    ∑ c ∈ K, (classCount C w c : M) * g c = ∑ p ∈ C ×ˢ C, g (w (p.2 - p.1)) := by
  rw [← Finset.sum_fiberwise_of_maps_to'
    (g := fun p : V × V => w (p.2 - p.1)) (t := K) (fun p _ => hw _) g]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

omit [Fintype V] in
/-- The inner distribution is the class count of the identity class map. -/
theorem innerCount_eq_classCount (C : Finset V) (v : V) :
    innerCount C v = classCount C id v := rfl

omit [Fintype V] [DecidableEq V] in
/-- **The spectral identity (H-free), ordered-pair form.** Against the ordered pairs of `C`,
the dual class sum of ANY finite character set `S` sums to `Σ_{χ∈S} ‖codeSum C χ‖²`. -/
theorem sum_pair_qEnt [Finite V] (C : Finset V) (S : Finset (AddChar V ℂ)) :
    ∑ p ∈ C ×ˢ C, qEnt S (p.2 - p.1)
      = ∑ χ ∈ S, ((Complex.normSq (codeSum C χ) : ℝ) : ℂ) := by
  simp only [qEnt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hsplit : ∀ p : V × V, χ (p.2 - p.1) = conj (χ p.1) * χ p.2 := by
    intro p
    rw [char_sub]
    ring
  rw [Finset.sum_congr rfl fun p _ => hsplit p,
    Finset.sum_product' (s := C) (t := C) (f := fun x y => conj (χ x) * χ y),
    ← Finset.sum_mul_sum, ← map_sum]
  rw [show (∑ x ∈ C, χ x) = codeSum C χ from rfl, mul_comm, Complex.mul_conj]

/-- **The spectral identity (H-free), inner-distribution form.** -/
theorem scheme_spectral (C : Finset V) (S : Finset (AddChar V ℂ)) :
    ∑ v : V, (innerCount C v : ℂ) * qEnt S v
      = ∑ χ ∈ S, ((Complex.normSq (codeSum C χ) : ℝ) : ℂ) := by
  rw [sum_innerCount_mul C (qEnt S)]
  exact sum_pair_qEnt C S

/-- **The LP inequality, ℤ-valued, pointwise form:** if an integer function `g` realises
the dual class sum of `S`, its pairing with the inner distribution is nonnegative. -/
theorem scheme_nonneg_int (C : Finset V) (S : Finset (AddChar V ℂ)) (g : V → ℤ)
    (hg : ∀ v, ((g v : ℤ) : ℂ) = qEnt S v) :
    0 ≤ ∑ v : V, (innerCount C v : ℤ) * g v := by
  have h := scheme_spectral C S
  rw [← Complex.ofReal_sum] at h
  have hL : ∑ v : V, (innerCount C v : ℂ) * qEnt S v
      = (((∑ v : V, (innerCount C v : ℤ) * g v : ℤ) : ℤ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun v _ => by rw [hg v]
  rw [hL] at h
  have hr : ((∑ v : V, (innerCount C v : ℤ) * g v : ℤ) : ℝ)
      = ∑ χ ∈ S, Complex.normSq (codeSum C χ) := by exact_mod_cast h
  have hnn : (0 : ℝ) ≤ ∑ χ ∈ S, Complex.normSq (codeSum C χ) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [← hr] at hnn
  exact_mod_cast hnn

omit [Fintype V] [DecidableEq V] in
/-- **The LP inequality through an arbitrary class map (the consumer form).** `w`
classifies differences, `K` contains every class, and `g` evaluates the dual class sum
of `S` on classes; the conclusion is the nonnegativity an LP layer consumes. The Hamming
bridge instantiates this with `w = hammingNorm`, `g = kraw`, `hg = charShellSum`. -/
theorem class_delsarte_nonneg [Finite V] {κ : Type*} [DecidableEq κ]
    (C : Finset V) (w : V → κ) (K : Finset κ) (hw : ∀ v : V, w v ∈ K)
    (S : Finset (AddChar V ℂ)) (g : κ → ℤ)
    (hg : ∀ v : V, qEnt S v = ((g (w v) : ℤ) : ℂ)) :
    0 ≤ ∑ c ∈ K, (classCount C w c : ℤ) * g c := by
  have hreg : ∑ c ∈ K, (classCount C w c : ℤ) * g c
      = ∑ p ∈ C ×ˢ C, g (w (p.2 - p.1)) := sum_classCount_mul C w K hw g
  have hC : ((∑ c ∈ K, (classCount C w c : ℤ) * g c : ℤ) : ℂ)
      = ∑ χ ∈ S, ((Complex.normSq (codeSum C χ) : ℝ) : ℂ) := by
    rw [hreg, ← sum_pair_qEnt C S]
    push_cast
    exact Finset.sum_congr rfl fun p _ => (hg (p.2 - p.1)).symm
  rw [← Complex.ofReal_sum] at hC
  have hR : ((∑ c ∈ K, (classCount C w c : ℤ) * g c : ℤ) : ℝ)
      = ∑ χ ∈ S, Complex.normSq (codeSum C χ) := by exact_mod_cast hC
  have hnn : (0 : ℝ) ≤ ∑ χ ∈ S, Complex.normSq (codeSum C χ) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  rw [← hR] at hnn
  exact_mod_cast hnn

omit [Fintype V] [DecidableEq V] in
/-- The real-valued mirror of `class_delsarte_nonneg`. -/
theorem class_delsarte_nonneg_real [Finite V] {κ : Type*} [DecidableEq κ]
    (C : Finset V) (w : V → κ) (K : Finset κ) (hw : ∀ v : V, w v ∈ K)
    (S : Finset (AddChar V ℂ)) (g : κ → ℝ)
    (hg : ∀ v : V, qEnt S v = ((g (w v) : ℝ) : ℂ)) :
    0 ≤ ∑ c ∈ K, (classCount C w c : ℝ) * g c := by
  have hreg : ∑ c ∈ K, (classCount C w c : ℝ) * g c
      = ∑ p ∈ C ×ˢ C, g (w (p.2 - p.1)) := sum_classCount_mul C w K hw g
  have hC : ((∑ c ∈ K, (classCount C w c : ℝ) * g c : ℝ) : ℂ)
      = ∑ χ ∈ S, ((Complex.normSq (codeSum C χ) : ℝ) : ℂ) := by
    rw [hreg, ← sum_pair_qEnt C S]
    push_cast
    exact Finset.sum_congr rfl fun p _ => (hg (p.2 - p.1)).symm
  rw [← Complex.ofReal_sum] at hC
  have hR : (∑ c ∈ K, (classCount C w c : ℝ) * g c : ℝ)
      = ∑ χ ∈ S, Complex.normSq (codeSum C χ) := by exact_mod_cast hC
  rw [hR]
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end ECCLib.Scheme

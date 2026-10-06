/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.EliminationOrder
import FTQCLib.Carrier.FinAppend
import Mathlib.GroupTheory.Perm.ClosureSwap

/-!
# The rules on carrier states

One relation, `CarrierRule`, collects every rule the completeness argument of T07 uses
(`docs/TARGETS.md`, T06). A carrier state `⟨m, h, Q, c, L, x₀⟩` denotes, at a free word `w` of its
support, `(c/√2^h)·Σ_y ζ^{Q(w, y)}` with `ζ` the primitive `2^m`-th root (`amp`). The rules are:

* **the gauge rewrites** R1 to R7, one constructor carrying `GaugeStep` (`EliminationOrder.lean`);
* **collapse** and **rotate**, the two eliminations of the last bound bit, with the shapes
  `SignAffine` and `RotateData` of `BoundElimination.lean`;
* **antipodal rephasing** (R8): on one set `P` of bound words, the same at every free word, on which
  a permutation pairs every phase with the phase `2^{m−1}` above it, the exponent may be changed to any
  other exponent paired the same way, since the paths on `P` sum to zero either way;
* **antipodal halving** (R9): when that set `P` is the complement of the image of an embedding of the
  words one bit shorter, the paths on `P` are deleted, the carrier state loses a bound bit and its
  scale is divided by `√2`;
* **the copy gadget**: two bound bits `z, t` carrying the constraint term `2^{m−1}·t·(z ⊕ P)`, where
  the bit `P` may read the free word and the other bound bits, are removed with `P` substituted for
  `z`. Read from left to right this is Vilmart's rule (HH) with the substituted variable bound.

Every side condition is an identity between values of the exponent, tested cell by cell (at a free
word of the support and a bound word), and never a condition on a sum over bound words: the sums are
what the rules certify, not what they assume.

Each step keeps the amplitude (`stateEq_of_carrierRule`) and multiplies the scale by a dyadic factor
(`exists_isDyadicRatio_of_carrierRule`), a root of unity of order a power of two times a power of
`√2` (decision D9, `docs/TARGETS.md`).

**The per-row relabelling.** R5 relabels the bound words by one bijection, the same for every free
word, and so do R8 and R9 with their one pairing. A relabelling with one bijection for each free word
is not a rule, and no rule that treats every row alike makes it (`HHWitness.hh_witness`,
`FTQCLib/Explore/CyclotomicKernelB.lean`). It is derivable: the copy gadget used twice, with an R5
between, flips a bound bit by any function of the free word and the other bound bits
(`flip_derivable`), and those flips generate every relabelling (`relabel_derivable`). Both are
stated for chains that never leave the endpoints' precision and Lagrangian and every carrier state
of which denotes the endpoints' state (`CarrierRuleWithin`), so that the conservativity of T07, a
chain between carrier states at one precision, can use them.

Everything here is frame-pure: `DiagPhase`, `Pauli`, `Submodule`, `ℂ`. No `FTQCLib.Hilbert` module
is imported, and nothing from `FTQCLib/Explore/`: the exploratory rules there (`AntipodalStep`,
`HalvingStep`, `amp_copy`) are restated here under this namespace, not moved.

## Main definitions

* `AntipodalOn` — at one free word, a set of bound words paired antipodally by a permutation.
* `CarrierRule` — the rules: gauge rewrites, collapse, rotate, rephasing, halving, the copy gadget.
* `IsDyadicRatio` — a root of unity of order a power of two times an integer power of `√2`.
* `CarrierRuleWithin` — `CarrierRule` restricted to steps whose two carrier states satisfy a
  predicate.

## Main results

* `stateEq_of_carrierRule` — each step keeps the amplitude.
* `exists_isDyadicRatio_of_carrierRule` — each step multiplies the scale by a dyadic factor.
* `isDyadicRatio_one`, `IsDyadicRatio.mul`, `IsDyadicRatio.inv`, `IsDyadicRatio.ne_zero`,
  `isDyadicRatio_sqrt_two_zpow`, `not_isDyadicRatio_two_fifths` — the dyadic ratios form a group
  holding every power of `√2` and not `2/5`; one copy for every module (docs/STEPS.md, entry
  2026-10-01n).
* `sq_norm_eq_zpow_of_isDyadicRatio`, `nine_div_two_ne_zpow`, `exists_isDyadicRatio_of_eqvGen` — a
  dyadic ratio's squared norm is a power of two, `9/2` is not one (decision D9's gap), and a chain of
  steps multiplies the scale by a dyadic ratio; moved here from the check modules (entry
  2026-10-02c).
* `flip_derivable` — a bound bit flipped by any function of the free word and the other bound bits.
* `relabel_derivable` — every per-row relabelling of the bound words.

## Implementation notes

* The directions follow the existing rules: a gauge rewrite as `GaugeStep` writes it, an elimination
  and a halving from the higher carrier state to the lower, the copy gadget from the carrier state
  that carries `z, t` to the one with `P` substituted. The equivalence the rules generate is
  `Relation.EqvGen CarrierRule`.
* The eliminations and the copy gadget act on the last bound bits; at another bit they are these
  after an instance of R5.
* The eliminations, rephasing, halving and the copy gadget carry `1 ≤ m`, as their certificates do.
  At `m = 0` the top bit `2^{m−1}` is `1 = 0` in `ZMod 1`, and collapse, halving and the copy gadget
  would change the amplitude; rotate and rephasing would not, and keep the hypothesis because their
  certificates carry it. It costs nothing on carrier states, which have `1 ≤ m` (`IsCarrier`).
  `flip_derivable` and `relabel_derivable` carry no hypothesis on `m`: at `m = 0` every exponent
  takes one value and R4 relates the two carrier states.
* Every side condition is quantified over the free words of the support coset only, the weakest
  form under which the certificate holds, since the amplitude is zero off the coset.

## References

* R. Vilmart, *Completeness of Sum-Over-Paths for Toffoli-Hadamard and the Dyadic Fragments of
  Quantum Computation*, arXiv:2205.02600: the rule (HH).
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## Antipodal pairing -/

/-- At the free word `w`, the bound words `P` are paired antipodally by `τ`: `τ` maps `P` onto
itself, and moves the exponent's value at each word of `P` by the top bit `2^{m−1}`. A condition on
values of the exponent, word by word; the pairing need not be an involution. -/
def AntipodalOn {m h : ℕ} (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2)
    (P : Finset (Fin h → ZMod 2)) (τ : Equiv.Perm (Fin h → ZMod 2)) : Prop :=
  (∀ y, y ∈ P ↔ τ y ∈ P) ∧
    ∀ y ∈ P, Q.eval (Fin.append w (τ y)) = Q.eval (Fin.append w y) + (2 : ZMod (2 ^ m)) ^ (m - 1)

/-! ## Local restatements

The exploratory rules of `FTQCLib/Explore/CyclotomicKernel.lean` and `FTQCLib/Explore/SquierModel.lean`
are restated here, under this namespace, rather than moved: this module imports nothing from
`FTQCLib/Explore/`. -/

section Restatements

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-- **Antipodal paths cancel.** Paths paired antipodally contribute nothing to the character sum;
the pairing is any permutation of `P`, not necessarily an involution. -/
private theorem sum_charOf_eq_zero_of_antipodalOn {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + h) m}
    {w : Fin n → ZMod 2} {P : Finset (Fin h → ZMod 2)} {τ : Equiv.Perm (Fin h → ZMod 2)}
    (hP : AntipodalOn Q w P τ) :
    ∑ y ∈ P, charOf m (Q.eval (Fin.append w y)) = 0 := by
  have hperm : ∑ y ∈ P, charOf m (Q.eval (Fin.append w (τ y)))
      = ∑ y ∈ P, charOf m (Q.eval (Fin.append w y)) :=
    Finset.sum_equiv τ hP.1 (fun _ _ => rfl)
  have hneg : ∑ y ∈ P, charOf m (Q.eval (Fin.append w (τ y)))
      = -∑ y ∈ P, charOf m (Q.eval (Fin.append w y)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [hP.2 y hy, charOf_add, charOf_two_pow_pred hm]
    ring
  rw [hperm] at hneg
  exact self_eq_neg.mp hneg

/-- **The rephasing certificate, per word.** -/
private theorem ampCore_eq_of_antipodalOn {m h : ℕ} (hm : 1 ≤ m) {Q Q' : DiagPhase (n + h) m}
    (c : ℂ) {w : Fin n → ZMod 2} {P : Finset (Fin h → ZMod 2)} {τ τ' : Equiv.Perm (Fin h → ZMod 2)}
    (hoff : ∀ y ∉ P, Q'.eval (Fin.append w y) = Q.eval (Fin.append w y))
    (hQ : AntipodalOn Q w P τ) (hQ' : AntipodalOn Q' w P τ') :
    ampCore m h Q' c w = ampCore m h Q c w := by
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf]
  congr 1
  rw [← Finset.sum_add_sum_compl P, ← Finset.sum_add_sum_compl P (fun y => charOf m _),
    sum_charOf_eq_zero_of_antipodalOn hm hQ, sum_charOf_eq_zero_of_antipodalOn hm hQ']
  congr 1
  exact Finset.sum_congr rfl (fun y hy => by rw [hoff y (Finset.mem_compl.mp hy)])

/-- **The halving certificate, per word.** -/
private theorem ampCore_halve {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + (h + 1)) m}
    {Q' : DiagPhase (n + h) m} (c : ℂ) {w : Fin n → ZMod 2}
    (e : (Fin h → ZMod 2) ↪ (Fin (h + 1) → ZMod 2)) {P : Finset (Fin (h + 1) → ZMod 2)}
    {τ : Equiv.Perm (Fin (h + 1) → ZMod 2)}
    (hP : ∀ y', y' ∈ P ↔ ∀ y, e y ≠ y')
    (hQ' : ∀ y, Q'.eval (Fin.append w y) = Q.eval (Fin.append w (e y)))
    (hpair : AntipodalOn Q w P τ) :
    ampCore m h Q' (c / (Real.sqrt 2 : ℂ)) w = ampCore m (h + 1) Q c w := by
  have hcompl : Pᶜ = Finset.univ.map e := by
    ext y'
    rw [Finset.mem_compl, hP, Finset.mem_map]
    simp only [Finset.mem_univ, true_and, not_forall, not_not]
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf, ← Finset.sum_add_sum_compl P,
    sum_charOf_eq_zero_of_antipodalOn hm hpair, zero_add, hcompl, Finset.sum_map]
  simp only [hQ']
  rw [pow_succ, div_div, mul_comm ((Real.sqrt 2 : ℂ) ^ h)]

/-- Summing the constraint bit `t` of the term `2^{m−1}·t·s` gives `2` where `s = 0` and `0` where
`s = 1`. -/
private theorem sum_charOf_constraint {m : ℕ} (hm : 1 ≤ m) (s : ZMod 2) :
    ∑ t : ZMod 2, charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * s).val : ℕ) : ZMod (2 ^ m)))
      = if s = 0 then 2 else 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, charOf_two_pow_mul hm,
    charOf_two_pow_mul hm]
  rcases zmod_two_dichotomy s with rfl | rfl
  · rw [if_pos rfl, show ((0 : ZMod 2) * 0).val = 0 from rfl,
      show ((1 : ZMod 2) * 0).val = 0 from rfl]
    norm_num
  · rw [if_neg (by decide), show ((0 : ZMod 2) * 1).val = 0 from rfl,
      show ((1 : ZMod 2) * 1).val = 1 from rfl]
    norm_num

end Restatements

/-! ## The rules -/

-- source: papers/tensor_network_simulation/
-- Vilmart_2023_sop_toffoli_hadamard_dyadic_complete_2205.02600 equation:h939465430480
/-- The rules on carrier states. Each constructor carries the hypotheses of the certificate that
proves it sound; every hypothesis on the exponent is an identity between its values at a free word of
the support and a bound word. The `copy` constructor is Vilmart's rule (HH) with the substituted
variable bound. -/
inductive CarrierRule : KernelSumState n → KernelSumState n → Prop
  /-- A gauge rewrite, R1 to R7. -/
  | gauge {S T : KernelSumState n} (hST : GaugeStep S T) : CarrierRule S T
  /-- **Collapse** (`amp_elimCollapse`): along the last bound bit the difference of the exponent is
  the top bit times the affine bit `ε + ⟨σ, w⟩` of the free word; the bit is dropped, the support is
  cut by `ε + ⟨σ, w⟩ = 0`, the scale gains `√2`. -/
  | collapse {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + h + 1) m) (c : ℂ)
      (L : Submodule (ZMod 2) (Pauli n)) (x₀ σ : Fin n → ZMod 2) (ε : ZMod 2)
      (hsign : SignAffine Q L x₀ σ ε) (L'' : Submodule (ZMod 2) (Pauli n)) (x₀'' : Fin n → ZMod 2)
      (hsupp : ∀ w : Fin n → ZMod 2,
        (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X) ∧ ε + dotF2 σ w = 0) :
      CarrierRule ⟨m, h + 1, Q, c, L, x₀⟩ (elimCollapse Q c L'' x₀'')
  /-- **Rotate** (`amp_elimRotate`): along the last bound bit the difference of the exponent is
  `a + 2^{m−1}·Λ` with `2a = 2^{m−1}` and `Λ` a bit; the bit is dropped, the exponent gains `−a·Λ`,
  the scale gains `(1 + ζ^a)/√2`. -/
  | rotate {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + h + 1) m) (c : ℂ)
      (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) (a : ZMod (2 ^ m))
      (Λ : DiagPhase (n + h) m) (hrot : RotateData Q L x₀ a Λ)
      (L'' : Submodule (ZMod 2) (Pauli n)) (x₀'' : Fin n → ZMod 2)
      (hsupp : ∀ w : Fin n → ZMod 2, (∃ p ∈ L'', w = x₀'' + p.X) ↔ (∃ p ∈ L, w = x₀ + p.X)) :
      CarrierRule ⟨m, h + 1, Q, c, L, x₀⟩ (elimRotate Q a Λ c L'' x₀'')
  /-- **Antipodal rephasing** (R8): one set `P` of bound words, the same at every free word, on
  which both exponents are paired antipodally, and off which they agree on the support. -/
  | rephase {m h : ℕ} (hm : 1 ≤ m) (Q Q' : DiagPhase (n + h) m) (c : ℂ)
      (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) (P : Finset (Fin h → ZMod 2))
      (τ τ' : Equiv.Perm (Fin h → ZMod 2))
      (hoff : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y ∉ P,
        Q'.eval (Fin.append w y) = Q.eval (Fin.append w y))
      (hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q w P τ)
      (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q' w P τ') :
      CarrierRule ⟨m, h, Q, c, L, x₀⟩ ⟨m, h, Q', c, L, x₀⟩
  /-- **Antipodal halving** (R9): one embedding `e` of the words one bit shorter and one pairing `τ`
  of the rest `P`, the same at every free word; the halved exponent reads `Q` through `e` on the
  support, and the scale is divided by `√2`. -/
  | halve {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + (h + 1)) m) (Q' : DiagPhase (n + h) m)
      (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
      (e : (Fin h → ZMod 2) ↪ (Fin (h + 1) → ZMod 2)) (P : Finset (Fin (h + 1) → ZMod 2))
      (τ : Equiv.Perm (Fin (h + 1) → ZMod 2)) (hP : ∀ y', y' ∈ P ↔ ∀ y, e y ≠ y')
      (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y,
        Q'.eval (Fin.append w y) = Q.eval (Fin.append w (e y)))
      (hpair : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → AntipodalOn Q w P τ) :
      CarrierRule ⟨m, h + 1, Q, c, L, x₀⟩ ⟨m, h, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩
  /-- **The copy gadget**, Vilmart's (HH) with the substituted variable bound. The last two bound
  bits `z, t` carry the constraint term `2^{m−1}·t·(z ⊕ P)`, where the bit `P w y` reads the free
  word `w` and the other bound bits `y`; they are removed with `P` substituted for `z`. The scale,
  the Lagrangian and the offset are unchanged. -/
  | copy {m h : ℕ} (hm : 1 ≤ m) (Q : DiagPhase (n + (h + 1 + 1)) m) (Q' : DiagPhase (n + h) m)
      (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
      (P : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod 2)
      (hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) →
        ∀ (y : Fin h → ZMod 2) (z t : ZMod 2),
          Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t))
            = Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0))
              + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + P w y)).val : ℕ) : ZMod (2 ^ m)))
      (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
        Q'.eval (Fin.append w y) = Q.eval (Fin.append w (Fin.snoc (Fin.snoc y (P w y)) 0))) :
      CarrierRule ⟨m, h + 1 + 1, Q, c, L, x₀⟩ ⟨m, h, Q', c, L, x₀⟩

/-- **The copy gadget, per word (soundness).** -/
private theorem ampCore_copy_supp {m h : ℕ} (hm : 1 ≤ m) {Q : DiagPhase (n + (h + 1 + 1)) m}
    {Q' : DiagPhase (n + h) m} {c : ℂ}
    {P : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod 2} {w : Fin n → ZMod 2}
    (hQ : ∀ (y : Fin h → ZMod 2) (z t : ZMod 2),
      Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t))
        = Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0))
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + P w y)).val : ℕ) : ZMod (2 ^ m)))
    (hQ' : ∀ y : Fin h → ZMod 2,
      Q'.eval (Fin.append w y) = Q.eval (Fin.append w (Fin.snoc (Fin.snoc y (P w y)) 0))) :
    ampCore m (h + 1 + 1) Q c w = ampCore m h Q' c w := by
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf]
  have hsplit : ∀ f : (Fin (h + 1 + 1) → ZMod 2) → ℂ,
      ∑ y'' : Fin (h + 1 + 1) → ZMod 2, f y''
        = ∑ y : Fin h → ZMod 2, ∑ z : ZMod 2, ∑ t : ZMod 2, f (Fin.snoc (Fin.snoc y z) t) := by
    intro f
    rw [sum_snoc_peel, Finset.sum_comm,
      sum_snoc_peel (fun y' : Fin (h + 1) → ZMod 2 => ∑ t : ZMod 2, f (Fin.snoc y' t)),
      Finset.sum_comm]
  rw [hsplit]
  have hword : ∀ y : Fin h → ZMod 2,
      ∑ z : ZMod 2, ∑ t : ZMod 2,
          charOf m (Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t)))
        = 2 * charOf m (Q'.eval (Fin.append w y)) := by
    intro y
    have hterm : ∀ z t : ZMod 2,
        charOf m (Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t)))
          = charOf m (Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0)))
            * charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)
                * (((t * (z + P w y)).val : ℕ) : ZMod (2 ^ m))) := by
      intro z t
      rw [hQ y z t, charOf_add]
    have hoff : ∀ z : ZMod 2, z ≠ P w y →
        charOf m (Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0)))
          * (if z + P w y = 0 then (2 : ℂ) else 0) = 0 := by
      intro z hne
      have hsum : z + P w y ≠ 0 := fun h0 =>
        hne (sub_eq_zero.mp (by rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]; exact h0))
      rw [if_neg hsum, mul_zero]
    have hself : P w y + P w y = 0 := by
      rcases zmod_two_dichotomy (P w y) with h0 | h0 <;> rw [h0] <;> decide
    have hzt : ∀ z : ZMod 2,
        ∑ t : ZMod 2, charOf m (Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t)))
          = charOf m (Q.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0)))
            * (if z + P w y = 0 then (2 : ℂ) else 0) := by
      intro z
      rw [Finset.sum_congr rfl (fun t _ => hterm z t), ← Finset.mul_sum, sum_charOf_constraint hm]
    rw [Finset.sum_congr rfl (fun z _ => hzt z), Fintype.sum_eq_single (P w y) hoff, if_pos hself,
      hQ']
    ring
  rw [Finset.sum_congr rfl (fun y _ => hword y), ← Finset.mul_sum]
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := sqrt_two_mul_self
  have hscale : c / (Real.sqrt 2 : ℂ) ^ (h + 1 + 1) * 2 = c / (Real.sqrt 2 : ℂ) ^ h := by
    rw [pow_succ, pow_succ, mul_assoc, hsq]
    field_simp
  rw [← mul_assoc, hscale]

/-- **Soundness.** Each step of `CarrierRule` keeps the amplitude. -/
theorem stateEq_of_carrierRule {S T : KernelSumState n} (hST : CarrierRule S T) : StateEq S T := by
  cases hST with
  | gauge hST => exact stateEq_of_gaugeStep hST
  | collapse hm Q c L x₀ σ ε hsign L'' x₀'' hsupp =>
    exact (amp_elimCollapse hm c hsign hsupp).symm
  | rotate hm Q c L x₀ a Λ hrot L'' x₀'' hsupp =>
    exact (amp_elimRotate hm c hrot hsupp).symm
  | @rephase m h hm Q Q' c L x₀ P τ τ' hoff hQ hQ' =>
    funext w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · rw [amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_pos (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw]
      exact ampCore_eq_of_antipodalOn hm c (fun y hy => (hoff w hw y hy).symm) (hQ' w hw) (hQ w hw)
    · rw [amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_neg (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw]
  | @halve m h hm Q Q' c L x₀ e P τ hP hQ' hpair =>
    funext w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · rw [amp_pos (S := (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_pos (S := (⟨m, h, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n)) hw]
      exact (ampCore_halve hm c e hP (hQ' w hw) (hpair w hw)).symm
    · rw [amp_neg (S := (⟨m, h + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_neg (S := (⟨m, h, Q', c / (Real.sqrt 2 : ℂ), L, x₀⟩ : KernelSumState n)) hw]
  | @copy m h hm Q Q' c L x₀ P hQ hQ' =>
    funext w
    by_cases hw : ∃ p ∈ L, w = x₀ + p.X
    · rw [amp_pos (S := (⟨m, h + 1 + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_pos (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw]
      exact ampCore_copy_supp hm (hQ w hw) (hQ' w hw)
    · rw [amp_neg (S := (⟨m, h + 1 + 1, Q, c, L, x₀⟩ : KernelSumState n)) hw,
        amp_neg (S := (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n)) hw]

/-! ## The scale -/

/-- A dyadic ratio (decision D9): a root of unity of order a power of two times an integer power of
`√2`. -/
def IsDyadicRatio (r : ℂ) : Prop :=
  ∃ (ζ : ℂ) (k : ℕ) (e : ℤ), ζ ^ 2 ^ k = 1 ∧ r = ζ * (Real.sqrt 2 : ℂ) ^ e

/-- `1` is a dyadic ratio. -/
theorem isDyadicRatio_one : IsDyadicRatio 1 :=
  ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩

/-- Every integer power of `√2` is a dyadic ratio. -/
theorem isDyadicRatio_sqrt_two_zpow (e : ℤ) : IsDyadicRatio ((Real.sqrt 2 : ℂ) ^ e) :=
  ⟨1, 0, e, by norm_num, by rw [one_mul]⟩

/-- A dyadic ratio is nonzero. -/
theorem IsDyadicRatio.ne_zero {r : ℂ} (hr : IsDyadicRatio r) : r ≠ 0 := by
  obtain ⟨ζ, k, e, hζ, rfl⟩ := hr
  refine mul_ne_zero ?_ (zpow_ne_zero _ ofReal_sqrt_two_ne_zero)
  rintro rfl
  rw [zero_pow (pow_ne_zero _ two_ne_zero)] at hζ
  exact zero_ne_one hζ

/-- Dyadic ratios are closed under products. -/
theorem IsDyadicRatio.mul {r s : ℂ} (hr : IsDyadicRatio r) (hs : IsDyadicRatio s) :
    IsDyadicRatio (r * s) := by
  obtain ⟨ζ, k, e, hζ, rfl⟩ := hr
  obtain ⟨ξ, l, f, hξ, rfl⟩ := hs
  refine ⟨ζ * ξ, k + l, e + f, ?_, ?_⟩
  · have h1 : ζ ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, hζ, one_pow]
    have h2 : ξ ^ 2 ^ (k + l) = 1 := by rw [pow_add, mul_comm, pow_mul, hξ, one_pow]
    rw [mul_pow, h1, h2, one_mul]
  · rw [zpow_add₀ ofReal_sqrt_two_ne_zero]
    ring

/-- Dyadic ratios are closed under inverses. -/
theorem IsDyadicRatio.inv {r : ℂ} (hr : IsDyadicRatio r) : IsDyadicRatio r⁻¹ := by
  obtain ⟨ζ, k, e, hζ, rfl⟩ := hr
  exact ⟨ζ⁻¹, k, -e, by rw [inv_pow, hζ, inv_one], by rw [mul_inv, zpow_neg]⟩

/-- `2/5` is not a dyadic ratio: its square `4/25` is no integer power of `2`. -/
theorem not_isDyadicRatio_two_fifths : ¬ IsDyadicRatio (2 / 5 : ℂ) := by
  rintro ⟨ζ, k, e, hζ, hr⟩
  have hζ1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (pow_ne_zero _ two_ne_zero)
  have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) hr
  simp only [norm_mul, hζ1, one_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)] at hn
  have hp : (Real.sqrt 2 ^ e) ^ 2 = (2 : ℝ) ^ e := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      Real.sq_sqrt (by norm_num)]
  rw [hp] at hn
  have h25 : ‖(2 / 5 : ℂ)‖ = 2 / 5 := by
    rw [norm_div]
    norm_num
  rw [h25] at hn
  rcases e with a | a
  · have h1 : (1 : ℝ) ≤ 2 ^ (Int.ofNat a) := one_le_zpow₀ (by norm_num) (by simp)
    rw [← hn] at h1
    norm_num at h1
  · rw [zpow_negSucc] at hn
    have h2 : (4 : ℝ) * 2 ^ (a + 1) = 25 := by
      field_simp at hn
      linarith
    have h3 : (4 : ℕ) * 2 ^ (a + 1) = 25 := by exact_mod_cast h2
    omega

/-- Every dyadic ratio has `‖r‖² = 2^e` for the same integer `e`. -/
theorem sq_norm_eq_zpow_of_isDyadicRatio {r : ℂ} (h : IsDyadicRatio r) :
    ∃ e : ℤ, ‖r‖ ^ 2 = (2 : ℝ) ^ e := by
  obtain ⟨ζ, k, e, hζ, hr⟩ := h
  refine ⟨e, ?_⟩
  have hζ1 : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (pow_ne_zero _ two_ne_zero)
  have hnorm : ‖r‖ = (Real.sqrt 2) ^ e := by
    rw [hr, norm_mul, hζ1, one_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hnorm, sq_zpow_sqrt_two]

/-- `9/2` is not an integer power of two (decision D9's gap: `‖3/√2‖² = 9/2`). -/
theorem nine_div_two_ne_zpow (k : ℤ) : (9 / 2 : ℝ) ≠ (2 : ℝ) ^ k := by
  intro hk
  have h9 : (9 : ℝ) = (2 : ℝ) ^ (k + 1) := by
    rw [zpow_add_one₀ two_ne_zero, ← hk]
    norm_num
  rcases Int.eq_nat_or_neg (k + 1) with ⟨t, ht | ht⟩
  · rw [ht, zpow_natCast] at h9
    have h9' : (9 : ℕ) = 2 ^ t := by exact_mod_cast h9
    rcases t with _ | t
    · norm_num at h9'
    · rw [pow_succ] at h9'
      omega
  · rw [ht, zpow_neg, zpow_natCast] at h9
    have hle : ((2 : ℝ) ^ t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    linarith

/-- **The scale of a step.** Each step of `CarrierRule` multiplies the scale by a dyadic factor:
`1` for R2 to R7, rephasing and the copy gadget, a `2^m`-th root of unity for R1, `√2` for collapse,
an eighth root of unity for rotate, `1/√2` for halving. -/
theorem exists_isDyadicRatio_of_carrierRule {S T : KernelSumState n} (hST : CarrierRule S T) :
    ∃ r : ℂ, IsDyadicRatio r ∧ T.c = r * S.c := by
  cases hST with
  | @gauge S T hST =>
    cases hST with
    | @addC m h Q a c L x₀ =>
      refine ⟨charOf m a, ⟨charOf m a, m, 0, ?_, by rw [zpow_zero, mul_one]⟩, by rw [mul_comm]⟩
      rw [charOf_eq_zeta_pow, ← pow_mul, mul_comm, pow_mul,
        (isPrimitiveRoot_zeta m).pow_eq_one, one_pow]
    | offsetAddMem Q c L x₀ hv =>
      exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩
    | congrXProj Q c L L' x₀ hsh =>
      exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩
    | congrSupport Q Q' c L x₀ hQ =>
      exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩
    | renameBound Q Q' c L x₀ σ hQ =>
      exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩
    | hRaiseIndep i u u' S horth hui hrep hui' hrep' hm =>
      refine ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, ?_⟩
      change S.c / (Real.sqrt 2 : ℂ) = 1 * (S.c / (Real.sqrt 2 : ℂ))
      ring
    | liftTo k hmk Q c L x₀ =>
      exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩
  | collapse hm Q c L x₀ σ ε hsign L'' x₀'' hsupp =>
    exact ⟨(Real.sqrt 2 : ℂ), ⟨1, 0, 1, by norm_num, by rw [zpow_one, one_mul]⟩, rfl⟩
  | @rotate m h hm Q c L x₀ a Λ hrot L'' x₀'' hsupp =>
    have hx2 : charOf m a * charOf m a = -1 := by
      rw [← charOf_add, ← two_mul, hrot.1, charOf_two_pow_pred hm]
    have hsqrt2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := sqrt_two_mul_self
    have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := sqrt_two_sq_complex
    have hr2 : ((1 + charOf m a) / (Real.sqrt 2 : ℂ)) ^ 2 = charOf m a := by
      rw [div_pow, hs2, div_eq_iff (show (2 : ℂ) ≠ 0 by norm_num)]
      linear_combination hx2
    have hr8 : ((1 + charOf m a) / (Real.sqrt 2 : ℂ)) ^ 2 ^ (3 : ℕ) = 1 := by
      have hr4 : ((1 + charOf m a) / (Real.sqrt 2 : ℂ)) ^ 4 = -1 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hr2, pow_two, hx2]
      calc ((1 + charOf m a) / (Real.sqrt 2 : ℂ)) ^ 2 ^ (3 : ℕ)
          = (((1 + charOf m a) / (Real.sqrt 2 : ℂ)) ^ 4) ^ 2 := by ring
        _ = (-1 : ℂ) ^ 2 := by rw [hr4]
        _ = 1 := by norm_num
    refine ⟨(1 + charOf m a) / (Real.sqrt 2 : ℂ),
      ⟨(1 + charOf m a) / (Real.sqrt 2 : ℂ), 3, 0, hr8, by rw [zpow_zero, mul_one]⟩, ?_⟩
    change c * (1 + charOf m a) / (Real.sqrt 2 : ℂ) = (1 + charOf m a) / (Real.sqrt 2 : ℂ) * c
    ring
  | rephase hm Q Q' c L x₀ P τ τ' hoff hQ hQ' =>
    exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩
  | halve hm Q Q' c L x₀ e P τ hP hQ' hpair =>
    refine ⟨1 / (Real.sqrt 2 : ℂ),
      ⟨1, 0, -1, by norm_num, by rw [zpow_neg_one, one_mul, one_div]⟩, ?_⟩
    change c / (Real.sqrt 2 : ℂ) = 1 / (Real.sqrt 2 : ℂ) * c
    ring
  | copy hm Q Q' c L x₀ P hQ hQ' =>
    exact ⟨1, ⟨1, 0, 0, by norm_num, by rw [zpow_zero, mul_one]⟩, by rw [one_mul]⟩

/-- **The dyadic-ratio invariant, over the whole equivalence closure.** Generalising
`exists_isDyadicRatio_of_carrierRule` from one `CarrierRule` step to a chain of them: the scale
ratio of any two states `Relation.EqvGen CarrierRule` relates is dyadic. -/
theorem exists_isDyadicRatio_of_eqvGen {S T : KernelSumState n}
    (hST : Relation.EqvGen CarrierRule S T) : ∃ r : ℂ, IsDyadicRatio r ∧ T.c = r * S.c := by
  induction hST with
  | rel S T h => exact exists_isDyadicRatio_of_carrierRule h
  | refl S => exact ⟨1, isDyadicRatio_one, by rw [one_mul]⟩
  | symm S T _ ih =>
      obtain ⟨r, hr, hc⟩ := ih
      refine ⟨r⁻¹, hr.inv, ?_⟩
      rw [hc, ← mul_assoc, inv_mul_cancel₀ (hr.ne_zero), one_mul]
  | trans S T U _ _ ih1 ih2 =>
      obtain ⟨r1, hr1, hc1⟩ := ih1
      obtain ⟨r2, hr2, hc2⟩ := ih2
      exact ⟨r2 * r1, hr2.mul hr1, by rw [hc2, hc1, mul_assoc]⟩

/-! ## Flips and per-row relabellings -/

/-- The steps of `CarrierRule` whose two carrier states both satisfy `p`: a chain of them never
leaves `p`. -/
def CarrierRuleWithin (p : KernelSumState n → Prop) (S T : KernelSumState n) : Prop :=
  CarrierRule S T ∧ p S ∧ p T

section FlipBuilding

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-- `DiagPhase.eval` on a difference. -/
private theorem eval_sub'' {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    DiagPhase.eval (A - B) v = DiagPhase.eval A v - DiagPhase.eval B v := by
  simp [DiagPhase.eval]

/-- `DiagPhase.eval` on the literal `1`. -/
private theorem eval_one' {N m : ℕ} (v : Fin N → ZMod 2) :
    DiagPhase.eval (1 : DiagPhase N m) v = 1 := by
  simp [DiagPhase.eval]

/-- A swap of two bound indices, as a rename of the bound block of a `DiagPhase`. -/
private noncomputable def swapBound {m h : ℕ} (a b : Fin h) (Q : DiagPhase (n + h) m) :
    DiagPhase (n + h) m :=
  MvPolynomial.rename (Equiv.swap (Fin.natAdd n a) (Fin.natAdd n b)) Q

/-- Two bound indices are unequal, cast to naturals via `natAdd`, when the originals are. -/
private theorem natAdd_ne_natAdd {h : ℕ} {a b : Fin h} (hab : a ≠ b) :
    Fin.natAdd n a ≠ Fin.natAdd n b := by
  simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]
  intro he
  exact hab (Fin.ext (by omega))

/-- **`swapBound`'s defining identity, through `Fin.append`.** Swapping two `natAdd`-embedded
bound indices of the appended word is the same as appending after swapping the two bound
coordinates. -/
private theorem append_comp_swap_natAdd {h : ℕ} (w : Fin n → ZMod 2) (y : Fin h → ZMod 2)
    (a b : Fin h) :
    (Fin.append w y) ∘ (Equiv.swap (Fin.natAdd n a) (Fin.natAdd n b))
      = Fin.append w (y ∘ Equiv.swap a b) := by
  funext i
  induction i using Fin.addCases with
  | left i' =>
    rw [Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (castAdd_ne_natAdd i' a) (castAdd_ne_natAdd i' b),
      Fin.append_left, Fin.append_left]
  | right i' =>
    rcases eq_or_ne i' a with rfl | hne1
    · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_left]
    · rcases eq_or_ne i' b with rfl | hne2
      · simp only [Function.comp_apply, Fin.append_right, Equiv.swap_apply_right]
      · simp only [Function.comp_apply, Fin.append_right,
          Equiv.swap_apply_of_ne_of_ne (natAdd_ne_natAdd hne1) (natAdd_ne_natAdd hne2),
          Equiv.swap_apply_of_ne_of_ne hne1 hne2]

/-- Under the top bit, the ordinary (ring) sum `z + b` of two casts is the cast of their `𝔽₂`
sum, once multiplied by a further cast `t`: restated from `FTQCLib/Explore/SquierModel.lean`'s
`two_pow_pred_mul_bits`. -/
private theorem two_pow_pred_mul_bits {m : ℕ} (t z b : ZMod 2) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * ((t.val : ℕ) : ZMod (2 ^ m))
        * (((z.val : ℕ) : ZMod (2 ^ m)) + ((b.val : ℕ) : ZMod (2 ^ m)))
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + b)).val : ℕ) : ZMod (2 ^ m)) := by
  have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := FTQCLib.Hierarchy.two_pow_pred_mul_two
  rcases zmod_two_dichotomy t with rfl | rfl <;> rcases zmod_two_dichotomy z with rfl | rfl <;>
    rcases zmod_two_dichotomy b with rfl | rfl <;>
    simp only [show ((0 : ZMod 2).val : ℕ) = 0 from rfl, show ((1 : ZMod 2).val : ℕ) = 1 from rfl,
      show (0 : ZMod 2) + 0 = 0 from rfl, show (0 : ZMod 2) + 1 = 1 from rfl,
      show (1 : ZMod 2) + 0 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl,
      mul_zero, mul_one, zero_mul, Nat.cast_zero, Nat.cast_one] <;>
    first | linear_combination h2 | ring1

/-- The exponent `F` (on `n' + 1` variables) plus the constraint term `2^{m−1}·t·(z + P)` for a
fresh last variable `t`, `F`'s own last variable `z`, and `P` (on `n'` variables): the copy
gadget's source exponent. Restated from `FTQCLib/Explore/SquierModel.lean`'s `copyExponent`. -/
private noncomputable def copyExpo {n' : ℕ} {m : ℕ} (F : DiagPhase (n' + 1) m)
    (P : DiagPhase n' m) : DiagPhase (n' + 1 + 1) m :=
  MvPolynomial.rename Fin.castSucc F
    + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * MvPolynomial.X (Fin.last (n' + 1))
      * (MvPolynomial.X (Fin.castSucc (Fin.last n'))
        + MvPolynomial.rename (fun j : Fin n' => j.castSucc.castSucc) P)

/-- **`copyExpo`'s defining equation**, at a value `P` is known to take. -/
private theorem copyExpo_eval {n' m : ℕ} (F : DiagPhase (n' + 1) m) (P : DiagPhase n' m)
    (p : (Fin n' → ZMod 2) → ZMod 2) (hP : ∀ v, P.eval v = (((p v).val : ℕ) : ZMod (2 ^ m)))
    (v : Fin n' → ZMod 2) (z t : ZMod 2) :
    (copyExpo F P).eval (Fin.snoc (Fin.snoc v z) t)
      = F.eval (Fin.snoc v z)
        + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + p v)).val : ℕ) : ZMod (2 ^ m)) := by
  unfold copyExpo
  rw [DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_mul, DiagPhase.eval_add,
    DiagPhase.eval_C, DiagPhase.eval_X, DiagPhase.eval_X, DiagPhase.eval_rename, DiagPhase.eval_rename]
  have hF : (Fin.snoc (Fin.snoc v z) t : Fin (n' + 1 + 1) → ZMod 2) ∘ Fin.castSucc
      = Fin.snoc v z := by
    funext i; simp only [Function.comp_apply, Fin.snoc_castSucc]
  have hP' : (Fin.snoc (Fin.snoc v z) t : Fin (n' + 1 + 1) → ZMod 2)
      ∘ (fun j : Fin n' => j.castSucc.castSucc) = v := by
    funext i; simp only [Function.comp_apply, Fin.snoc_castSucc]
  rw [hF, hP', hP]
  have hzt : (Fin.snoc (Fin.snoc v z) t : Fin (n' + 1 + 1) → ZMod 2) (Fin.last (n' + 1)) = t := by
    simp only [Fin.snoc_last]
  have hz : (Fin.snoc (Fin.snoc v z) t : Fin (n' + 1 + 1) → ZMod 2) (Fin.castSucc (Fin.last n'))
      = z := by
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hzt, hz, two_pow_pred_mul_bits]

/-- **The swap that trades bound bit `j` for the fresh "z" slot**, evaluated through the two
outer `Fin.snoc`s: at the last-but-one bit `β` and the last bit `γ`, bit `j` of `y` becomes `β`
and the traded-out slot becomes `y`'s old value at `j`. -/
private theorem snoc_snoc_comp_swap {h : ℕ} (y : Fin h → ZMod 2) (β γ : ZMod 2) (j : Fin h) :
    (Fin.snoc (Fin.snoc y β) γ : Fin (h + 1 + 1) → ZMod 2)
        ∘ (Equiv.swap (j.castSucc.castSucc) (Fin.castSucc (Fin.last h)))
      = Fin.snoc (Fin.snoc (Function.update y j β) (y j)) γ := by
  funext i
  simp only [Function.comp_apply]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · have hj := j.isLt
    have hne1 : (Fin.last (h + 1) : Fin (h + 1 + 1)) ≠ j.castSucc.castSucc := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]; omega
    have hne2 : (Fin.last (h + 1) : Fin (h + 1 + 1)) ≠ Fin.castSucc (Fin.last h) := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_castSucc]; omega
    simp only [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun i'' => ?_) i'
    · simp only [Equiv.swap_apply_right, Fin.snoc_castSucc, Fin.snoc_last]
    · by_cases hij : i'' = j
      · subst hij
        simp only [Equiv.swap_apply_left, Fin.snoc_castSucc, Fin.snoc_last, Function.update_self]
      · have hi'' := i''.isLt
        have hne1 : (i''.castSucc.castSucc : Fin (h + 1 + 1)) ≠ j.castSucc.castSucc := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]
          intro he; exact hij (Fin.ext he)
        have hne2 : (i''.castSucc.castSucc : Fin (h + 1 + 1)) ≠ Fin.castSucc (Fin.last h) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last]; omega
        simp only [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Fin.snoc_castSucc,
          Function.update_of_ne hij]

/-! ### Representing an arbitrary Boolean function as a `DiagPhase` -/

/-- **Representability.** Every function into `ZMod 2`, on a finite Boolean domain, is the `eval`
of a `DiagPhase` (the multilinear indicator expansion), casting its bit values into `ZMod (2 ^ m)`
the same way every side condition of `CarrierRule` does. -/
private theorem exists_diagPhase_eval_eq {N m : ℕ} (g : (Fin N → ZMod 2) → ZMod 2) :
    ∃ G : DiagPhase N m,
      ∀ v : Fin N → ZMod 2, DiagPhase.eval G v = (((g v).val : ℕ) : ZMod (2 ^ m)) :=
  DiagPhase.exists_diagPhase_eval fun v => (((g v).val : ℕ) : ZMod (2 ^ m))

end FlipBuilding

/-- **A flip is derivable.** Flipping the bound bit `j` by a bit `f w y` that reads the free word
and the other bound bits (not bit `j`) is a chain of steps: the copy gadget used twice, with an R5
between. Every carrier state of the chain has the endpoints' precision and Lagrangian and denotes
their state. -/
theorem flip_derivable {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) (j : Fin h)
    (f : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod 2)
    (hf : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ (y : Fin h → ZMod 2) (b : ZMod 2),
      f w (Function.update y j b) = f w y)
    (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
      Q'.eval (Fin.append w y) = Q.eval (Fin.append w (Function.update y j (y j + f w y)))) :
    Relation.EqvGen
      (CarrierRuleWithin fun A => A.m = m ∧ A.L = L ∧ StateEq A ⟨m, h, Q, c, L, x₀⟩)
      ⟨m, h, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · -- At `m = 0` every exponent takes the sole value of the subsingleton `ZMod (2 ^ 0)`, so R4
    -- relates the two carrier states directly.
    subst hm0
    haveI : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
    have hcs : GaugeStep (⟨0, h, Q', c, L, x₀⟩ : KernelSumState n) ⟨0, h, Q, c, L, x₀⟩ :=
      GaugeStep.congrSupport Q Q' c L x₀ (fun _ _ _ => Subsingleton.elim _ _)
    have hcr : CarrierRule (⟨0, h, Q', c, L, x₀⟩ : KernelSumState n) ⟨0, h, Q, c, L, x₀⟩ :=
      CarrierRule.gauge hcs
    exact Relation.EqvGen.rel _ _
      ⟨hcr, ⟨rfl, rfl, stateEq_of_carrierRule hcr⟩, ⟨rfl, rfl, StateEq.refl _⟩⟩
  set g : (Fin n → ZMod 2) → (Fin h → ZMod 2) → ZMod 2 := fun w y => y j + f w y with hg_def
  obtain ⟨Grepr, hGrepr⟩ := exists_diagPhase_eval_eq (m := m)
    (fun v : Fin (n + h) → ZMod 2 =>
      g (fun i => v (Fin.castAdd h i)) (fun i => v (Fin.natAdd n i)))
  have hGrepr_eval :
      ∀ w y, DiagPhase.eval Grepr (Fin.append w y) = (((g w y).val : ℕ) : ZMod (2 ^ m)) := by
    intro w y
    have := hGrepr (Fin.append w y)
    simpa [Fin.append_left, Fin.append_right] using this
  set F : DiagPhase (n + h + 1) m := MvPolynomial.rename Fin.castSucc Q with hF_def
  have hF_eval : ∀ v : Fin (n + h) → ZMod 2, ∀ z, F.eval (Fin.snoc v z) = Q.eval v := by
    intro v z
    rw [hF_def, DiagPhase.eval_rename]
    congr 1
    funext i
    simp only [Function.comp_apply, Fin.snoc_castSucc]
  set Q1 : DiagPhase (n + (h + 1 + 1)) m := copyExpo F Grepr with hQ1_def
  -- `Q1`'s defining formula, for every `y`, `z`, `t` (unconditional in `w`).
  have hQ1_formula : ∀ w : Fin n → ZMod 2, ∀ (y : Fin h → ZMod 2) (z t : ZMod 2),
      Q1.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t))
        = Q.eval (Fin.append w y)
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + g w y)).val : ℕ) : ZMod (2 ^ m)) := by
    intro w y z t
    rw [hQ1_def, Fin.append_snoc, Fin.append_snoc,
      copyExpo_eval F Grepr
        (fun v => g (fun i => v (Fin.castAdd h i)) (fun i => v (Fin.natAdd n i)))
        (fun v => hGrepr v) (Fin.append w y) z t, hF_eval]
    congr 2
    · simp only [Fin.append_left, Fin.append_right]
  have hQ1_hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) →
      ∀ (y : Fin h → ZMod 2) (z t : ZMod 2),
      Q1.eval (Fin.append w (Fin.snoc (Fin.snoc y z) t))
        = Q1.eval (Fin.append w (Fin.snoc (Fin.snoc y z) 0))
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + g w y)).val : ℕ) : ZMod (2 ^ m)) := by
    intro w _ y z t
    rw [hQ1_formula w y z t, hQ1_formula w y z 0]
    simp
  have hQ1_hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
      Q.eval (Fin.append w y) = Q1.eval (Fin.append w (Fin.snoc (Fin.snoc y (g w y)) 0)) := by
    intro w _ y
    rw [hQ1_formula w y (g w y) 0]
    simp
  have copy1 : CarrierRule (⟨m, h + 1 + 1, Q1, c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ :=
    CarrierRule.copy hm Q1 Q c L x₀ g hQ1_hQ hQ1_hQ'
  set τ : Equiv.Perm (Fin (h + 1 + 1)) :=
    Equiv.swap (j.castSucc.castSucc) (Fin.castSucc (Fin.last h)) with hτ_def
  set Q2 : DiagPhase (n + (h + 1 + 1)) m :=
    swapBound (j.castSucc.castSucc) (Fin.castSucc (Fin.last h)) Q1 with hQ2_def
  have hQ2_eval : ∀ (w : Fin n → ZMod 2) (y3 : Fin (h + 1 + 1) → ZMod 2),
      Q2.eval (Fin.append w y3) = Q1.eval (Fin.append w (y3 ∘ τ)) := by
    intro w y3
    rw [hQ2_def]
    unfold swapBound
    rw [DiagPhase.eval_rename, append_comp_swap_natAdd]
  set σ : (Fin (h + 1 + 1) → ZMod 2) ≃ (Fin (h + 1 + 1) → ZMod 2) :=
    τ.arrowCongr (Equiv.refl (ZMod 2)) with hσ_def
  have hcomp : ∀ y2 : Fin (h + 1 + 1) → ZMod 2, (σ y2) ∘ τ = y2 := by
    intro y2
    funext i
    simp [hσ_def, Equiv.arrowCongr_apply]
  have hQrename : ∀ w : Fin n → ZMod 2, ∀ y2 : Fin (h + 1 + 1) → ZMod 2,
      Q1.eval (Fin.append w y2) = Q2.eval (Fin.append w (σ y2)) := by
    intro w y2
    rw [hQ2_eval w (σ y2), hcomp y2]
  have gaugeStep2 : GaugeStep (⟨m, h + 1 + 1, Q1, c, L, x₀⟩ : KernelSumState n)
      ⟨m, h + 1 + 1, Q2, c, L, x₀⟩ :=
    GaugeStep.renameBound Q2 Q1 c L x₀ σ hQrename
  -- `Q2`'s defining formula in terms of `Q`, for every `y`, `β`, `γ` (unconditional in `w`).
  have hQ2_formula : ∀ w : Fin n → ZMod 2, ∀ (y : Fin h → ZMod 2) (β γ : ZMod 2),
      Q2.eval (Fin.append w (Fin.snoc (Fin.snoc y β) γ))
        = Q.eval (Fin.append w (Function.update y j β))
          + (2 : ZMod (2 ^ m)) ^ (m - 1)
            * (((γ * (y j + g w (Function.update y j β))).val : ℕ) : ZMod (2 ^ m)) := by
    intro w y β γ
    rw [hQ2_eval w (Fin.snoc (Fin.snoc y β) γ), snoc_snoc_comp_swap y β γ j,
      hQ1_formula w (Function.update y j β) (y j) γ]
  have copy3_hQ : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) →
      ∀ (y : Fin h → ZMod 2) (β γ : ZMod 2),
      Q2.eval (Fin.append w (Fin.snoc (Fin.snoc y β) γ))
        = Q2.eval (Fin.append w (Fin.snoc (Fin.snoc y β) 0))
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((γ * (β + g w y)).val : ℕ) : ZMod (2 ^ m)) := by
    intro w hw y β γ
    rw [hQ2_formula w y β γ, hQ2_formula w y β 0]
    have hgu : g w (Function.update y j β) = β + f w y := by
      rw [hg_def]
      simp only [Function.update_self, hf w hw y β]
    rw [hgu, zero_mul, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero, hg_def]
    congr 2
    ring_nf
  have copy3_hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
      Q'.eval (Fin.append w y) = Q2.eval (Fin.append w (Fin.snoc (Fin.snoc y (g w y)) 0)) := by
    intro w hw y
    rw [hQ2_formula w y (g w y) 0]
    have : Function.update y j (g w y) = Function.update y j (y j + f w y) := by
      simp only [hg_def]
    rw [this, ← hQ' w hw y]
    simp
  have copy3 : CarrierRule (⟨m, h + 1 + 1, Q2, c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q', c, L, x₀⟩ :=
    CarrierRule.copy hm Q2 Q' c L x₀ g copy3_hQ copy3_hQ'
  set p : KernelSumState n → Prop := fun A => A.m = m ∧ A.L = L ∧ StateEq A ⟨m, h, Q, c, L, x₀⟩
    with hp_def
  have hS0 : p (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n) := ⟨rfl, rfl, StateEq.refl _⟩
  have hS1 : p (⟨m, h + 1 + 1, Q1, c, L, x₀⟩ : KernelSumState n) :=
    ⟨rfl, rfl, stateEq_of_carrierRule copy1⟩
  have hS2 : p (⟨m, h + 1 + 1, Q2, c, L, x₀⟩ : KernelSumState n) :=
    ⟨rfl, rfl, (stateEq_of_carrierRule (CarrierRule.gauge gaugeStep2)).symm.trans hS1.2.2⟩
  have hS3 : p (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n) :=
    ⟨rfl, rfl, (stateEq_of_carrierRule copy3).symm.trans hS2.2.2⟩
  have step1 : CarrierRuleWithin p (⟨m, h + 1 + 1, Q1, c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q, c, L, x₀⟩ := ⟨copy1, hS1, hS0⟩
  have step2 : CarrierRuleWithin p (⟨m, h + 1 + 1, Q1, c, L, x₀⟩ : KernelSumState n)
      ⟨m, h + 1 + 1, Q2, c, L, x₀⟩ := ⟨CarrierRule.gauge gaugeStep2, hS1, hS2⟩
  have step3 : CarrierRuleWithin p (⟨m, h + 1 + 1, Q2, c, L, x₀⟩ : KernelSumState n)
      ⟨m, h, Q', c, L, x₀⟩ := ⟨copy3, hS2, hS3⟩
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step3))
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step2)))
    (Relation.EqvGen.rel _ _ step1)

section RelabelBuilding

/-! ### Relabellings from flips

The relabellings `σ` for which the chain exists form a subgroup of the per-row permutations
(`relabelGroup`). It holds every flip that swaps two bound words differing in one bit at one free
word (`relabels_mulSingle_bitSwap`, an instance of `flip_derivable`); those swaps generate every
permutation of the bound words (`closure_bitSwaps`), and one permutation at each free word generates
the per-row permutations (`Subgroup.pi_mem_of_mulSingle_mem`). -/

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

variable {n : ℕ}

/-- Two different bits of `ZMod 2` differ by one. -/
private theorem zmod_two_eq_add_one_of_ne {a b : ZMod 2} (hab : a ≠ b) : a = b + 1 := by
  revert a b; decide

/-- No bit of `ZMod 2` is its own successor. -/
private theorem zmod_two_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  revert a; decide

/-- Adding one twice in `ZMod 2` is the identity. -/
private theorem zmod_two_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by
  revert a; decide

/-- An exponent that reads `Q` through a relabelling `π w` of the bound words at each free word. -/
private theorem exists_diagPhase_relabel {m h : ℕ} (Q : DiagPhase (n + h) m)
    (π : (Fin n → ZMod 2) → (Fin h → ZMod 2) → (Fin h → ZMod 2)) :
    ∃ Q'' : DiagPhase (n + h) m, ∀ (w : Fin n → ZMod 2) (y : Fin h → ZMod 2),
      Q''.eval (Fin.append w y) = Q.eval (Fin.append w (π w y)) := by
  obtain ⟨G, hG⟩ := DiagPhase.exists_diagPhase_eval (N := n + h) (m := m)
    (fun v => Q.eval (Fin.append (fun i => v (Fin.castAdd h i))
      (π (fun i => v (Fin.castAdd h i)) (fun i => v (Fin.natAdd n i)))))
  refine ⟨G, fun w y => ?_⟩
  rw [hG]
  simp only [Fin.append_left, Fin.append_right]

/-- The chain of `flip_derivable` and `relabel_derivable`: `Q'` reaches `Q` by steps whose carrier
states keep the precision and the Lagrangian and denote the state of `Q`. -/
private def ChainTo (m h : ℕ) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (Q' Q : DiagPhase (n + h) m) : Prop :=
  Relation.EqvGen (CarrierRuleWithin fun A => A.m = m ∧ A.L = L ∧ StateEq A ⟨m, h, Q, c, L, x₀⟩)
    ⟨m, h, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩

/-- The two ends of a chain of `CarrierRuleWithin p` are equal or both satisfy `p`. -/
private theorem eqvGen_within_endpoints {p : KernelSumState n → Prop} {A B : KernelSumState n}
    (hAB : Relation.EqvGen (CarrierRuleWithin p) A B) : A = B ∨ (p A ∧ p B) := by
  induction hAB with
  | rel x y hxy =>
    obtain ⟨_, hx, hy⟩ := hxy
    exact Or.inr ⟨hx, hy⟩
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
    rcases ih with hxy | ⟨hx, hy⟩
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨hy, hx⟩
  | trans x y z _ _ ih₁ ih₂ =>
    rcases ih₁ with hxy | ⟨hx, hy⟩
    · rw [hxy]; exact ih₂
    · rcases ih₂ with hyz | ⟨_, hz⟩
      · rw [← hyz]; exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

/-- The two ends of a chain denote the same state. -/
private theorem chainTo_stateEq {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {Q' Q : DiagPhase (n + h) m} (hC : ChainTo m h c L x₀ Q' Q) :
    StateEq (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n) ⟨m, h, Q, c, L, x₀⟩ := by
  rcases eqvGen_within_endpoints hC with he | ⟨hp, _⟩
  · exact he ▸ StateEq.refl _
  · obtain ⟨_, _, hs⟩ := hp
    exact hs

/-- A chain whose steps stay among the carrier states denoting one state stays among those denoting
any state equal to it. -/
private theorem chainTo_retarget {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {Q₁ Q₂ : DiagPhase (n + h) m} {A B : KernelSumState n}
    (hs : StateEq (⟨m, h, Q₁, c, L, x₀⟩ : KernelSumState n) ⟨m, h, Q₂, c, L, x₀⟩)
    (hAB : Relation.EqvGen
      (CarrierRuleWithin fun A => A.m = m ∧ A.L = L ∧ StateEq A ⟨m, h, Q₁, c, L, x₀⟩) A B) :
    Relation.EqvGen
      (CarrierRuleWithin fun A => A.m = m ∧ A.L = L ∧ StateEq A ⟨m, h, Q₂, c, L, x₀⟩) A B :=
  Relation.EqvGen.mono (fun _ _ ⟨hr, ⟨hA₁, hA₂, hA₃⟩, ⟨hB₁, hB₂, hB₃⟩⟩ =>
    ⟨hr, ⟨hA₁, hA₂, hA₃.trans hs⟩, ⟨hB₁, hB₂, hB₃.trans hs⟩⟩) hAB

/-- Chains compose. -/
private theorem chainTo_trans {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {Q₁ Q₂ Q₃ : DiagPhase (n + h) m} (h₁₂ : ChainTo m h c L x₀ Q₁ Q₂)
    (h₂₃ : ChainTo m h c L x₀ Q₂ Q₃) : ChainTo m h c L x₀ Q₁ Q₃ :=
  Relation.EqvGen.trans _ _ _ (chainTo_retarget (chainTo_stateEq h₂₃) h₁₂) h₂₃

/-- Chains reverse. -/
private theorem chainTo_symm {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {Q₁ Q₂ : DiagPhase (n + h) m} (h₁₂ : ChainTo m h c L x₀ Q₁ Q₂) :
    ChainTo m h c L x₀ Q₂ Q₁ :=
  Relation.EqvGen.symm _ _ (chainTo_retarget (chainTo_stateEq h₁₂).symm h₁₂)

/-- The per-row relabelling `σ` is derivable: every exponent reading `Q` through `σ` on the support
reaches `Q` by a chain. -/
private def Relabels (m h : ℕ) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (σ : (Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2)) : Prop :=
  ∀ Q Q' : DiagPhase (n + h) m, (∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) →
    ∀ y : Fin h → ZMod 2, Q'.eval (Fin.append w y) = Q.eval (Fin.append w (σ w y))) →
    ChainTo m h c L x₀ Q' Q

/-- The identity relabelling is one step of R4. -/
private theorem relabels_one {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} : Relabels m h c L x₀ 1 := by
  intro Q Q' hQ'
  have hg : GaugeStep (⟨m, h, Q', c, L, x₀⟩ : KernelSumState n) ⟨m, h, Q, c, L, x₀⟩ :=
    GaugeStep.congrSupport Q Q' c L x₀ (fun w hw y => by simpa using hQ' w hw y)
  have hr := CarrierRule.gauge hg
  exact Relation.EqvGen.rel _ _
    ⟨hr, ⟨rfl, rfl, stateEq_of_carrierRule hr⟩, ⟨rfl, rfl, StateEq.refl _⟩⟩

/-- Derivable relabellings compose, through an exponent that reads `Q` through the first. -/
private theorem relabels_mul {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {σ₁ σ₂ : (Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2)}
    (h₁ : Relabels m h c L x₀ σ₁) (h₂ : Relabels m h c L x₀ σ₂) :
    Relabels m h c L x₀ (σ₁ * σ₂) := by
  intro Q Q' hQ'
  obtain ⟨Q'', hQ''⟩ := exists_diagPhase_relabel Q (fun w y => σ₁ w y)
  refine chainTo_trans (h₂ Q'' Q' (fun w hw y => ?_)) (h₁ Q Q'' (fun w _ y => hQ'' w y))
  rw [hQ' w hw y, hQ'' w (σ₂ w y), Pi.mul_apply, Equiv.Perm.mul_apply]

/-- The inverse of a derivable relabelling is derivable: the chain reversed. -/
private theorem relabels_inv {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} {σ : (Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2)}
    (hσ : Relabels m h c L x₀ σ) : Relabels m h c L x₀ σ⁻¹ := by
  intro Q Q' hQ'
  refine chainTo_symm (hσ Q' Q (fun w hw y => ?_))
  rw [hQ' w hw (σ w y)]
  simp

/-- The derivable per-row relabellings, a subgroup of the per-row permutations. -/
private def relabelGroup (m h : ℕ) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2) : Subgroup ((Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2)) where
  carrier := {σ | Relabels m h c L x₀ σ}
  one_mem' := relabels_one
  mul_mem' := relabels_mul
  inv_mem' := relabels_inv

/-- The swaps of two bound words that differ in one bit. -/
private def bitSwaps (h : ℕ) : Set (Equiv.Perm (Fin h → ZMod 2)) :=
  {π | ∃ (y₀ : Fin h → ZMod 2) (j : Fin h), π = Equiv.swap y₀ (Function.update y₀ j (y₀ j + 1))}

/-- Words that agree from bit `k` on are joined by the swaps of `bitSwaps`, by induction on `k`:
the bit below `k` is set first, then the rest. -/
private theorem exists_mem_closure_bitSwaps {h : ℕ} (x y : Fin h → ZMod 2) :
    ∀ k : ℕ, k ≤ h → (∀ i : Fin h, k ≤ i.val → x i = y i) →
      ∃ g ∈ Subgroup.closure (bitSwaps h), g x = y := by
  intro k
  induction k generalizing x with
  | zero =>
    intro _ hxy
    exact ⟨1, Subgroup.one_mem _, funext fun i => hxy i (Nat.zero_le _)⟩
  | succ k ih =>
    intro hk hxy
    set j : Fin h := ⟨k, by omega⟩ with hj
    have hx' : ∀ i : Fin h, k ≤ i.val → Function.update x j (y j) i = y i := by
      intro i hi
      by_cases hij : i = j
      · rw [hij, Function.update_self]
      · rw [Function.update_of_ne hij]
        have hik : i.val ≠ k := fun he => hij (Fin.ext he)
        exact hxy i (by omega)
    obtain ⟨g, hg, hgx⟩ := ih (Function.update x j (y j)) (by omega) hx'
    by_cases hxj : x j = y j
    · refine ⟨g, hg, ?_⟩
      rw [← hgx, ← hxj, Function.update_eq_self]
    · have hy : y j = x j + 1 := zmod_two_eq_add_one_of_ne (Ne.symm hxj)
      refine ⟨g * Equiv.swap x (Function.update x j (x j + 1)),
        Subgroup.mul_mem _ hg (Subgroup.subset_closure ⟨x, j, rfl⟩), ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, ← hy, hgx]

/-- **The one-bit swaps generate every permutation of the bound words.** -/
private theorem closure_bitSwaps (h : ℕ) : Subgroup.closure (bitSwaps h) = ⊤ := by
  haveI : MulAction.IsPretransitive (Subgroup.closure (bitSwaps h)) (Fin h → ZMod 2) :=
    ⟨fun x y => by
      obtain ⟨g, hg, hgx⟩ := exists_mem_closure_bitSwaps x y h le_rfl
        (fun i hi => absurd hi (Nat.not_le.mpr i.isLt))
      exact ⟨⟨g, hg⟩, hgx⟩⟩
  refine closure_of_isSwap_of_isPretransitive (fun π hπ => ?_)
  obtain ⟨y₀, j, rfl⟩ := hπ
  refine ⟨y₀, _, fun he => ?_, rfl⟩
  have hj := congrFun he j
  rw [Function.update_self] at hj
  exact zmod_two_ne_add_one (y₀ j) hj

/-- A one-bit swap moves a word that agrees with `y₀` off bit `j` by flipping bit `j`. -/
private theorem swap_bitSwap_apply_near {h : ℕ} (y₀ y : Fin h → ZMod 2) (j : Fin h)
    (hy : ∀ i, i ≠ j → y i = y₀ i) :
    Equiv.swap y₀ (Function.update y₀ j (y₀ j + 1)) y = Function.update y j (y j + 1) := by
  by_cases hyj : y j = y₀ j
  · have he : y = y₀ := funext fun i => by
      by_cases hij : i = j
      · rw [hij, hyj]
      · exact hy i hij
    rw [he, Equiv.swap_apply_left]
  · have hyj' : y j = y₀ j + 1 := zmod_two_eq_add_one_of_ne hyj
    have he : y = Function.update y₀ j (y₀ j + 1) := funext fun i => by
      by_cases hij : i = j
      · rw [hij, Function.update_self, hyj']
      · rw [Function.update_of_ne hij, hy i hij]
    rw [he, Equiv.swap_apply_right, Function.update_self, Function.update_idem,
      zmod_two_add_one_add_one, Function.update_eq_self]

/-- A one-bit swap at one free word, read pointwise: a flip of bit `j` by the indicator of that
free word and of the other bits of `y₀`. -/
private theorem mulSingle_bitSwap_apply {h : ℕ} (w₀ w : Fin n → ZMod 2) (y₀ y : Fin h → ZMod 2)
    (j : Fin h) :
    (Pi.mulSingle w₀ (Equiv.swap y₀ (Function.update y₀ j (y₀ j + 1)))
        : (Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2)) w y
      = Function.update y j (y j + if w = w₀ ∧ ∀ i, i ≠ j → y i = y₀ i then 1 else 0) := by
  by_cases hw : w = w₀
  · subst hw
    rw [Pi.mulSingle_eq_same]
    by_cases hy : ∀ i, i ≠ j → y i = y₀ i
    · rw [if_pos ⟨rfl, hy⟩]
      exact swap_bitSwap_apply_near y₀ y j hy
    · rw [if_neg (fun hc => hy hc.2), add_zero, Function.update_eq_self]
      refine Equiv.swap_apply_of_ne_of_ne (fun he => hy fun i _ => by rw [he]) (fun he => ?_)
      exact hy fun i hi => by rw [he, Function.update_of_ne hi]
  · rw [Pi.mulSingle_eq_of_ne hw, if_neg (fun hc => hw hc.1), add_zero, Function.update_eq_self,
      Equiv.Perm.one_apply]

/-- **A one-bit swap at one free word is derivable**: it is the flip of bit `j` by the indicator of
that free word and of the other bits of `y₀` (`flip_derivable`). -/
private theorem relabels_mulSingle_bitSwap {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} (w₀ : Fin n → ZMod 2) (y₀ : Fin h → ZMod 2) (j : Fin h) :
    Relabels m h c L x₀ (Pi.mulSingle w₀ (Equiv.swap y₀ (Function.update y₀ j (y₀ j + 1)))) := by
  intro Q Q' hQ'
  have hf : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ (y : Fin h → ZMod 2) (b : ZMod 2),
      (if w = w₀ ∧ ∀ i, i ≠ j → Function.update y j b i = y₀ i then (1 : ZMod 2) else 0)
        = if w = w₀ ∧ ∀ i, i ≠ j → y i = y₀ i then 1 else 0 := by
    intro w _ y b
    have hiff : (∀ i, i ≠ j → Function.update y j b i = y₀ i) ↔ ∀ i, i ≠ j → y i = y₀ i :=
      forall_congr' fun i => imp_congr_right fun hi => by rw [Function.update_of_ne hi]
    simp only [hiff]
  refine flip_derivable Q Q' c L x₀ j
    (fun w y => if w = w₀ ∧ ∀ i, i ≠ j → y i = y₀ i then 1 else 0) hf (fun w hw y => ?_)
  beta_reduce
  rw [hQ' w hw y, mulSingle_bitSwap_apply]

/-- **Every per-row relabelling is derivable**: each is one permutation at each free word, and each
of those is a product of one-bit swaps. -/
private theorem relabels_all {m h : ℕ} {c : ℂ} {L : Submodule (ZMod 2) (Pauli n)}
    {x₀ : Fin n → ZMod 2} (σ : (Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2)) :
    Relabels m h c L x₀ σ := by
  refine Subgroup.pi_mem_of_mulSingle_mem (H := relabelGroup m h c L x₀) σ (fun w₀ => ?_)
  have hle : Subgroup.closure (bitSwaps h)
      ≤ (relabelGroup m h c L x₀).comap (MonoidHom.mulSingle _ w₀) := by
    rw [Subgroup.closure_le]
    rintro π ⟨y₀, j, rfl⟩
    exact Subgroup.mem_comap.mpr (relabels_mulSingle_bitSwap w₀ y₀ j)
  have hmem : σ w₀ ∈ Subgroup.closure (bitSwaps h) := by
    rw [closure_bitSwaps]
    exact Subgroup.mem_top _
  exact hle hmem

end RelabelBuilding

/-- **Every per-row relabelling is derivable.** An exponent that reads the bound words through one
bijection `σ w` for each free word `w` of the support is related to the original by a chain of
steps, generated by the flips of `flip_derivable`. Every carrier state of the chain has the
endpoints' precision and Lagrangian and denotes their state. -/
theorem relabel_derivable {m h : ℕ} (Q Q' : DiagPhase (n + h) m) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (σ : (Fin n → ZMod 2) → Equiv.Perm (Fin h → ZMod 2))
    (hQ' : ∀ w : Fin n → ZMod 2, (∃ p ∈ L, w = x₀ + p.X) → ∀ y : Fin h → ZMod 2,
      Q'.eval (Fin.append w y) = Q.eval (Fin.append w (σ w y))) :
    Relation.EqvGen
      (CarrierRuleWithin fun A => A.m = m ∧ A.L = L ∧ StateEq A ⟨m, h, Q, c, L, x₀⟩)
      ⟨m, h, Q', c, L, x₀⟩ ⟨m, h, Q, c, L, x₀⟩ :=
  relabels_all σ Q Q' hQ'

end FTQCLib.Frame.Walkthrough

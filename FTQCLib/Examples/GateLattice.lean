/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.RegisterWalkthrough
import FTQCLib.Hilbert.CGKExactness

/-! # The gate lattice — the counting, tower, and parity-split facts

Three small results on the gate lattice, companions to `ctrlRootPoly_level` (the device) and the
CGK classification (`FTQCLib/Hilbert/CGKExactness.lean`):

* the level-`k` stratum of the (interaction, precision) lattice has exactly `k` points, of which
  `k − 2` are interior (`latticePoints_card`, `latticeInterior_card`);
* squaring descends the tower: the rung-`(m−1)` device, lifted, is the rung-`m` device doubled
  (`ctrlRootPoly_double`) — each column of the lattice is one gate under square roots;
* the parity split `T_{x⊕y} = (T ⊗ T)·CS†` at the exponent level (`tPar_split`, `tPar_cs`):
  substituting a parity into the precision-3 gate forces the lattice's first interior point — the
  `CS†` monomial is exactly the lift of `−1` from the ℤ/4 rung. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hilbert

variable {n : ℕ}

/-! ## The stratum count -/

/-- **Level `k` has exactly `k` lattice points**: pairs `(d, m)` with `d, m ≥ 1` and
`(m − 1) + d = k` (written `d + m = k + 1` to stay in `ℕ`). -/
theorem latticePoints_card (k : ℕ) (hk : 1 ≤ k) :
    (((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter fun p => p.1 + p.2 = k + 1).card = k := by
  have himg : (((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter fun p => p.1 + p.2 = k + 1)
      = (Finset.Icc 1 k).image (fun d => (d, k + 1 - d)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_Icc,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩
      exact ⟨a, ⟨ha1, ha2⟩, rfl, by omega⟩
    · rintro ⟨d, ⟨hd1, hd2⟩, rfl, rfl⟩
      refine ⟨⟨⟨hd1, hd2⟩, ?_, ?_⟩, ?_⟩ <;> omega
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab),
    Nat.card_Icc]
  omega

/-- **Of which `k − 2` are interior** (both coordinates ≥ 2): the two boundary families — the
multi-controlled signs (`m = 1`) and the root tower (`d = 1`) — cover only two points per level. -/
theorem latticeInterior_card (k : ℕ) (hk : 3 ≤ k) :
    (((Finset.Icc 2 k) ×ˢ (Finset.Icc 2 k)).filter fun p => p.1 + p.2 = k + 1).card = k - 2 := by
  have himg : (((Finset.Icc 2 k) ×ˢ (Finset.Icc 2 k)).filter fun p => p.1 + p.2 = k + 1)
      = (Finset.Icc 2 (k - 1)).image (fun d => (d, k + 1 - d)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_Icc,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩
      exact ⟨a, ⟨ha1, by omega⟩, rfl, by omega⟩
    · rintro ⟨d, ⟨hd1, hd2⟩, rfl, rfl⟩
      refine ⟨⟨⟨hd1, ?_⟩, ?_, ?_⟩, ?_⟩ <;> omega
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab),
    Nat.card_Icc]
  omega

/-! ## The tower relation: squaring descends a rung -/

/-- **Each lattice column is one gate under square roots**: the rung-`(m−1)` device, lifted to
rung `m`, is the rung-`m` device doubled — `R_{A,m}² = R_{A,m−1}` at the exponent level. -/
theorem ctrlRootPoly_double (A : Finset (Fin n)) (m : ℕ) (hm : 1 ≤ m) :
    liftTo m (Nat.sub_le m 1) (ctrlRootPoly A (m - 1))
      = ctrlRootPoly A m + ctrlRootPoly A m := by
  apply MvPolynomial.ext
  intro e
  rw [liftTo_coeff, ctrlRoot_eq_monomial, ctrlRoot_eq_monomial, MvPolynomial.coeff_add,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases hde : (∑ i ∈ A, Finsupp.single i (1 : ℕ)) = e
  · rw [if_pos hde, if_pos hde]
    show dmapTo (m - 1) m 1 = 1 + 1
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      unfold dmapTo
      decide
    · unfold dmapTo
      have hsub : m - (m - 1) = 1 := by omega
      have hval : (1 : ZMod (2 ^ (m - 1))).val = 1 := by
        rw [ZMod.val_one_eq_one_mod]
        refine Nat.mod_eq_of_lt ?_
        have h2 : (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        have : (2 : ℕ) ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [hsub, hval, pow_one, Nat.mul_one]
      norm_num
  · rw [if_neg hde, if_neg hde, dmapTo_zero, add_zero]

/-! ## The parity split: `T_{x⊕y} = (T ⊗ T) · CS†` at the exponent level -/

/-- **Raw form**: pushing the precision-3 gate's exponent through the CNOT substitution
(`x_k ↦ x_k ⊕ x_i`) splits it into the two single-bit exponents and a `−2`-weighted interaction
monomial. -/
theorem tPar_split (i k : Fin n) :
    DiagPhase.affinePushforward i k (DiagPhase.rzGatePoly k 3)
      = DiagPhase.rzGatePoly k 3 + DiagPhase.rzGatePoly i 3
        - 2 * (MvPolynomial.X i * MvPolynomial.X k) := by
  unfold DiagPhase.affinePushforward DiagPhase.rzGatePoly
  rw [MvPolynomial.bind₁_X_right]
  unfold DiagPhase.cnotSubst
  rw [if_pos rfl]

/-- **CS form**: the interaction term is exactly the **lift of `−1` from the ℤ/4 rung** — the
`CS†` exponent. Substituting a parity into the root tower's level-3 gate *forces the lattice's
first interior point*. -/
theorem tPar_cs (i k : Fin n) (hik : i ≠ k) :
    DiagPhase.affinePushforward i k (DiagPhase.rzGatePoly k 3)
      = DiagPhase.rzGatePoly k 3 + DiagPhase.rzGatePoly i 3
        + liftTo 3 (by norm_num) (- ctrlRootPoly {i, k} 2) := by
  rw [tPar_split, sub_eq_add_neg]
  congr 1
  have hXX : (MvPolynomial.X i * MvPolynomial.X k : DiagPhase n 3)
      = MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single k 1) 1 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  have hctrl : ctrlRootPoly ({i, k} : Finset (Fin n)) 2
      = MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single k 1) (1 : ZMod (2 ^ 2)) := by
    rw [ctrlRoot_eq_monomial, Finset.sum_pair hik]
  rw [hXX, hctrl]
  have h2 : (2 : DiagPhase n 3) = MvPolynomial.C 2 := (map_ofNat MvPolynomial.C 2).symm
  rw [h2, MvPolynomial.C_mul_monomial, mul_one]
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_neg, liftTo_coeff, MvPolynomial.coeff_neg,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases hde : (Finsupp.single i 1 + Finsupp.single k 1) = e
  · rw [if_pos hde, if_pos hde]
    show -(2 : ZMod (2 ^ 3)) = dmapTo 2 3 (-1)
    unfold dmapTo
    decide
  · rw [if_neg hde, if_neg hde, neg_zero, neg_zero, dmapTo_zero]

/-! ## Axiom check -/

#print axioms latticePoints_card
#print axioms latticeInterior_card
#print axioms ctrlRootPoly_double
#print axioms tPar_split
#print axioms tPar_cs

end FTQCLib.Frame.Walkthrough

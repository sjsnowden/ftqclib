/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.BoundElimination

/-!
# A Tietze transformation in carrier syntax

The feasibility study in `explore/squier/` asks whether Squier's invariants (finite derivation
type, homological type `FP₃`) could show that no finite convergent rewriting system on carrier
states exists from degree three on. Those invariants belong to the presented object, not to a
choice of generators: finite presentations of one monoid are joined by Tietze transformations,
each of which adds a generator together with a relation that names it, and finite derivation type
is kept along them.

This file checks the one piece of that machinery that has a direct carrier form. Two new bound
bits `z, t` with the constraint term `2^{m−1}·t·(z + P)` make `z` a name for the bit `P`: summing
`t` out leaves `2` where `z = P` and `0` elsewhere, and the factor `2` is exactly the scale of the
two extra bits. So the pair adds a generator with its defining relation, and the amplitude is
unchanged (`amp_copy`). Read from left to right, `amp_copy` is an instance of Vilmart's rule (HH)
on sums over paths, with the substituted variable bound; read from right to left it is the Tietze
transformation.

With `P` the product of two variables, the gadget trades one monomial of degree `k` for monomials
of degree at most `max (k − 1) 3` (`totalDegree_copyExponent_le`). The rows at the end do this for
the quartic phase `(−1)^{y₀y₁y₂y₃}`: at height four it has degree four, and at height six it is
presented by an exponent of degree at most three.

**How the outcome is read.** The study uses `amp_copy` for one inference: above three, the degree
of an exponent is a choice of generators, not a property of the carrier state's amplitude, so any
obstruction that an invariant of the presented object gives is the same for every degree bound
`d ≥ 3`. Iterating the gadget over every monomial of degree four and above is inferred there, not
proved here.

Everything here is frame-pure. An exploratory file; see `FTQCLib/Explore/README.md`.

## Main definitions

* `copyExponent F P` — the exponent `F` with the constraint pair appended.
* `substLast F P` — the exponent `F` with its last variable replaced by `P`.

## Main results

* `ampCore_copy`, `amp_copy` — the gadget keeps the amplitude.
* `amp_copyExponent` — the same, with both exponents built as polynomials.
* `totalDegree_copyExponent_le` — the gadget's degree bound.
* `amp_quartic_eq_gadget`, `totalDegree_quartic`, `totalDegree_quarticGadget_le` — the quartic row.
-/

namespace FTQCLib.Explore.SquierModel

open FTQCLib FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Frame.Walkthrough

variable {n : ℕ}

/-! ## The constraint bit -/

/-- A bit of `ZMod 2` is `0` or `1`. -/
private theorem bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- Summing the constraint bit `t` of the term `2^{m−1}·t·s` gives `2` where `s = 0` and `0` where
`s = 1`. -/
theorem sum_charOf_constraint {m : ℕ} (hm : 1 ≤ m) (s : ZMod 2) :
    ∑ t : ZMod 2, charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * s).val : ℕ) : ZMod (2 ^ m)))
      = if s = 0 then 2 else 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, charOf_two_pow_mul hm,
    charOf_two_pow_mul hm]
  rcases bit_cases s with rfl | rfl
  · rw [if_pos rfl, show ((0 : ZMod 2) * 0).val = 0 from rfl,
      show ((1 : ZMod 2) * 0).val = 0 from rfl]
    norm_num
  · rw [if_neg (by decide), show ((0 : ZMod 2) * 1).val = 0 from rfl,
      show ((1 : ZMod 2) * 1).val = 1 from rfl]
    norm_num

/-! ## The gadget on the amplitude -/

/-- The sum over `h + 2` bound bits split into the last bit `t`, the bit `z` before it, and the
first `h` bits. -/
private theorem sum_split_two {M : Type*} [AddCommMonoid M] {h : ℕ}
    (f : (Fin (h + 1 + 1) → ZMod 2) → M) :
    ∑ y'' : Fin (h + 1 + 1) → ZMod 2, f y''
      = ∑ y : Fin h → ZMod 2, ∑ z : ZMod 2, ∑ t : ZMod 2, f (Fin.snoc (Fin.snoc y z) t) := by
  rw [sum_snoc_peel, Finset.sum_comm,
    sum_snoc_peel (fun y' : Fin (h + 1) → ZMod 2 => ∑ t : ZMod 2, f (Fin.snoc y' t)),
    Finset.sum_comm]

/-- **The copy gadget on the raw amplitude.** Two bound bits `z, t` appended to an exponent `F`
with the constraint term `2^{m−1}·t·(z + P)` give the amplitude of `F` with `z` replaced by the
bit `P`, at two bound bits fewer and the same scale. -/
theorem ampCore_copy {m h : ℕ} (hm : 1 ≤ m) {F : DiagPhase (n + h + 1) m}
    {P : (Fin (n + h) → ZMod 2) → ZMod 2} {Q : DiagPhase (n + h) m}
    {Q' : DiagPhase (n + h + 1 + 1) m}
    (hQ' : ∀ (v : Fin (n + h) → ZMod 2) (z t : ZMod 2),
      Q'.eval (Fin.snoc (Fin.snoc v z) t)
        = F.eval (Fin.snoc v z)
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + P v)).val : ℕ) : ZMod (2 ^ m)))
    (hQ : ∀ v : Fin (n + h) → ZMod 2, Q.eval v = F.eval (Fin.snoc v (P v)))
    (c : ℂ) (w : Fin n → ZMod 2) :
    ampCore m (h + 1 + 1) Q' c w = ampCore m h Q c w := by
  rw [ampCore_eq_sum_charOf, ampCore_eq_sum_charOf, sum_split_two]
  -- each bound word `y` contributes twice its term at `z = P`
  have hword : ∀ y : Fin h → ZMod 2,
      ∑ z : ZMod 2, ∑ t : ZMod 2,
          charOf m (Q'.eval (@Fin.append n (h + 1 + 1) (ZMod 2) w (Fin.snoc (Fin.snoc y z) t)))
        = 2 * charOf m (Q.eval (@Fin.append n h (ZMod 2) w y)) := by
    intro y
    set v : Fin (n + h) → ZMod 2 := @Fin.append n h (ZMod 2) w y with hv
    have hterm : ∀ z t : ZMod 2,
        charOf m (Q'.eval (@Fin.append n (h + 1 + 1) (ZMod 2) w (Fin.snoc (Fin.snoc y z) t)))
          = charOf m (F.eval (Fin.snoc v z))
            * charOf m ((2 : ZMod (2 ^ m)) ^ (m - 1)
                * (((t * (z + P v)).val : ℕ) : ZMod (2 ^ m))) := by
      intro z t
      have hword : (@Fin.append n (h + 1 + 1) (ZMod 2) w (Fin.snoc (Fin.snoc y z) t)
          : Fin (n + h + 1 + 1) → ZMod 2) = Fin.snoc (Fin.snoc v z) t := by
        rw [Fin.append_snoc, Fin.append_snoc]
      rw [hword, hQ', charOf_add]
    have hoff : ∀ z : ZMod 2, z ≠ P v →
        charOf m (F.eval (Fin.snoc v z)) * (if z + P v = 0 then (2 : ℂ) else 0) = 0 := by
      intro z hne
      have hsum : z + P v ≠ 0 := fun h0 =>
        hne (sub_eq_zero.mp (by rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]; exact h0))
      rw [if_neg hsum, mul_zero]
    have hself : P v + P v = 0 := by
      rcases bit_cases (P v) with h0 | h0 <;> rw [h0] <;> rfl
    simp_rw [hterm, ← Finset.mul_sum, sum_charOf_constraint hm]
    rw [Fintype.sum_eq_single (P v) hoff, if_pos hself, hQ]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hword y), ← Finset.mul_sum]
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hne : (Real.sqrt 2 : ℂ) ^ h ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hscale : c / (Real.sqrt 2 : ℂ) ^ (h + 1 + 1) * 2 = c / (Real.sqrt 2 : ℂ) ^ h := by
    rw [pow_succ, pow_succ, mul_assoc, hsq]
    field_simp
  rw [← mul_assoc, hscale]

/-- **The copy gadget on carrier states.** The carrier state with the constraint pair appended
denotes the state of the exponent with `z` replaced by `P`: a Tietze transformation, with the
same scale, Lagrangian and offset. -/
theorem amp_copy {m h : ℕ} (hm : 1 ≤ m) {F : DiagPhase (n + h + 1) m}
    {P : (Fin (n + h) → ZMod 2) → ZMod 2} {Q : DiagPhase (n + h) m}
    {Q' : DiagPhase (n + h + 1 + 1) m}
    (hQ' : ∀ (v : Fin (n + h) → ZMod 2) (z t : ZMod 2),
      Q'.eval (Fin.snoc (Fin.snoc v z) t)
        = F.eval (Fin.snoc v z)
          + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + P v)).val : ℕ) : ZMod (2 ^ m)))
    (hQ : ∀ v : Fin (n + h) → ZMod 2, Q.eval v = F.eval (Fin.snoc v (P v)))
    (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    amp (⟨m, h + 1 + 1, Q', c, L, x₀⟩ : KernelSumState n) = amp ⟨m, h, Q, c, L, x₀⟩ := by
  funext w
  by_cases hw : ∃ p ∈ L, w = x₀ + p.X
  · rw [amp_pos (S := (⟨m, h + 1 + 1, Q', c, L, x₀⟩ : KernelSumState n)) hw,
      amp_pos (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]
    exact ampCore_copy hm hQ' hQ c w
  · rw [amp_neg (S := (⟨m, h + 1 + 1, Q', c, L, x₀⟩ : KernelSumState n)) hw,
      amp_neg (S := (⟨m, h, Q, c, L, x₀⟩ : KernelSumState n)) hw]

/-! ## The constraint pair as polynomials -/

/-- The exponent `F`, read on the first `n + h + 1` variables, plus the constraint term
`2^{m−1}·t·(z + P)` for the new last variable `t`, the last variable `z` of `F`, and `P`. The sum
`z + P` is the ordinary sum: under the factor `2^{m−1}` it agrees with the `𝔽₂` sum
(`copyExponent_eval`). -/
noncomputable def copyExponent {m h : ℕ} (F : DiagPhase (n + h + 1) m) (P : DiagPhase (n + h) m) :
    DiagPhase (n + h + 1 + 1) m :=
  MvPolynomial.rename Fin.castSucc F
    + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * MvPolynomial.X (Fin.last (n + h + 1))
      * (MvPolynomial.X (Fin.castSucc (Fin.last (n + h)))
        + MvPolynomial.rename (fun j : Fin (n + h) => j.castSucc.castSucc) P)

/-- The exponent `F` with its last variable replaced by the polynomial `P`. -/
noncomputable def substLast {N m : ℕ} (F : DiagPhase (N + 1) m) (P : DiagPhase N m) :
    DiagPhase N m :=
  MvPolynomial.bind₁
    (Fin.snoc (α := fun _ : Fin (N + 1) => DiagPhase N m)
      (fun j : Fin N => (MvPolynomial.X j : DiagPhase N m)) P) F

/-- A renamed exponent evaluates as the exponent at the word read through the renaming. -/
theorem eval_rename' {N N' m : ℕ} (f : Fin N → Fin N') (F : DiagPhase N m)
    (u : Fin N' → ZMod 2) :
    DiagPhase.eval (MvPolynomial.rename f F) u = DiagPhase.eval F (u ∘ f) := by
  unfold DiagPhase.eval
  rw [MvPolynomial.eval_rename]
  rfl

/-- Where `P` evaluates to the bit `b`, the substituted exponent evaluates as `F` with its last
variable set to `b`. -/
theorem substLast_eval {N m : ℕ} (F : DiagPhase (N + 1) m) (P : DiagPhase N m)
    (v : Fin N → ZMod 2) {b : ZMod 2} (hb : P.eval v = ((b.val : ℕ) : ZMod (2 ^ m))) :
    (substLast F P).eval v = F.eval (Fin.snoc v b) := by
  unfold substLast DiagPhase.eval
  have h := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
    (DiagPhase.liftBinary v)
    (Fin.snoc (α := fun _ : Fin (N + 1) => DiagPhase N m)
      (fun j : Fin N => (MvPolynomial.X j : DiagPhase N m)) P) F
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  have hfun : (fun i : Fin (N + 1) =>
      (MvPolynomial.eval (DiagPhase.liftBinary v))
        (Fin.snoc (α := fun _ : Fin (N + 1) => DiagPhase N m)
          (fun j : Fin N => (MvPolynomial.X j : DiagPhase N m)) P i))
      = DiagPhase.liftBinary (Fin.snoc v b) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [Fin.snoc_last, DiagPhase.liftBinary]
      exact hb
    · intro l
      simp [DiagPhase.liftBinary]
  rw [hfun]

/-- Under the top bit, the ordinary sum `z + b` of two bits is their `𝔽₂` sum. -/
private theorem two_pow_pred_mul_bits {m : ℕ} (t z b : ZMod 2) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * ((t.val : ℕ) : ZMod (2 ^ m))
        * (((z.val : ℕ) : ZMod (2 ^ m)) + ((b.val : ℕ) : ZMod (2 ^ m)))
      = (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + b)).val : ℕ) : ZMod (2 ^ m)) := by
  have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := two_pow_pred_mul_two
  rcases bit_cases t with rfl | rfl <;> rcases bit_cases z with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl,
      show (0 : ZMod 2) + 0 = 0 from rfl, show (0 : ZMod 2) + 1 = 1 from rfl,
      show (1 : ZMod 2) + 0 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl,
      mul_zero, mul_one, zero_mul, Nat.cast_zero, Nat.cast_one] <;>
    first | linear_combination h2 | ring1

/-- The constraint exponent evaluates as `F` plus the constraint term, with the `𝔽₂` sum. -/
theorem copyExponent_eval {m h : ℕ} (F : DiagPhase (n + h + 1) m) (P : DiagPhase (n + h) m)
    (p : (Fin (n + h) → ZMod 2) → ZMod 2)
    (hP : ∀ v, P.eval v = (((p v).val : ℕ) : ZMod (2 ^ m)))
    (v : Fin (n + h) → ZMod 2) (z t : ZMod 2) :
    (copyExponent F P).eval (Fin.snoc (Fin.snoc v z) t)
      = F.eval (Fin.snoc v z)
        + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((t * (z + p v)).val : ℕ) : ZMod (2 ^ m)) := by
  unfold copyExponent
  rw [eval_add, eval_mul, eval_mul, eval_add, eval_C, eval_X, eval_X, eval_rename', eval_rename']
  have hF : (Fin.snoc (Fin.snoc v z) t : Fin (n + h + 1 + 1) → ZMod 2) ∘ Fin.castSucc
      = Fin.snoc v z := by
    funext i
    simp only [Function.comp_apply, Fin.snoc_castSucc]
  have hP' : (Fin.snoc (Fin.snoc v z) t : Fin (n + h + 1 + 1) → ZMod 2)
      ∘ (fun j : Fin (n + h) => j.castSucc.castSucc) = v := by
    funext i
    simp only [Function.comp_apply, Fin.snoc_castSucc]
  rw [hF, hP', hP, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last, two_pow_pred_mul_bits]

/-- **The gadget with both exponents as polynomials.** Where `P` takes bit values, the carrier state
of `copyExponent F P` at height `h + 2` denotes the state of `substLast F P` at height `h`. -/
theorem amp_copyExponent {m h : ℕ} (hm : 1 ≤ m) (F : DiagPhase (n + h + 1) m)
    (P : DiagPhase (n + h) m) (p : (Fin (n + h) → ZMod 2) → ZMod 2)
    (hP : ∀ v, P.eval v = (((p v).val : ℕ) : ZMod (2 ^ m)))
    (c : ℂ) (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2) :
    amp (⟨m, h + 1 + 1, copyExponent F P, c, L, x₀⟩ : KernelSumState n)
      = amp ⟨m, h, substLast F P, c, L, x₀⟩ :=
  amp_copy hm (copyExponent_eval F P p hP) (fun v => substLast_eval F P v (hP v)) c L x₀

/-- A variable has total degree at most one, over any coefficient ring. -/
theorem totalDegree_X_le {N m : ℕ} (i : Fin N) :
    (MvPolynomial.X i : DiagPhase N m).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_monomial_le _ _).trans (by simp)

/-- **The gadget's degree.** The constraint pair adds monomials of degree at most `2` and
`deg P + 1`, and reads `F` unchanged. -/
theorem totalDegree_copyExponent_le {m h : ℕ} (F : DiagPhase (n + h + 1) m)
    (P : DiagPhase (n + h) m) :
    (copyExponent F P).totalDegree ≤ max F.totalDegree (max 2 (P.totalDegree + 1)) := by
  unfold copyExponent
  refine (MvPolynomial.totalDegree_add _ _).trans
    (max_le_max (MvPolynomial.totalDegree_rename_le _ _) ?_)
  have hC := MvPolynomial.totalDegree_C (σ := Fin (n + h + 1 + 1)) ((2 : ZMod (2 ^ m)) ^ (m - 1))
  have hCt := (MvPolynomial.totalDegree_mul
    (MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) : DiagPhase (n + h + 1 + 1) m)
    (MvPolynomial.X (Fin.last (n + h + 1)))).trans
    (add_le_add hC.le (totalDegree_X_le (Fin.last (n + h + 1))))
  have hsum := (MvPolynomial.totalDegree_add
    (MvPolynomial.X (Fin.castSucc (Fin.last (n + h))) : DiagPhase (n + h + 1 + 1) m)
    (MvPolynomial.rename (fun j : Fin (n + h) => j.castSucc.castSucc) P)).trans
    (max_le_max (totalDegree_X_le _) (MvPolynomial.totalDegree_rename_le _ P))
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have := add_le_add hCt hsum
  omega

/-! ## The quartic row

At `n = 0`, `m = 1`: the phase `(−1)^{y₀y₁y₂y₃}` at height four, and the same state at height six
with `z = y₀y₁` named by the gadget. -/

/-- The quartic exponent `y₀y₁y₂y₃` at precision one. -/
noncomputable def quartic : DiagPhase (0 + 4) 1 :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3

/-- The exponent `z·y₂·y₃`, with `z` the fifth and last variable. -/
noncomputable def quarticRest : DiagPhase (0 + 4 + 1) 1 :=
  MvPolynomial.X (Fin.last (0 + 4)) * MvPolynomial.X (Fin.castSucc 2)
    * MvPolynomial.X (Fin.castSucc 3)

/-- The named product `y₀y₁`. -/
noncomputable def quarticName : DiagPhase (0 + 4) 1 :=
  MvPolynomial.X 0 * MvPolynomial.X 1

/-- The product of two bits read in `ZMod (2 ^ m)` is the bit of their product. -/
private theorem val_mul_bits {m : ℕ} (a b : ZMod 2) :
    ((a.val : ℕ) : ZMod (2 ^ m)) * ((b.val : ℕ) : ZMod (2 ^ m))
      = (((a * b).val : ℕ) : ZMod (2 ^ m)) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl,
      mul_zero, mul_one, Nat.cast_zero, Nat.cast_one]

/-- The named product takes bit values. -/
theorem quarticName_eval (v : Fin (0 + 4) → ZMod 2) :
    quarticName.eval v = (((v 0 * v 1).val : ℕ) : ZMod (2 ^ 1)) := by
  unfold quarticName
  rw [eval_mul, eval_X, eval_X, val_mul_bits]

/-- The quartic exponent is `z·y₂·y₃` at `z = y₀y₁`. -/
theorem quartic_eval (v : Fin (0 + 4) → ZMod 2) :
    quartic.eval v = quarticRest.eval (Fin.snoc v (v 0 * v 1)) := by
  unfold quartic quarticRest
  simp only [eval_mul, eval_X, Fin.snoc_last, Fin.snoc_castSucc]
  rw [← val_mul_bits (v 0) (v 1)]

/-- **The row.** The quartic phase at height four and its gadget presentation at height six denote
one state. -/
theorem amp_quartic_eq_gadget (c : ℂ) (L : Submodule (ZMod 2) (Pauli 0))
    (x₀ : Fin 0 → ZMod 2) :
    amp (⟨1, 4 + 1 + 1, copyExponent quarticRest quarticName, c, L, x₀⟩ : KernelSumState 0)
      = amp ⟨1, 4, quartic, c, L, x₀⟩ :=
  amp_copy le_rfl (copyExponent_eval quarticRest quarticName (fun v => v 0 * v 1) quarticName_eval)
    quartic_eval c L x₀

/-- The quartic exponent has degree four. -/
theorem totalDegree_quartic : quartic.totalDegree = 4 := by
  haveI : Fact (Nat.Prime (2 ^ 1)) := ⟨by rw [pow_one]; exact Nat.prime_two⟩
  unfold quartic
  have hX : ∀ i : Fin (0 + 4), (MvPolynomial.X i : DiagPhase (0 + 4) 1) ≠ 0 :=
    fun i => MvPolynomial.X_ne_zero i
  have h01 : (MvPolynomial.X 0 * MvPolynomial.X 1 : DiagPhase (0 + 4) 1) ≠ 0 :=
    mul_ne_zero (hX 0) (hX 1)
  have h012 : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 : DiagPhase (0 + 4) 1)
      ≠ 0 := mul_ne_zero h01 (hX 2)
  rw [MvPolynomial.totalDegree_mul_of_isDomain h012 (hX 3),
    MvPolynomial.totalDegree_mul_of_isDomain h01 (hX 2),
    MvPolynomial.totalDegree_mul_of_isDomain (hX 0) (hX 1),
    MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X,
    MvPolynomial.totalDegree_X]

/-- The gadget presentation of the quartic phase has degree at most three. -/
theorem totalDegree_quarticGadget_le :
    (copyExponent quarticRest quarticName).totalDegree ≤ 3 := by
  have hRest : quarticRest.totalDegree ≤ 3 := by
    unfold quarticRest
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 := (MvPolynomial.totalDegree_mul
      (MvPolynomial.X (Fin.last (0 + 4)) : DiagPhase (0 + 4 + 1) 1)
      (MvPolynomial.X (Fin.castSucc 2))).trans
      (add_le_add (totalDegree_X_le _) (totalDegree_X_le _))
    have := add_le_add h1 (totalDegree_X_le (m := 1) (Fin.castSucc (3 : Fin (0 + 4))))
    omega
  have hName : quarticName.totalDegree ≤ 2 := by
    unfold quarticName
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (add_le_add (totalDegree_X_le 0) (totalDegree_X_le 1))
  have := totalDegree_copyExponent_le quarticRest quarticName
  omega

/-! ## Axiom sweep -/

/-- info: 'FTQCLib.Explore.SquierModel.amp_copy' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_copy

/-- info: 'FTQCLib.Explore.SquierModel.amp_copyExponent' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_copyExponent

/-- info: 'FTQCLib.Explore.SquierModel.totalDegree_copyExponent_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalDegree_copyExponent_le

/-- info: 'FTQCLib.Explore.SquierModel.amp_quartic_eq_gadget' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_quartic_eq_gadget

/-- info: 'FTQCLib.Explore.SquierModel.totalDegree_quartic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalDegree_quartic

/-- info: 'FTQCLib.Explore.SquierModel.totalDegree_quarticGadget_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms totalDegree_quarticGadget_le

end FTQCLib.Explore.SquierModel

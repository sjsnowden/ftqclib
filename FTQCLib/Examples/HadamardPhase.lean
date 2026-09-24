/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardGate

/-! # H on a finer-than-Clifford phase: the character-sum carrier (frame-native, direct)

`applyHPinned`/`applyHFree` (`HadamardGate.lean`) do `H` directly only when the Hadamarded bit's phase is
Clifford, collapsing `H`'s two Walsh branches into one `KernelState`. Off that (a superposed bit carrying a
finer phase) the branches do not collapse and the output is a genuine two-term sum. This file gives the
frame-native, **direct** account: the state carries extra **summation variables** in its exponent, and `H`
on such a bit is a pure exponent rewrite — adjoin one summation variable, redirect the bit's `X_k` to it, add
the floor-level coupling `2^{m-1}·X_k·y`.

Mathematically the state is a **partial character sum over 𝔽₂**: the amplitude `Σ_y ω^{Q(w,y)}` (`ω` a
`2^m`-th root of unity) with the output bits `w` **free** and the `h` adjoined bits `y` **bound** (summed) —
a **Gauss sum** when `Q` is quadratic, the finite Weil/Gauss-sum territory the frame already lives in. (This
is the object physics calls a Feynman "sum over paths"; here it is the finite 𝔽₂ exponential sum it is.)

This is `H` done **directly** (rewrite the carrier), not by injection. It reuses only the direct primitives
(`hSignPoly`'s `2^{m-1}` coefficient, `realPhase`, the `bind₁` substitution family that `freezeAt` is built
from); it imports no `FTQCLib.Hilbert` and nothing from `Teleport/`.

**Relation to the floor eliminators.** On a height-zero floor the bound bit this rule adjoins is
eliminated on the spot: `hFloor` and `hadamard_floor_total` in
`FTQCLib/Examples/HadamardElimination.lean` return every H on a floor to height zero, so the free rule
is the general rule above the floor and the floor's H is `hFloor`. Where neither eliminator applies
the record is a value at height one, exact: `hFiner_not_kernelState` below is the instance,
`FTQCLib/Examples/ResidualBit.lean` the theorem. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Complex

variable {n : ℕ}

/-! ## The carrier -/

/-- A character-sum kernel state: a phase polynomial `Q` over `n` **free** (output) variables and `h`
**bound** (summation) variables, plus the support data `(L, x₀)` (unchanged from `KernelState`). Ordinary
`KernelState` is the `h = 0` case. -/
structure KernelSumState (n : ℕ) where
  m  : ℕ
  h  : ℕ
  Q  : DiagPhase (n + h) m
  c  : ℂ
  L  : Submodule (ZMod 2) (Pauli n)
  x₀ : Fin n → ZMod 2

/-- The on-support amplitude, summed over the `h` summation variables:
`(c / √2^h) · Σ_{y ∈ 𝔽₂^h} exp(i · realPhase Q (w ++ y))`. Frame-native (`realPhase` + `ℂ`), the same
`c·exp` shape as the `KernelState` amplitude. -/
noncomputable def ampCore (m h : ℕ) (Q : DiagPhase (n + h) m) (c : ℂ) (w : Fin n → ZMod 2) : ℂ :=
  (c / (Real.sqrt 2 : ℂ) ^ h) *
    ∑ y : Fin h → ZMod 2,
      Complex.exp (Complex.I * (DiagPhase.realPhase Q (Fin.append w y) : ℂ))

/-! ## `H` on bit `k` as a direct exponent rewrite (adjoin a summation variable) -/

/-- The exponent rewrite: adjoin one summation variable (the new last variable of `Fin ((n+h)+1)`), redirect the
output bit `k`'s variable to it, and add the coupling `2^{m-1}·X_k·y`. Pure `DiagPhase` (`bind₁` +
monomial `+`), the same substitution family as `freezeAt`. -/
noncomputable def hSumExp {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m) :
    DiagPhase ((n + h) + 1) m :=
  MvPolynomial.bind₁
      (fun j : Fin (n + h) =>
        if j = Fin.castAdd h k then MvPolynomial.X (Fin.last (n + h))
        else MvPolynomial.X j.castSucc)
      Q
    + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) *
        (MvPolynomial.X (Fin.castSucc (Fin.castAdd h k)) * MvPolynomial.X (Fin.last (n + h)))

/-- **`H` on an X-free bit carrying a finer phase (the new case).** Adjoin a summation variable (`h ↦ h+1`),
rewrite the exponent by `hSumExp`; the support `(L, x₀)` and `c` are unchanged (the `√2` is absorbed by the
`√2^h` normalization). -/
noncomputable def applyHFiner (k : Fin n) (S : KernelSumState n) : KernelSumState n where
  m  := S.m
  h  := S.h + 1
  Q  := hSumExp k S.Q
  c  := S.c
  L  := S.L
  x₀ := S.x₀

/-! ## The evaluation of `hSumExp` -/

/-- **Eval-bridge for `hSumExp`** (mirrors `freezeAt_eval`). Evaluating the rewritten exponent at a point
`z` over `Fin ((n+h)+1)` reads: `Q` evaluated with the output-`k` coordinate replaced by the new summation
value `z(last)` (the rest of `z` restricted along `castSucc`), plus the coupling `2^{m-1}·z_k·z_last`. -/
theorem hSumExp_eval {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m)
    (z : Fin ((n + h) + 1) → ZMod 2) :
    (hSumExp k Q).eval z
      = Q.eval (Function.update (fun j => z j.castSucc) (Fin.castAdd h k) (z (Fin.last (n + h))))
        + (2 : ZMod (2 ^ m)) ^ (m - 1)
            * ((z (Fin.castSucc (Fin.castAdd h k))).val : ZMod (2 ^ m))
            * ((z (Fin.last (n + h))).val : ZMod (2 ^ m)) := by
  unfold hSumExp DiagPhase.eval
  rw [map_add]
  congr 1
  · have hbind := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
      (DiagPhase.liftBinary z)
      (fun j : Fin (n + h) =>
        if j = Fin.castAdd h k then MvPolynomial.X (Fin.last (n + h))
        else MvPolynomial.X j.castSucc) Q
    simp only [MvPolynomial.aeval_eq_eval] at hbind
    rw [hbind]
    have hAB :
        (fun j : Fin (n + h) =>
          (MvPolynomial.eval (DiagPhase.liftBinary z))
            (if j = Fin.castAdd h k then MvPolynomial.X (Fin.last (n + h))
              else MvPolynomial.X j.castSucc : DiagPhase ((n + h) + 1) m))
          = DiagPhase.liftBinary
              (Function.update (fun j => z j.castSucc) (Fin.castAdd h k) (z (Fin.last (n + h)))) := by
      funext j
      by_cases hj : j = Fin.castAdd h k
      · subst hj
        simp [DiagPhase.liftBinary]
      · rw [if_neg hj]
        simp [DiagPhase.liftBinary, Function.update_apply, hj]
    rw [hAB]
  · simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, DiagPhase.liftBinary]
    ring

/-! ## The two branches -/

/-- The `p`-branch exponent (`p` = the value of the new summation variable): freeze the summation variable to `p`
in `hSumExp`, which turns the coupling into the frozen sign term `2^{m-1}·p·X_k` on the output. Staying a
polynomial (not an extracted `(-1)^{w_k}`) keeps the identity `exp`-free. -/
noncomputable def hBranch {h m : ℕ} (k : Fin n) (p : ZMod 2) (Q : DiagPhase (n + h) m) :
    DiagPhase (n + h) m :=
  freezeAt (Fin.castAdd h k) p Q
    + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1) * (p.val : ZMod (2 ^ m)))
        * MvPolynomial.X (Fin.castAdd h k)

/-- Evaluating `hSumExp` at an appended point `w ++ y'` equals evaluating the `y'(last)`-branch at
`w ++ init y'`. The polynomial form of one Walsh branch. -/
theorem hSumExp_eval_append {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m)
    (w : Fin n → ZMod 2) (y' : Fin (h + 1) → ZMod 2) :
    (hSumExp k Q).eval (@Fin.append n (h + 1) (ZMod 2) w y')
      = (hBranch k (y' (Fin.last h)) Q).eval (Fin.append w (Fin.init y')) := by
  rw [hSumExp_eval]
  have hlast : Fin.append w y' (Fin.last (n + h)) = y' (Fin.last h) := by
    have : (Fin.last (n + h)) = Fin.natAdd n (Fin.last h) := by
      apply Fin.ext; simp [Fin.last]
    rw [this, Fin.append_right]
  have hcastfun : (fun j => Fin.append w y' j.castSucc) = Fin.append w (Fin.init y') := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      have h1 : (Fin.castAdd h i).castSucc = Fin.castAdd (h + 1) i := by apply Fin.ext; simp
      rw [h1, Fin.append_left, Fin.append_left]
    · intro l
      have h2 : (Fin.natAdd n l).castSucc = Fin.natAdd n l.castSucc := by apply Fin.ext; simp
      rw [h2, Fin.append_right, Fin.append_right, Fin.init]
  have hcastk : Fin.append w y' (Fin.castSucc (Fin.castAdd h k)) = w k := by
    have h3 : Fin.castSucc (Fin.castAdd h k) = Fin.castAdd (h + 1) k := by apply Fin.ext; simp
    rw [h3, Fin.append_left]
  rw [hlast, hcastfun, hcastk, ← freezeAt_eval]
  unfold hBranch
  simp only [DiagPhase.eval, map_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, DiagPhase.liftBinary, Fin.append_left]
  ring

/-- Real-phase form of `hSumExp_eval_append`. -/
theorem realPhase_hSumExp_append {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m)
    (w : Fin n → ZMod 2) (y' : Fin (h + 1) → ZMod 2) :
    DiagPhase.realPhase (hSumExp k Q) (@Fin.append n (h + 1) (ZMod 2) w y')
      = DiagPhase.realPhase (hBranch k (y' (Fin.last h)) Q) (Fin.append w (Fin.init y')) := by
  unfold DiagPhase.realPhase
  rw [hSumExp_eval_append]

/-- Peel the last coordinate of a sum over `Fin (h+1) → ZMod 2`. -/
theorem sum_snoc_peel {M : Type*} [AddCommMonoid M] {h : ℕ}
    (F : (Fin (h + 1) → ZMod 2) → M) :
    (∑ y' : Fin (h + 1) → ZMod 2, F y')
      = ∑ p : ZMod 2, ∑ y : Fin h → ZMod 2, F (Fin.snoc y p) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ => ZMod 2)) F, Fintype.sum_prod_type]
  rfl

/-! ## The evaluation identity (H on a finer phase) -/

/-- **The character-sum Hadamard rule (frame-native, uniform in `Q`).** `applyHFiner k` on the carrier
amplitude is the `(1/√2)`-scaled sum over the two branches `hBranch k p`. Each branch is an `ampCore`
at one fewer summation variable, so this is `H` as a direct exponent rewrite — valid for finer-than-Clifford `Q`,
with no Hilbert Walsh transform. -/
theorem ampCore_applyHFiner {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m (h + 1) (hSumExp k Q) c w
      = (1 / (Real.sqrt 2 : ℂ)) * ∑ p : ZMod 2, ampCore m h (hBranch k p Q) c w := by
  unfold ampCore
  have hterm :
      (∑ y' : Fin (h + 1) → ZMod 2,
          Complex.exp (Complex.I *
            (DiagPhase.realPhase (hSumExp k Q) (@Fin.append n (h + 1) (ZMod 2) w y') : ℂ)))
        = ∑ y' : Fin (h + 1) → ZMod 2,
            Complex.exp (Complex.I *
              (DiagPhase.realPhase (hBranch k (y' (Fin.last h)) Q)
                (Fin.append w (Fin.init y')) : ℂ)) :=
    Finset.sum_congr rfl (fun y' _ => by rw [realPhase_hSumExp_append])
  rw [hterm, sum_snoc_peel]
  simp only [Fin.snoc_last, Fin.init_snoc]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [pow_succ]
  ring

/-- **Two-term form.** The `p = 0` branch plus the `p = 1` branch; the `p = 1` branch's frozen coupling
`2^{m-1}·X_k` is exactly the `(-1)^{w_k}` Walsh sign, absorbed into `hBranch`. -/
theorem ampCore_applyHFiner_two_term {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m) (c : ℂ)
    (w : Fin n → ZMod 2) :
    ampCore m (h + 1) (hSumExp k Q) c w
      = (1 / (Real.sqrt 2 : ℂ))
          * (ampCore m h (hBranch k 0 Q) c w + ampCore m h (hBranch k 1 Q) c w) := by
  rw [ampCore_applyHFiner]
  congr 1
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The carrier stays **one row**: each finer `H` grows the number of summation variables by one, so `t` finer Hadamards give
`h + t` summation variables in a single exponent (size `O(t)`); the exponential cost is paid
only in the `2^{h+t}`-term evaluation. -/
theorem applyHFiner_h_succ (k : Fin n) (S : KernelSumState n) :
    (applyHFiner k S).h = S.h + 1 := rfl

/-! ## The coupling is a level-2 (Clifford) correction -/

open MvPolynomial in
/-- **The coupling `H` adds prices at effective level 2** — a Clifford-level correction from the level
below. Its coefficient `2^{m-1}` is the coarsest dyadic (sign) value and it couples exactly two variables.
This is "a gate is a conditional rewrite corrected from the level below" made literal on the direct route:
the correction is level 2. -/
theorem hCouple_effectiveLevel {h m : ℕ} (k : Fin n) (hm : 1 ≤ m) :
    DiagPhase.effectiveLevel
        (C ((2 : ZMod (2 ^ m)) ^ (m - 1))
            * (MvPolynomial.X (Fin.castSucc (Fin.castAdd h k)) * MvPolynomial.X (Fin.last (n + h)))
          : DiagPhase ((n + h) + 1) m) = 2 := by
  set a := Fin.castSucc (Fin.castAdd h k)
  set b := Fin.last (n + h)
  have hab : a ≠ b := by
    intro he
    have hv : a.val = b.val := by rw [he]
    simp only [a, b, Fin.val_castSucc, Fin.val_castAdd, Fin.val_last] at hv
    omega
  have hval : ((2 : ZMod (2 ^ m)) ^ (m - 1)).val = 2 ^ (m - 1) := by
    have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by push_cast; ring
    rw [h2, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  have hcne : (2 : ZMod (2 ^ m)) ^ (m - 1) ≠ 0 := by
    rw [← ZMod.val_ne_zero, hval]; positivity
  have htwo : DiagPhase.twoAdicVal ((2 : ZMod (2 ^ m)) ^ (m - 1)) = m - 1 := by
    rw [DiagPhase.twoAdicVal_of_ne_zero hcne, hval, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have hmon :
      (C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * (MvPolynomial.X a * MvPolynomial.X b)
          : DiagPhase ((n + h) + 1) m)
        = monomial (Finsupp.single a 1 + Finsupp.single b 1) ((2 : ZMod (2 ^ m)) ^ (m - 1)) := by
    rw [show (MvPolynomial.X a : DiagPhase ((n + h) + 1) m) = monomial (Finsupp.single a 1) 1 from rfl,
      show (MvPolynomial.X b : DiagPhase ((n + h) + 1) m) = monomial (Finsupp.single b 1) 1 from rfl,
      monomial_mul, C_mul_monomial, one_mul, mul_one]
  rw [hmon, DiagPhase.effectiveLevel_monomial_eq hcne]
  unfold DiagPhase.effLevelMonom
  rw [htwo, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
  omega

/-! ## The Clifford collapse (recombine condition) -/

/-- **Clifford collapse (recombine condition).** When `Q` is free of the output bit `X_k` (both
freezings fix `Q` — the Clifford case, where the exchanged sign is the *only* `X_k`-dependence), the two
branches differ by **exactly** the Clifford sign `2^{m-1}·X_k`. Then the `p=0` and `p=1` amplitude terms
combine to `1 + (-1)^{w_k}`, which pins bit `k` to a single value: the character sum collapses to a single
`KernelState`, recovering `applyHFree`. -/
theorem hBranch_clifford {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m)
    (hf0 : freezeAt (Fin.castAdd h k) 0 Q = Q) (hf1 : freezeAt (Fin.castAdd h k) 1 Q = Q) :
    hBranch k 1 Q
      = hBranch k 0 Q
        + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * MvPolynomial.X (Fin.castAdd h k) := by
  unfold hBranch
  rw [hf0, hf1]
  have h1 : ((1 : ZMod 2)).val = 1 := by decide
  have h0 : ((0 : ZMod 2)).val = 0 := by decide
  rw [h1, h0]
  simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, map_zero, zero_mul, add_zero]

/-! ## The finer witness (not a single KernelState) -/

/-- Concrete evaluation of the Hadamarded T-phase exponent at `![a, b]`. -/
theorem hSumExp_X0_eval (a b : ZMod 2) :
    (hSumExp (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) 3)).eval (Fin.append ![a] ![b])
      = (b.val : ZMod 8) + 4 * (a.val : ZMod 8) * (b.val : ZMod 8) := by
  rw [hSumExp_eval]
  have e0 : (Fin.append ![a] ![b] : Fin 2 → ZMod 2) (Fin.castSucc (Fin.castAdd 0 0)) = a := by
    rw [show Fin.castSucc (Fin.castAdd 0 (0 : Fin 1)) = Fin.castAdd 1 (0 : Fin 1) from by
        apply Fin.ext; simp, Fin.append_left]
    rfl
  have e1 : (Fin.append ![a] ![b] : Fin 2 → ZMod 2) (Fin.last (1 + 0)) = b := by
    rw [show (Fin.last (1 + 0)) = Fin.natAdd 1 (0 : Fin 1) from by apply Fin.ext; simp,
      Fin.append_right]
    rfl
  have eupd : (Function.update (fun j => (Fin.append ![a] ![b] : Fin 2 → ZMod 2) j.castSucc)
      (Fin.castAdd 0 0) ((Fin.append ![a] ![b] : Fin 2 → ZMod 2) (Fin.last (1 + 0))))
      = (fun _ => b) := by
    funext j
    fin_cases j
    rw [e1]
    rfl
  rw [eupd, e0, e1]
  simp only [DiagPhase.eval, DiagPhase.liftBinary, MvPolynomial.eval_X]
  norm_num

/-- The real phase of the Hadamarded T-phase exponent at `![a,b]`. -/
theorem realPhase_hSumExp_X0 (a b : ZMod 2) :
    DiagPhase.realPhase (hSumExp (0 : Fin 1) (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
        (Fin.append ![a] ![b])
      = 2 * Real.pi * (((b.val : ZMod 8) + 4 * (a.val : ZMod 8) * (b.val : ZMod 8)).val : ℝ) / 8 := by
  unfold DiagPhase.realPhase
  rw [hSumExp_X0_eval]
  norm_num

/-- `normSq (1 + exp(iθ)) = 2 + 2·cos θ`. -/
theorem normSq_one_add_expI (θ : ℝ) :
    Complex.normSq (1 + Complex.exp (Complex.I * (θ : ℂ))) = 2 + 2 * Real.cos θ := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    mul_comm Complex.I (θ : ℂ), Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- **The finer witness.** For the T-phase input, `H` produces an amplitude of **non-constant modulus**
(`normSq` differs at `w = 0` vs `w = 1`), so it is **not any single `KernelState`** (those have constant
modulus `|c|` on support). It remains frame data — a `KernelSumState` / two-term character sum. -/
theorem hFiner_not_kernelState :
    ∃ w w' : Fin 1 → ZMod 2,
      Complex.normSq (ampCore 3 1 (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3)) 1 w)
        ≠ Complex.normSq (ampCore 3 1 (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3)) 1 w') := by
  refine ⟨![0], ![1], ?_⟩
  have key : ∀ a : ZMod 2,
      ampCore 3 1 (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3)) 1 ![a]
        = (1 / (Real.sqrt 2 : ℂ))
          * (Complex.exp (Complex.I *
                (DiagPhase.realPhase (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
                  (Fin.append ![a] ![0]) : ℂ))
             + Complex.exp (Complex.I *
                (DiagPhase.realPhase (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
                  (Fin.append ![a] ![1]) : ℂ))) := by
    intro a
    unfold ampCore
    rw [pow_one, one_div,
      show (Finset.univ : Finset (Fin 1 → ZMod 2)) = {![0], ![1]} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton, inv_eq_one_div]
  rw [key 0, key 1]
  have h00 : DiagPhase.realPhase (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
      (Fin.append ![0] ![0]) = 0 := by
    rw [realPhase_hSumExp_X0]
    have hv : (((0:ZMod 2).val:ZMod 8) + 4*((0:ZMod 2).val:ZMod 8)*((0:ZMod 2).val:ZMod 8)).val
      = 0 := by decide
    rw [hv]; norm_num
  have h01 : DiagPhase.realPhase (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
      (Fin.append ![0] ![1]) = 2 * Real.pi / 8 := by
    rw [realPhase_hSumExp_X0]
    have hv : (((1:ZMod 2).val:ZMod 8) + 4*((0:ZMod 2).val:ZMod 8)*((1:ZMod 2).val:ZMod 8)).val
      = 1 := by decide
    rw [hv]; norm_num
  have h10 : DiagPhase.realPhase (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
      (Fin.append ![1] ![0]) = 0 := by
    rw [realPhase_hSumExp_X0]
    have hv : (((0:ZMod 2).val:ZMod 8) + 4*((1:ZMod 2).val:ZMod 8)*((0:ZMod 2).val:ZMod 8)).val
      = 0 := by decide
    rw [hv]; norm_num
  have h11 : DiagPhase.realPhase (hSumExp 0 (MvPolynomial.X 0 : DiagPhase (1 + 0) 3))
      (Fin.append ![1] ![1]) = 2 * Real.pi * 5 / 8 := by
    rw [realPhase_hSumExp_X0]
    have hv : (((1:ZMod 2).val:ZMod 8) + 4*((1:ZMod 2).val:ZMod 8)*((1:ZMod 2).val:ZMod 8)).val
      = 5 := by decide
    rw [hv]; norm_num
  rw [h00, h01, h10, h11]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [Complex.normSq_mul, Complex.normSq_mul, normSq_one_add_expI, normSq_one_add_expI]
  have hs : Complex.normSq (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [map_div₀, Complex.normSq_one, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hc1 : Real.cos (2 * Real.pi / 8) = Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi / 8 = Real.pi / 4 from by ring, Real.cos_pi_div_four]
  have hc5 : Real.cos (2 * Real.pi * 5 / 8) = -(Real.sqrt 2 / 2) := by
    rw [show 2 * Real.pi * 5 / 8 = Real.pi + Real.pi / 4 from by ring, Real.cos_add, Real.cos_pi,
      Real.sin_pi, Real.cos_pi_div_four]
    ring
  rw [hs, hc1, hc5]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro heq
  nlinarith [heq, h2]

end FTQCLib.Frame.Walkthrough

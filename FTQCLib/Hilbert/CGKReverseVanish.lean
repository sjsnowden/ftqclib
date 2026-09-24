/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.CGKReverseGeneral

set_option linter.unusedSectionVars false

/-! # CGK reverse — Möbius coefficient vanishing for `|S| > k`

At level `k ≥ 1` of the dyadic hierarchy with diagonal
`D_g = diagonalGateEquiv g`, for every subset `S` with `|S| > k`, the
iterated Möbius coefficient `funcDerivPhaseSubset S g 0` is an integer
multiple of `2π`. Sharper than dyadicity mod 2π: exact `2π·ℤ`
vanishing.

Induction on `k`. **Base `k = 1`**: at level 1,
`exp(I · g v) = α · (-1)^{p.Z · v}`, so `(Δ_i g)(v)` satisfies
`exp(I · (Δ_i g)(v)) = (-1)^{(p.Z i).val}`, constant in `v`. Hence
`Δ_i g` is `ConstantMod2pi`. Applying `Δ_j` then `VanishesMod2pi`;
further `funcDerivPhase` preserves vanishing. **Step `k → k + 1`**:
descent at `{i}` reduces to IH on `Δ_i g` at level `k`, with
commutativity bridging back.

Anchors: CGK 2017 (arXiv:1608.06596) eq. (62) degree formula; the
descent theorem of `CGKReverseDyadic.lean`; the level-1 phased-Pauli
witness.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase BooleanMobius

variable {n : ℕ}

/-! ## The `VanishesMod2pi` and `ConstantMod2pi` predicates

These are the real-valued analogues of "this complex unit equals 1
identically" and "this complex unit is constant in `v`". -/

/-- A real-valued function `g` **vanishes mod 2π** if every value
`g v` is an integer multiple of `2π`. -/
def VanishesMod2pi (g : (Fin n → ZMod 2) → ℝ) : Prop :=
  ∀ v, ∃ kint : ℤ, g v = 2 * Real.pi * (kint : ℝ)

/-- A real-valued function `g` is **constant mod 2π** if there exists
a single real number `c` such that every `g v` differs from `c` by an
integer multiple of `2π`. -/
def ConstantMod2pi (g : (Fin n → ZMod 2) → ℝ) : Prop :=
  ∃ c : ℝ, ∀ v, ∃ kint : ℤ, g v = c + 2 * Real.pi * (kint : ℝ)

/-! ## Closure under `funcDerivPhase`

The discrete-derivative operator preserves `VanishesMod2pi` and turns
`ConstantMod2pi` into `VanishesMod2pi`. -/

/-- If `g` vanishes mod 2π, then `funcDerivPhase i g` also vanishes
mod 2π. -/
theorem VanishesMod2pi.funcDerivPhase {g : (Fin n → ZMod 2) → ℝ}
    (hg : VanishesMod2pi g) (i : Fin n) :
    VanishesMod2pi (funcDerivPhase i g) := by
  intro v
  rw [funcDerivPhase_apply]
  obtain ⟨k1, h1⟩ := hg (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
  obtain ⟨k2, h2⟩ := hg v
  refine ⟨k1 - k2, ?_⟩
  rw [h1, h2]
  push_cast
  ring

/-- If `g` is constant mod 2π, then `funcDerivPhase i g` vanishes mod
2π. -/
theorem ConstantMod2pi.funcDerivPhase {g : (Fin n → ZMod 2) → ℝ}
    (hg : ConstantMod2pi g) (i : Fin n) :
    VanishesMod2pi (funcDerivPhase i g) := by
  obtain ⟨c, hc⟩ := hg
  intro v
  rw [funcDerivPhase_apply]
  obtain ⟨k1, h1⟩ := hc (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
  obtain ⟨k2, h2⟩ := hc v
  refine ⟨k1 - k2, ?_⟩
  rw [h1, h2]
  push_cast
  ring

/-- If `g` vanishes mod 2π, then `funcDerivPhaseSubset S g` also
vanishes mod 2π for every `S`. -/
theorem VanishesMod2pi.funcDerivPhaseSubset {g : (Fin n → ZMod 2) → ℝ}
    (hg : VanishesMod2pi g) (S : Finset (Fin n)) :
    VanishesMod2pi (funcDerivPhaseSubset S g) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [funcDerivPhaseSubset_empty]
      exact hg
  | @insert i S hi ih =>
      rw [funcDerivPhaseSubset_insert hi]
      exact ih.funcDerivPhase i

/-! ## Extraction of integer offsets via `Complex.exp_eq_exp_iff_exists_int`

The key technical tool: if `exp(I · x) = exp(I · y)` then `x - y ∈
2π·ℤ`. -/

/-- If `exp(I · x) = exp(I · y)`, then `x = y + 2π · k` for some
integer `k`. -/
private theorem real_eq_of_exp_eq {x y : ℝ}
    (h : Complex.exp (Complex.I * (x : ℂ)) = Complex.exp (Complex.I * (y : ℂ))) :
    ∃ kint : ℤ, x = y + 2 * Real.pi * (kint : ℝ) := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  -- hk: I · x = I · y + k · (2π · I).
  refine ⟨k, ?_⟩
  -- Equate imaginary parts.
  have h_re_eq : (Complex.I * (x : ℂ)).im
                = (Complex.I * (y : ℂ)
                    + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im := by
    rw [hk]
  have hLx : (Complex.I * (x : ℂ)).im = x := by
    rw [Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hLy : (Complex.I * (y : ℂ)).im = y := by
    rw [Complex.mul_im]
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hk_term :
      ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).im = (k : ℝ) * (2 * Real.pi) := by
    rw [Complex.mul_im]
    have h_k_re : (k : ℂ).re = (k : ℝ) := Complex.intCast_re k
    have h_k_im : (k : ℂ).im = 0 := Complex.intCast_im k
    have h_2pi_I_re : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I).re = 0 := by
      rw [Complex.mul_re]
      simp [Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
    have h_2pi_I_im : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
      rw [Complex.mul_im]
      simp [Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
    rw [h_k_re, h_k_im, h_2pi_I_re, h_2pi_I_im, mul_zero, add_zero]
  rw [Complex.add_im, hLx, hLy, hk_term] at h_re_eq
  linarith

/-! ## Level-1 first-derivative is constant mod 2π -/

/-- **Parity lemma.** `zDotVal p (v + e_i) + zDotVal p v` has the same
parity as `(p.Z i).val`, so `(-1)^{...}` collapses to `(-1)^{(p.Z i).val}`
(independent of `v`). -/
private theorem neg_one_pow_zDot_sum (p : Pauli n) (i : Fin n)
    (v : Fin n → ZMod 2) :
    (-1 : ℂ) ^ (zDotVal p (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
                  + zDotVal p v)
      = (-1 : ℂ) ^ (p.Z i).val := by
  have h_sdiff_erase : (Finset.univ : Finset (Fin n)) \ {i}
                    = Finset.univ.erase i := by
    ext j
    simp [Finset.mem_erase]
  have h_mod_eq :
      (zDotVal p (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
        + zDotVal p v) % 2 = (p.Z i).val % 2 := by
    -- Rewrite zDotVal p (v + e_i): the only differing term is index i.
    have h_zdot_v' :
        zDotVal p (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
          = (p.Z i).val * ((v i + 1 : ZMod 2)).val
            + ∑ j ∈ Finset.univ.erase i, (p.Z j).val * (v j).val := by
      unfold zDotVal
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)]
      have h_i_term :
          (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) i
            = v i + 1 := by
        simp only [Pi.add_apply, Pi.single_eq_same]
      rw [h_i_term]
      rw [h_sdiff_erase]
      have h_other_term :
          ∑ j ∈ Finset.univ.erase i,
              (p.Z j).val *
                ((v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) j).val
            = ∑ j ∈ Finset.univ.erase i, (p.Z j).val * (v j).val := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_erase] at hj
        have h_single_zero :
            (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j = 0 := by
          have hij : j ≠ i := hj.1
          simp [Pi.single, Function.update, hij]
        have h_eq : (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)) j
                  = v j := by
          simp only [Pi.add_apply, h_single_zero, add_zero]
        rw [h_eq]
      rw [h_other_term]
      ring
    have h_zdot_v :
        zDotVal p v = (p.Z i).val * (v i).val
                      + ∑ j ∈ Finset.univ.erase i, (p.Z j).val * (v j).val := by
      unfold zDotVal
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)]
      rw [h_sdiff_erase]
      ring
    rw [h_zdot_v', h_zdot_v]
    have h_sum_one : ((v i + 1 : ZMod 2)).val + (v i).val = 1 := by
      have h_val : v i = 0 ∨ v i = 1 := by
        have h_all : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        exact h_all _
      rcases h_val with h0 | h1
      · rw [h0]
        rw [show (0 + 1 : ZMod 2) = 1 from by decide]
        rw [ZMod.val_one, ZMod.val_zero]
      · rw [h1]
        rw [show (1 + 1 : ZMod 2) = 0 from by decide]
        rw [ZMod.val_zero, ZMod.val_one]
    -- Massage the LHS to extract a factor of 2.
    have h_lhs_eq :
        (p.Z i).val * ((v i + 1 : ZMod 2)).val
          + ∑ j ∈ Finset.univ.erase i, (p.Z j).val * (v j).val
          + ((p.Z i).val * (v i).val
              + ∑ j ∈ Finset.univ.erase i, (p.Z j).val * (v j).val)
          = (p.Z i).val * (((v i + 1 : ZMod 2)).val + (v i).val)
            + 2 * ∑ j ∈ Finset.univ.erase i, (p.Z j).val * (v j).val := by
      ring
    rw [h_lhs_eq, h_sum_one, Nat.mul_one]
    rw [Nat.add_mul_mod_self_left]
  -- Now use h_mod_eq to conclude (-1)^N = (-1)^((p.Z i).val).
  have hN := zDotVal p (v + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2))
               + zDotVal p v
  -- Use Nat.div_add_mod: N = 2 · (N/2) + (N mod 2).
  -- (-1)^N = ((-1)^2)^(N/2) · (-1)^(N mod 2) = 1 · (-1)^(N mod 2) = (-1)^(N mod 2).
  have h_pow_eq : ∀ N : ℕ, (-1 : ℂ) ^ N = (-1 : ℂ) ^ (N % 2) := by
    intro N
    conv_lhs => rw [← Nat.div_add_mod N 2]
    rw [pow_add, pow_mul]
    simp [show ((-1 : ℂ)) ^ 2 = 1 from by ring]
  rw [h_pow_eq, h_pow_eq (p.Z i).val, h_mod_eq]

/-- **Level-1 first derivative is constant mod 2π.** At level 1 of the
dyadic hierarchy with diagonal `D_g`, for every `i : Fin n` the
discrete derivative `funcDerivPhase i g` is constant mod 2π. -/
theorem funcDerivPhase_constantMod2pi_of_level_one
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g))
    (i : Fin n) :
    ConstantMod2pi (funcDerivPhase i g) := by
  -- Unpack the level-1 hypothesis.
  generalize hk_eq : (1 : ℕ) = klvl at h_hier
  cases h_hier with
  | base hU =>
      obtain ⟨α, p, hα_dy, hα⟩ := hU
      have hpX : p.X = 0 :=
        Pauli_X_zero_of_diagonal_phasedPauli rfl hα
      -- Step 1: For every w, exp(I · g w) = α · (-1)^{zDotVal p w}.
      have h_apply : ∀ w : Fin n → ZMod 2,
          Complex.exp (Complex.I * (g w : ℂ))
            = (α : ℂ) * (-1 : ℂ) ^ (zDotVal p w) := by
        intro w
        have h_apply_lin :
            (diagonalGateEquiv g) (computational w) =
              (α : ℂ) • (pauliOperator p) (computational w) := by
          have h := congrArg
            (fun (L : QubitSpace n →ₗ[ℂ] QubitSpace n) => L (computational w))
            hα
          simp only [LinearEquiv.coe_coe, LinearMap.smul_apply] at h
          exact h
        rw [diagonalGateEquiv_apply, diagonalGate_computational,
            pauliOperator_computational, hpX, add_zero] at h_apply_lin
        have h_eval :
            (Complex.exp (Complex.I * (g w : ℂ)) • computational w) w =
              ((α : ℂ) • (-1 : ℂ) ^ (zDotVal p w) • computational w) w :=
          congrFun h_apply_lin w
        simp only [Pi.smul_apply, computational_self, smul_eq_mul, mul_one]
          at h_eval
        exact h_eval
      -- Step 2: identify the constant `c` for `ConstantMod2pi`.
      -- The constant is `funcDerivPhase i g 0`, but we can pick any
      -- specific constant `c`. We use `c = funcDerivPhase i g 0`.
      refine ⟨funcDerivPhase i g 0, ?_⟩
      intro v
      -- Show: exp(I · funcDerivPhase i g v) = exp(I · funcDerivPhase i g 0).
      -- Both sides equal (-1)^{(p.Z i).val}.
      have h_exp_eq :
          Complex.exp (Complex.I * ((funcDerivPhase i g v : ℝ) : ℂ))
            = Complex.exp (Complex.I * ((funcDerivPhase i g 0 : ℝ) : ℂ)) := by
        -- Reduce each side to (-1)^{(p.Z i).val} via the parity lemma.
        have h_each : ∀ w,
            Complex.exp (Complex.I * ((funcDerivPhase i g w : ℝ) : ℂ))
              = (-1 : ℂ) ^ (p.Z i).val := by
          intro w
          rw [funcDerivPhase_apply]
          -- exp(I · (g w' - g w)) = exp(I · g w') · exp(-I · g w).
          set w' := w + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) with hw'
          have h_split :
              Complex.exp (Complex.I * ((g w' - g w : ℝ) : ℂ))
                = Complex.exp (Complex.I * (g w' : ℂ))
                  * Complex.exp (-(Complex.I * (g w : ℂ))) := by
            rw [show Complex.I * ((g w' - g w : ℝ) : ℂ)
                  = Complex.I * (g w' : ℂ) + (-(Complex.I * (g w : ℂ))) from by
                push_cast; ring]
            rw [Complex.exp_add]
          rw [h_split, h_apply w']
          rw [show -(Complex.I * (g w : ℂ)) = -Complex.I * (g w : ℂ) from by ring]
          have h_exp_neg :
              Complex.exp (-Complex.I * (g w : ℂ))
                = (Complex.exp (Complex.I * (g w : ℂ)))⁻¹ := by
            rw [show -Complex.I * (g w : ℂ) = -(Complex.I * (g w : ℂ)) from by ring]
            exact Complex.exp_neg _
          rw [h_exp_neg, h_apply w]
          have hα_ne : (α : ℂ) ≠ 0 := α.ne_zero
          rw [mul_inv]
          have h_inv_neg :
              ((-1 : ℂ) ^ zDotVal p w)⁻¹ = (-1 : ℂ) ^ zDotVal p w := by
            have h_sq : ((-1 : ℂ) ^ zDotVal p w) * ((-1 : ℂ) ^ zDotVal p w) = 1 := by
              rw [← pow_add, ← two_mul, pow_mul]
              norm_num
            exact (eq_inv_of_mul_eq_one_left h_sq).symm
          rw [h_inv_neg]
          rw [show (α : ℂ) * (-1 : ℂ) ^ zDotVal p w' *
                ((α : ℂ)⁻¹ * (-1 : ℂ) ^ zDotVal p w)
                = (α : ℂ) * (α : ℂ)⁻¹ *
                  ((-1 : ℂ) ^ zDotVal p w' * (-1 : ℂ) ^ zDotVal p w)
                from by ring]
          rw [mul_inv_cancel₀ hα_ne, one_mul]
          rw [← pow_add]
          rw [hw']
          exact neg_one_pow_zDot_sum p i w
        rw [h_each v, h_each 0]
      -- Step 3: extract the integer offset.
      obtain ⟨kint, h_eq⟩ := real_eq_of_exp_eq h_exp_eq
      exact ⟨kint, h_eq⟩
  | @step kpred _ h =>
      have hk0 : kpred = 0 := by omega
      subst hk0
      cases h 0

/-! ## Level-1 vanishing for `|S| ≥ 2`

Combining `funcDerivPhase_constantMod2pi_of_level_one` with closure of
`VanishesMod2pi`, we obtain that at level 1, for `|S| ≥ 2`, the
iterated derivative `funcDerivPhaseSubset S g` vanishes mod 2π
identically (in particular at `0`). -/

/-- **Level-1 vanishing for `|S| ≥ 2`.** At level 1 of the dyadic
hierarchy, for every `S` with `|S| ≥ 2`,
`funcDerivPhaseSubset S g v ∈ 2π · ℤ` for every `v`. -/
theorem funcDerivPhaseSubset_vanish_of_level_one
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g))
    {S : Finset (Fin n)} (h_card : 2 ≤ S.card) :
    VanishesMod2pi (funcDerivPhaseSubset S g) := by
  classical
  -- |S| ≥ 2 means we can pick two distinct elements. Take i ∈ S, j ∈ S.erase i.
  have h_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := h_nonempty
  set T := S.erase i with hT_def
  have hi_notin_T : i ∉ T := Finset.notMem_erase i S
  have hT_card : T.card = S.card - 1 := Finset.card_erase_of_mem hi
  have hT_nonempty : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    rw [Finset.card_eq_zero.mpr h_empty] at hT_card
    omega
  obtain ⟨j, hj⟩ := hT_nonempty
  set U := T.erase j with hU_def
  have hj_notin_U : j ∉ U := Finset.notMem_erase j T
  -- S = insert i (insert j U) (with j ∉ U, i ∉ insert j U).
  have h_T_eq : T = insert j U := by
    rw [hU_def, Finset.insert_erase hj]
  have hi_notin_insert : i ∉ insert j U := by
    rw [← h_T_eq]; exact hi_notin_T
  have h_S_eq : S = insert i (insert j U) := by
    rw [← h_T_eq, hT_def, Finset.insert_erase hi]
  rw [h_S_eq]
  rw [funcDerivPhaseSubset_insert hi_notin_insert]
  -- Goal: VanishesMod2pi (funcDerivPhase i (funcDerivPhaseSubset (insert j U) g)).
  -- Rewrite: funcDerivPhaseSubset (insert j U) = funcDerivPhase j (funcDerivPhaseSubset U).
  rw [funcDerivPhaseSubset_insert hj_notin_U]
  -- Goal: VanishesMod2pi (funcDerivPhase i (funcDerivPhase j (funcDerivPhaseSubset U g))).
  -- Swap funcDerivPhase i, j past funcDerivPhaseSubset U, then use
  -- ConstantMod2pi (funcDerivPhase j g) → vanish.
  have h_swap : funcDerivPhase i (funcDerivPhase j (funcDerivPhaseSubset U g))
              = funcDerivPhaseSubset U (funcDerivPhase i (funcDerivPhase j g)) := by
    -- First: funcDerivPhase j (funcDerivPhaseSubset U g)
    --        = funcDerivPhaseSubset U (funcDerivPhase j g)
    --      by commutativity (induction on U).
    have h_swap_j : funcDerivPhase j (funcDerivPhaseSubset U g)
                  = funcDerivPhaseSubset U (funcDerivPhase j g) := by
      classical
      induction U using Finset.induction_on with
      | empty =>
          rw [funcDerivPhaseSubset_empty, funcDerivPhaseSubset_empty]
      | @insert k V hk ih =>
          rw [funcDerivPhaseSubset_insert hk, funcDerivPhaseSubset_insert hk]
          rw [← ih]
          exact funcDerivPhase_comm j k _
    rw [h_swap_j]
    -- Now: funcDerivPhase i (funcDerivPhaseSubset U (funcDerivPhase j g))
    --      = funcDerivPhaseSubset U (funcDerivPhase i (funcDerivPhase j g)).
    classical
    induction U using Finset.induction_on with
    | empty =>
        rw [funcDerivPhaseSubset_empty, funcDerivPhaseSubset_empty]
    | @insert k V hk ih =>
        rw [funcDerivPhaseSubset_insert hk, funcDerivPhaseSubset_insert hk]
        rw [← ih]
        exact funcDerivPhase_comm i k _
  rw [h_swap]
  -- Goal: VanishesMod2pi (funcDerivPhaseSubset U (funcDerivPhase i (funcDerivPhase j g))).
  apply VanishesMod2pi.funcDerivPhaseSubset
  -- Goal: VanishesMod2pi (funcDerivPhase i (funcDerivPhase j g)).
  -- This follows from ConstantMod2pi (funcDerivPhase j g) at level 1.
  exact (funcDerivPhase_constantMod2pi_of_level_one h_hier j).funcDerivPhase i

/-! ## The main theorem

By induction on `k`, the iterated Möbius coefficient
`funcDerivPhaseSubset S g 0` vanishes mod 2π whenever `|S| > k`. -/

/-- **The vanishing theorem.** At level `k ≥ 1` of the dyadic
hierarchy with diagonal `D_g`, for every subset `S` with `|S| > k`,
the Möbius coefficient `funcDerivPhaseSubset S g 0` is an integer
multiple of `2π`.

This is the sharper form of dyadicity at the top of the hierarchy
descent: not just dyadic-rational residue, but exact `2π·ℤ` vanishing.
The CGK 2017 degree formula at `p = 2` predicts a polynomial of
degree ≤ `k`, which is exactly what `|S| > k` ⇒ coefficient vanishes
expresses.

Proof: induction on `k`. The base case `k = 1` uses the level-1
first-derivative-constant lemma plus closure of `VanishesMod2pi` under
iterated `funcDerivPhase`. The inductive step uses the descent
theorem to land at level `k`, then commutativity to bridge to the
inductive hypothesis. -/
theorem funcDerivPhaseSubset_vanish_mod_2pi_of_card_gt_level
    {n k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    {S : Finset (Fin n)} (h_card : k < S.card) :
    ∃ kint : ℤ, funcDerivPhaseSubset S g 0 = 2 * Real.pi * (kint : ℝ) := by
  induction k generalizing g S with
  | zero => omega
  | succ k' ih =>
      by_cases h_k'_zero : k' = 0
      · -- Base case: k = 1.
        subst h_k'_zero
        have h_card_ge_two : 2 ≤ S.card := h_card
        have h_vanish :=
          funcDerivPhaseSubset_vanish_of_level_one h_hier h_card_ge_two
        exact h_vanish 0
      · -- Inductive step: k = k' + 1 with k' ≥ 1.
        have h_k'_pos : 1 ≤ k' := Nat.one_le_iff_ne_zero.mpr h_k'_zero
        classical
        -- Pick any i ∈ S (S is nonempty since |S| > k' + 1 ≥ 2 > 0).
        have h_S_pos : 0 < S.card := by omega
        have h_S_nonempty : S.Nonempty := Finset.card_pos.mp h_S_pos
        obtain ⟨i, hi⟩ := h_S_nonempty
        set T := S.erase i with hT_def
        have hi_notin_T : i ∉ T := Finset.notMem_erase i S
        have h_T_card : T.card = S.card - 1 := Finset.card_erase_of_mem hi
        have h_T_card_gt : k' < T.card := by omega
        have h_S_eq : S = insert i T := by
          rw [hT_def, Finset.insert_erase hi]
        -- Descent at {i}: D_{Δ_i g} at level k'.
        have h_card_lt : ({i} : Finset (Fin n)).card < k' + 1 := by
          rw [Finset.card_singleton]; omega
        have h_descent :=
          diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
            g h_hier h_card_lt
        have h_level : (k' + 1 : ℕ) - ({i} : Finset (Fin n)).card = k' := by
          rw [Finset.card_singleton]; omega
        rw [h_level, funcDerivPhaseSubset_singleton] at h_descent
        -- h_descent : IsCliffordHierarchyDyadic k' (D_{Δ_i g}).
        -- Apply IH on T and Δ_i g.
        have h_ih := ih h_k'_pos h_descent h_T_card_gt
        -- h_ih : ∃ kint, funcDerivPhaseSubset T (funcDerivPhase i g) 0 = 2π · kint.
        -- Rewrite the goal via commutativity.
        rw [h_S_eq, funcDerivPhaseSubset_insert hi_notin_T]
        -- Goal: ∃ kint, funcDerivPhase i (funcDerivPhaseSubset T g) 0 = 2π · kint.
        have h_swap : funcDerivPhase i (funcDerivPhaseSubset T g)
                    = funcDerivPhaseSubset T (funcDerivPhase i g) := by
          classical
          induction T using Finset.induction_on with
          | empty =>
              rw [funcDerivPhaseSubset_empty, funcDerivPhaseSubset_empty]
          | @insert j U hj ih_T =>
              rw [funcDerivPhaseSubset_insert hj, funcDerivPhaseSubset_insert hj]
              rw [← ih_T]
              exact funcDerivPhase_comm i j _
        rw [h_swap]
        exact h_ih

/-- **Level-1 vanishing at every input.** Restatement of
`funcDerivPhaseSubset_vanish_of_level_one` in `(kint : ℤ)` form. -/
theorem funcDerivPhaseSubset_vanish_all_v_of_level_one
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g))
    {S : Finset (Fin n)} (h_card : 2 ≤ S.card) (v : Fin n → ZMod 2) :
    ∃ kint : ℤ, funcDerivPhaseSubset S g v = 2 * Real.pi * (kint : ℝ) :=
  funcDerivPhaseSubset_vanish_of_level_one h_hier h_card v

end FTQCLib.Hilbert

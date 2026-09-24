/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.ProjectiveHierarchy

set_option linter.unusedSectionVars false
set_option linter.style.whitespace false

/-! # Projective CGK reverse — strict `effectiveLevel ≤ k` bound

`ProjectiveHierarchy.lean` sets up the projective framework:
the constant-term-zeroed polynomial witness with `totalDegree ≤ k` and
`coeff 0 = 0`. The remaining obstacle to the strict level bound is
the per-`S` precision of the non-constant Möbius coefficients
`c_S = funcDerivPhaseSubset S g 0`: the loose uniform-precision lift
allows `m` to grow beyond `k`.

This file proves the strict bound via a **precision-by-level**
induction. The CGK precision-by-level statement at `p = 2` is:

  for non-empty `S` with `|S| ≤ k`,
    `funcDerivPhaseSubset S g 0` is dyadic mod 2π at precision
    **at most** `k - |S| + 1`.

The proof is by induction on `k`. The substantive content is the
mod-2 halving trick (`Δ_i Δ_i g = -2 · Δ_i g`, `CGKReverseLevel3.lean`), applied
recursively: each descent step both cuts the level by one and
halves a precision-relevant relation. We package the precision-
bounded variant of `IsDyadicMod2pi` as `IsDyadicMod2piAtPrecision`,
prove the structural closures (`add`, `neg`, `sub`, `half`,
`mono`), then run the induction.

## What this file delivers

* **`IsDyadicMod2piAtPrecision N x`** — a precision-bounded version
  of `IsDyadicMod2pi`. Closures: `add`, `neg`, `sub`, `half` (cuts
  precision by 1), `mono` (loosen precision).
* **`mobiusCoeff_precision_bound`** — for `k ≥ 1` and non-empty `S`
  with `|S| ≤ k`, the Möbius coefficient `c_S` is dyadic at
  precision `≤ k - |S| + 1`.
* **`cgk_reverse_dyadic_poly_projective_effectiveLevel`** — the
  strict bound: there is `P : DiagPhase n k` with `ScalarEquiv U
  (diagonalGateEquiv (realPhase P))`, `coeff 0 = 0`,
  `effectiveLevel P ≤ k`.

The `IsDyadicMod2pi (f 0)` hypothesis is DROPPED in the main
theorem: ScalarEquiv anchoring zeros the global phase factor `g(0)`
automatically.

## Anchors

* CGK 2017 (arXiv:1608.06596) §III, eq. (62): `w = (m-1) + d`.
* The mod-2 halving identity (`CGKReverseLevel3.lean`,
  `funcDerivPhase_self_zero`).
* `mobiusCoeff_dyadic_mod_2pi_level_k` (`CGKReverseGeneral.lean`).
* `funcDerivPhaseSubset_vanish_mod_2pi_of_card_gt_level` (`CGKReverseVanish.lean`).
* The `ProjectiveHierarchy.lean` infrastructure.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Hierarchy Complex DiagPhase BooleanMobius

variable {n : ℕ}

/-! ## Precision-bounded dyadic-mod-2π predicate

`IsDyadicMod2piAtPrecision N x` says: there is a representation of
`x` as `2π · c.val / 2^N + 2π · k` at precision exactly `N`. Unlike
`IsDyadicMod2pi`, the precision is fixed (not existential), so we
can track it through compositions.

The structural lemmas mirror those for `IsDyadicMod2pi`:
* `add`: precision = max of the two.
* `neg`: precision unchanged.
* `sub`: precision = max.
* `half`: halving costs 1 bit of precision.
* `mono`: loosen precision (every precision-`N` representation lifts
  to precision `N'` for `N' ≥ N`). -/

/-- A real number `x` is **dyadic mod 2π at precision `N`** if it
admits a representation `2π · c.val / 2^N + 2π · k` for some
`c : ZMod (2^N)` and `k : ℤ`. -/
def IsDyadicMod2piAtPrecision (N : ℕ) (x : ℝ) : Prop :=
  ∃ (c : ZMod (2 ^ N)) (kint : ℤ),
    x = 2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ N + 2 * Real.pi * (kint : ℝ)

/-- Precision-bounded dyadicity implies dyadicity (forgetting precision). -/
theorem IsDyadicMod2piAtPrecision.toIsDyadicMod2pi
    {N : ℕ} {x : ℝ} (h : IsDyadicMod2piAtPrecision N x) :
    IsDyadicMod2pi x := by
  obtain ⟨c, k, hx⟩ := h
  exact ⟨N, c, k, hx⟩

/-- Zero is dyadic at every precision. -/
theorem IsDyadicMod2piAtPrecision.zero (N : ℕ) :
    IsDyadicMod2piAtPrecision N 0 := by
  refine ⟨0, 0, ?_⟩
  simp

/-- Any integer multiple of 2π is dyadic at every precision. -/
theorem IsDyadicMod2piAtPrecision.int_mul_two_pi (N : ℕ) (k : ℤ) :
    IsDyadicMod2piAtPrecision N (2 * Real.pi * (k : ℝ)) := by
  refine ⟨0, k, ?_⟩
  simp

/-- **Monotonicity in precision.** A precision-`N` representation lifts
to any `N' ≥ N`. The trick: multiply both the numerator and the power
of two by `2^(N' - N)`. -/
theorem IsDyadicMod2piAtPrecision.mono {N N' : ℕ} {x : ℝ}
    (h : IsDyadicMod2piAtPrecision N x) (hNN' : N ≤ N') :
    IsDyadicMod2piAtPrecision N' x := by
  obtain ⟨c, kint, hx⟩ := h
  set Δ := N' - N with hΔ_def
  have hΔ_eq : N + Δ = N' := by rw [hΔ_def]; omega
  -- The new residue is c.val * 2^Δ in ZMod 2^N'.
  have h_bound : (c.val * 2 ^ Δ) < 2 ^ N' := by
    have h_cv_lt : c.val < 2 ^ N := ZMod.val_lt c
    have h_pow_split : (2 : ℕ) ^ N' = 2 ^ N * 2 ^ Δ := by
      rw [← pow_add, hΔ_eq]
    rw [h_pow_split]
    exact Nat.mul_lt_mul_of_pos_right h_cv_lt (Nat.two_pow_pos Δ)
  refine ⟨((c.val * 2 ^ Δ : ℕ) : ZMod (2 ^ N')), kint, ?_⟩
  have h_val_eq : (((c.val * 2 ^ Δ : ℕ) : ZMod (2 ^ N'))).val
                = c.val * 2 ^ Δ :=
    ZMod.val_natCast_of_lt h_bound
  rw [h_val_eq, hx]
  have h_pow_pos_N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h_pow_ne_N : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h_pow_pos_N
  have h_pow_pos_N' : (0 : ℝ) < (2 : ℝ) ^ N' := by positivity
  have h_pow_ne_N' : (2 : ℝ) ^ N' ≠ 0 := ne_of_gt h_pow_pos_N'
  have h_pow_split_real : (2 : ℝ) ^ N' = (2 : ℝ) ^ N * (2 : ℝ) ^ Δ := by
    rw [← pow_add, hΔ_eq]
  push_cast
  rw [h_pow_split_real]
  field_simp

/-- **Closure under addition.** Sum of two precision-`N` representations
admits a precision-`N` representation. -/
theorem IsDyadicMod2piAtPrecision.add {N : ℕ} {x y : ℝ}
    (hx : IsDyadicMod2piAtPrecision N x)
    (hy : IsDyadicMod2piAtPrecision N y) :
    IsDyadicMod2piAtPrecision N (x + y) := by
  obtain ⟨cx, kx, hxeq⟩ := hx
  obtain ⟨cy, ky, hyeq⟩ := hy
  -- The new residue is cx + cy in ZMod 2^N; the new offset is
  -- kx + ky + (carry), where the carry tracks the modular reduction.
  set c := cx + cy with hc_def
  set N0 : ℕ := cx.val + cy.val with hN0_def
  -- (cx + cy).val differs from cx.val + cy.val by a multiple of 2^N.
  have h_dvd : ((2 ^ N : ℕ) : ℤ) ∣ ((c.val : ℤ) - (N0 : ℤ)) := by
    rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have h1 : ((c.val : ℕ) : ZMod (2 ^ N)) = c := ZMod.natCast_zmod_val c
    have h2 : ((cx.val : ℕ) : ZMod (2 ^ N)) = cx := ZMod.natCast_zmod_val cx
    have h3 : ((cy.val : ℕ) : ZMod (2 ^ N)) = cy := ZMod.natCast_zmod_val cy
    rw [hN0_def]
    push_cast
    rw [h1, h2, h3, hc_def]
    ring
  obtain ⟨J, hJ⟩ := h_dvd
  refine ⟨c, kx + ky - J, ?_⟩
  rw [hxeq, hyeq]
  -- Need: cx.val + cy.val + ... = c.val + ...
  -- c.val = cx.val + cy.val + 2^N · J, where J ≤ 0 typically.
  -- So (c.val)/2^N = (cx.val + cy.val)/2^N + J.
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h_pow_ne : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h_pow_pos
  have h_real :
      ((c.val : ℝ)) - ((N0 : ℝ)) = ((2 ^ N : ℕ) : ℝ) * (J : ℝ) := by
    have h_cast : (((c.val : ℤ) - (N0 : ℤ)) : ℝ)
                = ((((2 ^ N : ℕ) : ℤ) * J) : ℝ) := by
      exact_mod_cast hJ
    push_cast at h_cast
    push_cast
    linarith
  have h_pow_real : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; rfl
  rw [h_pow_real] at h_real
  have h_N0_real : (N0 : ℝ) = (cx.val : ℝ) + (cy.val : ℝ) := by
    rw [hN0_def]; push_cast; ring
  rw [h_N0_real] at h_real
  push_cast
  field_simp
  linarith

/-- **Closure under negation.** Use the witness from
`IsDyadicMod2pi.neg`: `(-c).val = 2^N - c.val` (when `c ≠ 0`), and
we shift the integer offset by 1. For `c = 0`, just negate the offset. -/
theorem IsDyadicMod2piAtPrecision.neg {N : ℕ} {x : ℝ}
    (h : IsDyadicMod2piAtPrecision N x) :
    IsDyadicMod2piAtPrecision N (-x) := by
  obtain ⟨c, k, hx⟩ := h
  by_cases hc : c = 0
  · -- x = 2π · k, so -x = 2π · (-k). Use witness (0, -k).
    refine ⟨0, -k, ?_⟩
    rw [hc] at hx
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div,
               zero_add] at hx
    rw [hx]
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div,
               zero_add]
    push_cast
    ring
  · -- c ≠ 0: (-c).val = 2^N - c.val (with NeZero instance).
    refine ⟨-c, -k - 1, ?_⟩
    have hN_pos : 0 < (2 : ℕ) ^ N := Nat.two_pow_pos N
    haveI : NeZero (2 ^ N) := ⟨hN_pos.ne'⟩
    haveI : NeZero c := ⟨hc⟩
    have h_val_neg : (-c).val = 2 ^ N - c.val := ZMod.val_neg_of_ne_zero c
    rw [h_val_neg]
    have h_val_le : c.val ≤ 2 ^ N := (ZMod.val_lt c).le
    have h_val_real : ((2 ^ N - c.val : ℕ) : ℝ) = (2 ^ N : ℕ) - (c.val : ℝ) := by
      have h_le : c.val ≤ 2 ^ N := h_val_le
      rw [Nat.cast_sub h_le]
    rw [h_val_real]
    rw [hx]
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h_pow_ne : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h_pow_pos
    have h_pow_real : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; rfl
    rw [h_pow_real]
    push_cast
    field_simp
    ring

/-- **Closure under subtraction.** -/
theorem IsDyadicMod2piAtPrecision.sub {N : ℕ} {x y : ℝ}
    (hx : IsDyadicMod2piAtPrecision N x)
    (hy : IsDyadicMod2piAtPrecision N y) :
    IsDyadicMod2piAtPrecision N (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- **Halving lemma.** If `2 * x` is dyadic at precision `N`, then `x`
is dyadic at precision `N + 1`. This is the precision-tracking version
of `IsDyadicMod2pi.half`. -/
theorem IsDyadicMod2piAtPrecision.half {N : ℕ} {x : ℝ}
    (h : IsDyadicMod2piAtPrecision N (2 * x)) :
    IsDyadicMod2piAtPrecision (N + 1) x := by
  obtain ⟨c, k, hx_eq⟩ := h
  -- 2x = 2π · c.val / 2^N + 2π · k, so x = π · c.val / 2^N + π · k.
  -- π = 2π / 2 = 2π · 2^N / 2^(N+1). So π · c.val / 2^N = 2π · c.val / 2^(N+1).
  -- π · k: split by parity. If k = 2j: π · k = 2π · j. If k = 2j+1:
  -- π · k = 2π · j + π = 2π · j + 2π · 2^N / 2^(N+1).
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- k = j + j = 2j.
    refine ⟨(c.val : ZMod (2 ^ (N + 1))), j, ?_⟩
    have hc_lt : c.val < 2 ^ N := ZMod.val_lt c
    have h_lt : c.val < 2 ^ (N + 1) := by
      have : 2 ^ N < 2 ^ (N + 1) := by rw [pow_succ]; omega
      omega
    have h_val : ((c.val : ZMod (2 ^ (N + 1)))).val = c.val :=
      ZMod.val_natCast_of_lt h_lt
    rw [h_val]
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h_pow_ne : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h_pow_pos
    have h_pow_succ : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by
      rw [pow_succ]; ring
    have h_x : x = (2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ N
                      + 2 * Real.pi * (k : ℝ)) / 2 := by
      have := hx_eq; linarith
    rw [h_x, h_pow_succ]
    have hk : (k : ℝ) = 2 * (j : ℝ) := by
      have h_k : k = j + j := hj
      have h_cast : (k : ℝ) = (j : ℝ) + (j : ℝ) := by exact_mod_cast h_k
      linarith
    rw [hk]
    field_simp
  · -- k = 2j + 1.
    refine ⟨(c.val + 2 ^ N : ZMod (2 ^ (N + 1))), j, ?_⟩
    have hc_lt : c.val < 2 ^ N := ZMod.val_lt c
    have h_bound : c.val + 2 ^ N < 2 ^ (N + 1) := by
      have : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by rw [pow_succ]; ring
      omega
    have h_val : ((c.val + 2 ^ N : ZMod (2 ^ (N + 1)))).val = c.val + 2 ^ N := by
      have h_cast : ((c.val + 2 ^ N : ℕ) : ZMod (2 ^ (N + 1)))
                  = (c.val : ZMod (2 ^ (N + 1))) + (2 ^ N : ZMod (2 ^ (N + 1))) := by
        push_cast; rfl
      rw [show ((c.val + 2 ^ N : ZMod (2 ^ (N + 1)))).val
            = ((c.val + 2 ^ N : ℕ) : ZMod (2 ^ (N + 1))).val from by
        congr 1; push_cast; rfl]
      exact ZMod.val_natCast_of_lt h_bound
    rw [h_val]
    have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h_pow_ne : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h_pow_pos
    have h_pow_succ : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by
      rw [pow_succ]; ring
    have h_x : x = (2 * Real.pi * (c.val : ℝ) / (2 : ℝ) ^ N
                      + 2 * Real.pi * (k : ℝ)) / 2 := by
      have := hx_eq; linarith
    rw [h_x, h_pow_succ]
    have hk : (k : ℝ) = 2 * (j : ℝ) + 1 := by
      have h_k : k = 2 * j + 1 := hj
      exact_mod_cast h_k
    rw [hk]
    push_cast
    field_simp
    ring

/-! ## Level-1 base: precision-1 representation of `(Δ_i g)(0)`

At level 1 with diagonal `D_g`, `exp(I · g v) = α · (-1)^{p.Z · v}`,
so `(Δ_i g)(v)` satisfies `exp(I · (Δ_i g)(v)) = (-1)^{(p.Z i).val}`,
which is `±1`. Hence `(Δ_i g)(0) ∈ {0, π} (mod 2π)`, i.e., dyadic at
precision 1.

The proof uses the level-1 phased-Pauli structure (as in
`funcDerivPhase_constantMod2pi_of_level_one`): at level 1,
`Δ_i g` is constant mod 2π with value `funcDerivPhase i g 0`, and
`exp(I · funcDerivPhase i g 0) = (-1)^{(p.Z i).val} ∈ {-1, +1}`. -/

/-- **Level-1 precision-1 bound.** At level 1 of the dyadic hierarchy,
`(funcDerivPhase i g)(0)` is dyadic mod 2π at precision 1. -/
theorem funcDerivPhase_zero_precision_one_of_level_one
    {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic 1 (diagonalGateEquiv g))
    (i : Fin n) :
    IsDyadicMod2piAtPrecision 1 (funcDerivPhase i g 0) := by
  -- Strategy: at level 1, exp(I · (Δ_i g)(0)) ∈ {±1}. Equivalently,
  -- exp(2I · (Δ_i g)(0)) = 1, so 2 · (Δ_i g)(0) ∈ 2π · ℤ, so
  -- (Δ_i g)(0) ∈ π · ℤ. The dyadic precision-1 representation is
  -- (Δ_i g)(0) = 2π · 0/2 + 2π · k (when even) or 2π · 1/2 + 2π · k (when odd).
  --
  -- We need the precision-1 bound, so use the level-1 phased-Pauli structure directly
  -- to get exp(I · (Δ_i g)(0)) = (-1)^{(p.Z i).val} ∈ {±1}.
  generalize hk_eq : (1 : ℕ) = klvl at h_hier
  cases h_hier with
  | base hU =>
      obtain ⟨α, p, hα_dy, hα⟩ := hU
      have hpX : p.X = 0 :=
        Pauli_X_zero_of_diagonal_phasedPauli rfl hα
      have hzdot_zero : zDotVal p 0 = 0 := by
        unfold zDotVal
        refine Finset.sum_eq_zero ?_
        intro j _
        simp
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
      -- exp(I · (Δ_i g)(0)) = (-1)^{(p.Z i).val}.
      have h_di_exp :
          Complex.exp (Complex.I * (funcDerivPhase i g 0 : ℂ))
            = (-1 : ℂ) ^ (p.Z i).val := by
        rw [funcDerivPhase_apply]
        set w := (0 : Fin n → ZMod 2) + (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2)
          with hw_def
        have hw_simp : w = (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) := by
          rw [hw_def]; rw [zero_add]
        have h_zdot_w : zDotVal p w = (p.Z i).val := by
          rw [hw_simp]
          unfold zDotVal
          rw [Finset.sum_eq_single i]
          · simp [Pi.single_eq_same]
          · intro j _ hj
            rw [Pi.single, Function.update]
            simp [hj]
          · intro h; exact absurd (Finset.mem_univ i) h
        have h_split :
            Complex.exp (Complex.I * ((g w - g 0 : ℝ) : ℂ))
              = Complex.exp (Complex.I * (g w : ℂ))
                * (Complex.exp (Complex.I * (g 0 : ℂ)))⁻¹ := by
          rw [show Complex.I * ((g w - g 0 : ℝ) : ℂ)
                = Complex.I * (g w : ℂ) + (-(Complex.I * (g 0 : ℂ))) from by
              push_cast; ring]
          rw [Complex.exp_add, Complex.exp_neg]
        rw [h_split, h_apply w, h_apply 0, hzdot_zero, h_zdot_w]
        have hα_ne : (α : ℂ) ≠ 0 := α.ne_zero
        simp only [pow_zero, mul_one]
        field_simp
      -- Now express the precision-1 dyadic representation.
      -- exp(I · (Δ_i g)(0)) = (-1)^{(p.Z i).val}.
      -- (-1)^N = exp(I · π · N) for any N : ℕ.
      have h_neg_one_pow_exp :
          ((-1 : ℂ)) ^ (p.Z i).val
            = Complex.exp (Complex.I * ((Real.pi * ((p.Z i).val : ℝ) : ℝ) : ℂ)) := by
        have h_step : (-1 : ℂ) = Complex.exp (Complex.I * (Real.pi : ℂ)) := by
          rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I from by ring]
          exact Complex.exp_pi_mul_I.symm
        rw [h_step, ← Complex.exp_nat_mul]
        congr 1
        push_cast; ring
      rw [h_neg_one_pow_exp] at h_di_exp
      rw [Complex.exp_eq_exp_iff_exists_int] at h_di_exp
      obtain ⟨k, hk⟩ := h_di_exp
      -- hk : I · (Δ_i g)(0) = I · π · (p.Z i).val + 2π·I·k.
      -- So (Δ_i g)(0) = π · (p.Z i).val + 2π · k.
      have h_diff :
          (funcDerivPhase i g 0 : ℂ)
            = ((Real.pi * ((p.Z i).val : ℝ) : ℝ) : ℂ)
              + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
        have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
        have h_sub :
            Complex.I *
              ((funcDerivPhase i g 0 : ℂ)
                - ((Real.pi * ((p.Z i).val : ℝ) : ℝ) : ℂ))
              = Complex.I * ((k : ℂ) * (2 * (Real.pi : ℂ))) := by
          linear_combination hk
        have h_cancel := mul_left_cancel₀ hI_ne h_sub
        linear_combination h_cancel
      -- Now case-split on parity of (p.Z i).val.
      have h_pZ_val_lt : (p.Z i).val < 2 := ZMod.val_lt (p.Z i)
      have h_real : funcDerivPhase i g 0
                  = Real.pi * ((p.Z i).val : ℝ) + 2 * Real.pi * (k : ℝ) := by
        have h_cast :
            ((funcDerivPhase i g 0 : ℝ) : ℂ)
              = ((Real.pi * ((p.Z i).val : ℝ) + 2 * Real.pi * (k : ℝ) : ℝ) : ℂ) := by
          rw [h_diff]
          push_cast
          ring
        exact_mod_cast h_cast
      interval_cases (p.Z i).val
      · -- (p.Z i).val = 0: (Δ_i g)(0) = 2π · k. Use c = 0, offset k.
        refine ⟨0, k, ?_⟩
        rw [h_real]
        simp
      · -- (p.Z i).val = 1: (Δ_i g)(0) = π + 2π · k. Use c = 1 (in ZMod 2), offset k.
        refine ⟨1, k, ?_⟩
        rw [h_real]
        have h_val_one : ((1 : ZMod (2 ^ 1))).val = 1 := by decide
        rw [h_val_one]
        push_cast
        ring
  | @step kpred _ h =>
      have hk0 : kpred = 0 := by omega
      subst hk0
      cases h 0

/-! ## The precision-by-level induction

The bundled mutual-induction proposition: at level `k`, every
non-empty Möbius coefficient `(Δ_S g)(0)` with `|S| ≤ k` is dyadic at
precision `k - |S| + 1`. -/

/-- **Bundled mutual-induction proposition.** At level `k`, for every
non-empty `S` with `|S| ≤ k`, the Möbius coefficient is dyadic at
precision `k - |S| + 1`. -/
def PrecisionBoundPair (k : ℕ) : Prop :=
  ∀ {g : (Fin n → ZMod 2) → ℝ},
    IsCliffordHierarchyDyadic k (diagonalGateEquiv g) →
    ∀ {S : Finset (Fin n)}, S.Nonempty → S.card ≤ k →
      IsDyadicMod2piAtPrecision (k - S.card + 1)
        (funcDerivPhaseSubset S g 0)

/-- **Base case k = 1.** At level 1, the only non-empty S with |S| ≤ 1
is S = {i}, and (Δ_i g)(0) is dyadic at precision 1. -/
theorem precisionBoundPair_one : PrecisionBoundPair (n := n) 1 := by
  intro g h_hier S hS hScard
  -- |S| ≤ 1 and S nonempty, so |S| = 1.
  have h_card_one : S.card = 1 := by
    have h_pos : 0 < S.card := Finset.card_pos.mpr hS
    omega
  have h_level : 1 - S.card + 1 = 1 := by omega
  rw [h_level]
  -- S = {i} for some i.
  rw [Finset.card_eq_one] at h_card_one
  obtain ⟨i, hSi⟩ := h_card_one
  rw [hSi, funcDerivPhaseSubset_singleton]
  exact funcDerivPhase_zero_precision_one_of_level_one h_hier i

/-! ## Inductive step

Given `PrecisionBoundPair k`, derive `PrecisionBoundPair (k + 1)`.

For non-empty `S` with `|S| ≤ k + 1`:

* **Case `|S| = 1`** (`S = {i}`): use the halving trick.
  - Descent at `{i}` gives `D_{Δ_i g}` at level `k`.
  - By IH at `S' = {i}` applied to `D_{Δ_i g}` at level `k`:
    `(Δ_i Δ_i g)(0) = -2 · (Δ_i g)(0)` is dyadic at precision `k`.
  - By halving (and negation): `(Δ_i g)(0)` is dyadic at precision
    `k + 1 = (k + 1) - 1 + 1`. ✓

* **Case `|S| ≥ 2`**: use descent + IH.
  - Pick `i ∈ S`, set `T = S.erase i` (non-empty since `|S| ≥ 2`).
  - Descent at `{i}` gives `D_{Δ_i g}` at level `k`.
  - By IH at `T` applied to `D_{Δ_i g}` at level `k`:
    `(Δ_T (Δ_i g))(0) = (Δ_S g)(0)` is dyadic at precision
    `k - |T| + 1 = k - (|S| - 1) + 1 = (k + 1) - |S| + 1`. ✓
-/

theorem precisionBoundPair_succ {k : ℕ} (hk : 1 ≤ k)
    (ih : PrecisionBoundPair (n := n) k) :
    PrecisionBoundPair (n := n) (k + 1) := by
  intro g h_hier S hS hScard
  classical
  -- Pick i ∈ S.
  obtain ⟨i, hi⟩ := hS
  set T := S.erase i with hT_def
  have hi_notin_T : i ∉ T := Finset.notMem_erase i S
  have h_S_eq : S = insert i T := by
    rw [hT_def, Finset.insert_erase hi]
  have h_T_card : T.card = S.card - 1 := Finset.card_erase_of_mem hi
  -- Descent at {i}: D_{Δ_i g} at level k.
  have h_card_lt : ({i} : Finset (Fin n)).card < k + 1 := by
    rw [Finset.card_singleton]; omega
  have h_descent :=
    diagonalGateEquiv_funcDerivPhaseSubset_in_cliffordHierarchyDyadic
      g h_hier h_card_lt
  have h_level_eq : (k + 1 : ℕ) - ({i} : Finset (Fin n)).card = k := by
    rw [Finset.card_singleton]; omega
  rw [h_level_eq, funcDerivPhaseSubset_singleton] at h_descent
  -- h_descent : IsCliffordHierarchyDyadic k (diagonalGateEquiv (Δ_i g)).
  by_cases h_T_empty : T = ∅
  · -- |S| = 1, S = {i}. Use the halving trick.
    have h_S_singleton : S = {i} := by
      rw [h_S_eq, h_T_empty]; rfl
    rw [h_S_singleton, funcDerivPhaseSubset_singleton]
    -- Goal: IsDyadicMod2piAtPrecision (k + 1 - 1 + 1) (Δ_i g) 0.
    -- (k + 1 - 1 + 1) = k + 1.
    have h_idx : k + 1 - ({i} : Finset (Fin n)).card + 1 = k + 1 := by
      rw [Finset.card_singleton]; omega
    rw [h_idx]
    -- IH applied to D_{Δ_i g} at level k, S' = {i}, |S'| = 1 ≤ k.
    have h_ih_apply :
        IsDyadicMod2piAtPrecision (k - ({i} : Finset (Fin n)).card + 1)
          (funcDerivPhaseSubset {i} (funcDerivPhase i g) 0) := by
      apply ih h_descent (Finset.singleton_nonempty i)
      rw [Finset.card_singleton]; exact hk
    rw [Finset.card_singleton] at h_ih_apply
    have h_idx2 : k - 1 + 1 = k := by omega
    rw [h_idx2] at h_ih_apply
    rw [funcDerivPhaseSubset_singleton] at h_ih_apply
    -- h_ih_apply : IsDyadicMod2piAtPrecision k (Δ_i Δ_i g 0).
    rw [funcDerivPhase_self_zero] at h_ih_apply
    -- h_ih_apply : IsDyadicMod2piAtPrecision k (-2 * (Δ_i g) 0).
    -- Negate to get 2 * (Δ_i g) 0 dyadic at precision k.
    have h_two_dy : IsDyadicMod2piAtPrecision k (2 * funcDerivPhase i g 0) := by
      have h_neg := h_ih_apply.neg
      have h_eq : -(-2 * funcDerivPhase i g 0) = 2 * funcDerivPhase i g 0 := by ring
      rw [h_eq] at h_neg
      exact h_neg
    -- Halve to get (Δ_i g) 0 dyadic at precision k + 1.
    exact h_two_dy.half
  · -- |S| ≥ 2: T non-empty.
    rw [h_S_eq, funcDerivPhaseSubset_insert hi_notin_T]
    -- Goal: IsDyadicMod2piAtPrecision (k + 1 - |S| + 1) (Δ_i (Δ_T g) 0).
    -- Swap to Δ_T (Δ_i g) via commutativity.
    have h_swap : funcDerivPhase i (funcDerivPhaseSubset T g)
                = funcDerivPhaseSubset T (funcDerivPhase i g) := by
      induction T using Finset.induction_on with
      | empty =>
          rw [funcDerivPhaseSubset_empty, funcDerivPhaseSubset_empty]
      | @insert j U hj ih =>
          rw [funcDerivPhaseSubset_insert hj,
              funcDerivPhaseSubset_insert hj]
          rw [← ih]
          exact funcDerivPhase_comm i j _
    rw [h_swap]
    -- Goal: IsDyadicMod2piAtPrecision (k + 1 - |insert i T| + 1)
    --       (Δ_T (Δ_i g) 0).
    -- Apply IH on D_{Δ_i g} at T.
    have h_T_nonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_T_empty
    have h_T_card_le : T.card ≤ k := by
      rw [h_T_card]
      rw [h_S_eq, Finset.card_insert_of_notMem hi_notin_T] at hScard
      omega
    have h_ih_apply : IsDyadicMod2piAtPrecision (k - T.card + 1)
          (funcDerivPhaseSubset T (funcDerivPhase i g) 0) :=
      ih h_descent h_T_nonempty h_T_card_le
    -- The precision in the goal is k + 1 - (insert i T).card + 1.
    -- (insert i T).card = T.card + 1 (since i ∉ T).
    -- So k + 1 - (T.card + 1) + 1 = k - T.card + 1 (matches h_ih_apply).
    have h_card_eq : (insert i T).card = T.card + 1 :=
      Finset.card_insert_of_notMem hi_notin_T
    rw [h_card_eq]
    -- Goal: IsDyadicMod2piAtPrecision (k + 1 - (T.card + 1) + 1) (...).
    -- Need to show this equals (k - T.card + 1).
    have h_T_lt : T.card ≤ k := h_T_card_le
    have h_target : k + 1 - (T.card + 1) + 1 = k - T.card + 1 := by omega
    rw [h_target]
    exact h_ih_apply

/-! ## The general-`k` precision bound

By induction on `k` starting from `k = 1`, we obtain
`PrecisionBoundPair k` for every `k ≥ 1`. -/

theorem precisionBoundPair_of_one_le {k : ℕ} (hk : 1 ≤ k) :
    PrecisionBoundPair (n := n) k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases h_k'_zero : k' = 0
    · subst h_k'_zero
      exact precisionBoundPair_one
    · have h_k'_pos : 1 ≤ k' := Nat.one_le_iff_ne_zero.mpr h_k'_zero
      exact precisionBoundPair_succ h_k'_pos (ih h_k'_pos)

/-- **The precision-by-level bound.** For `k ≥ 1` and non-empty `S`
with `|S| ≤ k`, the Möbius coefficient `(Δ_S g)(0)` is dyadic mod 2π
at precision `k - |S| + 1`.

This is the substantive CGK precision-by-level bound at `p = 2`, the
key ingredient for the strict `effectiveLevel ≤ k` theorem. -/
theorem mobiusCoeff_precision_bound
    {n k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    {S : Finset (Fin n)} (hS : S.Nonempty) (hSk : S.card ≤ k) :
    IsDyadicMod2piAtPrecision (k - S.card + 1)
      (funcDerivPhaseSubset S g 0) :=
  precisionBoundPair_of_one_le (n := n) hk h_hier hS hSk

/-! ## Helper: `monomialOfFinset S` as a single monomial

The product `∏ i ∈ S, X_i` equals `MvPolynomial.monomial d_S 1` where
`d_S = ∑ i ∈ S, Finsupp.single i 1` is the indicator-vector of `S`. -/

/-- **`monomialOfFinset S` as a `monomial`.** The product
`∏ i ∈ S, X_i` equals the monomial with exponent vector
`∑ i ∈ S, Finsupp.single i 1` and coefficient `1`. -/
theorem monomialOfFinset_eq_monomial {n k : ℕ} (S : Finset (Fin n)) :
    (monomialOfFinset (n := n) (m := k) S : DiagPhase n k)
      = MvPolynomial.monomial (∑ i ∈ S, Finsupp.single i 1)
          (1 : ZMod (2 ^ k)) := by
  classical
  unfold monomialOfFinset
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j T hj ih =>
      rw [Finset.prod_insert hj, ih]
      have h_X_eq : (MvPolynomial.X j : MvPolynomial (Fin n) (ZMod (2 ^ k)))
                  = MvPolynomial.monomial (Finsupp.single j 1)
                      (1 : ZMod (2 ^ k)) := rfl
      rw [h_X_eq]
      rw [MvPolynomial.monomial_mul, one_mul]
      congr 1
      rw [Finset.sum_insert hj]

/-! ## Building the strict polynomial witness

We assemble the polynomial at uniform precision `k`. For each
non-empty `S` with `|S| ≤ k`, the residue `c_S` at precision
`k - |S| + 1` casts to a precision-`k` residue with the low
`|S| - 1` bits cleared. So `twoAdicVal c_S ≥ |S| - 1` in `ZMod 2^k`,
giving `effLevelMonom k c_S {} ≤ (k - 1 - (|S| - 1)) + |S| = k`.

We need to express the polynomial as before, but choose the precision
to be exactly `k`. The key bookkeeping is that the cast from precision
`k - |S| + 1` to precision `k` multiplies by `2^(|S| - 1)`, so the
resulting `ZMod 2^k` value has `twoAdicVal ≥ |S| - 1`. -/

/-- **Lifting a precision-`N`-bounded element to precision `k` with
divisibility witness.** If `x` is dyadic at precision `N` with `N ≤ k`,
then there is a precision-`k` residue `c' : ZMod 2^k` with
`2^(k - N) ∣ c'.val` realising the same `x`, and a corresponding
offset.

The construction: `c' := c.val * 2^(k - N)` in `ZMod 2^k`. -/
private theorem precision_lift_with_dvd {N k : ℕ} {x : ℝ}
    (h : IsDyadicMod2piAtPrecision N x) (hNk : N ≤ k) :
    ∃ (c' : ZMod (2 ^ k)) (kint : ℤ),
      x = 2 * Real.pi * (c'.val : ℝ) / (2 : ℝ) ^ k
            + 2 * Real.pi * (kint : ℝ)
        ∧ (2 ^ (k - N) ∣ c'.val) := by
  obtain ⟨c, kint, hx⟩ := h
  set Δ := k - N with hΔ_def
  have hΔ_eq : N + Δ = k := by rw [hΔ_def]; omega
  -- The new residue is c.val * 2^Δ in ZMod 2^k.
  have h_bound : (c.val * 2 ^ Δ) < 2 ^ k := by
    have h_cv_lt : c.val < 2 ^ N := ZMod.val_lt c
    have h_pow_split : (2 : ℕ) ^ k = 2 ^ N * 2 ^ Δ := by
      rw [← pow_add, hΔ_eq]
    rw [h_pow_split]
    exact Nat.mul_lt_mul_of_pos_right h_cv_lt (Nat.two_pow_pos Δ)
  refine ⟨((c.val * 2 ^ Δ : ℕ) : ZMod (2 ^ k)), kint, ?_, ?_⟩
  · -- Equation.
    have h_val_eq : (((c.val * 2 ^ Δ : ℕ) : ZMod (2 ^ k))).val
                  = c.val * 2 ^ Δ :=
      ZMod.val_natCast_of_lt h_bound
    rw [h_val_eq, hx]
    have h_pow_pos_N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h_pow_ne_N : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h_pow_pos_N
    have h_pow_pos_k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h_pow_ne_k : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h_pow_pos_k
    have h_pow_split_real : (2 : ℝ) ^ k = (2 : ℝ) ^ N * (2 : ℝ) ^ Δ := by
      rw [← pow_add, hΔ_eq]
    push_cast
    rw [h_pow_split_real]
    field_simp
  · -- Divisibility.
    have h_val_eq : (((c.val * 2 ^ Δ : ℕ) : ZMod (2 ^ k))).val
                  = c.val * 2 ^ Δ :=
      ZMod.val_natCast_of_lt h_bound
    rw [h_val_eq]
    exact ⟨c.val, by rw [hΔ_def]; ring⟩

/-- **Per-`S` precision-`k` lift with bounded `twoAdicVal`.** For
non-empty `S` with `|S| ≤ k`, the Möbius coefficient lifts to a
precision-`k` residue `c'_S : ZMod 2^k` with
`twoAdicVal c'_S ≥ |S| - 1`. -/
theorem mobiusCoeff_precision_k_lift
    {n k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g))
    {S : Finset (Fin n)} (hS : S.Nonempty) (hSk : S.card ≤ k) :
    ∃ (c' : ZMod (2 ^ k)) (kint : ℤ),
      funcDerivPhaseSubset S g 0
        = 2 * Real.pi * (c'.val : ℝ) / (2 : ℝ) ^ k
            + 2 * Real.pi * (kint : ℝ)
        ∧ (2 ^ (S.card - 1) ∣ c'.val) := by
  have h_prec := mobiusCoeff_precision_bound hk h_hier hS hSk
  -- h_prec : IsDyadicMod2piAtPrecision (k - S.card + 1) (...)
  have h_N_le : k - S.card + 1 ≤ k := by
    have h_pos : 1 ≤ S.card := Finset.card_pos.mpr hS
    omega
  obtain ⟨c', kint, h_eq, h_dvd⟩ := precision_lift_with_dvd h_prec h_N_le
  refine ⟨c', kint, h_eq, ?_⟩
  -- 2^(k - (k - S.card + 1)) = 2^(S.card - 1).
  have h_exp : k - (k - S.card + 1) = S.card - 1 := by
    have h_pos : 1 ≤ S.card := Finset.card_pos.mpr hS
    omega
  rw [h_exp] at h_dvd
  exact h_dvd

/-! ## The strict-level polynomial assembly

We now assemble the strict-level polynomial at precision `k`. -/

/-- **Coefficient extraction for the strict assembly.** Given the
hierarchy hypothesis at level `k`, for every `S` we produce a residue
`c_S : ZMod 2^k` and integer offset realising the Möbius coefficient
representation, with the divisibility witness `2^(|S|-1) ∣ c_S.val`
for non-empty `S` with `|S| ≤ k`. -/
private theorem extract_strict_coefficients
    {k : ℕ} (hk : 1 ≤ k) {g : (Fin n → ZMod 2) → ℝ}
    (h_hier : IsCliffordHierarchyDyadic k (diagonalGateEquiv g)) :
    ∃ (cS : Finset (Fin n) → ZMod (2 ^ k)) (kintS : Finset (Fin n) → ℤ),
      (∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k →
        funcDerivPhaseSubset S g 0
          = 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k
              + 2 * Real.pi * (kintS S : ℝ))
      ∧ (∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k →
          2 ^ (S.card - 1) ∣ (cS S).val)
      ∧ (∀ S : Finset (Fin n), ¬ (S.Nonempty ∧ S.card ≤ k) →
          cS S = 0) := by
  classical
  -- Use a choice principle: for each S satisfying the hypotheses, pick a
  -- (cS, kintS); for S violating the hypotheses, set cS = 0, kintS = 0.
  have h_choose : ∀ S : Finset (Fin n),
      ∃ (cS : ZMod (2 ^ k)) (kintS : ℤ),
        (S.Nonempty → S.card ≤ k →
          funcDerivPhaseSubset S g 0
            = 2 * Real.pi * (cS.val : ℝ) / (2 : ℝ) ^ k
                + 2 * Real.pi * (kintS : ℝ))
        ∧ (S.Nonempty → S.card ≤ k → 2 ^ (S.card - 1) ∣ cS.val)
        ∧ (¬ (S.Nonempty ∧ S.card ≤ k) → cS = 0) := by
    intro S
    by_cases h_S_valid : S.Nonempty ∧ S.card ≤ k
    · obtain ⟨cS, kintS, h_eq, h_dvd⟩ :=
        mobiusCoeff_precision_k_lift hk h_hier h_S_valid.1 h_S_valid.2
      refine ⟨cS, kintS, ?_, ?_, ?_⟩
      · intro _ _; exact h_eq
      · intro _ _; exact h_dvd
      · intro h; exact absurd h_S_valid h
    · refine ⟨0, 0, ?_, ?_, ?_⟩
      · intro hS hSk; exact absurd ⟨hS, hSk⟩ h_S_valid
      · intro hS hSk; exact absurd ⟨hS, hSk⟩ h_S_valid
      · intro _; rfl
  choose cS kintS h_data using h_choose
  refine ⟨cS, kintS, ?_, ?_, ?_⟩
  · intro S hS hSk; exact (h_data S).1 hS hSk
  · intro S hS hSk; exact (h_data S).2.1 hS hSk
  · intro S h; exact (h_data S).2.2 h

/-! ## The strict-level Möbius assembly polynomial

We build the polynomial at uniform precision `k` and only include
non-empty `S` with `|S| ≤ k`. The constant term is zero by
construction. Each non-empty term has `twoAdicVal cS ≥ |S| - 1`, so
its effective level contribution is at most `k`. -/

/-- **The strict-level Möbius assembly polynomial.** Sum over non-empty
`S` with `|S| ≤ k` of `C(cS S) · monomialOfFinset S`. The constant
term is excluded; the residues `cS S` satisfy `twoAdicVal ≥ |S| - 1`. -/
noncomputable def strictMobiusAssemblyPoly
    {n k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k)) : DiagPhase n k :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => S.Nonempty ∧ S.card ≤ k),
    MvPolynomial.C (cS S) * monomialOfFinset S

/-- The total degree of `strictMobiusAssemblyPoly cS` is at most `k`. -/
theorem strictMobiusAssemblyPoly_totalDegree
    {n k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k)) :
    (strictMobiusAssemblyPoly cS).totalDegree ≤ k := by
  unfold strictMobiusAssemblyPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro S hS
  rw [Finset.mem_filter] at hS
  obtain ⟨_, hS_ne, hSk⟩ := hS
  calc (MvPolynomial.C (cS S) * monomialOfFinset S).totalDegree
      ≤ (MvPolynomial.C (cS S)).totalDegree
          + (monomialOfFinset (m := k) S).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = 0 + (monomialOfFinset (m := k) S).totalDegree := by
        rw [MvPolynomial.totalDegree_C]
    _ ≤ 0 + S.card := by
        exact Nat.add_le_add_left (monomialOfFinset_totalDegree S) 0
    _ = S.card := zero_add _
    _ ≤ k := hSk

/-- The constant coefficient of `strictMobiusAssemblyPoly` is zero. -/
theorem strictMobiusAssemblyPoly_coeff_zero
    {n k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k)) :
    MvPolynomial.coeff 0 (strictMobiusAssemblyPoly cS) = 0 := by
  unfold strictMobiusAssemblyPoly
  classical
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [Finset.mem_filter] at hS
  obtain ⟨_, hS_ne, _⟩ := hS
  -- C(cS S) * monomialOfFinset S = monomial d_S (cS S) for d_S = sum of indicators.
  -- For nonempty S, d_S ≠ 0, so the coefficient at 0 is 0.
  set d_S : Fin n →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1 with hd_S_def
  have h_mof_eq : (monomialOfFinset (n := n) (m := k) S : DiagPhase n k)
                = MvPolynomial.monomial d_S 1 :=
    monomialOfFinset_eq_monomial S
  have h_full_eq : (MvPolynomial.C (cS S) * monomialOfFinset S : DiagPhase n k)
                 = MvPolynomial.monomial d_S (cS S) := by
    rw [h_mof_eq, MvPolynomial.C_mul_monomial, mul_one]
  rw [h_full_eq, MvPolynomial.coeff_monomial]
  -- Need: if d_S = 0 then cS S else 0 = 0.
  -- For S nonempty, d_S ≠ 0.
  have h_d_S_ne_zero : d_S ≠ 0 := by
    obtain ⟨i, hi⟩ := hS_ne
    intro hd_zero
    have h_eval_i : d_S i = (0 : Fin n →₀ ℕ) i := by rw [hd_zero]
    rw [Finsupp.coe_zero, Pi.zero_apply] at h_eval_i
    rw [hd_S_def] at h_eval_i
    rw [Finsupp.coe_finset_sum, Finset.sum_apply] at h_eval_i
    -- d_S i = ∑ j ∈ S, (Finsupp.single j 1) i = 1 (only j = i contributes).
    have h_eq_one : ∑ j ∈ S, (Finsupp.single j 1 : Fin n →₀ ℕ) i = 1 := by
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg hji]
      · intro h; exact absurd hi h
    rw [h_eq_one] at h_eval_i
    exact absurd h_eval_i (by norm_num)
  rw [if_neg h_d_S_ne_zero]

/-! ## Evaluation of the strict assembly polynomial

The evaluation matches the original `mobiusAssemblyPoly` evaluation
plus a constant shift (the c_∅ term we excluded). -/

/-- Evaluating `strictMobiusAssemblyPoly cS` at `v` gives the sum over
non-empty `S ⊆ supp v` with `|S| ≤ k` of `cS S`. -/
theorem strictMobiusAssemblyPoly_eval
    {n k : ℕ} (cS : Finset (Fin n) → ZMod (2 ^ k)) (v : Fin n → ZMod 2) :
    (strictMobiusAssemblyPoly cS).eval v
      = ∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter
              (fun S => S.Nonempty ∧ S.card ≤ k),
          cS S := by
  unfold strictMobiusAssemblyPoly DiagPhase.eval
  rw [map_sum]
  have h_each : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
                      (fun S => S.Nonempty ∧ S.card ≤ k),
      MvPolynomial.eval (DiagPhase.liftBinary v)
        (MvPolynomial.C (cS S) * monomialOfFinset S)
        = if S ⊆ FTQCLib.Codes.supp v then cS S else 0 := by
    intro S _hS
    rw [map_mul, MvPolynomial.eval_C]
    change cS S * (monomialOfFinset (m := k) S).eval v = _
    rw [monomialOfFinset_eval]
    by_cases hsub : S ⊆ FTQCLib.Codes.supp v
    · rw [if_pos hsub, if_pos hsub, mul_one]
    · rw [if_neg hsub, if_neg hsub, mul_zero]
  rw [Finset.sum_congr rfl h_each]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr ?_ (fun S _ => rfl)
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hS_ne, hSk⟩, hsub⟩
    exact ⟨hsub, hS_ne, hSk⟩
  · rintro ⟨hsub, hS_ne, hSk⟩
    exact ⟨⟨hS_ne, hSk⟩, hsub⟩

/-! ## Effective level of the strict assembly polynomial

For each non-empty `S` with `|S| ≤ k`, the residue `cS S` satisfies
`twoAdicVal (cS S) ≥ |S| - 1` (from the precision lift). Each
summand has effective level
`(k - 1 - twoAdicVal cS S) + |S| ≤ (k - 1 - (|S| - 1)) + |S| = k`.

By `effectiveLevel_finsetSum_le`, the total polynomial has effective
level `≤ k`. -/

/-- **Per-summand effective-level bound.** For non-empty `S` with
`|S| ≤ k`, the summand `C(cS S) * monomialOfFinset S` has effective
level at most `k` whenever `twoAdicVal (cS S) ≥ |S| - 1`. -/
theorem effectiveLevel_summand_le
    {n k : ℕ} (hk : 1 ≤ k) (S : Finset (Fin n)) (cS : ZMod (2 ^ k))
    (hS : S.Nonempty) (hSk : S.card ≤ k)
    (h_dvd : 2 ^ (S.card - 1) ∣ cS.val) :
    effectiveLevel
      ((MvPolynomial.C cS * monomialOfFinset S) : DiagPhase n k) ≤ k := by
  classical
  -- Case split on whether cS = 0.
  by_cases hcS : cS = 0
  · rw [hcS]
    simp only [map_zero, zero_mul]
    rw [effectiveLevel_zero]
    omega
  -- cS ≠ 0. Now use the per-monomial structure.
  -- C cS * monomialOfFinset S = monomial (sum of singletons) cS.
  -- Concretely, monomialOfFinset S = ∏ i ∈ S, X i = monomial d 1 where
  -- d = sum_{i ∈ S} Finsupp.single i 1 = indicator of S.
  -- And C cS * monomial d 1 = monomial d cS.
  have h_S_card_pos : 0 < S.card := Finset.card_pos.mpr hS
  -- Build the exponent vector d_S.
  set d_S : Fin n →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1 with hd_S_def
  -- monomialOfFinset S = monomial d_S 1.
  have h_mof_eq : (monomialOfFinset (n := n) (m := k) S : DiagPhase n k)
                = MvPolynomial.monomial d_S 1 :=
    monomialOfFinset_eq_monomial S
  -- C cS * monomial d_S 1 = monomial d_S cS.
  have h_full_eq : (MvPolynomial.C cS * monomialOfFinset S : DiagPhase n k)
                 = MvPolynomial.monomial d_S cS := by
    rw [h_mof_eq, MvPolynomial.C_mul_monomial, mul_one]
  rw [h_full_eq]
  -- Apply effectiveLevel_monomial_le and check the bound.
  refine le_trans (effectiveLevel_monomial_le d_S cS) ?_
  unfold effLevelMonom
  -- effLevelMonom k cS d_S = (k - 1 - twoAdicVal cS) + d_S.sum (fun _ e => e).
  -- d_S.sum (fun _ e => e) = ∑ i ∈ S, 1 = S.card.
  have h_d_S_sum : d_S.sum (fun _ e => e) = S.card := by
    rw [hd_S_def]
    -- d_S = ∑ i ∈ S, Finsupp.single i 1.
    -- d_S.sum (fun _ e => e) = ∑ k, d_S k = ∑ k ∈ S, 1 = S.card.
    rw [Finsupp.sum]
    -- For i ∈ S, (∑ j ∈ S, Finsupp.single j 1) i = 1; for i ∉ S, = 0.
    -- So support = S, and the sum equals S.card.
    have h_supp : (∑ i ∈ S, (Finsupp.single i 1 : Fin n →₀ ℕ)).support = S := by
      ext i
      simp only [Finsupp.mem_support_iff, Finsupp.coe_finset_sum,
                 Finset.sum_apply, Finsupp.single_apply]
      constructor
      · intro h
        by_contra h_not
        apply h
        apply Finset.sum_eq_zero
        intro j hj
        have hji : j ≠ i := fun heq => h_not (heq ▸ hj)
        rw [if_neg hji]
      · intro hi
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]; exact one_ne_zero
        · intro j _ hji
          rw [if_neg hji]
        · intro h; exact absurd hi h
    rw [h_supp]
    -- Now ∑ i ∈ S, d_S i = ∑ i ∈ S, 1 = S.card.
    have h_d_S_eq_one : ∀ i ∈ S, d_S i = 1 := by
      intro i hi
      rw [hd_S_def]
      rw [Finsupp.coe_finset_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg hji]
      · intro h; exact absurd hi h
    calc ∑ i ∈ S, d_S i = ∑ _i ∈ S, 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact h_d_S_eq_one i hi
      _ = S.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  rw [h_d_S_sum]
  -- Now bound (k - 1 - twoAdicVal cS) + S.card ≤ k.
  -- We have twoAdicVal cS ≥ S.card - 1 from h_dvd.
  have h_twoAdicVal_ge : S.card - 1 ≤ twoAdicVal cS := by
    rw [twoAdicVal_of_ne_zero hcS]
    have hval_ne : cS.val ≠ 0 := by
      intro h
      have : cS = 0 := by
        have hcast : cS = (cS.val : ZMod (2 ^ k)) := (ZMod.natCast_zmod_val cS).symm
        rw [hcast, h]; simp
      exact hcS this
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hval_ne] at h_dvd
    exact h_dvd
  -- (k - 1 - twoAdicVal cS) + S.card ≤ k.
  -- twoAdicVal cS ≥ S.card - 1, so k - 1 - twoAdicVal cS ≤ k - S.card.
  -- Adding S.card: (k - S.card) + S.card = k.
  omega

/-- **Total effective-level bound for the strict assembly polynomial.** -/
theorem strictMobiusAssemblyPoly_effectiveLevel_le
    {n k : ℕ} (hk : 1 ≤ k) (cS : Finset (Fin n) → ZMod (2 ^ k))
    (h_dvd : ∀ S : Finset (Fin n), S.Nonempty → S.card ≤ k →
        2 ^ (S.card - 1) ∣ (cS S).val)
    (_h_zero : ∀ S : Finset (Fin n), ¬ (S.Nonempty ∧ S.card ≤ k) → cS S = 0) :
    effectiveLevel (strictMobiusAssemblyPoly cS) ≤ k := by
  unfold strictMobiusAssemblyPoly
  refine le_trans (effectiveLevel_finsetSum_le _ _) ?_
  refine Finset.sup_le ?_
  intro S hS
  rw [Finset.mem_filter] at hS
  obtain ⟨_, hS_ne, hSk⟩ := hS
  exact effectiveLevel_summand_le hk S (cS S) hS_ne hSk (h_dvd S hS_ne hSk)

/-! ## The main theorem

We finally assemble everything: ScalarEquiv anchoring + strict
precision-`k` Möbius polynomial + effective-level bound. -/

/-- **The strict-level projective CGK reverse.** For every `k ≥ 1` and
every diagonal `U` at `IsCliffordHierarchyDyadic k`, there is a
polynomial `P : DiagPhase n k` (at precision exactly `k`) with:

* `U` `ScalarEquiv` `diagonalGateEquiv (DiagPhase.realPhase P)`,
* `P.effectiveLevel ≤ k`,
* `MvPolynomial.coeff 0 P = 0`.

The `IsDyadicMod2pi (f 0)` hypothesis is DROPPED: the ScalarEquiv
relation absorbs the global phase factor `α = exp(I · g 0)` for any
`g`, regardless of dyadic structure of `g 0`.

This is the CGK 2017 Theorem 2 / Lemma 4 reverse direction at `p = 2`
in its sharpest projective form. -/
theorem cgk_reverse_dyadic_poly_projective_effectiveLevel
    {n k : ℕ} (hk : 1 ≤ k)
    (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n)
    (h_diag : ∃ f, U = diagonalGateEquiv f)
    (h_hier : IsCliffordHierarchyDyadic k U) :
    ∃ (P : DiagPhase n k),
      ScalarEquiv U (diagonalGateEquiv (DiagPhase.realPhase P)) ∧
      P.effectiveLevel ≤ k ∧
      MvPolynomial.coeff 0 P = 0 := by
  classical
  -- Extract g from h_diag.
  obtain ⟨g, hU_eq⟩ := h_diag
  -- Anchor: replace g with g - g 0, an automatic shift.
  set g_anchored : (Fin n → ZMod 2) → ℝ := fun v => g v - g 0 with hg_anchored_def
  have h_g_anchored_zero : g_anchored 0 = 0 := by
    rw [hg_anchored_def]; simp
  -- The anchored function has dyadic-mod-2π zero: it equals 0 at v = 0,
  -- so it's trivially dyadic at any precision.
  have h_anchored_dyadic : IsDyadicMod2pi (g_anchored 0) := by
    rw [h_g_anchored_zero]; exact isDyadicMod2pi_zero
  -- But: the anchored operator diagonalGateEquiv g_anchored is NOT necessarily at
  -- IsCliffordHierarchyDyadic k unless g_anchored has the right structure.
  -- The ScalarEquiv relation, not the operator-side hierarchy, is what shifts.
  -- So we work with the original g but compute discrete derivatives, which are
  -- shift-invariant: (Δ_S g)(0) = (Δ_S g_anchored)(0) when |S| ≥ 1.
  --
  -- Strategy: work with the hierarchy hypothesis on the original g, extract
  -- precision-bounded Möbius coefficients for non-empty S, build the polynomial
  -- as a sum over non-empty S of c_S * monomialOfFinset S. The constant term
  -- being zero is automatic by construction.
  -- The ScalarEquiv relation arises because we drop the constant (= g 0)
  -- contribution to f.
  have h_hier_g : IsCliffordHierarchyDyadic k (diagonalGateEquiv g) := by
    rw [← hU_eq]; exact h_hier
  -- Step 1: Extract per-S precision-k coefficients with divisibility witness.
  obtain ⟨cS, kintS, h_eq, h_dvd, h_zero⟩ :=
    extract_strict_coefficients hk h_hier_g
  -- Step 2: Define the strict polynomial.
  set P := strictMobiusAssemblyPoly (n := n) (k := k) cS with hP_def
  refine ⟨P, ?_, ?_, ?_⟩
  · -- ScalarEquiv U (diagonalGateEquiv (realPhase P)).
    -- We need to show: there exists α : ℂˣ such that
    --   U.toLinearMap = α • (diagonalGateEquiv (realPhase P)).toLinearMap.
    -- The α is exp(I · g 0). The key identity:
    --   exp(I · g v) = exp(I · g 0) · exp(I · (g v - g 0))
    -- and we want to relate g v - g 0 to realPhase P v.
    --
    -- Möbius inversion: g(v) = ∑_{S ⊆ supp v} (Δ_S g)(0).
    -- The empty S gives g(0). Non-empty S contributions sum to g(v) - g(0).
    -- For |S| > k: contribution is 2π·ℤ (vanishing).
    -- For 1 ≤ |S| ≤ k: contribution is 2π · (cS S).val / 2^k + 2π · kintS S.
    -- So g(v) - g(0) ≡ realPhase P v (mod 2π).
    rw [hU_eq]
    refine ⟨expUnit (Complex.I * (g 0 : ℂ)), ?_⟩
    rw [diagonalGateEquiv_toLinearMap, diagonalGateEquiv_toLinearMap]
    apply LinearMap.ext
    intro ψ
    funext v
    rw [diagonalGate_apply]
    change Complex.exp (Complex.I * (g v : ℂ)) * ψ v
          = ((expUnit (Complex.I * (g 0 : ℂ)) : ℂˣ) : ℂ)
              * (Complex.exp (Complex.I * (DiagPhase.realPhase P v : ℂ)) * ψ v)
    rw [expUnit_val]
    -- We need exp(I · g v) = exp(I · g 0) · exp(I · realPhase P v).
    -- Equivalently, g v ≡ g 0 + realPhase P v (mod 2π).
    -- Möbius inversion:
    --   g v = ∑_{S ⊆ supp v} (Δ_S g)(0)
    --       = (Δ_∅ g)(0) + ∑_{S ⊆ supp v, S nonempty} (Δ_S g)(0)
    --       = g(0) + ∑_{S nonempty ⊆ supp v} (Δ_S g)(0).
    -- Split non-empty S by |S| ≤ k vs |S| > k:
    --   For |S| ≤ k: (Δ_S g)(0) = 2π · (cS S).val / 2^k + 2π · kintS S.
    --   For |S| > k: (Δ_S g)(0) = 2π · vanish-int.
    -- realPhase P v = sum of (cS S).val/2^k contributions + 2π · J.
    have h_funcDerivSubset_eq : ∀ (S : Finset (Fin n)),
        funcDerivSubset S g = funcDerivPhaseSubset S g := by
      intro S
      classical
      induction S using Finset.induction_on with
      | empty =>
          rw [funcDerivSubset_empty, funcDerivPhaseSubset_empty]
      | @insert i S hi ih =>
          rw [funcDerivSubset_insert hi, funcDerivPhaseSubset_insert hi, ih]
          funext w
          rw [funcDerivPhase_apply]
          rfl
    have h_mobius_g :
        g v = ∑ S ∈ (FTQCLib.Codes.supp v).powerset,
                funcDerivPhaseSubset S g 0 := by
      have h := eq_sum_mobiusCoeff g v
      unfold mobiusCoeff at h
      rw [h]
      apply Finset.sum_congr rfl
      intro S _
      exact congrFun (h_funcDerivSubset_eq S) 0
    -- Split S ∈ powerset by emptiness and S.card ≤ k.
    -- Three classes: S = ∅; S nonempty, |S| ≤ k; S nonempty, |S| > k.
    set P_empty := (FTQCLib.Codes.supp v).powerset.filter (fun S => S = ∅)
      with hP_empty_def
    set P_low := (FTQCLib.Codes.supp v).powerset.filter
        (fun S => S.Nonempty ∧ S.card ≤ k)
      with hP_low_def
    set P_high := (FTQCLib.Codes.supp v).powerset.filter
        (fun S => S.Nonempty ∧ k < S.card)
      with hP_high_def
    have h_split :
        (FTQCLib.Codes.supp v).powerset = P_empty ∪ P_low ∪ P_high := by
      ext S
      rw [hP_empty_def, hP_low_def, hP_high_def]
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hS
        by_cases hS_empty : S = ∅
        · left; left; exact ⟨hS, hS_empty⟩
        · have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
          by_cases hSk : S.card ≤ k
          · left; right; exact ⟨hS, hS_ne, hSk⟩
          · right; exact ⟨hS, hS_ne, by omega⟩
      · rintro ((⟨hS, _⟩ | ⟨hS, _, _⟩) | ⟨hS, _, _⟩) <;> exact hS
    have h_disj_low_high : Disjoint P_low P_high := by
      rw [hP_low_def, hP_high_def, Finset.disjoint_filter]
      intro S _ ⟨_, h1⟩ ⟨_, h2⟩
      omega
    have h_disj_empty_low : Disjoint P_empty P_low := by
      rw [hP_empty_def, hP_low_def, Finset.disjoint_filter]
      intro S _ hS_empty ⟨hS_ne, _⟩
      rw [hS_empty] at hS_ne
      exact absurd hS_ne (Finset.not_nonempty_empty)
    have h_disj_empty_high : Disjoint P_empty P_high := by
      rw [hP_empty_def, hP_high_def, Finset.disjoint_filter]
      intro S _ hS_empty ⟨hS_ne, _⟩
      rw [hS_empty] at hS_ne
      exact absurd hS_ne (Finset.not_nonempty_empty)
    have h_disj_empty_lh : Disjoint P_empty (P_low ∪ P_high) := by
      rw [Finset.disjoint_union_right]
      exact ⟨h_disj_empty_low, h_disj_empty_high⟩
    have h_disj_emp_low_high : Disjoint (P_empty ∪ P_low) P_high := by
      rw [Finset.disjoint_union_left]
      exact ⟨h_disj_empty_high, h_disj_low_high⟩
    have h_sum_split :
        (∑ S ∈ (FTQCLib.Codes.supp v).powerset, funcDerivPhaseSubset S g 0)
          = (∑ S ∈ P_empty, funcDerivPhaseSubset S g 0)
              + (∑ S ∈ P_low, funcDerivPhaseSubset S g 0)
              + (∑ S ∈ P_high, funcDerivPhaseSubset S g 0) := by
      rw [h_split]
      rw [Finset.sum_union h_disj_emp_low_high]
      rw [Finset.sum_union h_disj_empty_low]
    -- Empty contribution: g 0.
    have h_empty_eq : (∑ S ∈ P_empty, funcDerivPhaseSubset S g 0) = g 0 := by
      rw [hP_empty_def]
      -- P_empty contains only ∅.
      have h_P_empty_eq : (FTQCLib.Codes.supp v).powerset.filter (fun S => S = ∅)
                       = ({∅} : Finset (Finset (Fin n))) := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · intro hS; rw [hS]; exact ⟨Finset.empty_subset _, rfl⟩
      rw [h_P_empty_eq]
      rw [Finset.sum_singleton, funcDerivPhaseSubset_empty]
    -- High contribution: 2π · K_high (integer).
    have h_high_each : ∀ S ∈ P_high, ∃ kS : ℤ,
        funcDerivPhaseSubset S g 0 = 2 * Real.pi * (kS : ℝ) := by
      intro S hS
      rw [hP_high_def, Finset.mem_filter] at hS
      obtain ⟨_, _, hScard⟩ := hS
      exact funcDerivPhaseSubset_vanish_mod_2pi_of_card_gt_level
        hk h_hier_g hScard
    choose khigh_data h_high_eq using h_high_each
    set K_high : ℤ := ∑ S ∈ P_high.attach, khigh_data S.val S.property
      with hK_high_def
    have h_high_sum :
        (∑ S ∈ P_high, funcDerivPhaseSubset S g 0) = 2 * Real.pi * (K_high : ℝ) := by
      rw [← Finset.sum_attach P_high (fun S => funcDerivPhaseSubset S g 0)]
      rw [hK_high_def]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      exact h_high_eq S.val S.property
    -- Low contribution: sum of (cS S).val/2^k + 2π · K_low.
    have h_low_each : ∀ S ∈ P_low,
        funcDerivPhaseSubset S g 0
          = 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k
              + 2 * Real.pi * (kintS S : ℝ) := by
      intro S hS
      rw [hP_low_def, Finset.mem_filter] at hS
      obtain ⟨_, hS_ne, hSk⟩ := hS
      exact h_eq S hS_ne hSk
    set K_low : ℤ := ∑ S ∈ P_low, kintS S with hK_low_def
    have h_low_sum :
        (∑ S ∈ P_low, funcDerivPhaseSubset S g 0)
          = (∑ S ∈ P_low, 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k)
              + 2 * Real.pi * (K_low : ℝ) := by
      have h_per_term :
          (∑ S ∈ P_low, funcDerivPhaseSubset S g 0)
            = ∑ S ∈ P_low, (2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k
                              + 2 * Real.pi * (kintS S : ℝ)) :=
        Finset.sum_congr rfl h_low_each
      rw [h_per_term, Finset.sum_add_distrib]
      congr 1
      rw [hK_low_def]
      push_cast
      rw [Finset.mul_sum]
    -- Now: g v = g 0 + (sum_low) + 2π · K_low + 2π · K_high.
    have h_g_v_eq :
        g v = g 0
              + (∑ S ∈ P_low, 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k)
              + 2 * Real.pi * (K_low : ℝ)
              + 2 * Real.pi * (K_high : ℝ) := by
      rw [h_mobius_g, h_sum_split, h_empty_eq, h_low_sum, h_high_sum]
      ring
    -- realPhase P v = (sum over non-empty low S) + 2π · J for some J.
    have h_realPhase_P :
        ∃ J : ℤ,
          DiagPhase.realPhase P v
            = (∑ S ∈ P_low,
                  2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k)
                + 2 * Real.pi * (J : ℝ) := by
      -- Compute realPhase P v from strictMobiusAssemblyPoly_eval.
      -- Strategy parallel to realPhase_mobiusAssemblyPoly_eq_sum_mod_two_pi.
      unfold DiagPhase.realPhase
      rw [strictMobiusAssemblyPoly_eval]
      set s : ZMod (2 ^ k) := ∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter
                              (fun S => S.Nonempty ∧ S.card ≤ k), cS S
        with hs_def
      set N : ℕ := ∑ S ∈ (FTQCLib.Codes.supp v).powerset.filter
                          (fun S => S.Nonempty ∧ S.card ≤ k), (cS S).val
        with hN_def
      have h_natCast : ((N : ℕ) : ZMod (2 ^ k)) = s := by
        rw [hs_def, hN_def, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro S _
        exact ZMod.natCast_zmod_val (cS S)
      have h_dvd_sum : ((2 ^ k : ℕ) : ℤ) ∣ ((s.val : ℤ) - (N : ℤ)) := by
        rw [← @ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        have h1 : ((s.val : ℕ) : ZMod (2 ^ k)) = s := ZMod.natCast_zmod_val s
        rw [h1, h_natCast]
        ring
      obtain ⟨J, hJ⟩ := h_dvd_sum
      refine ⟨J, ?_⟩
      -- s.val = N + 2^k · J in ℤ. The filter form equals P_low definitionally.
      have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have h_pow_ne : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h_pow_pos
      have h_real_eq :
          ((s.val : ℝ)) - ((N : ℝ)) = ((2 ^ k : ℕ) : ℝ) * (J : ℝ) := by
        have h_cast : (((s.val : ℤ) - (N : ℤ)) : ℝ)
                    = ((((2 ^ k : ℕ) : ℤ) * J) : ℝ) := by
          exact_mod_cast hJ
        push_cast at h_cast
        push_cast
        linarith
      have h_sum_real :
          ((N : ℝ)) = (∑ S ∈ P_low, ((cS S).val : ℝ)) := by
        rw [hN_def, hP_low_def]; push_cast; rfl
      have h_pow_real_eq : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; rfl
      rw [h_pow_real_eq] at h_real_eq
      have h_sum_factor :
          (∑ S ∈ P_low, 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k)
          = 2 * Real.pi * ((N : ℝ)) / (2 : ℝ) ^ k := by
        rw [h_sum_real, ← Finset.sum_div, ← Finset.mul_sum]
      -- Show: 2π · s.val/2^k = (sum factor) + 2π · J.
      -- Filter form of sum is definitionally P_low.
      change 2 * Real.pi * (s.val : ℝ) / (2 : ℝ) ^ k
              = (∑ S ∈ P_low, 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k)
                  + 2 * Real.pi * (J : ℝ)
      rw [h_sum_factor]
      field_simp
      linarith
    obtain ⟨J, hJ⟩ := h_realPhase_P
    -- Now compute exp(I · g v) = exp(I · g 0) · exp(I · realPhase P v).
    -- g v = g 0 + (sum_low_real) + 2π · (K_low + K_high).
    -- realPhase P v = (sum_low_real) + 2π · J.
    -- So g v - g 0 = realPhase P v - 2π · J + 2π · (K_low + K_high)
    --             = realPhase P v + 2π · (K_low + K_high - J).
    set int_offset : ℤ := K_low + K_high - J with h_int_offset_def
    have h_sum_eq_realPhase :
        (∑ S ∈ P_low, 2 * Real.pi * ((cS S).val : ℝ) / (2 : ℝ) ^ k)
          = DiagPhase.realPhase P v - 2 * Real.pi * (J : ℝ) := by
      linarith [hJ]
    have h_g_v_minus_g0 :
        g v = g 0 + DiagPhase.realPhase P v
                + 2 * Real.pi * (int_offset : ℝ) := by
      rw [h_sum_eq_realPhase] at h_g_v_eq
      rw [h_int_offset_def]
      push_cast
      linarith [h_g_v_eq]
    -- Now exp(I · g v) = exp(I · (g 0 + realPhase P v + 2π · int_offset))
    --                  = exp(I · g 0) · exp(I · realPhase P v) · exp(I · 2π · int_offset)
    --                  = exp(I · g 0) · exp(I · realPhase P v).
    rw [h_g_v_minus_g0]
    -- exp(I · (g 0 + realPhase P v + 2π · int_offset)) = exp(I · g 0) · exp(I · realPhase P v)
    -- (the 2π · int_offset is absorbed via Complex.exp_int_mul_two_pi_mul_I).
    have h_split_complex :
        Complex.exp (Complex.I *
            ((g 0 + DiagPhase.realPhase P v
              + 2 * Real.pi * (int_offset : ℝ) : ℝ) : ℂ))
          = Complex.exp (Complex.I * (g 0 : ℂ))
              * Complex.exp (Complex.I * (DiagPhase.realPhase P v : ℂ)) := by
      have h_eq : Complex.I *
            ((g 0 + DiagPhase.realPhase P v
              + 2 * Real.pi * (int_offset : ℝ) : ℝ) : ℂ)
          = Complex.I * (g 0 : ℂ)
              + Complex.I * (DiagPhase.realPhase P v : ℂ)
              + (int_offset : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [h_eq, Complex.exp_add, Complex.exp_add]
      rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h_split_complex]
    ring
  · -- P.effectiveLevel ≤ k.
    exact strictMobiusAssemblyPoly_effectiveLevel_le hk cS h_dvd h_zero
  · -- coeff 0 P = 0.
    exact strictMobiusAssemblyPoly_coeff_zero cS

end FTQCLib.Hilbert

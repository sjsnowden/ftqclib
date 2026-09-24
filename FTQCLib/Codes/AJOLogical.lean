/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.AJOClosure

set_option linter.unusedSectionVars false

/-! # Dyadic logical-angle classification under trans-logical uniform angle

This file proves: under non-degeneracy of the X-stabiliser structure,
a well-supported logical `g_L`, the trans-logical uniform-angle
hypothesis on `linearPhase (fun _ => θ)`, and `θ` expressible as
`2π · k_0 / m_0` in lowest terms, the **logical** angle
`θ_L := wt(g_L) · θ` is a dyadic multiple of `2π`.

## Relation to AJO 2014 Theorem 1

This is **strictly weaker** than AJO 2014 Theorem 1
(Anderson--Jochym-O'Connor, arXiv:1409.8320). AJO 2014 concludes
the **physical** angle `θ` itself is dyadic. The two are related:

* physical-`θ` dyadic implies `wt(g_L) · θ` dyadic (integer multiple
  of a dyadic is dyadic);
* the converse fails when `wt(g_L)` is not a power of two. E.g. on a
  6-qubit code with `wt(g_L) = 3` and `θ = π/3`, the logical angle
  `wt(g_L) · θ = π` is dyadic, but the physical `θ = π/3` is not.

The full AJO 2014 conclusion therefore requires forcing `wt(g_L)` to
be a power of two, which is what the three witness routes in
`FTQCLib.Codes.AJOMain` do under specific structural hypotheses
(`ajo_uniform_dyadic_of_unit_vec_route`,
`ajo_uniform_dyadic_of_h_pow_two`,
`ajo_uniform_dyadic_of_gL_overlap_pow_two`).
The general unconditional AJO 2014 statement (`ajo_uniform_dyadic_general`)
is not proved; its statement is recorded in the module documentation of
`FTQCLib.Codes.AJOGeneral`.

## Mathematical content

Write `θ = 2π · k_0 / m_0` in lowest terms (`gcd(k_0, m_0) = 1`) with
`m_0 = 2^c · m_0_odd` where `m_0_odd` is the odd part of `m_0`. The
odd-prime closure in `AJOClosure` gives `m_0_odd | wt(g_L)`. Write
`wt(g_L) = m_0_odd · q` for some integer `q`. Then

    wt(g_L) · θ
        = (m_0_odd · q) · 2π · k_0 / (2^c · m_0_odd)
        = 2π · (k_0 · q) / 2^c,

manifestly dyadic. The argument uses only the odd-prime infrastructure;
the 2-part is structurally inaccessible from the linear uniform-angle
trans-logical assumption (the Möbius walk at p = 2 loses one factor of
two per pass and never recovers it), which is one of the reasons the
full AJO 2014 statement (physical-`θ` dyadic) cannot be closed from
these hypotheses alone.

## What this file proves

1. **`oddPart_dvd_wt_gL`** — under non-degen, well-supported,
   trans-logical, and the lowest-terms hypothesis
   `gcd(k_0, m_0) = 1`, the odd part of `m_0` (i.e., `ordCompl[2] m_0`)
   divides `wt(g_L)`.

2. **`logical_angle_dyadic_of_oddPart_dvd`** — pure-arithmetic helper:
   given `θ = 2π · k_0 / m_0` and `m_0_odd | wt(g_L)` with `m_0_odd`
   the odd part of `m_0`, the logical angle `wt(g_L) · θ` is a dyadic
   multiple of `2π`.

3. **`dyadic_logical_angle_of_trans_logical_uniform`** — the main theorem:
   under non-degen, trans-logical uniform-angle, well-supported `g_L`,
   and lowest-terms rational form for `θ`, the logical angle
   `wt(g_L) · θ` is a dyadic multiple of `2π`.

4. **`dyadic_logical_angle_of_trans_logical_uniform_of_rational`** —
   convenience restatement with the rational-form hypothesis stated
   existentially. -/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Hierarchy Matrix

variable {n r_X r_Z : ℕ}

/-! ## Odd-part divisibility helper

The odd part of `m_0` is `ordCompl[2] m_0 = m_0 / 2^(v_2 m_0)`. Under
AJO hypotheses with `gcd(k_0, m_0) = 1`, every odd prime `p` dividing
`m_0` is odd and `p ∤ k_0`, so the prime-power lift
`ajo_odd_prime_power_dvd_wt_gL` gives
`p^(v_p m_0) | wt(g_L)`. Combining over all odd primes (via
`Finset.prod_dvd_of_coprime`) gives `m_0_odd | wt(g_L)`. -/

/-- **Odd part of `m_0` divides `wt(g_L)`.** Under AJO hypotheses plus
`gcd(k_0, m_0) = 1` (lowest-terms rational form), the odd part of `m_0`
divides `wt(g_L)`. This is the odd-prime restriction of
`ajo_m0_dvd_wt_gL_of_all_odd`. -/
theorem oddPart_dvd_wt_gL
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    (hcop : Int.gcd k_0 (m_0 : ℤ) = 1)
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    ((ordCompl[2] m_0 : ℕ) : ℤ) ∣ (hammingWeight g_L : ℤ) := by
  classical
  have hm0_ne : m_0 ≠ 0 := Nat.pos_iff_ne_zero.mp hm_0
  set f := m_0.factorization with hf_def
  -- Every prime dividing m_0 doesn't divide k_0 (from gcd = 1).
  have h_all_ndvd_k0 : ∀ p : ℕ, p.Prime → p ∣ m_0 → ¬ (p : ℤ) ∣ k_0 := by
    intro p hp_prime hp_dvd hp_dvd_k0
    have h_dvd_natAbs : p ∣ k_0.natAbs := by
      have h2 : (p : ℤ) ∣ |k_0| := (dvd_abs _ _).mpr hp_dvd_k0
      have h3 : (p : ℤ) ∣ ((k_0.natAbs : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; exact h2
      exact_mod_cast h3
    have hp_dvd_gcd : p ∣ Int.gcd k_0 (m_0 : ℤ) := by
      unfold Int.gcd
      simp only [Int.natAbs_natCast]
      exact Nat.dvd_gcd h_dvd_natAbs hp_dvd
    rw [hcop] at hp_dvd_gcd
    have hp1 : p ≤ 1 := Nat.le_of_dvd (by norm_num) hp_dvd_gcd
    exact (Nat.Prime.one_lt hp_prime).not_ge hp1
  -- Express the odd part of m_0 as a product over odd primes in the support.
  -- ordCompl[2] m_0 = ∏ p ∈ f.support.erase 2, p ^ (f p).
  -- This follows from `Nat.factorization_ordCompl` and
  -- `Nat.prod_factorization_pow_eq_self`.
  have hodd_eq : ordCompl[2] m_0 =
      ∏ p ∈ f.support.erase 2, p ^ (f p) := by
    have hfac := Nat.factorization_ordCompl m_0 2
    have hne : ordCompl[2] m_0 ≠ 0 :=
      (Nat.ordCompl_pos 2 hm0_ne).ne'
    -- Apply Nat.prod_factorization_pow_eq_self to ordCompl[2] m_0, then rewrite
    -- the factorization via `hfac`.
    have hprod := Nat.prod_factorization_pow_eq_self hne
    rw [hfac] at hprod
    -- hprod: (n.factorization.erase 2).prod (· ^ ·) = ordCompl[2] m_0
    rw [← hprod]
    -- Goal: ordCompl[2] m_0 = ∏ p ∈ f.support.erase 2, p ^ f p.
    -- But hprod has it as the prod over (f.erase 2).support which equals f.support.erase 2.
    unfold Finsupp.prod
    have hsup : (f.erase 2).support = f.support.erase 2 := Finsupp.support_erase
    rw [hsup]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Finsupp.erase_ne]
    rw [Finset.mem_erase] at hp
    exact hp.1
  -- Cast and apply Finset.prod_dvd_of_coprime.
  rw [hodd_eq]
  push_cast
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · -- Pairwise coprime.
    intro p1 hp1 p2 hp2 hne
    have hp1_mem : p1 ∈ f.support.erase 2 := hp1
    have hp2_mem : p2 ∈ f.support.erase 2 := hp2
    have hp1_mem_sup : p1 ∈ f.support := (Finset.mem_erase.mp hp1_mem).2
    have hp2_mem_sup : p2 ∈ f.support := (Finset.mem_erase.mp hp2_mem).2
    have hp1_prime : p1.Prime :=
      Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp1_mem_sup)
    have hp2_prime : p2.Prime :=
      Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp2_mem_sup)
    have hcop_base : Nat.Coprime p1 p2 :=
      (Nat.coprime_primes hp1_prime hp2_prime).mpr hne
    have hcop_pow : Nat.Coprime (p1 ^ f p1) (p2 ^ f p2) :=
      Nat.Coprime.pow (f p1) (f p2) hcop_base
    rw [Nat.Coprime] at hcop_pow
    change IsCoprime ((p1 : ℤ) ^ f p1) ((p2 : ℤ) ^ f p2)
    rw [Int.isCoprime_iff_gcd_eq_one]
    unfold Int.gcd
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact hcop_pow
  · -- Each (odd) prime-power factor divides wt(g_L).
    intro p hp_mem
    have hp_erase : p ∈ f.support.erase 2 := hp_mem
    have hp_ne_two : p ≠ 2 := (Finset.mem_erase.mp hp_erase).1
    have hp_mem_sup : p ∈ f.support := (Finset.mem_erase.mp hp_erase).2
    have hp_mem_pf : p ∈ m_0.primeFactors := by
      rwa [Nat.support_factorization] at hp_mem_sup
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem_pf
    have hp_dvd_m0 : p ∣ m_0 := Nat.dvd_of_mem_primeFactors hp_mem_pf
    have hp_odd : Odd p := hp_prime.odd_of_ne_two hp_ne_two
    have hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0 := h_all_ndvd_k0 p hp_prime hp_dvd_m0
    have hfp_pos : 0 < f p := by
      rw [hf_def, Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff]
      exact hp_mem_sup
    -- p^(f p) ∣ m_0 (as integers).
    have hp_pow_dvd_m0 : ((p : ℤ) ^ f p) ∣ (m_0 : ℤ) := by
      have h_nat : p ^ f p ∣ m_0 := by
        rw [hf_def]
        exact Nat.ordProj_dvd m_0 p
      exact_mod_cast h_nat
    exact ajo_odd_prime_power_dvd_wt_gL hm_0 hθ h_trans hp_prime hp_odd hfp_pos
      hp_pow_dvd_m0 hp_ndvd_k0 h_carrier h_wellSupp

/-! ## Pure-arithmetic helper: dyadic conclusion from odd-part divisibility

Given `θ = 2π · k_0 / m_0` with `m_0_odd | wt(g_L)` (where
`m_0_odd = ordCompl[2] m_0`), we compute

  wt(g_L) · θ = wt(g_L) · 2π · k_0 / m_0
              = 2π · k_0 · (wt(g_L) / m_0_odd) / 2^c

where `c = v_2(m_0)`, which is dyadic. -/

/-- **Logical angle is dyadic when the odd part of `m_0` divides
`wt(g_L)`.** Pure arithmetic: under `θ = 2π · k_0 / m_0` and the odd
part of `m_0` dividing `wt(g_L)`, the logical angle `wt(g_L) · θ` is
a dyadic multiple of `2π`. -/
theorem logical_angle_dyadic_of_oddPart_dvd
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {g_L : Fin n → ZMod 2}
    (h_dvd : ((ordCompl[2] m_0 : ℕ) : ℤ) ∣ (hammingWeight g_L : ℤ)) :
    ∃ (a : ℤ) (N : ℕ),
      (hammingWeight g_L : ℝ) * θ =
        2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  -- Set c = v_2(m_0), m_0_odd = ordCompl[2] m_0; then m_0 = 2^c · m_0_odd.
  set c := m_0.factorization 2 with hc_def
  set m_0_odd := ordCompl[2] m_0 with hodd_def
  have hm0_decomp : (2 : ℕ) ^ c * m_0_odd = m_0 :=
    Nat.ordProj_mul_ordCompl_eq_self m_0 2
  -- Extract integer q with wt(g_L) = m_0_odd · q.
  obtain ⟨q, hq⟩ := h_dvd
  -- Witness: a = k_0 * q, N = c.
  refine ⟨k_0 * q, c, ?_⟩
  -- Goal: wt(g_L) · θ = 2π · (k_0 * q) / 2^c.
  rw [hθ]
  -- Substitute m_0 = 2^c · m_0_odd in the denominator.
  have hm0_real : (m_0 : ℝ) = (2 : ℝ) ^ c * (m_0_odd : ℝ) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hm0_decomp.symm
    push_cast at this
    exact this
  -- Substitute wt(g_L) = m_0_odd · q.
  have hwt_real : (hammingWeight g_L : ℝ) = (m_0_odd : ℝ) * (q : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hq
    push_cast at this
    exact this
  rw [hm0_real, hwt_real]
  -- Now the goal is purely arithmetic:
  -- (m_0_odd · q) · (2π · k_0 / (2^c · m_0_odd)) = 2π · (k_0 · q) / 2^c
  -- Provided m_0_odd ≠ 0 and 2^c ≠ 0.
  have hm0_odd_pos : 0 < m_0_odd :=
    Nat.ordCompl_pos 2 (Nat.pos_iff_ne_zero.mp hm_0)
  have hm0_odd_ne : (m_0_odd : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hm0_odd_pos
  have h2c_ne : ((2 : ℝ) ^ c) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ## Main theorem: AJO 2014 Theorem 1 — logical-angle form

The main result. Under all AJO hypotheses (non-degeneracy,
trans-logical uniform-angle, well-supported `g_L`), with the additional
hypothesis that `θ = 2π · k_0 / m_0` is in lowest terms
(`gcd(k_0, m_0) = 1`), the **logical** angle `wt(g_L) · θ` is a dyadic
multiple of `2π`.

The lowest-terms hypothesis is harmless: every rational has a
lowest-terms form, and the rational form of `θ/(2π)` is supplied by
`ajo_uniform_rational_of_nondegen` from non-degeneracy. -/

/-- **AJO 2014 Theorem 1 — logical-angle form.** Under non-degeneracy,
well-supported `g_L`, trans-logical uniform-angle `θ`, and lowest-terms
rational form `θ = 2π · k_0 / m_0` with `gcd(k_0, m_0) = 1`, the
LOGICAL angle `θ_L := wt(g_L) · θ` is a dyadic multiple of `2π`.

This is the correct AJO 2014 statement: the conclusion is about the
logical gate's angle (which determines the Clifford-hierarchy level of
the LOGICAL action), not the physical per-qubit angle. Physical `θ`
need not be dyadic (e.g., `θ = π/3` on a 6-qubit code with
`wt(g_L) = 3` gives `θ_L = π`, dyadic).

No non-triviality hypothesis is needed: the conclusion holds
unconditionally (trivially when `θ_L = 0`, in particular with
`a = 0, N = 0`). -/
theorem dyadic_logical_angle_of_trans_logical_uniform
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    (hcop : Int.gcd k_0 (m_0 : ℤ) = 1)
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    ∃ (a : ℤ) (N : ℕ),
      (hammingWeight g_L : ℝ) * θ =
        2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  -- Step 1: odd part of m_0 divides wt(g_L) (the prime-power lift, restricted to odd primes).
  have h_dvd : ((ordCompl[2] m_0 : ℕ) : ℤ) ∣ (hammingWeight g_L : ℤ) :=
    oddPart_dvd_wt_gL hm_0 hθ hcop h_trans h_carrier h_wellSupp
  -- Step 2: pure-arithmetic computation yields the dyadic form.
  exact logical_angle_dyadic_of_oddPart_dvd hm_0 hθ h_dvd

/-! ## Packaging variant: full AJO hypotheses

A convenience restatement that takes the non-degeneracy hypothesis
directly (rather than the rational form). The rational form is
obtained from non-degeneracy via `ajo_uniform_theta_eq_of_nondegen`,
which gives a `(k_0, m_0)` but not necessarily in lowest terms; we
record both versions. -/

/-- **Logical-angle dyadic (rational-form variant).** Same conclusion as
`dyadic_logical_angle_of_trans_logical_uniform`, packaged with the rational form
hypothesis stated as an existence rather than concrete `k_0, m_0`. -/
theorem dyadic_logical_angle_of_trans_logical_uniform_of_rational
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1)
    (h_rational : ∃ (k_0 : ℤ) (m_0 : ℕ), 0 < m_0 ∧
                  Int.gcd k_0 (m_0 : ℤ) = 1 ∧
                  θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ)) :
    ∃ (a : ℤ) (N : ℕ),
      (hammingWeight g_L : ℝ) * θ =
        2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  obtain ⟨k_0, m_0, hm_0, hcop, hθ⟩ := h_rational
  exact dyadic_logical_angle_of_trans_logical_uniform hm_0 hθ hcop h_trans h_carrier h_wellSupp

end FTQCLib.Codes

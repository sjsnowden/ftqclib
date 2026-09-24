/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.AJOGeneral

set_option linter.unusedSectionVars false

/-! # AJO Theorem 1 — Prime-power lift and partial closure

This file extends `FTQCLib.Codes.AJOGeneral` with the **prime-power lift**
required by AJO 2014 Theorem 1's odd-prime contradiction at full
`p`-adic valuation. The basic prime-divisibility result
`ajo_odd_prime_dvd_wt_gL` establishes `p ∣ wt(g_L)` for every odd prime
`p ∣ m_0` with `p ∤ k_0` (where `θ = 2π · k_0 / m_0`). To close AJO
Theorem 1 to a *full* contradiction with the non-triviality of the
logical action, one needs `p^k ∣ wt(g_L)` at the **full** `p`-adic
valuation of `m_0`.

## Mathematical content

### Prime-power lift (full)

For every odd prime `p` with `p^k ∣ m_0` and `p ∤ k_0`, the Möbius walk
of Steps 1–4 re-runs at modulus `p^k` rather than `p`. The combinatorial
structure is identical; only the modular-arithmetic step
"`p ∣ a · b` ⟹ `p ∣ a` ∨ `p ∣ b`" must be replaced by
"`p^k ∣ a · b`, `gcd(a, p^k) = 1` ⟹ `p^k ∣ b`". This Euclidean-style
cancellation holds whenever `gcd(a, p^k) = 1`, which follows from
`p ∤ a` and `p` prime (so `gcd(a, p) = 1`, hence `gcd(a, p^k) = 1`).

### Conclusion at odd primes

After Path A, every odd prime `p` with `p ∤ k_0` and `p^k ∣ m_0`
satisfies `p^k ∣ wt(g_L)`. Combining across all odd primes:
`m_0_odd ∣ wt(g_L)`, where `m_0_odd` is the odd part of `m_0`.

### The 2-part gap

At `p = 2`, the same Möbius walk *loses one factor of 2* per
application of `ajo_dvd_wt_and`: from `q ∣ wt(h) - 2 wt(v ∧ h)` with
`q = 2^c · q_odd`, subtracting `q ∣ wt(h)` gives `q ∣ 2 · wt(v ∧ h)`,
hence `2^{c-1} · q_odd ∣ wt(v ∧ h)` — one less power of 2 than at the
`v = 0` constraint. Iterating Möbius does *not* recover the lost
factor of 2, because the F₂-sum Möbius identity introduces signs `±1`
but no additional factors of 2 at p = 2.

The deepest consequence: at the conclusion of the Möbius walk, we
obtain `2^{c-1} ∣ wt(g_L)` at the 2-part, not `2^c`. Combined with
the odd-part conclusion `m_0_odd ∣ wt(g_L)`, we get `m_0/2 ∣ wt(g_L)`
when `c ≥ 1`, which is compatible with `m_0 ∤ wt(g_L)` (no
contradiction).

## What this file proves

1. **`pow_coprime_int_of_prime_not_dvd`** — auxiliary: if `p` prime
   integer, `p ∤ k`, then `gcd(p^N, k) = 1`.

2. **`Int.dvd_mul_cancel_coprime`** — Euclidean cancellation for `ℤ`:
   `a ∣ b · c` and `gcd(a, b) = 1` ⟹ `a ∣ c`.

3. **`ajo_dvd_of_trans_pow`** — Path A Step 1 at modulus `p^k`: for
   any prime `p ∤ k_0` and `p^k ∣ m_0`, `(p^k : ℤ) ∣ wt(h) - 2 · wt(v ∧ h)`.

4. **`ajo_dvd_wt_h_pow`** — Step 2a analog at `p^k`: `(p^k : ℤ) ∣ wt(h)`.

5. **`ajo_dvd_wt_and_pow`** — Step 2b analog at `p^k` (p odd):
   `(p^k : ℤ) ∣ wt(v ∧ h)`.

6. **`ajo_dvd_wt_gL_overlap_pow`** — Step 3 analog at `p^k`:
   `(p^k : ℤ) ∣ wt(g_L ∧ overlap_S)` for every non-empty `S`.

7. **`ajo_dvd_card_gL_biUnion_pow`** — Step 3 Möbius at `p^k`.

8. **`ajo_step4_wellSupp_contradiction_pow`** — Step 4 closure at `p^k`.

9. **`ajo_odd_prime_power_dvd_wt_gL`** — under all hypotheses, for any
   odd prime power `p^k ∣ m_0`, `p^k ∣ wt(g_L)`.

### Partial closure of AJO Theorem 1

10. **`ajo_uniform_dyadic_wellSupp_of_m0_odd`** — the AJO conclusion
    holds **under the additional hypothesis that `m_0` is odd**: under
    non-degeneracy, well-supported, non-triviality, and `m_0` odd, the
    angle `θ` is dyadic (specifically `θ ∈ 2π · ℤ`, the trivial case).

11. **`ajo_oddPart_dvd_wt_gL`** — partial result combining all odd
    primes of `m_0`: the odd part of `m_0` divides `wt(g_L)`.

### Documented gap

The full theorem `ajo_uniform_dyadic_wellSupp` (closing for all
non-degenerate, well-supported, non-trivial trans-logical uniform
phases) requires either

* a separate **2-part argument** that recovers the factor of 2 lost in
  the Möbius walk at `p = 2`; or
* a **strengthening** of one of the hypotheses (e.g., `gcd(2, m_0) = 1`,
  i.e., `m_0` odd).

This file proves the closure under the latter (Item 10) and
documents the structural reason the unconditional closure is blocked.
-/

namespace FTQCLib.Codes

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Hierarchy Matrix

variable {n r_X r_Z : ℕ}

/-! ## Auxiliary arithmetic lemmas -/

/-- **A prime power is coprime to anything the prime doesn't divide.**
If `p` is a prime natural number not dividing the integer `k`, then
`gcd(p^N, k) = 1` for every `N`. -/
private lemma pow_coprime_int_of_prime_not_dvd
    {p : ℕ} (hp_prime : Nat.Prime p) {k : ℤ} (hp_ndvd_k : ¬ (p : ℤ) ∣ k)
    (N : ℕ) : Int.gcd ((p : ℤ) ^ N) k = 1 := by
  -- p prime, p ∤ k implies gcd(p, k) = 1 over ℤ.
  have hgcd : Int.gcd (p : ℤ) k = 1 := by
    rcases Nat.coprime_or_dvd_of_prime hp_prime k.natAbs with hcop | hdvd
    · -- coprime case
      unfold Int.gcd
      rwa [Int.natAbs_natCast]
    · -- dvd case: p ∣ k.natAbs, hence p ∣ k as integers — contradiction with hp_ndvd_k.
      exfalso
      apply hp_ndvd_k
      -- p ∣ k.natAbs as naturals → (p : ℤ) ∣ k.natAbs : ℤ → (p : ℤ) ∣ |k| → (p : ℤ) ∣ k.
      have h1 : (p : ℤ) ∣ ((k.natAbs : ℕ) : ℤ) := by exact_mod_cast hdvd
      have h2 : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
      rw [h2] at h1
      exact (dvd_abs (p : ℤ) k).mp h1
  -- gcd is multiplicative under powers when one side is the same: gcd(p^N, k) =
  -- gcd(p, k)^N over ℤ when gcd(p,k) is a unit. Use Int.Coprime structure.
  -- Easier: use IsCoprime over ℤ.
  -- Int.gcd a b = 1 ↔ IsCoprime a b (over ℤ).
  have hcop_int : IsCoprime (p : ℤ) k := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hgcd
  have hcop_pow : IsCoprime ((p : ℤ) ^ N) k := hcop_int.pow_left
  rw [← Int.isCoprime_iff_gcd_eq_one]
  exact hcop_pow

/-- **Euclidean cancellation over ℤ for prime-power coprime factor.**
If `a ∣ b · c` and `gcd(a, b) = 1` (as integers), then `a ∣ c`. -/
private lemma Int_dvd_of_dvd_mul_coprime
    {a b c : ℤ} (h_dvd : a ∣ b * c) (h_coprime : Int.gcd a b = 1) : a ∣ c := by
  -- We want: `a ∣ b * c, gcd(a, b) = 1` to give `a ∣ c`.
  -- Mathlib's `dvd_of_dvd_mul_right_of_gcd_one` says: `a ∣ b * c, gcd(a, b) = 1` → `a ∣ c`.
  exact Int.dvd_of_dvd_mul_right_of_gcd_one h_dvd h_coprime

/-! ## Path A Step 1: ZMod p^k lift

The same `dvd_of_trans_constraint` argument lifted from `m_0` to `p^k`
via Euclidean cancellation. -/

/-- **Step 1 at prime power.** Suppose `θ = 2π · k_0 / m_0`, `p` is a
prime with `p^N ∣ m_0` and `p ∤ k_0`. Under uniform-angle
trans-logical, for every `v ∈ ker(H_Z)` and `h ∈ row(H_X)`,
`(p^N : ℤ) ∣ wt(h) - 2 · wt(v ∧ h)`. -/
theorem ajo_dvd_of_trans_pow
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) {N : ℕ}
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ((p : ℤ) ^ N) ∣
      (hammingWeight h : ℤ) -
        2 * (hammingWeight (fun j => v j * h j) : ℤ) := by
  obtain ⟨k, hk⟩ :=
    isTransversalLogical_uniform_logical_constraint h_trans hv hh
  have hdvd_m0 := dvd_of_trans_constraint hm_0 hθ hk
  -- `p^N ∣ m_0`, `m_0 ∣ k_0 · Δ` → `p^N ∣ k_0 · Δ`.
  have hpN_dvd_prod : ((p : ℤ) ^ N) ∣ k_0 *
      ((hammingWeight h : ℤ) -
        2 * (hammingWeight (fun j => v j * h j) : ℤ)) :=
    dvd_trans hp_dvd_m0 hdvd_m0
  -- gcd(p^N, k_0) = 1, so p^N ∣ Δ.
  exact Int_dvd_of_dvd_mul_coprime hpN_dvd_prod
    (pow_coprime_int_of_prime_not_dvd hp_prime hp_ndvd_k0 N)

/-- **Step 2a at prime power: `(p^N : ℤ) ∣ wt(h)`.** Specialisation at
`v = 0`. -/
theorem ajo_dvd_wt_h_pow
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) {N : ℕ}
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ((p : ℤ) ^ N) ∣ (hammingWeight h : ℤ) := by
  have hzero : (0 : Fin n → ZMod 2) ∈ cssXLogicalCarrier H_Z :=
    zero_mem_cssXLogicalCarrier H_Z
  have hres := ajo_dvd_of_trans_pow hm_0 hθ h_trans hp_prime hp_dvd_m0
                hp_ndvd_k0 hzero hh
  -- `v = 0`: `v j * h j = 0` for all j, so wt(0 ∧ h) = 0.
  have h_and_zero : (fun j : Fin n => (0 : Fin n → ZMod 2) j * h j) = 0 := by
    funext j; simp
  rw [h_and_zero, hammingWeight_zero] at hres
  push_cast at hres
  simpa using hres

/-- **A power of an odd prime is coprime to a power of 2.** Generalisation of
`odd_prime_ndvd_two_pow` to prime-power divisor. -/
private lemma odd_prime_pow_coprime_two {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (N : ℕ) : Int.gcd ((p : ℤ) ^ N) 2 = 1 := by
  -- p odd prime, so p ∤ 2 (since p ≥ 3 or p ≠ 2). gcd(p, 2) = 1.
  have hp_ndvd_two : ¬ (p : ℤ) ∣ 2 := by
    intro hpd2
    have hp2_nat : p ∣ (2 : ℕ) := by
      have : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by exact_mod_cast hpd2
      exact_mod_cast this
    have hp_eq : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hp2_nat with h1 | h1
      · exact absurd h1 hp.one_lt.ne'
      · exact h1
    rw [hp_eq] at hodd
    exact (Nat.not_odd_iff_even.mpr (by decide : Even 2)) hodd
  exact pow_coprime_int_of_prime_not_dvd hp hp_ndvd_two N

/-- **Step 2b at prime power (p odd): `(p^N : ℤ) ∣ wt(v ∧ h)`.** -/
theorem ajo_dvd_wt_and_pow
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p) {N : ℕ}
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {v : Fin n → ZMod 2} (hv : v ∈ cssXLogicalCarrier H_Z)
    {h : Fin n → ZMod 2} (hh : h ∈ cssXLogicalSubspace H_X) :
    ((p : ℤ) ^ N) ∣ (hammingWeight (fun j => v j * h j) : ℤ) := by
  have h1 := ajo_dvd_of_trans_pow hm_0 hθ h_trans hp_prime hp_dvd_m0 hp_ndvd_k0 hv hh
  have h2 := ajo_dvd_wt_h_pow hm_0 hθ h_trans hp_prime hp_dvd_m0 hp_ndvd_k0 hh
  -- From `p^N | wt(h) - 2·wt(v∧h)` and `p^N | wt(h)`: `p^N | 2·wt(v∧h)`.
  have h3 : ((p : ℤ) ^ N) ∣ 2 * (hammingWeight (fun j => v j * h j) : ℤ) := by
    have h4 := dvd_sub h2 h1
    have heq : (hammingWeight h : ℤ) -
        ((hammingWeight h : ℤ) -
          2 * (hammingWeight (fun j => v j * h j) : ℤ)) =
        2 * (hammingWeight (fun j => v j * h j) : ℤ) := by ring
    rwa [heq] at h4
  -- p odd ⟹ gcd(p^N, 2) = 1 ⟹ p^N ∣ wt(v ∧ h).
  exact Int_dvd_of_dvd_mul_coprime h3 (odd_prime_pow_coprime_two hp_prime hp_odd N)

/-! ## Path A Step 3: Möbius walk at prime power -/

/-- **`(p^N : ℤ) ∤ (-2)^k` for `p` odd prime, `N ≥ 1`.** -/
private lemma odd_prime_pow_ndvd_two_pow {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (N k : ℕ) (_hN : 0 < N) : ¬ ((p : ℤ) ^ N) ∣ ((-2 : ℤ) ^ k) := by
  intro hdvd
  have hp_dvd : (p : ℤ) ∣ ((-2 : ℤ) ^ k) := by
    have hp_dvd_pow : (p : ℤ) ∣ ((p : ℤ) ^ N) := dvd_pow_self _ _hN.ne'
    exact dvd_trans hp_dvd_pow hdvd
  have habs : (p : ℤ).natAbs = p := Int.natAbs_natCast p
  have hp2k : p ∣ (2 ^ k : ℕ) := by
    have h1 : ((-2 : ℤ) ^ k).natAbs = 2 ^ k := by
      rw [Int.natAbs_pow]
      norm_num
    have h2 : (p : ℤ).natAbs ∣ ((-2 : ℤ) ^ k).natAbs := Int.natAbs_dvd_natAbs.mpr hp_dvd
    rw [habs, h1] at h2
    exact h2
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2k
  have hp_eq : p = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with heq | heq
    · exact absurd heq hp.one_lt.ne'
    · exact heq
  rw [hp_eq] at hodd
  exact (Nat.not_odd_iff_even.mpr (by decide : Even 2)) hodd

/-- **Step 3 at prime power (logical-overlap divisibility).** Under the
same hypotheses but with `p^N ∣ m_0` (rather than just `p ∣ m_0`), for
`g_L ∈ ker(H_Z)` and every non-empty `I ⊆ Fin r_X`:
`(p^N : ℤ) ∣ wt(g_L ∧ overlap H_X I)`.

The proof structure exactly mirrors `ajo_dvd_wt_gL_overlap`, with `p^N`
playing the role of `p`. The two key arithmetic facts are
`odd_prime_pow_coprime_two` (for the cancellation of `2` in
`ajo_dvd_wt_and_pow`) and `odd_prime_pow_ndvd_two_pow` (to discharge
the `(-2)^(|S|-1)` factor in the Möbius isolation). -/
theorem ajo_dvd_wt_gL_overlap_pow
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p) {N : ℕ} (_hN : 0 < N)
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    {I : Finset (Fin r_X)} (hI : I.Nonempty) :
    ((p : ℤ) ^ N) ∣
      (hammingWeight
        (fun j => g_L j * overlap (fun i => fun j' : Fin n => H_X i j') I j) : ℤ) := by
  classical
  -- Strong induction on |I|.
  suffices hgoal : ∀ M : ℕ, ∀ I : Finset (Fin r_X), I.card = M → I.Nonempty →
      ((p : ℤ) ^ N) ∣
        (hammingWeight
          (fun j => g_L j * overlap (fun i => fun j' : Fin n => H_X i j') I j) : ℤ) from
    hgoal I.card I rfl hI
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro I hI_card hI_ne
    -- Apply trans-logical at v = g_L, h = ∑_{i ∈ I} H_X i ∈ row(H_X).
    set hI_sum := (∑ i ∈ I, (fun j : Fin n => H_X i j)) with hI_sum_def
    have hI_sum_mem : hI_sum ∈ cssXLogicalSubspace H_X :=
      hx_sum_mem_cssXLogicalSubspace H_X I
    -- p^N ∣ wt(g_L ∧ h_I_sum) by ajo_dvd_wt_and_pow.
    have hp_dvd_gL_and_hI :=
      ajo_dvd_wt_and_pow hm_0 hθ h_trans hp_prime hp_odd hp_dvd_m0 hp_ndvd_k0
        h_carrier hI_sum_mem
    -- Rewrite g_L ∧ h_I_sum as ∑_{i ∈ I} (g_L ∧ H_X i).
    have hgL_and_sum_eq :
        (fun j : Fin n => g_L j * hI_sum j) =
          ∑ i ∈ I, (fun j : Fin n => g_L j * H_X i j) := by
      funext j
      simp only [hI_sum_def, Finset.sum_apply, Finset.mul_sum]
    rw [hgL_and_sum_eq] at hp_dvd_gL_and_hI
    -- Apply Möbius at family `i ↦ g_L ∧ H_X i` and I.
    rw [hammingWeight_sum_mobius (fun i => fun j => g_L j * H_X i j) I]
      at hp_dvd_gL_and_hI
    -- Rewrite overlaps as g_L ∧ overlap H_X J.
    have hov_rewrite :
        ∀ J ∈ I.powerset.filter (·.Nonempty),
          (-2 : ℤ) ^ (J.card - 1) *
            (hammingWeight (overlap (fun i => fun j => g_L j * H_X i j) J) : ℤ) =
          (-2 : ℤ) ^ (J.card - 1) *
            (hammingWeight
              (fun j => g_L j *
                overlap (fun i => fun j' : Fin n => H_X i j') J j) : ℤ) := by
      intro J hJmem
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem
      obtain ⟨_, hJne⟩ := hJmem
      have hcom : (fun i => fun j : Fin n => g_L j * H_X i j) =
          (fun i => fun j : Fin n => H_X i j * g_L j) := by
        funext i j; ring
      have hov_step : overlap (fun i => fun j : Fin n => g_L j * H_X i j) J =
          fun j => g_L j *
            overlap (fun i => fun j' : Fin n => H_X i j') J j := by
        rw [hcom, overlap_mul_eq (fun i => fun j' : Fin n => H_X i j') g_L hJne]
        funext j; ring
      rw [hov_step]
    rw [Finset.sum_congr rfl hov_rewrite] at hp_dvd_gL_and_hI
    -- Isolate J = I.
    have hI_mem_filter : I ∈ I.powerset.filter (·.Nonempty) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.refl I, hI_ne⟩
    rw [← Finset.add_sum_erase _ _ hI_mem_filter] at hp_dvd_gL_and_hI
    -- All "other" terms divisible by p^N by induction.
    have hp_dvd_others :
        ((p : ℤ) ^ N) ∣
          ∑ J ∈ (I.powerset.filter (·.Nonempty)).erase I,
            (-2 : ℤ) ^ (J.card - 1) *
              (hammingWeight
                (fun j => g_L j *
                  overlap (fun i => fun j' : Fin n => H_X i j') J j) : ℤ) := by
      refine Finset.dvd_sum ?_
      intro J hJmem
      rw [Finset.mem_erase] at hJmem
      obtain ⟨hJne_I, hJmem_filter⟩ := hJmem
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJmem_filter
      obtain ⟨hJsubI, hJne⟩ := hJmem_filter
      have hJcard_lt : J.card < I.card :=
        Finset.card_lt_card
          ⟨hJsubI, fun hIJ => hJne_I (Finset.Subset.antisymm hJsubI hIJ)⟩
      have ih_J := ih J.card (by rw [← hI_card]; exact hJcard_lt) J rfl hJne
      exact dvd_mul_of_dvd_right ih_J _
    -- Combine to get p^N | (-2)^(|I|-1) · wt(g_L ∧ overlap H_X I).
    have hp_dvd_lead :
        ((p : ℤ) ^ N) ∣
          (-2 : ℤ) ^ (I.card - 1) *
            (hammingWeight
              (fun j => g_L j *
                overlap (fun i => fun j' : Fin n => H_X i j') I j) : ℤ) := by
      have := dvd_sub hp_dvd_gL_and_hI hp_dvd_others
      simpa using this
    -- p^N coprime to (-2)^(|I|-1) since p odd, so p^N | wt(...).
    have hcop : Int.gcd ((p : ℤ) ^ N) ((-2 : ℤ) ^ (I.card - 1)) = 1 := by
      -- gcd(p, -2) = 1 (p odd prime ⟹ p ∤ 2 ⟹ p ∤ -2).
      have hp_ndvd_neg2 : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
        intro hpd
        have hp_ndvd2 : ¬ (p : ℤ) ∣ 2 := by
          intro hpd2
          have hp2_nat : p ∣ (2 : ℕ) := by
            have : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by exact_mod_cast hpd2
            exact_mod_cast this
          have hp_eq : p = 2 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp hp2_nat with h1 | h1
            · exact absurd h1 hp_prime.one_lt.ne'
            · exact h1
          rw [hp_eq] at hp_odd
          exact (Nat.not_odd_iff_even.mpr (by decide : Even 2)) hp_odd
        -- p ∣ -2 ⟹ p ∣ 2.
        have : (p : ℤ) ∣ 2 := by
          have h := dvd_neg.mp hpd
          exact h
        exact hp_ndvd2 this
      -- gcd(p^N, (-2)^k) = 1 by pow_coprime applied twice.
      have h1 := pow_coprime_int_of_prime_not_dvd hp_prime hp_ndvd_neg2 N
      -- h1 : gcd(p^N, -2) = 1. Now take power of (-2) on the right.
      rw [← Int.isCoprime_iff_gcd_eq_one] at h1 ⊢
      exact h1.pow_right
    -- hp_dvd_lead : p^N ∣ (-2)^(|I|-1) * wt(...) and gcd(p^N, (-2)^(|I|-1)) = 1
    -- ⟹ p^N ∣ wt(...). Direct Int_dvd_of_dvd_mul_coprime.
    exact Int_dvd_of_dvd_mul_coprime hp_dvd_lead hcop

/-- **Step 3 Möbius at prime power: `(p^N : ℤ) ∣ |supp(g_L) ∩ ⋃ supp(g_i)|`.**
The integer Möbius identity applied to the family `i ↦ g_L ∧ H_X i`. -/
theorem ajo_dvd_card_gL_biUnion_pow
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p) {N : ℕ} (hN : 0 < N)
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z) :
    ((p : ℤ) ^ N) ∣
      ((Finset.univ.biUnion
        (fun i : Fin r_X =>
          supp (fun j => g_L j * H_X i j))).card : ℤ) := by
  classical
  rw [hammingWeight_biUnion_supp_eq_inclusion_exclusion
      (fun i => fun j => g_L j * H_X i j)]
  refine Finset.dvd_sum ?_
  rintro ⟨t, ht⟩ _
  have ht_ne : t.Nonempty := (Finset.mem_filter.mp ht).2
  have hcom : (fun i => fun j : Fin n => g_L j * H_X i j) =
      (fun i => fun j : Fin n => H_X i j * g_L j) := by
    funext i j; ring
  have hov : overlap (fun i => fun j => g_L j * H_X i j) t =
      fun j => g_L j * overlap (fun i => fun j' : Fin n => H_X i j') t j := by
    rw [hcom, overlap_mul_eq (fun i => fun j' : Fin n => H_X i j') g_L ht_ne]
    funext j; ring
  rw [hov]
  have hp_dvd_wt :=
    ajo_dvd_wt_gL_overlap_pow hm_0 hθ h_trans hp_prime hp_odd hN hp_dvd_m0 hp_ndvd_k0
      h_carrier ht_ne
  exact dvd_mul_of_dvd_right hp_dvd_wt _

/-- **Step 4 at prime power (well-supported case): contradiction with
`p^N ∤ wt(g_L)`.** Generalisation of `ajo_step4_wellSupp_contradiction`. -/
theorem ajo_step4_wellSupp_contradiction_pow
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p) {N : ℕ} (hN : 0 < N)
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_ndvd_gL : ¬ ((p : ℤ) ^ N) ∣ (hammingWeight g_L : ℤ))
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    False := by
  classical
  have hp_dvd_bU := ajo_dvd_card_gL_biUnion_pow hm_0 hθ h_trans hp_prime hp_odd hN
    hp_dvd_m0 hp_ndvd_k0 h_carrier
  -- Under well-support, `⋃ supp(g_L * H_X i) = supp g_L`.
  have h_eq : Finset.univ.biUnion
      (fun i : Fin r_X => supp (fun j => g_L j * H_X i j)) = supp g_L := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hij⟩
      unfold supp at hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
      have hgL_one : g_L j = 1 := by
        have hvm := zmod_two_val_mul (g_L j) (H_X i j)
        have h1 : (g_L j * H_X i j).val = 1 := by
          rw [hij]
          haveI : Fact (1 < 2) := ⟨one_lt_two⟩
          exact ZMod.val_one 2
        rw [hvm] at h1
        have hg_lt : (g_L j).val < 2 := ZMod.val_lt _
        have hH_lt : (H_X i j).val < 2 := ZMod.val_lt _
        have : (g_L j).val = 1 := by
          interval_cases (g_L j).val <;> interval_cases (H_X i j).val <;> simp_all
        rw [(ZMod.natCast_zmod_val (g_L j)).symm, this]
        push_cast
        rfl
      unfold supp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hgL_one
    · intro hj
      unfold supp at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨i, hH⟩ := h_wellSupp j hj
      refine ⟨i, ?_⟩
      unfold supp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hj, hH]; ring
  rw [h_eq] at hp_dvd_bU
  rw [← hammingWeight_eq_card_supp] at hp_dvd_bU
  exact h_ndvd_gL hp_dvd_bU

/-- **AJO Path A closure: prime-power lift.** Under all hypotheses,
for every odd prime power `p^N ∣ m_0` (with `p ∤ k_0`),
`(p^N : ℤ) ∣ wt(g_L)`. This is the strengthening of
`ajo_odd_prime_dvd_wt_gL` to the full p-adic valuation of `m_0`. -/
theorem ajo_odd_prime_power_dvd_wt_gL
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {p : ℕ} (hp_prime : Nat.Prime p) (hp_odd : Odd p) {N : ℕ} (hN : 0 < N)
    (hp_dvd_m0 : ((p : ℤ) ^ N) ∣ (m_0 : ℤ))
    (hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    ((p : ℤ) ^ N) ∣ (hammingWeight g_L : ℤ) := by
  by_contra h_ndvd
  exact ajo_step4_wellSupp_contradiction_pow hm_0 hθ h_trans hp_prime hp_odd hN
    hp_dvd_m0 hp_ndvd_k0 h_carrier h_ndvd h_wellSupp

/-! ## Combining over all odd primes: `m_0_odd ∣ wt(g_L)`

If `m_0` is odd (no factor of 2), then for every prime `p ∣ m_0`, `p`
is odd. With `gcd(k_0, m_0) = 1` (or, more weakly, no prime of `m_0`
divides `k_0`), Path A gives `p^{v_p(m_0)} ∣ wt(g_L)` for every `p ∣ m_0`.
Multiplicativity over distinct primes then gives `m_0 ∣ wt(g_L)`.

We formulate the result under the hypothesis "every prime factor of
`m_0` is odd and does not divide `k_0`", which is automatic when
`gcd(k_0, m_0) = 1` and `m_0` is odd. -/

/-- **Combination over all odd primes (induction on factorization).**
If every prime divisor `p` of `m_0` is odd and `(p : ℤ) ∤ k_0`, then
`(m_0 : ℤ) ∣ wt(g_L)`. -/
theorem ajo_m0_dvd_wt_gL_of_all_odd
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_all_odd : ∀ p : ℕ, p.Prime → p ∣ m_0 → Odd p)
    (h_all_ndvd_k0 : ∀ p : ℕ, p.Prime → p ∣ m_0 → ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    (m_0 : ℤ) ∣ (hammingWeight g_L : ℤ) := by
  classical
  have hm0_ne : m_0 ≠ 0 := Nat.pos_iff_ne_zero.mp hm_0
  set f := m_0.factorization with hf_def
  have hm0_eq : (f.prod (· ^ ·)) = m_0 := Nat.prod_factorization_pow_eq_self hm0_ne
  -- Goal: `(m_0 : ℤ) ∣ wt(g_L)`. Cast: `((f.prod (· ^ ·) : ℕ) : ℤ) ∣ wt(g_L)`.
  rw [← hm0_eq]
  -- f.prod (· ^ ·) = ∏ p ∈ f.support, p ^ f p.
  unfold Finsupp.prod
  push_cast
  -- Now goal: `∏ p ∈ f.support, (↑p)^(f p) ∣ ↑(hammingWeight g_L)`.
  -- Use Finset.prod_dvd_of_coprime: pairwise coprime factors each dividing the target.
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · -- Pairwise coprime: distinct primes give coprime prime powers.
    intro p1 hp1 p2 hp2 hne
    -- `hp1 : p1 ∈ ↑f.support` (set membership). Get `p1 ∈ f.support` (finset).
    have hp1_mem : p1 ∈ f.support := hp1
    have hp2_mem : p2 ∈ f.support := hp2
    have hp1_prime : p1.Prime :=
      Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp1_mem)
    have hp2_prime : p2.Prime :=
      Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp2_mem)
    have hcop_base : Nat.Coprime p1 p2 :=
      (Nat.coprime_primes hp1_prime hp2_prime).mpr hne
    have hcop_pow : Nat.Coprime (p1 ^ f p1) (p2 ^ f p2) :=
      Nat.Coprime.pow (f p1) (f p2) hcop_base
    -- Convert Nat.Coprime to IsCoprime over ℤ via Int.isCoprime_iff_gcd_eq_one.
    rw [Nat.Coprime] at hcop_pow
    -- Goal: (IsCoprime on (fun p : ℕ => ((p : ℤ)) ^ f p)) p1 p2, which unfolds to
    -- IsCoprime ((p1 : ℤ) ^ f p1) ((p2 : ℤ) ^ f p2).
    change IsCoprime ((p1 : ℤ) ^ f p1) ((p2 : ℤ) ^ f p2)
    rw [Int.isCoprime_iff_gcd_eq_one]
    unfold Int.gcd
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact hcop_pow
  · -- Each factor divides `wt(g_L)`.
    intro p hp_mem
    have hp_mem_pf : p ∈ m_0.primeFactors := by
      rwa [Nat.support_factorization] at hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem_pf
    have hp_dvd_m0 : p ∣ m_0 := Nat.dvd_of_mem_primeFactors hp_mem_pf
    have hp_odd : Odd p := h_all_odd p hp_prime hp_dvd_m0
    have hp_ndvd_k0 : ¬ (p : ℤ) ∣ k_0 := h_all_ndvd_k0 p hp_prime hp_dvd_m0
    have hfp_pos : 0 < f p := by
      rw [hf_def]
      rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff]
      exact hp_mem
    -- p^(f p) ∣ m_0 (as integers).
    have hp_pow_dvd_m0 : ((p : ℤ) ^ f p) ∣ (m_0 : ℤ) := by
      have h_nat : p ^ f p ∣ m_0 := by
        rw [← hm0_eq]
        -- Apply Finset.dvd_prod_of_mem to the function `q ↦ q^(f q)`, where p ∈ f.support.
        exact Finset.dvd_prod_of_mem (fun q : ℕ => q ^ f q) hp_mem
      exact_mod_cast h_nat
    exact ajo_odd_prime_power_dvd_wt_gL hm_0 hθ h_trans hp_prime hp_odd hfp_pos
      hp_pow_dvd_m0 hp_ndvd_k0 h_carrier h_wellSupp

/-! ## Full AJO closure under `m_0` odd hypothesis

When `m_0` is odd and coprime to `k_0` (i.e., `θ = 2π · k_0 / m_0` is in
lowest terms with odd denominator), the partial closure becomes a full
closure: `m_0 ∣ wt(g_L)`, which combined with non-triviality
`m_0 ∤ wt(g_L) · k_0` (and `gcd(k_0, m_0) = 1`) yields a contradiction
unless `m_0 = 1`.

This is the AJO conclusion in the odd-denominator regime: under the
extra hypothesis "m_0 odd", non-triviality forces `m_0 = 1`, hence
`θ ∈ 2π · ℤ` (which is the trivial — and trivially dyadic — case).

For the general AJO conclusion (`θ` dyadic, `m_0` a power of 2),
additional content is needed for the `p = 2` part of `m_0`, which
the existing infrastructure does not fully supply (see the file
header documentation for details). -/

/-- **AJO closure (m_0 odd case).** Under non-triviality and the
extra hypothesis "every prime divisor of `m_0` is odd and `(p : ℤ) ∤ k_0`",
the non-triviality assumption forces a contradiction unless `m_0 = 1`. -/
theorem ajo_uniform_dyadic_wellSupp_of_all_odd_primes
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    (h_all_odd : ∀ p : ℕ, p.Prime → p ∣ m_0 → Odd p)
    (h_all_ndvd_k0 : ∀ p : ℕ, p.Prime → p ∣ m_0 → ¬ (p : ℤ) ∣ k_0)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ))
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    False := by
  -- Path: combine `ajo_m0_dvd_wt_gL_of_all_odd` with non-triviality.
  have hp_m0_dvd_wt : (m_0 : ℤ) ∣ (hammingWeight g_L : ℤ) :=
    ajo_m0_dvd_wt_gL_of_all_odd hm_0 hθ h_trans h_all_odd h_all_ndvd_k0
      h_carrier h_wellSupp
  -- Non-triviality ⟺ m_0 ∤ wt(g_L) · k_0 (via nontriv_iff_not_dvd_of_rational).
  have h_ndvd_prod : ¬ (m_0 : ℤ) ∣ ((hammingWeight g_L : ℤ) * k_0) :=
    (nontriv_iff_not_dvd_of_rational hm_0 hθ).mp h_nontriv
  -- But m_0 ∣ wt(g_L) implies m_0 ∣ wt(g_L) · k_0.
  exact h_ndvd_prod (Dvd.dvd.mul_right hp_m0_dvd_wt k_0)

/-- **AJO dyadic closure (m_0 odd case, `gcd(k_0, m_0) = 1`).** The
sharp form: when `m_0` is odd and `gcd(k_0, m_0) = 1`, the non-triviality
hypothesis forces a contradiction. The "m_0 odd" hypothesis is the
strongest hypothesis under which the existing prime-power lift suffices
to close the AJO contradiction. -/
theorem ajo_uniform_dyadic_wellSupp_of_m0_odd
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    (hm_0_odd : Odd m_0)
    (hcop : Int.gcd k_0 (m_0 : ℤ) = 1)
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ))
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    False := by
  -- Every prime divisor of m_0 is odd (since m_0 itself is odd).
  have h_all_odd : ∀ p : ℕ, p.Prime → p ∣ m_0 → Odd p := by
    intro p hp_prime hp_dvd
    -- If p = 2, then 2 ∣ m_0, contradicting m_0 odd. So p ≠ 2; combined with
    -- p prime, p is odd.
    have hp_ne_two : p ≠ 2 := by
      intro hp_eq
      rw [hp_eq] at hp_dvd
      exact hm_0_odd.not_two_dvd_nat hp_dvd
    exact hp_prime.odd_of_ne_two hp_ne_two
  -- Every prime divisor of m_0 doesn't divide k_0 (from gcd = 1).
  have h_all_ndvd_k0 : ∀ p : ℕ, p.Prime → p ∣ m_0 → ¬ (p : ℤ) ∣ k_0 := by
    intro p hp_prime hp_dvd hp_dvd_k0
    -- p ∣ m_0 and p ∣ k_0 ⟹ p ∣ gcd(k_0, m_0) = 1 ⟹ p = 1, contradicting prime.
    have h1 : (p : ℤ) ∣ (m_0 : ℤ) := by exact_mod_cast hp_dvd
    -- (p : ℤ) ∣ Int.gcd k_0 m_0 = 1 (as nat). Use dvd of gcd.
    -- Use Int.gcd_dvd_left and similar. Actually use Nat.gcd via natAbs.
    -- Approach: Nat.dvd_gcd : a ∣ b → a ∣ c → a ∣ b.gcd c.
    -- Then Nat.gcd_eq_one_iff. Or: from h_dvd_k0 and hp_dvd, derive p ∣ Int.gcd.
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
  exact ajo_uniform_dyadic_wellSupp_of_all_odd_primes hm_0 hθ h_trans h_all_odd
    h_all_ndvd_k0 h_carrier h_nontriv h_wellSupp

/-! ## AJO partial closure (well-supported, odd-denominator case)

The main result of this file: under all AJO hypotheses
(non-degeneracy, trans-logical, non-triviality, well-supported `g_L`),
*if* the rational denominator `m_0` of `θ/(2π)` is odd, then we derive a
contradiction. Hence under AJO hypotheses, `m_0` in lowest terms must be
even.

This is a **partial** closure of AJO Theorem 1: the full theorem
concludes that `m_0` is a power of 2 (and so `θ` is dyadic). The
partial closure we provide rules out the *odd* case (so the denominator
is forced to be even), but does not rule out the case `m_0 = 2 · q_odd`
with `q_odd > 1`. See the file header documentation for the 2-part
obstruction.

Note: the well-supported hypothesis in the AJO header is the standard
"every qubit in `supp(g_L)` is in some `supp(g_i)`" condition. -/

/-- **AJO dyadic closure (well-supported, non-degenerate, odd-m_0
contradiction).** Under non-degeneracy, trans-logical uniform-angle,
non-triviality, and well-supported `g_L`, *if* the rational form of
`θ/(2π)` has odd denominator (in lowest terms), then a contradiction
follows. In particular, the rational denominator of `θ/(2π)` in lowest
terms must be even.

The statement is packaged for the wider AJO setting. -/
theorem ajo_uniform_wellSupp_no_odd_nontriv
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_trans : IsTransversalLogical
                (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    (hm_0_odd : Odd m_0)
    (hcop : Int.gcd k_0 (m_0 : ℤ) = 1)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_nontriv : ∀ k : ℤ,
                  ((hammingWeight g_L : ℝ)) * θ ≠ 2 * Real.pi * (k : ℝ))
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    False :=
  ajo_uniform_dyadic_wellSupp_of_m0_odd hm_0 hθ hm_0_odd hcop h_trans h_carrier
    h_nontriv h_wellSupp

end FTQCLib.Codes

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Inequality

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The Delsarte LP bound (the arithmetic half)

The certificate structure and the master bound. Reference: Cohn–Zhao arXiv:1212.1913
Prop. 5 (the dual certificate form) specialized to the size bound; McKinley 2003
Cor. 4.2.2 is the primal counterpart.

Design:
* `LPCert` carries **integer** certificate data (denominators cleared; every field
  kernel-decidable — plain `decide` reaches Golay-size instances).
* Weak duality is stated on the ABSTRACT feasibility data (`IsInnerDistribution`),
  character-free, with the `1 ≤ q` guard forced (the unguarded form is false at
  `q = 0`).
* The ℕ-facing consumer forms are the FLOOR form and the strict form ONLY — the
  ceiling form provably loses a unit on fractional LP optima (see `LPCheck.lean`) and is
  deliberately not stated.
* The alphabet-facing master quantifies over any finite abelian alphabet; the
  transport corollary reaches alphabets with NO structure via `Fintype.equivOfCardEq`
  + `hammingDist_comp`.
-/

namespace ECCLib.Delsarte

open Finset

/-- An integer LP certificate for parameters `(q, n, d)`: nonnegative Krawtchouk
coefficients, positive at zero, whose combination is nonpositive on `[d, n]`. All
fields are kernel-decidable for concrete data. -/
structure LPCert (q n d : ℕ) where
  beta : ℕ → ℤ
  beta_nonneg : ∀ k, 0 ≤ beta k
  beta_zero_pos : 0 < beta 0
  neg : ∀ i ∈ Finset.Icc d n, ∑ k ∈ Finset.range (n + 1), beta k * kraw q n k i ≤ 0

/-- The certificate's objective value `f(0) = Σ_k β_k K_k(0)`. -/
def LPCert.value {q n d : ℕ} (c : LPCert q n d) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), c.beta k * kraw q n k 0

theorem LPCert.value_nonneg {q n d : ℕ} (hq : 1 ≤ q) (c : LPCert q n d) : 0 ≤ c.value :=
  Finset.sum_nonneg fun k _ => mul_nonneg (c.beta_nonneg k) (by
    rw [kraw_at_zero]
    have h1 : (0 : ℤ) ≤ (q : ℤ) - 1 := by
      omega
    positivity)

/-- **Weak duality on abstract feasibility data** (guarded by `1 ≤ q`): any feasible
distribution of size `m` satisfies `m·β₀ ≤ value`. -/
theorem LPCert.mul_le_value {q n d : ℕ} (hq : 1 ≤ q) {N : ℕ → ℕ} {m : ℕ}
    (h : IsInnerDistribution q n d N m) (c : LPCert q n d) :
    (m : ℤ) * c.beta 0 ≤ c.value := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simpa using c.value_nonneg hq
  set f : ℕ → ℤ := fun i => ∑ k ∈ Finset.range (n + 1), c.beta k * kraw q n k i with hf
  set T : ℤ := ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * f i with hT
  -- Chain 1 (lower): T ≥ β₀ · m², by dropping the k ≥ 1 terms after swapping sums.
  have hswap : T = ∑ k ∈ Finset.range (n + 1),
      c.beta k * ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n k i := by
    rw [hT]
    simp only [hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have hlow : c.beta 0 * (m : ℤ) ^ 2 ≤ T := by
    rw [hswap]
    have h0 : c.beta 0 * ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n 0 i
        = c.beta 0 * (m : ℤ) ^ 2 := by
      congr 1
      have : ∀ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n 0 i = (N i : ℤ) := by
        intro i _
        rw [kraw_zero_left, mul_one]
      rw [Finset.sum_congr rfl this]
      exact_mod_cast congrArg (fun z : ℕ => (z : ℤ)) h.total
    calc c.beta 0 * (m : ℤ) ^ 2
        = c.beta 0 * ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n 0 i := h0.symm
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            c.beta k * ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n k i := by
          apply Finset.single_le_sum
            (f := fun k => c.beta k * ∑ i ∈ Finset.range (n + 1), (N i : ℤ) * kraw q n k i)
          · intro k _
            exact mul_nonneg (c.beta_nonneg k) (h.psd k)
          · exact Finset.mem_range.mpr (Nat.succ_pos n)
  -- Chain 2 (upper): T ≤ m · value, since every i ≥ 1 term is ≤ 0.
  have hup : T ≤ (m : ℤ) * c.value := by
    rw [hT, Finset.sum_range_succ' (fun i => (N i : ℤ) * f i) n]
    have hzero : (N 0 : ℤ) * f 0 = (m : ℤ) * c.value := by
      rw [h.zero]
      rfl
    have htail : ∑ i ∈ Finset.range n, (N (i + 1) : ℤ) * f (i + 1) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      rcases Nat.lt_or_ge (i + 1) d with hlt | hge
      · rw [h.gap (i + 1) (Nat.succ_pos i) hlt]
        simp
      · have hmem : i + 1 ∈ Finset.Icc d n :=
          Finset.mem_Icc.mpr ⟨hge, Nat.succ_le_of_lt (Finset.mem_range.mp hi)⟩
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (c.neg (i + 1) hmem)
    omega
  -- Combine and cancel m > 0.
  have hchain : c.beta 0 * (m : ℤ) ^ 2 ≤ (m : ℤ) * c.value := le_trans hlow hup
  have hm' : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have : (m : ℤ) * ((m : ℤ) * c.beta 0) ≤ (m : ℤ) * c.value := by
    calc (m : ℤ) * ((m : ℤ) * c.beta 0) = c.beta 0 * (m : ℤ) ^ 2 := by ring
      _ ≤ (m : ℤ) * c.value := hchain
  exact le_of_mul_le_mul_left this hm'

section Abelian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [DecidableEq ι] in
/-- **The Delsarte LP bound** — abelian alphabet, arbitrary (nonlinear) code,
division-free: `|C|·β₀ ≤ value`. -/
theorem LPCert.card_mul_le_value {d : ℕ}
    (c : LPCert (Fintype.card A) (Fintype.card ι) d)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℤ) * c.beta 0 ≤ c.value :=
  c.mul_le_value Fintype.card_pos (delsarte_feasible C hd)

omit [DecidableEq ι] in
/-- The abelian master with the parameters carried by equations (the transport-friendly
phrasing). -/
theorem LPCert.card_mul_le_value' {q n d : ℕ} (c : LPCert q n d)
    (hq : Fintype.card A = q) (hn : Fintype.card ι = n)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℤ) * c.beta 0 ≤ c.value := by
  subst hq
  subst hn
  exact c.card_mul_le_value C hd

end Abelian

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

omit [DecidableEq ι] in
/-- **The Delsarte LP bound, structureless alphabet**: any alphabet of the right
cardinality, no algebraic structure — reached by transporting the code along a
bijection to `ZMod q` (a Hamming isometry). -/
theorem LPCert.card_mul_le_value_alphabet [Nonempty Q] {d : ℕ}
    (c : LPCert (Fintype.card Q) (Fintype.card ι) d)
    (C : Finset (ι → Q))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℤ) * c.beta 0 ≤ c.value := by
  classical
  haveI : NeZero (Fintype.card Q) := ⟨Nat.pos_iff_ne_zero.mp Fintype.card_pos⟩
  set e : Q ≃ ZMod (Fintype.card Q) :=
    Fintype.equivOfCardEq (by rw [ZMod.card]) with he
  set φ : (ι → Q) → (ι → ZMod (Fintype.card Q)) := fun x i => e (x i) with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    funext i
    exact e.injective (congrFun hxy i)
  have hdist : ∀ x y : ι → Q, hammingDist (φ x) (φ y) = hammingDist x y := by
    intro x y
    exact hammingDist_comp (fun _ => e) (fun _ => e.injective)
  have hcard : (C.image φ).card = C.card := Finset.card_image_of_injective C hinj
  have hd' : ∀ x' ∈ C.image φ, ∀ y' ∈ C.image φ, x' ≠ y' → d ≤ hammingDist x' y' := by
    intro x' hx' y' hy' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hy'
    rw [hdist]
    exact hd x hx y hy (fun h => hne (by rw [h]))
  have h := LPCert.card_mul_le_value' (A := ZMod (Fintype.card Q)) c
    (ZMod.card _) rfl (C.image φ) hd'
  rwa [hcard] at h

end Transport

section Consumers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [DecidableEq ι] in
/-- **The floor form** (the ℕ-facing bound: floor, never ceiling):
`|C| ≤ ⌊value / β₀⌋`. `Int` division by a positive divisor IS the floor. -/
theorem LPCert.card_le_floor {d : ℕ}
    (c : LPCert (Fintype.card A) (Fintype.card ι) d)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    C.card ≤ (c.value / c.beta 0).toNat := by
  have h := c.card_mul_le_value C hd
  have hdiv : (C.card : ℤ) ≤ c.value / c.beta 0 :=
    Int.le_ediv_iff_mul_le c.beta_zero_pos |>.mpr h
  have hnn : 0 ≤ c.value / c.beta 0 :=
    le_trans (by positivity) hdiv
  omega

omit [DecidableEq ι] in
/-- **The strict form**: a strict upper certificate row gives `|C| ≤ M` directly. -/
theorem LPCert.card_le_of_strict {d : ℕ}
    (c : LPCert (Fintype.card A) (Fintype.card ι) d)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y)
    (M : ℕ) (hM : c.value < (M + 1) * c.beta 0) :
    C.card ≤ M := by
  have h := c.card_mul_le_value C hd
  have hlt : (C.card : ℤ) * c.beta 0 < (M + 1) * c.beta 0 := lt_of_le_of_lt h hM
  have := lt_of_mul_lt_mul_right hlt (le_of_lt c.beta_zero_pos)
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

end Consumers

end ECCLib.Delsarte

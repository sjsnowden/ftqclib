/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Corollaries
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The sphere-packing certificate (the ball route)

The Hamming bound as an LP certificate at general `(n, d, q)`. The certificate is `β_k = b̂(k)²`
where `b̂(k) = Σ_{j≤t} K_j(k)` is the ball transform — **index order `K_j(k)`** (the transposed
reading is infeasible). The mechanism made formal:
`Σ_k b̂(k)² K_k(wt v) = qⁿ · #{(z,z') ∈ B_t × B_t : z + z' = −v}` — a COUNT, hence nonnegative, and
empty above weight `2t` by norm subadditivity. At `v = 0` the count is `|B_t|`, so the master bound
cancels to `|C|·|B_t| ≤ qⁿ` — the Hamming bound a second time, now through the LP (McKinley §4.3's
"the LP bound is always at least as strong as the Hamming bound", realized).

Inputs: the primal shell identity `wordShellSum` (word-shell sums of a fixed
character tuple — the mirror of `charShellSum`, located in `Delsarte/Shell.lean` beside
its twin) and full-space
tuple-character orthogonality.
-/

namespace ECCLib.Delsarte

open Polynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Orthogonality at a fixed word: `Σ_χ χ(w) = qⁿ·[w = 0]` (the sum over ALL
character tuples). -/
theorem sum_tupleChar_fixed_word (w : ι → A) :
    ∑ χ : ι → AddChar A ℂ, tupleChar χ w
      = if w = 0 then ((Fintype.card A : ℂ)) ^ Fintype.card ι else 0 := by
  unfold tupleChar
  rw [← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset (AddChar A ℂ))
      (fun (i : ι) (ψ : AddChar A ℂ) => ψ (w i))]
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    have : ∀ i : ι, (∑ ψ : AddChar A ℂ, ψ ((0 : ι → A) i)) = (Fintype.card A : ℂ) := by
      intro i
      rw [show ((0 : ι → A) i) = (0 : A) from rfl, AddChar.sum_apply_eq_ite, if_pos rfl]
    rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hw]
    have : ∃ i, w i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [AddChar.sum_apply_eq_ite, if_neg hi]

/-! ## The ball transform and the counting spectral identity -/

/-- The ball transform `b̂(k) = Σ_{j ≤ t} K_j(k)` — index order pinned (gate A5). -/
def bhat (q n t k : ℕ) : ℤ := ∑ j ∈ Finset.range (t + 1), kraw q n j k

/-- `b̂` at the dual weight is the ball character sum. -/
theorem bhat_eq_ballSum (t : ℕ) (χ : ι → AddChar A ℂ) :
    ((bhat (Fintype.card A) (Fintype.card ι) t (hammingNorm χ) : ℤ) : ℂ)
      = ∑ v ∈ Finset.univ.filter (fun v : ι → A => hammingNorm v ≤ t), tupleChar χ v := by
  unfold bhat
  push_cast
  rw [Finset.sum_congr rfl fun j _ => (wordShellSum j χ).symm]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun v : ι → A => hammingNorm v) (t := Finset.range (t + 1))
    (fun v hv => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.mem_filter.mp hv).2)) (fun v => tupleChar χ v)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hje := Finset.mem_range.mp hj
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact ⟨by omega, h⟩
  · exact fun h => h.2

/-- **The counting spectral identity**: the `b̂²`-certificate's value at weight
`wt v` is `qⁿ` times a ball-pair COUNT. -/
theorem ball_spectral (t : ℕ) (v : ι → A) :
    ((∑ k ∈ Finset.range (Fintype.card ι + 1),
        bhat (Fintype.card A) (Fintype.card ι) t k ^ 2
          * kraw (Fintype.card A) (Fintype.card ι) k (hammingNorm v) : ℤ) : ℂ)
      = ((Fintype.card A : ℂ)) ^ Fintype.card ι
        * (((Finset.univ.filter (fun p : (ι → A) × (ι → A) =>
              hammingNorm p.1 ≤ t ∧ hammingNorm p.2 ≤ t ∧ p.1 + p.2 = -v)).card : ℕ) : ℂ) := by
  classical
  set n := Fintype.card ι
  set q := Fintype.card A
  set B : Finset (ι → A) := Finset.univ.filter (fun z : ι → A => hammingNorm z ≤ t) with hB
  have h1 : ((∑ k ∈ Finset.range (n + 1),
      bhat q n t k ^ 2 * kraw q n k (hammingNorm v) : ℤ) : ℂ)
      = ∑ k ∈ Finset.range (n + 1), ((bhat q n t k : ℤ) : ℂ) ^ 2
          * ((kraw q n k (hammingNorm v) : ℤ) : ℂ) := by
    push_cast
    rfl
  have h2 : ∀ k ∈ Finset.range (n + 1),
      ((bhat q n t k : ℤ) : ℂ) ^ 2 * ((kraw q n k (hammingNorm v) : ℤ) : ℂ)
        = ∑ χ ∈ Finset.univ.filter
            (fun χ : ι → AddChar A ℂ => hammingNorm χ = k),
            ((bhat q n t (hammingNorm χ) : ℤ) : ℂ) ^ 2 * tupleChar χ v := by
    intro k _
    rw [← charShellSum k v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ => by
      rw [(Finset.mem_filter.mp hχ).2]
  have h3 : ∑ k ∈ Finset.range (n + 1),
      (∑ χ ∈ Finset.univ.filter (fun χ : ι → AddChar A ℂ => hammingNorm χ = k),
        ((bhat q n t (hammingNorm χ) : ℤ) : ℂ) ^ 2 * tupleChar χ v)
      = ∑ χ : ι → AddChar A ℂ,
          ((bhat q n t (hammingNorm χ) : ℤ) : ℂ) ^ 2 * tupleChar χ v := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun χ _ => Finset.mem_range.mpr (Nat.lt_succ_of_le hammingNorm_le_card_fintype)) _
  have h4 : ∀ χ : ι → AddChar A ℂ,
      ((bhat q n t (hammingNorm χ) : ℤ) : ℂ) ^ 2 * tupleChar χ v
        = ∑ p ∈ B ×ˢ B, tupleChar χ (p.1 + p.2 + v) := by
    intro χ
    rw [bhat_eq_ballSum, sq, ← hB, Finset.sum_mul_sum,
      ← Finset.sum_product' (s := B) (t := B)
        (f := fun z z' => tupleChar χ z * tupleChar χ z'),
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by
      rw [← tupleChar_add, ← tupleChar_add]
  rw [h1, Finset.sum_congr rfl h2, h3, Finset.sum_congr rfl fun χ _ => h4 χ,
    Finset.sum_comm]
  rw [Finset.sum_congr rfl fun p _ => sum_tupleChar_fixed_word (p.1 + p.2 + v)]
  have hset : ((B ×ˢ B).filter fun p : (ι → A) × (ι → A) => p.1 + p.2 + v = 0)
      = Finset.univ.filter (fun p : (ι → A) × (ι → A) =>
          hammingNorm p.1 ≤ t ∧ hammingNorm p.2 ≤ t ∧ p.1 + p.2 = -v) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, hB]
    constructor
    · rintro ⟨⟨h1', h2'⟩, h3'⟩
      exact ⟨h1', h2', add_eq_zero_iff_eq_neg.mp h3'⟩
    · rintro ⟨h1', h2', h3'⟩
      exact ⟨⟨h1', h2'⟩, by rw [h3', neg_add_cancel]⟩
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    hset, mul_comm]

/-- The spectral identity, descended to ℤ. -/
theorem ball_spectral_int (t : ℕ) (v : ι → A) :
    ∑ k ∈ Finset.range (Fintype.card ι + 1),
        bhat (Fintype.card A) (Fintype.card ι) t k ^ 2
          * kraw (Fintype.card A) (Fintype.card ι) k (hammingNorm v)
      = (Fintype.card A : ℤ) ^ Fintype.card ι
        * ((Finset.univ.filter (fun p : (ι → A) × (ι → A) =>
            hammingNorm p.1 ≤ t ∧ hammingNorm p.2 ≤ t ∧ p.1 + p.2 = -v)).card : ℤ) := by
  exact_mod_cast ball_spectral t v

/-- Above weight `2t` the ball-pair count is empty (norm subadditivity). -/
theorem ball_pair_count_eq_zero {t : ℕ} {v : ι → A} (hv : 2 * t < hammingNorm v) :
    (Finset.univ.filter (fun p : (ι → A) × (ι → A) =>
      hammingNorm p.1 ≤ t ∧ hammingNorm p.2 ≤ t ∧ p.1 + p.2 = -v)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨z, z'⟩ -
  rintro ⟨hz, hz', hsum⟩
  have hz2 : hammingNorm z ≤ t := hz
  have hz2' : hammingNorm z' ≤ t := hz'
  have hsum2 : z + z' = -v := hsum
  have h1 : hammingNorm (z + z') = hammingNorm v := by
    rw [hsum2, hammingNorm_neg]
  have h2 := hammingNorm_add_le z z'
  omega

/-- At `v = 0` the ball-pair count is the ball size. -/
theorem ball_pair_count_zero (t : ℕ) :
    (Finset.univ.filter (fun p : (ι → A) × (ι → A) =>
      hammingNorm p.1 ≤ t ∧ hammingNorm p.2 ≤ t ∧ p.1 + p.2 = -(0 : ι → A))).card
      = (Finset.univ.filter (fun z : ι → A => hammingNorm z ≤ t)).card := by
  rw [eq_comm]
  apply Finset.card_nbij (i := fun z => (z, -z))
  · intro z hz
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨hz, by rwa [hammingNorm_neg], by simp⟩
  · intro z _ z' _ h
    exact congrArg Prod.fst h
  · rintro ⟨z, z'⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hp
    obtain ⟨hz, -, hsum⟩ := hp
    rw [neg_zero] at hsum
    have hz' : z' = -z := (neg_eq_of_add_eq_zero_right hsum).symm
    exact ⟨z, by simpa using hz, by rw [hz']⟩

/-! ## The certificate and the LP-route Hamming bound -/

theorem bhat_zero_pos {q n : ℕ} (hq : 1 ≤ q) (t : ℕ) : 0 < bhat q n t 0 := by
  unfold bhat
  apply Finset.sum_pos'
  · intro j _
    rw [kraw_at_zero]
    have hq' : (0 : ℤ) ≤ (q : ℤ) - 1 := by
      have : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      omega
    exact mul_nonneg (by positivity) (pow_nonneg hq' j)
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos t), by rw [kraw_at_zero]; simp⟩

/-- **The sphere-packing LP certificate** `β_k = b̂(k)²` at general `(q, n, t)`,
feasible for any `d ≥ 2t + 1`. The `neg` field is proved by instantiating the
counting spectral identity over `ZMod q`. -/
def ballCert (q n t d : ℕ) (hq : 2 ≤ q) (htd : 2 * t + 1 ≤ d) : LPCert q n d where
  beta := fun k => bhat q n t k ^ 2
  beta_nonneg := fun _ => sq_nonneg _
  beta_zero_pos := pow_pos (bhat_zero_pos (by omega) t) 2
  neg := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    haveI : NeZero q := ⟨by omega⟩
    have hcard : Fintype.card (ZMod q) = q := ZMod.card q
    have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
    have hA : 1 < Fintype.card (ZMod q) := by rw [hcard]; omega
    obtain ⟨v, hv⟩ := exists_word_of_weight (ι := Fin n) (A := ZMod q) hA (i := i)
      (by rw [hn]; exact hi.2)
    have hspec := ball_spectral_int (ι := Fin n) (A := ZMod q) t v
    rw [hcard, hn, hv] at hspec
    rw [hspec, ball_pair_count_eq_zero (by rw [hv]; omega)]
    simp

/-- The certificate's value: `qⁿ · |B_t|`. -/
theorem ballCert_value {q n t d : ℕ} (hq : 2 ≤ q) (htd : 2 * t + 1 ≤ d) :
    (ballCert q n t d hq htd).value
      = (q : ℤ) ^ n * ∑ j ∈ Finset.range (t + 1), (n.choose j : ℤ) * ((q : ℤ) - 1) ^ j := by
  haveI : NeZero q := ⟨by omega⟩
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hspec := ball_spectral_int (ι := Fin n) (A := ZMod q) t 0
  rw [hcard, hn, show hammingNorm (0 : Fin n → ZMod q) = 0 by simp] at hspec
  change ∑ k ∈ Finset.range (n + 1), bhat q n t k ^ 2 * kraw q n k 0 = _
  rw [hspec, ball_pair_count_zero]
  congr 1
  have hball := card_ball (ι := Fin n) (A := ZMod q) 0 t
  rw [hcard, hn] at hball
  have hfe : (Finset.univ.filter fun z : Fin n → ZMod q => hammingNorm z ≤ t)
      = Finset.univ.filter fun z => hammingDist 0 z ≤ t := by
    congr 1
    ext z
    rw [hammingDist_eq_hammingNorm, neg_zero, zero_add]
  rw [hfe, hball]
  have hq1 : 1 ≤ q := by omega
  push_cast [Nat.cast_sub hq1]
  rfl

omit [DecidableEq ι] in
/-- **The Hamming bound via the LP** (the second route; the direct route is
`hamming_bound_direct`): `|C|·|B_t| ≤ qⁿ`, over any finite abelian alphabet with at
least two letters. -/
theorem hamming_bound_lp {t : ℕ} (hA : 2 ≤ Fintype.card A)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y) :
    (C.card : ℤ) * ∑ j ∈ Finset.range (t + 1),
        ((Fintype.card ι).choose j : ℤ) * ((Fintype.card A : ℤ) - 1) ^ j
      ≤ (Fintype.card A : ℤ) ^ Fintype.card ι := by
  classical
  set q := Fintype.card A with hqdef
  set n := Fintype.card ι with hndef
  set B : ℤ := ∑ j ∈ Finset.range (t + 1), (n.choose j : ℤ) * ((q : ℤ) - 1) ^ j with hBdef
  have hcert := (ballCert q n t (2 * t + 1) hA le_rfl).card_mul_le_value C hd
  have hval := ballCert_value (q := q) (n := n) (t := t) hA le_rfl
  have hbhat : bhat q n t 0 = B := by
    unfold bhat
    rw [hBdef]
    exact Finset.sum_congr rfl fun j _ => kraw_at_zero q n j
  have hBpos : 0 < B := by
    rw [← hbhat]
    exact bhat_zero_pos (by omega) t
  have hβ0 : (ballCert q n t (2 * t + 1) hA le_rfl).beta 0 = B ^ 2 := by
    change bhat q n t 0 ^ 2 = B ^ 2
    rw [hbhat]
  rw [hβ0, hval, ← hBdef] at hcert
  have h' : ((C.card : ℤ) * B) * B ≤ ((q : ℤ) ^ n) * B := by
    calc ((C.card : ℤ) * B) * B = (C.card : ℤ) * B ^ 2 := by ring
      _ ≤ (q : ℤ) ^ n * B := hcert
  exact le_of_mul_le_mul_right h' hBpos

end ECCLib.Delsarte

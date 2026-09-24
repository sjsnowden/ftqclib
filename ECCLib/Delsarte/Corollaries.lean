/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.LP

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The classical bounds as LP certificates

Plotkin and Singleton fall out of the LP master bound as explicit integer certificates,
at general `(n, d, q)`. Sphere-packing/Hamming is proved here by the direct disjoint-ball
argument on `card_ball`; its LP-certificate route lives in `BallCert.lean`.

Reference anchors:
Plotkin = Pellikaan MasterMath Lect. 4.2 slide 25 (this file proves the cleared,
division-free form of that statement, by the LP route rather than the literature's
double-count); Hamming = ibid. slides 13–14, whose proof display IS
`hamming_bound_direct`'s statement; Singleton (arbitrary codes) = Hall Thm 3.1.14 +
p. 38. The Singleton CERTIFICATE identity is proved here from first principles via a
graded homogenization transform (its `if k ≤ m` guard is exactly what coefficient
extraction produces — this resolves the ℕ-truncation trap mathematically).

The Singleton bound is ALSO proved directly (puncturing) — a two-route cross-check:
two independent proofs of the same statement.
-/

namespace ECCLib.Delsarte

open Polynomial Finset

/-! ## The graded homogenization transform `P ↦ Σ_k P_k · X^k (1+X)^{n−k}` -/

/-- `homog n P = Σ_{k ≤ n} P_k · X^k (1+X)^{n−k}`. -/
noncomputable def homog (n : ℕ) (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (P.coeff k) * (Polynomial.X ^ k * (1 + Polynomial.X) ^ (n - k))

theorem homog_zero_poly (n : ℕ) : homog n 0 = 0 := by
  simp [homog]

theorem homog_add (n : ℕ) (P Q : Polynomial ℤ) :
    homog n (P + Q) = homog n P + homog n Q := by
  unfold homog
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_add, map_add, add_mul]

theorem homog_sum (n : ℕ) {σ : Type*} (s : Finset σ) (f : σ → Polynomial ℤ) :
    homog n (∑ l ∈ s, f l) = ∑ l ∈ s, homog n (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homog_zero_poly]
  | insert a s ha ih => rw [Finset.sum_insert ha, homog_add, ih, Finset.sum_insert ha]

/-- Graded multiplicativity against a monomial. -/
theorem homog_monomial_mul {a b : ℕ} {P : Polynomial ℤ} (hP : P.natDegree ≤ a)
    (c : ℤ) {l : ℕ} (hl : l ≤ b) :
    homog (a + b) (P * (Polynomial.C c * Polynomial.X ^ l))
      = homog a P * (Polynomial.C c * (Polynomial.X ^ l * (1 + Polynomial.X) ^ (b - l))) := by
  have hcoeff : ∀ k, (P * (Polynomial.C c * Polynomial.X ^ l)).coeff k
      = if l ≤ k then c * P.coeff (k - l) else 0 := by
    intro k
    rw [show P * (Polynomial.C c * Polynomial.X ^ l)
        = Polynomial.C c * P * Polynomial.X ^ l by ring,
      Polynomial.coeff_mul_X_pow', Polynomial.coeff_C_mul]
  unfold homog
  rw [Finset.sum_mul]
  have hwindow : ∑ k ∈ Finset.range (a + b + 1),
      Polynomial.C ((P * (Polynomial.C c * Polynomial.X ^ l)).coeff k)
        * (Polynomial.X ^ k * (1 + Polynomial.X) ^ (a + b - k))
      = ∑ k ∈ (Finset.range (a + 1)).map ⟨(· + l), fun x y h => Nat.add_right_cancel h⟩,
          Polynomial.C ((P * (Polynomial.C c * Polynomial.X ^ l)).coeff k)
            * (Polynomial.X ^ k * (1 + Polynomial.X) ^ (a + b - k)) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro k hk
      simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.add_le_add (Nat.lt_succ_iff.mp hj) hl))
    · intro k _ hk
      simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hk
      rw [hcoeff k]
      rcases Nat.lt_or_ge k l with hlk | hlk
      · rw [if_neg (by omega)]
        simp
      · have hgt : a < k - l := by
          by_contra hle
          exact hk ⟨k - l, by omega, by omega⟩
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hgt)]
        simp
  rw [hwindow, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [Function.Embedding.coeFn_mk]
  rw [hcoeff (j + l), if_pos (by omega), Nat.add_sub_cancel,
    show a + b - (j + l) = (a - j) + (b - l) from by omega,
    pow_add, pow_add, map_mul]
  ring

/-- Graded multiplicativity: `homog (a+b) (P·Q) = homog a P · homog b Q`. -/
theorem homog_mul {a b : ℕ} {P Q : Polynomial ℤ}
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b) :
    homog (a + b) (P * Q) = homog a P * homog b Q := by
  conv_lhs => rw [Polynomial.as_sum_range' Q (b + 1) (Nat.lt_succ_of_le hQ), Finset.mul_sum]
  rw [homog_sum]
  conv_rhs => rw [show homog b Q
    = ∑ l ∈ Finset.range (b + 1),
        Polynomial.C (Q.coeff l) * (Polynomial.X ^ l * (1 + Polynomial.X) ^ (b - l)) from rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [show ((Polynomial.monomial l) (Q.coeff l) : Polynomial ℤ)
      = Polynomial.C (Q.coeff l) * Polynomial.X ^ l from
    (Polynomial.C_mul_X_pow_eq_monomial).symm]
  exact homog_monomial_mul hP (Q.coeff l) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))

theorem homog_one : homog 0 (1 : Polynomial ℤ) = 1 := by
  simp [homog]

theorem homog_pow {P : Polynomial ℤ} (hP : P.natDegree ≤ 1) (c : ℕ) :
    homog c (P ^ c) = (homog 1 P) ^ c := by
  induction c with
  | zero => simpa using homog_one
  | succ c ih =>
    have hPc : (P ^ c).natDegree ≤ c :=
      le_trans Polynomial.natDegree_pow_le
        (le_trans (Nat.mul_le_mul_left c hP) (by omega))
    rw [pow_succ, homog_mul hPc hP, ih, pow_succ]

theorem homog_one_sub_X : homog 1 (1 - Polynomial.X) = 1 := by
  unfold homog
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

theorem homog_one_add_CX (q : ℕ) :
    homog 1 (1 + Polynomial.C ((q : ℤ) - 1) * Polynomial.X)
      = 1 + Polynomial.C (q : ℤ) * Polynomial.X := by
  unfold homog
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X]
  norm_num [map_sub]
  ring

/-- The homogenization of the Krawtchouk generating polynomial collapses to
`(1 + qX)^{n−i}`. -/
theorem homog_krawPoly (q n i : ℕ) (hi : i ≤ n) :
    homog n (krawPoly q n i) = (1 + Polynomial.C (q : ℤ) * Polynomial.X) ^ (n - i) := by
  have h1 : (1 - Polynomial.X : Polynomial ℤ).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_sub_le _ _) (by simp [Polynomial.natDegree_X])
  have h2 : (1 + Polynomial.C ((q : ℤ) - 1) * Polynomial.X).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_one, Nat.max_le]
    exact ⟨Nat.zero_le 1,
      le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le⟩
  have h1c : ((1 - Polynomial.X : Polynomial ℤ) ^ i).natDegree ≤ i :=
    le_trans Polynomial.natDegree_pow_le
      (le_trans (Nat.mul_le_mul_left i h1) (by omega))
  have h2c : ((1 + Polynomial.C ((q : ℤ) - 1) * Polynomial.X) ^ (n - i)).natDegree ≤ n - i :=
    le_trans Polynomial.natDegree_pow_le
      (le_trans (Nat.mul_le_mul_left (n - i) h2) (by omega))
  unfold krawPoly
  have hm := homog_mul (a := i) (b := n - i) h1c h2c
  rw [show i + (n - i) = n from by omega] at hm
  rw [hm, homog_pow h1 i, homog_pow h2 (n - i), homog_one_sub_X, homog_one_add_CX,
    one_pow, one_mul]

/-- Coefficient extraction — producing exactly the GUARDED Singleton coefficients. -/
theorem homog_coeff (n : ℕ) (P : Polynomial ℤ) (m : ℕ) :
    (homog n P).coeff m
      = ∑ k ∈ Finset.range (n + 1),
          P.coeff k * (if k ≤ m then ((n - k).choose (m - k) : ℤ) else 0) := by
  unfold homog
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_C_mul, mul_comm (Polynomial.X ^ k), Polynomial.coeff_mul_X_pow']
  by_cases hkm : k ≤ m
  · simp [hkm, Polynomial.coeff_one_add_X_pow]
  · simp [hkm]

/-! ## Singleton as an LP certificate -/

/-- **The Singleton transform identity** (found by exact computation, proved here):
`Σ_k β_k K_k(i) = C(n−i, m)·q^m` with the guarded `β_k = [k ≤ m]·C(n−k, m−k)`. -/
theorem singleton_transform (q n : ℕ) {i : ℕ} (hi : i ≤ n) (m : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (if k ≤ m then ((n - k).choose (m - k) : ℤ) else 0) * kraw q n k i
      = ((n - i).choose m : ℤ) * (q : ℤ) ^ m := by
  have h := congrArg (fun p => Polynomial.coeff p m) (homog_krawPoly q n i hi)
  simp only at h
  rw [homog_coeff, coeff_one_add_C_mul_X_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← kraw_eq_coeff]
  ring

/-- The Singleton LP certificate for `1 ≤ d ≤ n`, with `m = n − d + 1`. -/
def singletonCert (q n d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n) : LPCert q n d where
  beta := fun k => if k ≤ n - d + 1 then ((n - k).choose (n - d + 1 - k) : ℤ) else 0
  beta_nonneg := by
    intro k
    split_ifs <;> positivity
  beta_zero_pos := by
    rw [if_pos (Nat.zero_le _), Nat.sub_zero, Nat.sub_zero]
    exact_mod_cast Nat.choose_pos (by omega)
  neg := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [singleton_transform q n hi.2 (n - d + 1),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- **The Singleton bound via the LP** — arbitrary code, arbitrary finite abelian
alphabet: `|C| ≤ q^{n−d+1}`. -/
theorem singleton_bound_lp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {d : ℕ}
    (hd1 : 1 ≤ d) (hdn : d ≤ Fintype.card ι)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    C.card ≤ Fintype.card A ^ (Fintype.card ι - d + 1) := by
  classical
  set q := Fintype.card A with hq
  set n := Fintype.card ι with hn
  set m := n - d + 1 with hm
  have h := (singletonCert q n d hd1 hdn).card_mul_le_value C hd
  have hβ0 : (singletonCert q n d hd1 hdn).beta 0 = (n.choose m : ℤ) := by
    change (if 0 ≤ m then ((n - 0).choose (m - 0) : ℤ) else 0) = (n.choose m : ℤ)
    rw [if_pos (Nat.zero_le _), Nat.sub_zero, Nat.sub_zero]
  have hval : (singletonCert q n d hd1 hdn).value = (n.choose m : ℤ) * (q : ℤ) ^ m := by
    change ∑ k ∈ Finset.range (n + 1),
        (if k ≤ m then ((n - k).choose (m - k) : ℤ) else 0) * kraw q n k 0
      = (n.choose m : ℤ) * (q : ℤ) ^ m
    rw [singleton_transform q n (Nat.zero_le n) m, Nat.sub_zero]
  rw [hβ0, hval] at h
  have hpos : (0 : ℤ) < (n.choose m : ℤ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have h' : (C.card : ℤ) * (n.choose m : ℤ) ≤ (q : ℤ) ^ m * (n.choose m : ℤ) := by
    calc (C.card : ℤ) * (n.choose m : ℤ) ≤ (n.choose m : ℤ) * (q : ℤ) ^ m := h
      _ = (q : ℤ) ^ m * (n.choose m : ℤ) := by ring
  have hle : (C.card : ℤ) ≤ (q : ℤ) ^ m := le_of_mul_le_mul_right h' hpos
  exact_mod_cast hle

/-- **The Singleton bound, direct route** (puncturing — the two-route cross-check):
same statement, independent proof, no LP, no characters, any alphabet. -/
theorem singleton_bound_direct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Type*} [Fintype Q] [DecidableEq Q] {d : ℕ}
    (hd1 : 1 ≤ d) (hdn : d ≤ Fintype.card ι)
    (C : Finset (ι → Q))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    C.card ≤ Fintype.card Q ^ (Fintype.card ι - d + 1) := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := Fintype.card ι - d + 1)
    (by rw [Finset.card_univ]; omega)
  have hdc : ∀ x y : ι → Q,
      hammingDist x y = (Finset.univ.filter fun i => x i ≠ y i).card := fun _ _ => rfl
  have hinj : Set.InjOn (fun x : ι → Q => fun i : S => x i.1) ↑C := by
    intro x hx y hy hxy
    by_contra hne
    have hdist := hd x hx y hy hne
    have hsub : (Finset.univ.filter fun i => x i ≠ y i) ⊆ Finset.univ \ S := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ i, fun hiS => hi.2 (congrFun hxy ⟨i, hiS⟩)⟩
    have hcard : hammingDist x y ≤ (Finset.univ \ S).card := by
      rw [hdc]
      exact Finset.card_le_card hsub
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hS] at hcard
    omega
  calc C.card ≤ (Finset.univ : Finset ({ i // i ∈ S } → Q)).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    _ = Fintype.card Q ^ (Fintype.card ι - d + 1) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, hS]

/-! ## Plotkin as an LP certificate -/

/-- Sums against a support-`{0,1}` coefficient vector collapse to two terms. -/
theorem sum_range_two_support (n : ℕ) (hn : 1 ≤ n) (b0 b1 : ℤ) (g : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 1),
        (if k = 0 then b0 else if k = 1 then b1 else 0) * g k
      = b0 * g 0 + b1 * g 1 := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro k hk
    have : k = 0 ∨ k = 1 := by
      rcases Finset.mem_insert.mp hk with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    rcases this with h | h <;> exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (by
    intro k _ hk
    have h0 : k ≠ 0 := fun h => hk (by simp [h])
    have h1 : k ≠ 1 := fun h => hk (by simp [h])
    simp [h0, h1])]
  rw [show ({0, 1} : Finset ℕ) = insert 0 {1} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton]
  simp

/-- The Plotkin LP certificate: `β = (qd − (q−1)n, 1, 0, …)`. -/
def plotkinCert (q n d : ℕ) (h : ((q : ℤ) - 1) * n < q * d) : LPCert q n d where
  beta := fun k => if k = 0 then (q : ℤ) * d - ((q : ℤ) - 1) * n else if k = 1 then 1 else 0
  beta_nonneg := by
    intro k
    split_ifs <;> omega
  beta_zero_pos := by
    rw [if_pos rfl]
    omega
  neg := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      have hi0 : i = 0 := by omega
      have hd0 : d = 0 := by omega
      subst hn
      subst hd0
      simp at h
    · rw [sum_range_two_support n hn, kraw_zero_left, kraw_one q n i hi.2]
      have hq : (0 : ℤ) ≤ (q : ℤ) := by positivity
      have hdi : (d : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi.1
      nlinarith

/-- **The Plotkin bound via the LP**: `|C|·(qd − (q−1)n) ≤ qd` whenever
`(q−1)n < qd` (the division-free cleared form of Pellikaan Lect. 4.2 slide 25). -/
theorem plotkin_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {d : ℕ}
    (h : ((Fintype.card A : ℤ) - 1) * Fintype.card ι < (Fintype.card A : ℤ) * d)
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y) :
    (C.card : ℤ) * ((Fintype.card A : ℤ) * d - ((Fintype.card A : ℤ) - 1) * Fintype.card ι)
      ≤ (Fintype.card A : ℤ) * d := by
  classical
  set q := Fintype.card A with hq
  set n := Fintype.card ι with hn
  have hle := (plotkinCert q n d h).card_mul_le_value C hd
  have hβ0 : (plotkinCert q n d h).beta 0 = (q : ℤ) * d - ((q : ℤ) - 1) * n := by
    change (if (0 : ℕ) = 0 then (q : ℤ) * d - ((q : ℤ) - 1) * n
      else if (0 : ℕ) = 1 then 1 else 0) = _
    rw [if_pos rfl]
  have hval : (plotkinCert q n d h).value = (q : ℤ) * d := by
    change ∑ k ∈ Finset.range (n + 1),
        (if k = 0 then (q : ℤ) * d - ((q : ℤ) - 1) * n else if k = 1 then 1 else 0)
          * kraw q n k 0
      = (q : ℤ) * d
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rw [hn0, Finset.sum_range_one, if_pos rfl, kraw_zero_left, mul_one]
      push_cast
      ring
    · rw [sum_range_two_support n hn0, kraw_zero_left, kraw_one q n 0 (Nat.zero_le n)]
      push_cast
      ring
  rw [hβ0, hval] at hle
  exact hle

/-! ## The Hamming bound, direct route (the LP-certificate route: `BallCert.lean`) -/

/-- **The sphere-packing/Hamming bound** — the division-free `M·V_q(n,t) ≤ qⁿ`
(verbatim the display in Pellikaan Lect. 4.2 slide 14), via disjoint balls on
`card_ball`. -/
theorem hamming_bound_direct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A] {t : ℕ}
    (C : Finset (ι → A))
    (hd : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y) :
    C.card * (∑ j ∈ Finset.range (t + 1),
        (Fintype.card ι).choose j * (Fintype.card A - 1) ^ j)
      ≤ Fintype.card A ^ Fintype.card ι := by
  classical
  set ball : (ι → A) → Finset (ι → A) :=
    fun x => Finset.univ.filter fun y => hammingDist x y ≤ t with hball
  have hdisj : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (ball x) (ball y) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro z hzx hzy
    rw [hball] at hzx hzy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzx hzy
    have htri : hammingDist x y ≤ hammingDist x z + hammingDist z y :=
      hammingDist_triangle x z y
    have hzy' : hammingDist z y ≤ t := by rwa [hammingDist_comm] at hzy
    have := hd x hx y hy hne
    omega
  calc C.card * (∑ j ∈ Finset.range (t + 1),
        (Fintype.card ι).choose j * (Fintype.card A - 1) ^ j)
      = ∑ x ∈ C, (ball x).card := by
        rw [Finset.sum_congr rfl fun x _ => card_ball x t, Finset.sum_const, smul_eq_mul]
    _ = (C.biUnion ball).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset (ι → A)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card A ^ Fintype.card ι := by rw [Finset.card_univ, Fintype.card_fun]

end ECCLib.Delsarte

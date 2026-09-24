/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.GaussSumSign
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Complex.Basic

set_option linter.style.longLine false

/-!
# The definite quadratic Gauss sign over 𝔽_q — via Davenport–Hasse

The prime-field definite sign is closed (`ECCLib/GaussSumSign.lean`, `quadGaussSum_sign`). This
file builds the 𝔽_q generalization via the **Davenport–Hasse lifting relation**
`gaussSum (χ∘N)(ψ∘Tr) over GF(qⁿ) = (−1)^{n−1}·(gaussSum χ ψ)ⁿ`, proved through the function-field zeta
series `Z(t) = ∑_{f monic} λ(f) t^{deg f} = 1 + G·t` and its logarithmic derivative.

The file opens with the PowerSeries machinery the route rests on (`PowerSeries` has usable
log-derivative support): the **geometric inverse** of `1 + G·X` and the
**log-derivative extraction** `X·Z′·Z⁻¹` of `Z = 1 + G·X`, whose `n`-th coefficient is `(−1)^{n−1}Gⁿ` — the
elementary half of the lifting relation (no `log` needed).
-/

namespace ECCLib.GaussSumFq

open PowerSeries

/-- The geometric inverse identity: `(1 + G·X)·∑ₙ (−G)ⁿ Xⁿ = 1`. -/
theorem one_add_smul_mul_geom (G : ℂ) :
    (1 + C G * X) * mk (fun n => (-G) ^ n) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [add_mul, one_mul, map_add, mul_assoc, coeff_C_mul, coeff_succ_X_mul,
      coeff_one, if_neg (Nat.succ_ne_zero n)]
    simp only [coeff_mk]
    ring

/-- `(1 + G·X)⁻¹ = ∑ₙ (−G)ⁿ Xⁿ`. -/
theorem inv_one_add_smul (G : ℂ) :
    (1 + C G * X) ⁻¹ = mk (fun n => (-G) ^ n) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp), mul_comm]
  exact one_add_smul_mul_geom G

/-- The derivative of `1 + G·X` is the constant `G`. -/
theorem derivative_one_add_smul (G : ℂ) :
    derivative ℂ (1 + C G * X) = C G := by
  rw [map_add, (derivative ℂ).map_one_eq_zero, zero_add, Derivation.leibniz, derivative_X,
    derivative_C, smul_zero, add_zero, smul_eq_mul, mul_one]

/-- **Log-derivative extraction (the elementary half of Davenport–Hasse).** For `Z = 1 + G·X`,
`coeff n (X · Z′ · Z⁻¹) = (−1)^{n−1}·Gⁿ` for `n ≥ 1` (and `0` at `n = 0`). Combined with the Euler-product
side `X·Z′·Z⁻¹ = ∑ Sₙ Xⁿ`, this forces `Sₙ = (−1)^{n−1}Gⁿ`. -/
theorem coeff_logDeriv_one_add (G : ℂ) (n : ℕ) :
    coeff n (X * derivative ℂ (1 + C G * X) * (1 + C G * X) ⁻¹)
      = if n = 0 then 0 else (-1) ^ (n - 1) * G ^ n := by
  rw [derivative_one_add_smul, inv_one_add_smul]
  cases n with
  | zero => simp
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n), mul_comm X (C G), mul_assoc, coeff_C_mul,
      coeff_succ_X_mul, coeff_mk, Nat.succ_sub_one, neg_pow, pow_succ]
    ring

/-! ### The finite Newton frame

The infinite Euler product is unnecessary: the log-derivative identity is, coefficient-wise, the finite
Newton identity `n·Aₙ = ∑_{m=1}^n Sₘ·A_{n−m}` (double counting over unique factorization), and with
`A₀=1, A₁=G, A_{d≥2}=0` it collapses to the recursion solved by `dh_recursion` below. Here: the `Fintype`
frame for monics of fixed degree, the coefficient sums `A`, and the recursion endgame. -/

open Polynomial in
/-- Monic polynomials of degree `n` over a finite ring form a `Fintype`
(via `monicEquivDegreeLT` and `degreeLTEquiv`). -/
noncomputable instance {R : Type*} [CommRing R] [Nontrivial R] [Fintype R] (n : ℕ) :
    Fintype { p : R[X] // p.Monic ∧ p.natDegree = n } :=
  Fintype.ofEquiv (Fin n → R)
    (((monicEquivDegreeLT n).trans (degreeLTEquiv R n).toEquiv).symm)

open Polynomial in
/-- `A Λ n = ∑_{f monic, deg f = n} Λ f` — the degree-`n` coefficient of the zeta series of a
weight `Λ`. -/
noncomputable def monicSum {R : Type*} [CommRing R] [Nontrivial R] [Fintype R]
    (Λ : R[X] → ℂ) (n : ℕ) : ℂ :=
  ∑ f : { p : R[X] // p.Monic ∧ p.natDegree = n }, Λ f

/-- **The recursion endgame of Davenport–Hasse.** If `S 1 = G` and `Sₙ + G·S_{n−1} = 0` for `n ≥ 2`
(the collapse of the Newton identity under `A₀=1, A₁=G, A_{d≥2}=0`), then `Sₙ = (−1)^{n−1}·Gⁿ`. -/
theorem dh_recursion (G : ℂ) (S : ℕ → ℂ) (h1 : S 1 = G)
    (hrec : ∀ n, 2 ≤ n → S n + G * S (n - 1) = 0) :
    ∀ n, 1 ≤ n → S n = (-1) ^ (n - 1) * G ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with hm | hm
    · have hm0 : m = 0 := by omega
      subst hm0
      simpa using h1
    · have h2 : 2 ≤ m + 1 := by omega
      have hstep := hrec (m + 1) h2
      rw [Nat.add_sub_cancel, ih hm] at hstep
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hstep ⊢
      linear_combination hstep

/-! ### Unique factorization, degree-count form

The double-counting side of the Newton identity: a monic `f` over a field *equals* the product of its
normalized factors (both sides monic, associated), and `deg f = ∑_P v_P(f)·deg P`. -/

open Polynomial UniqueFactorizationMonoid in
/-- A monic polynomial over a field is *equal* to the product of its normalized factors. -/
theorem monic_prod_normalizedFactors {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
    (hf : f.Monic) : (normalizedFactors f).prod = f := by
  refine eq_of_monic_of_associated ?_ hf (prod_normalizedFactors hf.ne_zero)
  have h := monic_multiset_prod_of_monic (normalizedFactors f) id fun P hP => by
    obtain ⟨hirr, hnorm, -⟩ := (mem_normalizedFactors_iff' hf.ne_zero).mp hP
    exact (normalize_eq_self_iff_monic hirr.ne_zero).mp hnorm
  simpa using h

open Polynomial UniqueFactorizationMonoid in
/-- **Degree count over the factorization**: for monic `f`,
`deg f = ∑_{P ∈ factors} v_P(f)·deg P`. -/
theorem natDegree_eq_sum_count_mul {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
    (hf : f.Monic) :
    f.natDegree = ∑ P ∈ (normalizedFactors f).toFinset,
      (normalizedFactors f).count P * P.natDegree := by
  conv_lhs => rw [← monic_prod_normalizedFactors hf]
  rw [natDegree_multiset_prod _ (zero_notMem_normalizedFactors f),
    Finset.sum_multiset_map_count]
  simp [smul_eq_mul]

open Polynomial UniqueFactorizationMonoid in
open Classical in
/-- **Power-divisibility count**: for irreducible monic `P` and monic `f`, the number of
`j ∈ [1, N]` with `Pʲ ∣ f` is `v_P(f)` (any bound `N ≥ v_P(f)`). This converts the multiplicity
`v_P(f)` into the pair-count the Newton double-counting needs. -/
theorem card_pow_dvd_eq_count {F : Type*} [Field F] [DecidableEq F] {P f : F[X]}
    (hP : Irreducible P) (hPm : P.Monic) (hf : f.Monic) {N : ℕ}
    (hN : (normalizedFactors f).count P ≤ N) :
    ((Finset.Icc 1 N).filter fun j => P ^ j ∣ f).card = (normalizedFactors f).count P := by
  have hfin : FiniteMultiplicity P f :=
    .of_prime_left ((UniqueFactorizationMonoid.irreducible_iff_prime).mp hP) hf.ne_zero
  have hcount : multiplicity P f = (normalizedFactors f).count P := by
    rw [multiplicity_eq_count_normalizedFactors hP hf.ne_zero, hPm.normalize_eq_self]
  have hdvd : ∀ j : ℕ, P ^ j ∣ f ↔ j ≤ (normalizedFactors f).count P := fun j =>
    ⟨fun h => hcount ▸ hfin.le_multiplicity_of_pow_dvd h,
     fun h => pow_dvd_of_le_multiplicity (le_of_le_of_eq h hcount.symm)⟩
  have hset : (Finset.Icc 1 N).filter (fun j => P ^ j ∣ f)
      = Finset.Icc 1 ((normalizedFactors f).count P) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, hdvd j]
    omega
  rw [hset, Nat.card_Icc]
  omega

open Polynomial in
/-- The monics of degree `n`, as a `Finset F[X]` (the subtype `Fintype`, mapped in). Working at the
`Finset F[X]` level makes reindexing bijections total functions. -/
noncomputable def monicFinset (F : Type*) [Field F] [Fintype F] (n : ℕ) : Finset F[X] :=
  (Finset.univ : Finset { p : F[X] // p.Monic ∧ p.natDegree = n }).map
    ⟨Subtype.val, Subtype.val_injective⟩

open Polynomial in
theorem mem_monicFinset {F : Type*} [Field F] [Fintype F] {n : ℕ} {f : F[X]} :
    f ∈ monicFinset F n ↔ f.Monic ∧ f.natDegree = n := by
  simp [monicFinset]

open Polynomial in
theorem monicSum_eq_sum_monicFinset {F : Type*} [Field F] [Fintype F] (Λ : F[X] → ℂ) (n : ℕ) :
    monicSum Λ n = ∑ f ∈ monicFinset F n, Λ f := by
  rw [monicSum, monicFinset, Finset.sum_map]
  rfl

open Polynomial in
open Classical in
/-- **Divisibility-shift**: for monic `h` of degree `≤ n` and `Λ` multiplicative on monics,
`∑_{f monic deg n, h ∣ f} Λ f = Λ h · A_{n−deg h}` — the `f = h·g` reindex, the engine of the
Newton summation swap. -/
theorem sum_dvd_eq_mul_monicSum {F : Type*} [Field F] [Fintype F] {Λ : F[X] → ℂ}
    (hΛ : ∀ f g : F[X], f.Monic → g.Monic → Λ (f * g) = Λ f * Λ g)
    {h : F[X]} (hh : h.Monic) {n : ℕ} (hkn : h.natDegree ≤ n) :
    ∑ f ∈ (monicFinset F n).filter (h ∣ ·), Λ f = Λ h * monicSum Λ (n - h.natDegree) := by
  rw [monicSum_eq_sum_monicFinset, Finset.mul_sum]
  refine Finset.sum_nbij' (· /ₘ h) (h * ·) ?_ ?_ ?_ ?_ ?_
  · -- forward: quotient lands in monicFinset (n - deg h)
    intro f hf
    obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp hf
    obtain ⟨hfm, hfd⟩ := mem_monicFinset.mp hmem
    have heq : h * (f /ₘ h) = f := by
      conv_rhs => rw [← modByMonic_add_div f h]
      rw [(modByMonic_eq_zero_iff_dvd hh).mpr hdvd, zero_add]
    have hmon : (f /ₘ h).Monic := hh.of_mul_monic_left (heq.symm ▸ hfm)
    exact mem_monicFinset.mpr ⟨hmon, by rw [natDegree_divByMonic f hh, hfd]⟩
  · -- backward: h·g lands in the filter
    intro g hg
    obtain ⟨hgm, hgd⟩ := mem_monicFinset.mp hg
    refine Finset.mem_filter.mpr ⟨mem_monicFinset.mpr ⟨hh.mul hgm, ?_⟩, Dvd.intro _ rfl⟩
    rw [hh.natDegree_mul hgm, hgd]
    omega
  · -- left inverse: h·(f /ₘ h) = f
    intro f hf
    obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hf
    conv_rhs => rw [← modByMonic_add_div f h]
    rw [(modByMonic_eq_zero_iff_dvd hh).mpr hdvd, zero_add]
  · -- right inverse: (h·g) /ₘ h = g
    intro g _
    change (h * g) /ₘ h = g
    exact mul_divByMonic_cancel_left g hh
  · -- summands match: Λ f = Λ h · Λ (f /ₘ h)
    intro f hf
    obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp hf
    obtain ⟨hfm, -⟩ := mem_monicFinset.mp hmem
    have heq : h * (f /ₘ h) = f := by
      conv_rhs => rw [← modByMonic_add_div f h]
      rw [(modByMonic_eq_zero_iff_dvd hh).mpr hdvd, zero_add]
    have hmon : (f /ₘ h).Monic := hh.of_mul_monic_left (heq.symm ▸ hfm)
    change Λ f = Λ h * Λ (f /ₘ h)
    conv_lhs => rw [← heq]
    exact hΛ h _ hh hmon

/-- **Divisor-pair reindex**: summing over `m ∈ [1,n]` and divisors `d ∣ m` equals summing over
pairs `(d, j)` with `d·j ≤ n` — the `m = d·j` regrouping of the Newton identity. -/
theorem sum_divisors_reindex (n : ℕ) (w : ℕ → ℕ → ℂ) :
    ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors, w d (m / d)
      = ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d), w d j := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 / p.2⟩) (fun p => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    rintro ⟨m, d⟩ hp
    obtain ⟨hm, hd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hdvd, hm0⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd0, (Nat.le_of_dvd (by omega) hdvd).trans hmn⟩,
      Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hmn⟩⟩
    exact (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdvd)
  · -- backward membership
    rintro ⟨d, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hd1, hdn⟩, hj1, hjn⟩ := hp
    have hdj : d * j ≤ n := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hjn
    exact ⟨⟨Nat.mul_pos hd1 hj1, hdj⟩, Dvd.intro j rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
  · -- left inverse
    rintro ⟨m, d⟩ hp
    obtain ⟨-, hd⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    simp [Nat.mul_div_cancel' hdvd]
  · -- right inverse
    rintro ⟨d, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    simp [Nat.mul_div_cancel_left j (by omega : 0 < d)]
  · -- summand match
    rintro ⟨m, d⟩ _
    rfl

/-! ### The power-sum side: monic irreducibles, `S`, and helpers -/

open Polynomial in
open Classical in
/-- The monic irreducibles of degree `d`, as a `Finset F[X]`. -/
noncomputable def irredFinset (F : Type*) [Field F] [Fintype F] (d : ℕ) : Finset F[X] :=
  (monicFinset F d).filter (fun P => Irreducible P)

open Polynomial in
open Classical in
theorem mem_irredFinset {F : Type*} [Field F] [Fintype F] {d : ℕ} {P : F[X]} :
    P ∈ irredFinset F d ↔ P.Monic ∧ P.natDegree = d ∧ Irreducible P := by
  simp only [irredFinset, Finset.mem_filter, mem_monicFinset]
  tauto

open Polynomial in
open Classical in
/-- `S Λ m = ∑_{d ∣ m} ∑_{P irred monic, deg d} d·Λ(P)^{m/d}` — the degree-`m` **power sum** of the
weight `Λ`: the coefficient sum the Newton identity pairs with `A_{n−m}`, and (by
`powerSum_dhWeight_eq_sum`) the extension Gauss sum over `GF(q^m)`. -/
noncomputable def powerSum {F : Type*} [Field F] [Fintype F] (Λ : F[X] → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ m.divisors, ∑ P ∈ irredFinset F d, (d : ℂ) * Λ P ^ (m / d)

/-- `Λ(Pʲ) = Λ(P)ʲ` for `j ≥ 1`, from multiplicativity on monics (no `Λ 1 = 1` needed). -/
theorem lambda_pow {F : Type*} [Field F] {Λ : Polynomial F → ℂ}
    (hΛ : ∀ f g : Polynomial F, f.Monic → g.Monic → Λ (f * g) = Λ f * Λ g)
    {P : Polynomial F} (hP : P.Monic) : ∀ j, 1 ≤ j → Λ (P ^ j) = Λ P ^ j := by
  intro j hj
  induction j with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 1 with hk | hk
    · have hk0 : k = 0 := by omega
      subst hk0
      simp
    · rw [pow_succ, hΛ _ _ (hP.pow k) hP, ih hk, pow_succ]

open Polynomial in
open Classical in
/-- Degree kills divisibility: if `deg h > n`, no monic of degree `n` is divisible by `h`. -/
theorem filter_dvd_empty_of_degree_gt {F : Type*} [Field F] [Fintype F] {h : F[X]}
    {n : ℕ} (hd : n < h.natDegree) :
    (monicFinset F n).filter (h ∣ ·) = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun f hf hdvd => ?_
  obtain ⟨hfm, hfd⟩ := mem_monicFinset.mp hf
  have hle := Polynomial.natDegree_le_of_dvd hdvd hfm.ne_zero
  omega

open Polynomial UniqueFactorizationMonoid in
open Classical in
/-- **Per-`f` count, organized by degree (ℕ)**: for monic `f` of degree `n ≥ 1`,
`∑_{d ∈ [1,n]} ∑_{P irred monic deg d} v_P(f)·d = n` — the degree count extended over ALL monic
irreducibles (the off-factor terms vanish), the extension that makes the Newton swap's index
`f`-independent. -/
theorem sum_irred_count_mul_eq {F : Type*} [Field F] [Fintype F] {f : F[X]} {n : ℕ}
    (hf : f.Monic) (hfd : f.natDegree = n) :
    ∑ d ∈ Finset.Icc 1 n, ∑ P ∈ irredFinset F d, (normalizedFactors f).count P * d = n := by
  -- replace `d` by `deg P` on each `irredFinset d`
  have hstep : ∀ d ∈ Finset.Icc 1 n, ∑ P ∈ irredFinset F d, (normalizedFactors f).count P * d
      = ∑ P ∈ irredFinset F d, (normalizedFactors f).count P * P.natDegree := by
    intro d _
    exact Finset.sum_congr rfl fun P hP => by rw [(mem_irredFinset.mp hP).2.1]
  rw [Finset.sum_congr rfl hstep]
  -- fuse the double sum into a sum over the disjoint union
  have hdisj : (↑(Finset.Icc 1 n) : Set ℕ).PairwiseDisjoint (irredFinset F) := by
    intro d₁ _ d₂ _ hne
    refine Finset.disjoint_left.mpr fun P hP1 hP2 => ?_
    exact hne ((mem_irredFinset.mp hP1).2.1 ▸ (mem_irredFinset.mp hP2).2.1)
  rw [← Finset.sum_biUnion hdisj]
  -- restrict to the factor support and finish with the degree count
  have hsub : (normalizedFactors f).toFinset ⊆ (Finset.Icc 1 n).biUnion (irredFinset F) := by
    intro P hP
    obtain ⟨hirr, hnorm, hdvd⟩ :=
      (mem_normalizedFactors_iff' hf.ne_zero).mp (Multiset.mem_toFinset.mp hP)
    have hPm : P.Monic := (normalize_eq_self_iff_monic hirr.ne_zero).mp hnorm
    have hle : P.natDegree ≤ n := hfd ▸ Polynomial.natDegree_le_of_dvd hdvd hf.ne_zero
    exact Finset.mem_biUnion.mpr ⟨P.natDegree,
      Finset.mem_Icc.mpr ⟨hirr.natDegree_pos, hle⟩, mem_irredFinset.mpr ⟨hPm, rfl, hirr⟩⟩
  rw [← Finset.sum_subset hsub fun P _ hP =>
    by rw [Multiset.count_eq_zero.mpr (fun hm => hP (Multiset.mem_toFinset.mpr hm)), zero_mul]]
  rw [← natDegree_eq_sum_count_mul hf, hfd]

open Polynomial UniqueFactorizationMonoid in
open Classical in
/-- **Per-`f` expansion over `(d, j, P)` (ℂ)**: for monic `f` of degree `n ≥ 1`,
`(n:ℂ) = ∑_{d}∑_{j≤n/d}∑_{P irred deg d} [Pʲ∣f]·d`. -/
theorem complex_count_expansion {F : Type*} [Field F] [Fintype F] {f : F[X]} {n : ℕ}
    (hf : f.Monic) (hfd : f.natDegree = n) (_hn : 1 ≤ n) :
    (n : ℂ) = ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d), ∑ P ∈ irredFinset F d,
      (if P ^ j ∣ f then (d : ℂ) else 0) := by
  have hswap : ∀ d ∈ Finset.Icc 1 n,
      ∑ j ∈ Finset.Icc 1 (n / d), ∑ P ∈ irredFinset F d, (if P ^ j ∣ f then (d : ℂ) else 0)
        = ∑ P ∈ irredFinset F d, (((normalizedFactors f).count P * d : ℕ) : ℂ) := by
    intro d hd
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨hPm, hPd, hirr⟩ := mem_irredFinset.mp hP
    -- count bound: v_P(f) ≤ n/d
    have hbound : (normalizedFactors f).count P ≤ n / d := by
      rcases Nat.eq_zero_or_pos ((normalizedFactors f).count P) with hc | hc
      · exact hc ▸ Nat.zero_le _
      · have hmem : P ∈ (normalizedFactors f).toFinset :=
          Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hc)
        have hle : (normalizedFactors f).count P * P.natDegree ≤ n := by
          rw [← hfd, natDegree_eq_sum_count_mul hf]
          exact Finset.single_le_sum
            (f := fun Q => (normalizedFactors f).count Q * Q.natDegree)
            (fun Q _ => Nat.zero_le _) hmem
        rw [hPd] at hle
        have hd0 : 0 < d := by
          have := Finset.mem_Icc.mp hd; omega
        exact (Nat.le_div_iff_mul_le hd0).mpr hle
    rw [← Finset.sum_filter, Finset.sum_const,
      card_pow_dvd_eq_count hirr hPm hf hbound]
    push_cast
    ring
  rw [Finset.sum_congr rfl hswap]
  have := sum_irred_count_mul_eq hf hfd
  calc (n : ℂ) = ((∑ d ∈ Finset.Icc 1 n, ∑ P ∈ irredFinset F d,
      (normalizedFactors f).count P * d : ℕ) : ℂ) := by rw [this]
    _ = _ := by push_cast; rfl

open Polynomial in
open Classical in
/-- **The finite Newton identity** `n·Aₙ = ∑_{m=1}^{n} Sₘ·A_{n−m}` — the coefficient-level form of
the zeta log-derivative, by double counting over unique factorization. The master swap: expand `n`
per-`f` over `(d, j, P)` (`complex_count_expansion`), pull `f` inside (three `sum_comm`s), collapse
each inner sum by the `f = Pʲ·g` bijection (`sum_dvd_eq_mul_monicSum`), and regroup by `m = d·j`
(`sum_divisors_reindex`). -/
theorem newton_identity {F : Type*} [Field F] [Fintype F] {Λ : F[X] → ℂ}
    (hΛ : ∀ f g : F[X], f.Monic → g.Monic → Λ (f * g) = Λ f * Λ g)
    {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) * monicSum Λ n = ∑ m ∈ Finset.Icc 1 n, powerSum Λ m * monicSum Λ (n - m) := by
  have hRHS : ∑ m ∈ Finset.Icc 1 n, powerSum Λ m * monicSum Λ (n - m)
      = ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d),
          ∑ P ∈ irredFinset F d, (d : ℂ) * Λ P ^ j * monicSum Λ (n - d * j) := by
    have h1 : ∀ m ∈ Finset.Icc 1 n, powerSum Λ m * monicSum Λ (n - m)
        = ∑ d ∈ m.divisors, ∑ P ∈ irredFinset F d,
            (d : ℂ) * Λ P ^ (m / d) * monicSum Λ (n - d * (m / d)) := by
      intro m _
      rw [powerSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    rw [Finset.sum_congr rfl h1]
    exact sum_divisors_reindex n
      (fun d j => ∑ P ∈ irredFinset F d, (d : ℂ) * Λ P ^ j * monicSum Λ (n - d * j))
  have hLHS : (n : ℂ) * monicSum Λ n
      = ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d),
          ∑ P ∈ irredFinset F d, (d : ℂ) * Λ P ^ j * monicSum Λ (n - d * j) := by
    rw [monicSum_eq_sum_monicFinset, Finset.mul_sum]
    have h2 : ∀ f ∈ monicFinset F n, (n : ℂ) * Λ f
        = ∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d), ∑ P ∈ irredFinset F d,
            (if P ^ j ∣ f then (d : ℂ) * Λ f else 0) := by
      intro f hf
      obtain ⟨hfm, hfd⟩ := mem_monicFinset.mp hf
      calc (n : ℂ) * Λ f
          = (∑ d ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (n / d), ∑ P ∈ irredFinset F d,
              (if P ^ j ∣ f then (d : ℂ) else 0)) * Λ f := by
            rw [← complex_count_expansion hfm hfd hn]
        _ = _ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun P _ => ?_
            rw [ite_mul, zero_mul]
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P hP => ?_
    obtain ⟨hPm, hPd, hirr⟩ := mem_irredFinset.mp hP
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hd0 : 0 < d := by have := Finset.mem_Icc.mp hd; omega
    have hdeg : (P ^ j).natDegree = d * j := by
      rw [hPm.natDegree_pow, hPd, Nat.mul_comm]
    have hkn : (P ^ j).natDegree ≤ n := by
      rw [hdeg, Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hd0).mp (Finset.mem_Icc.mp hj).2
    rw [← Finset.sum_filter, ← Finset.mul_sum,
      sum_dvd_eq_mul_monicSum hΛ (hPm.pow j) hkn, hdeg,
      lambda_pow hΛ hPm j hj1]
    ring
  rw [hLHS]
  exact hRHS.symm

/-! ### The Davenport–Hasse character weight

For monic `f` with roots `αᵢ` (in a splitting field), `∏αᵢ = (−1)^{deg f}·f(0)` and
`∑αᵢ = −nextCoeff f`; so `dhWeight χ ψ f = χ(∏roots)·ψ(∑roots)` — the weight whose power sums
`powerSum_dhWeight_eq_sum` identifies with the extension Gauss sums `gaussSum (χ∘N) (ψ∘Tr)`. -/

open Polynomial in
/-- The Davenport–Hasse weight `λ(f) = χ((−1)^{deg f}·f(0))·ψ(−nextCoeff f)`. -/
noncomputable def dhWeight {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (f : F[X]) : ℂ :=
  χ ((-1) ^ f.natDegree * f.coeff 0) * ψ (-f.nextCoeff)

open Polynomial in
/-- **The weight is multiplicative on monics** — root-products multiply, root-sums add. -/
theorem dhWeight_mul {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) {f g : F[X]} (hf : f.Monic) (hg : g.Monic) :
    dhWeight χ ψ (f * g) = dhWeight χ ψ f * dhWeight χ ψ g := by
  unfold dhWeight
  have h1 : ((-1 : F)) ^ ((f * g).natDegree) * (f * g).coeff 0
      = ((-1) ^ f.natDegree * f.coeff 0) * ((-1) ^ g.natDegree * g.coeff 0) := by
    rw [hf.natDegree_mul hg, Polynomial.mul_coeff_zero, pow_add]
    ring
  rw [h1, map_mul, hf.nextCoeff_mul hg, neg_add, AddChar.map_add_eq_mul]
  ring

open Polynomial in
/-- **Coefficient `d = 0`**: `A₀ = 1` — the unique monic of degree `0` is `1`, with weight `1`. -/
theorem monicSum_dhWeight_zero {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    monicSum (dhWeight χ ψ) 0 = 1 := by
  rw [monicSum_eq_sum_monicFinset]
  have h : monicFinset F 0 = {1} := by
    ext f
    rw [mem_monicFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hd⟩
      exact hm.natDegree_eq_zero.mp hd
    · rintro rfl
      exact ⟨monic_one, natDegree_one⟩
  rw [h, Finset.sum_singleton]
  unfold dhWeight
  simp [Polynomial.nextCoeff]

open Polynomial in
/-- **Coefficient `d = 1`**: `A₁ = gaussSum χ ψ` — monics of degree one are `X + C a`, with weight
`χ(−a)·ψ(−a)`; reindexing `a ↦ −a` gives the Gauss sum. -/
theorem monicSum_dhWeight_one {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    monicSum (dhWeight χ ψ) 1 = gaussSum χ ψ := by
  rw [monicSum_eq_sum_monicFinset, gaussSum]
  refine Finset.sum_nbij' (fun f => -f.coeff 0)
    (fun a => Polynomial.X + Polynomial.C (-a)) ?_ ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro a _
    exact mem_monicFinset.mpr ⟨monic_X_add_C _, natDegree_X_add_C _⟩
  · -- left inverse: X + C (−(−coeff 0 f)) = f
    intro f hf
    obtain ⟨hfm, hfd⟩ := mem_monicFinset.mp hf
    have h1 : f.coeff 1 = 1 := by
      have := hfm.leadingCoeff
      rwa [Polynomial.leadingCoeff, hfd] at this
    have h2 := eq_X_add_C_of_natDegree_le_one (le_of_eq hfd)
    rw [h1, map_one, one_mul] at h2
    change Polynomial.X + Polynomial.C (-(-f.coeff 0)) = f
    rw [neg_neg]
    exact h2.symm
  · -- right inverse: −coeff 0 (X + C (−a)) = a
    intro a _
    simp
  · -- summand: dhWeight (f) = χ(−f₀)·ψ(−f₀)
    intro f hf
    obtain ⟨hfm, hfd⟩ := mem_monicFinset.mp hf
    change dhWeight χ ψ f = χ (-f.coeff 0) * ψ (-f.coeff 0)
    unfold dhWeight
    rw [hfd]
    simp [Polynomial.nextCoeff, hfd]

open Polynomial in
open Classical in
/-- **Coefficients `d ≥ 2`**: `A_d = 0` — the subleading coefficient is a free coordinate distinct
from the constant one, and summing `ψ` over it kills the whole sum (character orthogonality). Via
the subleading-shift bijection `(t, f₀) ↦ f₀ + t·X^{d−1}` on monics with vanishing subleading term.
-/
theorem monicSum_dhWeight_eq_zero {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {d : ℕ} (hd : 2 ≤ d) :
    monicSum (dhWeight χ ψ) d = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  rw [monicSum_eq_sum_monicFinset]
  -- adding a `C c·X^{k+1}` term preserves monic-of-degree-(k+2)
  have haux : ∀ (g : F[X]) (c : F), g.Monic → g.natDegree = k + 2 →
      (g + Polynomial.C c * Polynomial.X ^ (k + 1)).Monic ∧
      (g + Polynomial.C c * Polynomial.X ^ (k + 1)).natDegree = k + 2 := by
    intro g c hg hgd
    have hdeg : (Polynomial.C c * Polynomial.X ^ (k + 1)).degree < g.degree := by
      refine lt_of_le_of_lt (degree_C_mul_X_pow_le (k + 1) c) ?_
      rw [degree_eq_natDegree hg.ne_zero, hgd]
      exact_mod_cast (by omega : k + 1 < k + 2)
    exact ⟨hg.add_of_left hdeg, by rw [natDegree_add_eq_left_of_degree_lt hdeg, hgd]⟩
  -- coefficients of the shifted polynomial
  have hcoeff0 : ∀ (g : F[X]) (c : F),
      (g + Polynomial.C c * Polynomial.X ^ (k + 1)).coeff 0 = g.coeff 0 := by
    intro g c
    simp [Polynomial.coeff_X_pow]
  have hcoeffk : ∀ (g : F[X]) (c : F),
      (g + Polynomial.C c * Polynomial.X ^ (k + 1)).coeff (k + 1) = g.coeff (k + 1) + c := by
    intro g c
    simp [Polynomial.coeff_X_pow]
  -- the shift bijection
  have key : ∑ f ∈ monicFinset F (k + 2), dhWeight χ ψ f
      = ∑ p ∈ (Finset.univ ×ˢ ((monicFinset F (k + 2)).filter
          (fun f => f.coeff (k + 1) = 0)) : Finset (F × F[X])),
          χ ((-1) ^ (k + 2) * p.2.coeff 0) * ψ (-p.1) := by
    refine (Finset.sum_nbij'
      (fun p => p.2 + Polynomial.C p.1 * Polynomial.X ^ (k + 1))
      (fun f => (f.coeff (k + 1), f - Polynomial.C (f.coeff (k + 1)) * Polynomial.X ^ (k + 1)))
      ?_ ?_ ?_ ?_ ?_).symm
    · -- forward: the shift is a monic of degree k+2
      rintro ⟨t, f₀⟩ hp
      obtain ⟨-, hf₀⟩ := Finset.mem_product.mp hp
      obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hf₀
      obtain ⟨hm, hdeg⟩ := mem_monicFinset.mp hmem
      exact mem_monicFinset.mpr ((haux f₀ t hm hdeg).imp id id)
    · -- backward: subtracting the subleading term lands in the filter
      intro f hf
      obtain ⟨hm, hdeg⟩ := mem_monicFinset.mp hf
      have hsub : f - Polynomial.C (f.coeff (k + 1)) * Polynomial.X ^ (k + 1)
          = f + Polynomial.C (-(f.coeff (k + 1))) * Polynomial.X ^ (k + 1) := by
        rw [map_neg, neg_mul, sub_eq_add_neg]
      dsimp only
      refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨mem_monicFinset.mpr ?_, ?_⟩⟩
      · rw [hsub]
        exact (haux f _ hm hdeg).imp id id
      · rw [hsub, hcoeffk]
        ring
    · -- left inverse
      rintro ⟨t, f₀⟩ hp
      obtain ⟨-, hf₀⟩ := Finset.mem_product.mp hp
      obtain ⟨-, hc0⟩ := Finset.mem_filter.mp hf₀
      change (_, _) = (t, f₀)
      have h1 : (f₀ + Polynomial.C t * Polynomial.X ^ (k + 1)).coeff (k + 1) = t := by
        rw [hcoeffk, hc0, zero_add]
      rw [Prod.mk.injEq]
      constructor
      · exact h1
      · rw [h1, add_sub_cancel_right]
    · -- right inverse
      intro f _
      change f - _ + _ = f
      rw [sub_add_cancel]
    · -- summand
      rintro ⟨t, f₀⟩ hp
      obtain ⟨-, hf₀⟩ := Finset.mem_product.mp hp
      obtain ⟨hmem, hc0⟩ := Finset.mem_filter.mp hf₀
      obtain ⟨hm, hdeg⟩ := mem_monicFinset.mp hmem
      obtain ⟨hm', hdeg'⟩ := haux f₀ t hm hdeg
      dsimp only
      symm
      unfold dhWeight
      rw [hcoeff0, hdeg', Polynomial.nextCoeff, hdeg']
      simp only [Nat.succ_ne_zero, if_false]
      rw [show k + 2 - 1 = k + 1 from rfl, hcoeffk, hc0, zero_add]
  rw [key, Finset.sum_product]
  -- factor and kill with orthogonality
  have hfac : ∀ t : F, ∑ f₀ ∈ (monicFinset F (k + 2)).filter (fun f => f.coeff (k + 1) = 0),
      χ ((-1) ^ (k + 2) * f₀.coeff 0) * ψ (-t)
        = (∑ f₀ ∈ (monicFinset F (k + 2)).filter (fun f => f.coeff (k + 1) = 0),
            χ ((-1) ^ (k + 2) * f₀.coeff 0)) * ψ (-t) := by
    intro t
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl fun t _ => hfac t, ← Finset.mul_sum]
  have hneg : ∑ t : F, ψ (-t) = ∑ t : F, ψ t :=
    Fintype.sum_equiv (Equiv.neg F) _ _ fun t => rfl
  rw [hneg, AddChar.sum_eq_zero_of_ne_one hψ, mul_zero]

open Polynomial in
/-- **Abstract Davenport–Hasse (power-sum form).** For `ψ ≠ 1`, the power sums of the DH weight are
`Sₙ = (−1)^{n−1}·Gⁿ` with `G = gaussSum χ ψ`: the Newton identity collapses under
`A₀ = 1, A₁ = G, A_{d≥2} = 0` to the two-term recursion, which `dh_recursion` solves. Once
`powerSum_dhWeight_eq_sum` identifies `Sₙ` with the Gauss sum over `GF(qⁿ)`, this IS the lifting
relation. -/
theorem powerSum_dhWeight {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∀ n, 1 ≤ n → powerSum (dhWeight χ ψ) n = (-1) ^ (n - 1) * (gaussSum χ ψ) ^ n := by
  have hΛ : ∀ f g : F[X], f.Monic → g.Monic →
      dhWeight χ ψ (f * g) = dhWeight χ ψ f * dhWeight χ ψ g :=
    fun f g hf hg => dhWeight_mul χ ψ hf hg
  refine dh_recursion (gaussSum χ ψ) _ ?_ ?_
  · -- S 1 = G
    have h := newton_identity hΛ (le_refl 1)
    rw [monicSum_dhWeight_one, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
      monicSum_dhWeight_zero, mul_one, Nat.cast_one, one_mul] at h
    exact h.symm
  · -- Sₙ + G·S₍ₙ₋₁₎ = 0 for n ≥ 2
    intro n hn
    have h := newton_identity hΛ (by omega : 1 ≤ n)
    rw [monicSum_dhWeight_eq_zero χ hψ hn, mul_zero] at h
    have hsub : ({n - 1, n} : Finset ℕ) ⊆ Finset.Icc 1 n := by
      intro m hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · rw [Finset.mem_singleton] at hm
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hzero : ∀ m ∈ Finset.Icc 1 n, m ∉ ({n - 1, n} : Finset ℕ) →
        powerSum (dhWeight χ ψ) m * monicSum (dhWeight χ ψ) (n - m) = 0 := by
      intro m hm hnot
      obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hm
      have hne1 : m ≠ n - 1 := fun hc => hnot (by simp [hc])
      have hne2 : m ≠ n := fun hc => hnot (by simp [hc])
      rw [monicSum_dhWeight_eq_zero χ hψ (by omega), mul_zero]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : n - 1 ≠ n),
      show n - (n - 1) = 1 from by omega, Nat.sub_self, monicSum_dhWeight_one,
      monicSum_dhWeight_zero, mul_one] at h
    linear_combination -h

/-! ### The power sums are the extension Gauss sums

For a finite extension `E/F` of degree `m`, partition `E` by minimal polynomial: each `x` has a
monic irreducible minpoly `P` of degree `d ∣ m`, its norm/trace are read off `P`'s coefficients
through `F⟮x⟯`, and each `P` has exactly `d` roots. Summing: `Sₘ = ∑_x χ(N x)·ψ(Tr x)`. -/

open Polynomial IntermediateField in
/-- **Per-element weight**: `χ(N x)·ψ(Tr x) = dhWeight(minpoly x)^{[E:F]/deg}` — norm and
trace factor through `F⟮x⟯`, where the minimal polynomial's constant and subleading coefficients
read them off. -/
theorem char_norm_trace_eq_dhWeight_pow {F E : Type*} [Field F] [Fintype F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (x : E) :
    χ (Algebra.norm F x) * ψ (Algebra.trace F E x)
      = dhWeight χ ψ (minpoly F x) ^ (Module.finrank F E / (minpoly F x).natDegree) := by
  have hx : IsIntegral F x := .of_finite F x
  have hd0 : 0 < (minpoly F x).natDegree := minpoly.natDegree_pos hx
  have htower : (minpoly F x).natDegree * Module.finrank (↥F⟮x⟯) E = Module.finrank F E := by
    rw [← adjoin.finrank hx]
    exact Module.finrank_mul_finrank F (↥F⟮x⟯) E
  have hediv : Module.finrank F E / (minpoly F x).natDegree = Module.finrank (↥F⟮x⟯) E := by
    rw [← htower, Nat.mul_div_cancel_left _ hd0]
  have hnorm : Algebra.norm F x
      = ((-1) ^ (minpoly F x).natDegree * (minpoly F x).coeff 0) ^ Module.finrank (↥F⟮x⟯) E := by
    rw [Algebra.norm_eq_norm_adjoin F x]
    congr 1
    have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hx)
    rw [show (adjoin.powerBasis hx).gen = AdjoinSimple.gen F x from rfl,
      show (adjoin.powerBasis hx).dim = (minpoly F x).natDegree from rfl, minpoly_gen] at h1
    exact h1
  have htrace : Algebra.trace F E x
      = Module.finrank (↥F⟮x⟯) E • (-(minpoly F x).nextCoeff) := by
    rw [trace_eq_trace_adjoin F x, trace_adjoinSimpleGen hx]
  rw [hnorm, htrace, map_pow, AddChar.map_nsmul_eq_pow, hediv]
  unfold dhWeight
  rw [mul_pow]

open Polynomial in
open Classical in
set_option linter.unusedFintypeInType false in
/-- **Fiber cardinality**: a monic irreducible `P` with `deg P ∣ [E:F]` has exactly `deg P`
roots in `E`; equivalently, the minpoly fiber over `P` has cardinality `deg P`. Existence of one
root via `AdjoinRoot P ↪ E` (degrees divide), all of them via normality (finite fields are Galois),
distinctness via separability (finite fields are perfect). -/
theorem card_minpoly_fiber {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : Polynomial F} (hPm : P.Monic) (hirr : Irreducible P)
    (hdvd : P.natDegree ∣ Module.finrank F E) :
    (Finset.univ.filter (fun x : E => minpoly F x = P)).card = P.natDegree := by
  have hne : P ≠ 0 := hPm.ne_zero
  -- the fiber is exactly the root set of `P` in `E`
  have hfiber : Finset.univ.filter (fun x : E => minpoly F x = P) = (P.aroots E).toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_toFinset,
      Polynomial.mem_aroots]
    constructor
    · rintro rfl
      exact ⟨minpoly.ne_zero (IsIntegral.of_finite F x), minpoly.aeval F x⟩
    · rintro ⟨-, haeval⟩
      exact (minpoly.eq_of_irreducible_of_monic hirr haeval hPm).symm
  rw [hfiber]
  -- one root exists: embed `AdjoinRoot P` (degree `deg P` over `F`) into `E`
  haveI : Fact (Irreducible P) := ⟨hirr⟩
  have hfinrank : Module.finrank F (AdjoinRoot P) = P.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne)]
    rfl
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := F) (K := AdjoinRoot P) (L := E)
    (by rw [hfinrank]; exact hdvd)
  have hroot0 : Polynomial.aeval (AdjoinRoot.root P) P = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root P
  have hroot : Polynomial.aeval (φ (AdjoinRoot.root P)) P = 0 := by
    rw [Polynomial.aeval_algHom_apply, hroot0, map_zero]
  -- hence `P` is a minpoly in `E`, and normality (finite fields are Galois) makes it split
  have hmin : minpoly F (φ (AdjoinRoot.root P)) = P :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hPm).symm
  have hsplits : (P.map (algebraMap F E)).Splits := by
    rw [← hmin]
    exact Normal.splits inferInstance _
  -- separability (finite fields are perfect) makes the roots distinct
  have hsep : (P.map (algebraMap F E)).Separable :=
    (PerfectField.separable_of_irreducible hirr).map
  rw [show (P.aroots E).toFinset.card = (P.aroots E).card from by
    rw [Multiset.card_toFinset, (Polynomial.nodup_roots hsep).dedup]]
  have hcard := Polynomial.splits_iff_card_roots.mp hsplits
  rwa [Polynomial.natDegree_map] at hcard

open Polynomial IntermediateField in
open Classical in
/-- **The power sums are the extension character sums.** For a finite extension `E/F` of finite
fields with `m = [E:F]`, `Sₘ = ∑_{x∈E} χ(N x)·ψ(Tr x)` — partition `E` by minimal polynomial
(`sum_fiberwise`), evaluate each element by `char_norm_trace_eq_dhWeight_pow`, each fiber has
`deg P` elements by `card_minpoly_fiber`. -/
theorem powerSum_dhWeight_eq_sum {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    powerSum (dhWeight χ ψ) (Module.finrank F E)
      = ∑ x : E, χ (Algebra.norm F x) * ψ (Algebra.trace F E x) := by
  haveI : FiniteDimensional F E := Module.Finite.of_finite
  set m := Module.finrank F E with hm
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  -- the minpoly map lands in the divisor-indexed irreducibles
  have hmaps : ∀ x : E, x ∈ (Finset.univ : Finset E) →
      minpoly F x ∈ (m.divisors).biUnion (fun d => irredFinset F d) := by
    intro x _
    have hx : IsIntegral F x := .of_finite F x
    have htower : (minpoly F x).natDegree * Module.finrank (↥F⟮x⟯) E = m := by
      rw [← IntermediateField.adjoin.finrank hx]
      exact Module.finrank_mul_finrank F (↥F⟮x⟯) E
    exact Finset.mem_biUnion.mpr ⟨(minpoly F x).natDegree,
      Nat.mem_divisors.mpr ⟨⟨Module.finrank (↥F⟮x⟯) E, htower.symm⟩, hm0⟩,
      mem_irredFinset.mpr ⟨minpoly.monic hx, rfl, minpoly.irreducible hx⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => χ (Algebra.norm F x) * ψ (Algebra.trace F E x))]
  -- evaluate each fiber: constant value times cardinality
  have hfib : ∀ P ∈ (m.divisors).biUnion (fun d => irredFinset F d),
      (∑ x ∈ Finset.univ.filter (fun x : E => minpoly F x = P),
        χ (Algebra.norm F x) * ψ (Algebra.trace F E x))
      = (P.natDegree : ℂ) * dhWeight χ ψ P ^ (m / P.natDegree) := by
    intro P hP
    obtain ⟨d, hd, hPd⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hPm, hPdeg, hirr⟩ := mem_irredFinset.mp hPd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hsum : ∀ x ∈ Finset.univ.filter (fun x : E => minpoly F x = P),
        χ (Algebra.norm F x) * ψ (Algebra.trace F E x)
          = dhWeight χ ψ P ^ (m / P.natDegree) := by
      intro x hx
      obtain ⟨-, hxP⟩ := Finset.mem_filter.mp hx
      rw [char_norm_trace_eq_dhWeight_pow, hxP]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const,
      card_minpoly_fiber hPm hirr (by rw [hPdeg]; exact hdvd), nsmul_eq_mul]
  rw [Finset.sum_congr rfl hfib]
  -- fuse the disjoint union back into the divisor double sum
  have hdisj : (↑(m.divisors) : Set ℕ).PairwiseDisjoint (irredFinset F) := by
    intro d₁ _ d₂ _ hne
    refine Finset.disjoint_left.mpr fun P hP1 hP2 => ?_
    exact hne ((mem_irredFinset.mp hP1).2.1 ▸ (mem_irredFinset.mp hP2).2.1)
  rw [Finset.sum_biUnion hdisj, powerSum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun P hP => ?_
  rw [(mem_irredFinset.mp hP).2.1]

open Polynomial in
/-- **The DAVENPORT–HASSE lifting relation.** For finite fields `E/F` with `m = [E:F] ≥ 1` and
`ψ ≠ 1`: `∑_{x∈E} χ(N x)·ψ(Tr x) = (−1)^{m−1}·(gaussSum χ ψ)^m`. -/
theorem davenport_hasse {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (χ : MulChar F ℂ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∑ x : E, χ (Algebra.norm F x) * ψ (Algebra.trace F E x)
      = (-1) ^ (Module.finrank F E - 1) * gaussSum χ ψ ^ Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_finite
  rw [← powerSum_dhWeight_eq_sum]
  exact powerSum_dhWeight χ hψ _ Module.finrank_pos

/-! ### Norm compatibility of the quadratic character -/

open Classical in
/-- **Norm compatibility**: over finite fields `E/F` of odd characteristic,
`χ₂^{(E)}(x) = χ₂^{(F)}(N x)`. Both are Euler criteria, and the norm is the power
`x^{(#E−1)/(#F−1)}` (`algebraMap_norm_eq_pow`), whose exponent matches:
`(#E−1)/(#F−1) · #F/2 = #E/2`. -/
theorem quadraticChar_norm {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (hF : ringChar F ≠ 2) (x : E) :
    quadraticChar E x = quadraticChar F (Algebra.norm F x) := by
  haveI : FiniteDimensional F E := Module.Finite.of_finite
  haveI : CharP E (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F E).injective (ringChar F)
  have hE2 : ringChar E ≠ 2 := by
    rw [ringChar.eq E (ringChar F)]
    exact hF
  by_cases hx : x = 0
  · subst hx
    rw [Algebra.norm_zero, quadraticChar_zero, quadraticChar_zero]
  · have hN : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    -- the Euler exponents match through the norm-as-power
    have harith : ((Nat.card E - 1) / (Nat.card F - 1)) * (Fintype.card F / 2)
        = Fintype.card E / 2 := by
      have hoF := FiniteField.odd_card_of_char_ne_two hF
      have hoE := FiniteField.odd_card_of_char_ne_two hE2
      have hdvd : (Fintype.card F - 1) ∣ (Fintype.card E - 1) := by
        rw [Module.card_eq_pow_finrank (K := F) (V := E)]
        have h := sub_one_dvd_pow_sub_one ((Fintype.card F : ℤ)) (Module.finrank F E)
        have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
        have h2 : 1 ≤ Fintype.card F ^ Module.finrank F E := Nat.one_le_pow _ _ Fintype.card_pos
        zify [h1, h2]
        exact_mod_cast h
      have h1 : (Fintype.card F - 1) * ((Fintype.card E - 1) / (Fintype.card F - 1))
          = Fintype.card E - 1 := Nat.mul_div_cancel' hdvd
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      set r := Fintype.card F with hr
      set e := Fintype.card E with he
      set s := (e - 1) / (r - 1) with hs
      obtain ⟨u, hu⟩ : ∃ u, r = 2 * u + 1 := ⟨r / 2, by omega⟩
      have hr1 : r - 1 = 2 * u := by omega
      have h2 : 2 * (u * s) = e - 1 := by
        rw [← h1, hr1]
        ring
      have hru : r / 2 = u := by omega
      rw [hru, mul_comm]
      omega
    have keyE : x ^ (Fintype.card E / 2)
        = algebraMap F E ((Algebra.norm F x) ^ (Fintype.card F / 2)) := by
      rw [map_pow, FiniteField.algebraMap_norm_eq_pow, ← pow_mul, harith]
    have hpow : ∀ {c : F}, c = 1 ↔ algebraMap F E c = 1 := fun {c} =>
      ⟨fun h => by rw [h, map_one],
       fun h => (algebraMap F E).injective (by rwa [map_one])⟩
    have key : IsSquare x ↔ IsSquare (Algebra.norm F x) := by
      rw [FiniteField.isSquare_iff hE2 hx, FiniteField.isSquare_iff hF hN, keyE]
      exact hpow.symm
    by_cases hsq : IsSquare x
    · rw [(quadraticChar_one_iff_isSquare hx).mpr hsq,
        (quadraticChar_one_iff_isSquare hN).mpr (key.mp hsq)]
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsq,
        quadraticChar_neg_one_iff_not_isSquare.mpr (fun h => hsq (key.mpr h))]

/-! ### The main theorem: the definite quadratic Gauss sign over 𝔽_q -/

open Classical in
/-- **THE DEFINITE QUADRATIC GAUSS SIGN OVER 𝔽_q** (Berndt–Evans (10.2)+(1.7)). For an odd prime
`p`, a finite field `E` of degree `f` over `ZMod p`, and the canonical additive character
`ψ_E = ψ_p ∘ Tr` (where `ψ_p(a) = exp(2πi·a/p)` is the library's base character — definitionally, so
the prime-field value substitutes faithfully):

`∑_{x∈E} ψ_E(x²) = (−1)^{f−1} · g_p^f`, with `g_p = √p` (`p ≡ 1 mod 4`) / `i√p` (`p ≡ 3 mod 4`). -/
theorem quadGaussSum_sign_fq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    ECCLib.quadGaussSum
        ((AddChar.zmodChar p
          ((GaussSign.stdRoot_isPrimitiveRoot (p := p)
            (Fact.out : p.Prime).pos.ne').pow_eq_one)).compAddMonoidHom
          (Algebra.trace (ZMod p) E).toAddMonoidHom)
      = (-1) ^ (Module.finrank (ZMod p) E - 1)
        * (if p % 4 = 1 then (GaussSign.sqrtp p : ℂ) else Complex.I * GaussSign.sqrtp p)
          ^ Module.finrank (ZMod p) E := by
  haveI : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
  set ψp := AddChar.zmodChar p
    ((GaussSign.stdRoot_isPrimitiveRoot (p := p) (Fact.out : p.Prime).pos.ne').pow_eq_one)
    with hψp_def
  set ψE := ψp.compAddMonoidHom (Algebra.trace (ZMod p) E).toAddMonoidHom with hψE_def
  have hpZ : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  haveI : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  have hE2 : ringChar E ≠ 2 := by
    rw [ringChar.eq E p]
    exact hp2
  have hψp_prim : ψp.IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p
      (GaussSign.stdRoot_isPrimitiveRoot (Fact.out : p.Prime).pos.ne')
  have hψp_ne : ψp ≠ 1 := by
    have h := hψp_prim (show (1 : ZMod p) ≠ 0 from one_ne_zero)
    rwa [AddChar.mulShift_one] at h
  have hψE_ne : ψE ≠ 1 := by
    obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψp_ne
    obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod p) E a
    refine AddChar.ne_one_iff.mpr ⟨y, ?_⟩
    rw [hψE_def, AddChar.compAddMonoidHom_apply]
    change ψp (Algebra.trace (ZMod p) E y) ≠ 1
    rwa [hy]
  rw [ECCLib.quadGaussSum_eq_gaussSum hE2 hψE_ne, gaussSum]
  have hstep : ∀ x : E, quadCharC E x * ψE x
      = quadCharC (ZMod p) (Algebra.norm (ZMod p) x)
        * ψp (Algebra.trace (ZMod p) E x) := by
    intro x
    rw [quadCharC_apply, quadCharC_apply, quadraticChar_norm hpZ x, hψE_def,
      AddChar.compAddMonoidHom_apply]
    congr!
  rw [Finset.sum_congr rfl fun x _ => hstep x,
    davenport_hasse (quadCharC (ZMod p)) hψp_ne,
    ← ECCLib.quadGaussSum_eq_gaussSum hpZ hψp_ne,
    GaussSign.quadGaussSum_sign_char hp2]

end ECCLib.GaussSumFq

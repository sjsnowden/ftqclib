/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.DualObstruction

set_option linter.style.longLine false

/-!
# The Gowers dual norm

The **dual norm** `‖g‖^*_{U^d} = sup_{‖f‖_{U^d} ≤ 1} ‖⟨f, g⟩‖` (with `⟨f,g⟩ = 𝔼[f·\overline g]`), and the
Candela–González-Sánchez–Szegedy lemma **on the object**: a degree-`≤s` phase polynomial has
`U^{s+1}`-dual norm `≤ 1` (`gowersNormDual_phase_le_one`, their `lem:dualnormbound`).

`DualObstruction` proves the operational bound `‖⟨f, e(P)⟩‖ ≤ ‖f‖_{U^{s+1}}` for every `f`; packaging it
as a supremum gives `‖e(P)‖^*_{U^{s+1}} ≤ 1` directly, since `sSup S ≤ 1` needs only that `1` is an upper
bound (`csSup_le`), not that `S` is bounded above. (The *general* pairing `‖⟨f,g⟩‖ ≤ ‖f‖_{U^d}·‖g‖^*` for
arbitrary `g` requires the dual norm to be finite — a norm-equivalence input `‖f‖_2 ≲ ‖f‖_{U^d}` — and is a
further analysis layer.) Mathlib-only; FTQCLib-independent.
-/

namespace ECCLib

variable {V : Type*} [AddCommGroup V] {G : Type*} [AddCommGroup G]

omit [AddCommGroup G] in
lemma iterMderiv_zero (hs : List V) : iterMderiv hs (0 : V → ℂ) = 0 := by
  induction hs with
  | nil => rfl
  | cons h hs ih => rw [iterMderiv_cons, ih]; funext x; simp [mderiv]

variable [Fintype V]

lemma gowersInner_zero (d : ℕ) : gowersInner d (0 : V → ℂ) = 0 := by
  rw [gowersInner]
  simp only [iterMderiv_zero, Pi.zero_apply, Finset.expect_const_zero]

/-- The Gowers norm of the zero function is `0`. -/
lemma gowersNorm_zero (d : ℕ) : gowersNorm d (0 : V → ℂ) = 0 := by
  rw [gowersNorm_eq, gowersInner_zero, norm_zero, Real.zero_rpow]
  positivity

/-- **The `U^d`-dual norm** `‖g‖^*_{U^d} = sup_{‖f‖_{U^d} ≤ 1} ‖⟨f, g⟩‖`, where `⟨f,g⟩ = 𝔼[f·\overline g]`.
The dual of the Gowers norm as a linear functional; its finiteness for `d ≥ 2` is a norm-equivalence fact,
but the bound `‖·‖^* ≤ 1` used below needs only that `1` is an upper bound. -/
noncomputable def gowersNormDual (d : ℕ) (g : V → ℂ) : ℝ :=
  sSup ((fun f => ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖) ''
    {f : V → ℂ | gowersNorm d f ≤ 1})

/-- The dual norm is nonnegative. -/
lemma gowersNormDual_nonneg (d : ℕ) (g : V → ℂ) : 0 ≤ gowersNormDual d g := by
  apply Real.sSup_nonneg
  rintro c ⟨f, _, rfl⟩
  exact norm_nonneg _

/-- **The dual-norm bound, on the object** (Candela–González-Sánchez–Szegedy `lem:dualnormbound`): a
degree-`≤s` phase polynomial has `U^{s+1}`-dual norm at most `1`. -/
theorem gowersNormDual_phase_le_one (ψ : AddChar G ℂ) (hψ : ∀ t, star (ψ t) = ψ (-t))
    {s : ℕ} {P : V → G} (hP : IsPolyDegLE s P) :
    gowersNormDual (s + 1) (fun x => ψ (P x)) ≤ 1 := by
  apply csSup_le
  · exact ⟨_, 0, by simp only [Set.mem_setOf_eq, gowersNorm_zero]; norm_num, rfl⟩
  · rintro c ⟨f, hf, rfl⟩
    exact (correlation_le_gowersNorm ψ hψ hP f).trans hf

/-! ## Finiteness of the dual norm

For `d ≥ 2` the dual norm is a genuine (finite) real, because the Gowers norm dominates a multiple of the
`L²` norm: `‖f‖_2 ≤ |V|^{1/4}‖f‖_{U²}`. This is read straight off the box definition —
`gowersInner 2 f = 𝔼_h‖𝔼_x f(x)\overline{f(x+h)}‖²`, whose `h=0` term is `‖f‖_2^4/|V|` — with no Fourier
analysis. It gives `BddAbove` for the defining supremum and hence the unit-ball pairing. -/

section Finiteness
variable [Nonempty V]

/-- **`L²`–`U²` comparison** (the finiteness input, from the `h=0` term of the box):
`(𝔼_x ‖f x‖²)² ≤ |V| · ‖⟨f,f,f,f⟩_{U²}‖`. -/
lemma gowersU2_finiteness (f : V → ℂ) :
    (Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ))) ^ 2
      ≤ (Fintype.card V : ℝ) * ‖gowersInner 2 f‖ := by
  set G : (Fin 1 → V) → ℝ :=
    fun h' => ‖Finset.expect Finset.univ (iterMderiv (List.ofFn h') f)‖ ^ 2 with hG
  have hEnn : 0 ≤ Finset.expect Finset.univ G := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hnorm : ‖gowersInner 2 f‖ = Finset.expect Finset.univ G := by
    rw [gowersInner_succ_ofReal 1 f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEnn]
  have hofFn : (List.ofFn (0 : Fin 1 → V)) = [0] := by simp [List.ofFn_succ, List.ofFn_zero]
  have hm : iterMderiv (List.ofFn (0 : Fin 1 → V)) f = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [hofFn, iterMderiv_cons, iterMderiv_nil]
    simp only [mderiv, add_zero, ← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hterm : G 0 = (Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ))) ^ 2 := by
    rw [hG]; simp only
    rw [hm, ← Complex.ofReal_expect, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.expect_nonneg (fun _ _ => sq_nonneg _))]
  have hcard : Fintype.card (Fin 1 → V) = Fintype.card V :=
    Fintype.card_congr (Equiv.funUnique (Fin 1) V)
  have hcardpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hsingle : G 0 / (Fintype.card V : ℝ) ≤ Finset.expect Finset.univ G := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, hcard]
    gcongr
    exact Finset.single_le_sum (fun i _ => by rw [hG]; positivity) (Finset.mem_univ 0)
  calc (Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ))) ^ 2
      = G 0 := hterm.symm
    _ = (Fintype.card V : ℝ) * (G 0 / (Fintype.card V : ℝ)) := by field_simp
    _ ≤ (Fintype.card V : ℝ) * Finset.expect Finset.univ G :=
        mul_le_mul_of_nonneg_left hsingle (le_of_lt hcardpos)
    _ = (Fintype.card V : ℝ) * ‖gowersInner 2 f‖ := by rw [hnorm]

/-- The correlation bound behind `BddAbove`: for `‖f‖_{U^d} ≤ 1` (`d ≥ 2`), `‖⟨f,g⟩‖` is bounded by a
constant depending only on `g` and `|V|` — via Cauchy–Schwarz and the `L²`–`U²` comparison. -/
lemma inner_le_bddM {d : ℕ} (hd : 2 ≤ d) (f g : V → ℂ) (hf : gowersNorm d f ≤ 1) :
    ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖
      ≤ Real.sqrt (Real.sqrt (Fintype.card V)
          * Finset.expect Finset.univ (fun x => (‖g x‖ ^ 2 : ℝ))) := by
  have hpow : gowersNorm 2 f ^ (2 ^ 2) = ‖gowersInner 2 f‖ := by
    rw [gowersNorm_eq, ← Real.rpow_natCast (‖gowersInner 2 f‖ ^ ((1 : ℝ) / 2 ^ 2)) (2 ^ 2),
      ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, Nat.cast_ofNat, one_div,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  have h1 : ‖gowersInner 2 f‖ ≤ 1 := by
    rw [← hpow]; exact pow_le_one₀ (gowersNorm_nonneg 2 f) ((gowersNorm_mono hd f).trans hf)
  have hf2nn : 0 ≤ Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ)) :=
    Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have h3 : Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ)) ≤ Real.sqrt (Fintype.card V) := by
    rw [show Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ))
          = Real.sqrt ((Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ))) ^ 2) from
        (Real.sqrt_sq hf2nn).symm]
    apply Real.sqrt_le_sqrt
    calc (Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ))) ^ 2
        ≤ (Fintype.card V : ℝ) * ‖gowersInner 2 f‖ := gowersU2_finiteness f
      _ ≤ (Fintype.card V : ℝ) * 1 := by gcongr
      _ = Fintype.card V := mul_one _
  have hcs : ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖
      ≤ Finset.expect Finset.univ (fun x => ‖f x‖ * ‖g x‖) := by
    refine (RCLike.norm_expect_le (K := ℝ)).trans (le_of_eq (Finset.expect_congr rfl (fun x _ => ?_)))
    rw [norm_mul, Complex.norm_conj]
  have h5 : ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖ ^ 2
      ≤ Real.sqrt (Fintype.card V) * Finset.expect Finset.univ (fun x => (‖g x‖ ^ 2 : ℝ)) := by
    calc ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖ ^ 2
        ≤ (Finset.expect Finset.univ (fun x => ‖f x‖ * ‖g x‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcs 2
      _ ≤ (Finset.expect Finset.univ (fun x => (‖f x‖ ^ 2 : ℝ)))
            * (Finset.expect Finset.univ (fun x => (‖g x‖ ^ 2 : ℝ))) :=
          Finset.expect_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ Real.sqrt (Fintype.card V) * Finset.expect Finset.univ (fun x => (‖g x‖ ^ 2 : ℝ)) := by gcongr
  calc ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖
      = Real.sqrt (‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h5

/-- **The dual norm is finite** for `d ≥ 2`: the defining supremum is bounded above. -/
lemma gowersNormDual_bddAbove {d : ℕ} (hd : 2 ≤ d) (g : V → ℂ) :
    BddAbove ((fun f => ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖) ''
      {f : V → ℂ | gowersNorm d f ≤ 1}) :=
  ⟨_, by rintro c ⟨f, hf, rfl⟩; exact inner_le_bddM hd f g hf⟩

/-- **The unit-ball pairing:** for `‖f‖_{U^d} ≤ 1` (`d ≥ 2`), `‖⟨f,g⟩‖ ≤ ‖g‖^*_{U^d}`. -/
lemma le_gowersNormDual_of_norm_le_one {d : ℕ} (hd : 2 ≤ d) (g f : V → ℂ)
    (hf : gowersNorm d f ≤ 1) :
    ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖ ≤ gowersNormDual d g :=
  le_csSup (gowersNormDual_bddAbove hd g) ⟨f, hf, rfl⟩

/-! ### Homogeneity and the general pairing

Multiplying `f` by a scalar `c` scales the Gowers norm by `‖c‖` (`gowersNorm_const_smul`). With finiteness,
this upgrades the unit-ball pairing to the full defining inequality `‖⟨f,g⟩‖ ≤ ‖f‖_{U^d}·‖g‖^*_{U^d}`. -/

omit [Fintype V] [Nonempty V] in
/-- The multiplicative derivative scales by `‖k‖²`: `∂_h(k·g) = ‖k‖²·∂_h g`. -/
lemma mderiv_const_smul (k : ℂ) (h : V) (g : V → ℂ) :
    mderiv h (fun x => k * g x) = fun x => (↑(‖k‖ ^ 2) : ℂ) * mderiv h g x := by
  funext x
  simp only [mderiv, star_mul']
  rw [show k * g (x + h) * (star k * star (g x)) = (k * star k) * (g (x + h) * star (g x)) from by ring,
    show k * star k = ((‖k‖ ^ 2 : ℝ) : ℂ) from by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]]

omit [Fintype V] [Nonempty V] in
/-- Over a nonempty list of directions, `∂_{hs}(k·f) = ‖k‖^{2^{|hs|}}·∂_{hs} f` (the `k ↦ ‖k‖²`
compounding). -/
lemma iterMderiv_const_smul (k : ℂ) (f : V → ℂ) :
    ∀ hs : List V, hs ≠ [] →
      iterMderiv hs (fun x => k * f x)
        = fun x => (↑(‖k‖ ^ (2 ^ hs.length)) : ℂ) * iterMderiv hs f x := by
  intro hs
  induction hs with
  | nil => intro h; exact absurd rfl h
  | cons a hs ih =>
    intro _
    cases hs with
    | nil =>
      rw [iterMderiv_cons, iterMderiv_nil, mderiv_const_smul]
      funext x; simp [iterMderiv_cons, iterMderiv_nil]
    | cons b hs' =>
      rw [iterMderiv_cons, ih (by simp), mderiv_const_smul]
      funext x
      simp only [iterMderiv_cons]
      have hnn : (0 : ℝ) ≤ ‖k‖ ^ (2 ^ (b :: hs').length) := by positivity
      rw [show ‖((‖k‖ ^ (2 ^ (b :: hs').length) : ℝ) : ℂ)‖ ^ 2
            = ‖k‖ ^ (2 ^ (a :: b :: hs').length) from by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, ← pow_mul]
        congr 1]

omit [Nonempty V] in
/-- The Gowers inner product is `2^d`-homogeneous: `⟨c·f,…⟩ = ‖c‖^{2^d}·⟨f,…⟩`. -/
lemma gowersInner_const_smul {d : ℕ} (hd : 1 ≤ d) (c : ℂ) (f : V → ℂ) :
    gowersInner d (fun x => c * f x) = (↑(‖c‖ ^ (2 ^ d)) : ℂ) * gowersInner d f := by
  simp only [gowersInner]
  rw [Finset.mul_expect]
  refine Finset.expect_congr rfl (fun p _ => ?_)
  have hne : (List.ofFn p.2) ≠ [] := by rw [← List.length_pos_iff, List.length_ofFn]; omega
  rw [iterMderiv_const_smul c f (List.ofFn p.2) hne, List.length_ofFn]

omit [Nonempty V] in
/-- **Homogeneity of the Gowers norm:** `‖c·f‖_{U^d} = ‖c‖·‖f‖_{U^d}` (for `d ≥ 1`). -/
lemma gowersNorm_const_smul {d : ℕ} (hd : 1 ≤ d) (c : ℂ) (f : V → ℂ) :
    gowersNorm d (fun x => c * f x) = ‖c‖ * gowersNorm d f := by
  rw [gowersNorm_eq, gowersNorm_eq, gowersInner_const_smul hd, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖c‖ ^ (2 ^ d)),
    Real.mul_rpow (by positivity) (norm_nonneg _)]
  congr 1
  rw [← Real.rpow_natCast ‖c‖ (2 ^ d), ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, Nat.cast_ofNat,
    mul_one_div, div_self (by positivity), Real.rpow_one]

omit [Nonempty V] [AddCommGroup V] in
/-- The pairing is linear in `f`: `⟨c·f, g⟩ = c·⟨f, g⟩`. -/
lemma inner_const_smul (c : ℂ) (f g : V → ℂ) :
    Finset.expect Finset.univ (fun x => (c * f x) * (starRingEnd ℂ) (g x))
      = c * Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x)) := by
  rw [Finset.mul_expect]; exact Finset.expect_congr rfl (fun x _ => by ring)

/-- **The dual-norm pairing** (the defining inequality of `‖·‖^*`): `‖⟨f,g⟩‖ ≤ ‖f‖_{U^d}·‖g‖^*_{U^d}` for
`d ≥ 2`. Upgrades the unit-ball case by scaling `f` to Gowers-norm `1` (homogeneity). -/
theorem inner_le_gowersNorm_mul_dual {d : ℕ} (hd : 2 ≤ d) (f g : V → ℂ) :
    ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖
      ≤ gowersNorm d f * gowersNormDual d g := by
  rcases (gowersNorm_nonneg d f).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    by_contra hlt
    rw [not_le] at hlt
    set t : ℝ := (gowersNormDual d g + 1)
      / ‖Finset.expect Finset.univ (fun x => f x * (starRingEnd ℂ) (g x))‖ with ht
    have htnn : 0 ≤ t := by have := gowersNormDual_nonneg d g; positivity
    have hc : gowersNorm d (fun x => (↑t : ℂ) * f x) ≤ 1 := by
      rw [gowersNorm_const_smul (by omega), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg htnn, ← h0, mul_zero]
      norm_num
    have hpair := le_gowersNormDual_of_norm_le_one hd g _ hc
    rw [inner_const_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htnn,
      ht, div_mul_cancel₀ _ (ne_of_gt hlt)] at hpair
    linarith
  · have hc : gowersNorm d (fun x => (↑(1 / gowersNorm d f) : ℂ) * f x) ≤ 1 := by
      rw [gowersNorm_const_smul (by omega), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hpos)]
    have hpair := le_gowersNormDual_of_norm_le_one hd g _ hc
    rw [inner_const_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), one_div, inv_mul_le_iff₀ hpos] at hpair
    linarith

end Finiteness

end ECCLib

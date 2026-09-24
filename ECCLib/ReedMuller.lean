/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Decoding
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.VecNotation

set_option linter.unusedSectionVars false

/-!
# First-order Reed–Muller codes and the Walsh–Hadamard decoder

The first-order Reed–Muller code `RM(1,m)` has the point space `𝔽₂^m` as its index set and the
**affine forms** `x ↦ ⟨x,a⟩ + b` as its codewords — these are exactly the (±1-valued, after the
sign character) affine `𝔽₂` characters. Walsh–Hadamard decoding is "correlate the received word
against every character, take the argmax", i.e. **the library's own Fourier operator doing the
decoding**: the correlation table is `fourierOp sgnChar` applied to the ±1-lift of the received
word (`walsh_eq_fourier`).

Two layers, as throughout the coding library:

* the **executable decoder** `fwhtDec` runs on ℤ-valued correlations (`walsh`) — computable,
  `decide`-friendly, no ℂ anywhere;
* the **Fourier certificate** (`walsh_eq_fourier`, `two_mul_hammingDist_eq_fourier`) identifies
  those correlations with the `fourierOp` coefficients, tying the decoder to the Fourier engine.

Main results:

* `finrank_rm1` — `dim RM(1,m) = m + 1`;
* `two_mul_minDist_rm1` — `2·d = 2^m` (subtraction-free; `minDist_rm1` gives `d = 2^(m-1)`);
* `fwhtDec_isMD` — the argmax-correlation decoder is a minimum-distance decoder;
* `fwhtDec_corrects` — it corrects `t` errors whenever `4t < 2^m`;
* `walsh_eq_fourier` — the correlation IS the Fourier coefficient;
* worked examples at `m = 3` (`RM(1,3) = [8,4,4]`), including a live corrected transmission.
-/

namespace ECCLib.Coding

open ECCLib.Heisenberg

variable (m : ℕ)

/-! ## The code: affine forms, evaluated on the point space -/

/-- Affine evaluation: the pair `(a, b)` becomes the function `x ↦ ⟨x,a⟩ + b` on the point
space `𝔽₂^m`. `RM(1,m)` is its range; injectivity gives the dimension. -/
def affEval : ((Fin m → ZMod 2) × ZMod 2) →ₗ[ZMod 2] ((Fin m → ZMod 2) → ZMod 2) where
  toFun c := fun x => pairing x c.1 + c.2
  map_add' c d := by
    funext x
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [pairing_add_right]
    ring
  map_smul' r c := by
    funext x
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [pairing_smul_right]
    ring

lemma affEval_apply (c : (Fin m → ZMod 2) × ZMod 2) (x : Fin m → ZMod 2) :
    affEval m c x = pairing x c.1 + c.2 := rfl

/-- The **first-order Reed–Muller code** `RM(1,m)`: the evaluations of affine forms. Length
`2^m`, dimension `m + 1`, distance `2^(m-1)`. -/
def rm1 : Submodule (ZMod 2) ((Fin m → ZMod 2) → ZMod 2) :=
  LinearMap.range (affEval m)

theorem mem_rm1 {v : (Fin m → ZMod 2) → ZMod 2} :
    v ∈ rm1 m ↔ ∃ c, affEval m c = v :=
  LinearMap.mem_range

/-- Distinct affine data give distinct functions: evaluate at `0` for the constant, then use
nondegeneracy of the pairing for the linear part. -/
theorem affEval_injective : Function.Injective (affEval m) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro ⟨a, b⟩ hc
  rw [LinearMap.mem_ker] at hc
  have hb : b = 0 := by
    have h0 := congrFun hc 0
    simpa only [affEval_apply, pairing_zero_left, zero_add, Pi.zero_apply] using h0
  have ha : a = 0 := by
    refine eq_zero_of_pairing_left a fun p => ?_
    have hx := congrFun hc p
    rw [affEval_apply] at hx
    simp only [Pi.zero_apply] at hx
    rw [hb, add_zero] at hx
    rw [pairing_symm]
    exact hx
  rw [ha, hb]
  rfl

/-- `dim RM(1,m) = m + 1` — one dimension per coordinate functional plus the constants. -/
theorem finrank_rm1 : Module.finrank (ZMod 2) (rm1 m) = m + 1 := by
  unfold rm1
  rw [LinearMap.finrank_range_of_inj (affEval_injective m), Module.finrank_prod,
    Module.finrank_pi, Module.finrank_self, Fintype.card_fin]

/-! ## The half-count: a nonzero linear form is balanced

For `a ≠ 0` each fiber of `x ↦ ⟨x,a⟩` has exactly half the points. The bijection between the
two fibers is translation by any `x₀` with `⟨x₀,a⟩ = 1` — in characteristic 2 it is its own
inverse, so `Finset.card_bij'` applies with the same map both ways. -/

lemma exists_pairing_eq_one {a : Fin m → ZMod 2} (ha : a ≠ 0) :
    ∃ x₀ : Fin m → ZMod 2, pairing x₀ a = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have h2 : ∀ u : ZMod 2, u ≠ 0 → u = 1 := by decide
  refine ⟨Pi.single i 1, ?_⟩
  rw [pairing_single]
  exact h2 _ (by simpa using hi)

lemma two_mul_card_pairing_fiber {a : Fin m → ZMod 2} (ha : a ≠ 0) (c : ZMod 2) :
    2 * (Finset.univ.filter fun x => pairing x a = c).card = 2 ^ m := by
  obtain ⟨x₀, hx₀⟩ := exists_pairing_eq_one m ha
  have hself : ∀ v : Fin m → ZMod 2, v + v = 0 := by
    intro v
    funext i
    have h2 : ∀ u : ZMod 2, u + u = 0 := by decide
    simpa using h2 (v i)
  have h11 : ∀ u : ZMod 2, u + 1 + 1 = u := by decide
  have hbij : (Finset.univ.filter fun x => pairing x a = c).card
      = (Finset.univ.filter fun x => pairing x a = c + 1).card := by
    refine Finset.card_bij' (fun x _ => x + x₀) (fun y _ => y + x₀) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [pairing_add_left, hx, hx₀]
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [pairing_add_left, hy, hx₀, h11]
    · intro x _
      change x + x₀ + x₀ = x
      rw [add_assoc, hself, add_zero]
    · intro y _
      change y + x₀ + x₀ = y
      rw [add_assoc, hself, add_zero]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → ZMod 2))) (p := fun x => pairing x a = c)
  have hcompl : (Finset.univ.filter fun x => ¬ pairing x a = c)
      = (Finset.univ.filter fun x => pairing x a = c + 1) := by
    refine Finset.filter_congr fun x _ => ?_
    have hne : ∀ u v : ZMod 2, ¬ u = v ↔ u = v + 1 := by decide
    exact hne _ _
  rw [hcompl, ← hbij] at hsplit
  have hcard : (Finset.univ : Finset (Fin m → ZMod 2)).card = 2 ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  omega

/-- The weight of a codeword with nonzero linear part is exactly half the length. -/
lemma two_mul_hammingNorm_affEval {a : Fin m → ZMod 2} (ha : a ≠ 0) (b : ZMod 2) :
    2 * hammingNorm (affEval m (a, b)) = 2 ^ m := by
  have hnorm : hammingNorm (affEval m (a, b))
      = (Finset.univ.filter fun x => pairing x a = b + 1).card := by
    unfold hammingNorm
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    rw [affEval_apply]
    have h : ∀ u v : ZMod 2, u + v ≠ 0 ↔ u = v + 1 := by decide
    exact h _ _
  rw [hnorm, two_mul_card_pairing_fiber m ha]

/-! ## The distance -/

/-- **The distance theorem, subtraction-free**: `2·d(RM(1,m)) = 2^m`. Upper bound from any
coordinate functional; lower bound because every nonzero codeword either has nonzero linear
part (weight exactly `2^(m-1)`) or is the constant `1` (weight `2^m`). -/
theorem two_mul_minDist_rm1 (hm : 1 ≤ m) : 2 * minDist (rm1 m) = 2 ^ m := by
  set i₀ : Fin m := ⟨0, hm⟩
  have ha0 : (Pi.single i₀ 1 : Fin m → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h i₀
    rw [Pi.single_eq_same, Pi.zero_apply] at this
    exact one_ne_zero this
  set w : (Fin m → ZMod 2) → ZMod 2 := affEval m (Pi.single i₀ 1, 0) with hw_def
  have hw_mem : w ∈ rm1 m := LinearMap.mem_range_self _ _
  have hw0 : w ≠ 0 := by
    intro h
    have hc := affEval_injective m (h.trans (map_zero (affEval m)).symm)
    exact ha0 (congrArg Prod.fst hc)
  have hwt : 2 * hammingNorm w = 2 ^ m := two_mul_hammingNorm_affEval m ha0 0
  have hle : 2 * minDist (rm1 m) ≤ 2 ^ m := by
    have := minDist_le_of_mem hw_mem hw0
    omega
  have hbot : rm1 m ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hw_mem
    exact hw0 hw_mem
  obtain ⟨v, hvC, hv0, hvw⟩ := exists_minDist hbot
  obtain ⟨⟨ca, cb⟩, hc⟩ := LinearMap.mem_range.mp hvC
  have hge : 2 ^ m ≤ 2 * hammingNorm v := by
    by_cases hca : ca = 0
    · have hcb : cb ≠ 0 := by
        intro hcb0
        apply hv0
        rw [← hc, hca, hcb0]
        exact map_zero _
      have hval : ∀ x, v x = cb := by
        intro x
        rw [← hc, affEval_apply]
        simp only [hca, pairing_zero_right, zero_add]
      have hwv : hammingNorm v = 2 ^ m := by
        unfold hammingNorm
        rw [Finset.filter_true_of_mem fun x _ => by rw [hval x]; exact hcb]
        rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      omega
    · have h2 := two_mul_hammingNorm_affEval m hca cb
      rw [hc] at h2
      omega
  omega

/-- The literature form: `d(RM(1,m)) = 2^(m-1)`. -/
theorem minDist_rm1 (hm : 1 ≤ m) : minDist (rm1 m) = 2 ^ (m - 1) := by
  have h := two_mul_minDist_rm1 m hm
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
    ring
  omega

/-! ## A self-contained computable argmax

Mathlib's `List.argmax` at `β = ℤ` picks up the **noncomputable** conditionally-complete order
instance through this cone's analysis imports, which both blocks compilation of the decoder and
stalls kernel `decide` (the instance term contains `Classical.choice`). The decoder needs no
order structure — a bare recursive maximum over ℤ-scores with its spec lemmas keeps everything
computable and kernel-reducible. Generic; argmin searches elsewhere can reuse it. -/

section ArgmaxBy

variable {α : Type*}

/-- The argmax of an ℤ-valued score over a list (ties go to the later element). -/
def argmaxBy (f : α → ℤ) : List α → Option α
  | [] => none
  | a :: l =>
    match argmaxBy f l with
    | none => some a
    | some b => if f b < f a then some a else some b

theorem argmaxBy_cons (f : α → ℤ) (a : α) (l : List α) :
    argmaxBy f (a :: l) = match argmaxBy f l with
      | none => some a
      | some b => if f b < f a then some a else some b := rfl

theorem argmaxBy_ne_none {f : α → ℤ} (a : α) (l : List α) : argmaxBy f (a :: l) ≠ none := by
  rw [argmaxBy_cons]
  cases hrec : argmaxBy f l with
  | none => simp
  | some b => by_cases hlt : f b < f a <;> simp [hlt]

theorem argmaxBy_eq_none {f : α → ℤ} : ∀ {l : List α}, argmaxBy f l = none → l = [] := by
  intro l h
  cases l with
  | nil => rfl
  | cons x l => exact absurd h (argmaxBy_ne_none x l)

theorem argmaxBy_mem {f : α → ℤ} : ∀ {l : List α} {a : α}, argmaxBy f l = some a → a ∈ l := by
  intro l
  induction l with
  | nil => intro a h; simp [argmaxBy] at h
  | cons x l ih =>
    intro a h
    rw [argmaxBy_cons] at h
    cases hrec : argmaxBy f l with
    | none =>
      simp only [hrec] at h
      rw [← Option.some.inj h]
      exact List.mem_cons_self
    | some b =>
      simp only [hrec] at h
      by_cases hlt : f b < f x
      · rw [if_pos hlt] at h
        rw [← Option.some.inj h]
        exact List.mem_cons_self
      · rw [if_neg hlt] at h
        rw [← Option.some.inj h]
        exact List.mem_cons_of_mem _ (ih hrec)

/-- The argmax spec: every list element scores no higher. -/
theorem le_of_argmaxBy {f : α → ℤ} : ∀ {l : List α} {a b : α},
    argmaxBy f l = some a → b ∈ l → f b ≤ f a := by
  intro l
  induction l with
  | nil => intro a b h _; simp [argmaxBy] at h
  | cons x l ih =>
    intro a b h hb
    rw [argmaxBy_cons] at h
    rcases List.mem_cons.mp hb with hbx | hbl
    · rw [hbx]
      cases hrec : argmaxBy f l with
      | none =>
        simp only [hrec] at h
        rw [← Option.some.inj h]
      | some c =>
        simp only [hrec] at h
        by_cases hlt : f c < f x
        · rw [if_pos hlt] at h
          rw [← Option.some.inj h]
        · rw [if_neg hlt] at h
          rw [← Option.some.inj h]
          exact not_lt.mp hlt
    · cases hrec : argmaxBy f l with
      | none =>
        rw [argmaxBy_eq_none hrec] at hbl
        exact absurd hbl List.not_mem_nil
      | some c =>
        simp only [hrec] at h
        have hbc := ih hrec hbl
        by_cases hlt : f c < f x
        · rw [if_pos hlt] at h
          rw [← Option.some.inj h]
          exact le_trans hbc (le_of_lt hlt)
        · rw [if_neg hlt] at h
          rw [← Option.some.inj h]
          exact hbc

end ArgmaxBy

/-! ## The candidate list

`Finset.univ.toList` is noncomputable (`Multiset.toList` chooses a representative), so the
decoder enumerates its candidates by explicit structural recursion instead — computable,
order-stable, and kernel-reducible for the `decide` examples. -/

/-- All vectors of `𝔽₂^n`, as an explicit list (each vector splits as `Fin.cons`). -/
def allVecs : (n : ℕ) → List (Fin n → ZMod 2)
  | 0 => [Fin.elim0]
  | n + 1 => (allVecs n).flatMap fun v => [Fin.cons 0 v, Fin.cons 1 v]

theorem mem_allVecs : ∀ {n : ℕ} (v : Fin n → ZMod 2), v ∈ allVecs n := by
  intro n
  induction n with
  | zero =>
    intro v
    have hv : v = Fin.elim0 := funext fun i => i.elim0
    rw [hv]
    exact List.mem_cons_self
  | succ n ih =>
    intro v
    have h2 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
    change v ∈ (allVecs n).flatMap fun w => [Fin.cons 0 w, Fin.cons 1 w]
    refine List.mem_flatMap.mpr ⟨Fin.tail v, ih _, ?_⟩
    rw [List.mem_cons, List.mem_singleton]
    rcases h2 (v 0) with h0 | h1
    · exact Or.inl (by rw [← h0]; exact (Fin.cons_self_tail v).symm)
    · exact Or.inr (by rw [← h1]; exact (Fin.cons_self_tail v).symm)

/-- The decoder's candidate list: all affine data `(a, b)`. -/
def allCands : List ((Fin m → ZMod 2) × ZMod 2) :=
  (allVecs m).flatMap fun a => [(a, 0), (a, 1)]

theorem mem_allCands (c : (Fin m → ZMod 2) × ZMod 2) : c ∈ allCands m := by
  obtain ⟨a, b⟩ := c
  have h2 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  refine List.mem_flatMap.mpr ⟨a, mem_allVecs a, ?_⟩
  rw [List.mem_cons, List.mem_singleton]
  rcases h2 b with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem allCands_ne_nil : allCands m ≠ [] :=
  List.ne_nil_of_mem (mem_allCands m (0, 0))

/-! ## The Walsh correlations and the decoder (the executable layer, over ℤ) -/

/-- The **Walsh correlation** of a received word with the affine candidate `c`: agreements
minus disagreements, an integer. `walsh_eq` identifies it with `2^m − 2·d_H`; maximizing it is
minimizing Hamming distance. Computable — the decoder runs on this, not on ℂ. -/
def walsh (y : (Fin m → ZMod 2) → ZMod 2) (c : (Fin m → ZMod 2) × ZMod 2) : ℤ :=
  ∑ x : Fin m → ZMod 2, if y x = affEval m c x then 1 else -1

theorem walsh_eq (y : (Fin m → ZMod 2) → ZMod 2) (c : (Fin m → ZMod 2) × ZMod 2) :
    walsh m y c = (2 ^ m : ℤ) - 2 * hammingDist y (affEval m c) := by
  unfold walsh
  have hpt : ∀ x : Fin m → ZMod 2, (if y x = affEval m c x then (1 : ℤ) else -1)
      = 1 - 2 * (if y x ≠ affEval m c x then (1 : ℤ) else 0) := by
    intro x
    by_cases h : y x = affEval m c x <;> simp [h]
  rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_sub_distrib, Finset.sum_const,
    ← Finset.mul_sum, Finset.sum_boole]
  have hcard : (Finset.univ : Finset (Fin m → ZMod 2)).card = 2 ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hdist : (Finset.univ.filter fun x => y x ≠ affEval m c x).card
      = hammingDist y (affEval m c) := rfl
  rw [hdist, hcard]
  ring

/-- The **Walsh–Hadamard decoder**: correlate against every affine candidate, return the
argmax. Computable; `fwhtDec_isMD` is the correctness statement. -/
def fwhtDec (y : (Fin m → ZMod 2) → ZMod 2) : Option ((Fin m → ZMod 2) → ZMod 2) :=
  (argmaxBy (walsh m y) (allCands m)).map (affEval m)

/-- **Maximum correlation is minimum distance**: the Walsh–Hadamard decoder is an MD decoder
for `RM(1,m)`. -/
theorem fwhtDec_isMD : IsMDDecoder (fwhtDec m) (rm1 m) := by
  intro y
  obtain ⟨cmax, hcmax⟩ : ∃ cm, argmaxBy (walsh m y) (allCands m) = some cm := by
    cases hh : argmaxBy (walsh m y) (allCands m) with
    | none => exact absurd (argmaxBy_eq_none hh) (allCands_ne_nil m)
    | some cm => exact ⟨cm, rfl⟩
  refine ⟨affEval m cmax, ?_, LinearMap.mem_range_self _ cmax, ?_⟩
  · unfold fwhtDec
    rw [hcmax]
    rfl
  · intro c' hc'
    obtain ⟨p', hp'⟩ := LinearMap.mem_range.mp hc'
    have hle := le_of_argmaxBy hcmax (mem_allCands m p')
    have h1 := walsh_eq m y p'
    have h2 := walsh_eq m y cmax
    rw [hp'] at h1
    rw [h1, h2] at hle
    omega

/-- **The correction guarantee, subtraction-free**: the Walsh–Hadamard decoder corrects `t`
errors whenever `4t < 2^m` (that is, `t < 2^(m-2)` — e.g. `t = 1` at `m = 3`). -/
theorem fwhtDec_corrects (hm : 1 ≤ m) {t : ℕ} (ht : 4 * t < 2 ^ m) :
    Corrects (fwhtDec m) (rm1 m) t := by
  refine (fwhtDec_isMD m).corrects ?_
  have hd := two_mul_minDist_rm1 m hm
  omega

/-! ## The Fourier certificate (the ℂ layer)

The sign character `𝔽₂ → ℂˣ` turns the ℤ-valued Walsh correlation into a genuine Fourier
coefficient of the ±1-lift of the received word: `walsh y (a,b) = sgnChar b · (𝓕 (sgnChar ∘ y)) a`
with `𝓕 = fourierOp sgnChar` — **the library's DFT computes the decoder's correlation table**. -/

/-- The underlying function of the sign character: `0 ↦ 1`, `1 ↦ -1`. -/
noncomputable def sgnFun (u : ZMod 2) : ℂ :=
  if u = 0 then 1 else -1

private lemma sgnFun_add (a b : ZMod 2) : sgnFun (a + b) = sgnFun a * sgnFun b := by
  have h4 : ∀ u v : ZMod 2, u ≠ 0 → v ≠ 0 → u + v = 0 := by decide
  unfold sgnFun
  by_cases ha : a = 0
  · by_cases hb : b = 0 <;> simp [ha, hb]
  · by_cases hb : b = 0
    · simp [ha, hb]
    · simp [ha, hb, h4 a b ha hb]

/-- The **sign character** of `𝔽₂`, the nontrivial additive character `u ↦ (-1)^u : ℂ`. -/
noncomputable def sgnChar : AddChar (ZMod 2) ℂ where
  toFun := sgnFun
  map_zero_eq_one' := if_pos rfl
  map_add_eq_mul' := sgnFun_add

lemma sgnChar_apply (u : ZMod 2) : sgnChar u = if u = 0 then 1 else -1 := rfl

/-- The scalar bridge: the ±1 bookkeeping of one point of the correlation sum, written
multiplicatively through the sign character. -/
private lemma sgnChar_ite (u p b : ZMod 2) :
    (if u = p + b then (1 : ℂ) else -1) = sgnChar b * (sgnChar p * sgnChar u) := by
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, sgnChar_apply]
  have hiff : ∀ u p b : ZMod 2, u = p + b ↔ b + (p + u) = 0 := by decide
  exact if_congr (hiff u p b) rfl rfl

/-- **The correlation is the Fourier coefficient**: the executable decoder's ℤ-valued Walsh
statistic is, up to the sign of the constant term, the `fourierOp` coefficient of the ±1-lift
of the received word. This is the library's Fourier engine doing the decoding. -/
theorem walsh_eq_fourier (y : (Fin m → ZMod 2) → ZMod 2) (c : (Fin m → ZMod 2) × ZMod 2) :
    (walsh m y c : ℂ)
      = sgnChar c.2 * fourierOp sgnChar (fun x => sgnChar (y x)) c.1 := by
  rw [fourierOp_apply, Finset.mul_sum]
  unfold walsh
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [affEval_apply, pairing_symm c.1 x]
  exact sgnChar_ite (y x) (pairing x c.1) c.2

/-- **Distance from the Fourier coefficient** (the main form): `2·d_H(y, aff(a,b)) =
2^m − sgn(b)·(𝓕 (±1)^y)(a)`. Decoding = reading distances off the Fourier transform. -/
theorem two_mul_hammingDist_eq_fourier (y : (Fin m → ZMod 2) → ZMod 2)
    (c : (Fin m → ZMod 2) × ZMod 2) :
    2 * (hammingDist y (affEval m c) : ℂ)
      = 2 ^ m - sgnChar c.2 * fourierOp sgnChar (fun x => sgnChar (y x)) c.1 := by
  have h := walsh_eq_fourier m y c
  have h2 : (walsh m y c : ℂ) = 2 ^ m - 2 * (hammingDist y (affEval m c) : ℂ) := by
    rw [walsh_eq]
    push_cast
    ring
  rw [h2] at h
  linear_combination -h

/-! ## Worked examples — `RM(1,3) = [8,4,4]` and a live corrected transmission -/

example : Module.finrank (ZMod 2) (rm1 3) = 4 := finrank_rm1 3

theorem minDist_rm1_three : minDist (rm1 3) = 4 := by
  have := two_mul_minDist_rm1 3 (by norm_num)
  omega

example : IsMDDecoder (fwhtDec 3) (rm1 3) := fwhtDec_isMD 3

/-- `RM(1,3)` corrects one error through the Walsh–Hadamard decoder: `4·1 < 2³`. -/
theorem fwhtDec_corrects_one : Corrects (fwhtDec 3) (rm1 3) 1 :=
  fwhtDec_corrects 3 (by norm_num) (by norm_num)

/-- The transmitted codeword: the affine form `x ↦ x₀ + x₁` (data `a = (1,1,0)`, `b = 0`). -/
def rmSent : (Fin 3 → ZMod 2) → ZMod 2 := affEval 3 (![1, 1, 0], 0)

/-- A single-point error: flip the received bit at the point `(0,0,0)` of the cube. -/
def rmErr : (Fin 3 → ZMod 2) → ZMod 2 := fun x => if x = ![0, 0, 0] then 1 else 0

/-- **The corrected transmission, by theorem**: the correction guarantee applied to a weight-1
error (the weight bound is the only `decide`). -/
theorem fwhtDec_transmission : fwhtDec 3 (rmSent + rmErr) = some rmSent :=
  fwhtDec_corrects_one rmSent (LinearMap.mem_range_self _ _) rmErr (by decide)

/-- **The corrected transmission, by evaluation**: the same fact by running the executable
decoder — the argmax over all 16 correlations — inside the kernel. -/
example : fwhtDec 3 (rmSent + rmErr) = some rmSent := by decide

end ECCLib.Coding

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Frame.PrecisionValuation
import FTQCLib.Hierarchy.DyadicValuation

set_option linter.style.longLine false

/-!
# The Möbius product up the tower — the ℤ/8 product question, answered

The frame's Möbius/cup product `mobiusCoeff_mul` (`FTQCLib/Frame/CubicCeiling.lean`) — the engine of
the cubic ceiling — is stated at `ZMod 4`, and its ceiling mechanism (`even_mul_even_zero`,
`2·2 = 0`) is exactly the saturation that *changes* at `ℤ/8` (`4·4 = 0`, but `2·2 = 4 ≠ 0`). Does
the product calculus exist above the floor at all, and what does the degree bookkeeping become? This
file answers both:

1. **The product calculus exists at every rung** (§1). The Möbius convolution
   `mobiusCoeff S (f·g) = Σ_{A∪B=S} (mobiusCoeff A f)·(mobiusCoeff B g)` and the subadditive degree
   `MobiusDegLE (d+e) (f·g)` hold over **any commutative ring** — the `ZMod 4` typing of the
   `CubicCeiling` version reflects where it is used, not the mathematics. `ℤ/4`, `ℤ/8`, and every
   `ℤ/2^m` are instances of one theorem.
2. **The coefficient arithmetic is the saturating valuation** (§2). Over `ZMod (2^m)` the
   coefficient products obey `twoAdicVal_mul`: the grade is **filtered, not graded** —
   `mul_eq_zero_of_val_saturated` is the general ceiling mechanism.
3. **At `ℤ/8` the ceiling becomes a two-stage cascade** (§3). Sign-level (2-torsion, `{0,4}`) top
   coefficients annihilate (`4·4 = 0` — the `ℤ/4` ceiling mechanism recurring one rung up:
   `mobiusDegLE_mul_signTop`), while mid-level (4-torsion, `{0,2,4,6}`) tops do **not** vanish
   (`2·2 = 4`) but **descend one rung** to the sign level (`signTop_mul_of_midTop`). The *"each
   degree needs one more 2-adic rung"* law (`TowerPolarization`) is now a **product law**: one
   multiplication costs one rung of precision, and the degree ceiling fires only from the last rung.
4. **The staircase holds at every rung** (§4). `torsion_staircase`: `2^a`-torsion × `2^b`-torsion →
   `2^{a+b−m}`-torsion in `ZMod (2^m)` — annihilation (`a+b ≤ m`) and descent (`a+b > m`) as one
   Nat-subtraction statement; lifted to tops (`torsionTop_mul`) and to the degree ceiling
   (`mobiusDegLE_mul_of_torsionTop`). The `ℤ/8` cascade and the `ℤ/4` cubic-ceiling mechanism are
   the `m = 3` and `m = 2` faces of this one law.

Consequence: the cohomological picture has its ring at every precision; what it does not have is a
*grading* — the same valuation coupling (`twoAdicVal_mul`), now at the product level. -/

namespace FTQCLib.Frame.MobiusTower

open FTQCLib.Hierarchy.BooleanMobius FTQCLib.Hierarchy.DiagPhase

variable {N : ℕ} {R : Type*} [CommRing R]

/-! ## §1 — the product layer over an arbitrary commutative ring -/

/-- The **monomial character** into `R`: `monomChar A v = ∏_{i ∈ A} v_i` (each bit lifted `{0,1} ⊆ R`).
The `R`-valued indicator of `A ⊆ supp v`. -/
def monomChar (A : Finset (Fin N)) : (Fin N → ZMod 2) → R :=
  fun v => ∏ i ∈ A, ((v i).val : R)

/-- `monomChar A v = 1` iff `A ⊆ supp v`, else `0`. -/
theorem monomChar_eval (A : Finset (Fin N)) (v : Fin N → ZMod 2) :
    monomChar (R := R) A v = if A ⊆ FTQCLib.Codes.supp v then 1 else 0 := by
  unfold monomChar
  by_cases h : A ⊆ FTQCLib.Codes.supp v
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have hvi : v i = 1 := by
      have := h hi
      simpa [FTQCLib.Codes.supp, Finset.mem_filter] using this
    rw [hvi]; simp
  · rw [if_neg h]
    obtain ⟨i, hiA, hi⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hiA
    have hvi : v i = 0 := by
      have hne : v i ≠ 1 := by simpa [FTQCLib.Codes.supp, Finset.mem_filter] using hi
      have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact this _ hne
    simp [hvi]

/-- `monomChar A · monomChar B = monomChar (A ∪ B)` (boolean idempotence). -/
theorem monomChar_mul (A B : Finset (Fin N)) :
    monomChar (R := R) A * monomChar B = monomChar (A ∪ B) := by
  funext v
  simp only [Pi.mul_apply, monomChar_eval]
  by_cases hA : A ⊆ FTQCLib.Codes.supp v <;> by_cases hB : B ⊆ FTQCLib.Codes.supp v <;>
    simp [hA, hB, Finset.union_subset_iff]

/-- **Alternating powerset sum** in `R`: `∑_{U ⊆ D} (−1)^{|D|−|U|} = [D = ∅]`. -/
theorem altSum (D : Finset (Fin N)) :
    ∑ U ∈ D.powerset, ((-1 : R) ^ (D.card - U.card)) = if D = ∅ then 1 else 0 := by
  induction D using Finset.induction with
  | empty => simp
  | @insert j D hj IH =>
      have hjne : insert j D ≠ ∅ := Finset.insert_ne_empty j D
      have hdisj : Disjoint D.powerset (D.powerset.image (insert j)) :=
        Finset.disjoint_left.mpr (fun U hU hU' => by
          rw [Finset.mem_powerset] at hU
          rw [Finset.mem_image] at hU'
          obtain ⟨V, _, rfl⟩ := hU'
          exact hj (hU (Finset.mem_insert_self j V)))
      have hinj : ∀ x ∈ D.powerset, ∀ y ∈ D.powerset, insert j x = insert j y → x = y := by
        intro x hx y hy hxy
        rw [Finset.mem_powerset] at hx hy
        have hjx : j ∉ x := fun h => hj (hx h)
        have hjy : j ∉ y := fun h => hj (hy h)
        rw [← Finset.erase_insert hjx, hxy, Finset.erase_insert hjy]
      have hcard : (insert j D).card = D.card + 1 := Finset.card_insert_of_notMem hj
      rw [if_neg hjne, Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
        hcard]
      have h2 : ∀ V ∈ D.powerset,
          ((-1 : R)) ^ (D.card + 1 - (insert j V).card)
            = (-1 : R) ^ (D.card - V.card) := by
        intro V hV
        rw [Finset.mem_powerset] at hV
        have hjV : j ∉ V := fun h => hj (hV h)
        rw [Finset.card_insert_of_notMem hjV]
        congr 1
        omega
      rw [Finset.sum_congr rfl h2, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro U hU
      rw [Finset.mem_powerset] at hU
      have hle : U.card ≤ D.card := Finset.card_le_card hU
      rw [show D.card + 1 - U.card = (D.card - U.card) + 1 by omega, pow_succ]
      ring

/-- Möbius coefficients are additive in the function. -/
theorem mobiusCoeff_add (S : Finset (Fin N)) (f g : (Fin N → ZMod 2) → R) :
    mobiusCoeff S (f + g) = mobiusCoeff S f + mobiusCoeff S g := by
  simp only [mobiusCoeff_eq_alt_sum, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Möbius coefficients are linear under a constant multiple. -/
theorem mobiusCoeff_const_mul (c : R) (h : (Fin N → ZMod 2) → R) (S : Finset (Fin N)) :
    mobiusCoeff S (fun w => c * h w) = c * mobiusCoeff S h := by
  rw [mobiusCoeff_eq_alt_sum, mobiusCoeff_eq_alt_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  simp only [zsmul_eq_mul]
  ring

/-- Möbius coefficients distribute over a finite sum of functions. -/
theorem mobiusCoeff_sum {α : Type*} (s : Finset α) (h : α → (Fin N → ZMod 2) → R)
    (S : Finset (Fin N)) :
    mobiusCoeff S (∑ a ∈ s, h a) = ∑ a ∈ s, mobiusCoeff S (h a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [mobiusCoeff_eq_alt_sum]
  | insert a s ha IH =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mobiusCoeff_add, IH]

/-- **Möbius coefficient of a monomial:** `mobiusCoeff S (monomChar A) = [A = S]`. -/
theorem mobiusCoeff_monomChar (A S : Finset (Fin N)) :
    mobiusCoeff S (monomChar (R := R) A) = if A = S then 1 else 0 := by
  rw [mobiusCoeff_eq_alt_sum]
  have step : ∀ T ∈ S.powerset,
      ((-1 : ℤ) ^ (S.card - T.card)) • monomChar (R := R) A (charFn T)
        = if A ⊆ T then ((-1 : R) ^ (S.card - T.card)) else 0 := by
    intro T _
    rw [monomChar_eval, supp_charFn]
    by_cases h : A ⊆ T
    · rw [if_pos h, if_pos h, zsmul_eq_mul, mul_one]; push_cast; ring
    · rw [if_neg h, if_neg h, smul_zero]
  rw [Finset.sum_congr rfl step, ← Finset.sum_filter]
  by_cases hAS : A ⊆ S
  · have hbij : (∑ T ∈ (S.powerset).filter (A ⊆ ·), ((-1 : R) ^ (S.card - T.card)))
        = ∑ U ∈ (S \ A).powerset, ((-1 : R) ^ ((S \ A).card - U.card)) := by
      apply Finset.sum_nbij' (fun T => T \ A) (fun U => A ∪ U)
      · intro T hT
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        rw [Finset.mem_powerset]
        exact Finset.sdiff_subset_sdiff hT.1 (le_refl A)
      · intro U hU
        rw [Finset.mem_powerset] at hU
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset hAS (hU.trans Finset.sdiff_subset), Finset.subset_union_left⟩
      · intro T hT
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        rw [Finset.union_comm]
        exact Finset.sdiff_union_of_subset hT.2
      · intro U hU
        rw [Finset.mem_powerset] at hU
        have hdisj : Disjoint U A := Finset.sdiff_disjoint.mono_left hU
        rw [Finset.union_sdiff_left, hdisj.sdiff_eq_left]
      · intro T hT
        rw [Finset.mem_filter, Finset.mem_powerset] at hT
        have h1 : A.card ≤ T.card := Finset.card_le_card hT.2
        have h2 : T.card ≤ S.card := Finset.card_le_card hT.1
        rw [Finset.card_sdiff_of_subset hAS, Finset.card_sdiff_of_subset hT.2]
        congr 1
        omega
    rw [hbij, altSum]
    congr 1
    rw [eq_iff_iff, Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm hAS h, fun h => h ▸ Finset.Subset.refl S⟩
  · rw [Finset.filter_false_of_mem (fun T hT hAT =>
        hAS (hAT.trans (Finset.mem_powerset.mp hT))), Finset.sum_empty,
      if_neg (by rintro rfl; exact hAS (Finset.Subset.refl A))]

/-- **Möbius expansion** over `R`: `f = ∑_A (mobiusCoeff A f) · monomChar A`. -/
theorem mobius_expansion (f : (Fin N → ZMod 2) → R) :
    f = ∑ A : Finset (Fin N), (fun w => mobiusCoeff A f * monomChar A w) := by
  funext w
  simp only [Finset.sum_apply]
  rw [eq_sum_mobiusCoeff f w]
  rw [show (∑ A : Finset (Fin N), mobiusCoeff A f * monomChar A w)
        = ∑ A : Finset (Fin N), (if A ⊆ FTQCLib.Codes.supp w then mobiusCoeff A f else 0) from
      Finset.sum_congr rfl (fun A _ => by rw [monomChar_eval, mul_ite, mul_one, mul_zero])]
  rw [← Finset.sum_filter]
  congr 1
  ext A
  simp [Finset.mem_powerset, Finset.mem_filter]

/-- **The Möbius convolution over any commutative ring:**
`mobiusCoeff S (f·g) = Σ_{A∪B=S} (mobiusCoeff A f)·(mobiusCoeff B g)`. The product calculus exists at
every rung `ℤ/2^m` — the `ZMod 4` typing of the `CubicCeiling` version is not essential. -/
theorem mobiusCoeff_mul (f g : (Fin N → ZMod 2) → R) (S : Finset (Fin N)) :
    mobiusCoeff S (f * g)
      = ∑ A : Finset (Fin N), ∑ B : Finset (Fin N),
          (if A ∪ B = S then mobiusCoeff A f * mobiusCoeff B g else 0) := by
  conv_lhs => rw [mobius_expansion f, mobius_expansion g]
  rw [Finset.sum_mul_sum, mobiusCoeff_sum]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [mobiusCoeff_sum]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [show ((fun w => mobiusCoeff A f * monomChar A w)
            * (fun w => mobiusCoeff B g * monomChar B w))
        = (fun w => (mobiusCoeff A f * mobiusCoeff B g) * monomChar (A ∪ B) w) from ?_]
  · rw [mobiusCoeff_const_mul, mobiusCoeff_monomChar, mul_ite, mul_one, mul_zero]
  · funext w
    have hm := congrFun (monomChar_mul (R := R) A B) w
    simp only [Pi.mul_apply] at hm ⊢
    rw [← hm]; ring

/-- Möbius degree ≤ `d` over `R`: all coefficients above cardinality `d` vanish. -/
def MobiusDegLE (d : ℕ) (f : (Fin N → ZMod 2) → R) : Prop :=
  ∀ S : Finset (Fin N), d < S.card → mobiusCoeff S f = 0

/-- **Degree subadditivity at every rung:** `deg(f·g) ≤ deg f + deg g` over any commutative ring. -/
theorem mobiusDegLE_mul {d e : ℕ} {f g : (Fin N → ZMod 2) → R}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE e g) : MobiusDegLE (d + e) (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul]
  refine Finset.sum_eq_zero (fun A _ => Finset.sum_eq_zero (fun B _ => ?_))
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : d < A.card
    · rw [hf A hA, zero_mul]
    · by_cases hB : e < B.card
      · rw [hg B hB, mul_zero]
      · exfalso
        have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        omega
  · rw [if_neg h]

/-! ## §2 — the coefficient arithmetic is the saturating valuation (filtered, not graded) -/

/-- **The general ceiling mechanism:** over `ZMod (2^m)`, a coefficient product vanishes exactly when
the valuations saturate: `m ≤ v(c) + v(c') → c·c' = 0`. This is `twoAdicVal_mul` as a vanishing
criterion — the grade the product calculus carries is a *filtration* by `twoAdicVal`, not a grading. -/
theorem mul_eq_zero_of_val_saturated {m : ℕ} {c c' : ZMod (2 ^ m)}
    (h : m ≤ twoAdicVal c + twoAdicVal c') : c * c' = 0 := by
  by_contra hne
  have hlt := twoAdicVal_lt_of_ne_zero hne
  rw [twoAdicVal_mul] at hlt
  omega

/-! ## §3 — the `ℤ/8` cascade: one multiplication costs one rung -/

/-- **Sign-level products annihilate** in `ℤ/8`: `2x = 0 ∧ 2y = 0 → xy = 0` (the 2-torsion is `{0,4}`,
and `4·4 = 0`). The `ℤ/4` ceiling mechanism (`even_mul_even_zero`), one rung up. -/
theorem sign_mul_sign : ∀ x y : ZMod 8, 2 * x = 0 → 2 * y = 0 → x * y = 0 := by decide

/-- **Mid-level products descend one rung** in `ℤ/8`: `4x = 0 ∧ 4y = 0 → 2(xy) = 0` (the 4-torsion is
`{0,2,4,6}`; products land in the 2-torsion `{0,4}`). -/
theorem mid_mul_mid_descends : ∀ x y : ZMod 8, 4 * x = 0 → 4 * y = 0 → 2 * (x * y) = 0 := by decide

/-- **The descent is not a vanishing:** mid-level products can be nonzero (`2·2 = 4 ≠ 0`). This is
where the `ℤ/8` grading departs from `ℤ/4`: the first multiplication *descends*, only the second
*annihilates* — the two-stage cascade. -/
theorem mid_mul_mid_ne_zero : ∃ x y : ZMod 8, 4 * x = 0 ∧ 4 * y = 0 ∧ x * y ≠ 0 :=
  ⟨2, 2, by decide, by decide, by decide⟩

/-- Top coefficients (at exactly cardinality `d`) sit at the **sign level** (2-torsion). -/
def SignTop (d : ℕ) (f : (Fin N → ZMod 2) → ZMod 8) : Prop :=
  ∀ A : Finset (Fin N), A.card = d → 2 * mobiusCoeff A f = 0

/-- Top coefficients sit at the **mid level** (4-torsion). -/
def MidTop (d : ℕ) (f : (Fin N → ZMod 2) → ZMod 8) : Prop :=
  ∀ A : Finset (Fin N), A.card = d → 4 * mobiusCoeff A f = 0

/-- **The `ℤ/8` degree ceiling (sign-level tops):** two factors with sign-level top coefficients lose
a degree — `deg(f·g) ≤ d + e − 1`. The cubic-ceiling mechanism, one rung up the tower. -/
theorem mobiusDegLE_mul_signTop {d e : ℕ} {f g : (Fin N → ZMod 2) → ZMod 8}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE e g)
    (tf : SignTop d f) (tg : SignTop e g) :
    MobiusDegLE (d + e - 1) (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul]
  refine Finset.sum_eq_zero (fun A _ => Finset.sum_eq_zero (fun B _ => ?_))
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : d < A.card
    · rw [hf A hA, zero_mul]
    · by_cases hB : e < B.card
      · rw [hg B hB, mul_zero]
      · have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        have hAd : A.card = d := by omega
        have hBe : B.card = e := by omega
        exact sign_mul_sign _ _ (tf A hAd) (tg B hBe)
  · rw [if_neg h]

/-- **The `ℤ/8` descent law (mid-level tops):** two factors with mid-level top coefficients do *not*
lose a degree — but the product's top coefficients **descend to the sign level**:
`SignTop (d+e) (f·g)`. One multiplication costs one rung of precision; the degree ceiling fires only
from the last rung (`mobiusDegLE_mul_signTop`). "Each degree needs one more 2-adic rung", as a product
law. (The general-`m` staircase is §4's `torsionTop_mul`; this is its `m = 3` face.) -/
theorem signTop_mul_of_midTop {d e : ℕ} {f g : (Fin N → ZMod 2) → ZMod 8}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE e g)
    (tf : MidTop d f) (tg : MidTop e g) :
    SignTop (d + e) (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero (fun A _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun B _ => ?_)
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : d < A.card
    · rw [hf A hA, zero_mul, mul_zero]
    · by_cases hB : e < B.card
      · rw [hg B hB, mul_zero, mul_zero]
      · have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        have hAd : A.card = d := by omega
        have hBe : B.card = e := by omega
        exact mid_mul_mid_descends _ _ (tf A hAd) (tg B hBe)
  · rw [if_neg h, mul_zero]

/-! ## §4 — the general staircase: the full descent law at every rung `ℤ/2^m`

The `ℤ/8` cascade (§3) is the `m = 3` face of one law. Torsion levels compose under the coefficient
product by `2^a`-torsion × `2^b`-torsion → `2^{a+b−m}`-torsion (`torsion_staircase`) — Nat subtraction
makes the annihilation case (`a + b ≤ m` ⟹ exponent `0` ⟹ the product *vanishes*) and the descent
case (`a + b > m` ⟹ the product drops to a lower rung, without vanishing) one statement. Lifted to
Möbius tops: `torsionTop_mul` (the staircase for products of phases) and `mobiusDegLE_mul_of_torsionTop`
(the degree ceiling fires exactly when the torsion budget saturates). At `m = 3, a = b = 1` this is
`sign_mul_sign`/`mobiusDegLE_mul_signTop`; at `m = 3, a = b = 2` it is
`mid_mul_mid_descends`/`signTop_mul_of_midTop`. -/

/-- A saturated valuation forces zero: `m ≤ twoAdicVal c → c = 0`. -/
lemma eq_zero_of_val_ge {m : ℕ} {c : ZMod (2 ^ m)} (h : m ≤ twoAdicVal c) : c = 0 := by
  by_contra hne
  exact absurd h (by have := twoAdicVal_lt_of_ne_zero hne; omega)

/-- **The torsion staircase (every rung):** `2^a`-torsion × `2^b`-torsion → `2^{a+b−m}`-torsion in
`ZMod (2^m)`. Nat subtraction unifies the two regimes: for `a + b ≤ m` the exponent is `0` and the
product **vanishes** (annihilation — the ceiling mechanism); for `a + b > m` the product survives but
**descends** to the `2^{a+b−m}`-torsion rung. The `ℤ/8` cascade of §3 is `m = 3`. -/
theorem torsion_staircase {m : ℕ} {c c' : ZMod (2 ^ m)} {a b : ℕ}
    (hc : (2 : ZMod (2 ^ m)) ^ a * c = 0) (hc' : (2 : ZMod (2 ^ m)) ^ b * c' = 0) :
    (2 : ZMod (2 ^ m)) ^ (a + b - m) * (c * c') = 0 := by
  have h1 : min m (twoAdicVal ((2 : ZMod (2 ^ m)) ^ a) + twoAdicVal c) = m := by
    rw [← twoAdicVal_mul, hc, twoAdicVal_zero]
  have h2 : min m (twoAdicVal ((2 : ZMod (2 ^ m)) ^ b) + twoAdicVal c') = m := by
    rw [← twoAdicVal_mul, hc', twoAdicVal_zero]
  rw [twoAdicVal_pow_two] at h1 h2
  apply eq_zero_of_val_ge
  rw [twoAdicVal_mul, twoAdicVal_pow_two, twoAdicVal_mul]
  omega

/-- Cross-check: the staircase at `m = 3, a = b = 2` reproves the `ℤ/8` mid-level descent. -/
example (x y : ZMod (2 ^ 3)) (hx : (2 : ZMod (2 ^ 3)) ^ 2 * x = 0)
    (hy : (2 : ZMod (2 ^ 3)) ^ 2 * y = 0) :
    (2 : ZMod (2 ^ 3)) ^ 1 * (x * y) = 0 :=
  torsion_staircase hx hy

/-- Top coefficients (at exactly cardinality `d`) are `2^a`-torsion — the general-rung top condition
(`SignTop` is `a = 1` at `m = 3`; `MidTop` is `a = 2`). -/
def TorsionTop {m : ℕ} (a d : ℕ) (f : (Fin N → ZMod 2) → ZMod (2 ^ m)) : Prop :=
  ∀ A : Finset (Fin N), A.card = d → (2 : ZMod (2 ^ m)) ^ a * mobiusCoeff A f = 0

/-- **The staircase for phase products (every rung):** factors with `2^a`- and `2^b`-torsion top
coefficients produce a product whose top coefficients are `2^{a+b−m}`-torsion. Each multiplication
spends torsion budget; the tops descend the tower rung-by-rung. -/
theorem torsionTop_mul {m : ℕ} {d e a b : ℕ} {f g : (Fin N → ZMod 2) → ZMod (2 ^ m)}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE e g)
    (tf : TorsionTop a d f) (tg : TorsionTop b e g) :
    TorsionTop (a + b - m) (d + e) (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero (fun A _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun B _ => ?_)
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : d < A.card
    · rw [hf A hA, zero_mul, mul_zero]
    · by_cases hB : e < B.card
      · rw [hg B hB, mul_zero, mul_zero]
      · have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        have hAd : A.card = d := by omega
        have hBe : B.card = e := by omega
        exact torsion_staircase (tf A hAd) (tg B hBe)
  · rw [if_neg h, mul_zero]

/-- **The degree ceiling at every rung:** when the torsion budget saturates (`a + b ≤ m`), the tops
vanish outright and a degree is lost — `deg(f·g) ≤ d + e − 1`. `mobiusDegLE_mul_signTop` is the
`m = 3, a = b = 1` face; the `ℤ/4` cubic-ceiling mechanism is `m = 2, a = b = 1`. -/
theorem mobiusDegLE_mul_of_torsionTop {m : ℕ} {d e a b : ℕ}
    {f g : (Fin N → ZMod 2) → ZMod (2 ^ m)}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE e g)
    (tf : TorsionTop a d f) (tg : TorsionTop b e g) (hab : a + b ≤ m) :
    MobiusDegLE (d + e - 1) (f * g) := by
  intro S hS
  rcases Nat.lt_or_ge (d + e) S.card with h | h
  · exact mobiusDegLE_mul hf hg S h
  · have hSc : S.card = d + e := by omega
    have htop := torsionTop_mul hf hg tf tg S hSc
    rwa [Nat.sub_eq_zero_of_le hab, pow_zero, one_mul] at htop

end FTQCLib.Frame.MobiusTower

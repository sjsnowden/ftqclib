/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Frame.MetaplecticAction
import FTQCLib.Hierarchy.BooleanMobius

/-! # The cubic ceiling: transvection sign cochains are Möbius-degree ≤ 3

We observed computationally that every single transvection `τ_v`'s sign cochain is Möbius-degree
≤ 3. This file works toward an abstract proof. The route is the **rank-1 decomposition** of the
distortion: `τ_v = id + ω(v,·)·v` is a rank-one perturbation of the identity, so the distortion
`D_v(a,b) = betaFrame (τ_v a) (τ_v b) − betaFrame a b` decomposes into discrete directional
derivatives of `betaFrame` in the single direction `v`. This is the algebraic backbone; the degree
analysis builds on it (and on `betaFrame` being Möbius-degree ≤ 3) plus a boolean-idempotent
cancellation isolated as a named `Prop`. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Gates FTQCLib.Hierarchy.BooleanMobius

variable {n : ℕ}

/-! ## The degree notion and the per-qubit cubic core -/

/-- A map `(Fin N → ZMod 2) → ZMod 4` has **Möbius-degree ≤ d** if every Möbius (ANF) coefficient
above degree `d` vanishes — equivalently, its multilinear form has no monomial of degree `> d`. -/
def MobiusDegLE {N : ℕ} (d : ℕ) (f : (Fin N → ZMod 2) → ZMod 4) : Prop :=
  ∀ S : Finset (Fin N), d < S.card → mobiusCoeff S f = 0

/-- The **per-qubit core of `betaFrame`**: the `betaFrame_sum` summand at one qubit, as a function
of its four bits `w` (`w 0 = p.X`, `w 1 = p.Z`, `w 2 = q.X`, `w 3 = q.Z`). -/
def betaCore (w : Fin 4 → ZMod 2) : ZMod 4 :=
  (((w 1).val * (w 0).val + (w 3).val * (w 2).val + (w 1 + w 3).val * (w 0 + w 2).val
    + 2 * ((w 3).val * (w 0).val + (w 1 + w 3).val * (w 0 + w 2).val) : ℕ) : ZMod 4)

/-- **The per-qubit core is Möbius-degree ≤ 3** — the cubic source of `betaFrame`'s degree. The lone
`ℤ/4` carry that could give a degree-4 monomial (`p.X·p.Z·q.X·q.Z`) vanishes (`2·2 = 0`). Proved by
evaluating the top Möbius coefficient (`S = univ` on `Fin 4`) as a `16`-term alternating sum. -/
theorem betaCore_mobiusDegLE_three : MobiusDegLE 3 betaCore := by
  intro S hS
  have h4 : S.card = 4 := by
    have := Finset.card_le_univ S
    simp only [Fintype.card_fin] at this
    omega
  have hS4 : S = Finset.univ :=
    Finset.eq_univ_of_card S (by rw [h4, Fintype.card_fin])
  subst hS4
  rw [mobiusCoeff_eq_alt_sum]
  decide

/-! ## `MobiusDegLE` closure: additivity and support localization -/

variable {N : ℕ}

/-- Möbius coefficients are additive in the function (immediate from the alternating-sum form). -/
theorem mobiusCoeff_add (S : Finset (Fin N)) (f g : (Fin N → ZMod 2) → ZMod 4) :
    mobiusCoeff S (f + g) = mobiusCoeff S f + mobiusCoeff S g := by
  simp only [mobiusCoeff_eq_alt_sum, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- `MobiusDegLE` is closed under addition. -/
theorem MobiusDegLE.add {d : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE d g) : MobiusDegLE d (f + g) :=
  fun S hS => by rw [mobiusCoeff_add, hf S hS, hg S hS, add_zero]

/-- A function independent of coordinate `j` (flipping the `j`-th bit does not change it). -/
def IndepOf (j : Fin N) (h : (Fin N → ZMod 2) → ZMod 4) : Prop :=
  ∀ v, h (v + Pi.single j 1) = h v

/-- An `IndepOf j` function has vanishing `j`-th discrete derivative. -/
theorem funcDerivG_eq_zero_of_indep {j : Fin N} {h : (Fin N → ZMod 2) → ZMod 4} (hj : IndepOf j h) :
    funcDerivG j h = 0 := by
  funext v; rw [funcDerivG_apply, hj v, sub_self]; rfl

/-- `IndepOf j` is preserved by a discrete derivative in a different direction. -/
theorem IndepOf.deriv {j k : Fin N} {h : (Fin N → ZMod 2) → ZMod 4}
    (hj : IndepOf j h) : IndepOf j (funcDerivG k h) := by
  intro v
  simp only [funcDerivG_apply]
  rw [add_right_comm v (Pi.single j 1) (Pi.single k 1), hj (v + Pi.single k 1), hj v]

/-- `IndepOf j` is preserved by `funcDerivSubset S` as long as `j ∉ S`. -/
theorem IndepOf.funcDerivSubset {j : Fin N} {h : (Fin N → ZMod 2) → ZMod 4} :
    ∀ {S : Finset (Fin N)}, j ∉ S → IndepOf j h → IndepOf j (funcDerivSubset S h) := by
  intro S
  induction S using Finset.induction with
  | empty => intro _ hj; rwa [funcDerivSubset_empty]
  | insert i S hi IH =>
      intro hjS hj
      rw [funcDerivSubset_insert hi]
      exact (IH (fun a => hjS (Finset.mem_insert_of_mem a)) hj).deriv

/-- **Support localization.** If `h` is independent of coordinate `j` and `j ∈ S`, the Möbius
coefficient at `S` vanishes — Möbius support lies in subsets of the coordinates `h` uses. -/
theorem mobiusCoeff_eq_zero_of_indep {j : Fin N} {S : Finset (Fin N)}
    {h : (Fin N → ZMod 2) → ZMod 4} (hjS : j ∈ S) (hj : IndepOf j h) : mobiusCoeff S h = 0 := by
  have hje : j ∉ S.erase j := by simp
  rw [mobiusCoeff_apply, ← Finset.insert_erase hjS, funcDerivSubset_insert hje,
    funcDerivG_eq_zero_of_indep (hj.funcDerivSubset hje)]
  rfl

/-! ## Coordinate-injection reindex: the cubic core stays cubic when embedded -/

/-- Flipping the `ι k`-th bit then restricting along an injection `ι` equals restricting then
flipping the `k`-th bit. -/
theorem comp_add_single {ι : Fin 4 → Fin N} (hι : Function.Injective ι) (k : Fin 4)
    (w : Fin N → ZMod 2) :
    (w + Pi.single (ι k) (1 : ZMod 2)) ∘ ι = (w ∘ ι) + Pi.single k (1 : ZMod 2) := by
  funext k'
  simp only [Function.comp_apply, Pi.add_apply, Pi.single_apply, hι.eq_iff]

/-- **Single-derivative reindex:** `∂_{ι k}` of `w ↦ g(w∘ι)` is `∂_k g` of `w∘ι`. -/
theorem funcDerivG_reindex {ι : Fin 4 → Fin N} (hι : Function.Injective ι) (k : Fin 4)
    (g : (Fin 4 → ZMod 2) → ZMod 4) :
    funcDerivG (ι k) (fun w => g (w ∘ ι)) = fun w => funcDerivG k g (w ∘ ι) := by
  funext w
  simp only [funcDerivG_apply, comp_add_single hι k w]

/-- **Iterated reindex:** `funcDerivSubset (ι '' T)` of `w ↦ g(w∘ι)` is `funcDerivSubset T g` of
`w∘ι`. -/
theorem funcDerivSubset_reindex {ι : Fin 4 → Fin N} (hι : Function.Injective ι)
    (g : (Fin 4 → ZMod 2) → ZMod 4) :
    ∀ T : Finset (Fin 4), funcDerivSubset (Finset.image ι T) (fun w => g (w ∘ ι))
      = fun w => funcDerivSubset T g (w ∘ ι) := by
  intro T
  induction T using Finset.induction with
  | empty => simp [funcDerivSubset_empty]
  | insert k T hk IH =>
      have hkι : ι k ∉ Finset.image ι T := by
        simp only [Finset.mem_image, not_exists, not_and]
        exact fun x hx he => hk (hι he ▸ hx)
      rw [Finset.image_insert, funcDerivSubset_insert hkι, IH, funcDerivSubset_insert hk,
        funcDerivG_reindex hι]

/-- **Möbius-coefficient reindex** at the full image:
`mobiusCoeff (ι '' univ) (g∘(·∘ι)) = mobiusCoeff univ g`. -/
theorem mobiusCoeff_reindex {ι : Fin 4 → Fin N} (hι : Function.Injective ι)
    (g : (Fin 4 → ZMod 2) → ZMod 4) :
    mobiusCoeff (Finset.image ι Finset.univ) (fun w => g (w ∘ ι)) = mobiusCoeff Finset.univ g := by
  rw [mobiusCoeff_apply, mobiusCoeff_apply, funcDerivSubset_reindex hι g Finset.univ]
  rfl

/-- **The cubic core stays Möbius-degree ≤ 3 when embedded along an injection** `ι : Fin 4 ↪ Fin N`.
Off-image coordinates drop out (support localization); the on-image top coefficient reindexes to
`betaCore`'s, which is zero. -/
theorem betaCore_comp_mobiusDegLE_three {ι : Fin 4 → Fin N} (hι : Function.Injective ι) :
    MobiusDegLE 3 (fun w => betaCore (w ∘ ι)) := by
  intro S hS
  by_cases hsub : S ⊆ Finset.image ι Finset.univ
  · have hcard : (Finset.image ι Finset.univ).card = 4 := by
      rw [Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
    have hSeq : S = Finset.image ι Finset.univ :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; omega)
    subst hSeq
    rw [mobiusCoeff_reindex hι betaCore]
    exact betaCore_mobiusDegLE_three Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  · obtain ⟨j, hjS, hjι⟩ := Finset.not_subset.mp hsub
    refine mobiusCoeff_eq_zero_of_indep hjS (fun w => ?_)
    have hne : ∀ k, ι k ≠ j := fun k he => hjι (he ▸ Finset.mem_image_of_mem ι (Finset.mem_univ k))
    congr 1
    funext k
    simp [Function.comp_apply, Pi.add_apply, hne k]

/-! ## Assembly: `betaFrame` itself is Möbius-degree ≤ 3 -/

/-- `MobiusDegLE d` is closed under finite sums. -/
theorem MobiusDegLE.sum {α : Type*} {d : ℕ} (s : Finset α)
    (f : α → (Fin N → ZMod 2) → ZMod 4) (hf : ∀ i ∈ s, MobiusDegLE d (f i)) :
    MobiusDegLE d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => intro S _; simp [mobiusCoeff_eq_alt_sum]
  | insert i s hi IH =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (IH fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The four bit-slots of qubit `i` inside the `4n`-bit register `Fin (n*4)`. -/
def qubitInj (i : Fin n) : Fin 4 → Fin (n * 4) := fun j => finProdFinEquiv (i, j)

theorem qubitInj_injective (i : Fin n) : Function.Injective (qubitInj i) := fun a b hab =>
  (Prod.ext_iff.mp (finProdFinEquiv.injective hab)).2

/-- Decode the first Pauli of the pair from the bit register. -/
def decodeP (w : Fin (n * 4) → ZMod 2) : Pauli n :=
  ⟨fun k => w (qubitInj k 0), fun k => w (qubitInj k 1)⟩

/-- Decode the second Pauli of the pair from the bit register. -/
def decodeQ (w : Fin (n * 4) → ZMod 2) : Pauli n :=
  ⟨fun k => w (qubitInj k 2), fun k => w (qubitInj k 3)⟩

/-- `betaFrame` encoded as a function of the `4n` Pauli-pair bits. -/
def betaFrameBits (w : Fin (n * 4) → ZMod 2) : ZMod 4 := betaFrame (decodeP w) (decodeQ w)

/-- The encoded `betaFrame` is the per-qubit sum of cores (via `betaFrame_sum`). -/
theorem betaFrameBits_eq_sum (w : Fin (n * 4) → ZMod 2) :
    betaFrameBits w = ∑ i, betaCore (w ∘ qubitInj i) := by
  rw [betaFrameBits, betaFrame_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [betaCore, decodeP, decodeQ, Function.comp_apply, X_add, Z_add, Pi.add_apply]
  push_cast
  ring

/-- **`betaFrame` is Möbius-degree ≤ 3.** The Pauli-product cocycle — the source of all frame sign
data — is cubic. The `betaFrame_sum` separation makes it a sum of per-qubit cores, each cubic
(`betaCore_comp_mobiusDegLE_three`), and `MobiusDegLE` is closed under sums. -/
theorem betaFrame_mobiusDegLE_three : MobiusDegLE 3 (betaFrameBits (n := n)) := by
  have hsum : betaFrameBits = ∑ i, fun w : Fin (n * 4) → ZMod 2 => betaCore (w ∘ qubitInj i) := by
    funext w; rw [betaFrameBits_eq_sum, Finset.sum_apply]
  rw [hsum]
  exact MobiusDegLE.sum Finset.univ _
    (fun i _ => betaCore_comp_mobiusDegLE_three (qubitInj_injective i))

/-- Every `ZMod 2` element is `0` or `1`. -/
private theorem zmod2_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- **The rank-1 decomposition of the transvection distortion.** Since `τ_v a = a + ω(v,a)·v`, the
distortion is the discrete inclusion–exclusion of `betaFrame` along the single direction `v`, with
the linear "amounts" `s = ω(v,a)`, `t = ω(v,b)`:

`D_v(a,b) = s·∂¹ᵥβ + t·∂²ᵥβ + s·t·∂¹ᵥ∂²ᵥβ`,

where `∂¹ᵥβ = β(a+v,b) − β(a,b)`, `∂²ᵥβ = β(a,b+v) − β(a,b)`, and `∂¹ᵥ∂²ᵥβ` is the mixed second
difference. Proved by the four cases `s,t ∈ {0,1}`. -/
theorem frameDistortion_rankOne (v a b : Pauli n) :
    frameDistortion (transvectionEquiv v) a b
      = ((omega v a).val : ZMod 4) * (betaFrame (a + v) b - betaFrame a b)
        + ((omega v b).val : ZMod 4) * (betaFrame a (b + v) - betaFrame a b)
        + ((omega v a).val * (omega v b).val : ZMod 4)
          * (betaFrame (a + v) (b + v) - betaFrame (a + v) b
              - betaFrame a (b + v) + betaFrame a b) := by
  unfold frameDistortion
  rw [transvectionEquiv_apply, transvectionEquiv_apply]
  rcases zmod2_zero_or_one (omega v a) with ha | ha <;>
    rcases zmod2_zero_or_one (omega v b) with hb | hb <;>
      (rw [ha, hb]; simp <;> ring)

/-! ## The full transvection ceiling, modulo the rank-1 product crux -/

/-- The transvection distortion `D_v`, encoded on the bit register. -/
def distortionBits (v : Pauli n) (w : Fin (n * 4) → ZMod 2) : ZMod 4 :=
  frameDistortion (transvectionEquiv v) (decodeP w) (decodeQ w)

/-- First rank-1 term `s·∂¹ᵥβ`, encoded. -/
def rankOneTerm1 (v : Pauli n) (w : Fin (n * 4) → ZMod 2) : ZMod 4 :=
  ((omega v (decodeP w)).val : ZMod 4)
    * (betaFrame (decodeP w + v) (decodeQ w) - betaFrame (decodeP w) (decodeQ w))

/-- Second rank-1 term `t·∂²ᵥβ`, encoded. -/
def rankOneTerm2 (v : Pauli n) (w : Fin (n * 4) → ZMod 2) : ZMod 4 :=
  ((omega v (decodeQ w)).val : ZMod 4)
    * (betaFrame (decodeP w) (decodeQ w + v) - betaFrame (decodeP w) (decodeQ w))

/-- Third rank-1 term `s·t·∂¹ᵥ∂²ᵥβ`, encoded. -/
def rankOneTerm3 (v : Pauli n) (w : Fin (n * 4) → ZMod 2) : ZMod 4 :=
  ((omega v (decodeP w)).val * (omega v (decodeQ w)).val : ZMod 4)
    * (betaFrame (decodeP w + v) (decodeQ w + v) - betaFrame (decodeP w + v) (decodeQ w)
        - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w))

/-- The encoded distortion is the sum of the three rank-1 terms (`frameDistortion_rankOne`). -/
theorem distortionBits_rankOne (v : Pauli n) :
    distortionBits v = rankOneTerm1 v + rankOneTerm2 v + rankOneTerm3 v := by
  funext w
  simp only [distortionBits, rankOneTerm1, rankOneTerm2, rankOneTerm3, Pi.add_apply]
  exact frameDistortion_rankOne v (decodeP w) (decodeQ w)

/-- **The crux.** The three rank-1 terms are Möbius-degree ≤ 3.

**Proof (cracked, computationally verified `w=1..4`; formalization below).** Each term is a product
`ω(v,·) · (directional derivative of β)`. Both factors are Möbius-degree ≤ 2 with **even** degree-2
parts:
* `ω(v,a).val = Σ(its bits) − 2·Σ(pairs)` — the parity ANF over `ZMod 4` (the `|S|≥3` Möbius terms
  have coefficient `≡ 0 mod 4`), leaving degree 2 with degree-2 coefficient `−2` (even);
* `∂ᵥβ` is degree ≤ 2 with all degree-2 coefficients even (`= 2`): via `betaFrame_sum` it is a sum
  of per-qubit directional differences of the cubic cores, each with an even quadratic part.

The product of two degree-≤2 functions with even degree-2 parts is degree ≤ 3: the only degree-4
contribution to the product is `(deg-2 part)·(deg-2 part) = (2a)·(2b) = 4ab ≡ 0 (mod 4)`. So no
degree-4 monomial survives. (The key formal ingredient is the Möbius product-convolution
`mobiusCoeff S (f·g) = Σ_{A∪B=S} mobiusCoeff A f · mobiusCoeff B g`, proved below as
`mobiusCoeff_mul`; Mathlib does not provide it.) -/
def RankOneCubic (v : Pauli n) : Prop :=
  MobiusDegLE 3 (rankOneTerm1 v) ∧ MobiusDegLE 3 (rankOneTerm2 v) ∧ MobiusDegLE 3 (rankOneTerm3 v)

/-- **The full transvection ceiling, conditional on the rank-1 crux.** Every transvection's
distortion `D_v` is Möbius-degree ≤ 3, given the rank-1 product bound. The reduction is the rank-1
decomposition plus `MobiusDegLE` additivity; `#print axioms` stays clean (the crux is a `Prop`
hypothesis, not an axiom), so this isolates the remaining content into `RankOneCubic`. -/
theorem transvection_distortion_mobiusDegLE_three (v : Pauli n) (h : RankOneCubic v) :
    MobiusDegLE 3 (distortionBits v) := by
  rw [distortionBits_rankOne]
  exact (h.1.add h.2.1).add h.2.2

/-- Even degree-2: every degree-2 Möbius coefficient is even (`{0,2} ⊆ ZMod 4`). -/
def EvenDeg2 (f : (Fin N → ZMod 2) → ZMod 4) : Prop :=
  ∀ S : Finset (Fin N), S.card = 2 → 2 * mobiusCoeff S f = 0

/-- The squarefree monomial `∏_{i∈A} (v i).val` as a `ZMod 4`-valued function. -/
def monomChar (A : Finset (Fin N)) : (Fin N → ZMod 2) → ZMod 4 :=
  fun v => ∏ i ∈ A, ((v i).val : ZMod 4)

/-- `monomChar A v = 1` iff every coordinate of `A` is in the support of `v`, else `0`. -/
theorem monomChar_eval (A : Finset (Fin N)) (v : Fin N → ZMod 2) :
    monomChar A v = if A ⊆ FTQCLib.Codes.supp v then 1 else 0 := by
  unfold monomChar
  by_cases h : A ⊆ FTQCLib.Codes.supp v
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have hvi : v i = 1 := by
      have := h hi
      simpa [FTQCLib.Codes.supp, Finset.mem_filter] using this
    rw [hvi]; rfl
  · rw [if_neg h]
    obtain ⟨i, hiA, hi⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hiA
    have hvi : v i = 0 := by
      have hne : v i ≠ 1 := by simpa [FTQCLib.Codes.supp, Finset.mem_filter] using hi
      have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact this _ hne
    simp [hvi]

/-- `monomChar A · monomChar B = monomChar (A ∪ B)` (boolean idempotence, via the eval form). -/
theorem monomChar_mul (A B : Finset (Fin N)) :
    monomChar A * monomChar B = monomChar (A ∪ B) := by
  funext v
  simp only [Pi.mul_apply, monomChar_eval]
  by_cases hA : A ⊆ FTQCLib.Codes.supp v <;> by_cases hB : B ⊆ FTQCLib.Codes.supp v <;>
    simp [hA, hB, Finset.union_subset_iff]

/-- **Alternating powerset sum** in `ZMod 4`: `∑_{U ⊆ D} (-1)^{|D|-|U|} = [D = ∅]`. -/
theorem altSum (D : Finset (Fin N)) :
    ∑ U ∈ D.powerset, ((-1 : ZMod 4) ^ (D.card - U.card)) = if D = ∅ then 1 else 0 := by
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
      -- second sum: rewrite `(insert j V).card = V.card + 1`
      have h2 : ∀ V ∈ D.powerset,
          ((-1 : ZMod 4)) ^ (D.card + 1 - (insert j V).card)
            = (-1 : ZMod 4) ^ (D.card - V.card) := by
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

/-- **Möbius coefficient of a monomial:** `mobiusCoeff S (monomChar A) = [A = S]`. -/
theorem mobiusCoeff_monomChar (A S : Finset (Fin N)) :
    mobiusCoeff S (monomChar A) = if A = S then 1 else 0 := by
  rw [mobiusCoeff_eq_alt_sum]
  have step : ∀ T ∈ S.powerset,
      ((-1 : ℤ) ^ (S.card - T.card)) • monomChar A (charFn T)
        = if A ⊆ T then ((-1 : ZMod 4) ^ (S.card - T.card)) else 0 := by
    intro T _
    rw [monomChar_eval, supp_charFn]
    by_cases h : A ⊆ T
    · rw [if_pos h, if_pos h, zsmul_eq_mul, mul_one]; push_cast; ring
    · rw [if_neg h, if_neg h, smul_zero]
  rw [Finset.sum_congr rfl step, ← Finset.sum_filter]
  by_cases hAS : A ⊆ S
  · have hbij : (∑ T ∈ (S.powerset).filter (A ⊆ ·), ((-1 : ZMod 4) ^ (S.card - T.card)))
        = ∑ U ∈ (S \ A).powerset, ((-1 : ZMod 4) ^ ((S \ A).card - U.card)) := by
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

/-- Möbius coefficient is linear under multiplication by a constant. -/
theorem mobiusCoeff_const_mul (c : ZMod 4) (h : (Fin N → ZMod 2) → ZMod 4)
    (S : Finset (Fin N)) :
    mobiusCoeff S (fun w => c * h w) = c * mobiusCoeff S h := by
  rw [mobiusCoeff_eq_alt_sum, mobiusCoeff_eq_alt_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  simp only [zsmul_eq_mul]
  ring

/-- Möbius coefficient distributes over a finite sum of functions. -/
theorem mobiusCoeff_sum {α : Type*} (s : Finset α) (h : α → (Fin N → ZMod 2) → ZMod 4)
    (S : Finset (Fin N)) :
    mobiusCoeff S (∑ a ∈ s, h a) = ∑ a ∈ s, mobiusCoeff S (h a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [mobiusCoeff_eq_alt_sum]
  | insert a s ha IH =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mobiusCoeff_add, IH]

/-- **Möbius expansion:** `f = ∑_A (mobiusCoeff A f) · monomChar A`. -/
theorem mobius_expansion (f : (Fin N → ZMod 2) → ZMod 4) :
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

/-- **The Möbius convolution:**
`mobiusCoeff S (f·g) = Σ_{A∪B=S} (mobiusCoeff A f)·(mobiusCoeff B g)`. -/
theorem mobiusCoeff_mul (f g : (Fin N → ZMod 2) → ZMod 4) (S : Finset (Fin N)) :
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
    have hm := congrFun (monomChar_mul A B) w
    simp only [Pi.mul_apply] at hm ⊢
    rw [← hm]; ring

/-- **Product degree ≤ sum of degrees.** -/
theorem mobiusDegLE_mul {a b : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4}
    (hf : MobiusDegLE a f) (hg : MobiusDegLE b g) : MobiusDegLE (a + b) (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul]
  refine Finset.sum_eq_zero (fun A _ => Finset.sum_eq_zero (fun B _ => ?_))
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : a < A.card
    · rw [hf A hA, zero_mul]
    · by_cases hB : b < B.card
      · rw [hg B hB, mul_zero]
      · exfalso
        have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        omega
  · rw [if_neg h]

/-- A handy `ZMod 4` fact: `2x = 0` and `2y = 0` force `xy = 0`. -/
private theorem even_mul_even_zero : ∀ x y : ZMod 4, 2 * x = 0 → 2 * y = 0 → x * y = 0 := by decide

/-- **The two-factor even product lemma:** degree-≤2 with even degree-2 part, twice, gives ≤3. -/
theorem mobiusDegLE_mul_evenEven {f g : (Fin N → ZMod 2) → ZMod 4}
    (hf : MobiusDegLE 2 f) (hg : MobiusDegLE 2 g) (ef : EvenDeg2 f) (eg : EvenDeg2 g) :
    MobiusDegLE 3 (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul]
  refine Finset.sum_eq_zero (fun A _ => Finset.sum_eq_zero (fun B _ => ?_))
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : 2 < A.card
    · rw [hf A hA, zero_mul]
    · by_cases hB : 2 < B.card
      · rw [hg B hB, mul_zero]
      · have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        have hA2 : A.card = 2 := by omega
        have hB2 : B.card = 2 := by omega
        exact even_mul_even_zero _ _ (ef A hA2) (eg B hB2)
  · rw [if_neg h]

/-- **Special product lemma:** (≤2, even deg-2) × (≤1, all even) ⟹ degree ≤2. -/
theorem mobiusDegLE_mul_special {f g : (Fin N → ZMod 2) → ZMod 4}
    (hf : MobiusDegLE 2 f) (ef : EvenDeg2 f)
    (hg : MobiusDegLE 1 g) (eg : ∀ B : Finset (Fin N), 2 * mobiusCoeff B g = 0) :
    MobiusDegLE 2 (f * g) := by
  intro S hS
  rw [mobiusCoeff_mul]
  refine Finset.sum_eq_zero (fun A _ => Finset.sum_eq_zero (fun B _ => ?_))
  by_cases h : A ∪ B = S
  · rw [if_pos h]
    by_cases hA : 2 < A.card
    · rw [hf A hA, zero_mul]
    · by_cases hB : 1 < B.card
      · rw [hg B hB, mul_zero]
      · have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le A B
        have hA2 : A.card = 2 := by omega
        exact even_mul_even_zero _ _ (ef A hA2) (eg B)
  · rw [if_neg h]

/-- If every coefficient of `g` is even, so is every coefficient of `f·g`. -/
theorem even_of_mul_even {f g : (Fin N → ZMod 2) → ZMod 4}
    (hg : ∀ B : Finset (Fin N), 2 * mobiusCoeff B g = 0) (S : Finset (Fin N)) :
    2 * mobiusCoeff S (f * g) = 0 := by
  rw [mobiusCoeff_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero (fun A _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun B _ => ?_)
  by_cases h : A ∪ B = S
  · rw [if_pos h, show 2 * (mobiusCoeff A f * mobiusCoeff B g)
        = mobiusCoeff A f * (2 * mobiusCoeff B g) by ring, hg B, mul_zero]
  · rw [if_neg h, mul_zero]

/-! ## The parity factor `ω(v,·).val` is degree ≤2 with even degree-2 part -/

/-- Möbius coefficients are subtractive in the function. -/
theorem mobiusCoeff_sub (S : Finset (Fin N)) (f g : (Fin N → ZMod 2) → ZMod 4) :
    mobiusCoeff S (f - g) = mobiusCoeff S f - mobiusCoeff S g := by
  simp only [mobiusCoeff_eq_alt_sum, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- `MobiusDegLE` is closed under subtraction. -/
theorem MobiusDegLE.sub {d : ℕ} {f g : (Fin N → ZMod 2) → ZMod 4}
    (hf : MobiusDegLE d f) (hg : MobiusDegLE d g) : MobiusDegLE d (f - g) :=
  fun S hS => by rw [mobiusCoeff_sub, hf S hS, hg S hS, sub_zero]

/-- A singleton monomial has Möbius-degree ≤ 2 (it has degree 1). -/
theorem monomChar_singleton_degLE2 (j : Fin N) : MobiusDegLE 2 (monomChar {j}) := by
  intro S hS
  rw [mobiusCoeff_monomChar]
  apply if_neg
  intro h
  rw [← h, Finset.card_singleton] at hS
  omega

/-- The product `2 · monomChar {j} · P` is degree ≤2 when `P` is degree-≤2 with even degree-2. -/
theorem two_mul_monomChar_singleton_even (j : Fin N) (P : (Fin N → ZMod 2) → ZMod 4)
    (hP2 : MobiusDegLE 2 P) (hPe : EvenDeg2 P) :
    MobiusDegLE 2 (fun w => 2 * (monomChar {j} w * P w)) := by
  intro S hS
  rw [show (fun w => 2 * (monomChar {j} w * P w)) = (fun w => 2 * (monomChar {j} * P) w) from rfl,
    mobiusCoeff_const_mul, mobiusCoeff_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero (fun A _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun B _ => ?_)
  by_cases h : A ∪ B = S
  · rw [if_pos h, mobiusCoeff_monomChar]
    by_cases hAj : {j} = A
    · rw [if_pos hAj, one_mul]
      by_cases hB2 : 2 < B.card
      · rw [hP2 B hB2, mul_zero]
      · have hcard : S.card ≤ A.card + B.card := h ▸ Finset.card_union_le _ _
        have hA1 : A.card = 1 := by rw [← hAj]; exact Finset.card_singleton j
        have hB2' : B.card = 2 := by omega
        exact hPe B hB2'
    · rw [if_neg hAj, zero_mul, mul_zero]
  · rw [if_neg h, mul_zero]

/-- The XOR formula on `.val` over `ZMod 2`, cast into `ZMod 4`. -/
private theorem val_add_zmod2 : ∀ a b : ZMod 2,
    ((a + b).val : ZMod 4)
      = (a.val : ZMod 4) + (b.val : ZMod 4) - 2 * ((a.val : ZMod 4) * (b.val : ZMod 4)) := by
  decide

/-- Parity of a set of coordinates: `(∑_{j∈J} w_j).val`. -/
def parityOfSet (J : Finset (Fin N)) : (Fin N → ZMod 2) → ZMod 4 :=
  fun w => ((∑ j ∈ J, w j).val : ZMod 4)

theorem parityOfSet_empty : parityOfSet (∅ : Finset (Fin N)) = fun _ => 0 := by
  funext w; simp [parityOfSet]

/-- The XOR recursion for `parityOfSet` (in `Pi` form). -/
theorem parityOfSet_insert {j : Fin N} {J : Finset (Fin N)} (hj : j ∉ J) :
    parityOfSet (insert j J)
      = monomChar {j} + parityOfSet J
        - (fun w => 2 * (monomChar {j} w * parityOfSet J w)) := by
  funext w
  simp only [parityOfSet, Finset.sum_insert hj, Pi.sub_apply, Pi.add_apply]
  rw [val_add_zmod2]
  congr 1
  · congr 1
    rw [monomChar]; simp
  · rw [monomChar]; simp

/-- **The parity factor is Möbius-degree ≤2 with even degree-2 part.** -/
theorem parityOfSet_facts (J : Finset (Fin N)) :
    MobiusDegLE 2 (parityOfSet J) ∧ EvenDeg2 (parityOfSet J) := by
  induction J using Finset.induction with
  | empty =>
      rw [parityOfSet_empty]
      refine ⟨fun S _ => ?_, fun S _ => ?_⟩ <;>
        simp [mobiusCoeff_eq_alt_sum]
  | insert j J hj IH =>
      obtain ⟨IH2, IHe⟩ := IH
      rw [parityOfSet_insert hj]
      refine ⟨(MobiusDegLE.add (monomChar_singleton_degLE2 j) IH2).sub
          (two_mul_monomChar_singleton_even j (parityOfSet J) IH2 IHe), ?_⟩
      intro S hS
      rw [mobiusCoeff_sub, mobiusCoeff_add]
      have h1 : mobiusCoeff S (monomChar {j}) = 0 := by
        rw [mobiusCoeff_monomChar]; apply if_neg; intro h
        rw [← h, Finset.card_singleton] at hS; omega
      have h3 : (2 : ZMod 4)
          * mobiusCoeff S (fun w => 2 * (monomChar {j} w * parityOfSet J w)) = 0 := by
        rw [show (fun w => 2 * (monomChar {j} w * parityOfSet J w))
              = (fun w => 2 * (monomChar {j} * parityOfSet J) w) from rfl,
          mobiusCoeff_const_mul, ← mul_assoc, show (2 : ZMod 4) * 2 = 0 from by decide, zero_mul]
      rw [h1, zero_add, mul_sub, IHe S hS, zero_sub, h3, neg_zero]

/-- `fun i => qubitInj i s` is injective. -/
theorem qubitInj_slot_injective {n : ℕ} (s : Fin 4) :
    Function.Injective (fun i : Fin n => qubitInj i s) :=
  fun a b h => (Prod.ext_iff.mp (finProdFinEquiv.injective h)).1

/-- A `ZMod 2`-coefficient sum equals the indicator sum over the selected coordinates. -/
theorem sum_coeff_eq_image {n : ℕ} (c : Fin n → ZMod 2) (m : Fin n → Fin (n * 4))
    (hm : Function.Injective m) (w : Fin (n * 4) → ZMod 2) :
    ∑ i, c i * w (m i)
      = ∑ j ∈ (Finset.univ.filter (fun i => c i = 1)).image m, w j := by
  rw [Finset.sum_image (fun x _ y _ h => hm h), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hc : c i = 1
  · rw [if_pos hc, hc, one_mul]
  · have hc0 : c i = 0 := by
      have : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact this _ hc
    rw [if_neg hc, hc0, zero_mul]

/-- `ω(v, ·)` applied to a decoded Pauli is a parity over the selected coordinates. -/
theorem omega_decode_parity {n : ℕ} (v : Pauli n) (a b : Fin 4) (hab : a ≠ b) :
    (fun w => (((∑ i, v.Z i * w (qubitInj i a)) + (∑ i, v.X i * w (qubitInj i b))).val : ZMod 4))
      = parityOfSet ((Finset.univ.filter (fun i => v.Z i = 1)).image (fun i => qubitInj i a)
          ∪ (Finset.univ.filter (fun i => v.X i = 1)).image (fun i => qubitInj i b)) := by
  funext w
  simp only [parityOfSet]
  congr 1
  have hdisj : Disjoint ((Finset.univ.filter (fun i => v.Z i = 1)).image (fun i => qubitInj i a))
      ((Finset.univ.filter (fun i => v.X i = 1)).image (fun i => qubitInj i b)) := by
    rw [Finset.disjoint_left]
    rintro x hxa hxb
    rw [Finset.mem_image] at hxa hxb
    obtain ⟨i, _, rfl⟩ := hxa
    obtain ⟨i', _, hi'⟩ := hxb
    exact hab ((Prod.ext_iff.mp (finProdFinEquiv.injective hi')).2).symm
  rw [Finset.sum_union hdisj,
    ← sum_coeff_eq_image v.Z (fun i => qubitInj i a) (qubitInj_slot_injective a),
    ← sum_coeff_eq_image v.X (fun i => qubitInj i b) (qubitInj_slot_injective b)]

/-! ## `∂ᵥβ` and the cross-difference, via per-qubit core differences -/

/-- **Möbius coefficient reindex at any `T`** (generalizes the `univ` version). -/
theorem mobiusCoeff_reindex_general {n : ℕ} {ι : Fin 4 → Fin (n * 4)} (hι : Function.Injective ι)
    (h : (Fin 4 → ZMod 2) → ZMod 4) (T : Finset (Fin 4)) :
    mobiusCoeff (Finset.image ι T) (fun w => h (w ∘ ι)) = mobiusCoeff T h := by
  rw [mobiusCoeff_apply, mobiusCoeff_apply, funcDerivSubset_reindex hι h T]
  rfl

/-- The preimage finset realizing `S ⊆ image ι univ`. -/
private theorem image_preimage_filter {n : ℕ} {ι : Fin 4 → Fin (n * 4)} (hι : Function.Injective ι)
    {S : Finset (Fin (n * 4))} (hsub : S ⊆ Finset.image ι Finset.univ) :
    Finset.image ι (Finset.univ.filter (fun k => ι k ∈ S)) = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro hx
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hsub hx)
    exact ⟨k, hk ▸ hx, hk⟩

/-- **Degree is preserved under coordinate injection.** -/
theorem mobiusDegLE_comp_inj {n : ℕ} {ι : Fin 4 → Fin (n * 4)} (hι : Function.Injective ι) {d : ℕ}
    {h : (Fin 4 → ZMod 2) → ZMod 4} (hh : MobiusDegLE d h) :
    MobiusDegLE d (fun w => h (w ∘ ι)) := by
  intro S hS
  by_cases hsub : S ⊆ Finset.image ι Finset.univ
  · have hT' := image_preimage_filter hι hsub
    rw [← hT', mobiusCoeff_reindex_general hι h]
    apply hh
    rw [show (Finset.univ.filter (fun k => ι k ∈ S)).card = S.card from by
      rw [← Finset.card_image_of_injective _ hι, hT']]
    exact hS
  · obtain ⟨j, hjS, hjι⟩ := Finset.not_subset.mp hsub
    refine mobiusCoeff_eq_zero_of_indep hjS (fun w => ?_)
    have hne : ∀ k, ι k ≠ j := fun k he => hjι (he ▸ Finset.mem_image_of_mem ι (Finset.mem_univ k))
    congr 1
    funext k
    simp [Function.comp_apply, Pi.add_apply, hne k]

/-- **Even degree-2 is preserved under coordinate injection.** -/
theorem evenDeg2_comp_inj {n : ℕ} {ι : Fin 4 → Fin (n * 4)} (hι : Function.Injective ι)
    {h : (Fin 4 → ZMod 2) → ZMod 4} (hh : EvenDeg2 h) :
    EvenDeg2 (fun w => h (w ∘ ι)) := by
  intro S hS
  by_cases hsub : S ⊆ Finset.image ι Finset.univ
  · have hT' := image_preimage_filter hι hsub
    rw [← hT', mobiusCoeff_reindex_general hι h]
    apply hh
    rw [show (Finset.univ.filter (fun k => ι k ∈ S)).card = S.card from by
      rw [← Finset.card_image_of_injective _ hι, hT']]
    exact hS
  · obtain ⟨j, hjS, hjι⟩ := Finset.not_subset.mp hsub
    rw [mobiusCoeff_eq_zero_of_indep hjS (fun w => ?_), mul_zero]
    have hne : ∀ k, ι k ≠ j := fun k he => hjι (he ▸ Finset.mem_image_of_mem ι (Finset.mem_univ k))
    congr 1
    funext k
    simp [Function.comp_apply, Pi.add_apply, hne k]

/-- `EvenDeg2` is closed under addition. -/
theorem EvenDeg2.add {f g : (Fin N → ZMod 2) → ZMod 4} (hf : EvenDeg2 f) (hg : EvenDeg2 g) :
    EvenDeg2 (f + g) := by
  intro S hS
  rw [mobiusCoeff_add, mul_add, hf S hS, hg S hS, add_zero]

/-- `EvenDeg2` is closed under finite sums. -/
theorem EvenDeg2.sum {α : Type*} (s : Finset α) (f : α → (Fin N → ZMod 2) → ZMod 4)
    (hf : ∀ i ∈ s, EvenDeg2 (f i)) : EvenDeg2 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => intro S _; simp [mobiusCoeff_eq_alt_sum]
  | insert i s hi IH =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (IH fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- All Möbius coefficients even. -/
def AllEven (f : (Fin N → ZMod 2) → ZMod 4) : Prop := ∀ S : Finset (Fin N), 2 * mobiusCoeff S f = 0

theorem AllEven.add {f g : (Fin N → ZMod 2) → ZMod 4} (hf : AllEven f) (hg : AllEven g) :
    AllEven (f + g) := fun S => by rw [mobiusCoeff_add, mul_add, hf S, hg S, add_zero]

theorem AllEven.sum {α : Type*} (s : Finset α) (f : α → (Fin N → ZMod 2) → ZMod 4)
    (hf : ∀ i ∈ s, AllEven (f i)) : AllEven (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => intro S; simp [mobiusCoeff_eq_alt_sum]
  | insert i s hi IH =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (IH fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem allEven_comp_inj {n : ℕ} {ι : Fin 4 → Fin (n * 4)} (hι : Function.Injective ι)
    {h : (Fin 4 → ZMod 2) → ZMod 4} (hh : AllEven h) : AllEven (fun w => h (w ∘ ι)) := by
  intro S
  by_cases hsub : S ⊆ Finset.image ι Finset.univ
  · have hT' := image_preimage_filter hι hsub
    rw [← hT', mobiusCoeff_reindex_general hι h]; exact hh _
  · obtain ⟨j, hjS, hjι⟩ := Finset.not_subset.mp hsub
    rw [mobiusCoeff_eq_zero_of_indep hjS (fun w => ?_), mul_zero]
    have hne : ∀ k, ι k ≠ j := fun k he => hjι (he ▸ Finset.mem_image_of_mem ι (Finset.mem_univ k))
    congr 1; funext k; simp [Function.comp_apply, Pi.add_apply, hne k]

/-! ### The shift maps and the per-qubit decomposition -/

/-- Bit-register shift realizing `decodeP w ↦ decodeP w + v` (the `P`-slots). -/
def shiftP (v : Pauli n) : Fin (n * 4) → ZMod 2 :=
  fun j => ![v.X (finProdFinEquiv.symm j).1, v.Z (finProdFinEquiv.symm j).1, 0, 0]
    (finProdFinEquiv.symm j).2

/-- Bit-register shift realizing `decodeQ w ↦ decodeQ w + v` (the `Q`-slots). -/
def shiftQ (v : Pauli n) : Fin (n * 4) → ZMod 2 :=
  fun j => ![0, 0, v.X (finProdFinEquiv.symm j).1, v.Z (finProdFinEquiv.symm j).1]
    (finProdFinEquiv.symm j).2

theorem shiftP_qubitInj (v : Pauli n) (i : Fin n) (s : Fin 4) :
    shiftP v (qubitInj i s) = ![v.X i, v.Z i, 0, 0] s := by
  unfold shiftP qubitInj; rw [Equiv.symm_apply_apply]

theorem shiftQ_qubitInj (v : Pauli n) (i : Fin n) (s : Fin 4) :
    shiftQ v (qubitInj i s) = ![0, 0, v.X i, v.Z i] s := by
  unfold shiftQ qubitInj; rw [Equiv.symm_apply_apply]

theorem decodeP_add (w s : Fin (n * 4) → ZMod 2) : decodeP (w + s) = decodeP w + decodeP s := by
  refine Pauli.ext ?_ ?_ <;> · funext i; simp [decodeP]

theorem decodeQ_add (w s : Fin (n * 4) → ZMod 2) : decodeQ (w + s) = decodeQ w + decodeQ s := by
  refine Pauli.ext ?_ ?_ <;> · funext i; simp [decodeQ]

theorem decodeP_shiftP (v : Pauli n) : decodeP (shiftP v) = v := by
  refine Pauli.ext ?_ ?_ <;> · funext i; simp [decodeP, shiftP_qubitInj]

theorem decodeQ_shiftP (v : Pauli n) : decodeQ (shiftP v) = 0 := by
  refine Pauli.ext ?_ ?_ <;> · funext i; simp [decodeQ, shiftP_qubitInj]

theorem decodeP_shiftQ (v : Pauli n) : decodeP (shiftQ v) = 0 := by
  refine Pauli.ext ?_ ?_ <;> · funext i; simp [decodeP, shiftQ_qubitInj]

theorem decodeQ_shiftQ (v : Pauli n) : decodeQ (shiftQ v) = v := by
  refine Pauli.ext ?_ ?_ <;> · funext i; simp [decodeQ, shiftQ_qubitInj]

/-- Single-qubit core difference in direction `δ`. -/
def coreDiff (δ u : Fin 4 → ZMod 2) : ZMod 4 := betaCore (u + δ) - betaCore u

/-- Single-qubit mixed (second) core difference in directions `δ, δ'`. -/
def coreMixed (δ δ' u : Fin 4 → ZMod 2) : ZMod 4 :=
  betaCore (u + δ + δ') - betaCore (u + δ) - betaCore (u + δ') + betaCore u

private theorem coreDiff_aux2 : ∀ δ : Fin 4 → ZMod 2,
    ∀ S : Finset (Fin 4), 2 < S.card →
      (∑ T ∈ S.powerset, ((-1 : ℤ) ^ (S.card - T.card)) • coreDiff δ (charFn T)) = 0 := by
  decide

private theorem coreDiff_auxE : ∀ δ : Fin 4 → ZMod 2,
    ∀ S : Finset (Fin 4), S.card = 2 →
      2 * (∑ T ∈ S.powerset, ((-1 : ℤ) ^ (S.card - T.card)) • coreDiff δ (charFn T)) = 0 := by
  decide

private theorem coreMixed_aux1 : ∀ δ δ' : Fin 4 → ZMod 2, δ 2 = 0 → δ 3 = 0 → δ' 0 = 0 → δ' 1 = 0 →
    ∀ S : Finset (Fin 4), 1 < S.card →
      (∑ T ∈ S.powerset, ((-1 : ℤ) ^ (S.card - T.card)) • coreMixed δ δ' (charFn T)) = 0 := by
  decide

private theorem coreMixed_auxAll : ∀ δ δ' : Fin 4 → ZMod 2,
    δ 2 = 0 → δ 3 = 0 → δ' 0 = 0 → δ' 1 = 0 → δ' 2 = δ 0 → δ' 3 = δ 1 →
    ∀ S : Finset (Fin 4),
      2 * (∑ T ∈ S.powerset, ((-1 : ℤ) ^ (S.card - T.card)) • coreMixed δ δ' (charFn T)) = 0 := by
  decide

theorem coreDiff_degLE2 (δ : Fin 4 → ZMod 2) : MobiusDegLE 2 (coreDiff δ) :=
  fun S hS => by rw [mobiusCoeff_eq_alt_sum]; exact coreDiff_aux2 δ S hS

theorem coreDiff_evenDeg2 (δ : Fin 4 → ZMod 2) : EvenDeg2 (coreDiff δ) :=
  fun S hS => by rw [mobiusCoeff_eq_alt_sum]; exact coreDiff_auxE δ S hS

theorem coreMixed_degLE1 (δ δ' : Fin 4 → ZMod 2) (h2 : δ 2 = 0) (h3 : δ 3 = 0)
    (h0' : δ' 0 = 0) (h1' : δ' 1 = 0) : MobiusDegLE 1 (coreMixed δ δ') :=
  fun S hS => by rw [mobiusCoeff_eq_alt_sum]; exact coreMixed_aux1 δ δ' h2 h3 h0' h1' S hS

theorem coreMixed_allEven (δ δ' : Fin 4 → ZMod 2) (h2 : δ 2 = 0) (h3 : δ 3 = 0)
    (h0' : δ' 0 = 0) (h1' : δ' 1 = 0) (h2' : δ' 2 = δ 0) (h3' : δ' 3 = δ 1) :
    AllEven (coreMixed δ δ') :=
  fun S => by rw [mobiusCoeff_eq_alt_sum]; exact coreMixed_auxAll δ δ' h2 h3 h0' h1' h2' h3' S

/-- `(w + s) ∘ qubitInj i = (w ∘ qubitInj i) + (s ∘ qubitInj i)`, pointwise. -/
private theorem add_comp_qubitInj (w s : Fin (n * 4) → ZMod 2) (i : Fin n) (δ : Fin 4 → ZMod 2)
    (hδ : ∀ k, s (qubitInj i k) = δ k) : (w + s) ∘ qubitInj i = (w ∘ qubitInj i) + δ := by
  funext k; simp [Function.comp_apply, Pi.add_apply, hδ k]

/-- **`fac2 = ∂ᵥβ` (p-slot) decomposes into per-qubit core differences.** -/
theorem fac2_eq_sum (v : Pauli n) :
    (fun w => betaFrame (decodeP w + v) (decodeQ w) - betaFrame (decodeP w) (decodeQ w))
      = ∑ i, (fun w => coreDiff (![v.X i, v.Z i, 0, 0]) (w ∘ qubitInj i)) := by
  funext w
  rw [Finset.sum_apply]
  have e1 : betaFrame (decodeP w + v) (decodeQ w) = betaFrameBits (w + shiftP v) := by
    rw [betaFrameBits, decodeP_add, decodeP_shiftP, decodeQ_add, decodeQ_shiftP, add_zero]
  rw [e1, show betaFrame (decodeP w) (decodeQ w) = betaFrameBits w from rfl,
    betaFrameBits_eq_sum, betaFrameBits_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coreDiff, add_comp_qubitInj w (shiftP v) i _ (fun k => shiftP_qubitInj v i k)]

private theorem cons4_zero (a b c d : ZMod 2) : ![a, b, c, d] 0 = a := rfl
private theorem cons4_one (a b c d : ZMod 2) : ![a, b, c, d] 1 = b := rfl
private theorem cons4_two (a b c d : ZMod 2) : ![a, b, c, d] 2 = c := rfl
private theorem cons4_three (a b c d : ZMod 2) : ![a, b, c, d] 3 = d := rfl

/-- **`fac2q = ∂ᵥβ` (q-slot) decomposes into per-qubit core differences.** -/
theorem fac2q_eq_sum (v : Pauli n) :
    (fun w => betaFrame (decodeP w) (decodeQ w + v) - betaFrame (decodeP w) (decodeQ w))
      = ∑ i, (fun w => coreDiff (![0, 0, v.X i, v.Z i]) (w ∘ qubitInj i)) := by
  funext w
  rw [Finset.sum_apply]
  have e1 : betaFrame (decodeP w) (decodeQ w + v) = betaFrameBits (w + shiftQ v) := by
    rw [betaFrameBits, decodeP_add, decodeP_shiftQ, add_zero, decodeQ_add, decodeQ_shiftQ]
  rw [e1, show betaFrame (decodeP w) (decodeQ w) = betaFrameBits w from rfl,
    betaFrameBits_eq_sum, betaFrameBits_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coreDiff, add_comp_qubitInj w (shiftQ v) i _ (fun k => shiftQ_qubitInj v i k)]

/-- **The mixed cross-difference `M` decomposes into per-qubit mixed core differences.** -/
theorem M_eq_sum (v : Pauli n) :
    (fun w => betaFrame (decodeP w + v) (decodeQ w + v) - betaFrame (decodeP w + v) (decodeQ w)
        - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w))
      = ∑ i, (fun w => coreMixed (![v.X i, v.Z i, 0, 0]) (![0, 0, v.X i, v.Z i])
          (w ∘ qubitInj i)) := by
  funext w
  rw [Finset.sum_apply]
  have eAll : betaFrame (decodeP w + v) (decodeQ w + v)
      = betaFrameBits (w + shiftP v + shiftQ v) := by
    rw [betaFrameBits]
    simp only [decodeP_add, decodeQ_add, decodeP_shiftP, decodeQ_shiftP, decodeP_shiftQ,
      decodeQ_shiftQ, add_zero]
  have eP : betaFrame (decodeP w + v) (decodeQ w) = betaFrameBits (w + shiftP v) := by
    rw [betaFrameBits, decodeP_add, decodeP_shiftP, decodeQ_add, decodeQ_shiftP, add_zero]
  have eQ : betaFrame (decodeP w) (decodeQ w + v) = betaFrameBits (w + shiftQ v) := by
    rw [betaFrameBits, decodeP_add, decodeP_shiftQ, add_zero, decodeQ_add, decodeQ_shiftQ]
  rw [eAll, eP, eQ, show betaFrame (decodeP w) (decodeQ w) = betaFrameBits w from rfl,
    betaFrameBits_eq_sum, betaFrameBits_eq_sum, betaFrameBits_eq_sum, betaFrameBits_eq_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coreMixed,
    add_comp_qubitInj (w + shiftP v) (shiftQ v) i _ (fun k => shiftQ_qubitInj v i k),
    add_comp_qubitInj w (shiftP v) i _ (fun k => shiftP_qubitInj v i k),
    add_comp_qubitInj w (shiftQ v) i _ (fun k => shiftQ_qubitInj v i k)]

/-- **`fac2` (the p-slot `∂ᵥβ`) is Möbius-degree ≤2 with even degree-2 part.** -/
theorem fac2_facts (v : Pauli n) :
    MobiusDegLE 2 (fun w => betaFrame (decodeP w + v) (decodeQ w)
        - betaFrame (decodeP w) (decodeQ w))
      ∧ EvenDeg2 (fun w => betaFrame (decodeP w + v) (decodeQ w)
          - betaFrame (decodeP w) (decodeQ w)) := by
  rw [fac2_eq_sum]
  exact ⟨MobiusDegLE.sum _ _ (fun i _ => mobiusDegLE_comp_inj (qubitInj_injective i)
      (coreDiff_degLE2 _)),
    EvenDeg2.sum _ _ (fun i _ => evenDeg2_comp_inj (qubitInj_injective i)
      (coreDiff_evenDeg2 _))⟩

/-- **`fac2q` (the q-slot `∂ᵥβ`) is Möbius-degree ≤2 with even degree-2 part.** -/
theorem fac2q_facts (v : Pauli n) :
    MobiusDegLE 2 (fun w => betaFrame (decodeP w) (decodeQ w + v)
        - betaFrame (decodeP w) (decodeQ w))
      ∧ EvenDeg2 (fun w => betaFrame (decodeP w) (decodeQ w + v)
          - betaFrame (decodeP w) (decodeQ w)) := by
  rw [fac2q_eq_sum]
  exact ⟨MobiusDegLE.sum _ _ (fun i _ => mobiusDegLE_comp_inj (qubitInj_injective i)
      (coreDiff_degLE2 _)),
    EvenDeg2.sum _ _ (fun i _ => evenDeg2_comp_inj (qubitInj_injective i)
      (coreDiff_evenDeg2 _))⟩

/-- **The cross-difference `M` is Möbius-degree ≤1 and entirely even.** -/
theorem M_facts (v : Pauli n) :
    MobiusDegLE 1 (fun w => betaFrame (decodeP w + v) (decodeQ w + v)
        - betaFrame (decodeP w + v) (decodeQ w)
        - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w))
      ∧ AllEven (fun w => betaFrame (decodeP w + v) (decodeQ w + v)
        - betaFrame (decodeP w + v) (decodeQ w)
        - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w)) := by
  rw [M_eq_sum]
  refine ⟨MobiusDegLE.sum _ _ (fun i _ => mobiusDegLE_comp_inj (qubitInj_injective i)
      (coreMixed_degLE1 _ _ (cons4_two _ _ _ _) (cons4_three _ _ _ _)
        (cons4_zero _ _ _ _) (cons4_one _ _ _ _))),
    AllEven.sum _ _ (fun i _ => allEven_comp_inj (qubitInj_injective i)
      (coreMixed_allEven _ _ (cons4_two _ _ _ _) (cons4_three _ _ _ _)
        (cons4_zero _ _ _ _) (cons4_one _ _ _ _) ?_ ?_))⟩
  · rw [cons4_two, cons4_zero]
  · rw [cons4_three, cons4_one]

/-! ## Discharging `RankOneCubic` and the unconditional ceiling -/

/-- **The crux `RankOneCubic` is discharged unconditionally.** Each rank-one term is a product of
factors that are Möbius-degree ≤2 with even degree-2 parts (the parity factors and `∂ᵥβ`), so by the
even·even cancellation each term is degree ≤3. Term 3 (a triple product) factors as
parity × (parity × `M`), with `M` degree ≤1 and entirely even, via the special product lemma. -/
theorem rankOneCubic_holds (v : Pauli n) : RankOneCubic v := by
  have hpar_p : (fun w => ((omega v (decodeP w)).val : ZMod 4))
      = parityOfSet ((Finset.univ.filter (fun i => v.Z i = 1)).image (fun i => qubitInj i 0)
          ∪ (Finset.univ.filter (fun i => v.X i = 1)).image (fun i => qubitInj i 1)) := by
    rw [← omega_decode_parity v 0 1 (by decide)]
    funext w; congr 2
  have hpar_q : (fun w => ((omega v (decodeQ w)).val : ZMod 4))
      = parityOfSet ((Finset.univ.filter (fun i => v.Z i = 1)).image (fun i => qubitInj i 2)
          ∪ (Finset.univ.filter (fun i => v.X i = 1)).image (fun i => qubitInj i 3)) := by
    rw [← omega_decode_parity v 2 3 (by decide)]
    funext w; congr 2
  have hp2 : MobiusDegLE 2 (fun w => ((omega v (decodeP w)).val : ZMod 4)) := by
    rw [hpar_p]; exact (parityOfSet_facts _).1
  have hpe : EvenDeg2 (fun w => ((omega v (decodeP w)).val : ZMod 4)) := by
    rw [hpar_p]; exact (parityOfSet_facts _).2
  have hq2 : MobiusDegLE 2 (fun w => ((omega v (decodeQ w)).val : ZMod 4)) := by
    rw [hpar_q]; exact (parityOfSet_facts _).1
  have hqe : EvenDeg2 (fun w => ((omega v (decodeQ w)).val : ZMod 4)) := by
    rw [hpar_q]; exact (parityOfSet_facts _).2
  obtain ⟨hf2_2, hf2_e⟩ := fac2_facts v
  obtain ⟨hf2q_2, hf2q_e⟩ := fac2q_facts v
  obtain ⟨hM1, hMall⟩ := M_facts v
  refine ⟨mobiusDegLE_mul_evenEven hp2 hf2_2 hpe hf2_e,
    mobiusDegLE_mul_evenEven hq2 hf2q_2 hqe hf2q_e, ?_⟩
  have hmix2 : MobiusDegLE 2 ((fun w => ((omega v (decodeQ w)).val : ZMod 4))
      * (fun w => betaFrame (decodeP w + v) (decodeQ w + v) - betaFrame (decodeP w + v) (decodeQ w)
          - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w))) :=
    mobiusDegLE_mul_special hq2 hqe hM1 hMall
  have hmixe : EvenDeg2 ((fun w => ((omega v (decodeQ w)).val : ZMod 4))
      * (fun w => betaFrame (decodeP w + v) (decodeQ w + v) - betaFrame (decodeP w + v) (decodeQ w)
          - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w))) :=
    fun S _ => even_of_mul_even hMall S
  have hprod := mobiusDegLE_mul_evenEven hp2 hmix2 hpe hmixe
  rw [show rankOneTerm3 v = (fun w => ((omega v (decodeP w)).val : ZMod 4))
        * ((fun w => ((omega v (decodeQ w)).val : ZMod 4))
          * (fun w => betaFrame (decodeP w + v) (decodeQ w + v)
              - betaFrame (decodeP w + v) (decodeQ w)
              - betaFrame (decodeP w) (decodeQ w + v) + betaFrame (decodeP w) (decodeQ w)))
      from by funext w; simp only [rankOneTerm3, Pi.mul_apply]; ring]
  exact hprod

/-- **🎯 The unconditional cubic ceiling:** every single transvection's distortion cochain is
Möbius-degree ≤ 3. (`RankOneCubic` discharged, so the conditional ceiling becomes unconditional.) -/
theorem transvection_distortion_cubic (v : Pauli n) : MobiusDegLE 3 (distortionBits v) :=
  transvection_distortion_mobiusDegLE_three v (rankOneCubic_holds v)

end FTQCLib.Frame

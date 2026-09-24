/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.PolyList
import ECCLib.ReedSolomon
import ECCLib.Decoding

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# The Gao decoder for Reed–Solomon codes

The verified bounded-distance decoder, by Gao's algorithm: extended Euclid on the **nodal
product** `G₀ = ∏ᵢ (X − aᵢ)` and the **interpolant** `G₁` of the received word, stopped at the
first remainder `g` with `2·pdeg g < n + k + 2`; the output codeword re-evaluates `g / v`.
Native to the library's `rsCode` presentation (any injective point family — the monic direct-root
convention makes an evaluation point `0` an ordinary point), no syndromes, no GRS multipliers.

Everything executable (`prodLin`, `pinterp`, `gaoLoop`, `rsDecode`) is computable structural/
fuel recursion over a `FieldOps` kit; Mathlib's `Polynomial` appears only through `toPoly`.
Main results:

* `gaoLoop_spec` — the four Euclid invariants (Bezout divisibility, the two subtraction-free
  degree sums `≤ n + 2`, strict descent, the `±G₀` determinant identity) through the loop;
* `gao_identity` — the heart: at the stop, `g = f·v` and `v ≠ 0`, by the degree-count on
  `Δ = g·E − f·v·E` against `G₀ ∣ Δ`;
* `rsDecodeF_corrects` — `Corrects (rsDecodeF ops M a k) (rsCode a k) t` whenever
  `2t + k ≤ n` (subtraction-free; the `2t < minDist` form derived via `minDist_rsCode`).
-/

namespace ECCLib.Coding

open Polynomial

variable {R : Type*} {F : Type*} [Field F] {ops : FieldOps R} {φ : R → F}

/-! ## `psize` — the `pdeg` of a denotation, at the polynomial level -/

/-- Polynomial-level size: `natDegree + 1` on nonzero polynomials, `0` at `0` — what `pdeg`
computes through `toPoly` (`pdeg_eq_psize`). Keeps the loop-invariant arithmetic
subtraction-free on the proof side. -/
noncomputable def psize (p : Polynomial F) : ℕ :=
  letI := Classical.dec (p = 0)
  if p = 0 then 0 else p.natDegree + 1

@[simp] theorem psize_zero : psize (0 : Polynomial F) = 0 := by
  simp [psize]

theorem psize_of_ne_zero {p : Polynomial F} (hp : p ≠ 0) : psize p = p.natDegree + 1 := by
  simp [psize, hp]

theorem psize_eq_zero_iff {p : Polynomial F} : psize p = 0 ↔ p = 0 := by
  by_cases hp : p = 0 <;> simp [psize, hp]

theorem pdeg_eq_psize (M : ops.Model φ) (p : List R) : pdeg ops p = psize (toPoly φ p) := by
  by_cases hp : toPoly φ p = 0
  · rw [(pdeg_eq_zero_iff M p).mpr hp, hp, psize_zero]
  · rw [pdeg_eq_natDegree_succ M p hp, psize_of_ne_zero hp]

/-! ## The nodal product -/

/-- `∏_{x ∈ as} (X − x)` as a coefficient list — the executable nodal polynomial. -/
def prodLin (ops : FieldOps R) (as : List R) : List R :=
  as.foldr (fun x acc => pmul ops [ops.neg x, ops.one] acc) [ops.one]

private lemma monic_prod_map (l : List F) : (l.map fun w => X - C w).prod.Monic := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons]
    exact (monic_X_sub_C x).mul ih

private lemma natDegree_prod_map (l : List F) :
    (l.map fun w => X - C w).prod.natDegree = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons,
      natDegree_mul (X_sub_C_ne_zero x) (monic_prod_map l).ne_zero,
      natDegree_X_sub_C, ih, List.length_cons]
    omega

private lemma eval_prod_map (l : List F) (z : F) :
    (l.map fun w => X - C w).prod.eval z = (l.map fun w => z - w).prod := by
  rw [eval_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun w _ => ?_)
  simp

theorem toPoly_prodLin (M : ops.Model φ) : ∀ as : List R,
    toPoly φ (prodLin ops as) = ((as.map φ).map fun w => X - C w).prod
  | [] => by simp [prodLin, toPoly_singleton, M.map_one]
  | x :: as => by
    have h : prodLin ops (x :: as) = pmul ops [ops.neg x, ops.one] (prodLin ops as) := rfl
    rw [h, toPoly_pmul M, toPoly_prodLin M as, List.map_cons, List.map_cons, List.prod_cons]
    congr 1
    change C (φ (ops.neg x)) + X * (C (φ ops.one) + X * 0) = X - C (φ x)
    rw [M.map_neg, M.map_one, C_neg, C_1]
    ring

theorem prodLin_monic (M : ops.Model φ) (as : List R) : (toPoly φ (prodLin ops as)).Monic := by
  rw [toPoly_prodLin M]
  exact monic_prod_map _

theorem prodLin_natDegree (M : ops.Model φ) (as : List R) :
    (toPoly φ (prodLin ops as)).natDegree = as.length := by
  rw [toPoly_prodLin M, natDegree_prod_map, List.length_map]

theorem prodLin_eval (M : ops.Model φ) (as : List R) (z : F) :
    (toPoly φ (prodLin ops as)).eval z = ((as.map φ).map fun w => z - w).prod := by
  rw [toPoly_prodLin M, eval_prod_map]

/-! ## `eraseIdx` index bookkeeping -/

section EraseIdx

variable {α : Type*}

private lemma mem_eraseIdx_of_ne {l : List α} {i j : ℕ} (hi : i < l.length)
    (hne : i ≠ j) : l[i] ∈ l.eraseIdx j := by
  rw [List.eraseIdx_eq_take_drop_succ]
  rcases Nat.lt_or_ge i j with h | h
  · apply List.mem_append_left
    have hlen : i < (l.take j).length := by
      rw [List.length_take]
      omega
    have hg : (l.take j)[i] = l[i] := List.getElem_take
    rw [← hg]
    exact List.getElem_mem hlen
  · have hgt : j < i := by omega
    apply List.mem_append_right
    have hidx : i - (j + 1) < (l.drop (j + 1)).length := by
      rw [List.length_drop]
      omega
    have hg : (l.drop (j + 1))[i - (j + 1)] = l[i] := by
      rw [List.getElem_drop]
      congr 1
      omega
    rw [← hg]
    exact List.getElem_mem hidx

private lemma forall_mem_eraseIdx {l : List α} {j : ℕ} {P : α → Prop}
    (h : ∀ (i : ℕ) (_ : i < l.length), i ≠ j → P l[i]) :
    ∀ x ∈ l.eraseIdx j, P x := by
  intro x hx
  rw [List.eraseIdx_eq_take_drop_succ] at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < l.length ∧ i < j := by
      have := hi
      rw [List.length_take] at this
      omega
    rw [List.getElem_take]
    exact h i hi'.1 (by omega)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : j + 1 + i < l.length := by
      have := hi
      rw [List.length_drop] at this
      omega
    rw [List.getElem_drop]
    exact h (j + 1 + i) hi' (by omega)

end EraseIdx

/-! ## The interpolant -/

/-- The executable Lagrange interpolant: `Σᵢ yᵢ · (Nᵢ(aᵢ))⁻¹ · Nᵢ` with
`Nᵢ = ∏_{j ≠ i} (X − aⱼ)` — the denominator is `Nᵢ` evaluated at `aᵢ`, so `prodLin` and
`peval` are the only ingredients. -/
def pinterp (ops : FieldOps R) (as ys : List R) : List R :=
  (List.range as.length).foldr
    (fun i acc => padd ops
      (psmul ops
        (ops.mul (ys.getD i ops.zero)
          (ops.inv (peval ops (as.getD i ops.zero) (prodLin ops (as.eraseIdx i)))))
        (prodLin ops (as.eraseIdx i)))
      acc)
    []

private theorem toPoly_foldr_padd (M : ops.Model φ) (g : ℕ → List R) : ∀ l : List ℕ,
    toPoly φ (l.foldr (fun i acc => padd ops (g i) acc) [])
      = (l.map fun i => toPoly φ (g i)).sum
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons, toPoly_padd M, toPoly_foldr_padd M g l, List.map_cons, List.sum_cons]

theorem toPoly_pinterp (M : ops.Model φ) (as ys : List R) :
    toPoly φ (pinterp ops as ys)
      = ((List.range as.length).map fun i =>
          C (φ (ops.mul (ys.getD i ops.zero)
              (ops.inv (peval ops (as.getD i ops.zero) (prodLin ops (as.eraseIdx i))))))
            * toPoly φ (prodLin ops (as.eraseIdx i))).sum := by
  rw [pinterp, toPoly_foldr_padd M]
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [toPoly_psmul M]

private lemma list_sum_eval (l : List (Polynomial F)) (z : F) :
    l.sum.eval z = (l.map fun p => p.eval z).sum := by
  induction l with
  | nil => simp
  | cons p l ih => rw [List.sum_cons, eval_add, ih, List.map_cons, List.sum_cons]

private lemma degree_list_sum_lt (l : List (Polynomial F)) (m : ℕ)
    (h : ∀ p ∈ l, p.degree < (m : WithBot ℕ)) : l.sum.degree < (m : WithBot ℕ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.sum_cons]
    exact lt_of_le_of_lt (degree_add_le _ _)
      (max_lt (h p List.mem_cons_self) (ih fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem pinterp_degree_lt (M : ops.Model φ) (as ys : List R) :
    (toPoly φ (pinterp ops as ys)).degree < (as.length : WithBot ℕ) := by
  rw [toPoly_pinterp M]
  refine degree_list_sum_lt _ _ ?_
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hilt : i < as.length := List.mem_range.mp hi
  have hN : (toPoly φ (prodLin ops (as.eraseIdx i))).Monic := prodLin_monic M _
  have hNdeg : (toPoly φ (prodLin ops (as.eraseIdx i))).natDegree + 1 = as.length := by
    rw [prodLin_natDegree M]
    exact List.length_eraseIdx_add_one hilt
  have hnat : (toPoly φ (prodLin ops (as.eraseIdx i))).natDegree < as.length := by omega
  set c : F := φ (ops.mul (ys.getD i ops.zero)
    (ops.inv (peval ops (as.getD i ops.zero) (prodLin ops (as.eraseIdx i))))) with hc_def
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, C_0, zero_mul, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hp0 : C c * toPoly φ (prodLin ops (as.eraseIdx i)) ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr hc) hN.ne_zero
    rw [degree_eq_natDegree hp0, natDegree_mul (C_ne_zero.mpr hc) hN.ne_zero, natDegree_C]
    have hfin : 0 + (toPoly φ (prodLin ops (as.eraseIdx i))).natDegree < as.length := by omega
    exact_mod_cast hfin

/-- The interpolation property: at each node the interpolant reads the data. Needs the
mapped points pairwise distinct (`Nodup`); the data list `ys` is unconstrained (`getD`). -/
theorem pinterp_eval (M : ops.Model φ) {as ys : List R} (hnd : (as.map φ).Nodup)
    {i : ℕ} (hi : i < as.length) :
    (toPoly φ (pinterp ops as ys)).eval (φ (as.getD i ops.zero)) = φ (ys.getD i ops.zero) := by
  have hz : as.getD i ops.zero = as[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [toPoly_pinterp M]
  have hbridge : ∀ g : ℕ → F,
      ((List.range as.length).map g).sum = ∑ j ∈ Finset.range as.length, g j := by
    intro g
    rfl
  rw [list_sum_eval, List.map_map, hbridge]
  rw [Finset.sum_eq_single i]
  · -- the i-th term: φyᵢ · D⁻¹ · D = φyᵢ
    simp only [Function.comp_apply, eval_mul, eval_C]
    rw [M.map_mul, M.map_inv, peval_toPoly M]
    have hD : (toPoly φ (prodLin ops (as.eraseIdx i))).eval (φ (as.getD i ops.zero)) ≠ 0 := by
      rw [prodLin_eval M]
      intro h0
      obtain ⟨x, hx, hx0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h0)
      -- x ∈ (as.eraseIdx i).map φ, and φ (getD i) − x = 0
      have hxne : x ≠ φ (as[i]) := by
        rw [← List.eraseIdx_map] at hx
        refine forall_mem_eraseIdx (P := fun w => w ≠ φ as[i]) ?_ x hx
        intro j hj hji
        rw [List.getElem_map]
        intro heq
        have hji' : (as.map φ)[j]'hj = (as.map φ)[i]'(by rw [List.length_map]; exact hi) := by
          rw [List.getElem_map, List.getElem_map]
          exact heq
        exact hji (hnd.getElem_inj_iff.mp hji')
      rw [hz] at hx0
      exact hxne (sub_eq_zero.mp hx0).symm
    rw [mul_assoc, inv_mul_cancel₀ hD, mul_one]
  · -- other terms vanish: aᵢ is a root of Nⱼ for j ≠ i
    intro j hj hji
    simp only [Function.comp_apply, eval_mul, eval_C]
    have hjlt : j < as.length := Finset.mem_range.mp hj
    have hzero : (toPoly φ (prodLin ops (as.eraseIdx j))).eval (φ (as.getD i ops.zero)) = 0 := by
      rw [prodLin_eval M]
      apply List.prod_eq_zero
      have hmem : as[i] ∈ as.eraseIdx j := mem_eraseIdx_of_ne hi hji.symm
      refine List.mem_map.mpr ⟨φ as[i], List.mem_map.mpr ⟨as[i], hmem, rfl⟩, ?_⟩
      rw [hz, sub_self]
    rw [hzero, mul_zero]
  · intro hnotin
    exact absurd (Finset.mem_range.mpr hi) hnotin

/-! ## `pdeg` arithmetic for the loop invariants -/

theorem degree_lt_degree_of_pdeg_lt (M : ops.Model φ) {p q : List R}
    (hp : toPoly φ p ≠ 0) (h : pdeg ops q < pdeg ops p) :
    (toPoly φ q).degree < (toPoly φ p).degree := by
  rw [degree_eq_natDegree hp]
  by_cases hq : toPoly φ q = 0
  · rw [hq, degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hq]
    have h1 := pdeg_eq_natDegree_succ M p hp
    have h2 := pdeg_eq_natDegree_succ M q hq
    exact_mod_cast by omega

/-- Product sizes add (both factors semantically nonzero), subtraction-free. -/
theorem pdeg_pmul (M : ops.Model φ) {p q : List R}
    (hp : toPoly φ p ≠ 0) (hq : toPoly φ q ≠ 0) :
    pdeg ops (pmul ops p q) + 1 = pdeg ops p + pdeg ops q := by
  have hpq : toPoly φ (pmul ops p q) = toPoly φ p * toPoly φ q := toPoly_pmul M p q
  have hne : toPoly φ (pmul ops p q) ≠ 0 := by
    rw [hpq]
    exact mul_ne_zero hp hq
  rw [pdeg_eq_natDegree_succ M _ hne, pdeg_eq_natDegree_succ M _ hp,
    pdeg_eq_natDegree_succ M _ hq, hpq, natDegree_mul hp hq]
  omega

theorem pdeg_psub_le (M : ops.Model φ) (p q : List R) :
    pdeg ops (psub ops p q) ≤ max (pdeg ops p) (pdeg ops q) := by
  apply pdeg_le_of_degree_lt M
  rw [toPoly_psub M]
  refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
  · exact lt_of_lt_of_le (toPoly_degree_lt_pdeg M p) (by exact_mod_cast le_max_left _ _)
  · exact lt_of_lt_of_le (toPoly_degree_lt_pdeg M q) (by exact_mod_cast le_max_right _ _)

/-- The derived quotient size: division at `pdeg d ≤ pdeg p` is size-exact,
`pdeg q + pdeg d = pdeg p + 1`. -/
theorem pdeg_pdivMod_fst (M : ops.Model φ) {p d : List R} (hd : pdeg ops d ≠ 0)
    (hle : pdeg ops d ≤ pdeg ops p) :
    pdeg ops (pdivMod ops p d).1 + pdeg ops d = pdeg ops p + 1 := by
  obtain ⟨hid, hrem⟩ := pdivMod_spec M (p := p) (d := d) hd
  have hp0 : toPoly φ p ≠ 0 := by
    intro h
    rw [(pdeg_eq_zero_iff M p).mpr h] at hle
    omega
  have hd0 : toPoly φ d ≠ 0 := fun h => hd ((pdeg_eq_zero_iff M d).mpr h)
  have hq0 : toPoly φ (pdivMod ops p d).1 ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_add] at hid
    have : pdeg ops p < pdeg ops d := by
      rw [pdeg_eq_psize M, pdeg_eq_psize M, hid]
      rw [pdeg_eq_psize M, pdeg_eq_psize M] at hrem
      exact hrem
    omega
  have hRmlt : (toPoly φ (pdivMod ops p d).2).degree < (toPoly φ p).degree :=
    degree_lt_degree_of_pdeg_lt M hp0 (by omega)
  have hDQ : toPoly φ d * toPoly φ (pdivMod ops p d).1
      = toPoly φ p - toPoly φ (pdivMod ops p d).2 := by
    linear_combination -hid
  have hdeg : (toPoly φ d).degree + (toPoly φ (pdivMod ops p d).1).degree
      = (toPoly φ p).degree := by
    rw [← degree_mul, hDQ, degree_sub_eq_left_of_degree_lt hRmlt]
  rw [degree_eq_natDegree hd0, degree_eq_natDegree hq0, degree_eq_natDegree hp0] at hdeg
  have hnat : (toPoly φ d).natDegree + (toPoly φ (pdivMod ops p d).1).natDegree
      = (toPoly φ p).natDegree := by exact_mod_cast hdeg
  rw [pdeg_eq_natDegree_succ M _ hq0, pdeg_eq_natDegree_succ M _ hd0,
    pdeg_eq_natDegree_succ M _ hp0]
  omega

/-! ## The Euclid loop and its invariants -/

/-- The Gao loop state invariant: Bezout divisibility for both rows, the two subtraction-free
size sums (`≤ n + 2`), strict size descent, and the `±G₀` determinant identity. -/
structure GaoInv (φ : R → F) (ops : FieldOps R) (G₀ G₁ : Polynomial F) (n : ℕ)
    (rp vp rc vc : List R) : Prop where
  dvd_p : G₀ ∣ toPoly φ rp - toPoly φ vp * G₁
  dvd_c : G₀ ∣ toPoly φ rc - toPoly φ vc * G₁
  j1 : pdeg ops vc + pdeg ops rp ≤ n + 2
  j2 : pdeg ops vp + pdeg ops rp ≤ n + 2
  i3 : pdeg ops rc < pdeg ops rp
  i4 : toPoly φ rp * toPoly φ vc - toPoly φ rc * toPoly φ vp = G₀
      ∨ toPoly φ rp * toPoly φ vc - toPoly φ rc * toPoly φ vp = -G₀

/-- The extended-Euclid loop: rows carried as (remainder, cofactor) pairs, stopped at the
first remainder of size below the threshold. Fuel recursion (kernel-reducible); the spec's
side condition `pdeg rc < fuel` makes the fuel sufficient. -/
def gaoLoop (ops : FieldOps R) (nk2 : ℕ) :
    ℕ → List R → List R → List R → List R → List R × List R
  | 0, _, _, rc, vc => (rc, vc)
  | fuel + 1, rp, vp, rc, vc =>
    if 2 * pdeg ops rc < nk2 then (rc, vc)
    else
      gaoLoop ops nk2 fuel rc vc (pdivMod ops rp rc).2
        (psub ops vp (pmul ops (pdivMod ops rp rc).1 vc))

/-- One Euclid step preserves the invariant. -/
theorem gaoInv_step (M : ops.Model φ) {G₀ G₁ : Polynomial F} {n : ℕ} {rp vp rc vc : List R}
    (inv : GaoInv φ ops G₀ G₁ n rp vp rc vc) (hrc : pdeg ops rc ≠ 0) :
    GaoInv φ ops G₀ G₁ n rc vc (pdivMod ops rp rc).2
      (psub ops vp (pmul ops (pdivMod ops rp rc).1 vc)) := by
  obtain ⟨hid, hrem⟩ := pdivMod_spec M (p := rp) (d := rc) hrc
  have hvc' : toPoly φ (psub ops vp (pmul ops (pdivMod ops rp rc).1 vc))
      = toPoly φ vp - toPoly φ (pdivMod ops rp rc).1 * toPoly φ vc := by
    rw [toPoly_psub M, toPoly_pmul M]
  have hRm_eq : toPoly φ (pdivMod ops rp rc).2
      = toPoly φ rp - toPoly φ rc * toPoly φ (pdivMod ops rp rc).1 := by
    linear_combination -hid
  refine ⟨inv.dvd_c, ?_, ?_, ?_, hrem, ?_⟩
  · -- Bezout: Rm − vc'·G₁ = (rp − vp·G₁) − Q·(rc − vc·G₁)
    rw [hvc', hRm_eq]
    have hkey : toPoly φ rp - toPoly φ rc * toPoly φ (pdivMod ops rp rc).1
        - (toPoly φ vp - toPoly φ (pdivMod ops rp rc).1 * toPoly φ vc) * G₁
        = (toPoly φ rp - toPoly φ vp * G₁)
          - toPoly φ (pdivMod ops rp rc).1 * (toPoly φ rc - toPoly φ vc * G₁) := by
      ring
    rw [hkey]
    exact dvd_sub inv.dvd_p (Dvd.dvd.mul_left inv.dvd_c _)
  · -- J1': pdeg vc' + pdeg rc ≤ n + 2
    have hsub_le := pdeg_psub_le M vp (pmul ops (pdivMod ops rp rc).1 vc)
    have hbr1 : pdeg ops vp + pdeg ops rc ≤ n + 1 := by
      have h1 := inv.j2
      have h2 := inv.i3
      omega
    have hbr2 : pdeg ops (pmul ops (pdivMod ops rp rc).1 vc) + pdeg ops rc ≤ n + 2 := by
      by_cases hvc0 : toPoly φ vc = 0
      · have h0 : toPoly φ (pmul ops (pdivMod ops rp rc).1 vc) = 0 := by
          rw [toPoly_pmul M, hvc0, mul_zero]
        rw [(pdeg_eq_zero_iff M _).mpr h0]
        have h1 := inv.j2
        have h2 := inv.i3
        omega
      · by_cases hq0 : toPoly φ (pdivMod ops rp rc).1 = 0
        · exfalso
          have hrp_eq : toPoly φ rp = toPoly φ (pdivMod ops rp rc).2 := by
            rw [hq0, mul_zero, zero_add] at hid
            exact hid
          have h1 : pdeg ops rp = pdeg ops (pdivMod ops rp rc).2 := by
            rw [pdeg_eq_psize M, pdeg_eq_psize M, hrp_eq]
          have h2 := inv.i3
          omega
        · have hq_deg := pdeg_pdivMod_fst M hrc (le_of_lt inv.i3)
          have hmul := pdeg_pmul M hq0 hvc0
          have h1 := inv.j1
          omega
    omega
  · -- J2': pdeg vc + pdeg rc ≤ n + 2
    have h1 := inv.j1
    have h2 := inv.i3
    omega
  · -- I4': the determinant identity, sign flipped
    rw [hvc', hRm_eq]
    rcases inv.i4 with h | h
    · right
      linear_combination -h
    · left
      linear_combination -h

/-- The loop specification: at the stop, the returned row satisfies the threshold and Bezout
divisibility, and the previous row witnesses the size bounds and the determinant identity.
The extra hypothesis `nk2 ≤ 2·pdeg rp` (the previous row is above threshold) is itself
preserved: recursion only happens when the stop test fails. -/
theorem gaoLoop_spec (M : ops.Model φ) {G₀ G₁ : Polynomial F} {n nk2 : ℕ} (hnk2 : 2 ≤ nk2) :
    ∀ (fuel : ℕ) (rp vp rc vc : List R), pdeg ops rc < fuel →
      GaoInv φ ops G₀ G₁ n rp vp rc vc →
      nk2 ≤ 2 * pdeg ops rp →
      2 * pdeg ops (gaoLoop ops nk2 fuel rp vp rc vc).1 < nk2
      ∧ (G₀ ∣ toPoly φ (gaoLoop ops nk2 fuel rp vp rc vc).1
            - toPoly φ (gaoLoop ops nk2 fuel rp vp rc vc).2 * G₁)
      ∧ ∃ rr vv : List R, nk2 ≤ 2 * pdeg ops rr
          ∧ pdeg ops (gaoLoop ops nk2 fuel rp vp rc vc).2 + pdeg ops rr ≤ n + 2
          ∧ pdeg ops vv + pdeg ops rr ≤ n + 2
          ∧ (toPoly φ rr * toPoly φ (gaoLoop ops nk2 fuel rp vp rc vc).2
                - toPoly φ (gaoLoop ops nk2 fuel rp vp rc vc).1 * toPoly φ vv = G₀
             ∨ toPoly φ rr * toPoly φ (gaoLoop ops nk2 fuel rp vp rc vc).2
                - toPoly φ (gaoLoop ops nk2 fuel rp vp rc vc).1 * toPoly φ vv = -G₀)
  | 0, rp, vp, rc, vc, hfuel, _, _ => absurd hfuel (by omega)
  | fuel + 1, rp, vp, rc, vc, hfuel, inv, hthr => by
    by_cases hstop : 2 * pdeg ops rc < nk2
    · have heq : gaoLoop ops nk2 (fuel + 1) rp vp rc vc = (rc, vc) := by
        simp only [gaoLoop, if_pos hstop]
      rw [heq]
      exact ⟨hstop, inv.dvd_c, rp, vp, hthr, inv.j1, inv.j2, inv.i4⟩
    · have heq : gaoLoop ops nk2 (fuel + 1) rp vp rc vc
          = gaoLoop ops nk2 fuel rc vc (pdivMod ops rp rc).2
              (psub ops vp (pmul ops (pdivMod ops rp rc).1 vc)) := by
        simp only [gaoLoop, if_neg hstop]
      rw [heq]
      have hrc0 : pdeg ops rc ≠ 0 := by omega
      have hstep := gaoInv_step M inv hrc0
      have hrem := (pdivMod_spec M (p := rp) (d := rc) hrc0).2
      exact gaoLoop_spec M hnk2 fuel rc vc _ _ (by omega) hstep (by omega)

/-! ## The identity (the heart of the correctness proof) -/

section Identity

variable {n : ℕ} {a : Fin n → F}

private lemma nodal_monic (a : Fin n → F) : (∏ i, (X - C (a i))).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)

private lemma nodal_natDegree (a : Fin n → F) : (∏ i, (X - C (a i))).natDegree = n := by
  rw [natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (a i)]
  simp

/-- Root-counting at pairwise-distinct points: linear factors at common roots divide, by
pairwise coprimality. -/
theorem prod_X_sub_C_dvd (ha : Function.Injective a) {p : Polynomial F} :
    ∀ S : Finset (Fin n), (∀ i ∈ S, p.eval (a i) = 0) → (∏ i ∈ S, (X - C (a i))) ∣ p := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert i S hiS ih =>
    intro h
    rw [Finset.prod_insert hiS]
    have hdvd1 : (X - C (a i)) ∣ p := dvd_iff_isRoot.mpr (h i (Finset.mem_insert_self i S))
    have hdvd2 : (∏ j ∈ S, (X - C (a j))) ∣ p :=
      ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hcop : IsCoprime (X - C (a i)) (∏ j ∈ S, (X - C (a j))) := by
      refine IsCoprime.prod_right fun j hj => ?_
      have hne : a i ≠ a j := fun heq => hiS (by rw [ha heq]; exact hj)
      exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))
    exact hcop.mul_dvd hdvd1 hdvd2

variable [DecidableEq F]

/-- The key divisibility: with `E` the error-support locator, `G₀ ∣ (G₁ − f)·E` — at each
point either the interpolant agrees with `f` or the point is a root of `E`. -/
private lemma key_dvd (ha : Function.Injective a) {f G₁ : Polynomial F} {e : Fin n → F}
    (hval : ∀ i, G₁.eval (a i) = f.eval (a i) + e i) :
    (∏ i, (X - C (a i)))
      ∣ (G₁ - f) * ∏ i ∈ Finset.univ.filter (fun i => e i ≠ 0), (X - C (a i)) := by
  have hsplit : (∏ i, (X - C (a i)))
      = (∏ i ∈ Finset.univ.filter (fun i => e i ≠ 0), (X - C (a i)))
        * ∏ i ∈ Finset.univ.filter (fun i => ¬ e i ≠ 0), (X - C (a i)) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  rw [hsplit, mul_comm (G₁ - f)]
  refine mul_dvd_mul dvd_rfl (prod_X_sub_C_dvd ha _ fun i hi => ?_)
  have hei : e i = 0 := not_not.mp (Finset.mem_filter.mp hi).2
  rw [eval_sub, hval i, hei, add_zero, sub_self]

/-- **The Gao identity**: at the loop's stop, with the exports, the low-degree remainder is
exactly `f · v` and the cofactor is nonzero — by the degree count on `Δ = g·E − f·v·E`
against `G₀ ∣ Δ`. -/
theorem gao_identity {k t : ℕ} (ha : Function.Injective a)
    {f G₁ g v : Polynomial F} (hf : f ∈ degreeLT F k)
    {e : Fin n → F} (he : (Finset.univ.filter fun i => e i ≠ 0).card ≤ t)
    (hval : ∀ i, G₁.eval (a i) = f.eval (a i) + e i)
    (htk : 2 * t + k ≤ n)
    (hstop : 2 * psize g < n + k + 2)
    (hdvd : (∏ i, (X - C (a i))) ∣ g - v * G₁)
    (hexp : ∃ rp vp : Polynomial F, n + k + 2 ≤ 2 * psize rp
        ∧ psize v + psize rp ≤ n + 2 ∧ psize vp + psize rp ≤ n + 2
        ∧ (rp * v - g * vp = ∏ i, (X - C (a i))
           ∨ rp * v - g * vp = -∏ i, (X - C (a i)))) :
    g = f * v ∧ v ≠ 0 := by
  set G₀ : Polynomial F := ∏ i, (X - C (a i)) with hG₀_def
  have hG₀m : G₀.Monic := nodal_monic a
  have hG₀deg : G₀.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hG₀m.ne_zero, nodal_natDegree a]
  set E : Polynomial F := ∏ i ∈ Finset.univ.filter (fun i => e i ≠ 0), (X - C (a i))
    with hE_def
  have hEm : E.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hEnd : E.natDegree ≤ t := by
    rw [hE_def, natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (a i)]
    have h1 : ∀ i ∈ Finset.univ.filter (fun i => e i ≠ 0), (X - C (a i)).natDegree = 1 :=
      fun i _ => natDegree_X_sub_C (a i)
    rw [Finset.sum_congr rfl h1]
    simpa using he
  obtain ⟨rp, vp, hrp_thr, hvrp, hvprp, hdet⟩ := hexp
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv, zero_mul, sub_zero] at hdvd
    have hgdeg : g.degree < G₀.degree := by
      rw [hG₀deg]
      by_cases hg : g = 0
      · rw [hg, degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hg]
        have hpg := psize_of_ne_zero hg
        have hlt : g.natDegree < n := by omega
        exact_mod_cast hlt
    have hg0 : g = 0 := eq_zero_of_dvd_of_degree_lt hdvd hgdeg
    rw [hv, hg0] at hdet
    simp only [mul_zero, zero_mul, sub_self] at hdet
    rcases hdet with h | h
    · exact hG₀m.ne_zero h.symm
    · exact hG₀m.ne_zero (neg_eq_zero.mp h.symm)
  have hpv := psize_of_ne_zero hv0
  have hv_nd : 2 * v.natDegree + k ≤ n := by omega
  have hkey := key_dvd ha hval
  have hΔdvd : G₀ ∣ g * E - f * v * E := by
    have hsplit : g * E - f * v * E = (g - v * G₁) * E + v * ((G₁ - f) * E) := by ring
    rw [hsplit]
    exact dvd_add (hdvd.mul_right E) (hkey.mul_left v)
  have hΔdeg : (g * E - f * v * E).degree < G₀.degree := by
    rw [hG₀deg]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · by_cases hg : g = 0
      · rw [hg, zero_mul, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hgE : g * E ≠ 0 := mul_ne_zero hg hEm.ne_zero
        rw [degree_eq_natDegree hgE, natDegree_mul hg hEm.ne_zero]
        have hpg := psize_of_ne_zero hg
        have hlt : g.natDegree + E.natDegree < n := by omega
        exact_mod_cast hlt
    · by_cases hf0 : f = 0
      · rw [hf0, zero_mul, zero_mul, degree_zero]
        exact WithBot.bot_lt_coe _
      · have hfvE : f * v * E ≠ 0 := mul_ne_zero (mul_ne_zero hf0 hv0) hEm.ne_zero
        rw [degree_eq_natDegree hfvE, natDegree_mul (mul_ne_zero hf0 hv0) hEm.ne_zero,
          natDegree_mul hf0 hv0]
        have hfnd : f.natDegree < k :=
          (natDegree_lt_iff_degree_lt hf0).mpr (Polynomial.mem_degreeLT.mp hf)
        have hlt : f.natDegree + v.natDegree + E.natDegree < n := by omega
        exact_mod_cast hlt
  have hΔ0 : g * E - f * v * E = 0 := eq_zero_of_dvd_of_degree_lt hΔdvd hΔdeg
  have hgE : (g - f * v) * E = 0 := by linear_combination hΔ0
  have hgfv : g - f * v = 0 := by
    rcases mul_eq_zero.mp hgE with h | h
    · exact h
    · exact absurd h hEm.ne_zero
  exact ⟨sub_eq_zero.mp hgfv, hv0⟩

end Identity

/-! ## The decoder -/

/-- **The Gao decoder**, list-level: build the nodal polynomial and the interpolant, run the
Euclid loop to the threshold `n + k + 2`, divide the low remainder by its cofactor, guard
(nonzero cofactor, zero remainder, quotient size ≤ k), and re-evaluate at the points.
Fully computable — structural/fuel recursion only; `none` beyond the radius is the
bounded-distance contract. -/
def rsDecode (ops : FieldOps R) (as : List R) (k : ℕ) (ys : List R) : Option (List R) :=
  let gv := gaoLoop ops (as.length + k + 2) (as.length + 2)
    (prodLin ops as) [] (pinterp ops as ys) [ops.one]
  if pdeg ops gv.2 = 0 then none
  else
    let fr := pdivMod ops gv.1 gv.2
    if pdeg ops fr.2 = 0 ∧ pdeg ops fr.1 ≤ k then
      some (as.map fun x => peval ops x fr.1)
    else none

/-- The list-level correctness: within the radius (`2t + k ≤ n`), `rsDecode` returns exactly
the transmitted codeword's coefficient list. -/
theorem rsDecode_eq_some [DecidableEq F] (M : ops.Model φ) {n k t : ℕ}
    {a : Fin n → F} (ha : Function.Injective a) {ρ : F → R} (hρ : ∀ x, φ (ρ x) = x)
    (hkn : k ≤ n) (htk : 2 * t + k ≤ n)
    {f : Polynomial F} (hf : f ∈ Polynomial.degreeLT F k)
    {e : Fin n → F} (he : (Finset.univ.filter fun i => e i ≠ 0).card ≤ t) :
    rsDecode ops (List.ofFn fun i => ρ (a i)) k (List.ofFn fun i => ρ (f.eval (a i) + e i))
      = some (List.ofFn fun i => ρ (f.eval (a i))) := by
  set as : List R := List.ofFn fun i => ρ (a i) with has_def
  set ys : List R := List.ofFn fun i => ρ (f.eval (a i) + e i) with hys_def
  have hlen : as.length = n := by rw [has_def, List.length_ofFn]
  have hmapφ : as.map φ = List.ofFn a := by
    rw [has_def, List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => hρ (a i))
  -- the nodal polynomial
  have hG₀ : toPoly φ (prodLin ops as) = ∏ i, (X - C (a i)) := by
    rw [toPoly_prodLin M, hmapφ, List.map_ofFn, List.prod_ofFn]
    rfl
  have hG₀m : (toPoly φ (prodLin ops as)).Monic := prodLin_monic M as
  have hpdeg_G₀ : pdeg ops (prodLin ops as) = n + 1 := by
    rw [pdeg_eq_natDegree_succ M _ hG₀m.ne_zero, prodLin_natDegree M, hlen]
  -- the interpolant
  have hG₁deg : (toPoly φ (pinterp ops as ys)).degree < (n : WithBot ℕ) := by
    have h := pinterp_degree_lt M as ys
    rwa [hlen] at h
  have hpdeg_G₁ : pdeg ops (pinterp ops as ys) ≤ n := pdeg_le_of_degree_lt M hG₁deg
  have hnd : (as.map φ).Nodup := by
    rw [hmapφ]
    exact List.nodup_ofFn.mpr ha
  have hG₁val : ∀ i : Fin n,
      (toPoly φ (pinterp ops as ys)).eval (a i) = f.eval (a i) + e i := by
    intro i
    have hi : (i : ℕ) < as.length := by rw [hlen]; exact i.isLt
    have h := pinterp_eval M (ys := ys) hnd hi
    have hga : as.getD (i : ℕ) ops.zero = ρ (a i) := by
      rw [has_def, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp), Option.getD_some, List.getElem_ofFn]
    have hgy : ys.getD (i : ℕ) ops.zero = ρ (f.eval (a i) + e i) := by
      rw [hys_def, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp), Option.getD_some, List.getElem_ofFn]
    rw [hga, hgy, hρ, hρ] at h
    exact h
  -- the initial invariant, and the loop run
  have hone : toPoly φ [ops.one] = 1 := by
    rw [toPoly_singleton, M.map_one, C_1]
  have hpdeg_one : pdeg ops [ops.one] = 1 := by
    rw [pdeg_eq_psize M, hone, psize_of_ne_zero one_ne_zero, natDegree_one]
  have hpdeg_nil : pdeg ops ([] : List R) = 0 := rfl
  have hinv : GaoInv φ ops (toPoly φ (prodLin ops as)) (toPoly φ (pinterp ops as ys)) n
      (prodLin ops as) [] (pinterp ops as ys) [ops.one] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [toPoly_nil, zero_mul, sub_zero]
    · rw [hone, one_mul, sub_self]
      exact dvd_zero _
    · rw [hpdeg_one, hpdeg_G₀]
      omega
    · rw [hpdeg_nil, hpdeg_G₀]
      omega
    · rw [hpdeg_G₀]
      omega
    · left
      rw [hone, toPoly_nil, mul_one, mul_zero, sub_zero]
  obtain ⟨hstop, hdvd, rr, vv, hthr, hvrr, hvvrr, hdet⟩ :=
    gaoLoop_spec M (nk2 := as.length + k + 2) (by omega) (as.length + 2)
      (prodLin ops as) [] (pinterp ops as ys) [ops.one] (by omega) hinv (by omega)
  rw [hG₀] at hdvd hdet
  -- the identity
  have hstop' : 2 * psize (toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
      (prodLin ops as) [] (pinterp ops as ys) [ops.one]).1) < n + k + 2 := by
    rw [← pdeg_eq_psize M]
    omega
  have hexp' : ∃ rp vp : Polynomial F, n + k + 2 ≤ 2 * psize rp
      ∧ psize (toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
          (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2) + psize rp ≤ n + 2
      ∧ psize vp + psize rp ≤ n + 2
      ∧ (rp * toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
            (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2
          - toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
              (prodLin ops as) [] (pinterp ops as ys) [ops.one]).1 * vp
          = ∏ i, (X - C (a i))
         ∨ rp * toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
            (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2
          - toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
              (prodLin ops as) [] (pinterp ops as ys) [ops.one]).1 * vp
          = -∏ i, (X - C (a i))) := by
    refine ⟨toPoly φ rr, toPoly φ vv, ?_, ?_, ?_, hdet⟩
    · rw [← pdeg_eq_psize M]
      omega
    · rw [← pdeg_eq_psize M, ← pdeg_eq_psize M]
      omega
    · rw [← pdeg_eq_psize M, ← pdeg_eq_psize M]
      omega
  obtain ⟨hgfv, hv0⟩ := gao_identity ha hf he hG₁val htk hstop' hdvd hexp'
  -- unfold the decoder and discharge the guards
  simp only [rsDecode]
  have hguard1 : ¬ pdeg ops (gaoLoop ops (as.length + k + 2) (as.length + 2)
      (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2 = 0 :=
    fun h => hv0 ((pdeg_eq_zero_iff M _).mp h)
  rw [if_neg hguard1]
  obtain ⟨hdivid, hdivrem⟩ := pdivMod_spec M
    (p := (gaoLoop ops (as.length + k + 2) (as.length + 2)
      (prodLin ops as) [] (pinterp ops as ys) [ops.one]).1)
    (d := (gaoLoop ops (as.length + k + 2) (as.length + 2)
      (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2)
    (fun h => hv0 ((pdeg_eq_zero_iff M _).mp h))
  have h₂ : toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
      (prodLin ops as) [] (pinterp ops as ys) [ops.one]).1
      = toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
          (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2 * f + 0 := by
    rw [add_zero, hgfv]
    ring
  have hru : (toPoly φ (pdivMod ops
      (gaoLoop ops (as.length + k + 2) (as.length + 2)
        (prodLin ops as) [] (pinterp ops as ys) [ops.one]).1
      (gaoLoop ops (as.length + k + 2) (as.length + 2)
        (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2).2).degree
      < (toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
          (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2).degree :=
    degree_lt_degree_of_pdeg_lt M hv0 hdivrem
  have hr0 : (0 : Polynomial F).degree
      < (toPoly φ (gaoLoop ops (as.length + k + 2) (as.length + 2)
          (prodLin ops as) [] (pinterp ops as ys) [ops.one]).2).degree := by
    rw [degree_zero]
    exact Ne.bot_lt fun h => hv0 (degree_eq_bot.mp h)
  obtain ⟨hQ, hRm⟩ := pdiv_unique hdivid h₂ hru hr0
  have hpsize_f : psize f ≤ k := by
    by_cases hf0 : f = 0
    · rw [hf0, psize_zero]
      omega
    · rw [psize_of_ne_zero hf0]
      have := (natDegree_lt_iff_degree_lt hf0).mpr (Polynomial.mem_degreeLT.mp hf)
      omega
  rw [if_pos ⟨(pdeg_eq_zero_iff M _).mpr hRm, by rw [pdeg_eq_psize M, hQ]; exact hpsize_f⟩]
  -- the output is the codeword's list
  congr 1
  rw [has_def, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => M.injective ?_)
  rw [Function.comp_apply, peval_toPoly M, hQ, hρ, hρ]

/-! ## The field-level decoder and its correctness theorem -/

variable [Fintype F]

/-- The field-level Gao decoder: transport words through the model bijection, run the
computable `rsDecode`, wrap back. Noncomputable spec object; the computable content is
`rsDecode`. -/
noncomputable def rsDecodeF (ops : FieldOps R) {φ : R → F} (M : ops.Model φ) {n : ℕ}
    (a : Fin n → F) (k : ℕ) : (Fin n → F) → Option (Fin n → F) := fun y =>
  (rsDecode ops (List.ofFn fun i => (Equiv.ofBijective φ M.bij).symm (a i)) k
    (List.ofFn fun i => (Equiv.ofBijective φ M.bij).symm (y i))).map
    fun cs j => φ (cs.getD (j : ℕ) ops.zero)

/-- **The correction guarantee** (subtraction-free): the Gao decoder corrects `t` errors
whenever `2t + k ≤ n`, over any injective point family. -/
theorem rsDecodeF_corrects [DecidableEq F] (ops : FieldOps R) {φ : R → F} (M : ops.Model φ)
    {n k t : ℕ} {a : Fin n → F} (ha : Function.Injective a)
    (hkn : k ≤ n) (htk : 2 * t + k ≤ n) :
    Corrects (rsDecodeF ops M a k) (rsCode a k) t := by
  intro c hc e he
  obtain ⟨f, hf, hfc⟩ := mem_rsCode.mp hc
  have hρ : ∀ x, φ ((Equiv.ofBijective φ M.bij).symm x) = x := fun x =>
    (Equiv.ofBijective φ M.bij).apply_symm_apply x
  have hsupp : (Finset.univ.filter fun i => e i ≠ 0).card ≤ t := he
  simp only [rsDecodeF]
  have hlist : (List.ofFn fun i => (Equiv.ofBijective φ M.bij).symm ((c + e) i))
      = List.ofFn fun i => (Equiv.ofBijective φ M.bij).symm (f.eval (a i) + e i) := by
    refine congrArg List.ofFn (funext fun i => ?_)
    rw [← hfc]
    rfl
  rw [hlist, rsDecode_eq_some M ha hρ hkn htk hf hsupp, Option.map_some]
  congr 1
  funext j
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp),
    Option.getD_some, List.getElem_ofFn, hρ, ← hfc]
  simp

/-- The literature-facing form: correction below half the minimum distance, through the MDS
theorem `minDist_rsCode`. -/
theorem rsDecodeF_corrects' [DecidableEq F] (ops : FieldOps R) {φ : R → F} (M : ops.Model φ)
    {n k t : ℕ} {a : Fin n → F} (ha : Function.Injective a) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (h2t : 2 * t < minDist (rsCode a k)) :
    Corrects (rsDecodeF ops M a k) (rsCode a k) t := by
  refine rsDecodeF_corrects ops M ha hkn ?_
  have hmd := minDist_rsCode ha hk1 (by simpa using hkn)
  rw [Fintype.card_fin] at hmd
  omega

end ECCLib.Coding

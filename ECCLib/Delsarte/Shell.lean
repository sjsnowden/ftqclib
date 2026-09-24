/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.Delsarte.Krawtchouk
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.InformationTheory.Hamming

set_option linter.unusedSectionVars false

/-!
# The shell character identity

`charShellSum`: the sum of the tuple character `χ ↦ ∏ᵢ χᵢ(vᵢ)` over the dual weight-`k`
shell equals the Krawtchouk number `K_k(wt v)`. This is the one structural theorem of
the Delsarte layer — reference statement: McKinley 2003, Lemma 3.5.5 eq. (3.20); route
here: the ℂ[X]-valued generating identity (`tupleChar_genfun`, the dual-side port of the
library's `krawtchouk_pi` skeleton) followed by coefficient extraction through `kraw_eq_coeff` —
no `Polynomial.funext`, no primitivity hypothesis, arbitrary finite abelian alphabet.
The literature's support-partition proof of (3.20) is an alternative route.

Also here: the primal generating function over ANY pointed finite alphabet, giving the
weight-shell / sphere / ball cardinalities (`card_shell`, `card_sphere`, `card_ball`)
that the classical-bound certificates (`Corollaries.lean`, `BallCert.lean`) consume.

Instance note: `Fintype (AddChar A ℂ)` and
`DecidableEq (AddChar A ℂ)` are Mathlib's noncomputable global instances (the latter IS
`Classical.decEq`); we rely on them and keep every downstream consumer's interface in
ℕ/ℤ so no character instance escapes this file.
-/

namespace ECCLib.Delsarte

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `r ^ hammingNorm u` as a coordinatewise product of `ite`s — the weight-bookkeeping
helper shared by the dual and primal generating identities. -/
theorem pow_hammingNorm_eq_prod {R : Type*} [CommMonoid R] {β : ι → Type*}
    [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] (r : R) (u : ∀ i, β i) :
    r ^ hammingNorm u = ∏ i, if u i = 0 then 1 else r := by
  unfold hammingNorm
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, one_mul]

section Dual

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The tuple character: a family of characters of the alphabet, applied coordinatewise
and multiplied. The dual weight of `χ` is Mathlib's `hammingNorm χ` (the trivial
character IS the zero of `AddChar`). -/
def tupleChar (χ : ι → AddChar A ℂ) (v : ι → A) : ℂ := ∏ i, χ i (v i)

omit [DecidableEq ι] [Fintype A] [DecidableEq A] in
@[simp] theorem tupleChar_zero_left (v : ι → A) :
    tupleChar (0 : ι → AddChar A ℂ) v = 1 := by
  simp [tupleChar]

/-- The one-coordinate shell sum, `ℂ[X]`-valued: summing `ite(ψ=0) 1 X · ψ(a)` over ALL
characters of the alphabet gives `1 + (q−1)X` at `a = 0` and `1 − X` otherwise. The
only duality input is `AddChar.sum_apply_eq_ite` — no primitivity, no field. -/
theorem shellCoordSum (a : A) :
    ∑ ψ : AddChar A ℂ, (if ψ = 0 then (1 : Polynomial ℂ) else X) * C (ψ a)
      = if a = 0 then 1 + C ((Fintype.card A : ℂ) - 1) * X else 1 - X := by
  have hsplit : ∀ ψ : AddChar A ℂ, (if ψ = 0 then (1 : Polynomial ℂ) else X) * C (ψ a)
      = X * C (ψ a) + (if ψ = 0 then (1 - X) * C (ψ a) else 0) := by
    intro ψ
    by_cases hψ : ψ = 0
    · rw [if_pos hψ, if_pos hψ]; ring
    · rw [if_neg hψ, if_neg hψ]; ring
  rw [Finset.sum_congr rfl fun ψ _ => hsplit ψ, Finset.sum_add_distrib]
  have hchar : ∑ ψ : AddChar A ℂ, X * C (ψ a)
      = X * C (if a = 0 then (Fintype.card A : ℂ) else 0) := by
    rw [← Finset.mul_sum, ← map_sum, AddChar.sum_apply_eq_ite]
  have hdelta : ∑ ψ : AddChar A ℂ, (if ψ = 0 then (1 - X) * C (ψ a) else 0)
      = 1 - X := by
    rw [Finset.sum_ite_eq' Finset.univ (0 : AddChar A ℂ) (fun ψ => (1 - X) * C (ψ a))]
    simp
  rw [hchar, hdelta]
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ha]
    rw [map_sub, map_natCast, map_one]
    ring
  · rw [if_neg ha, if_neg ha]
    simp

/-- **The dual generating identity** (the `krawtchouk_pi` skeleton, ported to the dual
side, `ℂ[X]`-valued): summing `tupleChar χ v · X^{wt χ}` over ALL character tuples
factorizes coordinatewise into the Krawtchouk generating polynomial at `wt v`. -/
theorem tupleChar_genfun (v : ι → A) :
    ∑ χ : ι → AddChar A ℂ, C (tupleChar χ v) * X ^ hammingNorm χ
      = (1 - X) ^ hammingNorm v
        * (1 + C ((Fintype.card A : ℂ) - 1) * X) ^ (Fintype.card ι - hammingNorm v) := by
  have hfac : ∀ χ : ι → AddChar A ℂ, C (tupleChar χ v) * X ^ hammingNorm χ
      = ∏ i, ((if χ i = 0 then (1 : Polynomial ℂ) else X) * C ((χ i) (v i))) := by
    intro χ
    rw [Finset.prod_mul_distrib, mul_comm]
    congr 1
    · exact pow_hammingNorm_eq_prod X χ
    · unfold tupleChar
      rw [map_prod]
  rw [Finset.sum_congr rfl fun χ _ => hfac χ, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset (AddChar A ℂ))
      (fun (i : ι) (ψ : AddChar A ℂ) => (if ψ = 0 then (1 : Polynomial ℂ) else X) * C (ψ (v i)))]
  rw [Finset.prod_congr rfl fun i _ => shellCoordSum (v i)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => v i = 0)
  rw [Finset.card_univ] at hsplit
  have hwt : (Finset.univ.filter (fun i => ¬ v i = 0)).card = hammingNorm v := rfl
  rw [hwt, mul_comm]
  congr 2
  omega

/-- The `ℂ`-cast of the Krawtchouk generating polynomial. -/
theorem krawPoly_map_complex (q n i : ℕ) :
    (krawPoly q n i).map (Int.castRingHom ℂ)
      = (1 - X) ^ i * (1 + C ((q : ℂ) - 1) * X) ^ (n - i) := by
  unfold krawPoly
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X, Polynomial.map_C]
  have hcast : (Int.castRingHom ℂ) ((q : ℤ) - 1) = (q : ℂ) - 1 := by
    rw [eq_intCast]
    push_cast
    ring
  rw [hcast]

/-- **The shell character identity — the crux of the Delsarte layer.** The tuple-character sum over
the dual weight-`k` shell is the Krawtchouk number at `wt v`. Reference: McKinley 2003,
Lemma 3.5.5 (3.20); Cohn–Zhao (1)+(MS77 p. 151) via `kraw_eq_coeff`. -/
theorem charShellSum (k : ℕ) (v : ι → A) :
    ∑ χ ∈ Finset.univ.filter (fun χ : ι → AddChar A ℂ => hammingNorm χ = k),
        tupleChar χ v
      = ((kraw (Fintype.card A) (Fintype.card ι) k (hammingNorm v) : ℤ) : ℂ) := by
  have h := congrArg (fun p => Polynomial.coeff p k) (tupleChar_genfun (ι := ι) v)
  simp only at h
  rw [Polynomial.finset_sum_coeff] at h
  have hterm : ∀ χ : ι → AddChar A ℂ,
      (C (tupleChar χ v) * X ^ hammingNorm χ).coeff k
        = if hammingNorm χ = k then tupleChar χ v else 0 := by
    intro χ
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hχ : hammingNorm χ = k
    · simp [hχ]
    · simp [hχ, Ne.symm hχ]
  rw [Finset.sum_congr rfl fun χ _ => hterm χ, ← Finset.sum_filter] at h
  rw [h, ← krawPoly_map_complex, Polynomial.coeff_map, ← kraw_eq_coeff]
  rfl

/-- The one-coordinate **primal** shell sum — the mirror of `shellCoordSum` with the roles of
the alphabet and its character set exchanged: summing `ite(a=0) 1 X · ψ(a)` over the alphabet
gives `1 + (q−1)X` for the trivial character and `1 − X` otherwise. The only duality input is
`AddChar.sum_eq_ite`. -/
theorem coordSumOfChar (ψ : AddChar A ℂ) :
    ∑ a : A, (if a = 0 then (1 : Polynomial ℂ) else X) * C (ψ a)
      = if ψ = 0 then 1 + C ((Fintype.card A : ℂ) - 1) * X else 1 - X := by
  classical
  have hsplit : ∀ a : A, (if a = 0 then (1 : Polynomial ℂ) else X) * C (ψ a)
      = X * C (ψ a) + (if a = 0 then (1 - X) * C (ψ a) else 0) := by
    intro a
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos ha]; ring
    · rw [if_neg ha, if_neg ha]; ring
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← map_sum, Finset.sum_ite_eq' Finset.univ (0 : A)
      (fun a => (1 - X) * C (ψ a)),
    if_pos (Finset.mem_univ _), AddChar.map_zero_eq_one, map_one, mul_one,
    AddChar.sum_eq_ite]
  by_cases hψ : ψ = 0
  · rw [if_pos hψ, if_pos hψ]
    simp only [map_sub, map_natCast, map_one]
    ring
  · rw [if_neg hψ, if_neg hψ, map_zero, mul_zero, zero_add]

/-- **The primal generating identity** — the mirror of `tupleChar_genfun`: summing
`tupleChar χ v · X^{wt v}` over ALL words factorizes coordinatewise. -/
theorem wordChar_genfun (χ : ι → AddChar A ℂ) :
    ∑ v : ι → A, C (tupleChar χ v) * X ^ hammingNorm v
      = (1 - X) ^ hammingNorm χ
        * (1 + C ((Fintype.card A : ℂ) - 1) * X) ^ (Fintype.card ι - hammingNorm χ) := by
  classical
  have hfac : ∀ v : ι → A, C (tupleChar χ v) * X ^ hammingNorm v
      = ∏ i, ((if v i = 0 then (1 : Polynomial ℂ) else X) * C ((χ i) (v i))) := by
    intro v
    rw [Finset.prod_mul_distrib, mul_comm]
    congr 1
    · exact pow_hammingNorm_eq_prod X v
    · unfold tupleChar
      rw [map_prod]
  rw [Finset.sum_congr rfl fun v _ => hfac v, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset A)
      (fun (i : ι) (a : A) => (if a = 0 then (1 : Polynomial ℂ) else X) * C ((χ i) a))]
  rw [Finset.prod_congr rfl fun i _ => coordSumOfChar (χ i)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (p := fun i => χ i = 0)
  rw [Finset.card_univ] at hsplit
  have hwt : (Finset.univ.filter (fun i => ¬ χ i = 0)).card = hammingNorm χ := rfl
  rw [hwt, mul_comm]
  congr 2
  omega

/-- **The primal shell character sum** — the mirror of `charShellSum`, and the identity the
Hamming `P`-entries reduce to: the tuple-character sum over the weight-`w` word shell is the
Krawtchouk number at `wt χ`. No self-duality of the alphabet anywhere. -/
theorem wordShellSum (w : ℕ) (χ : ι → AddChar A ℂ) :
    ∑ v ∈ Finset.univ.filter (fun v : ι → A => hammingNorm v = w),
        tupleChar χ v
      = ((kraw (Fintype.card A) (Fintype.card ι) w (hammingNorm χ) : ℤ) : ℂ) := by
  classical
  have h := congrArg (fun p => Polynomial.coeff p w) (wordChar_genfun (ι := ι) χ)
  simp only at h
  rw [Polynomial.finset_sum_coeff] at h
  have hterm : ∀ v : ι → A,
      (C (tupleChar χ v) * X ^ hammingNorm v).coeff w
        = if hammingNorm v = w then tupleChar χ v else 0 := by
    intro v
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hv : hammingNorm v = w
    · simp [hv]
    · simp [hv, Ne.symm hv]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter] at h
  rw [h, ← krawPoly_map_complex, Polynomial.coeff_map, ← kraw_eq_coeff]
  rfl

end Dual

section Primal

variable {β : Type*} [Fintype β] [DecidableEq β] [Zero β]

/-- The primal generating function over ANY pointed finite alphabet: total weight
enumerator of the full space. -/
theorem primal_genfun :
    ∑ u : ι → β, (X : Polynomial ℤ) ^ hammingNorm u
      = (1 + C ((Fintype.card β : ℤ) - 1) * X) ^ Fintype.card ι := by
  have hone : 1 ≤ Fintype.card β := Fintype.card_pos
  have hfac : ∀ u : ι → β, (X : Polynomial ℤ) ^ hammingNorm u
      = ∏ i, if u i = 0 then (1 : Polynomial ℤ) else X :=
    fun u => pow_hammingNorm_eq_prod X u
  rw [Finset.sum_congr rfl fun u _ => hfac u, ← Fintype.piFinset_univ,
    Finset.sum_prod_piFinset (Finset.univ : Finset β)
      (fun (_ : ι) (b : β) => if b = 0 then (1 : Polynomial ℤ) else X)]
  have hcoord : ∀ i : ι, (∑ b : β, if b = 0 then (1 : Polynomial ℤ) else X)
      = 1 + C ((Fintype.card β : ℤ) - 1) * X := by
    intro _
    have h1 : (Finset.univ.filter (fun b : β => b = 0)).card = 1 := by
      rw [Finset.filter_eq' Finset.univ (0 : β), if_pos (Finset.mem_univ 0),
        Finset.card_singleton]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset β)) (p := fun b : β => b = 0)
    rw [Finset.card_univ] at hsplit
    have h2 : (Finset.univ.filter (fun b : β => ¬ b = 0)).card = Fintype.card β - 1 := by
      omega
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h2, one_smul, nsmul_eq_mul,
      ← Polynomial.C_eq_natCast,
      show ((Fintype.card β - 1 : ℕ) : ℤ) = (Fintype.card β : ℤ) - 1 by
        push_cast [Nat.cast_sub hone]; ring]
  rw [Finset.prod_congr rfl fun i _ => hcoord i, Finset.prod_const, Finset.card_univ]

/-- The weight-`k` shell of the full space has `C(n,k)(q−1)^k` elements. -/
theorem card_shell (k : ℕ) :
    (Finset.univ.filter fun u : ι → β => hammingNorm u = k).card
      = (Fintype.card ι).choose k * (Fintype.card β - 1) ^ k := by
  have hone : 1 ≤ Fintype.card β := Fintype.card_pos
  have h := congrArg (fun p => Polynomial.coeff p k) (primal_genfun (ι := ι) (β := β))
  simp only at h
  rw [Polynomial.finset_sum_coeff] at h
  have hterm : ∀ u : ι → β, ((X : Polynomial ℤ) ^ hammingNorm u).coeff k
      = if hammingNorm u = k then 1 else 0 := by
    intro u
    rw [Polynomial.coeff_X_pow]
    by_cases hu : hammingNorm u = k
    · simp [hu]
    · simp [hu, Ne.symm hu]
  rw [Finset.sum_congr rfl fun u _ => hterm u, Finset.sum_boole,
    coeff_one_add_C_mul_X_pow,
    show ((Fintype.card β : ℤ) - 1) = ((Fintype.card β - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hone]; ring] at h
  exact_mod_cast h

end Primal

section Sphere

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-! ### Norm helpers -/

omit [DecidableEq ι] [Fintype A] in
theorem hammingNorm_neg (v : ι → A) : hammingNorm (-v) = hammingNorm v := by
  unfold hammingNorm
  congr 1
  ext i
  simp

omit [DecidableEq ι] [Fintype A] in
theorem hammingNorm_add_le (u w : ι → A) :
    hammingNorm (u + w) ≤ hammingNorm u + hammingNorm w := by
  have h1 : hammingNorm (u + w) = hammingDist (-u) w := by
    rw [hammingDist_eq_hammingNorm, neg_neg]
  have h2 : hammingDist (-u) (0 : ι → A) = hammingNorm u := by
    rw [hammingDist_eq_hammingNorm, neg_neg, add_zero]
  have h3 : hammingDist (0 : ι → A) w = hammingNorm w := by
    rw [hammingDist_eq_hammingNorm, neg_zero, zero_add]
  rw [h1, ← h2, ← h3]
  exact hammingDist_triangle _ _ _

omit [DecidableEq ι] in
/-- Words of any prescribed weight `i ≤ n` exist once the alphabet is nontrivial. -/
theorem exists_word_of_weight (hA : 1 < Fintype.card A) {i : ℕ}
    (hi : i ≤ Fintype.card ι) : ∃ v : ι → A, hammingNorm v = i := by
  classical
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp hA
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := i) (by rwa [Finset.card_univ])
  refine ⟨fun idx => if idx ∈ S then a else 0, ?_⟩
  unfold hammingNorm
  rw [show (Finset.univ.filter fun idx => (if idx ∈ S then a else 0) ≠ 0) = S by
    ext idx
    by_cases hidx : idx ∈ S <;> simp [hidx, ha]]
  exact hS

/-- Spheres are translated shells. -/
theorem card_sphere (x : ι → A) (j : ℕ) :
    (Finset.univ.filter fun y : ι → A => hammingDist x y = j).card
      = (Fintype.card ι).choose j * (Fintype.card A - 1) ^ j := by
  rw [← card_shell (ι := ι) (β := A) j]
  apply Finset.card_nbij' (i := fun y => -x + y) (j := fun u => x + u)
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
    rw [← hammingDist_eq_hammingNorm]
    exact hy
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hu ⊢
    rw [hammingDist_eq_hammingNorm, neg_add_cancel_left]
    exact hu
  · intro y _
    simp [add_neg_cancel_left]
  · intro u _
    simp [neg_add_cancel_left]

/-- Ball cardinality, unconditional in the radius. -/
theorem card_ball (x : ι → A) (e : ℕ) :
    (Finset.univ.filter fun y : ι → A => hammingDist x y ≤ e).card
      = ∑ j ∈ Finset.range (e + 1),
          (Fintype.card ι).choose j * (Fintype.card A - 1) ^ j := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun y => hammingDist x y) (t := Finset.range (e + 1))
    (fun y hy => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hy).2))]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← card_sphere x j]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro hdist
  have hje := Finset.mem_range.mp hj
  omega


end Sphere

end ECCLib.Delsarte

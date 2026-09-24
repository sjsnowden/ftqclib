/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.ReedSolomon
import Mathlib.LinearAlgebra.Lagrange

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
# Generalized Reed–Solomon codes and the weighted parity check

The parity-check presentation of Reed–Solomon codes, which is false in its naive form, done
right. Plain Reed–Solomon codes are NOT closed under duality: the dual of `rsCode a k` is a
**generalized** RS code, an evaluation code with column multipliers — and the multipliers
are pinned (up to one global scalar) to the Lagrange leading coefficients
`uᵢ = (∏_{j≠i}(aᵢ − aⱼ))⁻¹`. This module builds:

* `grsCode a v k` — the multiplier-scaled evaluation code, with `rsCode` as its `v ≡ 1`
  instance and `finrank = k` by transport along the diagonal scaling equivalence;
* `sum_dualMult_eval` — the moment identity `deg P < n−1 ⟹ Σᵢ uᵢ P(aᵢ) = 0`, read off
  Mathlib's `Lagrange.coeff_eq_sum` at a vanishing coefficient;
* **`dualCode_grsCode`** — Hall 5.1.6: `(grsCode a v k)^⊥ = grsCode a (u/v) (n−k)`,
  annihilation + dimension count;
* **`rsCode_eq_ker_synMap`** — `rsCode a k = ker (synMap a (n−k))`, the correct `rsCode =
  ker H`: membership is the vanishing of the `u`-WEIGHTED syndrome moments. The unweighted
  power sums present the code only for constant-multiplier families (e.g. `n = q`); in
  general the unweighted form is false.

This is the seam the syndrome layer (`Decoding.lean`) and the codeword-checker netlist
(`GateChecker.lean`) consume.
-/

namespace ECCLib.Coding

open Polynomial ECCLib.Heisenberg

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## GRS codes -/

/-- The multiplier-scaled evaluation map: `p ↦ (vᵢ · p(aᵢ))ᵢ`. -/
noncomputable def grsEval (a v : ι → F) : Polynomial F →ₗ[F] (ι → F) where
  toFun p := fun i => v i * p.eval (a i)
  map_add' p q := by
    funext i
    simp only [eval_add, Pi.add_apply]
    ring
  map_smul' c p := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Polynomial.smul_eq_C_mul, eval_mul, eval_C]
    ring

omit [DecidableEq ι] in
@[simp] theorem grsEval_apply (a v : ι → F) (p : Polynomial F) (i : ι) :
    grsEval a v p i = v i * p.eval (a i) := rfl

/-- The **generalized Reed–Solomon code**: evaluations of degree-`< k` polynomials, scaled
per-column by the multipliers `v`. -/
noncomputable def grsCode (a v : ι → F) (k : ℕ) : Submodule F (ι → F) :=
  Submodule.map (grsEval a v) (degreeLT F k)

omit [DecidableEq ι] in
theorem mem_grsCode {a v : ι → F} {k : ℕ} {y : ι → F} :
    y ∈ grsCode a v k ↔ ∃ p ∈ degreeLT F k, grsEval a v p = y :=
  Submodule.mem_map

omit [DecidableEq ι] in
/-- Reed–Solomon is the unit-multiplier instance. -/
theorem grsCode_one (a : ι → F) (k : ℕ) : grsCode a (fun _ => 1) k = rsCode a k := by
  have h : grsEval a (fun _ => 1) = rsEval a := by
    ext p i
    simp
  unfold grsCode rsCode
  rw [h]

/-- Diagonal scaling by everywhere-nonzero multipliers, as a linear equivalence. -/
noncomputable def scaleEquiv (v : ι → F) (hv : ∀ i, v i ≠ 0) : (ι → F) ≃ₗ[F] (ι → F) :=
  LinearEquiv.ofLinear
    { toFun := fun y i => v i * y i
      map_add' := fun y z => by funext i; simp only [Pi.add_apply]; ring
      map_smul' := fun c y => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
    { toFun := fun y i => (v i)⁻¹ * y i
      map_add' := fun y z => by funext i; simp only [Pi.add_apply]; ring
      map_smul' := fun c y => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
    (by
      ext y i
      simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        LinearMap.id_coe, id_eq]
      rw [← mul_assoc, mul_inv_cancel₀ (hv i), one_mul])
    (by
      ext y i
      simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        LinearMap.id_coe, id_eq]
      rw [← mul_assoc, inv_mul_cancel₀ (hv i), one_mul])

theorem grsCode_eq_map_scale (a : ι → F) {v : ι → F} (hv : ∀ i, v i ≠ 0) (k : ℕ) :
    grsCode a v k
      = Submodule.map (scaleEquiv v hv : (ι → F) →ₗ[F] (ι → F)) (rsCode a k) := by
  have h : grsEval a v
      = (scaleEquiv v hv : (ι → F) →ₗ[F] (ι → F)).comp (rsEval a) := by
    ext p i
    simp [scaleEquiv]
  unfold grsCode rsCode
  rw [h, Submodule.map_comp]

omit [DecidableEq ι] in
/-- GRS dimension, by transport of `finrank_rsCode` along the scaling equivalence. -/
theorem finrank_grsCode {a : ι → F} (ha : Function.Injective a) {v : ι → F}
    (hv : ∀ i, v i ≠ 0) {k : ℕ} (hkn : k ≤ Fintype.card ι) :
    Module.finrank F (grsCode a v k) = k := by
  classical
  rw [grsCode_eq_map_scale a hv k, LinearEquiv.finrank_map_eq]
  exact finrank_rsCode ha hkn

/-! ## The pinned dual multipliers and the moment identity -/

/-- The **dual multipliers**: the Lagrange leading coefficients
`uᵢ = (∏_{j≠i}(aᵢ − aⱼ))⁻¹` — pinned up to one global scalar. -/
noncomputable def dualMult (a : ι → F) : ι → F :=
  fun i => (∏ j ∈ Finset.univ.erase i, (a i - a j))⁻¹

omit [Fintype F] in
theorem dualMult_ne_zero {a : ι → F} (ha : Function.Injective a) (i : ι) :
    dualMult a i ≠ 0 := by
  apply inv_ne_zero
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (ha h.symm)

omit [Fintype F] in
/-- **The moment identity**: a polynomial of degree below `n − 1` is annihilated by the
dual multipliers across all `n` points — Mathlib's `Lagrange.coeff_eq_sum` read at a
vanishing coefficient. This single identity drives the whole duality theory. -/
theorem sum_dualMult_eval {a : ι → F} (ha : Function.Injective a) {P : Polynomial F}
    (hP : P.degree < ((Fintype.card ι - 1 : ℕ) : WithBot ℕ)) :
    ∑ i, dualMult a i * P.eval (a i) = 0 := by
  have hn : P.degree < ((Finset.univ : Finset ι).card : WithBot ℕ) := by
    rw [Finset.card_univ]
    exact lt_of_lt_of_le hP (by exact_mod_cast Nat.sub_le _ _)
  have h := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset ι)) (v := a) ha.injOn hn
  rw [Finset.card_univ, coeff_eq_zero_of_degree_lt hP, eq_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv, mul_comm]
  rfl

/-! ## Dual of GRS is GRS -/

/-- **Hall 5.1.6, machine-checked**: the dual of a GRS code is the GRS code with the
complementary dimension and the multipliers `u/v`. The `⊇` inclusion is the moment
identity applied to products `p·q` of degree `≤ n − 2`; equality is the dimension count
through `finrank_dualCode_add_finrank`. -/
theorem dualCode_grsCode {a : ι → F} (ha : Function.Injective a) {v : ι → F}
    (hv : ∀ i, v i ≠ 0) {k : ℕ} (hkn : k ≤ Fintype.card ι) :
    dualCode (grsCode a v k)
      = grsCode a (fun i => dualMult a i / v i) (Fintype.card ι - k) := by
  have hw : ∀ i, dualMult a i / v i ≠ 0 := fun i =>
    div_ne_zero (dualMult_ne_zero ha i) (hv i)
  have hle : grsCode a (fun i => dualMult a i / v i) (Fintype.card ι - k)
      ≤ dualCode (grsCode a v k) := by
    rintro y ⟨q, hq, rfl⟩
    rw [mem_dualCode]
    rintro x ⟨p, hp, rfl⟩
    have hpair : pairing (grsEval a v p) (grsEval a (fun i => dualMult a i / v i) q)
        = ∑ i, dualMult a i * (p * q).eval (a i) := by
      unfold pairing
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [grsEval_apply, grsEval_apply, eval_mul]
      calc v i * p.eval (a i) * (dualMult a i / v i * q.eval (a i))
          = v i * (v i)⁻¹ * (dualMult a i * (p.eval (a i) * q.eval (a i))) := by
            rw [div_eq_mul_inv]
            ring
        _ = dualMult a i * (p.eval (a i) * q.eval (a i)) := by
            rw [mul_inv_cancel₀ (hv i), one_mul]
    rw [hpair]
    rcases eq_or_ne (p * q) 0 with hpq | hpq
    · simp [hpq]
    · refine sum_dualMult_eval ha ?_
      have hp0 : p ≠ 0 := fun h => hpq (by rw [h, zero_mul])
      have hq0 : q ≠ 0 := fun h => hpq (by rw [h, mul_zero])
      have hpd := (natDegree_lt_iff_degree_lt hp0).mpr (Polynomial.mem_degreeLT.mp hp)
      have hqd := (natDegree_lt_iff_degree_lt hq0).mpr (Polynomial.mem_degreeLT.mp hq)
      rw [degree_eq_natDegree hpq, natDegree_mul hp0 hq0]
      have hlt : p.natDegree + q.natDegree < Fintype.card ι - 1 := by omega
      exact_mod_cast hlt
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_grsCode ha hw (Nat.sub_le _ _)]
  have h1 := finrank_dualCode_add_finrank (grsCode a v k)
  rw [finrank_grsCode ha hv hkn, Module.finrank_pi] at h1
  omega

/-- The `v ≡ 1` instance: **the actual dual of Reed–Solomon** — a genuinely-weighted GRS
code, never plain RS at proper-subset point families (the correct form of the naive claim
that the dual of RS is RS). -/
theorem dualCode_rsCode {a : ι → F} (ha : Function.Injective a) {k : ℕ}
    (hkn : k ≤ Fintype.card ι) :
    dualCode (rsCode a k) = grsCode a (dualMult a) (Fintype.card ι - k) := by
  rw [← grsCode_one, dualCode_grsCode ha (fun _ => one_ne_zero) hkn]
  congr 1
  funext i
  rw [div_one]

/-! ## The weighted parity check -/

/-- The **syndrome map**: the `u`-weighted moment functionals
`y ↦ (Σᵢ uᵢ aᵢʲ yᵢ)_{j < nk}`. -/
noncomputable def synMap (a : ι → F) (nk : ℕ) : (ι → F) →ₗ[F] (Fin nk → F) where
  toFun y := fun j => ∑ i, dualMult a i * a i ^ (j : ℕ) * y i
  map_add' y z := by
    funext j
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  map_smul' c y := by
    funext j
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

@[simp] theorem synMap_apply (a : ι → F) (nk : ℕ) (y : ι → F) (j : Fin nk) :
    synMap a nk y j = ∑ i, dualMult a i * a i ^ (j : ℕ) * y i := rfl

/-- **`rsCode = ker H`**: membership in the Reed–Solomon
code is exactly the vanishing of the `u`-weighted syndrome moments. (The UNWEIGHTED power
sums present the code only for constant-multiplier families; in general that form is
false.) This is the kernel presentation the syndrome-decoding layer (`synDecoder`) and the
codeword-checker netlist consume. -/
theorem rsCode_eq_ker_synMap {a : ι → F} (ha : Function.Injective a) {k : ℕ}
    (hkn : k ≤ Fintype.card ι) :
    rsCode a k = LinearMap.ker (synMap a (Fintype.card ι - k)) := by
  rw [← dualCode_dualCode (rsCode a k), dualCode_rsCode ha hkn]
  ext y
  rw [mem_dualCode, LinearMap.mem_ker]
  constructor
  · intro h
    funext j
    have hx : grsEval a (dualMult a) (X ^ (j : ℕ))
        ∈ grsCode a (dualMult a) (Fintype.card ι - k) := by
      refine mem_grsCode.mpr ⟨X ^ (j : ℕ), ?_, rfl⟩
      rw [Polynomial.mem_degreeLT, degree_X_pow]
      exact_mod_cast j.isLt
    have hj := h _ hx
    unfold pairing at hj
    rw [show (0 : Fin (Fintype.card ι - k) → F) j = 0 from rfl]
    rw [synMap_apply, ← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [grsEval_apply, eval_pow, eval_X]
  · intro h x hx
    obtain ⟨p, hp, rfl⟩ := mem_grsCode.mp hx
    rcases Nat.eq_zero_or_pos (Fintype.card ι - k) with hnk | hnk
    · rw [hnk] at hp
      have hp0 : p = 0 := by
        by_contra hne
        have := Polynomial.mem_degreeLT.mp hp
        rw [degree_eq_natDegree hne] at this
        exact absurd this (by simp)
      rw [hp0, map_zero]
      exact pairing_zero_left y
    · have hnat : p.natDegree < Fintype.card ι - k := by
        rcases eq_or_ne p 0 with rfl | hp0
        · simpa using hnk
        · exact (natDegree_lt_iff_degree_lt hp0).mpr (Polynomial.mem_degreeLT.mp hp)
      unfold pairing
      calc ∑ i, grsEval a (dualMult a) p i * y i
          = ∑ i, ∑ j ∈ Finset.range (Fintype.card ι - k),
              p.coeff j * (dualMult a i * a i ^ j * y i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [grsEval_apply, eval_eq_sum_range' hnat, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ j ∈ Finset.range (Fintype.card ι - k),
              p.coeff j * ∑ i, dualMult a i * a i ^ j * y i := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j hj => ?_
            have hcomp := congrFun h ⟨j, Finset.mem_range.mp hj⟩
            simp only [Pi.zero_apply] at hcomp
            rw [synMap_apply] at hcomp
            rw [show ((⟨j, Finset.mem_range.mp hj⟩ : Fin (Fintype.card ι - k)) : ℕ) = j
              from rfl] at hcomp
            rw [hcomp, mul_zero]

end ECCLib.Coding

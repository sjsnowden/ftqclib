/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import ECCLib.WeilGenerationComplete
import Mathlib.FieldTheory.Finiteness

set_option linter.unusedSectionVars false
-- As in `Heisenberg.lean`: the `Fintype`/`DecidableEq` instances are used in the proofs (delta
-- expansions sum over `ι → F`), not in the statements; the linter's suggestion does not apply.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The Weil character formula, scale-invariant form

The trace non-vanishing statement the canonical trace-1 section needs, in its scale-invariant form:
for a symplectic `g` and **any** Weil operator `W` (invertible intertwiner of the Schrödinger
representation with its `g`-twist),

* `weil_trace_mul_trace_inv` — `Tr(W) · Tr(W⁻¹) = #{v ∈ V | ḡ v = v}`, the number of fixed points
  of the induced symplectic map on `V = 𝔽_q^ι × 𝔽_q^ι`;
* `weilTrace_ne_zero` / `weilTraceInv_ne_zero` — hence `Tr(W) ≠ 0`: the fixed set contains `0`, so
  the product is a positive integer. This is the statement the `weilUnit` docstring defers to;
* `weil_trace_mul_trace_inv_q_pow` — the classical form `q^{dim ker(ḡ − 1)}` via `vecLin`;
* `weil_trace_mul_trace_inv_fourierMap` — the witness instance: at the Weyl element the fixed set
  is `{0}` (odd characteristic), so `Tr(𝓕)·Tr(𝓕⁻¹) = 1` — the Gauss-sum product `G·Ḡ = q` seen
  operator-theoretically.

The left side is invariant under `W ↦ c•W` (`c·c⁻¹ = 1`), and by `weil_operator_unique` every Weil
operator for `g` is such a rescaling — so the product is a well-defined invariant of `g` alone,
the absolute square of the Weil character with no unitarity smuggled in. (Do **not** state this as
`|Tr W|²`: that form is not scale-invariant and needs an inner product this library does not
use.)

**Route** (the twirl): average conjugation by the zero-centre section
over `V`. Schur (`operator_scalar_of_commutes`) makes the average scalar, `trace_mul_comm` pins the
scalar to `(n·Tr X)`, and the double count of `Σ_v Tr(W ρ_v W⁻¹ ρ_v⁻¹)` — once through the twirl,
once through the intertwining and trace orthogonality — gives the theorem. `ψ ≠ 1` is load-bearing
twice; `IsSymplectic.map_cen` is exactly what excludes the classical trace-zero intertwiners
(`W = ρ(h)`, `h` non-central, which shifts the centre by `symp(h,·)`).
-/

namespace ECCLib.WeilCharacter

open ECCLib.Heisenberg ECCLib.Siegel ECCLib.WeilComplete

variable {F : Type*} [Field F] [Fintype F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The trace in the delta basis, and trace orthogonality of the Weyl operators -/

open Classical in
/-- The trace of any endomorphism of `ℂ[𝔽_q^ι]` is its delta-diagonal sum — the general form of the
computation inlined in `trace_fourierOp`. -/
theorem trace_eq_sum_delta_diag (X : Module.End ℂ ((ι → F) → ℂ)) :
    LinearMap.trace ℂ ((ι → F) → ℂ) X = ∑ x : ι → F, X (delta x) x := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ι → F)), Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← delta_eq_basisFun]
  rfl

/-- `Tr(1) = |𝔽_q^ι|` — via the delta diagonal, no finrank bookkeeping. -/
theorem trace_one_end :
    LinearMap.trace ℂ ((ι → F) → ℂ) (1 : Module.End ℂ ((ι → F) → ℂ))
      = (Fintype.card (ι → F) : ℂ) := by
  classical
  rw [trace_eq_sum_delta_diag]
  have h : ∀ x : ι → F, (1 : Module.End ℂ ((ι → F) → ℂ)) (delta x) x = 1 := by
    intro x
    change delta x x = 1
    simp [delta]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]

open Classical in
/-- The Weyl operator moves deltas: `W(p,m) δ_x = ψ(½⟨m,p⟩)·ψ(⟨m,x−p⟩) • δ_{x−p}`. -/
theorem weyl_delta (ψ : AddChar F ℂ) (p m x : ι → F) :
    Heisenberg.weyl ψ p m (delta x)
      = (ψ ((2 : F)⁻¹ * pairing m p) * ψ (pairing m (x - p))) • delta (x - p) := by
  unfold Heisenberg.weyl
  rw [LinearMap.smul_apply, LinearMap.comp_apply, translation_delta, modulation_delta,
    smul_smul]

open Classical in
/-- **Trace orthogonality of the Weyl operators**: `Tr(W(p,m)) = n·δ_{(p,m),0}`. The diagonal is
empty unless `p = 0`; at `p = 0` the diagonal sum is a full character sum, zero unless `m = 0`. -/
theorem trace_weyl {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (p m : ι → F) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (Heisenberg.weyl ψ p m)
      = if p = 0 ∧ m = 0 then (Fintype.card (ι → F) : ℂ) else 0 := by
  rw [trace_eq_sum_delta_diag]
  by_cases hp : p = 0
  · subst hp
    by_cases hm : m = 0
    · subst hm
      rw [if_pos ⟨rfl, rfl⟩]
      have h : ∀ x : ι → F, Heisenberg.weyl ψ (0 : ι → F) (0 : ι → F) (delta x) x = 1 := by
        intro x
        rw [weyl_delta]
        simp [delta, pairing_zero_left]
      rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one]
    · rw [if_neg (fun hc => hm hc.2)]
      have h : ∀ x : ι → F, Heisenberg.weyl ψ (0 : ι → F) m (delta x) x = ψ (pairing x m) := by
        intro x
        rw [weyl_delta]
        simp only [pairing_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, sub_zero,
          Pi.smul_apply, smul_eq_mul]
        rw [delta, pairing_symm]
        simp
      rw [Finset.sum_congr rfl fun x _ => h x, sum_pairingChar_eq_zero hψ hm]
  · rw [if_neg (fun hc => hp hc.1)]
    have h : ∀ x : ι → F, Heisenberg.weyl ψ p m (delta x) x = 0 := by
      intro x
      rw [weyl_delta]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [delta, if_neg (fun hc => hp (sub_eq_self.mp hc.symm)), mul_zero]
    rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_const, smul_zero]

open Classical in
/-- **Trace of a Schrödinger element**: `Tr(ρ(p,m,c)) = ψ(c)·n·[p = 0 ∧ m = 0]`. -/
theorem trace_schrodinger (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) (y : Heis F ι) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (schrodinger h2 ψ y)
      = ψ y.cen * (if y.pos = 0 ∧ y.mom = 0 then (Fintype.card (ι → F) : ℂ) else 0) := by
  rw [schrodinger_apply, map_smul, trace_weyl hψ, smul_eq_mul]

/-! ## The zero-centre section and the twirl -/

/-- The zero-centre section `V → H(V)`, `v ↦ (v₁, v₂, 0)` — the set the Weyl operators are indexed
by. Not a homomorphism; its multiplicativity defect is central (`sec_mul`), which is exactly what
the twirl's phase cancellation consumes. -/
def sec (v : W F ι) : Heis F ι := ⟨v.1, v.2, 0⟩

@[simp] lemma sec_pos (v : W F ι) : (sec v : Heis F ι).pos = v.1 := rfl
@[simp] lemma sec_mom (v : W F ι) : (sec v : Heis F ι).mom = v.2 := rfl
@[simp] lemma sec_cen (v : W F ι) : (sec v : Heis F ι).cen = 0 := rfl

lemma sec_zero : (sec (0 : W F ι) : Heis F ι) = 1 := rfl

/-- The section's defect is central: `sec u · sec v = central(½ω(u,v)) · sec(u+v)`. -/
lemma sec_mul (u v : W F ι) :
    (sec u : Heis F ι) * sec v
      = Heis.central ((2 : F)⁻¹ * Heis.symp (sec u) (sec v)) * sec (u + v) := by
  refine Heis.ext ?_ ?_ ?_
  · simp [Heis.central]
  · simp [Heis.central]
  · simp only [Heis.mul_cen, sec_cen, Heis.central_cen, Heis.symp_central_left]
    ring

/-- `ρ(sec v)⁻¹-style cancellation`: `ρ(sec v) · ρ((sec v)⁻¹) = 1` — from the group structure, no
operator inverses. -/
lemma schrodinger_sec_mul_inv (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (v : W F ι) :
    schrodinger h2 ψ (sec v) * schrodinger h2 ψ ((sec v)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

lemma schrodinger_sec_inv_mul (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (v : W F ι) :
    schrodinger h2 ψ ((sec v)⁻¹) * schrodinger h2 ψ (sec v) = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

/-- Central elements invert centrally. -/
lemma central_inv (c : F) : (Heis.central c : Heis F ι)⁻¹ = Heis.central (-c) := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [Heis.central]

/-- **The conjugation step**: conjugating a twirl term by `ρ(sec u)` shifts its index — the two
central phases `ψ(±½ω)` cancel exactly. -/
lemma conj_sec_term (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (u v : W F ι)
    (X : Module.End ℂ ((ι → F) → ℂ)) :
    schrodinger h2 ψ (sec u) * (schrodinger h2 ψ (sec v) * X * schrodinger h2 ψ ((sec v)⁻¹))
        * schrodinger h2 ψ ((sec u)⁻¹)
      = schrodinger h2 ψ (sec (u + v)) * X * schrodinger h2 ψ ((sec (u + v))⁻¹) := by
  have hmul : schrodinger h2 ψ (sec u) * schrodinger h2 ψ (sec v)
      = ψ ((2 : F)⁻¹ * Heis.symp (sec u) (sec v)) • schrodinger h2 ψ (sec (u + v)) := by
    rw [← map_mul, sec_mul, map_mul, schrodinger_central, ← Module.End.one_eq_id,
      smul_mul_assoc, one_mul]
  have hinvmul : schrodinger h2 ψ ((sec v)⁻¹) * schrodinger h2 ψ ((sec u)⁻¹)
      = ψ (-((2 : F)⁻¹ * Heis.symp (sec u) (sec v))) • schrodinger h2 ψ ((sec (u + v))⁻¹) := by
    rw [← map_mul, ← mul_inv_rev, sec_mul, mul_inv_rev, central_inv, map_mul,
      schrodinger_central, ← Module.End.one_eq_id, mul_smul_comm, mul_one]
  calc schrodinger h2 ψ (sec u) * (schrodinger h2 ψ (sec v) * X * schrodinger h2 ψ ((sec v)⁻¹))
        * schrodinger h2 ψ ((sec u)⁻¹)
      = (schrodinger h2 ψ (sec u) * schrodinger h2 ψ (sec v)) * X
          * (schrodinger h2 ψ ((sec v)⁻¹) * schrodinger h2 ψ ((sec u)⁻¹)) := by
        noncomm_ring
    _ = (ψ ((2 : F)⁻¹ * Heis.symp (sec u) (sec v))
          * ψ (-((2 : F)⁻¹ * Heis.symp (sec u) (sec v))))
          • (schrodinger h2 ψ (sec (u + v)) * X * schrodinger h2 ψ ((sec (u + v))⁻¹)) := by
        rw [hmul, hinvmul]
        rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm (ψ _) (ψ _)]
    _ = schrodinger h2 ψ (sec (u + v)) * X * schrodinger h2 ψ ((sec (u + v))⁻¹) := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_smul]

/-- The twirl: averaging conjugation by the zero-centre section over `V`. -/
noncomputable def twirl (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ)
    (X : Module.End ℂ ((ι → F) → ℂ)) : Module.End ℂ ((ι → F) → ℂ) :=
  ∑ v : Siegel.W F ι, schrodinger h2 ψ (sec v) * X * schrodinger h2 ψ ((sec v)⁻¹)

/-- The twirl commutes with every Schrödinger operator. -/
lemma twirl_comm (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (X : Module.End ℂ ((ι → F) → ℂ))
    (x : Heis F ι) :
    twirl h2 ψ X * schrodinger h2 ψ x = schrodinger h2 ψ x * twirl h2 ψ X := by
  -- first for the section elements, by the index shift
  have hsec : ∀ u : W F ι,
      schrodinger h2 ψ (sec u) * twirl h2 ψ X = twirl h2 ψ X * schrodinger h2 ψ (sec u) := by
    intro u
    have hconj : schrodinger h2 ψ (sec u) * twirl h2 ψ X * schrodinger h2 ψ ((sec u)⁻¹)
        = twirl h2 ψ X := by
      unfold twirl
      rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun v _ => conj_sec_term h2 ψ u v X]
      exact Fintype.sum_equiv (Equiv.addLeft u)
        (fun v => schrodinger h2 ψ (sec (u + v)) * X * schrodinger h2 ψ ((sec (u + v))⁻¹))
        (fun v => schrodinger h2 ψ (sec v) * X * schrodinger h2 ψ ((sec v)⁻¹))
        (fun v => rfl)
    calc schrodinger h2 ψ (sec u) * twirl h2 ψ X
        = schrodinger h2 ψ (sec u) * twirl h2 ψ X
            * (schrodinger h2 ψ ((sec u)⁻¹) * schrodinger h2 ψ (sec u)) := by
          rw [schrodinger_sec_inv_mul, mul_one]
      _ = (schrodinger h2 ψ (sec u) * twirl h2 ψ X * schrodinger h2 ψ ((sec u)⁻¹))
            * schrodinger h2 ψ (sec u) := by rw [← mul_assoc]
      _ = twirl h2 ψ X * schrodinger h2 ψ (sec u) := by rw [hconj]
  -- then for a general element, whose operator is a scalar times a section operator
  have hx : schrodinger h2 ψ x = ψ x.cen • schrodinger h2 ψ (sec (x.pos, x.mom)) := by
    rw [schrodinger_apply, schrodinger_apply, sec_cen, AddChar.map_zero_eq_one, one_smul]
    rfl
  rw [hx, mul_smul_comm, smul_mul_assoc, hsec (x.pos, x.mom)]

/-- **The twirl is scalar, and the scalar is the trace**: `twirl X = (n · Tr X) • 1`. Schur gives
scalarity; cyclicity of the trace pins the constant. -/
theorem twirl_eq (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (X : Module.End ℂ ((ι → F) → ℂ)) :
    twirl h2 ψ X
      = ((Fintype.card (ι → F) : ℂ) * LinearMap.trace ℂ ((ι → F) → ℂ) X)
          • (1 : Module.End ℂ ((ι → F) → ℂ)) := by
  classical
  obtain ⟨c, hc⟩ := schrodinger_irreducible h2 hψ (twirl h2 ψ X)
    (fun x => twirl_comm h2 X x)
  -- trace of the twirl: each term has trace Tr X by cyclicity, and there are n² terms
  have htr : LinearMap.trace ℂ ((ι → F) → ℂ) (twirl h2 ψ X)
      = ((Fintype.card (ι → F) : ℂ)) ^ 2 * LinearMap.trace ℂ ((ι → F) → ℂ) X := by
    rw [twirl, map_sum]
    have hterm : ∀ v : Siegel.W F ι,
        LinearMap.trace ℂ ((ι → F) → ℂ)
          (schrodinger h2 ψ (sec v) * X * schrodinger h2 ψ ((sec v)⁻¹))
        = LinearMap.trace ℂ ((ι → F) → ℂ) X := by
      intro v
      rw [LinearMap.trace_mul_comm, ← mul_assoc, schrodinger_sec_inv_mul, one_mul]
    rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : (Fintype.card (W F ι) : ℂ) = ((Fintype.card (ι → F) : ℂ)) ^ 2 := by
      rw [Fintype.card_prod]
      push_cast
      ring
    rw [hcard]
  -- trace of c • 1 is c·n; cancel n
  have hn : (Fintype.card (ι → F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc1 : c • (LinearMap.id : Module.End ℂ ((ι → F) → ℂ)) = c • 1 := rfl
  rw [hc1] at hc
  have htr2 : LinearMap.trace ℂ ((ι → F) → ℂ) (twirl h2 ψ X)
      = c * (Fintype.card (ι → F) : ℂ) := by
    rw [hc, map_smul, trace_one_end, smul_eq_mul]
  have hkey : c = (Fintype.card (ι → F) : ℂ) * LinearMap.trace ℂ ((ι → F) → ℂ) X := by
    have h := htr2.symm.trans htr
    refine mul_right_cancel₀ hn ?_
    rw [h]
    ring
  rw [hc, hkey]

/-! ## The main theorem -/

open Classical in
/-- **The Weil character formula, scale-invariant form**: for a symplectic
`g` and any Weil operator `W`,
`Tr(W) · Tr(W⁻¹) = #{v ∈ V | ḡ v = v}` — the number of fixed points of the induced map on `V`.
The left side is invariant under `W ↦ c•W`, and by `weil_operator_unique` every Weil operator of
`g` is such a rescaling, so this is a well-defined invariant of `g` — the absolute square of the
Weil character, with no unitarity assumed. -/
theorem weil_trace_mul_trace_inv (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g)
    (W : (Module.End ℂ ((ι → F) → ℂ))ˣ)
    (hW : ∀ x, (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (g x) * (W : Module.End ℂ ((ι → F) → ℂ))) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (W : Module.End ℂ ((ι → F) → ℂ))
        * LinearMap.trace ℂ ((ι → F) → ℂ) ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
            Module.End ℂ ((ι → F) → ℂ))
      = (Fintype.card {v : Siegel.W F ι // vecFun g v = v} : ℂ) := by
  classical
  set n : ℂ := (Fintype.card (ι → F) : ℂ) with hn_def
  have hn : n ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the double-counted sum
  set S : ℂ := ∑ v : Siegel.W F ι, LinearMap.trace ℂ ((ι → F) → ℂ)
    ((W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (sec v)
      * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      * schrodinger h2 ψ ((sec v)⁻¹)) with hS_def
  -- way 1: through the twirl
  have hway1 : S = n * LinearMap.trace ℂ ((ι → F) → ℂ)
      ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
      * LinearMap.trace ℂ ((ι → F) → ℂ) (W : Module.End ℂ ((ι → F) → ℂ)) := by
    have hterm : ∀ v : Siegel.W F ι,
        LinearMap.trace ℂ ((ι → F) → ℂ)
          ((W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (sec v)
            * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
            * schrodinger h2 ψ ((sec v)⁻¹))
        = LinearMap.trace ℂ ((ι → F) → ℂ)
            (schrodinger h2 ψ (sec v)
              * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
              * schrodinger h2 ψ ((sec v)⁻¹) * (W : Module.End ℂ ((ι → F) → ℂ))) := by
      intro v
      rw [show (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (sec v)
            * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
            * schrodinger h2 ψ ((sec v)⁻¹)
          = (W : Module.End ℂ ((ι → F) → ℂ)) * (schrodinger h2 ψ (sec v)
            * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
            * schrodinger h2 ψ ((sec v)⁻¹)) from by simp only [mul_assoc]]
      rw [LinearMap.trace_mul_comm]
    rw [hS_def, Finset.sum_congr rfl fun v _ => hterm v]
    have hsum : ∑ v : Siegel.W F ι, (schrodinger h2 ψ (sec v)
          * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
          * schrodinger h2 ψ ((sec v)⁻¹) * (W : Module.End ℂ ((ι → F) → ℂ)))
        = twirl h2 ψ ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
            * (W : Module.End ℂ ((ι → F) → ℂ)) := by
      rw [twirl, Finset.sum_mul]
    rw [← map_sum, hsum, twirl_eq h2 hψ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  -- way 2: through the intertwining and trace orthogonality
  have hway2 : S = n * (Fintype.card {v : Siegel.W F ι // vecFun g v = v} : ℂ) := by
    have hconj : ∀ v : Siegel.W F ι,
        (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (sec v)
          * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        = schrodinger h2 ψ (g (sec v)) := by
      intro v
      rw [hW (sec v)]
      exact Units.mul_inv_cancel_right _ _
    have hterm : ∀ v : Siegel.W F ι,
        LinearMap.trace ℂ ((ι → F) → ℂ)
          ((W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ (sec v)
            * ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
            * schrodinger h2 ψ ((sec v)⁻¹))
        = if vecFun g v = v then n else 0 := by
      intro v
      rw [hconj v, ← map_mul, trace_schrodinger h2 hψ]
      by_cases hfix : vecFun g v = v
      · -- fixed: `g (sec v) = sec v`, so the element is `1`
        have hgs : g (sec v) = sec v := by
          have h1 : (g (sec v)).pos = v.1 := congrArg Prod.fst hfix
          have h2' : (g (sec v)).mom = v.2 := congrArg Prod.snd hfix
          exact Heis.ext h1 h2' (by rw [hg.map_cen, sec_cen])
        rw [hgs, mul_inv_cancel, if_pos hfix, Heis.one_cen, AddChar.map_zero_eq_one, one_mul,
          if_pos ⟨Heis.one_pos, Heis.one_mom⟩, hn_def]
      · -- not fixed: the pos/mom of the product are nonzero, the if kills the trace
        rw [if_neg hfix]
        have hne : ¬((g (sec v) * (sec v)⁻¹).pos = 0 ∧ (g (sec v) * (sec v)⁻¹).mom = 0) := by
          rintro ⟨hp, hm⟩
          apply hfix
          have hp' : (g (sec v)).pos = v.1 := by
            have := hp
            rw [Heis.mul_pos, Heis.inv_pos, sec_pos] at this
            linear_combination (norm := module) this
          have hm' : (g (sec v)).mom = v.2 := by
            have := hm
            rw [Heis.mul_mom, Heis.inv_mom, sec_mom] at this
            linear_combination (norm := module) this
          exact Prod.ext hp' hm'
        rw [if_neg hne, mul_zero]
    rw [hS_def, Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
    ring
  -- equate and cancel n
  have h := hway1.symm.trans hway2
  have h' : n * (LinearMap.trace ℂ ((ι → F) → ℂ)
        ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ))
        * LinearMap.trace ℂ ((ι → F) → ℂ) (W : Module.End ℂ ((ι → F) → ℂ)))
      = n * (Fintype.card {v : Siegel.W F ι // vecFun g v = v} : ℂ) := by
    rw [← mul_assoc]
    exact h
  have hcancel := mul_left_cancel₀ hn h'
  rw [mul_comm]
  exact hcancel

/-! ## Corollaries: nonvanishing, the `q^d` form, the witness -/

open Classical in
/-- The fixed set contains `0` (symplectic maps fix the identity), so the count is nonzero. -/
lemma card_fix_ne_zero {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    (Fintype.card {v : Siegel.W F ι // vecFun g v = v} : ℂ) ≠ 0 := by
  classical
  have h0 : vecFun g (0 : W F ι) = 0 := by
    have hone : g 1 = 1 := (Heis.symplecticHom hg).map_one
    have : (sec (0 : W F ι) : Heis F ι) = 1 := sec_zero
    unfold vecFun
    rw [show (⟨(0 : W F ι).1, (0 : W F ι).2, 0⟩ : Heis F ι) = 1 from sec_zero, hone]
    rfl
  haveI : Nonempty {v : Siegel.W F ι // vecFun g v = v} := ⟨⟨0, h0⟩⟩
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- **Trace non-vanishing** — the statement the canonical trace-1 section needs: the
trace of every Weil operator of every symplectic map is nonzero. -/
theorem weilTrace_ne_zero (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g)
    (W : (Module.End ℂ ((ι → F) → ℂ))ˣ)
    (hW : ∀ x, (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (g x) * (W : Module.End ℂ ((ι → F) → ℂ))) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (W : Module.End ℂ ((ι → F) → ℂ)) ≠ 0 := by
  have h := weil_trace_mul_trace_inv h2 hψ hg W hW
  intro hc
  rw [hc, zero_mul] at h
  exact card_fix_ne_zero hg h.symm

/-- The inverse trace is nonzero too. -/
theorem weilTraceInv_ne_zero (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g)
    (W : (Module.End ℂ ((ι → F) → ℂ))ˣ)
    (hW : ∀ x, (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (g x) * (W : Module.End ℂ ((ι → F) → ℂ))) :
    LinearMap.trace ℂ ((ι → F) → ℂ)
      ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) : Module.End ℂ ((ι → F) → ℂ)) ≠ 0 := by
  have h := weil_trace_mul_trace_inv h2 hψ hg W hW
  intro hc
  rw [hc, mul_zero] at h
  exact card_fix_ne_zero hg h.symm

open Classical in
/-- The fixed-point count in its classical form: `#Fix = q^{dim ker(ḡ − 1)}` — the fixed set is the
kernel of `vecLin hg − id`, an `F`-subspace. -/
theorem card_fix_eq_q_pow {g : Heis F ι → Heis F ι} (hg : Heis.IsSymplectic g) :
    (Fintype.card {v : Siegel.W F ι // vecFun g v = v})
      = Fintype.card F
          ^ Module.finrank F (LinearMap.ker (vecLin hg - LinearMap.id)) := by
  have hequiv : {v : Siegel.W F ι // vecFun g v = v}
      ≃ LinearMap.ker (vecLin hg - LinearMap.id (R := F) (M := W F ι)) := by
    refine Equiv.subtypeEquiv (Equiv.refl _) fun v => ?_
    simp only [Equiv.refl_apply, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    exact ⟨fun h => by rw [show vecLin hg v = vecFun g v from rfl, h],
      fun h => by rw [← show vecLin hg v = vecFun g v from rfl, h]⟩
  rw [Fintype.card_congr hequiv, Module.card_eq_pow_finrank (K := F)]

/-- **The witness instance** (`g = fourierMap`): the Weyl element fixes only `0` in odd
characteristic, so `Tr(W)·Tr(W⁻¹) = 1` for any of its Weil operators — the operator-theoretic face
of the Gauss-sum modulus `G·Ḡ = q`. -/
theorem weil_trace_mul_trace_inv_fourierMap (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (W : (Module.End ℂ ((ι → F) → ℂ))ˣ)
    (hW : ∀ x, (W : Module.End ℂ ((ι → F) → ℂ)) * schrodinger h2 ψ x
        = schrodinger h2 ψ (Heis.fourierMap x) * (W : Module.End ℂ ((ι → F) → ℂ))) :
    LinearMap.trace ℂ ((ι → F) → ℂ) (W : Module.End ℂ ((ι → F) → ℂ))
        * LinearMap.trace ℂ ((ι → F) → ℂ) ((W⁻¹ : (Module.End ℂ ((ι → F) → ℂ))ˣ) :
            Module.End ℂ ((ι → F) → ℂ))
      = 1 := by
  classical
  rw [weil_trace_mul_trace_inv h2 hψ (Heis.isSymplectic_fourierMap) W hW]
  norm_cast
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, by unfold vecFun Heis.fourierMap; simp⟩, ?_⟩
  rintro ⟨v, hv⟩
  have hfix : vecFun Heis.fourierMap v = v := hv
  unfold vecFun Heis.fourierMap at hfix
  simp only at hfix
  have h1 : v.2 = v.1 := congrArg Prod.fst hfix
  have h2' : -v.1 = v.2 := congrArg Prod.snd hfix
  have hv1 : v.1 = 0 := by
    have hneg : -v.1 = v.1 := by rw [h2', h1]
    have h2v : (2 : F) • v.1 = 0 := by
      rw [two_smul]
      linear_combination (norm := module) -hneg
    rcases smul_eq_zero.mp h2v with h | h
    · exact absurd h h2
    · exact h
  have hv2 : v.2 = 0 := by rw [h1, hv1]
  exact Subtype.ext (Prod.ext (by simp [hv1]) (by simp [hv2]))

end ECCLib.WeilCharacter

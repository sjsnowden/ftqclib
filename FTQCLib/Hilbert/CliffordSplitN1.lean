/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.AffineSymplecticGroup
import FTQCLib.Hilbert.GateLifts

set_option linter.unusedSectionVars false

/-! # The split case `n = 1`: `CliffordSectionExists 1`

The extension `1 → V → Clₙ/U(1) → Sp(2n,𝔽₂) → 1` splits exactly for `n ≤ 1` (Galindo 2026,
arXiv:2603.24743; Mastel 2023, arXiv:2307.05810; n=1 = `S₄ = V₄ ⋊ S₃`). This file discharges the
positive instance `CliffordSectionExists 1`, so `cliffordAffineEquiv` becomes an unconditional
`V ⋊ Sp(V) ≅ Cl₁/U(1)` at one qubit.

**Strategy.** A group-hom section of `Φ : Cl₁/U(1) → Sp(2,𝔽₂)` is the inverse of `Φ` restricted to
a complement `K ≅ Sp(2,𝔽₂)`. The complement is `K = ⟨[H], [X·S†]⟩`: two order-2 "Hadamard-type"
reflections `H = (X+Z)/√2` and `H_{XY} = (X+Y)/√2 = X·S†` (mod phase), at 60° so `([H][X·S†])³ = 1`,
generating `S₃ = Sp(2,2)`. -/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates

/-- **The section, from any bijective complement.** If a subgroup `K ≤ Clₙ/U(1)` maps bijectively
onto `Sp(V)` under `Φ`, then `Φ` splits — the section is `Φ|_K⁻¹` then inclusion, and the section
property is `Φ ∘ (Φ|_K)⁻¹ = id`. -/
theorem cliffordSectionExists_of_bijective_complement (n : ℕ)
    (K : Subgroup (cliffordModPhase n))
    (hbij : Function.Bijective ⇑((cliffordModPhaseToSp n).comp K.subtype)) :
    CliffordSectionExists n := by
  let e : K ≃* spSubgroup n := MulEquiv.ofBijective _ hbij
  refine ⟨K.subtype.comp e.symm.toMonoidHom, fun g => ?_⟩
  have hg : ((cliffordModPhaseToSp n).comp K.subtype) (e.symm g) = g := e.apply_symm_apply g
  simpa using hg

/-! ## The two complement generators `a = [H]`, `b = [X·S†]`

`H` and `S` are Cliffords (the gate-lift conjugation laws make them so); `X·S†` is the operator
`(X+Y)/√2` mod phase. -/

/-- `H = hadamardEquiv k` is a Clifford operator (from its conjugation law). -/
theorem isCliffordOperator_hadamardEquiv {n : ℕ} (k : Fin n) :
    IsCliffordOperator (hadamardEquiv k) := fun p => ⟨_, _, hadamardEquiv_conj k p⟩

/-- `S = phaseGate k` is a Clifford operator (from its conjugation law). -/
theorem isCliffordOperator_phaseGate {n : ℕ} (k : Fin n) :
    IsCliffordOperator (phaseGate k) := fun p => ⟨_, _, phaseGate_conj k p⟩

/-- `H` as an element of the single-qubit Clifford group. -/
noncomputable def cliffH : cliffordSubgroup 1 :=
  ⟨hadamardEquiv 0, isCliffordOperator_hadamardEquiv 0⟩

/-- `S` as an element of the single-qubit Clifford group. -/
noncomputable def cliffS : cliffordSubgroup 1 :=
  ⟨phaseGate 0, isCliffordOperator_phaseGate 0⟩

/-- `X` as an element of the single-qubit Clifford group. -/
noncomputable def cliffX : cliffordSubgroup 1 :=
  ⟨pauliEquiv (paulix 0), isCliffordOperator_pauliEquiv (paulix 0)⟩

/-- `b`'s underlying Clifford: `X·S†` (= `(X+Y)/√2` mod phase). -/
noncomputable def cliffXSinv : cliffordSubgroup 1 := cliffX * cliffS⁻¹

/-- First complement generator `a = [H] ∈ Cl₁/U(1)` (projects to the transposition `(X Z)`). -/
noncomputable def aN1 : cliffordModPhase 1 := QuotientGroup.mk cliffH

/-- Second complement generator `b = [X·S†] ∈ Cl₁/U(1)` (projects to the transposition `(X Y)`). -/
noncomputable def bN1 : cliffordModPhase 1 := QuotientGroup.mk cliffXSinv

/-- `a² = 1`: `H` is involutive (`H² = id`). -/
theorem aN1_mul_self : aN1 * aN1 = 1 := by
  have hH : cliffH * cliffH = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    apply LinearEquiv.ext
    intro ψ
    rw [LinearEquiv.mul_apply]
    change hadamardEquiv 0 (hadamardEquiv 0 ψ) = ψ
    rw [hadamardEquiv_apply, hadamardEquiv_apply, hadamardGate_involutive]
  rw [aN1, ← QuotientGroup.mk_mul, hH, QuotientGroup.mk_one]

/-- `-(π/2)·I` phase: `exp(I·(-(π/2·1))) = -i`. -/
theorem exp_neg_pi_div_two :
    Complex.exp (Complex.I * -(Real.pi / 2 * (1 : ℝ))) = -Complex.I := by
  have harg : Complex.I * -(Real.pi / 2 * (1 : ℝ)) = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
  push_cast; ring

/-- The action of `b`'s Clifford `X·S†` on a state: `(X·S†) χ w = e^{-i(π/2)(w₀+1)} · χ(w + e₀)`.
The phase carries the `-f` form `-(π/2 · ·)` of `(phaseGate 0).symm`. -/
theorem cliffXSinv_apply (χ : QubitSpace 1) (w : Fin 1 → ZMod 2) :
    cliffXSinv.val χ w
      = Complex.exp (Complex.I * -(Real.pi / 2 * (((w 0) + 1).val : ℝ)))
        * χ (w + Pi.single 0 1) := by
  have hval : cliffXSinv.val = pauliEquiv (paulix 0) * (phaseGate 0).symm := rfl
  rw [hval, LinearEquiv.mul_apply, pauliEquiv_apply, phaseGate, diagonalGateEquiv_symm_apply]
  unfold pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk, diagonalGate_apply]
  have hsub : w - (paulix (0 : Fin 1)).X = w + Pi.single 0 1 := by
    rw [show (paulix (0 : Fin 1)).X = Pi.single 0 1 from rfl]
    funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_same]
    rw [sub_eq_add_neg, show (-1 : ZMod 2) = 1 from by decide]
  have hzero : zDotVal (paulix (0 : Fin 1)) (w - (paulix (0 : Fin 1)).X) = 0 := by
    unfold zDotVal; simp [paulix]
  rw [hzero, pow_zero, one_mul, hsub]
  simp only [Pi.add_apply, Pi.single_eq_same]
  norm_cast

/-- `b² = 1`: `(X·S†)² = -i·I` (a global phase), so `[b]² = 1` in `Cl₁/U(1)`. -/
theorem bN1_mul_self : bN1 * bN1 = 1 := by
  have hop : (cliffXSinv * cliffXSinv).val.toLinearMap
      = (-Complex.I) • (1 : cliffordSubgroup 1).val.toLinearMap := by
    apply LinearMap.ext; intro ψ; funext v
    rw [LinearEquiv.coe_coe, Subgroup.coe_mul, LinearEquiv.mul_apply,
      cliffXSinv_apply, cliffXSinv_apply]
    simp only [Pi.add_apply, Pi.single_eq_same]
    have hvv : (v + Pi.single 0 1) + Pi.single 0 1 = v := by
      funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
      rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same]
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v 0) with h | h <;> rw [h] <;> decide
    have hval2 : ((v 0 + 1) + 1).val = (v 0).val := by
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v 0) with h | h <;> rw [h] <;> decide
    have hsum : Complex.I * -(Real.pi / 2 * (((v 0) + 1).val : ℝ))
        + Complex.I * -(Real.pi / 2 * ((v 0).val : ℝ))
        = Complex.I * -(Real.pi / 2 * (1 : ℝ)) := by
      have h1 : (((v 0) + 1).val : ℝ) + ((v 0).val : ℝ) = 1 := by
        have hn : ((v 0) + 1).val + (v 0).val = 1 := by
          rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v 0) with h | h <;> rw [h] <;> decide
        exact_mod_cast hn
      rw [← h1]; push_cast; ring
    rw [hvv, hval2, ← mul_assoc, ← Complex.exp_add, hsum, exp_neg_pi_div_two]
    simp [LinearMap.smul_apply, smul_eq_mul]
  rw [bN1, ← QuotientGroup.mk_mul,
    mk_eq_of_toLinearMap_smul' (neg_ne_zero.mpr Complex.I_ne_zero) hop, QuotientGroup.mk_one]

/-- A sum over `ZMod 2` is the two-term sum (local copy; the `GateLifts` one is private). -/
private theorem sum_zmod2' (f : ZMod 2 → ℂ) : ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- The action of `a·b`'s Clifford `H·X·S†` on a state, with the Hadamard sum evaluated over the two
`Fin 1` basis points `↦0`, `↦1`: `(H·X·S†) χ w = (1/√2)·(-i·χ(↦1) + (-1)^{w₀}·χ(↦0))`. -/
theorem cliffHXSinv_apply (χ : QubitSpace 1) (w : Fin 1 → ZMod 2) :
    (cliffH * cliffXSinv).val χ w
      = invSqrt2 * (-Complex.I * χ (Function.update w 0 1)
        + (-1 : ℂ) ^ (w 0).val * χ (Function.update w 0 0)) := by
  have hu0 : Function.update w 0 (0 : ZMod 2) + Pi.single 0 1 = Function.update w 0 1 := by
    funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]; decide
  have hu1 : Function.update w 0 (1 : ZMod 2) + Pi.single 0 1 = Function.update w 0 0 := by
    funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]; decide
  have ph0 : (((0 : ZMod 2) + 1).val : ℝ) = 1 := by
    rw [show ((0 : ZMod 2) + 1).val = 1 from by decide]; norm_num
  have ph1 : (((1 : ZMod 2) + 1).val : ℝ) = 0 := by
    rw [show ((1 : ZMod 2) + 1).val = 0 from by decide]; norm_num
  have e0 : (0 : ZMod 2).val = 0 := by decide
  have e1 : (1 : ZMod 2).val = 1 := by decide
  have phase0 : Complex.exp (Complex.I * -(Real.pi / 2 * (((0 : ZMod 2) + 1).val : ℝ)))
      = -Complex.I := by rw [ph0]; exact exp_neg_pi_div_two
  have phase1 : Complex.exp (Complex.I * -(Real.pi / 2 * (((1 : ZMod 2) + 1).val : ℝ)))
      = 1 := by rw [ph1]; simp
  have hval : (cliffH * cliffXSinv).val = hadamardEquiv 0 * cliffXSinv.val := rfl
  rw [hval, LinearEquiv.mul_apply, hadamardEquiv_apply, hadamardGate_apply, sum_zmod2',
    cliffXSinv_apply, cliffXSinv_apply]
  simp only [Function.update_self, hu0, hu1]
  rw [phase0, phase1]
  simp only [e0, e1, mul_zero, mul_one, pow_zero, one_mul]

/-- `(a·b)³ = 1`: `(H·X·S†)³ = invSqrt2·(1+i)·I` (= `e^{iπ/4}·I`), a global phase, so `[ab]³ = 1`.
The two order-2 reflections `a`, `b` (at 60°) compose to the order-3 rotation `(X Y Z)` of
`Sp(2,2) ≅ S₃`. Expanding the three Hadamard sums gives `2·invSqrt2³·(1+i)·χ(·)` (the cross term
cancels by pure algebra); then `2·invSqrt2³ = invSqrt2` via `invSqrt2² = 1/2`. -/
theorem abN1_pow_three : (aN1 * bN1) ^ 3 = 1 := by
  have hc : invSqrt2 * (1 + Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ (fun h => ?_)
    · rw [invSqrt2]; exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
    · simpa using congrArg Complex.im h
  have hs3 : invSqrt2 ^ 3 = 2⁻¹ * invSqrt2 := by rw [pow_succ, sq, invSqrt2_mul_self]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have key : ((cliffH * cliffXSinv) * ((cliffH * cliffXSinv)
      * (cliffH * cliffXSinv))).val.toLinearMap
      = (invSqrt2 * (1 + Complex.I)) • (1 : cliffordSubgroup 1).val.toLinearMap := by
    apply LinearMap.ext; intro ψ; funext v
    have fold : ∀ X : QubitSpace 1, cliffH.val (cliffXSinv.val X) = (cliffH * cliffXSinv).val X :=
      fun X => by rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
    simp only [LinearEquiv.coe_coe, Subgroup.coe_mul, LinearEquiv.mul_apply]
    simp only [fold, cliffHXSinv_apply, Function.update_idem, Function.update_self,
      show (0 : ZMod 2).val = 0 from by decide, show (1 : ZMod 2).val = 1 from by decide,
      pow_zero, pow_one, one_mul]
    have hrhs : ((invSqrt2 * (1 + Complex.I)) • (1 : cliffordSubgroup 1).val.toLinearMap) ψ v
        = invSqrt2 * (1 + Complex.I) * ψ v := by simp [LinearMap.smul_apply, smul_eq_mul]
    rw [hrhs]
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v 0) with hv | hv
    · have hvu : Function.update v 0 (0 : ZMod 2) = v := by
        funext i; obtain rfl : i = 0 := Subsingleton.elim i 0; rw [Function.update_self, hv]
      rw [hv, show (0 : ZMod 2).val = 0 from by decide, pow_zero, one_mul, hvu]
      ring_nf; simp only [hs3, hI2, hI3]; ring
    · have hvu : Function.update v 0 (1 : ZMod 2) = v := by
        funext i; obtain rfl : i = 0 := Subsingleton.elim i 0; rw [Function.update_self, hv]
      rw [hv, show (1 : ZMod 2).val = 1 from by decide, pow_one, hvu]
      ring_nf; simp only [hs3, hI2, hI3]; ring
  have hab : aN1 * bN1 = QuotientGroup.mk (cliffH * cliffXSinv) := by
    rw [aN1, bN1, QuotientGroup.mk_mul]
  rw [pow_three, hab, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    mk_eq_of_toLinearMap_smul' hc key, QuotientGroup.mk_one]

/-! ## Surjectivity of `Φ|_K`: the generators map to the symplectic gate set -/

/-- `Φ([H]) = hadamardAt 0` (the symplectic `X ↔ Z` swap), via the Hadamard conjugation law. -/
theorem cliffordToSp_cliffH : cliffordToSp cliffH = ⟨hadamardAt 0, hadamardAt_isClifford 0⟩ := by
  apply Subtype.ext
  refine LinearEquiv.ext fun p => ?_
  change cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv 0) p = hadamardAt 0 p
  exact (cliffordToSymplecticFun_unique (isCliffordOperator_hadamardEquiv 0) p
    (hadamardEquiv_conj 0 p)).symm

/-- `Φ([S]) = phaseAt 0`, via the phase-gate conjugation law. -/
theorem cliffordToSp_cliffS : cliffordToSp cliffS = ⟨phaseAt 0, phaseAt_isClifford 0⟩ := by
  apply Subtype.ext
  refine LinearEquiv.ext fun p => ?_
  change cliffordToSymplecticFun (isCliffordOperator_phaseGate 0) p = phaseAt 0 p
  exact (cliffordToSymplecticFun_unique (isCliffordOperator_phaseGate 0) p
    (phaseGate_conj 0 p)).symm

/-- `Φ([X]) = 1`: Paulis lie in `ker Φ`. -/
theorem cliffordToSp_cliffX : cliffordToSp cliffX = 1 :=
  MonoidHom.mem_ker.mp (pauliEquiv_mem_ker (paulix 0))

/-- The `S₃` complement `K = ⟨[H], [X·S†]⟩ ≤ Cl₁/U(1)`. -/
noncomputable def KN1 : Subgroup (cliffordModPhase 1) := Subgroup.closure {aN1, bN1}

/-- `Φ(aN1) = ⟨hadamardAt 0,…⟩` (the `mk`↦`cliffordToSp` bridge + the gate value). -/
theorem cliffordModPhaseToSp_aN1 :
    cliffordModPhaseToSp 1 aN1 = ⟨hadamardAt 0, hadamardAt_isClifford 0⟩ :=
  cliffordToSp_cliffH

/-- `Φ(bN1) = ⟨phaseAt 0,…⟩⁻¹` (`X ∈ ker Φ`, and `S†` inverts the phase gate). -/
theorem cliffordModPhaseToSp_bN1 :
    cliffordModPhaseToSp 1 bN1 = (⟨phaseAt 0, phaseAt_isClifford 0⟩ : spSubgroup 1)⁻¹ := by
  change cliffordToSp cliffXSinv = (⟨phaseAt 0, phaseAt_isClifford 0⟩ : spSubgroup 1)⁻¹
  rw [cliffXSinv, map_mul, map_inv, cliffordToSp_cliffX, cliffordToSp_cliffS, one_mul]

/-- `Φ` maps the complement `K` onto all of `Sp(2,2)`: the gate generators (`H`, `S`; CNOT/CZ
vacuous at one qubit) lie in `closure{Φ aN1, Φ bN1}`. -/
theorem phi_map_KN1_top : Subgroup.map (cliffordModPhaseToSp 1) KN1 = ⊤ := by
  have hgen : Subgroup.closure (cliffordGateGens 1) = ⊤ := spGeneratedByCliffordGates 1
  rw [KN1, MonoidHom.map_closure, Set.image_pair, cliffordModPhaseToSp_aN1,
    cliffordModPhaseToSp_bN1, eq_top_iff, ← hgen]
  refine (Subgroup.closure_le _).mpr (fun x hx => ?_)
  rcases hx with ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨i, j, hij, rfl⟩) | ⟨i, j, hij, rfl⟩
  · obtain rfl : k = 0 := Subsingleton.elim k 0
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · obtain rfl : k = 0 := Subsingleton.elim k 0
    have hmem : (⟨phaseAt 0, phaseAt_isClifford 0⟩ : spSubgroup 1)⁻¹
        ∈ Subgroup.closure {(⟨hadamardAt 0, hadamardAt_isClifford 0⟩ : spSubgroup 1),
          (⟨phaseAt 0, phaseAt_isClifford 0⟩ : spSubgroup 1)⁻¹} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    simpa using Subgroup.inv_mem _ hmem
  · exact absurd (Subsingleton.elim i j) hij
  · exact absurd (Subsingleton.elim i j) hij

/-- `Φ|_K` is surjective onto `Sp(2,2)`. -/
theorem phi_KN1_surjective :
    Function.Surjective ⇑((cliffordModPhaseToSp 1).comp KN1.subtype) := by
  intro g
  have hg : g ∈ Subgroup.map (cliffordModPhaseToSp 1) KN1 := by
    rw [phi_map_KN1_top]; exact Subgroup.mem_top g
  obtain ⟨k, hk, hkg⟩ := hg
  exact ⟨⟨k, hk⟩, hkg⟩

/-! ## Injectivity of `Φ|_K`: the Cayley closure `K ⊆ {1,a,b,ab,ba,aba}` -/

/-- `(ab)² = ba`, from `(ab)³ = 1` and `a² = b² = 1` (so `(ab)⁻¹ = ba`). -/
theorem aN1bN1_sq : (aN1 * bN1) ^ 2 = bN1 * aN1 := by
  have h2inv : (aN1 * bN1) ^ 2 = (aN1 * bN1)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact abN1_pow_three
  rw [h2inv, mul_inv_rev, inv_eq_of_mul_eq_one_right bN1_mul_self,
    inv_eq_of_mul_eq_one_right aN1_mul_self]

/-- The braid relation `aba = bab` (the `S₃` relation), from `(ab)² = ba`. -/
theorem aN1bN1aN1 : aN1 * bN1 * aN1 = bN1 * aN1 * bN1 := by
  have h : aN1 * bN1 * aN1 * bN1 = bN1 * aN1 := by
    have hsq := aN1bN1_sq; rw [pow_two, ← mul_assoc] at hsq; exact hsq
  have hrw : aN1 * bN1 * aN1 = aN1 * bN1 * aN1 * bN1 * bN1 := by
    rw [mul_assoc (aN1 * bN1 * aN1), bN1_mul_self, mul_one]
  rw [hrw, h]

/-- `abab = ba`. -/
theorem aN1bN1aN1bN1 : aN1 * bN1 * aN1 * bN1 = bN1 * aN1 := by
  have hsq := aN1bN1_sq; rw [pow_two, ← mul_assoc] at hsq; exact hsq

/-- The six elements of the `S₃` complement. -/
def sixSet : Set (cliffordModPhase 1) :=
  {1, aN1, bN1, aN1 * bN1, bN1 * aN1, aN1 * bN1 * aN1}

theorem mem_sixSet_one : (1 : cliffordModPhase 1) ∈ sixSet := by simp [sixSet]
theorem mem_sixSet_a : aN1 ∈ sixSet := by simp [sixSet]
theorem mem_sixSet_b : bN1 ∈ sixSet := by simp [sixSet]
theorem mem_sixSet_ab : aN1 * bN1 ∈ sixSet := by simp [sixSet]
theorem mem_sixSet_ba : bN1 * aN1 ∈ sixSet := by simp [sixSet]
theorem mem_sixSet_aba : aN1 * bN1 * aN1 ∈ sixSet := by simp [sixSet]

/-- `sixSet` is closed under multiplication: the `S₃` Cayley table, reduced by `a²=b²=1`,
`aba=bab`, `abab=ba`. -/
theorem sixSet_mul {x y : cliffordModPhase 1} (hx : x ∈ sixSet) (hy : y ∈ sixSet) :
    x * y ∈ sixSet := by
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  obtain rfl | rfl | rfl | rfl | rfl | rfl := hx <;>
    obtain rfl | rfl | rfl | rfl | rfl | rfl := hy
  · rw [one_mul]; exact mem_sixSet_one
  · rw [one_mul]; exact mem_sixSet_a
  · rw [one_mul]; exact mem_sixSet_b
  · rw [one_mul]; exact mem_sixSet_ab
  · rw [one_mul]; exact mem_sixSet_ba
  · rw [one_mul]; exact mem_sixSet_aba
  · rw [mul_one]; exact mem_sixSet_a
  · rw [aN1_mul_self]; exact mem_sixSet_one
  · exact mem_sixSet_ab
  · rw [← mul_assoc, aN1_mul_self, one_mul]; exact mem_sixSet_b
  · rw [← mul_assoc]; exact mem_sixSet_aba
  · rw [← mul_assoc, ← mul_assoc, aN1_mul_self, one_mul]; exact mem_sixSet_ba
  · rw [mul_one]; exact mem_sixSet_b
  · exact mem_sixSet_ba
  · rw [bN1_mul_self]; exact mem_sixSet_one
  · rw [← mul_assoc, ← aN1bN1aN1]; exact mem_sixSet_aba
  · rw [← mul_assoc, bN1_mul_self, one_mul]; exact mem_sixSet_a
  · rw [← mul_assoc, ← mul_assoc, ← aN1bN1aN1, mul_assoc (aN1 * bN1) aN1 aN1,
      aN1_mul_self, mul_one]; exact mem_sixSet_ab
  · rw [mul_one]; exact mem_sixSet_ab
  · exact mem_sixSet_aba
  · rw [mul_assoc, bN1_mul_self, mul_one]; exact mem_sixSet_a
  · rw [← mul_assoc, aN1bN1aN1bN1]; exact mem_sixSet_ba
  · rw [← mul_assoc, mul_assoc aN1 bN1 bN1, bN1_mul_self, mul_one, aN1_mul_self]
    exact mem_sixSet_one
  · rw [← mul_assoc, ← mul_assoc, aN1bN1aN1bN1, mul_assoc, aN1_mul_self, mul_one]
    exact mem_sixSet_b
  · rw [mul_one]; exact mem_sixSet_ba
  · rw [mul_assoc, aN1_mul_self, mul_one]; exact mem_sixSet_b
  · rw [← aN1bN1aN1]; exact mem_sixSet_aba
  · rw [← mul_assoc, mul_assoc bN1 aN1 aN1, aN1_mul_self, mul_one, bN1_mul_self]
    exact mem_sixSet_one
  · rw [← mul_assoc, ← aN1bN1aN1, mul_assoc (aN1 * bN1) aN1 aN1, aN1_mul_self, mul_one]
    exact mem_sixSet_ab
  · rw [← mul_assoc, ← mul_assoc, mul_assoc bN1 aN1 aN1, aN1_mul_self, mul_one, bN1_mul_self,
      one_mul]; exact mem_sixSet_a
  · rw [mul_one]; exact mem_sixSet_aba
  · rw [mul_assoc (aN1 * bN1) aN1 aN1, aN1_mul_self, mul_one]; exact mem_sixSet_ab
  · rw [aN1bN1aN1bN1]; exact mem_sixSet_ba
  · rw [← mul_assoc, mul_assoc (aN1 * bN1) aN1 aN1, aN1_mul_self, mul_one, mul_assoc aN1 bN1 bN1,
      bN1_mul_self, mul_one]; exact mem_sixSet_a
  · rw [← mul_assoc, aN1bN1aN1bN1, mul_assoc bN1 aN1 aN1, aN1_mul_self, mul_one]
    exact mem_sixSet_b
  · rw [← mul_assoc, ← mul_assoc, mul_assoc (aN1 * bN1) aN1 aN1, aN1_mul_self, mul_one,
      mul_assoc aN1 bN1 bN1, bN1_mul_self, mul_one, aN1_mul_self]; exact mem_sixSet_one

/-- `sixSet` is closed under inverses (`a⁻¹=a`, `b⁻¹=b`, `(ab)⁻¹=ba`, `(aba)⁻¹=aba`). -/
theorem sixSet_inv {x : cliffordModPhase 1} (hx : x ∈ sixSet) : x⁻¹ ∈ sixSet := by
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  obtain rfl | rfl | rfl | rfl | rfl | rfl := hx
  · rw [inv_one]; exact mem_sixSet_one
  · rw [inv_eq_of_mul_eq_one_right aN1_mul_self]; exact mem_sixSet_a
  · rw [inv_eq_of_mul_eq_one_right bN1_mul_self]; exact mem_sixSet_b
  · rw [mul_inv_rev, inv_eq_of_mul_eq_one_right bN1_mul_self,
      inv_eq_of_mul_eq_one_right aN1_mul_self]; exact mem_sixSet_ba
  · rw [mul_inv_rev, inv_eq_of_mul_eq_one_right aN1_mul_self,
      inv_eq_of_mul_eq_one_right bN1_mul_self]; exact mem_sixSet_ab
  · rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right aN1_mul_self,
      inv_eq_of_mul_eq_one_right bN1_mul_self, ← mul_assoc]; exact mem_sixSet_aba

/-- The `S₃` complement as an explicit 6-element subgroup. -/
def sixSubgroup : Subgroup (cliffordModPhase 1) where
  carrier := sixSet
  mul_mem' := sixSet_mul
  one_mem' := mem_sixSet_one
  inv_mem' := sixSet_inv

/-- **The Cayley closure**: `K = closure{a,b}` lies in the 6-element set. -/
theorem KN1_le_sixSubgroup : KN1 ≤ sixSubgroup := by
  rw [KN1]
  refine (Subgroup.closure_le sixSubgroup).mpr (fun x hx => ?_)
  rcases hx with rfl | rfl
  · exact mem_sixSet_a
  · exact mem_sixSet_b

/-- A symplectic element that moves some Pauli is not the identity. -/
private theorem sp_ne_one_of_moves (s : spSubgroup 1) (p : Pauli 1) (hp : s.val p ≠ p) :
    s ≠ 1 := fun h => hp (by rw [h]; rfl)

/-- `phaseAt 0` is a symplectic involution (an `𝔽₂` transvection), so `[S]`'s image is its own
inverse. -/
theorem phaseSp_self_inv :
    (⟨phaseAt 0, phaseAt_isClifford 0⟩ : spSubgroup 1)⁻¹
      = ⟨phaseAt 0, phaseAt_isClifford 0⟩ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv]
  exact LinearEquiv.ext fun _ => rfl

/-- **Injectivity of `Φ|_K`**: the 6 elements of `K` have distinct symplectic images, shown via the
kernel (only the identity maps to `1`); each non-identity word moves `X` or `Z`. -/
theorem phi_KN1_injective :
    Function.Injective ⇑((cliffordModPhaseToSp 1).comp KN1.subtype) := by
  refine (injective_iff_map_eq_one _).mpr (fun k hk => ?_)
  have hmem : (k : cliffordModPhase 1) ∈ sixSet := KN1_le_sixSubgroup k.2
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hk' : cliffordModPhaseToSp 1 (k : cliffordModPhase 1) = 1 := hk
  obtain h | h | h | h | h | h := hmem
  · exact Subtype.ext h
  · rw [h, cliffordModPhaseToSp_aN1] at hk'
    exact absurd hk' (sp_ne_one_of_moves _ (paulix 0) (fun heq => by
      have := congrArg (fun p : Pauli 1 => p.X 0) heq
      simp [hadamardAt_X, paulix_X, paulix_Z, Function.update_self] at this))
  · rw [h, cliffordModPhaseToSp_bN1, phaseSp_self_inv] at hk'
    exact absurd hk' (sp_ne_one_of_moves _ (paulix 0) (fun heq => by
      have := congrArg (fun p : Pauli 1 => p.Z 0) heq
      simp [phaseAt_Z, paulix_X, paulix_Z, Function.update_self] at this))
  · rw [h, map_mul, cliffordModPhaseToSp_aN1, cliffordModPhaseToSp_bN1, phaseSp_self_inv] at hk'
    exact absurd hk' (sp_ne_one_of_moves _ (paulix 0) (fun heq => by
      have := congrArg (fun p : Pauli 1 => p.Z 0) heq
      simp [Subgroup.coe_mul, LinearEquiv.mul_apply, hadamardAt_Z, phaseAt_X, phaseAt_Z, paulix_X,
        paulix_Z, Function.update_self] at this))
  · rw [h, map_mul, cliffordModPhaseToSp_bN1, cliffordModPhaseToSp_aN1, phaseSp_self_inv] at hk'
    exact absurd hk' (sp_ne_one_of_moves _ (paulix 0) (fun heq => by
      have := congrArg (fun p : Pauli 1 => p.X 0) heq
      simp [Subgroup.coe_mul, LinearEquiv.mul_apply, phaseAt_X, hadamardAt_X, paulix_X, paulix_Z,
        Function.update_self] at this))
  · rw [h, map_mul, map_mul, cliffordModPhaseToSp_aN1, cliffordModPhaseToSp_bN1,
      phaseSp_self_inv] at hk'
    exact absurd hk' (sp_ne_one_of_moves _ (pauliz 0) (fun heq => by
      have := congrArg (fun p : Pauli 1 => p.X 0) heq
      simp [Subgroup.coe_mul, LinearEquiv.mul_apply, hadamardAt_X, hadamardAt_Z, phaseAt_X,
        phaseAt_Z, pauliz_X, pauliz_Z, Function.update_self] at this))

/-- **`CliffordSectionExists 1`** — the positive instance of the splitting:
`Φ : Cl₁/U(1) → Sp(2,𝔽₂)` splits.
The complement `K = ⟨[H], [X·S†]⟩ ≅ S₃` maps bijectively onto `Sp(2,2)`. -/
theorem cliffordSectionExists_one : CliffordSectionExists 1 :=
  cliffordSectionExists_of_bijective_complement 1 KN1 ⟨phi_KN1_injective, phi_KN1_surjective⟩

/-! ## Construction summary — the proof of `CliffordSectionExists 1`

The section is `cliffordSectionExists_of_bijective_complement 1 KN1 hbij` for `KN1 = ⟨aN1, bN1⟩`.
The obligations and how each is discharged:

**Relations (cleanest via the group structure, not raw operators).** Use `conjBridge` /
`mk_conj_cliffordPauli` (conjugating a Pauli class by `[U]` applies `Φ(U)` to the vector), plus the
gates' symplectic actions and `pauliModPhase` (a hom, so `[P][Q] = pauliModPhase(p+q)`):
* `aN1² = 1` — `aN1_mul_self` (`H² = id`).
* `bN1² = 1` — `bN1_mul_self`. Operator route: `X·S†` acts as
  `χ w ↦ e^{-i(π/2)(w₀+1)}·χ(w + e₀)` (`cliffXSinv_apply`), so `(X·S†)² = -i·I`
  (the two phase exponents `(w₀+1)` and `w₀` sum to `1` for both `w₀∈{0,1}`); then
  `mk_eq_of_toLinearMap_smul' (c := -i)` kills the global phase, giving `[b]² = 1`.
  (Group cross-check: `[b]² = [X][Y][Z] = pauliModPhase ((1,0)+(1,1)+(0,1)) = 1`.)
* `(aN1·bN1)³ = 1` — `abN1_pow_three`. `ab` projects to the 3-cycle
  `(X Z)(X Y) = (X Y Z)` (order 3 in `Sp(2,2)`), and at the operator level `(H·X·S†)³ = e^{iπ/4}·I`
  (`= invSqrt2·(1+i)·I`, a global phase — two 60° reflections compose to a 120° rotation), so the
  `V`-component is `0`. Realized by `cliffHXSinv_apply` (the `H·X·S†` action with the Hadamard sum
  evaluated over the two `Fin 1` basis points); the three nested Hadamard sums expand (a `fold`
  lemma keeps `cliffH·cliffXSinv` together against `Subgroup.coe_mul`) to `2·invSqrt2³·(1+i)·χ(·)`,
  then `invSqrt2³ = invSqrt2/2` and `I²=-1` (`ring_nf` + power reductions) close it.

**Surjectivity of `Φ|_K`** (`phi_map_KN1_top`, `phi_KN1_surjective`). `Φ(aN1) = hadamardAt 0`
(`cliffordModPhaseToSp_aN1`) and `Φ(bN1) = ⟨phaseAt 0,_⟩⁻¹` (`X ∈ ker Φ`); the gate generators lie
in `closure{Φ aN1, Φ bN1}`, and `spGeneratedByCliffordGates 1` (n=1 gate set `{H, S}`; CNOT/CZ
vacuous) gives `Subgroup.map Φ KN1 = ⊤` via `MonoidHom.map_closure`.

**Injectivity of `Φ|_K`** (`phi_KN1_injective`; no `Fintype (Cl₁/U(1))`, so via an explicit
Cayley closure). `KN1 ≤ sixSubgroup = {1,a,b,ab,ba,aba}` (`KN1_le_sixSubgroup`), the `S₃` table
closed under `·`/`⁻¹` from `a²=b²=1`, `aba=bab`, `abab=ba` (`sixSet_mul`/`sixSet_inv`, the 36+6
cases). Then `ker(Φ|_K)` is trivial: each non-identity word moves `X` or `Z` symplectically.
`decide` is unavailable on the `𝔽₂`-`LinearEquiv`, so this is by component (`hadamardAt_X/Z`,
`phaseAt_X/Z`, with `(phaseAt 0)⁻¹ = phaseAt 0` as `phaseAt` is an `𝔽₂` involution).

**Assembly** (`cliffordSectionExists_one`): `cliffordSectionExists_of_bijective_complement 1
KN1 ⟨injective, surjective⟩`. So `cliffordAffineEquiv 1 cliffordSectionExists_one :
affineSymplecticGroup 1 ≃* cliffordModPhase 1` is unconditional — the positive instance
`V ⋊ Sp(V) ≅ Cl₁/U(1)` (for `n ≥ 2` the extension is non-split, as cited above). -/

end FTQCLib.Hilbert

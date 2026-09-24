/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.SignedCharacter
import FTQCLib.Hilbert.CliffordSplitN1

set_option linter.unusedSectionVars false

/-!
# Witnesses for the signed character formula: the concrete gate lifts

Two-route witnesses for the signed character formula of `SignedCharacter.lean`:

* **Hadamard (any `n`, any qubit `k`) — the vanishing branch.** The label `Y_k = X_k + Z_k` is
  fixed by `hadamardAt k` and its sign is `−1`, so `Tr(H) = Tr(H⁻¹) = 0` — by the main theorem
  (`trace_eq_zero_of_fixed_sign_neg`, route B) *and* by direct computation
  (`hadamardGate_eq`: `H = (X + Z)/√2`, traceless termwise — route A). The `μ(Y_k) = −1` pin is
  extracted **without any matrix evaluation**: `μ(X_k) = μ(Z_k) = 1` come from the conjugation
  laws with *zero* phase exponents (`pow_zero` collapses the opaque phase units), and the cocycle
  law plus `pauliPhase` antisymmetry (`X_k`, `Z_k` anticommute) forces `μ(Y_k) = −1`.
* **Phase gate `S` (`n = 1`) — a nontrivial attained count**: the fixed set is `{1, Z}` with
  trivial sign, so `Tr(S)·Tr(S⁻¹) = 2`.
* **CNOT (`n = 2`) — rank 2, entangling**: fixed set `⟨X₂, Z₁⟩` (the labels with `X` clear on the
  control and `Z` clear on the target), trivial sign, product `= 4`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates Complex

variable {n : ℕ}

/-! ## Trace transport `QState ↔ QubitSpace`, and Pauli operator traces -/

/-- `qClifford` is the `toQState`-conjugate, so traces agree. -/
theorem trace_qClifford (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    LinearMap.trace ℂ (QState n) (qClifford U).toLinearMap
      = LinearMap.trace ℂ (QubitSpace n) U.toLinearMap := by
  have h : (qClifford U).toLinearMap = (toQState.conj (U.toLinearMap) :
      QState n →ₗ[ℂ] QState n) := by
    refine LinearMap.ext fun ψ => ?_
    simp [LinearEquiv.conj_apply]
  rw [h, LinearMap.trace_conj']

/-- Inverse-side transport. -/
theorem trace_qClifford_symm (U : QubitSpace n ≃ₗ[ℂ] QubitSpace n) :
    LinearMap.trace ℂ (QState n) (qClifford U).symm.toLinearMap
      = LinearMap.trace ℂ (QubitSpace n) U.symm.toLinearMap := by
  have h : (qClifford U).symm.toLinearMap = (qClifford U.symm).toLinearMap := by
    refine LinearMap.ext fun ψ => ?_
    rfl
  rw [h, trace_qClifford]

/-- The trace of a bare Pauli operator: `2ⁿ` at the identity label, `0` elsewhere — from the
Hermitian trace by unwinding the `Iˣᶻ` dressing. -/
theorem trace_pauliOperator (p : Pauli n) :
    LinearMap.trace ℂ (QubitSpace n) (pauliOperator p)
      = if p = 0 then (2 : ℂ) ^ n else 0 := by
  have hq : qPauli p = (toQState.conj ((pauliOperator p : QubitSpace n →ₗ[ℂ] QubitSpace n)) :
      QState n →ₗ[ℂ] QState n) := by
    refine LinearMap.ext fun ψ => ?_
    simp [qPauli_apply, LinearEquiv.conj_apply]
  have htr : LinearMap.trace ℂ (QState n) (qPauli p)
      = LinearMap.trace ℂ (QubitSpace n) (pauliOperator p) := by
    rw [hq, LinearMap.trace_conj']
  have hHq : qPauli p = (Complex.I ^ xzWeight p)⁻¹ • pauliHermitian p := by
    rw [pauliHermitian, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ I_ne_zero), one_smul]
  have h2 : LinearMap.trace ℂ (QState n) (qPauli p)
      = (Complex.I ^ xzWeight p)⁻¹ * (if p = 0 then (2 : ℂ) ^ n else 0) := by
    rw [hHq, map_smul, smul_eq_mul, pauliHermitian_trace]
  rw [← htr, h2]
  by_cases hp : p = 0
  · subst hp
    have hxz : xzWeight (0 : Pauli n) = 0 := by simp [xzWeight, zDotVal]
    simp [hxz]
  · simp [hp]

/-! ## The sign-pinning kit -/

/-- Pin `cliffordSign` from an explicit conjugation law. -/
theorem cliffordSign_eq_of_conj {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {p q : Pauli n} {α : ℂˣ}
    (hconj : (conjEquiv U (pauliEquiv p)).toLinearMap = (α : ℂ) • pauliOperator q) :
    cliffordSign hU p
      = Complex.I ^ xzWeight p * (α : ℂ) * (Complex.I ^ xzWeight q)⁻¹ := by
  have hfun := cliffordToSymplecticFun_unique hU p hconj
  have hphase := cliffordToSymplecticPhase_unique hU p hconj
  rw [cliffordSign, ← hphase, ← hfun]

/-- Pin the symplectic image from an explicit conjugation law. -/
theorem cliffordFun_eq_of_conj {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) {p q : Pauli n} {α : ℂˣ}
    (hconj : (conjEquiv U (pauliEquiv p)).toLinearMap = (α : ℂ) • pauliOperator q) :
    cliffordToSymplecticFun hU p = q :=
  (cliffordToSymplecticFun_unique hU p hconj).symm

/-! ## The Hadamard witness (any `n`, any qubit `k`) — the vanishing branch -/

section Hadamard

variable (k : Fin n)

/-- `X_k` weights: `xzWeight (paulix k) = 0` (no `Z` support). -/
lemma xzWeight_paulix : xzWeight (paulix k) = 0 := by
  simp [xzWeight, zDotVal]

/-- `Z_k` weights: `xzWeight (pauliz k) = 0` (no `X` support). -/
lemma xzWeight_pauliz : xzWeight (pauliz k) = 0 := by
  simp [xzWeight, zDotVal]

/-- The `Y` label at qubit `k`. -/
noncomputable def yLabel : Pauli n := paulix k + pauliz k

/-- `Y_k` has unit `xz`-weight: the single overlapping coordinate. -/
lemma xzWeight_yLabel : xzWeight (yLabel k) = 1 := by
  unfold xzWeight zDotVal yLabel
  rw [Finset.sum_eq_single k]
  · simp
    decide
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- `hadamardAt` swaps `X_k ↦ Z_k`. -/
lemma hadamardAt_paulix : hadamardAt k (paulix k) = pauliz k := by
  refine Pauli.ext ?_ ?_
  · rw [hadamardAt_X, paulix_X, paulix_Z, pauliz_X]
    funext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Function.update_of_ne hik, Pi.single_eq_of_ne hik]
  · rw [hadamardAt_Z, paulix_X, paulix_Z, pauliz_Z]
    funext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Function.update_of_ne hik, Pi.single_eq_of_ne hik]

/-- `hadamardAt` swaps `Z_k ↦ X_k`. -/
lemma hadamardAt_pauliz : hadamardAt k (pauliz k) = paulix k := by
  refine Pauli.ext ?_ ?_
  · rw [hadamardAt_X, pauliz_X, pauliz_Z, paulix_X]
    funext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Function.update_of_ne hik, Pi.single_eq_of_ne hik]
  · rw [hadamardAt_Z, pauliz_X, pauliz_Z, paulix_Z]
    funext i
    by_cases hik : i = k
    · subst hik; simp
    · simp [Function.update_of_ne hik, Pi.single_eq_of_ne hik]

/-- `hadamardAt` fixes `Y_k` (both bits set at `k`; the swap is invisible). -/
lemma hadamardAt_yLabel : hadamardAt k (yLabel k) = yLabel k := by
  unfold yLabel
  rw [map_add, hadamardAt_paulix, hadamardAt_pauliz, add_comm]

/-- `μ(X_k) = 1`: the conjugation phase exponent is `X·Z = 1·0 = 0`, so the opaque phase unit is
`u⁰ = 1` — no access to the phase unit's value is needed. -/
lemma cliffordSign_hadamard_paulix :
    cliffordSign (isCliffordOperator_hadamardEquiv k) (paulix k) = 1 := by
  have hconj := hadamardEquiv_conj k (paulix k)
  rw [show ((paulix k).X k).val * ((paulix k).Z k).val = 0 from by
      rw [paulix_Z]; simp, pow_zero] at hconj
  have h := cliffordSign_eq_of_conj (isCliffordOperator_hadamardEquiv k) hconj
  rw [h, hadamardAt_paulix, xzWeight_paulix, xzWeight_pauliz]
  simp

/-- `μ(Z_k) = 1`, symmetrically. -/
lemma cliffordSign_hadamard_pauliz :
    cliffordSign (isCliffordOperator_hadamardEquiv k) (pauliz k) = 1 := by
  have hconj := hadamardEquiv_conj k (pauliz k)
  rw [show ((pauliz k).X k).val * ((pauliz k).Z k).val = 0 from by
      rw [pauliz_X]; simp, pow_zero] at hconj
  have h := cliffordSign_eq_of_conj (isCliffordOperator_hadamardEquiv k) hconj
  rw [h, hadamardAt_pauliz, xzWeight_pauliz, xzWeight_paulix]
  simp

/-- The symplectic image pins for the generators. -/
lemma cliffordFun_hadamard_paulix :
    cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv k) (paulix k) = pauliz k := by
  have h := cliffordFun_eq_of_conj (isCliffordOperator_hadamardEquiv k)
    (hadamardEquiv_conj k (paulix k))
  rw [h, hadamardAt_paulix]

lemma cliffordFun_hadamard_pauliz :
    cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv k) (pauliz k) = paulix k := by
  have h := cliffordFun_eq_of_conj (isCliffordOperator_hadamardEquiv k)
    (hadamardEquiv_conj k (pauliz k))
  rw [h, hadamardAt_pauliz]

lemma cliffordFun_hadamard_yLabel :
    cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv k) (yLabel k) = yLabel k := by
  have h := cliffordFun_eq_of_conj (isCliffordOperator_hadamardEquiv k)
    (hadamardEquiv_conj k (yLabel k))
  rw [h, hadamardAt_yLabel]

/-- The anticommutation exponent of `(X_k, Z_k)` is odd: `e = 0 + 1`. -/
lemma zDotVal_pauliz_single : zDotVal (pauliz k) (Pi.single k 1) = 1 := by
  unfold zDotVal
  rw [Finset.sum_eq_single k]
  · simp
    decide
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **`μ(Y_k) = −1`, from sign bookkeeping alone.** The cocycle law at `(X_k, Z_k)` reads
`μ(X)·μ(Z)·pauliPhase(Z, X) = μ(Y)·pauliPhase(X, Z)`, and `pauliPhase` antisymmetry across the
anticommuting pair contributes the `−1`. No operator is ever evaluated. -/
theorem cliffordSign_hadamard_yLabel :
    cliffordSign (isCliffordOperator_hadamardEquiv k) (yLabel k) = -1 := by
  have hc := cliffordSign_cocycle (isCliffordOperator_hadamardEquiv k) (paulix k) (pauliz k)
  rw [cliffordSign_hadamard_paulix, cliffordSign_hadamard_pauliz, cliffordFun_hadamard_paulix,
    cliffordFun_hadamard_pauliz, one_mul, one_mul] at hc
  -- `hc : pauliPhase (pauliz k) (paulix k) = μ(Y)·pauliPhase (paulix k) (pauliz k)`
  have hswap := pauliPhase_swap (paulix k) (pauliz k)
  rw [show zDotVal (paulix k) (pauliz k).X + zDotVal (pauliz k) (paulix k).X = 1 from by
      rw [pauliz_X, paulix_X, zDotVal_pauliz_single]
      simp [zDotVal], pow_one] at hswap
  rw [hswap] at hc
  have hne := pauliPhase_ne_zero (paulix k) (pauliz k)
  have hμ := mul_right_cancel₀ hne hc.symm
  exact hμ

/-- **The Hadamard witness, route B (main theorem)**: both traces vanish, by the
individual-vanishing theorem at the fixed label `Y_k` — no trace is ever computed. -/
theorem hadamard_trace_eq_zero_general :
    LinearMap.trace ℂ (QState n) (qClifford (hadamardEquiv k)).toLinearMap = 0
      ∧ LinearMap.trace ℂ (QState n) (qClifford (hadamardEquiv k)).symm.toLinearMap = 0 :=
  trace_eq_zero_of_fixed_sign_neg (isCliffordOperator_hadamardEquiv k)
    (cliffordFun_hadamard_yLabel k) (cliffordSign_hadamard_yLabel k)

/-- **The Hadamard witness, route A (independent)**: `Tr(H) = 0` by direct computation —
`H = (X + Z)/√2` termwise traceless. Never touches the signed formula. -/
theorem hadamard_trace_eq_zero_independent :
    LinearMap.trace ℂ (QubitSpace n) (hadamardEquiv k).toLinearMap = 0 := by
  have h : (hadamardEquiv k).toLinearMap = hadamardGate k := by
    refine LinearMap.ext fun ψ => ?_
    rfl
  have hx : paulix k ≠ (0 : Pauli n) := by
    intro hc
    have := congrArg (fun p : Pauli n => p.X k) hc
    simp [paulix_X] at this
  have hz : pauliz k ≠ (0 : Pauli n) := by
    intro hc
    have := congrArg (fun p : Pauli n => p.Z k) hc
    simp [pauliz_Z] at this
  rw [h, hadamardGate_eq, map_smul, map_add, trace_pauliOperator, trace_pauliOperator,
    if_neg hx, if_neg hz, add_zero, smul_eq_mul, mul_zero]

/-- The two routes meet: transported to `QubitSpace`, route B's zero is route A's zero. -/
theorem hadamard_witness_routes_agree :
    LinearMap.trace ℂ (QState n) (qClifford (hadamardEquiv k)).toLinearMap
      = LinearMap.trace ℂ (QubitSpace n) (hadamardEquiv k).toLinearMap := by
  rw [(hadamard_trace_eq_zero_general k).1, hadamard_trace_eq_zero_independent]

end Hadamard


/-! ## Trace on `QubitSpace` in the delta basis -/

open Classical in
/-- The delta-diagonal trace on `QubitSpace n`. -/
theorem trace_qubit_eq_sum_diag (X : QubitSpace n →ₗ[ℂ] QubitSpace n) :
    LinearMap.trace ℂ (QubitSpace n) X
      = ∑ v : Fin n → ZMod 2, X ((Pi.basisFun ℂ (Fin n → ZMod 2)) v) v := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n → ZMod 2)), Matrix.trace]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rfl

/-! ## The phase-gate witness (`n = 1`) — a nontrivial attained count -/

section PhaseWitness

/-- The fixed labels of `phaseAt k` are exactly those with no `X` at `k`. -/
lemma phaseAt_fixed_iff (k : Fin n) (p : Pauli n) :
    phaseAt k p = p ↔ p.X k = 0 := by
  constructor
  · intro h
    have hZ := congrArg (fun q : Pauli n => q.Z k) h
    simp only [phaseAt_Z, Function.update_self] at hZ
    have h' : p.Z k + p.X k = p.Z k + 0 := by rw [add_zero]; exact hZ
    exact add_left_cancel h'
  · intro h
    refine Pauli.ext ?_ ?_
    · rw [phaseAt_X]
    · rw [phaseAt_Z, h, add_zero, Function.update_eq_self]

/-- The phase gate's symplectic image is `phaseAt`, at every label. -/
lemma cliffordFun_phase (k : Fin n) (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_phaseGate k) p = phaseAt k p :=
  cliffordFun_eq_of_conj _ (phaseGate_conj k p)

/-- The sign is trivial on every fixed label: the phase exponent is `(p.X k).val = 0`. -/
lemma cliffordSign_phase_of_fixed (k : Fin n) (p : Pauli n) (hp : p.X k = 0) :
    cliffordSign (isCliffordOperator_phaseGate k) p = 1 := by
  have hconj := phaseGate_conj k p
  rw [show (p.X k).val = 0 from by rw [hp]; decide, pow_zero] at hconj
  have h := cliffordSign_eq_of_conj (isCliffordOperator_phaseGate k) hconj
  rw [h, show phaseAt k p = p from (phaseAt_fixed_iff k p).mpr hp, Units.val_one, mul_one,
    mul_inv_cancel₀ (pow_ne_zero _ I_ne_zero)]

/-- The fixed subtype at `n = 1` is a copy of `ZMod 2` (the free `Z` bit). -/
noncomputable def phaseFixedEquiv : {p : Pauli 1 // p.X 0 = 0} ≃ ZMod 2 where
  toFun p := p.1.Z 0
  invFun z := ⟨{ X := 0, Z := fun _ => z }, rfl⟩
  left_inv := fun ⟨p, hp⟩ => by
    refine Subtype.ext (Pauli.ext ?_ ?_)
    · funext i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact hp.symm
    · funext i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      rfl
  right_inv := fun z => rfl

open Classical in
/-- The fixed-set count at `n = 1` is `2`. -/
lemma card_fixed_phase :
    (Finset.univ.filter (fun p : Pauli 1 =>
      cliffordToSymplecticFun (isCliffordOperator_phaseGate (0 : Fin 1)) p = p)).card = 2 := by
  have hpred : ∀ p : Pauli 1,
      (cliffordToSymplecticFun (isCliffordOperator_phaseGate (0 : Fin 1)) p = p)
        ↔ p.X 0 = 0 := by
    intro p
    rw [cliffordFun_phase]
    exact phaseAt_fixed_iff 0 p
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr ((Equiv.subtypeEquivRight hpred).trans phaseFixedEquiv), ZMod.card]

open Classical in
/-- **The `S` witness, route B (main theorem)**: trivial sign on a 2-element fixed set forces the
trace product to `2` through the main theorem — no trace is computed. -/
theorem phase_witness_general :
    LinearMap.trace ℂ (QState 1) (qClifford (phaseGate (0 : Fin 1))).toLinearMap
        * LinearMap.trace ℂ (QState 1) (qClifford (phaseGate (0 : Fin 1))).symm.toLinearMap
      = 2 := by
  rw [signed_trace_mul_trace_inv (isCliffordOperator_phaseGate (0 : Fin 1))]
  have hsign : ∀ p ∈ Finset.univ.filter (fun p : Pauli 1 =>
      cliffordToSymplecticFun (isCliffordOperator_phaseGate (0 : Fin 1)) p = p),
      cliffordSign (isCliffordOperator_phaseGate (0 : Fin 1)) p = 1 := by
    intro p hp
    have hfix := (Finset.mem_filter.mp hp).2
    rw [cliffordFun_phase] at hfix
    exact cliffordSign_phase_of_fixed 0 p ((phaseAt_fixed_iff 0 p).mp hfix)
  rw [Finset.sum_congr rfl hsign, Finset.sum_const, card_fixed_phase]
  norm_num

/-- `exp(I·π/2) = I`. -/
lemma exp_I_pi_div_two : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

/-- `exp(−I·π/2) = −I`. -/
lemma exp_neg_I_pi_div_two :
    Complex.exp (Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ)) = -Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

/-- Sums over `ZMod 2`, split. -/
lemma sum_zmod_two (f : ZMod 2 → ℂ) : (∑ b : ZMod 2, f b) = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **The `S` witness, route A (independent)**: `Tr(S) = 1 + i` by direct diagonal summation. -/
theorem phase_trace_independent :
    LinearMap.trace ℂ (QubitSpace 1) (phaseGate (0 : Fin 1)).toLinearMap = 1 + Complex.I := by
  rw [trace_qubit_eq_sum_diag]
  have hterm : ∀ v : Fin 1 → ZMod 2,
      (phaseGate (0 : Fin 1)).toLinearMap ((Pi.basisFun ℂ (Fin 1 → ZMod 2)) v) v
        = Complex.exp (Complex.I * ((Real.pi / 2 * ((v 0).val : ℝ) : ℝ) : ℂ)) := by
    intro v
    show Complex.exp (Complex.I * ((Real.pi / 2 * ((v 0).val : ℝ) : ℝ) : ℂ))
        * ((Pi.basisFun ℂ (Fin 1 → ZMod 2)) v) v = _
    rw [Pi.basisFun_apply, Pi.single_eq_same, mul_one]
  rw [Finset.sum_congr rfl fun v _ => hterm v]
  rw [show (∑ v : Fin 1 → ZMod 2,
        Complex.exp (Complex.I * ((Real.pi / 2 * ((v 0).val : ℝ) : ℝ) : ℂ)))
      = ∑ z : ZMod 2, Complex.exp (Complex.I * ((Real.pi / 2 * ((z).val : ℝ) : ℝ) : ℂ)) from
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod 2))
      (fun v : Fin 1 → ZMod 2 =>
        Complex.exp (Complex.I * ((Real.pi / 2 * ((v 0).val : ℝ) : ℝ) : ℂ)))
      (fun z : ZMod 2 => Complex.exp (Complex.I * ((Real.pi / 2 * ((z).val : ℝ) : ℝ) : ℂ)))
      (fun v => rfl)]
  have h0 : Complex.exp (Complex.I * ((Real.pi / 2 * (((0 : ZMod 2)).val : ℝ) : ℝ) : ℂ)) = 1 := by
    simp [show ((0 : ZMod 2)).val = 0 from by decide]
  have h1 : Complex.exp (Complex.I * ((Real.pi / 2 * (((1 : ZMod 2)).val : ℝ) : ℝ) : ℂ))
      = Complex.I := by
    rw [show (Real.pi / 2 * (((1 : ZMod 2)).val : ℝ) : ℝ) = Real.pi / 2 from by
      rw [show ((1 : ZMod 2)).val = 1 from by decide]; push_cast; ring]
    exact exp_I_pi_div_two
  rw [sum_zmod_two, h0, h1]

/-- Route A, inverse side: `Tr(S⁻¹) = 1 − i`. -/
theorem phase_trace_symm_independent :
    LinearMap.trace ℂ (QubitSpace 1) (phaseGate (0 : Fin 1)).symm.toLinearMap
      = 1 - Complex.I := by
  rw [trace_qubit_eq_sum_diag]
  have hterm : ∀ v : Fin 1 → ZMod 2,
      (phaseGate (0 : Fin 1)).symm.toLinearMap ((Pi.basisFun ℂ (Fin 1 → ZMod 2)) v) v
        = Complex.exp (Complex.I * ((-(Real.pi / 2 * ((v 0).val : ℝ)) : ℝ) : ℂ)) := by
    intro v
    show Complex.exp (Complex.I * ((-(Real.pi / 2 * ((v 0).val : ℝ)) : ℝ) : ℂ))
        * ((Pi.basisFun ℂ (Fin 1 → ZMod 2)) v) v = _
    rw [Pi.basisFun_apply, Pi.single_eq_same, mul_one]
  rw [Finset.sum_congr rfl fun v _ => hterm v]
  rw [show (∑ v : Fin 1 → ZMod 2,
        Complex.exp (Complex.I * ((-(Real.pi / 2 * ((v 0).val : ℝ)) : ℝ) : ℂ)))
      = ∑ z : ZMod 2, Complex.exp (Complex.I * ((-(Real.pi / 2 * ((z).val : ℝ)) : ℝ) : ℂ)) from
    Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod 2))
      (fun v : Fin 1 → ZMod 2 =>
        Complex.exp (Complex.I * ((-(Real.pi / 2 * ((v 0).val : ℝ)) : ℝ) : ℂ)))
      (fun z : ZMod 2 => Complex.exp (Complex.I * ((-(Real.pi / 2 * ((z).val : ℝ)) : ℝ) : ℂ)))
      (fun v => rfl)]
  have h0 : Complex.exp (Complex.I * ((-(Real.pi / 2 * (((0 : ZMod 2)).val : ℝ)) : ℝ) : ℂ))
      = 1 := by
    simp [show ((0 : ZMod 2)).val = 0 from by decide]
  have h1 : Complex.exp (Complex.I * ((-(Real.pi / 2 * (((1 : ZMod 2)).val : ℝ)) : ℝ) : ℂ))
      = -Complex.I := by
    rw [show (-(Real.pi / 2 * (((1 : ZMod 2)).val : ℝ)) : ℝ) = -(Real.pi / 2) from by
      rw [show ((1 : ZMod 2)).val = 1 from by decide]; push_cast; ring]
    exact exp_neg_I_pi_div_two
  rw [sum_zmod_two, h0, h1]
  ring

/-- **The two routes meet at `2`**: `(1+i)(1−i) = 2`, matching route B. -/
theorem phase_witness_routes_agree :
    LinearMap.trace ℂ (QubitSpace 1) (phaseGate (0 : Fin 1)).toLinearMap
        * LinearMap.trace ℂ (QubitSpace 1) (phaseGate (0 : Fin 1)).symm.toLinearMap
      = 2 := by
  rw [phase_trace_independent, phase_trace_symm_independent]
  have h := Complex.I_mul_I
  ring_nf
  linear_combination -h

end PhaseWitness

/-! ## The CNOT witness (`n = 2`) — rank 2, entangling -/

section CnotWitness

/-- CNOT is Clifford — phaselessly (`α = 1` at every label). Restated here from the conjugation
law (the bundled version lives in the `Examples` layer, outside this import cone). -/
theorem isCliffordOperator_cnotGate' (i j : Fin n) (hij : i ≠ j) :
    IsCliffordOperator (cnotGate i j hij) :=
  fun p => ⟨1, cnotAt i j hij p, by rw [Units.val_one, one_smul]; exact cnotGate_conj i j hij p⟩

/-- CNOT's symplectic image is `cnotAt`, at every label. -/
lemma cliffordFun_cnot (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_cnotGate' i j hij) p = cnotAt i j hij p :=
  cliffordFun_eq_of_conj _ (by rw [Units.val_one, one_smul]; exact cnotGate_conj i j hij p)

/-- The fixed labels of `cnotAt i j`: no `X` on the control, no `Z` on the target. -/
lemma cnotAt_fixed_iff (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    cnotAt i j hij p = p ↔ p.X i = 0 ∧ p.Z j = 0 := by
  constructor
  · intro h
    have hX := congrArg (fun q : Pauli n => q.X j) h
    have hZ := congrArg (fun q : Pauli n => q.Z i) h
    simp only [cnotAt_X, cnotAt_Z, Function.update_self] at hX hZ
    constructor
    · have h' : p.X j + p.X i = p.X j + 0 := by rw [add_zero]; exact hX
      exact add_left_cancel h'
    · have h' : p.Z i + p.Z j = p.Z i + 0 := by rw [add_zero]; exact hZ
      exact add_left_cancel h'
  · rintro ⟨hx, hz⟩
    refine Pauli.ext ?_ ?_
    · rw [cnotAt_X, hx, add_zero, Function.update_eq_self]
    · rw [cnotAt_Z, hz, add_zero, Function.update_eq_self]

/-- The sign is trivial on every fixed label (the conjugation is phaseless and the `xz`-dressings
cancel at a fixed point). -/
lemma cliffordSign_cnot_of_fixed (i j : Fin n) (hij : i ≠ j) (p : Pauli n)
    (hp : cnotAt i j hij p = p) :
    cliffordSign (isCliffordOperator_cnotGate' i j hij) p = 1 := by
  have h := cliffordSign_eq_of_conj (isCliffordOperator_cnotGate' i j hij)
    (show (conjEquiv (cnotGate i j hij) (pauliEquiv p)).toLinearMap
        = ((1 : ℂˣ) : ℂ) • pauliOperator (cnotAt i j hij p) from by
      rw [Units.val_one, one_smul]
      exact cnotGate_conj i j hij p)
  rw [h, hp, Units.val_one, mul_one, mul_inv_cancel₀ (pow_ne_zero _ I_ne_zero)]

/-- The fixed subtype of `cnotAt 0 1` at `n = 2` is a copy of `ZMod 2 × ZMod 2` (the free bits:
`X` on the target, `Z` on the control). -/
noncomputable def cnotFixedEquiv :
    {p : Pauli 2 // p.X 0 = 0 ∧ p.Z 1 = 0} ≃ ZMod 2 × ZMod 2 where
  toFun p := (p.1.X 1, p.1.Z 0)
  invFun z := ⟨{ X := Pi.single 1 z.1, Z := Pi.single 0 z.2 },
    ⟨show (Pi.single (1 : Fin 2) z.1 : Fin 2 → ZMod 2) 0 = 0 from
        Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1) _,
     show (Pi.single (0 : Fin 2) z.2 : Fin 2 → ZMod 2) 1 = 0 from
        Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0) _⟩⟩
  left_inv := fun ⟨p, hp⟩ => by
    refine Subtype.ext (Pauli.ext ?_ ?_)
    · funext i
      fin_cases i
      · show (Pi.single (1 : Fin 2) (p.X 1) : Fin 2 → ZMod 2) 0 = p.X 0
        rw [Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        exact hp.1.symm
      · show (Pi.single (1 : Fin 2) (p.X 1) : Fin 2 → ZMod 2) 1 = p.X 1
        rw [Pi.single_eq_same]
    · funext i
      fin_cases i
      · show (Pi.single (0 : Fin 2) (p.Z 0) : Fin 2 → ZMod 2) 0 = p.Z 0
        rw [Pi.single_eq_same]
      · show (Pi.single (0 : Fin 2) (p.Z 0) : Fin 2 → ZMod 2) 1 = p.Z 1
        rw [Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        exact hp.2.symm
  right_inv := fun z => by
    refine Prod.ext ?_ ?_
    · show (Pi.single (1 : Fin 2) z.1 : Fin 2 → ZMod 2) 1 = z.1
      rw [Pi.single_eq_same]
    · show (Pi.single (0 : Fin 2) z.2 : Fin 2 → ZMod 2) 0 = z.2
      rw [Pi.single_eq_same]

open Classical in
/-- The fixed-set count of CNOT at `n = 2` is `4`. -/
lemma card_fixed_cnot :
    (Finset.univ.filter (fun p : Pauli 2 =>
      cliffordToSymplecticFun
        (isCliffordOperator_cnotGate' (0 : Fin 2) 1 (by decide)) p = p)).card = 4 := by
  have hpred : ∀ p : Pauli 2,
      (cliffordToSymplecticFun (isCliffordOperator_cnotGate' (0 : Fin 2) 1 (by decide)) p = p)
        ↔ (p.X 0 = 0 ∧ p.Z 1 = 0) := by
    intro p
    rw [cliffordFun_cnot]
    exact cnotAt_fixed_iff 0 1 (by decide) p
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr ((Equiv.subtypeEquivRight hpred).trans cnotFixedEquiv),
    Fintype.card_prod, ZMod.card]

open Classical in
/-- **The CNOT witness, route B (main theorem)**: trivial sign on a 4-element fixed set forces the
trace product to `4` through the main theorem. -/
theorem cnot_witness_general :
    LinearMap.trace ℂ (QState 2)
        (qClifford (cnotGate (0 : Fin 2) 1 (by decide))).toLinearMap
        * LinearMap.trace ℂ (QState 2)
            (qClifford (cnotGate (0 : Fin 2) 1 (by decide))).symm.toLinearMap
      = 4 := by
  rw [signed_trace_mul_trace_inv (isCliffordOperator_cnotGate' (0 : Fin 2) 1 (by decide))]
  have hsign : ∀ p ∈ Finset.univ.filter (fun p : Pauli 2 =>
      cliffordToSymplecticFun
        (isCliffordOperator_cnotGate' (0 : Fin 2) 1 (by decide)) p = p),
      cliffordSign (isCliffordOperator_cnotGate' (0 : Fin 2) 1 (by decide)) p = 1 := by
    intro p hp
    have hfix := (Finset.mem_filter.mp hp).2
    rw [cliffordFun_cnot] at hfix
    exact cliffordSign_cnot_of_fixed 0 1 (by decide) p hfix
  rw [Finset.sum_congr rfl hsign, Finset.sum_const, card_fixed_cnot]
  norm_num

/-- The permutation fixed points: `cnotPerm 0 1` fixes `v` iff the control bit is clear. -/
lemma cnotPerm_fixed_iff (v : Fin 2 → ZMod 2) :
    cnotPerm (0 : Fin 2) 1 v = v ↔ v 0 = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : Fin 2 → ZMod 2 => w 1) h
    simp only [cnotPerm, Function.update_self] at h1
    have h' : v 1 + v 0 = v 1 + 0 := by
      rw [add_zero]
      exact h1
    exact add_left_cancel h'
  · intro h
    funext i
    fin_cases i
    · simp [cnotPerm]
    · simp [cnotPerm, h]

/-- The fixed vectors form a copy of `ZMod 2`. -/
noncomputable def cnotPermFixedEquiv : {v : Fin 2 → ZMod 2 // v 0 = 0} ≃ ZMod 2 where
  toFun v := v.1 1
  invFun z := ⟨Pi.single 1 z,
    show (Pi.single (1 : Fin 2) z : Fin 2 → ZMod 2) 0 = 0 from
      Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1) _⟩
  left_inv := fun ⟨v, hv⟩ => by
    refine Subtype.ext ?_
    funext i
    fin_cases i
    · show (Pi.single (1 : Fin 2) (v 1) : Fin 2 → ZMod 2) 0 = v 0
      rw [Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      exact hv.symm
    · show (Pi.single (1 : Fin 2) (v 1) : Fin 2 → ZMod 2) 1 = v 1
      rw [Pi.single_eq_same]
  right_inv := fun z => by
    show (Pi.single (1 : Fin 2) z : Fin 2 → ZMod 2) 1 = z
    rw [Pi.single_eq_same]

open Classical in
/-- **The CNOT witness, route A (independent)**: `Tr(CNOT) = 2` by direct diagonal summation —
the permutation matrix has one diagonal `1` per fixed computational vector. -/
theorem cnot_trace_independent :
    LinearMap.trace ℂ (QubitSpace 2)
      (cnotGate (0 : Fin 2) 1 (by decide)).toLinearMap = 2 := by
  rw [trace_qubit_eq_sum_diag]
  have hterm : ∀ v : Fin 2 → ZMod 2,
      (cnotGate (0 : Fin 2) 1 (by decide)).toLinearMap
          ((Pi.basisFun ℂ (Fin 2 → ZMod 2)) v) v
        = if cnotPerm (0 : Fin 2) 1 v = v then (1 : ℂ) else 0 := by
    intro v
    show ((Pi.basisFun ℂ (Fin 2 → ZMod 2)) v) (cnotPerm (0 : Fin 2) 1 v) = _
    rw [Pi.basisFun_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hpred : ∀ v : Fin 2 → ZMod 2,
      (cnotPerm (0 : Fin 2) 1 v = v) ↔ v 0 = 0 := cnotPerm_fixed_iff
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr ((Equiv.subtypeEquivRight hpred).trans cnotPermFixedEquiv), ZMod.card]
  norm_num

/-- Route A, inverse side: CNOT is an involution, so the inverse has the same trace. -/
theorem cnot_trace_symm_independent :
    LinearMap.trace ℂ (QubitSpace 2)
      (cnotGate (0 : Fin 2) 1 (by decide)).symm.toLinearMap = 2 := by
  rw [trace_qubit_eq_sum_diag]
  have hterm : ∀ v : Fin 2 → ZMod 2,
      (cnotGate (0 : Fin 2) 1 (by decide)).symm.toLinearMap
          ((Pi.basisFun ℂ (Fin 2 → ZMod 2)) v) v
        = if cnotPerm (0 : Fin 2) 1 v = v then (1 : ℂ) else 0 := by
    intro v
    show ((Pi.basisFun ℂ (Fin 2 → ZMod 2)) v) (cnotPerm (0 : Fin 2) 1 v) = _
    rw [Pi.basisFun_apply, Pi.single_apply]
  rw [Finset.sum_congr rfl fun v _ => hterm v, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hpred : ∀ v : Fin 2 → ZMod 2,
      (cnotPerm (0 : Fin 2) 1 v = v) ↔ v 0 = 0 := cnotPerm_fixed_iff
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr ((Equiv.subtypeEquivRight hpred).trans cnotPermFixedEquiv), ZMod.card]
  norm_num

/-- **The two routes meet at `4`.** -/
theorem cnot_witness_routes_agree :
    LinearMap.trace ℂ (QubitSpace 2)
        (cnotGate (0 : Fin 2) 1 (by decide)).toLinearMap
        * LinearMap.trace ℂ (QubitSpace 2)
            (cnotGate (0 : Fin 2) 1 (by decide)).symm.toLinearMap
      = 4 := by
  rw [cnot_trace_independent, cnot_trace_symm_independent]
  norm_num

end CnotWitness

end FTQCLib.Hilbert

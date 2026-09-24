/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.SymplecticGeneration
import FTQCLib.Hilbert.DiagonalEquiv

/-! # Hilbert-space lifts of the elementary Clifford gates

With the symplectic-generation half of the Clifford–symplectic lift unconditional
(`spGeneratedByCliffordGates`), the remaining hypothesis of `cliffordSymplecticLift_of_generation`
is `hmem : cliffordGateGens n ⊆ cliffordToSp.range`: each elementary symplectic gate must be the
symplectic image (`cliffordToSymplectic`) of an actual Hilbert-space Clifford unitary on
`QubitSpace n`.

This file provides the **reusable bridge** reducing one gate lift to a single conjugation identity
(`mem_cliffordToSp_range_of_conj`), and the **reduction of `hmem` to the four per-gate lifts**
(`hmem_of_gate_lifts`), then builds the per-gate Hilbert unitaries — diagonal for `S`/`CZ`
(`diagonalGateEquiv`), a computational-basis permutation for `CNOT`, the Walsh–Hadamard transform
for `H` — and concludes the unconditional lift `cliffordSymplecticLift_unconditional`. -/

open FTQCLib.Pauli FTQCLib.Gates

namespace FTQCLib.Hilbert

variable {n : ℕ}

/-- **Gate-lift bridge.** A Hilbert unitary `U` whose conjugation sends each Pauli operator
`pauliEquiv p` to the phased Pauli `c p • pauliOperator (g p)` witnesses `⟨g, hg⟩ ∈ range Φ`. This
reduces lifting a symplectic gate `g` to exhibiting `U` and proving one conjugation identity. -/
theorem mem_cliffordToSp_range_of_conj {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    {g : Pauli n ≃ₗ[ZMod 2] Pauli n} (hg : IsClifford g) (c : Pauli n → ℂˣ)
    (hconj : ∀ p, (conjEquiv U (pauliEquiv p)).toLinearMap = (c p : ℂ) • pauliOperator (g p)) :
    (⟨g, hg⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range := by
  have hU : IsCliffordOperator U := fun p => ⟨c p, g p, hconj p⟩
  have hgeq : cliffordToSymplectic hU = g := by
    refine LinearEquiv.ext fun p => ?_
    rw [cliffordToSymplectic_apply]
    exact (cliffordToSymplecticFun_unique hU p (hconj p)).symm
  exact ⟨⟨U, hU⟩, Subtype.ext hgeq⟩

/-- **`hmem` reduces to the four per-gate lifts.** Once each of `H`, `S`, `CNOT`, `CZ` is exhibited
as the symplectic image of a Clifford unitary, the generating set lies in `range Φ`, and (with
`spGeneratedByCliffordGates`) the Clifford–symplectic lift follows via
`cliffordSymplecticLift_of_gateLifts`. -/
theorem hmem_of_gate_lifts
    (had : ∀ k : Fin n,
      (⟨hadamardAt k, hadamardAt_isClifford k⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range)
    (pha : ∀ k : Fin n,
      (⟨phaseAt k, phaseAt_isClifford k⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range)
    (cno : ∀ (i j : Fin n) (h : i ≠ j),
      (⟨cnotAt i j h, cnotAt_isClifford i j h⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range)
    (cz : ∀ (i j : Fin n) (h : i ≠ j),
      (⟨czAt i j h, czAt_isClifford i j h⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range) :
    cliffordGateGens n ⊆ (cliffordToSp (n := n)).range := by
  rintro x (((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨i, j, h, rfl⟩) | ⟨i, j, h, rfl⟩)
  · exact had k
  · exact pha k
  · exact cno i j h
  · exact cz i j h

/-! ## The phase gate `S` (diagonal lift) -/

/-- `exp(i · (π/2) · m) = iᵐ` for a natural exponent. -/
private theorem exp_phase_pow (m : ℕ) :
    Complex.exp (Complex.I * (((Real.pi / 2) * (m : ℝ) : ℝ) : ℂ)) = Complex.I ^ m := by
  have key : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_natCast,
      show Complex.I * (((Real.pi / 2 : ℝ) : ℂ) * (m : ℂ))
         = (m : ℂ) * (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) from by ring,
      Complex.exp_nat_mul, key]

/-- The negated companion of `exp_phase_pow`: `exp(i · (-(π/2)·m)) = (iᵐ)⁻¹`. -/
private theorem exp_phase_pow_neg (m : ℕ) :
    Complex.exp (Complex.I * ((-((Real.pi / 2) * (m : ℝ)) : ℝ) : ℂ)) = (Complex.I ^ m)⁻¹ := by
  rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg, exp_phase_pow]

/-- The unit `i ∈ ℂˣ`, for packaging the conjugation phase. -/
private noncomputable def iUnit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

@[simp] private theorem iUnit_val : (iUnit : ℂ) = Complex.I := rfl

/-- The local `i`-power identity behind the phase gate's conjugation. -/
private theorem iPow_phase_local (A B : ZMod 2) :
    Complex.I ^ A.val * (Complex.I ^ (A + B).val)⁻¹ =
      Complex.I ^ B.val * (-1 : ℂ) ^ (B.val * (A + B).val) := by
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich A with hA | hA <;> rcases dich B with hB | hB <;> subst hA <;> subst hB <;>
    simp only [show (0:ZMod 2)+0 = 0 from by decide, show (0:ZMod 2)+1 = 1 from by decide,
      show (1:ZMod 2)+0 = 1 from by decide, show (1:ZMod 2)+1 = 0 from by decide,
      show ZMod.val (0:ZMod 2) = 0 from by decide, show ZMod.val (1:ZMod 2) = 1 from by decide,
      pow_zero, pow_one, mul_one, one_mul, Complex.inv_I] <;> norm_num

/-- The phase gate `S` on qubit `k`, as a diagonal Hilbert unitary `|v⟩ ↦ i^{v_k} |v⟩`. -/
noncomputable def phaseGate (k : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (fun v => (Real.pi / 2) * ((v k).val : ℝ))

/-- `phaseAt`'s effect on the `(-1)`-phase: a `Z_k += X_k` correction at qubit `k`. -/
private theorem neg_one_pow_zDotVal_phaseAt (k : Fin n) (p : Pauli n) (v : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDotVal (phaseAt k p) v =
      (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ ((p.X k).val * (v k).val) := by
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (p.X k) with hpk | hpk
  · have hp : phaseAt k p = p := by
      ext i
      · simp [phaseAt_X]
      · rcases eq_or_ne i k with rfl | hi
        · simp [phaseAt_Z, hpk]
        · simp [phaseAt_Z, Function.update_of_ne hi]
    rw [hp, hpk]; simp
  · have hp : phaseAt k p = p + pauliz k := by
      ext i
      · simp [phaseAt_X, X_add, pauliz_X]
      · rcases eq_or_ne i k with rfl | hi
        · simp [phaseAt_Z, Z_add, pauliz_Z, hpk]
        · simp [phaseAt_Z, Z_add, pauliz_Z, Function.update_of_ne hi, Pi.single_eq_of_ne hi]
    rw [hp, neg_one_pow_eq_of_mod_two_eq (zDotVal_add_left_mod_two p (pauliz k) v),
        pow_add, zDotVal_pauliz, hpk]
    have h1 : ZMod.val (1 : ZMod 2) = 1 := by decide
    rw [h1, one_mul]

/-- **The phase gate's conjugation action.** `S_k` conjugates each Pauli operator to the phased
Pauli at `phaseAt k p`, with phase `i^{X_k}` — the `S`-gate Heisenberg rule `X ↦ Y`, `Z ↦ Z`. -/
theorem phaseGate_conj (k : Fin n) (p : Pauli n) :
    (conjEquiv (phaseGate k) (pauliEquiv p)).toLinearMap =
      ((iUnit ^ (p.X k).val : ℂˣ) : ℂ) • pauliOperator (phaseAt k p) := by
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [phaseGate, LinearEquiv.coe_coe, conjEquiv_apply, diagonalGateEquiv_symm_apply,
    pauliEquiv_apply, diagonalGateEquiv_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    Units.val_pow_eq_pow_val, iUnit_val]
  unfold diagonalGate pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk, phaseAt_X]
  rw [exp_phase_pow, exp_phase_pow_neg, neg_one_pow_zDotVal_phaseAt,
    show (w - p.X) k = w k + p.X k from by rw [Pi.sub_apply, CharTwo.sub_eq_add],
    show Complex.I ^ (w k).val * ((-1 : ℂ) ^ zDotVal p (w - p.X) *
        ((Complex.I ^ (w k + p.X k).val)⁻¹ * ψ (w - p.X)))
      = Complex.I ^ (w k).val * (Complex.I ^ (w k + p.X k).val)⁻¹ *
        ((-1 : ℂ) ^ zDotVal p (w - p.X) * ψ (w - p.X)) from by ring,
    iPow_phase_local]
  ring

/-- **The phase gate lifts.** `phaseAt k ∈ range Φ`. -/
theorem phaseAt_mem_cliffordToSp_range (k : Fin n) :
    (⟨phaseAt k, phaseAt_isClifford k⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range :=
  mem_cliffordToSp_range_of_conj (phaseAt_isClifford k) (fun p => iUnit ^ (p.X k).val)
    (fun p => phaseGate_conj k p)

/-! ## The controlled-`Z` gate (diagonal lift) -/

/-- `exp(i · π · m) = (-1)ᵐ` for a natural exponent. -/
private theorem exp_pi_pow (m : ℕ) :
    Complex.exp (Complex.I * ((Real.pi * (m : ℝ) : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  rw [Complex.ofReal_mul, Complex.ofReal_natCast,
      show Complex.I * (((Real.pi : ℝ) : ℂ) * (m : ℂ)) = (m : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I)
        from by ring, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- The negated companion of `exp_pi_pow`. -/
private theorem exp_pi_pow_neg (m : ℕ) :
    Complex.exp (Complex.I * ((-(Real.pi * (m : ℝ)) : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg, exp_pi_pow, ← inv_pow]
  norm_num

/-- The controlled-`Z` gate on `i, j`, as a diagonal Hilbert unitary `|v⟩ ↦ (-1)^{v_i v_j}|v⟩`. -/
noncomputable def czGate (i j : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  diagonalGateEquiv (fun v => Real.pi * (((v i).val * (v j).val : ℕ) : ℝ))

/-- Adding one `pauliz l` flips the `(-1)`-phase by `(-1)^{v_l}`. -/
private theorem neg_one_pow_zDotVal_add_pauliz (p : Pauli n) (l : Fin n) (v : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDotVal (p + pauliz l) v = (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ (v l).val := by
  rw [neg_one_pow_eq_of_mod_two_eq (zDotVal_add_left_mod_two p (pauliz l) v), pow_add,
    zDotVal_pauliz]

/-- `czAt`'s effect on the `(-1)`-phase: the `Z_i += X_j`, `Z_j += X_i` corrections at qubits
`i` and `j`. -/
private theorem neg_one_pow_zDotVal_czAt (i j : Fin n) (hij : i ≠ j) (p : Pauli n)
    (v : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDotVal (czAt i j hij p) v =
      (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ ((p.X j).val * (v i).val) *
        (-1 : ℂ) ^ ((p.X i).val * (v j).val) := by
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hv1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have hv0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  rcases dich (p.X i) with hi | hi <;> rcases dich (p.X j) with hj | hj
  · have hcz : czAt i j hij p = p := by
      ext k
      · simp [czAt_X]
      · simp only [czAt_Z, czZ, Function.update_apply]
        rw [hi, hj]; split_ifs <;> simp_all
    rw [hcz]; simp only [hi, hj, hv0, zero_mul, pow_zero, mul_one]
  · have hcz : czAt i j hij p = p + pauliz i := by
      ext k
      · simp [czAt_X, X_add, pauliz_X]
      · simp only [czAt_Z, czZ, Z_add, pauliz_Z, Pi.add_apply, Function.update_apply,
          Pi.single_apply]
        rw [hi, hj]; split_ifs <;> simp_all
    rw [hcz, neg_one_pow_zDotVal_add_pauliz]
    simp only [hi, hj, hv0, hv1, zero_mul, one_mul, pow_zero, mul_one]
  · have hcz : czAt i j hij p = p + pauliz j := by
      ext k
      · simp [czAt_X, X_add, pauliz_X]
      · simp only [czAt_Z, czZ, Z_add, pauliz_Z, Pi.add_apply, Function.update_apply,
          Pi.single_apply]
        rw [hi, hj]; split_ifs <;> simp_all
    rw [hcz, neg_one_pow_zDotVal_add_pauliz]
    simp only [hi, hj, hv0, hv1, zero_mul, one_mul, pow_zero, mul_one]
  · have hcz : czAt i j hij p = p + pauliz i + pauliz j := by
      ext k
      · simp [czAt_X, X_add, pauliz_X]
      · simp only [czAt_Z, czZ, Z_add, pauliz_Z, Pi.add_apply, Function.update_apply,
          Pi.single_apply]
        rw [hi, hj]; split_ifs <;> simp_all
    rw [hcz, neg_one_pow_zDotVal_add_pauliz, neg_one_pow_zDotVal_add_pauliz]
    simp only [hi, hj, hv1, one_mul, mul_assoc]

/-- The unit `-1 ∈ ℂˣ`, for packaging the CZ conjugation phase. -/
private noncomputable def negOneUnit : ℂˣ := Units.mk0 (-1) (by norm_num)

@[simp] private theorem negOneUnit_val : (negOneUnit : ℂ) = -1 := rfl

/-- The local `(-1)`-power identity behind the CZ gate's conjugation (bilinearity mod 2). -/
private theorem neg_one_pow_cz_local (a b c d : ZMod 2) :
    (-1 : ℂ) ^ (a.val * b.val) * (-1 : ℂ) ^ ((a + c).val * (b + d).val) =
      (-1 : ℂ) ^ (c.val * d.val) * (-1 : ℂ) ^ (d.val * (a + c).val) *
        (-1 : ℂ) ^ (c.val * (b + d).val) := by
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich a with ha | ha <;> rcases dich b with hb | hb <;> rcases dich c with hc | hc <;>
    rcases dich d with hd | hd <;> subst ha <;> subst hb <;> subst hc <;> subst hd <;>
    simp only [show (0:ZMod 2)+0 = 0 from by decide, show (0:ZMod 2)+1 = 1 from by decide,
      show (1:ZMod 2)+0 = 1 from by decide, show (1:ZMod 2)+1 = 0 from by decide,
      show ZMod.val (0:ZMod 2) = 0 from by decide, show ZMod.val (1:ZMod 2) = 1 from by decide,
      mul_zero, mul_one, one_mul, pow_zero, pow_one] <;> norm_num

/-- **The CZ gate's conjugation action.** `CZ_{ij}` conjugates each Pauli operator to the phased
Pauli at `czAt i j p`, with the real phase `(-1)^{X_i·X_j}` — the rule `X_i ↦ X_i Z_j` etc. -/
theorem czGate_conj (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    (conjEquiv (czGate i j) (pauliEquiv p)).toLinearMap =
      ((negOneUnit ^ ((p.X i).val * (p.X j).val) : ℂˣ) : ℂ) • pauliOperator (czAt i j hij p) := by
  apply LinearMap.ext
  intro ψ
  funext w
  simp only [czGate, LinearEquiv.coe_coe, conjEquiv_apply, diagonalGateEquiv_symm_apply,
    pauliEquiv_apply, diagonalGateEquiv_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    Units.val_pow_eq_pow_val, negOneUnit_val]
  unfold diagonalGate pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk, czAt_X]
  rw [exp_pi_pow, exp_pi_pow_neg, neg_one_pow_zDotVal_czAt,
    show (w - p.X) i = w i + p.X i from by rw [Pi.sub_apply, CharTwo.sub_eq_add],
    show (w - p.X) j = w j + p.X j from by rw [Pi.sub_apply, CharTwo.sub_eq_add],
    show (-1 : ℂ) ^ ((w i).val * (w j).val) *
        ((-1 : ℂ) ^ zDotVal p (w - p.X) *
          ((-1 : ℂ) ^ ((w i + p.X i).val * (w j + p.X j).val) * ψ (w - p.X)))
      = ((-1 : ℂ) ^ ((w i).val * (w j).val) *
          (-1 : ℂ) ^ ((w i + p.X i).val * (w j + p.X j).val)) *
        ((-1 : ℂ) ^ zDotVal p (w - p.X) * ψ (w - p.X)) from by ring,
    neg_one_pow_cz_local]
  ring

/-- **The CZ gate lifts.** `czAt i j ∈ range Φ`. -/
theorem czAt_mem_cliffordToSp_range (i j : Fin n) (hij : i ≠ j) :
    (⟨czAt i j hij, czAt_isClifford i j hij⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range :=
  mem_cliffordToSp_range_of_conj (czAt_isClifford i j hij)
    (fun p => negOneUnit ^ ((p.X i).val * (p.X j).val)) (fun p => czGate_conj i j hij p)

/-! ## The controlled-NOT gate (basis-permutation lift) -/

/-- The CNOT basis permutation: flip qubit `j` controlled by qubit `i`, `x ↦ x ⊕ x_i e_j`. -/
def cnotPerm (i j : Fin n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  Function.update x j (x j + x i)

theorem cnotPerm_involutive (i j : Fin n) (hij : i ≠ j) (x : Fin n → ZMod 2) :
    cnotPerm i j (cnotPerm i j x) = x := by
  funext k
  unfold cnotPerm
  rcases eq_or_ne k j with rfl | hk
  · rw [Function.update_self, Function.update_self, Function.update_of_ne hij, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

theorem cnotPerm_add (i j : Fin n) (x y : Fin n → ZMod 2) :
    cnotPerm i j (x + y) = cnotPerm i j x + cnotPerm i j y := by
  funext k
  unfold cnotPerm
  rcases eq_or_ne k j with rfl | hk
  · simp only [Function.update_self, Pi.add_apply]; ring
  · simp only [Function.update_of_ne hk, Pi.add_apply]

/-- The CNOT gate as a Hilbert unitary: precomposition with the (involutive) basis permutation. -/
noncomputable def cnotGate (i j : Fin n) (hij : i ≠ j) : QubitSpace n ≃ₗ[ℂ] QubitSpace n where
  toFun ψ := fun w => ψ (cnotPerm i j w)
  map_add' ψ φ := by funext w; simp [Pi.add_apply]
  map_smul' c ψ := by funext w; simp
  invFun ψ := fun w => ψ (cnotPerm i j w)
  left_inv ψ := by funext w; simp [cnotPerm_involutive i j hij]
  right_inv ψ := by funext w; simp [cnotPerm_involutive i j hij]

@[simp] theorem cnotGate_apply (i j : Fin n) (hij : i ≠ j) (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    cnotGate i j hij ψ w = ψ (cnotPerm i j w) := rfl

@[simp] theorem cnotGate_symm_apply (i j : Fin n) (hij : i ≠ j) (ψ : QubitSpace n)
    (w : Fin n → ZMod 2) : (cnotGate i j hij).symm ψ w = ψ (cnotPerm i j w) := rfl

/-- CNOT maps a computational basis vector to the permuted one. -/
theorem cnotGate_computational (i j : Fin n) (hij : i ≠ j) (v : Fin n → ZMod 2) :
    cnotGate i j hij (computational v) = computational (cnotPerm i j v) := by
  funext w
  simp only [cnotGate_apply, computational]
  by_cases h : cnotPerm i j w = v
  · have hw : w = cnotPerm i j v := by rw [← h, cnotPerm_involutive i j hij]
    rw [if_pos h, if_pos hw]
  · have hw : w ≠ cnotPerm i j v := fun he => h (by rw [he, cnotPerm_involutive i j hij])
    rw [if_neg h, if_neg hw]

/-- `zDotVal` against a single-support vector picks out one term. -/
private theorem zDotVal_single_right (p : Pauli n) (j : Fin n) (c : ZMod 2) :
    zDotVal p (Pi.single j c) = (p.Z j).val * c.val := by
  unfold zDotVal
  rw [Finset.sum_eq_single j
      (fun l _ hl => by rw [Pi.single_eq_of_ne hl, ZMod.val_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]

/-- The CNOT permutation as a vector addition: `cnotPerm v = v + v_i · e_j`. -/
private theorem cnotPerm_eq_add (i j : Fin n) (v : Fin n → ZMod 2) :
    cnotPerm i j v = v + Pi.single j (v i) := by
  funext k
  unfold cnotPerm
  rcases eq_or_ne k j with rfl | hk
  · rw [Function.update_self, Pi.add_apply, Pi.single_eq_same]
  · rw [Function.update_of_ne hk, Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]

/-- `zDotVal` depends only on the `Z`-part. -/
private theorem zDotVal_congr_Z {q q' : Pauli n} (v : Fin n → ZMod 2) (h : q.Z = q'.Z) :
    zDotVal q v = zDotVal q' v := by unfold zDotVal; rw [h]

/-- **The CNOT parity identity.** Permuting the input equals applying `cnotAt` to the Pauli, on the
phase: both shift the `(-1)`-phase by the same `Z_j · v_i` correction. -/
private theorem neg_one_pow_zDotVal_cnotPerm (i j : Fin n) (hij : i ≠ j) (p : Pauli n)
    (v : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDotVal p (cnotPerm i j v) = (-1 : ℂ) ^ zDotVal (cnotAt i j hij p) v := by
  have hL : (-1 : ℂ) ^ zDotVal p (cnotPerm i j v) =
      (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ ((p.Z j).val * (v i).val) := by
    rw [cnotPerm_eq_add i j,
      neg_one_pow_eq_of_mod_two_eq (zDotVal_add_right_mod_two p v (Pi.single j (v i))), pow_add,
      zDotVal_single_right]
  have hR : (-1 : ℂ) ^ zDotVal (cnotAt i j hij p) v =
      (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ ((p.Z j).val * (v i).val) := by
    have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases dich (p.Z j) with hj | hj
    · have hz : zDotVal (cnotAt i j hij p) v = zDotVal p v := by
        apply zDotVal_congr_Z; funext k; rw [cnotAt_Z]
        rcases eq_or_ne k i with rfl | hki
        · rw [Function.update_self, hj, add_zero]
        · rw [Function.update_of_ne hki]
      rw [hz, hj]; simp
    · have hz : zDotVal (cnotAt i j hij p) v = zDotVal (p + pauliz i) v := by
        apply zDotVal_congr_Z; funext k; rw [cnotAt_Z, Z_add, pauliz_Z]
        rcases eq_or_ne k i with rfl | hki
        · rw [Function.update_self, hj, Pi.add_apply, Pi.single_eq_same]
        · rw [Function.update_of_ne hki, Pi.add_apply, Pi.single_eq_of_ne hki, add_zero]
      rw [hz, neg_one_pow_zDotVal_add_pauliz, hj]
      have h1 : ZMod.val (1 : ZMod 2) = 1 := by decide
      rw [h1, one_mul]
  rw [hL, hR]

/-- **The CNOT gate's conjugation action.** `CNOT_{ij}` conjugates each Pauli operator to the Pauli
at `cnotAt i j p`, with no phase — the rule `X_i ↦ X_i X_j`, `Z_j ↦ Z_i Z_j`. -/
theorem cnotGate_conj (i j : Fin n) (hij : i ≠ j) (p : Pauli n) :
    (conjEquiv (cnotGate i j hij) (pauliEquiv p)).toLinearMap =
      pauliOperator (cnotAt i j hij p) := by
  apply LinearMap.ext; intro ψ; funext w
  simp only [LinearEquiv.coe_coe, conjEquiv_apply, cnotGate_apply, pauliEquiv_apply]
  unfold pauliOperator
  simp only [LinearMap.coe_mk, AddHom.coe_mk, cnotGate_symm_apply]
  have hsub : ∀ a b : Fin n → ZMod 2, a - b = a + b := fun a b => by
    funext l; simp only [Pi.sub_apply, Pi.add_apply]; exact CharTwo.sub_eq_add (a l) (b l)
  have hX : (cnotAt i j hij p).X = cnotPerm i j p.X := by rw [cnotAt_X]; rfl
  have hpsi : cnotPerm i j (cnotPerm i j w - p.X) = w - (cnotAt i j hij p).X := by
    rw [hX]; simp only [hsub]; rw [cnotPerm_add, cnotPerm_involutive i j hij]
  have hexp : cnotPerm i j w - p.X = cnotPerm i j (w - (cnotAt i j hij p).X) := by
    rw [hX]; simp only [hsub]; rw [cnotPerm_add, cnotPerm_involutive i j hij]
  rw [hpsi, hexp, neg_one_pow_zDotVal_cnotPerm i j hij]

/-- **The CNOT gate lifts.** `cnotAt i j ∈ range Φ`. -/
theorem cnotAt_mem_cliffordToSp_range (i j : Fin n) (hij : i ≠ j) :
    (⟨cnotAt i j hij, cnotAt_isClifford i j hij⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range :=
  mem_cliffordToSp_range_of_conj (cnotAt_isClifford i j hij) (fun _ => 1)
    (fun p => by rw [Units.val_one, one_smul]; exact cnotGate_conj i j hij p)

/-! ## The Hadamard gate (Walsh transform lift) -/

/-- `1/√2 ∈ ℂ`. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = 2⁻¹ := by
  rw [invSqrt2, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- A sum over `ZMod 2` is the two-term sum. -/
private theorem sum_zmod2 (f : ZMod 2 → ℂ) : ∑ b : ZMod 2, f b = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- The Hadamard gate on `k`, the Walsh transform `|v⟩ ↦ (1/√2) ∑_b (-1)^{v_k·b} |v_{k←b}⟩`. -/
noncomputable def hadamardGate (k : Fin n) : QubitSpace n →ₗ[ℂ] QubitSpace n where
  toFun ψ := fun w =>
    invSqrt2 * ∑ b : ZMod 2, (-1 : ℂ) ^ ((w k).val * b.val) * ψ (Function.update w k b)
  map_add' ψ φ := by
    funext w
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring

@[simp] theorem hadamardGate_apply (k : Fin n) (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    hadamardGate k ψ w =
      invSqrt2 * ∑ b : ZMod 2, (-1 : ℂ) ^ ((w k).val * b.val) * ψ (Function.update w k b) := rfl

/-- **Hadamard is self-inverse** (`H² = id`): the Walsh transform is involutive, via the two-term
orthogonality `∑_b (-1)^{b·M} = 2·[M even]` and `(1/√2)² = 1/2`. -/
theorem hadamardGate_involutive (k : Fin n) (ψ : QubitSpace n) :
    hadamardGate k (hadamardGate k ψ) = ψ := by
  funext w
  rw [hadamardGate_apply]
  simp only [hadamardGate_apply, Function.update_self, Function.update_idem, sum_zmod2]
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (w k) with hwk | hwk
  · have hu : Function.update w k 0 = w := by rw [← hwk, Function.update_eq_self]
    rw [hwk]
    simp only [e0, e1, mul_zero, mul_one, pow_zero, one_mul, pow_one]
    rw [hu]
    linear_combination (2 * ψ w) * invSqrt2_mul_self
  · have hu : Function.update w k 1 = w := by rw [← hwk, Function.update_eq_self]
    rw [hwk]
    simp only [e0, e1, mul_zero, mul_one, pow_zero, one_mul, pow_one]
    rw [hu]
    linear_combination (2 * ψ w) * invSqrt2_mul_self

/-- The Hadamard gate packaged as a (self-inverse) linear equivalence on `QubitSpace n`. -/
noncomputable def hadamardEquiv (k : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n where
  toFun := hadamardGate k
  map_add' := (hadamardGate k).map_add'
  map_smul' := (hadamardGate k).map_smul'
  invFun := hadamardGate k
  left_inv := hadamardGate_involutive k
  right_inv := hadamardGate_involutive k

@[simp] theorem hadamardEquiv_apply (k : Fin n) (ψ : QubitSpace n) :
    hadamardEquiv k ψ = hadamardGate k ψ := rfl

@[simp] theorem hadamardEquiv_symm_apply (k : Fin n) (ψ : QubitSpace n) :
    (hadamardEquiv k).symm ψ = hadamardGate k ψ := rfl

/-- A single-coordinate update as a vector addition. -/
private theorem update_eq_add_single (v : Fin n → ZMod 2) (k : Fin n) (a : ZMod 2) :
    Function.update v k a = v + Pi.single k (a - v k) := by
  funext l
  rcases eq_or_ne l k with rfl | hl
  · rw [Function.update_self, Pi.add_apply, Pi.single_eq_same]; ring
  · rw [Function.update_of_ne hl, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]

/-- Updating one coordinate of the input shifts the `(-1)`-phase by `(p.Z k)·(a − v_k)`. -/
private theorem neg_one_pow_zDotVal_update_right (p : Pauli n) (v : Fin n → ZMod 2) (k : Fin n)
    (a : ZMod 2) :
    (-1 : ℂ) ^ zDotVal p (Function.update v k a) =
      (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ ((p.Z k).val * (a - v k).val) := by
  rw [update_eq_add_single,
    neg_one_pow_eq_of_mod_two_eq (zDotVal_add_right_mod_two p v (Pi.single k (a - v k))), pow_add,
    zDotVal_single_right]

/-- `hadamardAt`'s `X↔Z` swap on the `(-1)`-phase: it picks up `(X_k + Z_k)·v_k` at qubit `k`. -/
private theorem neg_one_pow_zDotVal_hadamardAt (k : Fin n) (p : Pauli n) (v : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDotVal (hadamardAt k p) v =
      (-1 : ℂ) ^ zDotVal p v * (-1 : ℂ) ^ ((p.X k).val * (v k).val) *
        (-1 : ℂ) ^ ((p.Z k).val * (v k).val) := by
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases dich (p.X k) with hx | hx <;> rcases dich (p.Z k) with hz | hz
  · have hZ : (hadamardAt k p).Z = p.Z := by rw [hadamardAt_Z, hx, ← hz, Function.update_eq_self]
    rw [zDotVal_congr_Z v hZ, hx, hz]; simp [e0]
  · have hZ : (hadamardAt k p).Z = (p + pauliz k).Z := by
      rw [hadamardAt_Z]; funext l
      rcases eq_or_ne l k with rfl | hl
      · rw [Function.update_self, hx, Z_add, pauliz_Z, Pi.add_apply, Pi.single_eq_same, hz]; decide
      · rw [Function.update_of_ne hl, Z_add, pauliz_Z, Pi.add_apply, Pi.single_eq_of_ne hl,
          add_zero]
    rw [zDotVal_congr_Z v hZ, neg_one_pow_zDotVal_add_pauliz, hx, hz]; simp [e0, e1]
  · have hZ : (hadamardAt k p).Z = (p + pauliz k).Z := by
      rw [hadamardAt_Z]; funext l
      rcases eq_or_ne l k with rfl | hl
      · rw [Function.update_self, hx, Z_add, pauliz_Z, Pi.add_apply, Pi.single_eq_same, hz]; decide
      · rw [Function.update_of_ne hl, Z_add, pauliz_Z, Pi.add_apply, Pi.single_eq_of_ne hl,
          add_zero]
    rw [zDotVal_congr_Z v hZ, neg_one_pow_zDotVal_add_pauliz, hx, hz]; simp [e0, e1]
  · have hZ : (hadamardAt k p).Z = p.Z := by rw [hadamardAt_Z, hx, ← hz, Function.update_eq_self]
    rw [zDotVal_congr_Z v hZ, hx, hz]
    simp only [e1, one_mul]
    rw [mul_assoc, ← pow_add, show (v k).val + (v k).val = 2 * (v k).val from by ring, pow_mul]
    norm_num

/-- Pure-`X` Pauli, general action: shifts the input by `e_k`, no phase. -/
theorem pauliOperator_paulix_apply (k : Fin n) (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    pauliOperator (paulix k) ψ w = ψ (w - Pi.single k 1) := by
  have hz : ∀ v, zDotVal (paulix k) v = 0 := fun v => by unfold zDotVal; simp [paulix_Z]
  unfold pauliOperator; simp [paulix_X, hz]

/-- Pure-`Z` Pauli, general action: phases by `(-1)^{w_k}`, no shift. -/
theorem pauliOperator_pauliz_apply (k : Fin n) (ψ : QubitSpace n) (w : Fin n → ZMod 2) :
    pauliOperator (pauliz k) ψ w = (-1 : ℂ) ^ (w k).val * ψ w := by
  unfold pauliOperator; simp [pauliz_X, zDotVal_pauliz]

/-- **`H = (X + Z)/√2`.** The Hadamard operator is `1/√2` times the sum of the `X` and `Z` Pauli
operators on qubit `k`. This turns the conjugation into Pauli algebra (via `pauliOperator_mul`). -/
theorem hadamardGate_eq (k : Fin n) :
    hadamardGate k = invSqrt2 • (pauliOperator (paulix k) + pauliOperator (pauliz k)) := by
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  apply LinearMap.ext; intro ψ; funext w
  rw [hadamardGate_apply, sum_zmod2]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    pauliOperator_paulix_apply, pauliOperator_pauliz_apply, e0, e1, mul_zero, mul_one, pow_zero,
    one_mul]
  rcases dich (w k) with hwk | hwk
  · have h0 : Function.update w k 0 = w := by rw [← hwk, Function.update_eq_self]
    have h1 : Function.update w k 1 = w - Pi.single k 1 := by
      funext l; rcases eq_or_ne l k with rfl | hl
      · rw [Function.update_self, Pi.sub_apply, Pi.single_eq_same, hwk]; decide
      · rw [Function.update_of_ne hl, Pi.sub_apply, Pi.single_eq_of_ne hl, sub_zero]
    rw [h0, h1, hwk, e0, pow_zero]; ring
  · have h0 : Function.update w k 0 = w - Pi.single k 1 := by
      funext l; rcases eq_or_ne l k with rfl | hl
      · rw [Function.update_self, Pi.sub_apply, Pi.single_eq_same, hwk]; decide
      · rw [Function.update_of_ne hl, Pi.sub_apply, Pi.single_eq_of_ne hl, sub_zero]
    have h1 : Function.update w k 1 = w := by rw [← hwk, Function.update_eq_self]
    rw [h0, h1, hwk, e1, pow_one]

/-- A triple Pauli product `a · p · b` collapses to a phased Pauli at `a + p + b` (two applications
of `pauliOperator_mul`). -/
theorem pauli_conj_triple (a p b : Pauli n) :
    pauliOperator a ∘ₗ pauliOperator p ∘ₗ pauliOperator b =
      ((-1 : ℂ) ^ (zDotVal p b.X + zDotVal a (b + p).X)) • pauliOperator (a + p + b) := by
  rw [pauliOperator_mul b p, LinearMap.comp_smul, pauliOperator_mul (b + p) a, smul_smul,
    ← pow_add, show b + p + a = a + p + b from by abel]

/-- Pure-`X` Pauli has trivial `zDot` (its `Z`-support is empty). -/
private theorem zDotVal_paulix (k : Fin n) (v : Fin n → ZMod 2) : zDotVal (paulix k) v = 0 := by
  unfold zDotVal; simp [paulix_Z]

/-- Char-2: every Pauli is its own additive inverse. -/
private theorem pauli_add_self (x : Pauli n) : x + x = 0 := by
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2), show ((2 : ℕ) : ZMod 2) = 0 from by decide,
    zero_smul]

set_option linter.unusedSimpArgs false in
/-- **The Hadamard gate's conjugation action.** `H_k` conjugates each Pauli operator to the Pauli at
`hadamardAt k p` (the `X_k ↔ Z_k` swap), with the real phase `(-1)^{X_k·Z_k}` (the `Y_k` sign).
Proved by Pauli algebra: `H = (X+Z)/√2`, so `H p H = ½·(four triple products)`. -/
theorem hadamardEquiv_conj (k : Fin n) (p : Pauli n) :
    (conjEquiv (hadamardEquiv k) (pauliEquiv p)).toLinearMap =
      ((negOneUnit ^ ((p.X k).val * (p.Z k).val) : ℂˣ) : ℂ) • pauliOperator (hadamardAt k p) := by
  have hzp0 : zDotVal p 0 = 0 := by unfold zDotVal; simp
  have e0 : ZMod.val (0 : ZMod 2) = 0 := by decide
  have e1 : ZMod.val (1 : ZMod 2) = 1 := by decide
  have dich : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hPeq : p.Z k = p.X k → hadamardAt k p = p := fun h => by
    refine Pauli.ext ?_ ?_
    · rw [hadamardAt_X, h, Function.update_eq_self]
    · rw [hadamardAt_Z, ← h, Function.update_eq_self]
  have hA2eq : p.Z k = 1 + p.X k → hadamardAt k p = paulix k + p + pauliz k := fun h => by
    have hv : p.X k - p.Z k = 1 := by
      rw [h]; rcases dich (p.X k) with h' | h' <;> rw [h'] <;> decide
    refine Pauli.ext ?_ ?_
    · rw [hadamardAt_X, update_eq_add_single, show p.Z k - p.X k = 1 from by rw [h]; ring, X_add,
        X_add, paulix_X, pauliz_X, add_zero]; abel
    · rw [hadamardAt_Z, update_eq_add_single, hv, Z_add, Z_add, paulix_Z, pauliz_Z, zero_add]
  have hLHS : (conjEquiv (hadamardEquiv k) (pauliEquiv p)).toLinearMap =
      hadamardGate k ∘ₗ pauliOperator p ∘ₗ hadamardGate k := by
    apply LinearMap.ext; intro ψ
    simp only [LinearEquiv.coe_coe, conjEquiv_apply, hadamardEquiv_symm_apply, hadamardEquiv_apply,
      pauliEquiv_apply, LinearMap.comp_apply]
  rw [hLHS, hadamardGate_eq, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_smul,
    smul_smul, invSqrt2_mul_self]
  simp only [LinearMap.add_comp, LinearMap.comp_add, pauli_conj_triple]
  rw [show paulix k + p + paulix k = p from by
        rw [show paulix k + p + paulix k = p + (paulix k + paulix k) from by abel, pauli_add_self,
          add_zero],
    show pauliz k + p + pauliz k = p from by
        rw [show pauliz k + p + pauliz k = p + (pauliz k + pauliz k) from by abel, pauli_add_self,
          add_zero],
    show pauliz k + p + paulix k = paulix k + p + pauliz k from by abel]
  simp only [paulix_X, pauliz_X, hzp0, zDotVal_paulix, zDotVal_pauliz, zDotVal_single_right, X_add,
    Pi.add_apply, Pi.single_eq_same, Pi.zero_apply, zero_add, add_zero, e1, mul_one]
  rcases dich (p.X k) with hx | hx <;> rcases dich (p.Z k) with hz | hz
  · rw [hPeq (by rw [hx, hz]), hx, hz]
    simp only [Units.val_pow_eq_pow_val, negOneUnit_val, e0, e1, mul_zero, mul_one, add_zero,
      pow_zero, pow_one]
    module
  · rw [hA2eq (by rw [hx, hz]; decide), hx, hz]
    simp only [Units.val_pow_eq_pow_val, negOneUnit_val, e0, e1,
      show ((1 : ZMod 2) + 1) = 0 from by decide, mul_zero, mul_one, add_zero, pow_zero, pow_one]
    module
  · rw [hA2eq (by rw [hx, hz]; decide), hx, hz]
    simp only [Units.val_pow_eq_pow_val, negOneUnit_val, e0, e1,
      show ((1 : ZMod 2) + 1) = 0 from by decide, mul_zero, mul_one, add_zero, pow_zero, pow_one]
    module
  · rw [hPeq (by rw [hx, hz]), hx, hz]
    simp only [Units.val_pow_eq_pow_val, negOneUnit_val, e0, e1,
      show ((1 : ZMod 2) + 1) = 0 from by decide, mul_zero, mul_one, add_zero, pow_zero, pow_one]
    module

/-- **The Hadamard gate lifts.** `hadamardAt k ∈ range Φ` — the last of the four gate lifts. -/
theorem hadamardAt_mem_cliffordToSp_range (k : Fin n) :
    (⟨hadamardAt k, hadamardAt_isClifford k⟩ : spSubgroup n) ∈ (cliffordToSp (n := n)).range :=
  mem_cliffordToSp_range_of_conj (hadamardAt_isClifford k)
    (fun p => negOneUnit ^ ((p.X k).val * (p.Z k).val)) (fun p => hadamardEquiv_conj k p)

/-! ## The Clifford–symplectic lift, unconditional -/

/-- **`hmem` holds.** All four elementary gates (`H`, `S`, `CNOT`, `CZ`) lift to Hilbert-space
Clifford unitaries, so the gate generators lie in `range Φ`. -/
theorem cliffordGateGens_subset_range (n : ℕ) :
    cliffordGateGens n ⊆ (cliffordToSp (n := n)).range :=
  hmem_of_gate_lifts hadamardAt_mem_cliffordToSp_range phaseAt_mem_cliffordToSp_range
    cnotAt_mem_cliffordToSp_range czAt_mem_cliffordToSp_range

/-- **The Clifford–symplectic lift, unconditional.** Every symplectic automorphism of the Pauli
group lifts to a Clifford unitary on `QubitSpace n`. The gate lifts (`hmem`) and
`spGeneratedByCliffordGates` together discharge `CliffordSymplecticLift`; `Φ = cliffordToSp` is
surjective onto `Sp(2n, 𝔽₂)`. -/
theorem cliffordSymplecticLift_unconditional (n : ℕ) : CliffordSymplecticLift n :=
  cliffordSymplecticLift_of_gateLifts (cliffordGateGens_subset_range n)

end FTQCLib.Hilbert

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.SignedCharacterFrame
import FTQCLib.Hilbert.AffineSymplecticGroup

set_option linter.unusedSectionVars false

/-!
# The selection theory: the frame's gate datum determines the Clifford operator mod phase

Two parts.

**Part 1 — the selection theorem.** The sign character is a faithful fiber coordinate:

* `cliffordSign_eq_phase` — the bridge between `cliffordSign` and the raw conjugation phase;
* `cliffordSign_pauliEquiv` / `cliffordSign_pauli_twist` — moving through the fiber of
  `Clifford → Sp` by a Pauli factor twists the sign character by `(−1)^{ω(w, g·)}`;
* `cliffordOperator_unique_of_sign` — **same symplectic part + same sign character ⟹ equal mod
  global phase**: the frame's gate datum (symplectic map + sign cochain) is a complete coordinate
  system for the projective Clifford group.

**Part 2 — the selected lifts.** The frame validates all three transvections at `k` with the ONE
cochain `tvSignZ`; the selection theorem then pins a unique Hilbert lift per generator, and this
file names all three:

* `τ_Z ↦ phaseGate k` (`SignedCharacterFrame.lean`, imported);
* `τ_X ↦ xRootGate k := H·S†·H` (**the inverse root** — `cliffordSign_xRootGate_eq_frame`), with
  the exact Pauli-dressing identity `xRootGate_eq_paulix_mul : H·S†·H = X_k·(H·S·H)` — the naive
  `H·S·H` is provably the wrong fiber point;
* `τ_Y ↦ hadamardEquiv k` (**the Hadamard itself** — `cliffordSign_hadamardEquiv_eq_frame`): the
  `Y`-transvection over `𝔽₂` is the axis swap, and `H`'s sign character is the same cochain.

The uniqueness theorems `frame_selects_phaseGate` / `frame_selects_xRootGate` /
`frame_selects_hadamardEquiv` combine the two parts, and `hadamard_trace_frame` /
`xRoot_trace_frame` extend the frame-pure trace formula to the new gates. No new operator
evaluations occur anywhere: the one Hilbert-level datum (`α = i`, `SignedCharacterFrame.lean`) plus
the witness file's `μ_H(Y_k) = −1` feed every computation through the crossed-homomorphism law.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.Gates FTQCLib.Frame Complex

variable {n : ℕ}

private lemma zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

/-! ## Witness-irrelevance and congruence -/

/-- `cliffordSign` depends only on the operator, so it transports along operator equalities. -/
theorem cliffordSign_congr {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hUV : U = V)
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) (p : Pauli n) :
    cliffordSign hU p = cliffordSign hV p := by
  subst hUV
  rfl

/-- `cliffordToSymplecticFun` depends only on the operator. -/
theorem cliffordFun_congr {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n} (hUV : U = V)
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V) (p : Pauli n) :
    cliffordToSymplecticFun hU p = cliffordToSymplecticFun hV p := by
  subst hUV
  rfl

/-! ## Part 1: the sign character is a faithful fiber coordinate -/

/-- The bridge: `cliffordSign` is the `I^{xz}`-normalized conjugation phase. -/
theorem cliffordSign_eq_phase {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (p : Pauli n) :
    cliffordSign hU p
      = Complex.I ^ xzWeight p * (cliffordToSymplecticPhase hU p : ℂ)
          * (Complex.I ^ xzWeight (cliffordToSymplecticFun hU p))⁻¹ :=
  cliffordSign_eq_of_conj hU (cliffordToSymplecticFun_spec hU p)

/-- Equal symplectic parts and equal sign characters force equal conjugation phases: the
`I^{xz}`-corrections coincide and cancel. -/
theorem phase_eq_of_sign_eq {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V)
    (hFun : ∀ p, cliffordToSymplecticFun hU p = cliffordToSymplecticFun hV p)
    (hsig : ∀ p, cliffordSign hU p = cliffordSign hV p) (p : Pauli n) :
    (cliffordToSymplecticPhase hU p : ℂ) = (cliffordToSymplecticPhase hV p : ℂ) := by
  have h1 := cliffordSign_eq_phase hU p
  have h2 := cliffordSign_eq_phase hV p
  rw [← hFun p] at h2
  have key := h1.symm.trans ((hsig p).trans h2)
  have hIa : (Complex.I : ℂ) ^ xzWeight p ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hIb : ((Complex.I : ℂ) ^ xzWeight (cliffordToSymplecticFun hU p))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
  exact mul_left_cancel₀ hIa (mul_right_cancel₀ hIb key)

/-- **The selection theorem.** Same symplectic part + same sign character ⟹ equal mod
global phase. Together with `cliffordSign_pauli_twist` this says the sign character is a faithful
coordinate on the fiber of `Clifford → Sp` mod scalar: the frame's gate datum (symplectic map +
sign cochain) determines the Hilbert operator uniquely up to `ℂˣ`. -/
theorem cliffordOperator_unique_of_sign {U V : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (hV : IsCliffordOperator V)
    (h_sym : cliffordToSymplectic hU = cliffordToSymplectic hV)
    (h_sign : ∀ p, cliffordSign hU p = cliffordSign hV p) :
    ∃ α : ℂˣ, V.toLinearMap = (α : ℂ) • U.toLinearMap := by
  have hFun : ∀ p, cliffordToSymplecticFun hU p = cliffordToSymplecticFun hV p := by
    intro p
    rw [← cliffordToSymplectic_apply, ← cliffordToSymplectic_apply, h_sym]
  exact cliffordOperator_unique_mod_phase hU hV h_sym (phase_eq_of_sign_eq hU hV hFun h_sign)

/-- The sign character of a Pauli operator is the commutation character `(−1)^{ω(w,·)}`. -/
theorem cliffordSign_pauliEquiv (w p : Pauli n) :
    cliffordSign (isCliffordOperator_pauliEquiv w) p = (-1 : ℂ) ^ (omega w p).val := by
  have hFun : cliffordToSymplecticFun (isCliffordOperator_pauliEquiv w) p = p := by
    rw [← cliffordToSymplectic_apply, cliffordToSymplectic_pauliEquiv]
    rfl
  have h := cliffordSign_eq_phase (isCliffordOperator_pauliEquiv w) p
  rw [hFun, phase_pauliEquiv_eq] at h
  rw [h, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]

/-- **The fiber twist.** Moving through the fiber of `Clifford → Sp` by a Pauli factor
`P_w` twists the sign character by `(−1)^{ω(w, g·)}`. Since `ω` is nondegenerate these twists
sweep every `±1`-character of the label group, so the sign character separates the fiber points
exactly (mod scalar, by `cliffordOperator_unique_of_sign`). -/
theorem cliffordSign_pauli_twist {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U) (w p : Pauli n) :
    cliffordSign (isCliffordOperator_mul (isCliffordOperator_pauliEquiv w) hU) p
      = (-1 : ℂ) ^ (omega w (cliffordToSymplecticFun hU p)).val * cliffordSign hU p := by
  rw [cliffordSign_mul (isCliffordOperator_pauliEquiv w) hU, cliffordSign_pauliEquiv, mul_comm]

/-! ## Part 2, τ_Y: the Hadamard's sign character is the same frame cochain, globally -/

/-- The `xz`-weight is invariant under the `X↔Z` swap at `k`. -/
lemma xzWeight_hadamardAt (k : Fin n) (p : Pauli n) :
    xzWeight (hadamardAt k p) = xzWeight p := by
  classical
  have hsplit : ∀ q : Pauli n, xzWeight q
      = (q.Z k).val * (q.X k).val + ∑ i ∈ Finset.univ.erase k, (q.Z i).val * (q.X i).val := by
    intro q
    unfold xzWeight zDotVal
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  rw [hsplit (hadamardAt k p), hsplit p]
  congr 1
  · rw [hadamardAt_X, hadamardAt_Z, Function.update_self, Function.update_self, Nat.mul_comm]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [hadamardAt_X, hadamardAt_Z, Function.update_of_ne hik, Function.update_of_ne hik]

/-- Pin the Hadamard conjugation unit to `−1` from the already-proven `μ_H(Y_k) = −1` — no
operator evaluation; the witness value converts through the sign bridge. -/
lemma hadamard_unit_eq (k : Fin n) {u : ℂˣ}
    (hconj : (conjEquiv (hadamardEquiv k) (pauliEquiv (yLabel k))).toLinearMap
      = (u : ℂ) • pauliOperator (hadamardAt k (yLabel k))) :
    (u : ℂ) = -1 := by
  have h := cliffordSign_eq_of_conj (isCliffordOperator_hadamardEquiv k) hconj
  rw [cliffordSign_hadamard_yLabel, hadamardAt_yLabel, xzWeight_yLabel, pow_one] at h
  rw [mul_right_comm, mul_inv_cancel₀ Complex.I_ne_zero, one_mul] at h
  exact h.symm

/-- **The τ_Y face, globally**: the Hadamard's sign character IS the frame cochain —
`cliffordSign (H_k) r = iZ4 (tvSignZ k r)` for every `n`, `k`, `r`. (The `Y`-transvection over
`𝔽₂` is the axis swap, `transvection_yLabel_eq_hadamardAt` below, so `H` is the frame's selected
`τ_Y` lift.) -/
theorem cliffordSign_hadamardEquiv_eq_frame (k : Fin n) (r : Pauli n) :
    cliffordSign (isCliffordOperator_hadamardEquiv k) r = iZ4 (tvSignZ k r) := by
  -- extract the unit from the `Y_k` instance
  have hyx : ((yLabel k).X k) = 1 := by
    unfold yLabel
    rw [X_add, paulix_X, pauliz_X]
    simp
  have hyz : ((yLabel k).Z k) = 1 := by
    unfold yLabel
    rw [Z_add, paulix_Z, pauliz_Z]
    simp
  have huy := hadamardEquiv_conj k (yLabel k)
  rw [hyx, hyz, show ((1 : ZMod 2)).val = 1 from by decide, mul_one, pow_one] at huy
  have hval := hadamard_unit_eq k huy
  -- the general label
  have h := cliffordSign_eq_of_conj (isCliffordOperator_hadamardEquiv k) (hadamardEquiv_conj k r)
  rw [Units.val_pow_eq_pow_val, hval] at h
  rw [h, xzWeight_hadamardAt, mul_right_comm,
    mul_inv_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul,
    show tvSignZ k r = ((2 * ((r.X k).val * (r.Z k).val) : ℕ) : ZMod 4) from by
      unfold tvSignZ; push_cast; ring,
    iZ4_natCast, pow_mul Complex.I 2, Complex.I_sq]

/-! ## The operator identities: `Z·S = S†` and `H·Z = X·H` -/

/-- **`Z_k·S_k = S_k†` exactly** (no phase): the diagonal `(−1)^{v_k}·e^{iπv_k/2}` is
`e^{−iπv_k/2}`. The two square roots of `Z` in the fiber are Pauli-related, and the frame's
cochain choices for `τ_Z` and `τ_X` sit on the two different points. -/
lemma pauliz_mul_phaseGate (k : Fin n) :
    pauliEquiv (pauliz k) * phaseGate k = (phaseGate k).symm := by
  refine LinearEquiv.ext fun ψ => funext fun v => ?_
  rw [LinearEquiv.mul_apply, pauliEquiv_apply]
  show ((-1 : ℂ)) ^ (zDotVal (pauliz k) (v - (pauliz k).X)) * (phaseGate k ψ) (v - (pauliz k).X)
      = (phaseGate k).symm ψ v
  rw [pauliz_X, sub_zero, zDotVal_pauliz]
  show ((-1 : ℂ)) ^ ((v k).val)
        * (Complex.exp (Complex.I * ((Real.pi / 2 * ((v k).val : ℝ) : ℝ) : ℂ)) * ψ v)
      = Complex.exp (Complex.I * ((-(Real.pi / 2 * ((v k).val : ℝ)) : ℝ) : ℂ)) * ψ v
  rcases zmod2_cases (v k) with hv | hv <;> rw [hv]
  · simp [show ((0 : ZMod 2)).val = 0 from rfl]
  · rw [show ((1 : ZMod 2)).val = 1 from by decide]
    rw [show (Real.pi / 2 * ((1 : ℕ) : ℝ) : ℝ) = Real.pi / 2 from by push_cast; ring]
    rw [exp_I_pi_div_two, exp_neg_I_pi_div_two, pow_one]
    ring

/-- **`H_k·Z_k = X_k·H_k`** at the operator level (the conjugation relation, rearranged). -/
lemma hadamardEquiv_mul_pauliz (k : Fin n) :
    hadamardEquiv k * pauliEquiv (pauliz k) = pauliEquiv (paulix k) * hadamardEquiv k := by
  have hconj := hadamardEquiv_conj k (pauliz k)
  rw [show ((pauliz k).X k).val * ((pauliz k).Z k).val = 0 from by rw [pauliz_X]; simp,
    pow_zero, Units.val_one, one_smul, hadamardAt_pauliz, ← pauliEquiv_toLinearMap] at hconj
  have hEq : conjEquiv (hadamardEquiv k) (pauliEquiv (pauliz k)) = pauliEquiv (paulix k) :=
    LinearEquiv.toLinearMap_injective hconj
  refine LinearEquiv.ext fun ψ => ?_
  have h := DFunLike.congr_fun hEq (hadamardEquiv k ψ)
  simp only [conjEquiv_apply, LinearEquiv.symm_apply_apply] at h
  simpa only [LinearEquiv.mul_apply] using h

/-! ## Part 2, τ_X: the selected lift `H·S†·H` -/

/-- The frame's selected `τ_X` lift: **the inverse root** `√X† = H·S†·H`. -/
noncomputable def xRootGate (k : Fin n) : QubitSpace n ≃ₗ[ℂ] QubitSpace n :=
  hadamardEquiv k * (phaseGate k).symm * hadamardEquiv k

theorem isCliffordOperator_xRootGate (k : Fin n) : IsCliffordOperator (xRootGate k) :=
  isCliffordOperator_mul (isCliffordOperator_mul (isCliffordOperator_hadamardEquiv k)
    (isCliffordOperator_symm (isCliffordOperator_phaseGate k))) (isCliffordOperator_hadamardEquiv k)

/-- **The exact Pauli dressing**: `H·S†·H = X_k·(H·S·H)`, on the nose (no phase). The naive
`τ_X` candidate `H·S·H` and the frame's selected lift differ by exactly the Pauli factor the
fiber-twist analysis predicted. -/
theorem xRootGate_eq_paulix_mul (k : Fin n) :
    xRootGate k = pauliEquiv (paulix k) * (hadamardEquiv k * phaseGate k * hadamardEquiv k) := by
  unfold xRootGate
  rw [← pauliz_mul_phaseGate,
    show hadamardEquiv k * (pauliEquiv (pauliz k) * phaseGate k)
        = hadamardEquiv k * pauliEquiv (pauliz k) * phaseGate k from (mul_assoc _ _ _).symm,
    hadamardEquiv_mul_pauliz,
    mul_assoc (pauliEquiv (paulix k)) (hadamardEquiv k) (phaseGate k),
    mul_assoc (pauliEquiv (paulix k)) (hadamardEquiv k * phaseGate k) (hadamardEquiv k)]

/-- The Hadamard's symplectic part, at every label (the general-`k` version of the split-file
computation). -/
lemma cliffordFun_hadamard (k : Fin n) (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv k) p = hadamardAt k p :=
  cliffordFun_eq_of_conj _ (hadamardEquiv_conj k p)

/-- `S†`'s symplectic part is the same shear (`phaseAt` is an involution). -/
lemma cliffordFun_phaseGate_symm (k : Fin n) (q : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_symm (isCliffordOperator_phaseGate k)) q
      = phaseAt k q := by
  have hcg := cliffordFun_congr (pauliz_mul_phaseGate k).symm
    (isCliffordOperator_symm (isCliffordOperator_phaseGate k))
    (isCliffordOperator_mul (isCliffordOperator_pauliEquiv (pauliz k))
      (isCliffordOperator_phaseGate k)) q
  rw [hcg, cliffordToSymplecticFun_mul (isCliffordOperator_pauliEquiv (pauliz k))
      (isCliffordOperator_phaseGate k),
    cliffordFun_phase, ← cliffordToSymplectic_apply, cliffordToSymplectic_pauliEquiv]
  rfl

/-- `ω(Z_k, ·)` reads off the `X`-bit at `k`. -/
lemma omega_pauliz_apply (k : Fin n) (w : Pauli n) : omega (pauliz k) w = w.X k := by
  unfold omega
  rw [pauliz_X, pauliz_Z,
    show (∑ i, (0 : Fin n → ZMod 2) i * w.Z i) = 0 from by simp, add_zero,
    Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_mul]
  · intro i _ hik
    rw [Pi.single_eq_of_ne hik, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- `ω(X_k, ·)` reads off the `Z`-bit at `k`. -/
lemma omega_paulix_apply (k : Fin n) (w : Pauli n) : omega (paulix k) w = w.Z k := by
  unfold omega
  rw [paulix_X, paulix_Z,
    show (∑ i, (0 : Fin n → ZMod 2) i * w.X i) = 0 from by simp, zero_add,
    Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_mul]
  · intro i _ hik
    rw [Pi.single_eq_of_ne hik, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- `S†`'s sign character is the frame cochain at the transported label — the inverse-cocycle
form (`μ_{U⁻¹} = μ_U ∘ g`, with `g = g⁻¹` for the shear). -/
theorem cliffordSign_phaseGate_symm (k : Fin n) (q : Pauli n) :
    cliffordSign (isCliffordOperator_symm (isCliffordOperator_phaseGate k)) q
      = iZ4 (tvSignZ k (phaseAt k q)) := by
  have hcg := cliffordSign_congr (pauliz_mul_phaseGate k).symm
    (isCliffordOperator_symm (isCliffordOperator_phaseGate k))
    (isCliffordOperator_mul (isCliffordOperator_pauliEquiv (pauliz k))
      (isCliffordOperator_phaseGate k)) q
  rw [hcg, cliffordSign_pauli_twist (isCliffordOperator_phaseGate k) (pauliz k),
    cliffordFun_phase, cliffordSign_phaseGate_eq_frame, omega_pauliz_apply, phaseAt_X]
  -- (-1)^{x} * iZ4(2·x·z) = iZ4(2·x·(z+x))
  rw [show tvSignZ k q = ((2 * ((q.X k).val * (q.Z k).val) : ℕ) : ZMod 4) from by
      unfold tvSignZ; push_cast; ring,
    show tvSignZ k (phaseAt k q)
        = ((2 * ((q.X k).val * ((q.Z k + q.X k)).val) : ℕ) : ZMod 4) from by
      unfold tvSignZ
      rw [phaseAt_X, phaseAt_Z, Function.update_self]
      push_cast; ring,
    iZ4_natCast, iZ4_natCast, pow_mul Complex.I 2, pow_mul Complex.I 2, Complex.I_sq]
  have hval1 : ((1 : ZMod 2)).val = 1 := by decide
  have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
  have h2v : ((2 : ZMod 2)).val = 0 := by decide
  rcases zmod2_cases (q.X k) with hx | hx <;> rcases zmod2_cases (q.Z k) with hz | hz <;>
    rw [hx, hz] <;>
    norm_num [hval1, h11, h2v]

/-- The frame cochain squares away: `tvSignZ + tvSignZ = 0` in `ℤ/4` (values `{0,2}`). -/
lemma tvSignZ_add_self (k : Fin n) (p : Pauli n) : tvSignZ k p + tvSignZ k p = 0 := by
  unfold tvSignZ
  generalize (((p.X k).val * (p.Z k).val : ℕ) : ZMod 4) = c
  have h : (2 : ZMod 4) * c + 2 * c = (2 + 2) * c := by ring
  rw [h, show ((2 : ZMod 4) + 2) = 0 from by decide, zero_mul]

/-- **The τ_X face, globally**: the selected lift's sign character IS the frame cochain —
`cliffordSign (H·S†·H) r = iZ4 (tvSignZ k r)` for every `n`, `k`, `r`. The composite computation
collapses because the `μ_{S†}` and trailing `μ_H` factors are the *same* cochain value, and the
cochain squares to `1`. -/
theorem cliffordSign_xRootGate_eq_frame (k : Fin n) (r : Pauli n) :
    cliffordSign (isCliffordOperator_xRootGate k) r = iZ4 (tvSignZ k r) := by
  have h1 : cliffordSign (isCliffordOperator_xRootGate k) r
      = cliffordSign (isCliffordOperator_mul
          (isCliffordOperator_mul (isCliffordOperator_hadamardEquiv k)
            (isCliffordOperator_symm (isCliffordOperator_phaseGate k)))
          (isCliffordOperator_hadamardEquiv k)) r := rfl
  rw [h1,
    cliffordSign_mul (isCliffordOperator_mul (isCliffordOperator_hadamardEquiv k)
        (isCliffordOperator_symm (isCliffordOperator_phaseGate k)))
      (isCliffordOperator_hadamardEquiv k),
    cliffordSign_mul (isCliffordOperator_hadamardEquiv k)
      (isCliffordOperator_symm (isCliffordOperator_phaseGate k)),
    cliffordFun_hadamard, cliffordFun_phaseGate_symm,
    cliffordSign_phaseGate_symm, cliffordSign_hadamardEquiv_eq_frame,
    cliffordSign_hadamardEquiv_eq_frame, ← iZ4_add, tvSignZ_add_self,
    show iZ4 (0 : ZMod 4) = 1 from by unfold iZ4; norm_num, mul_one]

/-- The selected `τ_X` lift's symplectic part is the `X`-transvection. -/
theorem cliffordFun_xRootGate (k : Fin n) (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_xRootGate k) p
      = transvectionEquiv (paulix k) p := by
  have h1 : cliffordToSymplecticFun (isCliffordOperator_xRootGate k) p
      = cliffordToSymplecticFun (isCliffordOperator_mul
          (isCliffordOperator_mul (isCliffordOperator_hadamardEquiv k)
            (isCliffordOperator_symm (isCliffordOperator_phaseGate k)))
          (isCliffordOperator_hadamardEquiv k)) p := rfl
  rw [h1,
    cliffordToSymplecticFun_mul (isCliffordOperator_mul (isCliffordOperator_hadamardEquiv k)
        (isCliffordOperator_symm (isCliffordOperator_phaseGate k)))
      (isCliffordOperator_hadamardEquiv k),
    cliffordToSymplecticFun_mul (isCliffordOperator_hadamardEquiv k)
      (isCliffordOperator_symm (isCliffordOperator_phaseGate k)),
    cliffordFun_hadamard, cliffordFun_phaseGate_symm, cliffordFun_hadamard]
  exact hadamardAt_phaseAt_hadamardAt k p
where
  /-- The label identity: `hadamardAt ∘ phaseAt ∘ hadamardAt = τ_{X_k}`. -/
  hadamardAt_phaseAt_hadamardAt (k : Fin n) (p : Pauli n) :
      hadamardAt k (phaseAt k (hadamardAt k p)) = transvectionEquiv (paulix k) p := by
    rw [transvectionEquiv_apply, omega_paulix_apply]
    rcases zmod2_cases (p.Z k) with hz | hz
    · rw [hz, zero_smul, add_zero]
      refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hik : i = k
      · subst hik
        simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_self, hz]
      · simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_of_ne hik]
      · subst hik
        simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_self, hz]
      · simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_of_ne hik]
    · rw [hz, one_smul]
      refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hik : i = k
      · subst hik
        simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_self,
          X_add, paulix_X, Pi.single_eq_same, hz, add_comm]
      · simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_of_ne hik,
          X_add, paulix_X, Pi.single_eq_of_ne hik]
      · subst hik
        simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_self,
          Z_add, paulix_Z, hz]
      · simp [hadamardAt_X, hadamardAt_Z, phaseAt_X, phaseAt_Z, Function.update_of_ne hik,
          Z_add, paulix_Z]

/-- The `Y`-transvection over `𝔽₂` IS the axis swap: `τ_{Y_k} = hadamardAt k` as label maps.
(With `cliffordSign_hadamardEquiv_eq_frame`, this says the frame's selected `τ_Y` lift is the
Hadamard itself.) -/
lemma transvection_yLabel_eq_hadamardAt (k : Fin n) (p : Pauli n) :
    transvectionEquiv (paulix k + pauliz k) p = hadamardAt k p := by
  rw [transvectionEquiv_apply, omega_add_left, omega_paulix_apply, omega_pauliz_apply]
  rcases zmod2_cases (p.X k) with hx | hx <;> rcases zmod2_cases (p.Z k) with hz | hz
  · rw [hx, hz, show ((0 : ZMod 2) + 0) = 0 from rfl, zero_smul, add_zero]
    refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hik : i = k
    · subst hik
      rw [hadamardAt_X, Function.update_self, hz, hx]
    · rw [hadamardAt_X, Function.update_of_ne hik]
    · subst hik
      rw [hadamardAt_Z, Function.update_self, hx, hz]
    · rw [hadamardAt_Z, Function.update_of_ne hik]
  · rw [hx, hz, show ((1 : ZMod 2) + 0) = 1 from rfl, one_smul]
    refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hik : i = k
    · subst hik
      simp [hadamardAt_X, Function.update_self, X_add, paulix_X, pauliz_X,
        Pi.single_eq_same, hx, hz]
    · simp [hadamardAt_X, Function.update_of_ne hik, X_add, paulix_X, pauliz_X,
        Pi.single_eq_of_ne hik]
    · subst hik
      simp [hadamardAt_Z, Function.update_self, Z_add, paulix_Z, pauliz_Z,
        Pi.single_eq_same, hx, hz, show ((1 : ZMod 2) + 1) = 0 from by decide]
    · simp [hadamardAt_Z, Function.update_of_ne hik, Z_add, paulix_Z, pauliz_Z,
        Pi.single_eq_of_ne hik]
  · rw [hx, hz, show ((0 : ZMod 2) + 1) = 1 from rfl, one_smul]
    refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hik : i = k
    · subst hik
      simp [hadamardAt_X, Function.update_self, X_add, paulix_X, pauliz_X,
        Pi.single_eq_same, hx, hz, show ((1 : ZMod 2) + 1) = 0 from by decide]
    · simp [hadamardAt_X, Function.update_of_ne hik, X_add, paulix_X, pauliz_X,
        Pi.single_eq_of_ne hik]
    · subst hik
      simp [hadamardAt_Z, Function.update_self, Z_add, paulix_Z, pauliz_Z,
        Pi.single_eq_same, hx, hz]
    · simp [hadamardAt_Z, Function.update_of_ne hik, Z_add, paulix_Z, pauliz_Z,
        Pi.single_eq_of_ne hik]
  · rw [hx, hz, show ((1 : ZMod 2) + 1) = 0 from by decide, zero_smul, add_zero]
    refine Pauli.ext ?_ ?_ <;> funext i <;> by_cases hik : i = k
    · subst hik
      rw [hadamardAt_X, Function.update_self, hz, hx]
    · rw [hadamardAt_X, Function.update_of_ne hik]
    · subst hik
      rw [hadamardAt_Z, Function.update_self, hx, hz]
    · rw [hadamardAt_Z, Function.update_of_ne hik]

/-- The Hadamard's symplectic part is the `Y`-transvection. -/
theorem cliffordFun_hadamard_transvection (k : Fin n) (p : Pauli n) :
    cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv k) p
      = transvectionEquiv (paulix k + pauliz k) p := by
  rw [cliffordFun_hadamard, transvection_yLabel_eq_hadamardAt]

/-! ## Uniqueness: the frame datum selects each lift, uniquely mod phase -/

/-- **The frame selects `S`.** Any Clifford with the shear's symplectic part and the frame
cochain as sign character IS the phase gate, up to global phase. -/
theorem frame_selects_phaseGate (k : Fin n) {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U)
    (h_sym : cliffordToSymplectic hU = cliffordToSymplectic (isCliffordOperator_phaseGate k))
    (h_sign : ∀ r, cliffordSign hU r = iZ4 (tvSignZ k r)) :
    ∃ α : ℂˣ, U.toLinearMap = (α : ℂ) • (phaseGate k).toLinearMap :=
  cliffordOperator_unique_of_sign (isCliffordOperator_phaseGate k) hU h_sym.symm
    (fun r => (cliffordSign_phaseGate_eq_frame k r).trans (h_sign r).symm)

/-- **The frame selects `H·S†·H`** as the `τ_X` lift, uniquely mod phase. -/
theorem frame_selects_xRootGate (k : Fin n) {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U)
    (h_sym : cliffordToSymplectic hU = cliffordToSymplectic (isCliffordOperator_xRootGate k))
    (h_sign : ∀ r, cliffordSign hU r = iZ4 (tvSignZ k r)) :
    ∃ α : ℂˣ, U.toLinearMap = (α : ℂ) • (xRootGate k).toLinearMap :=
  cliffordOperator_unique_of_sign (isCliffordOperator_xRootGate k) hU h_sym.symm
    (fun r => (cliffordSign_xRootGate_eq_frame k r).trans (h_sign r).symm)

/-- **The frame selects `H`** as the `τ_Y` lift, uniquely mod phase. -/
theorem frame_selects_hadamardEquiv (k : Fin n) {U : QubitSpace n ≃ₗ[ℂ] QubitSpace n}
    (hU : IsCliffordOperator U)
    (h_sym : cliffordToSymplectic hU
      = cliffordToSymplectic (isCliffordOperator_hadamardEquiv k))
    (h_sign : ∀ r, cliffordSign hU r = iZ4 (tvSignZ k r)) :
    ∃ α : ℂˣ, U.toLinearMap = (α : ℂ) • (hadamardEquiv k).toLinearMap :=
  cliffordOperator_unique_of_sign (isCliffordOperator_hadamardEquiv k) hU h_sym.symm
    (fun r => (cliffordSign_hadamardEquiv_eq_frame k r).trans (h_sign r).symm)

/-! ## The frame-pure trace formulas for the new gates -/

/-- `Tr(H_k)·Tr(H_k⁻¹)` is a frame-pure character sum (its value is `0` — the vanishing branch —
because the cochain is the nontrivial character `(−1)^{X_k Z_k}` on the swap's fixed labels). -/
theorem hadamard_trace_frame (k : Fin n) :
    LinearMap.trace ℂ (QState n) (qClifford (hadamardEquiv k)).toLinearMap
        * LinearMap.trace ℂ (QState n) (qClifford (hadamardEquiv k)).symm.toLinearMap
      = ∑ p ∈ Finset.univ.filter
          (fun p : Pauli n =>
            cliffordToSymplecticFun (isCliffordOperator_hadamardEquiv k) p = p),
          iZ4 (tvSignZ k p) := by
  classical
  rw [signed_trace_mul_trace_inv (isCliffordOperator_hadamardEquiv k)]
  exact Finset.sum_congr rfl fun p _ => cliffordSign_hadamardEquiv_eq_frame k p

/-- `Tr(√X†)·Tr(√X)` is a frame-pure character sum. -/
theorem xRoot_trace_frame (k : Fin n) :
    LinearMap.trace ℂ (QState n) (qClifford (xRootGate k)).toLinearMap
        * LinearMap.trace ℂ (QState n) (qClifford (xRootGate k)).symm.toLinearMap
      = ∑ p ∈ Finset.univ.filter
          (fun p : Pauli n =>
            cliffordToSymplecticFun (isCliffordOperator_xRootGate k) p = p),
          iZ4 (tvSignZ k p) := by
  classical
  rw [signed_trace_mul_trace_inv (isCliffordOperator_xRootGate k)]
  exact Finset.sum_congr rfl fun p _ => cliffordSign_xRootGate_eq_frame k p

end FTQCLib.Hilbert

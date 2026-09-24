/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CliffordWordFloor
import FTQCLib.Examples.CarrierCliffordCheck
import FTQCLib.Hilbert.CharSumCorrespondence

/-!
# Check: Clifford words on the floor

Axiom rows for every declaration of `CliffordWordFloor`, the **agreement rows** against the Hilbert
interpreter (this Check imports `FTQCLib.Hilbert`; the topic module does not), and worked
examples.

* Agreement, letter by letter and for every amplitude function: the referee's Walsh transform is
  `hadamardGate`, its phase is `diagonalGate (realPhase D)`, its permutation is `cnotGate`; hence
  `runNormalAmp` on a well-formed word is the head-first Hilbert circuit `runNormalHilbert`, and the
  Hilbert state `F` of a run record is the Hilbert circuit on the input's (`F_runNormal`).
* **Two H's** on the uniform record `Kpp` through the composite: a floor at height `0` with
  amplitude `2` at `00` and `0` at `01`, while two free H's leave two bound bits (`applyHFiner`
  twice has height `2`); the same on the graph state `K3`; and the word `CZ, H₀` on `Kpp`
  reproduces the Bell amplitude of `CarrierCliffordCheck`.
* **The level check** — the letter set is closed under a global phase (`S` times a phase at
  precision five is well-formed, the check the raw effective level fails), the level-three
  exponent `X₀` at precision three is rejected, and the rejection is not a formality: the class
  rule on that exponent takes a floor off the floor (`not_isFloor_applyDiagPolar_XT`), which is
  the row showing that `WF` cannot be replaced by `True`.
* **Precision one** — `S` is a well-formed letter there too, and its symplectic map is the
  identity: at precision one the letter is `Z`, whose shear is trivial.
* **Two-letter diagonal words** — the mixed `S · CZ` word and the rank-four `CZ₀₁ · CZ₂₃` word are
  each the class rule on their sum exponent, on every record at positive precision, and the sums
  are themselves well-formed letters.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer FTQCLib.Hilbert
  FTQCLib.Frame.Correspondence

variable {n : ℕ}

/-! ## Agreement with the Hilbert interpreter -/

/-- The Hilbert state of a record is its amplitude. -/
theorem F_eq_amp (S : KernelSumState n) : F S = amp S := rfl

/-- The referee's Walsh transform is the Hilbert `hadamardGate`, on every amplitude function. -/
theorem walshTransform_eq_hadamardGate (k : Fin n) (f : (Fin n → ZMod 2) → ℂ) :
    walshTransform k f = hadamardGate k f := by
  funext w
  rw [hadamardGate_apply]
  unfold walshTransform
  rw [show (∑ b : ZMod 2, (-1 : ℂ) ^ ((w k).val * b.val) * f (Function.update w k b)) =
      (-1 : ℂ) ^ ((w k).val * (0 : ZMod 2).val) * f (Function.update w k 0) +
        (-1 : ℂ) ^ ((w k).val * (1 : ZMod 2).val) * f (Function.update w k 1) from
      Fin.sum_univ_two _]
  rw [ZMod.val_zero, mul_zero, pow_zero, one_mul, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
    mul_one, signOf_eq, invSqrt2, Complex.ofReal_inv, one_div]

/-- The Hilbert interpreter of a letter (CNOT with distinct bits; the identity otherwise). -/
noncomputable def gateHilbertN {m : ℕ} (g : NormalGate n m) : QubitSpace n → QubitSpace n :=
  match g with
  | .H k => hadamardGate k
  | .Diag D => diagonalGate (DiagPhase.realPhase D)
  | .Cnot i j => if h : i ≠ j then cnotGate i j h else id

/-- The Hilbert interpreter on a word, head letter first. -/
noncomputable def runNormalHilbert {m : ℕ} (gs : List (NormalGate n m)) (ψ : QubitSpace n) :
    QubitSpace n :=
  gs.foldl (fun ψ g => gateHilbertN g ψ) ψ

/-- **Agreement, letter by letter.** On a well-formed letter the referee is the Hilbert gate. -/
theorem gateAmp_eq_gateHilbertN {m : ℕ} (g : NormalGate n m) (hg : g.WF) (f : QubitSpace n) :
    gateAmp g f = gateHilbertN g f := by
  cases g with
  | H k =>
    simp only [gateAmp, gateHilbertN]
    exact walshTransform_eq_hadamardGate k f
  | Diag D =>
    funext w
    simp only [gateAmp, gateHilbertN]
    rw [diagonalGate_apply, exp_realPhase_eq_charOf]
  | Cnot i j =>
    change i ≠ j at hg
    funext w
    simp only [gateAmp, gateHilbertN, dif_pos hg]
    rfl

/-- **Agreement on words.** -/
theorem runNormalAmp_eq_runNormalHilbert {m : ℕ} (gs : List (NormalGate n m)) (hwf : WordWF gs)
    (f : QubitSpace n) : runNormalAmp gs f = runNormalHilbert gs f := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.WF := hwf g (List.mem_cons_self ..)
    have hwf' : WordWF gs := fun g' hg' => hwf g' (List.mem_cons_of_mem _ hg')
    rw [runNormalAmp_cons, gateAmp_eq_gateHilbertN g hg f]
    exact ih hwf' _

/-- **The correspondence for the run record.** The Hilbert state of a well-formed word's run on a
height-`0` floor is the Hilbert circuit on the input's Hilbert state. -/
theorem F_runNormal {m : ℕ} (gs : List (NormalGate n m)) (hwf : WordWF gs) {S : KernelSumState n}
    (hF : IsFloor S) (h0 : S.h = 0) (hm : S.m = m) :
    F (runNormal gs S) = runNormalHilbert gs (F S) := by
  rw [F_eq_amp, F_eq_amp, (runNormal_floor gs hwf hF h0 hm).2.2.2,
    runNormalAmp_eq_runNormalHilbert gs hwf]

/-! ## Two H's through the composite -/

/-- The word `H₀, H₁`. -/
noncomputable def hhWord : List (NormalGate 2 1) := [.H 0, .H 1]

theorem hhWord_wf : WordWF hhWord := by
  intro g hg
  simp only [hhWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> trivial

/-- Two free H's leave two bound bits. -/
theorem applyHFiner_twice_h :
    (applyHFiner 1 (applyHFiner 0 (ofKernelState Kpp))).h = 2 := rfl

/-- Two H's: the composite on the uniform record `Kpp` is a floor at height `0`. -/
theorem isFloor_hh_Kpp : IsFloor (runNormal hhWord (ofKernelState Kpp)) :=
  (runNormal_floor hhWord hhWord_wf isFloor_Kpp rfl rfl).1

theorem hh_Kpp_h : (runNormal hhWord (ofKernelState Kpp)).h = 0 :=
  (runNormal_floor hhWord hhWord_wf isFloor_Kpp rfl rfl).2.1

/-- The referee on the constant `1`: `H₀` then `H₁`. -/
theorem amp_hh_Kpp :
    amp (runNormal hhWord (ofKernelState Kpp)) =
      walshTransform 1 (walshTransform 0 (amp (ofKernelState Kpp))) :=
  (runNormal_floor hhWord hhWord_wf isFloor_Kpp rfl rfl).2.2.2

/-- `H₀` on the constant `1`: `√2` where `w₀ = 0`, `0` otherwise. -/
theorem walsh0_Kpp (w : Fin 2 → ZMod 2) :
    walshTransform 0 (amp (ofKernelState Kpp)) w =
      if w 0 = 0 then (Real.sqrt 2 : ℂ) else 0 := by
  unfold walshTransform
  rw [amp_Kpp, amp_Kpp, signOf_eq, mul_one]
  rcases zmod_two_eq_zero_or_one (w 0) with h0 | h0 <;> rw [h0]
  · rw [if_pos rfl, ZMod.val_zero, pow_zero, one_add_one_eq_two]
    exact one_div_sqrt_two_mul_two
  · rw [if_neg one_ne_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide, pow_one]
    ring

/-- Two H's on `Kpp`: the amplitude at `00` is `2`. -/
theorem amp_hh_Kpp_00 : amp (runNormal hhWord (ofKernelState Kpp)) ![0, 0] = 2 := by
  rw [amp_hh_Kpp, walshTransform, walsh0_Kpp, walsh0_Kpp]
  have e0 : (Function.update (![0, 0] : Fin 2 → ZMod 2) 1 0) 0 = 0 := by decide
  have e1 : (Function.update (![0, 0] : Fin 2 → ZMod 2) 1 1) 0 = 0 := by decide
  have g1 : (![0, 0] : Fin 2 → ZMod 2) 1 = 0 := by decide
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)
  rw [e0, e1, g1, if_pos rfl, signOf_zero', one_mul, ← two_mul, mul_comm (2 : ℂ), ← mul_assoc,
    one_div_mul_cancel hs, one_mul]

/-- Two H's on `Kpp`: the amplitude at `01` is `0`. -/
theorem amp_hh_Kpp_01 : amp (runNormal hhWord (ofKernelState Kpp)) ![0, 1] = 0 := by
  rw [amp_hh_Kpp, walshTransform, walsh0_Kpp, walsh0_Kpp]
  have e0 : (Function.update (![0, 1] : Fin 2 → ZMod 2) 1 0) 0 = 0 := by decide
  have e1 : (Function.update (![0, 1] : Fin 2 → ZMod 2) 1 1) 0 = 0 := by decide
  have g1 : (![0, 1] : Fin 2 → ZMod 2) 1 = 1 := by decide
  rw [e0, e1, g1, if_pos rfl, signOf_one']
  ring

/-- Two H's on the graph state: two H's through the composite stay on the floor at height `0`. -/
theorem isFloor_hh_K3 : IsFloor (runNormal hhWord (ofKernelState K3)) :=
  (runNormal_floor hhWord hhWord_wf isFloor_K3 rfl rfl).1

theorem hh_K3_h : (runNormal hhWord (ofKernelState K3)).h = 0 :=
  (runNormal_floor hhWord hhWord_wf isFloor_K3 rfl rfl).2.1

/-! ## The Bell record through the composite -/

/-- The word `CZ₀₁, H₀` at `m = 1`. -/
noncomputable def czHWord : List (NormalGate 2 1) := [czLetter 1 0 1, .H 0]

theorem czHWord_wf : WordWF czHWord := by
  intro g hg
  simp only [czHWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact czLetter_wf 1 0 1
  · trivial

theorem isFloor_czH_Kpp : IsFloor (runNormal czHWord (ofKernelState Kpp)) :=
  (runNormal_floor czHWord czHWord_wf isFloor_Kpp rfl rfl).1

theorem czH_Kpp_h : (runNormal czHWord (ofKernelState Kpp)).h = 0 :=
  (runNormal_floor czHWord czHWord_wf isFloor_Kpp rfl rfl).2.1

/-- The `CZ` letter on `Kpp` gives the graph record's amplitude. -/
theorem gateAmp_cz_Kpp :
    gateAmp (czLetter 1 0 1) (amp (ofKernelState Kpp)) = amp (ofKernelState K3) := by
  funext w
  simp only [gateAmp, czLetter]
  rw [amp_Kpp, amp_K3, czGate_eval]
  simp only [mul_one, Nat.sub_self, pow_zero, one_mul]

/-- **The Bell record through the composite.** The word `CZ, H₀` on `Kpp` has the Bell record's
amplitude. -/
theorem amp_czH_Kpp : amp (runNormal czHWord (ofKernelState Kpp)) = amp bell3 := by
  rw [(runNormal_floor czHWord czHWord_wf isFloor_Kpp rfl rfl).2.2.2, amp_bell3]
  change walshTransform 0 (gateAmp (czLetter 1 0 1) (amp (ofKernelState Kpp))) = _
  rw [gateAmp_cz_Kpp]

/-! ## The level check on the letters -/

/-- **The global-phase control.** `S` times a global phase is a well-formed letter: the extended
level strips the constant first. -/
theorem globalPhase_letter_wf :
    (NormalGate.Diag (DiagPhase.sGate 5 (0 : Fin 1) + MvPolynomial.C 1) : NormalGate 1 5).WF :=
  diagLetter_wf_add_C (sLetter_wf 5 0) 1

/-- **Discriminating.** The raw effective level rejects that same exponent — it charges the
constant `m − 1 − v₂(c) = 4` — which is why the check is `levelExt` and not `effectiveLevel`. -/
theorem effectiveLevel_globalPhase_not_le_two :
    ¬ (effectiveLevel (DiagPhase.sGate 5 (0 : Fin 1) + MvPolynomial.C 1) ≤ 2) := by
  have hc : (1 : ZMod (2 ^ 5)) ≠ 0 := by decide
  have hco : (DiagPhase.sGate 5 (0 : Fin 1) + MvPolynomial.C 1).coeff 0 = 1 := by
    rw [MvPolynomial.coeff_add, DiagPhase.sGate_eq_monomial, MvPolynomial.coeff_monomial,
      if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), MvPolynomial.coeff_C, if_pos rfl, zero_add]
  intro hle
  have h0 : effLevelMonom 5 ((DiagPhase.sGate 5 (0 : Fin 1) + MvPolynomial.C 1).coeff 0) 0 ≤ 2 :=
    le_trans (Finset.le_sup (f := fun d => effLevelMonom 5
      ((DiagPhase.sGate 5 (0 : Fin 1) + MvPolynomial.C 1).coeff d) d)
      (MvPolynomial.mem_support_iff.mpr (by rw [hco]; exact hc))) hle
  rw [hco] at h0
  unfold effLevelMonom at h0
  rw [twoAdicVal_of_ne_zero hc, show (1 : ZMod (2 ^ 5)).val = 1 by decide,
    Nat.factorization_one] at h0
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sum_zero_index] at h0
  omega

/-- `X₀` at precision three, as a monomial. -/
theorem X_three_eq_monomial :
    (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3)
      = MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) 1 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_eq_monomial_iff]
  exact Or.inl ⟨rfl, rfl⟩

/-- Its Boolean normal form is itself. -/
theorem boolReduce_X_three :
    boolReduce (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3)
      = MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) 1 := by
  rw [X_three_eq_monomial, boolReduce_monomial (by decide : (1 : ZMod (2 ^ 3)) ≠ 0),
    boolShadow_eq_self_of_le_one (fun k => by rw [Finsupp.single_apply]; split_ifs <;> omega)]

/-- **The level-three exponent.** `X₀` at precision three has extended level `3`. -/
theorem levelExt_X_three : levelExt (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3) = 3 := by
  have hc : (1 : ZMod (2 ^ 3)) ≠ 0 := by decide
  unfold levelExt
  rw [X_three_eq_monomial, MvPolynomial.coeff_monomial,
    if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), MvPolynomial.C_0, sub_zero,
    boolReduce_monomial hc,
    boolShadow_eq_self_of_le_one (fun k => by rw [Finsupp.single_apply]; split_ifs <;> omega),
    effectiveLevel_monomial_eq hc]
  unfold effLevelMonom
  rw [twoAdicVal_of_ne_zero hc, show (1 : ZMod (2 ^ 3)).val = 1 by decide, Nat.factorization_one,
    Finsupp.sum_single_index (by rfl)]
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  decide

/-- **The level-three letter is rejected.** -/
theorem not_wf_X_three :
    ¬ (NormalGate.Diag (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3)).WF := by
  change ¬ (levelExt (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3) ≤ 2)
  rw [levelExt_X_three]
  omega

/-! ## The rejection is not a formality: the class rule on a level-three exponent -/

/-- The uniform record on one qubit at precision three, stabilizer `⟨X₀⟩`. -/
noncomputable def KT : KernelState 1 := ⟨3, 0, 1, lagX, 0⟩

/-- `KT` denotes the constant `1`. -/
theorem amp_KT (w : Fin 1 → ZMod 2) : amp (ofKernelState KT) w = 1 := by
  rw [amp_ofKernelState_pos KT (lagX_support w)]
  change (1 : ℂ) * charOf 3 (DiagPhase.eval (0 : DiagPhase 1 3) w) = 1
  rw [show DiagPhase.eval (0 : DiagPhase 1 3) w = 0 by unfold DiagPhase.eval; simp, charOf_zero,
    one_mul]

/-- The amplitude after the class rule on `X₀`: `ζ₈^{w₀}`. -/
theorem amp_applyDiagPolar_KT (w : Fin 1 → ZMod 2) :
    amp (applyDiagPolar (ofKernelState KT) (MvPolynomial.X 0)) w
      = charOf 3 (((w 0).val : ℕ) : ZMod (2 ^ 3)) := by
  rw [amp_applyDiagPolar]
  change charOf 3 (DiagPhase.eval (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3) w) *
    amp (ofKernelState KT) w = _
  rw [amp_KT, mul_one, DiagPhase.eval_X]

/-- The `(0,0)` entry of the polar matrix of `X₀`'s normal form: the diagonal bit reads
`2 · 1 ≠ 0` in `ZMod 8`. -/
theorem polarMatrix_X_three_00 :
    polarMatrix (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) (1 : ZMod (2 ^ 3))
      : DiagPhase 1 3) 0 0 = 1 := by
  rw [polarMatrix_apply_self, MvPolynomial.coeff_monomial, if_pos rfl,
    if_neg (by decide : ¬ (2 * (1 : ZMod (2 ^ 3)) = 0))]

/-- The polar matrix of `X₀` at precision three is the unit at `(0, 0)`. -/
theorem polarMatrix_X_three :
    polarMatrix (boolReduce (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3))
      = Matrix.single 0 0 1 := by
  rw [boolReduce_X_three]
  ext a b
  fin_cases a
  fin_cases b
  exact polarMatrix_X_three_00

/-- `Y₀` is in the sheared Lagrangian: the class rule sends `⟨X₀⟩` to `⟨Y₀⟩`. -/
theorem mem_L_applyDiagPolar_KT :
    (paulix 0 + pauliz 0 : Pauli 1) ∈
      (applyDiagPolar (ofKernelState KT) (MvPolynomial.X 0)).L := by
  change (paulix 0 + pauliz 0 : Pauli 1) ∈
    Submodule.map (zShearBy (Matrix.mulVecLin
      (polarMatrix (boolReduce (MvPolynomial.X (0 : Fin 1) : DiagPhase 1 3))))) lagX
  rw [polarMatrix_X_three, mulVecLin_single_self]
  refine Submodule.mem_map.mpr ⟨paulix 0, Submodule.mem_span_singleton_self _, ?_⟩
  change zShear 0 (Pi.single 0 1) (paulix 0) = _
  decide

/-- **`WF` cannot be replaced by `True`.** The class rule on the level-three exponent `X₀` shears
`⟨X₀⟩` to `⟨Y₀⟩`, and the amplitude `(1, ζ₈)` is not a sign eigenvector of `Y₀`: the scalar the
record would need is `ζ₈^7`, and the two signs are `ζ₈^0` and `ζ₈^4`. The output is a carrier, not
a floor — so the level check the alphabet applies is doing work. -/
theorem not_isFloor_applyDiagPolar_KT :
    ¬ IsFloor (applyDiagPolar (ofKernelState KT) (MvPolynomial.X 0)) := by
  intro hF
  obtain ⟨s, hs⟩ := hF.2 _ mem_L_applyDiagPolar_KT
  have h := congrFun hs 0
  have hy : yWeight (paulix 0 + pauliz 0 : Pauli 1) = 1 := by decide
  have hz : zDot (paulix 0 + pauliz 0 : Pauli 1)
      (0 + (paulix 0 + pauliz 0 : Pauli 1).X) = 1 := by decide
  have hw1 : (0 + (paulix 0 + pauliz 0 : Pauli 1).X) = Pi.single 0 1 := by decide
  have hsgn : ((-1 : ℂ)) ^ s.val
      = charOf 3 ((2 : ZMod (2 ^ 3)) ^ (3 - 1) * ((s.val : ℕ) : ZMod (2 ^ 3))) :=
    (charOf_two_pow_mul (by omega) s.val).symm
  have hI : (Complex.I : ℂ) = charOf 3 2 := by
    rw [show (2 : ZMod (2 ^ 3)) = (2 : ZMod (2 ^ 3)) ^ (3 - 2) * ((1 : ℕ) : ZMod (2 ^ 3)) by decide,
      charOf_two_pow_sub_two_mul (by omega), pow_one]
  have hn : ((-1 : ℂ)) = charOf 3 4 := by
    rw [show (4 : ZMod (2 ^ 3)) = (2 : ZMod (2 ^ 3)) ^ (3 - 1) * ((1 : ℕ) : ZMod (2 ^ 3)) by decide,
      charOf_two_pow_mul (by omega), pow_one]
  rw [pauliAct, hy, hz, hw1, amp_applyDiagPolar_KT, amp_applyDiagPolar_KT,
    show (((Pi.single 0 1 : Fin 1 → ZMod 2) 0).val : ℕ) = 1 by decide,
    show (((0 : Fin 1 → ZMod 2) 0).val : ℕ) = 0 by decide, hsgn, pow_one, pow_one, hI, hn,
    Nat.cast_zero, charOf_zero, mul_one, ← charOf_add, ← charOf_add] at h
  have h7 := (charOf_eq_iff 3 _ _).mp h
  rcases zmod_two_eq_zero_or_one s with rfl | rfl <;> revert h7 <;> decide

/-! ## Precision one: `S` is a letter there, and its map is the identity -/

/-- `S` is a well-formed letter at precision one. -/
theorem sLetter_one_wf : (sLetter 1 (0 : Fin 1)).WF := sLetter_wf 1 0

/-- **At precision one the `S` letter's symplectic map is the identity**: its polar matrix is zero
(the diagonal bit reads `2c`, and `2c = 0` for every `c` in `ZMod 2`), so the letter is `Z` and
leaves the Lagrangian where it is. -/
theorem letterLin_sLetter_one (i : Fin n) : letterLin (sLetter 1 i) = LinearMap.id := by
  change zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce (DiagPhase.sGate 1 i)))) = _
  rw [DiagPhase.boolReduce_sGate, DiagPhase.polarMatrix_sGate_one, Matrix.mulVecLin_zero,
    zShearBy_zero]

/-- The `Z` letter's map is the identity at precision one too. -/
theorem letterLin_zLetter_one (i : Fin n) : letterLin (zLetter 1 i) = LinearMap.id :=
  letterLin_zLetter le_rfl i

/-! ## Two-letter diagonal words -/

/-- **The mixed `S · CZ` word is the class rule on the sum exponent**, on every record at positive
precision — through the composition theorem, with no matrix computation. -/
theorem runNormal_mix_eq (S : KernelSumState 2) (hm : 1 ≤ S.m) :
    runNormal [sLetter S.m 0, czLetter S.m 0 1] S
      = applyDiagPolar S (DiagPhase.sGate S.m 0 + DiagPhase.czGate S.m 0 1) := by
  change runNormal [NormalGate.Diag (DiagPhase.sGate S.m 0),
    NormalGate.Diag (DiagPhase.czGate S.m 0 1)] S = _
  exact runNormal_pair_diag hm (DiagPhase.levelExt_sGate_le_two S.m 0)
    (DiagPhase.levelExt_czGate_le_two S.m 0 1)

/-- The mixed sum is itself a well-formed letter. -/
theorem mix_sum_wf (m : ℕ) :
    (NormalGate.Diag (DiagPhase.sGate m (0 : Fin 2) + DiagPhase.czGate m 0 1)
      : NormalGate 2 m).WF :=
  diagLetter_wf_add (sLetter_wf m 0) (czLetter_wf m 0 1)

/-- **The rank-four word `CZ₀₁ · CZ₂₃` is the class rule on its sum exponent** — the exponent whose
polar matrix is the row of no shear at one bit (`ZShearCheck.not_exists_shearRow_eq_polar4`), so
the general shear of the constructor is what makes the two-letter word one gate. -/
theorem runNormal_rank4_eq (S : KernelSumState 4) (hm : 1 ≤ S.m) :
    runNormal [czLetter S.m 0 1, czLetter S.m 2 3] S
      = applyDiagPolar S (DiagPhase.czGate S.m 0 1 + DiagPhase.czGate S.m 2 3) := by
  change runNormal [NormalGate.Diag (DiagPhase.czGate S.m 0 1),
    NormalGate.Diag (DiagPhase.czGate S.m 2 3)] S = _
  exact runNormal_pair_diag hm (DiagPhase.levelExt_czGate_le_two S.m 0 1)
    (DiagPhase.levelExt_czGate_le_two S.m 2 3)

/-- The rank-four sum is itself a well-formed letter. -/
theorem rank4_sum_wf (m : ℕ) :
    (NormalGate.Diag (DiagPhase.czGate m (0 : Fin 4) 1 + DiagPhase.czGate m 2 3)
      : NormalGate 4 m).WF :=
  diagLetter_wf_add (czLetter_wf m 0 1) (czLetter_wf m 2 3)

/-! ## Axiom rows -/

/-- info: 'FTQCLib.Frame.Walkthrough.NormalGate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NormalGate

/-- info: 'FTQCLib.Frame.Walkthrough.NormalGate.WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NormalGate.WF

/-- info: 'FTQCLib.Frame.Walkthrough.WordWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WordWF

/-- info: 'FTQCLib.Frame.Walkthrough.gateAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gateAmp

/-- info: 'FTQCLib.Frame.Walkthrough.runNormalAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormalAmp

/-- info: 'FTQCLib.Frame.Walkthrough.runNormalAmp_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormalAmp_nil

/-- info: 'FTQCLib.Frame.Walkthrough.runNormalAmp_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormalAmp_cons

/-- info: 'FTQCLib.Frame.Walkthrough.toKernelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toKernelState

/-- info: 'FTQCLib.Frame.Walkthrough.ofKernelState_toKernelState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ofKernelState_toKernelState

/-- info: 'FTQCLib.Frame.Walkthrough.hElimFloor_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hElimFloor_m

/-- info: 'FTQCLib.Frame.Walkthrough.hFloor_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hFloor_m

/-- info: 'FTQCLib.Frame.Walkthrough.hStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hStep

/-- info: 'FTQCLib.Frame.Walkthrough.hStep_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hStep_h

/-- info: 'FTQCLib.Frame.Walkthrough.hStep_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hStep_m

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hStep

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hStep

/-- info: 'FTQCLib.Frame.Walkthrough.applyNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyNormal

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_nil

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_cons

/-- info: 'FTQCLib.Frame.Walkthrough.step_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_normal

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_floor

/-- info: 'FTQCLib.Frame.Walkthrough.exists_isFloor_of_normalWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_isFloor_of_normalWord

/-- info: 'FTQCLib.Frame.Walkthrough.sLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sLetter

/-- info: 'FTQCLib.Frame.Walkthrough.czLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czLetter

/-- info: 'FTQCLib.Frame.Walkthrough.zLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zLetter

/-- info: 'FTQCLib.Frame.Walkthrough.sLetter_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sLetter_wf

/-- info: 'FTQCLib.Frame.Walkthrough.czLetter_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czLetter_wf

/-- info: 'FTQCLib.Frame.Walkthrough.zLetter_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zLetter_wf

/-- info: 'FTQCLib.Frame.Walkthrough.hLetter_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hLetter_wf

/-- info: 'FTQCLib.Frame.Walkthrough.cnotLetter_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cnotLetter_wf

/-- info: 'FTQCLib.Frame.Walkthrough.applyNormal_sLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyNormal_sLetter

/-- info: 'FTQCLib.Frame.Walkthrough.applyNormal_czLetter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyNormal_czLetter

/-- info: 'FTQCLib.Frame.Walkthrough.F_eq_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms F_eq_amp

/-- info: 'FTQCLib.Frame.Walkthrough.walshTransform_eq_hadamardGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walshTransform_eq_hadamardGate

/-- info: 'FTQCLib.Frame.Walkthrough.gateHilbertN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gateHilbertN

/-- info: 'FTQCLib.Frame.Walkthrough.runNormalHilbert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormalHilbert

/-- info: 'FTQCLib.Frame.Walkthrough.gateAmp_eq_gateHilbertN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gateAmp_eq_gateHilbertN

/-- info: 'FTQCLib.Frame.Walkthrough.runNormalAmp_eq_runNormalHilbert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormalAmp_eq_runNormalHilbert

/-- info: 'FTQCLib.Frame.Walkthrough.F_runNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms F_runNormal

/-- info: 'FTQCLib.Frame.Walkthrough.hhWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hhWord

/-- info: 'FTQCLib.Frame.Walkthrough.hhWord_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hhWord_wf

/-- info: 'FTQCLib.Frame.Walkthrough.applyHFiner_twice_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyHFiner_twice_h

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hh_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hh_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.hh_Kpp_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hh_Kpp_h

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hh_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hh_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.walsh0_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walsh0_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hh_Kpp_00' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hh_Kpp_00

/-- info: 'FTQCLib.Frame.Walkthrough.amp_hh_Kpp_01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_hh_Kpp_01

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_hh_K3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_hh_K3

/-- info: 'FTQCLib.Frame.Walkthrough.hh_K3_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hh_K3_h

/-- info: 'FTQCLib.Frame.Walkthrough.czHWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czHWord

/-- info: 'FTQCLib.Frame.Walkthrough.czHWord_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czHWord_wf

/-- info: 'FTQCLib.Frame.Walkthrough.isFloor_czH_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isFloor_czH_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.czH_Kpp_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms czH_Kpp_h

/-- info: 'FTQCLib.Frame.Walkthrough.gateAmp_cz_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gateAmp_cz_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.amp_czH_Kpp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_czH_Kpp

/-- info: 'FTQCLib.Frame.Walkthrough.applyNormal_diag' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyNormal_diag

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin

/-- info: 'FTQCLib.Frame.Walkthrough.wordLin' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordLin

/-- info: 'FTQCLib.Frame.Walkthrough.wordLin_nil' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordLin_nil

/-- info: 'FTQCLib.Frame.Walkthrough.wordLin_cons' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordLin_cons

/-- info: 'FTQCLib.Frame.Walkthrough.wordLin_append' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wordLin_append

/-- info: 'FTQCLib.Frame.Walkthrough.hStep_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hStep_L

/-- info: 'FTQCLib.Frame.Walkthrough.applyNormal_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms applyNormal_L

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_L' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_L

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_pair_diag' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_pair_diag

/-- info: 'FTQCLib.Frame.Walkthrough.zLetter_eq_czLetter_self' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zLetter_eq_czLetter_self

/-- info: 'FTQCLib.Frame.Walkthrough.diagLetter_wf_add_C' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagLetter_wf_add_C

/-- info: 'FTQCLib.Frame.Walkthrough.diagLetter_wf_add' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagLetter_wf_add

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_zLetter' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_zLetter

/-- info: 'FTQCLib.Frame.Walkthrough.globalPhase_letter_wf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalPhase_letter_wf

/-- info: 'FTQCLib.Frame.Walkthrough.effectiveLevel_globalPhase_not_le_two' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms effectiveLevel_globalPhase_not_le_two

/-- info: 'FTQCLib.Frame.Walkthrough.X_three_eq_monomial' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms X_three_eq_monomial

/-- info: 'FTQCLib.Frame.Walkthrough.boolReduce_X_three' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolReduce_X_three

/-- info: 'FTQCLib.Frame.Walkthrough.polarMatrix_X_three_00' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_X_three_00

/-- info: 'FTQCLib.Frame.Walkthrough.levelExt_X_three' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms levelExt_X_three

/-- info: 'FTQCLib.Frame.Walkthrough.not_wf_X_three' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_wf_X_three

/-- info: 'FTQCLib.Frame.Walkthrough.KT' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KT

/-- info: 'FTQCLib.Frame.Walkthrough.amp_KT' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_KT

/-- info: 'FTQCLib.Frame.Walkthrough.amp_applyDiagPolar_KT' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amp_applyDiagPolar_KT

/-- info: 'FTQCLib.Frame.Walkthrough.polarMatrix_X_three' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polarMatrix_X_three

/-- info: 'FTQCLib.Frame.Walkthrough.mem_L_applyDiagPolar_KT' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_L_applyDiagPolar_KT

/-- info: 'FTQCLib.Frame.Walkthrough.not_isFloor_applyDiagPolar_KT' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_isFloor_applyDiagPolar_KT

/-- info: 'FTQCLib.Frame.Walkthrough.sLetter_one_wf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sLetter_one_wf

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_sLetter_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_sLetter_one

/-- info: 'FTQCLib.Frame.Walkthrough.letterLin_zLetter_one' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms letterLin_zLetter_one

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_mix_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_mix_eq

/-- info: 'FTQCLib.Frame.Walkthrough.mix_sum_wf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mix_sum_wf

/-- info: 'FTQCLib.Frame.Walkthrough.runNormal_rank4_eq' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runNormal_rank4_eq

/-- info: 'FTQCLib.Frame.Walkthrough.rank4_sum_wf' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank4_sum_wf

end FTQCLib.Frame.Walkthrough

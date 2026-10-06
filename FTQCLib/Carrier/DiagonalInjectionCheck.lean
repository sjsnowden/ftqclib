/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.DiagonalInjection
import FTQCLib.Carrier.GateWordCheck
import FTQCLib.Hierarchy.GatePolynomials

/-!
# Check: witness for T22, injecting any diagonal gate

T22's witness (`docs/STEPS.md`, T22.2): rows on the frozen statement of `DiagonalInjection.lean`,
on its four named instances, each at its own precision, with the data qubits `q = id`.

* **The instances.** T at `m = 3` (`f = X₀`, `tGatePoly 0`); CS at `m = 2` (`f = X₀X₁`,
  `csPoly 0 1`); CCZ at `m = 1` (`f = X₀X₁X₂`, `cczPoly 0 1 2`); `√T` at `m = 4` (`f = X₀`,
  `rzGatePoly 0 4`).
* **The input of the protocol rows.** The register `∣+⟩^{⊗k}` on exactly the `k` data qubits
  (`plusRegister k`, precision `1`, every amplitude `1`), lifted to the gate's precision. Every
  amplitude is nonzero, so `ζ^f` changes it: its output is `ζ^{f(x)}` at `x`.
* **How the processed branch is computed.** From the semantics, not from the topic module's
  proofs. The processing of any protocol of the shape `Protocol m (n + k) k` is read off its
  referee (`restrictLast_restrictLast_interpret_spec`, by `amp_interpret` and
  `restrictLast_spec`); the input's amplitude by `amp_run`, `amp_appendFreeBits` and
  `amp_liftPrecision` (`diagonalInjectionInput_spec`), and the gate's output likewise
  (`amp_run_diagonal_rename`); the referee of the CNOTs and the Z-measurements is evaluated
  letter by letter at `k = 1, 2, 3` (`interpretAmp_measureAncillas_one`, `_two`, `_three`:
  `measureAncillas` unfolded into its letters, `pauliProjection_signedZ`, the CNOT bit-map), with
  `f` symbolic; the correction enters through its exponent, `correctionPhase_eval`.
* **Rows on the protocol (agreement).** For each instance, at every outcome string `c`, the
  processed branch `diagonalInjectionBranch` is `StateEq` to the gate's output, the run of
  `rename id f` on the lifted register. For T, also by value (the branch is `ζ₈` at `∣1⟩`, at each
  outcome) and the weight clause: the protocol's branch at `c` (T14's `branchWeight`) is
  `ampNormSq` of the input over `2^1`.
* **Rows on the protocol (discriminating).** The protocol with the correction's difference
  reversed (`reversedInjectionProtocol`), for T at `m = 3` on `∣+⟩`: its processed branch at
  `c = 1` is not `StateEq` to the gate's output, being `ζ₈² = i` at `∣0⟩`, where the gate's output
  is `1`.
* **Rows on the correction's exponent (agreement).** By `correctionPhase_eval`, on the word
  `Fin.append (Fin.append x a) c` of the data bits `x`, the ancilla bits `a` and the outcome bits
  `c` (the correction reads no ancilla, so `a` is free): for T at `c = 1` the correction is `S`
  (`sGate 3 0`) up to the global phase `ζ^{−1}`; for CS at `c = (1, 0)` it is `CZ · S₁†`
  (`czGate 2 0 1`, `sGate 2 1`) and at `c = (1, 1)` it is `S₀ S₁` up to a global phase; for CCZ at
  `c = (1, 0, 0)` it is `CZ₁₂` (`czGate 1 1 2`); for `√T` at `c = 1` its character is T's
  (`tGatePoly 0` at `m = 3`) up to the global phase `ζ₁₆^{−1}`. At `c = 0` the correction of T is
  the identity. And the phase identity: `f(x ⊕ c)`, which the magic state leaves on the data, plus
  the correction is `f(x)`, at every `x` and `c` (shown for T).
* **Rows on the correction's exponent (discriminating).** The correction with its difference
  reversed, `f(x ⊕ c) − f(x)` (`reversedCorrectionPhase`): for T at `x = 0`, `c = 1`, `f(x ⊕ c)`
  plus it is `2`, not `f(0) = 0`; and at `c = 1`, `x = 1` it is `−1`, where `S` up to `ζ^{−1}` is
  `1`.
* **Row (inhabitation).** `heightOneState` (`GateWordCheck.lean`, `m = 1`) meets
  `diagonalInjection_correct`'s hypotheses at the gate's precision `3`.

No row uses `diagonalInjection_correct` (proved at T22.3.1) or `correction_degree_lt` (T22.3.2).
The protocol rows test the processed branch as a carrier state on one input per instance, with
`n = k` and `q = id`; registers with qubits beside the chosen ones, other maps `q`, other inputs and
the clause relating the branch to the gate's output by T07's rules are not tested by a row. The
weight clause is tested for T only. The inhabitation row states only that the hypotheses hold
together, not the conclusions. The check step T22.4 added the axiom sweep of
`correction_degree_lt` and `diagonalInjection_correct` beside `correctionPhase_eval`'s, the
inhabitation row, and one aimed mutant on `correctionPhase`'s definition, caught.

Frame form (D5): the gate `ζ^f` and the corrections are diagonal letters, compared by their
exponents in `ZMod (2^m)`, or for `√T` by their characters `charOf m`, and the processed branches
by their amplitude functions. `DiagonalInjection.lean` imports no `FTQCLib.Hilbert` module; this
check module imports none either.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer
open Protocol

/-! ## The correction with its difference reversed -/

/-- **The correction with its difference reversed**, the nearest wrong correction: `f` at the
exclusive or of the chosen data qubits with the outcome bits, minus `f` at the data qubits. -/
noncomputable def reversedCorrectionPhase {n m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m) :
    DiagPhase (n + k + k) m :=
  let x : Fin k → DiagPhase (n + k + k) m :=
    fun i => MvPolynomial.X (Fin.castAdd k (Fin.castAdd k (q i)))
  let c : Fin k → DiagPhase (n + k + k) m := fun i => MvPolynomial.X (Fin.natAdd (n + k) i)
  MvPolynomial.bind₁ (fun i => x i + c i - 2 * x i * c i) f - MvPolynomial.bind₁ x f

/-- The reversed correction is the correction negated. -/
theorem reversedCorrectionPhase_eq_neg {n m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m) :
    reversedCorrectionPhase q f = -correctionPhase q f := by
  simp only [reversedCorrectionPhase, correctionPhase, neg_sub]

/-- The reversed correction's exponent is `f(x ∘ q ⊕ c) − f(x ∘ q)`. -/
theorem reversedCorrectionPhase_eval {n m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (w : Fin (n + k + k) → ZMod 2) :
    (reversedCorrectionPhase q f).eval w
      = f.eval (fun i => w (Fin.castAdd k (Fin.castAdd k (q i))) + w (Fin.natAdd (n + k) i))
        - f.eval (fun i => w (Fin.castAdd k (Fin.castAdd k (q i)))) := by
  rw [reversedCorrectionPhase_eq_neg, eval_neg, correctionPhase_eval, neg_sub]

/-! ## The register `∣+⟩^{⊗N}` -/

/-- The Lagrangian of `∣+⟩^{⊗N}`, constraint-presented: the Paulis on `N` bits with no `Z`-part. -/
def lagNoZ (N : ℕ) : Submodule (ZMod 2) (Pauli N) where
  carrier := {p | p.Z = 0}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [Z_add, hp, hq, add_zero]
  zero_mem' := rfl
  smul_mem' := by
    intro c p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Z_smul, hp, smul_zero]

/-- The record of `∣+⟩^{⊗N}` at precision `1`: every word on the support, exponent `0`,
scale `1`. -/
noncomputable def plusRegisterKernel (N : ℕ) : KernelState N := ⟨1, 0, 1, lagNoZ N, 0⟩

/-- **The register `∣+⟩^{⊗N}`**, up to the scale `√2^N`: every amplitude is `1`. -/
noncomputable def plusRegister (N : ℕ) : KernelSumState N :=
  ofKernelState (plusRegisterKernel N)

/-- `plusRegister N` is at most any positive precision. -/
theorem plusRegister_m_le (N : ℕ) {m : ℕ} (hm : 1 ≤ m) : (plusRegister N).m ≤ m := hm

/-- `plusRegister N` denotes the constant `1`. -/
theorem amp_plusRegister {N : ℕ} (w : Fin N → ZMod 2) : amp (plusRegister N) w = 1 := by
  have hw : ∃ p ∈ (plusRegisterKernel N).L, w = (plusRegisterKernel N).x₀ + p.X :=
    ⟨⟨w, 0⟩, rfl, (zero_add w).symm⟩
  rw [plusRegister, amp_ofKernelState_pos _ hw]
  change (1 : ℂ) * charOf 1 (DiagPhase.eval (0 : DiagPhase N 1) w) = 1
  have h0 : DiagPhase.eval (0 : DiagPhase N 1) w = 0 := by
    simp only [DiagPhase.eval, map_zero]
  rw [h0, charOf_zero, one_mul]

/-- `lagNoZ N` is isotropic: two Paulis with no `Z`-part commute. -/
theorem isStabilizer_lagNoZ (N : ℕ) : IsStabilizer (lagNoZ N) := by
  intro p hp q hq
  change p.Z = 0 at hp
  change q.Z = 0 at hq
  rw [omega_eq_dotF2, hp, hq]
  simp only [dotF2, Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

/-- `lagNoZ N` contains its symplectic complement. -/
theorem orthogonal_lagNoZ (N : ℕ) :
    LinearMap.BilinForm.orthogonal omegaBilin (lagNoZ N) ≤ lagNoZ N := by
  intro q hq
  change q.Z = 0
  funext k
  have h := hq (⟨Pi.single k 1, 0⟩ : Pauli N) rfl
  change omega (⟨Pi.single k 1, 0⟩ : Pauli N) q = 0 at h
  rw [omega_eq_dotF2, dotF2_single_left] at h
  have h0 : dotF2 (0 : Fin N → ZMod 2) q.X = 0 := by
    simp only [dotF2, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  rw [h0, zero_add] at h
  exact h

/-- **`plusRegister N` is a carrier state.** -/
theorem isCarrier_plusRegister (N : ℕ) : IsCarrier (plusRegister N) := by
  refine ⟨le_rfl, isStabilizer_lagNoZ N, orthogonal_lagNoZ N, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [amp_plusRegister] at h0
  exact one_ne_zero h0

/-! ## A processed branch, from its referee -/

/-! ## The referee letter by letter, at `k = 1, 2, 3` -/

/-- **After the CNOT and the Z-measurement, one qubit.** On `n = k = 1`, `q = id`, at the word
of the data bit `x`, the ancilla `a` and the outcome `c`, the referee of `measureAncillas` on any
amplitude `F` is `F` at `x` with the ancilla at `c ⊕ x` where `a = c`, and `0` elsewhere. -/
theorem interpretAmp_measureAncillas_one {m : ℕ} (F : (Fin (1 + 1) → ZMod 2) → ℂ)
    (x a c : Fin 1 → ZMod 2) :
    (measureAncillas (n := 1) (m := m) id 1 le_rfl).interpretAmp F (Fin.append (Fin.append x a) c)
      = if a = c then F (Fin.append x (c + x)) else 0 := by
  simp only [measureAncillas, ancillaCnotWord, interpretAmp_condition, interpretAmp_word,
    interpretAmp_nil, pauliProjection_signedZ, List.ofFn_succ, List.ofFn_zero, runAmp_cons,
    runAmp_nil, letterAmp, DiagPhase.cnotBitMap]
  by_cases h : a = c
  · subst h
    rw [if_pos (by rfl), if_pos rfl]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [if_neg h, if_neg (fun h' => h (funext fun i => by fin_cases i; exact h'))]

/-- `interpretAmp_measureAncillas_one` with the ancilla at the outcome, in the form
`amp_diagonalInjectionBranch_of_measure` takes. -/
theorem interpretAmp_measureAncillas_one_self {m : ℕ} (F : (Fin (1 + 1) → ZMod 2) → ℂ)
    (x c : Fin 1 → ZMod 2) :
    (measureAncillas (n := 1) (m := m) id 1 le_rfl).interpretAmp F (Fin.append (Fin.append x c) c)
      = F (Fin.append x (c + x)) := by
  rw [interpretAmp_measureAncillas_one, if_pos rfl]

/-- **After the CNOTs and the Z-measurements, two qubits.** On `n = k = 2`, `q = id`, at the word
of the data bits `x` with the ancillas and the outcomes both at `c`, the referee of
`measureAncillas` on any amplitude `F` is `F` at `x` with the ancillas at `c ⊕ x`. -/
theorem interpretAmp_measureAncillas_two {m : ℕ} (F : (Fin (2 + 2) → ZMod 2) → ℂ)
    (x c : Fin 2 → ZMod 2) :
    (measureAncillas (n := 2) (m := m) id 2 le_rfl).interpretAmp F (Fin.append (Fin.append x c) c)
      = F (Fin.append x (c + x)) := by
  simp only [measureAncillas, ancillaCnotWord, interpretAmp_condition, interpretAmp_word,
    interpretAmp_nil, pauliProjection_signedZ, List.ofFn_succ, List.ofFn_zero, runAmp_cons,
    runAmp_nil, letterAmp, DiagPhase.cnotBitMap]
  rw [if_pos (by rfl), if_pos (by rfl)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **After the CNOTs and the Z-measurements, three qubits.** As
`interpretAmp_measureAncillas_two`, on `n = k = 3`. -/
theorem interpretAmp_measureAncillas_three {m : ℕ} (F : (Fin (3 + 3) → ZMod 2) → ℂ)
    (x c : Fin 3 → ZMod 2) :
    (measureAncillas (n := 3) (m := m) id 3 le_rfl).interpretAmp F (Fin.append (Fin.append x c) c)
      = F (Fin.append x (c + x)) := by
  simp only [measureAncillas, ancillaCnotWord, interpretAmp_condition, interpretAmp_word,
    interpretAmp_nil, pauliProjection_signedZ, List.ofFn_succ, List.ofFn_zero, runAmp_cons,
    runAmp_nil, letterAmp, DiagPhase.cnotBitMap]
  rw [if_pos (by rfl), if_pos (by rfl), if_pos (by rfl)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The referee with any correction.** If the referee of `measureAncillas` on `n = k` qubits,
`q = id`, read with the ancillas and the outcomes at `c`, is the amplitude with the ancillas at
`c ⊕ x`, then the protocol ending in the diagonal letter `D` has, on the input's amplitude, the
referee `ζ^{D(x, c, c)} · ζ^{f(c ⊕ x)}` times the register's at `x`. -/
theorem interpretAmp_word_diagonal_of_measure {m k : ℕ} (f : DiagPhase k m)
    (D : DiagPhase (k + k + k) m)
    (hmeas : ∀ (F : (Fin (k + k) → ZMod 2) → ℂ) (x c : Fin k → ZMod 2),
      (measureAncillas (n := k) (m := m) id k le_rfl).interpretAmp F
        (Fin.append (Fin.append x c) c) = F (Fin.append x (c + x)))
    (s : (Fin k → ZMod 2) → ℂ) (x c : Fin k → ZMod 2) :
    ((measureAncillas (n := k) (m := m) id k le_rfl).word [GateLetter.diagonal D]).interpretAmp
        (fun u => charOf m (f.eval fun i => u (Fin.natAdd k i))
          * s (fun i => u (Fin.castAdd k i))) (Fin.append (Fin.append x c) c)
      = charOf m (D.eval (Fin.append (Fin.append x c) c)) * (charOf m (f.eval (c + x)) * s x) := by
  rw [interpretAmp_word, runAmp_cons, runAmp_nil]
  change charOf m _ * _ = _
  rw [hmeas]
  simp only [Fin.append_left, Fin.append_right]

/-- **The processed branch, from the referee letter by letter.** On `n = k` qubits with
`q = id`, if the referee of `measureAncillas` is as `interpretAmp_measureAncillas_two` states,
then on every carrier register the processed branch at every outcome string has amplitude
`ζ^{f(x)}` times the register's at `x`. The correction enters only through its exponent,
`correctionPhase_eval`. -/
theorem amp_diagonalInjectionBranch_of_measure {m k : ℕ} (f : DiagPhase k m)
    (hmeas : ∀ (F : (Fin (k + k) → ZMod 2) → ℂ) (x c : Fin k → ZMod 2),
      (measureAncillas (n := k) (m := m) id k le_rfl).interpretAmp F
        (Fin.append (Fin.append x c) c) = F (Fin.append x (c + x)))
    {S : KernelSumState k} (hS : IsCarrier S) (hmk : S.m ≤ m) (c : Fin k → ZMod 2) :
    amp (diagonalInjectionBranch id f S hmk c) = fun x => charOf m (f.eval x) * amp S x := by
  obtain ⟨hIc, hIm, hIa⟩ := diagonalInjectionInput_spec f hS hmk
  have hG : (fun x => charOf m (f.eval x) * amp S x) ≠ 0 := by
    intro h0
    apply hS.2.2.2
    funext x
    exact (mul_eq_zero.mp (congrFun h0 x)).resolve_left (charOf_ne_zero m _)
  refine (restrictLast_restrictLast_interpret_spec _ hIc hIm c hG fun x => ?_).2
  rw [hIa]
  unfold diagonalInjectionProtocol
  rw [interpretAmp_word_diagonal_of_measure f _ hmeas, correctionPhase_eval]
  simp only [Fin.append_left, Fin.append_right, id]
  rw [add_comm c x, ← mul_assoc]
  change charOf m (f.eval x - f.eval (x + c)) * charOf m (f.eval (x + c)) * amp S x = _
  rw [charOf_sub_mul]

/-! ## The protocol with the correction's difference reversed -/

/-- **The protocol with the correction's difference reversed**: `measureAncillas`, then the
diagonal letter `reversedCorrectionPhase` in place of `correctionPhase`. -/
noncomputable def reversedInjectionProtocol {n m k : ℕ} (q : Fin k → Fin n)
    (f : DiagPhase k m) : Protocol m (n + k) k :=
  (measureAncillas q k le_rfl).word [GateLetter.diagonal (reversedCorrectionPhase q f)]

/-- The branch of the outcome string `c` of `reversedInjectionProtocol`, processed as
`diagonalInjectionBranch` processes the protocol's. -/
noncomputable def reversedInjectionBranch {n m k : ℕ} (q : Fin k → Fin n) (f : DiagPhase k m)
    (S : KernelSumState n) (hmk : S.m ≤ m) (c : Fin k → ZMod 2) : KernelSumState n :=
  restrictLast k c
    (restrictLast k c ((reversedInjectionProtocol q f).interpret (diagonalInjectionInput f S hmk)))

/-- The reversed protocol's processed branch for T at `m = 3` on `∣+⟩`, at outcome `1`, is
`ζ^{rev(x, 1, 1)} · ζ^{f(1 ⊕ x)}` at `x`, `rev` the reversed correction's exponent. -/
theorem amp_reversedInjectionBranch_tGate :
    amp (reversedInjectionBranch (id : Fin 1 → Fin 1) (tGatePoly 0) (plusRegister 1)
        (plusRegister_m_le 1 (by norm_num)) 1)
      = fun x => charOf 3 ((reversedCorrectionPhase id (tGatePoly (0 : Fin 1))).eval
          (Fin.append (Fin.append x 1) 1))
        * (charOf 3 ((tGatePoly (0 : Fin 1)).eval (1 + x)) * 1) := by
  obtain ⟨hIc, hIm, hIa⟩ := diagonalInjectionInput_spec (tGatePoly (0 : Fin 1))
    (isCarrier_plusRegister 1) (plusRegister_m_le 1 (by norm_num))
  refine (restrictLast_restrictLast_interpret_spec _ hIc hIm 1 ?_ fun x => ?_).2
  · intro h0
    have h := congrFun h0 0
    simp only [Pi.zero_apply, mul_one] at h
    exact mul_ne_zero (charOf_ne_zero _ _) (charOf_ne_zero _ _) h
  · rw [hIa]
    unfold reversedInjectionProtocol
    rw [interpretAmp_word_diagonal_of_measure _ _ interpretAmp_measureAncillas_one_self,
      amp_plusRegister]

/-- On the T instance at `m = 3` on `∣+⟩`, the protocol's referee on the input has squared
modulus `1` where the ancilla equals the outcome `c`, and `0` elsewhere. -/
theorem normSq_interpretAmp_diagonalInjection_tGate (x a c : Fin 1 → ZMod 2) :
    Complex.normSq ((diagonalInjectionProtocol (id : Fin 1 → Fin 1) (tGatePoly 0)).interpretAmp
        (amp (diagonalInjectionInput (tGatePoly (0 : Fin 1)) (plusRegister 1)
          (plusRegister_m_le 1 (by norm_num))))
        (Fin.append (Fin.append x a) c)) = if a = c then 1 else 0 := by
  rw [(diagonalInjectionInput_spec (tGatePoly (0 : Fin 1)) (isCarrier_plusRegister 1)
    (plusRegister_m_le 1 (by norm_num))).2.2]
  unfold diagonalInjectionProtocol
  rw [interpretAmp_word, runAmp_cons, runAmp_nil]
  change Complex.normSq (charOf 3 _ * _) = _
  rw [interpretAmp_measureAncillas_one]
  split_ifs
  · simp only [Complex.normSq_mul, normSq_charOf, amp_plusRegister, map_one, one_mul]
  · simp only [mul_zero, map_zero]

/-! ## Rows on the correction's exponent -/

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:basic2
/-- **Agreement, T at `m = 3`, outcome `1`.** The correction is `S` (`sGate 3 0`) up to the global
phase `ζ^{−1}`: its exponent is `x − (x ⊕ 1) = 2x − 1`. -/
-- row: agreement
theorem correction_tGate_one (x a : Fin 1 → ZMod 2) :
    (correctionPhase (id : Fin 1 → Fin 1) (tGatePoly 0)).eval (Fin.append (Fin.append x a) 1)
      = (sGate 3 (0 : Fin 1)).eval x - 1 := by
  rw [correctionPhase_eval, sGate_eval]
  simp only [tGatePoly, eval_X, Fin.append_left, Fin.append_right, id, Pi.one_apply]
  generalize x 0 = u
  revert u
  decide

/-- **Agreement, T at `m = 3`, outcome `0`.** The correction is the identity. -/
-- row: agreement
theorem correction_tGate_zero (x a : Fin 1 → ZMod 2) :
    (correctionPhase (id : Fin 1 → Fin 1) (tGatePoly 0)).eval (Fin.append (Fin.append x a) 0)
      = 0 := by
  rw [correctionPhase_eval]
  simp only [tGatePoly, eval_X, Fin.append_left, Fin.append_right, id, Pi.zero_apply, add_zero,
    sub_self]

/-- **Agreement, T at `m = 3`, the phase identity.** At every data bit and outcome, the phase
`f(x ⊕ c)` the magic state leaves on the data, plus the correction, is `f(x)`: T is applied. -/
-- row: agreement
theorem tGate_magic_add_correction (x a c : Fin 1 → ZMod 2) :
    (tGatePoly (0 : Fin 1)).eval (x + c)
        + (correctionPhase (id : Fin 1 → Fin 1) (tGatePoly 0)).eval (Fin.append (Fin.append x a) c)
      = (tGatePoly (0 : Fin 1)).eval x := by
  rw [correctionPhase_eval]
  simp only [Fin.append_left, Fin.append_right, id]
  change (tGatePoly 0).eval (x + c) + ((tGatePoly 0).eval x - (tGatePoly 0).eval (x + c)) = _
  ring

/-- **Agreement, CS at `m = 2`, outcome `(1, 0)`.** The correction is `CZ · S₁†`, a Clifford:
its exponent is `x₀x₁ − (x₀ ⊕ 1)x₁ = 2x₀x₁ − x₁`. -/
-- row: agreement
theorem correction_csGate_one_zero (x a : Fin 2 → ZMod 2) :
    (correctionPhase (id : Fin 2 → Fin 2) (csPoly 0 1)).eval (Fin.append (Fin.append x a) ![1, 0])
      = (czGate 2 (0 : Fin 2) 1).eval x - (sGate 2 (1 : Fin 2)).eval x := by
  rw [correctionPhase_eval, czGate_eval, sGate_eval]
  simp only [csPoly, eval_mul, eval_X, Fin.append_left, Fin.append_right, id,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize x 0 = u
  generalize x 1 = v
  revert u v
  decide

/-- **Agreement, CS at `m = 2`, outcome `(1, 1)`.** The correction is `S₀ S₁` up to the global
phase `ζ^{−1}`: its exponent is `x₀x₁ − (1 − x₀)(1 − x₁) = x₀ + x₁ − 1`. -/
-- row: agreement
theorem correction_csGate_one_one (x a : Fin 2 → ZMod 2) :
    (correctionPhase (id : Fin 2 → Fin 2) (csPoly 0 1)).eval (Fin.append (Fin.append x a) ![1, 1])
      = (sGate 2 (0 : Fin 2)).eval x + (sGate 2 (1 : Fin 2)).eval x - 1 := by
  rw [correctionPhase_eval, sGate_eval, sGate_eval]
  simp only [csPoly, eval_mul, eval_X, Fin.append_left, Fin.append_right, id,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize x 0 = u
  generalize x 1 = v
  revert u v
  decide

/-- **Agreement, CCZ at `m = 1`, outcome `(1, 0, 0)`.** The correction is `CZ₁₂`, a Clifford: its
exponent is `x₀x₁x₂ − (x₀ ⊕ 1)x₁x₂ = x₁x₂` in `ZMod 2`. -/
-- row: agreement
theorem correction_cczGate_one_zero_zero (x a : Fin 3 → ZMod 2) :
    (correctionPhase (id : Fin 3 → Fin 3) (cczPoly 0 1 2)).eval
        (Fin.append (Fin.append x a) ![1, 0, 0])
      = (czGate 1 (1 : Fin 3) 2).eval x := by
  rw [correctionPhase_eval, czGate_eval]
  simp only [cczPoly, eval_mul, eval_X, Fin.append_left, Fin.append_right, id,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  generalize x 0 = u
  generalize x 1 = v
  generalize x 2 = t
  revert u v t
  decide

/-- At precision four, `ζ₁₆ = ζ₈ · ζ₁₆^{−1}`. -/
theorem charOf_four_one : charOf 4 1 = charOf 3 1 * charOf 4 (-1) := by
  have h32 : charOf 3 1 = charOf 4 2 := by
    unfold charOf
    congr 3
    have h1 : (1 : ZMod (2 ^ 3)).val = 1 := rfl
    have h2 : (2 : ZMod (2 ^ 4)).val = 2 := rfl
    rw [h1, h2]
    push_cast
    ring
  rw [h32, ← charOf_add]
  rfl

/-- **Agreement, `√T` at `m = 4`, outcome `1`.** The correction's character is T's, `tGatePoly 0`
at `m = 3`, up to the global phase `ζ₁₆^{−1}`: its exponent is `x − (x ⊕ 1) = 2x − 1` at
`m = 4`, and `ζ₁₆^{2x} = ζ₈^x`. -/
-- row: agreement
theorem correction_sqrtTGate_one (x a : Fin 1 → ZMod 2) :
    charOf 4 ((correctionPhase (id : Fin 1 → Fin 1) (rzGatePoly 0 4)).eval
        (Fin.append (Fin.append x a) 1))
      = charOf 3 ((tGatePoly (0 : Fin 1)).eval x) * charOf 4 (-1) := by
  rw [correctionPhase_eval]
  simp only [rzGatePoly, tGatePoly, eval_X, Fin.append_left, Fin.append_right, id, Pi.one_apply]
  rcases zmod_two_eq_zero_or_one (x 0) with h | h
  · rw [h]
    have hl : ((0 : ZMod 2).val : ZMod (2 ^ 4)) - ((0 + 1 : ZMod 2).val : ZMod (2 ^ 4)) = -1 := by
      decide
    have hr : ((0 : ZMod 2).val : ZMod (2 ^ 3)) = 0 := by decide
    rw [hl, hr, charOf_zero, one_mul]
  · rw [h]
    have hl : ((1 : ZMod 2).val : ZMod (2 ^ 4)) - ((1 + 1 : ZMod 2).val : ZMod (2 ^ 4)) = 1 := by
      decide
    have hr : ((1 : ZMod 2).val : ZMod (2 ^ 3)) = 1 := by decide
    rw [hl, hr]
    exact charOf_four_one

-- source: papers/clifford_hierarchy/
-- Gottesman_Chuang_1999_universal_via_teleportation_quant-ph_9908010 figure:fig:ftqc-ck
/-- **Discriminating, the difference reversed, the phase identity.** For T at `m = 3`, at the data
bit `0` and outcome `1`, the phase `f(x ⊕ c)` the magic state leaves plus the reversed correction
is `2`, not `f(0) = 0`: the reversed correction applies `S` where the correction applies T
(`tGate_magic_add_correction`). -/
-- row: discriminating
theorem tGate_magic_add_reversedCorrection_ne (a : Fin 1 → ZMod 2) :
    (tGatePoly (0 : Fin 1)).eval (0 + 1)
        + (reversedCorrectionPhase (id : Fin 1 → Fin 1) (tGatePoly 0)).eval
          (Fin.append (Fin.append 0 a) 1)
      ≠ (tGatePoly (0 : Fin 1)).eval 0 := by
  rw [reversedCorrectionPhase_eval]
  simp only [tGatePoly, eval_X, Fin.append_left, Fin.append_right, id, Pi.add_apply,
    Pi.zero_apply, Pi.one_apply]
  decide

/-- **Discriminating, the difference reversed, against `S`.** For T at `m = 3`, at outcome `1`
and the data bit `1`, the reversed correction's exponent is `−1`, where `S` up to `ζ^{−1}`, the
correction (`correction_tGate_one`), is `1`. -/
-- row: discriminating
theorem reversedCorrection_tGate_one_ne (a : Fin 1 → ZMod 2) :
    (reversedCorrectionPhase (id : Fin 1 → Fin 1) (tGatePoly 0)).eval
        (Fin.append (Fin.append 1 a) 1)
      ≠ (sGate 3 (0 : Fin 1)).eval 1 - 1 := by
  rw [reversedCorrectionPhase_eval, sGate_eval]
  simp only [tGatePoly, eval_X, Fin.append_left, Fin.append_right, id, Pi.one_apply]
  decide

/-! ## Rows on the protocol -/

-- source: papers/clifford_hierarchy/
-- Zhou_Leung_Chuang_2000_gate_construction_methodology_quant-ph_0002039 equation:eq:basic2
/-- **Agreement, T at `m = 3`, on the protocol.** On `∣+⟩` (`plusRegister 1`), at every outcome
`c`, the processed branch of the injection of T is `StateEq` to T run on the lifted register. -/
-- row: agreement
theorem stateEq_diagonalInjectionBranch_tGate (c : Fin 1 → ZMod 2) :
    StateEq (diagonalInjectionBranch (id : Fin 1 → Fin 1) (tGatePoly 0) (plusRegister 1)
        (plusRegister_m_le 1 (by norm_num)) c)
      (run [GateLetter.diagonal (MvPolynomial.rename id (tGatePoly (0 : Fin 1)))]
        (liftPrecision (plusRegister 1) 3 (plusRegister_m_le 1 (by norm_num)))) := by
  rw [StateEq, amp_diagonalInjectionBranch_of_measure _ interpretAmp_measureAncillas_one_self
    (isCarrier_plusRegister 1), amp_run_diagonal_rename _ _ (isCarrier_plusRegister 1)]
  rfl

/-- **Agreement, T at `m = 3`, on the protocol, by value.** On `∣+⟩`, at every outcome `c`, the
processed branch is `ζ₈` at `∣1⟩`: the input is one T changes. -/
-- row: agreement
theorem amp_diagonalInjectionBranch_tGate_one (c : Fin 1 → ZMod 2) :
    amp (diagonalInjectionBranch (id : Fin 1 → Fin 1) (tGatePoly 0) (plusRegister 1)
        (plusRegister_m_le 1 (by norm_num)) c) 1 = charOf 3 1 := by
  rw [amp_diagonalInjectionBranch_of_measure _ interpretAmp_measureAncillas_one_self
    (isCarrier_plusRegister 1)]
  simp only [amp_plusRegister, mul_one, tGatePoly, eval_X, Pi.one_apply]
  rfl

/-- **Agreement, T at `m = 3`, the weight clause.** On `∣+⟩`, at every outcome `c`, the protocol's
branch (T14's `branchWeight`) has weight `2^{−1}` of the input's `ampNormSq`: `2 = 4 / 2`. -/
-- row: agreement
theorem branchWeight_diagonalInjection_tGate (c : Fin 1 → ZMod 2) :
    (diagonalInjectionProtocol (id : Fin 1 → Fin 1) (tGatePoly 0)).branchWeight
        (diagonalInjectionInput (tGatePoly (0 : Fin 1)) (plusRegister 1)
          (plusRegister_m_le 1 (by norm_num))) c
      = ampNormSq (diagonalInjectionInput (tGatePoly (0 : Fin 1)) (plusRegister 1)
          (plusRegister_m_le 1 (by norm_num))) / 2 ^ 1 := by
  obtain ⟨hIc, hIm, hIa⟩ := diagonalInjectionInput_spec (tGatePoly (0 : Fin 1))
    (isCarrier_plusRegister 1) (plusRegister_m_le 1 (by norm_num))
  unfold Protocol.branchWeight Protocol.branch ampNormSq
  rw [(amp_interpret _ hIc hIm).2, ← sum_sum_append (N := 1) (k := 1)
    (fun w => Complex.normSq ((diagonalInjectionProtocol (id : Fin 1 → Fin 1)
      (tGatePoly 0)).interpretAmp (amp (diagonalInjectionInput (tGatePoly (0 : Fin 1))
        (plusRegister 1) (plusRegister_m_le 1 (by norm_num)))) (Fin.append w c)))]
  simp only [normSq_interpretAmp_diagonalInjection_tGate]
  rw [hIa]
  simp only [Finset.sum_ite_irrel, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Finset.univ_unique, ZMod.card, Finset.prod_const, Finset.card_singleton, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, mul_one, amp_plusRegister, normSq_charOf, Fintype.card_fin]
  norm_num

/-- **Agreement, CS at `m = 2`, on the protocol.** On `∣++⟩` (`plusRegister 2`), at every
outcome string `c`, the processed branch of the injection of CS is `StateEq` to CS run on the
lifted register. -/
-- row: agreement
theorem stateEq_diagonalInjectionBranch_csGate (c : Fin 2 → ZMod 2) :
    StateEq (diagonalInjectionBranch (id : Fin 2 → Fin 2) (csPoly 0 1) (plusRegister 2)
        (plusRegister_m_le 2 (by norm_num)) c)
      (run [GateLetter.diagonal (MvPolynomial.rename id (csPoly (0 : Fin 2) 1))]
        (liftPrecision (plusRegister 2) 2 (plusRegister_m_le 2 (by norm_num)))) := by
  rw [StateEq, amp_diagonalInjectionBranch_of_measure _ interpretAmp_measureAncillas_two
    (isCarrier_plusRegister 2), amp_run_diagonal_rename _ _ (isCarrier_plusRegister 2)]
  rfl

/-- **Agreement, CCZ at `m = 1`, on the protocol.** On `∣+++⟩` (`plusRegister 3`), at every
outcome string `c`, the processed branch of the injection of CCZ is `StateEq` to CCZ run on the
register. -/
-- row: agreement
theorem stateEq_diagonalInjectionBranch_cczGate (c : Fin 3 → ZMod 2) :
    StateEq (diagonalInjectionBranch (id : Fin 3 → Fin 3) (cczPoly 0 1 2) (plusRegister 3) le_rfl c)
      (run [GateLetter.diagonal (MvPolynomial.rename id (cczPoly (0 : Fin 3) 1 2))]
        (liftPrecision (plusRegister 3) 1 le_rfl)) := by
  rw [StateEq, amp_diagonalInjectionBranch_of_measure _ interpretAmp_measureAncillas_three
    (isCarrier_plusRegister 3), amp_run_diagonal_rename _ _ (isCarrier_plusRegister 3)]
  rfl

/-- **Agreement, `√T` at `m = 4`, on the protocol.** On `∣+⟩`, at every outcome `c`, the
processed branch of the injection of `√T` is `StateEq` to `√T` run on the lifted register. -/
-- row: agreement
theorem stateEq_diagonalInjectionBranch_sqrtTGate (c : Fin 1 → ZMod 2) :
    StateEq (diagonalInjectionBranch (id : Fin 1 → Fin 1) (rzGatePoly 0 4) (plusRegister 1)
        (plusRegister_m_le 1 (by norm_num)) c)
      (run [GateLetter.diagonal (MvPolynomial.rename id (rzGatePoly (0 : Fin 1) 4))]
        (liftPrecision (plusRegister 1) 4 (plusRegister_m_le 1 (by norm_num)))) := by
  rw [StateEq, amp_diagonalInjectionBranch_of_measure _ interpretAmp_measureAncillas_one_self
    (isCarrier_plusRegister 1), amp_run_diagonal_rename _ _ (isCarrier_plusRegister 1)]
  rfl

-- source: papers/clifford_hierarchy/
-- Gottesman_Chuang_1999_universal_via_teleportation_quant-ph_9908010 figure:fig:ftqc-ck
/-- **Discriminating, the difference reversed, on the protocol.** For T at `m = 3` on `∣+⟩`, the
protocol with the reversed correction (`reversedInjectionProtocol`) has, at outcome `1`, a
processed branch that is not `StateEq` to T's output: at `∣0⟩` it is `ζ₈² = i`, where T's output
is `1`. The protocol's own branch is (`stateEq_diagonalInjectionBranch_tGate`). -/
-- row: discriminating
theorem not_stateEq_reversedInjectionBranch_tGate :
    ¬ StateEq (reversedInjectionBranch (id : Fin 1 → Fin 1) (tGatePoly 0) (plusRegister 1)
        (plusRegister_m_le 1 (by norm_num)) 1)
      (run [GateLetter.diagonal (MvPolynomial.rename id (tGatePoly (0 : Fin 1)))]
        (liftPrecision (plusRegister 1) 3 (plusRegister_m_le 1 (by norm_num)))) := by
  intro h
  have h0 := congrFun h 0
  rw [amp_reversedInjectionBranch_tGate,
    amp_run_diagonal_rename _ _ (isCarrier_plusRegister 1)] at h0
  simp only [amp_plusRegister, reversedCorrectionPhase_eval, tGatePoly, eval_X, Fin.append_left,
    Fin.append_right, id, Pi.add_apply, Pi.zero_apply, Pi.one_apply, Function.comp_apply,
    mul_one, ← charOf_add] at h0
  have h1 := (charOf_injective 3) h0
  revert h1
  decide

/-! ## Inhabitation -/

/-- **Inhabitation.** `diagonalInjection_correct`'s hypotheses hold together on `heightOneState`
(`GateWordCheck.lean`): it is a carrier state, at precision `1`, at most the gate's precision `3`
(T's, `tGatePoly`). -/
-- row: inhabitation
theorem diagonalInjection_correct_hypotheses :
    IsCarrier heightOneState ∧ heightOneState.m ≤ 3 :=
  ⟨isCarrier_heightOneState, by rw [heightOneState_m]; decide⟩

/-! ## The axiom sweep of the proved theorems of the topic module

`diagonalInjection_correct` and `correction_degree_lt` are proved at T22.3 (T22.3.1, T22.3.2); this
check step adds their guards beside `correctionPhase_eval`'s. -/

/-- info: 'FTQCLib.Frame.Walkthrough.correctionPhase_eval' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms correctionPhase_eval

/-- info: 'FTQCLib.Frame.Walkthrough.correction_degree_lt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms correction_degree_lt

/-- info: 'FTQCLib.Frame.Walkthrough.diagonalInjection_correct' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms diagonalInjection_correct

/-- info: 'FTQCLib.Frame.Walkthrough.diagonalInjectionInput_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.diagonalInjectionInput_spec

/-- info: 'FTQCLib.Frame.Walkthrough.amp_run_diagonal_rename' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.amp_run_diagonal_rename

/-- info: 'FTQCLib.Frame.Walkthrough.restrictLast_restrictLast_interpret_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FTQCLib.Frame.Walkthrough.restrictLast_restrictLast_interpret_spec

end FTQCLib.Frame.Walkthrough

/-! ## Mutant -/

-- mutant: xor_coefficient | FTQCLib/Carrier/DiagonalInjection.lean | 2 * x i * c i | 3 * x i * c i

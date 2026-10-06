/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Carrier.ControlledHadamardMinimal
import FTQCLib.Carrier.ControlledHadamardCheck
import FTQCLib.Carrier.ResidualBit
import FTQCLib.Carrier.RowSumBounds

/-!
# Check: witness for T09.2.2, rows on controlled-H's output itself

`docs/STEPS.md`, "The unit", phase 2, T09.2.2: rows that compute `leastHeight` of
`controlledHAmp c t (amp S)` itself, on two-qubit carrier inputs, at the smallest inputs where it
is `0` and where it is `1` — not `leastHeight` of `S` or of some other gate's output, which is what
T09.2's rows computed instead (`docs/STEPS.md`, entry 2026-09-30c). `leastHeight_controlledH`
(T09.3) is proved. The height-zero rows use it nowhere: each exhibits a presenter and reads
`leastHeight` from its own definition. The height-one row takes its lower bound from
`one_le_leastHeight_of_norm_ne` (T09.3.2) and its upper bound from part 4 of the proved theorem.

* **Height `0`, control `0` on the whole support.** `KP` (`ControlledHadamardCheck.lean`,
  `L = prodL = ⟨X₀, Z₁⟩`, the product `|+⟩ ⊗ |0⟩`) is supported only where its own qubit `1` is
  `0` (`amp_KP_support_bit1`: every `p ∈ prodL` has `p.X 1 = 0`, and `KP.x₀ 1 = 0`, so every
  support word `x₀ + p.X` has bit `1` equal to `0`): with control `1` and target `0`,
  `controlledHAmp` is the identity on every point on and off `KP`'s support
  (`controlledHAmp_KP_eq_self`), so its least height is
  `KP`'s own, `0`, with `KP` itself the presenter.

* **Height `0`, the floor input `∣10⟩`.** `deltaAmp ![1,0]` (`ControlledHadamardCheck.lean`) is the
  basis state `∣10⟩`; with control `0` and target `1`, `controlledHAmp` sends it to `∣1⟩∣+⟩`
  (`ControlledHadamardCheck.lean`'s own `controlledHAmp_basis_control_one_ten`,
  `controlledHAmp_basis_control_one_eleven` compute two of its four values already). `KQ` — the
  record at `L = ctrlL = ⟨Z₀, X₁⟩` (qubit `0` fixed at `1`, qubit `1` free), offset `![1,0]`, flat
  exponent, scale `1/√2` — presents exactly this function (`amp_KQ_eq_controlledH`): a floor, so
  the least height is `0`.

* **Height `1`, at `∣1⟩ ⊗ KT`.** `KT2` is `KT` (`ResidualBitCheck.lean`'s T-state, exponent `X₀` at
  `m = 3`) carried on qubit `1` of two, with qubit `0` fixed at `1` by the same `ctrlL`: a floor,
  so `leastHeight (amp KT2) = 0`, and part 4 of `leastHeight_controlledH` bounds the output's least
  height above by `1`. Below: with control `0` and target `1`, every point of `KT2`'s support reads
  `controlledHAmp` as the Walsh transform at bit `1` (control is `1` on the whole support), and the
  pair `![1,0]`, `![1,0] + e₁` is residual for `KT2`'s exponent exactly as it is for `KT`'s own
  (the same difference `1`, `2 ≠ 0`, `2 ≠ 4`): `normSq_pair_ne_of_residual` (T09.3.2's route, one
  layer up from `ResidualBit.lean`'s own use of it) gives two nonzero values of different modulus,
  and `one_le_leastHeight_of_norm_ne` (T09.3.2) bounds the least height below by `1`, using the
  presenter `amp_controlledHWord` supplies — not a record built by hand. The least height is
  exactly `1`.

**What is not asserted.** `ControlledHadamardMinimal.lean`'s docstring's hand-computed input
(`n = 2`, `m = 1`, `h = 3`, exponent `y₀y₁y₂`, amplitude `3/√2` at three points) is marked inferred
there and is not touched, read, or relied on here: these rows are at different, smaller inputs, and
prove their own bounds independently of it.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer

/-! ## A bit of `ZMod 2` is `0` or `1` -/

/-! ## Two complex numbers of different `normSq` have different norm -/

private theorem norm_ne_of_normSq_ne {z w : ℂ} (h : Complex.normSq z ≠ Complex.normSq w) :
    ‖z‖ ≠ ‖w‖ := fun he => h (by
      rw [← Complex.norm_mul_self_eq_normSq, ← Complex.norm_mul_self_eq_normSq, he])

/-! ## Height `0`, control `0` on the whole support: `KP` -/

/-- `KP`'s support lies over bit `1` equal to `0` — `prodL`'s constraint `p.X 1 = 0` on the shadow
vector, read at the offset `0`. -/
private theorem amp_KP_support_bit1 {w : Fin 2 → ZMod 2}
    (hw : amp (ofKernelState KP) w ≠ 0) : w 1 = 0 := by
  rw [amp_ofKernelState_ne_zero_iff KP (c_ne_zero_of_isCarrier isCarrier_KP)] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  have hp1 : p.X 1 = 0 := (mem_prodL.mp hp).1
  change (KP.x₀ + p.X) 1 = 0
  rw [Pi.add_apply, hp1, add_zero]
  rfl

/-- **Controlled-H is the identity on `KP`**, control qubit `1` (fixed at `0` on the whole
support) and target qubit `0`: on support the referee's own `if` fires directly; off support
(bit `1` nonzero) both branches read `0`, `KP` at the updates of a point with bit `1` nonzero
still having bit `1` nonzero. -/
theorem controlledHAmp_KP_eq_self :
    controlledHAmp (1 : Fin 2) 0 (amp (ofKernelState KP)) = amp (ofKernelState KP) := by
  funext w
  unfold controlledHAmp
  by_cases hc : w 1 = 0
  · rw [if_pos hc]
  · rw [if_neg hc]
    have hw : amp (ofKernelState KP) w = 0 := by
      by_contra hne
      exact hc (amp_KP_support_bit1 hne)
    have hupdate0 : amp (ofKernelState KP) (Function.update w 0 0) = 0 := by
      by_contra hne
      apply hc
      have h := amp_KP_support_bit1 hne
      rwa [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] at h
    have hupdate1 : amp (ofKernelState KP) (Function.update w 0 1) = 0 := by
      by_contra hne
      apply hc
      have h := amp_KP_support_bit1 hne
      rwa [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)] at h
    unfold walshTransform
    rw [hupdate0, hupdate1, hw]
    ring

/-- **Height `0`, control `0` on the whole support.** `controlledHAmp` on `KP` is `KP`'s own
amplitude (`controlledHAmp_KP_eq_self`), and `KP` itself is a height-`0` presenter of it
(`isCarrier_KP`), the least element of `ℕ`. -/
-- row: agreement
theorem leastHeight_controlledH_KP_eq_zero :
    leastHeight (controlledHAmp (1 : Fin 2) 0 (amp (ofKernelState KP))) = 0 := by
  rw [controlledHAmp_KP_eq_self]
  exact Nat.le_antisymm (Nat.sInf_le ⟨ofKernelState KP, isCarrier_KP, rfl, rfl⟩) (Nat.zero_le _)

/-! ## Height `0`, the floor input `∣10⟩`: `KQ` presents `∣1⟩∣+⟩` -/

/-- The Lagrangian `⟨Z₀, X₁⟩`: qubit `0` fixed, qubit `1` free — `prodL`'s constraints with the
two bits exchanged, by its constraints (`prodL_isStabilizer`'s style: coisotropy discharged
directly against the two generators, no rank computation). -/
def ctrlL : Submodule (ZMod 2) (Pauli 2) where
  carrier := {p | p.X 0 = 0 ∧ p.Z 1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := fun hp hq => ⟨by simp [hp.1, hq.1], by simp [hp.2, hq.2]⟩
  smul_mem' := fun _ _ hp => ⟨by simp [hp.1], by simp [hp.2]⟩

@[simp] theorem mem_ctrlL {p : Pauli 2} : p ∈ ctrlL ↔ p.X 0 = 0 ∧ p.Z 1 = 0 := Iff.rfl

theorem ctrlL_isStabilizer : IsStabilizer ctrlL := by
  intro p hp q hq
  show omega p q = 0
  unfold omega
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hp.1, hp.2, hq.1, hq.2]

theorem ctrlL_coisotropic : LinearMap.BilinForm.orthogonal omegaBilin ctrlL ≤ ctrlL := by
  intro q hq
  have ha := hq (pauliz 0) (mem_ctrlL.mpr ⟨rfl, by decide⟩)
  have hb := hq (paulix 1) (mem_ctrlL.mpr ⟨by decide, rfl⟩)
  change omega (pauliz 0) q = 0 at ha
  change omega (paulix 1) q = 0 at hb
  rw [show (pauliz (0 : Fin 2)) = (⟨0, Pi.single 0 1⟩ : Pauli 2) from rfl, omega_pureZ,
    dotF2_single_left] at ha
  rw [show (paulix (1 : Fin 2)) = (⟨Pi.single 1 1, 0⟩ : Pauli 2) from rfl, omega_pureX,
    dotF2_single_left] at hb
  exact mem_ctrlL.mpr ⟨ha, hb⟩

/-- The flat-exponent, scale-`1/√2`, `L = ctrlL` record at offset `![1,0]`, precision `1`: the
floor `∣1⟩ ⊗ ∣+⟩`. -/
noncomputable def KQ : KernelState 2 := ⟨1, 0, 1 / (Real.sqrt 2 : ℂ), ctrlL, ![1, 0]⟩

/-- Off `KQ`'s support (qubit `0` not `1`): `0`. -/
private theorem amp_KQ_of_bit0_zero {w : Fin 2 → ZMod 2} (hw0 : w 0 = 0) :
    amp (ofKernelState KQ) w = 0 := by
  apply amp_ofKernelState_neg
  rintro ⟨p, hp, rfl⟩
  have hp0 : p.X 0 = 0 := (mem_ctrlL.mp hp).1
  have h1 : (KQ.x₀ + p.X) 0 = 1 := by
    rw [Pi.add_apply, hp0, add_zero]
    rfl
  rw [h1] at hw0
  exact absurd hw0 (by decide)

/-- On `KQ`'s support (qubit `0` equal to `1`): the flat scale `1/√2`. -/
private theorem amp_KQ_of_bit0_one {w : Fin 2 → ZMod 2} (hw0 : w 0 = 1) :
    amp (ofKernelState KQ) w = 1 / (Real.sqrt 2 : ℂ) := by
  have hmem : ∃ p ∈ ctrlL, w = KQ.x₀ + p.X := by
    refine ⟨⟨w - KQ.x₀, 0⟩, mem_ctrlL.mpr ⟨?_, rfl⟩, by simp⟩
    change (w - KQ.x₀) 0 = 0
    simp [KQ, hw0]
  rw [amp_ofKernelState_pos KQ hmem]
  have hz : DiagPhase.eval KQ.q w = 0 := by
    change DiagPhase.eval (0 : DiagPhase 2 1) w = 0
    exact eval_zero_poly w
  rw [hz, charOf_zero, mul_one]
  rfl

theorem isCarrier_KQ : IsCarrier (ofKernelState KQ) := by
  refine ⟨le_rfl, ctrlL_isStabilizer, ctrlL_coisotropic, ?_⟩
  intro hzero
  have h0 := congrFun hzero (![1, 0] : Fin 2 → ZMod 2)
  rw [amp_KQ_of_bit0_one (by decide)] at h0
  exact (one_div_ne_zero ofReal_sqrt_two_ne_zero) h0

/-- **`KQ` presents controlled-H's output on `∣10⟩`.** Off `KQ`'s support (qubit `0` equal to
`0`), `controlledHAmp`'s own `if` reads the input `deltaAmp ![1,0]` directly, `0` since the two
points differ at bit `0`; on it (qubit `0` equal to `1`), the Walsh transform's two branches read
`deltaAmp ![1,0]` at the two settings of bit `1` — `![1,0]` itself (`deltaAmp_self`, matching
`amp_KQ_of_bit0_one`'s flat value `1/√2` up to the `1/√2` prefactor) and the bit-`1`-flipped point,
which is never `![1,0]` (`deltaAmp_of_ne`). -/
theorem amp_KQ_eq_controlledH :
    amp (ofKernelState KQ)
      = controlledHAmp (0 : Fin 2) 1 (deltaAmp (![1, 0] : Fin 2 → ZMod 2)) := by
  funext w
  unfold controlledHAmp
  by_cases hc : w 0 = 0
  · rw [if_pos hc, amp_KQ_of_bit0_zero hc]
    have hne : w ≠ (![1, 0] : Fin 2 → ZMod 2) := by
      intro he
      rw [he] at hc
      exact absurd hc (by decide)
    exact (deltaAmp_of_ne hne).symm
  · rw [if_neg hc]
    have hw0 : w 0 = 1 := (zmod_two_dichotomy (w 0)).resolve_left hc
    have hu0 : Function.update w 1 0 = (![1, 0] : Fin 2 → ZMod 2) := by
      funext i
      fin_cases i <;> simp [Function.update, hw0]
    have hu1 : Function.update w 1 1 ≠ (![1, 0] : Fin 2 → ZMod 2) := by
      intro he
      have h1 := congrFun he 1
      simp [Function.update_self] at h1
    rw [amp_KQ_of_bit0_one hw0]
    unfold walshTransform
    rw [hu0, deltaAmp_self, deltaAmp_of_ne hu1, mul_zero, add_zero, mul_one]

/-- **Height `0`, the floor input `∣10⟩`.** `controlledHAmp` on the basis state `∣10⟩` is exactly
`KQ`'s amplitude (`amp_KQ_eq_controlledH`), and `KQ` is a height-`0` presenter of it
(`isCarrier_KQ`), the least element of `ℕ`: the floor `∣1⟩∣+⟩` that the target names. -/
-- row: agreement
theorem leastHeight_controlledH_KQ_eq_zero :
    leastHeight (controlledHAmp (0 : Fin 2) 1 (deltaAmp (![1, 0] : Fin 2 → ZMod 2))) = 0 := by
  rw [← amp_KQ_eq_controlledH]
  exact Nat.le_antisymm (Nat.sInf_le ⟨ofKernelState KQ, isCarrier_KQ, rfl, rfl⟩) (Nat.zero_le _)

/-! ## Height `1`, at `∣1⟩ ⊗ KT` -/

/-- `KT` (`ResidualBitCheck.lean`) carried on qubit `1` of two, qubit `0` fixed at `1` by `ctrlL`:
the T-state's own exponent `X₁`, at `m = 3`. -/
noncomputable def KT2 : KernelState 2 := ⟨3, MvPolynomial.X 1, 1, ctrlL, ![1, 0]⟩

/-- `KT2` denotes `1` at its own offset: flat evaluation of `X₁` there is `0`. -/
theorem amp_KT2_offset : amp (ofKernelState KT2) (![1, 0] : Fin 2 → ZMod 2) = 1 := by
  rw [amp_ofKernelState_pos KT2 ⟨0, ctrlL.zero_mem, by simp [KT2]⟩]
  have hz : DiagPhase.eval KT2.q (![1, 0] : Fin 2 → ZMod 2) = 0 := by
    change DiagPhase.eval (MvPolynomial.X 1 : DiagPhase 2 3) (![1, 0] : Fin 2 → ZMod 2) = 0
    rw [eval_X]
    decide
  rw [hz]
  change (1 : ℂ) * charOf 3 0 = 1
  rw [charOf_zero, mul_one]

theorem isCarrier_KT2 : IsCarrier (ofKernelState KT2) := by
  refine ⟨by decide, ctrlL_isStabilizer, ctrlL_coisotropic, ?_⟩
  intro hzero
  have h0 := congrFun hzero (![1, 0] : Fin 2 → ZMod 2)
  rw [amp_KT2_offset] at h0
  exact one_ne_zero h0

/-- **Height `1`, at `∣1⟩ ⊗ KT`.** Upper bound `1`: `KT2` is itself a height-`0` presenter of its
own amplitude, so `leastHeight (amp KT2) = 0`, and part 4 of `leastHeight_controlledH` bounds the
controlled-H output's least height by `leastHeight (amp KT2) + 1 = 1`. Lower bound `1`: on `KT2`'s
support (qubit `0` equal to `1`) `controlledHAmp` is the Walsh transform at qubit `1`, and the
pair `![1,0]`, `![1,0] + e₁` is residual for `KT2`'s exponent — the same difference `1` as `KT`'s
own (`2 ≠ 0` not collapse, `2 ≠ 4` not rotate) — so `normSq_pair_ne_of_residual` (T09.3.2's route)
gives two nonzero values of different modulus, and `one_le_leastHeight_of_norm_ne` (T09.3.2) with
the presenter `amp_controlledHWord` supplies bounds the least height below by `1`. -/
-- row: discriminating
theorem leastHeight_controlledH_KT2_eq_one :
    leastHeight (controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))) = 1 := by
  have hct : (0 : Fin 2) ≠ 1 := by decide
  -- the upper bound
  obtain ⟨-, -, -, hup4, -⟩ :=
    leastHeight_controlledH (S := ofKernelState KT2) isCarrier_KT2 hct 3 (le_refl 3) (le_refl 3)
  have hSle0 : leastHeight (amp (ofKernelState KT2)) ≤ 0 :=
    Nat.sInf_le ⟨ofKernelState KT2, isCarrier_KT2, rfl, rfl⟩
  have hup : leastHeight (controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))) ≤ 1 := by
    omega
  -- the lower bound
  have huk : (![1, 0] : Fin 2 → ZMod 2) 1 = 0 := by decide
  have hu_mem : ∃ p ∈ ctrlL, (![1, 0] : Fin 2 → ZMod 2) = KT2.x₀ + p.X :=
    ⟨0, ctrlL.zero_mem, by simp [KT2]⟩
  have hu'_mem : ∃ p ∈ ctrlL,
      (![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2) = KT2.x₀ + p.X :=
    ⟨paulix 1, mem_ctrlL.mpr ⟨by decide, rfl⟩, by simp [KT2, paulix]⟩
  have hpt : (![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2)
      = (![1, 1] : Fin 2 → ZMod 2) := by decide
  have heval_u : DiagPhase.eval KT2.q (![1, 0] : Fin 2 → ZMod 2) = 0 := by
    change DiagPhase.eval (MvPolynomial.X 1 : DiagPhase 2 3) (![1, 0] : Fin 2 → ZMod 2) = 0
    rw [eval_X]
    decide
  have heval_u' :
      DiagPhase.eval KT2.q ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2))
        = 1 := by
    rw [hpt]
    change DiagPhase.eval (MvPolynomial.X 1 : DiagPhase 2 3) (![1, 1] : Fin 2 → ZMod 2) = 1
    rw [eval_X]
    decide
  have h0 : 2 * (DiagPhase.eval KT2.q
        ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2))
      - DiagPhase.eval KT2.q (![1, 0] : Fin 2 → ZMod 2)) ≠ 0 := by
    rw [heval_u, heval_u']; decide
  have h1 : 2 * (DiagPhase.eval KT2.q
        ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2))
      - DiagPhase.eval KT2.q (![1, 0] : Fin 2 → ZMod 2))
      ≠ (2 : ZMod (2 ^ KT2.m)) ^ (KT2.m - 1) := by
    rw [heval_u, heval_u']; decide
  obtain ⟨hne0, hne1, hnormne⟩ :=
    normSq_pair_ne_of_residual KT2 (by decide) one_ne_zero (1 : Fin 2) huk hu_mem hu'_mem h0 h1
  have hc0u : (![1, 0] : Fin 2 → ZMod 2) (0 : Fin 2) ≠ 0 := by decide
  have hc0u' : (((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2) : Fin 2 → ZMod 2)
      (0 : Fin 2)) ≠ 0 := by
    rw [hpt]; decide
  have heq0 : controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2)) (![1, 0] : Fin 2 → ZMod 2)
      = walshTransform 1 (amp (ofKernelState KT2)) (![1, 0] : Fin 2 → ZMod 2) := by
    unfold controlledHAmp; rw [if_neg hc0u]
  have heq1 : controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))
      ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2))
      = walshTransform 1 (amp (ofKernelState KT2))
          ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2)) := by
    unfold controlledHAmp; rw [if_neg hc0u']
  have hfu : controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))
      (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := heq0 ▸ hne0
  have hfu' : controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))
      ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2)) ≠ 0 := heq1 ▸ hne1
  have hfne : Complex.normSq
      (controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2)) (![1, 0] : Fin 2 → ZMod 2))
      ≠ Complex.normSq (controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))
          ((![1, 0] : Fin 2 → ZMod 2) + Pi.single (1 : Fin 2) (1 : ZMod 2))) := by
    rw [heq0, heq1]; exact hnormne
  obtain ⟨hWcarrier, hWamp⟩ :=
    amp_controlledHWord (S := ofKernelState KT2) isCarrier_KT2 hct 3 (le_refl 3) (le_refl 3)
  have hlow : 1 ≤ leastHeight (controlledHAmp (0 : Fin 2) 1 (amp (ofKernelState KT2))) :=
    one_le_leastHeight_of_norm_ne hWcarrier hWamp hfu hfu' (norm_ne_of_normSq_ne hfne)
  exact Nat.le_antisymm hup hlow

/-! ## Inhabitation: the headline theorem's hypotheses hold together, at `KT2` -/

/-- **Inhabitation.** `leastHeight_controlledH`'s hypotheses — a carrier state, distinct free bits,
and a word run at a precision at least three and at least the state's own — hold together at
`KT2`, `c = 0`, `t = 1`, `k = 3`. -/
-- row: inhabitation
example := leastHeight_controlledH (S := ofKernelState KT2) isCarrier_KT2
  (show (0 : Fin 2) ≠ 1 by decide) 3 (le_refl 3) (le_refl 3)

/-! ## The axiom sweep — build-failing, one guard per public declaration of the topic module -/

/-- info: 'FTQCLib.Frame.Walkthrough.leastHeight' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leastHeight

/-- info: 'FTQCLib.Frame.Walkthrough.HasRowSums' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasRowSums

/-- info: 'FTQCLib.Frame.Walkthrough.leastHeight_controlledH' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leastHeight_controlledH

/-- info: 'FTQCLib.Frame.Walkthrough.hasRowSums_amp' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasRowSums_amp

/-! ## The axiom sweep — the helper module `RowSumBounds`, one guard per public declaration -/

/-- info: 'FTQCLib.Frame.Walkthrough.norm_le_of_hasRowSums' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_le_of_hasRowSums

/-- info: 'FTQCLib.Frame.Walkthrough.norm_eq_of_hasRowSums_zero' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_eq_of_hasRowSums_zero

/-- info: 'FTQCLib.Frame.Walkthrough.one_le_leastHeight_of_norm_ne' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_le_leastHeight_of_norm_ne

/-! ## A mutant on the headline theorem's conclusion -/

-- mutant: item4_bound_off_by_one | FTQCLib/Carrier/ControlledHadamardMinimal.lean | leastHeight (controlledHAmp c t (amp S)) ≤ leastHeight (amp S) + 1 | leastHeight (controlledHAmp c t (amp S)) ≤ leastHeight (amp S) + 2

end FTQCLib.Frame.Walkthrough

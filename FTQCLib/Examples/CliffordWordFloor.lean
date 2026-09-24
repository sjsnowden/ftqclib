/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierClifford

/-!
# Clifford words on the floor

The floor constructors — the eliminating H (`hFloor`), the diagonal class rule (`applyDiagPolar`)
and CNOT with the symplectic lift (`applyCnotSum`) — each send a height-zero floor to a
height-zero floor with a known amplitude. This module folds them along words of a frame-pure
alphabet and proves the composite statement: **a well-formed Clifford word sends a height-zero
floor at precision `m` to a height-zero floor at precision `m`, with the referee's amplitude**.
The referee `runNormalAmp` acts on amplitude functions alone (Walsh transform, phase,
permutation), so the statement is checkable letter by letter against the Hilbert interpreter in
the Check.

**A diagonal letter is its exponent alone.** Its shear is not data the letter carries but the
polar matrix read from the exponent's Boolean normal form, and its well-formedness is the level
check `levelExt D ≤ 2` — a static analysis of the presentation, which the constructor of
`CarrierClifford.lean` then reads. The check is blind to a global phase (`levelExt_add_C`), so the
letter set is closed under `D ↦ D + C c`, as the classification of diagonal Clifford gates is.

Each letter also has a symplectic map (`letterLin`), and a word the composite (`wordLin`): the
word moves the input's Lagrangian by that map (`runNormal_L`), which is what the group statement
of `CliffordFloorGeneration.lean` quantifies over.

The word is applied head first (`List.foldl`); the Hilbert-housed `runFrame` of
`FTQCLib/Hilbert/CharSumCorrespondence.lean` applies its list tail first and enters diagonal letters
with a stale Lagrangian — the relation between the two alphabets is `StateEq` per letter, which is
not developed here.

## Main definitions

* `NormalGate n m` — the alphabet `H k | Diag D | Cnot i j`; `NormalGate.WF` (a diagonal letter's
  exponent has extended level at most two, CNOT needs `i ≠ j`); `WordWF`.
* `gateAmp`, `runNormalAmp` — the referee on amplitudes.
* `hStep` — H on a record: `hFloor` at height `0`, the free rule otherwise; `applyNormal`,
  `runNormal` — the letters and words on records.
* `letterLin`, `wordLin` — the symplectic map of a letter and of a word.
* `sLetter`, `czLetter`, `zLetter` — the instances as letters, with their well-formedness.

## Main results

* `step_normal` — one well-formed letter: floor to floor, height `0` to `0`, precision kept, the
  referee's amplitude.
* `runNormal_floor`, `exists_isFloor_of_normalWord` — the composite, by induction on the word.
* `runNormal_L` — the word moves the Lagrangian by `wordLin`.
* `runNormal_pair_diag` — two diagonal letters in a row are the class rule on the sum exponent.

Everything here is frame-pure. No `FTQCLib.Hilbert`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## The alphabet and the referee -/

/-- The frame-pure alphabet at precision `m`: H at a bit, a diagonal exponent, CNOT with control
`i` and target `j`. A diagonal letter carries its exponent and nothing else — its shear is read
from the exponent by the class rule. -/
inductive NormalGate (n m : ℕ) where
  | H : Fin n → NormalGate n m
  | Diag : DiagPhase n m → NormalGate n m
  | Cnot : Fin n → Fin n → NormalGate n m

namespace NormalGate

/-- **Well-formedness of a letter**: a diagonal letter's exponent has extended level at most two
(the level of the Boolean normal form of its non-constant part — a static analysis, blind to a
global phase), CNOT needs distinct bits. -/
def WF {m : ℕ} : NormalGate n m → Prop
  | H _ => True
  | Diag D => levelExt D ≤ 2
  | Cnot i j => i ≠ j

end NormalGate

/-- Every letter of a word is well-formed. -/
def WordWF {m : ℕ} (gs : List (NormalGate n m)) : Prop := ∀ g ∈ gs, g.WF

/-- The referee: a letter's action on an amplitude function. -/
noncomputable def gateAmp {m : ℕ} (g : NormalGate n m) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  match g with
  | .H k => walshTransform k f
  | .Diag D => fun w => charOf m (D.eval w) * f w
  | .Cnot i j => fun w => f (cnotBitMap i j w)

/-- The referee on a word, head letter first. -/
noncomputable def runNormalAmp {m : ℕ} (gs : List (NormalGate n m)) (f : (Fin n → ZMod 2) → ℂ) :
    (Fin n → ZMod 2) → ℂ :=
  gs.foldl (fun f g => gateAmp g f) f

theorem runNormalAmp_nil {m : ℕ} (f : (Fin n → ZMod 2) → ℂ) :
    runNormalAmp ([] : List (NormalGate n m)) f = f := rfl

theorem runNormalAmp_cons {m : ℕ} (g : NormalGate n m) (gs : List (NormalGate n m))
    (f : (Fin n → ZMod 2) → ℂ) : runNormalAmp (g :: gs) f = runNormalAmp gs (gateAmp g f) := rfl

/-! ## The symplectic map of a letter and of a word -/

/-- **The symplectic map of a letter**: the swap at a bit for H, the shear by the polar matrix of
the exponent's normal form for a diagonal letter, the symplectic lift for CNOT. -/
noncomputable def letterLin {m : ℕ} : NormalGate n m → (Pauli n →ₗ[ZMod 2] Pauli n)
  | .H k => pauliSwapOn {k}
  | .Diag D => zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce D)))
  | .Cnot i j => cnotPauli i j

/-- **The symplectic map of a word**, head letter applied first. -/
noncomputable def wordLin {m : ℕ} : List (NormalGate n m) → (Pauli n →ₗ[ZMod 2] Pauli n)
  | [] => LinearMap.id
  | g :: gs => (wordLin gs).comp (letterLin g)

theorem wordLin_nil {m : ℕ} : wordLin ([] : List (NormalGate n m)) = LinearMap.id := rfl

theorem wordLin_cons {m : ℕ} (g : NormalGate n m) (gs : List (NormalGate n m)) :
    wordLin (g :: gs) = (wordLin gs).comp (letterLin g) := rfl

/-- The map of a concatenation is the composite, first word first. -/
theorem wordLin_append {m : ℕ} (gs₁ gs₂ : List (NormalGate n m)) :
    wordLin (gs₁ ++ gs₂) = (wordLin gs₂).comp (wordLin gs₁) := by
  induction gs₁ with
  | nil => rfl
  | cons g gs ih =>
    rw [List.cons_append, wordLin_cons, wordLin_cons, ih]
    rfl

/-! ## H on a record -/

/-- A height-`0` record as a kernel state (a choice; `ofKernelState` recovers the record). -/
noncomputable def toKernelState (S : KernelSumState n) (h0 : S.h = 0) : KernelState n :=
  Classical.choose (exists_kernelState_of_h_eq_zero S h0)

theorem ofKernelState_toKernelState (S : KernelSumState n) (h0 : S.h = 0) :
    ofKernelState (toKernelState S h0) = S :=
  (Classical.choose_spec (exists_kernelState_of_h_eq_zero S h0)).symm

/-- The precision of `hElimFloor` is the input's. -/
theorem hElimFloor_m (k : Fin n) (K : KernelState n) (g : Pauli n) :
    (hElimFloor k K g).m = K.m := by
  unfold hElimFloor
  split_ifs <;> rfl

/-- The precision of `hFloor` is the input's. -/
theorem hFloor_m (k : Fin n) (K : KernelState n) : (hFloor k K).m = K.m := by
  unfold hFloor
  split_ifs
  · exact hElimFloor_m k K _
  · rfl
  · rfl

open Classical in
/-- **H on a record**: through the floor constructor at height `0`, the free rule otherwise. -/
noncomputable def hStep (k : Fin n) (S : KernelSumState n) : KernelSumState n :=
  if h0 : S.h = 0 then hFloor k (toKernelState S h0) else applyHFiner k S

theorem hStep_h (k : Fin n) {S : KernelSumState n} (h0 : S.h = 0) : (hStep k S).h = 0 := by
  unfold hStep
  rw [dif_pos h0]
  exact hFloor_h _ _

theorem hStep_m (k : Fin n) {S : KernelSumState n} (h0 : S.h = 0) : (hStep k S).m = S.m := by
  unfold hStep
  rw [dif_pos h0, hFloor_m]
  exact congrArg KernelSumState.m (ofKernelState_toKernelState S h0)

theorem isFloor_hStep (k : Fin n) {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) :
    IsFloor (hStep k S) := by
  unfold hStep
  rw [dif_pos h0]
  exact isFloor_hFloor (by rw [ofKernelState_toKernelState]; exact hF) k

theorem amp_hStep (k : Fin n) {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) :
    amp (hStep k S) = walshTransform k (amp S) := by
  unfold hStep
  rw [dif_pos h0, amp_hFloor (by rw [ofKernelState_toKernelState]; exact hF) k,
    ofKernelState_toKernelState]

/-- **H moves the Lagrangian by the swap at the bit.** -/
theorem hStep_L (k : Fin n) {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) :
    (hStep k S).L = Submodule.map (pauliSwapOn {k}) S.L := by
  unfold hStep
  rw [dif_pos h0, hFloor_L (by rw [ofKernelState_toKernelState]; exact hF) k]
  exact congrArg (Submodule.map (pauliSwapOn {k}))
    (congrArg KernelSumState.L (ofKernelState_toKernelState S h0))

/-! ## Letters and words on records -/

/-- A letter's action on a record. A diagonal letter acts by the class rule, and only when the
precisions agree. -/
noncomputable def applyNormal {m : ℕ} (g : NormalGate n m) (S : KernelSumState n) :
    KernelSumState n :=
  match g with
  | .H k => hStep k S
  | .Diag D => if hm : S.m = m then applyDiagPolar S (hm ▸ D) else S
  | .Cnot i j => applyCnotSum i j S

/-- At the record's own precision a diagonal letter *is* the class rule. -/
theorem applyNormal_diag {S : KernelSumState n} (D : DiagPhase n S.m) :
    applyNormal (NormalGate.Diag D) S = applyDiagPolar S D := by
  change (if hm : S.m = S.m then applyDiagPolar S (hm ▸ D) else S) = _
  rw [dif_pos rfl]

/-- A word on a record, head letter first. -/
noncomputable def runNormal {m : ℕ} (gs : List (NormalGate n m)) (S : KernelSumState n) :
    KernelSumState n :=
  gs.foldl (fun S g => applyNormal g S) S

theorem runNormal_nil {m : ℕ} (S : KernelSumState n) :
    runNormal ([] : List (NormalGate n m)) S = S := rfl

theorem runNormal_cons {m : ℕ} (g : NormalGate n m) (gs : List (NormalGate n m))
    (S : KernelSumState n) : runNormal (g :: gs) S = runNormal gs (applyNormal g S) := rfl

/-- **The step theorem.** A well-formed letter sends a height-`0` floor at precision `m` to a
height-`0` floor at precision `m`, with the referee's amplitude. -/
theorem step_normal {m : ℕ} (g : NormalGate n m) (hg : g.WF) {S : KernelSumState n} (hF : IsFloor S)
    (h0 : S.h = 0) (hm : S.m = m) :
    IsFloor (applyNormal g S) ∧ (applyNormal g S).h = 0 ∧ (applyNormal g S).m = m ∧
      amp (applyNormal g S) = gateAmp g (amp S) := by
  cases g with
  | H k =>
    simp only [applyNormal, gateAmp]
    exact ⟨isFloor_hStep k hF h0, hStep_h k h0, by rw [hStep_m k h0]; exact hm, amp_hStep k hF h0⟩
  | Diag D =>
    subst hm
    change levelExt D ≤ 2 at hg
    simp only [applyNormal_diag, gateAmp]
    exact ⟨isFloor_applyDiagPolar hF hg, h0, rfl, amp_applyDiagPolar S D⟩
  | Cnot i j =>
    change i ≠ j at hg
    simp only [applyNormal, gateAmp]
    exact ⟨isFloor_applyCnotSum hg hF, h0, hm, amp_applyCnotSum hg S⟩

/-- **A letter moves the Lagrangian by its symplectic map.** -/
theorem applyNormal_L {m : ℕ} (g : NormalGate n m) {S : KernelSumState n} (hF : IsFloor S)
    (h0 : S.h = 0) (hm : S.m = m) :
    (applyNormal g S).L = Submodule.map (letterLin g) S.L := by
  cases g with
  | H k => exact hStep_L k hF h0
  | Diag D =>
    subst hm
    rw [applyNormal_diag, applyDiagPolar_L]
    rfl
  | Cnot i j => rfl

/-- **The composite.** A well-formed word sends a height-`0` floor at precision `m` to a height-`0`
floor at precision `m`, with the referee's amplitude. -/
theorem runNormal_floor {m : ℕ} (gs : List (NormalGate n m)) (hwf : WordWF gs)
    {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) (hm : S.m = m) :
    IsFloor (runNormal gs S) ∧ (runNormal gs S).h = 0 ∧ (runNormal gs S).m = m ∧
      amp (runNormal gs S) = runNormalAmp gs (amp S) := by
  induction gs generalizing S with
  | nil => exact ⟨hF, h0, hm, rfl⟩
  | cons g gs ih =>
    have hg : g.WF := hwf g (List.mem_cons_self ..)
    have hwf' : WordWF gs := fun g' hg' => hwf g' (List.mem_cons_of_mem _ hg')
    obtain ⟨hF1, h01, hm1, hamp1⟩ := step_normal g hg hF h0 hm
    obtain ⟨hF2, h02, hm2, hamp2⟩ := ih hwf' hF1 h01 hm1
    rw [runNormal_cons, runNormalAmp_cons, ← hamp1]
    exact ⟨hF2, h02, hm2, hamp2⟩

/-- The existence form of the composite. -/
theorem exists_isFloor_of_normalWord {m : ℕ} (gs : List (NormalGate n m)) (hwf : WordWF gs)
    {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) (hm : S.m = m) :
    ∃ T : KernelSumState n, IsFloor T ∧ T.h = 0 ∧ T.m = m ∧ amp T = runNormalAmp gs (amp S) :=
  ⟨_, runNormal_floor gs hwf hF h0 hm⟩

/-- **The word moves the Lagrangian by `wordLin`.** -/
theorem runNormal_L {m : ℕ} (gs : List (NormalGate n m)) (hwf : WordWF gs)
    {S : KernelSumState n} (hF : IsFloor S) (h0 : S.h = 0) (hm : S.m = m) :
    (runNormal gs S).L = Submodule.map (wordLin gs) S.L := by
  induction gs generalizing S with
  | nil => rw [runNormal_nil, wordLin_nil, Submodule.map_id]
  | cons g gs ih =>
    have hg : g.WF := hwf g (List.mem_cons_self ..)
    have hwf' : WordWF gs := fun g' hg' => hwf g' (List.mem_cons_of_mem _ hg')
    obtain ⟨hF1, h01, hm1, _⟩ := step_normal g hg hF h0 hm
    rw [runNormal_cons, ih hwf' hF1 h01 hm1, applyNormal_L g hF h0 hm, wordLin_cons,
      Submodule.map_comp]

/-- **Two diagonal letters in a row are one.** At positive precision the class rule composes, so a
two-letter diagonal word is the class rule on the sum exponent — no hypothesis on the two shears,
which are read from the exponents. -/
theorem runNormal_pair_diag {S : KernelSumState n} (hm : 1 ≤ S.m) {D E : DiagPhase n S.m}
    (hD : levelExt D ≤ 2) (hE : levelExt E ≤ 2) :
    runNormal [NormalGate.Diag D, NormalGate.Diag E] S = applyDiagPolar S (D + E) := by
  rw [runNormal_cons, runNormal_cons, runNormal_nil, applyNormal_diag]
  rw [show applyNormal (NormalGate.Diag E) (applyDiagPolar S D)
      = applyDiagPolar (applyDiagPolar S D) E from applyNormal_diag (S := applyDiagPolar S D) E]
  exact applyDiagPolar_add hm hD hE

/-! ## The instances as letters -/

/-- `S` at bit `i`: the phase `i^{w_i}`. -/
noncomputable def sLetter (m : ℕ) (i : Fin n) : NormalGate n m := .Diag (sGate m i)

/-- `CZ` at bits `i, j`: the phase `(−1)^{w_i w_j}`. -/
noncomputable def czLetter (m : ℕ) (i j : Fin n) : NormalGate n m := .Diag (czGate m i j)

/-- `Z` at bit `i` is the `CZ` letter at `i, i`: the phase `(−1)^{w_i}`, one term. -/
noncomputable def zLetter (m : ℕ) (i : Fin n) : NormalGate n m := czLetter m i i

theorem zLetter_eq_czLetter_self (m : ℕ) (i : Fin n) : zLetter m i = czLetter m i i := rfl

/-- **`S` is a well-formed letter at every precision.** At `m = 1` its exponent is `X i`, the `Z`
letter's, and the check accepts it there too. -/
theorem sLetter_wf (m : ℕ) (i : Fin n) : (sLetter m i).WF := levelExt_sGate_le_two m i

/-- **`CZ` is a well-formed letter at every precision, for every pair of bits** — including
`i = j`, where the exponent is the `Z` letter's. -/
theorem czLetter_wf (m : ℕ) (i j : Fin n) : (czLetter m i j).WF := levelExt_czGate_le_two m i j

theorem zLetter_wf (m : ℕ) (i : Fin n) : (zLetter m i).WF := czLetter_wf m i i

theorem hLetter_wf {m : ℕ} (k : Fin n) : (NormalGate.H k : NormalGate n m).WF := trivial

theorem cnotLetter_wf {m : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (NormalGate.Cnot i j : NormalGate n m).WF := hij

/-- **A global phase is a well-formed letter's business.** The level check strips the constant, so
a letter stays well-formed when a global phase is added to its exponent. -/
theorem diagLetter_wf_add_C {m : ℕ} {D : DiagPhase n m} (hD : (NormalGate.Diag D).WF)
    (c : ZMod (2 ^ m)) : (NormalGate.Diag (D + MvPolynomial.C c)).WF := by
  change levelExt (D + MvPolynomial.C c) ≤ 2
  rw [levelExt_add_C]
  exact hD

/-- **The sum of two well-formed diagonal letters is one**: the level of a sum is at most the
larger level. -/
theorem diagLetter_wf_add {m : ℕ} {D E : DiagPhase n m} (hD : (NormalGate.Diag D).WF)
    (hE : (NormalGate.Diag E).WF) : (NormalGate.Diag (D + E)).WF :=
  (levelExt_add_le D E).trans (max_le hD hE)

/-- The `S` letter acts as `applyS` at the matching precision, from precision two. -/
theorem applyNormal_sLetter {m : ℕ} (i : Fin n) {S : KernelSumState n} (hm : S.m = m)
    (h2 : 2 ≤ m) : applyNormal (sLetter m i) S = applyS S i := by
  subst hm
  rw [show sLetter S.m i = NormalGate.Diag (sGate S.m i) from rfl, applyNormal_diag]
  exact (applyS_eq_applyDiagPolar S h2 i).symm

/-- The `CZ` letter acts as `applyCZ` at the matching precision, at distinct bits. -/
theorem applyNormal_czLetter {m : ℕ} {i j : Fin n} (hij : i ≠ j) {S : KernelSumState n}
    (hm : S.m = m) (h1 : 1 ≤ m) : applyNormal (czLetter m i j) S = applyCZ S i j := by
  subst hm
  rw [show czLetter S.m i j = NormalGate.Diag (czGate S.m i j) from rfl, applyNormal_diag]
  exact (applyCZ_eq_applyDiagPolar S h1 hij).symm

/-- **The `Z` letter leaves the Lagrangian where it is.** Its exponent carries the datum of the
zero shear (`diagShiftDatum_czGate_self`), and a datum at `⊤` is unique, so the polar matrix the
class rule reads is the zero map. -/
theorem letterLin_zLetter {m : ℕ} (hm : 1 ≤ m) (i : Fin n) :
    letterLin (zLetter m i) = LinearMap.id := by
  have h : Matrix.mulVecLin (polarMatrix (boolReduce (czGate m i i))) = shearLin i 0 :=
    eq_of_diagShiftDatumBy_top hm
      (diagShiftDatumBy_polarMatrix (czGate m i i) (levelExt_czGate_le_two m i i) ⊤)
      (diagShiftDatum_czGate_self hm i ⊤)
  have h0 : shearLin i (0 : Fin n → ZMod 2) = 0 := LinearMap.ext (fun v => shearRow_zero i v)
  change zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce (czGate m i i)))) = _
  rw [h, h0, zShearBy_zero]

end FTQCLib.Frame.Walkthrough

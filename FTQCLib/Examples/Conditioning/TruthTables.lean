/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.Inject

/-! # Conditioning truth tables — the raw measure-and-condition operation

The conditioner-agnostic semantics: **measure a commuting family of Paulis; the state lands in a sector;
a bit string comes out.** Nothing here applies a correction, runs a decoder, or mentions an error — what
you do with the bit string is downstream and the semantics does not care. The only stated fact per code
is the **read-off**: after conditioning, the family generators sit in the Lagrangian with signs *equal to
the measured outcome bit string* (`sign gᵢ = sᵢ`). The codeword is the all-`+1` row; each other outcome is
another sector. Bare, unmotivated truth tables.

The correction/conditioner machinery (reconvergence, feed-forward, the remote CNOT) lives separately
under `FTQCLib/Examples/ConditionalAction/`. -/

namespace FTQCLib.Conditioning

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Hilbert FTQCLib.Teleport FTQCLib.Inject

/-! ## Toy 1 — the 3-qubit (bit-flip) code: family `(Z₀Z₁, Z₁Z₂)` -/

/-- `Z₀Z₁`. -/
def ZZ01 : Pauli 3 := pauliz 0 + pauliz 1
/-- `Z₁Z₂`. -/
def ZZ12 : Pauli 3 := pauliz 1 + pauliz 2

/-- An input on which the family is measurable (`|+++⟩`). -/
noncomputable def pppL : Submodule (ZMod 2) (Pauli 3) :=
  Submodule.span (ZMod 2) {paulix 0, paulix 1, paulix 2}

theorem pppL_isStabilizer : IsStabilizer pppL :=
  isStabilizer_span_of_pairwise (by
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> decide)

theorem pppL_finrank : Module.finrank (ZMod 2) pppL = 3 := by
  have hli : LinearIndependent (ZMod 2) ![paulix 0, paulix 1, paulix 2] :=
    linearIndependent_of_omega_dual (n := 3) (k := 3) (v := ![paulix 0, paulix 1, paulix 2])
      (w := ![pauliz 0, pauliz 1, pauliz 2]) (by decide)
  have hrange : ({paulix 0, paulix 1, paulix 2} : Set (Pauli 3))
      = Set.range ![paulix 0, paulix 1, paulix 2] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩]
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  have hspan : pppL = Submodule.span (ZMod 2) (Set.range ![paulix 0, paulix 1, paulix 2]) := by
    unfold pppL; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

noncomputable def ppp : PureSignedStab 3 := mkPureSlab pppL_isStabilizer pppL_finrank

theorem ZZ01_not_mem : ZZ01 ∉ ppp.toSignedStab.L := by
  show ZZ01 ∉ pppL
  intro h
  have h0 : omega ZZ01 (paulix 0) = 0 :=
    pppL_isStabilizer ZZ01 h (paulix 0) (Submodule.subset_span (by simp))
  rw [show omega ZZ01 (paulix 0) = 1 from by decide] at h0
  exact one_ne_zero h0

theorem X0_mem_ppp : paulix 0 ∈ ppp.toSignedStab.L := Submodule.subset_span (by simp)
theorem X2_mem_ppp : paulix 2 ∈ ppp.toSignedStab.L := Submodule.subset_span (by simp)

/-- **Condition on `Z₀Z₁`** (outcome `a`). -/
noncomputable def S1 (a : ℂ) (ha : a * a = 1) : PureSignedStab 3 :=
  injStepWith ppp ZZ01_not_mem ha (paulix 0) X0_mem_ppp (by decide)

theorem X2_mem_S1L (a : ℂ) (ha : a * a = 1) : paulix 2 ∈ (S1 a ha).toSignedStab.L := by
  show paulix 2 ∈ pauliCondition pppL ZZ01
  exact mem_pauliCondition_of_commute ZZ01_not_mem X2_mem_ppp (by decide)

theorem ZZ12_not_mem_S1L (a : ℂ) (ha : a * a = 1) : ZZ12 ∉ (S1 a ha).toSignedStab.L := by
  show ZZ12 ∉ pauliCondition pppL ZZ01
  intro h
  have h0 : omega ZZ12 (paulix 2) = 0 :=
    pauliCondition_isStabilizer pppL_isStabilizer ZZ01 ZZ12 h (paulix 2) (X2_mem_S1L a ha)
  rw [show omega ZZ12 (paulix 2) = 1 from by decide] at h0
  exact one_ne_zero h0

/-- **Condition on `Z₁Z₂`** (outcome `b`). The conditioned state for the outcome pair `(a,b)`. -/
noncomputable def S2 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) : PureSignedStab 3 :=
  injStepWith (S1 a ha) (ZZ12_not_mem_S1L a ha) hb (paulix 2) (X2_mem_S1L a ha) (by decide)

/-- **Truth-table read-off (row `(a,b)`):** `Z₁Z₂`'s sign in the conditioned state *is* the outcome `b` —
the kernel `injStepWith_sign_self` (the directly-measured generator reads off its outcome). -/
theorem threeQubit_sign_ZZ12 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (S2 a b ha hb).toSignedStab.sign ZZ12 = b :=
  injStepWith_sign_self (S1 a ha) (ZZ12_not_mem_S1L a ha) hb (paulix 2) (X2_mem_S1L a ha) (by decide)

/-- **Truth-table read-off (row `(a,b)`):** `Z₀Z₁`'s sign in the conditioned state *is* the outcome `a`
(it sits on the kept slice of the second measurement, so its sign passes through unchanged — then reads
off its own outcome via the kernel). -/
theorem threeQubit_sign_ZZ01 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (S2 a b ha hb).toSignedStab.sign ZZ01 = a :=
  (injStepWith_sign_of_zero (S1 a ha) (ZZ12_not_mem_S1L a ha) hb (paulix 2) (X2_mem_S1L a ha)
      (by decide)
      (mem_pauliCondition_of_commute (ZZ12_not_mem_S1L a ha) (pauliCondition_mem _ ZZ01) (by decide))
      (by decide)).trans
    (injStepWith_sign_self ppp ZZ01_not_mem ha (paulix 0) X0_mem_ppp (by decide))

/-- The family is stabilized after conditioning: `Z₁Z₂ ∈ L`. -/
theorem threeQubit_ZZ12_mem (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    ZZ12 ∈ (S2 a b ha hb).toSignedStab.L := by
  show ZZ12 ∈ pauliCondition (S1 a ha).toSignedStab.L ZZ12
  exact pauliCondition_mem _ _

/-- The family is stabilized after conditioning: `Z₀Z₁ ∈ L`. -/
theorem threeQubit_ZZ01_mem (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    ZZ01 ∈ (S2 a b ha hb).toSignedStab.L := by
  show ZZ01 ∈ pauliCondition (S1 a ha).toSignedStab.L ZZ12
  exact mem_pauliCondition_of_commute (ZZ12_not_mem_S1L a ha) (pauliCondition_mem _ ZZ01) (by decide)

/-! ## Toy 2 — the 4-qubit `[[4,2,2]]` code: family `(XXXX, ZZZZ)` (mixed X/Z) -/

/-- `X₀X₁X₂X₃`. -/
def XXXX : Pauli 4 := paulix 0 + paulix 1 + paulix 2 + paulix 3
/-- `Z₀Z₁Z₂Z₃`. -/
def ZZZZ : Pauli 4 := pauliz 0 + pauliz 1 + pauliz 2 + pauliz 3

/-- An input on which both checks are measurable (`⟨Z₀,X₁,Z₂,Z₃⟩`). -/
noncomputable def q4L : Submodule (ZMod 2) (Pauli 4) :=
  Submodule.span (ZMod 2) {pauliz 0, paulix 1, pauliz 2, pauliz 3}

theorem q4L_isStabilizer : IsStabilizer q4L :=
  isStabilizer_span_of_pairwise (by
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> decide)

theorem q4L_finrank : Module.finrank (ZMod 2) q4L = 4 := by
  have hli : LinearIndependent (ZMod 2) ![pauliz 0, paulix 1, pauliz 2, pauliz 3] :=
    linearIndependent_of_omega_dual (n := 4) (k := 4)
      (v := ![pauliz 0, paulix 1, pauliz 2, pauliz 3])
      (w := ![paulix 0, pauliz 1, paulix 2, paulix 3]) (by decide)
  have hrange : ({pauliz 0, paulix 1, pauliz 2, pauliz 3} : Set (Pauli 4))
      = Set.range ![pauliz 0, paulix 1, pauliz 2, pauliz 3] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩, ⟨3, by simp⟩]
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  have hspan : q4L = Submodule.span (ZMod 2) (Set.range ![pauliz 0, paulix 1, pauliz 2, pauliz 3]) := by
    unfold q4L; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

noncomputable def q4 : PureSignedStab 4 := mkPureSlab q4L_isStabilizer q4L_finrank

theorem XXXX_not_mem : XXXX ∉ q4.toSignedStab.L := by
  show XXXX ∉ q4L
  intro h
  have h0 : omega XXXX (pauliz 0) = 0 :=
    q4L_isStabilizer XXXX h (pauliz 0) (Submodule.subset_span (by simp))
  rw [show omega XXXX (pauliz 0) = 1 from by decide] at h0
  exact one_ne_zero h0

theorem Z0_mem_q4 : pauliz 0 ∈ q4.toSignedStab.L := Submodule.subset_span (by simp)
theorem X1_mem_q4 : paulix 1 ∈ q4.toSignedStab.L := Submodule.subset_span (by simp)

/-- **Condition on `XXXX`** (outcome `a`), witness `Z₀`. -/
noncomputable def T1 (a : ℂ) (ha : a * a = 1) : PureSignedStab 4 :=
  injStepWith q4 XXXX_not_mem ha (pauliz 0) Z0_mem_q4 (by decide)

theorem X1_mem_T1L (a : ℂ) (ha : a * a = 1) : paulix 1 ∈ (T1 a ha).toSignedStab.L := by
  show paulix 1 ∈ pauliCondition q4L XXXX
  exact mem_pauliCondition_of_commute XXXX_not_mem X1_mem_q4 (by decide)

theorem ZZZZ_not_mem_T1L (a : ℂ) (ha : a * a = 1) : ZZZZ ∉ (T1 a ha).toSignedStab.L := by
  show ZZZZ ∉ pauliCondition q4L XXXX
  intro h
  have h0 : omega ZZZZ (paulix 1) = 0 :=
    pauliCondition_isStabilizer q4L_isStabilizer XXXX ZZZZ h (paulix 1) (X1_mem_T1L a ha)
  rw [show omega ZZZZ (paulix 1) = 1 from by decide] at h0
  exact one_ne_zero h0

/-- **Condition on `ZZZZ`** (outcome `b`), witness `X₁`. The conditioned state for outcome `(a,b)`. -/
noncomputable def T2 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) : PureSignedStab 4 :=
  injStepWith (T1 a ha) (ZZZZ_not_mem_T1L a ha) hb (paulix 1) (X1_mem_T1L a ha) (by decide)

/-- **Truth-table read-off:** `ZZZZ`'s sign in the conditioned state *is* the outcome `b` (the kernel). -/
theorem fourQubit_sign_ZZZZ (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (T2 a b ha hb).toSignedStab.sign ZZZZ = b :=
  injStepWith_sign_self (T1 a ha) (ZZZZ_not_mem_T1L a ha) hb (paulix 1) (X1_mem_T1L a ha) (by decide)

/-- **Truth-table read-off:** `XXXX`'s sign in the conditioned state *is* the outcome `a` (pass-through
the `ZZZZ` measurement, then the kernel). -/
theorem fourQubit_sign_XXXX (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    (T2 a b ha hb).toSignedStab.sign XXXX = a :=
  (injStepWith_sign_of_zero (T1 a ha) (ZZZZ_not_mem_T1L a ha) hb (paulix 1) (X1_mem_T1L a ha)
      (by decide)
      (mem_pauliCondition_of_commute (ZZZZ_not_mem_T1L a ha) (pauliCondition_mem _ XXXX) (by decide))
      (by decide)).trans
    (injStepWith_sign_self q4 XXXX_not_mem ha (pauliz 0) Z0_mem_q4 (by decide))

/-- The family is stabilized after conditioning: `ZZZZ ∈ L`. -/
theorem fourQubit_ZZZZ_mem (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    ZZZZ ∈ (T2 a b ha hb).toSignedStab.L := by
  show ZZZZ ∈ pauliCondition (T1 a ha).toSignedStab.L ZZZZ
  exact pauliCondition_mem _ _

/-- The family is stabilized after conditioning: `XXXX ∈ L`. -/
theorem fourQubit_XXXX_mem (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    XXXX ∈ (T2 a b ha hb).toSignedStab.L := by
  show XXXX ∈ pauliCondition (T1 a ha).toSignedStab.L ZZZZ
  exact mem_pauliCondition_of_commute (ZZZZ_not_mem_T1L a ha) (pauliCondition_mem _ XXXX) (by decide)

/-! ## Toy 3 — a surface-code patch (rotated distance-2): family `(Z₀Z₁Z₂Z₃, X₀X₁, X₂X₃)`

A 4-qubit patch with a bulk Z-plaquette and two X-edge checks (`m = 3`). Measured on the input
`⟨X₀,Z₁,Z₂,Z₃⟩` with successive witnesses `X₀` (for the plaquette), `Z₁` (for the first edge), `Z₂` (for
the second). Same bare read-off, one conditioning deeper. -/

/-- The top X-edge `X₀X₁`. -/
def XX01 : Pauli 4 := paulix 0 + paulix 1
/-- The bottom X-edge `X₂X₃`. -/
def XX23 : Pauli 4 := paulix 2 + paulix 3

/-- The patch input `⟨X₀,Z₁,Z₂,Z₃⟩`. -/
noncomputable def spL : Submodule (ZMod 2) (Pauli 4) :=
  Submodule.span (ZMod 2) {paulix 0, pauliz 1, pauliz 2, pauliz 3}

theorem spL_isStabilizer : IsStabilizer spL :=
  isStabilizer_span_of_pairwise (by
    intro p hp q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;> decide)

theorem spL_finrank : Module.finrank (ZMod 2) spL = 4 := by
  have hli : LinearIndependent (ZMod 2) ![paulix 0, pauliz 1, pauliz 2, pauliz 3] :=
    linearIndependent_of_omega_dual (n := 4) (k := 4)
      (v := ![paulix 0, pauliz 1, pauliz 2, pauliz 3])
      (w := ![pauliz 0, paulix 1, paulix 2, paulix 3]) (by decide)
  have hrange : ({paulix 0, pauliz 1, pauliz 2, pauliz 3} : Set (Pauli 4))
      = Set.range ![paulix 0, pauliz 1, pauliz 2, pauliz 3] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩, ⟨3, by simp⟩]
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  have hspan : spL = Submodule.span (ZMod 2) (Set.range ![paulix 0, pauliz 1, pauliz 2, pauliz 3]) := by
    unfold spL; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

noncomputable def sp : PureSignedStab 4 := mkPureSlab spL_isStabilizer spL_finrank

theorem ZZZZ_not_mem_sp : ZZZZ ∉ sp.toSignedStab.L := by
  show ZZZZ ∉ spL
  intro h
  have h0 : omega ZZZZ (paulix 0) = 0 :=
    spL_isStabilizer ZZZZ h (paulix 0) (Submodule.subset_span (by simp))
  rw [show omega ZZZZ (paulix 0) = 1 from by decide] at h0
  exact one_ne_zero h0

theorem X0_mem_sp : paulix 0 ∈ sp.toSignedStab.L := Submodule.subset_span (by simp)
theorem Z1_mem_sp : pauliz 1 ∈ sp.toSignedStab.L := Submodule.subset_span (by simp)
theorem Z2_mem_sp : pauliz 2 ∈ sp.toSignedStab.L := Submodule.subset_span (by simp)

/-- **Condition on the plaquette `ZZZZ`** (outcome `a`), witness `X₀`. -/
noncomputable def U1 (a : ℂ) (ha : a * a = 1) : PureSignedStab 4 :=
  injStepWith sp ZZZZ_not_mem_sp ha (paulix 0) X0_mem_sp (by decide)

theorem Z1_mem_U1L (a : ℂ) (ha : a * a = 1) : pauliz 1 ∈ (U1 a ha).toSignedStab.L := by
  show pauliz 1 ∈ pauliCondition spL ZZZZ
  exact mem_pauliCondition_of_commute ZZZZ_not_mem_sp Z1_mem_sp (by decide)

theorem Z2_mem_U1L (a : ℂ) (ha : a * a = 1) : pauliz 2 ∈ (U1 a ha).toSignedStab.L := by
  show pauliz 2 ∈ pauliCondition spL ZZZZ
  exact mem_pauliCondition_of_commute ZZZZ_not_mem_sp Z2_mem_sp (by decide)

theorem XX01_not_mem_U1L (a : ℂ) (ha : a * a = 1) : XX01 ∉ (U1 a ha).toSignedStab.L := by
  show XX01 ∉ pauliCondition spL ZZZZ
  intro h
  have h0 : omega XX01 (pauliz 1) = 0 :=
    pauliCondition_isStabilizer spL_isStabilizer ZZZZ XX01 h (pauliz 1) (Z1_mem_U1L a ha)
  rw [show omega XX01 (pauliz 1) = 1 from by decide] at h0
  exact one_ne_zero h0

/-- **Condition on the first edge `XX01`** (outcome `b`), witness `Z₁`. -/
noncomputable def U2 (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) : PureSignedStab 4 :=
  injStepWith (U1 a ha) (XX01_not_mem_U1L a ha) hb (pauliz 1) (Z1_mem_U1L a ha) (by decide)

theorem Z2_mem_U2L (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    pauliz 2 ∈ (U2 a b ha hb).toSignedStab.L := by
  show pauliz 2 ∈ pauliCondition (U1 a ha).toSignedStab.L XX01
  exact mem_pauliCondition_of_commute (XX01_not_mem_U1L a ha) (Z2_mem_U1L a ha) (by decide)

theorem XX23_not_mem_U2L (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    XX23 ∉ (U2 a b ha hb).toSignedStab.L := by
  show XX23 ∉ pauliCondition (U1 a ha).toSignedStab.L XX01
  intro h
  have h0 : omega XX23 (pauliz 2) = 0 :=
    pauliCondition_isStabilizer (pauliCondition_isStabilizer spL_isStabilizer ZZZZ) XX01 XX23 h
      (pauliz 2) (Z2_mem_U2L a b ha hb)
  rw [show omega XX23 (pauliz 2) = 1 from by decide] at h0
  exact one_ne_zero h0

/-- **Condition on the second edge `XX23`** (outcome `c`), witness `Z₂`. The conditioned state for the
3-bit outcome `(a,b,c)`. -/
noncomputable def U3 (a b c : ℂ) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    PureSignedStab 4 :=
  injStepWith (U2 a b ha hb) (XX23_not_mem_U2L a b ha hb) hc (pauliz 2) (Z2_mem_U2L a b ha hb)
    (by decide)

/-- **Truth-table read-off:** the second edge's sign *is* the outcome `c` (the kernel). -/
theorem surfacePatch_sign_XX23 (a b c : ℂ) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    (U3 a b c ha hb hc).toSignedStab.sign XX23 = c :=
  injStepWith_sign_self (U2 a b ha hb) (XX23_not_mem_U2L a b ha hb) hc (pauliz 2) (Z2_mem_U2L a b ha hb)
    (by decide)

/-- **Truth-table read-off:** the first edge's sign *is* the outcome `b` (pass-through the second-edge
measurement, then the kernel). -/
theorem surfacePatch_sign_XX01 (a b c : ℂ) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    (U3 a b c ha hb hc).toSignedStab.sign XX01 = b :=
  (injStepWith_sign_of_zero (U2 a b ha hb) (XX23_not_mem_U2L a b ha hb) hc (pauliz 2)
      (Z2_mem_U2L a b ha hb) (by decide)
      (mem_pauliCondition_of_commute (XX23_not_mem_U2L a b ha hb) (pauliCondition_mem _ XX01)
        (by decide)) (by decide)).trans
    (injStepWith_sign_self (U1 a ha) (XX01_not_mem_U1L a ha) hb (pauliz 1) (Z1_mem_U1L a ha) (by decide))

/-- **Truth-table read-off:** the plaquette's sign *is* the outcome `a` (pass-through both edge
measurements, then the kernel). -/
theorem surfacePatch_sign_ZZZZ (a b c : ℂ) (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1) :
    (U3 a b c ha hb hc).toSignedStab.sign ZZZZ = a :=
  ((injStepWith_sign_of_zero (U2 a b ha hb) (XX23_not_mem_U2L a b ha hb) hc (pauliz 2)
        (Z2_mem_U2L a b ha hb) (by decide)
        (mem_pauliCondition_of_commute (XX23_not_mem_U2L a b ha hb)
          (mem_pauliCondition_of_commute (XX01_not_mem_U1L a ha) (pauliCondition_mem _ ZZZZ) (by decide))
          (by decide)) (by decide)).trans
      (injStepWith_sign_of_zero (U1 a ha) (XX01_not_mem_U1L a ha) hb (pauliz 1) (Z1_mem_U1L a ha)
        (by decide)
        (mem_pauliCondition_of_commute (XX01_not_mem_U1L a ha) (pauliCondition_mem _ ZZZZ) (by decide))
        (by decide))).trans
    (injStepWith_sign_self sp ZZZZ_not_mem_sp ha (paulix 0) X0_mem_sp (by decide))

end FTQCLib.Conditioning

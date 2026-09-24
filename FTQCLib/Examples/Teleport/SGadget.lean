/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.Teleport.ZTeleport
import FTQCLib.Hilbert.GateLifts

/-! # The S-gadget (gate injection) — support and feed-forward

Applying the phase gate `S` to a data qubit by *injection*: data on qubit 0 (here an `X`-eigenstate,
so `S` does something visible — `S` fixes `Z`-eigenstates), ancilla `|+i⟩` on qubit 1 (`Y`-stabilized),
entangle with a CNOT (control 0, target 1), then measure the ancilla in `Z`. `S` sends the data's
`X`-stabilizer to a `Y`-stabilizer (`S: X → Y`).

The first non-inert rung of the gadget ladder (above the computationally-inert Z-injection), built at
two levels, both axiom-clean:
* **support** (`Yd_mem`): `S: X₀ → Y₀`, via `cnotAt` + `pauliCondition`, reusing the Z-teleport helpers;
* **feed-forward sign** (`SoutS_sign_Yd`): the outcome `m` is a free factor in the data sign, so the
  `Z^m` correction is forced — via the **CNOT-Clifford bridge** `isCliffordOperator_cnotGate` (the
  `IsCliffordOperator` witness for CNOT) + `cliffordActionPure` + `measSign_of_one`. -/

namespace FTQCLib.SInjection

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Teleport FTQCLib.Hilbert FTQCLib.Gates

/-! ## The CNOT-Clifford bridge (unlocks the sign / feed-forward level)

`cnotGate` is a Clifford operator — the analogue for CNOT of the `IsCliffordOperator` witnesses for
`H` and `S` (`isCliffordOperator_hadamardEquiv`, `isCliffordOperator_phaseGate`). A one-liner from the
existing phaseless conjugation law `cnotGate_conj`. This is what `cliffordAction`/`qConjₗ` need to put
the CNOT into the operation monoid, so the S-gadget can be done at the *sign* (feed-forward) level, not
just the support level below. (Belongs in `FTQCLib/Hilbert/CliffordSplitN1.lean` with the other gate
Clifford-ness lemmas; stated here where it is used.) -/
theorem isCliffordOperator_cnotGate {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    IsCliffordOperator (cnotGate i j hij) :=
  fun p => ⟨1, cnotAt i j hij p, by rw [Units.val_one, one_smul]; exact cnotGate_conj i j hij p⟩

/-- The CNOT gate's symplectic image is `cnotAt` exactly (phaseless: `Φ(CNOT) = cnotAt`). -/
theorem cliffordToSymplecticFun_cnot {m : ℕ} (i j : Fin m) (hij : i ≠ j) (p : Pauli m) :
    cliffordToSymplecticFun (isCliffordOperator_cnotGate i j hij) p = cnotAt i j hij p :=
  (cliffordToSymplecticFun_unique (isCliffordOperator_cnotGate i j hij) p (α := 1)
    (q := cnotAt i j hij p) (by rw [Units.val_one, one_smul]; exact cnotGate_conj i j hij p)).symm

/-! ## The post-CNOT support

CNOT (control 0, target 1) applied to the input `⟨X₀, Y₁⟩` gives `cnotAt(X₀) = X₀X₁` and
`cnotAt(Y₁) = X₁Z₀Z₁`. We take those as the post-entanglement generators. -/

/-- `cnotAt(X₀) = X₀X₁`. -/
def gA : Pauli 2 := paulix 0 + paulix 1
/-- `cnotAt(Y₁) = X₁Z₀Z₁`. -/
def gB : Pauli 2 := paulix 1 + pauliz 0 + pauliz 1
/-- The measured observable: `Z` on the ancilla. -/
def Za : Pauli 2 := pauliz 1
/-- The `S`-transported data stabilizer: `Y₀ = X₀Z₀` (`S` sends the data's `X` to `Y`). -/
def Yd : Pauli 2 := paulix 0 + pauliz 0

/-- The post-CNOT support `⟨X₀X₁, X₁Z₀Z₁⟩`. -/
noncomputable def Lcnot : Submodule (ZMod 2) (Pauli 2) := Submodule.span (ZMod 2) {gA, gB}

/-- The two generators commute (the support is isotropic). -/
theorem gA_gB_pairwise :
    ∀ p ∈ ({gA, gB} : Set (Pauli 2)), ∀ q ∈ ({gA, gB} : Set (Pauli 2)), omega p q = 0 := by
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> decide

theorem Lcnot_isStabilizer : IsStabilizer Lcnot := isStabilizer_span_of_pairwise gA_gB_pairwise

theorem gA_mem : gA ∈ Lcnot := Submodule.subset_span (by simp)
theorem gB_mem : gB ∈ Lcnot := Submodule.subset_span (by simp)

/-- `Z₁ ∉` the post-CNOT support — it anticommutes with `gA = X₀X₁`, but the support is isotropic. -/
theorem Za_not_mem : Za ∉ Lcnot := by
  intro hZa
  have h0 : omega Za gA = 0 := Lcnot_isStabilizer Za hZa gA gA_mem
  have h1 : omega Za gA = 1 := by decide
  rw [h1] at h0
  exact one_ne_zero h0

/-- **`S` transports the data's stabilizer `X₀ → Y₀`.** After the CNOT and the `Z₁` measurement, the
data qubit's stabilizer is `Y₀ = X₀Z₀` — the phase gate `S` applied (at the support level). -/
theorem Yd_mem : Yd ∈ pauliCondition Lcnot Za := by
  have hsum : Yd = (gA + gB) + Za := by decide
  rw [hsum]
  exact add_mem
    (mem_pauliCondition_of_commute Za_not_mem (add_mem gA_mem gB_mem) (by decide))
    (pauliCondition_mem _ Za)

/-! ## Sign level: the input signed state `⟨X₀, Y₁⟩`

The data qubit's `X`-eigenstate (sign carried) tensor the ancilla `|+i⟩` (`Y`-stabilized), as a full
`PureSignedStab` — reusing the Z-teleport helpers (`isStabilizer_span_of_pairwise`,
`linearIndependent_of_omega_dual`). The CNOT transport (via `isCliffordOperator_cnotGate`) and the
feed-forward sign theorem follow. -/

/-- Input generator: data `X` on qubit 0. -/
def Xd : Pauli 2 := paulix 0
/-- Input generator: ancilla `Y` on qubit 1 (the `|+i⟩` resource). -/
def Ya : Pauli 2 := paulix 1 + pauliz 1

/-- The input support `⟨X₀, Y₁⟩`. -/
noncomputable def Lin_S : Submodule (ZMod 2) (Pauli 2) := Submodule.span (ZMod 2) {Xd, Ya}

theorem Lin_S_pairwise :
    ∀ p ∈ ({Xd, Ya} : Set (Pauli 2)), ∀ q ∈ ({Xd, Ya} : Set (Pauli 2)), omega p q = 0 := by
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> decide

theorem Lin_S_isStabilizer : IsStabilizer Lin_S := isStabilizer_span_of_pairwise Lin_S_pairwise

/-- `finrank ⟨X₀, Y₁⟩ = 2` via the `ω`-dual family `Z₀, Z₁`. -/
theorem Lin_S_finrank : Module.finrank (ZMod 2) Lin_S = 2 := by
  have hli : LinearIndependent (ZMod 2) ![Xd, Ya] :=
    linearIndependent_of_omega_dual (w := ![pauliz 0, pauliz 1]) (by decide)
  have hrange : ({Xd, Ya} : Set (Pauli 2)) = Set.range ![Xd, Ya] := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  have hspan : Lin_S = Submodule.span (ZMod 2) (Set.range ![Xd, Ya]) := by
    unfold Lin_S; rw [hrange]
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-- The input as a pure signed Lagrangian. -/
noncomputable def SinS : PureSignedStab 2 :=
  ⟨tighten (refStab Lin_S_isStabilizer),
    by rw [tighten_L]; exact Lin_S_isStabilizer,
    by rw [tighten_L]; exact Lin_S_finrank,
    fun p hp => tighten_sign_not_mem _ hp⟩

@[simp] theorem SinS_L : SinS.toSignedStab.L = Lin_S := rfl

/-! ## Sign level: the CNOT transport

`cliffordActionPure (cnotGate)` transports the input to the post-CNOT support `Lcnot` — the same
support the support-level proof used, now reached via `cliffordAction` (so the sign comes along). -/

/-- The CNOT transport lands on the support-level `Lcnot = ⟨gA, gB⟩`. -/
theorem Scnot_L :
    (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).L = Lcnot := by
  have hX : (cliffordToSymplectic (isCliffordOperator_cnotGate (0 : Fin 2) 1 (by decide))).toLinearMap
      Xd = gA := by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]
    decide
  have hY : (cliffordToSymplectic (isCliffordOperator_cnotGate (0 : Fin 2) 1 (by decide))).toLinearMap
      Ya = gB := by
    simp only [LinearEquiv.coe_toLinearMap, cliffordToSymplectic_apply,
      cliffordToSymplecticLinear_apply, cliffordToSymplecticFun_cnot]
    decide
  rw [cliffordAction_L, SinS_L]
  unfold Lin_S Lcnot
  rw [Submodule.map_span, Set.image_pair, hX, hY]

/-! ## Sign level: the feed-forward sign (the outcome forces the `Z^m` correction)

Measure `Z₁` on the CNOT-transported state (outcome `m`). The data generator `Y₀` lands on the
`Z₁`-coset (`ω(gA, Y₀)=1`), so `measSign_of_one` pulls out a single factor of `m` — everything else
(the transported input sign, the cocycle phase) is `m`-independent. So the outcome `m` is forced into
the data sign: flipping `m` flips it, and the `Z^m` correction is read off. Same shape as `S2_sign_Z2`,
with the CNOT's `cliffordSign` factor absorbed into the `m`-independent transported sign. -/

/-- The post-measurement state of the S-gadget (CNOT transport, then measure `Z₁` with outcome `m`). -/
noncomputable def SoutS (m : ℂ) (hm : m * m = 1) : SignedStab 2 :=
  measSignedStab (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab)
    (cliffordAction_isStabilizer (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.isStab)
    (by rw [cliffordAction_finrank]; exact SinS.full)
    (by rw [Scnot_L]; exact Za_not_mem) hm gA
    (by rw [Scnot_L]; exact gA_mem) (by decide)

/-- **Feed-forward: the outcome `m` is a free factor in the data qubit's sign.** Everything multiplying
`m` is `m`-independent, so the required `Z^m` correction is determined by the measurement. -/
theorem SoutS_sign_Yd (m : ℂ) (hm : m * m = 1) :
    (SoutS m hm).sign Yd
      = m * (cliffordAction (isCliffordOperator_cnotGate 0 1 (by decide)) SinS.toSignedStab).sign
              (Yd + Za)
          * pauliPhase Za (Yd + Za) := by
  show measSign _ Za gA m Yd = _
  rw [measSign_of_one _ Za gA m (by rw [Scnot_L]; exact Yd_mem) (by decide)]

end FTQCLib.SInjection




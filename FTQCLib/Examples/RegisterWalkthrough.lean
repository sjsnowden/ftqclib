/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.KernelState
import FTQCLib.Hierarchy.GatePolynomials
import FTQCLib.Hierarchy.EffectiveLevel
import FTQCLib.Hierarchy.RzHardness

/-! # The register-load walkthrough, formalised on the `KernelState` carrier

A worked walkthrough: load an 8-bit register into the frame and push it through `H`, `CZ`, `T`,
`T^{1/2}`, reading the `KernelState` field table at each step. Everything is literal
`KernelState`/`DiagPhase` data — no Hilbert kets.

Contents:

* the objects — the Z/X Lagrangians, the loaded register `load0`, and the single-bit gate exponents
  with their levels (mirroring `FTQCLib/Examples/Teleport/TGadget.lean`'s `magicA`);
* the general facts C1 (the classical register is the dimension-0 fibre), C2 (the superposition
  count) and C4 (inertness of a diagonal gate vanishing on the support);
* the numbered steps of the walkthrough: the carrier gate actions and the per-step
  transformation theorems, and the composition/effective-level facts.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy

variable {n : ℕ}

/-! ## The X- and Z-type Lagrangians -/

/-- The X-support of a Pauli, as a `ZMod 2`-linear map `Pauli n → (Fin n → ZMod 2)`. -/
def xProj : Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun p := p.X
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The Z-support of a Pauli, as a `ZMod 2`-linear map. -/
def zProj : Pauli n →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun p := p.Z
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The **Z-type Lagrangian**: the pure-`Z` Paulis (`X`-support zero), i.e. `⟨Z_0, …, Z_{n-1}⟩`.
Its `X`-projection is `⊥`, so a `KernelState` on it has a single-point support. -/
def Lz : Submodule (ZMod 2) (Pauli n) := LinearMap.ker xProj

/-- The **X-type Lagrangian**: the pure-`X` Paulis (`Z`-support zero), i.e. `⟨X_0, …, X_{n-1}⟩`.
Its `X`-projection is everything, so a `KernelState` on it has full support (the whole cube). -/
def Lx : Submodule (ZMod 2) (Pauli n) := LinearMap.ker zProj

@[simp] theorem mem_Lz {p : Pauli n} : p ∈ Lz ↔ p.X = 0 := LinearMap.mem_ker
@[simp] theorem mem_Lx {p : Pauli n} : p ∈ Lx ↔ p.Z = 0 := LinearMap.mem_ker

/-! ## Step 1 — the loaded all-zeros register `00000000` -/

/-- Loading the all-zeros 8-bit register: `L` the Z-Lagrangian, `q = 0`, `c = 1`, `x₀ = 0`. The classical
register lives entirely in `x₀`; here it is `0`. -/
noncomputable def load0 : KernelState 8 where
  m := 1
  q := 0
  c := 1
  L := Lz
  x₀ := 0

/-- **The loaded register is the single point `x₀`.** Its support `x₀ + π_X(L)` is `{00000000}`, because the
Z-Lagrangian has `π_X(L) = ⊥`. -/
theorem load0_support (w : Fin 8 → ZMod 2) :
    (∃ p ∈ load0.L, w = load0.x₀ + p.X) ↔ w = 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpx : p.X = 0 := mem_Lz.mp hp
    simp [load0, hpx]
  · rintro rfl
    exact ⟨0, Submodule.zero_mem _, by simp [load0]⟩

/-! ## The single-bit gate exponents and their levels

Per bit, `H` puts the bit in superposition and the diagonal gate writes the phase. These record the
exponent `q` and its Clifford-hierarchy `level` for each single-bit gate, reusing the proven level theorems
(as `TGadget.magicA` does for `T`). -/

/-- One bit after `H` then `T` — the magic state `T|+⟩`: support `{0,1}` (`L = ⊤`), exponent `x/8`. -/
noncomputable def tBit : KernelState 1 where
  m := 3
  q := DiagPhase.tGatePoly 0
  c := 1
  L := ⊤
  x₀ := 0

/-- **`T|+⟩` is level 3** — off the stabilizer floor. -/
theorem tBit_level : tBit.q.level = 3 := DiagPhase.tGatePoly_level 0

/-- One bit after `H` then `T^{1/2}` — the finer magic state: exponent `x/16` (precision `m = 4`). -/
noncomputable def thalfBit : KernelState 1 where
  m := 4
  q := DiagPhase.rzGatePoly 0 4
  c := 1
  L := ⊤
  x₀ := 0

/-- **`T^{1/2}|+⟩` is level 4** — one rung deeper than `T`, by precision. -/
theorem thalfBit_level : thalfBit.q.level = 4 := by
  haveI : Fact (1 < 2 ^ 4) := ⟨by norm_num⟩
  exact DiagPhase.rzGatePoly_level 0 4 (by norm_num)

/-! ## The support subcube — the normal-form spine

`psi` depends on `L` only through `π_X(L)` (the support test reads `p.X`). So a state's support is the affine
subcube `x₀ + suppSpace K`, a flat of `𝔽₂ⁿ`, and the classical registers are its dimension-0 fibre (C1). -/

@[simp] theorem xProj_apply (p : Pauli n) : xProj p = p.X := rfl

/-- The linear part of the support: the X-image of `L` (which bits are superposed). -/
noncomputable def suppSpace (K : KernelState n) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.map xProj K.L

/-- The number of superposed bits: the dimension of the support subcube. -/
noncomputable def suppDim (K : KernelState n) : ℕ := Module.finrank (ZMod 2) (suppSpace K)

/-- **Normal form (support).** `w` is in the support of `K` exactly when it lies in the affine subcube
`x₀ + suppSpace K`. This is the state-layer spine: the support is a flat of `𝔽₂ⁿ`. -/
theorem mem_support (K : KernelState n) (w : Fin n → ZMod 2) :
    (∃ p ∈ K.L, w = K.x₀ + p.X) ↔ w - K.x₀ ∈ suppSpace K := by
  rw [suppSpace, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, by rw [xProj_apply]; abel⟩
  · rintro ⟨p, hp, hp2⟩
    refine ⟨p, hp, ?_⟩
    rw [xProj_apply] at hp2
    rw [hp2]; abel

/-- A classical `n`-bit register with value `v`: the single basis state at `v`. `load0` is `classical 0`. -/
noncomputable def classical (v : Fin n → ZMod 2) : KernelState n where
  m := 1;  q := 0;  c := 1;  L := Lz;  x₀ := v

theorem load0_eq_classical : load0 = classical 0 := rfl

/-- **C1 — the classical register is the dimension-0 fibre.** Its support subcube is trivial. -/
@[simp] theorem classical_suppSpace (v : Fin n → ZMod 2) : suppSpace (classical v) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro y hy
  rw [suppSpace, Submodule.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have hpx : p.X = 0 := mem_Lz.mp hp
  rw [xProj_apply, hpx]
  exact Submodule.zero_mem _

/-- The classical register's support is the single point `v` — a `KernelState`-level statement. -/
theorem classical_support (v w : Fin n → ZMod 2) :
    (∃ p ∈ (classical v).L, w = (classical v).x₀ + p.X) ↔ w = v := by
  rw [mem_support, classical_suppSpace, Submodule.mem_bot, sub_eq_zero]
  exact Iff.rfl

/-! ## C4 — diagonal gates on the phase, and the inert cases

A diagonal gate is a phase polynomial `P`; applying it to a flat (`q = 0`) state writes `P` into the exponent.
It is **inert on the state's phase exactly when `P` vanishes on the support** — from which the walkthrough's
inert steps are corollaries, rather than separate proofs. -/

/-- Apply a diagonal gate `P` to a flat state: write `P` into the exponent (lifting the precision to `P`'s).
Correct when `K.q = 0` (the states the walkthrough applies diagonal gates to). -/
noncomputable def applyDiagFrom0 {mP : ℕ} (K : KernelState n) (P : DiagPhase n mP) : KernelState n where
  m := mP;  q := P;  c := K.c;  L := K.L;  x₀ := K.x₀

/-- **C4 (inertness).** If `K` is flat and the gate polynomial `P` vanishes on the support, then applying `P`
leaves the state's **phase** on the support unchanged. Stated with `realPhase` (the actual radian angle,
ℝ-valued and comparable across precisions) — `eval` cannot be equated across the `m`-change. -/
theorem applyDiagFrom0_inert {mP : ℕ} (K : KernelState n) (P : DiagPhase n mP)
    (hq : K.q = 0)
    (hP : ∀ w, (∃ p ∈ K.L, w = K.x₀ + p.X) → DiagPhase.eval P w = 0) :
    ∀ w, (∃ p ∈ K.L, w = K.x₀ + p.X) →
      DiagPhase.realPhase (applyDiagFrom0 K P).q w = DiagPhase.realPhase K.q w := by
  intro w hw
  have hPL : DiagPhase.realPhase (applyDiagFrom0 K P).q w = 0 := by
    show DiagPhase.realPhase P w = 0
    unfold DiagPhase.realPhase
    rw [hP w hw]; simp
  have hqL : DiagPhase.realPhase K.q w = 0 := by
    rw [hq]; simp [DiagPhase.realPhase, DiagPhase.eval]
  rw [hPL, hqL]

/-- The `T`-on-all-8-bits exponent: `∑_i x_i` over `ℤ/8`. -/
noncomputable def tRegPoly : DiagPhase 8 3 := ∑ i, DiagPhase.tGatePoly i

theorem tRegPoly_eval_zero : DiagPhase.eval tRegPoly (0 : Fin 8 → ZMod 2) = 0 := by
  unfold tRegPoly DiagPhase.eval
  rw [map_sum]
  refine Finset.sum_eq_zero ?_
  intro i _
  simp [DiagPhase.tGatePoly, MvPolynomial.eval_X, DiagPhase.liftBinary]

/-- **Step 6 (corollary of C4).** `T` on the all-zeros register is inert: its exponent vanishes on the
single-point support `{0}`, so the state's phase is unchanged. No bespoke proof — just C4. -/
theorem step6_T_inert :
    ∀ w, (∃ p ∈ load0.L, w = load0.x₀ + p.X) →
      DiagPhase.realPhase (applyDiagFrom0 load0 tRegPoly).q w = DiagPhase.realPhase load0.q w := by
  refine applyDiagFrom0_inert load0 tRegPoly rfl ?_
  intro w hw
  rw [(load0_support w).mp hw]
  exact tRegPoly_eval_zero

/-! ## Step 4 — the mixed Lagrangian, and CZ inert as a second C4 corollary

Hadamarding only bits `S` gives a *mixed* Lagrangian: X-type on `S`, Z-type off it. On the half-Hadamard
state (`S = {0,1,2,3}`), pairwise `CZ` is inert because its polynomial `∑ xᵢxᵢ₊₄` vanishes on the support
(the un-Hadamarded bits `4..7` are pinned to `0`). Another instance of C4. -/

/-- The per-bit "mixed" Lagrangian: X-type on `S`, Z-type off `S`. `Lmix ∅ = Lz`, `Lmix univ = Lx`. -/
def Lmix (S : Finset (Fin n)) : Submodule (ZMod 2) (Pauli n) where
  carrier := {p | (∀ i ∈ S, p.Z i = 0) ∧ (∀ i, i ∉ S → p.X i = 0)}
  zero_mem' := ⟨fun i _ => by simp, fun i _ => by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨fun i hi => by simp [ha.1 i hi, hb.1 i hi], fun i hi => by simp [ha.2 i hi, hb.2 i hi]⟩
  smul_mem' := fun c {a} ha =>
    ⟨fun i hi => by simp [ha.1 i hi], fun i hi => by simp [ha.2 i hi]⟩

/-- Off `S`, a member of `Lmix S` carries no `X`. -/
theorem Lmix_X_zero {S : Finset (Fin n)} {p : Pauli n} (hp : p ∈ Lmix S) {i : Fin n} (hi : i ∉ S) :
    p.X i = 0 := hp.2 i hi

/-- The half-Hadamard state: X-type on bits 0–3, Z-type on 4–7; support the 4-cube with bits 4–7 pinned. -/
noncomputable def halfH : KernelState 8 where
  m := 1;  q := 0;  c := 1;  L := Lmix ({0, 1, 2, 3} : Finset (Fin 8));  x₀ := 0

/-- The pairwise-CZ exponent `∑ xᵢ xᵢ₊₄` over `ℤ/2`. -/
noncomputable def czPairPoly : DiagPhase 8 1 :=
  MvPolynomial.X 0 * MvPolynomial.X 4 + MvPolynomial.X 1 * MvPolynomial.X 5
    + MvPolynomial.X 2 * MvPolynomial.X 6 + MvPolynomial.X 3 * MvPolynomial.X 7

/-- The CZ exponent vanishes on the half-Hadamard support: bits 4–7 are `0`, killing every term. -/
theorem czPairPoly_vanishes :
    ∀ w, (∃ p ∈ halfH.L, w = halfH.x₀ + p.X) → DiagPhase.eval czPairPoly w = 0 := by
  rintro w ⟨p, hp, rfl⟩
  have h4 : p.X 4 = 0 := Lmix_X_zero hp (by decide)
  have h5 : p.X 5 = 0 := Lmix_X_zero hp (by decide)
  have h6 : p.X 6 = 0 := Lmix_X_zero hp (by decide)
  have h7 : p.X 7 = 0 := Lmix_X_zero hp (by decide)
  simp [DiagPhase.eval, czPairPoly, DiagPhase.liftBinary, halfH, h4, h5, h6, h7]

/-- **Step 4 (corollary of C4).** Pairwise `CZ` on the half-Hadamard state is inert — its polynomial vanishes
on the support. Again no bespoke proof, just C4. -/
theorem step4_CZ_inert :
    ∀ w, (∃ p ∈ halfH.L, w = halfH.x₀ + p.X) →
      DiagPhase.realPhase (applyDiagFrom0 halfH czPairPoly).q w = DiagPhase.realPhase halfH.q w :=
  applyDiagFrom0_inert halfH czPairPoly rfl czPairPoly_vanishes

/-! ## The unified bigraded device — the interaction × precision lattice

Neither single axis covers CS (controlled-S: degree 2 at precision 2, level `(2-1)+2 = 3` — on *neither* the
pure-precision `rzGatePoly` axis (degree 1) nor the pure-interaction `multiZPoly` axis (`m=1`)). The right
object is one **bigraded** device: the `|A|`-controlled `2ᵐ`-th root of `Z`, whose level is the sum of the two
axes, `(m-1) + |A|`. It subsumes `rzGatePoly` (`|A|=1`), `multiZPoly` (`m=1`), CS, T, CZ, CCZ — the whole
lattice. Over `ℤ/2ᵐ` (not a domain for `m ≥ 2`) the `totalDegree` proof goes through the **monomial form**,
not domain multiplication. -/

/-- `(∑_{i∈A} single i 1).sum = |A|` — the degree of the product monomial. -/
private theorem sum_singles_sum (A : Finset (Fin n)) :
    (∑ i ∈ A, Finsupp.single i (1 : ℕ)).sum (fun _ e => e) = A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index rfl, ih, Finset.card_insert_of_notMem ha]
    omega

/-- The **unified device**: the `|A|`-controlled `2ᵐ`-th root of `Z`, exponent `∏_{i∈A} xᵢ` over `ℤ/2ᵐ`. -/
noncomputable def ctrlRootPoly (A : Finset (Fin n)) (m : ℕ) : DiagPhase n m := ∏ i ∈ A, MvPolynomial.X i

/-- The device is a single monomial: `∏_{i∈A} xᵢ = monomial (indicator A) 1`. -/
theorem ctrlRoot_eq_monomial (A : Finset (Fin n)) (m : ℕ) :
    ctrlRootPoly A m = MvPolynomial.monomial (∑ i ∈ A, Finsupp.single i 1) (1 : ZMod (2 ^ m)) := by
  unfold ctrlRootPoly
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, MvPolynomial.X,
      MvPolynomial.monomial_mul, one_mul]

theorem ctrlRootPoly_totalDegree (A : Finset (Fin n)) (m : ℕ) [Fact (1 < 2 ^ m)] :
    (ctrlRootPoly A m).totalDegree = A.card := by
  rw [ctrlRoot_eq_monomial, MvPolynomial.totalDegree_monomial _ one_ne_zero, sum_singles_sum]

/-- **The bigraded level: `(m-1) + |A|`** — precision plus interaction, the whole lattice in one theorem. -/
theorem ctrlRootPoly_level (A : Finset (Fin n)) (m : ℕ) [Fact (1 < 2 ^ m)] :
    (ctrlRootPoly A m).level = (m - 1) + A.card := by
  unfold DiagPhase.level
  rw [ctrlRootPoly_totalDegree]

/-- The **interaction axis** (`m=1`): the `|A|`-controlled `Z`, an instance of the unified device. -/
noncomputable def multiZPoly (A : Finset (Fin n)) : DiagPhase n 1 := ctrlRootPoly A 1

theorem multiZPoly_level (A : Finset (Fin n)) : (multiZPoly A).level = A.card := by
  haveI : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
  rw [multiZPoly, ctrlRootPoly_level]; simp

/-- `CZ` is level 2 (pure interaction, `m=1`, `|A|=2`). -/
theorem cz_level {i j : Fin n} (h : i ≠ j) : (multiZPoly {i, j}).level = 2 := by
  rw [multiZPoly_level, Finset.card_pair h]

/-- **CS = controlled-S is level 3** — interaction 2 at precision 2, `(2-1)+2 = 3`: the interior point of the
level-3 anti-diagonal, on neither single axis, covered by the unified device. -/
theorem cs_level {i j : Fin n} (h : i ≠ j) : (ctrlRootPoly {i, j} 2).level = 3 := by
  haveI : Fact (1 < 2 ^ 2) := ⟨by norm_num⟩
  rw [ctrlRootPoly_level, Finset.card_pair h]

/-! ## The Clifford layer — H rotates L (Step 2)

Per the reconciliation, a non-diagonal Clifford acts on the *full* `L` by its symplectic map (it mixes X and
Z, so it cannot be pushed to the support shadow). For `H` on every bit that map is the global `X ↔ Z` swap
`pauliSwap = Φ(H^⊗n)` — definable pure-frame, no Hilbert cocycle (these states are real-amplitude, trivial
sign). It rotates the Z-Lagrangian to the X-Lagrangian, exploding the support from a point to the full cube. -/

/-- The symplectic image of `H^⊗n`: the global `X ↔ Z` swap on the Pauli phase space. -/
def pauliSwap : Pauli n →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨p.Z, p.X⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp] theorem pauliSwap_apply (p : Pauli n) : pauliSwap p = ⟨p.Z, p.X⟩ := rfl

/-- A Clifford acts on the carrier by its symplectic map on the full `L` (the geometric half). -/
noncomputable def applyClifford (g : Pauli n →ₗ[ZMod 2] Pauli n) (K : KernelState n) : KernelState n :=
  { K with L := Submodule.map g K.L }

/-- **`H^⊗n` rotates the Z-Lagrangian to the X-Lagrangian.** -/
theorem map_pauliSwap_Lz : Submodule.map pauliSwap (Lz (n := n)) = Lx := by
  ext q
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_Lx]
    simpa using mem_Lz.mp hp
  · intro hq
    rw [mem_Lx] at hq
    exact ⟨⟨q.Z, q.X⟩, mem_Lz.mpr (by simpa using hq), by ext <;> simp⟩

/-- **Step 2.** `H` on the loaded register rotates `L` from Z-type to X-type. -/
theorem step2_H_rotates : (applyClifford pauliSwap load0).L = Lx := map_pauliSwap_Lz

/-- The X-Lagrangian's support subcube is everything — `H` explodes a point to the full cube. -/
theorem Lx_suppSpace : Submodule.map xProj (Lx (n := n)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [Submodule.mem_map]
  exact ⟨⟨v, 0⟩, by simp [mem_Lx], rfl⟩

/-! ## Step 3 — H on some bits → the mixed Lagrangian

Hadamarding only the bits in `S` swaps `X ↔ Z` there and leaves the rest — the symplectic image of `H` on
`S`. It rotates the Z-Lagrangian to the mixed Lagrangian `Lmix S` (X-type on `S`, Z-type off it). -/

/-- `H` on the bits in `S` only: swap `X ↔ Z` on `S`, identity off it. -/
def pauliSwapOn (S : Finset (Fin n)) : Pauli n →ₗ[ZMod 2] Pauli n where
  toFun p := ⟨fun i => if i ∈ S then p.Z i else p.X i, fun i => if i ∈ S then p.X i else p.Z i⟩
  map_add' _ _ := by ext i <;> by_cases hi : i ∈ S <;> simp [hi]
  map_smul' _ _ := by ext i <;> by_cases hi : i ∈ S <;> simp [hi]

@[simp] theorem pauliSwapOn_X (S : Finset (Fin n)) (p : Pauli n) (i : Fin n) :
    (pauliSwapOn S p).X i = if i ∈ S then p.Z i else p.X i := rfl
@[simp] theorem pauliSwapOn_Z (S : Finset (Fin n)) (p : Pauli n) (i : Fin n) :
    (pauliSwapOn S p).Z i = if i ∈ S then p.X i else p.Z i := rfl

/-- **`H` on `S` rotates the Z-Lagrangian to the mixed Lagrangian `Lmix S`** — X-type on `S`, Z-type off it. -/
theorem map_pauliSwapOn_Lz (S : Finset (Fin n)) :
    Submodule.map (pauliSwapOn S) (Lz (n := n)) = Lmix S := by
  ext q
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpx : p.X = 0 := mem_Lz.mp hp
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simp [hi, hpx]
    · simp [hi, hpx]
  · intro hq
    obtain ⟨hqS, hqcS⟩ := hq
    refine ⟨pauliSwapOn S q, mem_Lz.mpr ?_, ?_⟩
    · funext i
      by_cases hi : i ∈ S
      · simp [hi, hqS i hi]
      · simp [hi, hqcS i hi]
    · ext i <;> by_cases hi : i ∈ S <;> simp [hi]

/-- **Step 3.** `H` on bits `S` rotates `L` to the mixed Lagrangian — X-type on `S`, Z-type off it. -/
theorem step3_H_partial (S : Finset (Fin 8)) :
    (applyClifford (pauliSwapOn S) load0).L = Lmix S := map_pauliSwapOn_Lz S

/-! ## C2 — the superposition count -/

/-- **C2.** The support subcube has `2^{suppDim}` points — the superposition count is `dim π_X(L)`. (The
support coset `x₀ + suppSpace K` has the same cardinality by translation.) -/
theorem suppSpace_card (K : KernelState n) :
    Nat.card (suppSpace K) = 2 ^ suppDim K := by
  have : Fintype ↥(suppSpace K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, suppDim, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-! ## Step 9 — composition and the effective-level collapse

Composing diagonal gates adds their exponents at the finer precision. The revealing case is `T·T`: the
exponent `2·X₀` over `ℤ/8` has *raw* level `(3-1)+1 = 3` but **effective level 2** — the frame detecting
`T·T = S` (a Clifford), because the coefficient `2` is 2-divisible (`twoAdicVal = 1`). Contrast `T·T^{1/2}`
(coefficient `3`, odd): no reduction, genuine level 4. -/

/-- `twoAdicVal (2 : ℤ/8) = 1` — the coefficient `2` is 2-divisible once. -/
theorem twoAdicVal_two : DiagPhase.twoAdicVal (2 : ZMod (2 ^ 3)) = 1 := by
  rw [DiagPhase.twoAdicVal_of_ne_zero (by decide), show (2 : ZMod (2 ^ 3)).val = 2 from by decide,
    Nat.Prime.factorization Nat.prime_two, Finsupp.single_eq_same]

/-- **`T·T` collapses to `S` — effective level 2, not raw level 3.** The 2-adic discount on the coefficient
`2` catches `T² = S`, a Clifford. -/
theorem tt_effectiveLevel :
    DiagPhase.effectiveLevel (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) (2 : ZMod (2 ^ 3))) = 2 := by
  rw [DiagPhase.effectiveLevel_monomial_eq (by decide)]
  unfold DiagPhase.effLevelMonom
  rw [twoAdicVal_two, Finsupp.sum_single_index rfl]

/-- **`T·T^{1/2}` stays level 4** — coefficient `3` is odd, no 2-adic reduction. -/
theorem tThalf_level :
    DiagPhase.level (MvPolynomial.monomial (Finsupp.single (0 : Fin 1) 1) (3 : ZMod (2 ^ 4))) = 4 := by
  unfold DiagPhase.level
  rw [MvPolynomial.totalDegree_monomial _ (by decide), Finsupp.sum_single_index rfl]

/-! ## Register-sum applications — the phase turning on across the register (Steps 5, 7, 8)

Applying a single-bit phase gate to every bit gives `q = ∑ᵢ Xᵢ`, a degree-1 phase polynomial; its level is
pure precision `(m-1)+1`, so the T-register sits at level 3 and the T^{1/2}-register at level 4. Applying a
CZ across every pair gives `q = ∑ xₐxᵦ`, a homogeneous degree-2 phase (the graph state), at level 2 — the
interaction axis. -/

/-- `∑ᵢ Xᵢ` has total degree 1 (a linear form): `≤ 1` from each `Xᵢ`, `≥ 1` from the surviving monomial
`single 0 1`. -/
theorem totalDegree_sum_X {N M : ℕ} [NeZero N] (h1 : (1 : ZMod (2 ^ M)) ≠ 0) :
    (∑ i : Fin N, (MvPolynomial.X i : DiagPhase N M)).totalDegree = 1 := by
  classical
  haveI : Nontrivial (ZMod (2 ^ M)) := nontrivial_of_ne 1 0 h1
  refine le_antisymm ?_ ?_
  · refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    exact le_of_eq (MvPolynomial.totalDegree_X i)
  · have hc : MvPolynomial.coeff (Finsupp.single (0 : Fin N) 1)
        (∑ i : Fin N, (MvPolynomial.X i : DiagPhase N M)) = 1 := by
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_single (0 : Fin N)]
      · rw [MvPolynomial.coeff_X]
      · intro b _ hb
        rw [MvPolynomial.coeff_X', if_neg]
        exact fun hcon => hb (Finsupp.single_left_injective one_ne_zero hcon)
      · intro h; exact absurd (Finset.mem_univ _) h
    have hmem := MvPolynomial.mem_support_iff.mpr (by rw [hc]; exact h1)
    have hle := MvPolynomial.le_totalDegree hmem
    rwa [Finsupp.sum_single_index rfl] at hle

/-- **Step 7.** The T-register `∑ᵢ Xᵢ` (all bits at precision `m=3`) sits at **level 3** — pure precision. -/
theorem tReg_level : DiagPhase.level tRegPoly = 3 := by
  unfold DiagPhase.level tRegPoly
  simp only [DiagPhase.tGatePoly]
  rw [totalDegree_sum_X (by decide : (1 : ZMod (2 ^ 3)) ≠ 0)]

/-- The T^{1/2}-register: a `2^4`-th root of Z on every bit. -/
noncomputable def thalfRegPoly : DiagPhase 8 4 := ∑ i, DiagPhase.rzGatePoly i 4

/-- **Step 8.** The T^{1/2}-register sits at **level 4** — one notch deeper on the precision axis. -/
theorem thalfReg_level : DiagPhase.level thalfRegPoly = 4 := by
  unfold DiagPhase.level thalfRegPoly
  simp only [DiagPhase.rzGatePoly]
  rw [totalDegree_sum_X (by decide : (1 : ZMod (2 ^ 4)) ≠ 0)]

/-- The graph-state exponent `∑ xₐxᵦ` is homogeneous of degree 2 (a sum of degree-2 products). -/
theorem czPairPoly_homogeneous : (czPairPoly).IsHomogeneous 2 := by
  unfold czPairPoly
  have hX : ∀ i : Fin 8, (MvPolynomial.X i : DiagPhase 8 1).IsHomogeneous 1 :=
    fun i => MvPolynomial.isHomogeneous_X _ i
  have hmul : ∀ a b : Fin 8, (MvPolynomial.X a * MvPolynomial.X b : DiagPhase 8 1).IsHomogeneous 2 :=
    fun a b => (hX a).mul (hX b)
  exact (((hmul 0 4).add (hmul 1 5)).add (hmul 2 6)).add (hmul 3 7)

/-- The graph-state exponent is nonzero (evaluate at the point supported on bits `0,4`). -/
theorem czPairPoly_ne_zero : czPairPoly ≠ 0 := by
  intro h0
  have heval : MvPolynomial.eval (fun i : Fin 8 => if i = 0 ∨ i = 4 then (1 : ZMod 2) else 0) czPairPoly = 0 := by
    rw [h0]; exact map_zero _
  rw [czPairPoly] at heval
  simp only [map_add, map_mul, MvPolynomial.eval_X] at heval
  revert heval
  decide

/-- **Step 5.** The graph-state exponent has total degree 2 (homogeneous and nonzero). -/
theorem czPairPoly_totalDegree : (czPairPoly).totalDegree = 2 :=
  czPairPoly_homogeneous.totalDegree czPairPoly_ne_zero

/-- **Step 5 (level).** The graph state sits at **level 2** — the interaction axis (degree 2, precision 1). -/
theorem graph_level : DiagPhase.level czPairPoly = 2 := by
  unfold DiagPhase.level
  rw [czPairPoly_totalDegree]

/-! ## Axiom check -/

#print axioms load0_support
#print axioms tBit_level
#print axioms thalfBit_level
#print axioms mem_support
#print axioms classical_suppSpace
#print axioms classical_support
#print axioms applyDiagFrom0_inert
#print axioms step6_T_inert
#print axioms czPairPoly_vanishes
#print axioms step4_CZ_inert
#print axioms ctrlRootPoly_level
#print axioms multiZPoly_level
#print axioms cz_level
#print axioms cs_level
#print axioms map_pauliSwap_Lz
#print axioms step2_H_rotates
#print axioms Lx_suppSpace
#print axioms map_pauliSwapOn_Lz
#print axioms step3_H_partial
#print axioms suppSpace_card
#print axioms twoAdicVal_two
#print axioms tt_effectiveLevel
#print axioms tThalf_level
#print axioms totalDegree_sum_X
#print axioms tReg_level
#print axioms thalfReg_level
#print axioms czPairPoly_homogeneous
#print axioms czPairPoly_ne_zero
#print axioms czPairPoly_totalDegree
#print axioms graph_level

end FTQCLib.Frame.Walkthrough

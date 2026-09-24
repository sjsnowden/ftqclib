/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardElimination
import FTQCLib.Examples.CharSumPairing
import FTQCLib.Hierarchy.GatePolynomials
import FTQCLib.Hierarchy.PolarForm

/-!
# The Clifford gates on the carrier: the diagonal class and CNOT

The diagonal gate `applyDiagSum` adds a phase polynomial and keeps the Lagrangian; on a floor that
Lagrangian goes stale, since a level-two diagonal gate moves the stabilizer by a Z-shear. This
module adds the diagonal gate **with a shear as data** (`applyDiagShearBy S D M`, the Lagrangian
pushed by `zShearBy M`), the shift datum an exponent must satisfy along the shadow for the shear to
be the right one (`DiagShiftDatumBy D M V`), and **the class rule** `applyDiagPolar S D`: the shear
by the polar matrix of the exponent's Boolean normal form, which keeps the floor for every exponent
of level at most two (`isFloor_applyDiagPolar`, under `levelExt D ≤ 2`). The one-bit shear
`applyDiagShear S D k d` is the instance `M = shearLin k d`, and the two letters of the word
alphabet, `S` at bit `i` (precision `≥ 2`) and `CZ` at bits `i ≠ j`, are cases of the class rule
(`applyS_eq_applyDiagPolar`, `applyCZ_eq_applyDiagPolar`). The CNOT constructor `applyCnotSum`
gets its closure with the repaired symplectic lift `cnotPauli`.

Both closures go through one fact: a Pauli of the Lagrangian that acts on a carrier's amplitude by
*some* scalar acts by a sign (`isFloor_of_scalar`, from `pauliAct_pauliAct`). The intertwinings
`pauliAct_zShearBy_of_shift` and `pauliAct_cnotPauli` give the scalar explicitly; for the shear it
has the closed form `(−i)^A · (−1)^B · charOf m c` (`shearScalar_eq`), with `A` the number of bits
where `M x` and `x` both carry `1` and `B` the number where `z` does too.

## Main definitions

* `applyDiagShearBy S D M`, `DiagShiftDatumBy D M V`, `applyDiagPolar S D`; the instances
  `applyDiagShear S D k d`, `DiagShiftDatum D k d V`, `applyS`, `applyCZ`.
* `shearCount M x`, `shearTriple M g` — the two counts of the closed scalar.
* `upperSupport A`, `pairMatrix p` — the letters of a symmetric matrix.

## Main results

* `isFloor_of_scalar` — a carrier whose Lagrangian acts by scalars is a floor.
* `amp_applyDiagSum`, `amp_applyDiagShearBy`, `amp_applyDiagPolar` — DEN for the diagonal gates:
  a phase times the input.
* `isCarrier_applyDiagShearBy_of_symm_on`, `isCarrier_applyDiagPolar` — W: symmetry of the
  pairing on the shadow, which the polar matrix has everywhere.
* `DiagShiftDatumBy.add`, `isSymmPairingOn_of_diagShiftDatumBy`, `eq_of_diagShiftDatumBy_top` —
  the datum adds, forces symmetry on its subspace, and is unique at `⊤`.
* `pauliAct_zShearBy_of_shift`, `shearScalar_eq`, `pauliAct_zShearBy_of_shift_closed` — the
  intertwining for a shear and its scalar in closed form.
* `isFloor_applyDiagShearBy` — **FL from the datum alone**; `isFloor_applyDiagPolar` — FL for the
  class; `diagShiftDatum_sGate`, `diagShiftDatum_czGate` — the two instances carry their datum.
* `mulVecLin_eq_sum_shearLin`, `applyDiagPolar_L_eq_foldl` — **the word form**: the polar
  matrix's shear is the fold of the one-bit shears of its upper support, the `S` and `CZ` letters.
* `mulVecLin_polarMatrix_add`, `applyDiagPolar_add` — **the class rule composes**: two level-two
  diagonal gates in a row are the one gate of the sum exponent.
* `omega_cnotPauli`, `isStabilizer_map_cnotPauli` — the repaired lift is symplectic.
* `amp_applyCnotSum` — DEN for CNOT: the amplitude at the CNOT-permuted word.
* `pauliAct_cnotPauli` — the CNOT intertwining with the sign `(−1)^{x_i z_j (1 + x_j + z_i)}`.
* `isCarrier_applyCnotSum`, `isFloor_applyCnotSum` — W and FL for CNOT (`i ≠ j`).

Everything here is frame-pure. No `FTQCLib.Hilbert`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## A scalar action on a carrier is a signed action -/

/-- On a carrier, a Pauli of `L` acting on the amplitude by a scalar acts by a sign; so a carrier
whose Lagrangian acts by scalars is a floor. -/
theorem isFloor_of_scalar {S : KernelSumState n} (hS : IsCarrier S)
    (h : ∀ g ∈ S.L, ∃ lam : ℂ, pauliAct g (amp S) = fun w => lam * amp S w) : IsFloor S := by
  refine ⟨hS, fun g hg => ?_⟩
  obtain ⟨lam, hact⟩ := h g hg
  have hsq : lam * lam = 1 := by
    have hinv := pauliAct_pauliAct g (amp S)
    rw [hact, pauliAct_mul_left, hact] at hinv
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hS.2.2.2
    have h := congrFun hinv w
    simp only [Pi.zero_apply] at hw
    have h' : (lam * lam) * amp S w = 1 * amp S w := by
      rw [one_mul]
      linear_combination h
    exact mul_right_cancel₀ hw h'
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exact ⟨0, by rw [hact, h1]; simp⟩
  · refine ⟨1, ?_⟩
    rw [hact, h1]
    have hv : ((1 : ZMod 2)).val = 1 := by decide
    rw [hv]
    simp

/-! ## Signs -/

/-- `(−1)` to a sum of bits. -/
theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [show ((1 : ZMod 2) + 1) = 0 by decide, show ((1 : ZMod 2).val) = 1 by decide]

/-- The parity of `zDot` under the shear by `M`: `M` of the X-part pairs with the word. -/
theorem neg_one_pow_zDot_zShearBy (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (g : Pauli n)
    (u : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDot (zShearBy M g) u = (-1) ^ zDot g u * (-1) ^ (dotF2 (M g.X) u).val := by
  rw [← pow_add]
  apply neg_one_pow_eq_of_cast_eq
  push_cast
  rw [zDot_cast_two, zDot_cast_two, ZMod.natCast_zmod_val, zShearBy_Z]
  unfold dotF2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])

/-- The parity of `zDot` under the shear at a bit: the row pairs with the word. -/
theorem neg_one_pow_zDot_zShear (k : Fin n) (d : Fin n → ZMod 2) (g : Pauli n)
    (u : Fin n → ZMod 2) :
    (-1 : ℂ) ^ zDot (zShear k d g) u =
      (-1) ^ zDot g u * (-1) ^ (dotF2 (shearRow k d g.X) u).val :=
  neg_one_pow_zDot_zShearBy (shearLin k d) g u

/-! ## The diagonal gate with a shear as data -/

/-- **The diagonal gate with a shear as data.** The phase polynomial is added as in
`applyDiagSum`; the Lagrangian is pushed by the shear `zShearBy M`. -/
noncomputable def applyDiagShearBy (S : KernelSumState n) (D : DiagPhase n S.m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) : KernelSumState n :=
  { applyDiagSum S D with L := Submodule.map (zShearBy M) S.L }

@[simp] theorem applyDiagShearBy_m (S : KernelSumState n) (D : DiagPhase n S.m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) : (applyDiagShearBy S D M).m = S.m := rfl

@[simp] theorem applyDiagShearBy_h (S : KernelSumState n) (D : DiagPhase n S.m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) : (applyDiagShearBy S D M).h = S.h := rfl

@[simp] theorem applyDiagShearBy_L (S : KernelSumState n) (D : DiagPhase n S.m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (applyDiagShearBy S D M).L = Submodule.map (zShearBy M) S.L := rfl

@[simp] theorem applyDiagShearBy_x₀ (S : KernelSumState n) (D : DiagPhase n S.m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (applyDiagShearBy S D M).x₀ = S.x₀ := rfl

/-- **DEN for the diagonal gate.** A phase times the input's amplitude. -/
theorem amp_applyDiagSum (S : KernelSumState n) (D : DiagPhase n S.m) :
    amp (applyDiagSum S D) = fun w => charOf S.m (D.eval w) * amp S w := by
  funext w
  by_cases hw : ∃ p ∈ S.L, w = S.x₀ + p.X
  · rw [amp_pos (S := applyDiagSum S D) hw, amp_pos (S := S) hw, ampCore_applyDiagSum,
      exp_realPhase_eq_charOf]
  · rw [amp_neg (S := applyDiagSum S D) hw, amp_neg (S := S) hw, mul_zero]

/-- The shear is invisible to the amplitude. -/
theorem amp_applyDiagShearBy (S : KernelSumState n) (D : DiagPhase n S.m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) :
    amp (applyDiagShearBy S D M) = amp (applyDiagSum S D) :=
  amp_map_zShearBy (S.Q + MvPolynomial.rename (Fin.castAdd S.h) D) S.c M S.L S.x₀

/-- The shear preserves dimension. -/
theorem finrank_map_zShearBy (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (L : Submodule (ZMod 2) (Pauli n)) :
    finrank (ZMod 2) (Submodule.map (zShearBy M) L) = finrank (ZMod 2) L :=
  LinearEquiv.finrank_map_eq (zShearByEquiv M) L

/-- **W for a shear** whose pairing is symmetric on the shadow. -/
theorem isCarrier_applyDiagShearBy_of_symm_on {S : KernelSumState n} (hS : IsCarrier S)
    (D : DiagPhase n S.m) {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    (hM : IsSymmPairingOn M (Submodule.map xProj S.L)) : IsCarrier (applyDiagShearBy S D M) := by
  have hst : IsStabilizer (Submodule.map (zShearBy M) S.L) :=
    isStabilizer_map_zShearBy_of_symm_on hM (fun p hp => Submodule.mem_map_of_mem hp) hS.2.1
  refine ⟨hS.1, hst, orthogonal_le_of_lagrangian hst ?_, ?_⟩
  · change finrank (ZMod 2) (Submodule.map (zShearBy M) S.L) = n
    rw [finrank_map_zShearBy]
    exact finrank_eq_of_isCarrier hS
  rw [amp_applyDiagShearBy, amp_applyDiagSum]
  intro h0
  apply hS.2.2.2
  funext w
  have hw := congrFun h0 w
  simp only [Pi.zero_apply] at hw ⊢
  exact (mul_eq_zero.mp hw).resolve_left (charOf_ne_zero _ _)

/-- **W for a shear** with a symmetric pairing. -/
theorem isCarrier_applyDiagShearBy {S : KernelSumState n} (hS : IsCarrier S)
    (D : DiagPhase n S.m) {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    (hM : IsSymmPairing M) : IsCarrier (applyDiagShearBy S D M) :=
  isCarrier_applyDiagShearBy_of_symm_on hS D (hM.on _)

/-! ## The shift datum -/

/-- **The shift datum for a shear.** Along every `v` of the subspace, the exponent's shift is a
constant plus the top-bit pairing of `M v` with the word. -/
def DiagShiftDatumBy {m : ℕ} (D : DiagPhase n m) (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  ∀ v ∈ V, ∃ c : ZMod (2 ^ m), ∀ w : Fin n → ZMod 2,
    D.eval (w + v) - D.eval w =
      c + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((dotF2 (M v) w).val : ℕ) : ZMod (2 ^ m))

theorem DiagShiftDatumBy.mono {m : ℕ} {D : DiagPhase n m}
    {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)} {V V' : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hV : V ≤ V') (h : DiagShiftDatumBy D M V') : DiagShiftDatumBy D M V :=
  fun v hv => h v (hV hv)

/-- For the shear by a matrix, the frame's datum is the Hierarchy layer's datum of the exponent's
evaluation, definitionally. -/
theorem diagShiftDatumBy_mulVecLin_iff {m : ℕ} (D : DiagPhase n m)
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    DiagShiftDatumBy D (Matrix.mulVecLin A) V ↔ IsShiftDatum (DiagPhase.eval D) A V :=
  Iff.rfl

/-- **The datum is additive**: exponents add, shears add. -/
theorem DiagShiftDatumBy.add {m : ℕ} {D D' : DiagPhase n m}
    {M M' : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)} {V : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (h : DiagShiftDatumBy D M V) (h' : DiagShiftDatumBy D' M' V) :
    DiagShiftDatumBy (D + D') (M + M') V := by
  intro v hv
  obtain ⟨c, hc⟩ := h v hv
  obtain ⟨c', hc'⟩ := h' v hv
  refine ⟨c + c', fun w => ?_⟩
  rw [eval_add, eval_add, LinearMap.add_apply, dotF2_add_left, two_pow_pred_mul_val_add]
  linear_combination hc w + hc' w

open Matrix in
/-- **A datum makes the pairing symmetric** on its subspace (precision at least one): through the
matrix of the shear and the Hierarchy layer's `symm_on_of_isShiftDatum`. -/
theorem isSymmPairingOn_of_diagShiftDatumBy {m : ℕ} (hm : 1 ≤ m) {D : DiagPhase n m}
    {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)} {V : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hdat : DiagShiftDatumBy D M V) : IsSymmPairingOn M V := by
  have hM : M = Matrix.mulVecLin (LinearMap.toMatrix' M) :=
    LinearMap.ext (fun v => (LinearMap.toMatrix'_mulVec M v).symm)
  rw [hM] at hdat ⊢
  intro x hx y hy
  have h := symm_on_of_isShiftDatum hm ((diagShiftDatumBy_mulVecLin_iff D _ V).mp hdat) x hx y hy
  change (LinearMap.toMatrix' M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (LinearMap.toMatrix' M *ᵥ y)
  rw [h, dotProduct_comm]

/-- **Uniqueness**: two data at `⊤` are the same shear (precision at least one). -/
theorem eq_of_diagShiftDatumBy_top {m : ℕ} (hm : 1 ≤ m) {D : DiagPhase n m}
    {M M' : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)} (h : DiagShiftDatumBy D M ⊤)
    (h' : DiagShiftDatumBy D M' ⊤) : M = M' := by
  have hM : M = Matrix.mulVecLin (LinearMap.toMatrix' M) :=
    LinearMap.ext (fun v => (LinearMap.toMatrix'_mulVec M v).symm)
  have hM' : M' = Matrix.mulVecLin (LinearMap.toMatrix' M') :=
    LinearMap.ext (fun v => (LinearMap.toMatrix'_mulVec M' v).symm)
  rw [hM] at h
  rw [hM'] at h'
  exact LinearMap.toMatrix'.injective (eq_of_isShiftDatum_top hm
    ((diagShiftDatumBy_mulVecLin_iff D _ ⊤).mp h) ((diagShiftDatumBy_mulVecLin_iff D _ ⊤).mp h'))

/-! ## The intertwining and FL from the datum -/

/-- **The intertwining for a shear.** If the exponent shifts along `g.X` by a constant plus the
top-bit pairing with `M g.X`, the sheared `g` acts on the phased amplitude as `g` acts on the
amplitude, up to the scalar `i^{yWeight g'}·i^{−yWeight g}·(−1)^{⟨M x, x⟩}·charOf c`. -/
theorem pauliAct_zShearBy_of_shift {m : ℕ} (hm : 1 ≤ m) (D : DiagPhase n m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ)
    (c : ZMod (2 ^ m))
    (hD : ∀ w : Fin n → ZMod 2, D.eval (w + g.X) - D.eval w =
      c + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((dotF2 (M g.X) w).val : ℕ) : ZMod (2 ^ m))) :
    pauliAct (zShearBy M g) (fun w => charOf m (D.eval w) * f w) =
      fun w => (Complex.I ^ yWeight (zShearBy M g) * (Complex.I ^ yWeight g)⁻¹ *
        (-1) ^ (dotF2 (M g.X) g.X).val * charOf m c) *
          (charOf m (D.eval w) * pauliAct g f w) := by
  funext w
  simp only [pauliAct, zShearBy_X]
  have hchar : charOf m (D.eval (w + g.X)) =
      charOf m c * (-1) ^ (dotF2 (M g.X) w).val * charOf m (D.eval w) := by
    have h := hD w
    rw [sub_eq_iff_eq_add] at h
    rw [h, charOf_add, charOf_add, charOf_two_pow_mul hm]
  rw [hchar, neg_one_pow_zDot_zShearBy, dotF2_add_right, neg_one_pow_val_add]
  have hI : (Complex.I ^ yWeight g)⁻¹ * Complex.I ^ yWeight g = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero)
  have hsq : ((-1 : ℂ) ^ (dotF2 (M g.X) w).val) * (-1) ^ (dotF2 (M g.X) w).val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  linear_combination (Complex.I ^ yWeight (zShearBy M g) * (-1) ^ zDot g (w + g.X) *
      (-1) ^ (dotF2 (M g.X) g.X).val * charOf m c * charOf m (D.eval w) * f (w + g.X)) * hsq -
    (Complex.I ^ yWeight (zShearBy M g) * (-1) ^ zDot g (w + g.X) *
      (-1) ^ (dotF2 (M g.X) g.X).val * charOf m c * charOf m (D.eval w) * f (w + g.X)) * hI

/-- **FL from the datum alone.** Under the shift datum on the shadow, floors go to floors: the
datum gives the symmetry W needs and the scalar FL needs. -/
theorem isFloor_applyDiagShearBy {S : KernelSumState n} (hF : IsFloor S) {D : DiagPhase n S.m}
    {M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)}
    (hdat : DiagShiftDatumBy D M (Submodule.map xProj S.L)) :
    IsFloor (applyDiagShearBy S D M) := by
  refine isFloor_of_scalar (isCarrier_applyDiagShearBy_of_symm_on hF.1 D
    (isSymmPairingOn_of_diagShiftDatumBy hF.1.1 hdat)) ?_
  intro g' hg'
  rw [applyDiagShearBy_L] at hg'
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hg'
  obtain ⟨s, hs⟩ := hF.2 g hg
  obtain ⟨c, hc⟩ := hdat g.X (Submodule.mem_map_of_mem hg)
  rw [amp_applyDiagShearBy, amp_applyDiagSum]
  refine ⟨(Complex.I ^ yWeight (zShearBy M g) * (Complex.I ^ yWeight g)⁻¹ *
    (-1) ^ (dotF2 (M g.X) g.X).val * charOf S.m c) * (-1) ^ s.val, ?_⟩
  rw [pauliAct_zShearBy_of_shift hF.1.1 D M g (amp S) c hc, hs]
  funext w
  beta_reduce
  ring

/-! ## The scalar in closed form -/

/-- The number of bits where `M x` and `x` both carry `1`. -/
def shearCount (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (x : Fin n → ZMod 2) : ℕ :=
  ∑ i, (M x i).val * (x i).val

/-- The number of bits where `z`, `M x` and `x` all carry `1`. -/
def shearTriple (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (g : Pauli n) : ℕ :=
  ∑ i, (g.Z i).val * ((M g.X i).val * (g.X i).val)

/-- One bit of the `yWeight` computation, mod `4`. -/
theorem bit_val_add_mul_cast (a b c : ZMod 2) :
    (((a + b).val * c.val : ℕ) : ZMod 4) =
      ((a.val * c.val : ℕ) : ZMod 4) + ((b.val * c.val : ℕ) : ZMod 4) -
        2 * ((a.val * (b.val * c.val) : ℕ) : ZMod 4) := by
  revert a b c
  decide

/-- The `yWeight` of the sheared Pauli, mod `4`: the input's, plus the count of bits where `M x`
and `x` both carry `1`, minus twice the count where `z` does too. -/
theorem yWeight_zShearBy_cast (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (g : Pauli n) :
    ((yWeight (zShearBy M g) : ℕ) : ZMod 4) =
      ((yWeight g : ℕ) : ZMod 4) + ((shearCount M g.X : ℕ) : ZMod 4) -
        2 * ((shearTriple M g : ℕ) : ZMod 4) := by
  unfold yWeight zDot shearCount shearTriple
  rw [zShearBy_Z, zShearBy_X]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply]
  have h := bit_val_add_mul_cast (g.Z i) (M g.X i) (g.X i)
  push_cast at h
  exact h

/-- **The closed scalar**: the intertwining's scalar is `(−i)^A · (−1)^B · charOf m c`, with `A`
the count of bits where `M x` and `x` both carry `1` and `B` the count where `z` does too. -/
theorem shearScalar_eq {m : ℕ} (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (g : Pauli n)
    (c : ZMod (2 ^ m)) :
    Complex.I ^ yWeight (zShearBy M g) * (Complex.I ^ yWeight g)⁻¹ *
        (-1) ^ (dotF2 (M g.X) g.X).val * charOf m c =
      (-Complex.I) ^ shearCount M g.X * (-1) ^ shearTriple M g * charOf m c := by
  have hA : ((-1 : ℂ) ^ (dotF2 (M g.X) g.X).val) = (-1) ^ shearCount M g.X := by
    apply neg_one_pow_eq_of_cast_eq
    rw [ZMod.natCast_zmod_val]
    unfold shearCount dotF2
    push_cast
    exact Finset.sum_congr rfl (fun i _ => by rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have hY : Complex.I ^ yWeight (zShearBy M g) =
      Complex.I ^ yWeight g * Complex.I ^ shearCount M g.X * (-1) ^ shearTriple M g := by
    rw [neg_one_pow_eq_I_pow, ← pow_add, ← pow_add]
    apply I_pow_eq_of_natCast_eq
    push_cast
    rw [yWeight_zShearBy_cast]
    have h4 : (4 : ZMod 4) = 0 := by decide
    linear_combination (-((shearTriple M g : ℕ) : ZMod 4)) * h4
  have hI : (Complex.I ^ yWeight g)⁻¹ * Complex.I ^ yWeight g = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero)
  have hneg : (-Complex.I) ^ shearCount M g.X =
      (-1) ^ shearCount M g.X * Complex.I ^ shearCount M g.X := by
    rw [neg_eq_neg_one_mul, mul_pow]
  rw [hA, hY, hneg]
  linear_combination (Complex.I ^ shearCount M g.X * (-1) ^ shearTriple M g *
    (-1) ^ shearCount M g.X * charOf m c) * hI

/-- **The intertwining with the closed scalar.** -/
theorem pauliAct_zShearBy_of_shift_closed {m : ℕ} (hm : 1 ≤ m) (D : DiagPhase n m)
    (M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ)
    (c : ZMod (2 ^ m))
    (hD : ∀ w : Fin n → ZMod 2, D.eval (w + g.X) - D.eval w =
      c + (2 : ZMod (2 ^ m)) ^ (m - 1) * (((dotF2 (M g.X) w).val : ℕ) : ZMod (2 ^ m))) :
    pauliAct (zShearBy M g) (fun w => charOf m (D.eval w) * f w) =
      fun w => ((-Complex.I) ^ shearCount M g.X * (-1) ^ shearTriple M g * charOf m c) *
        (charOf m (D.eval w) * pauliAct g f w) := by
  rw [pauliAct_zShearBy_of_shift hm D M g f c hD, shearScalar_eq]

/-! ## The class rule: the shear by the polar matrix -/

/-- **The class rule.** A diagonal exponent acts with the shear by the polar matrix of its Boolean
normal form: the phase is `D`, the Lagrangian moves by `zShearBy (polarMatrix (boolReduce D))`. -/
noncomputable def applyDiagPolar (S : KernelSumState n) (D : DiagPhase n S.m) :
    KernelSumState n :=
  applyDiagShearBy S D (Matrix.mulVecLin (polarMatrix (boolReduce D)))

@[simp] theorem applyDiagPolar_m (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagPolar S D).m = S.m := rfl

@[simp] theorem applyDiagPolar_h (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagPolar S D).h = S.h := rfl

@[simp] theorem applyDiagPolar_L (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagPolar S D).L =
      Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce D)))) S.L := rfl

@[simp] theorem applyDiagPolar_x₀ (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagPolar S D).x₀ = S.x₀ := rfl

/-- **DEN for the class**: a phase times the input, for every exponent. -/
theorem amp_applyDiagPolar (S : KernelSumState n) (D : DiagPhase n S.m) :
    amp (applyDiagPolar S D) = fun w => charOf S.m (D.eval w) * amp S w := by
  rw [applyDiagPolar, amp_applyDiagShearBy, amp_applyDiagSum]

/-- **W for the class**, for every exponent: the polar matrix is symmetric. -/
theorem isCarrier_applyDiagPolar {S : KernelSumState n} (hS : IsCarrier S) (D : DiagPhase n S.m) :
    IsCarrier (applyDiagPolar S D) :=
  isCarrier_applyDiagShearBy hS D (isSymmPairing_mulVecLin (polarMatrix_isSymm _))

/-- Every level-two exponent carries the datum of the shear by its polar matrix, on every
subspace. -/
theorem diagShiftDatumBy_polarMatrix {m : ℕ} (D : DiagPhase n m) (hD : levelExt D ≤ 2)
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    DiagShiftDatumBy D (Matrix.mulVecLin (polarMatrix (boolReduce D))) V :=
  (diagShiftDatumBy_mulVecLin_iff D _ V).mpr
    (isShiftDatum_polarMatrix_boolReduce_of_levelExt_le_two D hD V)

/-- **FL for the class**: every diagonal gate of level at most two keeps the floor. -/
theorem isFloor_applyDiagPolar {S : KernelSumState n} (hF : IsFloor S) {D : DiagPhase n S.m}
    (hD : levelExt D ≤ 2) : IsFloor (applyDiagPolar S D) :=
  isFloor_applyDiagShearBy hF (diagShiftDatumBy_polarMatrix D hD _)

/-! ## The word form: the polar matrix's shear is a fold of one-bit shears -/

/-- The upper support of a matrix: the pairs `(k, j)` with `k ≤ j` and a `1` entry. -/
def upperSupport (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≤ p.2 ∧ A p.1 p.2 = 1)

/-- The matrix of one letter: `E_kk` on the diagonal, `E_kj + E_jk` off it. -/
def pairMatrix (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  if p.1 = p.2 then Matrix.single p.1 p.1 1 else Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1

theorem pairMatrix_apply_of_ne (p : Fin n × Fin n) {a b : Fin n} (h1 : p ≠ (a, b))
    (h2 : p ≠ (b, a)) : pairMatrix p a b = 0 := by
  obtain ⟨k, j⟩ := p
  have h1' : ¬ (k = a ∧ j = b) := fun h => h1 (Prod.ext h.1 h.2)
  have h2' : ¬ (k = b ∧ j = a) := fun h => h2 (Prod.ext h.1 h.2)
  unfold pairMatrix
  dsimp only
  split_ifs with hkj
  · subst hkj
    rw [Matrix.single_apply, if_neg h1']
  · rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1',
      if_neg (fun h => h2' ⟨h.2, h.1⟩), add_zero]

theorem pairMatrix_apply_self (a b : Fin n) : pairMatrix (a, b) a b = 1 := by
  unfold pairMatrix
  dsimp only
  split_ifs with hab
  · rw [Matrix.single_apply, if_pos ⟨rfl, hab⟩]
  · rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
      if_neg (fun h => hab h.2), add_zero]

theorem pairMatrix_apply_swap {a b : Fin n} (hab : a ≠ b) : pairMatrix (b, a) a b = 1 := by
  unfold pairMatrix
  dsimp only
  rw [if_neg (Ne.symm hab), Matrix.add_apply, Matrix.single_apply, Matrix.single_apply,
    if_neg (fun h => hab h.2), if_pos ⟨rfl, rfl⟩, zero_add]

/-- A symmetric matrix over `𝔽₂` is the sum of the letters of its upper support. -/
theorem eq_sum_pairMatrix {A : Matrix (Fin n) (Fin n) (ZMod 2)} (hA : A.IsSymm) :
    A = ∑ p ∈ upperSupport A, pairMatrix p := by
  ext a b
  rw [Matrix.sum_apply]
  rcases le_or_gt a b with hab | hba
  · rcases zmod_two_eq_zero_or_one (A a b) with h0 | h1
    · rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      apply pairMatrix_apply_of_ne
      · rintro rfl
        exact absurd hp'.2 (by rw [h0]; decide)
      · rintro rfl
        have : a = b := le_antisymm hab hp'.1
        subst this
        exact absurd hp'.2 (by rw [h0]; decide)
    · rw [h1]
      symm
      rw [Finset.sum_eq_single (a, b)]
      · exact pairMatrix_apply_self a b
      · intro p hp hne
        apply pairMatrix_apply_of_ne p hne
        rintro rfl
        have : a = b := le_antisymm hab (Finset.mem_filter.mp hp).2.1
        subst this
        exact hne rfl
      · intro hnot
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, h1⟩) hnot
  · rcases zmod_two_eq_zero_or_one (A b a) with h0 | h1
    · rw [hA.apply b a, h0]
      symm
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      apply pairMatrix_apply_of_ne
      · rintro rfl
        exact absurd hp'.1 (not_le.mpr hba)
      · rintro rfl
        exact absurd hp'.2 (by rw [h0]; decide)
    · rw [hA.apply b a, h1]
      symm
      rw [Finset.sum_eq_single (b, a)]
      · exact pairMatrix_apply_swap (ne_of_gt hba)
      · intro p hp hne
        apply pairMatrix_apply_of_ne p _ hne
        rintro rfl
        exact absurd (Finset.mem_filter.mp hp).2.1 (not_le.mpr hba)
      · intro hnot
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt hba, h1⟩) hnot

open Matrix in
/-- The map of `E_ii` is the row of the shear `(i, e_i)`. -/
theorem mulVecLin_single_self (i : Fin n) :
    Matrix.mulVecLin (Matrix.single i i (1 : ZMod 2)) = shearLin i (Pi.single i 1) := by
  apply LinearMap.ext
  intro v
  change Matrix.single i i (1 : ZMod 2) *ᵥ v = shearRow i (Pi.single i 1) v
  rw [Matrix.single_mulVec, shearRow_single_self, one_mul]
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · rw [Function.update_of_ne hj, Pi.zero_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]

open Matrix in
/-- The map of `E_ij + E_ji` is the row of the shear `(i, e_j)` (`i ≠ j`). -/
theorem mulVecLin_single_pair {i j : Fin n} (hij : i ≠ j) :
    Matrix.mulVecLin (Matrix.single i j (1 : ZMod 2) + Matrix.single j i 1) =
      shearLin i (Pi.single j 1) := by
  apply LinearMap.ext
  intro v
  change (Matrix.single i j (1 : ZMod 2) + Matrix.single j i 1) *ᵥ v = shearRow i (Pi.single j 1) v
  rw [Matrix.add_mulVec, Matrix.single_mulVec, Matrix.single_mulVec, shearRow_single_ne hij,
    one_mul, one_mul]
  funext l
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases hli : l = i
  · subst hli
    rw [Function.update_self, Function.update_of_ne hij, Pi.zero_apply, Pi.single_eq_of_ne hij,
      Pi.single_eq_same, mul_zero, mul_one, zero_add, add_zero]
  · by_cases hlj : l = j
    · subst hlj
      rw [Function.update_of_ne hli, Function.update_self, Pi.zero_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne hli, mul_one, mul_zero, zero_add, add_zero]
    · rw [Function.update_of_ne hli, Function.update_of_ne hlj, Pi.zero_apply,
        Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj, mul_zero, mul_zero, add_zero]

/-- The map of a letter is the one-bit shear of its pair. -/
theorem mulVecLin_pairMatrix (p : Fin n × Fin n) :
    Matrix.mulVecLin (pairMatrix p) = shearLin p.1 (Pi.single p.2 1) := by
  unfold pairMatrix
  split_ifs with h
  · rw [← h]
    exact mulVecLin_single_self p.1
  · exact mulVecLin_single_pair h

/-- **The row decomposition**: a symmetric matrix's map is the sum of the one-bit rows of its
upper support — the letters' shears. -/
theorem mulVecLin_eq_sum_shearLin {A : Matrix (Fin n) (Fin n) (ZMod 2)} (hA : A.IsSymm) :
    Matrix.mulVecLin A = ∑ p ∈ upperSupport A, shearLin p.1 (Pi.single p.2 1) := by
  have h : Matrix.mulVecLin A = Matrix.mulVecLin (∑ p ∈ upperSupport A, pairMatrix p) := by
    rw [← eq_sum_pairMatrix hA]
  rw [h]
  change Matrix.mulVecBilin (ZMod 2) (ZMod 2) (∑ p ∈ upperSupport A, pairMatrix p) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun p _ => mulVecLin_pairMatrix p)

/-- **The word form of the class rule.** The Lagrangian of `applyDiagPolar S D` is the fold of the
one-bit shears of the polar matrix's upper support — the `S` and `CZ` letters' shears — over
`S.L`; the amplitude is `amp_applyDiagPolar`, and the other fields are `applyDiagSum`'s. -/
theorem applyDiagPolar_L_eq_foldl (S : KernelSumState n) (D : DiagPhase n S.m) :
    (applyDiagPolar S D).L =
      (upperSupport (polarMatrix (boolReduce D))).toList.foldl
        (fun L p => Submodule.map (zShear p.1 (Pi.single p.2 1)) L) S.L := by
  rw [applyDiagPolar_L, mulVecLin_eq_sum_shearLin (polarMatrix_isSymm _), map_zShearBy_finset_sum]
  rfl

/-! ## The shear at a bit, as an instance -/

/-- **The diagonal gate with the shear at a bit as data**: the shear by the row `shearLin k d`. -/
noncomputable def applyDiagShear (S : KernelSumState n) (D : DiagPhase n S.m) (k : Fin n)
    (d : Fin n → ZMod 2) : KernelSumState n :=
  applyDiagShearBy S D (shearLin k d)

theorem applyDiagShear_eq_applyDiagShearBy (S : KernelSumState n) (D : DiagPhase n S.m)
    (k : Fin n) (d : Fin n → ZMod 2) :
    applyDiagShear S D k d = applyDiagShearBy S D (shearLin k d) :=
  rfl

@[simp] theorem applyDiagShear_m (S : KernelSumState n) (D : DiagPhase n S.m) (k : Fin n)
    (d : Fin n → ZMod 2) : (applyDiagShear S D k d).m = S.m := rfl

@[simp] theorem applyDiagShear_h (S : KernelSumState n) (D : DiagPhase n S.m) (k : Fin n)
    (d : Fin n → ZMod 2) : (applyDiagShear S D k d).h = S.h := rfl

@[simp] theorem applyDiagShear_L (S : KernelSumState n) (D : DiagPhase n S.m) (k : Fin n)
    (d : Fin n → ZMod 2) : (applyDiagShear S D k d).L = Submodule.map (zShear k d) S.L := rfl

@[simp] theorem applyDiagShear_x₀ (S : KernelSumState n) (D : DiagPhase n S.m) (k : Fin n)
    (d : Fin n → ZMod 2) : (applyDiagShear S D k d).x₀ = S.x₀ := rfl

/-- The shear is invisible to the amplitude. -/
theorem amp_applyDiagShear (S : KernelSumState n) (D : DiagPhase n S.m) (k : Fin n)
    (d : Fin n → ZMod 2) : amp (applyDiagShear S D k d) = amp (applyDiagSum S D) :=
  amp_applyDiagShearBy S D (shearLin k d)

/-- The shear preserves dimension. -/
theorem finrank_map_zShear (k : Fin n) (d : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Pauli n)) :
    finrank (ZMod 2) (Submodule.map (zShear k d) L) = finrank (ZMod 2) L :=
  LinearEquiv.finrank_map_eq (zShearEquiv k d) L

/-- **W for the diagonal shear.** -/
theorem isCarrier_applyDiagShear {S : KernelSumState n} (hS : IsCarrier S) (D : DiagPhase n S.m)
    (k : Fin n) (d : Fin n → ZMod 2) : IsCarrier (applyDiagShear S D k d) :=
  isCarrier_applyDiagShearBy hS D (isSymmPairing_shearLin k d)

/-- **The shift datum** for the shear at a bit: the datum of its row. -/
def DiagShiftDatum {m : ℕ} (D : DiagPhase n m) (k : Fin n) (d : Fin n → ZMod 2)
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : Prop :=
  DiagShiftDatumBy D (shearLin k d) V

theorem diagShiftDatum_eq_diagShiftDatumBy {m : ℕ} (D : DiagPhase n m) (k : Fin n)
    (d : Fin n → ZMod 2) (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    DiagShiftDatum D k d V = DiagShiftDatumBy D (shearLin k d) V :=
  rfl

/-- **The intertwining for the shear at a bit.** -/
theorem pauliAct_zShear_of_shift {m : ℕ} (hm : 1 ≤ m) (D : DiagPhase n m) (k : Fin n)
    (d : Fin n → ZMod 2) (g : Pauli n) (f : (Fin n → ZMod 2) → ℂ) (c : ZMod (2 ^ m))
    (hD : ∀ w : Fin n → ZMod 2, D.eval (w + g.X) - D.eval w =
      c + (2 : ZMod (2 ^ m)) ^ (m - 1) *
        (((dotF2 (shearRow k d g.X) w).val : ℕ) : ZMod (2 ^ m))) :
    pauliAct (zShear k d g) (fun w => charOf m (D.eval w) * f w) =
      fun w => (Complex.I ^ yWeight (zShear k d g) * (Complex.I ^ yWeight g)⁻¹ *
        (-1) ^ (dotF2 (shearRow k d g.X) g.X).val * charOf m c) *
          (charOf m (D.eval w) * pauliAct g f w) :=
  pauliAct_zShearBy_of_shift hm D (shearLin k d) g f c hD

/-- **FL for the diagonal shear.** Under the shift datum on the shadow, floors go to floors. -/
theorem isFloor_applyDiagShear {S : KernelSumState n} (hF : IsFloor S) {D : DiagPhase n S.m}
    {k : Fin n} {d : Fin n → ZMod 2} (hdat : DiagShiftDatum D k d (Submodule.map xProj S.L)) :
    IsFloor (applyDiagShear S D k d) :=
  isFloor_applyDiagShearBy hF hdat

/-! ## The two instances: `S` and `CZ` -/

/-- **`S` carries its datum** at precision `≥ 2`, along every word. -/
theorem diagShiftDatum_sGate {m : ℕ} (hm : 2 ≤ m) (i : Fin n)
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : DiagShiftDatum (sGate m i) i (Pi.single i 1) V := by
  intro v _
  refine ⟨(2 : ZMod (2 ^ m)) ^ (m - 2) * ((v i).val : ZMod (2 ^ m)), fun w => ?_⟩
  rw [sGate_eval, sGate_eval, shearLin_apply, shearRow_single_self, dotF2_smul_left,
    dotF2_single_left, Pi.add_apply]
  have h2 : (2 : ZMod (2 ^ m)) ^ (m - 1) = 2 ^ (m - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have h4 : (2 : ZMod (2 ^ m)) ^ (m - 2) * 4 = 0 := by
    rw [show (4 : ZMod (2 ^ m)) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hm]
    exact_mod_cast ZMod.natCast_self (2 ^ m)
  rcases zmod_two_eq_zero_or_one (v i) with hv | hv <;>
    rcases zmod_two_eq_zero_or_one (w i) with hw | hw <;>
    simp only [hv, hw, show ((1 : ZMod 2) + 1) = 0 by decide, add_zero, zero_add, mul_one,
      mul_zero, ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide,
      Nat.cast_zero, Nat.cast_one] <;>
    first | ring1 | linear_combination -h4 - h2

/-- **`CZ` carries its datum** (`i ≠ j`), along every word. -/
theorem diagShiftDatum_czGate {m : ℕ} (hm : 1 ≤ m) {i j : Fin n} (hij : i ≠ j)
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    DiagShiftDatum (czGate m i j) i (Pi.single j 1) V := by
  intro v _
  refine ⟨(2 : ZMod (2 ^ m)) ^ (m - 1) * (((v i).val : ZMod (2 ^ m)) * ((v j).val : ZMod (2 ^ m))),
    fun w => ?_⟩
  rw [czGate_eval, czGate_eval, shearLin_apply, shearRow_single_ne hij, dotF2_add_left,
    dotF2_smul_left, dotF2_smul_left, dotF2_single_left, dotF2_single_left, Pi.add_apply,
    Pi.add_apply]
  have hz : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := two_pow_pred_mul_two
  have _hm := hm
  rcases zmod_two_eq_zero_or_one (v i) with hvi | hvi <;>
    rcases zmod_two_eq_zero_or_one (v j) with hvj | hvj <;>
    rcases zmod_two_eq_zero_or_one (w i) with hwi | hwi <;>
    rcases zmod_two_eq_zero_or_one (w j) with hwj | hwj <;>
    simp only [hvi, hvj, hwi, hwj, show ((1 : ZMod 2) + 1) = 0 by decide, add_zero, zero_add,
      mul_one, mul_zero, ZMod.val_zero,
      show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_zero, Nat.cast_one] <;>
    first | ring1 | linear_combination hz | linear_combination -hz

/-- **The diagonal `i = j` instance `Z_i`** (`czGate m i i`) carries its datum with the **zero**
shear: the index-driven shear `(i, e_i)` is the wrong one there (the Check's control). -/
theorem diagShiftDatum_czGate_self {m : ℕ} (hm : 1 ≤ m) (i : Fin n)
    (V : Submodule (ZMod 2) (Fin n → ZMod 2)) : DiagShiftDatum (czGate m i i) i 0 V := by
  intro v _
  refine ⟨(2 : ZMod (2 ^ m)) ^ (m - 1) * ((v i).val : ZMod (2 ^ m)), fun w => ?_⟩
  rw [czGate_eval, czGate_eval, shearLin_apply, shearRow_zero, Pi.add_apply]
  have hz : (2 : ZMod (2 ^ m)) ^ (m - 1) * 2 = 0 := two_pow_pred_mul_two
  have _hm := hm
  rcases zmod_two_eq_zero_or_one (v i) with hv | hv <;>
    rcases zmod_two_eq_zero_or_one (w i) with hw | hw <;>
    simp only [hv, hw, show ((1 : ZMod 2) + 1) = 0 by decide, add_zero, zero_add, mul_one,
      mul_zero, ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_zero,
      Nat.cast_one, dotF2, Pi.zero_apply, zero_mul, Finset.sum_const_zero] <;>
    first | ring1 | linear_combination -hz

/-- **`S` at bit `i`**: the phase `i^{w_i}` with the shear `(i, e_i)`. -/
noncomputable def applyS (S : KernelSumState n) (i : Fin n) : KernelSumState n :=
  applyDiagShear S (sGate S.m i) i (Pi.single i 1)

/-- **`CZ` at bits `i, j`**: the phase `(−1)^{w_i w_j}` with the shear `(i, e_j)`. -/
noncomputable def applyCZ (S : KernelSumState n) (i j : Fin n) : KernelSumState n :=
  applyDiagShear S (czGate S.m i j) i (Pi.single j 1)

/-- DEN for `S`. -/
theorem amp_applyS (S : KernelSumState n) (i : Fin n) :
    amp (applyS S i) = fun w =>
      charOf S.m ((2 : ZMod (2 ^ S.m)) ^ (S.m - 2) * ((w i).val : ZMod (2 ^ S.m))) * amp S w := by
  unfold applyS
  rw [amp_applyDiagShear, amp_applyDiagSum]
  funext w
  rw [sGate_eval]

/-- DEN for `CZ`. -/
theorem amp_applyCZ (S : KernelSumState n) (i j : Fin n) :
    amp (applyCZ S i j) = fun w =>
      charOf S.m ((2 : ZMod (2 ^ S.m)) ^ (S.m - 1) *
        (((w i).val : ZMod (2 ^ S.m)) * ((w j).val : ZMod (2 ^ S.m)))) * amp S w := by
  unfold applyCZ
  rw [amp_applyDiagShear, amp_applyDiagSum]
  funext w
  rw [czGate_eval]

/-- W for `S`. -/
theorem isCarrier_applyS {S : KernelSumState n} (hS : IsCarrier S) (i : Fin n) :
    IsCarrier (applyS S i) :=
  isCarrier_applyDiagShear hS _ _ _

/-- **FL for `S`** at precision `≥ 2`. -/
theorem isFloor_applyS {S : KernelSumState n} (hF : IsFloor S) (hm : 2 ≤ S.m) (i : Fin n) :
    IsFloor (applyS S i) :=
  isFloor_applyDiagShear hF (diagShiftDatum_sGate hm i _)

/-- W for `CZ`. -/
theorem isCarrier_applyCZ {S : KernelSumState n} (hS : IsCarrier S) (i j : Fin n) :
    IsCarrier (applyCZ S i j) :=
  isCarrier_applyDiagShear hS _ _ _

/-- **FL for `CZ`** (`i ≠ j`). -/
theorem isFloor_applyCZ {S : KernelSumState n} (hF : IsFloor S) {i j : Fin n} (hij : i ≠ j) :
    IsFloor (applyCZ S i j) :=
  isFloor_applyDiagShear hF (diagShiftDatum_czGate hF.1.1 hij _)

/-! ## The instances as cases of the class rule -/

/-- `S` at bit `i` is the class rule on its exponent, at precision at least two. -/
theorem applyS_eq_applyDiagPolar (S : KernelSumState n) (hm : 2 ≤ S.m) (i : Fin n) :
    applyS S i = applyDiagPolar S (sGate S.m i) := by
  unfold applyS applyDiagPolar applyDiagShear
  rw [boolReduce_sGate, polarMatrix_sGate hm, mulVecLin_single_self]

/-- `CZ` at bits `i ≠ j` is the class rule on its exponent, at precision at least one. -/
theorem applyCZ_eq_applyDiagPolar (S : KernelSumState n) (hm : 1 ≤ S.m) {i j : Fin n}
    (hij : i ≠ j) : applyCZ S i j = applyDiagPolar S (czGate S.m i j) := by
  unfold applyCZ applyDiagPolar applyDiagShear
  rw [boolReduce_czGate _ hij, polarMatrix_czGate hm hij, mulVecLin_single_pair hij]

/-- **The polar matrices add on the level-two class.** Both maps carry the datum of the sum
exponent at `⊤` — the left by the class theorem, the right by additivity of the datum — and a
datum at `⊤` is unique at positive precision. -/
theorem mulVecLin_polarMatrix_add {m : ℕ} (hm : 1 ≤ m) {D E : DiagPhase n m}
    (hD : levelExt D ≤ 2) (hE : levelExt E ≤ 2) :
    Matrix.mulVecLin (polarMatrix (boolReduce (D + E)))
      = Matrix.mulVecLin (polarMatrix (boolReduce D)) +
          Matrix.mulVecLin (polarMatrix (boolReduce E)) :=
  eq_of_diagShiftDatumBy_top hm
    (diagShiftDatumBy_polarMatrix (D + E) ((levelExt_add_le D E).trans (max_le hD hE)) ⊤)
    (DiagShiftDatumBy.add (diagShiftDatumBy_polarMatrix D hD ⊤)
      (diagShiftDatumBy_polarMatrix E hE ⊤))

/-- **The class rule composes.** Two diagonal gates of level at most two in a row are the one gate
of the sum exponent: the phases add, and the polar matrices add, so the shears compose
(`map_zShearBy_add`). Nothing is assumed about the two shears — they are read from the exponents. -/
theorem applyDiagPolar_add {S : KernelSumState n} (hm : 1 ≤ S.m) {D E : DiagPhase n S.m}
    (hD : levelExt D ≤ 2) (hE : levelExt E ≤ 2) :
    applyDiagPolar (applyDiagPolar S D) E = applyDiagPolar S (D + E) := by
  have hQ : S.Q + MvPolynomial.rename (Fin.castAdd S.h) D +
      MvPolynomial.rename (Fin.castAdd S.h) E
        = S.Q + MvPolynomial.rename (Fin.castAdd S.h) (D + E) := by
    rw [map_add]
    ring
  have hL : Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce E))))
        (Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce D)))) S.L)
      = Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce (D + E))))) S.L := by
    rw [mulVecLin_polarMatrix_add hm hD hE, map_zShearBy_add]
  change (⟨S.m, S.h, S.Q + MvPolynomial.rename (Fin.castAdd S.h) D +
        MvPolynomial.rename (Fin.castAdd S.h) E, S.c,
      Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce E))))
        (Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce D)))) S.L),
      S.x₀⟩ : KernelSumState n) =
    ⟨S.m, S.h, S.Q + MvPolynomial.rename (Fin.castAdd S.h) (D + E), S.c,
      Submodule.map (zShearBy (Matrix.mulVecLin (polarMatrix (boolReduce (D + E))))) S.L, S.x₀⟩
  rw [hQ, hL]

/-! ## CNOT: the symplectic lift, DEN, W, FL -/

/-- The pairing is symmetric. -/
theorem dotF2_swap (u v : Fin n → ZMod 2) : dotF2 u v = dotF2 v u := by
  unfold dotF2
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The two CNOT bit maps are adjoint for the pairing (`i ≠ j`). -/
theorem dotF2_cnotBitMap {i j : Fin n} (hij : i ≠ j) (z x : Fin n → ZMod 2) :
    dotF2 (cnotBitMap j i z) (cnotBitMap i j x) = dotF2 z x := by
  rw [cnotBitMap_eq_add_smul_single, cnotBitMap_eq_add_smul_single]
  simp only [dotF2_add_left, dotF2_add_right, dotF2_smul_left, dotF2_smul_right, dotF2_single,
    dotF2_single_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hij.symm]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination (x i * z j) * h2

/-- **The repaired lift is symplectic** (`i ≠ j`). -/
theorem omega_cnotPauli {i j : Fin n} (hij : i ≠ j) (p q : Pauli n) :
    omega (cnotPauli i j p) (cnotPauli i j q) = omega p q := by
  rw [omega_eq_dotF2, omega_eq_dotF2, cnotPauli_X, cnotPauli_Z, cnotPauli_X, cnotPauli_Z,
    dotF2_cnotBitMap hij, dotF2_swap (cnotBitMap i j p.X) (cnotBitMap j i q.Z),
    dotF2_cnotBitMap hij, dotF2_swap q.Z p.X]

/-- The lift carries isotropic subspaces to isotropic subspaces (`i ≠ j`). -/
theorem isStabilizer_map_cnotPauli {i j : Fin n} (hij : i ≠ j) {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) : IsStabilizer (Submodule.map (cnotPauli i j) L) := by
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := Submodule.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := Submodule.mem_map.mp hq
  rw [omega_cnotPauli hij]
  exact hS p' hp' q' hq'

/-- **DEN for CNOT** (`i ≠ j`): the amplitude at the CNOT-permuted word. -/
theorem amp_applyCnotSum {i j : Fin n} (hij : i ≠ j) (S : KernelSumState n) :
    amp (applyCnotSum i j S) = fun w => amp S (cnotBitMap i j w) := by
  funext w
  by_cases hw : ∃ p ∈ S.L, cnotBitMap i j w = S.x₀ + p.X
  · rw [amp_pos (S := applyCnotSum i j S) ((cnotSum_support i j hij S w).mpr hw),
      amp_pos (S := S) hw]
    exact ampCore_affinePushforward i j S.Q S.c w
  · rw [amp_neg (S := applyCnotSum i j S) (fun hc => hw ((cnotSum_support i j hij S w).mp hc)),
      amp_neg (S := S) hw]

/-- Off the control and the target the two bit maps change nothing. -/
theorem cnot_sum_erase_erase {i j : Fin n} (hij : i ≠ j) (z x : Fin n → ZMod 2) :
    ∑ l ∈ (Finset.univ.erase i).erase j, ((cnotBitMap j i z) l).val * ((cnotBitMap i j x) l).val =
      ∑ l ∈ (Finset.univ.erase i).erase j, (z l).val * (x l).val := by
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
  have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
  have _ := hij
  simp only [cnotBitMap, Function.update_of_ne hli, Function.update_of_ne hlj]

/-- A sum over the bits split at two of them. -/
theorem sum_split_two {i j : Fin n} (hij : i ≠ j) (F : Fin n → ℕ) :
    ∑ l, F l = F i + F j + ∑ l ∈ (Finset.univ.erase i).erase j, F l := by
  rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ i),
    ← Finset.add_sum_erase (Finset.univ.erase i) F
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]

/-- The `yWeight` of the lifted `g`, mod `4`: the input's plus twice the sign exponent of D6. -/
theorem yWeight_cnotPauli_cast {i j : Fin n} (hij : i ≠ j) (g : Pauli n) :
    ((yWeight (cnotPauli i j g) : ℕ) : ZMod 4) =
      2 * (((g.X i * g.Z j * (1 + g.X j + g.Z i)).val : ℕ) : ZMod 4) +
        ((yWeight g : ℕ) : ZMod 4) := by
  unfold yWeight zDot
  rw [cnotPauli_X, cnotPauli_Z, sum_split_two hij,
    sum_split_two hij (fun l => (g.Z l).val * (g.X l).val), cnot_sum_erase_erase hij]
  simp only [cnotBitMap, Function.update_self, Function.update_of_ne hij,
    Function.update_of_ne hij.symm]
  push_cast
  have h4 : (4 : ZMod 4) = 0 := by decide
  rcases zmod_two_eq_zero_or_one (g.X i) with hxi | hxi <;>
    rcases zmod_two_eq_zero_or_one (g.X j) with hxj | hxj <;>
    rcases zmod_two_eq_zero_or_one (g.Z i) with hzi | hzi <;>
    rcases zmod_two_eq_zero_or_one (g.Z j) with hzj | hzj <;>
    simp only [hxi, hxj, hzi, hzj, show ((1 : ZMod 2) + 1) = 0 by decide, add_zero, zero_add,
      mul_one, mul_zero, ZMod.val_zero, show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_zero,
      Nat.cast_one] <;>
    first | ring1 | linear_combination h4 | linear_combination -h4

/-- The parity of `zDot` under the lift: read the input at the CNOT-permuted word. -/
theorem zDot_cnotPauli_cast {i j : Fin n} (hij : i ≠ j) (g : Pauli n) (u : Fin n → ZMod 2) :
    ((zDot (cnotPauli i j g) u : ℕ) : ZMod 2) = ((zDot g (cnotBitMap i j u) : ℕ) : ZMod 2) := by
  rw [zDot_cast_two, zDot_cast_two, cnotPauli_Z]
  change dotF2 (cnotBitMap j i g.Z) u = dotF2 g.Z (cnotBitMap i j u)
  rw [← dotF2_cnotBitMap hij g.Z (cnotBitMap i j u), cnotBitMap_involutive i j hij]

/-- **The CNOT intertwining** (D6): the lifted `g` acts on a pulled-back amplitude as `g` acts on
the amplitude, pulled back, up to the sign `(−1)^{x_i z_j (1 + x_j + z_i)}`. -/
theorem pauliAct_cnotPauli {i j : Fin n} (hij : i ≠ j) (g : Pauli n)
    (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct (cnotPauli i j g) (fun w => f (cnotBitMap i j w)) =
      fun w => (-1 : ℂ) ^ ((g.X i * g.Z j * (1 + g.X j + g.Z i)).val) *
        pauliAct g f (cnotBitMap i j w) := by
  funext w
  rw [pauliAct_apply, pauliAct_apply, cnotPauli_X, neg_one_pow_eq_I_pow, ← mul_assoc, ← pow_add]
  have harg : cnotBitMap i j (w + cnotBitMap i j g.X) = cnotBitMap i j w + g.X := by
    rw [cnotBitMap_add, cnotBitMap_involutive i j hij]
  change Complex.I ^ (yWeight (cnotPauli i j g) +
      2 * zDot (cnotPauli i j g) (w + cnotBitMap i j g.X)) *
      f (cnotBitMap i j (w + cnotBitMap i j g.X)) = _
  rw [harg]
  congr 1
  apply I_pow_eq_of_natCast_eq
  push_cast
  rw [← harg, two_mul_natCast_four (zDot (cnotPauli i j g) _),
    two_mul_natCast_four (zDot g (cnotBitMap i j (w + cnotBitMap i j g.X))),
    zDot_cnotPauli_cast hij, yWeight_cnotPauli_cast hij]
  ring

/-- **W for CNOT** (`i ≠ j`). -/
theorem isCarrier_applyCnotSum {i j : Fin n} (hij : i ≠ j) {S : KernelSumState n}
    (hS : IsCarrier S) : IsCarrier (applyCnotSum i j S) := by
  refine ⟨hS.1, isStabilizer_map_cnotPauli hij hS.2.1,
    orthogonal_le_of_lagrangian (isStabilizer_map_cnotPauli hij hS.2.1) ?_, ?_⟩
  · change finrank (ZMod 2) (Submodule.map (cnotPauli i j) S.L) = n
    rw [finrank_map_cnotPauli i j hij]
    exact finrank_eq_of_isCarrier hS
  · rw [amp_applyCnotSum hij]
    intro h0
    apply hS.2.2.2
    funext w
    have hw := congrFun h0 (cnotBitMap i j w)
    simp only [Pi.zero_apply] at hw ⊢
    rwa [cnotBitMap_involutive i j hij] at hw

/-- **FL for CNOT** (`i ≠ j`). -/
theorem isFloor_applyCnotSum {i j : Fin n} (hij : i ≠ j) {S : KernelSumState n}
    (hF : IsFloor S) : IsFloor (applyCnotSum i j S) := by
  refine isFloor_of_scalar (isCarrier_applyCnotSum hij hF.1) ?_
  intro g' hg'
  change g' ∈ Submodule.map (cnotPauli i j) S.L at hg'
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hg'
  obtain ⟨s, hs⟩ := hF.2 g hg
  rw [amp_applyCnotSum hij]
  refine ⟨(-1 : ℂ) ^ ((g.X i * g.Z j * (1 + g.X j + g.Z i)).val) * (-1) ^ s.val, ?_⟩
  rw [pauliAct_cnotPauli hij, hs]
  funext w
  beta_reduce
  ring

end FTQCLib.Frame.Walkthrough

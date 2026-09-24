/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.BoundElimination
import FTQCLib.Hierarchy.DyadicValuation
import FTQCLib.Examples.CarrierStateHadamard
import FTQCLib.Hierarchy.AffineDifference

/-!
# The eliminating H

The free rule `applyHFiner` adjoins a bound bit and leaves the floor; the previous module
eliminates a bound bit whose last-variable difference is collapse- or rotate-shaped on the support.
This module composes the two into a Hadamard that returns to the height it started from, and reads
the shape from the floor itself: at an X-supported bit a floor record carries a reader `g` with
`g.X = e_k`, and the exponent law along `g` is the difference of the adjoined bit up to the coupling
`2^{m−1}·w_k`.

## Main definitions

* `hElimCollapse k σ ε S` — the free rule at `k` followed by collapse elimination; the Lagrangian is
  swapped at `k` and the offset moved onto the cut `ε + ⟨σ, w⟩ = 0`.
* `hElimRotate k S a Λ` — the free rule at `k` followed by rotate elimination.
* `floorSigma k g`, `floorKappa K g`, `floorEps K g` — the data a floor reads at a reader `g`: the
  sign datum (`g.Z` with the `k`-th entry set to `1`), the residue of the exponent law along `g`,
  and the collapse bit.

## Main results

* `lastDiff_hSumExp` — the adjoined bit's difference is the input's `k`-difference at `w[k ← 0]`
  plus the coupling `2^{m−1}·w_k`.
* `amp_hElimCollapse`, `amp_hElimRotate` — the eliminators denote `walshTransform k (amp S)`.
* `isFloor_hElimCollapse`, `isFloor_hElimRotate` — floors go to floors, at the same height.
* `lastDiff_hSumExp_of_shiftLaw` — on a floor with a reader `g` at `k`, the adjoined difference is
  `κ + 2^{m−1}·⟨floorSigma k g, w⟩` with `2κ = 2^{m−1}·(g.Z k)`.
* `signAffine_of_shiftLaw`, `rotateData_of_shiftLaw` — the reader's `Z` bit at `k` selects the
  shape.
* `hElimFloor k K g`, `hFloor k K` — the eliminating H at a reader, and H on the floor as a
  constructor (eliminate at an X-supported bit, raise otherwise), with DEN and FL.
* `hadamard_floor_total` — every H on a height-zero floor has a height-zero floor image with
  the Walsh-transformed amplitude and the swapped Lagrangian: eliminated at an X-supported bit,
  raised otherwise.

Everything here is frame-pure. No `FTQCLib.Hilbert`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Hierarchy.DiagPhase FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## Words and pairings -/

/-- Setting a coordinate to `0` and then flipping it sets it to `1`. -/
theorem update_zero_add_single {N : ℕ} (z : Fin N → ZMod 2) (i : Fin N) :
    Function.update z i 0 + Pi.single i 1 = Function.update z i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Setting a coordinate to `0` is adding its value at the unit word (characteristic two). -/
theorem update_zero_eq_add_smul_single (w : Fin n → ZMod 2) (k : Fin n) :
    Function.update w k 0 = w + (w k) • (Pi.single k 1 : Fin n → ZMod 2) := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      CharTwo.add_self_eq_zero]
  · simp [hj]

/-- The pairing pulls a scalar out on the left. -/
theorem dotF2_smul_left (c : ZMod 2) (u v : Fin n → ZMod 2) : dotF2 (c • u) v = c * dotF2 u v := by
  unfold dotF2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-! ## The adjoined bit's difference -/

/-- The free rule's exponent at a snoc: the input at `k ← b` plus the coupling `2^{m−1}·w_k·b`. -/
theorem hSumExp_eval_snoc {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2)
    (y : Fin h → ZMod 2) (b : ZMod 2) :
    (hSumExp k Q).eval (Fin.snoc (Fin.append w y) b) =
      Q.eval (Function.update (Fin.append w y) (Fin.castAdd h k) b) +
        (2 : ZMod (2 ^ m)) ^ (m - 1) * ((w k).val : ZMod (2 ^ m)) *
          ((b.val : ℕ) : ZMod (2 ^ m)) := by
  rw [hSumExp_eval]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left]

/-- **The adjoined bit's difference.** The last-variable difference of the free rule's exponent is
the input's `k`-difference at `w[k ← 0]` plus the coupling `2^{m−1}·w_k`. -/
theorem lastDiff_hSumExp {h m : ℕ} (k : Fin n) (Q : DiagPhase (n + h) m) (w : Fin n → ZMod 2)
    (y : Fin h → ZMod 2) :
    (lastDiff (hSumExp k Q)).eval (Fin.append w y) =
      funcDerivEval (Fin.castAdd h k) Q
          (Function.update (Fin.append w y) (Fin.castAdd h k) 0) +
        (2 : ZMod (2 ^ m)) ^ (m - 1) * ((w k).val : ZMod (2 ^ m)) := by
  rw [lastDiff_eval, hSumExp_eval_snoc, hSumExp_eval_snoc]
  unfold funcDerivEval funcDeriv
  rw [update_zero_add_single, show ((1 : ZMod 2).val : ℕ) = 1 by decide, ZMod.val_zero,
    Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero]
  ring

/-! ## The eliminating H -/

/-- **Collapse.** The free rule at `k` followed by collapse elimination: the Lagrangian is swapped
at `k` and the offset moved onto the cut `ε + ⟨σ, w⟩ = 0`. -/
noncomputable def hElimCollapse (k : Fin n) (σ : Fin n → ZMod 2) (ε : ZMod 2)
    (S : KernelSumState n) : KernelSumState n :=
  elimCollapse (hSumExp k S.Q) S.c (Submodule.map (pauliSwapOn {k}) S.L)
    (S.x₀ + (ε + dotF2 σ S.x₀) • (Pi.single k 1 : Fin n → ZMod 2))

/-- **Rotate.** The free rule at `k` followed by rotate elimination: the Lagrangian is swapped at
`k` and the offset kept. -/
noncomputable def hElimRotate (k : Fin n) (S : KernelSumState n) (a : ZMod (2 ^ S.m))
    (Λ : DiagPhase (n + S.h) S.m) : KernelSumState n :=
  elimRotate (hSumExp k S.Q) a Λ S.c (Submodule.map (pauliSwapOn {k}) S.L) S.x₀

@[simp] theorem hElimCollapse_m (k : Fin n) (σ : Fin n → ZMod 2) (ε : ZMod 2)
    (S : KernelSumState n) : (hElimCollapse k σ ε S).m = S.m := rfl

/-- The height is the input's: the bit adjoined by the free rule is eliminated. -/
@[simp] theorem hElimCollapse_h (k : Fin n) (σ : Fin n → ZMod 2) (ε : ZMod 2)
    (S : KernelSumState n) : (hElimCollapse k σ ε S).h = S.h := rfl

@[simp] theorem hElimCollapse_L (k : Fin n) (σ : Fin n → ZMod 2) (ε : ZMod 2)
    (S : KernelSumState n) : (hElimCollapse k σ ε S).L = Submodule.map (pauliSwapOn {k}) S.L :=
  rfl

@[simp] theorem hElimCollapse_x₀ (k : Fin n) (σ : Fin n → ZMod 2) (ε : ZMod 2)
    (S : KernelSumState n) :
    (hElimCollapse k σ ε S).x₀ = S.x₀ + (ε + dotF2 σ S.x₀) • (Pi.single k 1 : Fin n → ZMod 2) :=
  rfl

@[simp] theorem hElimRotate_m (k : Fin n) (S : KernelSumState n) (a : ZMod (2 ^ S.m))
    (Λ : DiagPhase (n + S.h) S.m) : (hElimRotate k S a Λ).m = S.m := rfl

/-- The height is the input's. -/
@[simp] theorem hElimRotate_h (k : Fin n) (S : KernelSumState n) (a : ZMod (2 ^ S.m))
    (Λ : DiagPhase (n + S.h) S.m) : (hElimRotate k S a Λ).h = S.h := rfl

@[simp] theorem hElimRotate_L (k : Fin n) (S : KernelSumState n) (a : ZMod (2 ^ S.m))
    (Λ : DiagPhase (n + S.h) S.m) :
    (hElimRotate k S a Λ).L = Submodule.map (pauliSwapOn {k}) S.L := rfl

@[simp] theorem hElimRotate_x₀ (k : Fin n) (S : KernelSumState n) (a : ZMod (2 ^ S.m))
    (Λ : DiagPhase (n + S.h) S.m) : (hElimRotate k S a Λ).x₀ = S.x₀ := rfl

/-! ## The support laws -/

/-- The collapse eliminator's support is the input's support cut by `ε + ⟨σ, w⟩ = 0`, given collapse
alignment at the datum and isotropy of `L`. -/
theorem support_hElimCollapse (k : Fin n) {σ : Fin n → ZMod 2} (ε : ZMod 2)
    (S : KernelSumState n) (hσk : σ k = 1) (hal : AlignedCollapse S.L k σ)
    (hS : IsStabilizer S.L) (w : Fin n → ZMod 2) :
    (∃ p ∈ (hElimCollapse k σ ε S).L, w = (hElimCollapse k σ ε S).x₀ + p.X) ↔
      (∃ p ∈ S.L, w = S.x₀ + p.X) ∧ ε + dotF2 σ w = 0 := by
  have hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L :=
    single_mem_of_alignedCollapse hal
  have horth : ∀ p ∈ S.L, omega (⟨Pi.single k 1, σ + Pi.single k 1⟩ : Pauli n) p = 0 :=
    fun p hp => hS _ hal p hp
  rw [mem_support_iff, mem_support_iff, hElimCollapse_L, hElimCollapse_x₀,
    mem_xProj_map_pauliSwapOn_iff_of_alignedCollapse hal hσk horth, sub_add_eq_sub_sub,
    Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ _ hk), dotF2_sub_right, dotF2_sub_right,
    dotF2_smul_right, dotF2_single, hσk]
  have key : ∀ a b e : ZMod 2, (a - b - (e + b) * 1 = 0 ↔ e + a = 0) := by decide
  rw [key]

/-- The rotate eliminator's support is the input's, given rotate alignment. -/
theorem support_hElimRotate (k : Fin n) (S : KernelSumState n) (a : ZMod (2 ^ S.m))
    (Λ : DiagPhase (n + S.h) S.m) (hal : AlignedRotate S.L k) (w : Fin n → ZMod 2) :
    (∃ p ∈ (hElimRotate k S a Λ).L, w = (hElimRotate k S a Λ).x₀ + p.X) ↔
      (∃ p ∈ S.L, w = S.x₀ + p.X) := by
  rw [mem_support_iff, mem_support_iff, hElimRotate_L, hElimRotate_x₀,
    mem_xProj_map_pauliSwapOn_iff_of_alignedRotate hal]

/-! ## Denotation -/

/-- **DEN, collapse.** -/
theorem amp_hElimCollapse (k : Fin n) {σ : Fin n → ZMod 2} {ε : ZMod 2} (S : KernelSumState n)
    (hm : 1 ≤ S.m) (hσk : σ k = 1) (hal : AlignedCollapse S.L k σ) (hS : IsStabilizer S.L)
    (hsign : SignAffine (hSumExp k S.Q) S.L S.x₀ σ ε) :
    amp (hElimCollapse k σ ε S) = walshTransform k (amp S) := by
  rw [← amp_applyHFiner k S hm (single_mem_of_alignedCollapse hal)]
  exact amp_elimCollapse hm S.c hsign (support_hElimCollapse k ε S hσk hal hS)

/-- **DEN, rotate.** -/
theorem amp_hElimRotate (k : Fin n) (S : KernelSumState n) {a : ZMod (2 ^ S.m)}
    {Λ : DiagPhase (n + S.h) S.m} (hm : 1 ≤ S.m) (hal : AlignedRotate S.L k)
    (hrot : RotateData (hSumExp k S.Q) S.L S.x₀ a Λ) :
    amp (hElimRotate k S a Λ) = walshTransform k (amp S) := by
  rw [← amp_applyHFiner k S hm (single_mem_of_alignedRotate hal)]
  exact amp_elimRotate hm S.c hrot (support_hElimRotate k S a Λ hal)

/-! ## Closure: carriers and floors -/

/-- **W, collapse.** -/
theorem isCarrier_hElimCollapse (k : Fin n) {σ : Fin n → ZMod 2} {ε : ZMod 2}
    (S : KernelSumState n) (hS : IsCarrier S) (hσk : σ k = 1) (hal : AlignedCollapse S.L k σ)
    (hsign : SignAffine (hSumExp k S.Q) S.L S.x₀ σ ε) :
    IsCarrier (hElimCollapse k σ ε S) := by
  refine ⟨hS.1, isStabilizer_map_pauliSwapOn k hS.2.1,
    coisotropic_map_pauliSwapOn k hS.2.1 (finrank_eq_of_isCarrier hS), ?_⟩
  rw [amp_hElimCollapse k S hS.1 hσk hal hS.2.1 hsign]
  exact walshTransform_ne_zero k hS.2.2.2

/-- **W, rotate.** -/
theorem isCarrier_hElimRotate (k : Fin n) (S : KernelSumState n) {a : ZMod (2 ^ S.m)}
    {Λ : DiagPhase (n + S.h) S.m} (hS : IsCarrier S) (hal : AlignedRotate S.L k)
    (hrot : RotateData (hSumExp k S.Q) S.L S.x₀ a Λ) :
    IsCarrier (hElimRotate k S a Λ) := by
  refine ⟨hS.1, isStabilizer_map_pauliSwapOn k hS.2.1,
    coisotropic_map_pauliSwapOn k hS.2.1 (finrank_eq_of_isCarrier hS), ?_⟩
  rw [amp_hElimRotate k S hS.1 hal hrot]
  exact walshTransform_ne_zero k hS.2.2.2

/-- **FL, collapse.** -/
theorem isFloor_hElimCollapse (k : Fin n) {σ : Fin n → ZMod 2} {ε : ZMod 2}
    (S : KernelSumState n) (hF : IsFloor S) (hσk : σ k = 1) (hal : AlignedCollapse S.L k σ)
    (hsign : SignAffine (hSumExp k S.Q) S.L S.x₀ σ ε) :
    IsFloor (hElimCollapse k σ ε S) := by
  refine ⟨isCarrier_hElimCollapse k S hF.1 hσk hal hsign, ?_⟩
  rw [amp_hElimCollapse k S hF.1.1 hσk hal hF.1.2.1 hsign]
  exact stabilizedBy_map_pauliSwapOn_walshTransform k hF.2

/-- **FL, rotate.** -/
theorem isFloor_hElimRotate (k : Fin n) (S : KernelSumState n) {a : ZMod (2 ^ S.m)}
    {Λ : DiagPhase (n + S.h) S.m} (hF : IsFloor S) (hal : AlignedRotate S.L k)
    (hrot : RotateData (hSumExp k S.Q) S.L S.x₀ a Λ) :
    IsFloor (hElimRotate k S a Λ) := by
  refine ⟨isCarrier_hElimRotate k S hF.1 hal hrot, ?_⟩
  rw [amp_hElimRotate k S hF.1.1 hal hrot]
  exact stabilizedBy_map_pauliSwapOn_walshTransform k hF.2

/-! ## The floor reads its data -/

/-- The sign datum of a reader `g` at `k`: `g.Z` with the `k`-th entry set to `1`. -/
def floorSigma (k : Fin n) (g : Pauli n) : Fin n → ZMod 2 :=
  g.Z + (1 + g.Z k) • (Pi.single k 1 : Fin n → ZMod 2)

/-- The datum reads `1` at `k`. -/
theorem floorSigma_apply_self (k : Fin n) (g : Pauli n) : floorSigma k g k = 1 := by
  unfold floorSigma
  rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  have key : ∀ a : ZMod 2, a + (1 + a) = 1 := by decide
  exact key _

/-- With `g.Z k = 0` the datum plus the unit word is `g.Z`. -/
theorem floorSigma_add_single_of_Z_zero (k : Fin n) (g : Pauli n) (hZ : g.Z k = 0) :
    floorSigma k g + Pi.single k 1 = g.Z := by
  unfold floorSigma
  rw [hZ, add_zero, one_smul, add_assoc, add_self_word, add_zero]

/-- The pairing with the datum. -/
theorem dotF2_floorSigma (k : Fin n) (g : Pauli n) (w : Fin n → ZMod 2) :
    dotF2 (floorSigma k g) w = dotF2 g.Z w + (1 + g.Z k) * w k := by
  unfold floorSigma
  rw [dotF2_add_left, dotF2_smul_left, dotF2_single_left]

/-- With `g.Z k = 0` a reader is the collapse Pauli at its datum. -/
theorem alignedCollapse_floorSigma {L : Submodule (ZMod 2) (Pauli n)} {k : Fin n} {g : Pauli n}
    (hg : IsReader L k g) (hZ : g.Z k = 0) : AlignedCollapse L k (floorSigma k g) := by
  unfold AlignedCollapse
  rw [floorSigma_add_single_of_Z_zero k g hZ, ← hg.2]
  exact hg.1

/-- The residue of the exponent law along `g`, read at the offset. -/
noncomputable def floorKappa (K : KernelState n) (g : Pauli n) : ZMod (2 ^ K.m) :=
  DiagPhase.eval K.q (K.x₀ + g.X) - DiagPhase.eval K.q K.x₀ -
    (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m))

/-- On a record obeying the exponent law, the defect along `g ∈ L` is `floorKappa K g` everywhere
on the support. -/
theorem shiftLaw_defect_eq {K : KernelState n} (hlaw : ShiftLaw K) {g : Pauli n} (hg : g ∈ K.L)
    (w : Fin n → ZMod 2) (hw : ∃ p ∈ K.L, w = K.x₀ + p.X) :
    DiagPhase.eval K.q (w + g.X) - DiagPhase.eval K.q w -
      (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((zDot g w : ℕ) : ZMod (2 ^ K.m)) = floorKappa K g := by
  obtain ⟨κ, hκ⟩ := hlaw g hg
  rw [hκ w hw]
  unfold floorKappa
  rw [hκ K.x₀ (x₀_mem_support K)]

/-- The collapse bit: `0` when the residue vanishes, `1` otherwise. -/
noncomputable def floorEps (K : KernelState n) (g : Pauli n) : ZMod 2 :=
  if floorKappa K g = 0 then 0 else 1

/-- Under `2κ = 0` the residue is `2^{m−1}` times the collapse bit. -/
theorem floorKappa_eq_of_two_mul_eq_zero {K : KernelState n} (hm : 1 ≤ K.m) {g : Pauli n}
    (hκ : 2 * floorKappa K g = 0) :
    floorKappa K g =
      (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * (((floorEps K g).val : ℕ) : ZMod (2 ^ K.m)) := by
  obtain ⟨ε, hε⟩ := exists_bit_of_two_mul_eq_zero hm hκ
  unfold floorEps
  rcases zmod_two_eq_zero_or_one ε with rfl | rfl
  · rw [ZMod.val_zero, Nat.cast_zero, mul_zero] at hε
    rw [if_pos hε, ZMod.val_zero, Nat.cast_zero, mul_zero]
    exact hε
  · rw [show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_one, mul_one] at hε
    rw [if_neg (by rw [hε]; exact two_pow_pred_ne_zero hm),
      show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_one, mul_one]
    exact hε

/-- **The floor reader theorem.** On a record obeying the exponent law, a reader `g` at `k` gives
the adjoined bit's difference on the support as `floorKappa K g + 2^{m−1}·⟨floorSigma k g, w⟩`,
with `2·floorKappa K g = 2^{m−1}·(g.Z k)`. -/
theorem lastDiff_hSumExp_of_shiftLaw {K : KernelState n} (hlaw : ShiftLaw K) {k : Fin n}
    {g : Pauli n} (hg : IsReader K.L k g) :
    2 * floorKappa K g =
        (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * (((g.Z k).val : ℕ) : ZMod (2 ^ K.m)) ∧
      ∀ w : Fin n → ZMod 2, (∃ p ∈ K.L, w = K.x₀ + p.X) → ∀ y : Fin 0 → ZMod 2,
        (lastDiff (hSumExp (h := 0) k K.q)).eval (Fin.append w y) =
          floorKappa K g + (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) *
            (((dotF2 (floorSigma k g) w).val : ℕ) : ZMod (2 ^ K.m)) := by
  obtain ⟨hgL, hgX⟩ := hg
  have hκ := shiftLaw_defect_eq hlaw hgL
  have hz : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * 2 = 0 := two_pow_pred_mul_two
  refine ⟨?_, ?_⟩
  · have h0 := hκ K.x₀ (x₀_mem_support K)
    have h1 := hκ (K.x₀ + g.X) (support_add_X hgL (x₀_mem_support K))
    rw [add_assoc, add_self_word, add_zero] at h1
    have hsplit := two_pow_pred_mul_zDot_add_X (m := K.m) g K.x₀
    have hy : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((yWeight g : ℕ) : ZMod (2 ^ K.m)) =
        (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * (((g.Z k).val : ℕ) : ZMod (2 ^ K.m)) := by
      apply two_pow_pred_mul_eq_of_cast_eq
      rw [yWeight, zDot_cast_two, hgX, ZMod.natCast_zmod_val]
      exact dotF2_single g.Z k
    linear_combination -h0 - h1 - hsplit - hy -
      ((((g.Z k).val : ℕ) : ZMod (2 ^ K.m)) + ((zDot g K.x₀ : ℕ) : ZMod (2 ^ K.m))) * hz
  · intro w hw y
    have hk0 : Fin.castAdd 0 k = k := Fin.ext rfl
    rw [lastDiff_hSumExp, append_fin0, hk0]
    unfold funcDerivEval funcDeriv
    have hv : ∃ p ∈ K.L, Function.update w k 0 = K.x₀ + p.X := by
      rw [update_zero_eq_add_smul_single, ← hgX, ← X_smul]
      exact support_add_X (Submodule.smul_mem _ _ hgL) hw
    have hκv := hκ _ hv
    have hzd : (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) *
        ((zDot g (Function.update w k 0) : ℕ) : ZMod (2 ^ K.m)) =
        (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) *
          (((dotF2 g.Z (Function.update w k 0)).val : ℕ) : ZMod (2 ^ K.m)) := by
      apply two_pow_pred_mul_eq_of_cast_eq
      rw [zDot_cast_two, ZMod.natCast_zmod_val]
      rfl
    have hdv : dotF2 g.Z (Function.update w k 0) = dotF2 g.Z w + w k * g.Z k := by
      rw [update_zero_eq_add_smul_single, dotF2_add_right, dotF2_smul_right, dotF2_single]
    have hval : ∀ s t u : ZMod 2,
        (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * (((s + u * t).val : ℕ) : ZMod (2 ^ K.m)) +
            (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * ((u.val : ℕ) : ZMod (2 ^ K.m)) =
          (2 : ZMod (2 ^ K.m)) ^ (K.m - 1) * (((s + (1 + t) * u).val : ℕ) : ZMod (2 ^ K.m)) := by
      intro s t u
      rw [two_pow_pred_mul_val_add, two_pow_pred_mul_val_add,
        show (1 + t) * u = u * t + u by ring, two_pow_pred_mul_val_add]
      ring
    rw [dotF2_floorSigma, ← hval (dotF2 g.Z w) (g.Z k) (w k), ← hdv, ← hzd, ← hgX]
    linear_combination hκv

/-- **Collapse on the floor.** A reader with `g.Z k = 0` gives the collapse shape at its datum,
with the collapse bit read from the residue. -/
theorem signAffine_of_shiftLaw {K : KernelState n} (hm : 1 ≤ K.m) (hlaw : ShiftLaw K)
    {k : Fin n} {g : Pauli n} (hg : IsReader K.L k g) (hZ : g.Z k = 0) :
    SignAffine (h := 0) (hSumExp (h := 0) k K.q) K.L K.x₀ (floorSigma k g) (floorEps K g) := by
  obtain ⟨hκ2, hdiff⟩ := lastDiff_hSumExp_of_shiftLaw hlaw hg
  rw [hZ, ZMod.val_zero, Nat.cast_zero, mul_zero] at hκ2
  intro w hw y
  rw [hdiff w hw y, floorKappa_eq_of_two_mul_eq_zero hm hκ2, two_pow_pred_mul_val_add]

/-- **Rotate on the floor.** A reader with `g.Z k = 1` gives the rotate shape with the residue as
`a` and the XOR form of its datum as `Λ`. -/
theorem rotateData_of_shiftLaw {K : KernelState n} (hlaw : ShiftLaw K) {k : Fin n} {g : Pauli n}
    (hg : IsReader K.L k g) (hZ : g.Z k = 1) :
    RotateData (h := 0) (hSumExp (h := 0) k K.q) K.L K.x₀ (floorKappa K g)
      (xorForm (h := 0) (m := K.m) (floorSigma k g) 0) := by
  obtain ⟨hκ2, hdiff⟩ := lastDiff_hSumExp_of_shiftLaw hlaw hg
  rw [hZ, show ((1 : ZMod 2).val : ℕ) = 1 by decide, Nat.cast_one, mul_one] at hκ2
  refine ⟨hκ2, fun w hw y => ⟨dotF2 (floorSigma k g) w, ?_, hdiff w hw y⟩⟩
  rw [xorForm_eval, zero_add]
  have hfun : (fun j => Fin.append w y (Fin.castAdd 0 j)) = w :=
    funext fun j => Fin.append_left w y j
  rw [hfun]

/-! ## The eliminating H at a reader, and H on the floor -/

/-- **The eliminating H at a reader.** Collapse when `g.Z k = 0`, rotate when `g.Z k = 1`, the
data read from the floor. -/
noncomputable def hElimFloor (k : Fin n) (K : KernelState n) (g : Pauli n) : KernelSumState n :=
  if g.Z k = 0 then hElimCollapse k (floorSigma k g) (floorEps K g) (ofKernelState K)
  else
    hElimRotate k (ofKernelState K) (floorKappa K g)
      (xorForm (h := 0) (m := K.m) (floorSigma k g) 0)

/-- The height is `0`: the bit adjoined by the free rule is eliminated. -/
theorem hElimFloor_h (k : Fin n) (K : KernelState n) (g : Pauli n) : (hElimFloor k K g).h = 0 := by
  unfold hElimFloor
  split_ifs <;> rfl

/-- The Lagrangian is swapped at `k`. -/
theorem hElimFloor_L (k : Fin n) (K : KernelState n) (g : Pauli n) :
    (hElimFloor k K g).L = Submodule.map (pauliSwapOn {k}) K.L := by
  unfold hElimFloor
  split_ifs <;> rfl

/-- **DEN at a reader.** -/
theorem amp_hElimFloor {K : KernelState n} (hF : IsFloor (ofKernelState K)) {k : Fin n}
    {g : Pauli n} (hg : IsReader K.L k g) :
    amp (hElimFloor k K g) = walshTransform k (amp (ofKernelState K)) := by
  have hm : 1 ≤ K.m := hF.1.1
  have hlaw : ShiftLaw K := (isFloor_iff_shiftLaw K hF.1).mp hF
  unfold hElimFloor
  split_ifs with hZ
  · exact amp_hElimCollapse k _ hm (floorSigma_apply_self k g) (alignedCollapse_floorSigma hg hZ)
      hF.1.2.1 (signAffine_of_shiftLaw hm hlaw hg hZ)
  · have hZ1 : g.Z k = 1 := (zmod_two_eq_zero_or_one _).resolve_left hZ
    exact amp_hElimRotate k _ hm ⟨g, hg, hZ1⟩ (rotateData_of_shiftLaw hlaw hg hZ1)

/-- **FL at a reader.** -/
theorem isFloor_hElimFloor {K : KernelState n} (hF : IsFloor (ofKernelState K)) {k : Fin n}
    {g : Pauli n} (hg : IsReader K.L k g) : IsFloor (hElimFloor k K g) := by
  have hm : 1 ≤ K.m := hF.1.1
  have hlaw : ShiftLaw K := (isFloor_iff_shiftLaw K hF.1).mp hF
  unfold hElimFloor
  split_ifs with hZ
  · exact isFloor_hElimCollapse k _ hF (floorSigma_apply_self k g)
      (alignedCollapse_floorSigma hg hZ) (signAffine_of_shiftLaw hm hlaw hg hZ)
  · have hZ1 : g.Z k = 1 := (zmod_two_eq_zero_or_one _).resolve_left hZ
    exact isFloor_hElimRotate k _ hF ⟨g, hg, hZ1⟩ (rotateData_of_shiftLaw hlaw hg hZ1)

open Classical in
/-- **H on the floor**, as a constructor: eliminate at an X-supported bit through a reader, raise
otherwise through a representer; the last branch is never taken on a floor. -/
noncomputable def hFloor (k : Fin n) (K : KernelState n) : KernelSumState n :=
  if hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj K.L then
    hElimFloor k K (Classical.choose ((exists_reader_iff K.L k).mpr hk))
  else if hrep : ∃ u : Fin n → ZMod 2, u k = 0 ∧
      ∀ v ∈ Submodule.map xProj K.L, dotF2 u v = v k then
    hRaise k (Classical.choose hrep) (ofKernelState K)
  else ofKernelState K

/-- The height is `0`. -/
theorem hFloor_h (k : Fin n) (K : KernelState n) : (hFloor k K).h = 0 := by
  unfold hFloor
  split_ifs
  · exact hElimFloor_h k K _
  · rfl
  · rfl

/-- On a floor the Lagrangian is swapped at `k`. -/
theorem hFloor_L {K : KernelState n} (hF : IsFloor (ofKernelState K)) (k : Fin n) :
    (hFloor k K).L = Submodule.map (pauliSwapOn {k}) K.L := by
  unfold hFloor
  split_ifs with hk hrep
  · exact hElimFloor_L k K _
  · rfl
  · exact absurd (exists_representer hF.1.2.1 hF.1.2.2.1 hk) hrep

/-- **DEN on the floor.** -/
theorem amp_hFloor {K : KernelState n} (hF : IsFloor (ofKernelState K)) (k : Fin n) :
    amp (hFloor k K) = walshTransform k (amp (ofKernelState K)) := by
  unfold hFloor
  split_ifs with hk hrep
  · exact amp_hElimFloor hF (Classical.choose_spec ((exists_reader_iff K.L k).mpr hk))
  · obtain ⟨hu, hrep'⟩ := Classical.choose_spec hrep
    exact amp_hRaise k _ (ofKernelState K) hF.1.2.2.1 hu hrep' hF.1.1
  · exact absurd (exists_representer hF.1.2.1 hF.1.2.2.1 hk) hrep

/-- **FL on the floor.** -/
theorem isFloor_hFloor {K : KernelState n} (hF : IsFloor (ofKernelState K)) (k : Fin n) :
    IsFloor (hFloor k K) := by
  unfold hFloor
  split_ifs with hk hrep
  · exact isFloor_hElimFloor hF (Classical.choose_spec ((exists_reader_iff K.L k).mpr hk))
  · obtain ⟨hu, hrep'⟩ := Classical.choose_spec hrep
    exact isFloor_hRaise k _ hF hu hrep'
  · exact absurd (exists_representer hF.1.2.1 hF.1.2.2.1 hk) hrep

/-! ## Totality on the floor -/

/-- **The eliminating H at an X-supported bit.** A height-zero floor has a height-zero floor image
with the swapped Lagrangian and the Walsh-transformed amplitude. -/
theorem exists_floor_hElim (K : KernelState n) (hF : IsFloor (ofKernelState K)) {k : Fin n}
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj K.L) :
    ∃ T : KernelSumState n, IsFloor T ∧ T.h = 0 ∧ T.L = Submodule.map (pauliSwapOn {k}) K.L ∧
      amp T = walshTransform k (amp (ofKernelState K)) := by
  obtain ⟨g, hg⟩ := (exists_reader_iff K.L k).mpr hk
  exact ⟨hElimFloor k K g, isFloor_hElimFloor hF hg, hElimFloor_h k K g, hElimFloor_L k K g,
    amp_hElimFloor hF hg⟩

/-- **Hadamard on the floor is total at height zero** (the kernel-state form): `hFloor` is a
height-zero floor with the swapped Lagrangian and the Walsh-transformed amplitude. -/
theorem hadamard_floor_total_kernelState (K : KernelState n) (hF : IsFloor (ofKernelState K))
    (k : Fin n) :
    ∃ T : KernelSumState n, IsFloor T ∧ T.h = 0 ∧ T.L = Submodule.map (pauliSwapOn {k}) K.L ∧
      amp T = walshTransform k (amp (ofKernelState K)) :=
  ⟨hFloor k K, isFloor_hFloor hF k, hFloor_h k K, hFloor_L hF k, amp_hFloor hF k⟩

/-- A height-zero record is a kernel state. -/
theorem exists_kernelState_of_h_eq_zero (S : KernelSumState n) (h0 : S.h = 0) :
    ∃ K : KernelState n, S = ofKernelState K := by
  obtain ⟨m, h, Q, c, L, x₀⟩ := S
  dsimp only at h0
  subst h0
  exact ⟨⟨m, Q, c, L, x₀⟩, rfl⟩

/-- **Hadamard on the floor is total at height zero.** -/
theorem hadamard_floor_total (S : KernelSumState n) (hF : IsFloor S) (h0 : S.h = 0) (k : Fin n) :
    ∃ T : KernelSumState n, IsFloor T ∧ T.h = 0 ∧ T.L = Submodule.map (pauliSwapOn {k}) S.L ∧
      amp T = walshTransform k (amp S) := by
  obtain ⟨K, rfl⟩ := exists_kernelState_of_h_eq_zero S h0
  exact hadamard_floor_total_kernelState K hF k

end FTQCLib.Frame.Walkthrough

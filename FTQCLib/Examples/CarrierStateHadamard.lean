/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierState
import FTQCLib.Examples.HadamardCover
import FTQCLib.Examples.HadamardReduction

/-!
# Closure of the carrier and the floor under the Hadamard rules

Each Hadamard rule is certified by one equation, `amp (rule i S) = walshTransform i (amp S)`.
This file adds the closure properties of the state record: the rules send carriers to carriers
(*carrier closure*), and where they are meant to, floor records to floor records (*floor
closure*).

The one new proof is the **intertwining lemma** `pauliAct_pauliSwapOn_walshTransform`: the
Pauli action of the swap-lifted `g` on a Walsh transform is the Walsh transform of the action of
`g`, up to the sign `(−1)^{(g.X i)(g.Z i)}`. With it, a Lagrangian that stabilizes `amp S` with
signs is carried by `pauliSwapOn {i}` to one that stabilizes `walshTransform i (amp S)` with
signs — which is exactly what `hRaise` and `applyHPinned` do to `L`. The swap preserves the
symplectic form (`omega_pauliSwapOn_singleton`), so isotropy, dimension and co-isotropy transport
along it.

`applyHFiner` keeps `L` and adjoins a bound bit; it preserves the carrier (its denotation is a
Walsh transform, nonzero) and leaves the floor stratum by design — the eliminating H is the
constructor that returns to it.

Everything here is frame-pure. No `FTQCLib.Hilbert`.

## Main results

* `pauliAct_pauliSwapOn_walshTransform` — the intertwining lemma.
* `isCarrier_hRaise`, `isFloor_hRaise` — carrier and floor closure for the representer rule.
* `isCarrier_applyHFiner` — carrier closure for the free rule.
* `isCarrier_applyHPinned`, `isFloor_applyHPinned` — carrier and floor closure for the pinned rule
  (with `hqfree`).
* `hadamard_cover_of_isCarrier` — the two-constructor cover on a carrier.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## The swap preserves the symplectic form -/

/-- Swapping X and Z at one bit preserves `omega`. -/
theorem omega_pauliSwapOn_singleton (i : Fin n) (p q : Pauli n) :
    omega (pauliSwapOn {i} p) (pauliSwapOn {i} q) = omega p q := by
  unfold omega
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j = i
  · subst hj
    simp [add_comm]
  · simp [hj]

/-- The swap carries isotropic subspaces to isotropic subspaces. -/
theorem isStabilizer_map_pauliSwapOn (i : Fin n) {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) : IsStabilizer (Submodule.map (pauliSwapOn {i}) L) := by
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := Submodule.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := Submodule.mem_map.mp hq
  rw [omega_pauliSwapOn_singleton]
  exact hS p' hp' q' hq'

/-- The swap as a linear equivalence (it is an involution). -/
noncomputable def pauliSwapEquiv (i : Fin n) : Pauli n ≃ₗ[ZMod 2] Pauli n :=
  LinearEquiv.ofInvolutive (pauliSwapOn {i}) (pauliSwapOn_pauliSwapOn {i})

/-- The swap preserves dimension. -/
theorem finrank_map_pauliSwapOn (i : Fin n) (L : Submodule (ZMod 2) (Pauli n)) :
    finrank (ZMod 2) (Submodule.map (pauliSwapOn {i}) L) = finrank (ZMod 2) L :=
  LinearEquiv.finrank_map_eq (pauliSwapEquiv i) L

/-- The swap carries Lagrangians to co-isotropic subspaces. -/
theorem coisotropic_map_pauliSwapOn (i : Fin n) {L : Submodule (ZMod 2) (Pauli n)}
    (hS : IsStabilizer L) (hr : finrank (ZMod 2) L = n) :
    LinearMap.BilinForm.orthogonal omegaBilin (Submodule.map (pauliSwapOn {i}) L)
      ≤ Submodule.map (pauliSwapOn {i}) L :=
  orthogonal_le_of_lagrangian (isStabilizer_map_pauliSwapOn i hS)
    (by rw [finrank_map_pauliSwapOn]; exact hr)

/-! ## The Walsh transform of a nonzero function is nonzero -/

/-- The Walsh transform of the zero function is zero. -/
theorem walshTransform_zero (k : Fin n) : walshTransform k (0 : (Fin n → ZMod 2) → ℂ) = 0 := by
  funext w
  simp [walshTransform]

/-- The Walsh transform of a nonzero function is nonzero. -/
theorem walshTransform_ne_zero (k : Fin n) {f : (Fin n → ZMod 2) → ℂ} (hf : f ≠ 0) :
    walshTransform k f ≠ 0 := by
  intro h
  apply hf
  rw [← walshTransform_involutive k f, h, walshTransform_zero]

/-! ## The intertwining lemma -/

/-- `signOf` is the sign of the value. -/
theorem signOf_eq (b : ZMod 2) : signOf b = (-1) ^ b.val := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp [signOf]
  · have hv : ((1 : ZMod 2)).val = 1 := by decide
    simp [signOf, hv]

/-- Updating at `i` after adding the swapped X-part is updating after adding the X-part. -/
theorem update_add_swapX (i : Fin n) (g : Pauli n) (w : Fin n → ZMod 2) (b : ZMod 2) :
    Function.update (w + (pauliSwapOn {i} g).X) i b = Function.update (w + g.X) i b := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Adding the X-part after updating at `i` is updating after adding. -/
theorem update_add_X (i : Fin n) (g : Pauli n) (w : Fin n → ZMod 2) (b : ZMod 2) :
    Function.update w i b + g.X = Function.update (w + g.X) i (b + g.X i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- `zDot` split at one index. -/
theorem zDot_split (i : Fin n) (g : Pauli n) (v : Fin n → ZMod 2) :
    zDot g v = (g.Z i).val * (v i).val + ∑ j ∈ Finset.univ.erase i, (g.Z j).val * (v j).val := by
  unfold zDot
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]

/-- The off-`i` part of `zDot` does not see an update at `i`. -/
theorem sum_erase_update (i : Fin n) (z : Fin n → ZMod 2) (v : Fin n → ZMod 2) (b : ZMod 2) :
    ∑ j ∈ Finset.univ.erase i, (z j).val * ((Function.update v i b) j).val
      = ∑ j ∈ Finset.univ.erase i, (z j).val * (v j).val := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The off-`i` part of `zDot` does not see the swap at `i`, on either side. -/
theorem sum_erase_swap (i : Fin n) (g : Pauli n) (w : Fin n → ZMod 2) :
    ∑ j ∈ Finset.univ.erase i,
        ((pauliSwapOn {i} g).Z j).val * ((w + (pauliSwapOn {i} g).X) j).val
      = ∑ j ∈ Finset.univ.erase i, (g.Z j).val * ((w + g.X) j).val := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≠ i := Finset.ne_of_mem_erase hj
  simp [hj']

/-- The swap preserves `yWeight`. -/
theorem yWeight_pauliSwapOn (i : Fin n) (g : Pauli n) :
    yWeight (pauliSwapOn {i} g) = yWeight g := by
  unfold yWeight
  rw [zDot_split i, zDot_split i]
  have h1 : ∑ j ∈ Finset.univ.erase i,
      ((pauliSwapOn {i} g).Z j).val * ((pauliSwapOn {i} g).X j).val
        = ∑ j ∈ Finset.univ.erase i, (g.Z j).val * (g.X j).val := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hj']
  rw [h1]
  simp [mul_comm]

/-- **The intertwining lemma.** The action of the swap-lifted `g` on a Walsh transform is the Walsh
transform of the action of `g`, up to the sign `(−1)^{(g.X i)(g.Z i)}`. -/
theorem pauliAct_pauliSwapOn_walshTransform (i : Fin n) (g : Pauli n)
    (f : (Fin n → ZMod 2) → ℂ) :
    pauliAct (pauliSwapOn {i} g) (walshTransform i f)
      = fun w => (-1) ^ ((g.X i).val * (g.Z i).val) * walshTransform i (pauliAct g f) w := by
  funext w
  simp only [pauliAct, walshTransform]
  -- the evaluation points, all as updates of `w + g.X` at `i`
  rw [update_add_swapX, update_add_swapX, update_add_X, update_add_X, zero_add]
  -- the signs, split at `i`
  rw [zDot_split i (pauliSwapOn {i} g), sum_erase_swap, zDot_split i g, zDot_split i g,
    sum_erase_update, sum_erase_update, yWeight_pauliSwapOn]
  set T : ℕ := ∑ j ∈ Finset.univ.erase i, (g.Z j).val * ((w + g.X) j).val with hT
  have hv1 : ((1 : ZMod 2)).val = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  simp only [pauliSwapOn_Z, pauliSwapOn_X, Finset.mem_singleton, if_true, Pi.add_apply,
    Function.update_self, signOf_eq, pow_add]
  rcases zmod_two_eq_zero_or_one (g.X i) with hx | hx <;>
    rcases zmod_two_eq_zero_or_one (g.Z i) with hz | hz <;>
    rcases zmod_two_eq_zero_or_one (w i) with hw | hw <;>
    simp only [hx, hz, hw, ZMod.val_zero, hv1, h11, zero_add, add_zero, mul_zero, mul_one,
      one_mul, pow_zero, pow_one] <;>
    ring

/-! ## Closure of the floor under the swap lift -/

/-- A Lagrangian stabilizing `f` with signs is carried by the swap to one stabilizing the Walsh
transform of `f` with signs. -/
theorem stabilizedBy_map_pauliSwapOn_walshTransform (i : Fin n)
    {L : Submodule (ZMod 2) (Pauli n)} {f : (Fin n → ZMod 2) → ℂ} (hs : StabilizedBy L f) :
    StabilizedBy (Submodule.map (pauliSwapOn {i}) L) (walshTransform i f) := by
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hg'
  obtain ⟨s, hsg⟩ := hs g hg
  refine ⟨s + (g.X i) * (g.Z i), ?_⟩
  rw [pauliAct_pauliSwapOn_walshTransform, hsg]
  funext w
  have hlin : walshTransform i (fun w => (-1) ^ s.val * f w) w
      = (-1) ^ s.val * walshTransform i f w := by
    simp only [walshTransform]
    ring
  rw [hlin, ← mul_assoc, ← pow_add]
  congr 1
  apply neg_one_pow_eq_of_cast_eq
  rcases zmod_two_eq_zero_or_one (g.X i) with hx | hx <;>
    rcases zmod_two_eq_zero_or_one (g.Z i) with hz | hz <;>
    rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
    simp only [hx, hz] <;>
    decide

/-! ## The representer rule -/

/-- **Carrier closure for `hRaise`.** The representer rule sends carriers to carriers. -/
theorem isCarrier_hRaise (i : Fin n) (u : Fin n → ZMod 2) {S : KernelSumState n}
    (hS : IsCarrier S) (hui : u i = 0)
    (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i) :
    IsCarrier (hRaise i u S) := by
  refine ⟨hS.1, isStabilizer_map_pauliSwapOn i hS.2.1,
    coisotropic_map_pauliSwapOn i hS.2.1 (finrank_eq_of_isCarrier hS), ?_⟩
  rw [amp_hRaise i u S hS.2.2.1 hui hrep hS.1]
  exact walshTransform_ne_zero i hS.2.2.2

/-- **Floor closure for `hRaise`.** The representer rule sends floor records to floor records. -/
theorem isFloor_hRaise (i : Fin n) (u : Fin n → ZMod 2) {S : KernelSumState n}
    (hS : IsFloor S) (hui : u i = 0)
    (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i) :
    IsFloor (hRaise i u S) := by
  refine ⟨isCarrier_hRaise i u hS.1 hui hrep, ?_⟩
  rw [amp_hRaise i u S hS.1.2.2.1 hui hrep hS.1.1]
  exact stabilizedBy_map_pauliSwapOn_walshTransform i hS.2

/-! ## The free rule -/

/-- **Carrier closure for `applyHFiner`.** The free rule sends carriers to carriers when the bit is
X-supported. -/
theorem isCarrier_applyHFiner (k : Fin n) {S : KernelSumState n} (hS : IsCarrier S)
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L) :
    IsCarrier (applyHFiner k S) := by
  refine ⟨hS.1, hS.2.1, hS.2.2.1, ?_⟩
  rw [amp_applyHFiner k S hS.1 hk]
  exact walshTransform_ne_zero k hS.2.2.2

/-- The two-constructor cover on a carrier. -/
theorem hadamard_cover_of_isCarrier {S : KernelSumState n} (hS : IsCarrier S) (i : Fin n) :
    ((Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L
        ∧ amp (applyHFiner i S) = walshTransform i (amp S))
      ∨ ∃ u : Fin n → ZMod 2, u i = 0 ∧ (∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
          ∧ amp (hRaise i u S) = walshTransform i (amp S) :=
  hadamard_cover S hS.2.1 hS.2.2.1 hS.1 i

/-! ## The pinned rule -/

/-- **Carrier closure for `applyHPinned`.** The pinned rule sends carriers to carriers, under the
hypothesis `hqfree` that the exponent is free of the pinned bit. -/
theorem isCarrier_applyHPinned (i : Fin n) {K : KernelState n}
    (hK : IsCarrier (ofKernelState K)) (hpin : ∀ p ∈ K.L, p.X i = 0)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval K.q (Function.update w i b) = DiagPhase.eval K.q w) :
    IsCarrier (ofKernelState (applyHPinned i K)) := by
  refine ⟨hK.1, isStabilizer_map_pauliSwapOn i hK.2.1,
    coisotropic_map_pauliSwapOn i hK.2.1 (finrank_eq_of_isCarrier hK), ?_⟩
  rw [amp_ofKernelState_applyHPinned i K hK.2.2.1 hpin hqfree hK.1]
  exact walshTransform_ne_zero i hK.2.2.2

/-- **Floor closure for `applyHPinned`.** The pinned rule sends floor records to floor records. -/
theorem isFloor_applyHPinned (i : Fin n) {K : KernelState n}
    (hK : IsFloor (ofKernelState K)) (hpin : ∀ p ∈ K.L, p.X i = 0)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval K.q (Function.update w i b) = DiagPhase.eval K.q w) :
    IsFloor (ofKernelState (applyHPinned i K)) := by
  refine ⟨isCarrier_applyHPinned i hK.1 hpin hqfree, ?_⟩
  rw [amp_ofKernelState_applyHPinned i K hK.1.2.2.1 hpin hqfree hK.1.1]
  exact stabilizedBy_map_pauliSwapOn_walshTransform i hK.2

end FTQCLib.Frame.Walkthrough

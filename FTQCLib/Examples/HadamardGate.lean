/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.RegisterWalkthrough

/-! # The Hadamard as an executable table gate — the two dyadic modes

`RegisterWalkthrough` has H only as the symplectic rotation of `L` (`applyClifford (pauliSwapOn S)`),
which is faithful only for zero-offset, sign-free states. This file upgrades H to a **real executable**
on the `KernelState` table, like the diagonal gates: a state-transformer touching all five fields.

The design, from the four H runs: H at bit `i` is ONE symplectic move (the X↔Z swap at `i` on `L`)
plus an exchange of the dyadic sign `2^{m−1}·ε·Xᵢ` between the `x₀` row and the `q` row:

* **`applyHPinned i`** (pinned → free): frees a Z-definite bit; the bit's value `x₀ i` leaves the
  offset and is **emitted into `q` as the sign** `2^{m−1}·(x₀ i)·Xᵢ`; `c ↦ c/√2`.
* **`applyHFree i ε`** (free → pinned): recollapses an X-free bit whose `q`-coefficient at `Xᵢ` is the
  constant dyadic sign `2^{m−1}·ε`; the sign is **absorbed back into the offset** (`x₀ i ↦ ε`);
  `c ↦ √2·c`.

Coherence: the two modes are mutually inverse (`applyH_roundTrip`, `applyH_roundTrip'`) — H² = id on
the table, with the sign cancellation being exactly `2^{m−1} + 2^{m−1} = 2^m ≡ 0`.

Boundary (not built here, by design): the *linear* recollapse (coefficient `2^{m−1}·ℓ(x)`, which pins a
relation into `L` — graph state → Bell), and the odd-coefficient case, which provably has **no** table
output (non-uniform amplitudes — the metaplectic wall). The Hilbert certificate (`psi`-level: that these
updates ARE the Hadamard) belongs next to `FrameConditioning`, not here — this file stays pure frame. -/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy

variable {n : ℕ}

/-! ## The dyadic sign polynomial -/

/-- The sign H exchanges with the register: `2^{m−1}·ε` on `Xᵢ` — the π-phase `(−1)^{xᵢ}` when `ε = 1`,
nothing when `ε = 0`. At `m = 1` this is `ε·Xᵢ`; at `m = 3` it is `4ε·Xᵢ` (the `{0,4}` condition of the
runs). -/
noncomputable def hSignPoly (i : Fin n) (ε : ZMod 2) (m : ℕ) : DiagPhase n m :=
  ((ε.val : ZMod (2 ^ m)) * 2 ^ (m - 1)) • MvPolynomial.X i

/-- The dyadic sign is 2-torsion: emitting it twice is emitting nothing —
`2^{m−1} + 2^{m−1} = 2^m ≡ 0`. This is the algebra behind `H² = id`. -/
theorem hSignPoly_add_self (i : Fin n) (ε : ZMod 2) (m : ℕ) :
    hSignPoly i ε m + hSignPoly i ε m = 0 := by
  have key : (2 ^ (m - 1) + 2 ^ (m - 1) : ZMod (2 ^ m)) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      haveI : Subsingleton (ZMod (2 ^ 0)) := by
        rw [pow_zero]; exact inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    · have h2 : (2 ^ (m - 1) + 2 ^ (m - 1) : ZMod (2 ^ m)) = 2 ^ m := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      have h0 : ((2 ^ m : ℕ) : ZMod (2 ^ m)) = 0 := ZMod.natCast_self _
      rw [Nat.cast_pow, Nat.cast_ofNat] at h0
      rw [h2, h0]
  unfold hSignPoly
  rw [← add_smul, ← mul_add, key, mul_zero, zero_smul]

/-! ## The swap at one bit is an involution -/

/-- `pauliSwapOn S` is a pointwise involution. -/
@[simp] theorem pauliSwapOn_pauliSwapOn (S : Finset (Fin n)) (p : Pauli n) :
    pauliSwapOn S (pauliSwapOn S p) = p := by
  ext j <;> by_cases hj : j ∈ S <;> simp [hj]

/-- Mapping a subspace through the swap twice returns it. -/
@[simp] theorem map_pauliSwapOn_map (S : Finset (Fin n)) (L : Submodule (ZMod 2) (Pauli n)) :
    Submodule.map (pauliSwapOn S) (Submodule.map (pauliSwapOn S) L) = L := by
  rw [← Submodule.map_comp]
  have hid : (pauliSwapOn S).comp (pauliSwapOn S) = LinearMap.id := by
    apply LinearMap.ext
    intro p
    simp
  rw [hid, Submodule.map_id]

/-! ## The gate, both modes -/

/-- **H at a pinned bit** (pinned → free). The bit's definite value leaves the offset and enters `q` as
the dyadic sign; `L` rotates by the swap at `i`; `c` halves in norm. Faithful when bit `i` is Z-definite
in `L` and `q` does not involve `Xᵢ` — the hypotheses of the theorems, not the definition (as with
`applyDiagFrom0`). -/
noncomputable def applyHPinned (i : Fin n) (K : KernelState n) : KernelState n where
  m  := K.m
  q  := K.q + hSignPoly i (K.x₀ i) K.m
  c  := K.c / (Real.sqrt 2 : ℂ)
  L  := Submodule.map (pauliSwapOn {i}) K.L
  x₀ := Function.update K.x₀ i 0

/-- **H at a free bit, constant recollapse** (free → pinned). Absorbs the dyadic sign `2^{m−1}·ε·Xᵢ`
from `q` back into the offset: the bit pins to `ε`. Faithful when bit `i` is X-free in `L`, the offset
at `i` is `0`, and `q = q' + hSignPoly i ε` with `q'` free of `Xᵢ`. -/
noncomputable def applyHFree (i : Fin n) (ε : ZMod 2) (K : KernelState n) : KernelState n where
  m  := K.m
  q  := K.q + hSignPoly i ε K.m
  c  := (Real.sqrt 2 : ℂ) * K.c
  L  := Submodule.map (pauliSwapOn {i}) K.L
  x₀ := Function.update K.x₀ i ε

/-! ## Coherence: the two modes are mutually inverse (H² = id on the table) -/

private theorem sqrt_two_ne_zero' : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- **Round trip, pinned side:** free the bit, then recollapse onto its original value — the identity.
All five fields return: the sign cancels by 2-torsion, `L` by the swap involution, `c` by `√2·(c/√2)`. -/
theorem applyH_roundTrip (i : Fin n) (K : KernelState n) :
    applyHFree i (K.x₀ i) (applyHPinned i K) = K := by
  obtain ⟨m, q, c, L, x₀⟩ := K
  unfold applyHFree applyHPinned
  simp only [KernelState.mk.injEq, heq_eq_eq, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [add_assoc, hSignPoly_add_self, add_zero]
  · rw [mul_comm, div_mul_cancel₀ _ sqrt_two_ne_zero']
  · exact map_pauliSwapOn_map _ _
  · rw [Function.update_idem, Function.update_eq_self]

/-- **Round trip, free side:** recollapse onto `ε`, then free again — the identity, given the free bit's
offset was `0` (its gauge value on a free direction). -/
theorem applyH_roundTrip' (i : Fin n) (ε : ZMod 2) (K : KernelState n) (h : K.x₀ i = 0) :
    applyHPinned i (applyHFree i ε K) = K := by
  obtain ⟨m, q, c, L, x₀⟩ := K
  change x₀ i = 0 at h
  unfold applyHFree applyHPinned
  simp only [KernelState.mk.injEq, heq_eq_eq, true_and, Function.update_self]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [add_assoc, hSignPoly_add_self, add_zero]
  · rw [mul_comm, mul_div_assoc, div_self sqrt_two_ne_zero', mul_one]
  · exact map_pauliSwapOn_map _ _
  · rw [Function.update_idem, ← h, Function.update_eq_self]

/-! ## The runs, as executed gate applications

Run A/B on an arbitrary classical register: H frees bit `i`, the value `v i` is emitted as the sign
(`= 0` for run A — nothing appears; `= Xᵢ` for run B). Then the round trip restores the register. -/

/-- Executing H on bit `i` of the classical register `v`: `L` rotates to the mixed Lagrangian. -/
theorem applyHPinned_classical_L (i : Fin n) (v : Fin n → ZMod 2) :
    (applyHPinned i (classical v)).L = Lmix {i} :=
  map_pauliSwapOn_Lz {i}

/-- Executing H on bit `i` of the classical register `v`: the emitted sign is exactly the bit's value —
`q` picks up the dyadic sign of `v i` (run A: `v i = 0` → nothing; run B: `v i = 1` → the sign `Xᵢ`). -/
theorem applyHPinned_classical_q (i : Fin n) (v : Fin n → ZMod 2) :
    (applyHPinned i (classical v)).q = hSignPoly i (v i) 1 := by
  show (0 : DiagPhase n 1) + hSignPoly i (v i) 1 = hSignPoly i (v i) 1
  exact zero_add _

/-- Run A as a corollary: H on a bit holding `0` emits no sign. -/
theorem applyHPinned_classical_q_zero (i : Fin n) (v : Fin n → ZMod 2) (h : v i = 0) :
    (applyHPinned i (classical v)).q = 0 := by
  rw [applyHPinned_classical_q, h]
  unfold hSignPoly
  norm_num [show ((0 : ZMod 2)).val = 0 from rfl]
  rfl

/-- Run B as a corollary: H on a bit holding `1` emits the sign `Xᵢ` — the register bit has moved from
the `x₀` row to the `q` row. -/
theorem applyHPinned_classical_q_one (i : Fin n) (v : Fin n → ZMod 2) (h : v i = 1) :
    (applyHPinned i (classical v)).q = MvPolynomial.X i := by
  rw [applyHPinned_classical_q, h]
  unfold hSignPoly
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]
  rfl

/-- The offset after H: bit `i` cleared, the rest untouched. -/
theorem applyHPinned_classical_x₀ (i : Fin n) (v : Fin n → ZMod 2) :
    (applyHPinned i (classical v)).x₀ = Function.update v i 0 := rfl

/-- **Run B round trip on the register:** H then H restores the classical register exactly —
value out of `x₀` into the sign, sign back into `x₀`. -/
theorem applyH_classical_roundTrip (i : Fin n) (v : Fin n → ZMod 2) :
    applyHFree i (v i) (applyHPinned i (classical v)) = classical v :=
  applyH_roundTrip i (classical v)

/-! ## Axiom check -/

#print axioms hSignPoly_add_self
#print axioms map_pauliSwapOn_map
#print axioms applyH_roundTrip
#print axioms applyH_roundTrip'
#print axioms applyHPinned_classical_L
#print axioms applyHPinned_classical_q
#print axioms applyHPinned_classical_q_one
#print axioms applyH_classical_roundTrip

end FTQCLib.Frame.Walkthrough

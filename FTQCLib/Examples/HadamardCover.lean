/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardAmplitude

/-!
# The Hadamard, total: the covering theorem at amplitude level

The statement is one sentence: for every representable `KernelSumState` and every bit `i`,
the test `e_i ∈ π_X(L)` assigns exactly one constructor — `applyHFiner` in, `hRaise` out — and
the assigned constructor's output satisfies `amp (output) = walshTransform i (amp S)`. The support
half of the dichotomy is `FTQCLib/Examples/HadamardTotality.lean`, the amplitude half of `hRaise` is
`FTQCLib/Examples/HadamardAmplitude.lean`; this file supplies the amplitude half of `applyHFiner` and
assembles the covering theorem.

`applyHFiner`'s amplitude half is the frame-native restatement of `F_applyHFiner`
(`FTQCLib/Hilbert/CharSumCorrespondence.lean`) against the Walsh referee, and it is a transport with
no Hilbert content: the raw character sum already equals the Walsh transform of the raw amplitude
(`ampCore_applyHFiner_eq_walsh`, `FTQCLib/Examples/CharSumPairing.lean`), and when the Hadamarded
bit is X-supported both Walsh branches of a word sit on the input support together
(`branch_pair`), so the support indicator passes through both terms unchanged. Contrast `hRaise`,
where exactly one branch survives and the sum collapses.

With both constructors certified against the same referee, `H² = id` on the carrier follows from
the referee's involutivity alone, through either constructor and through the mixed round trip
raise-then-free — the overlap consistency of the two constructors, as transitivity of `=`.

Everything here is frame-pure: no `FTQCLib.Hilbert`.

**Relation to the floor eliminators.** `hadamard_floor_total` in
`FTQCLib/Examples/HadamardElimination.lean` refines `hadamard_total` on height-zero floors: the
`applyHFiner` branch is followed by the eliminating step, so the output is again a height-zero
floor; at a residual pair no height-zero record presents the output
(`FTQCLib/Examples/ResidualBit.lean`).

## Main definitions

None. The constructors and the referee are upstream.

## Main results

* `amp_applyHFiner` — `applyHFiner` is the Walsh transform on `amp` at an X-supported bit.
* `hadamard_cover`, `hadamard_cover_xor` — **the covering theorem**: every bit of every
  Lagrangian carrier state is handled by exactly one constructor, and that constructor computes
  the Walsh transform of the amplitude.
* `hadamard_total` — the existence form: for every state and bit there is an output state on the
  carrier whose amplitude is the Walsh transform, and it is one of the two constructors' outputs.
* `amp_applyHFiner_hRaise`, `amp_applyHFiner_applyHFiner` — `H² = id` on the carrier, through
  the mixed round trip and through the free constructor twice.

## Implementation notes

* `applyHFiner` changes neither `L` nor `x₀`, so its output support is the input support by
  `rfl`; the only support fact the amplitude half needs is that flipping an X-supported bit
  preserves support membership (`mem_support_update_iff`), which is `branch_pair` in the coset
  form `amp` speaks.
* `hadamard_cover` takes isotropy as well as co-isotropy because representer *existence*
  (`exists_representer`) uses it; the two amplitude theorems it assembles do not. The covering
  theorem is therefore stated for Lagrangian carriers, the target class, while
  each constructor's own certificate is stated at its weakest hypotheses.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## Flipping an X-supported bit preserves support membership -/

/-- A Walsh branch of `w` is `w` plus a multiple of `e_k`, the multiple recording the flip. -/
theorem update_eq_add_smul_single (w : Fin n → ZMod 2) (k : Fin n) (b : ZMod 2) :
    Function.update w k b = w + (b + w k) • (Pi.single k 1 : Fin n → ZMod 2) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    exact (show ∀ a c : ZMod 2, a = c + (a + c) * 1 by decide) b (w j)
  · simp only [Function.update_of_ne hj, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj,
      smul_eq_mul, mul_zero, add_zero]

/-- **Both branches or neither.** When `e_k` is in the X-shadow, a word is on the support coset
iff either of its Walsh branches at `k` is. This is `branch_pair` in the coset form `amp` uses. -/
theorem mem_support_update_iff (S : KernelSumState n) {k : Fin n}
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L)
    (w : Fin n → ZMod 2) (b : ZMod 2) :
    (∃ p ∈ S.L, Function.update w k b = S.x₀ + p.X) ↔ (∃ p ∈ S.L, w = S.x₀ + p.X) := by
  rw [mem_support_iff, mem_support_iff, update_eq_add_smul_single,
    show w + (b + w k) • (Pi.single k 1 : Fin n → ZMod 2) - S.x₀
      = (w - S.x₀) + (b + w k) • (Pi.single k 1 : Fin n → ZMod 2) from by abel]
  exact Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hk)

/-! ## The amplitude half of `applyHFiner` -/

/-- **`applyHFiner` is the Walsh transform on the support-restricted amplitude.** At an
X-supported bit (`e_k ∈ π_X(L)`) and `1 ≤ m`: `amp (applyHFiner k S) = walshTransform k (amp S)`.
The frame-native restatement of `F_applyHFiner`, with `hadamardGate` replaced by the referee:
the raw identity is `ampCore_applyHFiner_eq_walsh`, and `mem_support_update_iff` carries the
support indicator through both Walsh branches. -/
theorem amp_applyHFiner (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m)
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L) :
    amp (applyHFiner k S) = walshTransform k (amp S) := by
  funext w
  have hL : ∀ v : Fin n → ZMod 2,
      (∃ p ∈ (applyHFiner k S).L, v = (applyHFiner k S).x₀ + p.X)
        ↔ (∃ p ∈ S.L, v = S.x₀ + p.X) := fun _ => Iff.rfl
  by_cases hw : ∃ p ∈ S.L, w = S.x₀ + p.X
  · rw [amp_pos ((hL w).mpr hw), ampCore_applyHFiner_eq_walsh k S hm w]
    unfold walshTransform
    simp only [amp_pos ((mem_support_update_iff S hk w 0).mpr hw),
      amp_pos ((mem_support_update_iff S hk w 1).mpr hw)]
  · rw [amp_neg (fun h => hw ((hL w).mp h))]
    unfold walshTransform
    simp only [amp_neg (fun h => hw ((mem_support_update_iff S hk w 0).mp h)),
      amp_neg (fun h => hw ((mem_support_update_iff S hk w 1).mp h)), mul_zero, add_zero]

/-! ## The covering theorem -/

/-- **The Hadamard, total.** For every Lagrangian carrier state at `1 ≤ m` and every bit `i`:
either `e_i` is in the shadow and `applyHFiner` computes the Walsh transform, or some
representer exists and `hRaise` with it computes the Walsh transform. -/
theorem hadamard_cover (S : KernelSumState n) (hS : IsStabilizer S.L)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (hm : 1 ≤ S.m) (i : Fin n) :
    ((Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L
        ∧ amp (applyHFiner i S) = walshTransform i (amp S))
      ∨ ∃ u : Fin n → ZMod 2, u i = 0 ∧ (∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
          ∧ amp (hRaise i u S) = walshTransform i (amp S) := by
  by_cases hi : (Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L
  · exact Or.inl ⟨hi, amp_applyHFiner i S hm hi⟩
  · obtain ⟨u, hui, hrep⟩ := exists_representer hS horth hi
    exact Or.inr ⟨u, hui, hrep, amp_hRaise i u S horth hui hrep hm⟩

/-- **The covering theorem, exclusive.** The two cases of `hadamard_cover` are an exclusive-or:
the assignment is total *and* unique, through the data itself (`hadamard_dichotomy`). -/
theorem hadamard_cover_xor (S : KernelSumState n) (hS : IsStabilizer S.L)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (hm : 1 ≤ S.m) (i : Fin n) :
    Xor' ((Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L
        ∧ amp (applyHFiner i S) = walshTransform i (amp S))
      (∃ u : Fin n → ZMod 2, u i = 0 ∧ (∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i)
          ∧ amp (hRaise i u S) = walshTransform i (amp S)) := by
  rcases hadamard_dichotomy hS horth i with ⟨hi, hno⟩ | ⟨⟨u, hui, hrep⟩, hi⟩
  · exact Or.inl ⟨⟨hi, amp_applyHFiner i S hm hi⟩,
      fun ⟨u, hui, hrep, _⟩ => hno ⟨u, hui, hrep⟩⟩
  · exact Or.inr ⟨⟨u, hui, hrep, amp_hRaise i u S horth hui hrep hm⟩, fun ⟨hi', _⟩ => hi hi'⟩

/-- **The existence form.** For every Lagrangian carrier state and every bit there is an output
state on the carrier whose amplitude is the Walsh transform of the input's, and it is the output
of one of the two constructors. -/
theorem hadamard_total (S : KernelSumState n) (hS : IsStabilizer S.L)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L) (hm : 1 ≤ S.m) (i : Fin n) :
    ∃ S' : KernelSumState n, amp S' = walshTransform i (amp S)
      ∧ (S' = applyHFiner i S ∨ ∃ u : Fin n → ZMod 2, S' = hRaise i u S) := by
  rcases hadamard_cover S hS horth hm i with ⟨_, h⟩ | ⟨u, _, _, h⟩
  · exact ⟨applyHFiner i S, h, Or.inl rfl⟩
  · exact ⟨hRaise i u S, h, Or.inr ⟨u, rfl⟩⟩

/-! ## `H² = id` on the carrier -/

/-- **The mixed round trip.** After `hRaise` the raised bit is X-supported, so the second `H` is
`applyHFiner`; the composite is the identity on `amp`, by the referee's involutivity alone. -/
theorem amp_applyHFiner_hRaise (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n)
    (horth : LinearMap.BilinForm.orthogonal omegaBilin S.L ≤ S.L)
    (hui : u i = 0) (hrep : ∀ v ∈ Submodule.map xProj S.L, dotF2 u v = v i) (hm : 1 ≤ S.m) :
    amp (applyHFiner i (hRaise i u S)) = amp S := by
  have hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj S.L :=
    notMem_shadow_of_representer hui hrep
  have hk : (Pi.single i 1 : Fin n → ZMod 2) ∈ Submodule.map xProj (hRaise i u S).L := by
    rw [hRaise_L]
    exact single_mem_shadow_swap horth hi
  rw [amp_applyHFiner i (hRaise i u S) hm hk, amp_hRaise i u S horth hui hrep hm]
  exact walshTransform_involutive i (amp S)

/-- **The free round trip.** `applyHFiner` twice at an X-supported bit is the identity on `amp`;
the carrier grows by two summation variables and the denotation does not move. -/
theorem amp_applyHFiner_applyHFiner (k : Fin n) (S : KernelSumState n) (hm : 1 ≤ S.m)
    (hk : (Pi.single k 1 : Fin n → ZMod 2) ∈ Submodule.map xProj S.L) :
    amp (applyHFiner k (applyHFiner k S)) = amp S := by
  rw [amp_applyHFiner k (applyHFiner k S) hm hk, amp_applyHFiner k S hm hk]
  exact walshTransform_involutive k (amp S)

/-! ## The witnesses -/

/-- The mixed round trip on the Bell state: raise bit `0`, then free it; the amplitude returns.
Every hypothesis discharged on `bellL`. -/
theorem amp_applyHFiner_hRaise_bell :
    amp (applyHFiner 0 (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellState)) = amp bellState :=
  amp_applyHFiner_hRaise 0 ![0, 1] bellState bellL_coisotropic bellL_representer.1
    bellL_representer.2 le_rfl

/-- The covering theorem on the odd-parity state at `m = 2`, bit `0`: it lands in the `hRaise`
case with the representer `![0,1,1]`, every hypothesis discharged on `sParityL`. -/
theorem hadamard_cover_sParity :
    ∃ u : Fin 3 → ZMod 2, u 0 = 0 ∧ (∀ v ∈ Submodule.map xProj sParityState.L, dotF2 u v = v 0)
      ∧ amp (hRaise 0 u sParityState) = walshTransform 0 (amp sParityState) :=
  ⟨![0, 1, 1], sParityL_representer.1, sParityL_representer.2, amp_hRaise_sParity⟩

end FTQCLib.Frame.Walkthrough

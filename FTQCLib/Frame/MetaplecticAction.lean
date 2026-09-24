/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Pauli.Cocycle
import FTQCLib.Gates.Clifford
import FTQCLib.Gates.Transvection
import FTQCLib.Hierarchy.FloorEquivalence
import FTQCLib.Stabilizer.GottesmanKnill

/-! # A frame-pure metaplectic action on `(L,χ)`

The conjugation-sign action of a symplectic map on the signed Lagrangian chart, built
**frame-purely** (no `FTQCLib.Hilbert`). The sign cochain a symplectic `T` must carry is a `ZMod 4`
quadratic refinement of the *distortion* `Δ_T(a,b) = betaFrame (T a) (T b) − betaFrame a b`. This
file builds that distortion and its structural lemmas, and the actions of the generators: the Pauli
(translation) action, and the single-qubit `Z_k`-, `X_k`- and `Y_k`-transvection actions (`S`, `√X`,
`H`), each validated by the quadratic cochain `tvSignZ`. It also shows that a weight-2 (entangling)
transvection admits no quadratic cochain (its cubic cochain is in
`FTQCLib.Frame.EntanglingGate`).

The composition coherence (the metaplectic 2-cocycle and the non-split obstruction; see
`FTQCLib.Cohomology.Metaplectic`) is not built here. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Pauli FTQCLib.Gates

variable {n : ℕ}

/-- `zDot` cast to `ZMod 4` is the pointwise product sum. -/
theorem zDot_cast_four (p : Pauli n) (v : Fin n → ZMod 2) :
    ((zDot p v : ℕ) : ZMod 4) = ∑ i, ((p.Z i).val : ZMod 4) * ((v i).val : ZMod 4) := by
  unfold zDot
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [Nat.cast_mul])

/-- **`betaFrame` as a single pointwise `ZMod 4` sum** over the qubits. The foundation for
localizing a single-qubit gate: a transvection touching only position `k` changes only the
`k`-summand. -/
theorem betaFrame_sum (p q : Pauli n) :
    betaFrame p q = ∑ i,
      (((p.Z i).val : ZMod 4) * ((p.X i).val)
        + ((q.Z i).val) * ((q.X i).val)
        + (((p + q).Z i).val) * (((p + q).X i).val)
        + 2 * (((q.Z i).val) * ((p.X i).val)
              + (((p + q).Z i).val) * (((p + q).X i).val))) := by
  unfold betaFrame yWeight
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [zDot_cast_four p p.X, zDot_cast_four q q.X, zDot_cast_four (p + q) (p + q).X,
    zDot_cast_four q p.X]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **The symplectic distortion of the frame cocycle.**
`Δ_T(a,b) = betaFrame (T a) (T b) − betaFrame a b` measures how `T` distorts the Pauli cocycle.
A sign cochain `c_T` carried by a symplectic `T` on `(L,χ)` must quadratically refine it. -/
def frameDistortion (T : Pauli n ≃ₗ[ZMod 2] Pauli n) (a b : Pauli n) : ZMod 4 :=
  betaFrame (T a) (T b) - betaFrame a b

/-- **The distortion is symmetric for symplectic `T`.** The `betaFrame` swap-corrections
`2·ω(Ta,Tb)`, `2·ω(a,b)` cancel because a symplectic map preserves `ω` — no isotropy needed. So
`Δ_T` is a genuine symmetric `ZMod 4` form, ready to be quadratically refined. -/
theorem frameDistortion_swap {T : Pauli n ≃ₗ[ZMod 2] Pauli n} (hT : IsClifford T) (a b : Pauli n) :
    frameDistortion T b a = frameDistortion T a b := by
  have hω : omega (T a) (T b) = omega a b := by
    have h := hT a b; rwa [omegaBilin_apply, omegaBilin_apply] at h
  unfold frameDistortion
  rw [betaFrame_swap (T a) (T b), betaFrame_swap a b, hω]
  ring

/-- **The distortion vanishes on the diagonal** (`betaFrame_self`). With `frameDistortion_swap`,
this is what `quadRefine` of `Δ_T` needs: a symmetric form, zero diagonal, so `c_T` has no linear
self-term (`v = 0`) — the sign cochain is the pure quadratic (Arf-layer) piece. -/
@[simp] theorem frameDistortion_self (T : Pauli n ≃ₗ[ZMod 2] Pauli n) (a : Pauli n) :
    frameDistortion T a a = 0 := by
  unfold frameDistortion
  rw [betaFrame_self, betaFrame_self, sub_zero]

/-- **`betaFrame` is NOT bi-additive on an isotropic triple** (a decisive `n = 3` counterexample:
`betaFrame (a+a') b = 0` but `betaFrame a b + betaFrame a' b = 2`, all three pairwise `ω` zero).
So `frameDistortion` does **not** reconstruct as a bilinear double-sum over a Lagrangian, and the
`c_T = quadRefine(Δ_T)`-over-`L` route for a frame-native sign cochain is impossible: the
per-symplectic distortion is genuinely beyond quadratic (the cubic residual is metaplectic content).
A frame-native sign must instead be built over the support coordinates `π_X(L)` (the `encodeE`
route), where the amplitude *is* quadratic. (A `quadRefine` would force a bilinear polarization.) -/
theorem betaFrame_not_biadditive_on_isotropic :
    ∃ a a' b : Pauli 3, omega a a' = 0 ∧ omega a b = 0 ∧ omega a' b = 0 ∧
      betaFrame (a + a') b ≠ betaFrame a b + betaFrame a' b :=
  ⟨⟨![1, 1, 0], ![0, 0, 1]⟩, ⟨![1, 1, 0], ![1, 1, 1]⟩, ⟨![1, 1, 1], ![1, 0, 0]⟩,
    by decide, by decide, by decide, by decide⟩

open Classical in
/-- **The frame-pure `V` (Pauli/translation) action.** Conjugation by a Pauli `r` fixes the
Lagrangian and flips the sign of every stabilizer anticommuting with `r`: `χ ↦ χ + 2·ω(r,·)` on `L`,
`0` off `L`. The sign cochain is *linear* (`2·ω(r,·)`), the easy splitting part of the
affine-symplectic `V ⋊ Sp` — the frame-native action of the translation generators, validated
directly. -/
noncomputable def framePauliAction (r : Pauli n) (S : FramePureSignedStab n) :
    FramePureSignedStab n where
  toFrameSignedStab :=
    { L := S.L
      chi := fun p => if p ∈ S.L then S.chi p + 2 * ((omega r p).val : ZMod 4) else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), S.chi_zero,
          show omega r 0 = 0 by rw [← omegaBilin_apply, map_zero]]
        simp
      valid := by
        intro p hp q hq
        have hpq : p + q ∈ S.L := S.L.add_mem hp hq
        have hω : omega r (p + q) = omega r p + omega r q := by
          rw [← omegaBilin_apply, ← omegaBilin_apply, ← omegaBilin_apply, map_add]
        simp only [if_pos hp, if_pos hq, if_pos hpq]
        rw [hω, two_val_add, S.valid p hp q hq]
        ring }
  isStab := S.isStab
  full := S.full
  tight := fun p hp => if_neg hp

/-- `ω(Z_k, a) = a.X_k`: the `Z_k`-transvection's amount is the `X`-bit at `k`. -/
theorem omega_pauliz (k : Fin n) (a : Pauli n) : omega (pauliz k) a = a.X k := by
  unfold omega
  have h1 : ∑ i, (pauliz k).Z i * a.X i = a.X k := by
    simp only [pauliz, Pi.single_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ k (fun i => a.X i)]
    simp
  have h2 : ∑ i, (pauliz k).X i * a.Z i = 0 := by simp [pauliz]
  rw [h1, h2, add_zero]

/-- The `Z_k`-transvection in closed form: `τ a = a + (a.X_k)·Z_k` (it only touches `Z` at `k`). -/
theorem tvZ_apply (k : Fin n) (a : Pauli n) :
    transvectionEquiv (pauliz k) a = a + (a.X k) • pauliz k := by
  rw [transvectionEquiv_apply, omega_pauliz]

/-- The transvection leaves the `X`-coordinates fixed. -/
@[simp] theorem tvZ_X_apply (k : Fin n) (a : Pauli n) (j : Fin n) :
    (transvectionEquiv (pauliz k) a).X j = a.X j := by
  rw [tvZ_apply, X_add, X_smul, show (pauliz k).X = 0 from rfl]
  simp

/-- The transvection adds `a.X_k` to the `Z`-coordinate at `k` only. -/
@[simp] theorem tvZ_Z_apply (k : Fin n) (a : Pauli n) (j : Fin n) :
    (transvectionEquiv (pauliz k) a).Z j
      = a.Z j + (a.X k) * (Pi.single k 1 : Fin n → ZMod 2) j := by
  rw [tvZ_apply, Z_add, Z_smul, show (pauliz k).Z = (Pi.single k 1 : Fin n → ZMod 2) from rfl,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **The `Z_k`-transvection distortion is an explicit bilinear form** (general `n`). The
transvection touches only `Z` at `k`, so `betaFrame` localizes: off-`k` qubits cancel, the `k` gives
`2·(a.X_k·b.Z_k + b.X_k·a.Z_k)`. This is the second difference of the sign cochain
`c(p) = 2·p.X_k·p.Z_k`, so the single-qubit transvection action on `(L,χ)` is valid. -/
theorem frameDistortion_transvectionZ (k : Fin n) (a b : Pauli n) :
    frameDistortion (transvectionEquiv (pauliz k)) a b
      = 2 * (((a.X k).val * (b.Z k).val + (b.X k).val * (a.Z k).val : ℕ) : ZMod 4) := by
  unfold frameDistortion
  rw [betaFrame_sum, betaFrame_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single k]
  · -- the k-term, reduced to the four bits at k
    simp only [tvZ_X_apply, tvZ_Z_apply, X_add, Z_add, Pi.add_apply, Pi.single_eq_same, mul_one]
    have hax := a.X k; have haz := a.Z k; have hbx := b.X k; have hbz := b.Z k
    revert hax haz hbx hbz
    generalize a.X k = ax; generalize a.Z k = az; generalize b.X k = bx; generalize b.Z k = bz
    intro hax haz hbx hbz
    revert ax az bx bz
    decide
  · -- off-k qubits: the transvection does not touch them, so the summand difference is zero
    intro j _ hjk
    simp only [tvZ_X_apply, tvZ_Z_apply, X_add, Z_add, Pi.add_apply,
      Pi.single_eq_of_ne hjk, mul_zero, add_zero]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The `Z_k`-transvection is an involution. -/
theorem tvZ_invol (k : Fin n) (x : Pauli n) :
    transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) x) = x := by
  have h := LinearMap.congr_fun (transvectionLin_involutive (pauliz k)) x
  simpa [transvectionEquiv, LinearEquiv.ofLinear_apply] using h

/-- The single-qubit transvection sign cochain `c(r) = 2·r.X_k·r.Z_k` (`+1` on `X_k`/`Z_k`, `−1`
on `Y_k`), a `ZMod 4` quadratic form whose second difference is `frameDistortion_transvectionZ`. -/
def tvSignZ (k : Fin n) (r : Pauli n) : ZMod 4 :=
  2 * (((r.X k).val * (r.Z k).val : ℕ) : ZMod 4)

/-- **The sign cochain's second difference is exactly the transvection distortion.** This is the
validity identity for the `Z_k`-transvection action: with `S.valid` it makes the transported
character valid. Both sides depend only on the four bits at `k`, so a `16`-case `decide` after
reducing the transvection's components. -/
theorem tvSign_validity (k : Fin n) (p q : Pauli n) :
    tvSignZ k (transvectionEquiv (pauliz k) p) + tvSignZ k (transvectionEquiv (pauliz k) q)
      - tvSignZ k (transvectionEquiv (pauliz k) (p + q))
      = betaFrame (transvectionEquiv (pauliz k) p) (transvectionEquiv (pauliz k) q)
        - betaFrame p q := by
  have hfd := frameDistortion_transvectionZ k p q
  unfold frameDistortion at hfd
  rw [hfd, map_add]
  unfold tvSignZ
  simp only [tvZ_X_apply, tvZ_Z_apply, X_add, Z_add, Pi.add_apply, Pi.single_eq_same, mul_one]
  generalize p.X k = px; generalize p.Z k = pz; generalize q.X k = qx; generalize q.Z k = qz
  revert px pz qx qz
  decide

open Classical in
/-- **The frame-pure `Z_k`-transvection action on `(L,χ)`** (the `S = τ_{Z_k}` gate, generalizing to
`H`/`√X` by the `X`/`Y` transvections). The Lagrangian moves by the symplectic transvection
(`clifford_preserves_isStabilizer`/`_finrank`), and the character transports as `χ ↦ χ∘τ + c∘τ` with
the sign cochain `c = tvSignZ`. Validity is `S.valid` plus `tvSign_validity`. Fully frame-pure: no
Hilbert, no metaplectic 2-cocycle — a single generator's distortion is bilinear, so the action is a
genuine `(L,χ)`-endomorphism. -/
noncomputable def frameTransvectionZAction (k : Fin n) (S : FramePureSignedStab n) :
    FramePureSignedStab n where
  toFrameSignedStab :=
    { L := S.L.map (transvectionEquiv (pauliz k)).toLinearMap
      chi := fun p =>
        if p ∈ S.L.map (transvectionEquiv (pauliz k)).toLinearMap
        then S.chi (transvectionEquiv (pauliz k) p) + tvSignZ k (transvectionEquiv (pauliz k) p)
        else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), map_zero, S.chi_zero, zero_add]
        unfold tvSignZ; simp
      valid := by
        intro p hp q hq
        have hτp : transvectionEquiv (pauliz k) p ∈ S.L := by
          obtain ⟨p₀, hp₀, hep₀⟩ := Submodule.mem_map.mp hp
          rw [← hep₀]
          change transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) p₀) ∈ S.L
          rw [tvZ_invol]; exact hp₀
        have hτq : transvectionEquiv (pauliz k) q ∈ S.L := by
          obtain ⟨q₀, hq₀, heq₀⟩ := Submodule.mem_map.mp hq
          rw [← heq₀]
          change transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) q₀) ∈ S.L
          rw [tvZ_invol]; exact hq₀
        have hpq : p + q ∈ S.L.map (transvectionEquiv (pauliz k)).toLinearMap :=
          Submodule.add_mem _ hp hq
        simp only [if_pos hp, if_pos hq, if_pos hpq, map_add]
        rw [S.valid _ hτp _ hτq]
        have hval := tvSign_validity k p q
        rw [map_add] at hval
        linear_combination -hval }
  isStab := FTQCLib.Stabilizer.clifford_preserves_isStabilizer S.isStab (transvectionEquiv_isClifford _)
  full := by
    rw [FTQCLib.Stabilizer.clifford_preserves_finrank S.L (transvectionEquiv (pauliz k))]
    exact S.full
  tight := fun p hp => if_neg hp

/-! ### The `X_k`-transvection action (the `√X = H·S·H` gate) -/

/-- The `X_k`-transvection in closed form: `τ a = a + (a.Z_k)·X_k` (it only touches `X` at `k`). -/
theorem tvX_apply (k : Fin n) (a : Pauli n) :
    transvectionEquiv (paulix k) a = a + (a.Z k) • paulix k := by
  rw [transvectionEquiv_apply, omega_paulix_left]

/-- The transvection leaves the `Z`-coordinates fixed. -/
@[simp] theorem tvX_Z_apply (k : Fin n) (a : Pauli n) (j : Fin n) :
    (transvectionEquiv (paulix k) a).Z j = a.Z j := by
  rw [tvX_apply, Z_add, Z_smul, show (paulix k).Z = 0 from rfl]
  simp

/-- The transvection adds `a.Z_k` to the `X`-coordinate at `k` only. -/
@[simp] theorem tvX_X_apply (k : Fin n) (a : Pauli n) (j : Fin n) :
    (transvectionEquiv (paulix k) a).X j
      = a.X j + (a.Z k) * (Pi.single k 1 : Fin n → ZMod 2) j := by
  rw [tvX_apply, X_add, X_smul, show (paulix k).X = (Pi.single k 1 : Fin n → ZMod 2) from rfl,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **The `X_k`-transvection distortion equals the `Z_k` one.** The `X`/`Z` roles swap, but the form
`2·(a.X_k·b.Z_k + b.X_k·a.Z_k)` is symmetric under that swap, so the same sign cochain `tvSignZ`
validates the `X_k` action. -/
theorem frameDistortion_transvectionX (k : Fin n) (a b : Pauli n) :
    frameDistortion (transvectionEquiv (paulix k)) a b
      = 2 * (((a.X k).val * (b.Z k).val + (b.X k).val * (a.Z k).val : ℕ) : ZMod 4) := by
  unfold frameDistortion
  rw [betaFrame_sum, betaFrame_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
  · simp only [tvX_X_apply, tvX_Z_apply, X_add, Z_add, Pi.add_apply, Pi.single_eq_same, mul_one]
    have hax := a.X k; have haz := a.Z k; have hbx := b.X k; have hbz := b.Z k
    revert hax haz hbx hbz
    generalize a.X k = ax; generalize a.Z k = az; generalize b.X k = bx; generalize b.Z k = bz
    intro hax haz hbx hbz
    revert ax az bx bz
    decide
  · intro j _ hjk
    simp only [tvX_X_apply, tvX_Z_apply, X_add, Z_add, Pi.add_apply,
      Pi.single_eq_of_ne hjk, mul_zero, add_zero]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The `X_k`-transvection is an involution. -/
theorem tvX_invol (k : Fin n) (x : Pauli n) :
    transvectionEquiv (paulix k) (transvectionEquiv (paulix k) x) = x := by
  have h := LinearMap.congr_fun (transvectionLin_involutive (paulix k)) x
  simpa [transvectionEquiv, LinearEquiv.ofLinear_apply] using h

/-- The sign cochain `tvSignZ` validates the `X_k`-transvection too (its second difference is the
`X_k` distortion). -/
theorem tvSign_validity_X (k : Fin n) (p q : Pauli n) :
    tvSignZ k (transvectionEquiv (paulix k) p) + tvSignZ k (transvectionEquiv (paulix k) q)
      - tvSignZ k (transvectionEquiv (paulix k) (p + q))
      = betaFrame (transvectionEquiv (paulix k) p) (transvectionEquiv (paulix k) q)
        - betaFrame p q := by
  have hfd := frameDistortion_transvectionX k p q
  unfold frameDistortion at hfd
  rw [hfd, map_add]
  unfold tvSignZ
  simp only [tvX_X_apply, tvX_Z_apply, X_add, Z_add, Pi.add_apply, Pi.single_eq_same, mul_one]
  generalize p.X k = px; generalize p.Z k = pz; generalize q.X k = qx; generalize q.Z k = qz
  revert px pz qx qz
  decide

open Classical in
/-- **The frame-pure `X_k`-transvection action on `(L,χ)`** (the `√X = H·S·H` gate). Same shape as
the `Z_k` action, reusing `tvSignZ` (the `X`/`Z` distortions coincide). Fully frame-pure. -/
noncomputable def frameTransvectionXAction (k : Fin n) (S : FramePureSignedStab n) :
    FramePureSignedStab n where
  toFrameSignedStab :=
    { L := S.L.map (transvectionEquiv (paulix k)).toLinearMap
      chi := fun p =>
        if p ∈ S.L.map (transvectionEquiv (paulix k)).toLinearMap
        then S.chi (transvectionEquiv (paulix k) p) + tvSignZ k (transvectionEquiv (paulix k) p)
        else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), map_zero, S.chi_zero, zero_add]
        unfold tvSignZ; simp
      valid := by
        intro p hp q hq
        have hτp : transvectionEquiv (paulix k) p ∈ S.L := by
          obtain ⟨p₀, hp₀, hep₀⟩ := Submodule.mem_map.mp hp
          rw [← hep₀]
          change transvectionEquiv (paulix k) (transvectionEquiv (paulix k) p₀) ∈ S.L
          rw [tvX_invol]; exact hp₀
        have hτq : transvectionEquiv (paulix k) q ∈ S.L := by
          obtain ⟨q₀, hq₀, heq₀⟩ := Submodule.mem_map.mp hq
          rw [← heq₀]
          change transvectionEquiv (paulix k) (transvectionEquiv (paulix k) q₀) ∈ S.L
          rw [tvX_invol]; exact hq₀
        have hpq : p + q ∈ S.L.map (transvectionEquiv (paulix k)).toLinearMap :=
          Submodule.add_mem _ hp hq
        simp only [if_pos hp, if_pos hq, if_pos hpq, map_add]
        rw [S.valid _ hτp _ hτq]
        have hval := tvSign_validity_X k p q
        rw [map_add] at hval
        linear_combination -hval }
  isStab := FTQCLib.Stabilizer.clifford_preserves_isStabilizer S.isStab (transvectionEquiv_isClifford _)
  full := by
    rw [FTQCLib.Stabilizer.clifford_preserves_finrank S.L (transvectionEquiv (paulix k))]
    exact S.full
  tight := fun p hp => if_neg hp

/-! ### The `Y_k`-transvection action (the Hadamard `H = τ_{X_k+Z_k}` gate) -/

/-- The `Y_k`-transvection in closed form: `τ a = a + (a.Z_k + a.X_k)·(X_k + Z_k)` (it swaps the
`X` and `Z` coordinates at `k`). -/
theorem tvY_apply (k : Fin n) (a : Pauli n) :
    transvectionEquiv (paulix k + pauliz k) a
      = a + (a.Z k + a.X k) • (paulix k + pauliz k) := by
  rw [transvectionEquiv_apply, omega_add_left, omega_paulix_left, omega_pauliz_left]

/-- The `Y_k`-transvection on the `X`-coordinate: adds `a.Z_k + a.X_k` at `k`. -/
@[simp] theorem tvY_X_apply (k : Fin n) (a : Pauli n) (j : Fin n) :
    (transvectionEquiv (paulix k + pauliz k) a).X j
      = a.X j + (a.Z k + a.X k) * (Pi.single k 1 : Fin n → ZMod 2) j := by
  rw [tvY_apply]
  simp only [X_add, X_smul, paulix_X, pauliz_X, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The `Y_k`-transvection on the `Z`-coordinate: adds `a.Z_k + a.X_k` at `k`. -/
@[simp] theorem tvY_Z_apply (k : Fin n) (a : Pauli n) (j : Fin n) :
    (transvectionEquiv (paulix k + pauliz k) a).Z j
      = a.Z j + (a.Z k + a.X k) * (Pi.single k 1 : Fin n → ZMod 2) j := by
  rw [tvY_apply]
  simp only [Z_add, Z_smul, paulix_Z, pauliz_Z, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- **The `Y_k`-transvection distortion also equals the `Z_k` one.** `Y_k = X_k + Z_k` swaps the two
coordinates at `k`, and the swap difference collapses to `2·(a.X_k·b.Z_k + b.X_k·a.Z_k)` in `ZMod 4`
(the `−2 = 2` identity). So the same cochain `tvSignZ` validates the `Y_k` (Hadamard) action. -/
theorem frameDistortion_transvectionY (k : Fin n) (a b : Pauli n) :
    frameDistortion (transvectionEquiv (paulix k + pauliz k)) a b
      = 2 * (((a.X k).val * (b.Z k).val + (b.X k).val * (a.Z k).val : ℕ) : ZMod 4) := by
  unfold frameDistortion
  rw [betaFrame_sum, betaFrame_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single k]
  · simp only [tvY_X_apply, tvY_Z_apply, X_add, Z_add, Pi.add_apply, Pi.single_eq_same, mul_one]
    have hax := a.X k; have haz := a.Z k; have hbx := b.X k; have hbz := b.Z k
    revert hax haz hbx hbz
    generalize a.X k = ax; generalize a.Z k = az; generalize b.X k = bx; generalize b.Z k = bz
    intro hax haz hbx hbz
    revert ax az bx bz
    decide
  · intro j _ hjk
    simp only [tvY_X_apply, tvY_Z_apply, X_add, Z_add, Pi.add_apply,
      Pi.single_eq_of_ne hjk, mul_zero, add_zero]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The `Y_k`-transvection is an involution. -/
theorem tvY_invol (k : Fin n) (x : Pauli n) :
    transvectionEquiv (paulix k + pauliz k) (transvectionEquiv (paulix k + pauliz k) x) = x := by
  have h := LinearMap.congr_fun (transvectionLin_involutive (paulix k + pauliz k)) x
  simpa [transvectionEquiv, LinearEquiv.ofLinear_apply] using h

/-- The sign cochain `tvSignZ` validates the `Y_k`-transvection too. -/
theorem tvSign_validity_Y (k : Fin n) (p q : Pauli n) :
    tvSignZ k (transvectionEquiv (paulix k + pauliz k) p)
      + tvSignZ k (transvectionEquiv (paulix k + pauliz k) q)
      - tvSignZ k (transvectionEquiv (paulix k + pauliz k) (p + q))
      = betaFrame (transvectionEquiv (paulix k + pauliz k) p)
          (transvectionEquiv (paulix k + pauliz k) q)
        - betaFrame p q := by
  have hfd := frameDistortion_transvectionY k p q
  unfold frameDistortion at hfd
  rw [hfd, map_add]
  unfold tvSignZ
  simp only [tvY_X_apply, tvY_Z_apply, X_add, Z_add, Pi.add_apply, Pi.single_eq_same, mul_one]
  generalize p.X k = px; generalize p.Z k = pz; generalize q.X k = qx; generalize q.Z k = qz
  revert px pz qx qz
  decide

open Classical in
/-- **The frame-pure `Y_k`-transvection action on `(L,χ)`** (the Hadamard `H = τ_{X_k+Z_k}` gate).
Same shape as the `Z_k`/`X_k` actions, reusing the cochain `tvSignZ`. Fully frame-pure. -/
noncomputable def frameTransvectionYAction (k : Fin n) (S : FramePureSignedStab n) :
    FramePureSignedStab n where
  toFrameSignedStab :=
    { L := S.L.map (transvectionEquiv (paulix k + pauliz k)).toLinearMap
      chi := fun p =>
        if p ∈ S.L.map (transvectionEquiv (paulix k + pauliz k)).toLinearMap
        then S.chi (transvectionEquiv (paulix k + pauliz k) p)
          + tvSignZ k (transvectionEquiv (paulix k + pauliz k) p)
        else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), map_zero, S.chi_zero, zero_add]
        unfold tvSignZ; simp
      valid := by
        intro p hp q hq
        have hτp : transvectionEquiv (paulix k + pauliz k) p ∈ S.L := by
          obtain ⟨p₀, hp₀, hep₀⟩ := Submodule.mem_map.mp hp
          rw [← hep₀]
          change transvectionEquiv (paulix k + pauliz k)
            (transvectionEquiv (paulix k + pauliz k) p₀) ∈ S.L
          rw [tvY_invol]; exact hp₀
        have hτq : transvectionEquiv (paulix k + pauliz k) q ∈ S.L := by
          obtain ⟨q₀, hq₀, heq₀⟩ := Submodule.mem_map.mp hq
          rw [← heq₀]
          change transvectionEquiv (paulix k + pauliz k)
            (transvectionEquiv (paulix k + pauliz k) q₀) ∈ S.L
          rw [tvY_invol]; exact hq₀
        have hpq : p + q ∈ S.L.map (transvectionEquiv (paulix k + pauliz k)).toLinearMap :=
          Submodule.add_mem _ hp hq
        simp only [if_pos hp, if_pos hq, if_pos hpq, map_add]
        rw [S.valid _ hτp _ hτq]
        have hval := tvSign_validity_Y k p q
        rw [map_add] at hval
        linear_combination -hval }
  isStab := FTQCLib.Stabilizer.clifford_preserves_isStabilizer S.isStab
    (transvectionEquiv_isClifford _)
  full := by
    rw [FTQCLib.Stabilizer.clifford_preserves_finrank S.L (transvectionEquiv (paulix k + pauliz k))]
    exact S.full
  tight := fun p hp => if_neg hp

/-! ### `S² = Z`: the frame action carries the order-4 Clifford relation -/

/-- The sign-cochain identity behind `S² = Z`: `c(p) + c(τ_{Z_k} p) = 2·(p.X_k)`. -/
theorem tvSignZ_add_conj (k : Fin n) (p : Pauli n) :
    tvSignZ k p + tvSignZ k (transvectionEquiv (pauliz k) p) = 2 * ((p.X k).val : ZMod 4) := by
  unfold tvSignZ
  simp only [tvZ_X_apply, tvZ_Z_apply, Pi.single_eq_same, mul_one]
  generalize p.X k = px; generalize p.Z k = pz
  revert px pz
  decide

/-- **`S² = Z` in the frame.** Squaring the `Z_k`-transvection action (`S`) on `(L,χ)` gives
the Pauli-`Z_k` action. So the frame action carries the **order-4** Clifford relation `S² = Z` — not
the order-2 symplectic `τ_{Z_k}² = id`. The frame-visible group is the Clifford group, not `Sp`; the
factor `Z` is the per-Pauli sign the frame *does* see (vs the global phase it does not). -/
theorem frameTransvectionZAction_sq (k : Fin n) (S : FramePureSignedStab n) :
    frameTransvectionZAction k (frameTransvectionZAction k S) = framePauliAction (pauliz k) S := by
  classical
  have hid : (transvectionEquiv (pauliz k)).toLinearMap.comp
      (transvectionEquiv (pauliz k)).toLinearMap = LinearMap.id := by
    apply LinearMap.ext; intro x
    show transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) x) = x
    exact tvZ_invol k x
  apply framePureSignedStab_ext
  apply FrameSignedStab.ext'
  · show (S.L.map (transvectionEquiv (pauliz k)).toLinearMap).map
        (transvectionEquiv (pauliz k)).toLinearMap = S.L
    rw [← Submodule.map_comp, hid, Submodule.map_id]
  · funext p
    by_cases hp : p ∈ S.L
    · have hτp : transvectionEquiv (pauliz k) p
          ∈ S.L.map (transvectionEquiv (pauliz k)).toLinearMap := Submodule.mem_map_of_mem hp
      have hp2 : p ∈ (S.L.map (transvectionEquiv (pauliz k)).toLinearMap).map
          (transvectionEquiv (pauliz k)).toLinearMap := by
        rw [← Submodule.map_comp, hid, Submodule.map_id]; exact hp
      show (if p ∈ (S.L.map (transvectionEquiv (pauliz k)).toLinearMap).map
            (transvectionEquiv (pauliz k)).toLinearMap
          then (if transvectionEquiv (pauliz k) p
              ∈ S.L.map (transvectionEquiv (pauliz k)).toLinearMap
            then S.chi (transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) p))
              + tvSignZ k (transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) p))
            else 0) + tvSignZ k (transvectionEquiv (pauliz k) p) else 0)
        = if p ∈ S.L then S.chi p + 2 * ((omega (pauliz k) p).val : ZMod 4) else 0
      rw [if_pos hp2, if_pos hτp, if_pos hp, tvZ_invol, omega_pauliz, add_assoc, tvSignZ_add_conj]
    · have hp2 : p ∉ (S.L.map (transvectionEquiv (pauliz k)).toLinearMap).map
          (transvectionEquiv (pauliz k)).toLinearMap := by
        rw [← Submodule.map_comp, hid, Submodule.map_id]; exact hp
      show (if p ∈ (S.L.map (transvectionEquiv (pauliz k)).toLinearMap).map
            (transvectionEquiv (pauliz k)).toLinearMap
          then (if transvectionEquiv (pauliz k) p
              ∈ S.L.map (transvectionEquiv (pauliz k)).toLinearMap
            then S.chi (transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) p))
              + tvSignZ k (transvectionEquiv (pauliz k) (transvectionEquiv (pauliz k) p))
            else 0) + tvSignZ k (transvectionEquiv (pauliz k) p) else 0)
        = if p ∈ S.L then S.chi p + 2 * ((omega (pauliz k) p).val : ZMod 4) else 0
      rw [if_neg hp2, if_neg hp]

/-! ### The entangling boundary: a 2-qubit transvection is already non-quadratic -/

/-- **The single-qubit template stops at the first entangling generator.** For a *single* weight-2
(entangling) transvection `τ_{X₀X₁}`, the distortion `Δ_{τ_v}` is **not additive on an isotropic
triple** at `n = 3` — so no quadratic sign cochain (not even one restricted to a Lagrangian) can
validate its action, unlike the single-qubit `S`/`√X`/`H` (whose `Δ` is bilinear). Witnesses:
`a = X₀X₂`, `a' = Z₁`, `b = Z₀Z₂` (isotropic), with `Δ(a+a') = 0 ≠ 2 = Δa + Δa'`. So the cubic / Arf
content enters at a single entangling generator — not only in composition; this is the entangling
counterpart of `betaFrame_not_biadditive_on_isotropic`. -/
theorem frameDistortion_entangling_not_additive_on_isotropic :
    ∃ a a' b : Pauli 3, omega a a' = 0 ∧ omega a b = 0 ∧ omega a' b = 0 ∧
      frameDistortion (transvectionEquiv (paulix 0 + paulix 1)) (a + a') b
        ≠ frameDistortion (transvectionEquiv (paulix 0 + paulix 1)) a b
          + frameDistortion (transvectionEquiv (paulix 0 + paulix 1)) a' b := by
  refine ⟨⟨![1, 0, 1], ![0, 0, 0]⟩, ⟨![0, 0, 0], ![0, 1, 0]⟩, ⟨![0, 0, 0], ![1, 0, 1]⟩,
    by decide, by decide, by decide, ?_⟩
  unfold frameDistortion
  simp only [transvectionEquiv_apply]
  decide

end FTQCLib.Frame

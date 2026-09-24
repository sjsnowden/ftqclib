/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CarrierFloorChart
import FTQCLib.Examples.CarrierStateHadamard
import FTQCLib.Frame.MetaplecticAction

/-!
# The one-H certificate, on the chart read at the offset

One object, one H: the table executable (`applyHPinned`/`applyHFree`, `HadamardGate.lean`) and
the chart action (`frameTransvectionYAction`, `MetaplecticAction.lean`) are per-chart expressions
of the same gate. This file proves it on the floor: decoding the record after the executable H is
the chart's H after decoding.

The decode is the one built in `CarrierFloorChart.lean`: the exponent read **at the offset**
(`eAt`), the character `chiAt`, the chart `chartOf` of a floor record. Decoding at the origin
(`2·q(w)`) is not a function of the state at a nonzero offset (the graph-state example is in
`CarrierFloorChartCheck.lean`). The output's floor is a theorem (`isFloor_applyHPinned`), so
`cert_pinned` takes only the input's.

The fact that the table's swap is the chart's `Y`-transvection, the `L`-component (`cert_L`) and the
`χ`-component (`cert_chi`, the content: with `h := τ g ∈ L`, `h.X i = 0` and `q` free of `xᵢ`, the
two `χ`-formulas differ by `2·(x₀ᵢ·h.Zᵢ) + 2·(h.Zᵢ·x₀ᵢ) = 4·(…) ≡ 0 (mod 4)`) assemble into
`cert_pinned`; `cert_free` follows by the executable's round trip and the chart's involution.
The certificate is stated for the literal `m = 1` record `⟨1, q, c, L, x₀⟩`, the precision at which
the pinned executable emits its sign.

## Main definitions

* `decodeFloor`, `chartOf` — the floor chart and the signed Lagrangian of a floor record.

## Main results

* `cert_L`, `cert_chi`, `cert_pinned` — the certificate, pinned mode.
* `cert_free` — the certificate, free mode, by derivation.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Frame FTQCLib.Gates FTQCLib.Stabilizer Module

variable {n : ℕ}

/-! ## The table's swap is the chart's Y-transvection -/

/-- The one-bit swap `pauliSwapOn {i}` is pointwise the `Y_i`-transvection `τ_{X_i+Z_i}` — the same
symplectic element, in the two files' vocabularies. -/
theorem pauliSwapOn_singleton_eq_transvection (i : Fin n) (p : Pauli n) :
    pauliSwapOn {i} p = transvectionEquiv (paulix i + pauliz i) p := by
  ext j
  · rw [tvY_X_apply]
    by_cases hj : j = i
    · subst hj
      rw [pauliSwapOn_X, if_pos (Finset.mem_singleton_self j), Pi.single_eq_same, mul_one]
      generalize p.X j = a
      generalize p.Z j = b
      revert a b
      decide
    · rw [pauliSwapOn_X, if_neg (by simp [hj]), Pi.single_eq_of_ne hj, mul_zero, add_zero]
  · rw [tvY_Z_apply]
    by_cases hj : j = i
    · subst hj
      rw [pauliSwapOn_Z, if_pos (Finset.mem_singleton_self j), Pi.single_eq_same, mul_one]
      generalize p.X j = a
      generalize p.Z j = b
      revert a b
      decide
    · rw [pauliSwapOn_Z, if_neg (by simp [hj]), Pi.single_eq_of_ne hj, mul_zero, add_zero]

/-- The same identity at the `LinearMap` level. -/
theorem pauliSwapOn_singleton_eq_transvection' (i : Fin n) :
    (pauliSwapOn {i} : Pauli n →ₗ[ZMod 2] Pauli n)
      = (transvectionEquiv (paulix i + pauliz i)).toLinearMap :=
  LinearMap.ext (pauliSwapOn_singleton_eq_transvection i)

/-- Membership transport through the swap: the swap is an involution, so membership in the image
is membership of the swapped element. -/
theorem mem_map_pauliSwapOn (i : Fin n) (L : Submodule (ZMod 2) (Pauli n)) (g : Pauli n) :
    g ∈ Submodule.map (pauliSwapOn {i} : Pauli n →ₗ[ZMod 2] Pauli n) L
      ↔ pauliSwapOn {i} g ∈ L := by
  constructor
  · rintro ⟨g₀, hg₀, rfl⟩
    rwa [pauliSwapOn_pauliSwapOn]
  · intro hg
    exact ⟨pauliSwapOn {i} g, hg, pauliSwapOn_pauliSwapOn {i} g⟩

/-! ## The chart of a floor record -/

/-- The floor chart of a floor record at precision at most `2`. -/
noncomputable def decodeFloor (K : KernelState n) (hF : IsFloor (ofKernelState K))
    (hm : K.m ≤ 2) : FloorKernel n :=
  decodeAt K hF.1.2.1 (finrank_eq_of_isCarrier hF.1) ((isFloor_iff_shiftLaw K hF.1).mp hF)
    hF.1.1 hm

/-- The signed Lagrangian of a floor record: the chart's decode of its floor chart. -/
noncomputable def chartOf (K : KernelState n) (hF : IsFloor (ofKernelState K)) (hm : K.m ≤ 2) :
    FramePureSignedStab n :=
  fromFloor (decodeFloor K hF hm)

/-- The chart's Lagrangian is the record's. -/
theorem chartOf_L (K : KernelState n) (hF : IsFloor (ofKernelState K)) (hm : K.m ≤ 2) :
    (chartOf K hF hm).L = K.L := rfl

open scoped Classical in
/-- The chart's character is `chiAt` on `L` and `0` off it. -/
theorem chartOf_chi (K : KernelState n) (hF : IsFloor (ofKernelState K)) (hm : K.m ≤ 2)
    (g : Pauli n) : (chartOf K hF hm).chi g = if g ∈ K.L then chiAt K g else 0 := rfl

/-- `chartOf` respects record equality (the hypothesis arguments are proof-irrelevant). -/
theorem chartOf_congr {K₁ K₂ : KernelState n} (h : K₁ = K₂)
    (hF₁ : IsFloor (ofKernelState K₁)) (hm₁ : K₁.m ≤ 2)
    (hF₂ : IsFloor (ofKernelState K₂)) (hm₂ : K₂.m ≤ 2) :
    chartOf K₁ hF₁ hm₁ = chartOf K₂ hF₂ hm₂ := by
  subst h
  rfl

/-! ## Arithmetic helpers for the χ-component -/

/-- Evaluating the emitted sign at `m = 1`: `hSignPoly i ε 1` evaluates to `ε · w i`. -/
theorem eval_hSignPoly_one (i : Fin n) (ε : ZMod 2) (w : Fin n → ZMod 2) :
    DiagPhase.eval (hSignPoly i ε 1) w
      = ((ε.val : ZMod (2 ^ 1)) * ((w i).val : ZMod (2 ^ 1))) := by
  unfold hSignPoly DiagPhase.eval
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  norm_num [DiagPhase.liftBinary]

/-- `toFour` at precision `1` of a product of bit values is twice the product of the bits. -/
theorem toFour_one_mul_val (a b : ZMod 2) :
    toFour 1 ((a.val : ZMod (2 ^ 1)) * (b.val : ZMod (2 ^ 1)))
      = 2 * (a.val : ZMod 4) * (b.val : ZMod 4) := by
  revert a b
  decide

/-- Updating the left summand at `i` is updating the sum. -/
theorem update_add_left (i : Fin n) (x₀ v : Fin n → ZMod 2) (b : ZMod 2) :
    Function.update x₀ i b + v = Function.update (x₀ + v) i (b + v i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Updating the right summand at `i` is updating the sum. -/
theorem add_update_right (i : Fin n) (x₀ v : Fin n → ZMod 2) (b : ZMod 2) :
    x₀ + Function.update v i b = Function.update (x₀ + v) i (x₀ i + b) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- When `q` is free of `xᵢ`, the chart exponent does not see an update at `i`. -/
theorem eAt_update_free (i : Fin n) (K : KernelState n)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval K.q (Function.update w i b) = DiagPhase.eval K.q w)
    (v : Fin n → ZMod 2) (b : ZMod 2) :
    eAt K (Function.update v i b) = eAt K v := by
  unfold eAt
  rw [add_update_right, hqfree]

/-- The pinned executable's chart exponent is the input's plus the emitted sign. -/
theorem eAt_applyHPinned (i : Fin n) (q : DiagPhase n 1) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q (Function.update w i b) = DiagPhase.eval q w)
    (u : Fin n → ZMod 2) :
    eAt (applyHPinned i ⟨1, q, c, L, x₀⟩) u
      = eAt ⟨1, q, c, L, x₀⟩ u + 2 * (((x₀ i).val : ℕ) : ZMod 4) * (((u i).val : ℕ) : ZMod 4) := by
  unfold eAt
  change toFour 1 (DiagPhase.eval (q + hSignPoly i (x₀ i) 1) (Function.update x₀ i 0 + u)
      - DiagPhase.eval (q + hSignPoly i (x₀ i) 1) (Function.update x₀ i 0))
    = toFour 1 (DiagPhase.eval q (x₀ + u) - DiagPhase.eval q x₀) + _
  rw [DiagPhase.eval_add, DiagPhase.eval_add, eval_hSignPoly_one, eval_hSignPoly_one,
    update_add_left, hqfree, hqfree, zero_add]
  have h0 : (Function.update x₀ i 0) i = 0 := Function.update_self _ _ _
  have hu : (Function.update (x₀ + u) i (u i)) i = u i := Function.update_self _ _ _
  rw [h0, hu, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
  rw [show DiagPhase.eval q (x₀ + u) + (x₀ i).val * (u i).val - DiagPhase.eval q x₀
      = (DiagPhase.eval q (x₀ + u) - DiagPhase.eval q x₀)
        + ((x₀ i).val : ZMod (2 ^ 1)) * ((u i).val : ZMod (2 ^ 1)) from by ring]
  rw [toFour_add (by norm_num), toFour_one_mul_val]

/-! ## The L-component -/

/-- The table gate's `L`-update is the chart gate's `L`-update. -/
theorem cert_L (i : Fin n) (K : KernelState n) :
    (applyHPinned i K).L
      = Submodule.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap K.L := by
  change Submodule.map (pauliSwapOn {i} : Pauli n →ₗ[ZMod 2] Pauli n) K.L = _
  rw [pauliSwapOn_singleton_eq_transvection']

/-! ## The χ-component (the content) -/

/-- The coordinates of `τ h` when `h.X i = 0` — `X` picks up `h.Z i` at `i`, `Z` zeroes
there; both untouched elsewhere. -/
theorem tv_coords (i : Fin n) (h : Pauli n) (hXi : h.X i = 0) :
    (∀ j, (transvectionEquiv (paulix i + pauliz i) h).X j
        = if j = i then h.Z i else h.X j)
    ∧ (∀ j, (transvectionEquiv (paulix i + pauliz i) h).Z j
        = if j = i then 0 else h.Z j) := by
  constructor
  · intro j
    rw [tvY_X_apply, hXi, add_zero]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, mul_one, if_pos rfl, hXi, zero_add]
    · rw [Pi.single_eq_of_ne hj, mul_zero, add_zero, if_neg hj]
  · intro j
    rw [tvY_Z_apply, hXi, add_zero]
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, mul_one, if_pos rfl]
      generalize h.Z j = b
      revert b
      decide
    · rw [Pi.single_eq_of_ne hj, mul_zero, add_zero, if_neg hj]

/-- `yWeight` is invariant under the transvection on the pinned domain. -/
theorem yWeight_tv (i : Fin n) (h : Pauli n) (hXi : h.X i = 0) :
    yWeight (transvectionEquiv (paulix i + pauliz i) h) = yWeight h := by
  obtain ⟨hX, hZ⟩ := tv_coords i h hXi
  unfold yWeight zDot
  apply Finset.sum_congr rfl
  intro j _
  rw [hX j, hZ j]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, if_pos rfl, hXi]
    simp
  · rw [if_neg hj, if_neg hj]

/-- Updating the offset at a coordinate where the Pauli has no `Z`-support is invisible to
`zDot`. -/
theorem zDot_update_zero (i : Fin n) (p : Pauli n) (hZi : p.Z i = 0)
    (v : Fin n → ZMod 2) (b : ZMod 2) :
    zDot p (Function.update v i b) = zDot p v := by
  unfold zDot
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst hj
    rw [hZi]
    simp
  · rw [Function.update_apply, if_neg hj]

/-- `zDot` splits off the `i`-term across the transvection on the pinned domain. -/
theorem zDot_split_tv (i : Fin n) (h : Pauli n) (hXi : h.X i = 0) (v : Fin n → ZMod 2) :
    zDot h v = (h.Z i).val * (v i).val
      + zDot (transvectionEquiv (paulix i + pauliz i) h) v := by
  obtain ⟨hX, hZ⟩ := tv_coords i h hXi
  unfold zDot
  simp only [hZ]
  rw [← Finset.add_sum_erase _ (fun j => (h.Z j).val * (v j).val) (Finset.mem_univ i),
    ← Finset.add_sum_erase _
      (fun j => ((if j = i then (0 : ZMod 2) else h.Z j)).val * (v j).val) (Finset.mem_univ i)]
  rw [if_pos rfl]
  simp only [ZMod.val_zero, zero_mul, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj)]

/-- **The χ-component of the one-H certificate** (pinned mode, `m = 1`): on the output's
Lagrangian, the decoded character of the record after `applyHPinned` is the chart's transported
character. The crux cancellation is `2·(x₀ᵢ·h.Zᵢ) + 2·(h.Zᵢ·x₀ᵢ) = 4·(…) = 0` in `ZMod 4`. -/
theorem cert_chi (i : Fin n) (q : DiagPhase n 1) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2)
    (hpin : ∀ p ∈ L, p.X i = 0)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q (Function.update w i b) = DiagPhase.eval q w)
    {g : Pauli n}
    (hg : g ∈ Submodule.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap L) :
    chiAt (applyHPinned i ⟨1, q, c, L, x₀⟩) g
      = chiAt ⟨1, q, c, L, x₀⟩ (transvectionEquiv (paulix i + pauliz i) g)
        + tvSignZ i (transvectionEquiv (paulix i + pauliz i) g) := by
  have hτg : transvectionEquiv (paulix i + pauliz i) g ∈ L := by
    obtain ⟨h₀, hh₀, rfl⟩ := hg
    change transvectionEquiv (paulix i + pauliz i)
      (transvectionEquiv (paulix i + pauliz i) h₀) ∈ L
    rw [tvY_invol]
    exact hh₀
  have hXi : (transvectionEquiv (paulix i + pauliz i) g).X i = 0 := hpin _ hτg
  obtain ⟨hgX, hgZ⟩ := tv_coords i (transvectionEquiv (paulix i + pauliz i) g) hXi
  have htv : tvSignZ i (transvectionEquiv (paulix i + pauliz i) g) = 0 := by
    unfold tvSignZ
    rw [hXi]
    simp
  rw [htv, add_zero]
  have hginv : transvectionEquiv (paulix i + pauliz i)
      (transvectionEquiv (paulix i + pauliz i) g) = g := tvY_invol i g
  have hgXfun : g.X = Function.update (transvectionEquiv (paulix i + pauliz i) g).X i
      ((transvectionEquiv (paulix i + pauliz i) g).Z i) := by
    funext j
    rw [Function.update_apply, ← hginv, hgX j, hginv]
  have hyW : yWeight g = yWeight (transvectionEquiv (paulix i + pauliz i) g) := by
    conv_lhs => rw [← hginv]
    rw [yWeight_tv i _ hXi]
  have hgZi : g.Z i = 0 := by
    rw [← hginv, hgZ i, if_pos rfl]
  have hzupd : zDot g (Function.update x₀ i 0) = zDot g x₀ :=
    zDot_update_zero i g hgZi x₀ 0
  have hzsplit : zDot (transvectionEquiv (paulix i + pauliz i) g) x₀
      = ((transvectionEquiv (paulix i + pauliz i) g).Z i).val * (x₀ i).val + zDot g x₀ := by
    conv_lhs => rw [zDot_split_tv i _ hXi x₀]
    rw [hginv]
  have hgXi : g.X i = (transvectionEquiv (paulix i + pauliz i) g).Z i := by
    rw [← hginv, hgX i, if_pos rfl, hginv]
  have hEq : eAt (⟨1, q, c, L, x₀⟩ : KernelState n) g.X
      = eAt (⟨1, q, c, L, x₀⟩ : KernelState n)
          (transvectionEquiv (paulix i + pauliz i) g).X := by
    rw [hgXfun, eAt_update_free i _ hqfree]
  have hx' : (applyHPinned i (⟨1, q, c, L, x₀⟩ : KernelState n)).x₀
      = Function.update x₀ i 0 := rfl
  unfold chiAt chiOfE
  rw [hx', eAt_applyHPinned i q c L x₀ hqfree, eAt_applyHPinned i q c L x₀ hqfree, hEq, hyW,
    hzupd, hzsplit, hgXi]
  have h0i : (((((0 : Fin n → ZMod 2) i).val : ℕ)) : ZMod 4) = 0 := by
    simp
  rw [h0i, mul_zero, add_zero]
  push_cast
  have h4 : ∀ x : ZMod 4, 4 * x = 0 := by decide
  linear_combination
    h4 ((((transvectionEquiv (paulix i + pauliz i) g).Z i).val : ZMod 4) * ((x₀ i).val : ZMod 4))

/-! ## The certificate, assembled -/

/-- **The one-H certificate (pinned mode, m = 1).** For a floor record with bit `i` H-pinned and
`q` free of `xᵢ`, the chart of the record after the table executable is the chart action on the
chart of the record. The output's floor is a theorem (`isFloor_applyHPinned`), not a hypothesis. -/
theorem cert_pinned (i : Fin n) (q : DiagPhase n 1) (c : ℂ) (L : Submodule (ZMod 2) (Pauli n))
    (x₀ : Fin n → ZMod 2)
    (hpin : ∀ p ∈ L, p.X i = 0)
    (hqfree : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q (Function.update w i b) = DiagPhase.eval q w)
    (hF : IsFloor (ofKernelState (⟨1, q, c, L, x₀⟩ : KernelState n))) :
    chartOf (applyHPinned i ⟨1, q, c, L, x₀⟩) (isFloor_applyHPinned i hF hpin hqfree)
        one_le_two
      = frameTransvectionYAction i (chartOf ⟨1, q, c, L, x₀⟩ hF one_le_two) := by
  classical
  apply framePureSignedStab_ext
  apply FrameSignedStab.ext'
  · exact cert_L i ⟨1, q, c, L, x₀⟩
  · funext g
    rw [chartOf_chi]
    change _ = (if g ∈ Submodule.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap L
        then (chartOf (⟨1, q, c, L, x₀⟩ : KernelState n) hF one_le_two).chi
            (transvectionEquiv (paulix i + pauliz i) g)
          + tvSignZ i (transvectionEquiv (paulix i + pauliz i) g)
        else 0)
    rw [chartOf_chi]
    by_cases hg : g ∈ Submodule.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap L
    · have hτg : transvectionEquiv (paulix i + pauliz i) g ∈ L := by
        obtain ⟨h₀, hh₀, rfl⟩ := hg
        change transvectionEquiv (paulix i + pauliz i)
          (transvectionEquiv (paulix i + pauliz i) h₀) ∈ L
        rw [tvY_invol]
        exact hh₀
      rw [if_pos (by rw [cert_L]; exact hg), if_pos hg, if_pos hτg]
      exact cert_chi i q c L x₀ hpin hqfree hg
    · rw [if_neg (by rw [cert_L]; exact hg), if_neg hg]

/-! ## The free-mode certificate, by derivation

The chart's H is a literal involution (H² = id exactly — unlike S, whose square is the Pauli
`Z`): the cochain cancels itself across the swap, `tvSignZ p + tvSignZ (τp) = 2ab + 2ba = 4ab = 0`.
With the executable's round trip (`applyH_roundTrip'`), `cert_free` follows from `cert_pinned` with
no new χ-computation. -/

/-- The `tvSignZ` cochain cancels itself across the `Y`-swap. -/
theorem tvSignZ_add_tv (i : Fin n) (p : Pauli n) :
    tvSignZ i p + tvSignZ i (transvectionEquiv (paulix i + pauliz i) p) = 0 := by
  unfold tvSignZ
  rw [tvY_X_apply, tvY_Z_apply, Pi.single_eq_same, mul_one]
  generalize p.X i = a
  generalize p.Z i = b
  revert a b
  decide

/-- **The chart's H is an involution**: `frameTransvectionYAction i` squares to the identity on
`(L,χ)`. (Contrast `frameTransvectionZAction_sq : S² = Z`.) -/
theorem frameTransvectionYAction_invol (i : Fin n) (S : FramePureSignedStab n) :
    frameTransvectionYAction i (frameTransvectionYAction i S) = S := by
  classical
  have hLL : (S.L.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap).map
      (transvectionEquiv (paulix i + pauliz i)).toLinearMap = S.L := by
    rw [← Submodule.map_comp]
    have hid : (transvectionEquiv (paulix i + pauliz i)).toLinearMap.comp
        (transvectionEquiv (paulix i + pauliz i)).toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      change transvectionEquiv (paulix i + pauliz i)
        (transvectionEquiv (paulix i + pauliz i) x) = x
      exact tvY_invol i x
    rw [hid, Submodule.map_id]
  apply framePureSignedStab_ext
  apply FrameSignedStab.ext'
  · exact hLL
  · funext p
    change (if p ∈ (S.L.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap).map
          (transvectionEquiv (paulix i + pauliz i)).toLinearMap
        then (frameTransvectionYAction i S).chi (transvectionEquiv (paulix i + pauliz i) p)
          + tvSignZ i (transvectionEquiv (paulix i + pauliz i) p)
        else 0) = S.chi p
    by_cases hp : p ∈ S.L
    · rw [if_pos (by rw [hLL]; exact hp)]
      change (if transvectionEquiv (paulix i + pauliz i) p
            ∈ S.L.map (transvectionEquiv (paulix i + pauliz i)).toLinearMap
          then S.chi (transvectionEquiv (paulix i + pauliz i)
              (transvectionEquiv (paulix i + pauliz i) p))
            + tvSignZ i (transvectionEquiv (paulix i + pauliz i)
              (transvectionEquiv (paulix i + pauliz i) p))
          else 0)
          + tvSignZ i (transvectionEquiv (paulix i + pauliz i) p) = S.chi p
      rw [if_pos ⟨p, hp, rfl⟩, tvY_invol, add_assoc, tvSignZ_add_tv, add_zero]
    · rw [if_neg (by rw [hLL]; exact hp)]
      exact (S.tight p hp).symm

/-- **The one-H certificate (free/recollapse mode, m = 1)**, derived from the pinned mode via the
executable round trip and the chart involution. The free-side record carries its dyadic sign
explicitly (`q = q₀ + hSignPoly i ε`), bit `i` is X-type in `L` (no `Z`-support), and the offset
is gauge-zero at `i`. The free executable's floor closure is not proved here, so the output's floor
is a hypothesis. -/
theorem cert_free (i : Fin n) (q₀ : DiagPhase n 1) (ε : ZMod 2) (c : ℂ)
    (L : Submodule (ZMod 2) (Pauli n)) (x₀ : Fin n → ZMod 2)
    (hfree : ∀ p ∈ L, p.Z i = 0) (hx0 : x₀ i = 0)
    (hq₀free : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval q₀ (Function.update w i b) = DiagPhase.eval q₀ w)
    (hF : IsFloor (ofKernelState (⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ : KernelState n)))
    (hF' : IsFloor (ofKernelState
      (applyHFree i ε (⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ : KernelState n)))) :
    chartOf (applyHFree i ε ⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩) hF' one_le_two
      = frameTransvectionYAction i
          (chartOf ⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ hF one_le_two) := by
  classical
  -- the round trip: pinning the freed record returns the original
  have h1 : applyHPinned i (applyHFree i ε ⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩)
      = (⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ : KernelState n) :=
    applyH_roundTrip' i ε _ hx0
  -- the pinned certificate at the freed record (a literal m = 1 record)
  have hpinK : ∀ p ∈ (Submodule.map (pauliSwapOn {i} : Pauli n →ₗ[ZMod 2] Pauli n) L),
      p.X i = 0 := by
    rintro p ⟨p₀, hp₀, rfl⟩
    rw [pauliSwapOn_X, if_pos (Finset.mem_singleton_self i)]
    exact hfree p₀ hp₀
  have hq : ((q₀ + hSignPoly i ε 1) + hSignPoly i ε 1) = q₀ := by
    rw [add_assoc, hSignPoly_add_self, add_zero]
  have hqfreeK : ∀ (w : Fin n → ZMod 2) (b : ZMod 2),
      DiagPhase.eval ((q₀ + hSignPoly i ε 1) + hSignPoly i ε 1) (Function.update w i b)
        = DiagPhase.eval ((q₀ + hSignPoly i ε 1) + hSignPoly i ε 1) w := by
    intro w b
    rw [hq]
    exact hq₀free w b
  have h2 := cert_pinned i ((q₀ + hSignPoly i ε 1) + hSignPoly i ε 1)
    ((Real.sqrt 2 : ℂ) * c) (Submodule.map (pauliSwapOn {i}) L) (Function.update x₀ i ε)
    hpinK hqfreeK hF'
  -- restate the round trip on the literal record (defeq), for the syntactic rewrite
  have h1' : applyHPinned i (⟨1, (q₀ + hSignPoly i ε 1) + hSignPoly i ε 1,
      (Real.sqrt 2 : ℂ) * c, Submodule.map (pauliSwapOn {i}) L,
      Function.update x₀ i ε⟩ : KernelState n)
      = (⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ : KernelState n) := h1
  have h3 : chartOf (⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩ : KernelState n) hF one_le_two
      = frameTransvectionYAction i
          (chartOf (applyHFree i ε ⟨1, q₀ + hSignPoly i ε 1, c, L, x₀⟩) hF' one_le_two) := by
    rw [← chartOf_congr h1' (isFloor_applyHPinned i hF' hpinK hqfreeK) one_le_two hF
      one_le_two]
    exact h2
  rw [h3]
  exact (frameTransvectionYAction_invol i _).symm

end FTQCLib.Frame.Walkthrough

/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.FrameBridgeAmplitudeQuad
import FTQCLib.Hilbert.CategoricalEquivalence
import FTQCLib.Stabilizer.SignedLagrangian

/-! # The frame ↔ Hilbert signed-stabilizer bridge

The frame-pure `(L,χ)` chart (`FramePureSignedStab`, `χ : Pauli n → ZMod 4`) and the Hilbert
chart (`PureSignedStab`, `sign : Pauli n → ℂ`) are the same object in two value rings. This file
proves it, via the cocycle identity `pauliPhase p q = iZ4 (betaFrame p q)` — the Hilbert `i`-power
cocycle is the `iZ4`-image of the frame `ℤ/4` cocycle. The bridge is the **optional
Hilbert-faithfulness certificate** for the floor work: it lets the floor `(L,χ) ↔ floor`
correspondence sit inside the Hilbert `SCat ≌ OCat` (the Clifford-equivariant upgrade), so this
file imports Hilbert deliberately. -/

namespace FTQCLib.Hilbert

open FTQCLib FTQCLib.Pauli FTQCLib.Stabilizer FTQCLib.Frame

variable {n : ℕ}

/-- `iZ4` on a `ℕ`-cast is the actual power of `i` (period 4). -/
theorem iZ4_natCast (k : ℕ) : iZ4 (k : ZMod 4) = Complex.I ^ k := by
  unfold iZ4
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod k 4, pow_add, pow_mul]
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  rw [hI4, one_pow, one_mul]

/-- **The frame ↔ Hilbert cocycle identity.** The Hilbert `i`-power Pauli cocycle is the
`iZ4`-image of the frame `ℤ/4` cocycle: `pauliPhase p q = iZ4 (betaFrame p q)`. Both are `i` to
the power `yWeight p + yWeight q + yWeight (p+q) + 2·(Z·X)`; `−1 = i²` gives the parity. -/
theorem pauliPhase_eq_iZ4_betaFrame (p q : Pauli n) :
    pauliPhase p q = iZ4 (betaFrame p q) := by
  have hxz : ∀ r : Pauli n, xzWeight r = yWeight r := fun _ => rfl
  have hzz : ∀ (r : Pauli n) (v : Fin n → ZMod 2), zDotVal r v = zDot r v := fun _ _ => rfl
  unfold pauliPhase betaFrame
  rw [iZ4_natCast, hxz p, hxz q, hxz (p + q), hzz q p.X, hzz (p + q) (p + q).X,
    show ((-1 : ℂ)) = Complex.I ^ 2 from (Complex.I_sq).symm, ← pow_mul,
    ← pow_add, ← pow_add, ← pow_add]

/-- `clog` is a genuine inverse of `iZ4` on all of `ZMod 4` (not just the `μ₄` round-trip). -/
theorem clog_iZ4 (c : ZMod 4) : clog (iZ4 c) = c := by
  have h4 : ∀ d : ZMod 4, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by decide
  rcases h4 c with rfl | rfl | rfl | rfl
  · unfold iZ4; rw [show (0 : ZMod 4).val = 0 from rfl, pow_zero, clog_one]
  · unfold iZ4; rw [show (1 : ZMod 4).val = 1 from rfl, pow_one, clog_I]
  · unfold iZ4
    rw [show (2 : ZMod 4).val = 2 from rfl, pow_two, Complex.I_mul_I, clog_neg_one]
  · unfold iZ4
    rw [show (3 : ZMod 4).val = 3 from rfl, show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two,
      Complex.I_mul_I, pow_one, neg_one_mul, clog_neg_I]

/-- On `L` a stabilizer sign is `±1`, hence a fourth root of unity. -/
theorem isMu4_signOfMem (T : SignedStab n) {p : Pauli n} (hp : p ∈ T.L) : IsMu4 (T.sign p) := by
  rcases mul_self_eq_one_iff.mp (sign_mul_self T hp) with h | h
  · rw [h]; exact isMu4_one
  · rw [h]; exact isMu4_neg_one

open Classical in
/-- **Frame → Hilbert.** A frame-pure signed Lagrangian `(L,χ)` is a Hilbert signed stabilizer,
with `sign := iZ4 ∘ χ` on `L` and `0` off `L` (the Hilbert `tight` convention; the frame `tight`
is `χ = 0` off `L`, which `iZ4` sends to `1`, so the off-`L` zero is imposed explicitly). -/
noncomputable def frameToHilbert (S : FramePureSignedStab n) : PureSignedStab n where
  toSignedStab :=
    { L := S.L
      sign := fun p => if p ∈ S.L then iZ4 (S.chi p) else 0
      sign_zero := by
        rw [if_pos (Submodule.zero_mem _), S.chi_zero]; unfold iZ4; rw [ZMod.val_zero, pow_zero]
      valid := by
        intro p hp q hq
        have hpq : p + q ∈ S.L := S.L.add_mem hp hq
        simp only [if_pos hp, if_pos hq, if_pos hpq]
        rw [pauliPhase_eq_iZ4_betaFrame, ← iZ4_add, ← iZ4_add, S.valid p hp q hq]
        congr 1; ring }
  isStab := S.isStab
  full := S.full
  tight := fun p hp => if_neg hp

open Classical in
/-- **Hilbert → Frame.** Read the `ℤ/4` sign back with `clog` on `L`, `0` off `L`. -/
noncomputable def hilbertToFrame (T : PureSignedStab n) : FramePureSignedStab n where
  toFrameSignedStab :=
    { L := T.L
      chi := fun p => if p ∈ T.L then clog (T.sign p) else 0
      chi_zero := by
        rw [if_pos (Submodule.zero_mem _), T.toSignedStab.sign_zero, clog_one]
      valid := by
        intro p hp q hq
        have hpq : p + q ∈ T.L := T.toSignedStab.L.add_mem hp hq
        have hP : IsMu4 (pauliPhase p q) := by
          rw [pauliPhase_eq_iZ4_betaFrame]; unfold iZ4; exact isMu4_iPow _
        simp only [if_pos hp, if_pos hq, if_pos hpq]
        rw [← T.toSignedStab.valid p hp q hq,
          clog_mul (isMu4_mul (isMu4_signOfMem _ hq) (isMu4_signOfMem _ hp)) hP,
          clog_mul (isMu4_signOfMem _ hq) (isMu4_signOfMem _ hp),
          pauliPhase_eq_iZ4_betaFrame, clog_iZ4]
        ring }
  isStab := T.isStab
  full := T.full
  tight := fun p hp => if_neg hp

/-- Equality of `FramePureSignedStab` from equality of the underlying `FrameSignedStab`. -/
theorem framePureSignedStab_ext {S S' : FramePureSignedStab n}
    (h : S.toFrameSignedStab = S'.toFrameSignedStab) : S = S' := by
  cases S; cases S'; cases h; rfl

open Classical in
/-- **The frame ↔ Hilbert signed-stabilizer equivalence.** `(L,χ)` over `ZMod 4` and `(L, sign)`
over `ℂ` are the same junk-free stabilizer state, via `iZ4`/`clog`. The optional
Hilbert-faithfulness bridge that places the frame floor inside the Hilbert `SCat ≌ OCat`. -/
noncomputable def frameHilbertEquiv : FramePureSignedStab n ≃ PureSignedStab n where
  toFun := frameToHilbert
  invFun := hilbertToFrame
  left_inv S := by
    refine framePureSignedStab_ext (FrameSignedStab.ext' rfl ?_)
    funext p
    by_cases hpL : p ∈ S.L
    · show (if p ∈ S.L then clog (if p ∈ S.L then iZ4 (S.chi p) else 0) else 0) = S.chi p
      rw [if_pos hpL, if_pos hpL, clog_iZ4]
    · show (if p ∈ S.L then clog (if p ∈ S.L then iZ4 (S.chi p) else 0) else 0) = S.chi p
      rw [if_neg hpL, S.tight p hpL]
  right_inv T := by
    refine pureSignedStab_ext (signedStab_ext rfl ?_)
    funext p
    by_cases hpL : p ∈ T.L
    · show (if p ∈ T.L then iZ4 (if p ∈ T.L then clog (T.sign p) else 0) else 0) = T.sign p
      rw [if_pos hpL, if_pos hpL, iZ4_clog (isMu4_signOfMem _ hpL)]
    · show (if p ∈ T.L then iZ4 (if p ∈ T.L then clog (T.sign p) else 0) else 0) = T.sign p
      rw [if_neg hpL, (T.tight p hpL).symm]

end FTQCLib.Hilbert

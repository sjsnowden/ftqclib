/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hierarchy.KernelState
import FTQCLib.Hierarchy.GatePolynomials

/-! # The T-gate injection gadget, native to the kernel frame

T is the frontier of the gate-injection ladder: its resource `|A⟩ = T|+⟩` is a *magic* state that
leaves `(L,χ)`, and its correction is a conditional Clifford `S^m` (since `T²=S`), not a Pauli. So T is
built in the kernel frame (phase polynomials), on the `KernelState` carrier
(`FTQCLib/Hierarchy/KernelState.lean`). **Pure frame** — this file imports no `FTQCLib.Hilbert`.

This file: the magic resource `magicA` and its level-3 certification (the carrier holds what the bridge
cannot); and the gadget as a phase-polynomial identity — CNOT entangle (`affinePushforward`),
`Z`-measurement (`freezeAt`), the `S^b` correction (the doubled-coefficient descent `T²=S`). `T†` falls
out by linearity. The Hilbert faithfulness certificate is the separable bridge in
`FTQCLib/Hilbert/FrameConditioning.lean`. -/

namespace FTQCLib.Frame

open FTQCLib FTQCLib.Hierarchy

/-- The magic resource `|A⟩ = T|+⟩`, as a one-qubit kernel state: support `= {0,1}` (the `|+⟩` support,
`L = ⊤`), exponent the T phase polynomial `x/8`. The amplitude constant `c` is left `1` (an unnormalized
representative — the gadget is about the *exponent*, never `c`). The unit-norm value is
`|c| = 2^{-dim π_X(L)/2}` — here `2^{-½}`, since `|+⟩`'s support has `2` points — fixed entirely by the
**F2 support dimension** `dim π_X(L)`, not by any Hilbert structure. (The kernel gates are unitary and
preserve `‖·‖₂` exactly; only measurement rescales it, by the Born weight.) -/
noncomputable def magicA : KernelState 1 where
  m := 3
  q := DiagPhase.tGatePoly 0
  c := 1
  L := ⊤
  x₀ := 0

/-- **`|A⟩` is the level-3 magic state.** Its exponent sits at level 3 — beyond the level-≤2 stabilizer
states the bridge (`stabilizerState_isLevel2Kernel_unconditional`) reaches. So the `KernelState` carrier
genuinely holds the magic resource the `(L,χ)` frame cannot. -/
theorem magicA_q_level : magicA.q.level = 3 := DiagPhase.tGatePoly_level 0

/-- **The S correction sits one level below T.** The conditional correction in the T-gadget is `S`
(because `T² = S`), whose phase polynomial is the precision-2 root-of-`Z` exponent — level 2, exactly one
below T's level 3. This is "a gate corrected from the level below," made literal. -/
theorem tGadget_correction_level {n : ℕ} (d : Fin n) : (DiagPhase.rzGatePoly d 2).level = 2 := by
  haveI : Fact (1 < 2 ^ 2) := ⟨by norm_num⟩
  exact DiagPhase.rzGatePoly_level d 2 (by norm_num)

/-- **The whole `2^k`-th-root-of-`Z` tower, in one proof (the kth case).** For *any* precision `m`, the
gadget injecting `R_{m-1} = Z^{1/2^{m-1}}` (resource exponent `rzGatePoly 1 m = X₁`, the `R`-gate on the
ancilla) — entangle `CNOT(0→1)` (`affinePushforward`), measure `Z₁=b` (`freezeAt`), then the conditional
`R_{m-2}^b` correction (the doubled coefficient `2b·X₀`, one level down) — leaves the data-wire exponent
`rzGatePoly 0 m = X₀`, i.e. `R_{m-1}` injected, up to a global-phase constant. The proof uses nothing
about `m`: it's the `bind₁` algebra of the substitutions, and the `−2b·X₀` cross term cancels the
correction in any `ZMod(2^m)`. So `Z` (`m=1`), `S` (`m=2`), `T` (`m=3`), and every higher root are one
theorem. -/
theorem rzGadget_correct {m : ℕ} (b : ZMod 2) :
    freezeAt (1 : Fin 2) b (DiagPhase.affinePushforward 0 1 (DiagPhase.rzGatePoly 1 m))
        + 2 * MvPolynomial.C (b.val : ZMod (2 ^ m)) * MvPolynomial.X (0 : Fin 2)
      = DiagPhase.rzGatePoly (0 : Fin 2) m + MvPolynomial.C (b.val : ZMod (2 ^ m)) := by
  have h0 : ((0 : Fin 2) = 1) = False := eq_false (by decide)
  have h1 : ((1 : Fin 2) = 1) = True := eq_true rfl
  unfold freezeAt DiagPhase.affinePushforward DiagPhase.rzGatePoly DiagPhase.cnotSubst
  simp only [MvPolynomial.bind₁_X_right, map_add, map_sub, map_mul, map_ofNat,
    MvPolynomial.bind₁_C_right, h0, h1, if_true, if_false]
  ring

/-- **The T-gadget is correct, in pure phase-polynomial algebra** — the `m=3` instance of
the tower. Data `0`, ancilla `1` carrying `T|+⟩` (`tGatePoly 1 = rzGatePoly 1 3`): CNOT, measure `Z₁=b`,
the `S^b` correction (`2b·X₀`), and the data exponent is `T` up to a global-phase constant. No Hilbert. -/
theorem tGadget_correct (b : ZMod 2) :
    freezeAt (1 : Fin 2) b (DiagPhase.affinePushforward 0 1 (DiagPhase.tGatePoly 1))
        + 2 * MvPolynomial.C (b.val : ZMod 8) * MvPolynomial.X (0 : Fin 2)
      = DiagPhase.tGatePoly (0 : Fin 2) + MvPolynomial.C (b.val : ZMod 8) :=
  rzGadget_correct b

/-- **The conjugate tower `R_k†`, in one proof — `−1 ×` the gadget.** For any precision `m`, the
conjugate gadget (resource exponent `−rzGatePoly 1 m`, `= R_{m-1}†|+⟩`) injects `R_{m-1}†`, with the
correction flipped `R_{m-2} → R_{m-2}†` (`+2b·X₀ → −2b·X₀`). Falls out by linearity: `freezeAt` and
`affinePushforward` are additive (`bind₁` ring homs), so negating the resource negates the whole
identity. No new input, no new lemma — for the entire conjugate tower at once. -/
theorem rzGadget_dagger_correct {m : ℕ} (b : ZMod 2) :
    freezeAt (1 : Fin 2) b (DiagPhase.affinePushforward 0 1 (-DiagPhase.rzGatePoly 1 m))
        - 2 * MvPolynomial.C (b.val : ZMod (2 ^ m)) * MvPolynomial.X (0 : Fin 2)
      = -DiagPhase.rzGatePoly (0 : Fin 2) m - MvPolynomial.C (b.val : ZMod (2 ^ m)) := by
  have h0 : ((0 : Fin 2) = 1) = False := eq_false (by decide)
  have h1 : ((1 : Fin 2) = 1) = True := eq_true rfl
  unfold freezeAt DiagPhase.affinePushforward DiagPhase.rzGatePoly DiagPhase.cnotSubst
  simp only [map_neg, MvPolynomial.bind₁_X_right, map_add, map_sub, map_mul, map_ofNat,
    MvPolynomial.bind₁_C_right, h0, h1, if_true, if_false]
  ring

/-- **T† falls out by linearity** — the `m=3` instance of the conjugate tower. -/
theorem tGadget_dagger_correct (b : ZMod 2) :
    freezeAt (1 : Fin 2) b (DiagPhase.affinePushforward 0 1 (-DiagPhase.tGatePoly 1))
        - 2 * MvPolynomial.C (b.val : ZMod 8) * MvPolynomial.X (0 : Fin 2)
      = -DiagPhase.tGatePoly (0 : Fin 2) - MvPolynomial.C (b.val : ZMod 8) :=
  rzGadget_dagger_correct b

end FTQCLib.Frame

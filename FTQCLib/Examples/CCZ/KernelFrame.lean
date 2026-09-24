/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.CCZ.OperatorFrame
import FTQCLib.Hilbert.FrameKernel
import FTQCLib.Hierarchy.AffinePushforward
set_option linter.unusedSectionVars false
set_option linter.style.openClassical false
/-! # Physical CCZ in the kernel (phase-polynomial) frame

The companion to `OperatorFrame`. There the physical CCZ is priced *operationally* as a
product of native hardware pulses; here we re-express the same decomposition inside the
**kernel frame** — the phase-polynomial picture in which a diagonal gate is named by its
exponent polynomial `P` via `kernel P = diagonalGateEquiv (realPhase P)`.

The distinctive content of the kernel frame is **syntactic**:

* `kernel_affinePushforward` (the heart) — conjugating a kernel by a CNOT is the kernel of
  the *affine pushforward* of its exponent: `kernel (affinePushforward i k P)` = the CNOT-conjugate.
  The operator-side conjugation is realised purely as a substitution `X_k ↦ X_k ⊕ X_i` on the
  phase polynomial. The genuinely three-body `X_i X_j X_k` monomial appears in the kernel's
  exponent *for free*, as the cross term of that substitution.

* `threeBody_effectiveLevel_le` (the resource-accounting payoff) — that degree-raising
  substitution does **not** raise the effective frame level. The cross term `−2 X_i X_j X_k`
  carries an explicit factor of `2`, whose two-adic valuation absorbs the unit degree increase,
  so the level the frame charges is unchanged. This is the polynomial face of "Clifford
  conjugation is level-preserving": the syntactic degree of the exponent rises, but the priced
  resource does not.

* `cczKernel_eq_native` (the main theorem) — the full physical decomposition restated in the kernel
  frame: the CCZ kernel equals the native-pulse product (6 `ZZ` + 4 `H` + 7 `Rz`) up to the
  global phase `e^{i·5π/8}`.
-/

namespace FTQCLib.Examples.CCZ

open FTQCLib FTQCLib.Hilbert FTQCLib.Hierarchy FTQCLib.Frame FTQCLib.Hierarchy.DiagPhase

variable {n : ℕ}

/-! ### CCZ is the kernel of its exponent polynomial -/

/-- **CCZ is the kernel of `cczPoly`.** The operator-side `cczOperator` and the kernel-frame
`kernel (cczPoly i j k)` are the same diagonal gate by definition — both are
`diagonalGateEquiv (realPhase (cczPoly i j k))`. This is the bridge that lets the operator-frame
decomposition be read off in the kernel frame. -/
theorem cczOperator_eq_kernel (i j k : Fin n) :
    cczOperator i j k = kernel (DiagPhase.cczPoly i j k) := rfl

/-! ### The heart — CNOT conjugation is the affine pushforward on the exponent -/

/-- **The kernel of the affine pushforward IS the CNOT conjugate of the kernel.**

For `i ≠ k`,
`kernel (affinePushforward i k P) = CNOT_{i→k} · kernel P · CNOT_{i→k}`.

This is the syntactic core of the kernel frame: conjugating a diagonal unitary by a CNOT —
an operator-level Heisenberg conjugation — is realised *entirely* as the polynomial substitution
`X_k ↦ X_k ⊕ X_i` on the exponent (`affinePushforward`). No analysis on the operators is needed
beyond `cnotGate_conj_diag`; the rest is the eval-bridge `affinePushforward_eval_val` together with
the definitional identity `cnotBitMap = cnotPerm`. Stated for general precision `m` and any
`P : DiagPhase n m`. -/
theorem kernel_affinePushforward {m : ℕ} (i k : Fin n) (hik : i ≠ k) (P : DiagPhase n m) :
    kernel (DiagPhase.affinePushforward i k P)
      = conjEquiv (cnotGate i k hik) (kernel P) := by
  rw [kernel_def, kernel_def, cnotGate_conj_diag i k hik]
  -- Reduce to equality of the two phase functions.
  congr 1
  funext v
  unfold DiagPhase.realPhase
  -- The eval-bridge: the pushed-forward exponent at `v` equals the original at `cnotBitMap i k v`,
  -- and `cnotBitMap i k v = cnotPerm i k v` definitionally.
  rw [DiagPhase.affinePushforward_eval_val i k P v]
  rfl

/-! ### The three-body realization

Specialising the heart to the two-body monomial `c · X_j X_k` exhibits exactly how a CCZ-type
three-body phase is produced by a Clifford conjugation. The kernel of the pushforward is the CNOT
conjugate of the two-body kernel; expanding the pushforward exponent (via the `cnot_zz` identity)
shows the genuine three-body monomial `X_i X_j X_k` sitting in the kernel's exponent. -/

/-- **The three-body kernel from a two-body one.** For `i ≠ k`, the kernel of the CNOT pushforward
of the two-body phase `c · X_j X_k` is the CNOT conjugate of the two-body kernel:
`kernel (affinePushforward i k (C c · X_j X_k)) = CNOT_{i→k} · kernel (C c · X_j X_k) · CNOT_{i→k}`.
A direct instantiation of `kernel_affinePushforward`. -/
theorem threeBody_kernel {m : ℕ} (i j k : Fin n) (hik : i ≠ k) (c : ZMod (2 ^ m)) :
    kernel (DiagPhase.affinePushforward i k
        (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k)) : DiagPhase n m)
      = conjEquiv (cnotGate i k hik)
          (kernel (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k))) :=
  kernel_affinePushforward i k hik _

/-- **The three-body monomial is exposed in the exponent.** Rewriting the pushforward via
`affinePushforward_cnot_zz` (for `j ≠ k`) makes the genuine three-body term `X_i X_j X_k` explicit:
the CNOT conjugate of the two-body kernel equals the kernel of
`c · X_j X_k + c · X_i X_j − 2 c · X_i X_j X_k`. -/
theorem threeBody_kernel_exponent {m : ℕ} (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (c : ZMod (2 ^ m)) :
    conjEquiv (cnotGate i k hik)
        (kernel (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k)))
      = kernel (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k)
          + MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)
          - 2 * (MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X k))) := by
  rw [← threeBody_kernel i j k hik c, DiagPhase.affinePushforward_cnot_zz i j k c hjk]

/-! ### The resource-accounting payoff — the pushforward does not raise the frame level -/

/-- The two-body monomial `C c · (X_j · X_k)` is multilinear (degree ≤ 1 in every variable). The
factor structure forces every support exponent to be `single j 1 + single k 1` (when `j ≠ k`), which
has all entries `≤ 1`; a `C`-scaling only shrinks support. -/
private lemma isMultilinear_zz {m : ℕ} (j k : Fin n) (hjk : j ≠ k) (c : ZMod (2 ^ m)) :
    DiagPhase.IsMultilinear
      (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k) : DiagPhase n m) := by
  classical
  -- Rewrite as a single monomial, then read multilinearity off its (single) exponent vector.
  have hmon : (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k) : DiagPhase n m)
      = MvPolynomial.monomial (Finsupp.single j 1 + Finsupp.single k 1) c := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      MvPolynomial.C_mul_monomial, mul_one]
  -- The exponent `single j 1 + single k 1` has every entry ≤ 1 (since j ≠ k).
  have hd : ∀ l, (Finsupp.single j 1 + Finsupp.single k 1 : Fin n →₀ ℕ) l ≤ 1 := by
    intro l
    rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hjk
    all_goals omega
  -- Unfold `IsMultilinear`: every support exponent is `single j 1 + single k 1`.
  rw [hmon]
  intro d hd' l
  have hd_eq : d = (Finsupp.single j 1 + Finsupp.single k 1 : Fin n →₀ ℕ) :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd')
  rw [hd_eq]
  exact hd l

/-- **The level payoff.** For `i ≠ k`, `j ≠ k`, the CNOT pushforward of the two-body phase
`c · X_j X_k` has effective frame level no greater than the two-body phase itself:
`effectiveLevel (affinePushforward i k (C c · X_j X_k)) ≤ effectiveLevel (C c · X_j X_k)`.

This is the resource-accounting point. The pushforward *raises the polynomial degree* — it creates
the three-body `X_i X_j X_k` monomial (degree 3) out of a two-body (degree 2) input. Yet the
**effective level**, the resource the frame actually charges, does not rise: the three-body term
appears with coefficient `−2 c`, and the extra factor of `2` lifts its two-adic valuation by one,
which exactly cancels the one-unit degree increase in the `effLevelMonom` accounting. Clifford
(CNOT) conjugation is level-non-increasing even though the syntactic exponent grows. -/
theorem threeBody_effectiveLevel_le {m : ℕ} (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (c : ZMod (2 ^ m)) :
    DiagPhase.effectiveLevel (DiagPhase.affinePushforward i k
        (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k)) : DiagPhase n m)
      ≤ DiagPhase.effectiveLevel
          (MvPolynomial.C c * (MvPolynomial.X j * MvPolynomial.X k) : DiagPhase n m) :=
  DiagPhase.affinePushforward_effectiveLevel_le i k hik
    (isMultilinear_zz j k hjk c)

/-! ### The full physical decomposition in the kernel frame -/

/-- **The physical CCZ decomposition, stated in the kernel frame.** The kernel of `cczPoly i j k`
equals the native-pulse product `native17` — built from **6 `ZZ` interactions, 4 Hadamards (all on
`k`), and 7 `Rz` rotations** — up to the global phase `e^{i·5π/8}`. This is the native-pulse
identity read through `cczOperator_eq_kernel`: the same physical decomposition, now naming the
gate by its phase-polynomial exponent rather than as an opaque operator. -/
theorem cczKernel_eq_native (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    kernel (DiagPhase.cczPoly i j k)
      = scaleEquiv (expUnit (5 * Real.pi / 8)) (native17 i j k hik) := by
  rw [← cczOperator_eq_kernel, cczOperator_eq_native17 i j k hij hik hjk]

end FTQCLib.Examples.CCZ

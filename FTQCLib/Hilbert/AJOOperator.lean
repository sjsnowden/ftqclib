/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Codes.AJOLogical
import FTQCLib.Hilbert.Diagonal

set_option linter.unusedSectionVars false

/-! # Dyadic logical angle on a codespace-preserving uniform-angle gate

This file packages the operator-side form of the dyadic-logical-angle
classification (from `FTQCLib.Codes.AJOLogical`) as a single Lean theorem,
composing two existing results:

* The trans-logical surrogacy
  (`isTransversalLogical_iff_preservesCodespace` in
  `FTQCLib/Hilbert/Diagonal.lean`): a phase pattern `f` is trans-logical
  on a CSS code iff the diagonal gate `diagonalGate f` preserves the
  codespace.
* The F_2-side classification
  (`dyadic_logical_angle_of_trans_logical_uniform` in
  `FTQCLib/Codes/AJOLogical.lean`): trans-logical uniform-angle `θ` forces
  the logical angle `θ_L = wt(g_L) · θ` to be a dyadic multiple of `2π`.

Chaining: if the diagonal uniform-angle gate
`diagonalGate (linearPhase θ)` preserves the codespace, then
`wt(g_L) · θ` is dyadic.

This is **strictly weaker** than AJO 2014 Theorem 1
(Anderson--Jochym-O'Connor, arXiv:1409.8320), which forces the
physical angle `θ` itself dyadic. See the header of
`FTQCLib/Codes/AJOLogical.lean` for the precise relationship between this
weaker conclusion and the full AJO 2014 statement.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Codes Matrix

variable {n r_X r_Z : ℕ}

/-- **Dyadic logical angle for a codespace-preserving uniform-angle
diagonal gate.** For a CSS code with non-degenerate X-stabilisers and
a well-supported logical representative `g_L`, if the uniform-angle
diagonal gate `diagonalGate (linearPhase (λ _, θ))` preserves the
codespace, then the logical angle `wt(g_L) · θ` is a dyadic multiple
of `2π`.

The hypothesis `PreservesCodespace ...` is the operator-side
codespace-preservation condition; via the trans-logical surrogacy it
is equivalent to the F_2-side trans-logical hypothesis. The
conclusion is the dyadic logical-angle classification of
`FTQCLib.Codes.AJOLogical`.

This is **strictly weaker** than AJO 2014 Theorem 1 — see the file
header. -/
theorem dyadic_logical_angle_of_codespace_preserving_uniform
    {θ : ℝ} {k_0 : ℤ} {m_0 : ℕ} (hm_0 : 0 < m_0)
    (hθ : θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ))
    (hcop : Int.gcd k_0 (m_0 : ℤ) = 1)
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_preserves : PreservesCodespace
                    (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1) :
    ∃ (a : ℤ) (N : ℕ),
      (hammingWeight g_L : ℝ) * θ =
        2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  -- Translate the operator-side hypothesis to the F_2 side via the
  -- trans-logical surrogacy.
  have h_trans : IsTransversalLogical
                    (linearPhase (fun _ : Fin n => θ)) H_X H_Z :=
    isTransversalLogical_iff_preservesCodespace.mpr h_preserves
  -- Apply the F_2-side dyadic logical-angle classification.
  exact dyadic_logical_angle_of_trans_logical_uniform
    hm_0 hθ hcop h_trans h_carrier h_wellSupp

/-- **Packaged form with rational existence.** Same as
`dyadic_logical_angle_of_codespace_preserving_uniform` but the
rational-form hypothesis is existential rather than spelled out as
`(k_0, m_0)`. -/
theorem dyadic_logical_angle_of_codespace_preserving_uniform_of_rational
    {θ : ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (h_preserves : PreservesCodespace
                    (linearPhase (fun _ : Fin n => θ)) H_X H_Z)
    {g_L : Fin n → ZMod 2} (h_carrier : g_L ∈ cssXLogicalCarrier H_Z)
    (h_wellSupp : ∀ j : Fin n, g_L j = 1 → ∃ i : Fin r_X, H_X i j = 1)
    (h_rational : ∃ (k_0 : ℤ) (m_0 : ℕ), 0 < m_0 ∧
                  Int.gcd k_0 (m_0 : ℤ) = 1 ∧
                  θ = 2 * Real.pi * (k_0 : ℝ) / (m_0 : ℝ)) :
    ∃ (a : ℤ) (N : ℕ),
      (hammingWeight g_L : ℝ) * θ =
        2 * Real.pi * (a : ℝ) / ((2 : ℝ) ^ N) := by
  obtain ⟨k_0, m_0, hm_0, hcop, hθ⟩ := h_rational
  exact dyadic_logical_angle_of_codespace_preserving_uniform
    hm_0 hθ hcop h_preserves h_carrier h_wellSupp

end FTQCLib.Hilbert

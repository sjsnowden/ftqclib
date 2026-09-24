/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.QubitSpace
import FTQCLib.CSS.Defs
import FTQCLib.CSS.Logical

set_option linter.unusedSectionVars false

/-! # Codespace as a vector subspace of the qubit Hilbert space

For a CSS code with parity-check matrices `(H_X, H_Z)`, the codespace
`Code(H_X, H_Z) ⊂ QubitSpace n` is the simultaneous `+1` eigenspace
of all stabilizers. In computational-basis notation:

  Code(H_X, H_Z) = span_ℂ { |ψ_x⟩ : x ∈ ker(H_Z) }

where `|ψ_x⟩ = ∑_{h ∈ row(H_X)} |x + h⟩` is the unnormalised codestate
corresponding to seed `x`. Two seeds `x, x'` in the same coset of
`row(H_X)` give the same codestate; different cosets give different
(orthogonal) codestates. The dimension of `Code(H_X, H_Z)` is `2^k`
where `k = dim(ker(H_Z) / row(H_X))` is the number of logical qubits.

This file:

* **`codestate H_X x`** — the unnormalised codestate for seed `x`.
* **`codespace H_X H_Z`** — the codespace as a `Submodule ℂ`.
* **Sanity lemmas** — codestate support equals `x + row(H_X)`;
  codestate is fixed by X-stabilizer shifts.

We work with unnormalised codestates because the chapter 3
equivalence work concerns codespace preservation (a vector-subspace
condition), not state normalisation. Normalisation would be needed
for inner-product or measurement statements but is orthogonal to the
trans-logical equivalence theorem.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.CSS

variable {n r_X r_Z : ℕ}

/-- The unnormalised codestate seeded at `x`: the formal sum
`∑_{h ∈ row(H_X)} |x + h⟩` over the X-stabilizer subgroup.

As a function `(Fin n → ZMod 2) → ℂ`, it takes value `1` at every
`y ∈ x + row(H_X)` and `0` elsewhere. -/
noncomputable def codestate
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) : QubitSpace n :=
  open Classical in
  fun y => if y - x ∈ cssXLogicalSubspace H_X then 1 else 0

/-- The codespace of a CSS code `(H_X, H_Z)`: the `ℂ`-span of all
codestates seeded by elements of `ker(H_Z)`. Equivalently, the
simultaneous `+1` eigenspace of all stabilizers; here we
characterise it by spanning explicit codestates rather than via
projectors. -/
noncomputable def codespace
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) :
    Submodule ℂ (QubitSpace n) :=
  Submodule.span ℂ
    (Set.range (fun (xh : cssXLogicalCarrier H_Z) => codestate H_X xh.val))

/-! ## Codestate support and shift invariance -/

/-- The codestate `codestate H_X x` is nonzero precisely at `x +
row(H_X)`: the coset of the X-stabilizer subgroup containing `x`. -/
theorem codestate_apply
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (x y : Fin n → ZMod 2) :
    codestate H_X x y =
      open Classical in
      if y - x ∈ cssXLogicalSubspace H_X then (1 : ℂ) else 0 := rfl

/-- Shift invariance: `codestate H_X x = codestate H_X (x + h)` for any
`h ∈ row(H_X)`. Two seeds in the same coset of `row(H_X)` give the
same codestate. -/
theorem codestate_shift
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (x h : Fin n → ZMod 2) (hh : h ∈ cssXLogicalSubspace H_X) :
    codestate H_X (x + h) = codestate H_X x := by
  funext y
  unfold codestate
  congr 1
  -- y - (x + h) = (y - x) - h. Membership in `row(H_X)` is preserved
  -- by adding/subtracting an element of `row(H_X)`.
  refine propext ⟨?_, ?_⟩
  · intro hy
    have : y - x = (y - (x + h)) + h := by ring
    rw [this]
    exact Submodule.add_mem _ hy hh
  · intro hy
    have : y - (x + h) = (y - x) - h := by ring
    rw [this]
    exact Submodule.sub_mem _ hy hh

/-- Codestates seeded by `0` and by a stabilizer element coincide. -/
theorem codestate_stab_eq_zero
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (h : Fin n → ZMod 2) (hh : h ∈ cssXLogicalSubspace H_X) :
    codestate H_X h = codestate H_X 0 := by
  have := codestate_shift H_X 0 h hh
  rw [zero_add] at this
  exact this

end FTQCLib.Hilbert

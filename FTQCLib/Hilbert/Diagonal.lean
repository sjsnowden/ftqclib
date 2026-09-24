/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Hilbert.Codespace
import FTQCLib.Codes.AJO
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option linter.unusedSectionVars false

/-! # Diagonal transversal gates and the equivalence to `IsTransversalLogical`

This file builds the operator side of the chapter 3 surrogacy:

* The diagonal unitary `diagonalGate f` on `QubitSpace n`, acting on
  the computational basis as `|v⟩ ↦ e^{i·f(v)} |v⟩` for a phase
  pattern `f : (Fin n → ZMod 2) → ℝ`.
* The `PreservesCodespace` predicate — the operator-side statement
  "the diagonal gate maps the codespace into itself".
* The main equivalence:

      IsTransversalLogical f H_X H_Z ↔ PreservesCodespace f H_X H_Z

This is the formal verification that the F_2-side surrogate predicate
`IsTransversalLogical` from `FTQCLib/Codes/AJO.lean` is equivalent to the
operator-side statement on the qubit Hilbert space.

The equivalence is structural — no AJO combinatorial content. The
forward direction (trans-logical → preserves codespace) is direct:
trans-logical implies that the diagonal phase factor `e^{i·f(y)}` is
constant on each coset `x + row(H_X)`, so the gate acts on each
codestate as a global phase, sending it back to a codestate (a scalar
multiple of itself). The reverse direction (preserves codespace →
trans-logical) extracts the constancy on cosets from the
codestate-mapping condition: if the gate maps `codestate H_X x` to an
element of the codespace, that element is a linear combination of
codestates, and matching coefficients on the coset `x + row(H_X)`
forces the phase factors to agree modulo `2π`.
-/

namespace FTQCLib.Hilbert

open FTQCLib.Pauli FTQCLib.CSS FTQCLib.Codes Complex

variable {n r_X r_Z : ℕ}

/-- The diagonal unitary realising phase pattern `f`. As a linear map
on `QubitSpace n`, it sends `ψ` to `v ↦ e^{i · f(v)} · ψ(v)`. The
action on computational-basis vectors is
`diagonalGate f |v⟩ = e^{i · f(v)} |v⟩`.

The gate is `ℂ`-linear (multiplication by a fixed phase function
preserves linear combinations). Unitarity follows from `|e^{iθ}| = 1`
for real θ; we do not need unitarity here, only the linear-map
structure. -/
noncomputable def diagonalGate (f : (Fin n → ZMod 2) → ℝ) :
    QubitSpace n →ₗ[ℂ] QubitSpace n where
  toFun ψ := fun v => Complex.exp (Complex.I * f v) * ψ v
  map_add' x y := by
    funext v
    simp [mul_add]
  map_smul' c x := by
    funext v
    simp
    ring

/-- The diagonal gate's action on a computational-basis vector
`|v⟩` produces `e^{i f(v)} |v⟩`. -/
@[simp] theorem diagonalGate_computational
    (f : (Fin n → ZMod 2) → ℝ) (v : Fin n → ZMod 2) :
    diagonalGate f (computational v) =
      Complex.exp (Complex.I * f v) • computational v := by
  funext w
  unfold diagonalGate computational
  by_cases h : w = v
  · subst h; simp
  · simp [h]

/-- The diagonal gate's pointwise action on a function: at index `v`,
the output is `e^{i f(v)}` times the input at `v`. -/
@[simp] theorem diagonalGate_apply
    (f : (Fin n → ZMod 2) → ℝ) (ψ : QubitSpace n) (v : Fin n → ZMod 2) :
    diagonalGate f ψ v = Complex.exp (Complex.I * f v) * ψ v := rfl

/-! ## The operator-side predicate `PreservesCodespace` -/

/-- A diagonal gate with phase pattern `f` *preserves the codespace*
of CSS code `(H_X, H_Z)` iff its image of the codespace is contained
in the codespace. -/
def PreservesCodespace (f : (Fin n → ZMod 2) → ℝ)
    (H_X : Matrix (Fin r_X) (Fin n) (ZMod 2))
    (H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)) : Prop :=
  ∀ ψ ∈ codespace H_X H_Z, diagonalGate f ψ ∈ codespace H_X H_Z

/-! ## Forward direction: trans-logical implies preservation -/

/-- Helper: if two reals differ by an integer multiple of `2π`, their
phase factors `exp(i · _)` agree. -/
private lemma exp_I_eq_of_diff_two_pi_int
    {a b : ℝ} {k : ℤ} (h : a - b = 2 * Real.pi * k) :
    Complex.exp (Complex.I * a) = Complex.exp (Complex.I * b) := by
  have hR : a = b + 2 * Real.pi * (k : ℝ) := by linarith
  have hC : (a : ℂ) = (b : ℂ) + 2 * Real.pi * (k : ℂ) := by exact_mod_cast hR
  have h1 : Complex.I * (a : ℂ) =
      Complex.I * (b : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    calc Complex.I * (a : ℂ)
        = Complex.I * ((b : ℂ) + 2 * Real.pi * (k : ℂ)) := by rw [← hC]
      _ = Complex.I * (b : ℂ) + Complex.I * (2 * Real.pi * (k : ℂ)) := by ring
      _ = Complex.I * (b : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Forward direction of the equivalence.** If `f` is trans-logical
on `(H_X, H_Z)` then the diagonal gate `diagonalGate f` maps each
codestate `codestate H_X x` (for `x ∈ ker(H_Z)`) to a scalar multiple
of itself. -/
theorem diagonalGate_codestate_of_transversalLogical
    {f : (Fin n → ZMod 2) → ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hTransv : Codes.IsTransversalLogical f H_X H_Z)
    {x : Fin n → ZMod 2} (hx : x ∈ cssXLogicalCarrier H_Z) :
    diagonalGate f (codestate H_X x) =
      Complex.exp (Complex.I * f x) • codestate H_X x := by
  funext y
  by_cases hy : y - x ∈ cssXLogicalSubspace H_X
  · -- On the support: codestate H_X x y = 1; need exp(I·f y) = exp(I·f x).
    have hψ : codestate H_X x y = 1 := by
      unfold codestate; simp [hy]
    rw [diagonalGate_apply, hψ, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, hψ, mul_one]
    -- Trans-logical at v = x, h = y - x gives f(y) - f(x) = 2π·k.
    have hy_eq : x + (y - x) = y := by ring
    obtain ⟨k, hk⟩ := hTransv x hx (y - x) hy
    rw [hy_eq] at hk
    -- Apply the helper lemma with a = f y, b = f x.
    exact exp_I_eq_of_diff_two_pi_int hk
  · -- Off the support: codestate = 0, so both sides vanish.
    have hψ : codestate H_X x y = 0 := by
      unfold codestate; simp [hy]
    rw [diagonalGate_apply, hψ]
    simp [hψ]

/-- **Forward direction of the equivalence.** If `f` is trans-logical
on `(H_X, H_Z)`, then `diagonalGate f` preserves the codespace. -/
theorem PreservesCodespace.of_transversalLogical
    {f : (Fin n → ZMod 2) → ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hTransv : Codes.IsTransversalLogical f H_X H_Z) :
    PreservesCodespace f H_X H_Z := by
  intro ψ hψ
  -- By linearity it suffices to handle the codestate generators.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro ψ' ⟨x, rfl⟩
    have := diagonalGate_codestate_of_transversalLogical hTransv x.property
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · simp
  · intros x y _ _ hx hy
    rw [(diagonalGate f).map_add]
    exact Submodule.add_mem _ hx hy
  · intros c x _ hx
    rw [(diagonalGate f).map_smul]
    exact Submodule.smul_mem _ _ hx

/-! ## Reverse direction: preservation implies trans-logical -/

/-- **Codespace elements are constant on cosets of `row(H_X)`.** Every
element `ψ ∈ codespace H_X H_Z` satisfies `ψ y = ψ y'` whenever
`y - y' ∈ row(H_X)`. This is the structural fact that codestates are
constant on cosets, lifted to arbitrary codespace elements by
linearity. -/
theorem codespace_const_on_coset
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    {ψ : QubitSpace n} (hψ : ψ ∈ codespace H_X H_Z)
    {y y' : Fin n → ZMod 2}
    (hyy' : y - y' ∈ cssXLogicalSubspace H_X) :
    ψ y = ψ y' := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · -- Generator case: ψ = codestate H_X x.val.
    rintro ψ' ⟨x, rfl⟩
    have h1 : (y - x.val ∈ cssXLogicalSubspace H_X) ↔
              (y' - x.val ∈ cssXLogicalSubspace H_X) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have : y' - x.val = (y - x.val) - (y - y') := by ring
        rw [this]
        exact Submodule.sub_mem _ h hyy'
      · have : y - x.val = (y' - x.val) + (y - y') := by ring
        rw [this]
        exact Submodule.add_mem _ h hyy'
    change codestate H_X x.val y = codestate H_X x.val y'
    unfold codestate
    by_cases h : y - x.val ∈ cssXLogicalSubspace H_X
    · rw [if_pos h, if_pos (h1.mp h)]
    · rw [if_neg h, if_neg (fun hy' => h (h1.mpr hy'))]
  · -- Zero case.
    rfl
  · -- Sum: (ψ₁ + ψ₂) y = ψ₁ y + ψ₂ y = ψ₁ y' + ψ₂ y' = (ψ₁ + ψ₂) y'.
    intros ψ₁ ψ₂ _ _ h₁ h₂
    change ψ₁ y + ψ₂ y = ψ₁ y' + ψ₂ y'
    rw [h₁, h₂]
  · -- Scalar: (c • ψ) y = c · ψ y = c · ψ y' = (c • ψ) y'.
    intros c ψ' _ h'
    change c * ψ' y = c * ψ' y'
    rw [h']

/-- **Reverse direction of the equivalence.** If `diagonalGate f`
preserves the codespace of a CSS code, then `f` is trans-logical. The
argument: apply the gate to a codestate `codestate H_X v` (well-defined
because `v ∈ ker(H_Z)`); the result has values `e^{i·f(v)}` and
`e^{i·f(v + h)}` at `v` and `v + h` respectively (both in the support
of the codestate). The result is in the codespace, hence constant on
cosets by `codespace_const_on_coset`. So `e^{i·f(v)} = e^{i·f(v + h)}`,
forcing `f(v + h) - f(v) ∈ 2π·ℤ`. -/
theorem PreservesCodespace.toTransversalLogical
    {f : (Fin n → ZMod 2) → ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)}
    (hPres : PreservesCodespace f H_X H_Z) :
    Codes.IsTransversalLogical f H_X H_Z := by
  intro v hv h hh
  -- Apply the gate to codestate H_X v ∈ codespace.
  have hcs : codestate H_X v ∈ codespace H_X H_Z :=
    Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩
  have hGate : diagonalGate f (codestate H_X v) ∈ codespace H_X H_Z :=
    hPres _ hcs
  -- The image is constant on cosets. Evaluate at v and v + h:
  -- both are in the support of codestate H_X v (since h ∈ row(H_X)),
  -- so the codestate values are both 1, and the gate values are
  -- e^{i·f(v)} and e^{i·f(v+h)}.
  have hvh : v + h - v ∈ cssXLogicalSubspace H_X := by
    have : v + h - v = h := by ring
    rw [this]; exact hh
  have hConst := codespace_const_on_coset hGate hvh
  -- Compute the two values.
  have hAtv : diagonalGate f (codestate H_X v) v = Complex.exp (Complex.I * f v) := by
    rw [diagonalGate_apply]
    have : codestate H_X v v = 1 := by
      unfold codestate
      simp
    rw [this, mul_one]
  have hAtvh : diagonalGate f (codestate H_X v) (v + h) =
      Complex.exp (Complex.I * f (v + h)) := by
    rw [diagonalGate_apply]
    have : codestate H_X v (v + h) = 1 := by
      unfold codestate
      have : v + h - v = h := by ring
      rw [this]; simp [hh]
    rw [this, mul_one]
  rw [hAtv, hAtvh] at hConst
  -- hConst : exp(I·f(v+h)) = exp(I·f v). Want: f(v+h) - f(v) ∈ 2π·ℤ.
  have hExpEq : Complex.exp (Complex.I * f (v + h)) =
                Complex.exp (Complex.I * f v) := hConst
  -- Extract f(v+h) - f(v) ∈ 2π·ℤ from the exp equality.
  rw [Complex.exp_eq_exp_iff_exists_int] at hExpEq
  obtain ⟨k, hk⟩ := hExpEq
  -- hk : I * f(v+h) = I * f v + k * (2π·I)
  refine ⟨k, ?_⟩
  -- Multiply both sides by I^{-1} = -I or equivalently divide. We'll
  -- extract the real-valued equation from hk.
  have hk_real : (f (v + h) : ℂ) - (f v : ℂ) = 2 * Real.pi * (k : ℂ) := by
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    -- I · f(v+h) - I · f v = I · (f(v+h) - f v) = k · (2π·I)
    have : Complex.I * (f (v + h) : ℂ) - Complex.I * (f v : ℂ) =
           (k : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination hk
    have : Complex.I * ((f (v + h) : ℂ) - (f v : ℂ)) =
           Complex.I * (2 * Real.pi * (k : ℂ)) := by
      rw [show Complex.I * ((f (v + h) : ℂ) - (f v : ℂ)) =
              Complex.I * (f (v + h) : ℂ) - Complex.I * (f v : ℂ) from by ring]
      rw [this]
      ring
    exact mul_left_cancel₀ hI this
  -- Convert the complex equation to a real equation.
  have : (f (v + h) : ℝ) - f v = 2 * Real.pi * k := by exact_mod_cast hk_real
  linarith

/-! ## Main equivalence theorem -/

/-- **The equivalence.** A diagonal gate `diagonalGate f` preserves the
codespace of a CSS code `(H_X, H_Z)` if and only if `f` is
transversal-logical on `(H_X, H_Z)`.

This is the formal verification that the F_2-side surrogate predicate
`IsTransversalLogical` from `FTQCLib/Codes/AJO.lean` is equivalent to the
operator-side statement on the qubit Hilbert space `QubitSpace n`.
For chapter 3's AJO and EK arguments, this equivalence discharges the
"surrogacy" of the algebraic-skin formulation: trans-logical is not
just a "definition" of preservation, it is provably equivalent. -/
theorem isTransversalLogical_iff_preservesCodespace
    {f : (Fin n → ZMod 2) → ℝ}
    {H_X : Matrix (Fin r_X) (Fin n) (ZMod 2)}
    {H_Z : Matrix (Fin r_Z) (Fin n) (ZMod 2)} :
    Codes.IsTransversalLogical f H_X H_Z ↔ PreservesCodespace f H_X H_Z :=
  ⟨PreservesCodespace.of_transversalLogical,
   PreservesCodespace.toTransversalLogical⟩

end FTQCLib.Hilbert

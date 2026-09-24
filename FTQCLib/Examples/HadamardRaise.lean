/-
Copyright (c) 2026 Sam Snowden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam Snowden
-/
import FTQCLib.Examples.HadamardPhase
import FTQCLib.Hierarchy.DyadicValuation

/-!
# H at a support-raising bit: the correlated-bit Hadamard

`applyHPinned` (`HadamardGate.lean`) frees a bit whose value is *definite*: the emitted sign's
coefficient is the constant `x₀ i`. `applyHFiner` (`HadamardPhase.lean`) handles a bit already
X-supported. Between them sits the case neither covers: a bit whose value is neither definite nor
free but **correlated** with the other bits — the generic bit of an entangled state, where
`e_i ∉ π_X(L)` yet the coordinate functional `v ↦ v i` does not vanish on the shadow.

This file supplies that case. On the support the coordinate functional is represented by some `u`
with `u i = 0`, so the Hadamarded coordinate reads the branch value
`t(z) = x₀ i + u ⬝ x₀ + u ⬝ z`; H freezes the coordinate to `t` and emits the sign
`2^{m−1}·t·X_i`. Two polynomial forms of `t` appear, and keeping them straight is the file's one
subtlety:

* the **multilinear XOR form** `xorForm u b` (a `polyXor`-fold), whose evaluation at every binary
  point is the `𝔽₂` branch value (`xorForm_eval`) — the only form that may be **substituted**
  into the exponent (`raiseSubst`), because the exponent is read at full precision;
* the **ordinary-sum affine form** `raiseForm u b`, degree 1, which agrees with the XOR form
  **only under the factor `2^{m−1}`** (`two_pow_mul_xorForm`: every carry correction carries a
  factor `2`, and `2·2^{m−1} = 0`) — so it may be used in the emitted sign and nowhere else.
  Substituting it is wrong from `m = 2`; see `hRaise_sParity_exponent` for the aimed witness.

Everything here is frame-pure: `DiagPhase`, `Pauli`, `Submodule`, `ℂ`. No `FTQCLib.Hilbert`.

**Relation to the floor eliminators.** On a floor this raise branch is the `e_k ∉ π_X(L)` case of
`hFloor` (`FTQCLib/Examples/HadamardElimination.lean`), which chooses the representer; the aimed
control rows of `raiseForm` at `m = 3` are in `FTQCLib/Examples/CarrierCliffordCheck.lean` (the
two-qubit rotate example).

## Main definitions

* `polyXor`, `xorForm` — XOR as a polynomial operation on binary-valued phase polynomials, and
  the multilinear affine-XOR form it folds up to.
* `raiseForm` — the degree-1 ordinary-sum form, valid only under `2^{m−1}`.
* `raiseSubst` — the affine freeze: substitute the XOR form for the Hadamarded coordinate.
* `hRaise` — H at a support-raising bit.

## Main results

* `xorForm_eval`, `raiseSubst_eval`, `hRaise_eval` — the eval bridges, hypothesis-free.
* `two_pow_mul_xorForm` — the identity scoping the ordinary form to the emitted slot.
* `hRaise_bell_exponent`, `hRaise_sParity_exponent` — the two aimed witnesses (`m = 1` Bell;
  `m = 2` with the exponent reading the bit, a nonzero offset, and two correlated bits).
* `update_sub_update`, `branch_unique` — at most one Walsh branch survives off the shadow.

## Implementation notes

* The `DiagPhase.eval` ring-map lemmas (`eval_add`/`eval_mul`/`eval_C`/`eval_X`) are declared
  into `FTQCLib.Hierarchy.DiagPhase`, their owning namespace. Their physical home is
  `FTQCLib/Hierarchy/Defs.lean`.
* The example records fix `L`/`c` to placeholders (`⊤`, `1`): the `Q`-component of `hRaise`
  reads neither field, and the support half of the gate is proved separately
  (`HadamardTotality.lean`).
* `u` is data. That a representer with `u i = 0` exists for every off-shadow bit
  (`exists_representer`), and that the output amplitude does not depend on the choice
  (`amp_hRaise_indep`), are proved in `HadamardTotality.lean` and `HadamardAmplitude.lean`.
-/

namespace FTQCLib.Frame.Walkthrough

open FTQCLib FTQCLib.Pauli FTQCLib.Hierarchy FTQCLib.Stabilizer

variable {n : ℕ}

/-! ## The `𝔽₂` data of the branch -/

/-- The `𝔽₂` pairing `u ⬝ v`. -/
def dotF2 {n : ℕ} (u v : Fin n → ZMod 2) : ZMod 2 := ∑ j, u j * v j

/-- The constant of the branch form: `x₀ i + u ⬝ x₀`. On the support the Hadamarded coordinate
reads `v i = x₀ i + u ⬝ (v + x₀) + u ⬝ x₀ ⬝ …`; concretely, the branch value at `z` is
`raiseConst + u ⬝ z`, and the `u ⬝ x₀` term is invisible whenever `x₀ = 0`. -/
def raiseConst {n : ℕ} (i : Fin n) (u x₀ : Fin n → ZMod 2) : ZMod 2 := x₀ i + dotF2 u x₀

/-! ## XOR as a polynomial operation -/

/-- XOR as a polynomial operation: `A ⊕ B = A + B − 2·A·B`. On `{0,1}`-valued arguments this
computes XOR; the `2·A·B` term is the carry correction, and it is exactly what the ordinary sum
drops. -/
noncomputable def polyXor {N m : ℕ} (A B : DiagPhase N m) : DiagPhase N m :=
  A + B - MvPolynomial.C 2 * A * B

instance polyXorCommutative {N m : ℕ} : Std.Commutative (polyXor (N := N) (m := m)) :=
  ⟨fun A B => by unfold polyXor; ring⟩

instance polyXorAssociative {N m : ℕ} : Std.Associative (polyXor (N := N) (m := m)) :=
  ⟨fun A B C => by unfold polyXor; ring⟩

/-- `polyXor` evaluates to the arithmetic blend `a + b − 2ab`. -/
theorem polyXor_eval {N m : ℕ} (A B : DiagPhase N m) (v : Fin N → ZMod 2) :
    DiagPhase.eval (polyXor A B) v
      = DiagPhase.eval A v + DiagPhase.eval B v
        - 2 * (DiagPhase.eval A v * DiagPhase.eval B v) := by
  simp only [polyXor, DiagPhase.eval, map_sub, map_add, map_mul, MvPolynomial.eval_C]
  ring

/-- The `ℕ`-val of an `𝔽₂` sum, cast into `ZMod (2^m)`: XOR is the arithmetic blend. This is
the induction step of `fold_polyXor_eval`, read right-to-left. -/
theorem val_add_val {m : ℕ} (a b : ZMod 2) :
    (((a + b).val : ZMod (2 ^ m)))
      = (a.val : ZMod (2 ^ m)) + (b.val : ZMod (2 ^ m))
        - 2 * ((a.val : ZMod (2 ^ m)) * (b.val : ZMod (2 ^ m))) := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have e11 : ((1 : ZMod 2) + 1) = 0 := by decide
  have v0 : ((0 : ZMod 2)).val = 0 := by decide
  have v1 : ((1 : ZMod 2)).val = 1 := by decide
  rcases h a with ha | ha <;> rcases h b with hb | hb <;> subst ha <;> subst hb <;>
    simp only [add_zero, zero_add, e11, v0, v1] <;> push_cast <;> ring

/-- The `ℕ`-val of an `𝔽₂` product, cast into `ZMod (2^m)`. -/
theorem val_mul_val {m : ℕ} (a b : ZMod 2) :
    (((a * b).val : ZMod (2 ^ m))) = (a.val : ZMod (2 ^ m)) * (b.val : ZMod (2 ^ m)) := by
  have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have v0 : ((0 : ZMod 2)).val = 0 := by decide
  have v1 : ((1 : ZMod 2)).val = 1 := by decide
  rcases h a with ha | ha <;> rcases h b with hb | hb <;> subst ha <;> subst hb <;>
    simp only [mul_zero, mul_one, v0, v1] <;> push_cast <;> ring

/-! ## The multilinear XOR form -/

/-- The multilinear XOR form on the free block: the `polyXor`-fold of the active variables onto
the constant. Its evaluation at every binary point is the `𝔽₂` branch value (`xorForm_eval`),
which is what makes it substitutable at full precision. -/
noncomputable def xorForm {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2) :
    DiagPhase (n + h) m :=
  Finset.univ.fold polyXor (MvPolynomial.C ((b.val : ZMod (2 ^ m))))
    fun j : Fin n =>
      MvPolynomial.C (((u j).val : ZMod (2 ^ m))) * MvPolynomial.X (Fin.castAdd h j)

/-- The fold bridge: over any index set `s`, the `polyXor`-fold evaluates to the `val` of the
`𝔽₂` affine value over `s`. -/
theorem fold_polyXor_eval {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2)
    (z : Fin (n + h) → ZMod 2) (s : Finset (Fin n)) :
    DiagPhase.eval
        (s.fold polyXor (MvPolynomial.C ((b.val : ZMod (2 ^ m)))) fun j =>
          MvPolynomial.C (((u j).val : ZMod (2 ^ m))) * MvPolynomial.X (Fin.castAdd h j)) z
      = (((b + ∑ j ∈ s, u j * z (Fin.castAdd h j)).val : ZMod (2 ^ m))) := by
  induction s using Finset.cons_induction with
  | empty => simp [DiagPhase.eval]
  | cons a s ha ih =>
      rw [Finset.fold_cons, polyXor_eval, ih, Finset.sum_cons]
      have hf : DiagPhase.eval
          (MvPolynomial.C (((u a).val : ZMod (2 ^ m))) * MvPolynomial.X (Fin.castAdd h a)) z
          = (((u a * z (Fin.castAdd h a)).val : ZMod (2 ^ m))) := by
        rw [DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X, val_mul_val]
      rw [hf, ← val_add_val]
      have harg : u a * z (Fin.castAdd h a) + (b + ∑ j ∈ s, u j * z (Fin.castAdd h j))
          = b + (u a * z (Fin.castAdd h a) + ∑ j ∈ s, u j * z (Fin.castAdd h j)) := by
        ring
      rw [harg]

/-- **Eval bridge for the XOR form** — hypothesis-free: at every binary point the multilinear
form computes the `val` of the `𝔽₂` branch value `b + u ⬝ z`. Contrast `raiseForm`, whose
ordinary sum leaves `{0,1}` from `m = 2`. -/
theorem xorForm_eval {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2)
    (z : Fin (n + h) → ZMod 2) :
    DiagPhase.eval (xorForm (h := h) (m := m) u b) z
      = (((b + dotF2 u fun j => z (Fin.castAdd h j)).val : ZMod (2 ^ m))) := by
  unfold xorForm dotF2
  exact fold_polyXor_eval u b z Finset.univ

/-! ## The ordinary-sum form, and its exact scope -/

/-- The ordinary-sum affine form `b + Σ_j u_j X_j` on the free block, degree 1. **Valid only
under the factor `2^{m−1}`** (`two_pow_mul_xorForm`): its ordinary sum drops the XOR carries,
each of which costs a factor `2` and dies against `2^{m−1}`. It is used in the emitted sign,
where it keeps the sign term at degree 2; substituting it into an exponent instead of `xorForm`
denotes the wrong state from `m = 2`. -/
noncomputable def raiseForm {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2) :
    DiagPhase (n + h) m :=
  MvPolynomial.C ((b.val : ZMod (2 ^ m)))
    + ∑ j : Fin n, MvPolynomial.C (((u j).val : ZMod (2 ^ m))) * MvPolynomial.X (Fin.castAdd h j)

/-- Eval bridge for `raiseForm`: the ordinary sum `b + Σ_j u_j · z_j` in `ZMod (2^m)`. -/
theorem raiseForm_eval {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2)
    (z : Fin (n + h) → ZMod 2) :
    DiagPhase.eval (raiseForm (h := h) (m := m) u b) z
      = ((b.val : ZMod (2 ^ m)))
        + ∑ j : Fin n, ((u j).val : ZMod (2 ^ m)) * ((z (Fin.castAdd h j)).val : ZMod (2 ^ m)) := by
  simp only [raiseForm, DiagPhase.eval_add, DiagPhase.eval_C]
  congr 1
  simp only [DiagPhase.eval, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← DiagPhase.eval, DiagPhase.eval_mul, DiagPhase.eval_C, DiagPhase.eval_X]

/-- **The emitted-slot identity.** Under `2^{m−1}` the multilinear XOR form and the ordinary-sum
affine form are the *same polynomial*: every carry correction carries a factor `2`. This is the
precise scope of the ordinary form — the sign slot, and nothing else. -/
theorem two_pow_mul_xorForm {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2) :
    MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * xorForm (h := h) u b
      = MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * raiseForm (h := h) u b := by
  have hkey : MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1))
      * (MvPolynomial.C (2 : ZMod (2 ^ m)) : DiagPhase (n + h) m) = 0 := by
    rw [← MvPolynomial.C_mul, two_pow_pred_mul_two, MvPolynomial.C_0]
  have expand : ∀ A F : DiagPhase (n + h) m,
      MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * polyXor A F
        = MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * A
          + MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * F
          - MvPolynomial.C ((2 : ZMod (2 ^ m)) ^ (m - 1)) * MvPolynomial.C 2 * (A * F) := by
    intro A F
    unfold polyXor
    ring
  unfold xorForm raiseForm
  induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.fold_cons, expand, hkey, zero_mul, sub_zero, ih, Finset.sum_cons]
      ring

/-- Eval form of the emitted-slot identity: under `2^{m−1}`, the ordinary form's value is the
branch value's `val`. -/
theorem two_pow_mul_raiseForm_eval {n h m : ℕ} (u : Fin n → ZMod 2) (b : ZMod 2)
    (z : Fin (n + h) → ZMod 2) :
    (2 : ZMod (2 ^ m)) ^ (m - 1) * DiagPhase.eval (raiseForm (h := h) u b) z
      = (2 : ZMod (2 ^ m)) ^ (m - 1)
          * (((b + dotF2 u fun j => z (Fin.castAdd h j)).val : ZMod (2 ^ m))) := by
  have h1 := congrArg (fun P : DiagPhase (n + h) m => DiagPhase.eval P z)
    (two_pow_mul_xorForm (h := h) (m := m) u b)
  simp only [DiagPhase.eval_mul, DiagPhase.eval_C, xorForm_eval] at h1
  exact h1.symm

/-! ## The affine freeze -/

/-- **The affine freeze.** Substitute the multilinear XOR form for the Hadamarded coordinate,
everywhere in the exponent. At `u = 0` this is the constant substitution `freezeAt`
(`raiseSubst_zero_eval`) — which is why the pinned mode never needed anything more. -/
noncomputable def raiseSubst {n h m : ℕ} (i : Fin n) (u : Fin n → ZMod 2) (b : ZMod 2)
    (Q : DiagPhase (n + h) m) : DiagPhase (n + h) m :=
  MvPolynomial.bind₁
    (fun l => if l = Fin.castAdd h i then xorForm u b else MvPolynomial.X l) Q

/-- **Eval bridge for the freeze** — hypothesis-free: substituting then evaluating equals
evaluating with the coordinate set to the `𝔽₂` branch value. The affine cousin of
`freezeAt_eval`. -/
theorem raiseSubst_eval {n h m : ℕ} (i : Fin n) (u : Fin n → ZMod 2) (b : ZMod 2)
    (Q : DiagPhase (n + h) m) (z : Fin (n + h) → ZMod 2) :
    DiagPhase.eval (raiseSubst i u b Q) z
      = DiagPhase.eval Q (Function.update z (Fin.castAdd h i)
          (b + dotF2 u fun j => z (Fin.castAdd h j))) := by
  unfold raiseSubst DiagPhase.eval
  have hb := MvPolynomial.aeval_bind₁ (R := ZMod (2 ^ m)) (S := ZMod (2 ^ m))
    (DiagPhase.liftBinary z)
    (fun l => if l = Fin.castAdd h i then xorForm u b else MvPolynomial.X l) Q
  simp only [MvPolynomial.aeval_eq_eval] at hb
  have hfun : (fun l => (MvPolynomial.eval (DiagPhase.liftBinary z))
      (if l = Fin.castAdd h i then xorForm (h := h) (m := m) u b else MvPolynomial.X l))
      = DiagPhase.liftBinary (Function.update z (Fin.castAdd h i)
          (b + dotF2 u fun j => z (Fin.castAdd h j))) := by
    funext l
    by_cases hl : l = Fin.castAdd h i
    · subst hl
      simp only [DiagPhase.liftBinary, Function.update_self]
      exact xorForm_eval u b z
    · simp only [MvPolynomial.eval_X, DiagPhase.liftBinary,
        Function.update_apply, if_neg hl]
  rw [hb, hfun]

/-- At `u = 0` the freeze is `freezeAt` — the pinned mode's constant substitution — at the level
of every evaluation. Two independently proved bridges meet here; the check module records it as
the agreement row. -/
theorem raiseSubst_zero_eval {n h m : ℕ} (i : Fin n) (b : ZMod 2) (Q : DiagPhase (n + h) m)
    (z : Fin (n + h) → ZMod 2) :
    DiagPhase.eval (raiseSubst i 0 b Q) z
      = DiagPhase.eval (freezeAt (Fin.castAdd h i) b Q) z := by
  rw [raiseSubst_eval, freezeAt_eval]
  congr 1
  simp [dotF2]

/-! ## The gate -/

/-- **H at a support-raising bit.** Freeze the Hadamarded coordinate to the branch value via the
XOR form, emit the sign `2^{m−1}·ℓ_u·X_i` with the degree-1 ordinary form (sound there and only
there, by `two_pow_mul_xorForm`), rotate `L` by the swap at `i`, zero the offset at `i`, and
divide `c` by `√2`. The grade `h` does **not** grow: off the shadow at most one Walsh branch
survives (`branch_unique`), so no summation variable is adjoined — contrast
`applyHFiner_h_succ`. -/
noncomputable def hRaise (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) :
    KernelSumState n where
  m := S.m
  h := S.h
  Q := raiseSubst i u (raiseConst i u S.x₀) S.Q
        + MvPolynomial.C ((2 : ZMod (2 ^ S.m)) ^ (S.m - 1))
          * raiseForm u (raiseConst i u S.x₀) * MvPolynomial.X (Fin.castAdd S.h i)
  c := S.c / (Real.sqrt 2 : ℂ)
  L := Submodule.map (pauliSwapOn {i}) S.L
  x₀ := Function.update S.x₀ i 0

/-- The precision is unchanged. -/
@[simp] theorem hRaise_m (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) :
    (hRaise i u S).m = S.m := rfl

/-- **The grade is fixed.** Contrast `applyHFiner_h_succ`: the support-raising branch costs no
summation variable. `branch_unique` is the counting fact behind this field. -/
@[simp] theorem hRaise_h (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) :
    (hRaise i u S).h = S.h := rfl

/-- The support rotates by the X↔Z swap at `i`. -/
@[simp] theorem hRaise_L (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) :
    (hRaise i u S).L = Submodule.map (pauliSwapOn {i}) S.L := rfl

/-- The offset is zeroed at the raised bit. -/
@[simp] theorem hRaise_x₀ (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) :
    (hRaise i u S).x₀ = Function.update S.x₀ i 0 := rfl

/-- The amplitude scale divides by `√2` (one surviving branch of the Walsh pair). -/
@[simp] theorem hRaise_c (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n) :
    (hRaise i u S).c = S.c / (Real.sqrt 2 : ℂ) := rfl

/-- **Eval bridge for `hRaise`** — hypothesis-free. The rewritten exponent reads: the old
exponent with the Hadamarded coordinate frozen to the `𝔽₂` branch value
`t(z) = raiseConst + u ⬝ z`, plus the emitted sign `2^{m−1}·t(z)·z_i`. Mirrors `hSumExp_eval`
and `freezeAt_eval`. -/
theorem hRaise_eval (i : Fin n) (u : Fin n → ZMod 2) (S : KernelSumState n)
    (z : Fin (n + S.h) → ZMod 2) :
    DiagPhase.eval (hRaise i u S).Q z
      = DiagPhase.eval S.Q (Function.update z (Fin.castAdd S.h i)
            (raiseConst i u S.x₀ + dotF2 u fun j => z (Fin.castAdd S.h j)))
        + (2 : ZMod (2 ^ S.m)) ^ (S.m - 1)
            * (((raiseConst i u S.x₀ + dotF2 u fun j => z (Fin.castAdd S.h j)).val
                : ZMod (2 ^ S.m)))
            * ((z (Fin.castAdd S.h i)).val : ZMod (2 ^ S.m)) := by
  simp only [hRaise, DiagPhase.eval_add, DiagPhase.eval_mul, DiagPhase.eval_C,
    DiagPhase.eval_X]
  rw [raiseSubst_eval, two_pow_mul_raiseForm_eval]

/-! ## The Bell example — the case no other constructor covers

`L_Bell = ⟨X₀X₁, Z₀Z₁⟩` has shadow `⟨(1,1)⟩`, so bit `0` is neither pinned (`X₀X₁` has
`p.X 0 = 1`) nor X-supported (`(1,0) ∉ ⟨(1,1)⟩`): `applyHPinned`, `applyHFree` and `applyHFiner`
all fail their hypotheses, and only `hRaise` applies, with representer `u = ![0,1]`. -/

/-- The Bell **exponent** input at `m = 1`, `h = 0`: flat exponent, zero offset. `L` and `c` are
inert placeholders (`⊤`, `1`): the `Q`-component of `hRaise` reads neither, and the support half
of the gate is proved separately (`HadamardTotality.lean`) — this record is *not* the Bell state's
`(L, x₀)`. -/
@[reducible] noncomputable def bellIn : KernelSumState 2 where
  m := 1
  h := 0
  Q := 0
  c := 1
  L := ⊤
  x₀ := 0

/-- **The Bell witness** (`m = 1`). The exponent comes out as the graph-state coupling
`z₀·z₁` — the CZ phase. What this row does **not** test: the freeze (`Q = 0`) and the offset
pairing (`x₀ = 0`); those are `hRaise_sParity_exponent`'s job. -/
theorem hRaise_bell_exponent (z : Fin (2 + 0) → ZMod 2) :
    DiagPhase.eval (hRaise 0 (![0, 1] : Fin 2 → ZMod 2) bellIn).Q z
      = ((z (Fin.castAdd 0 0)).val : ZMod 2) * ((z (Fin.castAdd 0 1)).val : ZMod 2) := by
  rw [hRaise_eval]
  have h0 : ∀ w : Fin (2 + 0) → ZMod 2, DiagPhase.eval bellIn.Q w = 0 := fun w => by
    simp [bellIn, DiagPhase.eval]
  have hconst : raiseConst 0 (![0, 1] : Fin 2 → ZMod 2) bellIn.x₀ = 0 := by decide
  have hdot : (dotF2 (![0, 1] : Fin 2 → ZMod 2) fun j => z (Fin.castAdd 0 j))
      = z (Fin.castAdd 0 1) := by
    simp [dotF2, Fin.sum_univ_two]
  rw [h0, hconst, hdot, zero_add, zero_add]
  simp [pow_zero, mul_comm]

/-! ## The discriminating witness — `m = 2`, every historical blind spot covered -/

/-- The `m = 2` witness input: the offset parity state (support `v₀ = 1 + v₁ + v₂`) carrying the
S-gate phase `i^{v₀}` — exponent `X₀`, so the freeze has real work to do. `L`/`c` are inert
placeholders as in `bellIn`. Bit `0` is correlated with representer `u = ![0,1,1]`, and the
offset makes `raiseConst = 1`. -/
@[reducible] noncomputable def sParityIn : KernelSumState 3 where
  m := 2
  h := 0
  Q := MvPolynomial.X (Fin.castAdd 0 0)
  c := 1
  L := ⊤
  x₀ := ![1, 0, 0]

/-- **The discriminating witness** (`m = 2`; the freeze exercised through an exponent that reads
the bit; nonzero offset; two correlated bits). The output exponent is the branch-frozen
`t + 2·t·z₀` with `t = 1 + z₁ + z₂` in `𝔽₂`. This row is aimed: substituting the ordinary-sum
form instead of the XOR form gives `3 ≠ 1` at `z = (0,1,1)` (the `m = 2`
counterexample); skipping the freeze or dropping the offset pairing fails it
elsewhere. An `m = 1` witness can see none of this — there `2 = 0`. -/
theorem hRaise_sParity_exponent (z : Fin (3 + 0) → ZMod 2) :
    (DiagPhase.eval (hRaise 0 (![0, 1, 1] : Fin 3 → ZMod 2) sParityIn).Q z : ZMod (2 ^ 2))
      = (((1 + z (Fin.castAdd 0 1) + z (Fin.castAdd 0 2)).val : ZMod (2 ^ 2)))
        * (1 + 2 * ((z (Fin.castAdd 0 0)).val : ZMod (2 ^ 2))) := by
  have hconst : raiseConst 0 (![0, 1, 1] : Fin 3 → ZMod 2) sParityIn.x₀ = 1 := by decide
  have hdot : (dotF2 (![0, 1, 1] : Fin 3 → ZMod 2) fun j => z (Fin.castAdd 0 j))
      = z (Fin.castAdd 0 1) + z (Fin.castAdd 0 2) := by
    simp [dotF2, Fin.sum_univ_three]
  have h := hRaise_eval 0 (![0, 1, 1] : Fin 3 → ZMod 2) sParityIn z
  rw [hconst, hdot] at h
  refine h.trans ?_
  simp only [sParityIn, DiagPhase.eval, MvPolynomial.eval_X, DiagPhase.liftBinary,
    Function.update_self]
  rw [← add_assoc]
  have h2 : (2 : ZMod (2 ^ 2)) ^ (2 - 1) = 2 := by norm_num
  rw [h2]
  ring_nf

/-! ## The branch count: at most one Walsh branch survives

The correctness of `hRaise` rests on a counting fact about the support, not on anything
analytic. When the Hadamarded basis vector is **not** in the X-shadow `π_X(L)`, the two Walsh
branches `w[i ← 0]` and `w[i ← 1]` differ by exactly that vector, so they lie in different
cosets of the shadow and at most one of them is on the support. That is why no summation
variable is adjoined: the branch that would have needed one is empty.

This direction needs only `e_i ∉ π_X(L)`. The converse — that at least one branch survives,
i.e. that the shadow genuinely gains `e_i` — is a Lagrangian fact, proved in
`HadamardTotality.lean` (`shadow_swap_eq`). -/

/-- The two Walsh branches at bit `i` differ by `e_i`. -/
theorem update_sub_update (w : Fin n → ZMod 2) (i : Fin n) :
    Function.update w i 0 - Function.update w i 1 = (Pi.single i 1 : Fin n → ZMod 2) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- **At most one branch survives.** With `e_i` outside the X-shadow of `L`, the two branches
sit in different shadow-cosets, so no support point has both. This is the counting fact behind
`hRaise_h`: the surviving branch is unique, so there is nothing to sum over. -/
theorem branch_unique {L : Submodule (ZMod 2) (Pauli n)} {x₀ : Fin n → ZMod 2} {i : Fin n}
    (hi : (Pi.single i 1 : Fin n → ZMod 2) ∉ Submodule.map xProj L) (w : Fin n → ZMod 2) :
    ¬ ((∃ p ∈ L, Function.update w i 0 = x₀ + p.X)
        ∧ (∃ p ∈ L, Function.update w i 1 = x₀ + p.X)) := by
  rintro ⟨⟨p, hp, hp0⟩, ⟨q, hq, hq1⟩⟩
  refine hi ?_
  have hdiff : (Pi.single i 1 : Fin n → ZMod 2) = (p - q).X := by
    rw [← update_sub_update w i, hp0, hq1]
    have : (p - q).X = p.X - q.X := by
      simp
    rw [this]; ring
  rw [hdiff]
  exact ⟨p - q, sub_mem hp hq, rfl⟩

end FTQCLib.Frame.Walkthrough
